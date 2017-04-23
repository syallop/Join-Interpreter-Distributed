{-# LANGUAGE
    DataKinds
  , DeriveGeneric
  , GADTs
  , KindSignatures
  , LambdaCase
  , MultiParamTypeClasses
  , PolyKinds
  , RankNTypes
  , ScopedTypeVariables
  , TypeOperators
  , FlexibleContexts
  #-}
{-|
Module      : Join.Interpreter.Distributed
Copyright   : (C) Samuel A. Yallop, 2017
Maintainer  : syallop@gmail.com
Stability   : experimental

This module exports an interpreter for Programs containing core and distributed instructions from
"Join-Language".
-}
module Join.Interpreter.Distributed
    ( -- * Run an Interpreter
      run

    , coreInterpreter
    , distInterpreter

    , IState(..)
    , mkIState
    ) where

import Prelude hiding (lookup)

import Join hiding ((&))
import Join.Language.Distributed
import Join.Pattern.Rep

import Join.Interpreter.Distributed.Debug
import Join.Interpreter.Distributed.Status
import Join.Interpreter.Distributed.MessageBox
import Join.Interpreter.Distributed.Rule

import DSL.Instruction
import DSL.Program
import DSL.Program.InterpreterR

import DHT
import DHT.Contact

import DHT.NS

import           Control.Applicative                ((<$>),(<*>),pure)
import           Control.Concurrent                 (forkIO,newMVar,newEmptyMVar,threadDelay,ThreadId,forkFinally)
import           Control.Concurrent.MVar            (MVar,takeMVar,putMVar,readMVar,modifyMVar)
import           Control.Monad                      (liftM,void,join)
import           Control.Monad.IO.Class
import qualified Data.Bimap                as Bimap
import           Data.List                          (nub)
import qualified Data.Map                  as Map
import           Data.Maybe                         (fromJust,fromMaybe)
import           Data.Typeable
import           Data.Unique                        (hashUnique,newUnique)

import           Network.Socket                       (Socket,socket,Family(AF_INET),SocketType(Datagram),inet_addr,SockAddr(SockAddrInet),inet_ntoa,bind,connect)
import qualified Data.ByteString.Char8      as Strict
import qualified Data.ByteString.Lazy.Char8 as Lazy
import qualified Network.Socket.ByteString  as Strict

import qualified Control.Concurrent.Chan as CC

import Data.Binary
import Data.Binary.Get
import Data.Binary.Put
import GHC.Generics (Generic)

import Debug.Trace

-- | Some 'Rule tss p StatusPattern' with any 'tss'.
-- A Rule where we've forgotten the types of the definitions but retain the
-- program type.
data SomeRule p = forall tss. SomeRule (Rule tss p StatusPattern)

-- | A MVar reference to SomeRule
type SomeRuleRef p = MVar (SomeRule p)


-- | The name a Channel might be known by to other join instances
type GlobalName = String

-- | A message as sent across the network to another join instance
type RemoteMsg = ByteString


-- | Messages that remote join instances might send to our instance
-- NOTE: Currently the distributed language does not cover remote synchronous
-- channels, so we have no messages for syncsends and have no requirement to
-- return anything. In fact we'll probably ignore all miscoded data or names we
-- dont have. If we stored a type fingerprint in the DHT, the sender could check
-- theyre not doing this.
data JoinMsg
  -- They have it on good authority we registered some GlobalName and that it
  -- should be passed the given RemoteMsg
  = PleaseSend GlobalName RemoteMsg
  deriving (Generic,Show)

instance Binary JoinMsg

decodeJoinMsg :: ByteString -> Maybe JoinMsg
decodeJoinMsg bs = Just <$> (`runGet` Lazy.fromStrict bs) $ get

encodeJoinMsg :: JoinMsg -> ByteString
encodeJoinMsg = Lazy.toStrict . runPut . put


-- | Something responsible for handling a Channel.
data ChannelOwner p
  = OwnedByLocalRule  (SomeRuleRef p)
  | OwnedByRemote GlobalName Addr

-- | Associate ChanId's to the code that 'owns' it.
--
-- Channels have ChanIds so this structure allows us to decide whether it is
-- local or a reference to a Channel we've looked up on a remote join instance.
newtype ChannelOwners p = ChannelOwners {_channelOwners :: Map.Map ChanId (ChannelOwner p)}

-- | A MVar reference to 'ChannelOwners'
type ChannelOwnersRef p = MVar (ChannelOwners p)


-- | Child 'Process's are tracked in a list of MVar's,
-- each of which is left empty until the process has finished.
-- This allows the main process to wait for every subprocess to
-- finish before exiting.
type Children = MVar [MVar ()]

-- | Wait for all children to finish.
-- (Every child has put (), and is taken from the collection
-- , leaving it empty []).
waitForChildren :: Children -> IO ()
waitForChildren children = do
  cs <- takeMVar children
  case cs of
    []   -> return ()
    m:ms -> do
      putMVar children ms
      takeMVar m
      waitForChildren children

-- | Fork a new child thread in the given context.
forkChild :: Children -> IO () -> IO ThreadId
forkChild children io = do
  m  <- newEmptyMVar
  cs <- takeMVar children
  putMVar children (m:cs)
  forkFinally io (\_ -> putMVar m ())

-- | Interpreter state.
data IState p = IState
  { -- | Reference to spawned sub-processes.
    -- If we get to the end of a top-level join process, we must still wait for
    -- all of the children to die before we can terminate.
    _iStateChildren         :: Children

  -- | Map ChanId's to the code responsible for handling them.
  -- Channels contain a ChanId. This mapping allows us to determine whether we
  -- own them or whether they refer to a looked up name in some remote join
  -- instance.
  , _iStateChannelOwnersRef :: ChannelOwnersRef p

   -- | Map synchronous channel ids to the location waiting for a response.
  , _iStateReplyCtx         :: ReplyCtx

  -- | Map GlobalNames we've exported, to functions that accept remote
  -- messages directed to them.
  --
  -- When we encounter a message send to a Channel, we extract its ChanId, look
  -- up the owner in the ChannelOwnersRef, and then if it is owned remotely, we
  -- expect to find a function here which will send the message.
  , _iStateRegistrations    :: MVar (Map.Map GlobalName (RemoteMsg -> IO ()))

  -- | Reference to the dht responsible for looking up and registering channels
  , _iStateDHTNS            :: Maybe DHTNS

  -- Map each Join instances Address we've established contact with previously to its outgoing
  -- socket. Allows socket reuse.
  , _iStateSendingSockets   :: MVar (Map.Map Addr Socket)
  }

-- | Create a new IState instance, (with no registered nameserver).
mkIState :: IO (IState p)
mkIState = IState
  <$> newMVar []
  <*> newMVar (ChannelOwners Map.empty)
  <*> pure Map.empty
  <*> newMVar Map.empty
  <*> pure Nothing
  <*> newMVar Map.empty

-- | Interpreter for the core language which requires an 'IState p' 'R'eader
-- context to perform its interpretation.
-- This can be used on any composite DSL of 'CoreInst' within a program type
-- 'p'.
coreInterpreter :: InterpreterROn CoreInst p IO (IState p)
coreInterpreter iState@(IState children channelOwnersRef replyCtx registrations joinDHT sendingSockets) baseInt = \case
  Def definitions
    -> registerDefinition (toDefinitions definitions) channelOwnersRef

  NewChannel
    -> inferChannel <$> newChanId

  Send chan msg
    -> registerMessage chan msg iState baseInt

  Spawn p
    -> void $ forkChild children $ void $ baseInt iState p

  Sync chan msg
    -> registerSyncMessage chan msg iState baseInt

  Reply sc m
    -> putMVar (lookupReplyChan replyCtx (getId sc)) m

  With p q
    -> mapM_ (forkChild children . baseInt iState) [p,q]

  IOAction io
    -> io

-- Interpreter for the distributed extension which requires an 'IState p'
-- 'R'eader context to perform its interpretation.
-- This can be used on any composite DSL of 'DistInst' within a program type
-- 'p'.
distInterpreter :: forall p. InterpreterROn DistInst p IO (IState p)
distInterpreter iState@(IState children channelOwnersRef replyCtx registrations joinDHT sendingSockets) baseInt = \case
  LookupChannel n
    -> lookupChannel' iState n

  RegisterChannel name chan
    -> registerChannel' iState baseInt name chan


-- | Run a 'Program' containing 'CoreInst' and 'DistInst' instructions, in IO, using "DHT"
-- for registering/ looking up channels.
run :: forall i a
     . (i :<= (CoreInst :+: DistInst))
    => Addr         -- ^ Address to receive join messages
    -> Addr         -- ^ Address to bind OUR DHT on
    -> Maybe Addr   -- ^ Possible DHT bootstrap node
    -> LoggingOp IO -- ^ Possible logging operation
    -> Int          -- ^ Hash size to use for IDs in the DHT
    -> Program i a  -- ^ Program containing CoreInst and DistInst instructions
    -> IO a         -- ^ Execute in IO
run joinAddr ourDHTAddr mBootstrapAddr loggingOp hashSize p = do
    -- Create the config for the DHT Name Server
    -- Then start running it.
    dhtnsConfig <- mkDHTNSConfig ourDHTAddr hashSize loggingOp mBootstrapAddr
    dhtns       <- newDHTNSNode dhtnsConfig joinAddr

    -- The interpreter state
    iState <- do halfIState <- mkIState
                 return $ halfIState{_iStateDHTNS = Just dhtns}

    -- Start listening for channel sends by other Join instances
    forkIO $ receiveRemoteJoinMessages iState joinAddr

    -- Execute the join program using our two interpreters and current state
    result <- interpretUsing (coreInterpreter & distInterpreter) iState p

    -- We must wait for all children processes to die before ending, otherwise
    -- as soon as our interpreter reaches the last top-level instruction,
    -- everything will be killed.
    waitForChildren (_iStateChildren iState)
    return result
  where

    -- When other join instances have determined that we own a channel (by
    -- consulting the DHT) they may send messages to our channels.
    --
    -- Note: The DistInst instruction set only (currently) operates on so called
    -- 'Asynchronous' Channels and so none of these messages will require
    -- sending replies.
    receiveRemoteJoinMessages :: IState p -> Addr -> IO ()
    receiveRemoteJoinMessages iState joinAddr = do
      -- Queue of decoded messages from remote join instances
      externalChannelSends <- CC.newChan :: IO (CC.Chan JoinMsg)

      -- Receive all remote Join messages on a UDP socket, placing them into a
      -- channel
      void $ forkIO $ receiveRemoteJoinUDPMsgs joinAddr externalChannelSends iState

      -- Read the JoinMsgs from the channel and register messages locally
      -- (if they're valid).
      void $ forkIO $ registerRemoteJoinMsgs externalChannelSends iState

      return ()


    -- Create a UDP socket to listen for JoinMsgs on and fork a process to
    -- repeatedly parse any messages into the given Chan.
    -- You should then read from this channel and perform the appropriate
    -- actions E.G. registering the messages locally.
    receiveRemoteJoinUDPMsgs :: Addr
                            -> CC.Chan JoinMsg
                            -> IState p
                            -> IO ()
    receiveRemoteJoinUDPMsgs joinAddr externalJoinMsgs iState = do
      ourSock <- socket AF_INET Datagram 17

      -- Bind ourSock to the requested joinIP and port
      let Addr joinIP joinPort = joinAddr
          udpPort = fromInteger $ toInteger joinPort
      inetAddr <- inet_addr joinIP
      bind ourSock $ SockAddrInet udpPort inetAddr

      _ <- forkIO $ receiveRemoteJoinUDPMsgsOnSocket externalJoinMsgs ourSock
      return ()

    -- Read bytes sent to our UDP socket, parse and do something
    receiveRemoteJoinUDPMsgsOnSocket :: CC.Chan JoinMsg
                                    -> Socket
                                    -> IO x
    receiveRemoteJoinUDPMsgsOnSocket externalJoinMsgs ourSock = do
      (msg,SockAddrInet _port _fromHost) <- Strict.recvFrom ourSock 1024
      -- Attempt decoding
      case decodeJoinMsg msg of
        -- Doesnt follow our message format.
        -- Silently ignore and go again.
        Nothing
          -> receiveRemoteJoinUDPMsgsOnSocket externalJoinMsgs ourSock

        -- Queue the decoded message to be sent to the appropriate rule by
        -- another process.
        Just remoteJoinMsg
          -> do CC.writeChan externalJoinMsgs remoteJoinMsg
                receiveRemoteJoinUDPMsgsOnSocket externalJoinMsgs ourSock


    -- Continually read from the Chan of parsed remote JoinMsgs and register
    -- them in the same way as if the local join program had sent on that
    -- channel
    registerRemoteJoinMsgs :: CC.Chan JoinMsg
                           -> IState p
                           -> IO x
    registerRemoteJoinMsgs externalJoinMsgs iState = join $ do
      joinMsg <- CC.readChan externalJoinMsgs
      return $ do case joinMsg of
                    -- We have a request to send to a name the remote join
                    -- instance believes we possess.
                    PleaseSend globalName remoteMsg
                      -> do registrations <- takeMVar (_iStateRegistrations iState)
                            case Map.lookup globalName registrations of

                              -- They've sent us a message at a name we havnt
                              -- registered.
                              -- Silently drop.
                              -- TODO: DONT silently drop.
                              Nothing
                                -> return ()

                              -- We're storing a function which says how this
                              -- join channel message is to be registered
                              Just registerF
                                -> registerF remoteMsg

                  -- Go again.
                  registerRemoteJoinMsgs externalJoinMsgs iState


-- Given a JoinMsg to send, and a recipient that we've already determined,
-- physically send the message.
sendRemoteJoinMsg :: IState p -> JoinMsg -> Addr -> IO ()
sendRemoteJoinMsg iState joinMsg targetAddr = modifyMVar (_iStateSendingSockets iState) $ \sendingSockets -> do
  -- Get an existing socket if one exists, a new one if not and cache
  (sockToTarget,sendingSockets') <- getRemoteSocket sendingSockets

  let bs = encodeJoinMsg joinMsg

  -- If in the future we add messages which expect replies, we might need to
  -- append OUR port onto the message to send as part of the schema? Maybe that
  -- would be done at the encoding point better!
  nBytes <- Strict.send sockToTarget bs

  --TODO: Check the amount of bytes sent is what we expect

  return (sendingSockets',())
  where
    -- Lookup a remote socket in the map. If one does not exist, establish one
    -- and insert.
    getRemoteSocket :: Map.Map Addr Socket -> IO (Socket,Map.Map Addr Socket)
    getRemoteSocket sendingSockets =
      case Map.lookup targetAddr sendingSockets of
        -- Already have a socket to this target
        Just sock
          -> return (sock,sendingSockets)

        -- No existing socket to this target, create one
        Nothing
          -> do let Addr targetIp targetPort = targetAddr
                    ipv4 = AF_INET
                    udp  = 17
                    udpPort = fromInteger $ toInteger targetPort
                inetAddr <- inet_addr targetIp

                sock <- socket ipv4 Datagram udp
                connect sock $ SockAddrInet udpPort inetAddr
                return (sock, Map.insert targetAddr sock $ sendingSockets)

-- | Lookup a ChanId's associated ReplyChan 'r' within a ReplyCtx.
-- The ChanId must have an associated ReplyChan and it must
-- have the expected type.
lookupReplyChan :: MessageType r => ReplyCtx -> ChanId -> ReplyChan r
lookupReplyChan replyCtx cId = case Map.lookup cId replyCtx of
  Nothing -> error "ChanId has no associated ReplyChan in this context."
  Just (SomeReplyChan replyChan) -> case cast replyChan of
    Nothing -> error "ReplyChan does not have the assumed type."
    Just replyChan' -> replyChan'



-- | On an Asynchronous Channel, register a message 'a'.
--
-- This function is called on local OR remote channels.
registerMessage :: MessageType a
                => Channel A a
                -> a
                -> IState p
                -> (IState p -> p () -> IO b)
                -> IO ()
registerMessage chan msg iState retInt = do
  ChannelOwners channelOwners <- readMVar (_iStateChannelOwnersRef iState)
  let cId          = getId chan
      channelOwner = fromMaybe (error "registerMessage: chanId has no owner") $ Map.lookup cId channelOwners
  case channelOwner of

    OwnedByLocalRule someRuleRef
      -> do SomeRule rule <- takeMVar someRuleRef
            let (rule',mProcCtx) = addMessage (Message msg) cId rule
            putMVar someRuleRef (SomeRule rule')

            case mProcCtx of
               Nothing -> return ()
               Just (p,replyCtx) -> void $ forkChild (_iStateChildren iState) $ void $ retInt iState{_iStateReplyCtx=replyCtx} p

    -- TODO:
    OwnedByRemote globalName remoteJoinAddr
      {--> void $ forkChild (_children iState) $ void $ msgTo (fromJust $ _nsClient iState) name (encodeMessage msg)-}
      -> void $ forkChild (_iStateChildren iState) $ void $ sendRemoteJoinMsg iState (PleaseSend globalName (encodeMessage msg)) remoteJoinAddr

-- | On a Synchronous Channel, register a message 'a' and return a 'Response r' on which a response can
-- be waited.
--
-- This function is called on LOCAL channels.
registerSyncMessage :: (MessageType a, MessageType r)
                    => Channel (S r) a
                    -> a
                    -> IState p
                    -> (IState p -> p () -> IO b)
                    -> IO (Response r)
registerSyncMessage chan msg iState retInt = do
  let children         = _iStateChildren iState
      channelOwnersRef = _iStateChannelOwnersRef iState

  ChannelOwners channelOwners <- takeMVar channelOwnersRef
  let cId          = getId chan
      channelOwner = fromMaybe (error "registerSyncMessage: ChanId has no owner") $ Map.lookup cId channelOwners

  case channelOwner of
    OwnedByLocalRule someRuleRef
      -> do SomeRule rule <- takeMVar someRuleRef

            replyChan <- newEmptyMVar
            response  <- emptyResponse
            forkChild children $ waitOnReply replyChan response
            let (rule',mProcCtx) = addMessage (SyncMessage msg replyChan) cId rule
            putMVar someRuleRef (SomeRule rule')

            case mProcCtx of
              Nothing -> return response
              Just (p,replyCtx) -> do void $ forkChild (_iStateChildren iState) $ void $ retInt iState{_iStateReplyCtx=replyCtx} p
                                      return response

    OwnedByRemote globalName remoteJoinAddr
      -> error "Synchronous remote names not implemented"
  where
    waitOnReply :: ReplyChan r -> Response r -> IO ()
    waitOnReply replyChan response = takeMVar replyChan >>= writeResponse response



-- | Register a new Join Definition, associating all contained Channels
-- with the stored RuleRef.
registerDefinition :: Definitions tss (p ()) -> ChannelOwnersRef p -> IO ()
registerDefinition definition channelOwnersRef = do
  ChannelOwners channelOwners <- takeMVar channelOwnersRef
  rId <- newRuleId
  let someRule = SomeRule $ mkRule definition rId
      cIds     = uniqueIds definition
  rlRef <- newMVar someRule
  let additionalMappings = Map.fromSet (const (OwnedByLocalRule rlRef)) cIds
      channelOwners'     = additionalMappings `Map.union` channelOwners
  putMVar channelOwnersRef $ ChannelOwners channelOwners'

-- | New unique ChanId.
newChanId :: IO ChanId
newChanId = ChanId <$> newId

-- | New unique RuleId.
newRuleId :: IO RuleId
newRuleId = RuleId <$> newId

-- | New unique Int id.
newId :: IO Int
newId = hashUnique <$> newUnique



-- | Lookup a join channel maintained on some remote node.
--
-- It is the callers responsibility to ensure the channels type is correct.
-- Providing an incorrect type may cause exceptions on the recieving end.
lookupChannel' :: forall p a
                . MessageType a
               => IState p
               -> GlobalName
               -> IO (Maybe (Channel A a))
lookupChannel' iState globalName = do
  let dhtns = fromJust $ _iStateDHTNS iState
  mAddr <- lookupNameWithDHTNS dhtns globalName

  case mAddr of

    -- The DHT has no stored address for this value.
    Nothing
      -> return Nothing

    -- The DHT has a registered remote Join instance against this value.
    Just remoteJoinAddr
      -> do chan <- inferChannel <$> newChanId :: IO (Channel A a)

            -- TODO: ModifyMVar
            -- Associate the remote name with the new channel
            let channelOwnersRef = _iStateChannelOwnersRef iState
            ChannelOwners channelOwners <- takeMVar channelOwnersRef
            let channelOwners' = Map.insert (getId chan) (OwnedByRemote globalName remoteJoinAddr) channelOwners
            putMVar channelOwnersRef (ChannelOwners channelOwners')

            return $ Just chan




-- | Register a channel to a global name within the nameserver.
-- Return Bool indicates success.
registerChannel' :: forall p a. MessageType a
                 => IState p
                 -> (forall b. IState p -> p b -> IO b)
                 -> GlobalName
                 -> Channel A a
                 -> IO Bool
registerChannel' iState baseInt globalName chan = do
  let dhtns = fromJust $ _iStateDHTNS iState
  nowRegistered <- registerNameWithDHTNS dhtns globalName
  if nowRegistered
    then do registrations <- takeMVar (_iStateRegistrations iState)
            let rF = \msg -> registerMessage chan ((fromJust $ decodeMessage msg) :: a) iState baseInt

            putMVar (_iStateRegistrations iState) (Map.insert globalName rF registrations)
            return True
    else return False

