{-# LANGUAGE
    DataKinds
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
Module      : Join.Interpreter.Basic
Copyright   : (C) Samuel A. Yallop, 2014
Maintainer  : syallop@gmail.com
Stability   : experimental

This module exports an interpreter for Programs containing core and distributed instructions from
"Join-Language".
-}
module Join.Interpreter.Basic
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
import Join.Interpreter.Basic.Debug
import Join.Interpreter.Basic.Status
import Join.Interpreter.Basic.MessageBox
import Join.Interpreter.Basic.Rule

import Network.NS

import DSL.Instruction
import DSL.Program
import DSL.Program.InterpreterR

import           Control.Applicative                ((<$>),(<*>),pure)
import           Control.Concurrent                 (forkIO,newMVar,newEmptyMVar,threadDelay,ThreadId,forkFinally)
import           Control.Concurrent.MVar            (MVar,takeMVar,putMVar,readMVar)
import           Control.Monad                      (liftM,void)
import           Control.Monad.IO.Class
import qualified Data.Bimap                as Bimap
import           Data.List                          (nub)
import qualified Data.Map                  as Map
import           Data.Maybe                         (fromJust,fromMaybe)
import           Data.Typeable
import           Data.Unique                        (hashUnique,newUnique)

-- | Some 'Rule tss p StatusPattern' with any 'tss'.
data SomeRule p = forall tss. SomeRule (Rule tss p StatusPattern)

-- | A MVar reference to SomeRule
type SomeRuleRef p = MVar (SomeRule p)

-- | Something responsible for handling a Channel.
data ChannelOwner p
  = OwnedByLocalRule  (SomeRuleRef p)
  | OwnedByRemoteName Name

-- | Associate ChanId's to the code that 'owns' it.
newtype ChannelOwners p = ChannelOwners{_channelOwners :: Map.Map ChanId (ChannelOwner p)}

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
    _children         :: Children

  -- | Map ChanId's to the code responsible for handling them.
  , _channelOwnersRef :: ChannelOwnersRef p

   -- | Map synchronous channel ids to the location waiting for a response.
  , _replyCtx         :: ReplyCtx

  -- | Map Names we've exported, to functions that accept remote
  -- messages directed to them.
  , _registrations    :: MVar (Map.Map Name (Msg -> IO ()))

  -- | Reference to the client responsible for sending and receiving messages
  -- between us (the interpreter) and a nameserver.
  , _nsClient         :: Maybe Client
  }

-- | Create a new IState instance, (with no registered nameserver).
mkIState :: IO (IState p)
mkIState = IState
  <$> newMVar []
  <*> newMVar (ChannelOwners Map.empty)
  <*> pure Map.empty
  <*> newMVar Map.empty
  <*> pure Nothing

-- | Interpreter for the core language
coreInterpreter :: InterpreterROn CoreInst p IO (IState p)
coreInterpreter iState@(IState children channelOwnersRef replyCtx _ _) baseInt = \case
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

-- Interpreter for the distributed extension
distInterpreter :: forall p. InterpreterROn DistInst p IO (IState p)
distInterpreter iState@(IState children channelOwnersRef replyCtx _ _) baseInt = \case
  LookupChannel n
    -> lookupChannel' iState n

  RegisterChannel name chan
    -> registerChannel' iState baseInt name chan


-- | Run a 'Program' containing 'CoreInst' and 'DistInst' instructions, in IO, using "Network-NS" as a nameserver
-- for registering/ looking up channels etc where 'Maybe (String,Int) gives the address and port of the nameserver to use.
run :: forall i a. (i :<= (CoreInst :+: DistInst)) => Program i a -> Maybe (String,Int) -> IO a
run p maddr = do
    iState <- case maddr of
      Nothing
        -> mkIState
      Just (address,port)
        -> do iState <- mkIState
              nsClient <- runNewClient address port (msgHandler iState)
              return $ iState{_nsClient = Just nsClient}

    result <- interpretUsing (coreInterpreter & distInterpreter) iState p

    waitForChildren (_children iState)
    return result
  where
    msgHandler :: IState p -> Callbacks
    msgHandler iState = Callbacks
      {_callbackMsgFor = \name msg -> do registrations <- readMVar (_registrations iState)
                                         case Map.lookup name registrations of

                                             -- Client promises we wont be sent messages to names
                                             -- we havnt registered, so this shouldnt happen.
                                             Nothing -> return ()

                                             Just registerF -> registerF msg

      -- TODO
      -- Nameserver quiting while a node continues is currently undefined behavior.
      -- Currently, we continue executing and probably throw an exception if further communication is attempted.
      -- We should either:
      -- - Leave this undefined and up to the interpreter to choose a behaviour
      -- - Require this 'continue if possible' behaviour
      -- - Require the computation is terminated.
      ,_callbackServerQuit = return ()

      -- TODO
      -- A name we knew has been unregistered, meaning the owner has become disconnected to the nameserver.
      -- Currently, we continue executing and probably throw an exception if we send more messages to the name.
      --
      -- We should probably remove the name mapping from the interpreter state, and could either:
      -- - Treat an unregistration as cause to terminate.
      -- - Continue until the name is used, then terminate.
      -- - Continue until the name is used, then ..coninue. This is inline with Join-Calculus semantics in that matching
      --   messages /may/ trigger matches but are not required to. Not sending a message therefore is acceptable although probably
      --   not expected..
      ,_callbackUnregistered = \n ns -> return ()
      }




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
registerMessage :: MessageType a
                => Channel A a
                -> a
                -> IState p
                -> (IState p -> p () -> IO b)
                -> IO ()
registerMessage chan msg iState retInt = do
  ChannelOwners channelOwners <- readMVar (_channelOwnersRef iState)
  let cId          = getId chan
      channelOwner = fromMaybe (error "registerMessage: chanId has no owner") $ Map.lookup cId channelOwners
  case channelOwner of

    OwnedByLocalRule someRuleRef
      -> do SomeRule rule <- takeMVar someRuleRef
            let (rule',mProcCtx) = addMessage (Message msg) cId rule
            putMVar someRuleRef (SomeRule rule')

            case mProcCtx of
               Nothing -> return ()
               Just (p,replyCtx) -> void $ forkChild (_children iState) $ void $ retInt iState{_replyCtx=replyCtx} p

    OwnedByRemoteName name
      -> void $ forkChild (_children iState) $ void $ msgTo (fromJust $ _nsClient iState) name (encodeMessage msg)

-- | On a Synchronous Channel, register a message 'a' and return a 'Response r' on which a response can
-- be waited.
registerSyncMessage :: (MessageType a, MessageType r)
                    => Channel (S r) a
                    -> a
                    -> IState p
                    -> (IState p -> p () -> IO b)
                    -> IO (Response r)
registerSyncMessage chan msg iState retInt = do
  let children         = _children iState
      channelOwnersRef = _channelOwnersRef iState

  ChannelOwners channelOwners <- readMVar channelOwnersRef
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
              Just (p,replyCtx) -> do void $ forkChild (_children iState) $ void $ retInt iState{_replyCtx=replyCtx} p
                                      return response

    OwnedByRemoteName name -> error "Synchronous remote names not implemented"
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
lookupChannel' :: forall p a. MessageType a => IState p -> Name -> IO (Maybe (Channel A a))
lookupChannel' iState name = do
  nameExists <- query (fromJust $ _nsClient iState) name
  if nameExists
    then do chan <- inferChannel <$> newChanId :: IO (Channel A a)

            -- Associate the remote name with the new channel
            let channelOwnersRef = _channelOwnersRef iState
            ChannelOwners channelOwners <- takeMVar channelOwnersRef
            let channelOwners' = Map.insert (getId chan) (OwnedByRemoteName name) channelOwners

            putMVar channelOwnersRef (ChannelOwners channelOwners')
            return $ Just chan
    else return Nothing

-- | Register a channel to a global name within the nameserver.
-- Return Bool indicates success.
registerChannel' :: forall p a. MessageType a
                 => IState p
                 -> (forall b. IState p -> p b -> IO b)
                 -> Name
                 -> Channel A a
                 -> IO Bool
registerChannel' iState baseInt name chan = do
  nowRegistered <- register (fromJust $ _nsClient iState) name
  if nowRegistered
    then do registrations <- takeMVar (_registrations iState)
            let rF = \msg -> registerMessage chan ((fromJust $ decodeMessage msg) :: a) iState baseInt

            putMVar (_registrations iState) (Map.insert name rF registrations)
            return True
    else return False

