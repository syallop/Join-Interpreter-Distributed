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

This module exports an interpreter for 'Process a' s written in Join.Language.
-}
module Join.Interpreter.Basic
    ( -- * Run an Interpreter
      run
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
import DSL.Program.Interpreter

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

-- | Some 'Rule tss StatusPattern' with any 'tss'.
data SomeRule = forall tss. SomeRule (Rule tss StatusPattern)

-- | A MVar reference to SomeRule
type SomeRuleRef = MVar SomeRule

-- | Something responsible for handling a Channel.
data ChannelOwner
  = OwnedByLocalRule  SomeRuleRef
  | OwnedByRemoteName Name

-- | Associate ChanId's to the code that 'owns' it.
newtype ChannelOwners = ChannelOwners{_channelOwners :: Map.Map ChanId ChannelOwner}

-- | A MVar reference to 'ChannelOwners'
type ChannelOwnersRef = MVar ChannelOwners


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
data BasicInterpreter = BasicInterpreter
  { -- | Reference to spawned sub-processes.
    _children         :: Children

  -- | Map ChanId's to the code responsible for handling them.
  , _channelOwnersRef :: ChannelOwnersRef

   -- | Map synchronous channel ids to the location waiting for a response.
  , _replyCtx   :: ReplyCtx

  -- | Map Names we've exported, to functions that accept remote
  -- messages directed to them.
  , _registrations :: MVar (Map.Map Name (Msg -> IO ()))

  -- | Reference to the client responsible for sending and receiving messages
  -- between us (the interpreter) and a nameserver.
  , _nsClient      :: Maybe Client
  }

-- | Create a new BasicInterpreter instance.
mkBasicInterpreter :: IO BasicInterpreter
mkBasicInterpreter = BasicInterpreter
  <$> newMVar []
  <*> newMVar (ChannelOwners Map.empty)
  <*> pure Map.empty
  <*> newMVar Map.empty
  <*> pure Nothing

type BIState = BasicInterpreter

-- | Interpreter for the core language
coreInterpreter :: BIState -> Interpreter CoreInst IO
coreInterpreter basicInterpreter@(BasicInterpreter children channelOwnersRef replyCtx _ _) = \case
  Def definitions
    -> registerDefinition (toDefinitions definitions) channelOwnersRef

  NewChannel
    -> inferChannel <$> newChanId

  Send c m
    -> registerMessage c m basicInterpreter

  Spawn p
    -> void $ forkChild children $ interpretUsing (coreInterpreter basicInterpreter) p

  Sync sc sm
    -> registerSyncMessage sc sm basicInterpreter

  Reply sc m
    -> putMVar (lookupReplyChan replyCtx (getId sc)) m

  With p q
    -> mapM_ (forkChild children . interpretUsing (coreInterpreter basicInterpreter)) [p,q]

  IOAction io
    -> io

-- Interpreter for the distributed extension
distInterpreter :: BIState -> Interpreter DistInst IO
distInterpreter basicInterpreter@(BasicInterpreter children channelOwnersRef replyCtx _ _) = \case
  LookupChannel n
    -> interpretUsing (coreInterpreter basicInterpreter) $ lookupChannel' basicInterpreter n

  RegisterChannel n c
    -> interpretUsing (coreInterpreter basicInterpreter) $ registerChannel' basicInterpreter n c

-- Combined interpreter for the core and distributed instructions.
combInterpreters :: BIState -> Interpreter (CoreInst :+: DistInst) IO
combInterpreters bi = (coreInterpreter bi) & (distInterpreter bi)

run :: (i :<= (CoreInst :+: DistInst)) => Program i a -> Maybe (String,Int) -> IO a
run p maddr = do
    basicInterpreter <- case maddr of
      Nothing
        -> mkBasicInterpreter
      Just (address,port)
        -> do basicInterpreter <- mkBasicInterpreter
              nsClient <- runNewClient address port (msgHandler basicInterpreter)
              return $ basicInterpreter{_nsClient = Just nsClient}

    result <- interpretUsing (combInterpreters basicInterpreter) p

    waitForChildren (_children basicInterpreter)
    return result
  where
    msgHandler :: BasicInterpreter -> Callbacks
    msgHandler bi = Callbacks
      {_callbackMsgFor = \name msg -> do registrations <- readMVar (_registrations bi)
                                         case Map.lookup name registrations of

                                             -- Client promises we wont be sent messages to names
                                             -- we havnt registered, so this shouldnt happen.
                                             Nothing -> return ()

                                             Just registerF -> registerF msg

      -- TODO
      ,_callbackServerQuit = return ()

      -- TODO
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
registerMessage :: MessageType a => Channel A (a :: *) -> a -> BasicInterpreter -> IO ()
registerMessage chan msg bi = do
  let children         = _children bi
      channelOwnersRef = _channelOwnersRef bi

  ChannelOwners channelOwners <- readMVar channelOwnersRef
  let cId          = getId chan
      channelOwner = fromMaybe (error "registerMessage: ChanId has no owner") $ Map.lookup cId channelOwners

  case channelOwner of
    -- Channel is owned by a local rule.
    OwnedByLocalRule someRuleRef
      -> do SomeRule rule <- takeMVar someRuleRef
            let (rule',mProcCtx) = addMessage (Message msg) cId rule
            putMVar someRuleRef (SomeRule rule')

            case mProcCtx of
              Nothing -> return ()
              Just (p,replyCtx) -> do forkChild children $ interpretUsing (coreInterpreter $ bi{_replyCtx=replyCtx}) p
                                      return ()

    -- Channel is owned by a remote node. Encode and relay.
    OwnedByRemoteName name
      -> do forkChild children $ void $ msgTo (fromJust $ _nsClient bi) name (encodeMessage msg)
            return ()

-- | On a Synchronous Channel, register a message 'a' and return a 'Response r' on which a response can
-- be waited.
registerSyncMessage :: (MessageType a,MessageType r) => Channel (S r) a -> a -> BasicInterpreter -> IO (Response r)
registerSyncMessage chan msg bi = do
  let children         = _children bi
      channelOwnersRef = _channelOwnersRef bi

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
              Just (p,replyCtx) -> do forkChild children $ interpretUsing (coreInterpreter (BasicInterpreter children channelOwnersRef replyCtx undefined undefined)) p
                                      return response

    OwnedByRemoteName name -> error "Synchronous remote names not implemented"
  where
    waitOnReply :: ReplyChan r -> Response r -> IO ()
    waitOnReply replyChan response = takeMVar replyChan >>= writeResponse response

-- | Register a new Join Definition, associating all contained Channels
-- with the stored RuleRef.
registerDefinition :: Definitions tss Inert -> ChannelOwnersRef -> IO ()
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
lookupChannel' :: forall a. MessageType a => BasicInterpreter -> Name -> Process (Maybe (Channel A a))
lookupChannel' bi name = do
  nameExists <- liftIO $ query (fromJust $ _nsClient bi) name
  if nameExists
    then do chan <- newChannel :: Process (Channel A a)

            -- Associate the remote name with the new channel
            let channelOwnersRef = _channelOwnersRef bi
            ChannelOwners channelOwners <- liftIO $ takeMVar channelOwnersRef
            let channelOwners' = Map.insert (getId chan) (OwnedByRemoteName name) channelOwners

            liftIO $ putMVar channelOwnersRef (ChannelOwners channelOwners')
            return $ Just chan
    else return Nothing

-- | Register a channel to a global name within the nameserver.
-- Return Bool indicates success.
registerChannel' :: forall a. MessageType a => BasicInterpreter -> Name -> Channel A a -> Process Bool
registerChannel' bi name chan = do
  nowRegistered <- liftIO $ register (fromJust $ _nsClient bi) name
  if nowRegistered
    then do registrations <- liftIO $ takeMVar (_registrations bi)
            let rF = \msg -> registerMessage chan ((fromJust $ decodeMessage msg) :: a) bi

            liftIO $ putMVar (_registrations bi) (Map.insert name rF registrations)
            return True
    else return False

