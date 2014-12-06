{-# LANGUAGE DataKinds
            ,GADTs
            ,KindSignatures
            ,MultiParamTypeClasses
            ,PolyKinds
            ,RankNTypes
  #-}
{-|
Module      : Join.Interpreter.Basic
Copyright   : (C) Samuel A. Yallop, 2014
Maintainer  : syallop@gmail.com
Stability   : experimental

This module exports an interpreter for 'Process a' s written in Join.Language.
-}
module Join.Interpreter.Basic
    (run
    ) where

import Prelude hiding (lookup)

import Join
import Join.Interpreter.Interface
import Join.Pattern.Rep
import Join.Interpreter.Basic.Debug
import Join.Interpreter.Basic.Status
import Join.Interpreter.Basic.MessageBox
import Join.Interpreter.Basic.Rule

import           Control.Applicative                ((<$>),(<*>),pure)
import           Control.Concurrent                 (forkIO,newMVar,newEmptyMVar,threadDelay,ThreadId,forkFinally)
import           Control.Concurrent.MVar            (MVar,takeMVar,putMVar,readMVar)
import           Control.Monad                      (liftM,void)
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
  = OwnedByLocalRule SomeRuleRef

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
  {-, _ruleMapRef :: RuleMapRef-}
  , _channelOwnersRef :: ChannelOwnersRef

   -- | Map synchronous channel ids to the location waiting for a response.
  , _replyCtx   :: ReplyCtx
  }

-- | Create a new BasicInterpreter instance.
mkBasicInterpreter :: IO BasicInterpreter
mkBasicInterpreter = BasicInterpreter
  <$> newMVar []
  <*> newMVar (ChannelOwners Map.empty)
  <*> pure Map.empty

-- | Run a 'Process a' computation in IO
-- ,terminating only when all sub-processes have terminated.
run :: Process a -> IO a
run p = do
  basicInterpreter <- mkBasicInterpreter
  a <- interpretWith basicInterpreter p
  waitForChildren (_children basicInterpreter)
  return a

instance Interpreter BasicInterpreter IO where
  getInterpreterFs basicInterpreter@(BasicInterpreter children ruleMapRef replyCtx) = InterpreterFs
    {_iReturn     = \a -> return a

    ,_iDef        = \definitions
                     -> registerDefinition (toDefinitions definitions) ruleMapRef

    ,_iNewChannel = inferChannel <$> newChanId

    ,_iSend       = \c m
                     -> registerMessage c m children ruleMapRef

    ,_iSpawn      = \p
                     -> void $ forkChild children $ interpretWith basicInterpreter p

    ,_iSync       = \sc sm
                     -> registerSyncMessage sc sm children ruleMapRef

    ,_iReply      = \sc m
                     -> putMVar (lookupReplyChan replyCtx (getId sc)) m

    ,_iWith       = \p q
                     -> mapM_ (forkChild children . interpretWith basicInterpreter) [p,q]
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
registerMessage :: MessageType a => Channel A (a :: *) -> a -> Children -> ChannelOwnersRef -> IO ()
registerMessage chan msg children channelOwnersRef = do
  ChannelOwners channelOwners <- readMVar channelOwnersRef
  let cId          = getId chan
      channelOwner = fromMaybe (error "registerMessage: ChanId has no owner") $ Map.lookup cId channelOwners

  case channelOwner of
    OwnedByLocalRule someRuleRef
      -> do SomeRule rule <- takeMVar someRuleRef
            let (rule',mProcCtx) = addMessage (Message msg) cId rule
            putMVar someRuleRef (SomeRule rule')

            case mProcCtx of
              Nothing -> return ()
              Just (p,replyCtx) -> do forkChild children $ interpretWith (BasicInterpreter children channelOwnersRef replyCtx) p
                                      return ()

-- | On a Synchronous Channel, register a message 'a' and return a 'Response r' on which a response can
-- be waited.
registerSyncMessage :: (MessageType a,MessageType r) => Channel (S r) a -> a -> Children -> ChannelOwnersRef -> IO (Response r)
registerSyncMessage chan msg children channelOwnersRef = do
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
              Just (p,replyCtx) -> do forkChild children $ interpretWith (BasicInterpreter children channelOwnersRef replyCtx) p
                                      return response
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

