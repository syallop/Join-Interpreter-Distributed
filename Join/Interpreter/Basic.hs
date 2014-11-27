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
import           Control.Monad.IO.Class             (liftIO)
import           Control.Monad.Operational
import qualified Data.Bimap                as Bimap
import           Data.List                          (nub)
import qualified Data.Map                  as Map
import           Data.Maybe                         (fromJust,fromMaybe)
import           Data.Typeable
import           Data.Unique                        (hashUnique,newUnique)

-- | Some 'Rule tss StatusPattern' with any 'tss'.
data SomeRule = forall tss. SomeRule (Rule tss StatusPattern)

-- | A MVar reference to SomeRule
type RuleRef = MVar SomeRule

-- | Associate ChanId's to the RuleRef which is responsible for it.
newtype RuleMap = RuleMap{_ruleMap :: Map.Map ChanId RuleRef}

-- | A MVar reference to a RuleMap.
type RuleMapRef = MVar RuleMap


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
  {_children   :: Children   -- ^ Reference to spawned sub-processes
  ,_ruleMapRef :: RuleMapRef -- ^ Map Channel's ids to responsible Rules.
  ,_replyCtx   :: ReplyCtx   -- ^ Map synchronous channel ids to the location waiting for a response.
  }

-- | Create a new BasicInterpreter instance.
mkBasicInterpreter :: IO BasicInterpreter
mkBasicInterpreter = BasicInterpreter
  <$> newMVar []
  <*> newMVar (RuleMap Map.empty)
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

    ,_iNewChannel = inferSync <$> newChanId

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
registerMessage :: MessageType a => Channel A (a :: *) -> a -> Children -> RuleMapRef -> IO ()
registerMessage chan msg children ruleMapRef = do
  (RuleMap ruleMap) <- readMVar ruleMapRef
  let cId     = getId chan
      ruleRef = fromMaybe (error "registerMessage: ChanId has no RuleRef") $ Map.lookup cId ruleMap

  (SomeRule rule) <- takeMVar ruleRef
  let (rule',mProcCtx) = addMessage (Message msg) cId rule
  putMVar ruleRef (SomeRule rule')

  case mProcCtx of
    Nothing -> return ()
    Just (p,replyCtx) -> do forkChild children $ interpretWith (BasicInterpreter children ruleMapRef replyCtx) p
                            return ()

-- | On a Synchronous Channel, register a message 'a' and return a 'Response r' on which a response can
-- be waited.
registerSyncMessage :: (MessageType a,MessageType r) => Channel (S r) a -> a -> Children -> RuleMapRef -> IO (Response r)
registerSyncMessage chan msg children ruleMapRef = do
  (RuleMap ruleMap) <- readMVar ruleMapRef
  let cId = getId chan
      ruleRef = fromMaybe (error "registerSyncMessage: ChanId has no RuleRef") $ Map.lookup cId ruleMap

  (SomeRule rule) <- takeMVar ruleRef
  replyChan <- newEmptyMVar
  response <- emptyResponse
  forkChild children $ waitOnReply replyChan response
  let (rule',mProcCtx) = addMessage (SyncMessage msg replyChan) cId rule
  putMVar ruleRef (SomeRule rule')

  case mProcCtx of
    Nothing -> return response
    Just (p,replyCtx) -> do forkChild children $ interpretWith (BasicInterpreter children ruleMapRef replyCtx) p
                            return response
  where
    waitOnReply :: MessageType r => ReplyChan r -> Response r -> IO ()
    waitOnReply replyChan response = takeMVar replyChan >>= writeResponse response

-- | Register a new Join Definition, associating all contained Channels
-- with the stored RuleRef.
registerDefinition :: Definitions tss Inert -> RuleMapRef -> IO ()
registerDefinition definition ruleMapRef = do
  (RuleMap ruleMap) <- takeMVar ruleMapRef
  rId <- newRuleId
  let someRule = SomeRule $ mkRule definition rId
      cIds     = uniqueIds definition
  rlRef <- newMVar someRule
  let additionalMappings = Map.fromSet (const rlRef) cIds
      ruleMap'           = additionalMappings `Map.union` ruleMap :: Map.Map ChanId RuleRef
  putMVar ruleMapRef (RuleMap ruleMap')

-- | New unique ChanId.
newChanId :: IO ChanId
newChanId = ChanId <$> newId

-- | New unique RuleId.
newRuleId :: IO RuleId
newRuleId = RuleId <$> newId

-- | New unique Int id.
newId :: IO Int
newId = hashUnique <$> newUnique

