{-# LANGUAGE DataKinds
            ,GADTs
            ,KindSignatures
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
import Join.Pattern.Rep
import Join.Interpreter.Basic.Debug
import Join.Interpreter.Basic.Status
import Join.Interpreter.Basic.MessageBox
import Join.Interpreter.Basic.Rule

import           Control.Applicative                ((<$>),(<*>),pure)
import           Control.Concurrent                 (forkIO,newMVar,newEmptyMVar,threadDelay,ThreadId,forkFinally)
import           Control.Concurrent.MVar            (MVar,takeMVar,putMVar,readMVar)
import           Control.Monad                      (liftM)
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

-- | Create a new empty RuleMapRef
newRuleMapRef :: IO RuleMapRef
newRuleMapRef = newMVar (RuleMap Map.empty)

-- | Child 'Process's are tracked in a list of MVar's,
-- each of which is left empty until the process has finished.
-- This allows the main process to wait for every subprocess to
-- finish before exiting.
type Children = MVar [MVar ()]

-- | Create a new empty collection of Children.
emptyChildren :: IO Children
emptyChildren = newMVar []

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

-- | Run a 'Process a' computation in IO.
run :: Process a -> IO a
run p = do
  ruleMapRef <- newRuleMapRef
  children   <- emptyChildren
  let replyCtx = Map.empty
  a <- runWith ruleMapRef children replyCtx p
  waitForChildren children
  return a

-- | Run a 'Process a' computation in IO under the calling context of a
-- 'RuleMapRef' (mapping ChanId's to responsible Rules)
-- and a 'ReplyCtx' (mapping replied to ChanId's to the locations waiting for a response.)
runWith :: RuleMapRef -> Children -> ReplyCtx -> Process a -> IO a
runWith ruleMapRef children replyCtx p = do
  instr <- viewT p
  case instr of

    Return a -> return a

    Def definition
      :>>= k -> do registerDefinition (toDefinitions definition) ruleMapRef
                   runWith ruleMapRef children replyCtx (k ())

    NewChannel
      :>>= k -> do cId <- newChanId
                   runWith ruleMapRef children replyCtx (k $ inferSync cId)

    Send c m
      :>>= k -> do registerMessage c m children ruleMapRef
                   runWith ruleMapRef children replyCtx (k ())

    Spawn p
      :>>= k -> do forkChild children $ runWith ruleMapRef children replyCtx p
                   runWith ruleMapRef children replyCtx (k ())

    Sync sc sm
      :>>= k -> do syncVal <- registerSyncMessage sc sm children ruleMapRef
                   runWith ruleMapRef children replyCtx (k syncVal)

    Reply sc m
      :>>= k -> do putMVar (lookupReplyChan replyCtx (getId sc)) m
                   runWith ruleMapRef children replyCtx (k ())

    With p q 
      :>>= k -> do mapM_ (forkChild children . runWith ruleMapRef children replyCtx) [p,q]
                   runWith ruleMapRef children replyCtx (k ())

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
    Just (p,replyCtx) -> do forkChild children $ runWith ruleMapRef children replyCtx p
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
    Just (p,replyCtx) -> do forkChild children $ runWith ruleMapRef children replyCtx p
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

