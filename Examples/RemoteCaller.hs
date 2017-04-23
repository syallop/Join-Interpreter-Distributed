{-# LANGUAGE ScopedTypeVariables, TypeOperators, FlexibleContexts, RankNTypes #-}
module Main where

import Join
import Join.Language.Distributed
import Join.Interpreter.Distributed
import DHT.Contact
import DSL.Program
import DSL.Instruction

import Control.Concurrent hiding (Chan)

import DHT.NS.Logging

callRemoteCountdown :: Int -> ProcessIn (CoreInst :+: DistInst) ()
callRemoteCountdown i = do
    mChannel :: Maybe (Chan Int) <- lookupChannel "countdown"
    case mChannel of
      Nothing
        -> ioAction $ putStrLn "Failed to acquire channel named 'countdown'."

      Just countdownChannel
        -> do ioAction $ putStrLn "Got channel named 'countdown'."
              send countdownChannel i

    -- Delay
    spawn $ ioAction $ threadDelay 1000000000

main :: IO ()
main = do
 let joinAddr         = Addr "127.0.0.1" 7772
     ourDHTAddr       = Addr "127.0.0.1" 6662
     bootstrapDHTAddr = Addr "127.0.0.1" 6660
     hashSize         = 16
 logger <- newDHTNSLogging
 run joinAddr ourDHTAddr (Just bootstrapDHTAddr) logger hashSize (callRemoteCountdown 10)
 putStrLn "REMOTECALLER DEAD"
