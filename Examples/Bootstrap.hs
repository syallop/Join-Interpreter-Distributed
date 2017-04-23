{-# LANGUAGE ScopedTypeVariables, TypeOperators, FlexibleContexts #-}
module Main where

import Join
import Join.Language.Distributed
import Join.Interpreter.Distributed

import DHT.Contact
import DSL.Program
import DSL.Instruction

import DHT.NS.Logging

import Control.Concurrent

-- Do nothing but wait, running a DHT in the background
bootstrap :: ProcessIn (CoreInst :+: DistInst) ()
bootstrap = spawn $ do ioAction $ threadDelay 10000000000
                       ioAction $ putStrLn "BOOTSTRAP DEAD"

main :: IO ()
main = do
 logger <- newDHTNSLogging
 let joinAddr         = Addr "127.0.0.1" 7770
     ourDHTAddr       = Addr "127.0.0.1" 6660
     hashSize         = 16
 run joinAddr ourDHTAddr Nothing logger hashSize bootstrap
 threadDelay 10000000000
