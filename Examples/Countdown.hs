{-# LANGUAGE ScopedTypeVariables, TypeOperators, FlexibleContexts #-}
module Main where

import Join
import Join.Language.Distributed
import Join.Interpreter.Distributed
import DHT.Contact
import DSL.Program
import DSL.Instruction

import Control.Concurrent

countDown :: ProcessIn (CoreInst :+: DistInst) ()
countDown = do
  -- Get a new Channel, inferred to be of type 'Chan Int'.
  intChannel <- newChannel

  -- Make a join definition:
  --  When there's an int on intChannel:
  --    If 0, do nothing.
  --    Otherwise, print and send the de-incremented int.
  def $ intChannel&=0 |> inert
     |$ intChannel    |> \(i::Int) -> do ioAction $ putStrLn $ "Count " ++ show i
                                         send intChannel (i-1)

  -- Send the starting number on intChannel and initiate the countdown.
  send intChannel 10
  b <- registerChannel "countdown" intChannel
  if b
    then ioAction $ putStrLn "Registered countdown"
    else ioAction $ putStrLn "Failed to register countdown"

  spawn $ ioAction $ threadDelay 10000000

main :: IO ()
main = do
 let joinAddr         = Addr "127.0.0.1" 7771
     ourDHTAddr       = Addr "127.0.0.1" 6661
     bootstrapDHTAddr = Addr "127.0.0.1" 6660
     hashSize         = 16
 run joinAddr ourDHTAddr (Just bootstrapDHTAddr) Nothing hashSize countDown
 putStrLn "COUNTDOWN DEAD"
