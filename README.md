#Basic Join-Language Interpreter
This module exports a basic interpreter for
[Join-Language](../Join-Language/)
which is an attempt at encoding the join calculus within the Haskell programming
language as an embedded DSL.

##Usage

1. Write a join program using [Join-Language](../Join-Language/)
2. Call ‘run’ (from Join.Interpreter.Basic) on the top-level process
   to execute it as an IO action.

##Implementation details
The interpreter is called ‘basic’ because it is a fairly quick and dirty implementation
, not fully optimised and not implementing some possible features.

The primary optimisation is that definitions are compiled to bit-patterns
making testing a single ‘pattern |> trigger’ a cheap bitwise operation against a status bit-pattern.

Regarding execution, Instructions are executed concurrently with respect to instructions
related to separate definition blocks. ‘spawn’ and ‘with’ instructions use ‘forkIO’ and so
use lightweight Haskell threads as opposed to OS threads.

Not all invalid programs are caught at compile-time by Join-Language and have undefined behavior.
This interpreter behaves in the following manner:

| Erroneous action                        | Result                                                                                   |
| --------------------------------------- | ---------------------------------------------------------------------------------------- |
| Sending >1 reply                        | Silently dropped                                                                         |
| Sending an unexpected reply             | Runtime error                                                                            |
| Sync without reply                      | Possible runtime error “Blocked on MVar”                                                 |
| Overlapping definition block            | Actions on overlapping patterns are considered on the later definition, in isolation     |
| Channel appears >1 in single definition | Will trigger as if only 1 occurrence, probably resulting in “no such message” exceptions |

