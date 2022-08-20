(* 
TODO need to model event queue to avoid missed signals! 

A bit similar to Hanoi...
*)

---- MODULE clickcounterBad ----
EXTENDS TLC, Integers
CONSTANTS CounterMin, CounterMax
ASSUME CounterMin < CounterMax

INC == "inc"
DEC == "dec"
RESET == "reset"
NONE == "none"

(* --algorithm unbounded_clickcounter

variables action = NONE

process user = "user"
begin U:
  while TRUE do
    either 
      action := INC
    or 
      action := DEC
    or 
      action := RESET
    or 
      action := NONE
    end either
  end while
end process
  
process counter = "counter"
variables value = CounterMin
begin C:
  while TRUE do
    assert CounterMin <= value /\ value <= CounterMax
  ; either
      await action = INC; value := value + 1
    or
      await action = DEC; value := value - 1
    or
      await action = RESET; value := CounterMin
    end either
  end while
end process

end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "418e8b42" /\ chksum(tla) = "b0691739")
VARIABLES action, value

vars == << action, value >>

ProcSet == {"user"} \cup {"counter"}

Init == (* Global variables *)
        /\ action = NONE
        (* Process counter *)
        /\ value = CounterMin

user == /\ \/ /\ action' = INC
           \/ /\ action' = DEC
           \/ /\ action' = RESET
           \/ /\ action' = NONE
        /\ value' = value

counter == /\ Assert(CounterMin <= value /\ value <= CounterMax, 
                     "Failure of assertion at line 40, column 5.")
           /\ \/ /\ action = INC
                 /\ value' = value + 1
              \/ /\ action = DEC
                 /\ value' = value - 1
              \/ /\ action = RESET
                 /\ value' = CounterMin
           /\ UNCHANGED action

Next == user \/ counter

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
