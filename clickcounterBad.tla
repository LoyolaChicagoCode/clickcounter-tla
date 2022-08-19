---- MODULE clickcounterBad ----
EXTENDS TLC, Integers
CONSTANTS CounterMin, CounterMax, N
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
    either
      await action = INC; value := value + 1
    or
      await action = DEC; value := value - 1
    or
      await action = RESET; value := CounterMin
    end either
    assert CounterMin <= value /\ value <= CounterMax
  end while
end process

end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "bdf17c92" /\ chksum(tla) = "a6b0023")
VARIABLES action, value

vars == << action, value >>

ProcSet == {"user"} \cup {"counter"}

Init == (* Global variables *)
        /\ action = "none"
        (* Process counter *)
        /\ value = CounterMin

user == /\ \/ /\ action' = "inc"
           \/ /\ action' = "dec"
           \/ /\ action' = "reset"
           \/ /\ action' = "none"
        /\ value' = value

counter == /\ \/ /\ action = "inc"
                 /\ value' = value + 1
              \/ /\ action = "dec"
                 /\ value' = value - 1
              \/ /\ action = "reset"
                 /\ value' = CounterMin
           /\ Assert(CounterMin <= value' /\ value' <= CounterMax, 
                     "Failure of assertion at line 36, column 5.")
           /\ UNCHANGED action

Next == user \/ counter

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
