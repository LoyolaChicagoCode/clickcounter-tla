---- MODULE clickcounter ----
EXTENDS TLC, Integers
CONSTANTS CounterMin, CounterMax
ASSUME CounterMin < CounterMax

INC == "inc"
DEC == "dec"
RESET == "reset"
NONE == "none"

(* --algorithm bounded_clickcounter

variables action = NONE

process user = "user"
begin U:
  while TRUE do
    either 
      I: action := INC
    or 
      D: action := DEC
    or 
      R: action := RESET
    or 
      N: action := NONE
    end either
  ; print action
  end while
end process
  
process counter = "counter"
variables value = CounterMin
begin C:
  while TRUE do
    assert CounterMin <= value /\ value <= CounterMax
  ; A: either
      await action = INC
    ; if value < CounterMax then value := value + 1 end if
    or
      await action = DEC
    ; if value > CounterMin then value := value - 1 end if
    or
      await action = RESET
    ; value := CounterMin
    end either
  ; print value
  end while
end process

end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "1dad8e5b" /\ chksum(tla) = "27ff4caa")
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
        /\ PrintT(action')
        /\ value' = value

counter == /\ Assert(CounterMin <= value /\ value <= CounterMax, 
                     "Failure of assertion at line 35, column 5.")
           /\ \/ /\ action = INC
                 /\ IF value < CounterMax
                       THEN /\ value' = value + 1
                       ELSE /\ TRUE
                            /\ value' = value
              \/ /\ action = DEC
                 /\ IF value > CounterMin
                       THEN /\ value' = value - 1
                       ELSE /\ TRUE
                            /\ value' = value
              \/ /\ action = RESET
                 /\ value' = CounterMin
           /\ PrintT(value')
           /\ UNCHANGED action

Next == user \/ counter

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
