---- MODULE clickcounter ----
EXTENDS TLC, Integers
CONSTANTS CounterMin, CounterMax, N
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
      await action = INC
    ; if value < CounterMax then value := value + 1 end if
    or
      await action = DEC
    ; if value > CounterMin then value := value - 1 end if
    or
      await action = RESET
    ; value := CounterMin
    end either
  ; assert CounterMin <= value /\ value <= CounterMax
  end while
end process

end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "d80ce1ef" /\ chksum(tla) = "aeb12eec")
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

counter == /\ \/ /\ action = INC
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
           /\ Assert(CounterMin <= value' /\ value' <= CounterMax, 
                     "Failure of assertion at line 44, column 5.")
           /\ UNCHANGED action

Next == user \/ counter

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
