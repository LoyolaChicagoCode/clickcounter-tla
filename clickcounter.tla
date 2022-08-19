---- MODULE clickcounter ----
EXTENDS TLC, Integers
CONSTANTS CounterMin, CounterMax, N
ASSUME CounterMin < CounterMax

(* --algorithm bounded_clickcounter

variables action = "none"

process user = "user"
begin U:
  while TRUE do
    either 
      action := "inc"
    or 
      action := "dec"
    or 
      action := "reset"
    or 
      action := "none"
    end either
  end while
end process
  
process counter = "counter"
variables value = CounterMin
begin C:
  while TRUE do
    either
      await action = "inc"
    ; if value < CounterMax then value := value + 1 end if
    or
      await action = "dec"
    ; if value > CounterMin then value := value - 1 end if
    or
      await action = "reset"
    ; value := CounterMin
    end either
  ; assert CounterMin <= value /\ value <= CounterMax
  end while
end process

end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "d597c43f" /\ chksum(tla) = "12f9a1a4")
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
                 /\ IF value < CounterMax
                       THEN /\ value' = value + 1
                       ELSE /\ TRUE
                            /\ value' = value
              \/ /\ action = "dec"
                 /\ IF value > CounterMin
                       THEN /\ value' = value - 1
                       ELSE /\ TRUE
                            /\ value' = value
              \/ /\ action = "reset"
                 /\ value' = CounterMin
           /\ Assert(CounterMin <= value' /\ value' <= CounterMax, 
                     "Failure of assertion at line 39, column 5.")
           /\ UNCHANGED action

Next == user \/ counter

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
