---- MODULE clickcounterBad ----
EXTENDS TLC, Integers, Sequences
CONSTANTS CounterMin, CounterMax
ASSUME CounterMin < CounterMax

(* --algorithm unbounded_clickcounter

variables value = CounterMin

define
  Bounded == CounterMin <= value /\ value <= CounterMax
end define

macro Inc() begin
  value := value + 1
end macro

macro Dec() begin
  value := value - 1
end macro

macro Reset() begin
  value := CounterMin
end macro

begin
  while TRUE do
    either 
      Inc()
    or 
      Dec()
    or 
      Reset()
    end either
  end while
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "5363801e" /\ chksum(tla) = "986553d0")
VARIABLE value

(* define statement *)
Bounded == CounterMin <= value /\ value <= CounterMax


vars == << value >>

Init == (* Global variables *)
        /\ value = CounterMin

Next == \/ /\ value' = value + 1
        \/ /\ value' = value - 1
        \/ /\ value' = CounterMin

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

====
