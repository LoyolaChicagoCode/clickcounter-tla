---- MODULE clickcounter ----
EXTENDS TLC, Integers, Sequences
CONSTANTS CounterMin, CounterMax
ASSUME CounterMin < CounterMax

(* --algorithm bounded_clickcounter

variables value = CounterMin, n = 10

define
  Bounded == CounterMin <= value /\ value <= CounterMax
end define

macro Inc() begin
  if value < CounterMax then value := value + 1 end if
end macro

macro Dec() begin
  if value > CounterMin then value := value - 1 end if
end macro

macro Reset() begin
  value := CounterMin
end macro

begin
  while TRUE do
    n := n - 1
  ; either 
      Inc()
    or 
      Dec()
    or 
      Reset()
    end either
  end while
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "fe58f7de" /\ chksum(tla) = "645407fa")
VARIABLES value, n

(* define statement *)
Bounded == CounterMin <= value /\ value <= CounterMax


vars == << value, n >>

Init == (* Global variables *)
        /\ value = CounterMin
        /\ n = 10

Next == /\ n' = n - 1
        /\ \/ /\ IF value < CounterMax
                    THEN /\ value' = value + 1
                    ELSE /\ TRUE
                         /\ value' = value
           \/ /\ IF value > CounterMin
                    THEN /\ value' = value - 1
                    ELSE /\ TRUE
                         /\ value' = value
           \/ /\ value' = CounterMin

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

====
