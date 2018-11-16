-------------------------------- MODULE main --------------------------------
EXTENDS TLC, Integers, Sequences

(*--algorithm telepath

begin
  skip;
end algorithm *)
\* BEGIN TRANSLATION
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Nov 15 11:57:26 EST 2018 by john
\* Created Thu Nov 15 11:56:05 EST 2018 by john
