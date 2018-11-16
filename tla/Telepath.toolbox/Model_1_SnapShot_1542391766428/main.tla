-------------------------------- MODULE main --------------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS Clients, Server, NULL, MaxMessageLength

Chars == 1..3

(*--algorithm telepath
variables
  all_msgs = [c \in Clients |-> <<>>];

process client \in Clients
variables local_msgs = [c \in Clients |-> <<>>];
begin
  Client:
  either
  Type:
    if Len(all_msgs[self]) <= MaxMessageLength + 1 then
        with c \in Chars do
            print(<< "char: ", c >>);
            print(<< "before update: ", all_msgs[self] >>);
            all_msgs[self] := all_msgs[self] \o << c >>;
            print(<< "after_update: ", all_msgs[self] >>);
        end with;
    end if; 
  or
  Delete:
    skip;
  or
  Get:
    local_msgs := all_msgs;
    assert local_msgs = all_msgs;
  end either;
end process;

process server \in {Server}
variables all = [c \in Clients |-> <<>>];
begin
  Serve:
    skip;
end process;
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES all_msgs, pc, local_msgs, all

vars == << all_msgs, pc, local_msgs, all >>

ProcSet == (Clients) \cup ({Server})

Init == (* Global variables *)
        /\ all_msgs = [c \in Clients |-> <<>>]
        (* Process client *)
        /\ local_msgs = [self \in Clients |-> [c \in Clients |-> <<>>]]
        (* Process server *)
        /\ all = [self \in {Server} |-> [c \in Clients |-> <<>>]]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "Client"
                                        [] self \in {Server} -> "Serve"]

Client(self) == /\ pc[self] = "Client"
                /\ \/ /\ pc' = [pc EXCEPT ![self] = "Type"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "Delete"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "Get"]
                /\ UNCHANGED << all_msgs, local_msgs, all >>

Type(self) == /\ pc[self] = "Type"
              /\ IF Len(all_msgs[self]) <= MaxMessageLength + 1
                    THEN /\ \E c \in Chars:
                              /\ PrintT((<< "char: ", c >>))
                              /\ PrintT((<< "before update: ", all_msgs[self] >>))
                              /\ all_msgs' = [all_msgs EXCEPT ![self] = all_msgs[self] \o << c >>]
                              /\ PrintT((<< "after_update: ", all_msgs'[self] >>))
                    ELSE /\ TRUE
                         /\ UNCHANGED all_msgs
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << local_msgs, all >>

Delete(self) == /\ pc[self] = "Delete"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << all_msgs, local_msgs, all >>

Get(self) == /\ pc[self] = "Get"
             /\ local_msgs' = [local_msgs EXCEPT ![self] = all_msgs]
             /\ Assert(local_msgs'[self] = all_msgs, 
                       "Failure of assertion at line 32, column 5.")
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << all_msgs, all >>

client(self) == Client(self) \/ Type(self) \/ Delete(self) \/ Get(self)

Serve(self) == /\ pc[self] = "Serve"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << all_msgs, local_msgs, all >>

server(self) == Serve(self)

Next == (\E self \in Clients: client(self))
           \/ (\E self \in {Server}: server(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TypeInvariant ==
  /\ \A c \in Clients: Len(all_msgs[c]) <= MaxMessageLength

=============================================================================
\* Modification History
\* Last modified Fri Nov 16 13:09:15 EST 2018 by dsherry
\* Last modified Thu Nov 15 13:53:42 EST 2018 by john
\* Created Thu Nov 15 11:56:05 EST 2018 by john
