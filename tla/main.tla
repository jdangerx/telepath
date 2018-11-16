-------------------------------- MODULE main --------------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS Clients, Server, NULL, MaxMessageLength

Chars == 1..3

(*--algorithm telepath
variables
  all_msgs = [c \in Clients |-> <<>>],
  \* what's in the pipes?
  in_flight_msgs = [c \in Clients |-> <<>>];

fair process client \in Clients
variables local_msgs = [c \in Clients |-> <<>>];
begin
  Client:
  while TRUE do
  either
  Type:
    if Len(all_msgs[self]) < MaxMessageLength then
        with c \in Chars do
            all_msgs[self] := all_msgs[self] \o << c >>;
            \* add [source |-> self, msg |-> own_msg] to in_flight[self]
        end with;
    end if; 
  or
  Delete:
    skip;
  end either;
  Get:
    \* await push from server, then: 
    local_msgs := all_msgs;
    assert local_msgs = all_msgs;
  end while;
end process;

\* server does stuff - receives messages from client, updates connections
fair process server \in {Server}
variables server_msgs = [c \in Clients |-> <<>>];
begin
  Serve:
  
end process;

end algorithm *)
\* BEGIN TRANSLATION
VARIABLES all_msgs, pc, local_msgs

vars == << all_msgs, pc, local_msgs >>

ProcSet == (Clients)

Init == (* Global variables *)
        /\ all_msgs = [c \in Clients |-> <<>>]
        (* Process client *)
        /\ local_msgs = [self \in Clients |-> [c \in Clients |-> <<>>]]
        /\ pc = [self \in ProcSet |-> "Client"]

Client(self) == /\ pc[self] = "Client"
                /\ \/ /\ pc' = [pc EXCEPT ![self] = "Type"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "Delete"]
                /\ UNCHANGED << all_msgs, local_msgs >>

Get(self) == /\ pc[self] = "Get"
             /\ local_msgs' = [local_msgs EXCEPT ![self] = all_msgs]
             /\ Assert(local_msgs'[self] = all_msgs, 
                       "Failure of assertion at line 32, column 5.")
             /\ pc' = [pc EXCEPT ![self] = "Client"]
             /\ UNCHANGED all_msgs

Type(self) == /\ pc[self] = "Type"
              /\ IF Len(all_msgs[self]) < MaxMessageLength
                    THEN /\ \E c \in Chars:
                              all_msgs' = [all_msgs EXCEPT ![self] = all_msgs[self] \o << c >>]
                    ELSE /\ TRUE
                         /\ UNCHANGED all_msgs
              /\ pc' = [pc EXCEPT ![self] = "Get"]
              /\ UNCHANGED local_msgs

Delete(self) == /\ pc[self] = "Delete"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "Get"]
                /\ UNCHANGED << all_msgs, local_msgs >>

client(self) == Client(self) \/ Get(self) \/ Type(self) \/ Delete(self)

Next == (\E self \in Clients: client(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(client(self))

\* END TRANSLATION

TypeInvariant ==
  /\ \A c \in Clients: Len(all_msgs[c]) <= MaxMessageLength
  
  
EventualConsistency ==
  /\ \A c \in Clients: <>[](all_msgs = local_msgs[c]) 

=============================================================================
\* Modification History
\* Last modified Fri Nov 16 14:18:13 EST 2018 by dsherry
\* Last modified Thu Nov 15 13:53:42 EST 2018 by john
\* Created Thu Nov 15 11:56:05 EST 2018 by john
