-------------------------------- MODULE main --------------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS Clients, Server, NULL

Chars == 1..3

(*--algorithm telepath
variables
  server = [c \in Clients |-> <<>>],
  queue = <<>>;

process client \in Clients
variables own = <<>>, all = [c \in Clients |-> <<>>];
begin
  Client:
  either
  Type:
    with c \in Chars do
      own := own \o c;
    end with 
  or
  Send:
    queue := queue \o [client |-> self, msg |-> own];
  or
  Get:
    skip;
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
\* Process server at line 31 col 1 changed to server_
\* Process variable all of process client at line 14 col 23 changed to all_
VARIABLES server, queue, pc, own, all_, all

vars == << server, queue, pc, own, all_, all >>

ProcSet == (Clients) \cup ({Server})

Init == (* Global variables *)
        /\ server = [c \in Clients |-> <<>>]
        /\ queue = <<>>
        (* Process client *)
        /\ own = [self \in Clients |-> <<>>]
        /\ all_ = [self \in Clients |-> [c \in Clients |-> <<>>]]
        (* Process server_ *)
        /\ all = [self \in {Server} |-> [c \in Clients |-> <<>>]]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "Client"
                                        [] self \in {Server} -> "Serve"]

Client(self) == /\ pc[self] = "Client"
                /\ \/ /\ pc' = [pc EXCEPT ![self] = "Type"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "Send"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "Get"]
                /\ UNCHANGED << server, queue, own, all_, all >>

Type(self) == /\ pc[self] = "Type"
              /\ \E c \in Chars:
                   own' = [own EXCEPT ![self] = own[self] \o c]
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << server, queue, all_, all >>

Send(self) == /\ pc[self] = "Send"
              /\ queue' = queue \o [client |-> self, msg |-> own[self]]
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << server, own, all_, all >>

Get(self) == /\ pc[self] = "Get"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << server, queue, own, all_, all >>

client(self) == Client(self) \/ Type(self) \/ Send(self) \/ Get(self)

Serve(self) == /\ pc[self] = "Serve"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << server, queue, own, all_, all >>

server_(self) == Serve(self)

Next == (\E self \in Clients: client(self))
           \/ (\E self \in {Server}: server_(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Nov 15 13:53:42 EST 2018 by john
\* Created Thu Nov 15 11:56:05 EST 2018 by john
