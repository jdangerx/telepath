-------------------------------- MODULE main --------------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Clients, Server, NULL, MaxMessageLength

Chars == 1..3

(*--algorithm telepath
variables
  to_server = [c \in Clients |-> <<>>],
  from_server = [c \in Clients |-> <<>>];

define
  ClientsWithChanges == {c \in Clients: to_server[c] /= <<>>}
end define

fair process client \in Clients
variables local_msgs = [c \in Clients |-> <<>>], own_msg = <<>>;
begin
  Client:
  while TRUE do
  either
  Type:
    if Len(own_msg) < MaxMessageLength then
        with c \in Chars do
            own_msg := Append(own_msg, c);
            local_msgs[self] := own_msg;
            to_server[self] := Append(to_server[self], [source |-> self, msg |-> own_msg]);
        end with;
    end if; 
  or
  Delete:
    skip;
  end either;
  Get:
    if from_server[self] /= <<>> then
      with update = Head(from_server[self]) do
        local_msgs[update.source] := update.msg;
      end with;
      from_server[self] := Tail(from_server[self]);
    end if;
  end while;
end process;


\* server does stuff - receives messages from client, updates connections
fair process server \in {Server}
variables server_msgs = [c \in Clients |-> <<>>];
begin
  Serve:
    while TRUE do
      await Cardinality(ClientsWithChanges) > 0;
      ReadAndNotify:
      while Cardinality(ClientsWithChanges) > 0 do
        with source_client \in ClientsWithChanges do
          from_server := [
            dest_client \in Clients |-> Append(from_server[dest_client], Head(to_server[source_client]))
          ];
          to_server[source_client] := Tail(to_server[source_client]);
        end with;
      end while;
    \* while there's clients that have sent messages, grab the last one from each client (by dropping as long as there's two or more, then taking)
    \* send a push to every client
      skip;
    end while;
    
end process;

end algorithm *)
\* BEGIN TRANSLATION
VARIABLES to_server, from_server, pc

(* define statement *)
ClientsWithChanges == {c \in Clients: to_server[c] /= <<>>}

VARIABLES local_msgs, own_msg, server_msgs

vars == << to_server, from_server, pc, local_msgs, own_msg, server_msgs >>

ProcSet == (Clients) \cup ({Server})

Init == (* Global variables *)
        /\ to_server = [c \in Clients |-> <<>>]
        /\ from_server = [c \in Clients |-> <<>>]
        (* Process client *)
        /\ local_msgs = [self \in Clients |-> [c \in Clients |-> <<>>]]
        /\ own_msg = [self \in Clients |-> <<>>]
        (* Process server *)
        /\ server_msgs = [self \in {Server} |-> [c \in Clients |-> <<>>]]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "Client"
                                        [] self \in {Server} -> "Serve"]

Client(self) == /\ pc[self] = "Client"
                /\ \/ /\ pc' = [pc EXCEPT ![self] = "Type"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "Delete"]
                /\ UNCHANGED << to_server, from_server, local_msgs, own_msg, 
                                server_msgs >>

Get(self) == /\ pc[self] = "Get"
             /\ IF from_server[self] /= <<>>
                   THEN /\ LET update == Head(from_server[self]) IN
                             local_msgs' = [local_msgs EXCEPT ![self][update.source] = update.msg]
                        /\ from_server' = [from_server EXCEPT ![self] = Tail(from_server[self])]
                   ELSE /\ TRUE
                        /\ UNCHANGED << from_server, local_msgs >>
             /\ pc' = [pc EXCEPT ![self] = "Client"]
             /\ UNCHANGED << to_server, own_msg, server_msgs >>

Type(self) == /\ pc[self] = "Type"
              /\ IF Len(own_msg[self]) < MaxMessageLength
                    THEN /\ \E c \in Chars:
                              /\ own_msg' = [own_msg EXCEPT ![self] = Append(own_msg[self], c)]
                              /\ local_msgs' = [local_msgs EXCEPT ![self][self] = own_msg'[self]]
                              /\ to_server' = [to_server EXCEPT ![self] = Append(to_server[self], [source |-> self, msg |-> own_msg'[self]])]
                    ELSE /\ TRUE
                         /\ UNCHANGED << to_server, local_msgs, own_msg >>
              /\ pc' = [pc EXCEPT ![self] = "Get"]
              /\ UNCHANGED << from_server, server_msgs >>

Delete(self) == /\ pc[self] = "Delete"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "Get"]
                /\ UNCHANGED << to_server, from_server, local_msgs, own_msg, 
                                server_msgs >>

client(self) == Client(self) \/ Get(self) \/ Type(self) \/ Delete(self)

Serve(self) == /\ pc[self] = "Serve"
               /\ Cardinality(ClientsWithChanges) > 0
               /\ pc' = [pc EXCEPT ![self] = "ReadAndNotify"]
               /\ UNCHANGED << to_server, from_server, local_msgs, own_msg, 
                               server_msgs >>

ReadAndNotify(self) == /\ pc[self] = "ReadAndNotify"
                       /\ IF Cardinality(ClientsWithChanges) > 0
                             THEN /\ \E source_client \in ClientsWithChanges:
                                       /\ from_server' =                [
                                                           dest_client \in Clients |-> Append(from_server[dest_client], Head(to_server[source_client]))
                                                         ]
                                       /\ to_server' = [to_server EXCEPT ![source_client] = Tail(to_server[source_client])]
                                  /\ pc' = [pc EXCEPT ![self] = "ReadAndNotify"]
                             ELSE /\ TRUE
                                  /\ pc' = [pc EXCEPT ![self] = "Serve"]
                                  /\ UNCHANGED << to_server, from_server >>
                       /\ UNCHANGED << local_msgs, own_msg, server_msgs >>

server(self) == Serve(self) \/ ReadAndNotify(self)

Next == (\E self \in Clients: client(self))
           \/ (\E self \in {Server}: server(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(client(self))
        /\ \A self \in {Server} : WF_vars(server(self))

\* END TRANSLATION

TypeInvariant ==
  /\ \A x, y \in Clients: Len(local_msgs[x][y]) <= MaxMessageLength

=============================================================================
\* Modification History
\* Last modified Mon Nov 19 16:12:25 EST 2018 by john
\* Last modified Fri Nov 16 14:18:13 EST 2018 by dsherry
\* Created Thu Nov 15 11:56:05 EST 2018 by john
