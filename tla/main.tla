-------------------------------- MODULE main --------------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Clients, Server, NULL, MaxMessageLength, MaxQueueLength, Chars

(*--algorithm telepath
\* Sequences in to_server and from_server are sequences of updates sent 
\* between client and server; sequences in ghost_all_messages are the literal
\* messages the clients have typed 
variables
  to_server = [c \in Clients |-> <<>>],
  from_server = [c \in Clients |-> <<>>],
  ghost_all_msgs = [c \in Clients |-> <<>>];

define
  ClientsWithChanges == {c \in Clients: to_server[c] /= <<>>}
  AppendQueue(queue, elt) ==
    IF Len(queue) < MaxQueueLength
    THEN Append(queue, elt)
    ELSE Append(SubSeq(queue, Len(queue) - MaxQueueLength  + 2, Len(queue)), elt)
end define;

macro send_message()
begin
  local_msgs[self] := own_msg;
  ghost_all_msgs[self] := own_msg;
  to_server[self] := AppendQueue(to_server[self], [source |-> self, msg |-> own_msg]);
end macro;

\* assume client does not crash
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
            send_message();
        end with;
    end if; 
  or
  Delete:
    if Len(own_msg) = 1 then
      own_msg := <<>>;
      send_message();      
    elsif Len(own_msg) > 0 then
      own_msg := SubSeq(own_msg, 1, Len(own_msg) - 1);
      send_message();     
    end if;  
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


\* assume server does not crash
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
            dest_client \in Clients |-> AppendQueue(from_server[dest_client], Head(to_server[source_client]))
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
VARIABLES to_server, from_server, ghost_all_msgs, pc

(* define statement *)
ClientsWithChanges == {c \in Clients: to_server[c] /= <<>>}
AppendQueue(queue, elt) ==
  IF Len(queue) < MaxQueueLength
  THEN Append(queue, elt)
  ELSE Append(SubSeq(queue, Len(queue) - MaxQueueLength  + 2, Len(queue)), elt)

VARIABLES local_msgs, own_msg, server_msgs

vars == << to_server, from_server, ghost_all_msgs, pc, local_msgs, own_msg, 
           server_msgs >>

ProcSet == (Clients) \cup ({Server})

Init == (* Global variables *)
        /\ to_server = [c \in Clients |-> <<>>]
        /\ from_server = [c \in Clients |-> <<>>]
        /\ ghost_all_msgs = [c \in Clients |-> <<>>]
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
                /\ UNCHANGED << to_server, from_server, ghost_all_msgs, 
                                local_msgs, own_msg, server_msgs >>

Get(self) == /\ pc[self] = "Get"
             /\ IF from_server[self] /= <<>>
                   THEN /\ LET update == Head(from_server[self]) IN
                             local_msgs' = [local_msgs EXCEPT ![self][update.source] = update.msg]
                        /\ from_server' = [from_server EXCEPT ![self] = Tail(from_server[self])]
                   ELSE /\ TRUE
                        /\ UNCHANGED << from_server, local_msgs >>
             /\ pc' = [pc EXCEPT ![self] = "Client"]
             /\ UNCHANGED << to_server, ghost_all_msgs, own_msg, server_msgs >>

Type(self) == /\ pc[self] = "Type"
              /\ IF Len(own_msg[self]) < MaxMessageLength
                    THEN /\ \E c \in Chars:
                              /\ own_msg' = [own_msg EXCEPT ![self] = Append(own_msg[self], c)]
                              /\ local_msgs' = [local_msgs EXCEPT ![self][self] = own_msg'[self]]
                              /\ ghost_all_msgs' = [ghost_all_msgs EXCEPT ![self] = own_msg'[self]]
                              /\ to_server' = [to_server EXCEPT ![self] = AppendQueue(to_server[self], [source |-> self, msg |-> own_msg'[self]])]
                    ELSE /\ TRUE
                         /\ UNCHANGED << to_server, ghost_all_msgs, local_msgs, 
                                         own_msg >>
              /\ pc' = [pc EXCEPT ![self] = "Get"]
              /\ UNCHANGED << from_server, server_msgs >>

Delete(self) == /\ pc[self] = "Delete"
                /\ IF Len(own_msg[self]) = 1
                      THEN /\ own_msg' = [own_msg EXCEPT ![self] = <<>>]
                           /\ local_msgs' = [local_msgs EXCEPT ![self][self] = own_msg'[self]]
                           /\ ghost_all_msgs' = [ghost_all_msgs EXCEPT ![self] = own_msg'[self]]
                           /\ to_server' = [to_server EXCEPT ![self] = AppendQueue(to_server[self], [source |-> self, msg |-> own_msg'[self]])]
                      ELSE /\ IF Len(own_msg[self]) > 0
                                 THEN /\ own_msg' = [own_msg EXCEPT ![self] = SubSeq(own_msg[self], 1, Len(own_msg[self]) - 1)]
                                      /\ local_msgs' = [local_msgs EXCEPT ![self][self] = own_msg'[self]]
                                      /\ ghost_all_msgs' = [ghost_all_msgs EXCEPT ![self] = own_msg'[self]]
                                      /\ to_server' = [to_server EXCEPT ![self] = AppendQueue(to_server[self], [source |-> self, msg |-> own_msg'[self]])]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << to_server, 
                                                      ghost_all_msgs, 
                                                      local_msgs, own_msg >>
                /\ pc' = [pc EXCEPT ![self] = "Get"]
                /\ UNCHANGED << from_server, server_msgs >>

client(self) == Client(self) \/ Get(self) \/ Type(self) \/ Delete(self)

Serve(self) == /\ pc[self] = "Serve"
               /\ Cardinality(ClientsWithChanges) > 0
               /\ pc' = [pc EXCEPT ![self] = "ReadAndNotify"]
               /\ UNCHANGED << to_server, from_server, ghost_all_msgs, 
                               local_msgs, own_msg, server_msgs >>

ReadAndNotify(self) == /\ pc[self] = "ReadAndNotify"
                       /\ IF Cardinality(ClientsWithChanges) > 0
                             THEN /\ \E source_client \in ClientsWithChanges:
                                       /\ from_server' =                [
                                                           dest_client \in Clients |-> AppendQueue(from_server[dest_client], Head(to_server[source_client]))
                                                         ]
                                       /\ to_server' = [to_server EXCEPT ![source_client] = Tail(to_server[source_client])]
                                  /\ pc' = [pc EXCEPT ![self] = "ReadAndNotify"]
                             ELSE /\ TRUE
                                  /\ pc' = [pc EXCEPT ![self] = "Serve"]
                                  /\ UNCHANGED << to_server, from_server >>
                       /\ UNCHANGED << ghost_all_msgs, local_msgs, own_msg, 
                                       server_msgs >>

server(self) == Serve(self) \/ ReadAndNotify(self)

Next == (\E self \in Clients: client(self))
           \/ (\E self \in {Server}: server(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(client(self))
        /\ \A self \in {Server} : WF_vars(server(self))

\* END TRANSLATION

TypeInvariant ==
  /\ \A x, y \in Clients: Len(local_msgs[x][y]) <= MaxMessageLength
  /\ \A c \in Clients: (Len(to_server[c]) <= MaxQueueLength /\ Len(from_server[c]) <= MaxQueueLength)
  /\ \A c \in Clients: Len(own_msg[c]) <= MaxMessageLength
  
SendsArePropagated ==
  /\ \A src \in Clients: to_server[src] /= <<>> ~>
    \A dst \in Clients: from_server[dst] /= <<>>
    
EventuallyConsistent ==
  \A src \in Clients: ghost_all_msgs[src] /= <<>> ~>
    \A dst \in Clients: local_msgs[dst][src] = ghost_all_msgs[src]
    

=============================================================================
\* Modification History
\* Last modified Wed Nov 21 12:52:08 EST 2018 by john
\* Last modified Fri Nov 16 14:18:13 EST 2018 by dsherry
\* Created Thu Nov 15 11:56:05 EST 2018 by john
