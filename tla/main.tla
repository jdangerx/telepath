-------------------------------- MODULE main --------------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Users, Server, MaxMessageLength, Chars, NULL

(*--algorithm telepath
variables 
  to_server = [u \in Users |-> NULL], \* map from client names to current message
  from_server = [u \in Users |-> NULL]; \* map from client name to state updates from server (map of maps)

define
UsersPendingWrite == {u \in Users: to_server[u] /= NULL}
UsersPendingRead == {u \in Users: from_server[u] /= NULL}
Update(func, key, new) ==
  IF func[key] = NULL
  THEN new
  ELSE func[key] @@ new
end define;

fair process user \in Users
variables
  typed = "", 
  local_state = [u \in Users |-> ""];
begin
  User:
  either \* type
    await Len(typed) < MaxMessageLength;
    with c \in Chars do
      typed := typed \o c;
      \* could optimistically update here on frontend
      to_server[self] := typed;
    end with; 
  or \* delete
    await Len(typed) > 0;
    typed := SubSeq(typed, 2, Len(typed));
    to_server[self] := typed;
  or \* receive
    await from_server[self] /= NULL;
    local_state := local_state @@ from_server[self];
    from_server[self] := NULL;
  end either;
  goto User;
end process;

fair process server \in {Server}
begin
Serve:
  await Cardinality(UsersPendingWrite) > 0;
  from_server := [dest \in Users |-> Update(from_server, dest, to_server)];
goto Serve;
end process;

end algorithm *)
\* BEGIN TRANSLATION
VARIABLES to_server, from_server, pc

(* define statement *)
UsersPendingWrite == {u \in Users: to_server[u] /= NULL}
UsersPendingRead == {u \in Users: from_server[u] /= NULL}
Update(func, key, new) ==
  IF func[key] = NULL
  THEN new
  ELSE func[key] @@ new

VARIABLES typed, local_state

vars == << to_server, from_server, pc, typed, local_state >>

ProcSet == (Users) \cup ({Server})

Init == (* Global variables *)
        /\ to_server = [u \in Users |-> NULL]
        /\ from_server = [u \in Users |-> NULL]
        (* Process user *)
        /\ typed = [self \in Users |-> ""]
        /\ local_state = [self \in Users |-> [u \in Users |-> ""]]
        /\ pc = [self \in ProcSet |-> CASE self \in Users -> "User"
                                        [] self \in {Server} -> "Serve"]

User(self) == /\ pc[self] = "User"
              /\ \/ /\ Len(typed[self]) < MaxMessageLength
                    /\ \E c \in Chars:
                         /\ typed' = [typed EXCEPT ![self] = typed[self] \o c]
                         /\ to_server' = [to_server EXCEPT ![self] = typed'[self]]
                    /\ UNCHANGED <<from_server, local_state>>
                 \/ /\ Len(typed[self]) > 0
                    /\ typed' = [typed EXCEPT ![self] = SubSeq(typed[self], 2, Len(typed[self]))]
                    /\ to_server' = [to_server EXCEPT ![self] = typed'[self]]
                    /\ UNCHANGED <<from_server, local_state>>
                 \/ /\ from_server[self] /= NULL
                    /\ local_state' = [local_state EXCEPT ![self] = local_state[self] @@ from_server[self]]
                    /\ from_server' = [from_server EXCEPT ![self] = NULL]
                    /\ UNCHANGED <<to_server, typed>>
              /\ pc' = [pc EXCEPT ![self] = "User"]

user(self) == User(self)

Serve(self) == /\ pc[self] = "Serve"
               /\ Cardinality(UsersPendingWrite) > 0
               /\ from_server' = [dest \in Users |-> Update(from_server, dest, to_server)]
               /\ pc' = [pc EXCEPT ![self] = "Serve"]
               /\ UNCHANGED << to_server, typed, local_state >>

server(self) == Serve(self)

Next == (\E self \in Users: user(self))
           \/ (\E self \in {Server}: server(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Users : WF_vars(user(self))
        /\ \A self \in {Server} : WF_vars(server(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

ConsistencyWhenDone ==
  (UsersPendingRead = {} /\ UsersPendingWrite = {})
    => \A u1, u2 \in Users: typed[u1] = local_state[u2][u1]

=============================================================================
\* Modification History
\* Last modified Mon Nov 26 17:02:18 EST 2018 by john
\* Last modified Fri Nov 16 14:18:13 EST 2018 by dsherry
\* Created Thu Nov 15 11:56:05 EST 2018 by john
