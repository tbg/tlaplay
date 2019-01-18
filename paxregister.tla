---------------------------- MODULE paxregister ----------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS
    Acceptors,
    Proposers,
    Proposed,
    Accepted,
    Values,
    None

(*--algorithm paxregister

variable
    proposer_msgs = {}, \* produced by proposers
    acceptor_msgs = {}, \* produced by acceptors

procedure SendProposerMsg(type, number, value) begin
Send:
    proposer_msgs := proposer_msgs \cup [ type |-> type, number |-> number, value |-> value ]
end procedure

process proposer \in Proposers
variables
    prop = 1,
    current_value = None
begin  d
Run:
while Cardinality(Values) /= 0 do
    either
        await current_value = None; \* only start new after finishing old
        current_value := CHOOSE v \in Values: TRUE; \* allow others to chose same value
    or
        await current_value /= None;
        prop := SendProposerMsg(<<"promise", prop, None>>); \* phase 1
    or
        skip \* prop := HandlePromiseResponse(self)
    end either;
end while;
Accept:
    skip;
end process;


process acceptor \in Acceptors
variables
    promised = 0,
    accepted = 0,
    value
begin
HandlePropose:
while TRUE do
    skip;
end while;
end process;



end algorithm; *)
\* BEGIN TRANSLATION
\* Process variable value of process acceptor at line 49 col 5 changed to value_
CONSTANT defaultInitValue
VARIABLES proposer_msgs, acceptor_msgs, pc, stack, type, number, value, prop, 
          current_value, promised, accepted, value_

vars == << proposer_msgs, acceptor_msgs, pc, stack, type, number, value, prop, 
           current_value, promised, accepted, value_ >>

ProcSet == (Proposers) \cup (Acceptors)

Init == (* Global variables *)
        /\ proposer_msgs = {}
        /\ acceptor_msgs = {}
        (* Procedure SendProposerMsg *)
        /\ type = [ self \in ProcSet |-> defaultInitValue]
        /\ number = [ self \in ProcSet |-> defaultInitValue]
        /\ value = [ self \in ProcSet |-> defaultInitValue]
        (* Process proposer *)
        /\ prop = [self \in Proposers |-> 1]
        /\ current_value = [self \in Proposers |-> None]
        (* Process acceptor *)
        /\ promised = [self \in Acceptors |-> 0]
        /\ accepted = [self \in Acceptors |-> 0]
        /\ value_ = [self \in Acceptors |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Proposers -> "Run"
                                        [] self \in Acceptors -> "HandlePropose"]

Send(self) == /\ pc[self] = "Send"
              /\ proposer_msgs' = (proposer_msgs \cup [ type |-> type[self], number |-> number[self], value |-> value[self] ])
              /\ pc' = [pc EXCEPT ![self] = "Error"]
              /\ UNCHANGED << acceptor_msgs, stack, type, number, value, prop, 
                              current_value, promised, accepted, value_ >>

SendProposerMsg(self) == Send(self)

Run(self) == /\ pc[self] = "Run"
             /\ IF Cardinality(Values) /= 0
                   THEN /\ \/ /\ current_value[self] = None
                              /\ current_value' = [current_value EXCEPT ![self] = CHOOSE v \in Values: TRUE]
                              /\ prop' = prop
                           \/ /\ current_value[self] /= None
                              /\ prop' = [prop EXCEPT ![self] = SendProposerMsg(<<"promise", prop[self], None>>)]
                              /\ UNCHANGED current_value
                           \/ /\ TRUE
                              /\ UNCHANGED <<prop, current_value>>
                        /\ pc' = [pc EXCEPT ![self] = "Run"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Accept"]
                        /\ UNCHANGED << prop, current_value >>
             /\ UNCHANGED << proposer_msgs, acceptor_msgs, stack, type, number, 
                             value, promised, accepted, value_ >>

Accept(self) == /\ pc[self] = "Accept"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << proposer_msgs, acceptor_msgs, stack, type, 
                                number, value, prop, current_value, promised, 
                                accepted, value_ >>

proposer(self) == Run(self) \/ Accept(self)

HandlePropose(self) == /\ pc[self] = "HandlePropose"
                       /\ TRUE
                       /\ pc' = [pc EXCEPT ![self] = "HandlePropose"]
                       /\ UNCHANGED << proposer_msgs, acceptor_msgs, stack, 
                                       type, number, value, prop, 
                                       current_value, promised, accepted, 
                                       value_ >>

acceptor(self) == HandlePropose(self)

Next == (\E self \in ProcSet: SendProposerMsg(self))
           \/ (\E self \in Proposers: proposer(self))
           \/ (\E self \in Acceptors: acceptor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Jan 18 12:19:35 CET 2019 by tschottdorf
\* Created Thu Jan 17 22:09:15 CET 2019 by tschottdorf
