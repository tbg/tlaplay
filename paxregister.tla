---------------------------- MODULE paxregister ----------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS
    Acceptors,
    SeedAcceptor,
    Proposers,
    MaxEpoch,
    
    Config,

    Epoch,
    Proposed,
    Accepted
    
ASSUME SeedAcceptor \in Acceptors

ASSUME MaxEpoch \in Nat
Range(f) == { f[x]: x \in DOMAIN f }

(*--algorithm paxregister

variable
    propose_requests = [ a \in Acceptors |-> <<>> ],
    propose_responses = [ a \in Proposers |-> <<>> ],
    active_proposers = Proposers;

process proposer \in Proposers
variables
   epoch = 1,
   prop,
begin Run:
while epoch <= MaxEpoch do
    StartNewWrite:
        prop := 1;
        goto SendProposeRequest;
    SendProposeRequest:
        with new_proposers \in {s \in SUBSET Proposers: Cardinality(s) > 0} do
            propose_requests[SeedAcceptor] := Append(propose_requests[SeedAcceptor], [ Proposed |-> prop, Epoch |-> epoch+1, Config |-> new_proposers ]);
        end with;
    HandleProposeResponse:
        await propose_responses[self] /= {};
        with resp \in Range(propose_responses[self]) do
            skip;
        end with;
            skip;
        skip;
end while;
end process;


process acceptor \in Acceptors
variables
    state = [
        Epoch         |-> IF self = SeedAcceptor THEN 1 ELSE 0,
        Proposed      |-> IF self = SeedAcceptor THEN 1 ELSE 0,
        Accepted      |-> IF self = SeedAcceptor THEN 1 ELSE 0,
        NextAcceptors |-> IF self = SeedAcceptor THEN {self} ELSE {}   
    ]
begin
HandlePropose:
while active_proposers /= {} do
    HandleProposeRequest:
        skip;
    HandleProposeResponse:
    await propose_requests[self] /= {};
    with req \in Range(propose_requests[self]) do
        \* TODO(tbg): remove req from the vector. Surprisingly hard.
        with 
    end with;
HandleAccept:
    skip;
end while;
end process;



end algorithm; *)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES propose_requests, propose_responses, active_proposers, pc, epoch, 
          prop, state

vars == << propose_requests, propose_responses, active_proposers, pc, epoch, 
           prop, state >>

ProcSet == (Proposers) \cup (Acceptors)

Init == (* Global variables *)
        /\ propose_requests = [ a \in Acceptors |-> <<>> ]
        /\ propose_responses = [ a \in Proposers |-> <<>> ]
        /\ active_proposers = Proposers
        (* Process proposer *)
        /\ epoch = [self \in Proposers |-> 1]
        /\ prop = [self \in Proposers |-> defaultInitValue]
        (* Process acceptor *)
        /\ state = [self \in Acceptors |->         [
                                               Epoch         |-> IF self = SeedAcceptor THEN 1 ELSE 0,
                                               Proposed      |-> IF self = SeedAcceptor THEN 1 ELSE 0,
                                               Accepted      |-> IF self = SeedAcceptor THEN 1 ELSE 0,
                                               NextAcceptors |-> IF self = SeedAcceptor THEN {self} ELSE {}
                                           ]]
        /\ pc = [self \in ProcSet |-> CASE self \in Proposers -> "Run"
                                        [] self \in Acceptors -> "HandlePropose"]

Run(self) == /\ pc[self] = "Run"
             /\ IF epoch[self] <= MaxEpoch
                   THEN /\ pc' = [pc EXCEPT ![self] = "StartNewWrite"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << propose_requests, propose_responses, 
                             active_proposers, epoch, prop, state >>

StartNewWrite(self) == /\ pc[self] = "StartNewWrite"
                       /\ prop' = [prop EXCEPT ![self] = 1]
                       /\ pc' = [pc EXCEPT ![self] = "SendProposeRequest"]
                       /\ UNCHANGED << propose_requests, propose_responses, 
                                       active_proposers, epoch, state >>

SendProposeRequest(self) == /\ pc[self] = "SendProposeRequest"
                            /\ \E new_proposers \in {s \in SUBSET Proposers: Cardinality(s) > 0}:
                                 propose_requests' = [propose_requests EXCEPT ![SeedAcceptor] = Append(propose_requests[SeedAcceptor], [ Proposed |-> prop[self], Epoch |-> epoch[self]+1, Config |-> new_proposers ])]
                            /\ pc' = [pc EXCEPT ![self] = "HandleProposeResponse"]
                            /\ UNCHANGED << propose_responses, 
                                            active_proposers, epoch, prop, 
                                            state >>

HandleProposeResponse(self) == /\ pc[self] = "HandleProposeResponse"
                               /\ propose_responses[self] /= {}
                               /\ \E resp \in Range(propose_responses[self]):
                                    TRUE
                               /\ TRUE
                               /\ TRUE
                               /\ pc' = [pc EXCEPT ![self] = "Run"]
                               /\ UNCHANGED << propose_requests, 
                                               propose_responses, 
                                               active_proposers, epoch, prop, 
                                               state >>

proposer(self) == Run(self) \/ StartNewWrite(self)
                     \/ SendProposeRequest(self)
                     \/ HandleProposeResponse(self)

HandlePropose(self) == /\ pc[self] = "HandlePropose"
                       /\ IF active_proposers /= {}
                             THEN /\ propose_requests[self] /= {}
                                  /\ \E req \in Range(propose_requests[self]):
                                       state' = [state EXCEPT ![self][Epoch] = IF TRUE THEN FALSE ELSE TRUE]
                                  /\ pc' = [pc EXCEPT ![self] = "HandleAccept"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ state' = state
                       /\ UNCHANGED << propose_requests, propose_responses, 
                                       active_proposers, epoch, prop >>

HandleAccept(self) == /\ pc[self] = "HandleAccept"
                      /\ TRUE
                      /\ pc' = [pc EXCEPT ![self] = "HandlePropose"]
                      /\ UNCHANGED << propose_requests, propose_responses, 
                                      active_proposers, epoch, prop, state >>

acceptor(self) == HandlePropose(self) \/ HandleAccept(self)

Next == (\E self \in Proposers: proposer(self))
           \/ (\E self \in Acceptors: acceptor(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Jan 18 11:15:54 CET 2019 by tschottdorf
\* Created Thu Jan 17 22:09:15 CET 2019 by tschottdorf
