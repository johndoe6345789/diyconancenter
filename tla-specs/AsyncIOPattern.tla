------------------------------- MODULE AsyncIOPattern -------------------------------
(*
  TLA+ Specification for Async I/O Pattern
  
  This pattern models asynchronous I/O operations using callbacks, futures, or
  promises. Operations are initiated without blocking, and completion is signaled
  through callbacks or by checking operation status.
  
  Key Properties:
  - Non-blocking: Operations return immediately with a handle
  - Completion notification: Callbacks invoked when operations complete
  - Cancellation: Operations can be cancelled before completion
  - No double completion: Callbacks called exactly once
  - Resource cleanup: All operations eventually complete or are cancelled
*)

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    MaxOperations   \* Maximum concurrent async operations

VARIABLES
    operations,         \* Function from operation ID to operation state
    nextOpId,           \* Next operation ID to allocate
    callbacks,          \* Function from operation ID to callback state
    completedOps,       \* Set of completed operation IDs
    cancelledOps,       \* Set of cancelled operation IDs
    eventLog            \* Log of events

vars == <<operations, nextOpId, callbacks, completedOps, cancelledOps, eventLog>>

OperationStates == {"pending", "running", "completed", "cancelled", "error"}
CallbackStates == {"not_called", "called"}

OperationIds == 1..MaxOperations

-----------------------------------------------------------------------------

\* Type invariants
TypeOK == 
    /\ operations \in [OperationIds -> OperationStates \union {"none"}]
    /\ nextOpId \in 1..(MaxOperations + 1)
    /\ callbacks \in [OperationIds -> CallbackStates]
    /\ completedOps \subseteq OperationIds
    /\ cancelledOps \subseteq OperationIds
    /\ completedOps \cap cancelledOps = {}

\* Initial state
Init == 
    /\ operations = [id \in OperationIds |-> "none"]
    /\ nextOpId = 1
    /\ callbacks = [id \in OperationIds |-> "not_called"]
    /\ completedOps = {}
    /\ cancelledOps = {}
    /\ eventLog = <<>>

-----------------------------------------------------------------------------

\* Operations

\* Initiate an async operation
InitiateOperation ==
    /\ nextOpId <= MaxOperations
    /\ operations' = [operations EXCEPT ![nextOpId] = "pending"]
    /\ nextOpId' = nextOpId + 1
    /\ eventLog' = Append(eventLog, [op |-> "Initiate", id |-> nextOpId])
    /\ UNCHANGED <<callbacks, completedOps, cancelledOps>>

\* Start executing a pending operation
StartExecution(opId) ==
    /\ opId \in OperationIds
    /\ operations[opId] = "pending"
    /\ operations' = [operations EXCEPT ![opId] = "running"]
    /\ eventLog' = Append(eventLog, [op |-> "Start", id |-> opId])
    /\ UNCHANGED <<nextOpId, callbacks, completedOps, cancelledOps>>

\* Complete an operation successfully
CompleteOperation(opId) ==
    /\ opId \in OperationIds
    /\ operations[opId] = "running"
    /\ operations' = [operations EXCEPT ![opId] = "completed"]
    /\ completedOps' = completedOps \union {opId}
    /\ eventLog' = Append(eventLog, [op |-> "Complete", id |-> opId])
    /\ UNCHANGED <<nextOpId, callbacks, cancelledOps>>

\* Invoke callback for completed operation
InvokeCallback(opId) ==
    /\ opId \in OperationIds
    /\ operations[opId] = "completed"
    /\ callbacks[opId] = "not_called"
    /\ callbacks' = [callbacks EXCEPT ![opId] = "called"]
    /\ eventLog' = Append(eventLog, [op |-> "Callback", id |-> opId])
    /\ UNCHANGED <<operations, nextOpId, completedOps, cancelledOps>>

\* Cancel a pending or running operation
CancelOperation(opId) ==
    /\ opId \in OperationIds
    /\ operations[opId] \in {"pending", "running"}
    /\ operations' = [operations EXCEPT ![opId] = "cancelled"]
    /\ cancelledOps' = cancelledOps \union {opId}
    /\ eventLog' = Append(eventLog, [op |-> "Cancel", id |-> opId])
    /\ UNCHANGED <<nextOpId, callbacks, completedOps>>

\* Operation encounters an error
OperationError(opId) ==
    /\ opId \in OperationIds
    /\ operations[opId] \in {"pending", "running"}
    /\ operations' = [operations EXCEPT ![opId] = "error"]
    /\ eventLog' = Append(eventLog, [op |-> "Error", id |-> opId])
    /\ UNCHANGED <<nextOpId, callbacks, completedOps, cancelledOps>>

\* Invoke error callback
InvokeErrorCallback(opId) ==
    /\ opId \in OperationIds
    /\ operations[opId] = "error"
    /\ callbacks[opId] = "not_called"
    /\ callbacks' = [callbacks EXCEPT ![opId] = "called"]
    /\ eventLog' = Append(eventLog, [op |-> "ErrorCallback", id |-> opId])
    /\ UNCHANGED <<operations, nextOpId, completedOps, cancelledOps>>

\* Check if operation is complete (polling)
PollOperation(opId) ==
    /\ opId \in OperationIds
    /\ operations[opId] \in {"pending", "running", "completed", "cancelled", "error"}
    /\ eventLog' = Append(eventLog, [op |-> "Poll", id |-> opId, 
                                     state |-> operations[opId]])
    /\ UNCHANGED <<operations, nextOpId, callbacks, completedOps, cancelledOps>>

-----------------------------------------------------------------------------

\* Next state relation
Next == 
    \/ InitiateOperation
    \/ \E id \in OperationIds: StartExecution(id)
    \/ \E id \in OperationIds: CompleteOperation(id)
    \/ \E id \in OperationIds: InvokeCallback(id)
    \/ \E id \in OperationIds: CancelOperation(id)
    \/ \E id \in OperationIds: OperationError(id)
    \/ \E id \in OperationIds: InvokeErrorCallback(id)
    \/ \E id \in OperationIds: PollOperation(id)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* Safety Properties

\* Operations must be initiated before execution
InitiatedBeforeExecution ==
    \A id \in OperationIds:
        operations[id] \in {"running", "completed", "cancelled", "error"} =>
            \E i \in 1..Len(eventLog):
                eventLog[i].op = "Initiate" /\ eventLog[i].id = id

\* Running before completion
RunningBeforeCompletion ==
    \A id \in completedOps:
        \E i, j \in 1..Len(eventLog):
            /\ i < j
            /\ eventLog[i].op = "Start" /\ eventLog[i].id = id
            /\ eventLog[j].op = "Complete" /\ eventLog[j].id = id

\* Callbacks called exactly once for completed operations
CallbackCalledOnce ==
    \A id \in OperationIds:
        operations[id] = "completed" =>
            (callbacks[id] = "called" =>
                Cardinality({i \in 1..Len(eventLog): 
                    eventLog[i].op = "Callback" /\ eventLog[i].id = id}) = 1)

\* No callback for cancelled operations
NoCallbackAfterCancel ==
    \A id \in cancelledOps:
        callbacks[id] = "not_called"

\* Cannot complete cancelled operation
CannotCompleteCancelled ==
    \A id \in OperationIds:
        operations[id] = "cancelled" => id \notin completedOps

\* Completed operations disjoint from cancelled
CompletedAndCancelledDisjoint ==
    completedOps \cap cancelledOps = {}

\* Non-blocking: Initiate returns immediately
NonBlocking ==
    \A i \in 1..Len(eventLog):
        eventLog[i].op = "Initiate" =>
            (i < Len(eventLog) => 
                eventLog[i+1].op \in {"Initiate", "Start", "Complete", "Callback", 
                                      "Cancel", "Error", "ErrorCallback", "Poll"})

-----------------------------------------------------------------------------

\* Liveness Properties

\* Pending operations eventually start or get cancelled
PendingEventuallyProcessed ==
    \A id \in OperationIds:
        [](operations[id] = "pending" => <>(operations[id] # "pending"))

\* Running operations eventually complete, error, or cancelled
RunningEventuallyFinishes ==
    \A id \in OperationIds:
        [](operations[id] = "running" => <>(operations[id] \in {"completed", "cancelled", "error"}))

\* Completed operations eventually invoke callback
CompletedEventuallyCallsCallback ==
    \A id \in OperationIds:
        [](operations[id] = "completed" => <>(callbacks[id] = "called"))

\* Error operations eventually invoke error callback
ErrorEventuallyCallsCallback ==
    \A id \in OperationIds:
        [](operations[id] = "error" => <>(callbacks[id] = "called"))

=============================================================================
