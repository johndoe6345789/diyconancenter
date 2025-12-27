---------------------------- MODULE UniformWrapperPattern ----------------------------
(*
  TLA+ Specification for the Uniform Wrapper Pattern (Pimpl Pattern)
  
  This pattern provides a consistent API while using real production libraries as backends.
  It uses the Pimpl (Pointer to Implementation) idiom to hide implementation details.
  
  Key Properties:
  - Predictable API: All packages follow the same pattern with initialize() and process() methods
  - Implementation hiding: Internal details are hidden behind an opaque pointer
  - Resource safety: Proper initialization before use, cleanup on destruction
*)

EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    MaxCalls  \* Maximum number of method calls to check

VARIABLES
    state,          \* Current state of the wrapper object: "uninitialized", "initialized", "destroyed"
    implPtr,        \* Pointer to implementation (NULL or valid)
    callHistory,    \* Sequence of method calls made
    resourceLeak    \* Boolean flag indicating if resources are leaked

vars == <<state, implPtr, callHistory, resourceLeak>>

-----------------------------------------------------------------------------

\* Type invariants
TypeOK == 
    /\ state \in {"uninitialized", "initialized", "destroyed"}
    /\ implPtr \in {"NULL", "VALID"}
    /\ resourceLeak \in BOOLEAN
    /\ Len(callHistory) <= MaxCalls

\* Initial state
Init == 
    /\ state = "uninitialized"
    /\ implPtr = "NULL"
    /\ callHistory = <<>>
    /\ resourceLeak = FALSE

-----------------------------------------------------------------------------

\* Constructor - creates the object
Constructor ==
    /\ state = "uninitialized"
    /\ state' = "uninitialized"
    /\ implPtr' = "VALID"
    /\ callHistory' = Append(callHistory, "Constructor")
    /\ UNCHANGED resourceLeak

\* Initialize method - sets up resources
Initialize ==
    /\ state = "uninitialized"
    /\ implPtr = "VALID"
    /\ state' = "initialized"
    /\ callHistory' = Append(callHistory, "Initialize")
    /\ UNCHANGED <<implPtr, resourceLeak>>

\* Process method - main functionality
Process ==
    /\ state = "initialized"
    /\ implPtr = "VALID"
    /\ callHistory' = Append(callHistory, "Process")
    /\ UNCHANGED <<state, implPtr, resourceLeak>>

\* Destructor - cleans up resources
Destructor ==
    /\ state \in {"uninitialized", "initialized"}
    /\ implPtr = "VALID"
    /\ state' = "destroyed"
    /\ implPtr' = "NULL"
    /\ callHistory' = Append(callHistory, "Destructor")
    /\ resourceLeak' = (state = "initialized")  \* Leak if destroyed while initialized without cleanup

-----------------------------------------------------------------------------

\* Next state relation
Next == 
    \/ Constructor
    \/ Initialize
    \/ Process
    \/ Destructor

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* Safety Properties

\* Process can only be called after initialization
ProcessRequiresInitialization ==
    \A i \in 1..Len(callHistory):
        callHistory[i] = "Process" =>
            \E j \in 1..(i-1): 
                callHistory[j] = "Initialize"

\* Initialize should only be called once before process
SingleInitialization ==
    \A i, j \in 1..Len(callHistory):
        (i < j /\ callHistory[i] = "Initialize" /\ callHistory[j] = "Initialize") =>
            \E k \in (i+1)..(j-1):
                callHistory[k] = "Destructor"

\* No operations after destruction
NoUseAfterDestruction ==
    \A i \in 1..Len(callHistory):
        callHistory[i] = "Destructor" =>
            \A j \in (i+1)..Len(callHistory):
                callHistory[j] \notin {"Initialize", "Process"}

\* Resource management: no leaks allowed
NoResourceLeaks ==
    ~resourceLeak

\* Pimpl pointer validity
PimplPointerValidity ==
    /\ (state = "uninitialized" => implPtr = "VALID")
    /\ (state = "initialized" => implPtr = "VALID")
    /\ (state = "destroyed" => implPtr = "NULL")

-----------------------------------------------------------------------------

\* Liveness Properties

\* Eventually, if initialized, process should be callable
EventuallyProcessable ==
    <>(state = "initialized" => ENABLED Process)

=============================================================================
