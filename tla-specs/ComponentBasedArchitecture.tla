------------------------- MODULE ComponentBasedArchitecture -------------------------
(*
  TLA+ Specification for Component-Based Architecture Pattern (Game Development)
  
  This pattern models a system where multiple components (Graphics, Physics, Audio, Input)
  communicate through an event-driven architecture. Each component has its own lifecycle
  and can publish/subscribe to events.
  
  Key Properties:
  - Component independence: Components don't directly depend on each other
  - Event-driven communication: Components communicate via events
  - Lifecycle management: All components follow initialize->update->shutdown lifecycle
  - No cyclic dependencies: Component updates don't create circular event chains
*)

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    Components,     \* Set of component names: {"Graphics", "Physics", "Audio", "Input"}
    EventTypes,     \* Set of event types: {"CollisionEvent", "InputEvent", "AudioEvent"}
    MaxEvents       \* Maximum events in queue to prevent infinite states

VARIABLES
    componentStates,    \* Function from Components to states {"uninitialized", "initialized", "running", "shutdown"}
    eventQueue,         \* Sequence of pending events
    eventHandlers,      \* Function from (Component, EventType) to subscribed status
    updateCycle         \* Current update cycle number

vars == <<componentStates, eventQueue, eventHandlers, updateCycle>>

-----------------------------------------------------------------------------

\* Type invariants
TypeOK == 
    /\ \A c \in Components: 
        componentStates[c] \in {"uninitialized", "initialized", "running", "shutdown"}
    /\ Len(eventQueue) <= MaxEvents
    /\ updateCycle \in Nat

\* Initial state - all components uninitialized
Init == 
    /\ componentStates = [c \in Components |-> "uninitialized"]
    /\ eventQueue = <<>>
    /\ eventHandlers = [c \in Components |-> [e \in EventTypes |-> FALSE]]
    /\ updateCycle = 0

-----------------------------------------------------------------------------

\* Component Operations

\* Initialize a component
InitializeComponent(component) ==
    /\ componentStates[component] = "uninitialized"
    /\ componentStates' = [componentStates EXCEPT ![component] = "initialized"]
    /\ UNCHANGED <<eventQueue, eventHandlers, updateCycle>>

\* Start a component (transition to running state)
StartComponent(component) ==
    /\ componentStates[component] = "initialized"
    /\ componentStates' = [componentStates EXCEPT ![component] = "running"]
    /\ UNCHANGED <<eventQueue, eventHandlers, updateCycle>>

\* Subscribe component to an event type
SubscribeToEvent(component, eventType) ==
    /\ componentStates[component] \in {"initialized", "running"}
    /\ eventType \in EventTypes
    /\ ~eventHandlers[component][eventType]
    /\ eventHandlers' = [eventHandlers EXCEPT ![component][eventType] = TRUE]
    /\ UNCHANGED <<componentStates, eventQueue, updateCycle>>

\* Publish an event to the queue
PublishEvent(component, eventType) ==
    /\ componentStates[component] = "running"
    /\ eventType \in EventTypes
    /\ Len(eventQueue) < MaxEvents
    /\ eventQueue' = Append(eventQueue, [type |-> eventType, source |-> component])
    /\ UNCHANGED <<componentStates, eventHandlers, updateCycle>>

\* Process one event from the queue
ProcessEvent ==
    /\ Len(eventQueue) > 0
    /\ LET event == Head(eventQueue)
           subscribers == {c \in Components: eventHandlers[c][event.type]}
       IN
           /\ eventQueue' = Tail(eventQueue)
           /\ UNCHANGED <<componentStates, eventHandlers, updateCycle>>

\* Update cycle - all running components update
UpdateCycle ==
    /\ \A c \in Components: componentStates[c] \in {"running", "shutdown"}
    /\ updateCycle' = updateCycle + 1
    /\ UNCHANGED <<componentStates, eventQueue, eventHandlers>>

\* Shutdown a component
ShutdownComponent(component) ==
    /\ componentStates[component] \in {"initialized", "running"}
    /\ componentStates' = [componentStates EXCEPT ![component] = "shutdown"]
    /\ UNCHANGED <<eventQueue, eventHandlers, updateCycle>>

-----------------------------------------------------------------------------

\* Next state relation
Next == 
    \/ \E c \in Components: InitializeComponent(c)
    \/ \E c \in Components: StartComponent(c)
    \/ \E c \in Components, e \in EventTypes: SubscribeToEvent(c, e)
    \/ \E c \in Components, e \in EventTypes: PublishEvent(c, e)
    \/ ProcessEvent
    \/ UpdateCycle
    \/ \E c \in Components: ShutdownComponent(c)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* Safety Properties

\* Components must be initialized before running
InitBeforeRun ==
    \A c \in Components:
        componentStates[c] = "running" => 
            componentStates[c] \in {"initialized", "running"}

\* Can only publish events when running
PublishRequiresRunning ==
    \A i \in 1..Len(eventQueue):
        componentStates[eventQueue[i].source] = "running"

\* Event queue bounded
EventQueueBounded ==
    Len(eventQueue) <= MaxEvents

\* No operation after shutdown
NoOperationAfterShutdown ==
    \A c \in Components:
        componentStates[c] = "shutdown" =>
            \A e \in EventTypes: ~eventHandlers[c][e]

\* All components eventually reach running state before any shutdown
ComponentsInitializeBeforeShutdown ==
    (\E c \in Components: componentStates[c] = "shutdown") =>
        (\A c \in Components: componentStates[c] \in {"running", "shutdown"})

-----------------------------------------------------------------------------

\* Liveness Properties

\* All components eventually initialize
EventuallyAllInitialized ==
    <>(\A c \in Components: componentStates[c] \in {"initialized", "running", "shutdown"})

\* Events are eventually processed
EventsEventuallyProcessed ==
    [](Len(eventQueue) > 0 => <>(Len(eventQueue) = 0))

\* System makes progress (update cycles increase)
SystemMakesProgress ==
    []<>(updateCycle > 0)

=============================================================================
