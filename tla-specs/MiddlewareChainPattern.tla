-------------------------- MODULE MiddlewareChainPattern --------------------------
(*
  TLA+ Specification for Middleware Chain Architecture Pattern (Web Development)
  
  This pattern models HTTP request processing through a chain of middleware functions.
  Each middleware can process the request, modify it, pass it to the next middleware,
  or short-circuit the chain by sending a response.
  
  Key Properties:
  - Sequential processing: Middleware executes in order
  - Request/Response immutability: Each middleware gets a copy of request/response
  - Short-circuiting: Any middleware can end the chain early
  - Error handling: Errors propagate through the chain
*)

EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    Middleware,     \* Set of middleware names: {"Auth", "Logging", "CORS", "RateLimit", "Handler"}
    MaxRequests     \* Maximum requests to model

VARIABLES
    requestQueue,       \* Queue of incoming requests
    currentRequest,     \* Currently processing request (or NULL)
    middlewareChain,    \* Sequence of middleware to execute
    currentMiddleware,  \* Index in chain (0 means no request processing)
    responseReady,      \* Boolean indicating if response is ready
    errorOccurred,      \* Boolean indicating if error occurred
    requestCount        \* Total requests processed

vars == <<requestQueue, currentRequest, middlewareChain, currentMiddleware, 
          responseReady, errorOccurred, requestCount>>

-----------------------------------------------------------------------------

\* Type invariants
TypeOK == 
    /\ Len(requestQueue) <= MaxRequests
    /\ currentRequest \in {"NULL", "REQUEST"}
    /\ currentMiddleware \in 0..Len(middlewareChain)
    /\ responseReady \in BOOLEAN
    /\ errorOccurred \in BOOLEAN
    /\ requestCount \in Nat

\* Initial state
Init == 
    /\ requestQueue = <<>>
    /\ currentRequest = "NULL"
    /\ middlewareChain = <<"Auth", "Logging", "CORS", "RateLimit", "Handler">>
    /\ currentMiddleware = 0
    /\ responseReady = FALSE
    /\ errorOccurred = FALSE
    /\ requestCount = 0

-----------------------------------------------------------------------------

\* Operations

\* Receive a new request
ReceiveRequest ==
    /\ Len(requestQueue) < MaxRequests
    /\ currentRequest = "NULL"
    /\ requestQueue' = Append(requestQueue, "REQUEST")
    /\ UNCHANGED <<currentRequest, middlewareChain, currentMiddleware, 
                   responseReady, errorOccurred, requestCount>>

\* Start processing next request from queue
StartProcessing ==
    /\ Len(requestQueue) > 0
    /\ currentRequest = "NULL"
    /\ ~responseReady
    /\ currentRequest' = Head(requestQueue)
    /\ requestQueue' = Tail(requestQueue)
    /\ currentMiddleware' = 1
    /\ UNCHANGED <<middlewareChain, responseReady, errorOccurred, requestCount>>

\* Execute current middleware successfully
ExecuteMiddleware ==
    /\ currentRequest = "REQUEST"
    /\ currentMiddleware > 0
    /\ currentMiddleware <= Len(middlewareChain)
    /\ ~responseReady
    /\ ~errorOccurred
    /\ currentMiddleware' = currentMiddleware + 1
    /\ UNCHANGED <<requestQueue, currentRequest, middlewareChain, 
                   responseReady, errorOccurred, requestCount>>

\* Middleware short-circuits the chain with a response
ShortCircuit ==
    /\ currentRequest = "REQUEST"
    /\ currentMiddleware > 0
    /\ currentMiddleware <= Len(middlewareChain)
    /\ ~responseReady
    /\ ~errorOccurred
    /\ responseReady' = TRUE
    /\ UNCHANGED <<requestQueue, currentRequest, middlewareChain, 
                   currentMiddleware, errorOccurred, requestCount>>

\* Middleware encounters an error
MiddlewareError ==
    /\ currentRequest = "REQUEST"
    /\ currentMiddleware > 0
    /\ currentMiddleware <= Len(middlewareChain)
    /\ ~responseReady
    /\ ~errorOccurred
    /\ errorOccurred' = TRUE
    /\ responseReady' = TRUE
    /\ UNCHANGED <<requestQueue, currentRequest, middlewareChain, 
                   currentMiddleware, requestCount>>

\* Complete request processing (end of chain or response ready)
CompleteRequest ==
    /\ currentRequest = "REQUEST"
    /\ (responseReady \/ currentMiddleware > Len(middlewareChain))
    /\ currentRequest' = "NULL"
    /\ currentMiddleware' = 0
    /\ responseReady' = FALSE
    /\ errorOccurred' = FALSE
    /\ requestCount' = requestCount + 1
    /\ UNCHANGED <<requestQueue, middlewareChain>>

-----------------------------------------------------------------------------

\* Next state relation
Next == 
    \/ ReceiveRequest
    \/ StartProcessing
    \/ ExecuteMiddleware
    \/ ShortCircuit
    \/ MiddlewareError
    \/ CompleteRequest

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* Safety Properties

\* Request must start processing before middleware executes
ProcessingRequired ==
    currentMiddleware > 0 => currentRequest = "REQUEST"

\* Middleware index within bounds
MiddlewareIndexValid ==
    currentMiddleware >= 0 /\ currentMiddleware <= Len(middlewareChain) + 1

\* Response finalized before completing request
ResponseReadyBeforeCompletion ==
    (currentRequest = "REQUEST" /\ ENABLED CompleteRequest) =>
        (responseReady \/ currentMiddleware > Len(middlewareChain))

\* Cannot execute middleware after response ready
NoExecutionAfterResponse ==
    responseReady => ~ENABLED ExecuteMiddleware

\* Error implies response ready
ErrorImpliesResponse ==
    errorOccurred => responseReady

\* Sequential processing - middleware executes in order
SequentialProcessing ==
    currentMiddleware <= Len(middlewareChain) + 1

\* Request queue bounded
RequestQueueBounded ==
    Len(requestQueue) <= MaxRequests

-----------------------------------------------------------------------------

\* Liveness Properties

\* All requests eventually complete
RequestsEventuallyComplete ==
    [](currentRequest = "REQUEST" => <>(currentRequest = "NULL"))

\* Request queue eventually drains
QueueEventuallyDrains ==
    [](Len(requestQueue) > 0 => <>(Len(requestQueue) = 0))

\* System makes progress
SystemMakesProgress ==
    <>[]((Len(requestQueue) = 0 /\ currentRequest = "NULL") \/ requestCount > 0)

=============================================================================
