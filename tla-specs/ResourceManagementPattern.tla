-------------------------- MODULE ResourceManagementPattern --------------------------
(*
  TLA+ Specification for Resource Management Pattern
  
  This pattern models a resource manager that handles loading, unloading, and accessing
  resources (e.g., game assets, CAD models, ML models). Resources are identified by
  handles to enable efficient management.
  
  Key Properties:
  - Handle uniqueness: Each resource has a unique handle
  - Load before use: Resources must be loaded before access
  - No double load: Same resource not loaded twice simultaneously
  - Proper cleanup: All loaded resources can be unloaded
  - No use-after-free: Cannot access unloaded resources
*)

EXTENDS Naturals, FiniteSets

CONSTANTS 
    ResourcePaths,  \* Set of resource paths/names
    MaxHandles      \* Maximum number of handles

VARIABLES
    resources,          \* Function from handles to resource paths (or NULL)
    loadedResources,    \* Set of currently loaded resource paths
    nextHandle,         \* Next handle to allocate
    accessLog           \* Log of access operations for verification

vars == <<resources, loadedResources, nextHandle, accessLog>>

Handles == 1..MaxHandles

-----------------------------------------------------------------------------

\* Type invariants
TypeOK == 
    /\ resources \in [Handles -> ResourcePaths \union {"NULL"}]
    /\ loadedResources \subseteq ResourcePaths
    /\ nextHandle \in Handles
    /\ \A h \in Handles: resources[h] \in ResourcePaths => resources[h] \in loadedResources

\* Initial state - no resources loaded
Init == 
    /\ resources = [h \in Handles |-> "NULL"]
    /\ loadedResources = {}
    /\ nextHandle = 1
    /\ accessLog = <<>>

-----------------------------------------------------------------------------

\* Operations

\* Load a resource and return a handle
LoadResource(path) ==
    /\ path \in ResourcePaths
    /\ path \notin loadedResources
    /\ nextHandle <= MaxHandles
    /\ resources' = [resources EXCEPT ![nextHandle] = path]
    /\ loadedResources' = loadedResources \union {path}
    /\ nextHandle' = IF nextHandle < MaxHandles THEN nextHandle + 1 ELSE nextHandle
    /\ accessLog' = Append(accessLog, [op |-> "Load", path |-> path, handle |-> nextHandle])

\* Unload a resource by handle
UnloadResource(handle) ==
    /\ handle \in Handles
    /\ resources[handle] \in ResourcePaths
    /\ LET path == resources[handle] IN
        /\ resources' = [resources EXCEPT ![handle] = "NULL"]
        /\ loadedResources' = loadedResources \ {path}
        /\ accessLog' = Append(accessLog, [op |-> "Unload", path |-> path, handle |-> handle])
        /\ UNCHANGED nextHandle

\* Access a resource by handle
AccessResource(handle) ==
    /\ handle \in Handles
    /\ resources[handle] \in ResourcePaths
    /\ accessLog' = Append(accessLog, [op |-> "Access", path |-> resources[handle], handle |-> handle])
    /\ UNCHANGED <<resources, loadedResources, nextHandle>>

\* Reset handle allocation (optional cleanup operation)
ResetHandles ==
    /\ loadedResources = {}
    /\ nextHandle' = 1
    /\ UNCHANGED <<resources, loadedResources, accessLog>>

-----------------------------------------------------------------------------

\* Next state relation
Next == 
    \/ \E p \in ResourcePaths: LoadResource(p)
    \/ \E h \in Handles: UnloadResource(h)
    \/ \E h \in Handles: AccessResource(h)
    \/ ResetHandles

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* Safety Properties

\* Handle uniqueness - each handle maps to at most one resource
HandleUniqueness ==
    \A h1, h2 \in Handles:
        (h1 # h2 /\ resources[h1] \in ResourcePaths /\ resources[h2] \in ResourcePaths) =>
            resources[h1] # resources[h2]

\* No double load - resource not loaded twice
NoDoubleLoad ==
    \A p \in ResourcePaths:
        Cardinality({h \in Handles: resources[h] = p}) <= 1

\* Access requires loaded resource
AccessRequiresLoaded ==
    \A i \in 1..Len(accessLog):
        accessLog[i].op = "Access" =>
            \E j \in 1..(i-1):
                /\ accessLog[j].op = "Load"
                /\ accessLog[j].path = accessLog[i].path
                /\ accessLog[j].handle = accessLog[i].handle
                /\ ~(\E k \in (j+1)..(i-1):
                      accessLog[k].op = "Unload" /\ accessLog[k].handle = accessLog[i].handle)

\* No use after free
NoUseAfterFree ==
    \A i \in 1..Len(accessLog):
        (accessLog[i].op = "Access") =>
            LET handle == accessLog[i].handle IN
                ~(\E j \in 1..(i-1):
                    accessLog[j].op = "Unload" /\ accessLog[j].handle = handle /\
                    ~(\E k \in (j+1)..(i-1):
                        accessLog[k].op = "Load" /\ accessLog[k].handle = handle))

\* Resources consistency
ResourcesConsistent ==
    \A h \in Handles:
        resources[h] \in ResourcePaths => resources[h] \in loadedResources

\* Handle allocation bounds
HandleAllocationValid ==
    nextHandle >= 1 /\ nextHandle <= MaxHandles

\* Loaded resources have handles
LoadedResourcesHaveHandles ==
    \A p \in loadedResources:
        \E h \in Handles: resources[h] = p

-----------------------------------------------------------------------------

\* Liveness Properties

\* Resources can be unloaded
ResourcesCanBeUnloaded ==
    \A p \in ResourcePaths:
        [](p \in loadedResources => <>ENABLED(\E h \in Handles: UnloadResource(h)))

\* All resources can eventually be loaded (if space available)
EventuallyLoadable ==
    \A p \in ResourcePaths:
        []<>(p \in loadedResources \/ ENABLED LoadResource(p))

=============================================================================
