--------------------------- MODULE PluginArchitecturePattern ---------------------------
(*
  TLA+ Specification for Plugin Architecture Pattern
  
  This pattern models a plugin system where plugins can be dynamically loaded,
  registered, and executed. Common in extensible applications like CAD software,
  game engines, and development tools.
  
  Key Properties:
  - Dynamic loading: Plugins loaded at runtime
  - Registration: Plugins must register before use
  - Name uniqueness: Each plugin has unique name
  - Lifecycle: Plugins go through load->register->execute->unregister->unload
  - Dependencies: Plugins can depend on other plugins
*)

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    PluginNames,        \* Set of plugin names
    PluginDependencies  \* Function from plugin to set of required plugins

VARIABLES
    loadedPlugins,      \* Set of loaded plugins
    registeredPlugins,  \* Set of registered plugins
    executingPlugins,   \* Set of currently executing plugins
    pluginStates,       \* Function from plugin name to state
    operationLog        \* Log of operations

vars == <<loadedPlugins, registeredPlugins, executingPlugins, pluginStates, operationLog>>

PluginStates == {"unloaded", "loaded", "registered", "executing", "error"}

-----------------------------------------------------------------------------

\* Type invariants
TypeOK == 
    /\ loadedPlugins \subseteq PluginNames
    /\ registeredPlugins \subseteq loadedPlugins
    /\ executingPlugins \subseteq registeredPlugins
    /\ pluginStates \in [PluginNames -> PluginStates]
    /\ \A p \in PluginNames:
        /\ (p \in loadedPlugins <=> pluginStates[p] \in {"loaded", "registered", "executing"})
        /\ (p \in registeredPlugins <=> pluginStates[p] \in {"registered", "executing"})
        /\ (p \in executingPlugins <=> pluginStates[p] = "executing")

\* Initial state
Init == 
    /\ loadedPlugins = {}
    /\ registeredPlugins = {}
    /\ executingPlugins = {}
    /\ pluginStates = [p \in PluginNames |-> "unloaded"]
    /\ operationLog = <<>>

-----------------------------------------------------------------------------

\* Helper: Check if all dependencies are registered
DependenciesSatisfied(plugin) ==
    PluginDependencies[plugin] \subseteq registeredPlugins

-----------------------------------------------------------------------------

\* Operations

\* Load a plugin from disk
LoadPlugin(plugin) ==
    /\ plugin \in PluginNames
    /\ pluginStates[plugin] = "unloaded"
    /\ pluginStates' = [pluginStates EXCEPT ![plugin] = "loaded"]
    /\ loadedPlugins' = loadedPlugins \union {plugin}
    /\ operationLog' = Append(operationLog, [op |-> "Load", plugin |-> plugin])
    /\ UNCHANGED <<registeredPlugins, executingPlugins>>

\* Register a plugin with the system
RegisterPlugin(plugin) ==
    /\ plugin \in PluginNames
    /\ pluginStates[plugin] = "loaded"
    /\ DependenciesSatisfied(plugin)
    /\ pluginStates' = [pluginStates EXCEPT ![plugin] = "registered"]
    /\ registeredPlugins' = registeredPlugins \union {plugin}
    /\ operationLog' = Append(operationLog, [op |-> "Register", plugin |-> plugin])
    /\ UNCHANGED <<loadedPlugins, executingPlugins>>

\* Execute a plugin
ExecutePlugin(plugin) ==
    /\ plugin \in PluginNames
    /\ pluginStates[plugin] = "registered"
    /\ pluginStates' = [pluginStates EXCEPT ![plugin] = "executing"]
    /\ executingPlugins' = executingPlugins \union {plugin}
    /\ operationLog' = Append(operationLog, [op |-> "Execute", plugin |-> plugin])
    /\ UNCHANGED <<loadedPlugins, registeredPlugins>>

\* Complete execution of a plugin
CompleteExecution(plugin) ==
    /\ plugin \in PluginNames
    /\ pluginStates[plugin] = "executing"
    /\ pluginStates' = [pluginStates EXCEPT ![plugin] = "registered"]
    /\ executingPlugins' = executingPlugins \ {plugin}
    /\ operationLog' = Append(operationLog, [op |-> "Complete", plugin |-> plugin])
    /\ UNCHANGED <<loadedPlugins, registeredPlugins>>

\* Unregister a plugin
UnregisterPlugin(plugin) ==
    /\ plugin \in PluginNames
    /\ pluginStates[plugin] = "registered"
    /\ ~(\E p \in registeredPlugins: plugin \in PluginDependencies[p])  \* No dependent plugins
    /\ pluginStates' = [pluginStates EXCEPT ![plugin] = "loaded"]
    /\ registeredPlugins' = registeredPlugins \ {plugin}
    /\ operationLog' = Append(operationLog, [op |-> "Unregister", plugin |-> plugin])
    /\ UNCHANGED <<loadedPlugins, executingPlugins>>

\* Unload a plugin
UnloadPlugin(plugin) ==
    /\ plugin \in PluginNames
    /\ pluginStates[plugin] = "loaded"
    /\ pluginStates' = [pluginStates EXCEPT ![plugin] = "unloaded"]
    /\ loadedPlugins' = loadedPlugins \ {plugin}
    /\ operationLog' = Append(operationLog, [op |-> "Unload", plugin |-> plugin])
    /\ UNCHANGED <<registeredPlugins, executingPlugins>>

\* Plugin encounters error
PluginError(plugin) ==
    /\ plugin \in PluginNames
    /\ pluginStates[plugin] \in {"loaded", "registered", "executing"}
    /\ pluginStates' = [pluginStates EXCEPT ![plugin] = "error"]
    /\ loadedPlugins' = IF plugin \in loadedPlugins THEN loadedPlugins \ {plugin} ELSE loadedPlugins
    /\ registeredPlugins' = IF plugin \in registeredPlugins THEN registeredPlugins \ {plugin} ELSE registeredPlugins
    /\ executingPlugins' = IF plugin \in executingPlugins THEN executingPlugins \ {plugin} ELSE executingPlugins
    /\ operationLog' = Append(operationLog, [op |-> "Error", plugin |-> plugin])

-----------------------------------------------------------------------------

\* Next state relation
Next == 
    \/ \E p \in PluginNames: LoadPlugin(p)
    \/ \E p \in PluginNames: RegisterPlugin(p)
    \/ \E p \in PluginNames: ExecutePlugin(p)
    \/ \E p \in PluginNames: CompleteExecution(p)
    \/ \E p \in PluginNames: UnregisterPlugin(p)
    \/ \E p \in PluginNames: UnloadPlugin(p)
    \/ \E p \in PluginNames: PluginError(p)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* Safety Properties

\* Load before register
LoadBeforeRegister ==
    \A p \in PluginNames:
        pluginStates[p] \in {"registered", "executing"} => p \in loadedPlugins

\* Register before execute
RegisterBeforeExecute ==
    \A p \in PluginNames:
        pluginStates[p] = "executing" => p \in registeredPlugins

\* Dependencies satisfied for all registered plugins
DependenciesAlwaysSatisfied ==
    \A p \in registeredPlugins:
        DependenciesSatisfied(p)

\* No circular dependencies in operation log
NoCyclicDependencies ==
    \A p1, p2 \in PluginNames:
        (p1 \in PluginDependencies[p2]) => (p2 \notin PluginDependencies[p1])

\* Cannot unregister if other plugins depend on it
CannotUnregisterWithDependents ==
    \A p \in registeredPlugins:
        (\E p2 \in registeredPlugins: p \in PluginDependencies[p2]) =>
            pluginStates[p] = "registered"

\* State consistency
StateConsistency ==
    /\ \A p \in executingPlugins: pluginStates[p] = "executing"
    /\ \A p \in registeredPlugins: pluginStates[p] \in {"registered", "executing"}
    /\ \A p \in loadedPlugins: pluginStates[p] \in {"loaded", "registered", "executing"}

-----------------------------------------------------------------------------

\* Liveness Properties

\* Loaded plugins can eventually be registered (if dependencies satisfied)
LoadedCanBeRegistered ==
    \A p \in PluginNames:
        [](pluginStates[p] = "loaded" /\ DependenciesSatisfied(p) => <>ENABLED RegisterPlugin(p))

\* Registered plugins can eventually execute
RegisteredCanExecute ==
    \A p \in PluginNames:
        [](pluginStates[p] = "registered" => <>ENABLED ExecutePlugin(p))

\* Executing plugins eventually complete
ExecutingEventuallyCompletes ==
    \A p \in PluginNames:
        [](pluginStates[p] = "executing" => <>(pluginStates[p] # "executing"))

=============================================================================
