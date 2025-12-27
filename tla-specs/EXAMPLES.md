# Example: Finding Bugs with TLA+ Model Checking

This document demonstrates how the TLA+ specifications can be used to find subtle bugs in design pattern implementations before they make it into production code.

## Example 1: Use-After-Free in Uniform Wrapper Pattern

### The Bug

Consider this implementation of the Uniform Wrapper Pattern:

```cpp
// BUGGY CODE - DO NOT USE
class JsonParser {
public:
    JsonParser() {
        pImpl = new Impl();  // Allocate implementation
    }
    
    ~JsonParser() {
        delete pImpl;
        pImpl = nullptr;
    }
    
    void initialize() {
        if (pImpl) pImpl->setup();
    }
    
    bool process() {
        // BUG: No check if initialized!
        return pImpl->execute();
    }
    
private:
    class Impl;
    Impl* pImpl;
};

// Usage that triggers the bug:
JsonParser parser;
// Forgot to call initialize()!
parser.process();  // May work by accident, but undefined behavior
```

### TLA+ Catches the Bug

The TLA+ specification `UniformWrapperPattern.tla` includes this invariant:

```tla
ProcessRequiresInitialization ==
    \A i \in 1..Len(callHistory):
        callHistory[i] = "Process" =>
            \E j \in 1..(i-1): 
                callHistory[j] = "Initialize"
```

Running the model checker:

```bash
$ java -cp tla2tools.jar tlc2.TLC UniformWrapperPattern.tla
...
Error: Invariant ProcessRequiresInitialization is violated.

State trace:
  1: Initial state with state = "uninitialized"
  2: Constructor → pImpl = "VALID", state = "uninitialized"
  3: Process → ERROR!
     
The invariant requires Initialize to be called before Process,
but the trace shows Process called directly after Constructor.
```

### The Fix

Add a state check in the `process()` method:

```cpp
// CORRECT CODE
class JsonParser {
public:
    JsonParser() : pImpl(std::make_unique<Impl>()), state_(State::Uninitialized) {}
    
    ~JsonParser() = default;  // unique_ptr handles cleanup
    
    void initialize() {
        assert(state_ == State::Uninitialized);
        if (pImpl) pImpl->setup();
        state_ = State::Initialized;
    }
    
    bool process() {
        assert(state_ == State::Initialized);  // FIX: Check state!
        return pImpl->execute();
    }
    
private:
    enum class State { Uninitialized, Initialized };
    class Impl;
    std::unique_ptr<Impl> pImpl;
    State state_;
};
```

---

## Example 2: Callback Double-Call in Async I/O

### The Bug

```cpp
// BUGGY CODE - DO NOT USE
class AsyncOperation {
public:
    void complete() {
        if (callback_) {
            callback_();  // BUG: No protection against double call!
            // callback_ is not cleared
        }
    }
    
    void setCallback(std::function<void()> cb) {
        callback_ = cb;
    }
    
private:
    std::function<void()> callback_;
};

// Usage that triggers the bug:
AsyncOperation op;
op.setCallback([]{ std::cout << "Done!\n"; });
op.complete();  // Prints "Done!"
op.complete();  // BUG: Prints "Done!" again!
```

### TLA+ Catches the Bug

The TLA+ specification `AsyncIOPattern.tla` includes:

```tla
CallbackCalledOnce ==
    \A id \in OperationIds:
        operations[id] = "completed" =>
            (callbacks[id] = "called" =>
                Cardinality({i \in 1..Len(eventLog): 
                    eventLog[i].op = "Callback" /\ eventLog[i].id = id}) = 1)
```

Running the model checker:

```bash
$ java -cp tla2tools.jar tlc2.TLC AsyncIOPattern.tla
...
Error: Invariant CallbackCalledOnce is violated.

State trace:
  1: InitiateOperation → opId=1, state="pending"
  2: StartExecution(1) → state="running"
  3: CompleteOperation(1) → state="completed"
  4: InvokeCallback(1) → callbacks[1]="called"
  5: InvokeCallback(1) → ERROR! Callback called twice!
```

### The Fix

Add protection against double invocation:

```cpp
// CORRECT CODE
class AsyncOperation {
public:
    void complete() {
        if (callback_ && !completed_) {  // FIX: Check completed_ flag
            callback_();
            callback_ = nullptr;  // FIX: Clear callback
            completed_ = true;    // FIX: Set flag
        }
    }
    
    void setCallback(std::function<void()> cb) {
        callback_ = cb;
    }
    
private:
    std::function<void()> callback_;
    bool completed_ = false;  // FIX: Add flag
};
```

---

## Example 3: Plugin Circular Dependency

### The Bug

```cpp
// BUGGY CODE - system will deadlock
PluginManager manager;

// Plugin A depends on Plugin B
manager.registerPlugin("PluginA", {"PluginB"});

// Plugin B depends on Plugin A - CIRCULAR DEPENDENCY!
manager.registerPlugin("PluginB", {"PluginA"});

// This will deadlock or fail:
manager.loadPlugin("PluginA");
```

### TLA+ Catches the Bug

The TLA+ specification `PluginArchitecturePattern.tla` includes:

```tla
NoCyclicDependencies ==
    \A p1, p2 \in PluginNames:
        (p1 \in PluginDependencies[p2]) => (p2 \notin PluginDependencies[p1])
```

Running the model checker:

```bash
$ java -cp tla2tools.jar tlc2.TLC PluginArchitecturePattern.tla
...
Error: Invariant NoCyclicDependencies is violated.

Constants:
  PluginDependencies = [
    PluginA |-> {"PluginB"},
    PluginB |-> {"PluginA"}  <-- CIRCULAR!
  ]

The specification found a circular dependency between PluginA and PluginB.
```

### The Fix

Detect circular dependencies at registration time:

```cpp
// CORRECT CODE
class PluginManager {
public:
    void registerPlugin(const std::string& name, 
                       const std::set<std::string>& deps) {
        // FIX: Check for circular dependencies
        if (hasCircularDependency(name, deps)) {
            throw std::runtime_error("Circular dependency detected!");
        }
        plugins_[name] = deps;
    }
    
private:
    bool hasCircularDependency(const std::string& name,
                              const std::set<std::string>& deps) {
        // Check if any dependency depends on this plugin (directly or transitively)
        for (const auto& dep : deps) {
            if (dependsOn(dep, name)) {
                return true;
            }
        }
        return false;
    }
    
    bool dependsOn(const std::string& plugin, const std::string& target) {
        if (plugin == target) return true;
        
        auto it = plugins_.find(plugin);
        if (it == plugins_.end()) return false;
        
        for (const auto& dep : it->second) {
            if (dependsOn(dep, target)) return true;
        }
        return false;
    }
    
    std::map<std::string, std::set<std::string>> plugins_;
};
```

---

## Example 4: Resource Double-Free

### The Bug

```cpp
// BUGGY CODE - DO NOT USE
class ResourceManager {
public:
    Handle load(const std::string& path) {
        auto handle = nextHandle_++;
        resources_[handle] = loadFromDisk(path);
        return handle;
    }
    
    void unload(Handle handle) {
        resources_.erase(handle);  // BUG: No check if already unloaded
    }
    
    Resource* get(Handle handle) {
        return resources_[handle].get();  // BUG: May return nullptr!
    }
};

// Usage that triggers bug:
auto h = manager.load("model.obj");
manager.unload(h);
manager.unload(h);  // BUG: Double-free attempt
auto* r = manager.get(h);  // BUG: Use-after-free
```

### TLA+ Catches the Bug

The specification `ResourceManagementPattern.tla` includes:

```tla
NoUseAfterFree ==
    \A i \in 1..Len(accessLog):
        (accessLog[i].op = "Access") =>
            ~(\E j \in 1..(i-1):
                accessLog[j].op = "Unload" /\ accessLog[j].handle = accessLog[i].handle)
```

Running the model checker finds the violation immediately.

### The Fix

Add proper state checking:

```cpp
// CORRECT CODE
class ResourceManager {
public:
    Handle load(const std::string& path) {
        auto handle = nextHandle_++;
        resources_[handle] = loadFromDisk(path);
        return handle;
    }
    
    void unload(Handle handle) {
        auto it = resources_.find(handle);
        if (it != resources_.end()) {  // FIX: Check if exists
            resources_.erase(it);
        } else {
            throw std::runtime_error("Handle not found!");  // FIX: Error on invalid
        }
    }
    
    Resource* get(Handle handle) {
        auto it = resources_.find(handle);
        if (it == resources_.end()) {  // FIX: Check if exists
            throw std::runtime_error("Handle not found!");
        }
        return it->second.get();
    }
};
```

---

## Benefits of TLA+ Verification

### 1. **Early Detection**
Bugs found during design, not in production.

### 2. **Exhaustive Testing**
Model checker explores ALL possible execution paths, not just the ones you think to test.

### 3. **Concurrency Bugs**
Finds race conditions and deadlocks that are nearly impossible to catch with traditional testing.

### 4. **Edge Cases**
Discovers corner cases you didn't know existed.

### 5. **Documentation**
Specifications serve as precise, unambiguous documentation of expected behavior.

### 6. **Refactoring Confidence**
After changes, re-run model checker to ensure no regression.

---

## Running the Examples

To verify these patterns yourself:

```bash
cd tla-specs

# Check Uniform Wrapper Pattern
java -cp ~/tla2tools.jar tlc2.TLC UniformWrapperPattern.tla

# Check Async I/O Pattern  
java -cp ~/tla2tools.jar tlc2.TLC AsyncIOPattern.tla

# Check Plugin Architecture Pattern
java -cp ~/tla2tools.jar tlc2.TLC PluginArchitecturePattern.tla

# Check Resource Management Pattern
java -cp ~/tla2tools.jar tlc2.TLC ResourceManagementPattern.tla
```

All patterns should pass verification, confirming they are correctly designed!

---

## Lessons Learned

1. **State Machines Are Subtle**: Even simple patterns have subtle state management bugs
2. **Assertions Are Essential**: Runtime assertions catch violations in production
3. **Formal Methods Work**: TLA+ finds bugs that code review and testing miss
4. **Prevention > Cure**: Fixing bugs in design is 100x cheaper than fixing in production
5. **Documentation Clarity**: Formal specs eliminate ambiguity in requirements

## Next Steps

- Study the TLA+ specifications in `tla-specs/`
- Run model checker on your own designs
- Add runtime assertions based on TLA+ invariants
- Use specs as reference during code review
- Update specs when patterns evolve

---

**Remember**: These specifications aren't just academic exercises—they're practical tools that find real bugs before they reach production!
