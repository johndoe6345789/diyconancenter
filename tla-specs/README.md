# TLA+ Specifications for Design Patterns

This directory contains formal specifications in TLA+ (Temporal Logic of Actions) for the architectural design patterns used in the DIY Conan Center project.

## What is TLA+?

TLA+ is a formal specification language developed by Leslie Lamport for designing, modeling, documenting, and verifying concurrent systems and algorithms. It uses temporal logic and set theory to specify the behavior of systems precisely.

### Why TLA+ for Design Patterns?

- **Formal Verification**: Mathematically prove that design patterns satisfy critical properties
- **Exhaustive Testing**: Model checkers explore all possible states and behaviors
- **Documentation**: Precise, unambiguous specifications serve as documentation
- **Bug Detection**: Find subtle concurrency bugs and edge cases before implementation
- **Design Validation**: Ensure patterns work correctly before coding

## Specifications Overview

### 1. Uniform Wrapper Pattern (Pimpl Pattern)
**File**: `UniformWrapperPattern.tla`

Models the Pimpl (Pointer to Implementation) idiom used throughout the repository to provide uniform APIs while hiding implementation details.

**Key Properties Verified**:
- Process can only be called after initialization
- Single initialization before use
- No operations after destruction
- No resource leaks
- Pimpl pointer validity

**Use Cases**: json-parser, logger, string-utils, math-lib

---

### 2. Component-Based Architecture Pattern
**File**: `ComponentBasedArchitecture.tla`

Models game development architecture with independent components (Graphics, Physics, Audio, Input) communicating through events.

**Key Properties Verified**:
- Components must be initialized before running
- Events published only when running
- Event queue remains bounded
- No operations after shutdown
- All components eventually initialize
- Events are eventually processed

**Use Cases**: game-engine, game-physics, game-audio, game-networking

---

### 3. Middleware Chain Architecture Pattern
**File**: `MiddlewareChainPattern.tla`

Models HTTP request processing through a chain of middleware functions (Auth, Logging, CORS, Rate Limiting).

**Key Properties Verified**:
- Sequential middleware execution
- Request must be started before middleware executes
- Middleware executes in order
- Short-circuiting support (early response)
- Error handling propagation
- All requests eventually complete
- Request queue eventually drains

**Use Cases**: web-server, http-server, rest-framework

---

### 4. Resource Management Pattern
**File**: `ResourceManagementPattern.tla`

Models resource handles for managing game assets, CAD models, or ML models with load/unload operations.

**Key Properties Verified**:
- Handle uniqueness (each resource has unique handle)
- No double loading (same resource not loaded twice)
- Access requires loaded resource
- No use-after-free
- Resources consistent with handles
- All resources can be unloaded

**Use Cases**: game assets, CAD models, ML models, texture management

---

### 5. Plugin Architecture Pattern
**File**: `PluginArchitecturePattern.tla`

Models dynamic plugin loading with dependency management, common in extensible applications.

**Key Properties Verified**:
- Load before register
- Register before execute
- Dependencies always satisfied
- No circular dependencies
- Cannot unregister with dependents
- State consistency
- Loaded plugins can be registered
- Registered plugins can execute

**Use Cases**: CAD extensions, game mods, dev tool plugins

---

### 6. Async I/O Pattern
**File**: `AsyncIOPattern.tla`

Models asynchronous I/O operations with callbacks, futures, or promises for non-blocking operations.

**Key Properties Verified**:
- Operations initiated before execution
- Running before completion
- Callbacks called exactly once
- No callback after cancellation
- Cannot complete cancelled operation
- Non-blocking behavior
- Pending operations eventually processed
- Completed operations invoke callbacks

**Use Cases**: web servers, game networking, ML inference, async file I/O

---

## Getting Started

### Prerequisites

1. **Install TLA+ Tools**:
   ```bash
   # Download TLA+ Toolbox from:
   # https://github.com/tlaplus/tlaplus/releases
   
   # Or use command-line tools:
   wget https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
   ```

2. **Java Runtime**: TLA+ requires Java 11 or higher
   ```bash
   java -version
   ```

### Running Model Checker

#### Using TLA+ Toolbox (GUI)
1. Open TLA+ Toolbox
2. File → Open Spec → Add New Spec
3. Select a `.tla` file (e.g., `UniformWrapperPattern.tla`)
4. Create a new model with corresponding `.cfg` file
5. Run TLC Model Checker

#### Using Command Line
```bash
# Check a specification
java -cp tla2tools.jar tlc2.TLC -config UniformWrapperPattern.cfg UniformWrapperPattern.tla

# With more workers for faster checking
java -cp tla2tools.jar tlc2.TLC -workers 4 -config ComponentBasedArchitecture.cfg ComponentBasedArchitecture.tla

# Generate state graph
java -cp tla2tools.jar tlc2.TLC -dump dot graph.dot UniformWrapperPattern.tla
```

### Example: Checking Uniform Wrapper Pattern

```bash
cd tla-specs
java -cp ~/tla2tools.jar tlc2.TLC -config UniformWrapperPattern.cfg UniformWrapperPattern.tla
```

Expected output:
```
TLC2 Version 2.18
...
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = ...
States analyzed: 1234 states
States on queue: 0 states
```

## Understanding TLA+ Specifications

### Basic Structure

```tla
---------------------------- MODULE ModuleName ----------------------------
(* Description and comments *)

EXTENDS Naturals, Sequences    \* Import standard modules

CONSTANTS                       \* System parameters
    MaxValue

VARIABLES                       \* System state
    state,
    counter

Init == state = "initial"       \* Initial state

Next == ...                     \* State transitions

Spec == Init /\ [][Next]_vars   \* Complete specification

Property == ...                 \* Safety/liveness properties

=============================================================================
```

### Key Concepts

#### State Variables
Variables that define the system state:
```tla
VARIABLES
    operations,     \* Current operations
    nextId          \* Next ID to allocate
```

#### Actions
State transitions that modify variables:
```tla
Initialize ==
    /\ state = "uninitialized"
    /\ state' = "initialized"
    /\ UNCHANGED other_vars
```

#### Invariants (Safety Properties)
Properties that must always be true:
```tla
TypeOK == state \in {"uninitialized", "initialized"}
NoResourceLeaks == ~resourceLeak
```

#### Temporal Properties (Liveness)
Properties about eventual outcomes:
```tla
EventuallyInitialized == <>(state = "initialized")
AlwaysEventually == [](condition => <>(result))
```

### Operators

- `/\` : AND (conjunction)
- `\/` : OR (disjunction)
- `~`  : NOT (negation)
- `=>` : IMPLIES
- `[]` : Always (in all future states)
- `<>` : Eventually (in some future state)
- `'`  : Next state (e.g., `state'` is state in next step)
- `UNCHANGED var` : Variable doesn't change

## Interpreting Results

### Success
```
Model checking completed. No error has been found.
```
All properties verified! The design pattern is correct.

### Invariant Violation
```
Error: Invariant NoResourceLeaks is violated.
State trace:
  1. <Initial State>
  2. Constructor ->
  3. Initialize ->
  4. Destructor ->
```
Shows exact sequence of steps that violate a property.

### Deadlock
```
Error: Deadlock reached.
```
System reached a state where no actions are enabled but specification requires progress.

### Temporal Property Violation
```
Error: Temporal property EventuallyProcessed is violated.
```
A liveness property failed - something that should eventually happen never does.

## Customizing Specifications

### Adjusting Constants

Edit `.cfg` files to change parameters:
```
CONSTANTS
    MaxOperations = 3    \* Try 5 for more thorough checking
    Components = {"Graphics", "Physics"}  \* Reduce for faster checking
```

### Adding Properties

Add new invariants to `.tla` files:
```tla
MyNewProperty ==
    \A x \in SomeSet: 
        condition(x) => result(x)
```

Then add to `.cfg`:
```
INVARIANTS
    MyNewProperty
```

## Best Practices

1. **Start Small**: Begin with small constant values, increase gradually
2. **Check Type Invariants First**: `TypeOK` catches many basic errors
3. **Use Symmetry**: Reduce state space by marking symmetric constants
4. **Bounded Model Checking**: Set reasonable bounds to make checking feasible
5. **Incremental Development**: Add properties one at a time
6. **Document Assumptions**: Use comments to explain design decisions

## Mapping to Code

These specifications guide implementation:

```cpp
// UniformWrapperPattern.tla → json_parser.cpp
class JsonParser {
    // State machine from TLA+ spec
    enum class State { Uninitialized, Initialized, Destroyed };
    State state_;
    
    void initialize() {
        assert(state_ == State::Uninitialized);  // From spec
        state_ = State::Initialized;
    }
    
    bool process() {
        assert(state_ == State::Initialized);    // From spec
        // Implementation
    }
};
```

## Advanced Topics

### Refinement Mapping
Map abstract spec to concrete implementation:
```tla
INSTANCE AbstractSpec WITH 
    abstractState <- ConcreteState,
    abstractOp <- ConcreteOp
```

### Liveness Under Fairness
Ensure progress assumptions:
```tla
Fairness == WF_vars(Action)  \* Weak fairness
Fairness == SF_vars(Action)  \* Strong fairness
```

### PlusCal Algorithm Language
Higher-level language that compiles to TLA+:
```tla
--algorithm Pattern {
    variables state = "init";
    {
        state := "initialized";
    }
}
```

## Resources

### Learning TLA+
- [Learn TLA+](https://learntla.com/) - Interactive tutorial
- [Practical TLA+](https://www.apress.com/gp/book/9781484238288) - Book by Hillel Wayne
- [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html) - By Leslie Lamport
- [TLA+ Examples](https://github.com/tlaplus/Examples) - Official examples repository

### Documentation
- [TLA+ Language Specification](https://lamport.azurewebsites.net/tla/summary.pdf)
- [TLC Model Checker Documentation](https://lamport.azurewebsites.net/tla/tlc.html)
- [Specifying Systems Book](https://lamport.azurewebsites.net/tla/book.html) - Free PDF

### Community
- [TLA+ Google Group](https://groups.google.com/g/tlaplus)
- [TLA+ Discord Server](https://discord.gg/tlaplus)
- [/r/tlaplus](https://www.reddit.com/r/tlaplus/) - Reddit community

## Troubleshooting

### "Out of Memory" Errors
```bash
# Increase Java heap size
java -Xmx4g -cp tla2tools.jar tlc2.TLC ...
```

### State Space Explosion
- Reduce constant values
- Add symmetry constraints
- Use state constraints
- Check subsets of properties

### Long Check Times
- Use multiple workers: `-workers 8`
- Enable simulation mode: `-simulate`
- Reduce depth: `-depth 20`

## Contributing

When adding new design patterns:

1. Create `.tla` specification file
2. Create corresponding `.cfg` configuration
3. Document key properties
4. Add examples mapping to code
5. Update this README

## Related Documentation

- [ARCHITECTURAL_PATTERNS.md](../ARCHITECTURAL_PATTERNS.md) - Design patterns overview
- [DESIGN_PATTERN_ENFORCEMENT.md](../DESIGN_PATTERN_ENFORCEMENT.md) - Validation tooling
- [README.md](../README.md) - Project overview

---

**Note**: These specifications are living documents. As patterns evolve and new edge cases are discovered, specifications should be updated to reflect the refined understanding.
