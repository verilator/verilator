---
name: verilator-coding-conventions
description: Verilator C++ coding standards: style, AST manipulation, visitors, errors/warnings, performance, thread safety
---

# Verilator Coding Conventions Skill

## Code Style (enforced by `make format`, `make cppcheck`, `make lint-py`)

### Variables & Types
```cpp
// Mark everything const where possible
int const value = 42;
AstVar* const varp = nodep;           // Pointer: p suffix, doubly const
const AstNode* nodep;                 // Non-pointer: never use p suffix

// No auto except iterators or genuinely unwieldy types
for (auto it = map.begin(); it != map.end(); ++it)  // OK

// Pre-increment
++i;  // not i++

// Brace-initialize
new AstIf{fl, condp, thenp, elsep};

// No C-style casts
static_cast<T>(ptr);      // Non-AST types
VN_AS(nodep, Type);       // AST downcasts (when impossible to be wrong)
VN_CAST(nodep, Type);     // AST conditional casts (preferred)
```

### Constants & Enums
```cpp
static constexpr int MAX_DEPTH = 100;  // Not #define or file-scope const

// Every class/struct: final or VL_NOT_FINAL
class MyClass final { ... };
struct MyStruct VL_NOT_FINAL { ... };  // Distribution test scans all
```

### Functions & Headers
- Keep functions <=100-150 lines; thread state through context struct
- Move implementation to `.cpp`; convert large lambdas -> named member functions
- Every new `.cpp` starts with top-of-file algorithm comment
- Comments: capitalized sentences, no "I/we/our", remove dead code
- No `using namespace`; prefix non-namespaced with `VL`/`Vl`

### Naming
```cpp
// Compiler temporaries: __V prefix + context suffix
__VInside, __VCase

// Runtime utilities: vl_ prefix
vl_print_warn_error()

// Semantic predicates over enum comparisons
varp->isClassMember()    // NOT varp->varType() == VVarType::MEMBER

// new* = returns new object; make* = does something more complex
```

### AST Construction Rules
```cpp
// Build logic as AST nodes, NEVER raw C text in AstCStmt
// Later passes (V3Name, --protect) rename AST identifiers but can't see into strings

// Always use skipRefp() when comparing/resolving dtypes - missing it breaks typedefs
dtypep->skipRefp()

// Use V3Number arithmetic for AstConst > 32 bits
V3Number result = num1 + num2;  // NOT 1 << i (overflows at i >= 32)

// Use FileLine::operatorCompare for source-position ordering
if (fl1.operatorCompare(fl2) < 0)  // NOT hand-rolled filename/lineno

// Identify compiler-generated constructs by attribute flag (with dump support)
// NEVER by name-pattern matching - magic names break with escaped identifiers

// Use VMemberMap/findMember() for name lookups - O(1) vs quadratic

// Never allocate AstNode on stack or by value - always pointers

// Prefer new visit() in existing visitor over nodep->foreach(...)
// Better for runtime, handles diverse types, preserves traversal order

// Prefer AstForeach over unrolled loop bodies - O(1) code size vs O(N)
// Wrap body in AstBegin for scope isolation

// Pointers to nodes outside op1p-op4p -> broken() override + cloneRelink()
// Avoid when possible

// Every new AST member needs dump() AND dumpJson() - never LCOV_EXCL
// Override isSame() to include new semantically meaningful fields
```

## Visitor/Pass Rules

```cpp
// VL_RESTORER on EVERY member a visit() modifies before iterating children
VL_RESTORER(m_someState);

// Every pass using userNp() needs VNUser1InUse/VNUser2InUse/etc. guard, header documents which fields

// Use iterateAndNextNull() not iterate() - null-safe, prevents refactor bugs

// Derive read-only visitors from VNVisitorConst with iterateChildrenConst

// Reset per-module state in visit(AstNodeModule*) - including numeric ID counters

// Capture first-occurrence module state inside node's own visit()
// NOT via foreach pre-scan - source order matches IEEE declaration-before-use

// Avoid backp() - returns parent or prior sibling, causes O(n^2) hunts
// Build maps or capture context during forward traversal

// When raw node pointers key a map/set, erase entries when node deleted
// Allocators reuse addresses -> stale entries alias new nodes

// Derive graph-shaped passes from V3Graph - free dump, color, rank, topo sort
```

## Errors & Warnings (Diagnostic API Choice Determines Required Test)

| API | Output | Meaning | Required Test |
|-----|--------|---------|---------------|
| `v3error("...")` | `%Error:` | User wrote invalid SystemVerilog | `t_*_bad*.v` + `.out` golden |
| `v3error("Unsupported: ...")` | `%Error-UNSUPPORTED:` | Legal SV not yet supported | `t_*_unsup*.v` + `.out` golden |
| `v3warn(CODE, "...")` | `%Warning-CODE:` | Legal but suspicious | Warning test + `.out` golden |
| `v3fatalSrc("...")` | `%Error: Internal Error` | Should-never-happen assertion | None - not user-triggerable |

### Diagnostic Rules
```cpp
// Every v3error/v3warn needs test in test_regress/t/ - enforced by warn-coverage test
// "Unsupported:" ONLY for not-yet-implemented features, NEVER for user mistakes
// Spec restriction? Cite clause: IEEE 1800-2023 11.4.7
// Update docs/guide/warnings.rst when adding/changing warnings
// On error paths: clean up/replace invalid AST (e.g., AstConst::BitFalse) so later passes don't crash

// User-facing names: nodep->prettyNameQ() - use name() only in debug/UINFO
// Enclose values in single quotes: 'value'
// End messages with periods, never exclamation marks
// Don't write "Error:" in text - macro prints prefix
// State what was attempted and what was found:
//   "Instance attempts to connect to 'PARAM' as a parameter, but it is a variable"
// Add warnMore() suggestion where possible

// Warning codes: object-first and short (ASCRANGE not RANGEASC)
// Rename via renamedTo() so old suppressions keep working
// Set warning suppression on AstVar, not AstVarRef - VarRefs recreated, lose warnIsOff
// "Unsupported:" messages: specific unsupported context, not just construct name
// When replacing/refactoring a pass, KEEP existing error strings - .out goldens/docs depend on wording
```

## Performance & Memory

```cpp
// O(n^2) NEVER acceptable - build maps for batch lookups
// Any quadratic loop needs explicit justification in comment

// std::map for per-module structures (many small instances)
// unordered_map ONLY for one-per-netlist data
// NEVER let unordered_* iteration order reach generated output

// Prefer emplace over insert; check returned .second instead of separate find()
// reserve() strings/vectors when size estimable

// NO new static/global mutable data - statics being eliminated for future parallelism

// Use Verilator's fixed-width types for model data:
//   CData/SData/IData/QData/VlWide - NOT size_t
// Process wide data word-by-word: VL_ZERO_W, VL_MEMCPY_W - NEVER bit-by-bit

// No exceptions in verilated runtime code
// String parsing at verilation time, NEVER during simulation

// Wrap unlikely hot-path branches: VL_UNLIKELY / VL_LIKELY

// Count what every new pass does via V3Stats - stats become deterministic regression anchors
```

## Thread Safety

```cpp
// Annotate hierarchy: VL_PURE > VL_MT_SAFE > VL_MT_STABLE
// PURE = no side effects, calls only PURE
// MT_SAFE = safe under locks
// MT_STABLE = safe only while tree topology stable
// Annotations MUST match implementation

// Never include verilated.h in compiler - use verilatedos.h

// Mutex-protected members: VL_GUARDED_BY + document acquisition ordering
// ++ on shared state and container empty() are NOT thread-safe
```

## Parser/Lexer (verilog.y, verilog.l)

```cpp
// Preserve IEEE Appendix A BNF comments: // IEEE: {rule}
// Comment explicitly when accepting syntax beyond IEEE as extension

// Parser ONLY builds AST nodes - defer semantic validation to V3LinkParse/V3Width+

// Hierarchical paths = structured nodes (AstDot/parse-ref chains via idDotted)
// NEVER concatenated strings - preserves per-segment FileLine

// Tighten grammar rule's operand type over runtime cast-chain guard in later visitor
// Illegal operands then fail with clean syntax error

// Solve ambiguities with token-pipeline look-ahead (tokenPipeScan*)
// NOT by limiting grammar rules
// Mark unsupported rules with //UNSUP

// Sort token declarations alphabetically by string literal
// Sort yD_* productions by token name

// Add test for EVERY | alternative and optional clause of new/changed grammar rule
// Untested alternatives = where parse regressions hide
```

## File-Specific Rules

| File | Rule |
|------|------|
| `V3Options.cpp` | Chain `.notForRerun()` on `DECL_OPTION()` for options not affecting semantic output |
| `V3Ast.cpp` | Composite types (queues, dyn arrays): use `computeCastableImp()` on subtypes - shallow `width()`/`similarDType()` miss nested incompatibility |
| `V3AstNode*.h` | Every node class: what-construct comment; every member: semantic-purpose comment; enum types in `V3AstAttr.h` |
| `V3AstNodeExpr.h` | `CCast` ONLY for basic C types (char/short/int/QData) - NEVER 4-state logic or structs |
| `V3AstNodeOther.h` | `cloneRelink` must propagate all stateful flags (e.g. `maybePointedTo`) and update internal refs |
| `V3Const.cpp` | Check `keepIfEmpty` before removing empty functions - flagged funcs must survive for codegen/side effects |
| `V3Coverage.cpp` | Instrumentation contexts = opt-in (allowlist), NEVER blocklist - blocklists silently break when new contexts appear |
| `V3Inline.cpp` | Preserve `VarXRef::varp()` during passes - pin-reconnection needs it before V3LinkDot re-resolves |
| `V3Sched*.cpp` | Every change needs test proving necessity; isolate unrelated scheduler changes - high-risk area |