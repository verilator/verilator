<!-- DESCRIPTION: Verilator: src/ guidelines for AI coding agents
     SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
     SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0 -->

# src/ Coding Guidelines -- Verilator compiler sources

When to check: before editing any C++ source or header under `src/`, including astgen inputs and the parser/lexer (`verilog.y`, `verilog.l`).
Read the repository-root [AGENTS.md](../AGENTS.md) first for process and cross-cutting rules.

## Code style

- Mark every variable, parameter, and pointer `const` where possible -- one missing `const` found in review triggers a rescan of the whole change.

- Pointer variables take a `p` suffix and pointer locals are doubly const where possible: `AstVar* const varp` -- non-pointers must not use the `p` suffix; names describe content, not type.

- Do not use `auto` except for iterators or genuinely unwieldy types -- explicit types aid comprehension.

- Use pre-increment (`++i`), never post-increment -- faster for non-trivial types, always correct.

- Use brace initialization for all node and struct construction: `new AstIf{fl, condp, thenp, elsep}` -- not parentheses.

- No C-style casts -- use `static_cast<T>` for non-AST types and `VN_AS`/`VN_CAST` for AST downcasts.

- Use `static constexpr` for compile-time constants -- not `#define` or file-scope `const`.

- Mark every `class`/`struct` `final` or `VL_NOT_FINAL` -- including nested and private helper structs; a distribution test scans all definitions.

- Keep functions under roughly 100-150 lines -- split larger ones into helpers with clear contracts; thread shared state through a context struct rather than long parameter lists.

- Keep headers lean: move implementation to `.cpp` files; convert large lambdas into named member functions or file-local `static` functions -- lambdas are opaque in stack traces and block reuse.

- Start every new `.cpp` file with a top-of-file comment explaining the algorithm.

- Use `//` line comments; write comments as capitalized sentences without "I"/"we"/"our" -- write for an unknown future reader.

- Use section markers in class declarations: `// MEMBERS`, `// CONSTRUCTORS`, `// METHODS`.

- Categorize visitor state comments: "STATE - across all visitors", "STATE - Statistic tracking", "STATE - for current visit position (use VL_RESTORER)".

- Start continuation lines with the operator (`&&` at line start, not line end).

- No `using namespace` -- expand types where used; prefix non-namespaced symbols with `VL`/`Vl`.

- Prefer semantic predicates over enum comparisons: `varp->isClassMember()`, not `varp->varType() == VVarType::MEMBER` -- survives enum changes and reads as intent.

- Getter is the member name minus `m_`; setter is the same name taking an argument; a setter that only ever sets true uses a `set` prefix with no argument.

- `new*` functions return a `new` object; `make*` functions do something more complex -- pick the prefix accordingly.

- Use `T_`/`N_` prefixes for template type/value parameters (`T_Func`, `N_Depth`) -- distinguishes them from concrete types.

- Name compiler-created temporaries with a `__V` prefix plus a context suffix (`__VInside`, `__VCase`), no redundant "Tmp"; use a `vl_` prefix for runtime utility functions.

- Use `VL_*` macros from `verilatedos.h` (`VL_WORDS_I`, `VL_MASK_I`, `VL_BIT`) for bit/word math -- no hand-rolled shifts; do not include `<cstdint>` directly, `verilatedos.h` provides it.

- Use the `"text"s` literal suffix for `std::string` concatenation chains -- cleaner than multi-line `+=` sequences.

- Wrap multi-statement macros in `do { ... } while (0)` -- single-statement behavior in all control-flow contexts.

- Convert pointers to integers via `uintptr_t`: `static_cast<uint64_t>(reinterpret_cast<uintptr_t>(p))` -- portable across 32/64-bit platforms.

- Preserve `splitCheck()` in emit code paths for functions that can grow arbitrarily large -- a build safeguard against oversized generated code; refactor around it, never remove it.

- Extract a shared helper when two flows build the same logical structure -- parallel implementations drift and create omission bugs.

- Remove commented-out code -- version control preserves history.

- Replace magic numbers with named `static constexpr` constants for thresholds, limits, and weights -- self-documenting and centrally tunable.

## AST construction and manipulation

- Build logic as AST nodes, never as raw C text in `AstCStmt` -- later passes (V3Name, `--protect`) rename AST identifiers but cannot see into raw strings.

- Know the three cast forms and their null-safety: `VN_IS` returns false for nullptr, `VN_CAST` returns nullptr on mismatch, `VN_AS` asserts the type. Never pair `VN_IS` with `VN_AS` on the same node -- use a single `VN_CAST`:

  ```cpp
  // BAD: redundant double check
  if (VN_IS(nodep, VarRef)) { AstVarRef* const refp = VN_AS(nodep, VarRef); }
  // GOOD: single conditional cast
  if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) { ... }
  ```

- Trust tree invariants: `dtypep()`, `subDTypep()`, `varp()` results are never null after the resolving pass -- defensive null checks for impossible cases hide bugs and create uncoverable code; V3Broken validates the tree.

- Use `UASSERT_OBJ(cond, nodep, "...")` over `UASSERT` whenever a node is in scope -- the node supplies the error location; pass the condition directly, never `UASSERT_OBJ(false, ...)` inside an `if`.

- Use `v3fatalSrc("...")` for unreachable code paths -- never a silent `if (!ptr) return;`.

- Use `VL_DO_DANGLING(pushDeletep(nodep), nodep)` instead of `deleteTree()` in visitors -- deferred deletion is safe against re-entry and unlinking order, and keeps nodes visible for debugging; `deleteTree()` only for fresh nodes that never entered the tree.

- Every new AST member variable needs both `dump()` and `dumpJson()` support -- never wrap these in `LCOV_EXCL`; cover them naturally by adding a construct exercising the node to the tree-dump test (`test_regress/t/t_debug_emitv.v`), which dumps every node at every stage.

- Override `isSame()` to include any new semantically meaningful field added to a node.

- Let astgen generate child accessors via `@astgen op` annotations -- do not write manual accessors; use `@astgen ptr` (with `Optional[_]` for nullable) for cross-node pointers instead of hand-coded `brokenGen`/`cloneRelinkGen`; make generated virtual methods abstract (`= 0`), not empty defaults.

- Pointers to nodes outside op1p-op4p require a `broken()` override and `cloneRelink()` support -- avoid storing out-of-tree node pointers when possible.

- When caching derived data on AST nodes, add a `broken()` check that recomputes and verifies the cache.

- Never allocate AstNode objects on the stack or by value -- always pointers; leak checking complains otherwise.

- `AstSelBit` exists only during parse -- later passes use `AstArraySel`/`AstSel`.

- Use `nodep->foreach(...)` for simple traversals and named accessors (`lhsp()`, `fromp()`) over `op1p()`..`op4p()` -- but verify traversal order is preserved when converting manual iteration.

- `addNext()` walks to the list tail itself -- do not pre-walk `nextp()` chains before calling it.

- Prefer `AstForeach` over generating unrolled loop bodies for array iteration -- constant-size generated code instead of O(N), uniform across array types; wrap the body in `AstBegin` for scope isolation.

- Always `skipRefp()` when comparing or resolving dtypes -- missing it breaks typedef support; prove the paths with typedef tests.

- Use `num().isOpaque()` rather than spelling out `isDouble() || isString()` when guarding V3Number comparisons against non-integer types.

- Use `FileLine::operatorCompare` for source-position ordering -- never hand-roll filename/lineno comparisons; it covers file, line, column, last-line, and last-column.

- Prefer a virtual `isSomething()` predicate on the base node class over long `VN_IS(x, A) || VN_IS(x, B) || ...` chains at call sites -- a single place to extend when subclasses are added.

- Never identify compiler-generated constructs by name-pattern matching -- add an attribute flag to the node (with dump/dumpJson support); magic-name matching breaks with escaped identifiers.

- Use `V3Number` arithmetic for `AstConst` values wider than 32 bits -- `1 << i` silently overflows at `i >= 32`.

- Use `VMemberMap`/`findMember()` for name lookups in structs, unions, classes, modules, and packages -- O(1) versus quadratic repeated linear scans.

- Never emit raw source filenames or identifiers in generated code -- pass them through `protect()`/`putsQuoted` so `--protect` mode does not leak source.

## Visitors and passes

- Use VL_RESTORER on every visitor member that a `visit()` modifies before iterating children -- even when nesting "cannot happen" today; nested classes/modules eventually appear and it documents intent.

- Every pass using `userNp()` needs a `VNUserNInUse` guard, and the visitor header documents which user fields it uses -- undeclared use causes silent cross-pass conflicts.

- Use `iterateAndNextNull()` rather than `iterate()` -- the null-safe form prevents copy-paste errors during refactors.

- Derive read-only visitors from `VNVisitorConst` and use `iterateChildrenConst` -- better performance when the tree is not modified.

- Visitors are algorithms: private constructor plus a static `apply()` entry point, class name prefixed with the source file name (`TimingSuspendableVisitor` in `V3Timing.cpp`).

- Reset per-module visitor state in `visit(AstNodeModule*)` -- including numeric ID counters, to keep generated names stable.

- Avoid `backp()` -- it returns parent or prior sibling depending on position, breaks on complex expressions, and causes O(n^2) hunts in loops; build maps or capture context during forward traversal.

- Capture first-occurrence module state inside the node's own `visit()` handler, not via a `foreach` pre-scan from `visit(AstNodeModule)` -- the visitor already walks every node, and source order matches IEEE declaration-before-use rules.

- When raw node pointers key a map or set, erase entries when the node is deleted -- allocators reuse addresses, so stale entries eventually alias new nodes.

- Derive graph-shaped passes from V3Graph (`V3GraphVertex`/`V3GraphEdge`) -- never roll your own Node/Edge classes; V3Graph provides dump, color, rank, topological sort, and reachability for free.

- When a change outgrows local rewrites, create a dedicated pass instead of growing an existing one -- keeps pass invariants clear and reduces coupling regressions.

- Do not overload established internal terminology for new concepts -- if a term has a stable meaning (e.g. "pre" triggers in the scheduler), pick a distinct name.

- State explicitly how side effects are preserved in optimizations involving purity, expression lifting, or simplification -- purity assumptions for functions, DPI, and methods are easy to misclassify.

- Use `forall` only for simple predicates -- it is cheaper than a visit-everything visitor but more expensive than a visitor that can shortcut subtrees.

- Avoid global numbering or shared mutable state when a module-local or pass-local alternative exists -- global coupling amplifies diff noise and is harder to reason about.

- Leave explicit comments at the contract points where astgen or other generated metadata drives runtime behavior -- missing registration silently degrades type safety.

## Errors and warnings

- Append `nodep->prettyNameQ()` for user-facing names; use `name()` only in UINFO/debug output -- users see pretty names, `.tree` debuggers see internal ones.

- Enclose specific values and variable names in single quotes: `'value'`.

- End messages with periods, never exclamation marks; do not write "Error:" in the text -- the macro already prints the prefix.

- Include a suggestion via `warnMore()` where possible (e.g. "Suggest use 'function automatic'"); the first location uses `warnContextPrimary()`, later ones `warnContextSecondary()`.

- State what was attempted and what was found: "Instance attempts to connect to 'PARAM' as a parameter, but it is a variable".

- Reference named constants or option names in messages, not magic numbers; capitalize acronyms (UDP, not udp); use formal modal verbs (must/must not).

- Name warning codes object-first and short (`ASCRANGE`, not `RANGEASC`); rename via `renamedTo()` so old suppressions keep working; when splitting a warning, keep the old name as a meta-control.

- Set warning suppression on `AstVar`, not `AstVarRef` -- VarRefs get recreated and lose `warnIsOff`.

- `v3warn` checks `warnIsOff` internally -- no redundant guard needed.

- User errors use `v3error` (non-fatal), not `v3fatal`; move fatal aborts out of visitors to the top level so AST dumps still occur on failure.

- "Unsupported:" messages must describe the specific unsupported context ("Unsupported: sequence referenced outside assertion property"), not just the construct name -- each message must be distinct.

- New warnings must not fire on previously-clean parameterized code -- constant-folded loops should not trigger lint; over-permissive suppression beats false positives, and survey other tools before adding a warning.

- Internally constructed AST that uses warning-prone language features must suppress its own warnings via `fileline()->warnOff(...)`.

- Never call bare `abort()` -- print a searchable message first (`vlAbortOrExit()`); mark unreachable code `VL_UNCOVERABLE`.

- Defer `abortIfErrors()` to pipeline exit points, not after every operation -- users see all errors in one compile attempt.

- When an assertion fires, fix the root-cause initialization -- never weaken the assertion.

- When replacing or refactoring a pass, keep existing user-facing error strings (or provide direct equivalents) -- `.out` goldens and user documentation depend on the wording.

## Performance and memory

- O(n^2) is never acceptable -- build maps for batch lookups instead of per-item scans; any quadratic-looking loop needs explicit complexity justification in comments.

- Prefer `std::map` for per-module structures (many small instances) -- older libc++ allocates dozens of KB per unordered container; use `unordered_map` only for one-per-netlist data.

- Never let `unordered_*` iteration order reach generated output -- for stable deduplication use an `unordered_set` for membership plus a `vector` for order, pushing only on successful insertion.

- Prefer `emplace` over `insert`; check the returned `.second` instead of a separate `find()` -- avoids double lookups.

- `reserve()` strings and vectors when the size is estimable.

- Add no new static or global mutable data -- statics are being eliminated for future parallelism.

- Process wide data word-by-word (`VL_MEMSET_W`, `VL_MEMCPY_W`), never bit-by-bit or byte-by-byte loops -- compilers do not optimize byte-wise sign fill.

- No exceptions in verilated runtime code -- use error returns or assertions; exceptions add overhead.

- Move string parsing to verilation time -- never parse strings during simulation; emit structured data or compile-time hints instead.

- Do not add vtables to high-frequency runtime objects (8 bytes per instance); guard optional runtime features behind `hasClasses()`/`hasEvents()`-style checks.

- Functions called per-cycle must avoid mutexes -- use atomics or lockless designs.

- Each full-netlist visitor costs minutes on large designs -- merge visitors where possible, or collect into vectors and process afterwards.

- Count what every new pass does via V3Stats -- stats become deterministic regression anchors in tests.

- Use Verilator's data types for model data (`CData`/`SData`/`IData`/`QData`/`VlWide`), not `size_t` -- fixed widths across platforms; `size_t` only answers "how big is this container".

- Emit no runtime loops in generated C++ -- either expand loops at verilation time or call a single runtime function.

- Wrap unlikely hot-path branches (error checks, bounds checks) in `VL_UNLIKELY`/`VL_LIKELY` -- guides the compiler to optimize the common case.

- Use generation counters (alongside `user*` fields) to invalidate caches instead of clearing them between passes.

- Reducing memory footprint often beats reducing instruction count -- smaller per-element data wins through cache effects.

- The `inline` keyword alone does nothing for member functions defined in headers -- use `VL_ATTR_ALWINLINE` where forced inlining matters, and weigh macro versus function overhead in `-O0` debug builds.

## Thread safety

- Annotate with the three-level hierarchy `VL_PURE` > `VL_MT_SAFE` > `VL_MT_STABLE` -- VL_PURE has no side effects and may call only VL_PURE; VL_MT_SAFE is safe under locks; VL_MT_STABLE is safe only while tree topology is stable; VL_MT_SAFE must not call VL_MT_STABLE.

- Annotations must match the implementation -- a function that calls non-safe functions cannot itself be marked safe.

- Never include `verilated.h` in the compiler itself -- use `verilatedos.h` or create a new header.

- Annotate mutex-protected members with `VL_GUARDED_BY` and document mutex acquisition ordering -- prevents priority inversion.

- `++` on shared state and `empty()` on standard containers are not thread-safe -- use atomics or hold the lock.

- `_exit()` is acceptable only from non-main threads in multithreaded mode; the main thread and single-threaded code use `std::exit()`, and dump gcov on any non-exit termination path.

- Prefer has-a over is-a for thread-safe classes: a guarded class wrapping the unguarded internal one, with the guarded version as the default public API.

## Parser and lexer (verilog.y, verilog.l)

- Preserve IEEE Appendix A BNF comments (`// IEEE: {rule}`) mapping grammar rules to the standard; explain any split/combined rules, and comment explicitly when accepting syntax beyond IEEE as an extension.

- The parser only builds AST nodes: defer semantic validation, `VN_IS` checks, and context-dependent logic to V3LinkParse/V3Width and later passes.

- Represent hierarchical paths as structured nodes (`AstDot`/parse-ref chains via the existing `idDotted` production), never concatenated strings -- preserves per-segment FileLine.

- Prefer tightening a grammar rule's operand type over a runtime cast-chain-plus-`v3fatalSrc` guard in a later visitor -- illegal operands then fail with a clean syntax error; the visitor guard becomes defense-in-depth.

- Solve ambiguities with token-pipeline look-ahead (`tokenPipeScan*`) rather than limiting grammar rules; name tokens for semantic meaning, not one syntax case.

- Mark unsupported grammar rules with the `//UNSUP` comment convention.

- Extract repeated grammar action sequences into helper functions in `V3ParseGrammar` at the top of `verilog.y`.

- Format grammar rules with the opening `{` at column 56 for short rules, column 24 for long rules, contents indented two more spaces -- match surrounding rules.

- Keep lexer rules matching only semantic token content, excluding trailing whitespace; when adding lexer states or tokens, update every cross-cutting section (comments, preprocessor directives, `/*verilator*/` meta-comments).

- Sort token declarations alphabetically by string literal; sort `yD_*` productions by token name.

- `m_modp` can be null on parse errors, and nested modules break simple tracking -- assert non-null via helpers that carry fileline context.

- Add a test for every `|` alternative and optional clause of a new or changed grammar rule -- untested alternatives are where parse regressions hide.

## File-specific rules

| File | Rule |
|---|---|
| `configure.ac` | Keep build-time flags (sanitizers, debug) orthogonal to runtime flags and document which is which -- tool-compile options and generated-code options must be independently controllable |
| `src/V3Options.cpp` | Chain `.notNeededForRerun()` onto `DECL_OPTION()` for options that do not affect semantic output -- rerun logic then skips them |
| `src/V3Ast.cpp` | For composite types (queues, dynamic arrays) use `computeCastableImp()` on subtypes -- shallow `width()`/`similarDType()` checks miss nested incompatibility |
| `src/V3AstNode*.h` | File DESCRIPTION names the node category; every node class gets a what-construct comment and every member (especially node pointers) a semantic-purpose comment; put enum type definitions in `V3NodeAttr.h`, not `V3AstNodeOther.h` |
| `src/V3AstNodeExpr.h` | `CCast` is only for basic C types (char/short/int/QData) -- never 4-state logic or structs |
| `src/V3AstNodeOther.h` | `cloneRelink` must propagate all stateful flags (e.g. `maybePointedTo`) and update internal references -- otherwise clones keep stale pointers into the original tree |
| `src/V3AstNodes.cpp` | Override `name()` in subclasses that store names or `.tree` dumps lose them; in JSON dumps store derived type properties (e.g. `width`) once on the dtype node, not per node |
| `src/V3Const.cpp` | Check `keepIfEmpty` before removing empty functions -- flagged functions must survive for codegen/linking/side effects |
| `src/V3Coverage.cpp` | Instrumentation contexts are opt-in (allowlist of known-safe contexts), never blocklist -- blocklists silently break when new contexts appear |
| `src/V3Inline.cpp` | Preserve `VarXRef::varp()` during passes -- intermediate pin-reconnection passes need it before V3LinkDot re-resolves |
| `src/V3LinkJump.cpp` | Track concurrent constructs (forks) path-sensitively with scope-local flags -- global flags over-conservatively block safe control-flow optimizations |
| `src/V3LinkLValue.cpp` | Propagate assignment attributes from original variables when processing aliases -- aliases are references, not new assignments |
| `src/V3Localize.cpp` | Mark scope-specific optimization restrictions on `AstVarScope`, not `AstVar` -- preserves per-scope granularity |
| `src/V3Sched*.cpp` | Every change needs a test proving necessity; isolate unrelated scheduler changes into separate PRs -- high-risk, hard-to-debug area |
| `src/V3SchedTrigger.cpp` | Name trigger eval helpers `_eval_triggers_{qualifier}__` (qualifier after "triggers") |
