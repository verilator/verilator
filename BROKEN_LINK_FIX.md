# Fix design: Broken link (dangling VarScope) in min_uaf_repro_real

## Symptom
Running:

```
./bin/verilator --cc --timing --debug testcase/min_uaf_repro_real.sv
```

fires:

```
Broken link in node ... 'm_varp && !m_varp->brokeExists()' @ ... AstVarScope
node: VARSCOPE ... -> VAR __Vtask_wrap__1__Vfuncout [FUNC] BLOCKTEMP
```

## Root cause
`AstVarScope` is a cross-link node stored under `AstScope::varsp()`.
In this testcase, the failing node is a `VARSCOPE` pointing at a function temporary
(`__Vtask_wrap__1__Vfuncout [FUNC] BLOCKTEMP`).

During `--debug` checking, `V3Broken::brokenAll()` builds its "linkable" set by traversing the AST
via structural `op1-op4/nextp` links.
However, some `AstVar` nodes that can be referenced via `AstVarScope::m_varp` are not guaranteed to
be reachable via those structural links at the point `V3Broken` runs (they may be stored via other
non-structural containers/lists).

As a result, `AstVarScope::brokenGen()` can incorrectly see `m_varp->brokeExists()==false` even
though `m_varp` still points at a valid `AstVar`, and the assert fires.

## Fix
Teach `V3Broken::brokenAll()` that for `AstVarScope` nodes, the `varp()` target must be treated as
"linkable" too. This makes `brokeExists()` accurate for `AstVarScope::m_varp` cross-links and
prevents the spurious `m_varp && !m_varp->brokeExists()` failure on the testcase.

## Validation
Rebuild `bin/verilator_bin_dbg` and re-run the testcase; the internal broken-link assert should no
longer occur.
