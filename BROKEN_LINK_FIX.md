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
In this testcase, `V3Task` creates statement-expression wrappers (`AstExprStmt`) that include a
temporary variable declaration (e.g. `__Vtask_wrap__1__Vfuncout [FUNC] BLOCKTEMP`) in the
`AstExprStmt::stmtsp()` list.

Later, `V3Const` simplifies certain `AstExprStmt` nodes by replacing the whole ExprStmt with its
`resultp()` and deleting the ExprStmt node. That deletes the `stmtsp()` subtree (including the
temporary `AstVar`), but the corresponding `AstVarScope` under the enclosing `AstScope` is not
removed.

This leaves a dangling `AstVarScope::m_varp` pointer and `V3Broken` correctly detects it.

## Fix
`V3Broken` only considers nodes reachable via the structural `op1-op4/nextp` AST links as
"linkable" targets. However, Verilator also has *member-pointer cross-links* (via `foreachLink`),
notably `AstVarScope::m_varp`, which can refer to valid nodes that are not necessarily reachable via
structural links.

Update `V3Broken::brokenAll()` so that when building the linkable set it also adds the targets of
`foreachLink` for every node in the main tree. This allows `brokeExists()` checks in `brokenGen()`
(e.g. `AstVarScope::brokenGen`) to succeed for valid cross-linked nodes.

## Validation
Rebuild `bin/verilator_bin_dbg` and re-run the testcase; the internal broken-link assert should no
longer occur.
