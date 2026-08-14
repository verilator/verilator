---
name: verilator-code-map
description: Symptom-to-function map for efficient navigation - which function/class in which file handles each issue type
---

# Verilator Code Map

Quick reference: Symptom -> File -> Function/Class to Edit

## Type/Width Errors

| Symptom | File | Function/Class |
|---------|------|----------------|
| Type mismatch / width error | `V3Width.cpp` | `WidthVisitor::visit(AstVarRef*)`, `WidthVisitor::visit(AstNodeExpr*)` |
| Implicit conversion issue | `V3Width.cpp` | `WidthVisitor::computeCastableImp()` |
| Parameter array sizing | `V3Param.cpp` | `ParamVisitor::visit(AstVar*)`, `ParamVisitor::visit(AstNodeArray*)` |
| Typedef resolution | `V3Width.cpp` | `WidthVisitor::visit(AstNodeDType*)`, `dtypep()->skipRefp()` |

## Name/Scope/Parameter Resolution

| Symptom | File | Function/Class |
|---------|------|----------------|
| "Can't find module/signal" | `V3LinkDot.cpp` | `LinkDotVisitor::visit(AstDot*)`, `VMemberMap::findMember()` |
| Hierarchy resolution | `V3LinkDot.cpp` | `LinkDotVisitor::linkModule()`, `LinkDotVisitor::visit(AstModPort*)` |
| Parameter evaluation | `V3Param.cpp` | `ParamVisitor::visit(AstNodeParamAssign*)`, `ParamVisitor::evalParam()` |
| Scope lookup | `V3LinkParse.cpp` | `LinkParseVisitor::visit(AstScope*)`, `VMemberMap::findMember()` |

## Randomize/Constraint

| Symptom | File | Function/Class |
|---------|------|----------------|
| Randomize fails | `V3Randomize.cpp` | `RandomizeVisitor::visit(AstClass*)`, `newRandomizeFunc()` |
| Constraint solver | `V3Randomize.cpp` | `RandomizeVisitor::addConstraints()`, `V3Randomize::solve()` |
| rand/randc variables | `V3Randomize.cpp` | `RandomizeVisitor::visit(AstVar*)`, `isRand()` |

## Assert/Property/Cover

| Symptom | File | Function/Class |
|---------|------|----------------|
| Assert property error | `V3Assert.cpp` | `AssertVisitor::visit(AstAssert*)`, `assertAll()` |
| Assert preprocessing | `V3AssertPre.cpp` | `AssertPreVisitor::visit(AstAssert*)`, `preprocessAssert()` |
| NFA construction | `V3AssertNfa.cpp` | `NfaVisitor::visit(AstAssert*)`, `buildNFA()` |
| SVA sequence | `V3AssertNfa.cpp` | `NfaSequence::compile()`, `NfaState::transition()` |
| Covergroup/coverpoint | `V3AssertPre.cpp` | `AssertPreVisitor::visit(AstCovergroup*)` |

## Scheduling/NBA/Fork

| Symptom | File | Function/Class |
|---------|------|----------------|
| Schedule/NBA bug | `V3Sched.cpp` | `SchedVisitor::visit(AstNodeStmt*)`, `scheduleAll()` |
| Fork/join handling | `V3Fork.cpp` | `ForkVisitor::visit(AstFork*)`, `ForkVisitor::processFork()` |
| Timing/delay | `V3Timing.cpp` | `TimingVisitor::visit(AstDelayControl*)` |
| Event scheduling | `V3Sched.cpp` | `SchedVisitor::insertEvent()`, `V3Sched::processEvents()` |

## Parser/Syntax

| Symptom | File | Function/Class |
|---------|------|----------------|
| Syntax accepted/rejected | `verilog.y` | Grammar rule for construct (search for keyword) |
| Lexer token issue | `verilog.l` | Flex rule for token (search for keyword) |
| Precedence wrong | `verilog.y` | `%left`/`%right`/`%nonassoc` sections |
| //UNSUP needed | `verilog.y` | Add `error` production + `v3error("Unsupported: ...")` |
| Token look-ahead | `verilog.y` | Use `tokenPipeScan*()` in grammar action |

## Wrong Generated C++

| Symptom | File | Function/Class |
|---------|------|----------------|
| Function emission | `V3EmitCFunc.cpp` | `EmitCInlines::visit(AstFunc*)`, `emitFunc()` |
| Module emission | `V3EmitCMain.cpp` | `EmitCMain::visit(AstModule*)`, `emitModule()` |
| Statement emission | `V3EmitCImp.cpp` | `EmitCBaseVisitorConst::visit(AstNodeStmt*)`, `emitStmt()` |
| Expression emission | `V3EmitCImp.cpp` | `EmitCBaseVisitorConst::visit(AstNodeExpr*)`, `emitExpr()` |

## Runtime/Simulation

| Symptom | File | Function/Class |
|---------|------|----------------|
| Runtime crash | `include/verilated.cpp` | `Verilated::eval()`, `Verilated::eval_step()`, `Verilated::trace()` |
| VPI callback | `include/verilated_vpi.cpp` | `vlog_startup_routines_bootstrap()`, `vpi_register_cb()` |
| Coverage/trace | `include/verilated.cpp` | `Verilated::internalsDump()`, `Verilated::commandArgs()` |
| Model evaluation | `obj_dir/V<mod>___024root.cpp` | `eval()`, `eval_step()`, `eval_initial()`, `eval_final()` |

## Performance/Memory

| Symptom | File | Function/Class |
|---------|------|----------------|
| O(n^2) loop | Search in pass file | Look for nested `foreach` or `iterateChildren` -- replace with `VMemberMap` |
| Memory leak | `V3Dead.cpp` | `DeadVisitor::cleanup()`, `maybePointedTo()` check |
| Deferred delete | Pass file | Use `VL_DO_DANGLING(pushDeletep(nodep), nodep)` instead of `deleteTree()` |
| Static mutable data | Any file | Remove `static`/`global` -- use `VL_RESTORER` for thread-local state |

## Key Patterns to Search

```bash
# Find pass entry point
grep -n "void.*::apply\|static void.*apply" src/V3*.cpp

# Find visitor for node type
grep -n "visit(AstNodeType" src/V3*.cpp

# Find where warning is emitted
grep -rn "v3warn.*WARNCODE" src/

# Find where error is emitted
grep -rn "v3error" src/

# Find option handling
grep -rn "DECL_OPTION" src/V3Options.cpp
```

## Quick Navigation

```
Pass registration: src/Verilator.cpp -> process() -> pass list order
AST node dump: grep -rn "dump()" src/V3Ast.cpp
AST node clone: grep -rn "cloneRelink()" src/V3Ast.cpp
isSame override: grep -rn "isSame" src/V3Ast.cpp
```

## Token Efficiency

- Don't read entire pass -- search for `visit(AstNodeType*`
- Most fixes are 5-20 lines in one `visit()` method
- Tests in `test_regress/t/t_*_bad.v` + `.py` + `.out`