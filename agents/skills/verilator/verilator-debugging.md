---
name: verilator-debugging
description: Debug Verilator issues - AST dumps, --dumpi-* flags, JSON AST, graphviz, reproduce minimal tests
---

# Verilator Debugging Skill

## Debugging Workflow

1. **Reproduce minimally** - reduce test to smallest SystemVerilog that triggers the issue
2. **Dump AST** at relevant pass - see flags below
3. **Inspect generated C++** - find where behavior diverges
4. **Check V3Stats** for pass counts / complexity
5. **Bisect** with `git log` if regression

## AST Dump Flags

```bash
# Dump AST after a specific pass (9 = highest verbosity)
verilator --dumpi-tree 9 --dumpi-V3Width 9 test.v
verilator --dumpi-V3Sched 9 test.v
verilator --dumpi-V3AssertPre 9 test.v

# Dump AST before/after a pass
verilator --dumpi-tree 9 --dumpi-V3Width 9 test.v   # After V3Width

# JSON AST dump (for programmatic inspection)
verilator --dumpi-tree-json 9 --no-json-ids test.v

# Debug emit Verilog (compare generated model vs source)
verilator --debug-emitv --dumpi-V3EmitV 9 test.v

# Stats output
verilator --stats-vars test.v

# Combined debug
verilator --debug --dumpi-tree 9 test.v
```

## Graphviz Output

```bash
# Generate DFG graph (data flow graph)
verilator --dumpi-dfg 9 test.v   # Produces .dot files

# View with:
dot -Tsvg dfg.dot -o dfg.svg
```

## Reproduce Minimal Test

```systemverilog
// test_regress/t/t_<feature>_debug.v - minimal reproducer
module t;
   // Smallest construct that triggers the bug
endmodule
```

```python
# test_regress/t/t_<feature>_debug.py
import vltest_bootstrap
test.lint(v_flags2=["--debug", "--dumpi-tree", "9", "--dumpi-V3Width", "9"])
test.passes()
```

## Common Debug Scenarios

| Symptom | Where to Look | Flag |
|---------|--------------|------|
| Type/width wrong | After V3Width | `--dumpi-V3Width 9` |
| Name resolution error | After V3LinkDot | `--dumpi-V3LinkDot 9` |
| Assertion fails silently | After V3AssertPre | `--dumpi-V3AssertPre 9` |
| Scheduling wrong | After V3Sched | `--dumpi-V3Sched 9` |
| Wrong C++ emitted | After V3EmitC | `--dumpi-V3EmitC 9` |
| Generated model crashes | Runtime | `include/verilated*.cpp` + gdb |

## V3Stats Debugging

```cpp
// In a pass: add stats to track counts
V3Stats::addStat("pass_name", "metric", count);

// Run with --stats-vars to see all stats
// Look for:
// - Unexpected O(n^2) growth (pass runs too many times)
// - Memory leaks (deferred delete not working)
// - Incorrect constant folding
```

## Minimal Reproducer Checklist

- [ ] Removed all unrelated modules/interfaces
- [ ] Reduced to single failing construct
- [ ] Added `--debug --dumpi-tree 9` to driver
- [ ] Confirmed bug reproduces with minimal test
- [ ] Filed issue with minimal test attached

## GDB / LLDB Setup

```bash
# Build with debug symbols
autoconf && ./configure --enable-ccwarn --enable-debug && make -j8

# Run under gdb
gdb --args ./bin/verilator --cc test.v

# Common breakpoints
break AstNode::dump
break V3Width::visit
break V3EmitC::emit
```

## Token Efficiency

- Use `--dumpi-<Pass>` to target one pass, not full tree dump
- JSON dumps for grep/sed analysis of specific node types
- Graphviz only when structure matters (DFG, scheduling)