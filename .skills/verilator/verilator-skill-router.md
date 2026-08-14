---
name: verilator-skill-router
description: Automatic skill routing for Verilator tasks - ensures AI agents invoke the right skills based on task type. ALWAYS use this skill first when working on Verilator.
---

# Verilator Skill Router

## MANDATORY: Invoke This Skill First

**Every Verilator task starts here.** This skill routes you to the exact skills needed for your task.

---

## Task -> Skill Mapping

| If Your Task Is... | Invoke These Skills (In Order) |
|--------------------|--------------------------------|
| **New to Verilator / Cold start** | `verilator-onboarding` -> `verilator-architecture` -> `verilator-coding-conventions` |
| **Add new SystemVerilog feature** | `verilator-onboarding` -> `verilator-architecture` -> `verilator-coding-conventions` -> `verilator-examples` (Ex 1, 2) |
| **Fix type/width bug** | `verilator-architecture` (V3Width) -> `verilator-coding-conventions` (dtype rules) -> `verilator-examples` (Ex 6) |
| **Fix assert/property/cover bug** | `verilator-architecture` (V3Assert*) -> `verilator-coding-conventions` -> `verilator-examples` |
| **Fix scheduling/NBA/fork bug** | `verilator-architecture` (V3Sched) -> `verilator-performance` (scheduler) -> `verilator-examples` |
| **Fix parser/syntax bug** | `verilator-architecture` (parser) -> `verilator-coding-conventions` (parser rules) |
| **Wrong generated C++** | `verilator-architecture` (V3EmitC*) -> `verilator-coding-conventions` (emit rules) |
| **Runtime crash / wrong simulation** | `verilator-runtime` -> `verilator-testing` |
| **Add new warning/diagnostic** | `verilator-coding-conventions` (diagnostics) -> `verilator-examples` (Ex 4) -> `verilator-testing` |
| **Optimize slow pass / memory** | `verilator-performance` -> `verilator-performance-guard` -> `verilator-examples` (Ex 5) |
| **Fix VPI / coverage / trace** | `verilator-runtime` -> `verilator-testing` |
| **Prepare PR for submission** | `verilator-pr-review` (FULL checklist) |
| **Review/verify existing change** | `verilator-pr-review` -> `verilator-performance-guard` |
| **Find function/class to edit** | `verilator-code-map` -> `verilator-architecture` |

---

## Automatic Invocation Rules

**ALWAYS invoke `verilator-skill-router` first** - it tells you exactly which skills to read.

**Then invoke each routed skill in order** before writing any code.

**Before ANY commit**, invoke `verilator-performance-guard` and `verilator-pr-review`.

---

## Keyword Auto-Trigger Rules

When a task mentions these keywords, the corresponding skills are automatically relevant (in addition to the task-based mapping above):

| Keywords | Skills to Load |
|----------|----------------|
| warning, lint, diagnostic, v3warn, v3error, Unsupported | coding-conventions, testing |
| performance, slow, O(n^2), memory leak, optimize, V3Stats, deferred | performance, performance-guard |
| runtime, verilated, VPI, trace, coverage, simulation | runtime, testing |
| parser, syntax, grammar, verilog.y, verilog.l, lexer | architecture, coding-conventions |
| assert, property, sequence, cover, V3Assert, SVA, NFA | architecture, coding-conventions, testing |
| schedule, NBA, fork, delay, V3Sched, V3Timing, V3Fork | architecture, performance, testing |
| debug, dump, dumpi, AST dump, graphviz, reproduce | debugging, testing |
| release, version, tag, Changes, ccwarn, longtests | release |
| VPI, vpi, callback, verilated_vpi | vpi, runtime |

**Rule:** If ANY keyword matches, the router confirms these skills should be loaded.

---

## Quick Reference Card

```
SYMPTOM -> START HERE
----------------------------------------------
Type/width error              -> V3Width.cpp
Name/scope/parameter          -> V3LinkDot.cpp, V3Param.cpp
randomize/constraint          -> V3Randomize.cpp
assert/property/cover         -> V3Assert*.cpp
fork/delay/NBA/scheduling     -> V3Sched.cpp, V3Timing.cpp
Syntax accept/reject          -> verilog.y, verilog.l
Wrong generated C++           -> V3EmitC*.cpp
Runtime behavior              -> include/verilated*.h/.cpp
Slow verilation               -> performance (O(n^2) patterns)
Memory leak                   -> performance-guard (deferred delete)
New diagnostic                -> coding-conventions (diagnostics)
Prepare PR                    -> pr-review (checklist)
```

---

## How to use

1. Read this router once -- it points you to the right skill for your task.
2. Read only the routed skills, not all of them.
3. Copy patterns from `verilator-examples` rather than re-deriving.

These skills are optional tooling for AI agents. They do not change how
Verilator is built or reviewed, and the broader project is unaffected if an
agent ignores them.