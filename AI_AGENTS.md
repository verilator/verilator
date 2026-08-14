# Verilator Skills Usage Guide

This document describes how to use the Verilator skills in `.skills/verilator/`.

## Skill Location

All Verilator skills live in one canonical location:

```
.skills/verilator/
```

## How to Use the Skills

Any coding tool or agent can use the skills by:

1. Reading `.skills/verilator/verilator-skill-router.md` first
2. Following the routing to other skills based on the task
3. The skills are plain Markdown — no tool-specific formatting required

## Quick Start

```bash
# From verilator repo root:

# 1. Read the router first
cat .skills/verilator/verilator-skill-router.md

# 2. Follow its routing for your task
```

## Skill Invocation

The router skill (`verilator-skill-router.md`) contains keyword triggers that map task types to the relevant skills. Tools that support skill invocation can reference the router directly; others can read the skill files as plain documentation.

## File Structure

```
.skills/verilator/
├── skills.yaml              # Skill manifest with triggers and dependencies
├── verilator-skill-router.md  # ALWAYS START HERE - routes task to skills
├── verilator-onboarding.md    # 5-minute mental model + quick start
├── verilator-architecture.md  # Pipeline, AST, visitors, passes
├── verilator-coding-conventions.md  # C++ style, AST rules, visitors, errors, performance
├── verilator-testing.md       # Test structure, drivers, goldens, naming
├── verilator-pr-review.md     # Maintainer feedback patterns, pre-PR checklist
├── verilator-performance.md   # Memory, O(n^2) elimination, compile vs runtime
├── verilator-performance-guard.md  # 10 mandatory performance gates (before commit)
├── verilator-runtime.md       # include/ library: C++14, fixed-width, threads
├── verilator-examples.md      # Worked examples: new pass, AST node, bug fix, warning
├── verilator-debugging.md     # Debug: AST dump, --dumpi-*, graphviz, reproduce
├── verilator-parser.md        # Lexer/grammar: verilog.y, verilog.l
├── verilator-release.md       # Release process checklist
├── verilator-code-map.md      # Symptom-to-function navigation map
├── verilator-vpi.md           # VPI module structure and callbacks
└── *.yaml                     # Per-skill metadata (optional)
```

The skills are optional reference material. They do not change how Verilator is built or reviewed.