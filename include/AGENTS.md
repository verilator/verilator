<!-- DESCRIPTION: Verilator: include/ guidelines for AI coding agents
     SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
     SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0 -->

# include/ -- Verilator runtime library

Covers the C++ runtime under `include/` (`verilated.h/.cpp`, `verilated_*.h/.cpp`)
that every generated model links against. Read the repository-root
[AGENTS.md](../AGENTS.md) first. The rules here differ from `src/`: this code
ships to users, runs every simulation cycle, and must stay portable and fast.

---

# Orientation

- **This is the runtime, not the compiler.** The passes in `src/` *emit* C++ that
  calls into this library; this code then *runs* during simulation. Optimize it
  for execution speed and portability, not for compile-time clarity.
- **Key files:** `verilated.h` (core model API), `verilated_types.h` (data
  types), `verilated_random.cpp` (constrained-random runtime), `verilated_cov.*`
  (coverage), `verilated_threads.*` (MT runtime), `verilated_timing.*`
  (`--timing` runtime), `verilated_vcd_c.*`/`verilated_fst_c.*` (tracing).
- A runtime-only fix lives entirely here and does not rebuild `verilator_bin`.

---

# Before you open a PR

- **C++14 baseline.** The runtime must build under `--no-timing` with C++14; C++20
  features are allowed only in `--timing` code paths.
- **Public API naming and docs.** Prefix public classes and types with
  `Verilated`/`Vl` to avoid collisions with user code, and document the API with
  `///` comments -- they feed doc generation.
- **No exceptions in runtime code** -- use error returns or assertions; exceptions
  add overhead on every path.
- **Use fixed-width model types** (`CData`/`SData`/`IData`/`QData`/`VlWide`), never
  `size_t`, for model data. Process wide data word-by-word (`VL_ZERO_W`,
  `VL_MEMCPY_W`), never bit-by-bit or byte-by-byte.
- **Do all string parsing at verilation time** -- never parse strings during
  simulation; emit structured data or compile-time hints instead.
- **Keep per-cycle code lean.** Do not add vtables to high-frequency objects
  (8 bytes per instance); guard optional features behind
  `hasClasses()`/`hasEvents()`-style checks; functions called per cycle must avoid
  mutexes -- use atomics or lockless designs.
- **Emit no runtime loops** the compiler could have expanded at verilation time;
  prefer a single runtime call.
- **Thread safety.** Annotate with the hierarchy `VL_PURE` > `VL_MT_SAFE` >
  `VL_MT_STABLE`; annotations must match the implementation. Annotate
  mutex-protected members with `VL_GUARDED_BY` and document acquisition ordering.
  Prefer has-a over is-a: a guarded class wrapping the unguarded internal one, with
  the guarded version as the default public API.
- **Keep runtime and compiler headers separate** -- never include `verilated.h`
  into the compiler in `src/`.

## File-specific rules

| File | Rule |
|---|---|
| `verilated_random.cpp` | Emit only portable SMT-LIB 2.6 -- no solver-specific or MaxSMT extensions; the generated solver text is the model's runtime constraint interface |
| `verilated_cov.cpp` | Coverage runtime is shared by all models -- keep per-point overhead minimal and the on-disk format stable for `verilator_coverage` |
