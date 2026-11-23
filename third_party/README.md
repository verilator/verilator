<!-- SPDX-FileCopyrightText: 2026-2026 Wilson Snyder -->

<!-- SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0 -->

# Bundled RepCut sources

Verilator links RepCut and Mt-KaHyPar into its compiler. These source snapshots
retain their upstream licenses and style. `manifest.json` records repository
URLs, exact commits, exclusions and SHA-256 hashes of the original imported
files. `patches/` contains the local embedding and library interface changes;
the partitioning algorithms and preset are unchanged. `NOTICES.txt` is installed
with Verilator.
Standalone CLIs, conversion tools, Python bindings, packaging helpers and the
upstream Mt-KaHyPar test harness are excluded from the consumer snapshots.
The bundled build is a static library with no dependency-download paths.
RCP's API tests remain included; full Mt-KaHyPar upstream testing uses its
complete source checkout. CLI11 documentation/examples/tests are also omitted.

The consumer build omits the RCP CLI (and Boost), Mt-KaHyPar's Python and test
frontends, hwloc and Parlay. The external Mt-KaHyPar executable backend and
tiny-process-library are excluded; nonempty `RepCutContext::mtkahypar_bin`
requests are rejected. Verilator's `--repcut-partitioner` override uses its own
process launcher and remains available. CLI11, WHFC and KaHyPar shared resources
are bundled.
Mt-KaHyPar's ordinary library algorithms, including flow refinement, remain
available through a serial execution adapter for the pinned library's task,
container, allocator, and scan interfaces. The adapter is part of Verilator,
not bundled oneTBB code. The library requires exactly one partitioning thread
and has no oneTBB or tbbmalloc dependency. Its C++17 reference wrapper uses
ordinary operations only inside this serial backend; the process-wide entry
guard remains atomic. Bit operations use portable C++17 helpers. Generated
simulators do not link the partitioner. Internal memory-pool, timer and
initial-partition statistics locks are removed; serial ownership markers
retain their state. NUMA startup and duplicate task-dispatch paths are omitted.

The `repcut_run_graph` C API accepts borrowed CSR arrays and returns memberships
through a synchronous callback. It shares the file API's partitioning pipeline
and process-wide concurrency guard. Without intermediate dumps it requires no
working directory and performs no configuration, graph or membership file I/O.
The embedded preset is parsed directly from memory through the bundled
Mt-KaHyPar INI parser.

Both Verilator build systems use `CMakeLists.txt` here, requiring CMake 3.15
or newer and a C++17-capable compiler. The embedding patch lowers Mt-KaHyPar's
declared minimum for this configuration, which disables optional paths
requiring newer CMake commands.
CMake 3.15 builds without Mt-KaHyPar's optional precompiled headers.
The standalone API tests can be built with:

```sh
cmake -S third_party -B build-repcut -DRCP_BUILD_TESTS=ON
cmake --build build-repcut --target test-library test-memory test-serial test-hypergraph test-mtkahypar-config
(cd build-repcut && ctest --output-on-failure)
```

Reproduce the snapshots in a fresh directory using `nodist/import_repcut` with
`--output <directory>` and one `--checkout NAME=PATH` for each manifest path:
`repcut`, `repcut/external/mt-kahypar`, `cli11`, `WHFC`, and
`kahypar-shared-resources`. Local checkouts supply Git objects; the script does
not download sources or overwrite the working tree. For an update, add
`--revision NAME=REV` for each changed component. Review the new manifest,
resolve any patch conflicts, update notices, and qualify the partitioner before
copying the staged snapshots back. Submodule entries are supplied by their own
manifest package, so release archives contain ordinary files.
