# RepCut Partitioner

A C++ implementation of the RepCut partitioner from *RepCut: Superlinear
Parallel RTL Simulation with Replication-Aided Partitioning* (Wang & Beamer,
ASPLOS 2023).

```bibtex
@inproceedings{wang2023repcut,
  title={Repcut: Superlinear parallel rtl simulation with replication-aided partitioning},
  author={Wang, Haoyuan and Beamer, Scott},
  booktitle={Proceedings of the 28th ACM International Conference on Architectural Support for Programming Languages and Operating Systems, Volume 3},
  pages={572--585},
  year={2023}
}
```

This release ships both a command-line tool (`rcp`) and a C
library (`librepcut`) suitable for embedding into other simulators/tools.

# Requirements & Dependencies

- C++20 compiler and CMake 3.26 or newer.
- oneTBB 2021.5 or newer and hwloc development files.
- Boost.Program_options for the `rcp` CLI.

# Build

RepCut builds and statically links the bundled MtKaHyPar v1.7 submodule.

```sh
git submodule update --init --recursive
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=install
cmake --build build -j 4
cmake --install build
```

The binary is at `build/tools/rcp/rcp`, or `install/bin/rcp` after installation.
The install also includes both libraries and the CMake target `repcut::repcut`.
The first configure downloads MtKaHyPar's pinned source dependencies.
Add `-DRCP_BUILD_CLI=OFF` to build only the libraries, without Boost.

oneTBB and hwloc must also be available at runtime.

## Build without linked MtKaHyPar

Configure with `-DRCP_USE_MTKAHYPAR=OFF`. C++17 is sufficient; the MtKaHyPar
submodule, oneTBB, and hwloc are not needed to build RCP.
At runtime, provide `MtKaHyPar` on `$PATH` or specify its path with
`--mtkahypar_bin` (`ctx->mtkahypar_bin` in the C API).

# Command Line Options

`--help`               produce help message

`--nparts num`         num of partitions (required)

`--graph_file arg`     input graph file (required)

`--work_directory arg`  Working directory (required). Must be writable; must
                       be **unique per concurrent run** (the tool places a
                       `.lock` file in it as a concurrent-use safeguard).

`--target_ib arg`      target imbalance factor. Default 0.03.

`--threads arg`        parallel threads passed to MtKaHyPar. Default `1`.

`--seed arg`           nonnegative seed passed to MtKaHyPar. Default `-1`
                       chooses a random seed. Use `-v` to see the chosen seed.

`--mtkahypar_bin arg`  external executable override, using MtKaHyPar's CLI and
                       partition-file format. Defaults to linked MtKaHyPar.

`--save-intermediate-files` save the hypergraph and cone assignments for debugging.

`--log_level arg`      log level: `silent`, `error`, `warn`, `info`, `debug`.

`-v` / `-vv`           shorthand for `--log_level info` / `--log_level debug`.

## On `--target_ib` (imbalance target)

When the cone-overlap hypergraph has no edges, the cones are independent.
RepCut assigns whole cones in descending weight order to the least-loaded
partition, breaking ties by cone and partition id. This skips MtKaHyPar's
partitioning call. Executable overrides are still checked at startup. The
existing hypergraph weights, including their positive floor, are used. This
greedy balance is not guaranteed to meet `--target_ib`, especially when one
cone is much heavier than the others. No replication is needed in this case.

RepCut asks MtKaHyPar to do two things:

1. **Balance partition size** — controlled by `--target_ib` (the ε passed to
   MtKaHyPar).  MtKaHyPar tries to constraint deviate from the average by at
   most a factor of ε. (Depending on input graph, this target may be impossible)
2. **Minimize replication** — the km1 objective.  Replication is what breaks
   intra-cycle dependences between partitions, but it also adds work.

The RepCut algorithm itself cannot *a priori* formulate where the replication
will land across partitions.  Even when MtKaHyPar produces a well-balanced
result on the proxy hypergraph, the replication it introduces is distributed
back across the RepCut partitions in a way RepCut does not directly control.
So in situations with high replication, the post-replication RepCut
partitions can still be unbalanced despite a tight `--target_ib`.

This has a less-than-intuitive consequence: **if you observe high
replication, raising `--target_ib` may actually both reduce replication and improve the real balance.**
A larger `target_ib` gives MtKaHyPar more search space to reduce the km1 objective
(replication), and the resulting drop in replication can more than offset
the looser balance target on the proxy hypergraph.

In short:

- The best value of `--target_ib` depends on the input graph.
- `0.03` is simply MtKaHyPar's default and is **likely too small** for many
  RepCut inputs.
- If your partition stats show a high duplication cost, try a larger value
  (e.g. 0.1, 0.3) and compare the resulting balance.

## Example

To partition `rocket21-1c.graph` into 4 partitions with info-level logging:

> rcp --graph_file ./example/rocket21-1c.graph --work_directory ~/tmp --nparts 4 --threads 1 --seed 42

## Output

The partitioned result is written to `${work_directory}/rcp_output.txt`.

Format: one line per partition, containing a comma-separated list of DAG node
ids that the partition must simulate (replicated ancestors included). Node ids
are sorted ascending and correspond to the graph file's line number minus one
(line 1 = node 0, line 2 = node 1, ...).

> `node_id,node_id,...`\
> `node_id,node_id,...`\
> ...

Partition lines are written in partition-id order (0, 1, ..., nparts-1).

With `--save-intermediate-files`, the work directory also contains `parts.hmetis`
and `parts.hmetis.part<N>.epsilon<E>.seed<S>.KaHyPar` (one partition id per cone).
This works with either backend, including independent cones. The external
backend already retains the files it needs to communicate with MtKaHyPar.

# Deterministic

For deterministic partitioning, use a fixed seed (not `-1`), `--threads 1`, and
a fresh process for each run.
MtKaHyPar's default preset does not guarantee determinism with multiple threads.
MtKaHyPar 1.7 reseeds its generator but does not reset the cached coin-flip
position or normal-distribution cache. Earlier linked-library calls can therefore
affect later partitions, even with the same seed and one thread.
The CLI and library backends may produce different partitions for the same seed.

# C Library API

`librepcut` exposes an extern-C entry point declared in
`include/repcut.h`:

```c
int repcut_run(const struct RepCutContext* ctx,
               struct RepCutStatistics* stats_out);
```

Zero-initialize `RepCutContext` before setting its fields.

- Returns 0 on success, non-zero on failure.
- On success, writes `rcp_output.txt` under `ctx->work_directory`.
- Repeated sequential calls are supported. Overlapping calls in the same
  process are rejected, even with distinct work directories.
- The first linked call initializes MtKaHyPar's process-wide thread pool.
  Later linked calls must use the same `parallel_threads`; graphs, partition
  counts and seeds may change. The host must not initialize or use MtKaHyPar
  independently of `librepcut`.
- Per-call contexts and graphs are released. MtKaHyPar's global pool and
  allocator caches can remain until process exit. Its TBB concurrency limit
  also affects other TBB users in the process.
- `ctx->mtkahypar_bin`: NULL/empty uses linked MtKaHyPar. A nonempty value
  selects that executable, checked before graph traversal.
- By default writes nothing to stderr on success; errors always print.
  Info/debug output is gated by `ctx->log_level`.
- `ctx->seed`: a nonnegative fixed seed, or `-1` for a random seed.
  The chosen value is logged at info level.
- Aggregate statistics are available via the optional `stats_out` parameter.
- Set `ctx->save_intermediate_files` to `true` to save intermediate files.

# Graph File Format

The input graph file is similar to the Metis input format. The first line
contains number of edges and nodes in the graph, separated by a space:

> `numEdges` `numNodes`

Each following line represents a node in the graph, including its label,
weight, and connecting nodes (out neighbors). Node id starts from 0
(i.e. line 1 is node 0, line 2 is node 1) and fields are separated by
space. A node weight less than 0 indicates an invalid node, and such invalid
nodes will not participate in later partitioning. For correctness, any
invalid node should not have any connecting nodes.

> `Label` `Node Weight` `list of output neighbors (nodes that the current node connects to)`

The value of `Label` does not affect partitioning result. However, `Label` is
mandatory and should not contain spaces. Consecutive spaces between fields
are tolerated by the parser.

An example graph file is under the `example/` directory.

# Tests

Library tests cover sequential reuse, dependency closure, error recovery and
overlap rejection:

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DRCP_BUILD_TESTS=ON
cmake --build build -j 4
ctest --test-dir build --output-on-failure
```

The independent-cone regression uses a guarded MtKaHyPar stub to check that
edgeless hypergraphs bypass partitioning, while shared dependencies still
invoke the external tool and propagate its failures. The seed regression
checks seed selection and replay. Python 3 is required:

```sh
python3 tests/test_edgeless.py --rcp build/tools/rcp/rcp --work-directory build/test-edgeless
python3 tests/test_seed.py --rcp build/tools/rcp/rcp --work-directory build/test-seed
python3 tests/test_weights.py --rcp build/tools/rcp/rcp --work-directory build/test-weights
python3 tests/test_intermediates.py --rcp build/tools/rcp/rcp --work-directory build/test-intermediates
c++ -std=c++17 -Iinclude tests/test_cone_trie.cpp lib/repcut/ConeTrie.cpp -o build/test-cone-trie
build/test-cone-trie
c++ -std=c++17 -Iinclude tests/test_dag.cpp lib/repcut/DAG.cpp -o build/test-dag
build/test-dag build/test-dag-data
```

Generated graphs, memberships and logs remain in the selected work directory.
