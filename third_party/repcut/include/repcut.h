// Public C interface to librepcut (RepCut partitioning pipeline).
// Sequential calls are supported; overlapping calls in one process are rejected.

#ifndef REPCUT_H
#define REPCUT_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

enum RepCutLogLevel {
    REPCUT_LOG_SILENT = 0, // default: no output on success
    REPCUT_LOG_ERROR = 1,  // errors always print (cannot be suppressed)
    REPCUT_LOG_WARN = 2,
    REPCUT_LOG_INFO = 3,  // -v
    REPCUT_LOG_DEBUG = 4, // -vv
};

// Zero-initialize before setting fields.
struct RepCutContext
{
    const char* graph_filename;    // required by repcut_run; ignored by repcut_run_graph
    const char* work_directory;    // required for file API or intermediate dumps
    int nparts;                    // required: partition count
    float target_ib;               // default 0.03
    int parallel_threads;          // required: 1 (serial-only bundled backend)
    int seed;                      // nonnegative fixed seed; -1 = choose randomly, logged at INFO
    enum RepCutLogLevel log_level; // default SILENT

    // Reserved for compatibility with upstream RCP. The bundled build accepts
    // only NULL/empty, selecting linked MtKaHyPar; nonempty values are rejected.
    const char* mtkahypar_bin;

    // Default false. Save parts.hmetis and cone assignments in work_directory.
    bool save_intermediate_files;
};

// Aggregated partitioning statistics.  Optional out-parameter of repcut_run;
// pass NULL if not needed.  All aggregate fields; per-partition breakdown is
// not exposed at the C ABI level (C++ callers can use RepCutPartitioner::
// reportPartitionStatus for the full PartitionStatistics object).
struct RepCutStatistics
{
    uint32_t nparts;

    float ib_factor_weight;
    float sg_weight;
    float total_part_weight;
    float replication_weight;
    float replication_rate_weight;

    float ib_factor_size;
    uint32_t sg_size;
    uint32_t total_part_size;
    uint32_t replication_size;
    float replication_rate_size;
};

// Run the full RepCut pipeline.  Returns 0 on success, non-zero on failure.
// On success, writes "rcp_output.txt" under ctx->work_directory.  If
// stats_out is non-NULL, populated with aggregate partition statistics.
// Only one call may be active per process, even with distinct work directories.
// The bundled backend executes on the calling thread and requires
// parallel_threads = 1. MtKaHyPar retains process-global state; the host must
// not initialize or use MtKaHyPar independently of librepcut.
// MtKaHyPar 1.7 does not reset all cached RNG state when reseeding, so repeated
// linked calls may produce different partitions with the same seed, even at
// one thread. For reproducibility, use a fixed seed, one thread, and a fresh
// process for each run with the same backend.
int repcut_run(const struct RepCutContext* ctx, struct RepCutStatistics* stats_out);

// Borrowed CSR graph: offsets has num_vertices + 1 entries, starts at zero,
// and ends at num_edges. Neighbors are outgoing vertex IDs in caller order.
// Weights must be finite; negative weights mark invalid vertices, as in files.
struct RepCutGraph
{
    uint32_t num_vertices;
    size_t num_edges;
    const float* weights;
    const size_t* offsets;
    const uint32_t* neighbors;
};

// Called synchronously once per partition, in ascending partition order.
// Members include replicated ancestors and are sorted by vertex ID. The borrowed
// array is valid only during the callback (may be NULL when count is zero).
// Return nonzero to abort. Discard all received memberships if the run fails.
// Do not throw or reenter the partitioner from the callback.
typedef int (*RepCutPartitionCallback)(void* user, uint32_t partition,
                                     const uint32_t* members, size_t count);

// Same pipeline, process-wide guard, and RNG/thread-pool rules as repcut_run.
// No filesystem access unless save_intermediate_files is true, in which case
// work_directory must exist and receives intermediate hypergraph/cone dumps.
// graph_filename is ignored. This function never writes rcp_output.txt.
int repcut_run_graph(const struct RepCutContext* ctx, const struct RepCutGraph* graph,
                     RepCutPartitionCallback callback, void* user,
                     struct RepCutStatistics* stats_out);

#ifdef __cplusplus
}
#endif

#endif // REPCUT_H
