#pragma once

#include "ClusterGraph.h"
#include "repcut.h"

// Distinguish the library header from this wrapper on case-insensitive filesystems.
#include "../external/mt-kahypar/include/mtkahypar.h"

#include <cstdint>
#include <memory>
#include <vector>

namespace repcut {
    // Load the embedded default preset with low-memory Louvain contraction.
    // The caller owns the returned context; no files are read or written.
    mt_kahypar_context_t* makeMtKaHyParContext();

    // Per-call resources. MtKaHyPar retains process-global RNG and serial state;
    // repcut_run serializes access by rejecting overlapping calls.
    class MtKaHyPar
    {
    private:
        using Context = std::unique_ptr<mt_kahypar_context_t, decltype(&mt_kahypar_free_context)>;
        Context context;
        mt_kahypar_hypergraph_t graph{nullptr, NULLPTR_HYPERGRAPH};
        mt_kahypar_partitioned_hypergraph_t partitioned{nullptr, NULLPTR_PARTITION};
        mt_kahypar_error_t error{};
        RepCutLogLevel log_level;
        int num_parts;
        bool failed(const char* operation) const;

    public:
        static bool initialize(int threads, RepCutLogLevel log_level);

        MtKaHyPar(int parts, float imbalance, int32_t seed, RepCutLogLevel log_level);
        ~MtKaHyPar();
        MtKaHyPar(const MtKaHyPar&) = delete;
        MtKaHyPar& operator=(const MtKaHyPar&) = delete;

        bool create(const ClusterGraph& clusters);
        bool partition(std::vector<uint32_t>& assignment);
    };
} // namespace repcut
