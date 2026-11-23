#pragma once

#include <cstdint>
#include <filesystem>
#include <memory>
#include <string>
#include <vector>

#include "DAG.h"
#include "Util.h"
#include "repcut.h"

namespace fs = std::filesystem;

namespace repcut {
    class RepCutPartitioner
    {
    private:
        bool _resolveSeed();
        bool _partitionCones(DirectedAcyclicGraph& dag);
        void _partitionIndependentCones(const std::vector<uint32_t>& weights);
        bool _saveConeAssignment() const;
        bool _reconstruct(DirectedAcyclicGraph& dag);

        // hmetis file path for the optional debug dump.
        fs::path hmetis_path;
        // Output filename produced by MtKaHyPar.
        fs::path mtkahypar_output_filename;
        // Resolved once per partition() call; the requested seed may remain -1.
        int32_t mtkahypar_seed = 0;

    public:
        // Parameters.
        float kahypar_imbalance_factor = 0.015;
        int32_t kahypar_seed = -1;
        uint32_t desired_parts = 0;
        int parallel_threads = -1;
        bool save_intermediate_files = false;

        std::string work_directory;
        void set_work_directory(const std::string& work_dir) { work_directory = work_dir; }

        // Log threshold carried from RepCutContext.
        RepCutLogLevel log_level = REPCUT_LOG_SILENT;

        // Initialize the linked library; executable overrides are unsupported.
        bool prepareMtKaHyPar(const char* bin);

        // Result: cone (sink) → partition id.
        std::vector<uint32_t> coneIdToPartId;
        std::vector<std::vector<uint32_t>> partIdToConeId;

        // Per-partition DAG node ids (replicated ancestors included), sorted.
        std::vector<std::vector<uint32_t>> partitions;

        // Run the full RepCut pipeline on a design DAG.
        bool partition(DirectedAcyclicGraph& dag, const int nparts);

        // Compute partition statistics against the design DAG.
        std::unique_ptr<PartitionStatistics> reportPartitionStatus(DirectedAcyclicGraph& dag);

        // Write partitions (CSV, one line per partition) to work_directory.
        void saveToFile(const char* filename);
    };
} // namespace repcut
