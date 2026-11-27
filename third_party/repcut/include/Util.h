#pragma once

#include <cstdint>
#include <vector>

namespace repcut {
    float calculate_ib_factor(std::vector<uint32_t>& dat);
    float calculate_ib_factor(std::vector<float>& dat);

    struct PartitionStatistics
    {
        uint32_t nparts;

        float ib_factor_weight;
        float sg_weight;
        float total_part_weight;
        float replication_weight;
        float replication_rate_weight;
        std::vector<float> partition_weights;

        float ib_factor_size;
        uint32_t sg_size;
        uint32_t total_part_size;
        uint32_t replication_size;
        float replication_rate_size;
        std::vector<uint32_t> partition_size;
    };
} // namespace repcut
