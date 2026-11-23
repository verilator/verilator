/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 ******************************************************************************/

#include "static_hypergraph.h"

#include "mt-kahypar/parallel/parallel_prefix_sum.h"
#include "mt-kahypar/datastructures/concurrent_bucket_map.h"
#include "mt-kahypar/datastructures/hypergraph_utils.h"
#include "mt-kahypar/utils/timer.h"
#include "mt-kahypar/utils/memory_tree.h"

#include <tbb/parallel_reduce.h>
#include <tbb/parallel_sort.h>

namespace mt_kahypar::ds {


  /*!
  * This struct is used during multilevel coarsening to efficiently
  * detect parallel hyperedges.
  */
  struct ContractedHyperedgeInformation {
    HyperedgeID he = kInvalidHyperedge;
    size_t hash = kEdgeHashSeed;
    size_t size = std::numeric_limits<size_t>::max();
    bool valid = false;
  };

  /*!
   * Contracts a given community structure. All vertices with the same label
   * are collapsed into the same vertex. The resulting single-pin and parallel
   * hyperedges are removed from the contracted graph. The function returns
   * the contracted hypergraph and a mapping which specifies a mapping from
   * community label (given in 'communities') to a vertex in the coarse hypergraph.
   *
   * \param communities Community structure that should be contracted
   */
  StaticHypergraph StaticHypergraph::contract(parallel::scalable_vector<HypernodeID>& communities, bool deterministic) {

    ASSERT(communities.size() == _num_hypernodes);

    if ( !_tmp_contraction_buffer ) {
      allocateTmpContractionBuffer();
    }

    // Auxiliary buffers - reused during multilevel hierarchy to prevent expensive allocations
    Array<size_t>& mapping = _tmp_contraction_buffer->mapping;
    Array<Hypernode>& tmp_hypernodes = _tmp_contraction_buffer->tmp_hypernodes;
    IncidentNets& tmp_incident_nets = _tmp_contraction_buffer->tmp_incident_nets;
    Array<parallel::IntegralAtomicWrapper<size_t>>& tmp_num_incident_nets =
            _tmp_contraction_buffer->tmp_num_incident_nets;
    Array<parallel::IntegralAtomicWrapper<HypernodeWeight>>& hn_weights =
            _tmp_contraction_buffer->hn_weights;
    Array<Hyperedge>& tmp_hyperedges = _tmp_contraction_buffer->tmp_hyperedges;
    IncidenceArray& tmp_incidence_array = _tmp_contraction_buffer->tmp_incidence_array;
    Array<size_t>& he_sizes = _tmp_contraction_buffer->he_sizes;
    Array<size_t>& valid_hyperedges = _tmp_contraction_buffer->valid_hyperedges;

    ASSERT(static_cast<size_t>(_num_hypernodes) <= mapping.size());
    ASSERT(static_cast<size_t>(_num_hypernodes) <= tmp_hypernodes.size());
    ASSERT(static_cast<size_t>(_total_degree) <= tmp_incident_nets.size());
    ASSERT(static_cast<size_t>(_num_hypernodes) <= tmp_num_incident_nets.size());
    ASSERT(static_cast<size_t>(_num_hypernodes) <= hn_weights.size());
    ASSERT(static_cast<size_t>(_num_hyperedges) <= tmp_hyperedges.size());
    ASSERT(static_cast<size_t>(_num_pins) <= tmp_incidence_array.size());
    ASSERT(static_cast<size_t>(_num_hyperedges) <= he_sizes.size());
    ASSERT(static_cast<size_t>(_num_hyperedges) <= valid_hyperedges.size());


    // #################### STAGE 1 ####################
    // Compute vertex ids of coarse hypergraph with a parallel prefix sum
    mapping.assign(_num_hypernodes, 0);

    doParallelForAllNodes([&](const HypernodeID& hn) {
      ASSERT(static_cast<size_t>(communities[hn]) < mapping.size());
      mapping[communities[hn]] = UL(1);
    });

    // Prefix sum determines vertex ids in coarse hypergraph
    parallel::TBBPrefixSum<size_t, Array> mapping_prefix_sum(mapping);
    tbb::parallel_scan(tbb::blocked_range<size_t>(UL(0), _num_hypernodes), mapping_prefix_sum);
    HypernodeID num_hypernodes = mapping_prefix_sum.total_sum();

    // Remap community ids
    tbb::parallel_for(ID(0), _num_hypernodes, [&](const HypernodeID& hn) {
      if ( nodeIsEnabled(hn) ) {
        communities[hn] = mapping_prefix_sum[communities[hn]];
      } else {
        communities[hn] = kInvalidHypernode;
      }

      // Reset tmp contraction buffer
      if ( hn < num_hypernodes ) {
        hn_weights[hn] = 0;
        tmp_hypernodes[hn] = Hypernode(true);
        tmp_num_incident_nets[hn] = 0;
      }
    });

    // Mapping from a vertex id of the current hypergraph to its
    // id in the coarse hypergraph
    auto map_to_coarse_hypergraph = [&](const HypernodeID hn) {
      ASSERT(hn < communities.size());
      return communities[hn];
    };

    doParallelForAllNodes([&](const HypernodeID& hn) {
      const HypernodeID coarse_hn = map_to_coarse_hypergraph(hn);
      ASSERT(coarse_hn < num_hypernodes, V(coarse_hn) << V(num_hypernodes));
      // Weight vector is atomic => thread-safe
      hn_weights[coarse_hn] += nodeWeight(hn);
      // Aggregate upper bound for number of incident nets of the contracted vertex
      tmp_num_incident_nets[coarse_hn] += nodeDegree(hn);
    });

    // #################### STAGE 2 ####################
    // In this step hyperedges and incident nets of vertices are contracted inside the temporary
    // buffers. The vertex ids of pins are already remapped to the vertex ids in the coarse
    // graph and duplicates are removed. Also nets that become single-pin hyperedges are marked
    // as invalid. All incident nets of vertices that are collapsed into one vertex in the coarse
    // graph are also aggregate in a consecutive memory range and duplicates are removed. Note
    // that parallel and single-pin hyperedges are not removed from the incident nets (will be done
    // in a postprocessing step).
    auto cs2 = [](const HypernodeID x) { return x * x; };
    ConcurrentBucketMap<ContractedHyperedgeInformation> hyperedge_hash_map;
    hyperedge_hash_map.reserve_for_estimated_number_of_insertions(_num_hyperedges);
    tbb::parallel_invoke([&] {
      // Contract Hyperedges
      tbb::parallel_for(ID(0), _num_hyperedges, [&](const HyperedgeID& he) {
        if ( edgeIsEnabled(he) ) {
          // Copy hyperedge and pins to temporary buffer
          const Hyperedge& e = _hyperedges[he];
          ASSERT(static_cast<size_t>(he) < tmp_hyperedges.size());
          ASSERT(e.firstInvalidEntry() <= tmp_incidence_array.size());
          tmp_hyperedges[he] = e;
          valid_hyperedges[he] = 1;

          // Map pins to vertex ids in coarse graph
          const size_t incidence_array_start = tmp_hyperedges[he].firstEntry();
          const size_t incidence_array_end = tmp_hyperedges[he].firstInvalidEntry();
          for ( size_t pos = incidence_array_start; pos < incidence_array_end; ++pos ) {
            const HypernodeID pin = _incidence_array[pos];
            ASSERT(pos < tmp_incidence_array.size());
            tmp_incidence_array[pos] = map_to_coarse_hypergraph(pin);
          }

          // Remove duplicates and disabled vertices
          auto first_entry_it = tmp_incidence_array.begin() + incidence_array_start;
          std::sort(first_entry_it, tmp_incidence_array.begin() + incidence_array_end);
          auto first_invalid_entry_it = std::unique(first_entry_it, tmp_incidence_array.begin() + incidence_array_end);
          while ( first_entry_it != first_invalid_entry_it && *(first_invalid_entry_it - 1) == kInvalidHypernode ) {
            --first_invalid_entry_it;
          }

          // Update size of hyperedge in temporary hyperedge buffer
          const size_t contracted_size = std::distance(
                  tmp_incidence_array.begin() + incidence_array_start, first_invalid_entry_it);
          tmp_hyperedges[he].setSize(contracted_size);


          if ( contracted_size > 1 ) {
            // Compute hash of contracted hyperedge
            size_t footprint = kEdgeHashSeed;
            for ( size_t pos = incidence_array_start; pos < incidence_array_start + contracted_size; ++pos ) {
              footprint += cs2(tmp_incidence_array[pos]);
            }
            hyperedge_hash_map.insert(footprint,
                                      ContractedHyperedgeInformation{ he, footprint, contracted_size, true });
          } else {
            // Hyperedge becomes a single-pin hyperedge
            valid_hyperedges[he] = 0;
            tmp_hyperedges[he].disable();
          }
        } else {
          valid_hyperedges[he] = 0;
        }
      });
    }, [&] {
      // Contract Incident Nets
      // Compute start position the incident nets of a coarse vertex in the
      // temporary incident nets array with a parallel prefix sum
      parallel::scalable_vector<parallel::IntegralAtomicWrapper<size_t>> tmp_incident_nets_pos;
      parallel::TBBPrefixSum<parallel::IntegralAtomicWrapper<size_t>, Array>
              tmp_incident_nets_prefix_sum(tmp_num_incident_nets);
      tbb::parallel_invoke([&] {
        tbb::parallel_scan(tbb::blocked_range<size_t>(
                UL(0), UI64(num_hypernodes)), tmp_incident_nets_prefix_sum);
      }, [&] {
        tmp_incident_nets_pos.assign(num_hypernodes, parallel::IntegralAtomicWrapper<size_t>(0));
      });

      // Write the incident nets of each contracted vertex to the temporary incident net array
      doParallelForAllNodes([&](const HypernodeID& hn) {
        const HypernodeID coarse_hn = map_to_coarse_hypergraph(hn);
        const HyperedgeID node_degree = nodeDegree(hn);
        size_t incident_nets_pos = tmp_incident_nets_prefix_sum[coarse_hn] +
                                   tmp_incident_nets_pos[coarse_hn].fetch_add(node_degree);
        ASSERT(incident_nets_pos + node_degree <= tmp_incident_nets_prefix_sum[coarse_hn + 1]);
        memcpy(tmp_incident_nets.data() + incident_nets_pos,
               _incident_nets.data() + _hypernodes[hn].firstEntry(),
               sizeof(HyperedgeID) * node_degree);
      });

      // Setup temporary hypernodes
      parallel::scalable_vector<HypernodeID> high_degree_vertices;
      tbb::parallel_for(ID(0), num_hypernodes, [&](const HypernodeID& coarse_hn) {
        // Remove duplicates
        const size_t incident_nets_start = tmp_incident_nets_prefix_sum[coarse_hn];
        const size_t incident_nets_end = tmp_incident_nets_prefix_sum[coarse_hn + 1];
        const size_t tmp_degree = incident_nets_end - incident_nets_start;
        if ( tmp_degree <= HIGH_DEGREE_CONTRACTION_THRESHOLD ) {
          std::sort(tmp_incident_nets.begin() + incident_nets_start,
                    tmp_incident_nets.begin() + incident_nets_end);
          auto first_invalid_entry_it = std::unique(tmp_incident_nets.begin() + incident_nets_start,
                                                    tmp_incident_nets.begin() + incident_nets_end);

          // Setup pointers to temporary incident nets
          const size_t contracted_size = std::distance(tmp_incident_nets.begin() + incident_nets_start,
                                                       first_invalid_entry_it);
          tmp_hypernodes[coarse_hn].setSize(contracted_size);
        } else {
          high_degree_vertices.push_back(coarse_hn);
        }
        tmp_hypernodes[coarse_hn].setWeight(hn_weights[coarse_hn]);
        tmp_hypernodes[coarse_hn].setFirstEntry(incident_nets_start);
      });

      if ( !high_degree_vertices.empty() ) {
        // High degree vertices are treated special, because sorting and afterwards
        // removing duplicates can become a major sequential bottleneck. Therefore,
        // we distribute the incident nets of a high degree vertex into our concurrent
        // bucket map. As a result all equal incident nets reside in the same bucket
        // afterwards. In a second step, we process each bucket in parallel and apply
        // for each bucket the duplicate removal procedure from above.
        ConcurrentBucketMap<HyperedgeID> duplicate_incident_nets_map;
        for ( const HypernodeID& coarse_hn : high_degree_vertices ) {
          const size_t incident_nets_start = tmp_incident_nets_prefix_sum[coarse_hn];
          const size_t incident_nets_end = tmp_incident_nets_prefix_sum[coarse_hn + 1];
          const size_t tmp_degree = incident_nets_end - incident_nets_start;

          // Insert incident nets into concurrent bucket map
          duplicate_incident_nets_map.reserve_for_estimated_number_of_insertions(tmp_degree);
          tbb::parallel_for(incident_nets_start, incident_nets_end, [&](const size_t pos) {
            HyperedgeID he = tmp_incident_nets[pos];
            duplicate_incident_nets_map.insert(he, std::move(he));
          });

          // Process each bucket in parallel and remove duplicates
          std::atomic<size_t> incident_nets_pos(incident_nets_start);
          tbb::parallel_for(UL(0), duplicate_incident_nets_map.numBuckets(), [&](const size_t bucket) {
            auto& incident_net_bucket = duplicate_incident_nets_map.getBucket(bucket);
            std::sort(incident_net_bucket.begin(), incident_net_bucket.end());
            auto first_invalid_entry_it = std::unique(incident_net_bucket.begin(), incident_net_bucket.end());
            const size_t bucket_degree = std::distance(incident_net_bucket.begin(), first_invalid_entry_it);
            const size_t tmp_incident_nets_pos = incident_nets_pos.fetch_add(bucket_degree);
            memcpy(tmp_incident_nets.data() + tmp_incident_nets_pos,
                   incident_net_bucket.data(), sizeof(HyperedgeID) * bucket_degree);
            duplicate_incident_nets_map.clear(bucket);
          });

          // Update number of incident nets of high degree vertex
          const size_t contracted_size = incident_nets_pos.load() - incident_nets_start;
          tmp_hypernodes[coarse_hn].setSize(contracted_size);

          if (deterministic) {
            // sort for determinism
            tbb::parallel_sort(tmp_incident_nets.begin() + incident_nets_start,
                               tmp_incident_nets.begin() + incident_nets_start + contracted_size);
          }
        }
        duplicate_incident_nets_map.free();
      }
    });

    // #################### STAGE 3 ####################
    // In the step before we aggregated hyperedges within a bucket data structure.
    // Hyperedges with the same hash/footprint are stored inside the same bucket.
    // We iterate now in parallel over each bucket and sort each bucket
    // after its hash. A bucket is processed by one thread and parallel
    // hyperedges are detected by comparing the pins of hyperedges with
    // the same hash.

    // Helper function that checks if two hyperedges are parallel
    // Note, pins inside the hyperedges are sorted.
    auto check_if_hyperedges_are_parallel = [&](const HyperedgeID lhs,
                                                const HyperedgeID rhs) {
      const Hyperedge& lhs_he = tmp_hyperedges[lhs];
      const Hyperedge& rhs_he = tmp_hyperedges[rhs];
      if ( lhs_he.size() == rhs_he.size() ) {
        const size_t lhs_start = lhs_he.firstEntry();
        const size_t rhs_start = rhs_he.firstEntry();
        for ( size_t i = 0; i < lhs_he.size(); ++i ) {
          const size_t lhs_pos = lhs_start + i;
          const size_t rhs_pos = rhs_start + i;
          if ( tmp_incidence_array[lhs_pos] != tmp_incidence_array[rhs_pos] ) {
            return false;
          }
        }
        return true;
      } else {
        return false;
      }
    };

    tbb::parallel_for(UL(0), hyperedge_hash_map.numBuckets(), [&](const size_t bucket) {
      auto& hyperedge_bucket = hyperedge_hash_map.getBucket(bucket);
      std::sort(hyperedge_bucket.begin(), hyperedge_bucket.end(),
                [&](const ContractedHyperedgeInformation& lhs, const ContractedHyperedgeInformation& rhs) {
                  return std::tie(lhs.hash, lhs.size, lhs.he) < std::tie(rhs.hash, rhs.size, rhs.he);
                });

      // Parallel Hyperedge Detection
      for ( size_t i = 0; i < hyperedge_bucket.size(); ++i ) {
        ContractedHyperedgeInformation& contracted_he_lhs = hyperedge_bucket[i];
        if ( contracted_he_lhs.valid ) {
          const HyperedgeID lhs_he = contracted_he_lhs.he;
          HyperedgeWeight lhs_weight = tmp_hyperedges[lhs_he].weight();
          for ( size_t j = i + 1; j < hyperedge_bucket.size(); ++j ) {
            ContractedHyperedgeInformation& contracted_he_rhs = hyperedge_bucket[j];
            const HyperedgeID rhs_he = contracted_he_rhs.he;
            if ( contracted_he_rhs.valid &&
                 contracted_he_lhs.hash == contracted_he_rhs.hash &&
                 check_if_hyperedges_are_parallel(lhs_he, rhs_he) ) {
              // Hyperedges are parallel
              lhs_weight += tmp_hyperedges[rhs_he].weight();
              contracted_he_rhs.valid = false;
              valid_hyperedges[rhs_he] = false;
            } else if ( contracted_he_lhs.hash != contracted_he_rhs.hash  ) {
              // In case, hash of both are not equal we go to the next hyperedge
              // because we compared it with all hyperedges that had an equal hash
              break;
            }
          }
          tmp_hyperedges[lhs_he].setWeight(lhs_weight);
        }
      }
      hyperedge_hash_map.free(bucket);
    });

    // #################### STAGE 4 ####################
    // Coarsened hypergraph is constructed here by writting data from temporary
    // buffers to corresponding members in coarsened hypergraph. For the
    // incidence array, we compute a prefix sum over the hyperedge sizes in
    // the contracted hypergraph which determines the start position of the pins
    // of each net in the incidence array. Furthermore, we postprocess the incident
    // nets of each vertex by removing invalid hyperedges and remapping hyperedge ids.
    // Incident nets are also written to the incident nets array with the help of a prefix
    // sum over the node degrees.

    StaticHypergraph hypergraph;

    // Compute number of hyperedges in coarse graph (those flagged as valid)
    parallel::TBBPrefixSum<size_t, Array> he_mapping(valid_hyperedges);
    tbb::parallel_invoke([&] {
      tbb::parallel_scan(tbb::blocked_range<size_t>(size_t(0), size_t(_num_hyperedges)), he_mapping);
    }, [&] {
      hypergraph._hypernodes.resize(num_hypernodes);
    });

    const HyperedgeID num_hyperedges = he_mapping.total_sum();
    hypergraph._num_hypernodes = num_hypernodes;
    hypergraph._num_hyperedges = num_hyperedges;

    auto assign_communities = [&] {
      hypergraph._community_ids.resize(num_hypernodes, 0);
      doParallelForAllNodes([&](HypernodeID fine_hn) {
        hypergraph.setCommunityID(map_to_coarse_hypergraph(fine_hn), communityID(fine_hn));
      });
    };

    auto setup_hyperedges = [&] {
      // Compute start position of each hyperedge in incidence array
      parallel::TBBPrefixSum<size_t, Array> num_pins_prefix_sum(he_sizes);
      tbb::parallel_invoke([&] {
        tbb::parallel_for(HyperedgeID(0), _num_hyperedges, [&](HyperedgeID id) {
          if ( he_mapping.value(id) ) {
            he_sizes[id] = tmp_hyperedges[id].size();
          } else {
            he_sizes[id] = 0;
          }
        });

        tbb::parallel_scan(tbb::blocked_range<size_t>(UL(0), UI64(_num_hyperedges)), num_pins_prefix_sum);

        const size_t num_pins = num_pins_prefix_sum.total_sum();
        hypergraph._num_pins = num_pins;
        hypergraph._incidence_array.resize(num_pins);
      }, [&] {
        hypergraph._hyperedges.resize(num_hyperedges);
      });

      // Write hyperedges from temporary buffers to incidence array
      tbb::enumerable_thread_specific<size_t> local_max_edge_size(UL(0));
      tbb::parallel_for(ID(0), _num_hyperedges, [&](const HyperedgeID& id) {
        if ( he_mapping.value(id) > 0 /* hyperedge is valid */ ) {
          const size_t he_pos = he_mapping[id];
          const size_t incidence_array_start = num_pins_prefix_sum[id];
          Hyperedge& he = hypergraph._hyperedges[he_pos];
          he = tmp_hyperedges[id];
          const size_t tmp_incidence_array_start = he.firstEntry();
          const size_t edge_size = he.size();
          local_max_edge_size.local() = std::max(local_max_edge_size.local(), edge_size);
          std::memcpy(hypergraph._incidence_array.data() + incidence_array_start,
                      tmp_incidence_array.data() + tmp_incidence_array_start,
                      sizeof(HypernodeID) * edge_size);
          he.setFirstEntry(incidence_array_start);
        }
      });
      hypergraph._max_edge_size = local_max_edge_size.combine(
              [&](const size_t lhs, const size_t rhs) {
                return std::max(lhs, rhs);
              });
    };

    auto setup_hypernodes = [&] {
      // Remap hyperedge ids in temporary incident nets to hyperedge ids of the
      // coarse hypergraph and remove singple-pin/parallel hyperedges.
      tbb::parallel_for(ID(0), num_hypernodes, [&](const HypernodeID& id) {
        const size_t incident_nets_start =  tmp_hypernodes[id].firstEntry();
        size_t incident_nets_end = tmp_hypernodes[id].firstInvalidEntry();
        for ( size_t pos = incident_nets_start; pos < incident_nets_end; ++pos ) {
          const HyperedgeID he = tmp_incident_nets[pos];
          if ( he_mapping.value(he) > 0 /* hyperedge is valid */ ) {
            tmp_incident_nets[pos] = he_mapping[he];
          } else {
            std::swap(tmp_incident_nets[pos--], tmp_incident_nets[--incident_nets_end]);
          }
        }
        const size_t incident_nets_size = incident_nets_end - incident_nets_start;
        tmp_hypernodes[id].setSize(incident_nets_size);
        tmp_num_incident_nets[id] = incident_nets_size;
      });

      // Compute start position of the incident nets for each vertex inside
      // the coarsened incident net array
      parallel::TBBPrefixSum<parallel::IntegralAtomicWrapper<size_t>, Array>
              num_incident_nets_prefix_sum(tmp_num_incident_nets);
      tbb::parallel_scan(tbb::blocked_range<size_t>(
              UL(0), UI64(num_hypernodes)), num_incident_nets_prefix_sum);
      const size_t total_degree = num_incident_nets_prefix_sum.total_sum();
      hypergraph._total_degree = total_degree;
      hypergraph._incident_nets.resize(total_degree);
      // Write incident nets from temporary buffer to incident nets array
      tbb::parallel_for(ID(0), num_hypernodes, [&](const HypernodeID& id) {
        const size_t incident_nets_start = num_incident_nets_prefix_sum[id];
        Hypernode& hn = hypergraph._hypernodes[id];
        hn = tmp_hypernodes[id];
        const size_t tmp_incident_nets_start = hn.firstEntry();
        std::memcpy(hypergraph._incident_nets.data() + incident_nets_start,
                    tmp_incident_nets.data() + tmp_incident_nets_start,
                    sizeof(HyperedgeID) * hn.size());
        hn.setFirstEntry(incident_nets_start);
      });
    };

    tbb::parallel_invoke(assign_communities, setup_hyperedges, setup_hypernodes);

    if ( hasFixedVertices() ) {
      // Map fixed vertices to coarse hypergraph
      FixedVertexSupport<StaticHypergraph> coarse_fixed_vertices(
        hypergraph.initialNumNodes(), _fixed_vertices.numBlocks());
      coarse_fixed_vertices.setHypergraph(&hypergraph);
      doParallelForAllNodes([&](const HypernodeID hn) {
        if ( isFixed(hn) ) {
          coarse_fixed_vertices.fixToBlock(communities[hn], fixedVertexBlock(hn));
        }
      });
      hypergraph.addFixedVertexSupport(std::move(coarse_fixed_vertices));
    }

    hypergraph._total_weight = _total_weight;   // didn't lose any vertices
    hypergraph._tmp_contraction_buffer = _tmp_contraction_buffer;
    _tmp_contraction_buffer = nullptr;
    return hypergraph;
  }


  // ! Copy static hypergraph in parallel
  StaticHypergraph StaticHypergraph::copy(parallel_tag_t) const {
    StaticHypergraph hypergraph;

    hypergraph._num_hypernodes = _num_hypernodes;
    hypergraph._num_removed_hypernodes = _num_removed_hypernodes;
    hypergraph._max_removed_degree_zero_hn_weight = _max_removed_degree_zero_hn_weight;
    hypergraph._num_hyperedges = _num_hyperedges;
    hypergraph._num_removed_hyperedges = _num_removed_hyperedges;
    hypergraph._max_edge_size = _max_edge_size;
    hypergraph._num_pins = _num_pins;
    hypergraph._total_degree = _total_degree;
    hypergraph._total_weight = _total_weight;

    tbb::parallel_invoke([&] {
      hypergraph._hypernodes.resize(_hypernodes.size());
      memcpy(hypergraph._hypernodes.data(), _hypernodes.data(),
             sizeof(Hypernode) * _hypernodes.size());
    }, [&] {
      hypergraph._incident_nets.resize(_incident_nets.size());
      memcpy(hypergraph._incident_nets.data(), _incident_nets.data(),
             sizeof(HyperedgeID) * _incident_nets.size());
    }, [&] {
      hypergraph._hyperedges.resize(_hyperedges.size());
      memcpy(hypergraph._hyperedges.data(), _hyperedges.data(),
             sizeof(Hyperedge) * _hyperedges.size());
    }, [&] {
      hypergraph._incidence_array.resize(_incidence_array.size());
      memcpy(hypergraph._incidence_array.data(), _incidence_array.data(),
             sizeof(HypernodeID) * _incidence_array.size());
    }, [&] {
      hypergraph._community_ids = _community_ids;
    }, [&] {
      hypergraph.addFixedVertexSupport(_fixed_vertices.copy());
    });
    return hypergraph;
  }

  // ! Copy static hypergraph sequential
  StaticHypergraph StaticHypergraph::copy() const {
    StaticHypergraph hypergraph;

    hypergraph._num_hypernodes = _num_hypernodes;
    hypergraph._num_removed_hypernodes = _num_removed_hypernodes;
    hypergraph._max_removed_degree_zero_hn_weight = _max_removed_degree_zero_hn_weight;
    hypergraph._num_hyperedges = _num_hyperedges;
    hypergraph._num_removed_hyperedges = _num_removed_hyperedges;
    hypergraph._max_edge_size = _max_edge_size;
    hypergraph._num_pins = _num_pins;
    hypergraph._total_degree = _total_degree;
    hypergraph._total_weight = _total_weight;

    hypergraph._hypernodes.resize(_hypernodes.size());
    memcpy(hypergraph._hypernodes.data(), _hypernodes.data(),
           sizeof(Hypernode) * _hypernodes.size());
    hypergraph._incident_nets.resize(_incident_nets.size());
    memcpy(hypergraph._incident_nets.data(), _incident_nets.data(),
           sizeof(HyperedgeID) * _incident_nets.size());

    hypergraph._hyperedges.resize(_hyperedges.size());
    memcpy(hypergraph._hyperedges.data(), _hyperedges.data(),
           sizeof(Hyperedge) * _hyperedges.size());
    hypergraph._incidence_array.resize(_incidence_array.size());
    memcpy(hypergraph._incidence_array.data(), _incidence_array.data(),
           sizeof(HypernodeID) * _incidence_array.size());

    hypergraph._community_ids = _community_ids;
    hypergraph.addFixedVertexSupport(_fixed_vertices.copy());

    return hypergraph;
  }

  void StaticHypergraph::memoryConsumption(utils::MemoryTreeNode* parent) const {
    ASSERT(parent);
    parent->addChild("Hypernodes", sizeof(Hypernode) * _hypernodes.size());
    parent->addChild("Incident Nets", sizeof(HyperedgeID) * _incident_nets.size());
    parent->addChild("Hyperedges", sizeof(Hyperedge) * _hyperedges.size());
    parent->addChild("Incidence Array", sizeof(HypernodeID) * _incidence_array.size());
    parent->addChild("Communities", sizeof(PartitionID) * _community_ids.capacity());
    if ( hasFixedVertices() ) {
      parent->addChild("Fixed Vertex Support", _fixed_vertices.size_in_bytes());
    }
  }

  // ! Computes the total node weight of the hypergraph
  void StaticHypergraph::computeAndSetTotalNodeWeight(parallel_tag_t) {
    _total_weight = computeTotalNodeWeightParallel(*this, _num_hypernodes);
  }

} // namespace
