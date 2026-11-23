# Guide for Implementing a Custom Objective Function

We have defined a common interface for the gain computation techniques that we use in our refinement algorithms. This enables us to extend Mt-KaHyPar with new objective functions without having to modify the internal implementation of the refinement algorithms. This guide explains step-by-step how you can add your new custom objective function to Mt-KaHyPar. The only limitation of the current implementation is that it only allows you to define minimization problems, and the objective function must be defined on the hyperedges.

## Setup

- ```partition/context_enum_classes.h```: Add a new enum type to the enum classes ```Objective``` and ```GainPolicy``` representing your new objective function.
- ```partition/context_enum_classes.cpp```: Create a mapping between a string description and your new enum type in ```operator<< (std::ostream& os, const Objective& objective)```, ```operator<< (std::ostream& os, const GainPolicy& type)``` and ```objectiveFromString(const std::string& obj)```
- ```partition/metrics.cpp```: Create a template specialization of the ```ObjectiveFunction``` struct for your ```Objective``` enum type and override ```operator()(const PartitionedHypergraph& phg, const HyperedgeID he)```. The function takes a partitioned hypergraph and a hyperedge ID and computes the contribution of the hyperedge to the objective function. Moreover, add your new objective function to the switch statements in ```quality(...)``` and ```contribution(...)```.
- ```partition/refinement/gains/gain_definitions.h```: Create a gain type struct for your new objective function. You can copy one of the existing structures. This struct contains all relevant implementations for the gain computation in our refinement algorithms. We will later replace them with custom implementations for the new objective function. You also have to add this struct to the type list ```GainTypes``` and to the macro ```INSTANTIATE_CLASS_WITH_TYPE_TRAITS_AND_GAIN_TYPES```.
- ```partition/refinement/gains/gain_cache_ptr.h```: Add the ```GainPolicy``` type of your new objective function to all switch statements in the ```GainCachePtr``` class. Use the gain cache implementation of your gain type struct defined in ```gain_definitions.h```. We will later replace it by the concrete gain cache implementation for your new objective function. Moreover, add the ```GainPolicy``` type of your new objective function to the switch statement of the ```bipartition_each_block(...)``` function in ```partition/deep_multilevel.cpp```
- ```partition/context.cpp```: Create a mapping between the enum type ```Objective``` and ```GainPolicy``` in the ```sanityCheck(...)``` function.
- ```partition/registries/register_policies.cpp```: Create a mapping between the enum class ```GainPolicy``` and your gain type struct.
- ```partition/refinement/gains/bipartitioning_policy.h```: Add the ```GainPolicy``` type of your new objective function to the switch statements in ```useCutNetSplitting(...)``` and ```nonCutEdgeMultiplier(...)```. You can copy one of the existing parameters of an other objective function for now. An explanation how to configure these functions properly follows later.
- Create a folder for your objective function in ```partition/refinement/gains```. We will later add here all relevant gain computation techniques.

At this point, you can run Mt-KaHyPar with your new objective function by adding the command line parameter ```-o <string description of your objective function>```. At the end of the partitioning process, you should see the value of your new objective function (directly under the *Partitioning Result* section). However, running Mt-KaHyPar in debug mode will fail due to failing assertions.

## Initial Partitioning

We perform recursive bipartitioning to compute an initial k-way partition. The scheme recursively bipartitions the hypergraph until we reach the desired number of blocks. Each bipartitioning call optimizes the cut metric (weight of all cut nets). However, other objective functions can be optimized implicitly by implementing the two functions defined in ```partition/refinement/gains/bipartitioning_policy.h```. The main invariant of our recursive bipartitioning algorithm is that the cut of all bipartitions sum up to the objective value of the initial k-way partition. There are unit tests that asserts this invariant in ```tests/partition/refinement/bipartitioning_gain_policy_test.cc``` (build test suite via ```make mtkahypar_tests``` and then run ```./tests/mtkahypar_tests --gtest_filter=*ABipartitioningPolicy*```).

### Cut Net Splitting and Removal

The recursive bipartitioning algorithm bipartitions the hypergraph and then extracts both blocks as separate hypergraphs on which we then perform the recursive calls. The block extraction algorithm requires information how deal with cut hyperedges of the bipartition. There are two options: *cut net splitting* and *cut net removal*. The former splits a hyperedge containing only the pins of the extracted block, while the latter removes cut hyperedges in the extracted hypergraph. For example, if we optimize the cut metric, we can remove all cut hyperedges as they do not contribute to the cut in further bipartitions. If we optimize the connectivity metric (connectivity minus one of each cut hyperedge times their weight), we have to split cut hyperedges as increasing their connectivity can still increase the connectivity metric of the final k-way partition in further bipartitions.

### Non-Cut Edge Multiplier

We multiply the weight of each hyperedge that was not cut in any of the previous bipartitions by this multiplier before bipartitioning a hypergraph. This feature was introduced due to a percularity of the sum-of-external-degree metric (connectivity of each cut hyperedge times their weight, also called *soed*). We can reduce the soed metric by 2 * w(e) if we remove hyperedge e from the cut (w(e) is the weight of hyperedge e). However, the soed metric only reduces by w(e) if we reduce the connectivity of e by one, but e is still cut afterwards. Therefore, we multiply the weight of all hyperedges that were not cut in any of the previous bipartitions by two. This maintains the invariant that the cut of all bipartitions sum up to the value of the soed metric of the initial k-way partition.

## Label Propagation Refinement

Our label propagation algorithm iterates over all nodes in parallel and moves each node to the block with the highest gain. The algorithm requires two gain techniques: A *gain computation* algorithm to compute the highest gain move for a node and the *attributed gain* technique to double-check the gain of a node move at the time performed on the partition. Create for both techniques a separate header file in the folder of your objective function. You can copy an existing implementation from another objective function (rename the classes appropriately). Afterwards, include both files in ```partition/refinement/gains/gain_definitions.h``` and replace the ```GainComputation``` and ```AttributedGains``` member of your gain type struct with the concrete implementations.

### Attributed Gains

The gain of a node move can change between its initial calculation and execution due to concurrent node moves in its neighborhood. We therefore double-check the gain of a node move at the time performed on the partition via synchronized data structure updates. This technique is called *attributed gains*. The label propagation algorithm reverts node moves that worsen the solution quality by checking the attributed gain value. The attributed gain function implements the following interface:
```cpp
static HyperedgeWeight gain(const SynchronizedEdgeUpdate& sync_update);
```
The ```SynchronizedEdgeUpdate``` structs contains the following members:
```cpp
struct SynchronizedEdgeUpdate {
  HyperedgeID he;
  PartitionID from;
  PartitionID to;
  HyperedgeID edge_weight;
  HypernodeID edge_size;
  HypernodeID pin_count_in_from_part_after;
  HypernodeID pin_count_in_to_part_after;
  PartitionID block_of_other_node; // only set in graph partitioning mode
  mutable ds::Bitset* connectivity_set_after; // only set when optimizing the Steiner tree metric
  mutable ds::PinCountSnapshot* pin_counts_after; // only set when optimizing the Steiner tree metric
  const TargetGraph* target_graph; // only set when optimizing the Steiner tree metric
  ds::Array<SpinLock>* edge_locks; // only set when optimizing the Steiner tree metric
};
```

When we move a node from its *source* (```from```) to a *target* block (```to```), we iterate over all hyperedges, perform syncronized data structure updates and call this function for each incident hyperedge of the moved node. The sum of all calls to this function is the attributed gain of the node move. The most important parameters of the ```SynchronizedEdgeUpdate``` struct are ```pin_count_in_from_part_after``` and ```pin_count_in_to_part_after```, which are the number of pins contained in the source and target block of hyperedge ```he``` after the node move. For example, the node move removes an hyperedge from the cut if ```pin_count_in_to_part_after == edge_size```. If ```pin_count_in_from_part_after == 0```, then the node move reduces the connectivity of the hyperedge by one. Conversely, if ```pin_count_in_to_part_after == 1```, then the node move increases the connectivity of the hyperedge by one.

### Gain Computation

All gain computation techniques inherit from ```GainComputationBase``` (see ```partition/refinement/gains/gain_compute_base.h```). The base class has two template parameters: the derived class and the attributed gain implementation of the objective function (curiously recurring template pattern, avoids vtable lookups). The base class calls the ```precomputeGains(...)``` function of the derived class, which has the following interface:
```cpp
template<typename PartitionedHypergraph>
void precomputeGains(const PartitionedHypergraph& phg,
                     const HypernodeID hn,
                     RatingMap& tmp_scores,
                     Gain& isolated_block_gain);
```
We split the gain computation in two steps: (i) compute the gain of moving the node into an isolated block (stored in ```isolated_block_gain```) and (ii) moving the node from the isolated block to all adjacent blocks (stored in ```tmp_scores```). ```tmp_scores``` can be used similar to an ```std::vector``` and has exactly k entries. The gain of moving a node to a block ```to``` can then be computed by ```isolated_block_gain - tmp_scores[to]``` (a negative value means that moving the node to block ```to``` improves the objective function). However, the derived class still implements a function that computes the gain to a particular block:
```cpp
HyperedgeWeight gain(const Gain to_score, // tmp_scores[to]
                     const Gain isolated_block_gain);
```
The implementation of this function is most likely ```isolated_block_gain - to_score``` (except for the Steiner tree metric).

At this point, you should be able to run the ```default``` configuration of Mt-KaHyPar in debug mode without failing assertions if you disable the FM algorithm. To test this, add the following command line parameters to the Mt-KaHyPar call: ```--i-r-fm-type=do_nothing``` and ```--r-fm-type=do_nothing```. If you discover failing assertions, please check the implementations of the techniques described in the initial partitioning and label propagation section for bugs.

## FM Refinement

Our FM algorithm starts several localized FM searches in parallel. Each search polls several seed nodes from a shared task queue and then gradually expands around them by claiming neighbors of moved nodes. In each step, the algorithm performs the node move with the highest gain (stored in a priority queue). A search terminates when the PQ becomes empty or when it becomes unlikely to find further improvements. We repeatedly start localized FM searches until the task queue is empty. At the end, the move sequences found by the individual searches are concatenated to a global move sequence for which gains are recomputed in parallel. The algorithm then applies the best prefix of this move sequence to the partition.

The FM algorithm requires three additional gain computation techniques: (i) a *gain cache* that stores and maintains the gain values for all possible nodes moves, (ii) a *thread-local gain cache* or also called *delta gain cache* that stores changes on the gain cache without making them visible to other threads, and (iii) a *rollback* implementation that recomputes the gain values for the global move sequence. Create for all techniques a separate header file in the folder of your objective function. You can copy the existing implementations from another objective function (rename the classes appropriately). Afterwards, include the files in ```partition/refinement/gains/gain_definitions.h``` and replace the ```GainCache```,  ```DeltaGainCache``` and ```Rollback``` member of your gain type struct with the concrete implementations. Moreover, add your gain cache implementation to all switch statements in ```partition/deep_multilevel.cpp``` and ```partition/refinement/gains/gain_cache_ptr.h```.

### Gain Cache

The gain cache stores and maintains the gain values for all possible node moves. We split a gain value into an benefit and penalty term b(u, V_j) and p(u) that stores the benefit of moving a node to block V_j and the penalty of moving the node out of its current block. The gain of moving the node to block V_j is then given by b(u, V_j) - p(u) (> 0 means improvement). For example for the cut metric, the benefit term is b(u, V_j) := w({ e \in I(u) | pin_count(e, V_j) = |e| - 1 }) (nets that would become non-cut if we move u to V_j) and the penalty term is p(u) := w({e \in I(u) | pin_count(e, V_i) = |e|}) (nets that would become cut if we move u out of its current block V_i). Thus, the gain cache for the cut metric stores k + 1 entries for each node.

The interface of the gain cache class contains functions to initialize the gain cache, accessing gain values, and updating the gain cache after a node move. Implementing these functions is highly individual for each objective function and we recommend to look at some existing implementation to understand the semantics.
Most notable is the delta gain update function, which has the following interface:
```cpp
template<typename PartitionedHypergraph>
void deltaGainUpdate(const PartitionedHypergraph& partitioned_hg,
                     const SynchronizedEdgeUpdate& sync_update);
```
If we move a node u to another block, we call this function for each incident hyperedge of u (similar to the attributed gains). The function should be used to update gain cache entries affected by the node move.

Mt-KaHyPar also implements the n-level partitioning scheme. In this scheme, we contract only a single node on each level. Consequently, we also uncontract only a single node in the uncoarsening phase followed by a highly localized search for improvements around the uncontracted node. An uncontraction can also affect the gain cache. For a contraction that contracts a node v onto a node u, we provide two functions to update the gain cache after the uncontraction operation:
```cpp
template<typename PartitionedHypergraph>
void uncontractUpdateAfterRestore(
  const PartitionedHypergraph& partitioned_hg,
  const HypernodeID u,
  const HypernodeID v,
  const HyperedgeID he,
  const HypernodeID pin_count_in_part_after);

template<typename PartitionedHypergraph>
void uncontractUpdateAfterReplacement(
  const PartitionedHypergraph& partitioned_hg,
  const HypernodeID u,
  const HypernodeID v,
  const HyperedgeID he);
```
The first function is called if ```u``` and ```v``` are both contained in hyperedge ```he``` after the uncontraction. The second function is called if ```v``` replaces ```u``` in hyperedge ```he```. If it is not possible to update the gain cache after the uncontraction operation, you can throw an error/exception in both functions or optimize out the n-level code by adding ```-DKAHYPAR_ENABLE_HIGHEST_QUALITY_FEATURES=OFF``` to the cmake build command. However, if you do not implement these functions, it is not possible to use our ```highest_quality``` configuration.

There is a unit test that verifies your gain cache implementation, which you can find in ```tests/partition/refinement/gain_cache_test.cc``` (build test suite via ```make mtkahypar_tests``` and then run ```./tests/mtkahypar_tests --gtest_filter=*AGainCache*```). To test your gain cache implementation, you can add your gain type struct to the ```TestConfigs```.

### Thread-Local Gain Cache

The localized FM searches apply node moves to a thread-local partition which are not visible for other threads. Only improvements are applied to the global partition. The thread-local partition maintains a delta gain cache that stores gain updates relative to the global gain cache. For example, the penalty term of the thread-local gain cache is given by p'(u) := p(u) + Δp(u) where p(u) is the penalty term stored in the global gain cache and Δp(u) is the penalty term stored in the delta gain cache after performing some moves locally. The internal implementation of a thread-local gain cache uses a hash table to store Δp(u) and Δb(u, V_j). To update both terms, you can copy the implementation of your delta gain update function of the global gain cache and apply changes to the hash table instead of the global gain cache.

### Rollback

After all localized FM searches terminate, we concatenate the move sequences of all searches to a global move sequence and recompute the gain values in parallel assuming that the moves are executed exactly in this order. After recomputing all gain values, the prefix with the highest accumulated gain is applied to the global partition. The gain recomputation algorithm iterates over all hyperedges in parallel. For each hyperedge, we iterate two times over all pins. The first loop precomputes some auxiliary data, which we then use in the second loop to decide which moved node contained in the hyperedge increases or decreases the objective function. The implementations for all functions required to implement the parallel gain recomputation algorithm are highly individual for each objective function. We recommend to read one of our papers for a detailed explanation of this technique. Furthermore, you can find the implementation of the gain recomputation algorithm in ```partition/refinement/fm/global_rollback.cpp```. If you do not want to use the parallel gain recalculation algorithm, you can disable the feature by setting ```static constexpr bool supports_parallel_rollback = false;``` in your rollback class. The global rollback algorithm then uses an alternative parallelization which is slightly slower (but still acceptable).

## Flow-Based Refinement

We use flow-based refinement to improve bipartitions. The bipartitioning algorithm can be scheduled on pairs of blocks to improve k-way partitions. To improve a bipartition, we grow a size-constrained region around the cut hyperedges and then construct a flow network on which we then run a maximum flow algorithm to compute a minimum cut that separates a source and a sink node. We recommend to read our paper on flow-based refinement to get a better understanding of the overall algorithm.

To adapt the flow-based refinement algorithm to your new objective function, you have to implement a ```FlowNetworkConstruction``` policy. The interface implements two functions:
```cpp
template<typename PartitionedHypergraph>
static HyperedgeWeight capacity(const PartitionedHypergraph& phg,
                                const HyperedgeID he,
                                const PartitionID block_0,
                                const PartitionID block_1);

template<typename PartitionedHypergraph>
static bool dropHyperedge(const PartitionedHypergraph& phg,
                          const HyperedgeID he,
                          const PartitionID block_0,
                          const PartitionID block_1);
```
The ```capacity(...)``` function gives a hyperedge in the flow network a capacity. The flow network contains nodes of block ```block_0``` and ```block_1```. The capacity should be chosen such that the initial objective value of the bipartition induced by the region minus the maximum flow value equals the reduction in the objective function when we apply the minimum cut to the k-way partition. The ```dropHyperedge(...)``` function removes hyperedges from the flow network that are not relevant for the objective function. For example for the cut metric, we can remove all hyperedges that contains nodes of a block different from ```block_0``` and ```block_1```. The flow algorithm can not remove such nets from cut.

To test your implementation, you can enable logging in our flow-based refinement algorithm by setting the ```debug``` flag to ```true``` in the class ```FlowRefinementScheduler``` (see ```partition/refinement/flows/flow_refinement_scheduler.h```). Then, run Mt-KaHyPar with one thread using the following command line parameters: ```-t 1 --preset-type=quality```. If our flow-based refinement algorithm finds an improvement, it outputs the expected gain (initial objective value - maximum flow value) and the real gain (computed via attributed gains). If your implementation is correct, then the expected should always match the real gain.

## Extending the Library Interface with a Custom Objective Function

### C Interface

- ```include/mtkahypartypes.h```: Add a enum type to ```mt_kahypar_objective_t``` representing your new objective function
- ```lib/mtkahypar.cpp```: Create a mapping between the enum types ```mt_kahypar_objective_t``` and ```Objective``` in ```mt_kahypar_set_context_parameter(...)``` and ```mt_kahypar_set_partitioning_parameters(...)```
- ```include/mtkahypar.h```: Add a function that takes a ```mt_kahypar_partitioned_hypergraph_t``` and computes your objective function (similar to ```mt_kahypar_cut(...)``` and ```mt_kahypar_km1```).

### Python Interface

The Python interface is defined in ```python/module.cpp```. You only have to add a mapping between a string representation of your new objective function and our ```Objective``` enum type in the enum type section of the file. Afterwards, add function to the ```PartitionedGraph```, ```PartitionedHypergraph``` and ```SparsePartitionedHypergraph``` class that computes the value of your objective function.
