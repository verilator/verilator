# File Formats

The following is an overview of the input and output file formats which are used by Mt-KaHyPar.

**Important note:** For historical reasons, the hMetis and Metis input formats use indices starting at 1.
However, Mt-KaHyPar converts the indices when reading the files, so that they start at 0.
Any results obtained from the binary or one of the library interfaces will also use indices starting at 0 (i.e., shifted by -1 in comparison to the input file).

## hMetis Format for Input Hypergraphs

Per default, Mt-KaHyPar assumes that the input hypergraph is provided in the hMetis format:
[Unweighted Example](/tests/instances/unweighted_hypergraph.hgr), [Weighted Example](/tests/instances/hypergraph_with_node_and_edge_weights.hgr), [hMetis manual](https://karypis.github.io/glaros/files/sw/hmetis/manual.pdf)

The general format looks as follows:

```
% comment
num_hypergedges num_hypernodes [weight_type]
[hyperedge_weight_1] pin_1 pin_2 ... pin_i
...
[hyperedge_weight_m] pin_1 pin_2 ... pin_j
[hypernode_weight_1]
...
[hypernode_weight_n]
```

Any line that starts with ‘%’ is a comment line and is skipped.
The first line is a header containing two or three numbers describing the total number of hyperedges, the total number of hypernodes and the types of weights used by the hypergraph
(00/omitted = unweighted, 10 = node weights, 01 = edge weights, 11 = node and edge weights).

Afterwards, there is one line for each hyperedge which contains a list of the pins (hypernode IDs) of the hyperedge.
If hyperedge weights are used, there is an additional entry at the start of the line which is the weight of the hyperedge.

If no hypernode weights are used, this is the end of the file.
Otherwise, there is one line for each hypernode containing a single entry, which is the weight of the hypernode.

## Metis Format for Input Graphs

Mt-KaHyPar can also read input *graphs* in Metis format via `--file-format=metis`.
Also, target graphs for the Steiner tree metric need to be provided in the Metis format:
[Unweighted Example](/tests/instances/unweighted_graph.graph), [Weighted Example](/tests/instances/graph_with_node_and_edge_weights.graph), [Metis manual](https://karypis.github.io/glaros/files/sw/metis/manual.pdf)

**Important note:** Mt-KaHyPar only works on undirected graphs. Therefore, for each edge `u -> v` in the input file there *must be* a corresponding entry for `v -> u` with the same edge weight.

The general format looks as follows:

```
% comment
num_nodes num_edges [weight_type] [num_constraints]
[node_weight_1] neigbor_1 [edge_weight_1] neighbor_2 [edge_weight_2] ... neighbor_i [edge_weight_i]
...
[node_weight_n] neigbor_1 [edge_weight_1] neighbor_2 [edge_weight_2] ... neighbor_j [edge_weight_j]
```

Any line that starts with ‘%’ is a comment line and is skipped.
The first line is a header containing two or three numbers describing the total number of nodes, the total number of edges and the types of weights used by the graph
(00/omitted = unweighted, 10 = node weights, 01 = edge weights, 11 = node and edge weights).

The Metis format also supports multi-dimensional weights/constraints, where the dimension is specified with a fourth header entry.
However, multi-contraint partitioning is currently not supported by Mt-KaHyPar and thus the `num_constraints` entry is *not allowed* in input files.

Afterwards, there is one line for each node which contains the edges as an adjacency list, i.e., a list of the neighbor nodes (node IDs).
If node weights are used, there is an additional entry at the start of the line which is the weight of the node.
If edge weights are used, the adjacency list contains pairs as entries, with the first number being the node ID and the second number being the edge weight.

## Partition Output Format

When outputting the partitioning result via `--write-partition-file=true --partition-output-folder=<path/to/folder>`, Mt-KaHyPar uses the following format:

```
block_ID_1
...
block_ID_n
```

The file contains one line for each (hyper)node.
Each line contains a single number which is the ID of the block that the node is assigned to.

## hMetis Fix File Format

When partitioning with fixed vertices via `-f <path-to-fixed-vertex-file>`, Mt-KaHyPar assumes that the fixed vertices are provided in hMetis fix file format:
[hMetis manual](https://karypis.github.io/glaros/files/sw/hmetis/manual.pdf)

The format looks as follows:

```
-1|block_ID_1
...
-1|block_ID_n
```

The file contains one line for each (hyper)node.
Each line contains a single number which is the block ID if the node should be fixed, or -1 if the node can be assigned to any block.

## Conversion Tools for Other Formats

While we do not support other graph or hypergraph file formats as direct input, we provide some conversion tools. Each can be built via `make <tool-name>`.
 - `MtxToGraph`
 - `SnapToHgr`
 - `SnapToMetis`

Furthermore, there are conversion tools from hMetis/Metis format to other formats, which are especially useful for comparison benchmarks to other partitioning algorithms.
