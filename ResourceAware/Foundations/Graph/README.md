# Graph Foundations

This folder contains the graph-facing foundation layer used by resource-aware algorithms. It
separates four concerns:

1. experimental concrete graph structures,
2. a stable graph interface for algorithms,
3. graph-representation resource models,
4. adapters from the concrete API to the stable interface.

`ThirdParty/Graph.lean` is a local experimental copy of the graph API proposed in CSLib PR #503.
`GraphAdapters.lean` is its only consumer in the algorithm-facing stack. Algorithm-specific state,
traces, and traversal programs live under `ResourceAware/Algorithms` or `TextbookAlgorithms`.

## File Map

The modules used by this layer are:

* `ThirdParty/Graph.lean`

  Defines the experimental concrete graph structures in `ResourceAware.Graph.Concrete`. Its
  source is CSLib PR #503, and its copyright and authorship are preserved.

* `Interface.lean`

  Defines the stable interface that graph algorithms should depend on:

  * `Interface`
  * `NeighborAccess`
  * `WeightedEdgeView`
  * `OutgoingEdge`
  * `WeightedNeighborAccess`
  * `VertexEnumeration`
  * `GraphVertex`
  * `VertexIndex`
  * `Reachable`

  This file is intentionally independent of any one concrete graph representation.

* `ResourceModel.lean`

  Defines graph-side resource models for executable graph representations:

  * `ResourceModel`
  * `WeightedResourceModel`
  * `ResourceModel.ofAdjacencyList`
  * `ResourceModel.ofAdjacencyMatrix`
  * `WeightedResourceModel.ofAdjacencyList`

  This file records graph storage and neighbor-query costs.  It deliberately does not contain
  BFS state, DFS stack state, traces, visited tables, levels, or traversal-tree storage.

* `GraphAdapters.lean`

  Connects the concrete graph structures in `ThirdParty/Graph.lean` to the stable interface in
  `Interface.lean`, including a label-to-weight adapter for `Concrete.DiGraph`.

  This file is the place to update when concrete graph APIs change.

## Layering

The intended dependency direction is:

```text
Experimental concrete graph definitions
  ThirdParty/Graph.lean
        |
        v
Concrete-to-stable adapters
  ResourceAware/Foundations/Graph/GraphAdapters.lean
        |
        v
Stable semantic/operational graph interface
  ResourceAware/Foundations/Graph/Interface.lean
        |
        v
Graph representation resource models
  ResourceAware/Foundations/Graph/ResourceModel.lean
        |
        v
Algorithm infrastructure and case studies
  ResourceAware/Algorithms/GraphTraversal
  TextbookAlgorithms/KleinbergTardos/Chapter03/BFS
  TextbookAlgorithms/KleinbergTardos/Chapter03/DFS
  TextbookAlgorithms/KleinbergTardos/Chapter04/Dijkstra
```

`Interface.lean` and `ResourceModel.lean` should not import BFS, DFS, `TraceM`, `TimeM`, or graph
traversal models. Those modules are algorithm-side consumers of the graph interface.

## Concrete Graph Structures

`ThirdParty/Graph.lean` defines the concrete graph-like structures proposed in CSLib PR #503 under
the `ResourceAware.Graph.Concrete` namespace.

For undirected graphs:

```lean
structure Graph (alpha beta : Type*) where
  vertexSet : Set alpha
  edgeSet : Set (Edge alpha beta)
  incidence' : ...
```

```lean
structure SimpleGraph (alpha : Type*) where
  vertexSet : Set alpha
  edgeSet : Set (Sym2 alpha)
  incidence' : ...
  loopless' : ...
```

For directed graphs:

```lean
structure DiGraph (alpha beta : Type*) where
  vertexSet : Set alpha
  edgeSet : Set (Arc alpha beta)
  incidence' : ...
```

```lean
structure SimpleDiGraph (alpha : Type*) where
  vertexSet : Set alpha
  edgeSet : Set (Prod alpha alpha)
  incidence' : ...
  loopless' : ...
```

These are useful for formal graph theory and for future algorithm adapters, but algorithms do
not need to depend on them directly.

## Stable Graph Interface

`Interface.lean` defines:

```lean
structure Interface (G : Type u) (V : Type v) where
  vertexSet : G -> Set V
  Adj : G -> V -> V -> Prop
  adj_source_mem : ...
  adj_target_mem : ...
```

This is the semantic graph view:

```text
which vertices exist?
when is one vertex adjacent to another?
does adjacency imply both endpoints are vertices?
```

For undirected graphs, expose `Adj` as a symmetric relation.  For directed graphs, expose
`Adj g u v` as the directed edge relation from `u` to `v`.

The same file also defines:

```lean
structure NeighborAccess (Gamma : Interface G V) where
  outNeighbors : G -> V -> List V
  nodup : ...
  sound : ...
  complete : ...
```

This is the executable neighbor-query view:

```text
given a graph g and vertex u, produce the finite list of outgoing neighbors of u
```

It is separate from `Interface` because a clean semantic graph relation does not always come
with a chosen executable enumeration.

Finally:

```lean
structure VertexEnumeration (Gamma : Interface G V) where
  vertices : G -> List V
  nodup : ...
  sound : ...
  complete : ...
```

This supplies the finite vertex list needed by executable algorithms and resource models.

`VertexEnumeration` says which vertices exist. Some representations additionally prepare:

```lean
abbrev GraphVertex (Gamma : Interface G V) (g : G) :=
  {v : V // Gamma.IsVertex g v}

abbrev VertexIndex (Gamma : Interface G V)
    (enumeration : VertexEnumeration Gamma) (g : G) :=
  GraphVertex Gamma g ≃ Fin (enumeration.vertices g).length
```

`VertexIndex` optionally gives those vertices dense names. It is graph-owned representation
infrastructure, not part of an algorithm's mathematical specification and not a restriction
that the ambient vertex type itself be `Fin n`. Positional heaps and array-backed algorithm
state can encode graph vertices for table access and decode identifiers before querying the
graph.

A concrete backend must supply this bijection through stable IDs, direct inverse lookup,
identity indexing, or direct pattern matching for a fixed graph. Implementations must not hide
linear search such as `findIdx` or repeated scans of the vertex enumeration.

## Weighted Edge Access

`WeightedEdgeView` extends an existing `Interface`; it does not duplicate vertex sets,
adjacency, or reachability. Its `Arc` relation identifies an edge occurrence together with
its source, target, and generic weight. `WeightedNeighborAccess` returns ordered
`OutgoingEdge` lists and requires completeness for whole edge occurrences, so parallel edges
to the same target are preserved.

Concrete `DiGraph` labels are interpreted through `diGraphWeightedEdgeView` using a
`Label -> Weight` function. The concrete `Arc` is the edge identity. Because the concrete
edge collection is a `Set`, otherwise-identical parallel occurrences need distinct labels;
`WeightedLabel EdgeId Weight` is provided as a convenience for that case.

## Reachability

`Reachable` is a stable reachability predicate:

```lean
inductive Reachable (Gamma : Interface G V) (g : G) : V -> V -> Prop
  | refl ...
  | step ...
```

Algorithm correctness theorems should be stated against this predicate when possible, rather
than against a particular concrete graph API.

This lets a BFS or DFS theorem say:

```text
the algorithm reaches exactly the vertices reachable from the source
```

without committing to `Graph`, `SimpleGraph`, an adjacency list, a matrix, or a mathlib graph.

## Resource Models

`ResourceModel.lean` defines:

```lean
structure ResourceModel (G : Type u) (V : Type v) where
  interface : Interface G V
  vertexEnumeration : VertexEnumeration interface
  neighborAccess : NeighborAccess interface
  neighborCost : G -> V -> Nat
  graphSpace : G -> Nat
```

A `ResourceModel` packages the graph-side data needed by resource-aware algorithms:

```text
semantic graph relation
finite vertex list
executable neighbor query
cost of one neighbor query
storage used by the graph representation
```

It intentionally does not include algorithm working storage.  For example:

* BFS layer storage belongs to `KleinbergBFS.spaceUsage`.
* DFS stack storage belongs to `KleinbergDFS.spaceUsage`.
* visited tables, level tables, and tree output belong to graph traversal backend models.

`WeightedResourceModel` contains a complete base `ResourceModel` and adds only the weighted
view, weighted outgoing access, and weighted query cost. Its unit adjacency-list constructor
charges one unit per returned edge occurrence. Consequently, summing one scan of every source
row equals `directedEdgeOccurrenceCount`, the graph-side `m` used by the Dijkstra complexity
proof.

## Adjacency Lists

The adjacency-list constructor is:

```lean
ResourceModel.ofAdjacencyList
```

It models:

```text
neighborCost(g, u) = outdegree(u)
graphSpace(g) = n + m
```

where:

```text
n = number of vertices in the selected vertex enumeration
m = total number of adjacency-list entries
```

This matches the textbook adjacency-list model:

```text
space: O(n + m)
neighbor iteration: constant work per neighbor
```

## Adjacency Matrices

The adjacency-matrix constructor is:

```lean
ResourceModel.ofAdjacencyMatrix
```

It models:

```text
neighborCost(g, u) = n
graphSpace(g) = n * n
```

The matrix neighbor query is implemented by scanning the whole vertex enumeration and
filtering by a Boolean edge predicate:

```lean
matrixOutNeighbors
```

This matches the textbook adjacency-matrix model:

```text
space: O(n^2)
neighbor query by scanning a row: O(n)
```

The vertex enumeration is still operationally needed so the matrix model can scan all possible
targets.  It is not counted in `graphSpace` for the current textbook-facing model.

## Adapters

`GraphAdapters.lean` connects concrete graph structures to the stable interface.

For example:

```lean
def simpleGraphInterface (alpha : Type u) :
    Interface (Concrete.SimpleGraph alpha) alpha
```

The adapter translates the concrete representation into:

```text
vertexSet
Adj
adj_source_mem
adj_target_mem
```

The concrete definitions may evolve while the upstream PR is open. The adapter should absorb
those changes so algorithm modules continue to depend on the stable interface.

## What Belongs Here

Add definitions here when they are graph-foundational:

* experimental concrete graph definitions being evaluated for this project,
* a stable semantic interface,
* an executable neighbor-access interface,
* an executable weighted-edge occurrence interface,
* a finite vertex enumeration interface,
* a graph representation resource model,
* adapters from concrete graphs to stable interfaces,
* representation-level graph storage costs.

## What Does Not Belong Here

Do not put the following here:

* BFS or DFS programs,
* free-monad traversal signatures,
* `TraceM` or `TimeM`,
* visited table implementations,
* level-output implementations,
* traversal-tree output implementations,
* BFS layer storage,
* DFS stack storage,
* algorithm-specific exact event traces,
* shortest-path state, nonnegative-weight hypotheses, or Dijkstra's algorithm.

Those belong under:

```text
ResourceAware/Effects/
ResourceAware/Algorithms/
TextbookAlgorithms/
```

The graph foundations layer should stay reusable by many algorithms.

## Current Consumers

The current resource-aware graph case studies use this folder as follows:

```text
BFS and DFS algorithms
  use GraphTraversal.Program
        |
        v
GraphTraversal.Model
  uses ResourceModel for graph-side costs
        |
        v
ResourceAware.Graph.ResourceModel
  uses Interface, NeighborAccess, VertexEnumeration

Dijkstra
  uses WeightedResourceModel, WeightedEdgeView, and WeightedNeighborAccess
```

The BFS and DFS toy tests compare:

```text
same algorithm + adjacency-list ResourceModel
same algorithm + adjacency-matrix ResourceModel
```

This is how the tests expose Kleinberg's difference between adjacency-list and
adjacency-matrix graph representations.

## Adding a New Representation

To add a new graph representation:

1. Provide or reuse an `Interface`.
2. Provide a `VertexEnumeration`, if the algorithm/resource analysis needs finite vertices.
3. Provide a `NeighborAccess`.
4. Define `neighborCost`.
5. Define `graphSpace`.
6. Package them in a `ResourceModel`.

For example, a compressed-sparse-row graph representation could get its own constructor:

```lean
def ResourceModel.ofCSR ... : ResourceModel G V := ...
```

without changing BFS, DFS, or the shared traversal model.

## Design Rule

The main design rule is:

```text
Foundations describe what graphs are and what graph representations cost.
Algorithms describe what traversals do.
Family models connect those choices through the generic program interpreter.
```

Keeping this boundary clear is what lets BFS, DFS, and future graph algorithms share the same
graph representations and cost models.
