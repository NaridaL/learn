# Purpose of Dijkstra's Algorithm

Given

1. a directed graph $G = (V, A)$,
2. an arc weight $l(a)$ for each arc $a in A$,
3. a root node $s in V$,

find the shortest path from the root node to any other node.

# Dijkstra's Algorithm: Implementation

Given directed graph $(V, A)$.

## Auxiliary data:

1. Temporary distance value for each node. $forall v in V: delta(v) in RR$
2. Bounded priority queue $Q$ of size $|V| - 1$, containing graph nodes and
   their distance value as

## Algorithm:

1. Set distance of start node $s$ to 0: $delta(s) := 0$.
2. Set distance of all other nodes to $infty$: $forall v in V \\ {s}: delta(v)
   := infty$
3. Insert all nodes into priority queue $Q$.
4. While the queue contains a node with a key/distance value less than infinite:
    5. Extract the minimum node $v$ from the queue.
    6. For each node $w$ which can be reached from $v$, update that node's
       distance if is reduced by taking that path. For each outgoing arc $a =
       (v, w) \in A$ such that $w \in Q$, set $delta(w) := min {delta(w),
       delta(v) + l(a)}$

# Dijkstra's Algorithm: Prerequisite

The weight of all edges must be greater or equal to zero. Given directed graph
$(V, A)$, $\forall a \in A: l(a) \ge 0$, where $l(a)$ is the length of edge $a$.

# Dijkstra's Algorithm: Complexity

$n = |V|$ (number of nodes)

$m = |A|$ (number of arcs)

$T(n)$: Worst case complexity for extraction/insertion of nodes in $Q$.

Worst case complexity: $O(T(n) \* (n + m))$

## Proof

Each node is extracted and inserted in Q at most once, which gives $O(T(n) \*
n)$.

Also, each arc $(v, w) \in A$ is touched at most once, when $v$ is extracted
from $Q$, which gives $O(T(n) \* m)$ for all decrease-key operations.

# Dijkstra's Algorithm: Heuristics

1. Do not insert nodes with distance $infty$ into the queue.
2. Early termination variant: stop when the target node has been extracted from
   the queue.
3. Bidirectional search: In the single-source, single-target case: Interleave
   two searches: one from $s$ on $G$ and one from $t$ on the inverse of $G$.
   When one node has been extracted by both searches,
4. When performing multiple searches on same large graph:

    Use heuristics 1. and 2.

    Instead of initializing the distances on every search, use a version
    counter. If the version counter does not match the current search, assume
    $delta(v) = infty$.

# Bounded Priority Queue: Methods

1. insert
2. extract minimum
3. find minimum
4. decrease key
5. number

# Path: Simple

A path is simple if it does not meet any node more than once.

# Path: Ordinary

An ordinary path in an undirected graph is a finite ordered sequence $({v_1,
v_2}, {v_2, v_3}, ..., {v\_(k-2), v\_(k-2)}, {v\_(k-2), v\_(k-2)})$.

An ordinary path in a directed graph is a finite ordered sequence $((v_1, v_2),
(v_2, v_3), ..., (v\_(k-2), v\_(k-2)), (v\_(k-2), v\_(k-2)))$.

# Path: Generalized

Also known as a weak path.

A generalized path in a directed graph is a finite sequence $((v_1, v_2), (v_2,
v_3), ..., (v\_(k-2), v\_(k-2)), (v\_(k-2), v\_(k-2)))$, such that turning some
($>= 0$) of the arcs yields an ordinary path.

# Graph: Reachability

A node $t in V$ is _reachable_ from $s in V$ if there is a path from $s$ to $t$
in the graph.

# Path: Internal Nodes

The internal nodes of a path are all the nodes of that path except the start and
end nodes. If the start or end nodes appear more than once on the path, they are
also internal nodes.

# Path: Disjointedness

Two paths are **edge-disjoint**, if they have no edge in common.

Two paths are **arc-disjoint**, if they have no arc in common.

Two paths are **(internally) node-disjoint** if they have no node in common that
is internal on either path.
