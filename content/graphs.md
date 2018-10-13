# Purpose of Dijkstra's Algorithm

Given

1. a directed graph $G = (V, A)$,
2. an arc weight $l(a)$ for each arc $a \in A$,
3. a root node $s \in V$,

find the shortest path from the root node to any other node.

# Dijkstra's Algorithm: Implementation

Given directed graph $(V, A)$.

## Auxiliary data:

1. Temporary distance value for each node. $\forall v \in V: 𝛿(v) \in
   \mathbb{R}$
2. Bounded priority queue $Q$ of size $|V| - 1$, containing graph nodes and
   their distance value as

## Algorithm:

1. Set distance of start node $s$ to 0: $𝛿(s) := 0$.
2. Set distance of all other nodes to $\infty$: $\forall v \in V \\ {s}: 𝛿(v) :=
   \infty$
3. Insert all nodes into priority queue $Q$.
4. While the queue contains a node with a key/distance value less than infinite:
    5. Extract the minimum node $v$ from the queue.
    6. For each node $w$ which can be reached from $v$, update that node's
       distance if is reduced by taking that path. For each outgoing arc $a =
       (v, w) \in A$ such that $w \in Q$, set $𝛿(w) := min {𝛿(w), 𝛿(v) + l(a)}$

# Dijkstra's Algorithm: Prerequisite

The weight of all edges must be greater or equal to zero. Given directed graph
$(V, A)$, $\forall a \in A: l(a) \ge 0$, where $l(a)$ is the length of edge $a$.

# Dijkstra's Algorith: Complexity

$n = |V|$ (number of nodes)

$m = |A|$ (number of arcs)

Worst case complexity: $O(T(n) \* (n + m))$

Worst case complexity for extraction/insertion of nodes in $Q$.

## Proof

Each node is extracted and inserted in Q at most once, which gives $O(T(n) \*
n)$.

Also, each arc $(v, w) \in A$ is touched at most once, when $v$ is extracted
from $Q$, which gives $O(T(n) \* m)$ for all decrease-key operations.

# Dijkstra's Algorithm: Heuristics

1. Do not insert nodes with distance $\infty$ into the queue.
2. Early termination variant: stop when the target node has been extracted from
   the queue.
3. Bidirectional search: In the single-source, single-target case: Interleave
   two searches: one from $s$ on $G$ and one from $t$ on the inverse of $G$.
   When one node has been extracted by both searches,
4. When performing multiple searches on same large graph:

    Use heuristics 1. and 2.

    Instead of initializing the distances on every search, use a version
    counter. If the version counter does not match the current search, assume
    $𝛿(v) = \infty$.
