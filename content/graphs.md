# Purpose of Dijkstra's Algorithm

Given

1. a directed graph §G = (V, A)§,
2. an arc weight §l(a)§ for each arc §a in A§,
3. a root node §s in V§,

find the shortest path from the root node to any other node.

# Dijkstra's Algorithm: Implementation

Given directed graph §(V, A)§.

## Auxiliary data:

1. Temporary distance value for each node. §forall v in V: delta(v) in RR§
2. Bounded priority queue §Q§ of size §|V| - 1§, containing graph nodes and
   their distance value as

## Algorithm:

1. Set distance of start node §s§ to 0: §delta(s) := 0§.
2. Set distance of all other nodes to §infty§: §forall v in V setminus {s}:
   delta(v) := infty§
3. Insert all nodes into priority queue §Q§.
4. While the queue contains a node with a key/distance value less than infinite:
    5. Extract the minimum node §v§ from the queue.
    6. For each node §w§ which can be reached from §v§, update that node's
       distance if is reduced by taking that path. For each outgoing arc §a =
       (v, w) \in A§ such that §w \in Q§, set §delta(w) := min {delta(w),
       delta(v) + l(a)}§

# Dijkstra's Algorithm: Prerequisite

The weight of all edges must be greater or equal to zero. Given directed graph
§(V, A)§, §\forall a \in A: l(a) \ge 0§, where §l(a)§ is the length of edge §a§.

# Dijkstra's Algorithm: Complexity

§n = |V|§ (number of nodes)

§m = |A|§ (number of arcs)

§T(n)§: Worst case complexity for extraction/insertion of nodes in §Q§.

Worst case complexity: §O(T(n) \* (n + m))§

## Proof

Each node is extracted and inserted in Q at most once, which gives §O(T(n) \*
n)§.

Also, each arc §(v, w) \in A§ is touched at most once, when §v§ is extracted
from §Q§, which gives §O(T(n) \* m)§ for all decrease-key operations.

# Dijkstra's Algorithm: Heuristics

1. Do not insert nodes with distance §infty§ into the queue.
2. Early termination variant: stop when the target node has been extracted from
   the queue.
3. Bidirectional search: In the single-source, single-target case: Interleave
   two searches: one from §s§ on §G§ and one from §t§ on the inverse of §G§.
   When one node has been extracted by both searches,
4. When performing multiple searches on same large graph:

    Use heuristics 1. and 2.

    Instead of initializing the distances on every search, use a version
    counter. If the version counter does not match the current search, assume
    §delta(v) = infty§.

# Bounded Priority Queue: Methods

1. insert
2. extract minimum
3. find minimum
4. decrease key
5. number

# Path: Simple

A path is simple if it does not meet any node more than once.

# Path: Ordinary

An ordinary path in an undirected graph is a finite ordered sequence §({v_1,
v_2}, {v_2, v_3}, ..., {v\_(k-2), v\_(k-2)}, {v\_(k-2), v\_(k-2)})§.

An ordinary path in a directed graph is a finite ordered sequence §((v_1, v_2),
(v_2, v_3), ..., (v\_(k-2), v\_(k-2)), (v\_(k-2), v\_(k-2)))§.

# Path: Generalized

Also known as a weak path.

A generalized path in a directed graph is a finite sequence §((v_1, v_2), (v_2,
v_3), ..., (v\_(k-2), v\_(k-2)), (v\_(k-2), v\_(k-2)))§, such that turning some
(§>= 0§) of the arcs yields an ordinary path.

# Graph: Reachability

A node §t in V§ is _reachable_ from §s in V§ if there is a path from §s§ to §t§
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

# Inclusion-Minimal/Maximal

Let §ccS§ (read calligraphic S) be a set of (multi)sets.

1. A set §S in ccS§ is **inclusion-minimal** if no other set (in §ccS§) is a
   subset of it. (If §not EE S' in ccS setminus S: S' sub S§)

2. A set §S in ccS§ is **inclusion-maximal** if no other set (in §ccS§) is a
   proper superset of it / if it is not a proper subset of any other set (in
   §ccS§). (If §not EE S' in ccS setminus S: S' sup S§)

<!-- Let $\mathcal{S}$ (read calligraphic S) be a set of (multi)sets.

1. A set $S\in\mathcal{S}$ is **inclusion-minimal** (resp.
   **inclusion-maximal**) in $\mathcal{S}$ if $S'\subsetneq S$ (resp.
   $S'\supsetneq S$) for no $S'\in\mathcal{S}\setminus\{S\}$.
2. A set $S\in\mathcal{S}$ is **cardinality-minimal** (resp.
   **cardinality-maximal**) in $\mathcal{S}$ if $|S'|<|S|$ (resp. $|S'|>|S|$)
   for no $S'\in\mathcal{S}\setminus\{S\}$. -->

# Cardinality-Minimal/Maximal

Let §ccS§ (read calligraphic S) be a set of (multi)sets.

1. A set §S in ccS§ is **cardinality-minimal** if it has the smallest number of
   elements of any set (in §ccS§). (§AA S' in ccS: |S| <= |S'|§)
2. A set §S in ccS§ is **cardinality-maximal** if it has the largest number of
   elements of any set (in §ccS§). (§AA S' in ccS: |S| >= |S'|§)

# Connectedness

An **undirected graph** is said to be **connected** if every pair of nodes is
connected by a path.

It is §k§-connected if every pair of nodes is connected by at least §k§
**internally node-disjoint paths**. _Connected_ means _1-connected_.
_2-connected_ is synonmous with _biconnected_.

# Weak Connectedness

A **directed graph** is said to be _weakly connected_ if every pair of nodes is
connected by a **generalized/weak path**.

# Strong Connectedness

A **directed graph** is said to be _strongly connected_ if every **ordered
pair** of nodes is connected by a an **ordinary path**.

# Articulation Node

An arcticulation node in a **connected undirected graph** is a node such that
the graph would become disconnected if it and its incident arcs were removed.

# Bridge

A bridge in a **connected undirected graph** is an edge such that the graph
would become disconnected if it were removed.

# Subgraph

Let §G_1 = (V_1, E_1)§ and §G_2 = (V_2, E_2)§ be two simple undirected graphs.

§G_1§ is a subgraph of §G_2§ if there is §V' sube V_2§ and bijection §varphi:V_1
-> V'§ such that §{v, w} in E_1§ implies §{varphi(v), varphi(w)} in E_2§.

If all the edges of §G_2§ defined on §V'§ are also in §G_1§, we say §G_2§ is the
graph **induced** by §V'§.

# Spanning subgraph

A spanning subgraph of an undirected or directed graph §G§ is a subgraph which
contains all nodes of §G§.

# Graph: Simple

A directed or undirected graph is simple, if:

1. No node is paired with itself in §A§/§E§.
2. The multiset §A§/§E§ is a sete. I.e., no edge is "double".

# Arc: Lexicographically Smaller

Assuming, for each node, an arbitrary but fixed ordering of outgoing arcs, an
arc §(v,w)§ preceding and arc §(v, w')§ is lexicographically smaller than §(v,
w')§.

# Path: Lexicographically Smaller

Let §p§ and §p'§ be two paths that start from the same node §v in V§. Let §w§ be
the last common node such that the subpaths of §p§ and §p'§ are identical. If
the next arc of §p§ from §w§ onwards is lexicographically smaller than the next
arc of §p'§, §p§ is **lexicographically smaller** than §p'§.

The lexicograpically smallest path from §v in V§ to §w in V§ is **well defined**
and **unique**.

# Node: Lexicographically Smaller

**With respect to a starting node §s in V§**, a node §v in V§ is
lexicographically smaller than §w in V§ if the lexicographically smallest path
from §s§ to §v§ is lexicographically smaller than the lexicographically smallest
path from §s§ to §w§.

# Node/Path: Lexicographical Order

A node §v in V§ is lexicographically smaller than a path §p§ if §v§ does not
belong to §p§ and the lexicographically smallest path from the start of §p§ to
§v§ precedes §p§.

A node §v in V§ is lexicographically larger than a path §p§ if §v§ does not
belong to §p§ and the **lexicographically smallest** path from the start of §p§
to §v§ succeeds §p§.

# Forest

A _forest_ is a **cycle-free undirected graph**.

For a forest §G = (V, E)§ Let §n = |V|§ be the number of nodes, §m = |E|§ the
number of edges, and §k§ the number of trees in the forest. Then it is §m = n -
k§.

Proof?

# Tree

A _tree_ is a **connected forest**.

# Branching

A _branching_ is a **cycle-free directed** graph such that the **indegree** of
each node is zero or one.

# Arborescence

An _arborescence_ is a **branching** such that **exactly one node has indegree
zero**.

For branchings, this condition is equivalent to weak connectedness.

Also known as a **rooted tree**, the unique node with indegree zero is the
**root**.

# Head/Tail

Let §G = (V, A)§ be a directed graph.

For an arc §a = (v, w) in A§, §v§ is the _tail_ of §a§, and §w§ is the _head_ of
§a§.

# Outgoing/Incoming

Let §G = (V, A)§ be a directed graph.

An arc §(v, w) in A§ is an outgoing arc of §v§ and an incoming arc of §w§.

# Outdegree/Indegree

Let §G = (V, A)§ be a directed graph.

The outdegree of a node §v in V§ is the number of **outgoing arcs**, the
indegree of §v§ is the number of **incoming arcs**.

# Depth-First Search: Invariant/Variant

Given:

1. A stack §S§ whose elements are nodes in §V§.
2. Each node has a **current arc** §a_v in V§, which is either void or an
   outgoing arc §a_v = (v, w)§ of §v§. (May be viewed as an iterator over the
   list of all outgoing arcs.)

**Invariant**: Before and after each iteration:

1. §S§ forms a path §p§ from the start node §s§ to some other node, that is, the
   order of the ndoes on §p§ is the order in which they appear in §S§ (start
   node §s§ at the bottom of §S§).
2. For each node not yet seen, the current arc is the first arc (or void if
   outdegree = 0).
3. For each node §v§ on §p§:
    1. If there are arcs §(v, w) in A§ such that w is not yet seen, the current
       arc equals or precedes the first such arc.
    2. The subpath of §p§ from the start node §s§ to §v§ is the
       lexicographically first §(s, v)§-path.
4. The nodes on §p§ are seen but not finished. Let §p + a§ denote the
   concatenation of §p§ with the current arc §a§ of the last node of §p§. The
   nodes that lexicographically precede §p + a§ are seen and finished, and the
   nodes that lexicographically succeed §p + a§ are neither seen nor finished.
   (Nothing is said about the head of §a§).

**Variant**: Either one node is seen for the first time or finished, or
(inclusive) the current arc of one node is moved forward.

# Breadth-First Search

§Q = "(" ubrace(v_1, ..., v_l)\_k, ubrace(v\_(l+1), ... v_n)\_(k+1) ")"§
