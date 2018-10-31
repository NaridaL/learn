# Types of Algorithmic Problems

1.  **Decision Problem**: is there a solution or not.
2.  **Construction problem**: if there is a solution, construct one.
3.  **Enumeration problem**: give all solutions.
4.  **Optimization problem**: construct a solution that is optimal (or at least
    nearly optimal) subject to a given objective.

Construction and optimization problems are by far the most important in
practice.

Algorithms for decision problems are typically constructive. Construction
problems may be viewed as an optimization problem with all solutions having
equal value.

Many generic algorithms are applicable only to optimization problems.

--> Focus on optimization problems.

# Optimization Problem: Ingredients

1.  Feasible inputs (a.k.a. instances). (Zulässigen Inputs/Eingaben/Instanzen)

    A set §ccI§ of potential inputs.

2.  Feasible outputs for a given instance.

    For each §I in ccI§ a set §F_I§ of **feasible solutions**.

3.  The objective.

    Objective function §obj_I : F_I -> RR§ and a direction: **minimizing** or
    **maximizing**.

4.  Task:

    1.  Determine whether §F_I != 0§ and,
    2.  if so, find §x in F_I§ such that

        §obj_I(x) = {(min,{obj_I(y)|y in F_I}),(max,{obj_I(y)|y in F_I}):}§

# Optimization Problem: Matching

1. Input: undirected graph §G = (V, E)§
2. Feasible output: as set §M sube E§ such that no two edges in M have an
   incident node in common. §<=>§ §M§ is called a **matching** of §G§.
3. Objective: maximizing §#M§.

# Feasible Solutions: Specification

1. Typically the sets §F_I§ are specified by ground sets §S_I§ and side
   constraints.
2. **Side constraint**: a predicate on §S_I§.
3. For an instance §I in ccI§, let §ccSccC_I§ denote the set of all side
   constraints for §I§.
4. **Feasible solution** §{x in S_I | forall c in ccSC_I : c(x) }§

# Optimization Problem: TSP

1. §ccI§: set of quadratic real-valued matrices §D§:

    §D[i, j]§ = distance from point §i§ to point §j§.

2. For an §(n x n)§-matrix §I in ccI§, §S_I§ may then be the set of all
   quadratic 0/1-matrices §X§ of size §n§:

    §X[i, j] = 1 <=> j§ follows §i§ immediately on the cycle corresponding to
    §X§.

3. Objective for matrix size n:

    minimizing §sum\_(i=1)^n sum\_(j=1)^n D[i, j] \* X[i, j]§

# Feasibility

<!-- prettier-ignore -->
1. An instance §I in ccI§ of an algorithmic problem is called _feasible_, if
   §F_I != 0§, otherwise _infeasible_.

2) An instance §I in ccI§ of a minimization (resp. maximization) problem is
   called _bounded_, if the objective function is bounded over §F_I§ from below
   (resp. above), otherwise it is called unbounded.

# Neighborhoods

§I§: instance of an optimization problem.

§F_I§ set of feasible solutions of §I§.

§obj_I : F_I |-> RR§: objective function.

Given a feasible point §f in F_I§, it is useful to define a set §N_I(f)§ of
points which are **"close" is some sense** to the point §f§.

A _neighborhood_ is a mapping §N_I : F_I |-> 2^(F_I)§.

# Neighborhood: Exact

An optimization problem neighborhood is _exact_ **iff. every local minimum is also a global minimum**.