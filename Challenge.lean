import Mathlib

/-!
# Erdős problem #548 (Erdős–Sós conjecture): proof

*Reference:* [erdosproblems.com/548](https://www.erdosproblems.com/548)

The Erdős–Sós conjecture (1962) states that every graph on `n` vertices with more than `(k-2)n/2`
edges contains every tree on `k` vertices. The weaker statement with `(k-2)n` edges is an easy
induction, and the conjecture was proved in many special cases (for example for trees of bounded
diameter, for spiders, and for large `k` relative to `n` in the work announced by Ajtai, Komlós,
Simonovits and Szemerédi), but it remained open in general; Chung's collection of Erdős's graph
problems called it "one of the most tantalizing problems in extremal graph theory".
erdosproblems.com lists a $100 prize and states the problem as: let `n ≥ k+1`; every graph on `n`
vertices with at least `(k-1)n/2 + 1` edges contains every tree on `k+1` vertices.

The conjecture is **true**. Formally, the theorem proved is `Erdos548.erdos_548`, the statement of
the FrontierMath Erdős benchmark: for all `n, k` with `k + 1 ≤ n`, every `G : SimpleGraph (Fin n)`
with `(k-1)/2 · n + 1 ≤ |E(G)|` (as rationals) contains every tree `T : SimpleGraph (Fin (k+1))`
as a (not necessarily induced) subgraph, `T.IsContained G`.

This file is the small statement surface a reader should audit: the theorem `Erdos548.erdos_548`
below is the compared declaration, and the conjecture is proved in `Solution.lean` and the module
it imports. Only the theorem's `sorry` is filled in there.

The statement is copied verbatim from the FrontierMath Erdős benchmark file
`apn/data/erdos_autoformalized/Isolated/Erdos548.erdos_548.lean` in [LeanOpenProblems](https://github.com/epoch-research/LeanOpenProblems) at commit
`77882c437ca1dfefab3b27fa00f1d29788100311` (formalized by Epoch AI's autoformalization pipeline and reviewed by
Thomas F. Bloom; the problem had no statement in Formal Conjectures). It is exactly the
statement the AI system was given.
-/
open SimpleGraph

namespace Erdos548

/--
**Erdős problem #548 (the Erdős–Sós conjecture).** Let $n\geq k+1$. Every graph on $n$ vertices with
at least $\frac{k-1}{2}n+1$ edges contains every tree on $k+1$ vertices (as a subgraph, not
necessarily induced). This is the statement of the FrontierMath Erdős benchmark, following the
phrasing on erdosproblems.com; see the README for its relation to the classical phrasing
"more than $\frac{k-2}{2}n$ edges, trees on $k$ vertices".
-/
theorem erdos_548 :
    ∀ (n k : ℕ), k + 1 ≤ n → ∀ G : SimpleGraph (Fin n),
      ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ) →
        ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T.IsContained G := by
  sorry

end Erdos548
