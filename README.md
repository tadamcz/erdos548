# Erdős problem #548 (Erdős–Sós conjecture): proof

[![CI](https://github.com/tadamcz/erdos548/actions/workflows/ci.yml/badge.svg)](https://github.com/tadamcz/erdos548/actions/workflows/ci.yml)

> **Note.** This README, the documentation in `Challenge.lean` and `formalization.yaml` were machine-written by Claude (Anthropic)
> at the direction of Tom Adamczewski, from the FrontierMath Erdős paper, the benchmark files and the module documentation inside
> the proof files, and reviewed by him. The Lean proofs themselves were written by GPT-6 Astra, as described below.

Machine-checked proof of [Erdős problem #548](https://www.erdosproblems.com/548) in Lean 4 with Mathlib, found autonomously by a
pre-release version of **GPT-6 Astra** (OpenAI) in the **FrontierMath Erdős** benchmark (Adamczewski and Bloom, 2026). The
repository packages the AI-written proof for the [Palomar registry](https://palomar-registry.org/): `Challenge.lean` is the
small statement a reader audits, `Solution.lean` proves it, and [Comparator](https://github.com/leanprover/comparator) checks that the two
statements coincide and that only the standard axioms are used.

## The result

The Erdős–Sós conjecture (1962) states that every graph on `n` vertices with more than `(k-2)n/2` edges contains every
tree on `k` vertices. The weaker statement with `(k-2)n` edges is an easy induction, and the conjecture was proved in
many special cases (for example for trees of bounded diameter, for spiders, and for large `k` relative to `n` in the
work announced by Ajtai, Komlós, Simonovits and Szemerédi), but it remained open in general; Chung's collection of
Erdős's graph problems called it "one of the most tantalizing problems in extremal graph theory". erdosproblems.com
lists a $100 prize and states the problem as: let `n ≥ k+1`; every graph on `n` vertices with at least `(k-1)n/2 + 1`
edges contains every tree on `k+1` vertices.

The conjecture is **true**. Formally, the theorem proved is `Erdos548.erdos_548`, the statement of the FrontierMath
Erdős benchmark: for all `n, k` with `k + 1 ≤ n`, every `G : SimpleGraph (Fin n)` with `(k-1)/2 · n + 1 ≤ |E(G)|` (as
rationals) contains every tree `T : SimpleGraph (Fin (k+1))` as a (not necessarily induced) subgraph, `T.IsContained G`.

The compared declaration, from `Challenge.lean`:

```lean
theorem erdos_548 :
    ∀ (n k : ℕ), k + 1 ≤ n → ∀ G : SimpleGraph (Fin n),
      ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ) →
        ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T.IsContained G := by
  sorry
```



**Fidelity.** Relative to the cited source (the erdosproblems.com statement) there is no divergence: the compared theorem is its
direct formalisation, with trees on `k+1` vertices and the hypothesis `|E| ≥ (k-1)n/2 + 1`. Relative to the classical
phrasing of the Erdős–Sós conjecture ("more than `(t-2)n/2` edges, trees on `t` vertices"; here `t = k+1`) there is one
marginal difference: when `(k-1)n` is odd, `|E| > (k-1)n/2` already holds with one edge fewer than `|E| ≥ (k-1)n/2 + 1`
requires, so in that parity case the compared theorem assumes half an edge more and is very slightly weaker than the
classical statement (the classical statement implies it, not conversely). The Lean proof's internal counting lemma
derives `2|E(G)| ≤ (k-1)n` whenever the tree is absent, which is the sharp classical bound, but only the advertised
statement is compared. The vertex type `Fin n` loses no generality; `G.edgeSet.ncard` is the number of edges; `T.IsTree`
and `T.IsContained G` are Mathlib's notions (containment as a not necessarily induced subgraph); `k + 1 ≤ n` is `n ≥
k+1`.

## Provenance

**Benchmark.** FrontierMath Erdős (Adamczewski and Bloom, 2026) evaluates AI systems on 68 open Erdős problems selected by Thomas F. Bloom, in the Lean proof
assistant, autonomously and under a fixed, disclosed budget per attempt. The
agent works in a network-isolated Docker container with a Lean 4 toolchain (v4.27.0) and Mathlib, SageMath and Python; its final
`Spec.lean` is checked in a separate pristine container by Comparator against the trusted statement, permitting only `propext`,
`Quot.sound` and `Classical.choice`. The benchmark, harness and statements are public at
[epoch-research/LeanOpenProblems](https://github.com/epoch-research/LeanOpenProblems); the paper is in preparation. No human saw or steered the proof search.

**Statement.** The problem had no statement in Formal Conjectures. The statement was produced by the benchmark authors' autoformalization pipeline and reviewed for faithfulness by Thomas F. Bloom; the file the model received is [`apn/data/erdos_autoformalized/Isolated/Erdos548.erdos_548.lean`](https://github.com/epoch-research/LeanOpenProblems/blob/77882c437ca1dfefab3b27fa00f1d29788100311/apn/data/erdos_autoformalized/Isolated/Erdos548.erdos_548.lean).

**Resolutions.** One attempt resolved this statement.
"Default configuration" is the deepagent-based agent with subagents, memory and an offline arXiv snapshot under the benchmark's
fixed per-attempt budget; "ReAct agent, larger budget" is a basic agent given a larger budget. The file names carry the harness's
metered cost and working time as released with the paper; the paper is the reference for those figures. The Inspect transcripts are
linked for the record (access may be restricted).

| Module | Role | Attempt | Inspect log |
|---|---|---|---|
| `Erdos548/Resolutions/Erdos548_192usd_21h.lean` | **primary** (wired to `Solution.lean`) | ReAct agent, larger budget, 26 Aug 2026 | [transcript](https://viewer.hawk.hawkbench.com/permalink/sample/DtNfGbQAp2VSeoBwkKV8bE) |

## Proof account

The accounts below paraphrase the module documentation the model wrote inside each file; they describe the Lean proofs actually
present. They are not a human verification of the mathematics beyond what Comparator establishes.

**`Erdos548_192usd_21h`** (ReAct agent, larger budget, 26 Aug 2026). Counts, for each permutation word of the host vertices, the prefixes ending at a neighbour of the first vertex that support a rooted copy of the target tree. Two reversible word operations (rotating the first qualifying prefix; reversing both blocks at a cut, which moves the root to a newly attached leaf) drive an induction on the tree, giving `rooted_word_tree_bound`: the number of adjacency-marked states, exactly `2|E(G)|(n-1)!`, is at most the rooted-copy count plus `(t-2) n!`. If the tree is absent this yields `2|E(G)| ≤ (t-2) n`, contradicting the edge density.

**Informal summary from the FrontierMath Erdős paper** (Thomas F. Bloom, appendix; a fuller sketch is on the problem page of
erdosproblems.com): The proof is surprisingly short and elegant. It considers the number of pairs `(π, j)` where `π = (v_1 ⋯ v_n)` is an
ordering of the vertices of `G` and `2 ≤ j ≤ n` is a label such that `v_1 v_j` is an edge. The number of such pairs is
`2m(n-1)!`, where `m` is the number of edges. On the other hand, for any fixed tree `T` on `k` vertices, an inductive
argument shows this number to be at most `C(T) + (k-2)n!`, where `C(T)` counts the pairs in which `(v_1 ⋯ v_j)` contains
a copy of `T` rooted at `v_1`. If `G` contains no copy of `T` then `C(T) = 0`, and rearranging yields the result.

## Repository layout

- `Challenge.lean` — the statement surface: definitions copied verbatim from the benchmark statement and the compared theorem with `sorry`.
- `Solution.lean` — imports the primary resolution module, in whose environment the compared theorem is proved.
- `Erdos548.lean`, `Erdos548/Resolutions/` — the AI-written proof module(s); `Erdos548.lean` imports the primary one.

- `comparator.json` — Comparator configuration naming `Erdos548.erdos_548`.
- `formalization.yaml` — structured metadata (provenance, sources, classification, automation, review) in the mathlib-initiative v0.4 format.
- `provenance/` — SHA-256 sums of the benchmark output files and unified diffs from them to the modules here.
- `scripts/verify-comparator.sh` runs the pinned Comparator, lean4export, NanoDa and Landrun locally (Linux); `scripts/validate-formalization.rb` checks the metadata file.
- `.github/workflows/ci.yml` — builds the project and runs Comparator (layout from the Palomar template; the template's doc-gen4 job is omitted because the modules import all of Mathlib).

## Edits relative to the benchmark output

The proof modules are the model's final `Spec.lean` files, verified by the benchmark, with only the following mechanical changes; the
exact diffs are in `provenance/`. The toolchain was moved from Lean v4.27.0 / Mathlib (via Formal Conjectures at commit
`488aade2`) to Lean v4.28.0 / Mathlib v4.28.0, the oldest release Palomar accepts; the only change this required is the
`loopless` adjustment listed below for the files it affects.

- `Erdos548_192usd_21h.lean` (SHA-256 of the benchmark output: `f34f78eff21941750ffd45f93c0201a80cdd71ebe4bb808b79031028d93ff7fd`):
  - line 1: `import FormalConjecturesUtil` → `import Mathlib`
  - no other changes (react-agent file: statement contained only the proved direction)
  - port to Mathlib v4.28.0: Mathlib v4.28.0 changed the field `SimpleGraph.loopless` from `Irreflexive Adj` to the class `Std.Irrefl Adj`, so proofs of that field need a `constructor` step (or an anonymous-constructor wrapper) and uses of `G.loopless` as a function become `G.loopless.irrefl`. Changed lines:
    - line 601: `loopless := by rintro (a | a) <;> simp` → `loopless := by constructor; rintro (a | a) <;> simp`

## Verification

```sh
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh   # Linux: Comparator + NanoDa under Landrun
```

CI runs the same checks. The compared theorem depends on no `sorry` and on no axioms beyond `propext`, `Quot.sound` and
`Classical.choice`. This repository is prepared for submission to Palomar through the
[submission form](https://submit.palomar-registry.org/) with the full commit SHA; registration is a separate step by the maintainer.

## Licence and attribution

This repository snapshot is licensed under the Apache License 2.0 (see `LICENSE`). The benchmark statement it reproduces is
from the FrontierMath Erdős benchmark (Adamczewski and Bloom; LeanOpenProblems, MIT licence; see `NOTICE`). Cited papers,
erdosproblems.com and Mathlib retain their own licences.
