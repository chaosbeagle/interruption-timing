# Formal proofs

[繁體中文](../README.md) · [English](../README.en.md) · [日本語](../README.ja.md)

[Read the paper](../paper/manuscript.pdf).

The article defines safety by quantifying over every admissible late target set.
The Lean project derives the displayed threshold from that definition, proves
the obstruction bounds, and gives sharp constructions and counterexamples.

## Build

With Elan and Git installed, run from this directory:

```text
lake update
lake exe cache get
lake build
```

The toolchain and mathlib dependency are pinned in the project files.

## Correspondence with the article

| Article statement | Formal declaration |
|---|---|
| Definition 3.1: safety and feasibility | `ReserveThreshold.Safe`, `ReserveThreshold.Feasible` |
| Lemma 3.2: expenditure identity and monotonicity | `ReserveThreshold.late_budget_iff`, `cost_eq_min`, `cost_mono` |
| Theorem 3.3: exact minimum budget and canonical early action | `ReserveThreshold.feasible_iff_threshold`, `mandatory_safe_of_safe`; `ResourceArticle.threshold_is_minimum` |
| Corollary 3.4: monotonicity in the information class | `ReserveThreshold.threshold_mono_worlds` |
| Lemma 4.1: selecting target witnesses | `ResourceWitness.cover_by_small_subfamily` |
| Theorem 4.2: obstruction bound and sharpness | `ResourceObstruction.small_obstruction`, `feasible_iff_small_subfamilies`, `sharp_obstruction` |
| Theorem 4.4: reserve refinement | `ResourceObstruction.reserve_obstruction`, `feasible_iff_reserve_subfamilies` |
| Theorem 4.4: sharpness for d ≤ k | `ResourceExamples.reserve_pool_unchanged`, `reserve_example_threshold`, `reserve_bound_sharp` |
| Theorem 4.4: sharpness for d > k | `ResourceArticle.late_singleton_sharp` |
| Three-state values and Proposition 5.1 | `ResourceExamples.three_world_values`, `pairs_do_not_suffice`, `increasing_marginal_cost`, `locality_failure` |
| Proposition 5.2: multi-target action counterexample | `ResourceExamples.unbounded_area_obstruction` |

The article provides direct mathematical proofs of the sequential interpretation,
the private-target proposition, the set-intersection representation argument,
and the signal-coloring correspondence. The tactical card position is justified
through the stated card effects and timing rules.

The formal threshold is defined by the closed expression; `feasible_iff_threshold`
and `threshold_is_minimum` identify it with the article's minimum feasible budget.
The reserve bound uses subtraction on natural numbers, so `k - d + 1` means
`1 + max(k - d, 0)` with ordinary integer subtraction inside the maximum.
The residual reserve is measured after the mandatory urgent union.
