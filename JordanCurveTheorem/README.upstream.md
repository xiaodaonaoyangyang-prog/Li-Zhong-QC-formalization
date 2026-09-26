# Jordan Curve Theorem in Lean 4

A *reformalization* of the **Jordan Curve Theorem** in Lean 4 / Mathlib, based on the HOL Light proof by Thomas C. Hales.

## Theorem Statement

A simple closed curve $C \subset \mathbb{R}^2$ (a subset homeomorphic to $S^1$) separates the plane into exactly two open connected components:

```lean
theorem jordan_curve_theorem {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : IsSimpleClosedCurve C) :
    ∃ A B : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen A ∧ IsOpen B ∧
      IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
      A ∪ B ∪ C = Set.univ
```

## Building

Requires [elan](https://github.com/leanprover/elan). Then:

```bash
lake exe cache get   # fetch prebuilt Mathlib cache
lake build
```

Built with Lean 4.29.0 and Mathlib v4.29.0.
