# Provenance

Vendored copy of the Lean 4 / Mathlib formalization of the Jordan Curve Theorem
(reformalization of T. C. Hales's HOL Light proof) from

  https://github.com/epfl-lara/jordan-curve-theorem  (folder `HOLLight-Lean/`)
  upstream commit: e442525a662e9e3beb8205b9fa1fc99509076ded
  licence: Apache License 2.0 (see `LICENSE` in this folder)

Copied on 2026-09-13 into this project as the separate Lean library `JordanCurveTheorem`
(module names unchanged). Upstream built it with Lean v4.29.0 and Mathlib v4.29.0; here it is
compiled against this project's toolchain (Lean v4.31.0-rc1, local Mathlib), so any local edits
needed for that are Mathlib-drift fixes only and are listed below.

## Local changes

All are proof-script fixes for Mathlib drift; no statement or definition was changed.

* `SectionL_ArcTopology.lean` (line 417): `simpa using hdist` → `simpa [Subtype.dist_eq] using hdist`
  (newer Mathlib's `simp` no longer rewrites `dist` on a subtype to `dist` of the values).
* `SectionP_Automation.lean` (lines 343 and 364, in `rScale_continuous` / `uScale_continuous`):
  `simpa using (continuous_rscale_coord r).comp …` → `simpa [Function.comp_def] using …`, and the same
  for `continuous_uscale_coord` (newer `simp` no longer unfolds `∘` there).
* **Rename `Graph` → `HolGraph`** (137 occurrences in code, 11 files; comments untouched).  Upstream
  declares a root-level `structure Graph (V E : Type*)` and imports only parts of Mathlib; this
  project's `LiZhongQC/Basic.lean` imports all of Mathlib, whose `Mathlib.Combinatorics.Graph.Basic`
  already has `Graph`, so `import LiZhongQC` + `import JordanCurveTheorem` failed with
  "environment already contains 'Graph.vertexSet'".  A scan of all 2969 constants defined by this
  library against the `LiZhongQC` environment found no other clash.  `HolGraph` is not a Mathlib or
  project name; `jordan_curve_theorem` does not mention graphs, so its statement is unchanged.

## Verification (2026-09-13)

`lake build JordanCurveTheorem JordanCurveTheorem.JordanCurveTheoremStatement` succeeds (2369 jobs,
no `sorry` warnings).  All 324 theorems in the `JordanCurveTheorem` modules depend only on
`propext`, `Classical.choice`, `Quot.sound`; in particular
`JordanCurveTheorem.jordan_curve_theorem` does.  `IsSimpleClosedCurve C` unfolds to
`∃ f, C = f '' Icc 0 1 ∧ Continuous f ∧ InjOn f (Ico 0 1) ∧ f 0 = f 1`.
`import LiZhongQC` and `import JordanCurveTheorem` load together.
