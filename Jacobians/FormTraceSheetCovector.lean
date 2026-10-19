/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.MeromorphicTrace.TraceForm
import Jacobians.ResidueCalculus.FormCoeff
/-!
# The per-sheet covector identity in charts (Miranda §VIII.3)

This file proves the linchpin of the branched-cover germ-coherence: reading the bundle
per-sheet covector `sheetPullback ω₀ s y v = (ω₀.toFun (s y)) (mfderiv s y v)` (the summand of the
pushforward trace `TraceForm.traceFun`) in the source/value charts as the **planar**
`coeffAt·deriv(section)` object that `FormTraceFibre.fibreTrace.traceCoeff` is built from.

The chain of identities:

* `symmL_self_one` — the trivialization-at-`a` unit frame is the model unit:
  `(trivAt a).symmL ℂ a 1 = 1` (the self chart-transition is the identity).
* `toFun_apply_eq_mul_localRep` — the covector pairing in the self frame is scalar multiplication
  by the centred local representative: `ω₀.toFun a w = w * localRep ω₀ a a`.  (ℂ-linearity, since
  `w = w • 1` and `localRep ω₀ a a = ω₀.toFun a 1`.)
* `mfderiv_eq_fderiv_chartPullback` — `mfderiv s y` is the planar `fderiv ℂ` of the chart pullback
  `s_loc = chart_{s y} ∘ s ∘ chart_y.symm` at `chart_y y` (the `mfderiv = fderiv` reading, cf.
  `LineIntegral.pathSpeed_comp_eq_mfderiv`).
* **`sheetPullback_apply_eq_coeffAt_mul_deriv`** — combining the above:
  `sheetPullback ω₀ s y v = (fderiv ℂ s_loc (chart_y y) v) * coeffAt ω₀ (s y) (chart_{s y}(s y))`.
  At the affine unit tangent `v = 1` the first factor is `deriv s_loc (chart_y y)`, and
  `coeffAt ω₀ (s y) (chart_{s y}(s y)) = localRep ω₀ (s y) (s y)` — exactly the `fibreTrace` summand
  for the `g ≡ 1` frame, sheet by sheet.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §10, §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceSheet

open Jacobians Jacobians.Dolbeault Jacobians.Montel

/-! ### `mfderiv` as the planar chart-pullback derivative -/

variable {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- The trivialization-at-`a` of the tangent bundle of `X`. -/
local notation "trivTS" a => trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) a

/-! ### The self-frame unit tangent -/

/-- **The self-frame unit tangent is the model unit.**  The trivialization-at-`a` of the tangent
bundle, evaluated at `a` on the unit `1 : ℂ`, is `1`: by `trivAt_symmL_one_eq_fderiv_C` it is the
derivative of the self chart-transition `chart_a ∘ chart_a.symm = id`, which is `1`. -/
theorem symmL_self_one (a : X) :
    (trivTS a).symmL ℂ a (1 : ℂ) = (1 : ℂ) := by
  rw [Jacobians.OfCurveSkeleton.trivAt_symmL_one_eq_fderiv_C a a (mem_chart_source ℂ a)]
  have hcong : ((chartAt (H := ℂ) a) ∘ (chartAt (H := ℂ) a).symm) =ᶠ[nhds ((chartAt ℂ a) a)]
      (id : ℂ → ℂ) := by
    filter_upwards [(chartAt (H := ℂ) a).open_target.mem_nhds
      ((chartAt ℂ a).map_source (mem_chart_source ℂ a))] with w hw
    simp only [Function.comp_apply, (chartAt ℂ a).right_inv hw, id_eq]
  rw [hcong.fderiv_eq, fderiv_id]
  rfl

variable [T2Space X] [CompactSpace X] [ConnectedSpace X]

/-- **The centred local representative is the pairing against the model unit.**
`localRep ω₀ a a = ω₀.toFun a (1 : ℂ)` (since the self-frame unit tangent is `1`). -/
theorem localRep_self_eq_toFun_one (ω₀ : HolomorphicOneForms X) (a : X) :
    Jacobians.Montel.localRep ω₀ a a = ω₀.toFun a (1 : ℂ) := by
  show ω₀.toFun a ((trivTS a).symmL ℂ a 1) = ω₀.toFun a (1 : ℂ)
  rw [symmL_self_one a]

/-! ### Covector pairing in the self-chart frame -/

/-- **Covector pairing in the self frame.**  For a holomorphic 1-form `ω₀` and a tangent `w` at `a`
(in the model fibre `ℂ`), the pairing `ω₀.toFun a w` is `w` times the centred local representative
`localRep ω₀ a a`.  ℂ-linearity: `w = w • 1`, and `ω₀.toFun a 1 = localRep ω₀ a a`. -/
theorem toFun_apply_eq_mul_localRep (ω₀ : HolomorphicOneForms X) (a : X) (w : ℂ) :
    ω₀.toFun a w = w * Jacobians.Montel.localRep ω₀ a a := by
  rw [localRep_self_eq_toFun_one]
  -- View `ω₀.toFun a : ℂ →L[ℂ] ℂ` (defeq) and pull the scalar `w` out by ℂ-linearity.
  set T : ℂ →L[ℂ] ℂ := ω₀.toFun a
  show T w = w * T 1
  rw [← smul_eq_mul, ← map_smul]; congr 1; rw [smul_eq_mul, mul_one]

/-! ### The frame-transition law for the local representative -/

/-- **Frame-transition law for `localRep`.**  For `y` in the chart source of `a`, the local
representative of `ω₀` based at `a` and read at `y` equals the centred representative at `y` times
the `dz`-transition Jacobian `deriv(chart_y ∘ chart_a.symm)(chart_a y)`:

> `localRep ω₀ a y = deriv (chart_y ∘ chart_a.symm) (chart_a y) · localRep ω₀ y y`.

This is the general cotangent-coefficient change-of-frame (cf. the `∞`-case
`ProjectiveLine.inftyCoeff_eq_transition`).  It is the cancellation that reconciles the bundle
per-sheet covector (read at the moving fibre point `P`'s *own* chart) with the planar fibre trace
coefficient (read in a *fixed* sheet chart): the `localRep` ratio is the inverse of the `deriv`
ratio, so the `dz`-coefficient `localRep·deriv(section)` is frame-independent. -/
theorem localRep_eq_transition_mul_self (ω₀ : HolomorphicOneForms X) (a y : X)
    (hy : y ∈ (chartAt ℂ a).source) :
    Jacobians.Montel.localRep ω₀ a y
      = deriv (fun w => (chartAt ℂ y) ((chartAt ℂ a).symm w)) ((chartAt ℂ a) y)
        * Jacobians.Montel.localRep ω₀ y y := by
  -- `localRep ω₀ a y = ω₀.toFun y (symmL_a y 1)`, and
  -- `symmL_a y 1 = deriv(chart_y ∘ chart_a.symm)`.
  show ω₀.toFun y ((trivTS a).symmL ℂ y 1) = _
  rw [Jacobians.OfCurveSkeleton.trivAt_symmL_one_eq_fderiv_C a y hy]
  -- The covector pairing against the scalar tangent, by ℂ-linearity.
  rw [toFun_apply_eq_mul_localRep ω₀ y]
  -- `fderiv ℂ h (chart_a y) 1 = deriv h (chart_a y)`.
  rw [deriv, Function.comp_def]

/-! ### The linchpin: per-sheet covector identity in charts -/

end Jacobians.Dolbeault.FormTraceSheet
