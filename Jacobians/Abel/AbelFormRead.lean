/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Chart reads for the Abel pairing: chart reads of `(0,1)`-forms and conjugate forms

The scalar dictionary between intrinsic `(0,1)`-data and planar functions, feeding the
`∬ σ∧ω` pairing atom (Forster 19.10):

* `read01 g y` — the chart-`y` read of a smooth `(0,1)`-form `g`: the value of `g` on the
  `y`-frame tangent vector `symmL (trivAt y) x 1`.  Smooth on the chart source
  (`contMDiffAt_read01`, via `contMDiffAt_chartRead_datum`), with the explicit
  conjugate-frame formula `read01_eq_conj_mul` and the `(0,1)`-transformation law
  `read01_transform` (`read_y = conj(T′)·read_{y′}`, `T` the chart transition).
* `read01_proj01_mfderiv` — **the `∂̄`-bridge**: the read of `proj01 (mfderiv w x)` in ANY
  chart containing `x` is the planar Wirtinger `DbarDisk.dbar` of the chart pullback of `w`
  (chart bridge `dbar_apply_one_eq_dbarDisk'` + Wirtinger chain rule `dbarDisk_comp_holo`);
  specialised to `read01_dbarL`.
* `localRep_transform` — the matching `(1,0)`-law `h_y = h_{y′}·T′` for the holomorphic
  coefficient `Montel.localRep` (from `localRep_eq_transition_mul_self` + the transition
  derivative cocycle `deriv_transition_cocycle`).
* `conjForm η` — the **conjugate form** `ω̄` of a holomorphic 1-form, as a smooth
  `(0,1)`-form (`conjForm_mem_zeroOne`), with read `conj (localRep η y ·)`
  (`read01_conjForm`).

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §19 (pp. 153–157).
-/
import Jacobians.DolbeaultComparison.DolbeaultComparisonProof
import Jacobians.DolbeaultComparison.DolbeaultComparisonInverse
import Jacobians.FormTraceSheetCovector
import Jacobians.ResidueTheorem.ResidueLedgerTransport

noncomputable section

-- ℝ/ℂ-module diamond discipline (as in `RealForms`/`DolbeaultComparisonProof`).
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Set Filter Complex

namespace Jacobians.Dolbeault.AbelPairing

open Jacobians.Dolbeault Jacobians

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ### Chart bookkeeping: `extChartAt 𝓘(ℝ,ℂ)` is `chartAt` -/

/-- The boundaryless identity-model `extChartAt` is the bare chart, as a function. -/
theorem extChartAt_real_eq_chartAt (y : X) :
    ((extChartAt 𝓘(ℝ, ℂ) y) : X → ℂ) = (chartAt (H := ℂ) y) := by
  funext w; simp [extChartAt]

/-- Source transfer between the two chart spellings. -/
theorem mem_extChartAt_real_source_iff (y x : X) :
    x ∈ (extChartAt 𝓘(ℝ, ℂ) y).source ↔ x ∈ (chartAt (H := ℂ) y).source := by
  rw [extChartAt_source]

/-! ### The transition-derivative cocycle -/

/-- The transition derivative in `extChartAt 𝓘(ℝ,ℂ)` spelling equals the `chartAt`
(λ-form) spelling. -/
theorem deriv_transition_ext_eq_chart (y x : X) :
    deriv ((extChartAt 𝓘(ℝ, ℂ) x) ∘ (extChartAt 𝓘(ℝ, ℂ) y).symm) ((extChartAt 𝓘(ℝ, ℂ) y) x)
      = deriv (fun w => (chartAt (H := ℂ) x) ((chartAt (H := ℂ) y).symm w))
          ((chartAt (H := ℂ) y) x) := by
  have h1 : ((extChartAt 𝓘(ℝ, ℂ) x) ∘ (extChartAt 𝓘(ℝ, ℂ) y).symm)
      = fun w => (chartAt (H := ℂ) x) ((chartAt (H := ℂ) y).symm w) := by
    funext w; simp [extChartAt]
  have h2 : (extChartAt 𝓘(ℝ, ℂ) y) x = (chartAt (H := ℂ) y) x := by simp [extChartAt]
  rw [h1, h2]

/-- The self-chart transition has derivative `1` at the centre image. -/
theorem deriv_transition_self (x : X) {z : ℂ} (hz : z ∈ (chartAt (H := ℂ) x).target) :
    deriv (fun w => (chartAt (H := ℂ) x) ((chartAt (H := ℂ) x).symm w)) z = 1 := by
  have hev : (fun w => (chartAt (H := ℂ) x) ((chartAt (H := ℂ) x).symm w)) =ᶠ[𝓝 z] id := by
    filter_upwards [(chartAt (H := ℂ) x).open_target.mem_nhds hz] with w hw
    exact (chartAt (H := ℂ) x).right_inv hw
  rw [hev.deriv_eq, deriv_id]

/-- `MDifferentiableAt` over the real model gives plain real differentiability of the
own-chart pullback at the chart coordinate. -/
theorem differentiableAt_pullback_of_mdifferentiableAt {w : X → ℂ} {x : X}
    (hw : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) w x) :
    DifferentiableAt ℝ (fun z => w ((extChartAt 𝓘(ℝ, ℂ) x).symm z))
      (extChartAt 𝓘(ℝ, ℂ) x x) := by
  have h := hw.differentiableWithinAt_writtenInExtChartAt
  rw [ModelWithCorners.Boundaryless.range_eq_univ, differentiableWithinAt_univ] at h
  have hpull : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) x w =
      fun z => w ((extChartAt 𝓘(ℝ, ℂ) x).symm z) := by
    ext z; simp only [writtenInExtChartAt, Function.comp_apply]; rfl
  rwa [hpull] at h

/-- **The frame vector in chart spelling**: `symmL (trivAt y) x 1` is the transition
derivative `(chart_x ∘ chart_y⁻¹)′(chart_y x)`. -/
theorem frameVector_eq_deriv_chart [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] {y x : X} (hx : x ∈ (chartAt (H := ℂ) y).source) :
    ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) y) x) (1 : ℂ) : ℂ)
      = deriv (fun w => (chartAt (H := ℂ) x) ((chartAt (H := ℂ) y).symm w))
          ((chartAt (H := ℂ) y) x) := by
  rw [frameVector_eq_deriv_transition_symm y x ((mem_extChartAt_real_source_iff y x).mpr hx)]
  exact deriv_transition_ext_eq_chart y x

/-- On the germ window at `chart_y x`, the `x`-transition through `y` factors through the
`y → y'` transition. -/
theorem transition_eventuallyEq_comp [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] {x y y' : X}
    (hxy : x ∈ (chartAt (H := ℂ) y).source) (hxy' : x ∈ (chartAt (H := ℂ) y').source) :
    (fun w => (chartAt (H := ℂ) x) ((chartAt (H := ℂ) y).symm w))
        =ᶠ[𝓝 ((chartAt (H := ℂ) y) x)]
      (fun w => (chartAt (H := ℂ) x) ((chartAt (H := ℂ) y').symm w))
        ∘ (fun w => (chartAt (H := ℂ) y') ((chartAt (H := ℂ) y).symm w)) :=
  Jacobians.Dolbeault.StokesResidue.read_eventuallyEq_read_comp_transition
    (chartAt (H := ℂ) x) hxy hxy'

/-- **The transition-derivative cocycle**: for `x` in both chart sources,
`(chart_x ∘ chart_y⁻¹)′(chart_y x) = (chart_x ∘ chart_{y'}⁻¹)′(chart_{y'} x) ·
(chart_{y'} ∘ chart_y⁻¹)′(chart_y x)`. -/
theorem deriv_transition_cocycle [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] {x y y' : X}
    (hxy : x ∈ (chartAt (H := ℂ) y).source) (hxy' : x ∈ (chartAt (H := ℂ) y').source) :
    deriv (fun w => (chartAt (H := ℂ) x) ((chartAt (H := ℂ) y).symm w))
        ((chartAt (H := ℂ) y) x)
      = deriv (fun w => (chartAt (H := ℂ) x) ((chartAt (H := ℂ) y').symm w))
          ((chartAt (H := ℂ) y') x)
        * deriv (fun w => (chartAt (H := ℂ) y') ((chartAt (H := ℂ) y).symm w))
            ((chartAt (H := ℂ) y) x) := by
  set T : ℂ → ℂ := fun w => (chartAt (H := ℂ) y') ((chartAt (H := ℂ) y).symm w) with hT
  have hTx : T ((chartAt (H := ℂ) y) x) = (chartAt (H := ℂ) y') x := by
    simp only [hT, (chartAt (H := ℂ) y).left_inv hxy]
  have hTdiff : DifferentiableAt ℂ T ((chartAt (H := ℂ) y) x) :=
    (transition_analyticAt_of_mem hxy hxy').differentiableAt
  have houter : DifferentiableAt ℂ
      (fun w => (chartAt (H := ℂ) x) ((chartAt (H := ℂ) y').symm w))
      (T ((chartAt (H := ℂ) y) x)) := by
    rw [hTx]
    exact (transition_analyticAt_of_mem hxy' (mem_chart_source ℂ x)).differentiableAt
  rw [(transition_eventuallyEq_comp hxy hxy').deriv_eq,
    deriv_comp _ houter hTdiff, hTx]

/-! ### The chart read of a `(0,1)`-form -/

/-- **The chart-`y` read of a smooth `(0,1)`-form**: the value of `g` at `x` on the
constant `y`-frame tangent vector (the `symmL` of the fixed `y`-trivialization at `1`). -/
def read01 [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (g : SmoothCOneForms X) (y : X) : X → ℂ :=
  fun x => (g x) ((Bundle.Trivialization.symmL ℝ
    (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) y) x) (1 : ℂ))

/-- The read is smooth at every point of the chart source (`contMDiffAt_chartRead_datum`). -/
theorem contMDiffAt_read01 [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (g : SmoothCOneForms X) {y x : X}
    (hx : x ∈ (chartAt (H := ℂ) y).source) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (read01 g y) x :=
  contMDiffAt_chartRead_datum g y x ((mem_extChartAt_real_source_iff y x).mpr hx)

/-- **The conjugate-frame formula**: for `g ∈ A^{0,1}` and `x` in the chart source of `y`,
`read01 g y x = conj((chart_x ∘ chart_y⁻¹)′(chart_y x)) · (g x) 1`. -/
theorem read01_eq_conj_mul [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    {g : SmoothCOneForms X} (hg : g ∈ OneFormsZeroOne X) {y x : X}
    (hx : x ∈ (chartAt (H := ℂ) y).source) :
    read01 g y x = (starRingEnd ℂ)
      (deriv (fun w => (chartAt (H := ℂ) x) ((chartAt (H := ℂ) y).symm w))
        ((chartAt (H := ℂ) y) x))
        * (g x) (1 : ℂ) := by
  rw [read01, frameVector_eq_deriv_chart hx, oneForm_apply_conjLinear hg]

/-- **The `(0,1)`-transformation law**: `read_y = conj(T′)·read_{y'}` along the chart
transition `T = chart_{y'} ∘ chart_y⁻¹`. -/
theorem read01_transform [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    {g : SmoothCOneForms X} (hg : g ∈ OneFormsZeroOne X) {x y y' : X}
    (hxy : x ∈ (chartAt (H := ℂ) y).source) (hxy' : x ∈ (chartAt (H := ℂ) y').source) :
    read01 g y x = (starRingEnd ℂ)
      (deriv (fun w => (chartAt (H := ℂ) y') ((chartAt (H := ℂ) y).symm w))
        ((chartAt (H := ℂ) y) x))
        * read01 g y' x := by
  rw [read01_eq_conj_mul hg hxy, read01_eq_conj_mul hg hxy',
    deriv_transition_cocycle hxy hxy', map_mul]
  ring

/-- **The `(1,0)`-transformation law** for the holomorphic coefficient:
`localRep_y = T′ · localRep_{y'}` along the chart transition `T = chart_{y'} ∘ chart_y⁻¹`. -/
theorem localRep_transform [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (η : HolomorphicOneForms X) {x y y' : X}
    (hxy : x ∈ (chartAt (H := ℂ) y).source) (hxy' : x ∈ (chartAt (H := ℂ) y').source) :
    Jacobians.Montel.localRep η y x
      = deriv (fun w => (chartAt (H := ℂ) y') ((chartAt (H := ℂ) y).symm w))
          ((chartAt (H := ℂ) y) x)
        * Jacobians.Montel.localRep η y' x := by
  rw [Jacobians.Dolbeault.FormTraceSheet.localRep_eq_transition_mul_self η y x hxy,
    Jacobians.Dolbeault.FormTraceSheet.localRep_eq_transition_mul_self η y' x hxy',
    deriv_transition_cocycle hxy hxy']
  ring

/-! ### The `∂̄`-bridge: reads of `proj01 (mfderiv w x)` are planar Wirtinger derivatives -/

/-- **The `∂̄`-bridge in any chart.** For `w` real-differentiable at `x ∈ source_y`, the
`y`-frame read of the `(0,1)`-part of `mfderiv w x` is the planar Wirtinger derivative of
the chart-`y` pullback of `w`:

  `proj01 (mfderiv w x) (frame_y) = ∂̄(w ∘ chart_y⁻¹)(chart_y x)`. -/
theorem read01_proj01_mfderiv [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    {w : X → ℂ} {x y : X}
    (hx : x ∈ (chartAt (H := ℂ) y).source)
    (hw : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) w x) :
    proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) w x) ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) y) x) (1 : ℂ))
      = DbarDisk.dbar (w ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) x) := by
  set τ : ℂ → ℂ := fun z => (chartAt (H := ℂ) x) ((chartAt (H := ℂ) y).symm z) with hτ
  have hpb : (extChartAt 𝓘(ℝ, ℂ) x) x = (chartAt (H := ℂ) x) x := by simp [extChartAt]
  -- LHS: the frame vector + conjugate-linearity + the own-chart bridge.
  have hlhs : proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) w x) ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) y) x) (1 : ℂ))
      = (starRingEnd ℂ) (deriv τ ((chartAt (H := ℂ) y) x))
        * DbarDisk.dbar (fun z => w ((extChartAt 𝓘(ℝ, ℂ) x).symm z))
            (extChartAt 𝓘(ℝ, ℂ) x x) := by
    rw [frameVector_eq_deriv_chart hx, proj01_eq_conj_smul, dbar_apply_one_eq_dbarDisk' hw]
  rw [hlhs]
  -- RHS: the Wirtinger chain rule along the holomorphic transition `τ`.
  have hτpt : τ ((chartAt (H := ℂ) y) x) = (chartAt (H := ℂ) x) x := by
    simp only [hτ, (chartAt (H := ℂ) y).left_inv hx]
  have hτdiff : DifferentiableAt ℂ τ ((chartAt (H := ℂ) y) x) :=
    (transition_analyticAt_of_mem hx (mem_chart_source ℂ x)).differentiableAt
  have hgerm : (w ∘ (chartAt (H := ℂ) y).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) y) x)]
      (fun z => w ((extChartAt 𝓘(ℝ, ℂ) x).symm z)) ∘ τ := by
    filter_upwards [Jacobians.Dolbeault.StokesResidue.eventually_chart_window
      (y := y) (y' := x) hx (mem_chart_source ℂ x)] with z hz
    show w ((chartAt (H := ℂ) y).symm z) = w ((extChartAt 𝓘(ℝ, ℂ) x).symm (τ z))
    rw [show (extChartAt 𝓘(ℝ, ℂ) x).symm (τ z) = (chartAt (H := ℂ) x).symm (τ z) by
      simp [extChartAt]]
    rw [show (chartAt (H := ℂ) x).symm (τ z) = (chartAt (H := ℂ) y).symm z from
      (chartAt (H := ℂ) x).left_inv hz.2]
  have hwdiff : DifferentiableAt ℝ (fun z => w ((extChartAt 𝓘(ℝ, ℂ) x).symm z))
      (τ ((chartAt (H := ℂ) y) x)) := by
    rw [hτpt, ← hpb]
    exact differentiableAt_pullback_of_mdifferentiableAt hw
  rw [dbarDisk_congr hgerm, dbarDisk_comp_holo _ τ _ hwdiff hτdiff, hτpt, hpb]

/-- The read of `∂̄u` in the chart at `y`: `read01 (∂̄u) y = ∂̄(u ∘ chart_y⁻¹) ∘ chart_y` on
the chart source. -/
theorem read01_dbarL [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (u : SmoothCFunctions X) {y x : X}
    (hx : x ∈ (chartAt (H := ℂ) y).source) :
    read01 (dbarL u) y x
      = DbarDisk.dbar (⇑u ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) x) := by
  have hu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x :=
    (u.contMDiff x).mdifferentiableAt (by simp)
  exact read01_proj01_mfderiv hx hu

/-! ### Read algebra -/

theorem read01_add [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (g₁ g₂ : SmoothCOneForms X) (y x : X) :
    read01 (g₁ + g₂) y x = read01 g₁ y x + read01 g₂ y x := by
  unfold read01
  rw [show ((g₁ + g₂) x) = (g₁ x) + (g₂ x) by
    rw [show (⇑(g₁ + g₂)) x = (g₁ + g₂) x from rfl, ContMDiffSection.coe_add]; rfl]
  rfl

theorem read01_smul [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] (r : ℝ)
    (g : SmoothCOneForms X) (y x : X) :
    read01 (r • g) y x = r • read01 g y x := by
  unfold read01
  rw [show ((r • g) x) = r • (g x) by
    rw [show (⇑(r • g)) x = (r • g) x from rfl, ContMDiffSection.coe_smul]; rfl]
  rfl

theorem read01_zero [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] (y x : X)
    : read01 (0 : SmoothCOneForms X) y x = 0 := by
  unfold read01
  rw [show ((0 : SmoothCOneForms X) x) = 0 by
    rw [show (⇑(0 : SmoothCOneForms X)) x = (0 : SmoothCOneForms X) x from rfl,
      ContMDiffSection.coe_zero]; rfl]
  rfl

theorem read01_zsmul [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] (n : ℤ)
    (g : SmoothCOneForms X) (y x : X) :
    read01 (n • g) y x = n • read01 g y x := by
  unfold read01
  rw [show ((n • g) x) = n • (g x) by
    rw [show (⇑(n • g)) x = (n • g) x from rfl, ContMDiffSection.coe_zsmul]; rfl]
  rfl

theorem read01_cSmulForm [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (c : SmoothCFunctions X) (g : SmoothCOneForms X) (y x : X) :
    read01 (cSmulForm c g) y x = c x * read01 g y x := by
  unfold read01
  rw [cSmulForm_apply]
  rfl

/-- Reads vanish wherever the fiber value vanishes. -/
theorem read01_eq_zero_of_apply_eq_zero [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] {g : SmoothCOneForms X} {x : X}
    (h : (g x) = (0 : ℂ →L[ℝ] ℂ)) (y : X) : read01 g y x = 0 := by
  unfold read01
  rw [h]
  simp

/-! ### Conjugate forms `ω̄` -/

/-- A conjugate-linear fiber form is fixed by `proj01` (it IS `(0,1)`). -/
theorem proj01_eq_self_of_conjLinear {α : ℂ →L[ℝ] ℂ}
    (h : ∀ v, α (Complex.I * v) = -(Complex.I * α v)) : proj01 α = α := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [proj01_apply_val, h v]
  linear_combination (-(2 : ℂ)⁻¹ * α v) * Complex.I_sq

/-- The fiberwise conjugate of a holomorphic form: `v ↦ conj (η x v)`, an `ℝ`-CLM. -/
def conjFiber [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (η : HolomorphicOneForms X) (x : X) : ℂ →L[ℝ] ℂ :=
  (Complex.conjCLE.toContinuousLinearMap).comp
    ((η.toFun x : ℂ →L[ℂ] ℂ).restrictScalars ℝ)

theorem conjFiber_apply [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (η : HolomorphicOneForms X) (x : X) (v : ℂ) :
    conjFiber η x v = (starRingEnd ℂ) (η.toFun x v) := rfl

/-- The conjugate fiber is conjugate-linear. -/
theorem conjFiber_conjLinear [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (η : HolomorphicOneForms X) (x : X) (v : ℂ) :
    conjFiber η x (Complex.I * v) = -(Complex.I * conjFiber η x v) := by
  rw [conjFiber_apply, conjFiber_apply]
  have : (η.toFun x : ℂ →L[ℂ] ℂ) (Complex.I * v)
      = Complex.I * (η.toFun x : ℂ →L[ℂ] ℂ) v := by
    rw [show Complex.I * v = Complex.I • v from rfl, map_smul]; rfl
  rw [this, map_mul, Complex.conj_I]
  ring

/-- The conjugate fiber against the `y`-frame vector is `conj (localRep η y x)`. -/
theorem conjFiber_frame [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (η : HolomorphicOneForms X) {y x : X}
    (hx : x ∈ (chartAt (H := ℂ) y).source) :
    conjFiber η x ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) y) x) (1 : ℂ))
      = (starRingEnd ℂ) (Jacobians.Montel.localRep η y x) := by
  rw [frameVector_eq_deriv_chart hx, conjFiber_apply]
  congr 1
  -- `η x (d) = d · localRep η x x` and `localRep η y x = d · localRep η x x`.
  rw [Jacobians.Dolbeault.FormTraceSheet.toFun_apply_eq_mul_localRep,
    Jacobians.Dolbeault.FormTraceSheet.localRep_eq_transition_mul_self η y x hx]

/-- Smoothness of the conjugate-fiber section (hom-bundle reduction: near `y` the
in-coordinates read is `(mul (conj (localRep η y ·))).comp conj`, with `conj (localRep η y ·)`
real-smooth since `localRep η y` is chart-analytic). -/
theorem contMDiff_conjFiber [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (η : HolomorphicOneForms X) :
    ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ)) (⊤ : ℕ∞)
      (fun x => (⟨x, conjFiber η x⟩ : Bundle.TotalSpace (ℂ →L[ℝ] ℂ)
        (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x))) := by
  intro y
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  simp only [ContinuousLinearMap.inCoordinates,
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    Bundle.Trivial.fiberBundle_trivializationAt', ContinuousLinearMap.id_comp]
  -- the smooth model: `(mul (conj (localRep η y x))).comp conjCLM`.
  have hrep : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (fun x => Jacobians.Montel.localRep η y x) y := by
    refine contMDiffAt_real_of_chart_analyticAt ?_
    have htgt : (chartAt (H := ℂ) y) y ∈ (chartAt (H := ℂ) y).target :=
      (chartAt (H := ℂ) y).map_source (mem_chart_source ℂ y)
    exact (Jacobians.Montel.localRep_analyticOn_chartTarget η y).analyticAt
      ((chartAt (H := ℂ) y).open_target.mem_nhds htgt)
  have hconjrep : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (fun x => (starRingEnd ℂ) (Jacobians.Montel.localRep η y x)) y := by
    have hc : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun z : ℂ => (starRingEnd ℂ) z) := by
      rw [contMDiff_iff_contDiff]
      exact Complex.conjCLE.toContinuousLinearMap.contDiff
    exact (hc.contMDiffAt).comp y hrep
  have hmodel : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ) (⊤ : ℕ∞)
      (fun x => (ContinuousLinearMap.mul ℝ ℂ
          ((starRingEnd ℂ) (Jacobians.Montel.localRep η y x))).comp
        Complex.conjCLE.toContinuousLinearMap) y := by
    have hM : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ) (⊤ : ℕ∞)
        (fun x => ContinuousLinearMap.mul ℝ ℂ
          ((starRingEnd ℂ) (Jacobians.Montel.localRep η y x))) y :=
      ContMDiffAt.clm_apply contMDiffAt_const hconjrep
    exact hM.clm_comp contMDiffAt_const
  refine hmodel.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt (H := ℂ) y).open_source.mem_nhds (mem_chart_source ℂ y)] with x hx
  -- pointwise: both are conjugate-linear with the same value on the frame vector.
  refine ContinuousLinearMap.ext fun v => ?_
  have hα : conjFiber η x ((Bundle.Trivialization.symmL ℝ
      (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) y) x) v)
      = (starRingEnd ℂ) v * conjFiber η x ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) y) x) (1 : ℂ)) := by
    -- `symmL` is multiplication by the (holomorphic) transition derivative.
    have h1 : Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) y) x
        = tangentCoordChange 𝓘(ℝ, ℂ) y x x :=
      TangentBundle.symmL_trivializationAt_eq_core hx
    have hσdiff : DifferentiableAt ℂ
        ((extChartAt 𝓘(ℝ, ℂ) x) ∘ (extChartAt 𝓘(ℝ, ℂ) y).symm)
        ((extChartAt 𝓘(ℝ, ℂ) y) x) :=
      differentiableAt_chartTransition_symm y x
        ((mem_extChartAt_real_source_iff y x).mpr hx)
    have hfd : fderiv ℝ ((extChartAt 𝓘(ℝ, ℂ) x) ∘ (extChartAt 𝓘(ℝ, ℂ) y).symm)
        ((extChartAt 𝓘(ℝ, ℂ) y) x)
        = (deriv ((extChartAt 𝓘(ℝ, ℂ) x) ∘ (extChartAt 𝓘(ℝ, ℂ) y).symm)
            ((extChartAt 𝓘(ℝ, ℂ) y) x)) • (1 : ℂ →L[ℝ] ℂ) :=
      hσdiff.hasDerivAt.complexToReal_fderiv.fderiv
    have h2 : tangentCoordChange 𝓘(ℝ, ℂ) y x x
        = fderiv ℝ ((extChartAt 𝓘(ℝ, ℂ) x) ∘ (extChartAt 𝓘(ℝ, ℂ) y).symm)
            ((extChartAt 𝓘(ℝ, ℂ) y) x) := by
      rw [tangentCoordChange_def, ModelWithCorners.Boundaryless.range_eq_univ,
        fderivWithin_univ]
    rw [h1, h2, hfd]
    -- the smul-CLM applications are plain complex multiplications.
    show conjFiber η x ((deriv ((extChartAt 𝓘(ℝ, ℂ) x) ∘ (extChartAt 𝓘(ℝ, ℂ) y).symm)
          ((extChartAt 𝓘(ℝ, ℂ) y) x)) * v)
      = (starRingEnd ℂ) v * conjFiber η x
          ((deriv ((extChartAt 𝓘(ℝ, ℂ) x) ∘ (extChartAt 𝓘(ℝ, ℂ) y).symm)
            ((extChartAt 𝓘(ℝ, ℂ) y) x)) * 1)
    rw [conjFiber_apply, conjFiber_apply,
      Jacobians.Dolbeault.FormTraceSheet.toFun_apply_eq_mul_localRep η x,
      Jacobians.Dolbeault.FormTraceSheet.toFun_apply_eq_mul_localRep η x]
    simp only [map_mul, mul_one]
    ring
  show conjFiber η x ((Bundle.Trivialization.symmL ℝ
      (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) y) x) v)
    = (ContinuousLinearMap.mul ℝ ℂ ((starRingEnd ℂ) (Jacobians.Montel.localRep η y x)))
        (Complex.conjCLE.toContinuousLinearMap v)
  rw [hα, conjFiber_frame η hx]
  show (starRingEnd ℂ) v * (starRingEnd ℂ) (Jacobians.Montel.localRep η y x)
    = (starRingEnd ℂ) (Jacobians.Montel.localRep η y x) * (starRingEnd ℂ) v
  ring

/-- **The conjugate form `ω̄`** of a holomorphic 1-form, as a smooth `ℂ`-valued 1-form. -/
def conjForm [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (η : HolomorphicOneForms X) : SmoothCOneForms X where
  toFun := fun x => conjFiber η x
  contMDiff_toFun := contMDiff_conjFiber η

theorem conjForm_apply [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (η : HolomorphicOneForms X) (x : X) :
    (conjForm η) x = conjFiber η x := rfl

/-- `ω̄` is a `(0,1)`-form. -/
theorem conjForm_mem_zeroOne [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (η : HolomorphicOneForms X) :
    conjForm η ∈ OneFormsZeroOne X := by
  refine ⟨conjForm η, ?_⟩
  refine ContMDiffSection.ext fun x => ?_
  show proj01 ((conjForm η) x) = (conjForm η) x
  rw [conjForm_apply]
  exact proj01_eq_self_of_conjLinear (conjFiber_conjLinear η x)

/-- The chart-`y` read of `ω̄` is the conjugate of the holomorphic coefficient:
`read01 (conjForm η) y = conj ∘ localRep η y` on the chart source. -/
theorem read01_conjForm [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (η : HolomorphicOneForms X) {y x : X}
    (hx : x ∈ (chartAt (H := ℂ) y).source) :
    read01 (conjForm η) y x = (starRingEnd ℂ) (Jacobians.Montel.localRep η y x) := by
  unfold read01
  rw [show ((conjForm η) x) = conjFiber η x from rfl]
  exact conjFiber_frame η hx

end Jacobians.Dolbeault.AbelPairing
