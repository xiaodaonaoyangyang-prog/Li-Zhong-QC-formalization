/-
  The residue-ledger chart transport engine.

  The genus-uniform pair-form residue theorem (`ResidueTheoremStokes.lean`) is a ledger of
  planar integrals of ONE canonical integrand shape, read in varying charts of the compact
  Riemann surface `X`:

    `ledgerIntegrand g₀ h P v y V (z) = 𝟙_{chart_y''V}(z) · P(chart_y⁻¹ z) · ∂̄(v∘chart_y⁻¹)(z)
        · pairRead g₀ h y (z)`

  — a scalar field `P : X → ℂ`, the planar `∂̄` of (the chart read of) a smooth cutoff
  `v : X → ℝ` (the `(0,1)`-factor), and the pair-form coefficient
  `pairRead g₀ h y = (h∘chart⁻¹)·(g₀∘chart⁻¹)′` (the `(1,0)`-factor).  This file provides the
  engine lemmas:

  * `pairRead_transform` — the `(1,0)`-coefficient rule `f_y = (f_{y'}∘T)·T′` under the chart
    transition `T = chart_{y'} ∘ chart_y⁻¹` (valid at points where the `h`/`g₀` reads are
    honestly analytic — `ReadsAnalyticAt`, whose failure set is FINITE);
  * `analyticAt_pairRead` — off the bad set the pair coefficient is holomorphic in EVERY chart;
  * `integral_ledgerIntegrand_transport` — **the chart-change invariance**
    `∫_ℂ ledgerIntegrand … y V = ∫_ℂ ledgerIntegrand … y' V`: holomorphic change of variables,
    with `conj T′` (from the `∂̄` chain rule) × `T′` (from `pairRead_transform`)
    combining EXACTLY into the real Jacobian `|T′|²`;
  * `ledgerIntegrand_congr_superset` — the indicator set may be enlarged/shrunk freely as long
    as `P` vanishes or `v` is locally constant on the difference;
  * `sum_ledgerIntegrand` — finite sums of cutoffs aggregate inside the `∂̄`;
  * `continuous_ledgerIntegrand` / `hasCompactSupport_ledgerIntegrand` /
    `integrable_ledgerIntegrand` — the integrability kit (continuity off a compact core is
    bought by `P`-vanishing or local constancy of `v`; the finitely many non-analytic points
    are killed the same way).

  Reference: Forster GTM 81 §10 (the proof of the Residue Theorem 10.21 — these are the
  chart-bookkeeping steps Forster performs implicitly when integrating `d(f_k ω)` "using the
  coordinate `z_k`").
-/
import Jacobians.Cech.MeromorphicAnalyticBadSet
import Jacobians.Finiteness.CechModelManifold
import Jacobians.PlanarStokes.AnnulusResidueIntegral
import Jacobians.PlanarStokes.PlanarHolomorphicChangeOfVariables
set_option backward.isDefEq.respectTransparency false

open Complex MeasureTheory Filter Set Topology
open scoped Manifold ContDiff

namespace Jacobians.Dolbeault.StokesResidue

open Jacobians.Dolbeault Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The pair-form coefficient and its chart calculus -/

/-- The pair-form coefficient `h·dg₀` read in the canonical chart at `y`:
`(h∘chart⁻¹)·(g₀∘chart⁻¹)′`.  (`pairFormResidue g₀ h a = resAt (pairRead g₀ h a) (chart a a)`.) -/
noncomputable def pairRead (g₀ h : MeromorphicFunction X) (y : X) : ℂ → ℂ :=
  fun z => h.toFun ((chartAt (H := ℂ) y).symm z)
    * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) y).symm w)) z

/-- Honest own-chart analyticity of BOTH reads at `x` (the good locus of the ledger; its
complement is finite by `MeromorphicFunction.finite_nonAnalyticAt`). -/
def ReadsAnalyticAt (g₀ h : MeromorphicFunction X) (x : X) : Prop :=
  AnalyticAt ℂ (fun z => h.toFun ((chartAt (H := ℂ) x).symm z)) ((chartAt (H := ℂ) x) x)
  ∧ AnalyticAt ℂ (fun z => g₀.toFun ((chartAt (H := ℂ) x).symm z)) ((chartAt (H := ℂ) x) x)

/-- The bad locus `{¬ReadsAnalyticAt}` is finite (union of the two finite analytic-bad sets). -/
theorem finite_not_readsAnalyticAt (g₀ h : MeromorphicFunction X) :
    {x : X | ¬ ReadsAnalyticAt g₀ h x}.Finite := by
  refine (h.finite_nonAnalyticAt.union g₀.finite_nonAnalyticAt).subset ?_
  intro x hx
  rw [Set.mem_setOf_eq, ReadsAnalyticAt, not_and_or] at hx
  rcases hx with h1 | h2
  · exact Set.mem_union_left _ h1
  · exact Set.mem_union_right _ h2

/-- Chart-read analyticity transports from the own chart to ANY chart containing the point. -/
theorem analyticAt_read_of_ownChart {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    {f : X → ℂ} {x y : X}
    (hxy : x ∈ (chartAt (H := ℂ) y).source)
    (hx : AnalyticAt ℂ (fun z => f ((chartAt (H := ℂ) x).symm z)) ((chartAt (H := ℂ) x) x)) :
    AnalyticAt ℂ (fun z => f ((chartAt (H := ℂ) y).symm z)) ((chartAt (H := ℂ) y) x) := by
  have h := analyticAt_chart_change_to (h := f) hxy (by simpa [Function.comp_def] using hx)
  simpa [Function.comp_def] using h

/-- **Off the bad set the pair coefficient is holomorphic in every chart** (the chart-uniform
Claim A): `pairRead g₀ h y` is `AnalyticAt` at `chart_y x` for every good `x ∈ source_y`. -/
theorem analyticAt_pairRead {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    {g₀ h : MeromorphicFunction X} {x y : X}
    (hx : ReadsAnalyticAt g₀ h x) (hxy : x ∈ (chartAt (H := ℂ) y).source) :
    AnalyticAt ℂ (pairRead g₀ h y) ((chartAt (H := ℂ) y) x) := by
  have hh := analyticAt_read_of_ownChart hxy hx.1
  have hg := analyticAt_read_of_ownChart hxy hx.2
  exact hh.mul hg.deriv

/-- Eventually near `chart_y x`, points stay in the chart target and their preimages stay in any
chart source containing `x` — the germ window for all the transition computations below. -/
theorem eventually_chart_window {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x y y' : X}
    (hxy : x ∈ (chartAt (H := ℂ) y).source) (hxy' : x ∈ (chartAt (H := ℂ) y').source) :
    ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) y) x),
      w ∈ (chartAt (H := ℂ) y).target
        ∧ (chartAt (H := ℂ) y).symm w ∈ (chartAt (H := ℂ) y').source := by
  set φ := chartAt (H := ℂ) y
  have htgt : φ x ∈ φ.target := φ.map_source hxy
  have h1 : ∀ᶠ w in 𝓝 (φ x), w ∈ φ.target := φ.open_target.mem_nhds htgt
  have hcont : ContinuousAt φ.symm (φ x) := φ.continuousAt_symm htgt
  have hsrc : φ.symm (φ x) ∈ (chartAt (H := ℂ) y').source := by
    rw [φ.left_inv hxy]; exact hxy'
  have h2 : ∀ᶠ w in 𝓝 (φ x), φ.symm w ∈ (chartAt (H := ℂ) y').source :=
    hcont.preimage_mem_nhds ((chartAt (H := ℂ) y').open_source.mem_nhds hsrc)
  filter_upwards [h1, h2] with w hw1 hw2
  exact ⟨hw1, hw2⟩

/-- On the germ window, a read through chart `y` is the read through chart `y'` composed with
the transition `T = chart_{y'} ∘ chart_y⁻¹`. -/
theorem read_eventuallyEq_read_comp_transition {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (f : X → ℂ) {x y y' : X}
    (hxy : x ∈ (chartAt (H := ℂ) y).source) (hxy' : x ∈ (chartAt (H := ℂ) y').source) :
    (fun w => f ((chartAt (H := ℂ) y).symm w)) =ᶠ[𝓝 ((chartAt (H := ℂ) y) x)]
      (fun w => f ((chartAt (H := ℂ) y').symm w))
        ∘ (fun w => (chartAt (H := ℂ) y') ((chartAt (H := ℂ) y).symm w)) := by
  filter_upwards [eventually_chart_window hxy hxy'] with w hw
  simp only [Function.comp_apply, (chartAt (H := ℂ) y').left_inv hw.2]

/-- **The `(1,0)`-coefficient transformation rule (Claim B)**: at a good point `x` in the overlap
of two chart sources, `pairRead` through `y` is `pairRead` through `y'` at the transported point,
times the transition derivative. -/
theorem pairRead_transform {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {g₀ h : MeromorphicFunction X} {x y y' : X}
    (hx : ReadsAnalyticAt g₀ h x)
    (hxy : x ∈ (chartAt (H := ℂ) y).source) (hxy' : x ∈ (chartAt (H := ℂ) y').source) :
    pairRead g₀ h y ((chartAt (H := ℂ) y) x)
      = pairRead g₀ h y' ((chartAt (H := ℂ) y') x)
        * deriv (fun w => (chartAt (H := ℂ) y') ((chartAt (H := ℂ) y).symm w))
            ((chartAt (H := ℂ) y) x) := by
  set φ := chartAt (H := ℂ) y with hφdef
  set ψ := chartAt (H := ℂ) y' with hψdef
  set T : ℂ → ℂ := fun w => ψ (φ.symm w) with hTdef
  have hsymm : φ.symm (φ x) = x := φ.left_inv hxy
  have hTx : T (φ x) = ψ x := by rw [hTdef]; simp only [hsymm]
  have hTdiff : DifferentiableAt ℂ T (φ x) := by
    have := (transition_analyticAt_of_mem (y := y) (z := y') hxy hxy').differentiableAt
    simpa [Function.comp_def] using this
  have hgdiff : DifferentiableAt ℂ (fun w => g₀.toFun (ψ.symm w)) (T (φ x)) := by
    rw [hTx]
    exact (analyticAt_read_of_ownChart hxy' hx.2).differentiableAt
  have hgerm := read_eventuallyEq_read_comp_transition g₀.toFun hxy hxy'
  have hderiv : deriv (fun w => g₀.toFun (φ.symm w)) (φ x)
      = deriv (fun w => g₀.toFun (ψ.symm w)) (T (φ x)) * deriv T (φ x) := by
    rw [hgerm.deriv_eq]
    exact deriv_comp (φ x) hgdiff hTdiff
  show h.toFun (φ.symm (φ x)) * deriv (fun w => g₀.toFun (φ.symm w)) (φ x)
    = h.toFun (ψ.symm (ψ x)) * deriv (fun w => g₀.toFun (ψ.symm w)) (ψ x) * deriv T (φ x)
  rw [hsymm, hderiv, hTx, ψ.left_inv hxy']
  ring

/-! ### Smooth chart reads and their `∂̄` -/

/-- The complexified chart read of a smooth real function is `C^∞` at chart-target points. -/
theorem contDiffAt_complexRead {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    {v : X → ℝ}
    (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) v) (y : X) {z : ℂ}
    (hz : z ∈ (chartAt (H := ℂ) y).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w => ((v ((chartAt (H := ℂ) y).symm w) : ℝ) : ℂ)) z := by
  set φ := chartAt (H := ℂ) y with hφ
  have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) φ.symm z :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := y) _ hz).contMDiffAt
      (φ.open_target.mem_nhds hz)
  have hρ : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (fun w : ℂ => v (φ.symm w)) z :=
    hv.contMDiffAt.comp z hsymm
  have hcomplex : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (fun w : ℂ => ((v (φ.symm w) : ℝ) : ℂ)) z :=
    (Complex.ofRealCLM.contMDiff (n := (⊤ : ℕ∞))).contMDiffAt.comp z hρ
  exact contMDiffAt_iff_contDiffAt.1 hcomplex

/-- Real differentiability of the complexified chart read at target points. -/
theorem differentiableAt_complexRead {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    {v : X → ℝ}
    (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) v) (y : X) {z : ℂ}
    (hz : z ∈ (chartAt (H := ℂ) y).target) :
    DifferentiableAt ℝ (fun w => ((v ((chartAt (H := ℂ) y).symm w) : ℝ) : ℂ)) z :=
  (contDiffAt_complexRead hv y hz).differentiableAt (by simp)

/-- Continuity of the `∂̄` of a smooth chart read at target points. -/
theorem continuousAt_dbar_complexRead {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    {v : X → ℝ}
    (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) v) (y : X) {z : ℂ}
    (hz : z ∈ (chartAt (H := ℂ) y).target) :
    ContinuousAt (DbarDisk.dbar
      (fun w => ((v ((chartAt (H := ℂ) y).symm w) : ℝ) : ℂ))) z :=
  DbarDisk.continuousAt_dbar_of_contDiffAt ((contDiffAt_complexRead hv y hz).of_le (by simp))

/-- If `v` is locally constant at the underlying point, the `∂̄` of its chart read vanishes AT the
chart point (and indeed near it). -/
theorem dbar_complexRead_eq_zero_of_eventually_const {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X]
    {v : X → ℝ} {y : X} {z : ℂ}
    (hz : z ∈ (chartAt (H := ℂ) y).target)
    (hconst : ∃ cst : ℝ, ∀ᶠ x' in 𝓝 ((chartAt (H := ℂ) y).symm z), v x' = cst) :
    DbarDisk.dbar (fun w => ((v ((chartAt (H := ℂ) y).symm w) : ℝ) : ℂ)) z = 0 := by
  obtain ⟨cst, hcst⟩ := hconst
  have hcont : ContinuousAt (chartAt (H := ℂ) y).symm z :=
    (chartAt (H := ℂ) y).continuousAt_symm hz
  have hev : (fun w => ((v ((chartAt (H := ℂ) y).symm w) : ℝ) : ℂ))
      =ᶠ[𝓝 z] fun _ => (cst : ℂ) := by
    filter_upwards [hcont.eventually hcst] with w hw
    rw [hw]
  rw [DbarDisk.dbar_congr hev, DbarDisk.dbar_const]

/-! ### The canonical ledger integrand -/

open scoped Classical in
/-- **The canonical ledger integrand** in the chart at `y`, over the window `V ⊆ X`:

  `𝟙_{chart''V} · (P∘chart⁻¹) · ∂̄(v∘chart⁻¹) · pairRead`

— scalar field × `(0,1)`-cutoff-form coefficient × `(1,0)`-pair-form coefficient.  The indicator
makes the formula globally defined (the chart inverse takes junk values outside the target). -/
noncomputable def ledgerIntegrand (g₀ h : MeromorphicFunction X) (P : X → ℂ) (v : X → ℝ)
    (y : X) (V : Set X) : ℂ → ℂ :=
  fun z =>
    if z ∈ (chartAt (H := ℂ) y) '' V then
      P ((chartAt (H := ℂ) y).symm z)
        * DbarDisk.dbar (fun w => ((v ((chartAt (H := ℂ) y).symm w) : ℝ) : ℂ)) z
        * pairRead g₀ h y z
    else 0

/-- Membership unpacking for chart images of subsets of the source. -/
theorem symm_mem_of_mem_image {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {y : X} {V : Set X} (hV : V ⊆ (chartAt (H := ℂ) y).source)
    {z : ℂ} (hz : z ∈ (chartAt (H := ℂ) y) '' V) :
    z ∈ (chartAt (H := ℂ) y).target ∧ (chartAt (H := ℂ) y).symm z ∈ V := by
  obtain ⟨x, hxV, rfl⟩ := hz
  exact ⟨(chartAt (H := ℂ) y).map_source (hV hxV),
    by rwa [(chartAt (H := ℂ) y).left_inv (hV hxV)]⟩

/-- **Window change**: the indicator window may be replaced by a larger one as long as on the
difference either the scalar field vanishes (pointwise) or the cutoff is locally constant. -/
theorem ledgerIntegrand_congr_superset {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g₀ h : MeromorphicFunction X) (P : X → ℂ) (v : X → ℝ)
    (y : X) {V W : Set X} (hVW : V ⊆ W) (hW : W ⊆ (chartAt (H := ℂ) y).source)
    (hkill : ∀ x ∈ W, x ∉ V → P x = 0 ∨ ∃ cst : ℝ, ∀ᶠ x' in 𝓝 x, v x' = cst) :
    ledgerIntegrand g₀ h P v y V = ledgerIntegrand g₀ h P v y W := by
  funext z
  rw [ledgerIntegrand, ledgerIntegrand]
  by_cases hzV : z ∈ (chartAt (H := ℂ) y) '' V
  · rw [if_pos hzV, if_pos (Set.image_mono hVW hzV)]
  · rw [if_neg hzV]
    by_cases hzW : z ∈ (chartAt (H := ℂ) y) '' W
    · rw [if_pos hzW]
      obtain ⟨hz_tgt, hz_mem⟩ := symm_mem_of_mem_image hW hzW
      have hxV : (chartAt (H := ℂ) y).symm z ∉ V := by
        intro hmem
        exact hzV ⟨_, hmem, (chartAt (H := ℂ) y).right_inv hz_tgt⟩
      rcases hkill _ hz_mem hxV with hP0 | hconst
      · rw [hP0, zero_mul, zero_mul]
      · rw [dbar_complexRead_eq_zero_of_eventually_const hz_tgt hconst, mul_zero, zero_mul]
    · rw [if_neg hzW]

/-- **Cutoff aggregation**: a finite sum of ledger integrands over a family of cutoffs is the
ledger integrand of the summed cutoff (pointwise; the `∂̄` is additive on smooth reads). -/
theorem sum_ledgerIntegrand {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    {ι : Type*} (s : Finset ι) (vF : ι → X → ℝ)
    (hvF : ∀ i ∈ s, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (vF i))
    (g₀ h : MeromorphicFunction X) (P : X → ℂ) (y : X) {V : Set X}
    (hV : V ⊆ (chartAt (H := ℂ) y).source) (z : ℂ) :
    ∑ i ∈ s, ledgerIntegrand g₀ h P (vF i) y V z
      = ledgerIntegrand g₀ h P (fun x => ∑ i ∈ s, vF i x) y V z := by
  rw [ledgerIntegrand]
  by_cases hz : z ∈ (chartAt (H := ℂ) y) '' V
  · simp only [ledgerIntegrand, if_pos hz]
    have hz_tgt : z ∈ (chartAt (H := ℂ) y).target := (symm_mem_of_mem_image hV hz).1
    have hfun : (fun w => (((∑ i ∈ s, vF i ((chartAt (H := ℂ) y).symm w)) : ℝ) : ℂ))
        = fun w => ∑ i ∈ s, ((vF i ((chartAt (H := ℂ) y).symm w) : ℝ) : ℂ) := by
      funext w
      push_cast
      rfl
    have hsum_dbar : DbarDisk.dbar
        (fun w => (((∑ i ∈ s, vF i ((chartAt (H := ℂ) y).symm w)) : ℝ) : ℂ)) z
        = ∑ i ∈ s, DbarDisk.dbar
            (fun w => ((vF i ((chartAt (H := ℂ) y).symm w) : ℝ) : ℂ)) z := by
      rw [hfun]
      exact DbarDisk.dbar_fun_sum fun i hi => differentiableAt_complexRead (hvF i hi) y hz_tgt
    rw [hsum_dbar, Finset.mul_sum, Finset.sum_mul]
  · simp only [ledgerIntegrand, if_neg hz, Finset.sum_const_zero]

/-! ### The chart-transport theorem -/

/-- **THE CHART-TRANSPORT INVARIANCE.**  The total plane integral of the ledger integrand does
not depend on the chart it is read in: for an open window `V` inside both chart sources, and
`g₀`/`h`-reads honestly analytic on `V` off a finite set,

  `∫_ℂ ledgerIntegrand g₀ h P v y V = ∫_ℂ ledgerIntegrand g₀ h P v y' V`.

Holomorphic change of variables along the transition `T = chart_{y'} ∘ chart_y⁻¹`:
the `∂̄`-chain-rule factor `conj T′` and the `pairRead` factor `T′` combine exactly into the real
Jacobian `|T′|²`; the finitely many bad points are a null set. -/
theorem integral_ledgerIntegrand_transport {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    (g₀ h : MeromorphicFunction X)
    (P : X → ℂ) (v : X → ℝ) (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) v)
    {y y' : X} {V : Set X} (hVopen : IsOpen V)
    (hVy : V ⊆ (chartAt (H := ℂ) y).source) (hVy' : V ⊆ (chartAt (H := ℂ) y').source)
    {E : Set X} (hE : E.Finite)
    (hgood : ∀ x ∈ V, x ∉ E → ReadsAnalyticAt g₀ h x) :
    ∫ z, ledgerIntegrand g₀ h P v y V z = ∫ w, ledgerIntegrand g₀ h P v y' V w := by
  classical
  set φ := chartAt (H := ℂ) y with hφdef
  set ψ := chartAt (H := ℂ) y' with hψdef
  set T : ℂ → ℂ := fun z => ψ (φ.symm z) with hTdef
  have hUopen : IsOpen (φ '' V) := φ.isOpen_image_of_subset_source hVopen hVy
  -- reduce both sides to set integrals over the chart images
  have hlhs : (∫ z, ledgerIntegrand g₀ h P v y V z)
      = ∫ z in φ '' V, ledgerIntegrand g₀ h P v y V z :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by rw [ledgerIntegrand, if_neg hz])).symm
  have hrhs : (∫ w, ledgerIntegrand g₀ h P v y' V w)
      = ∫ w in ψ '' V, ledgerIntegrand g₀ h P v y' V w :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun w hw => by rw [ledgerIntegrand, if_neg hw])).symm
  -- the transition data on the chart image
  have hTdiff : ∀ z ∈ φ '' V, DifferentiableAt ℂ T z := by
    rintro z ⟨x, hxV, rfl⟩
    have := (transition_analyticAt_of_mem (y := y) (z := y') (hVy hxV)
      (hVy' hxV)).differentiableAt
    simpa [Function.comp_def] using this
  have hTinj : Set.InjOn T (φ '' V) := by
    rintro z₁ ⟨x₁, hx₁, rfl⟩ z₂ ⟨x₂, hx₂, rfl⟩ heq
    have h1 : T (φ x₁) = ψ x₁ := by rw [hTdef]; simp only [φ.left_inv (hVy hx₁)]
    have h2 : T (φ x₂) = ψ x₂ := by rw [hTdef]; simp only [φ.left_inv (hVy hx₂)]
    rw [h1, h2] at heq
    have hx12 : x₁ = x₂ := ψ.injOn (hVy' hx₁) (hVy' hx₂) heq
    rw [hx12]
  have hTimage : T '' (φ '' V) = ψ '' V := by
    rw [← Set.image_comp]
    refine Set.image_congr (fun x hx => ?_)
    show ψ (φ.symm (φ x)) = ψ x
    rw [φ.left_inv (hVy hx)]
  -- holomorphic change of variables
  have hcov := integral_image_holomorphic hUopen.measurableSet hTdiff hTinj
    (ledgerIntegrand g₀ h P v y' V)
  rw [hTimage] at hcov
  rw [hlhs, hrhs, hcov]
  -- pointwise identification a.e. on `φ '' V` (off the finite bad image)
  refine setIntegral_congr_ae hUopen.measurableSet ?_
  have hEfin : ((φ '' (E ∩ V)) : Set ℂ).Finite := (hE.inter_of_left V).image _
  filter_upwards [compl_mem_ae_iff.mpr (hEfin.measure_zero volume)] with z hzE hzU
  obtain ⟨x, hxV, rfl⟩ := hzU
  have hxE : x ∉ E := fun hmem => hzE (Set.mem_image_of_mem _ ⟨hmem, hxV⟩)
  have hx : ReadsAnalyticAt g₀ h x := hgood x hxV hxE
  have hsymm : φ.symm (φ x) = x := φ.left_inv (hVy hxV)
  have hTx : T (φ x) = ψ x := by rw [hTdef]; simp only [hsymm]
  have hzV : φ x ∈ φ '' V := Set.mem_image_of_mem _ hxV
  have hwV : T (φ x) ∈ ψ '' V := by rw [hTx]; exact Set.mem_image_of_mem _ hxV
  -- unfold both indicators
  rw [ledgerIntegrand, ledgerIntegrand, if_pos hzV, if_pos hwV]
  -- collapse the points
  have hψsymm : ψ.symm (T (φ x)) = x := by rw [hTx]; exact ψ.left_inv (hVy' hxV)
  -- the ∂̄ factor transformation (Wirtinger chain rule)
  have hTdiffz : DifferentiableAt ℂ T (φ x) := hTdiff _ hzV
  have hvdiff : DifferentiableAt ℝ
      (fun w => ((v (ψ.symm w) : ℝ) : ℂ)) (T (φ x)) := by
    rw [hTx]
    exact differentiableAt_complexRead hv y' (ψ.map_source (hVy' hxV))
  have hdgerm : (fun w => ((v (φ.symm w) : ℝ) : ℂ)) =ᶠ[𝓝 (φ x)]
      (fun w => ((v (ψ.symm w) : ℝ) : ℂ)) ∘ T := by
    filter_upwards [eventually_chart_window (y := y) (y' := y') (hVy hxV) (hVy' hxV)]
      with w hw
    have hw2 : φ.symm w ∈ ψ.source := hw.2
    simp only [Function.comp_apply, hTdef]
    rw [ψ.left_inv hw2]
  have hdbar : DbarDisk.dbar (fun w => ((v (φ.symm w) : ℝ) : ℂ)) (φ x)
      = DbarDisk.dbar (fun w => ((v (ψ.symm w) : ℝ) : ℂ)) (T (φ x))
        * (starRingEnd ℂ) (deriv T (φ x)) := by
    rw [DbarDisk.dbar_congr hdgerm]
    exact dbar_comp_holomorphic hvdiff hTdiffz
  -- the pairRead factor transformation (Claim B)
  have hpair : pairRead g₀ h y (φ x) = pairRead g₀ h y' (T (φ x)) * deriv T (φ x) := by
    rw [hTx]
    exact pairRead_transform hx (hVy hxV) (hVy' hxV)
  -- assemble: conj T′ × T′ = |T′|²
  rw [hsymm, hψsymm, hdbar, hpair, Complex.real_smul]
  rw [show ((Complex.normSq (deriv T (φ x)) : ℝ) : ℂ)
      = deriv T (φ x) * (starRingEnd ℂ) (deriv T (φ x)) from
    (Complex.mul_conj (deriv T (φ x))).symm]
  ring

/-! ### The integrability kit -/

/-- **Continuity of the ledger integrand.**  Bought pointwise: honest continuity at good interior
points; local vanishing at bad points and outside a compact core `K` (the scalar field vanishes
or the cutoff is locally constant there); eventual vanishing outside the window (neighbourhoods
avoid the compact core image). -/
theorem continuous_ledgerIntegrand {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    (g₀ h : MeromorphicFunction X)
    {P : X → ℂ} (hP : Continuous P)
    {v : X → ℝ} (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) v)
    {y : X} {V : Set X} (hVopen : IsOpen V) (hVsub : V ⊆ (chartAt (H := ℂ) y).source)
    {K : Set X} (hK : IsCompact K) (hKV : K ⊆ V)
    (hsupp : ∀ x ∈ V, x ∉ K → P x = 0 ∨ ∃ cst : ℝ, ∀ᶠ x' in 𝓝 x, v x' = cst)
    (hbad : ∀ x ∈ V, ¬ ReadsAnalyticAt g₀ h x →
      (∀ᶠ x' in 𝓝 x, P x' = 0) ∨ ∃ cst : ℝ, ∀ᶠ x' in 𝓝 x, v x' = cst) :
    Continuous (ledgerIntegrand g₀ h P v y V) := by
  set φ := chartAt (H := ℂ) y with hφdef
  have hUopen : IsOpen (φ '' V) := φ.isOpen_image_of_subset_source hVopen hVsub
  have hKimg : IsCompact (φ '' K) :=
    hK.image_of_continuousOn (φ.continuousOn.mono (hKV.trans hVsub))
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hzV : z ∈ φ '' V
  · obtain ⟨hz_tgt, hz_mem⟩ := symm_mem_of_mem_image hVsub hzV
    set x := φ.symm z with hxdef
    have hzx : φ x = z := φ.right_inv hz_tgt
    by_cases hgood : ReadsAnalyticAt g₀ h x
    · -- honest point: product of continuous factors, indicator locally true
      have hev : ledgerIntegrand g₀ h P v y V =ᶠ[𝓝 z]
          fun w => P (φ.symm w)
            * DbarDisk.dbar (fun w' => ((v (φ.symm w') : ℝ) : ℂ)) w
            * pairRead g₀ h y w := by
        filter_upwards [hUopen.mem_nhds hzV] with w hw
        rw [ledgerIntegrand, if_pos hw]
      refine ContinuousAt.congr ?_ hev.symm
      have hc1 : ContinuousAt (fun w => P (φ.symm w)) z :=
        hP.continuousAt.comp (φ.continuousAt_symm hz_tgt)
      have hc2 := continuousAt_dbar_complexRead hv y hz_tgt
      have hc3 : ContinuousAt (pairRead g₀ h y) z := by
        have := (analyticAt_pairRead hgood (hVsub hz_mem)).continuousAt
        rwa [hzx] at this
      exact (hc1.mul hc2).mul hc3
    · -- bad point: the kill conditions force the integrand to vanish near `z`
      rcases hbad x hz_mem hgood with hP0 | hconst
      · -- the scalar field vanishes near `x`
        have hev : ledgerIntegrand g₀ h P v y V =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [(φ.continuousAt_symm hz_tgt).eventually hP0] with w hw
          rw [ledgerIntegrand]
          by_cases hwV : w ∈ φ '' V
          · rw [if_pos hwV, hw, zero_mul, zero_mul]
          · rw [if_neg hwV]
        exact continuousAt_const.congr hev.symm
      · -- the cutoff is locally constant near `x`: its read is constant near every nearby `w`
        obtain ⟨cst, hcst⟩ := hconst
        obtain ⟨O, hO_sub, hO_open, hxO⟩ := eventually_nhds_iff.mp hcst
        have hpre : ∀ᶠ w in 𝓝 z, w ∈ φ.target ∧ φ.symm w ∈ O := by
          have h1 : ∀ᶠ w in 𝓝 z, w ∈ φ.target := φ.open_target.mem_nhds hz_tgt
          have h2 : ∀ᶠ w in 𝓝 z, φ.symm w ∈ O :=
            (φ.continuousAt_symm hz_tgt).preimage_mem_nhds (hO_open.mem_nhds hxO)
          filter_upwards [h1, h2] with w hw1 hw2 using ⟨hw1, hw2⟩
        have hev : ledgerIntegrand g₀ h P v y V =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [hpre] with w hw
          rw [ledgerIntegrand]
          by_cases hwV : w ∈ φ '' V
          · rw [if_pos hwV,
              dbar_complexRead_eq_zero_of_eventually_const hw.1
                ⟨cst, by filter_upwards [hO_open.mem_nhds hw.2] with x' hx' using hO_sub x' hx'⟩,
              mul_zero, zero_mul]
          · rw [if_neg hwV]
        exact continuousAt_const.congr hev.symm
  · -- outside the window: neighbourhoods avoid the compact core image, the kill conditions
    -- force pointwise vanishing
    have hzK : z ∉ φ '' K := fun hmem => hzV (Set.image_mono hKV hmem)
    have hev : ledgerIntegrand g₀ h P v y V =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hKimg.isClosed.isOpen_compl.mem_nhds hzK] with w hw
      rw [ledgerIntegrand]
      by_cases hwV : w ∈ φ '' V
      · rw [if_pos hwV]
        obtain ⟨hw_tgt, hw_mem⟩ := symm_mem_of_mem_image hVsub hwV
        have hwK : φ.symm w ∉ K := fun hmem => hw ⟨_, hmem, φ.right_inv hw_tgt⟩
        rcases hsupp _ hw_mem hwK with hP0 | hconst
        · rw [hP0, zero_mul, zero_mul]
        · rw [dbar_complexRead_eq_zero_of_eventually_const hw_tgt hconst, mul_zero, zero_mul]
      · rw [if_neg hwV]
    exact continuousAt_const.congr hev.symm

/-- **Compact support of the ledger integrand** (support inside the chart image of the core). -/
theorem hasCompactSupport_ledgerIntegrand {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g₀ h : MeromorphicFunction X)
    (P : X → ℂ) {v : X → ℝ}
    {y : X} {V : Set X} (hVsub : V ⊆ (chartAt (H := ℂ) y).source)
    {K : Set X} (hK : IsCompact K) (hKV : K ⊆ V)
    (hsupp : ∀ x ∈ V, x ∉ K → P x = 0 ∨ ∃ cst : ℝ, ∀ᶠ x' in 𝓝 x, v x' = cst) :
    HasCompactSupport (ledgerIntegrand g₀ h P v y V) := by
  set φ := chartAt (H := ℂ) y with hφdef
  have hKimg : IsCompact (φ '' K) :=
    hK.image_of_continuousOn (φ.continuousOn.mono (hKV.trans hVsub))
  refine HasCompactSupport.intro hKimg ?_
  intro z hz
  rw [ledgerIntegrand]
  by_cases hzV : z ∈ φ '' V
  · rw [if_pos hzV]
    obtain ⟨hz_tgt, hz_mem⟩ := symm_mem_of_mem_image hVsub hzV
    have hzK : φ.symm z ∉ K := fun hmem => hz ⟨_, hmem, φ.right_inv hz_tgt⟩
    rcases hsupp _ hz_mem hzK with hP0 | hconst
    · rw [hP0, zero_mul, zero_mul]
    · rw [dbar_complexRead_eq_zero_of_eventually_const hz_tgt hconst, mul_zero, zero_mul]
  · rw [if_neg hzV]

/-- **Integrability of the ledger integrand** (continuity + compact support). -/
theorem integrable_ledgerIntegrand {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    (g₀ h : MeromorphicFunction X)
    {P : X → ℂ} (hP : Continuous P)
    {v : X → ℝ} (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) v)
    {y : X} {V : Set X} (hVopen : IsOpen V) (hVsub : V ⊆ (chartAt (H := ℂ) y).source)
    {K : Set X} (hK : IsCompact K) (hKV : K ⊆ V)
    (hsupp : ∀ x ∈ V, x ∉ K → P x = 0 ∨ ∃ cst : ℝ, ∀ᶠ x' in 𝓝 x, v x' = cst)
    (hbad : ∀ x ∈ V, ¬ ReadsAnalyticAt g₀ h x →
      (∀ᶠ x' in 𝓝 x, P x' = 0) ∨ ∃ cst : ℝ, ∀ᶠ x' in 𝓝 x, v x' = cst) :
    Integrable (ledgerIntegrand g₀ h P v y V) volume :=
  (continuous_ledgerIntegrand g₀ h hP hv hVopen hVsub hK hKV hsupp
    hbad).integrable_of_hasCompactSupport
    (hasCompactSupport_ledgerIntegrand g₀ h P hVsub hK hKV hsupp)

end Jacobians.Dolbeault.StokesResidue
