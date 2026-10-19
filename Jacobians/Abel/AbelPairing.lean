/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# The `∬_X σ∧ω` pairing atom (Forster 19.10)

The global pairing of a smooth `(0,1)`-form `g` against a holomorphic 1-form `η`, realised
as a PoU-weighted finite sum of planar chart integrals over the fixed Montel chart cover —
never a manifold-Stokes theory:

  `pairForm η g := ∑ⱼ ∫_ℂ 𝟙_{chartⱼ''Vⱼ}·ρ̂ⱼ·(read01 g)ⱼ·(localRep η)ⱼ dA`.

Contents:
* `pairingIntegrand` + the continuity/compact-support/integrability kit;
* `integral_pairingIntegrand_transport` — **chart-change invariance** (the `conj T′ × T′ =
  |T′|²` cancellation against the holomorphic change of variables);
* `pairingIntegrand_congr_window` — windows shrink/grow across kill zones;
* `pairForm` and its ℝ-linearity in `g` (`pairForm_add/smul/zsmul/sum/zero/cSmul`) and
  ℂ-linearity in `η` (`pairForm_eta_add/eta_smul`);
* `pairForm_eq_singleChart` — **the collapse lemma**: for `g` fiber-supported in a compact
  inside one chart window, the PoU sum collapses to a single un-weighted chart integral
  (transport + `∑ρⱼ = 1`).

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §19 (pp. 153–157).
-/
import Jacobians.Abel.AbelFormRead
import Jacobians.ResidueTheorem.ResidueStokesCoverPoU
noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Set Filter Complex MeasureTheory
open Jacobians.Montel Jacobians.Dolbeault.StokesResidue

namespace Jacobians.Dolbeault.AbelPairing

open Jacobians.Dolbeault Jacobians

/-! ### The pairing integrand -/

open scoped Classical in
/-- **The pairing integrand** in the chart at `y`, over the window `V ⊆ X`:
`𝟙_{chart''V} · (P∘chart⁻¹) · (read01 g y ∘ chart⁻¹) · (localRep η y ∘ chart⁻¹)`.
The indicator makes the formula globally defined (junk chart-inverse values are cut off). -/
def pairingIntegrand {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (g : SmoothCOneForms X)
    (η : HolomorphicOneForms X)
    (P : X → ℂ) (y : X) (V : Set X) : ℂ → ℂ :=
  fun z =>
    if z ∈ (chartAt (H := ℂ) y) '' V then
      P ((chartAt (H := ℂ) y).symm z)
        * read01 g y ((chartAt (H := ℂ) y).symm z)
        * Jacobians.Montel.localRep η y ((chartAt (H := ℂ) y).symm z)
    else 0

/-- The vanishing kill condition: at `x` either the scalar field or the `(0,1)`-fiber dies. -/
def KillsAt {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (P : X → ℂ) (g : SmoothCOneForms X) (x : X) : Prop :=
  P x = 0 ∨ (g x) = (0 : ℂ →L[ℝ] ℂ)

theorem pairingIntegrand_eq_zero_of_killsAt {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {g : SmoothCOneForms X}
    {η : HolomorphicOneForms X} {P : X → ℂ} {y : X} {V : Set X}
    (_hV : V ⊆ (chartAt (H := ℂ) y).source) {z : ℂ}
    (hz : z ∈ (chartAt (H := ℂ) y) '' V → KillsAt P g ((chartAt (H := ℂ) y).symm z)) :
    pairingIntegrand g η P y V z = 0 := by
  rw [pairingIntegrand]
  by_cases hzV : z ∈ (chartAt (H := ℂ) y) '' V
  · rw [if_pos hzV]
    rcases hz hzV with h | h
    · rw [h, zero_mul, zero_mul]
    · rw [read01_eq_zero_of_apply_eq_zero h, mul_zero, zero_mul]
  · rw [if_neg hzV]

/-- **Window change**: the indicator window may be enlarged as long as the kill condition
holds on the difference. -/
theorem pairingIntegrand_congr_window {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (g : SmoothCOneForms X)
    (η : HolomorphicOneForms X)
    (P : X → ℂ) (y : X) {V W : Set X} (hVW : V ⊆ W)
    (hW : W ⊆ (chartAt (H := ℂ) y).source)
    (hkill : ∀ x ∈ W, x ∉ V → KillsAt P g x) :
    pairingIntegrand g η P y V = pairingIntegrand g η P y W := by
  funext z
  rw [pairingIntegrand, pairingIntegrand]
  by_cases hzV : z ∈ (chartAt (H := ℂ) y) '' V
  · rw [if_pos hzV, if_pos (Set.image_mono hVW hzV)]
  · rw [if_neg hzV]
    by_cases hzW : z ∈ (chartAt (H := ℂ) y) '' W
    · rw [if_pos hzW]
      obtain ⟨hz_tgt, hz_mem⟩ := StokesResidue.symm_mem_of_mem_image hW hzW
      have hxV : (chartAt (H := ℂ) y).symm z ∉ V := fun hmem =>
        hzV ⟨_, hmem, (chartAt (H := ℂ) y).right_inv hz_tgt⟩
      rcases hkill _ hz_mem hxV with h | h
      · rw [h, zero_mul, zero_mul]
      · rw [read01_eq_zero_of_apply_eq_zero h, mul_zero, zero_mul]
    · rw [if_neg hzW]

/-! ### The integrability kit -/

/-- **Continuity of the pairing integrand**: honest continuity at window points (all three
factors are smooth/analytic reads on the chart source), local vanishing outside the compact
core image (the kill condition). -/
theorem continuous_pairingIntegrand {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (g : SmoothCOneForms X)
    (η : HolomorphicOneForms X)
    {P : X → ℂ} (hP : Continuous P)
    {y : X} {V : Set X} (hVopen : IsOpen V) (hVsub : V ⊆ (chartAt (H := ℂ) y).source)
    {K : Set X} (hK : IsCompact K) (hKV : K ⊆ V)
    (hsupp : ∀ x ∈ V, x ∉ K → KillsAt P g x) :
    Continuous (pairingIntegrand g η P y V) := by
  set φ := chartAt (H := ℂ) y with hφdef
  have hUopen : IsOpen (φ '' V) := φ.isOpen_image_of_subset_source hVopen hVsub
  have hKimg : IsCompact (φ '' K) :=
    hK.image_of_continuousOn (φ.continuousOn.mono (hKV.trans hVsub))
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hzV : z ∈ φ '' V
  · -- interior point: product of continuous factors.
    obtain ⟨hz_tgt, hz_mem⟩ := StokesResidue.symm_mem_of_mem_image hVsub hzV
    have hev : pairingIntegrand g η P y V =ᶠ[𝓝 z]
        fun w => P (φ.symm w) * read01 g y (φ.symm w)
          * Jacobians.Montel.localRep η y (φ.symm w) := by
      filter_upwards [hUopen.mem_nhds hzV] with w hw
      rw [pairingIntegrand, if_pos hw]
    refine ContinuousAt.congr ?_ hev.symm
    have hsymm : ContinuousAt φ.symm z := φ.continuousAt_symm hz_tgt
    have hc1 : ContinuousAt (fun w => P (φ.symm w)) z := hP.continuousAt.comp hsymm
    have hc2 : ContinuousAt (fun w => read01 g y (φ.symm w)) z :=
      ((contMDiffAt_read01 g (hVsub hz_mem)).continuousAt).comp hsymm
    have hc3 : ContinuousAt (fun w => Jacobians.Montel.localRep η y (φ.symm w)) z :=
      ((Jacobians.Montel.localRep_analyticOn_chartTarget η y).analyticAt
        (φ.open_target.mem_nhds hz_tgt)).continuousAt
    exact (hc1.mul hc2).mul hc3
  · -- outside the window: the integrand vanishes near `z`.
    have hzK : z ∉ φ '' K := fun hmem => hzV (Set.image_mono hKV hmem)
    have hev : pairingIntegrand g η P y V =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hKimg.isClosed.isOpen_compl.mem_nhds hzK] with w hw
      refine pairingIntegrand_eq_zero_of_killsAt hVsub fun hwV => ?_
      obtain ⟨hw_tgt, hw_mem⟩ := StokesResidue.symm_mem_of_mem_image hVsub hwV
      have hwK : φ.symm w ∉ K := fun hmem => hw ⟨_, hmem, φ.right_inv hw_tgt⟩
      exact hsupp _ hw_mem hwK
    exact continuousAt_const.congr hev.symm

/-- Compact support of the pairing integrand (inside the chart image of the core). -/
theorem hasCompactSupport_pairingIntegrand {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (g : SmoothCOneForms X)
    (η : HolomorphicOneForms X) (P : X → ℂ)
    {y : X} {V : Set X} (hVsub : V ⊆ (chartAt (H := ℂ) y).source)
    {K : Set X} (hK : IsCompact K) (hKV : K ⊆ V)
    (hsupp : ∀ x ∈ V, x ∉ K → KillsAt P g x) :
    HasCompactSupport (pairingIntegrand g η P y V) := by
  set φ := chartAt (H := ℂ) y with hφdef
  have hKimg : IsCompact (φ '' K) :=
    hK.image_of_continuousOn (φ.continuousOn.mono (hKV.trans hVsub))
  refine HasCompactSupport.intro hKimg fun z hz => ?_
  refine pairingIntegrand_eq_zero_of_killsAt hVsub fun hzV => ?_
  obtain ⟨hz_tgt, hz_mem⟩ := StokesResidue.symm_mem_of_mem_image hVsub hzV
  have hzK : φ.symm z ∉ K := fun hmem => hz ⟨_, hmem, φ.right_inv hz_tgt⟩
  exact hsupp _ hz_mem hzK

/-- Integrability of the pairing integrand (continuity + compact support). -/
theorem integrable_pairingIntegrand {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (g : SmoothCOneForms X)
    (η : HolomorphicOneForms X)
    {P : X → ℂ} (hP : Continuous P)
    {y : X} {V : Set X} (hVopen : IsOpen V) (hVsub : V ⊆ (chartAt (H := ℂ) y).source)
    {K : Set X} (hK : IsCompact K) (hKV : K ⊆ V)
    (hsupp : ∀ x ∈ V, x ∉ K → KillsAt P g x) :
    Integrable (pairingIntegrand g η P y V) volume :=
  (continuous_pairingIntegrand g η hP hVopen hVsub hK hKV
    hsupp).integrable_of_hasCompactSupport
    (hasCompactSupport_pairingIntegrand g η P hVsub hK hKV hsupp)

/-! ### The chart-transport invariance -/

/-- **Chart-change invariance of the pairing integral**: for `g ∈ A^{0,1}` and an open
window inside both chart sources, the plane integral of the pairing integrand does not
depend on the chart it is read in.  Holomorphic change of variables along the transition:
the `(0,1)`-factor transforms by `conj T′` (`read01_transform`), the `(1,0)`-factor by `T′`
(`localRep_transform`), and `conj T′ · T′ = |T′|²` is the real Jacobian. -/
theorem integral_pairingIntegrand_transport {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {g : SmoothCOneForms X}
    (hg : g ∈ OneFormsZeroOne X) (η : HolomorphicOneForms X) (P : X → ℂ)
    {y y' : X} {V : Set X} (hVopen : IsOpen V)
    (hVy : V ⊆ (chartAt (H := ℂ) y).source) (hVy' : V ⊆ (chartAt (H := ℂ) y').source) :
    ∫ z, pairingIntegrand g η P y V z = ∫ w, pairingIntegrand g η P y' V w := by
  classical
  set φ := chartAt (H := ℂ) y with hφdef
  set ψ := chartAt (H := ℂ) y' with hψdef
  set T : ℂ → ℂ := fun z => ψ (φ.symm z) with hTdef
  have hUopen : IsOpen (φ '' V) := φ.isOpen_image_of_subset_source hVopen hVy
  -- reduce both sides to set integrals over the chart images.
  have hlhs : (∫ z, pairingIntegrand g η P y V z)
      = ∫ z in φ '' V, pairingIntegrand g η P y V z :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by rw [pairingIntegrand, if_neg hz])).symm
  have hrhs : (∫ w, pairingIntegrand g η P y' V w)
      = ∫ w in ψ '' V, pairingIntegrand g η P y' V w :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun w hw => by rw [pairingIntegrand, if_neg hw])).symm
  -- the transition data on the chart image.
  have hTdiff : ∀ z ∈ φ '' V, DifferentiableAt ℂ T z := by
    rintro z ⟨x, hxV, rfl⟩
    have h := (transition_analyticAt_of_mem (y := y) (z := y') (hVy hxV)
      (hVy' hxV)).differentiableAt
    simpa [Function.comp_def] using h
  have hTinj : Set.InjOn T (φ '' V) := by
    rintro z₁ ⟨x₁, hx₁, rfl⟩ z₂ ⟨x₂, hx₂, rfl⟩ heq
    have h1 : T (φ x₁) = ψ x₁ := by rw [hTdef]; simp only [φ.left_inv (hVy hx₁)]
    have h2 : T (φ x₂) = ψ x₂ := by rw [hTdef]; simp only [φ.left_inv (hVy hx₂)]
    rw [h1, h2] at heq
    rw [ψ.injOn (hVy' hx₁) (hVy' hx₂) heq]
  have hTimage : T '' (φ '' V) = ψ '' V := by
    rw [← Set.image_comp]
    refine Set.image_congr fun x hx => ?_
    show ψ (φ.symm (φ x)) = ψ x
    rw [φ.left_inv (hVy hx)]
  -- holomorphic change of variables.
  have hcov := integral_image_holomorphic hUopen.measurableSet hTdiff hTinj
    (pairingIntegrand g η P y' V)
  rw [hTimage] at hcov
  rw [hlhs, hrhs, hcov]
  -- pointwise identification on `φ '' V`.
  refine setIntegral_congr_fun hUopen.measurableSet ?_
  rintro z hzU
  obtain ⟨x, hxV, rfl⟩ := hzU
  have hsymm : φ.symm (φ x) = x := φ.left_inv (hVy hxV)
  have hTx : T (φ x) = ψ x := by rw [hTdef]; simp only [hsymm]
  have hzV : φ x ∈ φ '' V := Set.mem_image_of_mem _ hxV
  have hwV : T (φ x) ∈ ψ '' V := by rw [hTx]; exact Set.mem_image_of_mem _ hxV
  show pairingIntegrand g η P y V (φ x)
    = Complex.normSq (deriv T (φ x)) • pairingIntegrand g η P y' V (T (φ x))
  rw [pairingIntegrand, pairingIntegrand, if_pos hzV, if_pos hwV]
  have hψsymm : ψ.symm (T (φ x)) = x := by rw [hTx]; exact ψ.left_inv (hVy' hxV)
  -- the two transformation laws + the Jacobian.
  have hread : read01 g y x = (starRingEnd ℂ) (deriv T (φ x)) * read01 g y' x := by
    have h := read01_transform hg (hVy hxV) (hVy' hxV)
    rwa [show deriv (fun w => (chartAt (H := ℂ) y') ((chartAt (H := ℂ) y).symm w))
        ((chartAt (H := ℂ) y) x) = deriv T (φ x) from rfl] at h
  have hrep : Jacobians.Montel.localRep η y x
      = deriv T (φ x) * Jacobians.Montel.localRep η y' x := by
    have h := localRep_transform η (hVy hxV) (hVy' hxV)
    rwa [show deriv (fun w => (chartAt (H := ℂ) y') ((chartAt (H := ℂ) y).symm w))
        ((chartAt (H := ℂ) y) x) = deriv T (φ x) from rfl] at h
  rw [hsymm, hψsymm, hread, hrep, Complex.real_smul,
    show ((Complex.normSq (deriv T (φ x)) : ℝ) : ℂ)
        = deriv T (φ x) * (starRingEnd ℂ) (deriv T (φ x)) from
      (Complex.mul_conj (deriv T (φ x))).symm]
  ring

/-! ### The pairing `pairForm` over the fixed Montel chart cover -/

/-- The `j`-th cover window: the outer open shrinkage at the `j`-th cover centre. -/
def coverWindow {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]
    (j : Fin ((chartCover : Finset X).card)) : Set X :=
  chartOpen (X := X) (coverCenter j)

theorem coverWindow_isOpen {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] (j : Fin ((chartCover : Finset X).card)) :
    IsOpen (coverWindow (X := X) j) := chartOpen_isOpen _

theorem coverWindow_subset_source {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (j : Fin ((chartCover : Finset X).card)) :
    coverWindow (X := X) j ⊆ (chartAt (H := ℂ) (coverCenter j)).source :=
  chartOpen_subset_chartAt_source (coverCenter j) (coverCenter_mem j)

theorem tsupport_coverPoU_subset_window {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (j : Fin ((chartCover : Finset X).card)) :
    tsupport (coverPoU (X := X) j) ⊆ coverWindow (X := X) j :=
  coverPoU_tsupport_subset j

/-- The kill condition for the PoU scalar field: `ρ̂ⱼ` vanishes off its compact support. -/
theorem killsAt_coverRhoC {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (g : SmoothCOneForms X)
    (j : Fin ((chartCover : Finset X).card)) :
    ∀ x ∈ coverWindow (X := X) j, x ∉ tsupport (coverPoU (X := X) j) →
      KillsAt (coverRhoC j) g x :=
  fun _ _ hx => Or.inl (coverRhoC_eq_zero_of_notMem j hx)

/-- The `j`-th piece of the pairing is integrable. -/
theorem integrable_pairForm_piece {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (g : SmoothCOneForms X)
    (η : HolomorphicOneForms X)
    (j : Fin ((chartCover : Finset X).card)) :
    Integrable (pairingIntegrand g η (coverRhoC j) (coverCenter j)
      (coverWindow (X := X) j)) volume :=
  integrable_pairingIntegrand g η (continuous_coverRhoC j) (coverWindow_isOpen j)
    (coverWindow_subset_source j) (isCompact_tsupport_coverPoU j)
    (tsupport_coverPoU_subset_window j) (killsAt_coverRhoC g j)

/-- **The pairing `⟨η, g⟩ = ∬_X g∧η`** (up to the fixed constant `2i`), as the PoU-weighted
sum of planar chart integrals over the fixed Montel chart cover. -/
def pairForm {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (η : HolomorphicOneForms X) (g : SmoothCOneForms X) :
    ℂ :=
  ∑ j : Fin ((chartCover : Finset X).card),
    ∫ z, pairingIntegrand g η (coverRhoC j) (coverCenter j) (coverWindow (X := X) j) z

/-! ### Linearity in the `(0,1)`-slot -/

theorem pairingIntegrand_add {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (g₁ g₂ : SmoothCOneForms X)
    (η : HolomorphicOneForms X)
    (P : X → ℂ) (y : X) (V : Set X) (z : ℂ) :
    pairingIntegrand (g₁ + g₂) η P y V z
      = pairingIntegrand g₁ η P y V z + pairingIntegrand g₂ η P y V z := by
  rw [pairingIntegrand, pairingIntegrand, pairingIntegrand]
  by_cases hz : z ∈ (chartAt (H := ℂ) y) '' V
  · rw [if_pos hz, if_pos hz, if_pos hz, read01_add]
    ring
  · rw [if_neg hz, if_neg hz, if_neg hz, add_zero]

theorem pairingIntegrand_zsmul {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (n : ℤ) (g : SmoothCOneForms X)
    (η : HolomorphicOneForms X)
    (P : X → ℂ) (y : X) (V : Set X) (z : ℂ) :
    pairingIntegrand (n • g) η P y V z = n • pairingIntegrand g η P y V z := by
  rw [pairingIntegrand, pairingIntegrand]
  by_cases hz : z ∈ (chartAt (H := ℂ) y) '' V
  · rw [if_pos hz, if_pos hz, read01_zsmul]
    rw [zsmul_eq_mul, zsmul_eq_mul]
    ring
  · rw [if_neg hz, if_neg hz, smul_zero]

theorem pairingIntegrand_smul {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (r : ℝ) (g : SmoothCOneForms X)
    (η : HolomorphicOneForms X)
    (P : X → ℂ) (y : X) (V : Set X) (z : ℂ) :
    pairingIntegrand (r • g) η P y V z = r • pairingIntegrand g η P y V z := by
  rw [pairingIntegrand, pairingIntegrand]
  by_cases hz : z ∈ (chartAt (H := ℂ) y) '' V
  · rw [if_pos hz, if_pos hz, read01_smul]
    rw [Complex.real_smul, Complex.real_smul]
    ring
  · rw [if_neg hz, if_neg hz, smul_zero]

theorem pairingIntegrand_zero {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (η : HolomorphicOneForms X)
    (P : X → ℂ) (y : X) (V : Set X) (z : ℂ) :
    pairingIntegrand (0 : SmoothCOneForms X) η P y V z = 0 := by
  rw [pairingIntegrand]
  by_cases hz : z ∈ (chartAt (H := ℂ) y) '' V
  · rw [if_pos hz, read01_zero]
    ring
  · rw [if_neg hz]

theorem pairForm_add {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (η : HolomorphicOneForms X)
    (g₁ g₂ : SmoothCOneForms X) :
    pairForm η (g₁ + g₂) = pairForm η g₁ + pairForm η g₂ := by
  rw [pairForm, pairForm, pairForm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_add (integrable_pairForm_piece g₁ η j) (integrable_pairForm_piece g₂ η j)]
  exact integral_congr_ae (Eventually.of_forall fun z =>
    pairingIntegrand_add g₁ g₂ η _ _ _ z)

theorem pairForm_zero {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (η : HolomorphicOneForms X) :
    pairForm η (0 : SmoothCOneForms X) = 0 := by
  rw [pairForm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show (fun z => pairingIntegrand (0 : SmoothCOneForms X) η (coverRhoC j)
      (coverCenter j) (coverWindow (X := X) j) z) = fun _ => (0 : ℂ) from
    funext fun z => pairingIntegrand_zero η _ _ _ z]
  exact integral_zero _ _

theorem pairForm_zsmul {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (η : HolomorphicOneForms X) (n : ℤ)
    (g : SmoothCOneForms X) :
    pairForm η (n • g) = n • pairForm η g := by
  rw [pairForm, pairForm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (∫ z, pairingIntegrand (n • g) η (coverRhoC j) (coverCenter j)
        (coverWindow (X := X) j) z)
      = ∫ z, (n : ℂ) * pairingIntegrand g η (coverRhoC j) (coverCenter j)
        (coverWindow (X := X) j) z from
    integral_congr_ae (Eventually.of_forall fun z => by
      rw [pairingIntegrand_zsmul n g η _ _ _ z, zsmul_eq_mul])]
  rw [integral_const_mul, zsmul_eq_mul]

theorem pairForm_sum {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {ι : Type*}
    (η : HolomorphicOneForms X) (s : Finset ι)
    (g : ι → SmoothCOneForms X) :
    pairForm η (∑ k ∈ s, g k) = ∑ k ∈ s, pairForm η (g k) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using pairForm_zero η
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pairForm_add, ih]

/-! ### Linearity in the holomorphic slot -/

theorem pairForm_eta_add {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (η₁ η₂ : HolomorphicOneForms X)
    (g : SmoothCOneForms X) :
    pairForm (η₁ + η₂) g = pairForm η₁ g + pairForm η₂ g := by
  rw [pairForm, pairForm, pairForm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_add (integrable_pairForm_piece g η₁ j) (integrable_pairForm_piece g η₂ j)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show pairingIntegrand g (η₁ + η₂) (coverRhoC j) (coverCenter j) (coverWindow (X := X) j) z
    = pairingIntegrand g η₁ (coverRhoC j) (coverCenter j) (coverWindow (X := X) j) z
      + pairingIntegrand g η₂ (coverRhoC j) (coverCenter j) (coverWindow (X := X) j) z
  rw [pairingIntegrand, pairingIntegrand, pairingIntegrand]
  by_cases hz : z ∈ (chartAt (H := ℂ) (coverCenter j)) '' coverWindow (X := X) j
  · rw [if_pos hz, if_pos hz, if_pos hz, Jacobians.Montel.localRep_add]
    ring
  · rw [if_neg hz, if_neg hz, if_neg hz, add_zero]

theorem pairForm_eta_smul {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (c : ℂ) (η : HolomorphicOneForms X)
    (g : SmoothCOneForms X) :
    pairForm (c • η) g = c * pairForm η g := by
  rw [pairForm, pairForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show pairingIntegrand g (c • η) (coverRhoC j) (coverCenter j) (coverWindow (X := X) j) z
    = c * pairingIntegrand g η (coverRhoC j) (coverCenter j) (coverWindow (X := X) j) z
  rw [pairingIntegrand, pairingIntegrand]
  by_cases hz : z ∈ (chartAt (H := ℂ) (coverCenter j)) '' coverWindow (X := X) j
  · rw [if_pos hz, if_pos hz, Jacobians.Montel.localRep_smul]
    rw [smul_eq_mul]
    ring
  · rw [if_neg hz, if_neg hz, mul_zero]

/-! ### The collapse lemma -/

/-- **The collapse lemma**: if the `(0,1)`-form `g` is fiber-supported in a compact `K`
inside an open window `W` of a single chart (centre `c`), the PoU pairing collapses to the
single un-weighted chart-`c` integral:

  `pairForm η g = ∫_ℂ 𝟙_{chart_c''W}·(read01 g)_c·(localRep η)_c dA`.

Per cover chart `j`: shrink the window to `Vⱼ ∩ W` (the kill condition holds on the
difference since `g` dies off `K ⊆ W`), transport to the chart at `c`, and sum the PoU
weights to `1`. -/
theorem pairForm_eq_singleChart {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {g : SmoothCOneForms X}
    (hg : g ∈ OneFormsZeroOne X)
    (η : HolomorphicOneForms X) {c : X} {W K : Set X} (hWopen : IsOpen W)
    (hWsub : W ⊆ (chartAt (H := ℂ) c).source) (hK : IsCompact K) (hKW : K ⊆ W)
    (hgsupp : ∀ x, x ∉ K → (g x) = (0 : ℂ →L[ℝ] ℂ)) :
    pairForm η g = ∫ z, pairingIntegrand g η (fun _ => 1) c W z := by
  classical
  -- Step A: shrink each cover window to its intersection with `W`.
  have hshrink : ∀ j : Fin ((chartCover : Finset X).card),
      pairingIntegrand g η (coverRhoC j) (coverCenter j) (coverWindow (X := X) j)
        = pairingIntegrand g η (coverRhoC j) (coverCenter j)
            (coverWindow (X := X) j ∩ W) := by
    intro j
    refine (pairingIntegrand_congr_window g η (coverRhoC j) (coverCenter j)
      Set.inter_subset_left (coverWindow_subset_source j) ?_).symm
    intro x _ hxVW
    by_cases hxV : x ∈ coverWindow (X := X) j ∩ W
    · exact absurd hxV hxVW
    · -- x ∈ Vⱼ ∖ (Vⱼ ∩ W) means x ∉ W, hence x ∉ K, hence the fiber dies.
      by_cases hxW : x ∈ W
      · exact absurd ⟨by assumption, hxW⟩ hxVW
      · exact Or.inr (hgsupp x fun hxK => hxW (hKW hxK))
  -- Step B: transport each piece to the chart at `c`.
  have htrans : ∀ j : Fin ((chartCover : Finset X).card),
      (∫ z, pairingIntegrand g η (coverRhoC j) (coverCenter j)
        (coverWindow (X := X) j ∩ W) z)
      = ∫ z, pairingIntegrand g η (coverRhoC j) c (coverWindow (X := X) j ∩ W) z := by
    intro j
    exact integral_pairingIntegrand_transport hg η (coverRhoC j)
      ((coverWindow_isOpen j).inter hWopen)
      (Set.inter_subset_left.trans (coverWindow_subset_source j))
      (Set.inter_subset_right.trans hWsub)
  -- Step C: integrability of the transported pieces (core `tsupport ρⱼ ∩ K`).
  have hint : ∀ j : Fin ((chartCover : Finset X).card),
      Integrable (pairingIntegrand g η (coverRhoC j) c
        (coverWindow (X := X) j ∩ W)) volume := by
    intro j
    refine integrable_pairingIntegrand g η (continuous_coverRhoC j)
      ((coverWindow_isOpen j).inter hWopen) (Set.inter_subset_right.trans hWsub)
      ((isCompact_tsupport_coverPoU j).inter_right hK.isClosed) ?_ ?_
    · exact Set.subset_inter (Set.inter_subset_left.trans
        (tsupport_coverPoU_subset_window j)) (Set.inter_subset_right.trans hKW)
    · intro x _ hxK
      by_cases hxsupp : x ∈ tsupport (coverPoU (X := X) j)
      · refine Or.inr (hgsupp x fun hxKmem => hxK ⟨hxsupp, hxKmem⟩)
      · exact Or.inl (coverRhoC_eq_zero_of_notMem j hxsupp)
  -- Step D: assemble — sum the integrands pointwise and use `∑ρⱼ = 1`.
  rw [pairForm]
  rw [show (∑ j : Fin ((chartCover : Finset X).card),
        ∫ z, pairingIntegrand g η (coverRhoC j) (coverCenter j)
          (coverWindow (X := X) j) z)
      = ∑ j : Fin ((chartCover : Finset X).card),
        ∫ z, pairingIntegrand g η (coverRhoC j) c (coverWindow (X := X) j ∩ W) z from
    Finset.sum_congr rfl fun j _ => by rw [hshrink j, htrans j]]
  rw [← integral_finsetSum _ fun j _ => hint j]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show (∑ j : Fin ((chartCover : Finset X).card),
      pairingIntegrand g η (coverRhoC j) c (coverWindow (X := X) j ∩ W) z)
    = pairingIntegrand g η (fun _ => 1) c W z
  -- pointwise: the indicator-weighted PoU sum collapses.
  by_cases hzW : z ∈ (chartAt (H := ℂ) c) '' W
  · obtain ⟨hz_tgt, hz_mem⟩ := StokesResidue.symm_mem_of_mem_image hWsub hzW
    set x := (chartAt (H := ℂ) c).symm z with hxdef
    have hsum : ∀ j : Fin ((chartCover : Finset X).card),
        pairingIntegrand g η (coverRhoC j) c (coverWindow (X := X) j ∩ W) z
          = coverRhoC j x * (read01 g c x * Jacobians.Montel.localRep η c x) := by
      intro j
      rw [pairingIntegrand]
      by_cases hzj : z ∈ (chartAt (H := ℂ) c) '' (coverWindow (X := X) j ∩ W)
      · rw [if_pos hzj]
        ring
      · rw [if_neg hzj]
        -- `x ∉ Vⱼ`, so `ρⱼ x = 0`.
        have hxnot : x ∉ coverWindow (X := X) j := by
          intro hmem
          exact hzj ⟨x, ⟨hmem, hz_mem⟩, (chartAt (H := ℂ) c).right_inv hz_tgt⟩
        have hρ0 : coverRhoC j x = 0 :=
          coverRhoC_eq_zero_of_notMem j fun hmem =>
            hxnot (tsupport_coverPoU_subset_window j hmem)
        rw [hρ0, zero_mul]
    rw [Finset.sum_congr rfl fun j _ => hsum j, ← Finset.sum_mul, sum_coverRhoC_eq_one]
    rw [pairingIntegrand, if_pos hzW, one_mul, one_mul]
  · -- off the `W`-image: every term vanishes (`g` dies off `K ⊆ W`), and so does the RHS.
    have hzero : ∀ j : Fin ((chartCover : Finset X).card),
        pairingIntegrand g η (coverRhoC j) c (coverWindow (X := X) j ∩ W) z = 0 := by
      intro j
      refine pairingIntegrand_eq_zero_of_killsAt
        (Set.inter_subset_right.trans hWsub) fun hzj => ?_
      exact absurd (Set.image_mono Set.inter_subset_right hzj) hzW
    rw [Finset.sum_congr rfl fun j _ => hzero j, Finset.sum_const_zero,
      pairingIntegrand, if_neg hzW]

end Jacobians.Dolbeault.AbelPairing
