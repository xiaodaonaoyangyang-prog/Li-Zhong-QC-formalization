/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Stokes vanishing for the Abel pairing: `⟨η, ∂̄u⟩ = 0` (Forster 19.10, necessity half)

The pairing of a holomorphic form against any `∂̄`-coboundary vanishes:

  `pairForm η (∂̄u) = 0`.

Per cover chart `j`, the planar compact-support Stokes identity `∫ ∂̄Φⱼ = 0` for
`Φⱼ = 𝟙·ρ̂ⱼ·ûⱼ·η̂ⱼ` (smooth, compactly supported in the chart image) splits — since `η̂ⱼ` is
holomorphic — into

  `∫ 𝟙·ρ̂ⱼ·∂̄ûⱼ·η̂ⱼ = − ∫ 𝟙·(∂̄ρ̂ⱼ)·ûⱼ·η̂ⱼ`,

i.e. (by the `∂̄`-bridge reads) `⟨η, ∂̄u⟩ⱼ = −⟨η, u·∂̄ρⱼ⟩` (the collapse lemma).  Summing
over the cover, `∑ⱼ u·∂̄ρⱼ = u·∂̄(∑ρⱼ) = u·∂̄1 = 0` kills the right side.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §19 (19.9/19.10, pp. 155–157).
-/
import Jacobians.Abel.AbelPairing

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Set Filter Complex MeasureTheory
open Jacobians.Montel Jacobians.Dolbeault.StokesResidue

namespace Jacobians.Dolbeault.AbelPairing

open Jacobians.Dolbeault Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The cover PoU components as bundled smooth functions -/

/-- The `j`-th cover PoU component as a complex `SmoothCFunctions` (`ρ̃ⱼ = ofReal ∘ ρⱼ`). -/
def coverRhoCF (j : Fin ((chartCover : Finset X).card)) : SmoothCFunctions X :=
  ofRealCM.comp (coverPoU (X := X) j)

/-- The PoU components sum to the constant `1`. -/
theorem sum_coverRhoCF : ∑ j, coverRhoCF (X := X) j = 1 := by
  refine ContMDiffMap.ext fun x => ?_
  have h1 : (⇑(∑ j, coverRhoCF (X := X) j) : X → ℂ) = ∑ j, ⇑(coverRhoCF (X := X) j) :=
    map_sum ContMDiffMap.coeFnAddMonoidHom _ _
  rw [show (∑ j, coverRhoCF (X := X) j) x
      = (⇑(∑ j, coverRhoCF (X := X) j) : X → ℂ) x from rfl, h1, Finset.sum_apply,
    ContMDiffMap.coe_one, Pi.one_apply]
  exact sum_coverRhoC_eq_one (X := X) x

/-- `∂̄ρ̃ⱼ` vanishes off `tsupport ρⱼ`. -/
theorem dbarL_coverRhoCF_eq_zero_of_notMem (j : Fin ((chartCover : Finset X).card)) {x : X}
    (hx : x ∉ tsupport (coverPoU (X := X) j)) : (dbarL (coverRhoCF j)) x = 0 := by
  refine dbarL_eq_zero_of_notMem_tsupport (coverRhoCF j) fun hc => hx ?_
  refine closure_mono (fun y hy => ?_) hc
  simp only [Function.mem_support, ne_eq] at hy ⊢
  intro h0
  exact hy (by
    rw [show (coverRhoCF j) y = coverRhoC (X := X) j y from rfl, coverRhoC, h0]
    simp)

/-! ### The gluing data `τⱼ = u · ∂̄ρⱼ` -/

/-- The `j`-th gluing form `τⱼ := u • ∂̄ρ̃ⱼ` (a global smooth `(0,1)`-valued form). -/
def glueForm (u : SmoothCFunctions X) (j : Fin ((chartCover : Finset X).card)) :
    SmoothCOneForms X :=
  cSmulForm u (dbarL (coverRhoCF j))

theorem glueForm_apply (u : SmoothCFunctions X) (j : Fin ((chartCover : Finset X).card))
    (x : X) : (glueForm u j) x = u x • (dbarL (coverRhoCF j)) x := rfl

/-- `τⱼ` dies off `tsupport ρⱼ`. -/
theorem glueForm_eq_zero_of_notMem (u : SmoothCFunctions X)
    (j : Fin ((chartCover : Finset X).card)) {x : X}
    (hx : x ∉ tsupport (coverPoU (X := X) j)) :
    (glueForm u j) x = (0 : ℂ →L[ℝ] ℂ) := by
  rw [glueForm_apply, dbarL_coverRhoCF_eq_zero_of_notMem j hx]
  module

/-- **The gluing forms sum to zero**: `∑ⱼ u·∂̄ρⱼ = u·∂̄(∑ρⱼ) = u·∂̄1 = 0` (pointwise). -/
theorem sum_glueForm_apply (u : SmoothCFunctions X) (x : X) :
    ∑ j, ((glueForm u j) x) = (0 : ℂ →L[ℝ] ℂ) := by
  have h1 : ∑ j, ((glueForm u j) x) = u x • ∑ j, ((dbarL (coverRhoCF (X := X) j)) x) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => rfl
  have h2 : ∑ j, ((dbarL (coverRhoCF (X := X) j)) x) = 0 := by
    have hsum : ∑ j, dbarL (coverRhoCF (X := X) j)
        = dbarL (∑ j, coverRhoCF (X := X) j) := (map_sum (dbarL (X := X)) _ _).symm
    have hcoe : (⇑(∑ j, dbarL (coverRhoCF (X := X) j)))
        = ∑ j, ⇑(dbarL (coverRhoCF (X := X) j)) :=
      map_sum (ContMDiffSection.coeAddHom _ _ _ _) _ _
    have h3 : (∑ j, dbarL (coverRhoCF (X := X) j)) x
        = ∑ j, ((dbarL (coverRhoCF (X := X) j)) x) := by
      rw [show ((∑ j, dbarL (coverRhoCF (X := X) j)) x)
          = (⇑(∑ j, dbarL (coverRhoCF (X := X) j))) x from rfl, hcoe, Finset.sum_apply]
    rw [← h3, hsum, sum_coverRhoCF, dbarL_one_eq_zero]
    rfl
  rw [h1, h2]
  module

/-- `∑ⱼ τⱼ = 0` as forms. -/
theorem sum_glueForm (u : SmoothCFunctions X) :
    ∑ j, glueForm (X := X) u j = 0 := by
  refine ContMDiffSection.ext fun x => ?_
  have hcoe : (⇑(∑ j, glueForm (X := X) u j)) = ∑ j, ⇑(glueForm (X := X) u j) :=
    map_sum (ContMDiffSection.coeAddHom _ _ _ _) _ _
  rw [show ((∑ j, glueForm (X := X) u j) x) = (⇑(∑ j, glueForm (X := X) u j)) x from rfl,
    hcoe, Finset.sum_apply, show (⇑(0 : SmoothCOneForms X)) x = (0 : SmoothCOneForms X) x
      from rfl, ContMDiffSection.coe_zero, Pi.zero_apply]
  exact sum_glueForm_apply u x

/-! ### The per-chart Stokes split -/

open scoped Classical in
/-- The per-chart Stokes potential `Φⱼ = 𝟙·ρ̂ⱼ·ûⱼ·η̂ⱼ`. -/
def stokesPotential (u : SmoothCFunctions X) (η : HolomorphicOneForms X)
    (j : Fin ((chartCover : Finset X).card)) : ℂ → ℂ :=
  fun z =>
    if z ∈ (chartAt (H := ℂ) (coverCenter j)) '' coverWindow (X := X) j then
      coverRhoC (X := X) j ((chartAt (H := ℂ) (coverCenter j)).symm z)
        * u ((chartAt (H := ℂ) (coverCenter j)).symm z)
        * Jacobians.Montel.localRep η (coverCenter j)
            ((chartAt (H := ℂ) (coverCenter j)).symm z)
    else 0

/-- Inside the chart image of the window the potential is the bare product (locally). -/
theorem stokesPotential_eventuallyEq (u : SmoothCFunctions X) (η : HolomorphicOneForms X)
    (j : Fin ((chartCover : Finset X).card)) {z : ℂ}
    (hz : z ∈ (chartAt (H := ℂ) (coverCenter j)) '' coverWindow (X := X) j) :
    stokesPotential u η j =ᶠ[𝓝 z]
      fun w => coverRhoC (X := X) j ((chartAt (H := ℂ) (coverCenter j)).symm w)
        * u ((chartAt (H := ℂ) (coverCenter j)).symm w)
        * Jacobians.Montel.localRep η (coverCenter j)
            ((chartAt (H := ℂ) (coverCenter j)).symm w) := by
  have hopen : IsOpen ((chartAt (H := ℂ) (coverCenter j)) '' coverWindow (X := X) j) :=
    (chartAt (H := ℂ) (coverCenter j)).isOpen_image_of_subset_source (coverWindow_isOpen j)
      (coverWindow_subset_source j)
  filter_upwards [hopen.mem_nhds hz] with w hw
  rw [stokesPotential, if_pos hw]

/-- Off the (compact) chart image of `tsupport ρⱼ` the potential vanishes locally. -/
theorem stokesPotential_eventually_zero (u : SmoothCFunctions X) (η : HolomorphicOneForms X)
    (j : Fin ((chartCover : Finset X).card)) {z : ℂ}
    (hz : z ∉ (chartAt (H := ℂ) (coverCenter j)) '' tsupport (coverPoU (X := X) j)) :
    stokesPotential u η j =ᶠ[𝓝 z] fun _ => 0 := by
  set φ := chartAt (H := ℂ) (coverCenter j) with hφ
  have hKimg : IsCompact (φ '' tsupport (coverPoU (X := X) j)) :=
    (isCompact_tsupport_coverPoU j).image_of_continuousOn (φ.continuousOn.mono
      ((tsupport_coverPoU_subset_window j).trans (coverWindow_subset_source j)))
  filter_upwards [hKimg.isClosed.isOpen_compl.mem_nhds hz] with w hw
  rw [stokesPotential]
  by_cases hwV : w ∈ φ '' coverWindow (X := X) j
  · rw [if_pos hwV]
    obtain ⟨hw_tgt, hw_mem⟩ := StokesResidue.symm_mem_of_mem_image
      (coverWindow_subset_source j) hwV
    have hwK : φ.symm w ∉ tsupport (coverPoU (X := X) j) := fun hmem =>
      hw ⟨_, hmem, φ.right_inv hw_tgt⟩
    rw [coverRhoC_eq_zero_of_notMem j hwK, zero_mul, zero_mul]
  · rw [if_neg hwV]

/-- The potential is globally smooth. -/
theorem contDiff_stokesPotential (u : SmoothCFunctions X) (η : HolomorphicOneForms X)
    (j : Fin ((chartCover : Finset X).card)) :
    ContDiff ℝ (⊤ : ℕ∞) (stokesPotential u η j) := by
  set φ := chartAt (H := ℂ) (coverCenter j) with hφ
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ φ '' coverWindow (X := X) j
  · -- on the window: the three factors are smooth.
    obtain ⟨hz_tgt, hz_mem⟩ := StokesResidue.symm_mem_of_mem_image
      (coverWindow_subset_source j) hz
    refine ContDiffAt.congr_of_eventuallyEq ?_ (stokesPotential_eventuallyEq u η j hz)
    have hρ : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun w => coverRhoC (X := X) j (φ.symm w)) z :=
      StokesResidue.contDiffAt_complexRead (contMDiff_coverPoU j) (coverCenter j) hz_tgt
    have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) φ.symm z :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := coverCenter j) _
        hz_tgt).contMDiffAt (φ.open_target.mem_nhds hz_tgt)
    have hu : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (u (φ.symm w) : ℂ)) z :=
      contMDiffAt_iff_contDiffAt.mp ((u.contMDiff (φ.symm z)).comp z hsymm)
    have hη : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun w => Jacobians.Montel.localRep η (coverCenter j) (φ.symm w)) z :=
      (((Jacobians.Montel.localRep_analyticOn_chartTarget η (coverCenter j)).analyticAt
        (φ.open_target.mem_nhds hz_tgt)).contDiffAt).restrict_scalars ℝ
    exact (hρ.mul hu).mul hη
  · -- outside: vanishes locally (`z` avoids the compact support image).
    have hzK : z ∉ φ '' tsupport (coverPoU (X := X) j) := fun hmem =>
      hz (Set.image_mono (tsupport_coverPoU_subset_window j) hmem)
    exact contDiffAt_const.congr_of_eventuallyEq
      (stokesPotential_eventually_zero u η j hzK)

/-- The potential has compact support. -/
theorem hasCompactSupport_stokesPotential (u : SmoothCFunctions X)
    (η : HolomorphicOneForms X) (j : Fin ((chartCover : Finset X).card)) :
    HasCompactSupport (stokesPotential u η j) := by
  set φ := chartAt (H := ℂ) (coverCenter j) with hφ
  have hKimg : IsCompact (φ '' tsupport (coverPoU (X := X) j)) :=
    (isCompact_tsupport_coverPoU j).image_of_continuousOn (φ.continuousOn.mono
      ((tsupport_coverPoU_subset_window j).trans (coverWindow_subset_source j)))
  refine HasCompactSupport.intro hKimg fun z hz => ?_
  exact (stokesPotential_eventually_zero u η j hz).self_of_nhds

/-- **The pointwise Stokes split**: `∂̄Φⱼ = (𝟙·(∂̄ρ̂ⱼ)·ûⱼ·η̂ⱼ) + (𝟙·ρ̂ⱼ·∂̄ûⱼ·η̂ⱼ)`, i.e.
`∂̄` of the potential is the `glueForm`-integrand plus the `∂̄u`-integrand (the `η̂ⱼ` factor
is holomorphic so its `∂̄` dies). -/
theorem dbar_stokesPotential (u : SmoothCFunctions X) (η : HolomorphicOneForms X)
    (j : Fin ((chartCover : Finset X).card)) (z : ℂ) :
    DbarDisk.dbar (stokesPotential u η j) z
      = pairingIntegrand (glueForm u j) η (fun _ => 1) (coverCenter j)
          (coverWindow (X := X) j) z
        + pairingIntegrand (dbarL u) η (coverRhoC (X := X) j) (coverCenter j)
          (coverWindow (X := X) j) z := by
  classical
  set φ := chartAt (H := ℂ) (coverCenter j) with hφ
  by_cases hz : z ∈ φ '' coverWindow (X := X) j
  · obtain ⟨hz_tgt, hz_mem⟩ := StokesResidue.symm_mem_of_mem_image
      (coverWindow_subset_source j) hz
    set x := φ.symm z with hxdef
    have hzx : φ x = z := φ.right_inv hz_tgt
    -- differentiability of the three planar reads at `z`.
    have hρd : DifferentiableAt ℝ (fun w => coverRhoC (X := X) j (φ.symm w)) z :=
      (StokesResidue.contDiffAt_complexRead (contMDiff_coverPoU j) (coverCenter j)
        hz_tgt).differentiableAt (by simp)
    have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) φ.symm z :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := coverCenter j) _
        hz_tgt).contMDiffAt (φ.open_target.mem_nhds hz_tgt)
    have hud : DifferentiableAt ℝ (fun w => (u (φ.symm w) : ℂ)) z :=
      (contMDiffAt_iff_contDiffAt.mp ((u.contMDiff (φ.symm z)).comp z
        hsymm)).differentiableAt (by simp)
    have hηan : AnalyticAt ℂ
        (fun w => Jacobians.Montel.localRep η (coverCenter j) (φ.symm w)) z :=
      (Jacobians.Montel.localRep_analyticOn_chartTarget η (coverCenter j)).analyticAt
        (φ.open_target.mem_nhds hz_tgt)
    have hηd : DifferentiableAt ℝ
        (fun w => Jacobians.Montel.localRep η (coverCenter j) (φ.symm w)) z :=
      hηan.differentiableAt.restrictScalars ℝ
    -- `∂̄` of the product through the germ.
    have hgermdbar : DbarDisk.dbar (stokesPotential u η j) z
        = DbarDisk.dbar (fun w => coverRhoC (X := X) j (φ.symm w) * (u (φ.symm w) : ℂ)
            * Jacobians.Montel.localRep η (coverCenter j) (φ.symm w)) z :=
      dbarDisk_congr (stokesPotential_eventuallyEq u η j hz)
    -- expand: `∂̄((ρ̂·û)·η̂) = η̂·∂̄(ρ̂·û)` (`η̂` holomorphic) `= η̂·(û·∂̄ρ̂ + ρ̂·∂̄û)`.
    have hprod1 : DbarDisk.dbar (fun w => coverRhoC (X := X) j (φ.symm w)
          * (u (φ.symm w) : ℂ)
          * Jacobians.Montel.localRep η (coverCenter j) (φ.symm w)) z
        = (coverRhoC (X := X) j (φ.symm z) * (u (φ.symm z) : ℂ))
            * DbarDisk.dbar (fun w =>
                Jacobians.Montel.localRep η (coverCenter j) (φ.symm w)) z
          + Jacobians.Montel.localRep η (coverCenter j) (φ.symm z)
            * DbarDisk.dbar (fun w => coverRhoC (X := X) j (φ.symm w)
                * (u (φ.symm w) : ℂ)) z :=
      DbarDisk.dbar_fun_mul (hρd.mul hud) hηd
    have hη0 : DbarDisk.dbar (fun w =>
        Jacobians.Montel.localRep η (coverCenter j) (φ.symm w)) z = 0 :=
      DbarDisk.dbar_eq_zero_of_differentiableAt hηan.differentiableAt
    have hprod2 : DbarDisk.dbar (fun w => coverRhoC (X := X) j (φ.symm w)
          * (u (φ.symm w) : ℂ)) z
        = coverRhoC (X := X) j (φ.symm z)
            * DbarDisk.dbar (fun w => (u (φ.symm w) : ℂ)) z
          + (u (φ.symm z) : ℂ)
            * DbarDisk.dbar (fun w => coverRhoC (X := X) j (φ.symm w)) z :=
      DbarDisk.dbar_fun_mul hρd hud
    -- identify the two `∂̄`-reads with the intrinsic ones.
    have hreadu : DbarDisk.dbar (fun w => (u (φ.symm w) : ℂ)) z
        = read01 (dbarL u) (coverCenter j) x := by
      rw [read01_dbarL u (coverWindow_subset_source j hz_mem), hzx]
      exact dbarDisk_congr (Eventually.of_forall fun w => rfl)
    have hreadρ : DbarDisk.dbar (fun w => coverRhoC (X := X) j (φ.symm w)) z
        = read01 (dbarL (coverRhoCF j)) (coverCenter j) x := by
      rw [read01_dbarL (coverRhoCF j) (coverWindow_subset_source j hz_mem), hzx]
      exact dbarDisk_congr (Eventually.of_forall fun w => rfl)
    have hreadglue : read01 (glueForm u j) (coverCenter j) x
        = (u x : ℂ) * read01 (dbarL (coverRhoCF j)) (coverCenter j) x := by
      rw [show glueForm u j = cSmulForm u (dbarL (coverRhoCF j)) from rfl]
      exact read01_cSmulForm u (dbarL (coverRhoCF j)) (coverCenter j) x
    -- assemble.
    rw [hgermdbar, hprod1, hη0, hprod2, hreadu, hreadρ, pairingIntegrand,
      pairingIntegrand, if_pos hz, if_pos hz, hreadglue]
    ring
  · -- off the window: both sides vanish.
    have hdbar0 : DbarDisk.dbar (stokesPotential u η j) z = 0 := by
      by_cases hzK : z ∈ φ '' tsupport (coverPoU (X := X) j)
      · exact absurd (Set.image_mono (tsupport_coverPoU_subset_window j) hzK) hz
      · rw [dbarDisk_congr (stokesPotential_eventually_zero u η j hzK)]
        exact DbarDisk.dbar_const 0 z
    rw [hdbar0, pairingIntegrand, pairingIntegrand, if_neg hz, if_neg hz, add_zero]

/-! ### The per-chart Stokes identity and the assembly -/

/-- Integrability of the `glueForm` piece. -/
theorem integrable_glueForm_piece (u : SmoothCFunctions X) (η : HolomorphicOneForms X)
    (j : Fin ((chartCover : Finset X).card)) :
    Integrable (pairingIntegrand (glueForm u j) η (fun _ => 1) (coverCenter j)
      (coverWindow (X := X) j)) volume :=
  integrable_pairingIntegrand (glueForm u j) η continuous_const (coverWindow_isOpen j)
    (coverWindow_subset_source j) (isCompact_tsupport_coverPoU j)
    (tsupport_coverPoU_subset_window j)
    (fun _ _ hx => Or.inr (glueForm_eq_zero_of_notMem u j hx))

/-- **The per-chart Stokes identity**: the `∂̄u`-piece integral is minus the
`glueForm`-piece integral. -/
theorem integral_dbar_piece_eq_neg (u : SmoothCFunctions X) (η : HolomorphicOneForms X)
    (j : Fin ((chartCover : Finset X).card)) :
    (∫ z, pairingIntegrand (dbarL u) η (coverRhoC (X := X) j) (coverCenter j)
      (coverWindow (X := X) j) z)
    = -∫ z, pairingIntegrand (glueForm u j) η (fun _ => 1) (coverCenter j)
        (coverWindow (X := X) j) z := by
  have hStokes : ∫ z, DbarDisk.dbar (stokesPotential u η j) z = 0 :=
    Jacobians.Dolbeault.integral_dbar_eq_zero (stokesPotential u η j)
      ((contDiff_stokesPotential u η j).of_le (by simp))
      (hasCompactSupport_stokesPotential u η j)
  have hsplit : (∫ z, DbarDisk.dbar (stokesPotential u η j) z)
      = (∫ z, pairingIntegrand (glueForm u j) η (fun _ => 1) (coverCenter j)
          (coverWindow (X := X) j) z)
        + ∫ z, pairingIntegrand (dbarL u) η (coverRhoC (X := X) j) (coverCenter j)
          (coverWindow (X := X) j) z := by
    rw [← integral_add (integrable_glueForm_piece u η j)
      (integrable_pairForm_piece (dbarL u) η j)]
    exact integral_congr_ae (Eventually.of_forall fun z => dbar_stokesPotential u η j z)
  rw [hsplit] at hStokes
  exact eq_neg_of_add_eq_zero_right hStokes

/-- **Stokes vanishing of the pairing** (Forster 19.10, necessity): the pairing of any
holomorphic 1-form against a `∂̄`-coboundary is zero. -/
theorem pairForm_dbarL (η : HolomorphicOneForms X) (u : SmoothCFunctions X) :
    pairForm η (dbarL u) = 0 := by
  classical
  -- each cover piece is minus the glueForm pairing, by the collapse lemma.
  have hpiece : ∀ j : Fin ((chartCover : Finset X).card),
      (∫ z, pairingIntegrand (dbarL u) η (coverRhoC (X := X) j) (coverCenter j)
        (coverWindow (X := X) j) z)
      = -pairForm η (glueForm u j) := by
    intro j
    rw [integral_dbar_piece_eq_neg u η j]
    congr 1
    exact (pairForm_eq_singleChart (cSmulForm_mem_zeroOne u
        (dbarL_mem_zeroOne (coverRhoCF j))) η (coverWindow_isOpen j)
      (coverWindow_subset_source j) (isCompact_tsupport_coverPoU j)
      (tsupport_coverPoU_subset_window j)
      (fun x hx => glueForm_eq_zero_of_notMem u j hx)).symm
  rw [pairForm, Finset.sum_congr rfl fun j _ => hpiece j]
  rw [show (∑ j, -pairForm η (glueForm (X := X) u j))
      = -∑ j, pairForm η (glueForm (X := X) u j) from
    Finset.sum_neg_distrib (fun j => pairForm η (glueForm (X := X) u j))]
  rw [← pairForm_sum, sum_glueForm, pairForm_zero, neg_zero]

end Jacobians.Dolbeault.AbelPairing
