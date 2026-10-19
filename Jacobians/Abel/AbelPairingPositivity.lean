/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Positivity for the Abel pairing: `⟨η, ω̄⟩`-nondegeneracy (Forster 19.9)

The pairing of a nonzero holomorphic 1-form against its own conjugate is nonzero:

  `pairForm η (conjForm η) ≠ 0`   (`η ≠ 0`),

because each chart piece is `∫ ρⱼ·|h|² dA ≥ 0` (the `2i`-normalised `∬ i·η∧η̄ > 0`
positivity) and at a point where `η ≠ 0` some PoU weight is positive.  Together with the
ℂ-scaling rules (`pairForm_cSmul_const`, `conjForm_smul/add/sum`), this gives the
invertibility of the period Gram matrix `pairMatrix` in `AbelDbarKill`.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), 19.6/19.9 (pp. 155–156).
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
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Constant scalars and the ℂ-scaling rule for the pairing -/

/-- The constant `c` as a `SmoothCFunctions`. -/
def constCF (c : ℂ) : SmoothCFunctions X := ⟨fun _ => c, contMDiff_const⟩

@[simp] theorem constCF_apply (c : ℂ) (x : X) : (constCF (X := X) c) x = c := rfl

/-- `⟨η, c·g⟩ = c·⟨η, g⟩` for a constant ℂ-scale of the `(0,1)`-slot. -/
theorem pairForm_cSmul_const (η : HolomorphicOneForms X) (c : ℂ) (g : SmoothCOneForms X) :
    pairForm η (cSmulForm (constCF c) g) = c * pairForm η g := by
  rw [pairForm, pairForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show pairingIntegrand (cSmulForm (constCF c) g) η (coverRhoC j) (coverCenter j)
      (coverWindow (X := X) j) z
    = c * pairingIntegrand g η (coverRhoC j) (coverCenter j) (coverWindow (X := X) j) z
  rw [pairingIntegrand, pairingIntegrand]
  by_cases hz : z ∈ (chartAt (H := ℂ) (coverCenter j)) '' coverWindow (X := X) j
  · rw [if_pos hz, if_pos hz, read01_cSmulForm]
    rw [show (constCF (X := X) c) ((chartAt (H := ℂ) (coverCenter j)).symm z) = c from rfl]
    ring
  · rw [if_neg hz, if_neg hz, mul_zero]

/-! ### Conjugate-form algebra -/

theorem conjForm_add (η₁ η₂ : HolomorphicOneForms X) :
    conjForm (η₁ + η₂) = conjForm η₁ + conjForm η₂ := by
  refine ContMDiffSection.ext fun x => ?_
  have hval : (η₁ + η₂).toFun x = η₁.toFun x + η₂.toFun x := rfl
  rw [show ((conjForm η₁ + conjForm η₂) x) = (conjForm η₁) x + (conjForm η₂) x by
    rw [show (⇑(conjForm η₁ + conjForm η₂)) x = (conjForm η₁ + conjForm η₂) x from rfl,
      ContMDiffSection.coe_add]
    rfl]
  show conjFiber (η₁ + η₂) x = conjFiber η₁ x + conjFiber η₂ x
  refine ContinuousLinearMap.ext fun v => ?_
  rw [conjFiber_apply, hval]
  show (starRingEnd ℂ) ((η₁.toFun x + η₂.toFun x) v)
    = conjFiber η₁ x v + conjFiber η₂ x v
  rw [ContinuousLinearMap.add_apply, map_add, conjFiber_apply, conjFiber_apply]

theorem conjForm_zero : conjForm (0 : HolomorphicOneForms X) = 0 := by
  refine ContMDiffSection.ext fun x => ?_
  have hval : (0 : HolomorphicOneForms X).toFun x = 0 := rfl
  rw [show ((0 : SmoothCOneForms X) x) = 0 by
    rw [show (⇑(0 : SmoothCOneForms X)) x = (0 : SmoothCOneForms X) x from rfl,
      ContMDiffSection.coe_zero]
    rfl]
  show conjFiber 0 x = 0
  refine ContinuousLinearMap.ext fun v => ?_
  rw [conjFiber_apply, hval]
  simp

/-- Conjugation of a ℂ-scaled form: `conj(c·η) = c̄·conj(η)` (as a `cSmulForm`). -/
theorem conjForm_smul (c : ℂ) (η : HolomorphicOneForms X) :
    conjForm (c • η) = cSmulForm (constCF ((starRingEnd ℂ) c)) (conjForm η) := by
  refine ContMDiffSection.ext fun x => ?_
  have hval : (c • η).toFun x = c • η.toFun x := rfl
  rw [cSmulForm_apply, constCF_apply]
  show conjFiber (c • η) x = (starRingEnd ℂ) c • conjFiber η x
  refine ContinuousLinearMap.ext fun v => ?_
  rw [conjFiber_apply, hval]
  show (starRingEnd ℂ) ((c • η.toFun x) v) = ((starRingEnd ℂ) c • conjFiber η x) v
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, map_mul, ContinuousLinearMap.smul_apply,
    conjFiber_apply, smul_eq_mul]

theorem conjForm_sum {ι : Type*} (s : Finset ι) (f : ι → HolomorphicOneForms X) :
    conjForm (∑ k ∈ s, f k) = ∑ k ∈ s, conjForm (f k) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using conjForm_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, conjForm_add, ih]

/-! ### `pairForm` is ℂ-linear over finite sums in the holomorphic slot -/

theorem pairForm_eta_zero (g : SmoothCOneForms X) :
    pairForm (0 : HolomorphicOneForms X) g = 0 := by
  rw [pairForm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show (fun z => pairingIntegrand g (0 : HolomorphicOneForms X) (coverRhoC j)
      (coverCenter j) (coverWindow (X := X) j) z) = fun _ => (0 : ℂ) from ?_,
    integral_zero]
  funext z
  rw [pairingIntegrand]
  by_cases hz : z ∈ (chartAt (H := ℂ) (coverCenter j)) '' coverWindow (X := X) j
  · rw [if_pos hz]
    have h0 : Jacobians.Montel.localRep (0 : HolomorphicOneForms X) (coverCenter j)
        ((chartAt (H := ℂ) (coverCenter j)).symm z) = 0 := rfl
    rw [h0, mul_zero]
  · rw [if_neg hz]

theorem pairForm_eta_sum {ι : Type*} (s : Finset ι) (f : ι → HolomorphicOneForms X)
    (g : SmoothCOneForms X) :
    pairForm (∑ k ∈ s, f k) g = ∑ k ∈ s, pairForm (f k) g := by
  classical
  induction s using Finset.induction with
  | empty => simpa using pairForm_eta_zero g
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairForm_eta_add, ih]

/-! ### The positivity of `⟨η, η̄⟩` -/

/-- **Positivity of the conjugate pairing** (Forster 19.6-style): for `η ≠ 0`,
`pairForm η (conjForm η) ≠ 0` — each chart piece is `∫ ρⱼ·|h|² ≥ 0` and some piece is
strictly positive at a point where the coefficient and the PoU weight are both nonzero. -/
theorem pairForm_conjForm_ne_zero {η : HolomorphicOneForms X} (hη : η ≠ 0) :
    pairForm η (conjForm η) ≠ 0 := by
  classical
  -- the real piece integrands.
  set pos : Fin ((chartCover : Finset X).card) → ℂ → ℝ := fun j z =>
    if z ∈ (chartAt (H := ℂ) (coverCenter j)) '' coverWindow (X := X) j then
      coverPoU (X := X) j ((chartAt (H := ℂ) (coverCenter j)).symm z)
        * Complex.normSq (Jacobians.Montel.localRep η (coverCenter j)
            ((chartAt (H := ℂ) (coverCenter j)).symm z))
    else 0 with hposdef
  -- the integrand is the coercion of its real part: `ρ·conj(h)·h = ρ·|h|²`.
  have hofReal : ∀ (j : Fin ((chartCover : Finset X).card)) (z : ℂ),
      pairingIntegrand (conjForm η) η (coverRhoC j) (coverCenter j)
        (coverWindow (X := X) j) z = ((pos j z : ℝ) : ℂ) := by
    intro j z
    show pairingIntegrand (conjForm η) η (coverRhoC j) (coverCenter j)
        (coverWindow (X := X) j) z
      = (((if z ∈ (chartAt (H := ℂ) (coverCenter j)) '' coverWindow (X := X) j then
          coverPoU (X := X) j ((chartAt (H := ℂ) (coverCenter j)).symm z)
            * Complex.normSq (Jacobians.Montel.localRep η (coverCenter j)
                ((chartAt (H := ℂ) (coverCenter j)).symm z))
        else 0) : ℝ) : ℂ)
    rw [pairingIntegrand]
    by_cases hz : z ∈ (chartAt (H := ℂ) (coverCenter j)) '' coverWindow (X := X) j
    · rw [if_pos hz, if_pos hz]
      obtain ⟨hz_tgt, hz_mem⟩ := StokesResidue.symm_mem_of_mem_image
        (coverWindow_subset_source j) hz
      set x := (chartAt (H := ℂ) (coverCenter j)).symm z with hxdef
      rw [read01_conjForm η (coverWindow_subset_source j hz_mem)]
      rw [show coverRhoC (X := X) j x = ((coverPoU (X := X) j x : ℝ) : ℂ) from rfl]
      rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
      ring
    · rw [if_neg hz, if_neg hz, Complex.ofReal_zero]
  -- nonnegativity of the real pieces.
  have hnonneg : ∀ (j : Fin ((chartCover : Finset X).card)) (z : ℂ), 0 ≤ pos j z := by
    intro j z
    show 0 ≤ if z ∈ (chartAt (H := ℂ) (coverCenter j)) '' coverWindow (X := X) j then
        coverPoU (X := X) j ((chartAt (H := ℂ) (coverCenter j)).symm z)
          * Complex.normSq (Jacobians.Montel.localRep η (coverCenter j)
              ((chartAt (H := ℂ) (coverCenter j)).symm z))
      else 0
    by_cases hz : z ∈ (chartAt (H := ℂ) (coverCenter j)) '' coverWindow (X := X) j
    · rw [if_pos hz]
      exact mul_nonneg ((coverPoU (X := X)).nonneg j _) (Complex.normSq_nonneg _)
    · rw [if_neg hz]
  -- the real pieces are the real parts of the complex integrands.
  have hposre : ∀ j : Fin ((chartCover : Finset X).card),
      pos j = fun z => (pairingIntegrand (conjForm η) η (coverRhoC j) (coverCenter j)
        (coverWindow (X := X) j) z).re := by
    intro j
    funext z
    rw [hofReal j z, Complex.ofReal_re]
  -- integrability of the real pieces.
  have hint : ∀ j : Fin ((chartCover : Finset X).card), Integrable (pos j) volume := by
    intro j
    rw [hposre j]
    exact (integrable_pairForm_piece (conjForm η) η j).re
  -- the pairing is the coercion of the real sum.
  have hpair : pairForm η (conjForm η)
      = ((∑ j : Fin ((chartCover : Finset X).card), ∫ z, pos j z : ℝ) : ℂ) := by
    rw [pairForm, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (∫ z, pairingIntegrand (conjForm η) η (coverRhoC j) (coverCenter j)
          (coverWindow (X := X) j) z) = ∫ z, ((pos j z : ℝ) : ℂ) from
      integral_congr_ae (Eventually.of_forall fun z => hofReal j z)]
    exact integral_ofReal
  -- the strictly positive piece.
  obtain ⟨a, ha⟩ := exists_localRep_self_ne_zero η hη
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin ((chartCover : Finset X).card),
      coverPoU (X := X) j₀ a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 := sum_coverPoU_eq_one (X := X) a
    rw [Finset.sum_congr rfl fun j _ => hcon j] at h1
    simp at h1
  have hρpos : 0 < coverPoU (X := X) j₀ a :=
    lt_of_le_of_ne ((coverPoU (X := X)).nonneg j₀ a) (Ne.symm hj₀)
  have haW : a ∈ coverWindow (X := X) j₀ :=
    tsupport_coverPoU_subset_window j₀ (subset_tsupport _ hj₀)
  have hasrc : a ∈ (chartAt (H := ℂ) (coverCenter j₀)).source :=
    coverWindow_subset_source j₀ haW
  -- the transported coefficient is nonzero.
  have hrep : Jacobians.Montel.localRep η (coverCenter j₀) a ≠ 0 := by
    have hcoc := deriv_transition_cocycle (x := a) (y := a) (y' := coverCenter j₀)
      (mem_chart_source ℂ a) hasrc
    rw [deriv_transition_self a ((chartAt (H := ℂ) a).map_source
      (mem_chart_source ℂ a))] at hcoc
    have hd : deriv (fun w => (chartAt (H := ℂ) a)
        (((chartAt (H := ℂ) (coverCenter j₀))).symm w))
        ((chartAt (H := ℂ) (coverCenter j₀)) a) ≠ 0 :=
      left_ne_zero_of_mul_eq_one hcoc.symm
    rw [Jacobians.Dolbeault.FormTraceSheet.localRep_eq_transition_mul_self η
      (coverCenter j₀) a hasrc]
    exact mul_ne_zero hd ha
  -- the witness point and the positive value.
  set z₀ : ℂ := (chartAt (H := ℂ) (coverCenter j₀)) a with hz₀def
  have hz₀W : z₀ ∈ (chartAt (H := ℂ) (coverCenter j₀)) '' coverWindow (X := X) j₀ :=
    Set.mem_image_of_mem _ haW
  have hsymm₀ : (chartAt (H := ℂ) (coverCenter j₀)).symm z₀ = a :=
    (chartAt (H := ℂ) (coverCenter j₀)).left_inv hasrc
  have hposz₀ : 0 < pos j₀ z₀ := by
    show 0 < if z₀ ∈ (chartAt (H := ℂ) (coverCenter j₀)) '' coverWindow (X := X) j₀ then
        coverPoU (X := X) j₀ ((chartAt (H := ℂ) (coverCenter j₀)).symm z₀)
          * Complex.normSq (Jacobians.Montel.localRep η (coverCenter j₀)
              ((chartAt (H := ℂ) (coverCenter j₀)).symm z₀))
      else 0
    rw [if_pos hz₀W, hsymm₀]
    exact mul_pos hρpos (Complex.normSq_pos.mpr hrep)
  -- continuity of the real piece and positivity of its integral.
  have hcont : Continuous (pos j₀) := by
    rw [hposre j₀]
    exact Complex.continuous_re.comp (continuous_pairingIntegrand (conjForm η) η
      (continuous_coverRhoC j₀) (coverWindow_isOpen j₀) (coverWindow_subset_source j₀)
      (isCompact_tsupport_coverPoU j₀) (tsupport_coverPoU_subset_window j₀)
      (killsAt_coverRhoC (conjForm η) j₀))
  have hop : IsOpen {z : ℂ | 0 < pos j₀ z} := isOpen_lt continuous_const hcont
  have hμpos : 0 < volume (Function.support (pos j₀)) := by
    refine lt_of_lt_of_le (hop.measure_pos volume ⟨z₀, hposz₀⟩) (measure_mono ?_)
    intro z hz
    exact ne_of_gt hz
  have hintpos : 0 < ∫ z, pos j₀ z := by
    rw [MeasureTheory.integral_pos_iff_support_of_nonneg
      (fun z => hnonneg j₀ z) (hint j₀)]
    exact hμpos
  -- assemble: the real sum is positive.
  have hsumpos : 0 < ∑ j : Fin ((chartCover : Finset X).card), ∫ z, pos j z := by
    refine Finset.sum_pos' (fun j _ => integral_nonneg fun z => hnonneg j z) ?_
    exact ⟨j₀, Finset.mem_univ j₀, hintpos⟩
  rw [hpair]
  exact_mod_cast ne_of_gt hsumpos

end Jacobians.Dolbeault.AbelPairing
