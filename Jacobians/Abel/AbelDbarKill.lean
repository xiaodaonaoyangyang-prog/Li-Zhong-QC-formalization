/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# The Abel ∂̄-kill step: Forster 19.10 — `⟨ω,σ⟩ = 0 ∀ω ⟹ σ = ∂̄u`

The solvability criterion for `∂̄`: a smooth `(0,1)`-form whose pairing against every
holomorphic basis form vanishes is a `∂̄`-coboundary.

Mechanism: the pairing functional
`Λ : A^{0,1} → ℂ^g`, `Λ(σ)ᵢ = ⟨ωᵢ, σ⟩` kills `im ∂̄` (`pairForm_dbarL`), hence descends to
`Λ̄ : H^{0,1} → ℂ^g`; `Λ̄` is surjective because the **period Gram matrix**
`pairMatrix i j = ⟨ωᵢ, ω̄ⱼ⟩` is invertible (`pairForm_conjForm_ne_zero` positivity) and the
range is an `ℝ`-submodule containing all `c·colⱼ`; and `dim_ℝ H^{0,1} = 2·h¹(𝒪) = 2g
= dim_ℝ ℂ^g` (the Dolbeault comparison + the `h¹ = g` dimension count), so surjective ⟹
injective ⟹ `[σ] = 0`.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), 19.9–19.10 (pp. 155–157).
-/
import Jacobians.Abel.AbelPairingStokes
import Jacobians.Abel.AbelPairingPositivity
import Jacobians.H1Genus.CechH1Genus
noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Set Filter Complex MeasureTheory Module
open Jacobians.Montel Jacobians.Dolbeault.StokesResidue

namespace Jacobians.Dolbeault.AbelPairing

open Jacobians.Dolbeault Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### ℝ-homogeneity of the pairing (completing the linearity kit) -/

theorem pairForm_smul (η : HolomorphicOneForms X) (r : ℝ) (g : SmoothCOneForms X) :
    pairForm η (r • g) = r • pairForm η g := by
  rw [pairForm, pairForm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (∫ z, pairingIntegrand (r • g) η (coverRhoC j) (coverCenter j)
        (coverWindow (X := X) j) z)
      = ∫ z, r • pairingIntegrand g η (coverRhoC j) (coverCenter j)
        (coverWindow (X := X) j) z from
    integral_congr_ae (Eventually.of_forall fun z => pairingIntegrand_smul r g η _ _ _ z)]
  exact integral_smul r _

/-! ### The period Gram matrix and its invertibility -/

/-- **The period Gram matrix** `Nᵢⱼ = ⟨ωᵢ, ω̄ⱼ⟩` of the basis forms against their
conjugates. -/
def pairMatrix (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    Matrix (Fin (genus X)) (Fin (genus X)) ℂ :=
  Matrix.of fun i j =>
    pairForm (periodBasisForm X i) (conjForm (periodBasisForm X j))

/-- The expansion of `ambientIso` over the period basis (cf. `PeriodLatticeNondegenerate`). -/
theorem ambientIso_eq_sum (d : Fin (genus X) → ℂ) :
    ambientIso X d = ∑ j, d j • periodBasisForm X j := by
  have hv' : (∑ i, d i • Pi.basisFun ℂ (Fin (genus X)) i) = d := by
    ext k
    simp [Pi.basisFun_apply, Pi.single_apply, Finset.sum_ite_eq]
  calc ambientIso X d = ambientIso X (∑ i, d i • Pi.basisFun ℂ (Fin (genus X)) i) := by
        rw [hv']
    _ = ∑ i, d i • periodBasisForm X i := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl

/-- **The period Gram matrix is nonsingular** (the 19.9 positivity argument): a kernel
vector `v` would make `g = ∑ v̄ⱼ·ωⱼ ≠ 0` pair to zero against its own conjugate. -/
theorem pairMatrix_det_ne_zero : (pairMatrix X).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  -- the witness form `g = ∑ⱼ v̄ⱼ • ωⱼ`.
  set d : Fin (genus X) → ℂ := fun j => (starRingEnd ℂ) (v j) with hd
  set gv : HolomorphicOneForms X := ambientIso X d with hgv
  have hgv0 : gv ≠ 0 := by
    rw [hgv]
    intro h
    have hd0 : d = 0 := (ambientIso X).map_eq_zero_iff.mp h
    refine hv0 (funext fun j => ?_)
    have := congrFun hd0 j
    rw [hd] at this
    simpa using congrArg (starRingEnd ℂ) this
  have hgsum : gv = ∑ j, d j • periodBasisForm X j := ambientIso_eq_sum d
  -- the conjugate decomposes over the scaled conjugate basis forms.
  have hconj : conjForm gv
      = ∑ j, cSmulForm (constCF (v j)) (conjForm (periodBasisForm X j)) := by
    rw [hgsum, conjForm_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjForm_smul, hd]
    congr 2
    exact Complex.conj_conj (v j)
  -- the basis pairings vanish (the kernel relation).
  have hkill : ∀ i, pairForm (periodBasisForm X i) (conjForm gv) = 0 := by
    intro i
    rw [hconj, pairForm_sum]
    rw [show (∑ j, pairForm (periodBasisForm X i)
          (cSmulForm (constCF (v j)) (conjForm (periodBasisForm X j))))
        = ∑ j, v j * pairMatrix X i j from
      Finset.sum_congr rfl fun j _ => by rw [pairForm_cSmul_const]; rfl]
    have hmv := congrFun hv i
    rw [Matrix.mulVec, dotProduct] at hmv
    rw [show (∑ j, v j * pairMatrix X i j) = ∑ j, pairMatrix X i j * v j from
      Finset.sum_congr rfl fun j _ => mul_comm _ _]
    exact hmv
  -- the quadratic form vanishes — contradicting positivity.
  have hquad : pairForm gv (conjForm gv) = 0 := by
    rw [show pairForm gv (conjForm gv)
        = ∑ i, pairForm (d i • periodBasisForm X i) (conjForm gv) from by
      rw [show gv = ∑ i, d i • periodBasisForm X i from hgsum]
      exact pairForm_eta_sum _ _ _]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [pairForm_eta_smul, hkill i, mul_zero]
  exact pairForm_conjForm_ne_zero hgv0 hquad

/-! ### The pairing functional and its descent to `H^{0,1}` -/

/-- `pairForm η` as an `ℝ`-linear functional on `A¹`, bundling its `ℝ`-linearity in the
form argument (`pairForm_add` / `pairForm_smul`). -/
def pairFormL (η : HolomorphicOneForms X) : SmoothCOneForms X →ₗ[ℝ] ℂ where
  toFun g := pairForm η g
  map_add' := pairForm_add η
  map_smul' r g := pairForm_smul η r g

/-- **The pairing functional** `Λ : A^{0,1} →ₗ[ℝ] ℂ^g`, `Λ(σ)ᵢ = ⟨ωᵢ, σ⟩`.  Assembled from
combinators (`LinearMap.pi` of `pairFormL ∘ subtype`) so additivity and homogeneity are
inherited, rather than re-proved by hand against the `Fin g → ℂ` real-module diamond. -/
def pairFunctional (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    ↥(OneFormsZeroOne X) →ₗ[ℝ] (Fin (genus X) → ℂ) :=
  LinearMap.pi fun i => (pairFormL (periodBasisForm X i)).comp (OneFormsZeroOne X).subtype

theorem pairFunctional_apply (s : ↥(OneFormsZeroOne X)) (i : Fin (genus X)) :
    pairFunctional X s i = pairForm (periodBasisForm X i) (s : SmoothCOneForms X) := rfl

/-- The functional kills `im ∂̄` (Stokes vanishing). -/
theorem dbarImage_le_ker_pairFunctional :
    dbarImageInZeroOne X ≤ LinearMap.ker (pairFunctional X) := by
  intro s hs
  rw [LinearMap.mem_ker]
  funext i
  rw [dbarImageInZeroOne, Submodule.submoduleOf, Submodule.mem_comap] at hs
  obtain ⟨u, hu⟩ := hs
  show pairForm (periodBasisForm X i) (s : SmoothCOneForms X) = 0
  rw [show (s : SmoothCOneForms X) = dbarL u from hu.symm]
  exact pairForm_dbarL _ u

/-- **The descended functional** `Λ̄ : H^{0,1} →ₗ[ℝ] ℂ^g`. -/
def pairFunctionalH01 (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    DolbeaultH01 X →ₗ[ℝ] (Fin (genus X) → ℂ) :=
  (dbarImageInZeroOne X).liftQ (pairFunctional X) dbarImage_le_ker_pairFunctional

theorem pairFunctionalH01_mk (s : ↥(OneFormsZeroOne X)) :
    pairFunctionalH01 X (Submodule.Quotient.mk s) = pairFunctional X s := rfl

/-- **Surjectivity of the descended functional**: the range contains every `c·colⱼ` of the
nonsingular Gram matrix, hence all of `ℂ^g`. -/
theorem pairFunctionalH01_surjective : Function.Surjective (pairFunctionalH01 X) := by
  classical
  intro w
  -- solve `N.mulVec v = w` by nonsingularity.
  have hdet : IsUnit (pairMatrix X).det := isUnit_iff_ne_zero.mpr pairMatrix_det_ne_zero
  set e := (pairMatrix X).toLinearEquiv' ((pairMatrix X).invertibleOfIsUnitDet hdet) with he
  set v : Fin (genus X) → ℂ := e.symm w with hvdef
  have hev : (pairMatrix X).mulVec v = w := by
    have h := e.apply_symm_apply w
    rwa [show e (e.symm w) = (pairMatrix X).mulVec (e.symm w) from rfl] at h
  -- the preimage element `∑ⱼ vⱼ·ω̄ⱼ`.
  set s : ↥(OneFormsZeroOne X) := ∑ j, (⟨cSmulForm (constCF (v j))
      (conjForm (periodBasisForm X j)),
    cSmulForm_mem_zeroOne _ (conjForm_mem_zeroOne _)⟩ : ↥(OneFormsZeroOne X)) with hs
  refine ⟨Submodule.Quotient.mk s, ?_⟩
  rw [pairFunctionalH01_mk]
  funext i
  rw [pairFunctional_apply, hs]
  rw [show ((∑ j, (⟨cSmulForm (constCF (v j)) (conjForm (periodBasisForm X j)),
        cSmulForm_mem_zeroOne _ (conjForm_mem_zeroOne _)⟩ : ↥(OneFormsZeroOne X)) :
      ↥(OneFormsZeroOne X)) : SmoothCOneForms X)
      = ∑ j, cSmulForm (constCF (v j)) (conjForm (periodBasisForm X j)) from by
    exact_mod_cast AddSubmonoidClass.coe_finsetSum _ _]
  rw [pairForm_sum]
  rw [show (∑ j, pairForm (periodBasisForm X i)
        (cSmulForm (constCF (v j)) (conjForm (periodBasisForm X j))))
      = ∑ j, pairMatrix X i j * v j from
    Finset.sum_congr rfl fun j _ => by rw [pairForm_cSmul_const]; rw [mul_comm]; rfl]
  have hmv := congrFun hev i
  rw [Matrix.mulVec, dotProduct] at hmv
  exact hmv

/-! ### The dimension count `dim_ℝ H^{0,1} = 2g` -/

/-- The canonical chart-disk cover is Leray. -/
theorem chartDiskCover_isLeray : (chartDiskCover (X := X)).toFiniteCover.IsLeray :=
  fun i => by simpa using chartDiskCover_simplyConnected (X := X) i

instance : FiniteDimensional ℝ (DolbeaultH01 X) := by
  haveI h1 : FiniteDimensional ℂ ((chartDiskCover (X := X)).toFiniteCover.cechH1 0) :=
    finiteDimensional_cechH1_general _ 0
  haveI h2 : FiniteDimensional ℝ ((chartDiskCover (X := X)).toFiniteCover.cechH1 0) :=
    FiniteDimensional.trans ℝ ℂ _
  exact (comparison_linearEquiv (chartDiskCover (X := X))
    chartDiskCover_isLeray).symm.finiteDimensional

/-- **`dim_ℝ H^{0,1}(X) = 2g`** (Dolbeault comparison + the `h¹ = g` dimension count). -/
theorem finrank_dolbeaultH01 : finrank ℝ (DolbeaultH01 X) = 2 * genus X := by
  rw [cechH1_dolbeault_comparison_proof (chartDiskCover (X := X)) chartDiskCover_isLeray]
  congr 1
  exact FiniteCover.h1Dim_zero_eq_genus (chartDiskCover (X := X)).toFiniteCover
    locallyRealizable_chartDiskCover

/-! ### The kill theorem (Forster 19.10) -/

/-- **Forster 19.10 (the `∂̄`-solvability criterion)**: a smooth `(0,1)`-form pairing to
zero against every basis holomorphic form is a `∂̄`-coboundary. -/
theorem exists_dbarL_eq_of_pairForm_eq_zero {s : SmoothCOneForms X}
    (hs : s ∈ OneFormsZeroOne X)
    (h0 : ∀ i : Fin (genus X), pairForm (periodBasisForm X i) s = 0) :
    ∃ u : SmoothCFunctions X, dbarL u = s := by
  classical
  -- equal real dimensions.
  have hfr : finrank ℝ (DolbeaultH01 X) = finrank ℝ (Fin (genus X) → ℂ) := by
    rw [finrank_dolbeaultH01, finrank_real_of_complex]
    congr 1
    rw [Module.finrank_pi, Fintype.card_fin]
  -- surjective ⟹ injective on equal finite dimensions.
  have hinj : Function.Injective (pairFunctionalH01 X) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mpr
      pairFunctionalH01_surjective
  -- the class of `s` dies.
  have hzero : pairFunctionalH01 X (Submodule.Quotient.mk
      (⟨s, hs⟩ : ↥(OneFormsZeroOne X))) = 0 := by
    rw [pairFunctionalH01_mk]
    funext i
    exact h0 i
  have hmk : (Submodule.Quotient.mk (⟨s, hs⟩ : ↥(OneFormsZeroOne X)) : DolbeaultH01 X)
      = 0 := by
    refine hinj ?_
    rw [hzero, map_zero]
  rw [Submodule.Quotient.mk_eq_zero] at hmk
  rw [dbarImageInZeroOne, Submodule.submoduleOf, Submodule.mem_comap] at hmk
  obtain ⟨u, hu⟩ := hmk
  exact ⟨u, hu⟩

end Jacobians.Dolbeault.AbelPairing
