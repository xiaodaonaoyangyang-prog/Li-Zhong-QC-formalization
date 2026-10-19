/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Serre duality for the tail `H¹`, the surjective half — meromorphic pair frame
(Miranda Thm 3.3, pp. 189–191)

The pair-frame port of `TailDualitySurjective` + §3–§5 of `TailDualitySurjectiveAssembly`
(the genus ≥ 1 holomorphic-ω₀ specialization).  The Λ-side (§1–§2 of the assembly:
`tailMulDual(Q)`, injectivity, `finrank_range_tailMulDualQ`) is frame-independent and reused
by import.

* **truncation invariance** `tailResidue_truncateRaw`: dropped entries have *zero weights*.
* **the master bridge** `tailResidue_eq_sum_resAt`: the residue functional as a base-point sum
  of `resAt`-pairings of the tail polynomial against `pairCoeffFun`.
* **μ-compatibility** `tailResidue_tailMul`: `Res_{h·dg₀}(μ_ψ Z) = Res_{(ψh)·dg₀}(Z)`.
* **Miranda Lemma 3.6** `pairOrderBounded_of_vanishing`: the order downgrade.
* **the recovery step** `pairDualMap_recovery` and **surjectivity** `pairDualMap_surjective`
  (pigeonhole on `H¹(D − nP)*` with the RR-I counts), giving the dimension identity

    `h1TailDim_eq_lDim_pairCanonical_sub : h¹(D) = l(K − D)`, `K = div (dg₀)`

  for any nonconstant meromorphic `g₀` — no genus hypothesis anywhere.
-/
import Jacobians.TailDuality.PairDualityInjective
import Jacobians.TailDuality.TailDualitySurjectiveAssembly

open scoped Manifold ContDiff Topology
open Filter Set Module
open Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace

namespace Jacobians.LaurentTail

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### §1 Truncation invariance of the residue functional -/

/-! ### §2 The master bridge and μ-compatibility of the residue functional -/

open Classical in
/-- **The master bridge**: on tails of level `B` paired against a form of order ≥ `B`, the
residue functional is the sum over base points of the `resAt`-pairings of the tail polynomial
against the form's local coefficient (`resAt_mul_eq_sum_tailPairing`, read in reverse, with the
tail polynomial as the meromorphic factor — its coefficients *are* the entries). -/
theorem tailResidue_eq_sum_resAt {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g₀ g : MeromorphicFunction X) {B : Divisor X}
    (hord : PairOrderBounded g₀ g B)
    {Z : TailSpace X} (hZ : Z ∈ tailSubspace (X := X) B) (P : Finset X)
    (hP : Z.support.image Prod.fst ⊆ P) :
    tailResidue g₀ g Z = ∑ p ∈ P,
      resAt (fun z => tailFnAt Z p z * pairCoeffFun g₀ g p z) ((chartAt (H := ℂ) p) p) := by
  rw [tailResidue_apply]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Z.support) (t := P) (g := Prod.fst)
    (fun q hq => hP (Finset.mem_image_of_mem _ hq))
    (fun q => Z q * tailResidueWeight g₀ g q)]
  refine Finset.sum_congr rfl fun p _ => ?_
  set Wp : Finset ℤ := (Z.support.filter (fun q : X × ℤ => q.1 = p)).image Prod.snd with hWp
  have hWlt : ∀ n ∈ Wp, n < -(B p) := by
    intro n hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hsupp, hfst⟩ := Finset.mem_filter.mp hq
    by_contra hge
    apply Finsupp.mem_support_iff.mp hsupp
    have := mem_tailSubspace_iff.mp hZ (p, q.2) hge
    rw [show q = (p, q.2) from Prod.ext hfst rfl]
    exact this
  have hWcap : ∀ n : ℤ, n < -(B p)
      → laurentCoeff (tailFnAt Z p) ((chartAt (H := ℂ) p) p) n ≠ 0 → n ∈ Wp := by
    intro n hn hne
    rw [laurentCoeff_tailFnAt] at hne
    exact Finset.mem_image.mpr ⟨(p, n),
      Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, rfl⟩, rfl⟩
  have hpair := resAt_mul_eq_sum_tailPairing (meromorphicAt_tailFnAt Z p)
    (meromorphicAt_pairCoeffFun g₀ g p) (hord p) Wp hWlt hWcap
  rw [hpair]
  rw [Finset.sum_image (fun (q : X × ℤ) hq (q' : X × ℤ) hq' hqq' => by
    have h1 := (Finset.mem_filter.mp hq).2
    have h2 := (Finset.mem_filter.mp hq').2
    exact Prod.ext (h1.trans h2.symm) hqq')]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hfst := (Finset.mem_filter.mp hq).2
  rw [laurentCoeff_tailFnAt]
  rw [show ((p, q.2) : X × ℤ) = q from Prod.ext hfst.symm rfl]
  rw [show tailResidueWeight g₀ g q = laurentCoeff (pairCoeffFun g₀ g q.1)
    ((chartAt (H := ℂ) q.1) q.1) (-1 - q.2) from rfl, hfst]

/-- The form-order bound multiplies: `ord((ψ·h)·dg₀) ≥ A` when `ord(h·dg₀) ≥ E` and
`A − E ≤ ord ψ`. -/
theorem pairOrderBounded_mul {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g₀ h ψ : MeromorphicFunction X) {A E : Divisor X}
    (hord : PairOrderBounded g₀ h E) (hlev : MulLevelLE ψ A E) :
    PairOrderBounded g₀ (ψ * h) A := by
  intro p
  set c : ℂ := (chartAt (H := ℂ) p) p with hc
  set Ψ : ℂ → ℂ := fun z => ψ.toFun ((chartAt (H := ℂ) p).symm z) with hΨ
  have hΨm : MeromorphicAt Ψ c := ψ.meromorphic p
  have hWm : MeromorphicAt (pairCoeffFun g₀ h p) c := meromorphicAt_pairCoeffFun g₀ h p
  have hgerm : pairCoeffFun g₀ (ψ * h) p =ᶠ[𝓝[≠] c] Ψ * pairCoeffFun g₀ h p := by
    refine Eventually.of_forall fun z => ?_
    show (ψ * h).toFun ((chartAt (H := ℂ) p).symm z)
        * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) p).symm w)) z
      = Ψ z * (h.toFun ((chartAt (H := ℂ) p).symm z)
        * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) p).symm w)) z)
    rw [MeromorphicFunction.mul_toFun, Pi.mul_apply]
    ring
  rw [meromorphicOrderAt_congr hgerm, meromorphicOrderAt_mul hΨm hWm]
  have h1 := hlev p
  have h2 := hord p
  have horder : meromorphicOrderAt Ψ c = ψ.orderW p := rfl
  rw [horder]
  rcases eq_or_ne (ψ.orderW p) ⊤ with htop | hne
  · rw [htop, WithTop.top_add]
    exact le_top
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  rcases eq_or_ne (meromorphicOrderAt (pairCoeffFun g₀ h p) c) ⊤ with htop2 | hne2
  · rw [htop2, WithTop.add_top]
    exact le_top
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne2
  rw [← hm, ← hk, ← WithTop.coe_add]
  rw [← hm] at h1
  rw [← hk] at h2
  have h1' : A p - E p ≤ m := by exact_mod_cast h1
  have h2' : E p ≤ k := by exact_mod_cast h2
  exact_mod_cast (by omega : (A p : ℤ) ≤ m + k)

/-- **μ-compatibility: the residue functional intertwines the multiplication action.**
`Res_{h·dg₀}(μ_ψ Z) = Res_{(ψ·h)·dg₀}(Z)` for `Z` of level `A`, the form of order ≥ `E`, and
`A − E ≤ ord ψ`: per point, the defect `tailFn(μ_ψ Z) − ψ·tailFn(Z)` has order ≥ `−E` and
pairs against order ≥ `E` to residue `0`. -/
theorem tailResidue_tailMul {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g₀ h ψ : MeromorphicFunction X) {A E : Divisor X}
    (hord : PairOrderBounded g₀ h E) (hlev : MulLevelLE ψ A E) {Z : TailSpace X}
    (hZ : Z ∈ tailSubspace (X := X) A) :
    tailResidue g₀ h (tailMul ψ E Z) = tailResidue g₀ (ψ * h) Z := by
  classical
  set P : Finset X := Z.support.image Prod.fst with hP
  -- the base points of `μ_ψ Z` sit among those of `Z`
  have hpts : (tailMul ψ E Z).support.image Prod.fst ⊆ P := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    by_contra hpn
    apply Finsupp.mem_support_iff.mp hq
    rw [tailMul_apply]
    split_ifs with hlt
    · have h0 : (fun z => ψ.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z)
          =ᶠ[𝓝[≠] ((chartAt (H := ℂ) q.1) q.1)] fun _ => (0 : ℂ) := by
        refine Eventually.of_forall fun z => ?_
        show ψ.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z = 0
        rw [tailFnAt_eq_zero_of_notMem Z q.1 hpn z, mul_zero]
      rw [laurentCoeff_congr h0, laurentCoeff_def]
      have hz : (fun z => (fun _ : ℂ => (0 : ℂ)) z
          * (z - (chartAt (H := ℂ) q.1) q.1) ^ (-q.2 - 1)) = fun _ : ℂ => (0 : ℂ) := by
        funext z; ring
      rw [hz]
      exact Jacobians.Dolbeault.resAt_eq_zero_of_analyticAt analyticAt_const
    · rfl
  have hmem : tailMul ψ E Z ∈ tailSubspace (X := X) E := tailMulRaw_mem ψ E Z
  rw [tailResidue_eq_sum_resAt g₀ h hord hmem P hpts,
    tailResidue_eq_sum_resAt g₀ (ψ * h) (pairOrderBounded_mul g₀ h ψ hord hlev) hZ P
      (le_refl P)]
  refine Finset.sum_congr rfl fun p _ => ?_
  set c : ℂ := (chartAt (H := ℂ) p) p with hc
  set Ψ : ℂ → ℂ := fun z => ψ.toFun ((chartAt (H := ℂ) p).symm z) with hΨ
  set T : ℂ → ℂ := tailFnAt Z p with hT
  set S : ℂ → ℂ := tailFnAt (tailMul ψ E Z) p with hS
  set W : ℂ → ℂ := pairCoeffFun g₀ h p with hW
  have hΨm : MeromorphicAt Ψ c := ψ.meromorphic p
  have hTm : MeromorphicAt T c := meromorphicAt_tailFnAt Z p
  have hSm : MeromorphicAt S c := meromorphicAt_tailFnAt _ p
  have hWm : MeromorphicAt W c := meromorphicAt_pairCoeffFun g₀ h p
  -- the defect has order ≥ −E p
  have hSdiff : ((-(E p) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (S - Ψ * T) c := by
    rw [le_order_iff_laurentCoeff_eq_zero ((hSm.sub (hΨm.mul hTm)))]
    intro j hj
    have hsub : laurentCoeff (S - Ψ * T) c j
        = laurentCoeff S c j - laurentCoeff (Ψ * T) c j := by
      have hneg : laurentCoeff (-(Ψ * T)) c j = -laurentCoeff (Ψ * T) c j := by
        have hsm : (-(Ψ * T)) = (-1 : ℂ) • (Ψ * T) := by funext z; simp
        rw [hsm, laurentCoeff_smul (-1 : ℂ) (hΨm.mul hTm)]
        ring
      have hfun : (S - Ψ * T) = S + -(Ψ * T) := by
        funext z
        simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
        ring
      rw [hfun, laurentCoeff_add hSm (hΨm.mul hTm).neg, hneg]
      ring
    rw [hsub, hS, laurentCoeff_tailFnAt, tailMul_apply, if_pos hj]
    have hrfl : laurentCoeff (Ψ * T) c j
        = laurentCoeff (fun z => ψ.toFun ((chartAt (H := ℂ) p).symm z)
            * tailFnAt Z p z) c j := rfl
    rw [hrfl]
    exact sub_self _
  -- so the two pairings agree
  have hzero : resAt ((S - Ψ * T) * W) c = 0 := by
    refine resAt_eq_zero_of_nonneg_order ((hSm.sub (hΨm.mul hTm)).mul hWm) ?_
    rw [meromorphicOrderAt_mul (hSm.sub (hΨm.mul hTm)) hWm]
    calc ((0 : ℤ) : WithTop ℤ)
        = ((-(E p) : ℤ) : WithTop ℤ) + ((E p : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add]; norm_num
      _ ≤ _ := add_le_add hSdiff (hord p)
  have hsplit : resAt (fun z => S z * W z) c = resAt (fun z => Ψ z * T z * W z) c := by
    have hfun : (fun z => S z * W z)
        = (fun z => Ψ z * T z * W z) + ((S - Ψ * T) * W) := by
      funext z
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
      ring
    have hp1 : HoloPunctured (fun z => Ψ z * T z * W z) c :=
      ((hΨm.mul hTm).mul hWm).holoPunctured
    have hp2 : HoloPunctured ((S - Ψ * T) * W) c :=
      ((hSm.sub (hΨm.mul hTm)).mul hWm).holoPunctured
    rw [hfun, resAt_add hp1 hp2, hzero, add_zero]
  rw [show resAt (fun z => tailFnAt (tailMul ψ E Z) p z * pairCoeffFun g₀ h p z) c
      = resAt (fun z => S z * W z) c from rfl, hsplit]
  refine resAt_congr (Eventually.of_forall fun z => ?_)
  show Ψ z * T z * W z = tailFnAt Z p z * pairCoeffFun g₀ (ψ * h) p z
  show Ψ z * T z * W z = T z * ((ψ * h).toFun ((chartAt (H := ℂ) p).symm z)
    * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) p).symm w)) z)
  rw [MeromorphicFunction.mul_toFun, Pi.mul_apply]
  show Ψ z * T z * (h.toFun ((chartAt (H := ℂ) p).symm z)
      * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) p).symm w)) z)
    = T z * (ψ.toFun ((chartAt (H := ℂ) p).symm z) * h.toFun ((chartAt (H := ℂ) p).symm z)
      * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) p).symm w)) z)
  ring

/-! ### §3 Miranda Lemma 3.6: the order downgrade -/

/-- **Miranda Lemma 3.6.**  If the residue functional of `h·dg₀` (honestly defined at a fine
level `D'`) vanishes on every `D'`-tail killed by the `D`-truncation, then `h·dg₀` satisfies the
coarser bound `D` — else the single-monomial witness `z^{−1−o}·p` at a violating point is killed
by the truncation yet pairs to the nonzero leading coefficient. -/
theorem pairOrderBounded_of_vanishing {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g₀ h : MeromorphicFunction X) {D' D : Divisor X}
    (hord : PairOrderBounded g₀ h D')
    (hvan : ∀ Z : TailSpace X, Z ∈ tailSubspace (X := X) D' →
      truncateRaw (X := X) D Z = 0 → tailResidue g₀ h Z = 0) :
    PairOrderBounded g₀ h D := by
  intro p
  by_contra hcon
  rw [not_le] at hcon
  have hne : meromorphicOrderAt (pairCoeffFun g₀ h p) ((chartAt (H := ℂ) p) p) ≠ ⊤ :=
    ne_top_of_lt hcon
  obtain ⟨o, ho⟩ := WithTop.ne_top_iff_exists.mp hne
  have hoD : o < D p := by
    rw [← ho] at hcon
    exact_mod_cast hcon
  have hoD' : D' p ≤ o := by
    have := hord p
    rw [← ho] at this
    exact_mod_cast this
  -- the witness tail
  have hmem : Finsupp.single ((p, -1 - o) : X × ℤ) (1 : ℂ) ∈ tailSubspace (X := X) D' := by
    rw [mem_tailSubspace_iff]
    intro q hq
    rcases eq_or_ne q (p, -1 - o) with rfl | hne'
    · exact absurd (by omega : (-1 - o : ℤ) < -(D' p)) (by simpa using hq)
    · exact Finsupp.single_eq_of_ne hne'
  have hkill : truncateRaw (X := X) D (Finsupp.single ((p, -1 - o) : X × ℤ) (1 : ℂ)) = 0 := by
    ext q
    rw [truncateRaw_apply, Finsupp.coe_zero, Pi.zero_apply]
    split_ifs with hq
    · rcases eq_or_ne q (p, -1 - o) with rfl | hne'
      · exact absurd hq (by simp only [not_lt]; omega)
      · exact Finsupp.single_eq_of_ne hne'
    · rfl
  have hval : tailResidue g₀ h (Finsupp.single ((p, -1 - o) : X × ℤ) (1 : ℂ))
      = laurentCoeff (pairCoeffFun g₀ h p) ((chartAt (H := ℂ) p) p) o := by
    rw [tailResidue_apply, Finsupp.support_single _ one_ne_zero,
      Finset.sum_singleton, Finsupp.single_eq_same, one_mul, tailResidueWeight]
    congr 1
    omega
  have hne0 : laurentCoeff (pairCoeffFun g₀ h p) ((chartAt (H := ℂ) p) p) o ≠ 0 :=
    laurentCoeff_order_ne_zero (meromorphicAt_pairCoeffFun g₀ h p) ho.symm
  exact hne0 (hval ▸ hvan _ hmem hkill)

/-! ### §4 The recovery step (Miranda pp. 190–191) -/

/-- `dim I = l(K − D)`: the range of the (injective) residue pairing has the dimension of its
source `L(K − D)/germ0`. -/
theorem finrank_range_pairDualMap (g₀ : MeromorphicFunction X) (hg₀ : ¬ IsGermConstant g₀)
    (D : Divisor X) :
    finrank ℂ ↥(LinearMap.range (pairDualMap g₀ hg₀ D))
      = lDim (X := X) (pairCanonicalDivisor g₀ hg₀ - D) :=
  LinearMap.finrank_range_of_inj (pairDualMap_injective g₀ hg₀ D)

/-- **The recovery step** (Miranda Thm 3.3, surjectivity, second half): if `φ ∘ T̄_ψ` is the
residue functional of `h·dg₀` at the finer level `D − C` (with `ψ ∈ L(C)` of surviving germ),
then `φ` itself is the residue functional of `(ψ⁻¹h)·dg₀` at level `D`:

* the composite identity turns `T̄_ψ ∘ μ_{ψ⁻¹}` into the truncation `𝒯[D−C−div ψ] → 𝒯[D]`,
* μ-compatibility (`tailResidue_tailMul`) turns `Res_{h·dg₀} ∘ μ_{ψ⁻¹}` into
  `Res_{(ψ⁻¹h)·dg₀}`,
* Miranda Lemma 3.6 downgrades the order bound of `(ψ⁻¹h)·dg₀` from the fine level to `D`. -/
theorem pairDualMap_recovery (g₀ : MeromorphicFunction X) (hg₀ : ¬ IsGermConstant g₀)
    {D C : Divisor X}
    (φ : Module.Dual ℂ (mittagLefflerH1 (X := X) D))
    (ψ : ↥(linearSystem (X := X) C))
    (hψ : ∃ p : X, (ψ : MeromorphicFunction X).orderW p ≠ ⊤)
    (h : ↥(linearSystem (X := X) (pairCanonicalDivisor g₀ hg₀ - (D - C))))
    (heq : φ.comp (tailMulH1 (ψ : MeromorphicFunction X) (mulLevelLE_of_mem ψ.2 D))
      = pairDualFun g₀ hg₀ (D - C) h) :
    ∃ g : ↥(linearSystem (X := X) (pairCanonicalDivisor g₀ hg₀ - D)),
      pairDualMap g₀ hg₀ D (Submodule.Quotient.mk g) = φ := by
  classical
  have hψfin : ∀ p : X, (ψ : MeromorphicFunction X).orderW p ≠ ⊤ :=
    MeromorphicFunction.orderW_ne_top_of_exists _ hψ
  -- the level condition for `μ_{ψ⁻¹} : 𝒯[D − C − div ψ] → 𝒯[D − C]` (an exact shift)
  have hlev' : MulLevelLE ((ψ : MeromorphicFunction X)⁻¹)
      (D - C - ((ψ : MeromorphicFunction X).div : Divisor X)) (D - C) := by
    intro p
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (hψfin p)
    have hdiv : (((ψ : MeromorphicFunction X).div : Divisor X)) p = m := by
      rw [div_apply, ← hm, WithTop.untop₀_coe]
    have hpt : (D - C - ((ψ : MeromorphicFunction X).div : Divisor X)) p - (D - C) p = -m := by
      rw [Finsupp.sub_apply, hdiv]
      ring
    have hinv : ((ψ : MeromorphicFunction X)⁻¹).orderW p = ((-m : ℤ) : WithTop ℤ) := by
      rw [MeromorphicFunction.orderW_inv, ← hm]
      rfl
    rw [hpt, hinv]
  have hordh : PairOrderBounded g₀ (h : MeromorphicFunction X) (D - C) :=
    (pairOrderBounded_iff_mem g₀ hg₀ _ (D - C)).mpr h.2
  have hordg : PairOrderBounded g₀
      ((ψ : MeromorphicFunction X)⁻¹ * (h : MeromorphicFunction X))
      (D - C - ((ψ : MeromorphicFunction X).div : Divisor X)) :=
    pairOrderBounded_mul g₀ (h : MeromorphicFunction X) ((ψ : MeromorphicFunction X)⁻¹)
      hordh hlev'
  -- the fine level sits below `D`: `div ψ ≥ −C` pointwise
  have hD'le : (D - C - ((ψ : MeromorphicFunction X).div : Divisor X)) ≤ D := by
    intro p
    have hψm : ((-(C p) : ℤ) : WithTop ℤ) ≤ (ψ : MeromorphicFunction X).orderW p := ψ.2 p
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (hψfin p)
    have hdiv : (((ψ : MeromorphicFunction X).div : Divisor X)) p = m := by
      rw [div_apply, ← hm, WithTop.untop₀_coe]
    rw [← hm] at hψm
    have hCm : -(C p) ≤ m := by exact_mod_cast hψm
    have hpt : (D - C - ((ψ : MeromorphicFunction X).div : Divisor X)) p
        = D p - C p - m := by
      rw [Finsupp.sub_apply, Finsupp.sub_apply, hdiv]
    rw [hpt]
    omega
  -- the bridge: `φ` reads through the truncation as the `(ψ⁻¹h)`-residue on the fine tails
  have hkey : ∀ V : TailSpace X,
      V ∈ tailSubspace (X := X) (D - C - ((ψ : MeromorphicFunction X).div : Divisor X)) →
      φ (Submodule.Quotient.mk
        ⟨truncateRaw (X := X) D V, truncateRaw_mem_tailSubspace D V⟩)
        = tailResidue g₀
            ((ψ : MeromorphicFunction X)⁻¹ * (h : MeromorphicFunction X)) V := by
    intro V hV
    have hZmem : tailMul ((ψ : MeromorphicFunction X)⁻¹) (D - C) V
        ∈ tailSubspace (X := X) (D - C) := tailMulRaw_mem _ _ _
    have h1 := LinearMap.congr_fun heq
      (Submodule.Quotient.mk (⟨tailMul ((ψ : MeromorphicFunction X)⁻¹) (D - C) V, hZmem⟩ :
        ↥(tailSubspace (X := X) (D - C))))
    rw [LinearMap.comp_apply, tailMulH1_mk, pairDualFun_mk] at h1
    -- left side: the composite `μ_ψ ∘ μ_{ψ⁻¹}` is the truncation
    have hcls : tailMulCo (ψ : MeromorphicFunction X) (D - C) D
        ⟨tailMul ((ψ : MeromorphicFunction X)⁻¹) (D - C) V, hZmem⟩
        = ⟨truncateRaw (X := X) D V, truncateRaw_mem_tailSubspace D V⟩ := by
      refine Subtype.ext ?_
      rw [tailMulCo_coe]
      exact tailMul_tailMul_inv_trunc (ψ : MeromorphicFunction X) hψ
        (mulLevelLE_of_mem ψ.2 D) V
    rw [hcls] at h1
    -- right side: μ-compatibility turns the `μ_{ψ⁻¹}`-image residue into the `ψ⁻¹h`-residue
    rw [show ((⟨tailMul ((ψ : MeromorphicFunction X)⁻¹) (D - C) V, hZmem⟩ :
        ↥(tailSubspace (X := X) (D - C))) : TailSpace X)
        = tailMul ((ψ : MeromorphicFunction X)⁻¹) (D - C) V from rfl,
      tailResidue_tailMul g₀ (h : MeromorphicFunction X)
        ((ψ : MeromorphicFunction X)⁻¹) hordh hlev' hV] at h1
    exact h1
  -- Miranda Lemma 3.6: the order bound downgrades to `D`
  have hordgD : PairOrderBounded g₀
      ((ψ : MeromorphicFunction X)⁻¹ * (h : MeromorphicFunction X)) D := by
    refine pairOrderBounded_of_vanishing g₀ _ hordg fun Z hZ h0 => ?_
    have hk := hkey Z hZ
    rw [← hk]
    have hzero : (⟨truncateRaw (X := X) D Z, truncateRaw_mem_tailSubspace D Z⟩ :
        ↥(tailSubspace (X := X) D)) = 0 := Subtype.ext h0
    rw [hzero, Submodule.Quotient.mk_zero, map_zero]
  have hgmem : (ψ : MeromorphicFunction X)⁻¹ * (h : MeromorphicFunction X)
      ∈ linearSystem (X := X) (pairCanonicalDivisor g₀ hg₀ - D) :=
    (pairOrderBounded_iff_mem g₀ hg₀ _ D).mp hordgD
  -- conclusion: `φ = Res_{(ψ⁻¹h)·dg₀}` on every class
  refine ⟨⟨_, hgmem⟩, ?_⟩
  refine LinearMap.ext fun ξ => ?_
  obtain ⟨W, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  show pairDualFun g₀ hg₀ D ⟨_, hgmem⟩ (Submodule.Quotient.mk W)
    = φ (Submodule.Quotient.mk W)
  rw [pairDualFun_mk]
  have hWD' : (W : TailSpace X)
      ∈ tailSubspace (X := X) (D - C - ((ψ : MeromorphicFunction X).div : Divisor X)) :=
    tailSubspace_anti hD'le W.2
  have h2 := hkey (W : TailSpace X) hWD'
  have hWtr : (⟨truncateRaw (X := X) D (W : TailSpace X),
      truncateRaw_mem_tailSubspace D (W : TailSpace X)⟩ : ↥(tailSubspace (X := X) D)) = W :=
    Subtype.ext (truncateRaw_eq_self_of_mem W.2)
  rw [hWtr] at h2
  exact h2.symm

/-! ### §5 Surjectivity (Miranda Thm 3.3 / Forster 17.9) -/

/-- **Serre duality for the tail `H¹`, the surjective half** (Miranda Thm 3.3, pp. 189–191;
Forster 17.9): every functional on the Mittag-Leffler `H¹(D)` is a residue functional
`Res_{h·dg₀}` with `h ∈ L(K − D)`.  Pigeonhole on `H¹(D − nP)*` between the multiplication
functionals `φ ∘ T̄_ψ` (`ψ ∈ L(nP)`) and the residue functionals, with the RR-I counts; then
the recovery step pulls the matched functional back to level `D`.  Every genus. -/
theorem pairDualMap_surjective (g₀ : MeromorphicFunction X) (hg₀ : ¬ IsGermConstant g₀)
    (D : Divisor X) :
    Function.Surjective (pairDualMap g₀ hg₀ D) := by
  classical
  intro φ
  rcases eq_or_ne φ 0 with rfl | hφ
  · exact ⟨0, map_zero _⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty X)
  -- the pole budget `n`: large enough for both RR-I counts
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, Divisor.deg X D < (n : ℤ)
      ∧ 3 * (h1TailDim (X := X) 0 : ℤ) - 3
          - Divisor.deg X (pairCanonicalDivisor g₀ hg₀) < (n : ℤ) := by
    refine ⟨(max (Divisor.deg X D) (3 * (h1TailDim (X := X) 0 : ℤ) - 3
      - Divisor.deg X (pairCanonicalDivisor g₀ hg₀))).toNat + 1, ?_, ?_⟩
    · have h1 := Int.self_le_toNat (max (Divisor.deg X D)
        (3 * (h1TailDim (X := X) 0 : ℤ) - 3 - Divisor.deg X (pairCanonicalDivisor g₀ hg₀)))
      have h2 : Divisor.deg X D ≤ max (Divisor.deg X D)
          (3 * (h1TailDim (X := X) 0 : ℤ) - 3
            - Divisor.deg X (pairCanonicalDivisor g₀ hg₀)) := le_max_left _ _
      push_cast
      omega
    · have h1 := Int.self_le_toNat (max (Divisor.deg X D)
        (3 * (h1TailDim (X := X) 0 : ℤ) - 3 - Divisor.deg X (pairCanonicalDivisor g₀ hg₀)))
      have h2 : 3 * (h1TailDim (X := X) 0 : ℤ) - 3
          - Divisor.deg X (pairCanonicalDivisor g₀ hg₀)
          ≤ max (Divisor.deg X D) (3 * (h1TailDim (X := X) 0 : ℤ) - 3
            - Divisor.deg X (pairCanonicalDivisor g₀ hg₀)) := le_max_right _ _
      push_cast
      omega
  -- dimension bookkeeping for the two subspaces of `H¹(D − nP)*`
  have hΛ := finrank_range_tailMulDualQ φ (Finsupp.single P (n : ℤ)) hφ
  have hI := finrank_range_pairDualMap g₀ hg₀ (D - Finsupp.single P (n : ℤ))
  have hdegC : Divisor.deg X (Finsupp.single P (n : ℤ)) = n := by
    rw [Divisor.deg_single]
  have hdegDn : Divisor.deg X (D - Finsupp.single P (n : ℤ)) = Divisor.deg X D - n := by
    rw [Divisor.deg_sub, hdegC]
  have hdegKDn : Divisor.deg X (pairCanonicalDivisor g₀ hg₀ - (D - Finsupp.single P (n : ℤ)))
      = Divisor.deg X (pairCanonicalDivisor g₀ hg₀) - Divisor.deg X D + n := by
    rw [Divisor.deg_sub, hdegDn]
    ring
  -- RR-I three times: the `Λ`-count, the `I`-count, and the ambient count
  have hRRC := riemannRoch_tailForm (X := X) (Finsupp.single P (n : ℤ))
  have hRRK := riemannRoch_tailForm (X := X)
    (pairCanonicalDivisor g₀ hg₀ - (D - Finsupp.single P (n : ℤ)))
  have hRRDn := riemannRoch_tailForm (X := X) (D - Finsupp.single P (n : ℤ))
  have hlDn : lDim (X := X) (D - Finsupp.single P (n : ℤ)) = 0 :=
    lDim_eq_zero_of_deg_neg _ (by omega)
  -- the pigeonhole: the two subspaces meet in a nonzero functional
  have hgt : finrank ℂ ↥(LinearMap.range (tailMulDualQ φ (Finsupp.single P (n : ℤ))))
      + finrank ℂ ↥(LinearMap.range (pairDualMap g₀ hg₀ (D - Finsupp.single P (n : ℤ))))
      > finrank ℂ (Module.Dual ℂ (mittagLefflerH1 (X := X)
          (D - Finsupp.single P (n : ℤ)))) := by
    rw [hΛ, hI, Subspace.dual_finrank_eq]
    have e1 : (0 : ℤ) ≤ (h1TailDim (X := X) (Finsupp.single P (n : ℤ)) : ℤ) :=
      Int.natCast_nonneg _
    have e2 : (0 : ℤ) ≤ (h1TailDim (X := X)
        (pairCanonicalDivisor g₀ hg₀ - (D - Finsupp.single P (n : ℤ))) : ℤ) :=
      Int.natCast_nonneg _
    have hcount : (h1TailDim (X := X) (D - Finsupp.single P (n : ℤ)) : ℤ)
        < (lDim (X := X) (Finsupp.single P (n : ℤ)) : ℤ)
          + (lDim (X := X)
              (pairCanonicalDivisor g₀ hg₀ - (D - Finsupp.single P (n : ℤ))) : ℤ) := by
      omega
    exact_mod_cast hcount
  have hne := SerreDuality.subspaces_inf_ne_bot_of_finrank_add_gt _ _ hgt
  obtain ⟨χ, hχmem, hχne⟩ := (Submodule.ne_bot_iff _).mp hne
  obtain ⟨hχΛ, hχI⟩ := Submodule.mem_inf.mp hχmem
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hχΛ
  obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨d, hd⟩ := LinearMap.mem_range.mp hχI
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ d
  -- the germ of `ψ` survives (else the matched functional were `0`)
  have hψex : ∃ p : X, (ψ : MeromorphicFunction X).orderW p ≠ ⊤ := by
    by_contra hall
    push Not at hall
    apply hχne
    rw [← hc, tailMulDualQ_mk]
    exact tailMulDual_eq_zero_of_germZero φ _ ψ hall
  -- the matched functional equation, and the recovery
  have heq : φ.comp (tailMulH1 (ψ : MeromorphicFunction X) (mulLevelLE_of_mem ψ.2 D))
      = pairDualFun g₀ hg₀ (D - Finsupp.single P (n : ℤ)) h := by
    have h1 : tailMulDualQ φ (Finsupp.single P (n : ℤ)) (Submodule.Quotient.mk ψ)
        = pairDualMap g₀ hg₀ (D - Finsupp.single P (n : ℤ)) (Submodule.Quotient.mk h) := by
      rw [hc, hd]
    rw [tailMulDualQ_mk, tailMulDual_apply] at h1
    exact h1
  obtain ⟨g, hg⟩ := pairDualMap_recovery g₀ hg₀ φ ψ hψex h heq
  exact ⟨Submodule.Quotient.mk g, hg⟩

/-! ### §6 The dimension identity `h¹(D) = l(K − D)` -/

/-- **Serre duality for the tail `H¹` as a dimension identity** (Miranda Thm 3.3):
`h¹(D) = l(K − D)` for the canonical divisor `K = div (dg₀)` of any nonconstant meromorphic
`g₀` — no genus hypothesis. -/
theorem h1TailDim_eq_lDim_pairCanonical_sub (g₀ : MeromorphicFunction X)
    (hg₀ : ¬ IsGermConstant g₀) (D : Divisor X) :
    h1TailDim (X := X) D = lDim (X := X) (pairCanonicalDivisor g₀ hg₀ - D) := by
  have e := LinearEquiv.ofBijective (pairDualMap g₀ hg₀ D)
    ⟨pairDualMap_injective g₀ hg₀ D, pairDualMap_surjective g₀ hg₀ D⟩
  have h := e.finrank_eq
  rw [Subspace.dual_finrank_eq] at h
  exact h.symm

end Jacobians.LaurentTail
