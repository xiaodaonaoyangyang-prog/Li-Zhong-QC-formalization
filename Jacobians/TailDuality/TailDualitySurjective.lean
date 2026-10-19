/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Serre duality for the tail `H¹`, the surjective half (Miranda Thm 3.3, pp. 189–191)

The pigeonhole half (Forster 17.9's shape, on the abstract core
`SerreDuality.serre_surjectivity_dim_core`): every functional `φ : H¹(D) → ℂ` is a residue
functional `Res_{h'·ω₀}`.  This file builds the compatibility toolkit and the order-downgrade:

* **truncation invariance** `omegaTailResidue_truncateRaw`: dropped entries have *zero
  weights* (their pairing degree exceeds the form's order — pure anchor (a)).
* **the generalized composite** `tailMul_tailMul_inv_trunc`:
  `μ_ψ(μ_{ψ⁻¹}(Z)) = truncate_B(Z)` under the level condition — subsumes the exact-shift
  identity and gives `T̄_ψ ∘ μ̄_{ψ⁻¹} = truncation` on `H¹`.
* **μ-compatibility** `omegaTailResidue_tailMul`: `Res_{h}(μ_ψ Z) = Res_{ψ·h}(Z)` under
  order conditions — the per-point difference pairs with nonnegative total order.
* **Miranda Lemma 3.6** `omegaOrderBounded_of_vanishing`: a residue functional vanishing on
  `ker(truncation)` has the coarser order bound — the single-monomial witness contrapositive.
-/
import Jacobians.TailDuality.TailDualityInjective
import Jacobians.TailDuality.TailMultiplicationH1

open scoped Manifold ContDiff Topology
open Filter Set
open Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace

namespace Jacobians.LaurentTail

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### §1 Truncation invariance of the residue functional -/

/-! ### §2 The generalized composite: `μ_ψ ∘ μ_{ψ⁻¹} = truncation` -/

/-- **The generalized composite identity**: for `ψ` with surviving germ and the level condition
`A − B ≤ ord ψ`, the round trip `μ_ψ(μ_{ψ⁻¹}(Z))` at levels `𝒯 → 𝒯[A] → 𝒯[B]` is the plain
truncation of `Z` at `B`.  (The exact-shift identity `tailMul_tailMul_inv` is the case
`A = B + div ψ`,
`Z ∈ 𝒯[B]`.) -/
theorem tailMul_tailMul_inv_trunc (ψ : MeromorphicFunction X) (hψ : ∃ x, ψ.orderW x ≠ ⊤)
    {A B : Divisor X} (h : MulLevelLE ψ A B) (Z : TailSpace X) :
    tailMul ψ B (tailMul ψ⁻¹ A Z) = truncateRaw (X := X) B Z := by
  classical
  ext q
  obtain ⟨p, n⟩ := q
  rw [tailMul_apply, truncateRaw_apply]
  by_cases hlt : n < -(B p)
  swap
  · rw [if_neg hlt, if_neg hlt]
  rw [if_pos hlt, if_pos hlt]
  set c : ℂ := (chartAt (H := ℂ) p) p with hc
  set Ψ : ℂ → ℂ := fun z => ψ.toFun ((chartAt (H := ℂ) p).symm z) with hΨ
  set Ψi : ℂ → ℂ := fun z => (ψ⁻¹).toFun ((chartAt (H := ℂ) p).symm z) with hΨi
  set T : ℂ → ℂ := tailFnAt Z p with hT
  set S : ℂ → ℂ := tailFnAt (tailMul ψ⁻¹ A Z) p with hS
  have hΨm : MeromorphicAt Ψ c := ψ.meromorphic p
  have hΨim : MeromorphicAt Ψi c := (ψ⁻¹).meromorphic p
  have hTm : MeromorphicAt T c := meromorphicAt_tailFnAt Z p
  have hSm : MeromorphicAt S c := meromorphicAt_tailFnAt _ p
  have hordψ : ψ.orderW p ≠ ⊤ := MeromorphicFunction.orderW_ne_top_of_exists ψ hψ p
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hordψ
  have hSdiff : ((-(A p) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (S - Ψi * T) c := by
    rw [le_order_iff_laurentCoeff_eq_zero ((hSm.sub (hΨim.mul hTm)))]
    intro j hj
    have hsub : laurentCoeff (S - Ψi * T) c j
        = laurentCoeff S c j - laurentCoeff (Ψi * T) c j := by
      have hneg : laurentCoeff (-(Ψi * T)) c j = -laurentCoeff (Ψi * T) c j := by
        have hsm : (-(Ψi * T)) = (-1 : ℂ) • (Ψi * T) := by funext z; simp
        rw [hsm, laurentCoeff_smul (-1 : ℂ) (hΨim.mul hTm)]
        ring
      have hfun : (S - Ψi * T) = S + -(Ψi * T) := by
        funext z
        simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
        ring
      rw [hfun, laurentCoeff_add hSm (hΨim.mul hTm).neg, hneg]
      ring
    rw [hsub, hS, laurentCoeff_tailFnAt, tailMul_apply, if_pos hj]
    have hrfl : laurentCoeff (Ψi * T) c j
        = laurentCoeff (fun z => (ψ⁻¹).toFun ((chartAt (H := ℂ) p).symm z)
            * tailFnAt Z p z) c j := rfl
    rw [hrfl]
    exact sub_self _
  have hkey : laurentCoeff (Ψ * S) c n = laurentCoeff (Ψ * (Ψi * T)) c n := by
    have hzero : laurentCoeff (Ψ * (S - Ψi * T)) c n = 0 := by
      refine laurentCoeff_eq_zero_of_lt_order (hΨm.mul (hSm.sub (hΨim.mul hTm))) ?_
      rw [meromorphicOrderAt_mul hΨm (hSm.sub (hΨim.mul hTm))]
      have hψA : ((A p - B p : ℤ) : WithTop ℤ) ≤ ψ.orderW p := h p
      have horder : meromorphicOrderAt Ψ c = ψ.orderW p := rfl
      calc ((n : ℤ) : WithTop ℤ) < ((-(B p) : ℤ) : WithTop ℤ) := by exact_mod_cast hlt
        _ ≤ ψ.orderW p + ((-(A p) : ℤ) : WithTop ℤ) := by
            rw [← hm, ← WithTop.coe_add]
            have hAB : A p - B p ≤ m := by
              rw [← hm] at hψA
              exact_mod_cast hψA
            exact_mod_cast (by omega : -(B p) ≤ m + -(A p))
        _ ≤ meromorphicOrderAt Ψ c + meromorphicOrderAt (S - Ψi * T) c := by
            rw [horder]
            exact add_le_add le_rfl hSdiff
    have hfun : (Ψ * S) = (Ψ * (Ψi * T)) + (Ψ * (S - Ψi * T)) := by
      funext z
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
      ring
    rw [hfun, laurentCoeff_add (hΨm.mul (hΨim.mul hTm))
      (hΨm.mul (hSm.sub (hΨim.mul hTm))), hzero, add_zero]
  have hone : laurentCoeff (Ψ * (Ψi * T)) c n = laurentCoeff T c n := by
    refine laurentCoeff_congr ?_ n
    filter_upwards [psi_mul_inv_eventually_one ψ hψ p] with z hz
    show Ψ z * (Ψi z * T z) = T z
    calc Ψ z * (Ψi z * T z) = (Ψ z * Ψi z) * T z := by ring
      _ = T z := by rw [hz, one_mul]
  show laurentCoeff (fun z => ψ.toFun ((chartAt (H := ℂ) p).symm z)
      * tailFnAt (tailMul ψ⁻¹ A Z) p z) c n = Z (p, n)
  rw [show (fun z => ψ.toFun ((chartAt (H := ℂ) p).symm z)
      * tailFnAt (tailMul ψ⁻¹ A Z) p z) = Ψ * S from rfl]
  rw [hkey, hone, hT, laurentCoeff_tailFnAt]

/-! ### §3 The master bridge and μ-compatibility of the residue functional -/

open Classical in
/-- **The master bridge**: on tails of level `B` paired against a form of order ≥ `B`, the
residue functional is the sum over base points of the `resAt`-pairings of the tail polynomial
against the form's local coefficient (`resAt_mul_eq_sum_tailPairing`, read in reverse, with the
tail polynomial as the meromorphic factor — its coefficients *are* the entries). -/
theorem omegaTailResidue_eq_sum_resAt (ω₀ : HolomorphicOneForms X)
    (g : MeromorphicFunction X) {B : Divisor X} (hord : OmegaOrderBounded ω₀ g B)
    {Z : TailSpace X} (hZ : Z ∈ tailSubspace (X := X) B) (P : Finset X)
    (hP : Z.support.image Prod.fst ⊆ P) :
    omegaTailResidue ω₀ g Z = ∑ p ∈ P,
      resAt (fun z => tailFnAt Z p z * omegaCoeffFun ω₀ g p z) ((chartAt (H := ℂ) p) p) := by
  rw [omegaTailResidue_apply]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Z.support) (t := P) (g := Prod.fst)
    (fun q hq => hP (Finset.mem_image_of_mem _ hq))
    (fun q => Z q * omegaTailWeight ω₀ g q)]
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
    (meromorphicAt_omegaCoeffFun ω₀ g p) (hord p) Wp hWlt hWcap
  rw [hpair]
  rw [Finset.sum_image (fun (q : X × ℤ) hq (q' : X × ℤ) hq' hqq' => by
    have h1 := (Finset.mem_filter.mp hq).2
    have h2 := (Finset.mem_filter.mp hq').2
    exact Prod.ext (h1.trans h2.symm) hqq')]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hfst := (Finset.mem_filter.mp hq).2
  rw [laurentCoeff_tailFnAt]
  rw [show ((p, q.2) : X × ℤ) = q from Prod.ext hfst.symm rfl]
  rw [show omegaTailWeight ω₀ g q = laurentCoeff (omegaCoeffFun ω₀ g q.1)
    ((chartAt (H := ℂ) q.1) q.1) (-1 - q.2) from rfl, hfst]

/-- The form-order bound multiplies: `ord((ψ·h)·ω₀) ≥ A` when `ord(h·ω₀) ≥ E` and
`A − E ≤ ord ψ`. -/
theorem omegaOrderBounded_mul (ω₀ : HolomorphicOneForms X)
    (h ψ : MeromorphicFunction X) {A E : Divisor X} (hord : OmegaOrderBounded ω₀ h E)
    (hlev : MulLevelLE ψ A E) : OmegaOrderBounded ω₀ (ψ * h) A := by
  intro p
  set c : ℂ := (chartAt (H := ℂ) p) p with hc
  set Ψ : ℂ → ℂ := fun z => ψ.toFun ((chartAt (H := ℂ) p).symm z) with hΨ
  have hΨm : MeromorphicAt Ψ c := ψ.meromorphic p
  have hWm : MeromorphicAt (omegaCoeffFun ω₀ h p) c := meromorphicAt_omegaCoeffFun ω₀ h p
  have hgerm : omegaCoeffFun ω₀ (ψ * h) p =ᶠ[𝓝[≠] c] Ψ * omegaCoeffFun ω₀ h p := by
    refine Eventually.of_forall fun z => ?_
    show coeffAt ω₀ p z * (ψ * h).toFun ((chartAt (H := ℂ) p).symm z)
      = Ψ z * (coeffAt ω₀ p z * h.toFun ((chartAt (H := ℂ) p).symm z))
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
  rcases eq_or_ne (meromorphicOrderAt (omegaCoeffFun ω₀ h p) c) ⊤ with htop2 | hne2
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
`Res_{h·ω₀}(μ_ψ Z) = Res_{(ψ·h)·ω₀}(Z)` for `Z` of level `A`, the form of order ≥ `E`, and
`A − E ≤ ord ψ`: per point, the defect `tailFn(μ_ψ Z) − ψ·tailFn(Z)` has order ≥ `−E` and
pairs against order ≥ `E` to residue `0`. -/
theorem omegaTailResidue_tailMul (ω₀ : HolomorphicOneForms X)
    (h ψ : MeromorphicFunction X) {A E : Divisor X} (hord : OmegaOrderBounded ω₀ h E)
    (hlev : MulLevelLE ψ A E) {Z : TailSpace X} (hZ : Z ∈ tailSubspace (X := X) A) :
    omegaTailResidue ω₀ h (tailMul ψ E Z) = omegaTailResidue ω₀ (ψ * h) Z := by
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
  rw [omegaTailResidue_eq_sum_resAt ω₀ h hord hmem P hpts,
    omegaTailResidue_eq_sum_resAt ω₀ (ψ * h) (omegaOrderBounded_mul ω₀ h ψ hord hlev) hZ P
      (le_refl P)]
  refine Finset.sum_congr rfl fun p _ => ?_
  set c : ℂ := (chartAt (H := ℂ) p) p with hc
  set Ψ : ℂ → ℂ := fun z => ψ.toFun ((chartAt (H := ℂ) p).symm z) with hΨ
  set T : ℂ → ℂ := tailFnAt Z p with hT
  set S : ℂ → ℂ := tailFnAt (tailMul ψ E Z) p with hS
  set W : ℂ → ℂ := omegaCoeffFun ω₀ h p with hW
  have hΨm : MeromorphicAt Ψ c := ψ.meromorphic p
  have hTm : MeromorphicAt T c := meromorphicAt_tailFnAt Z p
  have hSm : MeromorphicAt S c := meromorphicAt_tailFnAt _ p
  have hWm : MeromorphicAt W c := meromorphicAt_omegaCoeffFun ω₀ h p
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
  rw [show resAt (fun z => tailFnAt (tailMul ψ E Z) p z * omegaCoeffFun ω₀ h p z) c
      = resAt (fun z => S z * W z) c from rfl, hsplit]
  refine resAt_congr (Eventually.of_forall fun z => ?_)
  show Ψ z * T z * W z = tailFnAt Z p z * omegaCoeffFun ω₀ (ψ * h) p z
  show Ψ z * T z * W z = T z * (coeffAt ω₀ p z
    * (ψ * h).toFun ((chartAt (H := ℂ) p).symm z))
  rw [MeromorphicFunction.mul_toFun, Pi.mul_apply]
  show Ψ z * T z * (coeffAt ω₀ p z * h.toFun ((chartAt (H := ℂ) p).symm z))
    = T z * (coeffAt ω₀ p z
      * (ψ.toFun ((chartAt (H := ℂ) p).symm z) * h.toFun ((chartAt (H := ℂ) p).symm z)))
  ring

/-! ### §4 Miranda Lemma 3.6: the order downgrade -/

/-- **Miranda Lemma 3.6.**  If the residue functional of `h·ω₀` (honestly defined at a fine
level `D'`) vanishes on every `D'`-tail killed by the `D`-truncation, then `h·ω₀` satisfies the
coarser bound `D` — else the single-monomial witness `z^{−1−o}·p` at a violating point is killed
by the truncation yet pairs to the nonzero leading coefficient. -/
theorem omegaOrderBounded_of_vanishing (ω₀ : HolomorphicOneForms X)
    (h : MeromorphicFunction X) {D' D : Divisor X}
    (hord : OmegaOrderBounded ω₀ h D')
    (hvan : ∀ Z : TailSpace X, Z ∈ tailSubspace (X := X) D' →
      truncateRaw (X := X) D Z = 0 → omegaTailResidue ω₀ h Z = 0) :
    OmegaOrderBounded ω₀ h D := by
  intro p
  by_contra hcon
  rw [not_le] at hcon
  have hne : meromorphicOrderAt (omegaCoeffFun ω₀ h p) ((chartAt (H := ℂ) p) p) ≠ ⊤ :=
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
  have hval : omegaTailResidue ω₀ h (Finsupp.single ((p, -1 - o) : X × ℤ) (1 : ℂ))
      = laurentCoeff (omegaCoeffFun ω₀ h p) ((chartAt (H := ℂ) p) p) o := by
    rw [omegaTailResidue_apply, Finsupp.support_single _ one_ne_zero,
      Finset.sum_singleton, Finsupp.single_eq_same, one_mul, omegaTailWeight]
    congr 1
    omega
  have hne0 : laurentCoeff (omegaCoeffFun ω₀ h p) ((chartAt (H := ℂ) p) p) o ≠ 0 :=
    laurentCoeff_order_ne_zero (meromorphicAt_omegaCoeffFun ω₀ h p) ho.symm
  exact hne0 (hval ▸ hvan _ hmem hkill)

end Jacobians.LaurentTail
