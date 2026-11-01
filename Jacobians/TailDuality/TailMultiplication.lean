/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Multiplication operators on Laurent tail divisors (Miranda Ch. VI p. 179, Problem VI.2.A)

For a meromorphic `ψ` and a target level `E`, the operator

  `μ_ψ : 𝒯(X) → 𝒯[E](X)`,  `μ_ψ(∑ r_p·p) = ∑ (tail of ψ·r_p below −E(p))·p`

multiplies each per-point tail polynomial by `ψ` and re-truncates.  The Lean representation goes
through the **tail polynomial as an actual function** `tailFnAt Z p : ℂ → ℂ`, whose Laurent
coefficients are literally the tail entries (`laurentCoeff_tailFnAt`) — so the operator algebra
reduces to the `laurentCoeff` toolkit and no explicit convolution ever appears.

Contents:
* `tailFnAt`, `laurentCoeff_tailFnAt`, meromorphy, additivity/homogeneity;
* `tailMul ψ E : TailSpace X →ₗ[ℂ] TailSpace X`, range in `tailSubspace E`;
* **Miranda (2.2)** `tailMul_tailMap`: `μ_ψ(α_D f) = α_E(ψ·f)` whenever
  `−E ≤ ord ψ + (−D)` pointwise — "coefficients below a level only see the complementary tail".

The `H¹`-level maps and the surjectivity assembly (Forster 17.9 / Miranda 3.4) build on this. -/
import Jacobians.TailDuality.TailResidue
open scoped Manifold ContDiff Topology
open Filter Set
open Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace

namespace Jacobians.LaurentTail

/-! ### §0 A generic finiteness window for coefficients of a meromorphic germ -/

/-- For a meromorphic germ, only finitely many Laurent coefficients below any level are
nonzero. -/
theorem finite_setOf_laurentCoeff_ne_zero_lt {g : ℂ → ℂ} {c : ℂ} (hg : MeromorphicAt g c)
    (b : ℤ) : {n : ℤ | n < b ∧ laurentCoeff g c n ≠ 0}.Finite := by
  rcases eq_or_ne (meromorphicOrderAt g c) ⊤ with htop | hne
  · refine Set.Finite.subset Set.finite_empty fun n hn => ?_
    obtain ⟨-, hne0⟩ := hn
    exact (hne0 (laurentCoeff_eq_zero_of_lt_order hg (htop ▸ WithTop.coe_lt_top n))).elim
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
    refine Set.Finite.subset (Set.finite_Ico m b) fun n hn => ?_
    obtain ⟨hnb, hne0⟩ := hn
    refine ⟨?_, hnb⟩
    by_contra hlt
    exact hne0 (laurentCoeff_eq_zero_of_lt_order hg
      (by rw [← hm]; exact_mod_cast (by omega : n < m)))

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ### §1 The per-point tail polynomial as a function -/

open Classical in
/-- The tail polynomial of `Z` at `p`, as an actual function:
`tailFnAt Z p (z) = ∑_{(p,n) ∈ supp Z} Z(p,n)·(z − c_p)^n`. -/
noncomputable def tailFnAt (Z : TailSpace X) (p : X) : ℂ → ℂ :=
  fun z => Z.sum fun q a =>
    if q.1 = p then a * (z - (chartAt (H := ℂ) p) p) ^ q.2 else 0

open Classical in
theorem tailFnAt_def (Z : TailSpace X) (p : X) :
    tailFnAt Z p = fun z => ∑ q ∈ Z.support,
      (if q.1 = p then Z q * (z - (chartAt (H := ℂ) p) p) ^ q.2 else 0) :=
  rfl

open Classical in
theorem meromorphicAt_tailFnAt (Z : TailSpace X) (p : X) :
    MeromorphicAt (tailFnAt Z p) ((chartAt (H := ℂ) p) p) := by
  rw [tailFnAt_def]
  refine meromorphicAt_finset_sum Z.support _ fun q _ => ?_
  by_cases hq : q.1 = p
  · simp only [hq, if_true]
    exact (analyticAt_const.meromorphicAt).mul (meromorphicAt_monomial _ q.2)
  · simp only [hq, if_false]
    exact analyticAt_const.meromorphicAt

open Classical in
/-- **The coefficients of the tail polynomial are the tail entries.** -/
theorem laurentCoeff_tailFnAt (Z : TailSpace X) (p : X) (n : ℤ) :
    laurentCoeff (tailFnAt Z p) ((chartAt (H := ℂ) p) p) n = Z (p, n) := by
  rw [tailFnAt_def, laurentCoeff_finset_sum Z.support _ (fun q _ => by
    by_cases hq : q.1 = p
    · simp only [hq, if_true]
      exact (analyticAt_const.meromorphicAt).mul (meromorphicAt_monomial _ q.2)
    · simp only [hq, if_false]
      exact analyticAt_const.meromorphicAt) n]
  have hterm : ∀ q ∈ Z.support,
      laurentCoeff (fun z => if q.1 = p then Z q * (z - (chartAt (H := ℂ) p) p) ^ q.2 else 0)
        ((chartAt (H := ℂ) p) p) n
      = if q = (p, n) then Z q else 0 := by
    intro q _
    by_cases hq : q.1 = p
    · have hfun : (fun z => if q.1 = p then Z q * (z - (chartAt (H := ℂ) p) p) ^ q.2 else 0)
          = fun z => Z q * (z - (chartAt (H := ℂ) p) p) ^ q.2 := by
        funext z; rw [if_pos hq]
      rw [hfun, laurentCoeff_const_mul_monomial]
      by_cases hq2 : q.2 = n
      · rw [if_pos hq2, if_pos (Prod.ext hq hq2)]
      · rw [if_neg hq2, if_neg (fun hcon => hq2 (by rw [hcon]))]
    · have hfun : (fun z => if q.1 = p then Z q * (z - (chartAt (H := ℂ) p) p) ^ q.2 else 0)
          = fun _ => (0 : ℂ) := by
        funext z; rw [if_neg hq]
      rw [hfun, if_neg (fun hcon => hq (by rw [hcon])), laurentCoeff_def]
      have h0 : (fun z => (fun _ : ℂ => (0 : ℂ)) z
          * (z - (chartAt (H := ℂ) p) p) ^ (-n - 1)) = fun _ : ℂ => (0 : ℂ) := by
        funext z; ring
      rw [h0]
      exact Jacobians.Dolbeault.resAt_eq_zero_of_analyticAt analyticAt_const
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' Z.support ((p, n) : X × ℤ) Z]
  split_ifs with hmem
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hmem).symm

open Classical in
/-- The tail polynomial is additive in `Z`. -/
theorem tailFnAt_add (Z₁ Z₂ : TailSpace X) (p : X) (z : ℂ) :
    tailFnAt (Z₁ + Z₂) p z = tailFnAt Z₁ p z + tailFnAt Z₂ p z := by
  show Finsupp.sum (Z₁ + Z₂) _ = Finsupp.sum Z₁ _ + Finsupp.sum Z₂ _
  refine Finsupp.sum_add_index' (fun q => ?_) (fun q a₁ a₂ => ?_)
  · split_ifs <;> simp
  · split_ifs <;> ring

open Classical in
/-- The tail polynomial is homogeneous in `Z`. -/
theorem tailFnAt_smul (c : ℂ) (Z : TailSpace X) (p : X) (z : ℂ) :
    tailFnAt (c • Z) p z = c * tailFnAt Z p z := by
  show Finsupp.sum (c • Z) _ = c * Finsupp.sum Z _
  rw [Finsupp.sum_smul_index (fun q => by split_ifs <;> simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun q _ => ?_
  split_ifs <;> ring

open Classical in
/-- For `p` outside the base points of `Z`, the tail polynomial vanishes. -/
theorem tailFnAt_eq_zero_of_notMem (Z : TailSpace X) (p : X)
    (hp : p ∉ Z.support.image Prod.fst) (z : ℂ) : tailFnAt Z p z = 0 := by
  classical
  rw [tailFnAt_def]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [if_neg fun hq1 => hp (Finset.mem_image.mpr ⟨q, hq, hq1⟩)]

/-! ### §2 The multiplication operator -/

open Classical in
/-- The entries of `μ_ψ(Z)` at target level `E`: the coefficients of `ψ·(tail polynomial)`,
truncated below `−E`. -/
noncomputable def tailMulFun (ψ : MeromorphicFunction X) (E : Divisor X) (Z : TailSpace X) :
    (X × ℤ) → ℂ :=
  fun q => if q.2 < -(E q.1)
    then laurentCoeff
      (fun z => ψ.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z)
      ((chartAt (H := ℂ) q.1) q.1) q.2
    else 0

theorem meromorphicAt_psi_mul_tailFnAt (ψ : MeromorphicFunction X) (Z : TailSpace X) (p : X) :
    MeromorphicAt (fun z => ψ.toFun ((chartAt (H := ℂ) p).symm z) * tailFnAt Z p z)
      ((chartAt (H := ℂ) p) p) :=
  (ψ.meromorphic p).mul (meromorphicAt_tailFnAt Z p)

open Classical in
theorem finite_support_tailMulFun (ψ : MeromorphicFunction X) (E : Divisor X)
    (Z : TailSpace X) : (Function.support (tailMulFun ψ E Z)).Finite := by
  refine Set.Finite.subset (Set.Finite.biUnion
    (Z.support.image Prod.fst).finite_toSet (fun p _ =>
      ((finite_setOf_laurentCoeff_ne_zero_lt (meromorphicAt_psi_mul_tailFnAt ψ Z p)
        (-(E p))).image fun n => ((p, n) : X × ℤ)))) ?_
  intro q hq
  rw [Function.mem_support, tailMulFun] at hq
  by_cases hlt : q.2 < -(E q.1)
  · rw [if_pos hlt] at hq
    have hp : q.1 ∈ Z.support.image Prod.fst := by
      by_contra hpn
      apply hq
      have h0 : (fun z => ψ.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z)
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
    refine Set.mem_biUnion hp ?_
    exact ⟨q.2, ⟨hlt, hq⟩, Prod.ext rfl rfl⟩
  · rw [if_neg hlt] at hq
    exact absurd rfl hq

/-- `μ_ψ(Z)` as a tail divisor. -/
noncomputable def tailMulRaw (ψ : MeromorphicFunction X) (E : Divisor X) (Z : TailSpace X) :
    TailSpace X :=
  Finsupp.ofSupportFinite _ (finite_support_tailMulFun ψ E Z)

theorem tailMulRaw_apply (ψ : MeromorphicFunction X) (E : Divisor X) (Z : TailSpace X)
    (q : X × ℤ) : tailMulRaw ψ E Z q = tailMulFun ψ E Z q := rfl

theorem tailMulRaw_mem (ψ : MeromorphicFunction X) (E : Divisor X) (Z : TailSpace X) :
    tailMulRaw ψ E Z ∈ tailSubspace (X := X) E := by
  rw [mem_tailSubspace_iff]
  intro q hq
  rw [tailMulRaw_apply, tailMulFun, if_neg hq]

/-- **Miranda's multiplication operator `μ_ψ`** (Ch. VI p. 179) at target level `E`, as a linear
endomorphism of the ambient tail space (range in `𝒯[E]` by `tailMulRaw_mem`). -/
noncomputable def tailMul (ψ : MeromorphicFunction X) (E : Divisor X) :
    TailSpace X →ₗ[ℂ] TailSpace X where
  toFun := tailMulRaw ψ E
  map_add' Z₁ Z₂ := by
    classical
    ext q
    rw [Finsupp.add_apply, tailMulRaw_apply, tailMulRaw_apply, tailMulRaw_apply,
      tailMulFun, tailMulFun, tailMulFun]
    split_ifs with hlt
    · have hfun : (fun z => ψ.toFun ((chartAt (H := ℂ) q.1).symm z)
          * tailFnAt (Z₁ + Z₂) q.1 z)
          = fun z => (fun w => ψ.toFun ((chartAt (H := ℂ) q.1).symm w) * tailFnAt Z₁ q.1 w) z
            + (fun w => ψ.toFun ((chartAt (H := ℂ) q.1).symm w) * tailFnAt Z₂ q.1 w) z := by
        funext z
        rw [tailFnAt_add]
        ring
      rw [hfun]
      have := laurentCoeff_add (meromorphicAt_psi_mul_tailFnAt ψ Z₁ q.1)
        (meromorphicAt_psi_mul_tailFnAt ψ Z₂ q.1) q.2
      rw [← this]
      rfl
    · ring
  map_smul' c Z := by
    classical
    ext q
    rw [RingHom.id_apply, Finsupp.smul_apply, tailMulRaw_apply, tailMulRaw_apply,
      tailMulFun, tailMulFun]
    split_ifs with hlt
    · have hfun : (fun z => ψ.toFun ((chartAt (H := ℂ) q.1).symm z)
          * tailFnAt (c • Z) q.1 z)
          = c • fun z => ψ.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z := by
        funext z
        rw [Pi.smul_apply, tailFnAt_smul, smul_eq_mul]
        ring
      rw [hfun, laurentCoeff_smul c (meromorphicAt_psi_mul_tailFnAt ψ Z q.1), smul_eq_mul]
    · rw [smul_zero]

theorem tailMul_apply (ψ : MeromorphicFunction X) (E : Divisor X) (Z : TailSpace X)
    (q : X × ℤ) :
    tailMul ψ E Z q = if q.2 < -(E q.1)
      then laurentCoeff
        (fun z => ψ.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z)
        ((chartAt (H := ℂ) q.1) q.1) q.2
      else 0 := rfl

/-! ### §3 Compatibility with the truncated-Laurent-series map (Miranda (2.2)) -/

/-- **Miranda (2.2)**: `μ_ψ(α_D f) = α_E(ψ·f)` whenever `−E ≤ ord ψ + (−D)` pointwise — the
re-truncated coefficients of `ψ·(D-tail of f)` and of `ψ·f` agree below `−E`, because `ψ` times
the complementary part of `f` has order ≥ `ord ψ − D ≥ −E`. -/
theorem tailMul_tailMap [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (ψ f : MeromorphicFunction X) (D E : Divisor X)
    (hE : ∀ p : X, ((-(E p) : ℤ) : WithTop ℤ) ≤ ψ.orderW p + ((-(D p) : ℤ) : WithTop ℤ)) :
    tailMul ψ E (tailMap (X := X) D f) = tailMap (X := X) E (ψ * f) := by
  classical
  ext q
  obtain ⟨p, n⟩ := q
  rw [tailMul_apply, tailMap_apply]
  by_cases hlt : n < -(E p)
  · rw [if_pos hlt, if_pos hlt]
    -- the two integrands differ by `ψ·(tail − f)`, whose order is ≥ −E p > n
    set c : ℂ := (chartAt (H := ℂ) p) p with hc
    set T : ℂ → ℂ := tailFnAt (tailMap (X := X) D f) p with hT
    set F : ℂ → ℂ := fun z => f.toFun ((chartAt (H := ℂ) p).symm z) with hF
    set Ψ : ℂ → ℂ := fun z => ψ.toFun ((chartAt (H := ℂ) p).symm z) with hΨ
    have hTm : MeromorphicAt T c := meromorphicAt_tailFnAt _ p
    have hFm : MeromorphicAt F c := f.meromorphic p
    have hΨm : MeromorphicAt Ψ c := ψ.meromorphic p
    have hTFm : MeromorphicAt (T - F) c := hTm.sub hFm
    -- coefficients of `T − F` below `−D p` vanish, so its order is ≥ −D p
    have hTF : ((-(D p) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (T - F) c := by
      rw [le_order_iff_laurentCoeff_eq_zero hTFm]
      intro m hm
      have hsub : laurentCoeff (T - F) c m
          = laurentCoeff T c m - laurentCoeff F c m := by
        have hnegT : laurentCoeff (-F) c m = -laurentCoeff F c m := by
          have hF' : (-F) = (-1 : ℂ) • F := by funext z; simp
          rw [hF', laurentCoeff_smul (-1 : ℂ) hFm]
          ring
        have hfun : (T - F) = T + -F := by
          funext z
          simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
          ring
        rw [hfun, laurentCoeff_add hTm hFm.neg, hnegT]
        ring
      rw [hsub, hT, laurentCoeff_tailFnAt, tailMap_apply, if_pos hm]
      exact sub_self _
    -- hence `Ψ·(T − F)` has order ≥ −E p, and its coefficient at `n < −E p` vanishes
    have hcoeff0 : laurentCoeff (Ψ * (T - F)) c n = 0 := by
      refine laurentCoeff_eq_zero_of_lt_order (hΨm.mul hTFm) ?_
      rw [meromorphicOrderAt_mul hΨm hTFm]
      calc ((n : ℤ) : WithTop ℤ) < ((-(E p) : ℤ) : WithTop ℤ) := by exact_mod_cast hlt
        _ ≤ ψ.orderW p + ((-(D p) : ℤ) : WithTop ℤ) := hE p
        _ ≤ meromorphicOrderAt Ψ c + meromorphicOrderAt (T - F) c := by
            exact add_le_add le_rfl hTF
    -- so the coefficients of `Ψ·T` and `Ψ·F` agree at `n`
    have hsplit : laurentCoeff (Ψ * T) c n = laurentCoeff (Ψ * F) c n := by
      have hfun : (Ψ * T) = (Ψ * F) + (Ψ * (T - F)) := by
        funext z
        simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
        ring
      rw [hfun, laurentCoeff_add (hΨm.mul hFm) (hΨm.mul hTFm), hcoeff0, add_zero]
    rw [show laurentCoeff (fun z => ψ.toFun ((chartAt (H := ℂ) p).symm z)
        * tailFnAt (tailMap (X := X) D f) p z) ((chartAt (H := ℂ) p) p) n
        = laurentCoeff (Ψ * T) c n from rfl, hsplit]
    show laurentCoeff (Ψ * F) c n = laurentCoeffAt (ψ * f).toFun p n
    refine laurentCoeff_congr (Eventually.of_forall fun z => ?_) n
    show Ψ z * F z = ((ψ * f).toFun ∘ (chartAt (H := ℂ) p).symm) z
    rw [Function.comp_apply, MeromorphicFunction.mul_toFun, Pi.mul_apply]
  · rw [if_neg hlt, if_neg hlt]

end Jacobians.LaurentTail
