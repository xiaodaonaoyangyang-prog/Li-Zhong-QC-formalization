/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# The multiplication action on the Mittag-Leffler `H¹` (Forster 17.8 / Miranda Problem VI.2.J)

For a meromorphic `ψ` with `A − B ≤ ord ψ` pointwise, the operator `μ_ψ` maps `𝒯[A]` into
`𝒯[B]` and sends realized tails to realized tails (Miranda (2.2)), hence descends to

  `tailMulH1 ψ A B : H¹(A) →ₗ H¹(B)`.

The two key facts for the Serre-duality surjectivity (Forster 17.8):
* the **composite identity** `μ_ψ ∘ μ_{ψ⁻¹} = id` on `𝒯[B]` at the exact shift `A = B + div ψ`
  (for `ψ` with globally surviving germ — the identity theorem `orderW_ne_top_of_exists`),
  making `tailMulH1 ψ (B + div ψ) B` surjective;
* the **factoring** `tailMulH1 ψ A B = tailMulH1 ψ (B + div ψ) B ∘ mittagLefflerTruncate`
  (coefficients below `−B` cannot see the dropped window), so with the truncation epimorphism
  the general `tailMulH1 ψ A B` is surjective as well.

Consequently, for `λ ≠ 0` and `ψ` with surviving germ, `λ ∘ tailMulH1 ψ A B ≠ 0` — the
dimension input for the pigeonhole half of Serre duality.
-/
import Jacobians.Meromorphic.MeromorphicInverse
import Jacobians.TailDuality.TailMultiplication

open scoped Manifold ContDiff Topology
open Filter Set
open Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace

namespace Jacobians.LaurentTail

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ### §1 The order bookkeeping interface -/

/-- The standing order condition for `μ_ψ : 𝒯[A] → 𝒯[B]` to be compatible with realization:
`A − B ≤ ord ψ` pointwise. -/
def MulLevelLE (ψ : MeromorphicFunction X) (A B : Divisor X) : Prop :=
  ∀ p : X, ((A p - B p : ℤ) : WithTop ℤ) ≤ ψ.orderW p

theorem MulLevelLE.hE {ψ : MeromorphicFunction X} {A B : Divisor X} (h : MulLevelLE ψ A B) :
    ∀ p : X, ((-(B p) : ℤ) : WithTop ℤ) ≤ ψ.orderW p + ((-(A p) : ℤ) : WithTop ℤ) := by
  intro p
  have h1 := h p
  rcases eq_or_ne (ψ.orderW p) ⊤ with htop | hne
  · rw [htop, WithTop.top_add]
    exact le_top
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hm] at h1 ⊢
  rw [← WithTop.coe_add]
  have : A p - B p ≤ m := by exact_mod_cast h1
  exact_mod_cast (by omega : -(B p) ≤ m + -(A p))

/-- Membership `ψ ∈ L(C)` gives the level condition for `A := B − C`-type shifts:
`MulLevelLE ψ (B - C) B`. -/
theorem mulLevelLE_of_mem [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    {ψ : MeromorphicFunction X} {C : Divisor X}
    (hψ : ψ ∈ linearSystem (X := X) C) (B : Divisor X) :
    MulLevelLE ψ (B - C) B := by
  intro p
  have h1 : ((-(C p) : ℤ) : WithTop ℤ) ≤ ψ.orderW p := hψ p
  have : ((B - C) p : ℤ) - B p = -(C p) := by
    rw [Finsupp.sub_apply]
    ring
  rw [this]
  exact h1

/-- The exact shift `A := B + div ψ` satisfies the level condition. -/
theorem mulLevelLE_add_div [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    [Nonempty X] (ψ : MeromorphicFunction X) (B : Divisor X) :
    MulLevelLE ψ (B + (ψ.div : Divisor X)) B := by
  intro p
  have : ((B + (ψ.div : Divisor X)) p : ℤ) - B p = (ψ.div : Divisor X) p := by
    rw [Finsupp.add_apply]
    ring
  rw [this, div_apply]
  rcases eq_or_ne (ψ.orderW p) ⊤ with htop | hne
  · rw [htop]
    exact le_top
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hm, WithTop.untop₀_coe]

/-! ### §2 The `H¹`-level map -/

/-- `μ_ψ` co-restricted between tail levels (the target membership is unconditional — the
operator truncates at `B` by construction). -/
noncomputable def tailMulCo [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (ψ : MeromorphicFunction X) (A B : Divisor X) :
    ↥(tailSubspace (X := X) A) →ₗ[ℂ] ↥(tailSubspace (X := X) B) :=
  ((tailMul ψ B).comp (Submodule.subtype _)).codRestrict _
    fun Z => tailMulRaw_mem ψ B (Z : TailSpace X)

@[simp] theorem tailMulCo_coe [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (ψ : MeromorphicFunction X) (A B : Divisor X)
    (Z : ↥(tailSubspace (X := X) A)) :
    (tailMulCo ψ A B Z : TailSpace X) = tailMul ψ B (Z : TailSpace X) := rfl

/-- **The `H¹`-level multiplication action** (Miranda Problem VI.2.J): `μ_ψ` descends to the
Mittag-Leffler quotients under the level condition (realized tails map to realized tails by
Miranda (2.2)). -/
noncomputable def tailMulH1 [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (ψ : MeromorphicFunction X) {A B : Divisor X}
    (h : MulLevelLE ψ A B) :
    mittagLefflerH1 (X := X) A →ₗ[ℂ] mittagLefflerH1 (X := X) B :=
  Submodule.mapQ _ _ (tailMulCo ψ A B) (by
    rintro Z ⟨f, rfl⟩
    refine Submodule.mem_comap.mpr ⟨ψ * f, ?_⟩
    refine Subtype.ext ?_
    rw [tailMapCo_coe, tailMulCo_coe, tailMapCo_coe]
    exact (tailMul_tailMap ψ f A B h.hE).symm)

@[simp] theorem tailMulH1_mk [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (ψ : MeromorphicFunction X) {A B : Divisor X}
    (h : MulLevelLE ψ A B) (Z : ↥(tailSubspace (X := X) A)) :
    tailMulH1 ψ h (Submodule.Quotient.mk Z) = Submodule.Quotient.mk (tailMulCo ψ A B Z) :=
  rfl

/-! ### §3 The composite identity at the exact shift, and surjectivity -/

/-- For `ψ` whose germ survives somewhere (hence everywhere — `orderW_ne_top_of_exists`),
`ψ·ψ⁻¹` has germ `1` at every point. -/
theorem psi_mul_inv_eventually_one [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] (ψ : MeromorphicFunction X)
    (hψ : ∃ x, ψ.orderW x ≠ ⊤) (p : X) :
    ∀ᶠ z in 𝓝[≠] ((chartAt (H := ℂ) p) p),
      ψ.toFun ((chartAt (H := ℂ) p).symm z)
        * (ψ⁻¹).toFun ((chartAt (H := ℂ) p).symm z) = 1 := by
  have hne := (MeromorphicFunction.orderW_ne_top_iff ψ p).mp
    (MeromorphicFunction.orderW_ne_top_of_exists ψ hψ p)
  have htrans := (MeromorphicFunction.eventually_comp_chart_iff ψ.toFun p (· ≠ 0)).mpr hne
  filter_upwards [htrans] with z hz
  exact mul_inv_cancel₀ hz

/-- **The composite identity** `μ_ψ(μ_{ψ⁻¹}(W)) = W` on `𝒯[B]` at the exact shift
`A = B + div ψ`: the coefficients of `ψ·(A-tail of ψ⁻¹·(tail of W))` below `−B` are those of
`ψ·ψ⁻¹·(tail of W) = tail of W`, because the dropped part has order ≥ `ord ψ − A ≥ −B`. -/
theorem tailMul_tailMul_inv [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    [Nonempty X] (ψ : MeromorphicFunction X) (hψ : ∃ x, ψ.orderW x ≠ ⊤)
    (B : Divisor X) (W : ↥(tailSubspace (X := X) B)) :
    tailMul ψ B (tailMul ψ⁻¹ (B + (ψ.div : Divisor X)) (W : TailSpace X))
      = (W : TailSpace X) := by
  classical
  set A : Divisor X := B + (ψ.div : Divisor X) with hA
  ext q
  obtain ⟨p, n⟩ := q
  rw [tailMul_apply]
  by_cases hlt : n < -(B p)
  swap
  · rw [if_neg hlt]
    exact ((mem_tailSubspace_iff.mp W.2) (p, n) hlt).symm
  rw [if_pos hlt]
  set c : ℂ := (chartAt (H := ℂ) p) p with hc
  set Ψ : ℂ → ℂ := fun z => ψ.toFun ((chartAt (H := ℂ) p).symm z) with hΨ
  set Ψi : ℂ → ℂ := fun z => (ψ⁻¹).toFun ((chartAt (H := ℂ) p).symm z) with hΨi
  set T : ℂ → ℂ := tailFnAt (W : TailSpace X) p with hT
  set S : ℂ → ℂ := tailFnAt (tailMul ψ⁻¹ A (W : TailSpace X)) p with hS
  have hΨm : MeromorphicAt Ψ c := ψ.meromorphic p
  have hΨim : MeromorphicAt Ψi c := (ψ⁻¹).meromorphic p
  have hTm : MeromorphicAt T c := meromorphicAt_tailFnAt _ p
  have hSm : MeromorphicAt S c := meromorphicAt_tailFnAt _ p
  have hordψ : ψ.orderW p ≠ ⊤ := MeromorphicFunction.orderW_ne_top_of_exists ψ hψ p
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hordψ
  -- `S − Ψi·T` has order ≥ −A p (its coefficients below `−A p` agree by construction)
  have hSdiff : ((-(A p) : ℤ) : WithTop ℤ)
      ≤ meromorphicOrderAt (S - Ψi * T) c := by
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
    have : laurentCoeff (Ψi * T) c j
        = laurentCoeff (fun z => (ψ⁻¹).toFun ((chartAt (H := ℂ) p).symm z)
            * tailFnAt (W : TailSpace X) p z) c j := rfl
    rw [this]
    exact sub_self _
  -- hence `Ψ·S` and `Ψ·Ψi·T` have equal coefficients below `−B p`
  have hkey : laurentCoeff (Ψ * S) c n = laurentCoeff (Ψ * (Ψi * T)) c n := by
    have hzero : laurentCoeff (Ψ * (S - Ψi * T)) c n = 0 := by
      refine laurentCoeff_eq_zero_of_lt_order (hΨm.mul (hSm.sub (hΨim.mul hTm))) ?_
      rw [meromorphicOrderAt_mul hΨm (hSm.sub (hΨim.mul hTm))]
      have hψA : ((A p - B p : ℤ) : WithTop ℤ) ≤ ψ.orderW p := mulLevelLE_add_div ψ B p
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
  -- `Ψ·Ψi·T` has the germ of `T` (`ψ·ψ⁻¹ = 1` near `p`)
  have hone : laurentCoeff (Ψ * (Ψi * T)) c n = laurentCoeff T c n := by
    refine laurentCoeff_congr ?_ n
    filter_upwards [psi_mul_inv_eventually_one ψ hψ p] with z hz
    show Ψ z * (Ψi z * T z) = T z
    calc Ψ z * (Ψi z * T z) = (Ψ z * Ψi z) * T z := by ring
      _ = T z := by rw [hz, one_mul]
  -- assemble
  show laurentCoeff (fun z => ψ.toFun ((chartAt (H := ℂ) p).symm z)
      * tailFnAt (tailMul ψ⁻¹ A (W : TailSpace X)) p z) c n = (W : TailSpace X) (p, n)
  rw [show (fun z => ψ.toFun ((chartAt (H := ℂ) p).symm z)
      * tailFnAt (tailMul ψ⁻¹ A (W : TailSpace X)) p z) = Ψ * S from rfl]
  rw [hkey, hone, hT, laurentCoeff_tailFnAt]

/-! ### §4 Surjectivity of the `H¹` action (Forster 17.8) -/

/-- **Surjectivity of the `H¹` multiplication action** (Forster 17.8): for `ψ` with surviving
germ, every class of `H¹(B)` is hit — the preimage is the `ψ⁻¹`-image at the exact shift
`B + div ψ`, which lies in the (coarser) `𝒯[A]` since `A ≤ B + div ψ`. -/
theorem tailMulH1_surjective [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    [Nonempty X] (ψ : MeromorphicFunction X) (hψ : ∃ x, ψ.orderW x ≠ ⊤)
    {A B : Divisor X} (h : MulLevelLE ψ A B) :
    Function.Surjective (tailMulH1 ψ h) := by
  intro ξ
  obtain ⟨W, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  have hAC : ∀ p : X, A p ≤ (B + (ψ.div : Divisor X)) p := by
    intro p
    have h1 := h p
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (MeromorphicFunction.orderW_ne_top_of_exists ψ hψ p)
    rw [Finsupp.add_apply, div_apply, ← hm, WithTop.untop₀_coe]
    rw [← hm] at h1
    have h2 : A p - B p ≤ m := by exact_mod_cast h1
    omega
  refine ⟨Submodule.Quotient.mk
    ⟨(tailMulCo ψ⁻¹ B (B + (ψ.div : Divisor X)) W : TailSpace X), ?_⟩, ?_⟩
  · -- membership in the coarser `𝒯[A]`
    have hmem := (tailMulCo ψ⁻¹ B (B + (ψ.div : Divisor X)) W).2
    rw [mem_tailSubspace_iff] at hmem ⊢
    intro q hq
    refine hmem q fun hlt => hq ?_
    have := hAC q.1
    omega
  · rw [tailMulH1_mk]
    congr 1
    refine Subtype.ext ?_
    rw [tailMulCo_coe]
    exact tailMul_tailMul_inv ψ hψ B W

/-- For `λ ≠ 0` and `ψ` with surviving germ, `λ ∘ T̄_ψ ≠ 0` — the dimension input for the
Λ-side of the Serre-duality pigeonhole (Forster 17.9). -/
theorem comp_tailMulH1_ne_zero [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    [Nonempty X] {B : Divisor X}
    (φ : Module.Dual ℂ (mittagLefflerH1 (X := X) B)) (hφ : φ ≠ 0)
    (ψ : MeromorphicFunction X) (hψ : ∃ x, ψ.orderW x ≠ ⊤)
    {A : Divisor X} (h : MulLevelLE ψ A B) :
    φ.comp (tailMulH1 ψ h) ≠ 0 := by
  intro h0
  apply hφ
  refine LinearMap.ext fun ξ => ?_
  obtain ⟨η, rfl⟩ := tailMulH1_surjective ψ hψ h ξ
  simpa using LinearMap.ext_iff.mp h0 η

end Jacobians.LaurentTail
