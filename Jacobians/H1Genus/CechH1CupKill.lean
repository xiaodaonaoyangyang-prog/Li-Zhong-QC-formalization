/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Killing a Čech `H¹(𝒪)` class in a larger divisor (Miranda Ch. X §2 / Forster §16-style)

The pigeonhole engine for the dimension count `h¹(0) = g`: every class `ξ ∈ H¹(𝔘, 𝒪)` dies in
`H¹(𝔘, 𝒪_A)` for **some** effective divisor `A` (depending on `ξ`).

*Proof (the classical multiplication trick).*  Fix a point `P` and set `K₁ := h¹(0)·P`.  By
cohomological Riemann–Roch (`cohomological_riemannRoch`) `l(K₁) = h¹(K₁) + 1 > h¹(K₁)`, so the
linear map `L(K₁) → H¹(𝒪_{K₁})`, `f ↦ f ⌣ ξ` (the `SerreCupProduct` multiplication action) has a
**nonzero kernel element** `f`.  Dividing back by `f` — multiplication by `f⁻¹ ∈ L(div f)` —
recovers the inclusion-induced image of `ξ` in `H¹(𝒪_A)` for `A := K₁ + div f ≥ 0`:

    h1Incl ξ = 1 ⌣ ξ = (f⁻¹·f) ⌣ ξ = f⁻¹ ⌣ (f ⌣ ξ) = f⁻¹ ⌣ 0 = 0.

The new algebraic ingredients are the multiplicativity laws for the cup action (`cupH1_mul`,
`cupH1_one_eq_h1Incl`, `cupH1_congr_germ`) and the order bookkeeping for products/reciprocals of
meromorphic functions (`orderW_mul`, `inv_mem_linearSystem_div`).

References: Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. X §2 (pp. 313–315, the
`H¹(D_n) = 0` enlargement in Lemma 2.3); Forster, *Lectures on Riemann Surfaces* (GTM 81),
§16–17 (the multiplication action; the same pigeonhole drives 17.8).
-/
import Jacobians.Cech.MeromorphicAnalyticBadSet
import Jacobians.H1Genus.CechH1Monotonicity
import Jacobians.H1Genus.SerreCupProduct
import Jacobians.Meromorphic.MeromorphicInverse
open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)


namespace Jacobians

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ### Order and linear-system bookkeeping for products, the constant `1`, and reciprocals -/

/-- Constant functions are meromorphic (chart pullbacks of constants are constant). -/
theorem IsMeromorphic.const {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (c : ℂ) :
    IsMeromorphic X fun _ => c := by
  intro x
  show MeromorphicAt (fun _ => c) ((chartAt (H := ℂ) x) x)
  exact MeromorphicAt.const c _

/-- The constant function `1` as a meromorphic function. -/
noncomputable instance : One (MeromorphicFunction X) :=
  ⟨⟨fun _ => 1, IsMeromorphic.const (X := X) 1⟩⟩

@[simp] theorem MeromorphicFunction.one_toFun {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] :
    (1 : MeromorphicFunction X).toFun = fun _ => (1 : ℂ) := rfl

/-- The constant `1` has germ-order `0` at every point. -/
theorem MeromorphicFunction.orderW_one {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) :
    (1 : MeromorphicFunction X).orderW x = 0 := by
  classical
  show meromorphicOrderAt ((fun _ : X => (1 : ℂ)) ∘ (chartAt (H := ℂ) x).symm) _ = 0
  rw [show ((fun _ : X => (1 : ℂ)) ∘ (chartAt (H := ℂ) x).symm) = fun _ => (1 : ℂ) from rfl,
    meromorphicOrderAt_const]
  simp

/-- **Order is additive in products**: `orderW (f·g) = orderW f + orderW g`
(Mathlib `meromorphicOrderAt_mul`, read in the chart at each point). -/
theorem MeromorphicFunction.orderW_mul {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (f g : MeromorphicFunction X) (x : X) :
    (f * g).orderW x = f.orderW x + g.orderW x := by
  show meromorphicOrderAt ((f.toFun * g.toFun) ∘ (chartAt (H := ℂ) x).symm) _ = _
  rw [show (f.toFun * g.toFun) ∘ (chartAt (H := ℂ) x).symm
      = (f.toFun ∘ (chartAt (H := ℂ) x).symm) * (g.toFun ∘ (chartAt (H := ℂ) x).symm) from rfl,
    meromorphicOrderAt_mul (f.meromorphic x) (g.meromorphic x)]
  rfl

/-- Products multiply linear systems: `L(E)·L(E') ⊆ L(E + E')`. -/
theorem mul_mem_linearSystem {E E' : Divisor X} {f g : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) E) (hg : g ∈ linearSystem (X := X) E') :
    f * g ∈ linearSystem (X := X) (E + E') := by
  intro x
  rw [MeromorphicFunction.orderW_mul, Finsupp.add_apply]
  refine le_trans (le_of_eq ?_) (add_le_add (hf x) (hg x))
  exact_mod_cast neg_add (E x) (E' x)

/-- The constant `1` lies in `L(E)` for every effective `E`. -/
theorem one_mem_linearSystem {E : Divisor X} (hE : 0 ≤ E) :
    (1 : MeromorphicFunction X) ∈ linearSystem (X := X) E := by
  intro x
  rw [MeromorphicFunction.orderW_one]
  have hx : (0 : ℤ) ≤ E x := by
    have := Finsupp.le_def.mp hE x
    simpa using this
  exact_mod_cast neg_nonpos.mpr hx

/-- Transport of linear-system membership along an equality of divisors (the divisor appears in
dependent positions at call sites, so a plain `rw` can fail the motive check; this helper rewrites
at the statement level, where `f` is opaque). -/
theorem linearSystem_congr {E E' : Divisor X} (h : E = E') {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) E) : f ∈ linearSystem (X := X) E' := h ▸ hf

/-- **`f⁻¹·f − 1` is germ-zero** for a non-germ-zero `f`: off the (isolated) zeros of `f.toFun`
the product is exactly `1`. -/
theorem orderW_inv_mul_sub_one {f : MeromorphicFunction X} (hne : ∀ x, f.orderW x ≠ ⊤) (x : X) :
    (f⁻¹ * f - 1).orderW x = ⊤ := by
  rw [MeromorphicFunction.orderW_eq_top_iff]
  have hev : ∀ᶠ z in 𝓝[≠] x, f.toFun z ≠ 0 := (MeromorphicFunction.orderW_ne_top_iff f x).mp (hne x)
  filter_upwards [hev] with z hz
  show (f⁻¹ * f - 1).toFun z = 0
  rw [MeromorphicFunction.sub_toFun, MeromorphicFunction.mul_toFun, MeromorphicFunction.inv_toFun,
    MeromorphicFunction.one_toFun]
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.inv_apply]
  rw [inv_mul_cancel₀ hz, sub_self]

variable [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ) ω X]

/-- The divisor `div f` reads the germ-order: at every point `(div f) x = untop₀ (orderW f x)`. -/
theorem MeromorphicFunction.div_apply_eq_untop₀ (f : MeromorphicFunction X) (x : X) :
    MeromorphicFunction.div X f x = (f.orderW x).untop₀ := by
  show Finsupp.ofSupportFinite (MeromorphicFunction.orderAtPoint f) _ x = _
  rw [Finsupp.ofSupportFinite_coe]
  rfl

/-- For a non-germ-zero `f`, the order at every point is the (finite) divisor coefficient. -/
theorem MeromorphicFunction.orderW_eq_div {f : MeromorphicFunction X}
    (hne : ∀ x, f.orderW x ≠ ⊤) (x : X) :
    f.orderW x = ((MeromorphicFunction.div X f x : ℤ) : WithTop ℤ) := by
  rw [MeromorphicFunction.div_apply_eq_untop₀]
  lift f.orderW x to ℤ using hne x with a ha
  simp

/-- **The reciprocal lies in `L(div f)`**: `orderW (f⁻¹) = −orderW f = −div f ≥ −div f`. -/
theorem inv_mem_linearSystem_div {f : MeromorphicFunction X} (hne : ∀ x, f.orderW x ≠ ⊤) :
    f⁻¹ ∈ linearSystem (X := X) (MeromorphicFunction.div X f) := by
  intro x
  rw [MeromorphicFunction.orderW_inv, MeromorphicFunction.orderW_eq_div hne x]

/-- For `f ∈ L(E)` (non-germ-zero), the divisor `E + div f` is effective. -/
theorem effective_add_div {E : Divisor X} {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) E) (hne : ∀ x, f.orderW x ≠ ⊤) :
    0 ≤ E + MeromorphicFunction.div X f := by
  rw [Finsupp.le_def]
  intro x
  rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.add_apply]
  have hx := hf x
  rw [MeromorphicFunction.orderW_eq_div hne x] at hx
  have hcoe : -(E x) ≤ MeromorphicFunction.div X f x := by exact_mod_cast hx
  omega

variable [ConnectedSpace X]

namespace Dolbeault

/-! ### Multiplicativity of the cup action on `H¹` -/

variable {𝔘 : FiniteFamily X}

/-- `globalGerm` is **multiplicative** in the meromorphic function. -/
theorem globalGerm_mul {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (f g : MeromorphicFunction X) (U : Opens X) :
    globalGerm (f * g) U = globalGerm f U * globalGerm g U := rfl

/-- `globalGerm` of the constant `1` is the unit germ. -/
theorem globalGerm_one {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (U : Opens X) :
    globalGerm (1 : MeromorphicFunction X) U = 1 := rfl

/-- `globalGerm` is **subtractive** in the meromorphic function. -/
theorem globalGerm_sub {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (f g : MeromorphicFunction X) (U : Opens X) :
    globalGerm (f - g) U = globalGerm f U - globalGerm g U := by
  have h1 : f - g = f + (-1 : ℂ) • g := by
    rw [neg_one_smul, sub_eq_add_neg]
  rw [h1, globalGerm_add, globalGerm_smul, neg_one_smul, ← sub_eq_add_neg]

/-- **The cup action is multiplicative**: `g ⌣ (f ⌣ ξ) = (g·f) ⌣ ξ` (germ multiplication is
associative). -/
theorem cupH1_mul {D K K' : Divisor X} {f g : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) (K - D)) (hg : g ∈ linearSystem (X := X) (K' - K))
    (hgf : g * f ∈ linearSystem (X := X) (K' - D)) (ξ : 𝔘.cechH1 D) :
    cupH1 hg (cupH1 hf ξ) = cupH1 hgf ξ := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [cupH1_mk, cupH1_mk, cupH1_mk]
  congr 1
  apply Subtype.ext
  show cupCochain1 𝔘 g (cupCochain1 𝔘 f (c : 𝔘.Cochain1)) = cupCochain1 𝔘 (g * f) (c : 𝔘.Cochain1)
  funext p
  simp only [cupCochain1_apply, globalGerm_mul, mul_assoc]

/-- **Cup with the constant `1` is the inclusion-induced map** `h1Incl`. -/
theorem cupH1_one_eq_h1Incl {𝔘 : FiniteCover X} {D K : Divisor X} (hDK : D ≤ K)
    (h1m : (1 : MeromorphicFunction X) ∈ linearSystem (X := X) (K - D)) (ξ : 𝔘.cechH1 D) :
    cupH1 h1m ξ = 𝔘.h1Incl hDK ξ := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [cupH1_mk, FiniteCover.h1Incl_mk]
  congr 1
  apply Subtype.ext
  show cupCochain1 𝔘.toFiniteFamily 1 (c : 𝔘.Cochain1) = (c : 𝔘.Cochain1)
  funext p
  rw [cupCochain1_apply, globalGerm_one, one_mul]

/-- **The cup action only sees the germ**: germ-equal multipliers give equal cup actions. -/
theorem cupH1_congr_germ {D K : Divisor X} {f f' : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) (K - D)) (hf' : f' ∈ linearSystem (X := X) (K - D))
    (h : ∀ x, (f - f').orderW x = ⊤) (ξ : 𝔘.cechH1 D) :
    cupH1 hf ξ = cupH1 hf' ξ := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [cupH1_mk, cupH1_mk]
  congr 1
  apply Subtype.ext
  show cupCochain1 𝔘 f (c : 𝔘.Cochain1) = cupCochain1 𝔘 f' (c : 𝔘.Cochain1)
  funext p
  simp only [cupCochain1_apply]
  have hzero := globalGerm_eq_zero_of_germZero h (𝔘.U p.1 ⊓ 𝔘.U p.2)
  rw [globalGerm_sub] at hzero
  rw [sub_eq_zero.mp hzero]

/-! ### The kill lemma: every `H¹(𝒪)` class dies in some effective enlargement -/

/-- **The kill lemma (Miranda Ch. X §2 / the Forster §16–17 pigeonhole).**  For a locally
realizable cover, every class `ξ ∈ H¹(𝔘, 𝒪)` has an effective divisor `A` (depending on `ξ`)
whose inclusion-induced map kills it: `H¹(𝒪) → H¹(𝒪_A)`, `ξ ↦ 0`.

`A = h¹(0)·P + div f` where `f ∈ L(h¹(0)·P)` is a pigeonhole kernel element of the cup action
`f ↦ f ⌣ ξ` (which exists since `l(h¹(0)·P) > h¹(h¹(0)·P)` by cohomological Riemann–Roch). -/
theorem exists_effective_h1Incl_eq_zero (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    (ξ : 𝔘.cechH1 (0 : Divisor X)) :
    ∃ (A : Divisor X) (h0A : (0 : Divisor X) ≤ A), 𝔘.h1Incl h0A ξ = 0 := by
  classical
  obtain ⟨P⟩ := (inferInstance : Nonempty X)
  set K₁ : Divisor X := Finsupp.single P (𝔘.h1Dim 0 : ℤ) with hK₁
  have hsub0 : K₁ - 0 = K₁ := sub_zero K₁
  -- dimension count: `l(K₁ − 0) > h¹(K₁)` from cohomological RR at `K₁`.
  have hRR := cohomological_riemannRoch 𝔘 hR K₁
  rw [𝔘.h0Dim_eq_lDim K₁,
    show Divisor.deg X K₁ = (𝔘.h1Dim 0 : ℤ) from by rw [hK₁, Divisor.deg_single]] at hRR
  have hdim : 𝔘.h1Dim K₁ < lDim (X := X) (K₁ - 0) := by
    rw [hsub0]
    omega
  -- the pigeonhole: the cup action `f ↦ f ⌣ ξ` on `L(K₁)` has a nonzero kernel class.
  set φ : lSysModule (X := X) (K₁ - 0) →ₗ[ℂ] 𝔘.cechH1 K₁ :=
    (cup (𝔘 := 𝔘.toFiniteFamily) 0 K₁).flip ξ with hφ
  haveI := finiteDimensional_cechH1_general 𝔘 K₁
  have hker : ∃ F : lSysModule (X := X) (K₁ - 0), F ≠ 0 ∧ φ F = 0 := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective φ := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro F hF
      by_contra hFne
      exact hcon F hFne (LinearMap.mem_ker.mp hF)
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [show Module.finrank ℂ (lSysModule (X := X) (K₁ - 0)) = lDim (X := X) (K₁ - 0) from rfl,
      show Module.finrank ℂ (𝔘.cechH1 K₁) = 𝔘.h1Dim K₁ from rfl] at hle
    omega
  obtain ⟨F, hFne, hFzero⟩ := hker
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ F
  -- the kernel element is not germ-zero, hence (identity theorem) nowhere germ-zero.
  have hex : ∃ x, (f : MeromorphicFunction X).orderW x ≠ ⊤ := by
    by_contra hcon
    push Not at hcon
    refine hFne ((Submodule.Quotient.mk_eq_zero _).mpr ?_)
    rw [Submodule.submoduleOf, Submodule.mem_comap]
    exact fun x => hcon x
  have hne : ∀ x, (f : MeromorphicFunction X).orderW x ≠ ⊤ :=
    fun x => MeromorphicFunction.orderW_ne_top_of_exists _ hex x
  -- the cup vanishing `f ⌣ ξ = 0`.
  have hcup : cupH1 (𝔘 := 𝔘.toFiniteFamily) f.2 ξ = 0 := by
    have h := hFzero
    rw [hφ, LinearMap.flip_apply, cup_mk] at h
    exact h
  -- divide back by `f⁻¹ ∈ L(div f)`.
  set A : Divisor X := K₁ + MeromorphicFunction.div X (f : MeromorphicFunction X) with hA
  have hfmem : (f : MeromorphicFunction X) ∈ linearSystem (X := X) K₁ :=
    linearSystem_congr hsub0 f.2
  have h0A : (0 : Divisor X) ≤ A := effective_add_div hfmem hne
  have hinvmem : (f : MeromorphicFunction X)⁻¹ ∈ linearSystem (X := X) (A - K₁) := by
    rw [hA, add_sub_cancel_left]
    exact inv_mem_linearSystem_div hne
  have hprod : (f : MeromorphicFunction X)⁻¹ * (f : MeromorphicFunction X)
      ∈ linearSystem (X := X) (A - 0) :=
    linearSystem_congr (show (A - K₁) + K₁ = A - 0 from by abel)
      (mul_mem_linearSystem hinvmem hfmem)
  have hone : (1 : MeromorphicFunction X) ∈ linearSystem (X := X) (A - 0) :=
    one_mem_linearSystem (by rw [sub_zero]; exact h0A)
  refine ⟨A, h0A, ?_⟩
  calc 𝔘.h1Incl h0A ξ
      = cupH1 hone ξ := (cupH1_one_eq_h1Incl h0A hone ξ).symm
    _ = cupH1 hprod ξ :=
        (cupH1_congr_germ hprod hone (fun x => orderW_inv_mul_sub_one hne x) ξ).symm
    _ = cupH1 hinvmem (cupH1 f.2 ξ) := (cupH1_mul f.2 hinvmem hprod ξ).symm
    _ = cupH1 hinvmem 0 := by rw [hcup]
    _ = 0 := map_zero _

end Dolbeault

end Jacobians
