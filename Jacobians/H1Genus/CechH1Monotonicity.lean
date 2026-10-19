/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# The inclusion-induced maps `H¹(𝒪_D) → H¹(𝒪_{D'})` for `D ≤ D'` and their surjectivity

`SkyscraperLESBase` provides the **single-point** inclusion arrow `h1Map D P : H¹(𝒪_D) →
H¹(𝒪_{D+P})` together with (via `exists_skyscraperLES`) its surjectivity.  This file generalises
to an arbitrary pair `D ≤ D'` (Forster Corollary 16.8): the order bound only weakens, so the
cocycle/coboundary submodules grow monotonically, the quotient map `h1Incl` descends, composition
is functorial, and surjectivity follows by induction on the degree of the (effective) difference
`D' − D`, one point at a time.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), 16.7–16.8 (pp. 129).
-/
import Jacobians.Finiteness.CohomologicalRR

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)


namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace FiniteCover

open FiniteFamily

/-! ### Monotonicity of the section/cocycle/coboundary submodules in the divisor -/

/-- The order bound for `𝒪_D` implies that for `𝒪_{D'}` whenever `D ≤ D'` (the bound `−D' ≤ −D`
weakens).  Generalises `mem_OmegaD_add_single`. -/
theorem mem_OmegaD_mono {D D' : Divisor X} (h : D ≤ D') {U : Opens X} {f : U → ℂ}
    (hf : f ∈ OmegaD D U) : f ∈ OmegaD D' U := by
  refine ⟨hf.1, fun u => le_trans ?_ (hf.2 u)⟩
  exact_mod_cast neg_le_neg (h u.1)

/-- Germ-class sections inherit the inclusion `𝒪_D(U) ⊆ 𝒪_{D'}(U)` for `D ≤ D'`. -/
theorem OmegaDGerm_mono {D D' : Divisor X} (h : D ≤ D') (U : Opens X) :
    OmegaDGerm D U ≤ OmegaDGerm D' U := by
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, mem_OmegaD_mono h hg, rfl⟩

variable (𝔘 : FiniteCover X)

/-- The `𝒪_D` 0-sections are contained in the `𝒪_{D'}` 0-sections for `D ≤ D'`. -/
theorem sections0_mono {D D' : Divisor X} (h : D ≤ D') :
    𝔘.sections0 D ≤ 𝔘.sections0 D' :=
  fun _ hf i => OmegaDGerm_mono h (𝔘.U i) (hf i)

/-- The `𝒪_D` 1-sections are contained in the `𝒪_{D'}` 1-sections for `D ≤ D'`. -/
theorem sections1_mono {D D' : Divisor X} (h : D ≤ D') :
    𝔘.sections1 D ≤ 𝔘.sections1 D' :=
  fun _ hf p => OmegaDGerm_mono h _ (hf p)

/-- The `𝒪_D` 1-cocycles are contained in the `𝒪_{D'}` 1-cocycles for `D ≤ D'`. -/
theorem cocycles1_mono {D D' : Divisor X} (h : D ≤ D') :
    𝔘.cocycles1 D ≤ 𝔘.cocycles1 D' :=
  inf_le_inf_left _ (𝔘.sections1_mono h)

/-- The `𝒪_D` 1-coboundaries are contained in the `𝒪_{D'}` 1-coboundaries for `D ≤ D'`. -/
theorem coboundaries1_mono {D D' : Divisor X} (h : D ≤ D') :
    𝔘.coboundaries1 D ≤ 𝔘.coboundaries1 D' :=
  Submodule.map_mono (𝔘.sections0_mono h)

/-! ### The inclusion-induced map on `H¹` and its functoriality -/

/-- The 1-cocycle inclusion `Z¹(𝒪_D) ↪ Z¹(𝒪_{D'})` for `D ≤ D'`. -/
noncomputable def cocyclesInclMono {D D' : Divisor X} (h : D ≤ D') :
    ↥(𝔘.cocycles1 D) →ₗ[ℂ] ↥(𝔘.cocycles1 D') :=
  Submodule.inclusion (𝔘.cocycles1_mono h)

/-- **The inclusion-induced arrow `H¹(𝒪_D) → H¹(𝒪_{D'})`** for `D ≤ D'` (generalising the
single-point `h1Map`): the cocycle inclusion descends through the `Z¹/B¹` quotients. -/
noncomputable def h1Incl {D D' : Divisor X} (h : D ≤ D') :
    𝔘.cechH1 D →ₗ[ℂ] 𝔘.cechH1 D' := by
  refine Submodule.mapQ _ _ (𝔘.cocyclesInclMono h) ?_
  rintro ⟨c, _⟩ hcob
  exact 𝔘.coboundaries1_mono h hcob

@[simp] theorem h1Incl_mk {D D' : Divisor X} (h : D ≤ D') (c : ↥(𝔘.cocycles1 D)) :
    𝔘.h1Incl h (Submodule.Quotient.mk c)
      = Submodule.Quotient.mk (𝔘.cocyclesInclMono h c) :=
  rfl

/-- `h1Incl` along `D ≤ D` is the identity. -/
theorem h1Incl_refl (D : Divisor X) (h : D ≤ D) :
    𝔘.h1Incl h = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- Functoriality: `h1Incl (D₂ ≤ D₃) ∘ h1Incl (D₁ ≤ D₂) = h1Incl (D₁ ≤ D₃)`. -/
theorem h1Incl_comp {D₁ D₂ D₃ : Divisor X} (h₁ : D₁ ≤ D₂) (h₂ : D₂ ≤ D₃) (x : 𝔘.cechH1 D₁) :
    𝔘.h1Incl h₂ (𝔘.h1Incl h₁ x) = 𝔘.h1Incl (h₁.trans h₂) x := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- The general inclusion arrow at a single-point step agrees with `h1Map` (same underlying
`Submodule.inclusion`). -/
theorem h1Incl_eq_h1Map (D : Divisor X) (P : X)
    (h : D ≤ D + Finsupp.single P 1) :
    𝔘.h1Incl h = 𝔘.h1Map D P := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-! ### Surjectivity (Forster 16.8) -/

/-- Single-point surjectivity, with the target divisor given by an equation `D' = D + P` (so the
statement composes cleanly in the degree induction): the inclusion-induced `H¹(𝒪_D) → H¹(𝒪_{D'})`
is onto, by the skyscraper long exact sequence. -/
theorem h1Incl_surjective_single (hR : 𝔘.LocallyRealizable) {D D' : Divisor X} {P : X}
    (hD' : D' = D + Finsupp.single P 1) (h : D ≤ D') :
    Function.Surjective (𝔘.h1Incl h) := by
  subst hD'
  rw [𝔘.h1Incl_eq_h1Map D P h]
  exact (𝔘.exists_skyscraperLES hR D P).elim fun S => S.surj₄

/-- A nonzero effective divisor has a point with a positive coefficient. -/
theorem exists_pos_of_effective_ne_zero {X : Type*} {E : Divisor X} (hE : 0 ≤ E)
    (hne : E ≠ 0) :
    ∃ P : X, 1 ≤ E P := by
  by_contra hcon
  push Not at hcon
  refine hne (Finsupp.ext fun x => ?_)
  have h0 := hE x
  have h1 := hcon x
  rw [Finsupp.coe_zero, Pi.zero_apply] at h0 ⊢
  omega

/-- The degree of an effective divisor is nonnegative. -/
theorem deg_nonneg_of_effective {X : Type*} {E : Divisor X} (hE : 0 ≤ E) :
    0 ≤ Divisor.deg X E := by
  rw [show Divisor.deg X E = Finsupp.degree E from rfl, Finsupp.degree_apply]
  exact Finset.sum_nonneg fun x _ => hE x

/-- An effective divisor of degree `0` is `0`. -/
theorem eq_zero_of_effective_deg_zero {X : Type*} {E : Divisor X} (hE : 0 ≤ E)
    (hdeg : Divisor.deg X E = 0) : E = 0 := by
  rw [show Divisor.deg X E = Finsupp.degree E from rfl, Finsupp.degree_apply] at hdeg
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hE x).mp hdeg
  refine Finsupp.ext fun x => ?_
  by_cases hx : x ∈ E.support
  · exact hall x hx
  · exact Finsupp.notMem_support_iff.mp hx

/-- **Surjectivity of the inclusion-induced `H¹` map (Forster 16.8).**  For a locally realizable
cover and `D ≤ D'`, the map `H¹(𝒪_D) → H¹(𝒪_{D'})` is onto: induct on the degree of the
effective difference `D' − D`, peeling one point per step via the skyscraper LES. -/
theorem h1Incl_surjective (hR : 𝔘.LocallyRealizable) {D D' : Divisor X} (h : D ≤ D') :
    Function.Surjective (𝔘.h1Incl h) := by
  classical
  -- induct on the (nonnegative) degree of the difference.
  generalize hn : (Divisor.deg X (D' - D)).toNat = n
  induction n generalizing D D' with
  | zero =>
    -- difference is effective of degree 0, hence 0, hence D' = D.
    have heff : 0 ≤ D' - D := by
      rw [Finsupp.le_def]
      intro x
      rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.sub_apply]
      have := Finsupp.le_def.mp h x
      omega
    have hdeg0 : Divisor.deg X (D' - D) = 0 := by
      have hnn := deg_nonneg_of_effective heff
      omega
    have hDD' : D' = D := by
      have := eq_zero_of_effective_deg_zero heff hdeg0
      have := sub_eq_zero.mp this
      exact this
    subst hDD'
    rw [𝔘.h1Incl_refl D' h]
    exact Function.surjective_id
  | succ n ih =>
    -- peel one point P with (D' − D) P ≥ 1.
    have heff : 0 ≤ D' - D := by
      rw [Finsupp.le_def]
      intro x
      rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.sub_apply]
      have := Finsupp.le_def.mp h x
      omega
    have hne : D' - D ≠ 0 := by
      intro h0
      rw [h0, Divisor.deg_zero] at hn
      simp at hn
    obtain ⟨P, hP⟩ := exists_pos_of_effective_ne_zero heff hne
    rw [Finsupp.sub_apply] at hP
    set D'' : Divisor X := D' - Finsupp.single P 1 with hD''
    have h₁ : D ≤ D'' := by
      rw [Finsupp.le_def]
      intro x
      rw [hD'', Finsupp.sub_apply, Finsupp.single_apply]
      have hx := Finsupp.le_def.mp h x
      by_cases hPx : P = x
      · subst hPx; rw [if_pos rfl]; omega
      · rw [if_neg hPx]; omega
    have h₂ : D'' ≤ D' := by
      rw [Finsupp.le_def]
      intro x
      rw [hD'', Finsupp.sub_apply, Finsupp.single_apply]
      by_cases hPx : P = x
      · subst hPx; rw [if_pos rfl]; omega
      · rw [if_neg hPx]; omega
    have hD'eq : D' = D'' + Finsupp.single P 1 := by
      rw [hD'']
      abel
    have hdeg'' : (Divisor.deg X (D'' - D)).toNat = n := by
      have : D'' - D = (D' - D) - Finsupp.single P 1 := by rw [hD'']; abel
      rw [this, Divisor.deg_sub, Divisor.deg_single]
      have hnn := deg_nonneg_of_effective heff
      omega
    have hsurj₁ := ih h₁ hdeg''
    have hsurj₂ := 𝔘.h1Incl_surjective_single hR hD'eq h₂
    intro y
    obtain ⟨z, hz⟩ := hsurj₂ y
    obtain ⟨w, hw⟩ := hsurj₁ z
    exact ⟨w, by rw [← 𝔘.h1Incl_comp h₁ h₂ w, hw, hz]⟩

end FiniteCover

end Jacobians.Dolbeault
