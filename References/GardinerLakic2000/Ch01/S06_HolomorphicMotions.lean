import References.GardinerLakic2000.Ch01.S05_BeltramiEquation

/-!
# Gardiner–Lakic 2000, Ch. 1 §1.6 Holomorphic motions

Source `teichmuller.txt`, lines 871–906 (Chapter 1, §1.6).

* Definition 5 (holomorphic motion of `ℂ̄`, normalized, l. 880) and Definition 6 (holomorphic motion of a closed set,
  l. 889) — `IsHolMotion`, `IsNormalizedHolMotion`
* Definition (part of a holomorphic motion, l. 882; used in Ch. 14) — `IsPartOfHolMotion`
* Theorem 2 (Mañé–Sad–Sullivan, l. 886; cited in Ch. 3, 9) — `thm1_2_a`, `thm1_2_b`
* Theorem 3 (Slodkowski, l. 897; cited ten times) — `thm1_3`
* Theorem 4 (l. 901) — `thm1_4`

Not items: "every quasiconformal map is part of a holomorphic motion" (l. 882, U−; from Theorem 1); the announcement of
equicontinuity (l. 899). Modelling: a motion is a family `f t : ℂ → ℂ` for `t` in the unit disc (values for
`|t| ≥ 1` are junk); the point `∞` is fixed implicitly (the book's `f_t(∞) = ∞`). In Theorem 4 the set `Λ ⊆ ℂ̄`
contains `∞`; here `Λ ⊆ ℂ` and `∞` is the fixed point at infinity. Theorem 2's "holomorphic into the unit ball of
`L∞`" is read weakly, `t ↦ ∬ μ_t φ` holomorphic for every `φ ∈ L¹` (leader ruling A0.6; with `‖μ_t‖∞ < 1`
this is equivalent). Theorems 2 and 3 are stated for motions with `f_t(∞) = ∞` (values in `ℂ`): by Mañé–Sad–Sullivan every `f_t` is a homeomorphism of `ℂ̄`, so a
`ℂ`-valued motion fixes `∞`; the book's versions also cover motions in which `∞` moves [scope, AUDIT4 G11; the case used in Ch. 3, 14 is `∞` fixed]. Theorem 4: "a constant `C` depending only on `R`" is read as `C = C(R, t)` for each `t`
[reading]: normalized `K`-quasiconformal maps are unbounded on `|z| ≤ R` as `K → ∞`, so no `C` uniform in `t` exists.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (IsKQC complexDilatation)

/-- **Definition 6** (§1.6, l. 889), and **Definition 5** for `Λ = ℂ` (l. 880). `f t` (`|t| < 1`) is a holomorphic
motion of `Λ` parametrized by the unit disc: (1) `f 0 = id` on `Λ`; (2) each `f t` is injective on `Λ`; (3) for each
`z ∈ Λ`, `t ↦ f t z` is holomorphic on the unit disc. -/
def IsHolMotion (Λ : Set ℂ) (f : ℂ → ℂ → ℂ) : Prop :=
  (∀ z ∈ Λ, f 0 z = z) ∧ (∀ t ∈ ball (0 : ℂ) 1, InjOn (f t) Λ) ∧
    ∀ z ∈ Λ, DifferentiableOn ℂ (fun t => f t z) (ball 0 1)

/-- **Definition 5** (§1.6, l. 880), normalized motions: property (iv), each `f t` fixes `0` and `1` (and `∞`). -/
def IsNormalizedHolMotion (Λ : Set ℂ) (f : ℂ → ℂ → ℂ) : Prop :=
  IsHolMotion Λ f ∧ ∀ t ∈ ball (0 : ℂ) 1, f t 0 = 0 ∧ f t 1 = 1

/-- **Definition** (§1.6, l. 882). A map `g` is part of a holomorphic motion if `g = f_{t₀}` for a holomorphic motion
`f` of `ℂ̄` and some `|t₀| < 1`. -/
def IsPartOfHolMotion (g : ℂ → ℂ) : Prop :=
  ∃ f : ℂ → ℂ → ℂ, IsHolMotion univ f ∧ ∃ t₀ ∈ ball (0 : ℂ) 1, g = f t₀

/-- **Theorem 2** (Mañé, Sad and Sullivan, §1.6, l. 886), first part. Every `f_{t₀}` of a holomorphic motion of `ℂ̄`
is quasiconformal with `K(f_{t₀}) ≤ (1 + |t₀|)/(1 − |t₀|)`. -/
theorem thm1_2_a {f : ℂ → ℂ → ℂ} (hf : IsHolMotion univ f) {t₀ : ℂ} (ht₀ : t₀ ∈ ball (0 : ℂ) 1) :
    IsKQC (f t₀) univ ((1 + ‖t₀‖) / (1 - ‖t₀‖)) ∧ f t₀ '' univ = univ := by
  sorry

/-- **Theorem 2** (§1.6, l. 886), second part. The Beltrami coefficients `μ_t` of `f_t` depend holomorphically on `t`
(weak reading: `t ↦ ∬ μ_t φ` is holomorphic on the unit disc for every integrable `φ`). -/
theorem thm1_2_b {f : ℂ → ℂ → ℂ} (hf : IsHolMotion univ f) {φ : ℂ → ℂ} (hφ : Integrable φ) :
    DifferentiableOn ℂ (fun t => ∫ z, complexDilatation (f t) z * φ z) (ball 0 1) := by
  sorry

/-- **Theorem 3** (Slodkowski, §1.6, l. 897). A holomorphic motion of a closed set `Λ ⊆ ℂ` extends to a holomorphic
motion of `ℂ̄` parametrized by the same disc. -/
theorem thm1_3 {Λ : Set ℂ} (hΛ : IsClosed Λ) {f : ℂ → ℂ → ℂ} (hf : IsHolMotion Λ f) :
    ∃ F : ℂ → ℂ → ℂ, IsHolMotion univ F ∧ ∀ t ∈ ball (0 : ℂ) 1, ∀ z ∈ Λ, F t z = f t z := by
  sorry

/-- **Theorem 4** (§1.6, l. 901). A normalized holomorphic motion of a closed set containing `0, 1, ∞` is Hölder
continuous with exponent `(1 − |t|)/(1 + |t|)` on bounded sets: for `|z|, |w| ≤ R`,
`|f_t(z) − f_t(w)| ≤ C |z − w|^{(1−|t|)/(1+|t|)}` (`C = C(R, t)`, see the module docstring).
[CORRECTION] (AUDIT4 G10) `C` is chosen before `Λ` and `f` (it depends only on `R` and `t`, as in the book); with `∃ C` after `Λ, f` the
statement was the much weaker Hölder continuity of a single motion. `∞ ∈ Λ` is implicit (`f_t(∞) = ∞`). -/
theorem thm1_4 {t : ℂ} (ht : t ∈ ball (0 : ℂ) 1) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, ∀ (Λ : Set ℂ), IsClosed Λ → (0 : ℂ) ∈ Λ → (1 : ℂ) ∈ Λ → ∀ (f : ℂ → ℂ → ℂ), IsNormalizedHolMotion Λ f →
      ∀ z ∈ Λ, ∀ w ∈ Λ, ‖z‖ ≤ R → ‖w‖ ≤ R →
        ‖f t z - f t w‖ ≤ C * ‖z - w‖ ^ ((1 - ‖t‖) / (1 + ‖t‖)) := by
  sorry

end GardinerLakic2000
