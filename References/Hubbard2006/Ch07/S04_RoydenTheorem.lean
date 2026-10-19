import References.Common.HyperbolicSurface
import References.ImayoshiTaniguchi1992.Ch06.S04_Royden

/-!
# Hubbard 2006, Chapter 7 §7.4: Royden's theorem on automorphisms of Teichmüller spaces (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H2` lines 3932–4335.

**Conventions.** As in `ImayoshiTaniguchi1992.Ch06.S04_Royden`: `𝒯_S` is `LiZhongQC.TeichGamma Γ` for the Fuchsian model
`Γ` of a Riemann surface `S = ℍ/Γ`, its complex structure is the Bers one (`GardinerLakic2000.IsHolAutT`: a bijection
which, with its inverse, maps holomorphic discs to holomorphic discs), `MCG(S)` is `GardinerLakic2000.mcgGamma Γ` and
the
action `[ω]_*` of a mapping class is `GardinerLakic2000.IsRhoGamma`. A Riemann surface of finite type `(g, n, 0)` (genus
`g`, `n` punctures, no holes) has `dim 𝒯_S = 3g − 3 + n`. Quadratic differentials of a compact surface are
`LiZhongQC.holQuadDiffSubmodule` (all integrable); the order of a vanishing at `y` is the analytic order of the local
coefficient in the preferred chart at `y`.

* Thm 7.4.1 (Royden's theorem: for `1 < dim 𝒯_S < ∞` the group of complex-analytic automorphisms of `𝒯_S` is `MCG(S)`) —
  `thm7_4_1`
* Prop. 7.4.15 (a compact surface of genus `≥ 3`: `Q¹(X)` is base-point free, and each point has a line of quadratic
  differentials vanishing at it to higher order than at any other point; the assignment is injective) — `qdOrderAt`,
  `prop7_4_15`
* Prop. 7.4.2 (the transpose of the derivative of an automorphism is an isometry `Q¹(X₂) → Q¹(X₁)`) — deferred: needs
  the differential of the Bers chart (tangent spaces of `𝒯_S`)
* Lemmas 7.4.3, 7.4.5, Prop. 7.4.4 (the derivative of the `L¹` norm, an estimate for `arg`), Def. 7.4.6–7.4.10 (skew
  curves, flags, Grassmannians, osculating flags), Prop. 7.4.11, 7.4.14, Example 7.4.12 — omitted: proof step
* Exercises 7.4.9, 7.4.13 — omitted: exercise
-/

open Set
open scoped Manifold ContDiff

namespace Hubbard2006

open LiZhongQC GardinerLakic2000

/-- **Theorem 7.4.1 (Royden's theorem)** (H2:3952), for surfaces of finite type with punctures. Let `S = ℍ/Γ` be a
Riemann surface of finite type `(g, n, 0)` with `1 < dim 𝒯_S = 3g − 3 + n`. Then the map `[ω] ↦ [ω]_* = ρ_ω` from
`MCG(S)` to the group of biholomorphic automorphisms of `𝒯_S` is surjective (except for `(g, n) = (1, 2)`), and its
kernel
has one element, except for `(g, n) = (2, 0)` and `(1, 2)`, where it has exactly two (the hyperelliptic involution
acts trivially on `𝒯_S`). *Corrections to the book:* "the group of automorphisms is `MCG(S)`" holds only modulo this
kernel, and fails to be onto for `(g, n) = (1, 2)`: `𝒯_{1,2} ≅ 𝒯_{0,5}` (Patterson, Earle–Kra), whose automorphism
group `MCG(0, 5)` contains the image of `MCG(1, 2)/⟨ι⟩` with index `5`; for `n = 0` the statement is
`ImayoshiTaniguchi1992.thm6_20_a`, `thm6_20_b` (near misses: closed surfaces only). -/
theorem thm7_4_1 {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} {g n : ℕ}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hS : IsFiniteType S g n 0)
    (hdim : 5 ≤ 3 * g + n) :
    ∃ i : mcgGamma Γ → {F : TeichGamma Γ → TeichGamma Γ // IsHolAutT Γ Γ F},
      (¬ (g = 1 ∧ n = 2) → Function.Surjective i) ∧
      (∀ (w : ℂ → ℂ) (hw : w ∈ qcNormalizer Γ), IsRhoGamma Γ Γ w (i (Quot.mk _ ⟨w, hw⟩)).1) ∧
        Set.ncard {c : mcgGamma Γ | (i c).1 = id} = if (g = 2 ∧ n = 0) ∨ (g = 1 ∧ n = 2) then 2 else 1 := by
  sorry

/-- **The order of vanishing at `y`** of a quadratic differential `q` on a Riemann surface (the analytic order of its
local coefficient at the centre of the preferred chart at `y`). -/
noncomputable def qdOrderAt {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (q : X → ℂ → ℂ) (y : X) : ℕ∞ :=
  analyticOrderAt (q y) (chartAt ℂ y y)

/-- **Proposition 7.4.15** (H2:4270). Let `X` be a compact Riemann surface of genus `g ≥ 3`. (1) For every `x ∈ X`
there is
a holomorphic quadratic differential `q` with `q(x) ≠ 0`. (2) For every `x ∈ X` there is a line `L_X(x) ⊂ Q¹(X)` such
that every `q ∈ L_X(x) ∖ {0}` has a zero of higher order at `x` than at any other point of `X`; and (3) the map
`L_X : X → ℙ(Q¹(X))` is injective. (Its analyticity is not stated: `ℙ(Q¹(X))` has no manifold structure in the
project.) -/
theorem prop7_4_15 {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {g : ℕ} (hX : HasGenus X g) (hg : 3 ≤ g) :
    (∀ x : X, ∃ q ∈ holQuadDiffSubmodule X, q x (chartAt ℂ x x) ≠ 0) ∧
      ∃ L : X → Submodule ℂ (X → ℂ → ℂ), (∀ x, L x ≤ holQuadDiffSubmodule X ∧ Module.finrank ℂ (L x) = 1 ∧
        ∀ q ∈ L x, q ≠ 0 → ∀ y, y ≠ x → qdOrderAt q y < qdOrderAt q x) ∧ Function.Injective L := by
  sorry

end Hubbard2006
