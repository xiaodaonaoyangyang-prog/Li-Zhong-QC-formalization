import References.Common.FenchelNielsen
import References.ImayoshiTaniguchi1992.Ch03.S02_FenchelNielsen

/-!
# Hubbard 2006, Chapter 7 §7.6: Fenchel–Nielsen coordinates

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H2` lines 4436–4604.

**Conventions.** `S₀` is a closed Riemann surface of genus `g ≥ 2` with a fixed uniformization `(Γ₀, p₀)` by a
torsion-free Fuchsian group (a hyperbolic surface); the Teichmüller space is `LiZhongQC.TeichSpace S₀` with the metric
`LiZhongQC.teichDistance`. **Teichmüller distance (D18):** Hubbard's `d` is `2 · LiZhongQC.teichDistance` (his
Def. 6.4.4, display (6.4.2), is `inf ln K`; the project's is `½ inf ln K`; see the module docstring of `Ch07/S02`).
Surfaces with punctures (finite type with cusps, trouser lengths `0`) are not treated: the statement `thm7_6_3'` for
them is deferred, because the installed datum `ImayoshiTaniguchi1992.IsAdjacentPantsDatum` is stated for closed surfaces
of genus `≥ 2` only.

*Lengths and twists.* The lengths `l_γ(τ)` and the twists `t_γ(τ)` are the relations `References.lengthOf` and
`References.twistOf` of `Common/FenchelNielsen.lean` (relations, because `Quot` has no choice-free evaluation); the
twist is Hubbard's signed `References.twistLength g a b`.

*The Fenchel–Nielsen datum.* The topological choices of Hubbard's construction (the maximal multicurve `Γ`, the arcs
`γ'`, the base points `p_γ`) become, in the base uniformization, a system of decomposing curves given by loops
`L : Fin (3g − 3) → Loop S₀` (`ImayoshiTaniguchi1992.IsDecomposingSystemLoops`, a maximal geodesic multicurve) and three
based loops `σg j, σa j, σb j` for each curve (`ImayoshiTaniguchi1992.IsAdjacentPantsDatum`): their lifts from one point
`z₀` end at `G, A, B ∈ Γ₀`, where `G` is the class of the curve `γ_j`, and `A`, `B` are the classes of the boundary
curves of the two adjacent lifted pants joined by the arc `γ'` through the base point of `γ_j`. The datum is installed
(Lane D owns it), so it is used here rather than redefined.

* Definition (the Fenchel–Nielsen datum) — exists: `ImayoshiTaniguchi1992.IsDecomposingSystemLoops`,
  `ImayoshiTaniguchi1992.IsAdjacentPantsDatum`
* Definition (length functions `l_γ(τ)`, display (7.6.1)) — exists: `References.lengthOf`, `References.IsLengthOfLoop`
* Proposition (the length relation is single valued: `l_γ(τ)` depends only on `τ`; H2:4470) — `prop7_6_0`
* Definition 7.6.1 (twist coordinates) — exists: `References.twistOf`, `References.IsTwistOfLoops`,
  `References.twistLength`
* Remark 7.6.2 (the sign of the twist does not depend on the end of the arc `γ'`) — `remark7_6_2`
* Theorem 7.6.3 (Fenchel–Nielsen coordinates: `FN : T_S → (ℝ₊*)^Γ × ℝ^Γ` is a homeomorphism) — `thm7_6_3`
* Theorem 7.6.3 for finite type with punctures (`thm7_6_3'`) — deferred: the installed datum is for closed surfaces
* Theorem 7.6.4 (the logarithms of the lengths are `1`-Lipschitz) — `thm7_6_4`
* Proposition 7.6.5 (the twists are continuous) — `prop7_6_5`
* Figures 7.6.1–7.6.8, the construction of the inverse and of the marking `φ_T` (7.6.7–7.6.10) — omitted: proof content
-/

open Set Filter Topology
open scoped Manifold ContDiff
open LiZhongQC References ImayoshiTaniguchi1992

namespace Hubbard2006

/-- **Proposition 7.6.0** (the length of a geodesic depends only on `τ`, Ch. 7 §7.6, H2:4470; "this geodesic clearly
depends only on `τ`"). If `ℓ₁` and `ℓ₂` are lengths of the geodesic of the loop `γ` for the class `τ`, then `ℓ₁ = ℓ₂`.
-/
theorem prop7_6_0 {S₀ : Type} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] (τ : TeichSpace S₀) (γ : Loop S₀) {ℓ₁ ℓ₂ : ℝ}
    (h₁ : lengthOf τ γ ℓ₁) (h₂ : lengthOf τ γ ℓ₂) : ℓ₁ = ℓ₂ := by
  sorry

/-- **Remark 7.6.2** (Ch. 7 §7.6, H2:4478). It does not matter which end of the arc `γ'` one starts at: the signed twist
is symmetric in the two sides. For a hyperbolic `g` and elements `a`, `b` lying on opposite sides of `axisH g` (with
unique foot points), `twistLength g a b = twistLength g b a`. -/
theorem remark7_6_2 {g a b : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg : IsHyperbolic g) (ha : ∃! q, IsFootPoint g a q)
    (hb : ∃! q, IsFootPoint g b q) (hs : sideSign g a = - sideSign g b) (hne : sideSign g a ≠ 0) :
    twistLength g a b = twistLength g b a := by
  sorry

variable {S₀ : Type} [TopologicalSpace S₀] [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [ChartedSpace ℂ S₀]
  [IsManifold 𝓘(ℂ) ω S₀]

/-- **Theorem 7.6.3** (Fenchel–Nielsen coordinates, Ch. 7 §7.6, H2:4486). Let `S₀` be a closed Riemann surface of genus
`g ≥ 2` with uniformization `(Γ₀, p₀)`, `L : Fin (3g − 3) → Loop S₀` a system of decomposing curves and `σg, σa, σb`
the loops of an adjacent-pants datum (see the module docstring). Then there is a map `FN = (FN_L, FN_T) : T_S →
(ℝ₊*)^{3g−3} × ℝ^{3g−3}` whose components are the lengths `l_{γ_j}(τ)` and the twists `t_{γ_j}(τ)` (the relations
`lengthOf`, `twistOf` hold), it is a bijection onto `(ℝ₊*)^{3g−3} × ℝ^{3g−3}`, and it is a homeomorphism: a sequence
`τ_n` converges to `τ` in the Teichmüller metric iff `FN τ_n` converges to `FN τ` in the product topology (both
topologies are metric, so this is the homeomorphism property for `FN` and `FN⁻¹`). -/
theorem thm7_6_3 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀)
    {L : Fin (3 * g - 3) → Loop S₀} (hL : IsDecomposingSystemLoops Γ₀ p₀ L) {x : S₀}
    {σg σa σb : Fin (3 * g - 3) → Path x x} (hD : IsAdjacentPantsDatum Γ₀ p₀ L σg σa σb) :
    ∃ FN : TeichSpace S₀ → (Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ),
      (∀ τ j, lengthOf τ (L j) ((FN τ).1 j) ∧ twistOf τ (σg j) (σa j) (σb j) ((FN τ).2 j)) ∧
      (∀ τ j, 0 < (FN τ).1 j) ∧ (∀ y : (Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ), (∀ j, 0 < y.1 j) → ∃! τ, FN τ = y) ∧
      ∀ (τ : TeichSpace S₀) (τs : ℕ → TeichSpace S₀),
        Tendsto (fun n => teichDistance (τs n) τ) atTop (𝓝 0) ↔ Tendsto (fun n => FN (τs n)) atTop (𝓝 (FN τ)) := by
  sorry

/-- **Theorem 7.6.4** (logarithms of lengths are `1`-Lipschitz, Ch. 7 §7.6, H2:4496). For a closed curve `γ` that is not
null-homotopic and classes `τ₁, τ₂` with geodesic lengths `ℓ₁, ℓ₂` of `γ`: `|ln ℓ₁ − ln ℓ₂| ≤ d(τ₁, τ₂) = 2 ·
teichDistance τ₁ τ₂` (D18; Hubbard's `d` is `inf ln K`, the project's `teichDistance` is half of it). -/
theorem thm7_6_4 (τ₁ τ₂ : TeichSpace S₀) (γ : Loop S₀) (hγ : ¬ FreelyHomotopic γ ⟨γ.1, Path.refl γ.1⟩) {ℓ₁ ℓ₂ : ℝ}
    (h₁ : lengthOf τ₁ γ ℓ₁) (h₂ : lengthOf τ₂ γ ℓ₂) (hℓ₁ : 0 < ℓ₁) (hℓ₂ : 0 < ℓ₂) :
    |Real.log ℓ₁ - Real.log ℓ₂| ≤ 2 * teichDistance τ₁ τ₂ := by
  sorry

/-- **Proposition 7.6.5** (twists are continuous, Ch. 7 §7.6, H2:4528). In the situation of `thm7_6_3`, the twist
coordinate `FN_T` is continuous: if `t` is a twist of `τ` and `ε > 0`, there is `δ > 0` such that every twist `t'` of
every `τ'` with `teichDistance τ τ' < δ` has `|t − t'| < ε`. -/
theorem prop7_6_5 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀)
    {L : Fin (3 * g - 3) → Loop S₀} (hL : IsDecomposingSystemLoops Γ₀ p₀ L) {x : S₀}
    {σg σa σb : Fin (3 * g - 3) → Path x x} (hD : IsAdjacentPantsDatum Γ₀ p₀ L σg σa σb)
    (j : Fin (3 * g - 3)) (τ : TeichSpace S₀) {t : ℝ} (ht : twistOf τ (σg j) (σa j) (σb j) t) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (τ' : TeichSpace S₀) (t' : ℝ), teichDistance τ τ' < δ → twistOf τ' (σg j) (σa j) (σb j) t' →
      |t - t'| < ε := by
  sorry

end Hubbard2006
