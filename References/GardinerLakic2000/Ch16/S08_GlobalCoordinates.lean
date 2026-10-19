import References.GardinerLakic2000.Ch16.S07_HilbertTransform

/-!
# Gardiner–Lakic 2000, Ch. 16 §16.8 Global coordinates for `QS mod S`

Source `teichmuller.txt`, lines 12600–12668 (Chapter 16, §16.8).

* Definition (the map `Ŝ : QS mod S → B/B₀` induced by the Bers embedding, l. 12601) — exists:
  `GardinerLakic2000.bersMapOmega` `GardinerLakic2000.boundedCuspForms0` (batch D)
* Theorem 8 (J. Kahn, l. 12603) — `thm16_8`

Not items: the proof (generalized Ahlfors–Weill extension, Earle–Nag reflection, local boundary dilatation; it uses
`sup_p H_p = H`, Corollary 17.1); the exercises (l. 12620–12667). Modelling [reading, E0.4]: a quasisymmetric `h` of
`ℝ̄` normalized to fix `0, 1, ∞` is represented by normalized welding maps (§16.5's `IsWeldingMap` with `d = ∞`,
`h(0) = 0`, `h(1) = 1`), and `Ŝ` sends it to the class of `S(f)` on `ℍ*` modulo `B₀(ℍ*)` (batch D's
`boundedCuspForms0` for the trivial group). "`Ŝ` is an isomorphism" is read as: `S(f₁) − S(f₀) ∈ B₀` iff
`h₁ = s ∘ h₀` for a symmetric `s` (well defined and injective on `QS mod S`); the proof shows injectivity, and the
statement that `Ŝ` is onto its image as a complex-analytic isomorphism is not captured.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (ExtPlane extInf lowerHalf schwarzian)

/-- **Theorem 8** (J. Kahn, §16.8, l. 12603). The map `Ŝ` from `QS mod S` into `B/B₀` is an isomorphism: for
normalized welding maps `f₀, f₁` of normalized quasisymmetric `h₀, h₁`, `S(f₁) − S(f₀) ∈ B₀(ℍ*)` iff `h₁ ∘ h₀⁻¹` is
symmetric. -/
theorem thm16_8 {Ω₀ Ωs₀ Ω₁ Ωs₁ : Set ℂ} {f₀ g₀ f₁ g₁ : ℂ → ℂ} {fb₀ gb₀ fb₁ gb₁ : ℝ → ExtPlane} {h₀ h₁ : ℝ → ℝ}
    (hw₀ : IsWeldingMap Ω₀ Ωs₀ f₀ g₀ fb₀ gb₀ extInf h₀) (hw₁ : IsWeldingMap Ω₁ Ωs₁ f₁ g₁ fb₁ gb₁ extInf h₁)
    (hn₀ : h₀ 0 = 0 ∧ h₀ 1 = 1) (hn₁ : h₁ 0 = 0 ∧ h₁ 1 = 1)
    (hq₀ : ∃ M, LiZhongQC.IsQuasisymmetric h₀ M) (hq₁ : ∃ M, LiZhongQC.IsQuasisymmetric h₁ M) :
    (fun z => schwarzian f₁ z - schwarzian f₀ z) ∈
        boundedCuspForms0 {fun z => z} lowerHalf (boundedCuspFormsC ⊥ lowerHalf) ↔
      ∃ s : ℝ → ℝ, HasVanishingRatioDistortionReal s ∧ ∀ x : ℝ, s (h₀ x) = h₁ x := by
  sorry

end GardinerLakic2000
