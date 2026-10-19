import References.GardinerLakic2000.Ch02.S01_ConformalStructure

/-!
# Gardiner–Lakic 2000, Ch. 2 §2.2 Examples and uniformization

Source `teichmuller.txt`, lines 1140–1187 (Chapter 2, §2.2).

* Theorem 1 (uniformization, l. 1151; cited in Ch. 4, 11), "conformally equivalent to one of the five examples" —
  exists: `LiZhongQC.thm22_3_classification` (the sphere, the plane, the punctured plane, a torus, or ℍ modulo a
  torsion-free Fuchsian group acting freely)
* Theorem 1 (l. 1151), "exactly one" — `uniformizationType`, `thm2_1_b`
* Unlabelled (the covering group is unique up to conjugation in PSL(2,ℝ), l. 1160; used at l. 1551) —
  `para2_2_conj_unique`

Not items: Examples 1–5 (l. 1141–1149; their content is Theorem 1); Koebe's planarity theorem (l. 1153, a step of the
proof); "the covering group of `ℂ̄ ∖ {0, 1, ∞}` is the level-two congruence subgroup" (l. 1175, U−). Modelling: the
five types are those of `LiZhongQC.thm22_3_classification` (the sphere as a compact simply connected surface, the
torus by a holomorphic covering from `ℂ` whose fibres are lattice cosets); Fuchsian groups are subgroups of
SL(2,ℝ) (leader ruling A0.2), so "`G′ = B G B⁻¹`" is read modulo `±1`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (RSConformallyEquivalent puncturedPlaneOpens IsFuchsian ActsFreely IsUniformization)

/-- Helper for **Theorem 1** (§2.2, l. 1151). The five types of Examples 1–5: `0` the sphere (compact, simply
connected), `1` the plane, `2` the punctured plane (the cylinder), `3` a torus `ℂ/L`, `4` a hyperbolic surface `ℍ/G`
with `G` a torsion-free Fuchsian group acting freely. -/
def uniformizationType (R : Type*) [TopologicalSpace R] [ChartedSpace ℂ R] : Fin 5 → Prop :=
  ![CompactSpace R ∧ SimplyConnectedSpace R, RSConformallyEquivalent R ℂ,
    RSConformallyEquivalent R puncturedPlaneOpens,
    ∃ (L : PeriodPair) (p : ℂ → R), IsCoveringMap p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p ∧ Function.Surjective p ∧
      ∀ z w, p z = p w ↔ z - w ∈ L.lattice,
    ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → R),
      IsFuchsian Γ ∧ ActsFreely Γ ∧ IsUniformization Γ p]

/-- **Theorem 1** (uniformization, §2.2, l. 1151), "exactly one": a Riemann surface is of at most one of the five
types. -/
theorem thm2_1_b (R : Type*) [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] (i j : Fin 5) (hi : uniformizationType R i) (hj : uniformizationType R j) : i = j := by
  sorry

/-- **Unlabelled** (§2.2, l. 1160). If `ℍ/G` and `ℍ/G′` are both conformal to `R` (torsion-free Fuchsian groups
acting freely), there is a Möbius transformation `B` preserving `ℍ` with `G′ = B G B⁻¹` (in PSL(2,ℝ), i.e. modulo
`±1`). -/
theorem para2_2_conj_unique {R : Type*} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] {Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p p' : UpperHalfPlane → R}
    (hΓ : IsFuchsian Γ) (hΓ' : IsFuchsian Γ') (hf : ActsFreely Γ) (hf' : ActsFreely Γ')
    (hp : IsUniformization Γ p) (hp' : IsUniformization Γ' p') :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (γ ∈ Γ' ∨ -γ ∈ Γ') ↔ (B⁻¹ * γ * B ∈ Γ ∨ -(B⁻¹ * γ * B) ∈ Γ) := by
  sorry

end GardinerLakic2000
