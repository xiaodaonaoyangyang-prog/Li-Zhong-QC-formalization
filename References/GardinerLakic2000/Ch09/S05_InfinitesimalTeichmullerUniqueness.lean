import References.GardinerLakic2000.Ch09.S04_DeltaInequalities

/-!
# Gardiner–Lakic 2000, Ch. 9 §9.5 Infinitesimal Teichmüller uniqueness

Source `teichmuller.txt`, lines 7765–7840 (Chapter 9, §9.5).

* Lemma 4 (l. 7768) — `lemma9_4`
* Lemma 5 (l. 7804) — `lemma9_5`
* Theorem 6 (l. 7839; cited at l. 7850) — `thm9_6`

Not items: the Steps I–III of the two proofs. The proofs call the lemmas "Lemma 3" and "Lemma 4" (l. 7771, 7812, 7838)
[misprint]. Modelling: surface level, as §9.2 without the constant-modulus hypothesis.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

variable {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R] [IsManifold 𝓘(ℂ) ω R]

/-- **Lemma 4** (§9.5, l. 7768). If `μ` is uniquely extremal in its class in `T`, it is uniquely extremal in its class
in `Z`. -/
theorem lemma9_4 {p : UpperHalfPlane → R} (hp : ∃ Γ, LiZhongQC.IsFuchsian Γ ∧ LiZhongQC.IsUniformization Γ p)
    {μ : beltramiBall R} (hμ : IsUniquelyExtremalRS p μ) : IsInfUniquelyExtremal μ.1 := by
  sorry

/-- **Lemma 5** (§9.5, l. 7804). If `μ` is uniquely extremal in its class in `Z`, it is uniquely extremal in its class
in `T`. -/
theorem lemma9_5 {p : UpperHalfPlane → R} (hp : ∃ Γ, LiZhongQC.IsFuchsian Γ ∧ LiZhongQC.IsUniformization Γ p)
    {μ : beltramiBall R} (hμ : IsInfUniquelyExtremal μ.1) : IsUniquelyExtremalRS p μ := by
  sorry

/-- **Theorem 6** (§9.5, l. 7839). A Beltrami coefficient is uniquely extremal in its class in `T` if and only if it is
uniquely extremal in its class in `Z`. -/
theorem thm9_6 {p : UpperHalfPlane → R} (hp : ∃ Γ, LiZhongQC.IsFuchsian Γ ∧ LiZhongQC.IsUniformization Γ p)
    (μ : beltramiBall R) : IsUniquelyExtremalRS p μ ↔ IsInfUniquelyExtremal μ.1 := by
  sorry

end GardinerLakic2000
