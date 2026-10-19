import LiZhongQC.Lemmas.F1CuspFamilySupport

/-! D1 V producer: one ordinary neighborhood of the finite removed-orbit centers
avoiding all translates of the height-one cusp families and of their mirrors.
Reuses ft1fas_cusp_family_avoids_ordinary_compact; the mirror family is handled by
spherical conjugation, which fixes every point of the extended real line. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- V. Choose an ordinary neighborhood of the FINITE removed-orbit centers
avoiding ALL translates of the height-one cusp families and their mirrors.
Reuse ft1fas_cusp_family_avoids_ordinary_compact on range a and conjugate the
result; no compact core or ordinary-arc coverage is needed here. -/
theorem s36d1_cusp_avoidance (hΓ : IsFuchsian Γ) {c : ℕ} (A π₀ : Fin c → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hcusp : ∀ i, π₀ i ∈ Γ ∧ ∀ τ : UpperHalfPlane,
      π₀ i • (A i • τ) = A i • ((1 : ℝ) +ᵥ τ))
    (hpc : ∀ i i' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im →
      1 < ((A i')⁻¹ • (γ • (A i • τ))).im →
      i = i' ∧ ∃ t : ℤ, γ = π₀ i ^ t ∨ γ = -π₀ i ^ t)
    {k : ℕ} (a : Fin k → ExtPlane) (hord : ∀ i, a i ∈ ordinarySet Γ) :
    ∃ V : Set ExtPlane, IsOpen V ∧ (∀ i, a i ∈ V) ∧
      Disjoint V {p : ExtPlane | ∃ γ ∈ Γ, ∃ i : Fin c, ∃ τ : UpperHalfPlane,
      1 < τ.im ∧ p = (((γ • (A i • τ) : UpperHalfPlane) : ℂ) : ExtPlane)} ∧
      Disjoint V {p : ExtPlane | ∃ γ ∈ Γ, ∃ i : Fin c, ∃ τ : UpperHalfPlane,
      1 < τ.im ∧ p = ((conj (((γ • (A i • τ)) : UpperHalfPlane) : ℂ) : ℂ) : ExtPlane)} := by
  classical
  obtain ⟨V₁, hV₁o, hLV₁, hV₁d⟩ := ft1fas_cusp_family_avoids_ordinary_compact hΓ A π₀ hcusp hpc
    (Set.range a) (Set.finite_range a).isCompact (by
      rintro _ ⟨i, rfl⟩
      exact hord i)
  let σ : ExtPlane ≃ₜ ExtPlane := Complex.conjCLE.toHomeomorph.onePointCongr
  have hσ : ∀ z : ℂ, σ (z : ExtPlane) = ((conj z : ℂ) : ExtPlane) := fun z => rfl
  have hσa : ∀ i, σ (a i) = a i := by
    intro i
    rcases (hord i).1 with ⟨z, hz, hza⟩ | hinf
    · rw [← hza, hσ]
      congr 1
      exact Complex.conj_eq_iff_im.2 hz
    · rw [Set.mem_singleton_iff.1 hinf]
      rfl
  have hai : ∀ i, a i ∈ V₁ := fun i => hLV₁ ⟨i, rfl⟩
  refine ⟨V₁ ∩ σ ⁻¹' V₁, hV₁o.inter (hV₁o.preimage σ.continuous), fun i => ⟨hai i, ?_⟩, ?_, ?_⟩
  · show σ (a i) ∈ V₁
    rw [hσa]
    exact hai i
  · exact hV₁d.mono_left inter_subset_left
  · rw [Set.disjoint_left]
    rintro p ⟨-, hp⟩ ⟨γ, hγ, i, τ, hτ, rfl⟩
    rw [Set.mem_preimage, hσ, Complex.conj_conj] at hp
    exact Set.disjoint_left.1 hV₁d hp ⟨γ, hγ, i, τ, hτ, rfl⟩

end LiZhongQC
