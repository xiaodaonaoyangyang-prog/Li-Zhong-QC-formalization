import LiZhongQC.Lemmas.D0DomainOpen
import LiZhongQC.Lemmas.D0DomainConnected
import LiZhongQC.Lemmas.D0OrdinaryStabilizer
import LiZhongQC.Lemmas.D0Quotient

/-! Assembly of the approved D0 endpoint from O/C/F/Q.
Source-only; no new assumptions, definitions, or changes to the frozen header. -/
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **D0 (the quotient `Ω'(E)/Γ`).**  `Γ` acts freely and properly discontinuously on `Ω'(E)` (ordinary points; the
removed orbits are closed and discrete in the ordinary set), which is connected for the second kind; the orbit space
is a Riemann surface (Mathlib quotient charts, Möbius transitions, as in F0), with a surjective projection `P` whose
fibres are the orbits and whose local sheets are biholomorphic. -/
theorem s36d_quotient (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hsecond : (ordinarySet Γ).Nonempty)
    {E : Finset ℝ} (hE : ∀ e ∈ E, (((e : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ) {Ω : Set ℂ}
    (hΩ : ∀ z : ℂ, z ∈ Ω ↔ ((z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
      (∀ γ ∈ Γ, ∀ s ∈ E, (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) ∧
      (∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ)))) :
    ∃ (S : Type) (_ : TopologicalSpace S) (_ : ChartedSpace ℂ S) (_ : T2Space S)
      (_ : ConnectedSpace S) (_ : IsManifold 𝓘(ℂ) ω S) (P : ℂ → S),
      P '' Ω = univ ∧
      (∀ z ∈ Ω, ∀ w ∈ Ω, (P z = P w ↔ ∃ γ ∈ Γ, w = h36p_m γ z)) ∧
      ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source ∧
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target := by
  have hopen := s36d0_domain_open hΓ hE hΩ
  have hinv := (s36a_omega hΓ hΩ).2.2
  have hconn := s36d0_domain_connected hΓ hsecond hE hΩ
  refine s36d0_quotient_of_domain hΓ hopen hconn (fun z hz => ((hΩ z).1 hz).1) hinv ?_
  intro γ hγ z hz hfix
  exact s36d0_ordinary_stabilizer hΓ hfree ((hΩ z).1 hz).1 hγ
    (hinv γ hγ z hz).1 hfix

end LiZhongQC
