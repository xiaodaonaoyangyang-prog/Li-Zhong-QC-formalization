import LiZhongQC.Lemmas.S22gbOrders
import LiZhongQC.Lemmas.HurwitzProofChain

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

section GaussBonnetFinal

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- §22.4 (Gauss–Bonnet), relocated block: statement byte-identical to `gauss_bonnet_area`. -/
theorem s22gb_gauss_bonnet_area [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {F : Set ℂ} (hF : F ⊆ upperHalf)
    (hFund : MeasurableSet F ∧ (∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, ((γ • τ : UpperHalfPlane) : ℂ) ∈ F) ∧
      (∀ τ₁ τ₂ : UpperHalfPlane, (τ₁ : ℂ) ∈ interior F → (τ₂ : ℂ) ∈ interior F → p τ₁ = p τ₂ → τ₁ = τ₂) ∧
      volume (F \ interior F) = 0) :
    ∫⁻ z in F, ENNReal.ofReal (1 / z.im ^ 2) = ENNReal.ofReal (4 * π * (g - 1)) := by
  classical
  haveI : CompactSpace S := hS.1
  letI : MeasurableSpace S := borel S
  haveI : BorelSpace S := ⟨rfl⟩
  have hFH : IsFundamentalDomainH Γ F :=
    ⟨hF, hFund.1, hFund.2.1, fun τ₁ τ₂ h₁ h₂ h => hFund.2.2.1 τ₁ τ₂ h₁ h₂ ((hp.2.2.2 τ₁ τ₂).2 h),
      hFund.2.2.2⟩
  obtain ⟨K, q, hq, hmer, hKq⟩ := k22q_canonical_exists (S := S)
  have hK : IsCanonicalDivisor K := ⟨q, hq, hmer, hKq⟩
  have hord : ∀ x : S, meromorphicOrderAt (q x) (chartAt ℂ x x) ≠ ⊤ := fun x => by
    rw [← hKq x]; exact WithTop.coe_ne_top
  have hZ : ∀ x : S, x ∉ K.support → meromorphicOrderAt (q x) (chartAt ℂ x x) = 0 := fun x hx => by
    rw [← hKq x, Finsupp.notMem_support_iff.1 hx]; rfl
  have key := s22gb_area_eq_orders hp hFH hq hmer hord K.support hZ
  have hsum : ∑ x ∈ K.support, ((meromorphicOrderAt (q x) (chartAt ℂ x x)).untop₀ : ℝ) =
      ((Divisor.deg K : ℤ) : ℝ) := by
    have : ∀ x : S, ((meromorphicOrderAt (q x) (chartAt ℂ x x)).untop₀ : ℝ) = ((K x : ℤ) : ℝ) :=
      fun x => by rw [← hKq x]; simp
    simp only [this]
    rw [Divisor.deg, Finsupp.sum]
    push_cast
    rfl
  have hdeg : ((Divisor.deg K : ℤ) : ℝ) = 2 * (g : ℝ) - 2 := by
    have h := h77d_canonical_degree_analytic hK
    have hgen : genus S = g := k22rr_genus_eq hS
    have h' : Divisor.deg K = 2 * (g : ℤ) - 2 := by rw [← hgen]; exact h
    have := congrArg (fun z : ℤ => (z : ℝ)) h'
    simpa using this
  rw [hsum, hdeg, s22gm_surfaceArea_univ (S := S) hp.1.continuous F] at key
  rw [key]
  congr 1
  ring

end GaussBonnetFinal

section RelocatedS32

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- §22.4 (Gauss–Bonnet): for a closed Riemann surface of genus `g > 1` uniformized as `ℍ/Γ`,
the hyperbolic area of a fundamental domain of `Γ` is `4π(g - 1)`.
[CORRECTION] (user-approved 2026-10-06; found by the skillor's F0 audit): `hFund` now also requires
`volume (F \ interior F) = 0`. Without it the statement was false: a closed Dirichlet polygon together with a fat
Cantor set inside a `Γ`-translate of its interior satisfies the other hypotheses (same interior) and has area
`> 4π(g - 1)`. This is the correction made to S36's `IsFundamentalDomainH`. -/
theorem gauss_bonnet_area [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {F : Set ℂ} (hF : F ⊆ upperHalf)
    (hFund : MeasurableSet F ∧ (∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, ((γ • τ : UpperHalfPlane) : ℂ) ∈ F) ∧
      (∀ τ₁ τ₂ : UpperHalfPlane, (τ₁ : ℂ) ∈ interior F → (τ₂ : ℂ) ∈ interior F → p τ₁ = p τ₂ → τ₁ = τ₂) ∧
      volume (F \ interior F) = 0) :
    ∫⁻ z in F, ENNReal.ofReal (1 / z.im ^ 2) = ENNReal.ofReal (4 * π * (g - 1)) := by
  exact s22gb_gauss_bonnet_area hg hS hp hF hFund

end RelocatedS32

end LiZhongQC
