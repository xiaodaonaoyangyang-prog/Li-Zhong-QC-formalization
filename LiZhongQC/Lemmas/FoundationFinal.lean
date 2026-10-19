import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.FoundationSmallSupport
import LiZhongQC.Lemmas.FoundationCuspEnds
import LiZhongQC.Lemmas.FoundationCapPoints
import LiZhongQC.Lemmas.F1Final
import LiZhongQC.Lemmas.D0QuotientFinal
import LiZhongQC.Lemmas.D1Final

/-!
# Foundation final host (S36): `ft1_decomposition`, `ft_foundation`, `s36d_double_foundation`

`ft1_decomposition` is the projection of the coherent F1 export
`ft1fas_decomposition_with_ordinary` (projection block by the F1 assembly lane).
`ft_foundation` and `s36d_double_foundation` are the approved FTIface2 assemblies, consuming the
accepted support F1e/F4a/F5 (FoundationSmallSupport), F2c (FoundationCuspEnds), F3p (FoundationCapPoints),
D0 `s36d_quotient` and D1 `s36d_ends`. No new definitions.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **F1 (Katok Thm 4.6.1, Beardon's proof, run to the end decomposition).**  A finitely generated Fuchsian group
acting freely (up to `±1`) is trivial up to sign, or cyclic parabolic, or there are a compact `C ⊆ ℍ`, `n` cusps
(`A i`, with `π₀ i ∈ Γ` acting as `τ ↦ τ + 1` in the coordinate `A i`) and `m` funnels (`B j`, with `h j ∈ Γ` acting
as `z ↦ lam j * z`, `lam j > 1`, in the coordinate `B j`) such that the horoballs `A i • {Im > 1}` and the sectors
`B j • {arg < θ j}` are precisely invariant under `⟨π₀ i⟩`, `⟨h j⟩` (up to sign) and pairwise disjoint modulo `Γ`, and
every point of `ℍ` has a `Γ`-translate in `C`, in a horoball or in a sector. -/
theorem ft1_decomposition (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hfg : Γ.FG) :
    (∀ γ ∈ Γ, γ = 1 ∨ γ = -1) ∨
    (∃ A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ, π₀ ∈ Γ ∧
      (∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ)) ∧
      ∀ γ ∈ Γ, ∃ k : ℤ, γ = π₀ ^ k ∨ γ = -π₀ ^ k) ∨
    ∃ (n m : ℕ) (C : Set UpperHalfPlane) (A π₀ : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (B h : Fin m → Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam θ : Fin m → ℝ),
      IsCompact C ∧
      (∀ i, π₀ i ∈ Γ ∧ ∀ τ : UpperHalfPlane, π₀ i • (A i • τ) = A i • ((1 : ℝ) +ᵥ τ)) ∧
      (∀ j, h j ∈ Γ ∧ 1 < lam j ∧ 0 < θ j ∧ θ j < π ∧
        ∀ τ : UpperHalfPlane, (((B j)⁻¹ • (h j • (B j • τ)) : UpperHalfPlane) : ℂ) = (lam j : ℂ) * (τ : ℂ)) ∧
      (∀ i i' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im → 1 < ((A i')⁻¹ • (γ • (A i • τ))).im →
        i = i' ∧ ∃ k : ℤ, γ = π₀ i ^ k ∨ γ = -π₀ i ^ k) ∧
      (∀ j j' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, arg (τ : ℂ) < θ j →
        arg (((B j')⁻¹ • (γ • (B j • τ)) : UpperHalfPlane) : ℂ) < θ j' →
        j = j' ∧ ∃ k : ℤ, γ = h j ^ k ∨ γ = -h j ^ k) ∧
      (∀ i j γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im →
        θ j ≤ arg (((B j)⁻¹ • (γ • (A i • τ)) : UpperHalfPlane) : ℂ)) ∧
      ∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, γ • τ ∈ C ∨ (∃ i, 1 < ((A i)⁻¹ • (γ • τ)).im) ∨
        ∃ j, arg (((B j)⁻¹ • (γ • τ) : UpperHalfPlane) : ℂ) < θ j := by
  rcases ft1fas_decomposition_with_ordinary hΓ hfree hfg with htriv | hpar | hdata
  · exact Or.inl htriv
  · exact Or.inr (Or.inl hpar)
  · obtain ⟨n, m, C, A, π₀, B, h, lam, θ, hC, hcusp, hfun, hpc, hpf,
      hcross, hcover, _, _⟩ := hdata
    exact Or.inr (Or.inr ⟨n, m, C, A, π₀, B, h, lam, θ, hC, hcusp, hfun,
      hpc, hpf, hcross, hcover⟩)

/-- **Foundation (Siegel–Nielsen), first kind.**  For a finitely generated Fuchsian group `Γ` of the first kind
acting freely (up to `±1`), there are a Riemann surface `S` of finite type `(g, n, 0)`, not exceptional (`S²`, `ℂ`,
torus and `ℂ*` are not quotients of `ℍ`), and a holomorphic covering `p : ℍ → S` whose fibres are the `Γ`-orbits
(`IsUniformization Γ p`). -/
theorem ft_foundation (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hfg : Γ.FG) (hfirst : ordinarySet Γ = ∅) :
    ∃ (g n : ℕ) (S : Type) (_ : TopologicalSpace S) (_ : ChartedSpace ℂ S) (_ : T2Space S)
      (_ : ConnectedSpace S) (_ : IsManifold 𝓘(ℂ) ω S) (p : UpperHalfPlane → S),
      IsUniformization Γ p ∧ IsFiniteType S g n 0 ∧ ¬ IsExceptionalType g n 0 := by
  obtain ⟨S, iT, iC, i2, iCo, iM, p, hp⟩ := ft0_quotient hΓ hfree
  rcases ft1_decomposition hΓ hfree hfg with hel | hel |
    ⟨n, m, C, A, π₀, B, h, lam, θ, hC, hcusp, hfun, hpc, hpf, -, hcover⟩
  · exact absurd hfirst (ft1_elementary_ordinary hΓ (Or.inl hel)).ne_empty
  · exact absurd hfirst (ft1_elementary_ordinary hΓ (Or.inr hel)).ne_empty
  · obtain rfl : m = 0 := by
      by_contra hm
      have j : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
      obtain ⟨hh, hlam, hθ0, hθπ, hscale⟩ := hfun j
      exact (ft4_funnel_ordinary hΓ (B j) (h j) (lam j) (θ j) hh hlam hθ0 hθπ hscale
        fun γ hγ τ h1 h2 => (hpf j j γ hγ τ h1 h2).2).ne_empty hfirst
    have hcover' : ∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, γ • τ ∈ C ∨ ∃ i, 1 < ((A i)⁻¹ • (γ • τ)).im := by
      intro τ
      obtain ⟨γ, hγ, hτ⟩ := hcover τ
      rcases hτ with hτ | hτ | ⟨j, -⟩
      · exact ⟨γ, hγ, Or.inl hτ⟩
      · exact ⟨γ, hγ, Or.inr hτ⟩
      · exact j.elim0
    obtain ⟨φ, K, r, hK, hr, hφ, hφφ, hcov, hend⟩ := ft2_cusp_ends hp hΓ hfree C A π₀ hC hcusp hpc hcover'
    obtain ⟨g, hg⟩ := ft3_cap_points φ K r hK hr hφ hφφ hcov hend
    exact ⟨g, n, S, iT, iC, i2, iCo, iM, p, hp, hg, ft5_not_exceptional hp hg⟩

/-- **Foundation for the punctured Schottky double.**  For a finitely generated torsion-free Fuchsian group of the
second kind and a finite set `E` of ordinary real points containing three points in distinct `Γ`-orbits,
`Ω'(E)/Γ` is a non-exceptional Riemann surface of type `(g, n, 0)`, with a projection `P` which is a holomorphic
local homeomorphism on `Ω'(E)` whose fibres are the `Γ`-orbits. -/
theorem s36d_double_foundation (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hfg : Γ.FG)
    (hsecond : (ordinarySet Γ).Nonempty) {E : Finset ℝ}
    (hE : ∀ e ∈ E, (((e : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ)
    (hE3 : ∃ e₁ ∈ E, ∃ e₂ ∈ E, ∃ e₃ ∈ E, e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ ∧
      ∀ i ∈ ({e₁, e₂, e₃} : Finset ℝ), ∀ j ∈ ({e₁, e₂, e₃} : Finset ℝ), ∀ γ ∈ Γ, (γ 1 0 : ℝ) * i + γ 1 1 ≠ 0 → h36p_m γ (i : ℂ) = (j : ℂ) → i = j)
    {Ω : Set ℂ}
    (hΩ : ∀ z : ℂ, z ∈ Ω ↔ ((z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
      (∀ γ ∈ Γ, ∀ s ∈ E, (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) ∧
      (∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ)))) :
    ∃ (g n : ℕ) (S : Type) (_ : TopologicalSpace S) (_ : ChartedSpace ℂ S) (_ : T2Space S)
      (_ : ConnectedSpace S) (_ : IsManifold 𝓘(ℂ) ω S) (P : ℂ → S),
      IsFiniteType S g n 0 ∧ ¬ IsExceptionalType g n 0 ∧ P '' Ω = univ ∧
      (∀ z ∈ Ω, ∀ w ∈ Ω, (P z = P w ↔ ∃ γ ∈ Γ, w = h36p_m γ z)) ∧
      ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source ∧
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target := by
  obtain ⟨S, iT, iC, i2, iCo, iM, P, hPsurj, hPfib, hPloc⟩ := s36d_quotient hΓ hfree hsecond hE hΩ
  obtain ⟨n, hn, φ, K, r, hK, hr, hφ, hφφ, hcov, hend⟩ :=
    s36d_ends hΓ hfree hfg hsecond hE hE3 hΩ hPsurj hPfib hPloc
  obtain ⟨g, hg⟩ := ft3_cap_points φ K r hK hr hφ hφφ hcov hend
  have hex : ¬ IsExceptionalType g n 0 := by
    simp only [IsExceptionalType, Prod.mk.injEq]
    omega
  exact ⟨g, n, S, iT, iC, i2, iCo, iM, P, hg, hex, hPsurj, hPfib, hPloc⟩

end LiZhongQC
