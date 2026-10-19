import LiZhongQC.Lemmas.F1Final
import LiZhongQC.Lemmas.D1BasicEnds
import LiZhongQC.Lemmas.D1ParabolicCore
import LiZhongQC.Lemmas.D1DoubleCore
import LiZhongQC.Lemmas.D1CuspAvoidance
import LiZhongQC.Lemmas.D1OrbitIsolation
import LiZhongQC.Lemmas.D1PunctureCharts
import LiZhongQC.Lemmas.D1CuspCharts
import LiZhongQC.Lemmas.D1CrossDisjoint
import LiZhongQC.Lemmas.D1CompactCore

/-! D1 final host: the geometric assembly G from the shared F1 endpoint and the frozen D1 theorem
`s36d_ends`, assembled mechanically from the accepted producers R, G0, G1, G2, V,
I, P, C, X, K, E, A. Statements byte-identical to D1DecompositionIface rev002 (fa46d638);
`s36d_ends` is byte-identical to FTIface2 (cdf79372). -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- G. Mechanical geometric assembly of the two elementary branches and G2.
The input decomposition is PRODUCED by the shared F1 endpoint; none of it is a
new hypothesis on frozen D1. -/
theorem s36d1_geometric_data (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hfg : Γ.FG) :
    ∃ (c : ℕ) (A π₀ : Fin c → Matrix.SpecialLinearGroup (Fin 2) ℝ) (L : Set ExtPlane),
      IsCompact L ∧ L ⊆ (fuchsianLimitSet Γ)ᶜ ∧
      (∀ i, π₀ i ∈ Γ ∧ ∀ τ : UpperHalfPlane,
      π₀ i • (A i • τ) = A i • ((1 : ℝ) +ᵥ τ)) ∧
      (∀ i i' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im →
      1 < ((A i')⁻¹ • (γ • (A i • τ))).im →
      i = i' ∧ ∃ t : ℤ, γ = π₀ i ^ t ∨ γ = -π₀ i ^ t) ∧
      (∀ p : ExtPlane, p ∉ fuchsianLimitSet Γ → ∃ γ ∈ Γ,
      mobiusSL (slRealToComplex γ) p ∈ L ∨
      ∃ i : Fin c, ∃ τ : UpperHalfPlane, 2 < τ.im ∧
        (mobiusSL (slRealToComplex γ) p = (((A i • τ : UpperHalfPlane) : ℂ) : ExtPlane) ∨
         mobiusSL (slRealToComplex γ) p = ((conj ((A i • τ : UpperHalfPlane) : ℂ) : ℂ) : ExtPlane))) := by
  rcases ft1fas_decomposition_with_ordinary hΓ hfree hfg with hel | hel |
    ⟨c, m, C, A, π₀, B, h, lam, θ, hC, hcusp, hfun, hpc, hpf, hcross, hcover, harcord, harccover⟩
  · obtain ⟨L, hL, hLord, hcover⟩ := s36d1_trivial_core hΓ hel
    refine ⟨0, (fun i => i.elim0), (fun i => i.elim0), L, hL, hLord, ?_, ?_, ?_⟩
    · intro i
      exact i.elim0
    · intro i
      exact i.elim0
    · intro p hp
      obtain ⟨γ, hγ, hγp⟩ := hcover p hp
      exact ⟨γ, hγ, Or.inl hγp⟩
  · obtain ⟨A, π₀, hπ, htrans, hcyc⟩ := hel
    obtain ⟨L, hL, hLord, hcover⟩ := s36d1_parabolic_core hΓ A π₀ hπ htrans hcyc
    refine ⟨1, (fun _ => A), (fun _ => π₀), L, hL, hLord, ?_, ?_, ?_⟩
    · intro i
      exact ⟨hπ, htrans⟩
    · intro i j γ hγ τ hτ hτ'
      exact ⟨Subsingleton.elim i j, hcyc γ hγ⟩
    · intro p hp
      obtain ⟨γ, hγ, hγp⟩ := hcover p hp
      refine ⟨γ, hγ, ?_⟩
      rcases hγp with hL | ⟨τ, hτ, heq⟩
      · exact Or.inl hL
      · exact Or.inr ⟨0, τ, hτ, heq⟩
  · obtain ⟨L, hL, hLord, hdouble⟩ :=
      s36d1_double_core hΓ hfree C A π₀ B h lam θ hC hcusp hfun hpc hpf hcross hcover harcord harccover
    exact ⟨c, A, π₀, L, hL, hLord, hcusp, hpc, hdouble⟩

/-- **D1 (ends of `Ω'(E)/Γ`).**  For finitely generated `Γ` of the second kind, any surface `S` with a projection
`P : Ω'(E) → S` as in D0 has the cusp end data with `n ≥ 3` ends: by F1, the compact core is the image of
`C ∪ conj C ∪` the closed double sectors (minus small discs at the removed orbits), and the ends are the horoballs and
their mirror images and punctured discs at the removed orbits of `E` and `∞`; the three points of `hE3` give three
distinct ends.  The elementary cases are explicit (`ℂ ∖ E`, `ℂ* ∖ …`). -/
theorem s36d_ends {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hfg : Γ.FG)
    (hsecond : (ordinarySet Γ).Nonempty) {E : Finset ℝ}
    (hE : ∀ e ∈ E, (((e : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ)
    (hE3 : ∃ e₁ ∈ E, ∃ e₂ ∈ E, ∃ e₃ ∈ E, e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ ∧
      ∀ i ∈ ({e₁, e₂, e₃} : Finset ℝ), ∀ j ∈ ({e₁, e₂, e₃} : Finset ℝ), ∀ γ ∈ Γ, (γ 1 0 : ℝ) * i + γ 1 1 ≠ 0 → h36p_m γ (i : ℂ) = (j : ℂ) → i = j)
    {Ω : Set ℂ}
    (hΩ : ∀ z : ℂ, z ∈ Ω ↔ ((z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
      (∀ γ ∈ Γ, ∀ s ∈ E, (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) ∧
      (∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ))))
    {P : ℂ → S} (hPsurj : P '' Ω = univ)
    (hPfib : ∀ z ∈ Ω, ∀ w ∈ Ω, (P z = P w ↔ ∃ γ ∈ Γ, w = h36p_m γ z))
    (hPloc : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source ∧
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target) :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ (φ : Fin n → ℂ → S) (K : Set S) (r : ℝ), IsCompact K ∧ r < 1 ∧
      (∀ i, InjOn (φ i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (φ i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧
        ∀ V : Set ℂ, IsOpen V → V ⊆ {w | w ≠ 0 ∧ ‖w‖ < 1} → IsOpen (φ i '' V)) ∧
      (∀ i i', i ≠ i' → Disjoint (φ i '' {w | w ≠ 0 ∧ ‖w‖ < 1}) (φ i' '' {w | w ≠ 0 ∧ ‖w‖ < 1})) ∧
      (∀ x : S, x ∈ K ∨ ∃ i w, w ≠ 0 ∧ ‖w‖ ≤ r ∧ φ i w = x) ∧
      (∀ x : S, ∃ N ∈ 𝓝 x, ∃ δ > (0 : ℝ), ∀ i w, w ≠ 0 → ‖w‖ < 1 → φ i w ∈ N → δ ≤ ‖w‖) := by
  -- hsecond stays frozen; the constructed decomposition also handles its unused
  -- first-kind branch. Here the three ordinary removed orbits already force it.
  have _ := hsecond
  obtain ⟨k, a, hk, hseed, hord, hsep, hcomplete⟩ :=
    s36d1_removed_orbits hΓ hE hE3
  obtain ⟨c, A, π₀, L, hL, hLord, hcusp, hpc, hcover⟩ :=
    s36d1_geometric_data hΓ hfree hfg
  obtain ⟨V, hVo, hVa, hVu, hVl⟩ :=
    s36d1_cusp_avoidance hΓ A π₀ hcusp hpc a hord
  obtain ⟨e, ζ, he0, hesrc, heV, heord, hedel, heprec, heeq, hehol⟩ :=
    s36d1_orbit_isolation hΓ hfree hE hΩ a hseed hord hsep hcomplete V hVo hVa
  obtain ⟨ψ, hψeq, hψchart, hψdisj, hψescape⟩ :=
    s36d1_puncture_charts hΓ hE hΩ hPsurj hPfib hPloc a hseed hord hsep hcomplete
      e ζ he0 hesrc heord hedel heprec heeq hehol
  obtain ⟨χ, q, hq0, hq1, hχchart, hχdisj, hχescape, hχrange, hχtail⟩ :=
    s36d1_cusp_charts hΓ hfree hE hΩ hPsurj hPfib hPloc A π₀ hcusp hpc
  have hcross :=
    s36d1_cross_disjoint hΓ hE hΩ hPsurj hPfib hPloc A e ζ hesrc heeq
      V heV hVu hVl ψ hψeq χ hχrange
  obtain ⟨K, hK, hKcover⟩ :=
    s36d1_compact_core hΓ hE hΩ hPsurj hPfib hPloc a hseed hord hsep hcomplete
      e ζ he0 hesrc heord hedel heprec heeq hehol ψ hψeq L hL hLord
  obtain ⟨r, hr, hglobal⟩ :=
    s36d1_exhaustive_ends hΓ hE hΩ hPsurj hPfib hPloc A L hcover
      ψ χ q hq0 hq1 hχtail K hKcover
  obtain ⟨φ, hφ, hφφ, hcov, hend⟩ :=
    s36d1_assemble ψ χ K r hK hr hψchart hψdisj hψescape
      hχchart hχdisj hχescape hcross hglobal
  exact ⟨k + c + c, by omega, φ, K, r, hK, hr, hφ, hφφ, hcov, hend⟩

end LiZhongQC
