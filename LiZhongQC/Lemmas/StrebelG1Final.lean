import LiZhongQC.Lemmas.StrebelDoubleInequalityHelpers
import LiZhongQC.Lemmas.StrebelFirstKind
import LiZhongQC.Lemmas.StrebelGammaBounds
import LiZhongQC.Lemmas.StrebelG1bApproxPacket
import LiZhongQC.Lemmas.StrebelG1bLimit
import LiZhongQC.Lemmas.FoundationFinal

/-!
# G1 final host: `str_g1a`, `s36a_double_ineq`, `str_g1b`

`str_g1a` is `str_g1a_of_foundation` (StrebelFirstKind) applied to `ft_foundation`; `s36a_double_ineq` is the Step A
assembly over `StrebelDoubleInequalityHelpers`; `str_g1b` (second kind) combines Step A, the two-sided approximation
packet, the B1/B2 bounds and the ENNReal limit bridge; the first kind case is `str_g1a`. Headers are byte-identical to
StrebelGammaIface (95317f71) and IFACE_G1B (f119f5da).

`ft_foundation` and `s36d_double_foundation` are imported from FoundationFinal.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **G1a.** (35.5) for a finitely generated, torsion-free Fuchsian group of the first kind (`ℍ/Γ` of finite
analytic type). -/
theorem str_g1a (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hfg : Γ.FG) (hfirst : ordinarySet Γ = ∅)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ ν : BeltramiGamma Γ) (hrel : teichSetoidGamma Γ ν μ)
    {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F) :
    phiArea φ F ≤ ∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal
      (lambdaStretchPlane φ φ (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z) := by
  exact str_g1a_of_foundation hΓ (ft_foundation hΓ hfree hfg hfirst) hF μ ν hrel hφ

/-- **(A) The double inequality.**  For `ψ` holomorphic and `Γ`-automorphic on `Ω'(E)`, integrable on `F` and on the
mirror domain (as `ψ* = conj ∘ ψ ∘ conj` on `F`), (35.5) on the punctured double `Ω'(E)/Γ` for the reflected map
`g̃` reads `‖ψ‖_F + ‖ψ*‖_F ≤ I_g(ψ) + I_g(ψ*)`. -/
theorem s36a_double_ineq (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hfg : Γ.FG)
    (hsecond : (ordinarySet Γ).Nonempty) {E : Finset ℝ}
    (hE : ∀ e ∈ E, (((e : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ)
    (hE3 : ∃ e₁ ∈ E, ∃ e₂ ∈ E, ∃ e₃ ∈ E, e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ ∧
      ∀ i ∈ ({e₁, e₂, e₃} : Finset ℝ), ∀ j ∈ ({e₁, e₂, e₃} : Finset ℝ), ∀ γ ∈ Γ, (γ 1 0 : ℝ) * i + γ 1 1 ≠ 0 → h36p_m γ (i : ℂ) = (j : ℂ) → i = j)
    {Ω : Set ℂ}
    (hΩ : ∀ z : ℂ, z ∈ Ω ↔ ((z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
      (∀ γ ∈ Γ, ∀ s ∈ E, (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) ∧
      (∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ))))
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ ν : BeltramiGamma Γ) (hrel : teichSetoidGamma Γ ν μ)
    {ψ : ℂ → ℂ} (hψd : DifferentiableOn ℂ ψ Ω)
    (hψΓ : ∀ γ ∈ Γ, ∀ z ∈ Ω, ψ (h36p_m γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = ψ z)
    (hψF : phiArea ψ F < ⊤) (hψF' : phiArea (fun z => conj (ψ (conj z))) F < ⊤) :
    phiArea ψ F + phiArea (fun z => conj (ψ (conj z))) F ≤
      (∫⁻ z in F, ENNReal.ofReal ‖ψ z‖ * ENNReal.ofReal
        (lambdaStretchPlane ψ ψ (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z)) +
      ∫⁻ z in F, ENNReal.ofReal ‖conj (ψ (conj z))‖ * ENNReal.ofReal
        (lambdaStretchPlane (fun w => conj (ψ (conj w))) (fun w => conj (ψ (conj w)))
          (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z) := by
  classical
  obtain ⟨g₀, n, S, _, _, _, _, _, P, hft, hex, hPs, hPf, hPe⟩ :=
    s36d_double_foundation hΓ hfree hfg hsecond hE hE3 hΩ
  obtain ⟨hΩH, hΩc, hΩΓ⟩ := s36a_omega hΓ hΩ
  obtain ⟨F₀⟩ := hft
  letI : MeasurableSpace S := borel S
  haveI : BorelSpace S := ⟨rfl⟩
  have hΩo : IsOpen Ω := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨e, hze, hes, -⟩ := hPe z hz
    exact Filter.mem_of_superset (e.open_source.mem_nhds hze) hes
  obtain ⟨K, hGK, -, hGg, hGr, hGc, hGH, -⟩ := s36a_gt μ ν hrel
  set G := Function.invFunOn (fMuSym ν.1.1) univ ∘ fMuSym μ.1.1 with hGdef
  set g := Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1 with hgdef
  set ψs : ℂ → ℂ := fun z => conj (ψ (conj z)) with hψs
  have hGcont : Continuous G := continuousOn_univ.1 hGK.2.2.1.1
  have hGΩ : ∀ z ∈ Ω, G z ∈ Ω := by
    intro z hz
    rcases lt_trichotomy z.im 0 with hlt | heq | hgt
    · have hcz : conj z ∈ upperHalf := by
        show 0 < (conj z).im
        rw [Complex.conj_im]
        linarith
      have h1 : 0 < (G (conj z)).im := hGH _ hcz
      have h2 : G z = conj (G (conj z)) := by rw [hGc, Complex.conj_conj]
      refine hΩH _ ?_
      rw [h2, Complex.conj_im]
      linarith
    · have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [heq])
      rw [hzr, hGr, ← hzr]
      exact hz
    · exact hΩH _ (ne_of_gt (hGH z hgt))
  obtain ⟨h, hhqc, hhom, hh⟩ := s36a_h hΩH hΩc hΩΓ hPs hPf hPe μ ν hrel
  obtain ⟨q, hq, hqψ⟩ := s36a_q hΩΓ hPs hPf hPe hψd hψΓ
  have hFH : F ⊆ upperHalf := hF.1
  have hFm : MeasurableSet F := hF.2.1
  have hNe : Nonempty S := ⟨P (Complex.I)⟩
  have hL : IsLindelof (univ : Set S) := s36a_lindelof hPs fun z hz => by
    obtain ⟨e, h1, h2, h3, -⟩ := hPe z hz
    exact ⟨e, h1, h2, h3⟩
  have hT1 := s36a_T3 hΓ hfree hF hΩH hΩc hΩΓ hPs hPf hPe hψd hψΓ hq hqψ (U := fun _ => 1) measurable_const
  have hnorm : quadDiffNorm q = phiArea ψ F + phiArea ψs F := by
    simp only [quadDiffNorm, phiArea, one_mul] at hT1 ⊢
    exact hT1
  by_cases hq0 : q = 0
  · -- `q = 0`: then `ψ = 0` on `Ω`, and both norms vanish
    have hψ0 : ∀ z ∈ Ω, ψ z = 0 := by
      intro z hz
      obtain ⟨-, h1⟩ := hqψ z hz (P z) (mem_chart_source ℂ _)
      rw [h1, hq0]
      simp
    have e1 : phiArea ψ F = 0 := by
      unfold phiArea
      refine (setLIntegral_congr_fun hFm (g := fun _ => (0 : ℝ≥0∞)) fun z hz => ?_).trans (by simp)
      rw [hψ0 z (hΩH z (ne_of_gt (hFH hz)))]
      simp
    have e2 : phiArea ψs F = 0 := by
      unfold phiArea
      refine (setLIntegral_congr_fun hFm (g := fun _ => (0 : ℝ≥0∞)) fun z hz => ?_).trans (by simp)
      have hcz : conj z ∈ Ω := hΩc _ (hΩH z (ne_of_gt (hFH hz)))
      simp only [hψs]
      rw [hψ0 _ hcz]
      simp
    rw [e1, e2, add_zero]
    exact bot_le
  rw [← hnorm]
  have hfin : quadDiffNorm q < ⊤ := by
    rw [hnorm]
    exact ENNReal.add_lt_top.2 ⟨hψF, hψF'⟩
  have hadm := s36a_adm hex F₀ hq hfin
  have hsurf := str_surface_lambda hex F₀ hadm hq hq0 hhqc hhom
  have hmeas : Measurable (s26v_lam q h) := str_measurable_borel hL (s26v_lam_borel hq h)
  have hT2 := s36a_T3 hΓ hfree hF hΩH hΩc hΩΓ hPs hPf hPe hψd hψΓ hq hqψ hmeas
  refine hsurf.trans (le_of_eq ?_)
  rw [str_surfaceIntegral_lam hq h, hT2]
  congr 1
  · refine setLIntegral_congr_fun hFm fun z hz => ?_
    have hzH := hFH hz
    rw [s36a_T4 hΩo hq hqψ hPe hGcont hGΩ h hh (hΩH z (ne_of_gt hzH)), mul_comm]
    congr 2
    refine s36a_lam_congr ?_
    filter_upwards [isOpen_upperHalf.mem_nhds hzH] with w hw
    exact hGg w hw
  · refine setLIntegral_congr_fun hFm fun z hz => ?_
    have hzH := hFH hz
    have hcz : conj z ∈ Ω := hΩc _ (hΩH z (ne_of_gt hzH))
    rw [s36a_T4 hΩo hq hqψ hPe hGcont hGΩ h hh hcz, mul_comm, s36a_reflect hGc z]
    congr 2
    refine s36a_lam_congr ?_
    filter_upwards [isOpen_upperHalf.mem_nhds hzH] with w hw
    exact hGg w hw

/-- **G1b.** The same for finitely generated, torsion-free `Γ` of any kind (boundary curves, by symmetrization). -/
theorem str_g1b (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hfg : Γ.FG)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ ν : BeltramiGamma Γ) (hrel : teichSetoidGamma Γ ν μ)
    {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F) :
    phiArea φ F ≤ ∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal
      (lambdaStretchPlane φ φ (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z) := by
  classical
  by_cases hfirst : ordinarySet Γ = ∅
  · exact str_g1a hΓ hfree hfg hfirst hF μ ν hrel hφ
  have hsecond : (ordinarySet Γ).Nonempty := Set.nonempty_iff_ne_empty.mpr hfirst
  obtain ⟨C, hC, hcont⟩ := s36g_lam_cont hΓ hF μ ν hrel
  obtain ⟨D, hD, hbound⟩ := s36g_lam_bound hΓ hF μ ν hrel
  let L : (ℂ → ℂ) → ℝ≥0∞ := fun χ =>
    ∫⁻ z in F, ENNReal.ofReal ‖χ z‖ * ENNReal.ofReal
      (lambdaStretchPlane χ χ
        (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z)
  change phiArea φ F ≤ L φ
  apply s36g_error_limit hφ.2.1 hC hD
  intro ε hε hεfin
  obtain ⟨E, Ω, ψ, hE, hE3, hΩ, hψd, hψΓ, hψ, hψs, hdist, hsmall, hupper, hlower⟩ :=
    s36a_approx_packet hΓ hsecond hF hφ hε hεfin
  have hdbl := s36a_double_ineq hΓ hfree hfg hsecond hE hE3 hΩ hF μ ν hrel
    hψd hψΓ hψ.2.1 hψs.2.1
  change phiArea ψ F + phiArea (fun z => conj (ψ (conj z))) F ≤
    L ψ + L (fun z => conj (ψ (conj z))) at hdbl
  have hcontψ := hcont φ hφ ψ hψ
  change L ψ ≤ L φ + C * (phiArea φ F + phiArea ψ F) ^ (1 / 2 : ℝ) *
    phiArea (φ - ψ) F ^ (1 / 2 : ℝ) at hcontψ
  have hboundψ := hbound (fun z => conj (ψ (conj z))) hψs
  change L (fun z => conj (ψ (conj z))) ≤
    D * phiArea (fun z => conj (ψ (conj z))) F at hboundψ
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hmass : phiArea φ F + phiArea ψ F ≤ phiArea φ F + (phiArea φ F + ε) :=
    add_le_add le_rfl hupper
  have hcontε : L ψ ≤ L φ +
      C * (phiArea φ F + (phiArea φ F + ε)) ^ (1 / 2 : ℝ) * ε ^ (1 / 2 : ℝ) :=
    hcontψ.trans (add_le_add le_rfl
      (mul_le_mul' (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hmass hhalf))
        (ENNReal.rpow_le_rpow hdist.le hhalf)))
  have hboundε : L (fun z => conj (ψ (conj z))) ≤ D * ε :=
    hboundψ.trans (mul_le_mul' le_rfl hsmall.le)
  calc
    phiArea φ F ≤ phiArea ψ F + ε := hlower
    _ ≤ (L ψ + L (fun z => conj (ψ (conj z)))) + ε :=
      add_le_add ((le_self_add : phiArea ψ F ≤
        phiArea ψ F + phiArea (fun z => conj (ψ (conj z))) F).trans hdbl) le_rfl
    _ ≤ (L φ + C * (phiArea φ F + (phiArea φ F + ε)) ^ (1 / 2 : ℝ) *
        ε ^ (1 / 2 : ℝ) + D * ε) + ε :=
      add_le_add (add_le_add hcontε hboundε) le_rfl

end LiZhongQC
