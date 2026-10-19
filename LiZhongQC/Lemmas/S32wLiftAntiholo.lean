import LiZhongQC.Ch09.S31_FiniteType

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

/-- **L0.**  A lift to `ℍ` of an anti-conformal map `Jd` of a Riemann surface uniformized by `ℍ` is
anti-holomorphic: `z ↦ conj (liftToC Jt z)` is holomorphic on `ℍ`.  (Locally
`Jt = (ψ₁ ∘ p)⁻¹ ∘ (ψ_{Jd} ∘ Jd ∘ ψ⁻¹) ∘ (ψ ∘ p)` with `ψ ∘ p` conformal.) -/
theorem s32w_lift_antiholo {D : Type u} [TopologicalSpace D] [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ) ω D]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → D}
    (hp : IsUniformization Γ p) {Jd : D ≃ₜ D} (hJ : IsAnticonformalInvolution Jd)
    {Jt : UpperHalfPlane ≃ₜ UpperHalfPlane} (hlift : ∀ τ, p (Jt τ) = Jd (p τ)) :
    DifferentiableOn ℂ (fun z => conj (liftToC Jt z)) upperHalf := by
  intro z₀ hz₀
  have hz₀' : 0 < z₀.im := hz₀
  set τ₀ : UpperHalfPlane := ⟨z₀, hz₀'⟩ with hτ₀
  obtain ⟨U₀, hU₀o, hτU₀, hU₀H, hU₀s, hψ₀⟩ :=
    h23l_chart_proj (τ := τ₀) hp.1 hp.2.1 (p τ₀) (mem_chart_source ℂ _)
  obtain ⟨U₁, hU₁o, hτU₁, -, -, hψ₁⟩ :=
    h23l_chart_proj (τ := Jt τ₀) hp.1 hp.2.1 (p (Jt τ₀)) (mem_chart_source ℂ _)
  have hc₀ := thm7_3_one_qc_conformal hψ₀
  have hc₁ := thm7_3_one_qc_conformal hψ₁
  have hFx : p (Jt τ₀) = Jd (p τ₀) := hlift _
  have hkey : ∀ z ∈ U₀, chartAt ℂ (p (Jt τ₀)) (p (UpperHalfPlane.ofComplex (liftToC Jt z))) =
      localMapExpr Jd (p τ₀) (chartAt ℂ (p τ₀) (p (UpperHalfPlane.ofComplex z))) := by
    intro z hz
    rw [h23l_liftToC_eq Jt (hU₀H hz), UpperHalfPlane.ofComplex_apply, hFx,
      hlift (UpperHalfPlane.ofComplex z)]
    unfold localMapExpr
    rw [(chartAt ℂ (p τ₀)).left_inv (hU₀s z hz)]
  have hl₀ : liftToC Jt z₀ = ((Jt τ₀ : UpperHalfPlane) : ℂ) := h23l_liftToC_coe Jt τ₀
  have hfa : AnalyticAt ℂ (fun z => chartAt ℂ (p (Jt τ₀)) (p (UpperHalfPlane.ofComplex z)))
      ((Jt τ₀ : UpperHalfPlane) : ℂ) := hc₁.1.analyticAt (hU₁o.mem_nhds hτU₁)
  have hder := deriv_ne_zero_of_injOn hU₁o hc₁.1 hc₁.2.1 hτU₁
  have hs := hfa.hasStrictDerivAt
  have hinv := hs.to_localInverse hder
  have hleft := hs.eventually_left_inverse hder
  -- differentiability of the three factors at `z₀`
  have h1 : DifferentiableAt ℂ (fun z => chartAt ℂ (p τ₀) (p (UpperHalfPlane.ofComplex z))) z₀ :=
    hc₀.1.differentiableAt (hU₀o.mem_nhds hτU₀)
  have hDo : IsOpen (localMapDomain Jd (p τ₀)) :=
    (chartAt ℂ (p τ₀)).isOpen_inter_preimage_symm
      ((chartAt ℂ (Jd (p τ₀))).open_source.preimage Jd.continuous)
  have hz₀D : chartAt ℂ (p τ₀) (p (UpperHalfPlane.ofComplex z₀)) ∈ localMapDomain Jd (p τ₀) := by
    have e : UpperHalfPlane.ofComplex z₀ = τ₀ := UpperHalfPlane.ofComplex_apply_of_im_pos hz₀'
    rw [e]
    exact (s23_h_center Jd _).1
  have h2 : DifferentiableAt ℂ (fun w => conj (localMapExpr Jd (p τ₀) w))
      (chartAt ℂ (p τ₀) (p (UpperHalfPlane.ofComplex z₀))) :=
    (hJ.2 (p τ₀)).differentiableAt (hDo.mem_nhds hz₀D)
  have hpt : localMapExpr Jd (p τ₀) (chartAt ℂ (p τ₀) (p (UpperHalfPlane.ofComplex z₀))) =
      chartAt ℂ (p (Jt τ₀)) (p (UpperHalfPlane.ofComplex ((Jt τ₀ : UpperHalfPlane) : ℂ))) := by
    rw [← hkey z₀ hτU₀, hl₀]
  have h3 : DifferentiableAt ℂ (fun u => conj ((hs.localInverse _ _ _ hder) (conj u)))
      (conj (localMapExpr Jd (p τ₀) (chartAt ℂ (p τ₀) (p (UpperHalfPlane.ofComplex z₀))))) := by
    have := hinv.hasDerivAt.differentiableAt
    rw [hpt]
    exact (this.hasDerivAt.conj_conj).differentiableAt
  have hcomp := h3.comp z₀ (h2.comp z₀ h1)
  have hcont : ContinuousAt (liftToC Jt) z₀ :=
    (h23l_liftToC_continuousOn Jt.continuous).continuousAt (isOpen_upperHalf.mem_nhds hz₀)
  have hev : ∀ᶠ z in 𝓝 z₀, liftToC Jt z ∈ {y | hs.localInverse _ _ _ hder
      ((fun z => chartAt ℂ (p (Jt τ₀)) (p (UpperHalfPlane.ofComplex z))) y) = y} := by
    have : Tendsto (liftToC Jt) (𝓝 z₀) (𝓝 ((Jt τ₀ : UpperHalfPlane) : ℂ)) := by
      rw [← hl₀]; exact hcont
    exact this.eventually hleft
  apply DifferentiableAt.differentiableWithinAt
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hU₀o.mem_nhds hτU₀, hev] with z hz hzev
  simp only [Function.comp_apply, conj_conj]
  rw [← hkey z hz]
  exact congrArg conj hzev.symm

end LiZhongQC
