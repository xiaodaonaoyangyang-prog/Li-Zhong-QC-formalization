import LiZhongQC.Lemmas.S36G1dThetaFixed
import LiZhongQC.Lemmas.S36G1dMassEscape

/-! E5 source-only producer. No compiler run; no new global definitions. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Two additive error bounds imply ENNReal convergence, without subtracting infinities. -/
theorem s36e_tendsto_of_add_error {a : ℝ≥0∞} {x e : ℕ → ℝ≥0∞}
    (he : Tendsto e atTop (𝓝 0))
    (hupper : ∀ i, x i ≤ a + e i) (hlower : ∀ i, a ≤ x i + e i) :
    Tendsto x atTop (𝓝 a) := by
  apply ENNReal.tendsto_nhds_of_Icc
  intro ε hε
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 he) ε hε] with i hi
  refine ⟨?_, (hupper i).trans (add_le_add le_rfl hi)⟩
  apply tsub_le_iff_right.2
  exact (hlower i).trans (add_le_add le_rfl hi)

/-- The L1 reverse triangle estimate on a measurable subset of H.
Automorphy and finite area are not needed for this nonnegative-integral inequality. -/
theorem s36e_phiArea_le_add {F : Set ℂ} (hF : MeasurableSet F) (hFH : F ⊆ upperHalf)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf)
    (hg : DifferentiableOn ℂ g upperHalf) :
    phiArea f F ≤ phiArea g F + phiArea (f - g) F := by
  have hgm : AEMeasurable (fun z => ENNReal.ofReal ‖g z‖) (volume.restrict F) :=
    (hg.continuousOn.mono hFH).aestronglyMeasurable hF |>.aemeasurable.norm.ennreal_ofReal
  change (∫⁻ z in F, ENNReal.ofReal ‖f z‖) ≤
    (∫⁻ z in F, ENNReal.ofReal ‖g z‖) + ∫⁻ z in F, ENNReal.ofReal ‖(f - g) z‖
  rw [← lintegral_add_left' hgm]
  apply lintegral_mono
  intro z
  show ENNReal.ofReal ‖f z‖ ≤ ENNReal.ofReal ‖g z‖ + ENNReal.ofReal ‖(f - g) z‖
  rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc ‖f z‖ = ‖g z + (f z - g z)‖ := by congr 1; ring
    _ ≤ ‖g z‖ + ‖f z - g z‖ := norm_add_le _ _

/-- E5: pass the left integral. This is a consequence of E3, E4, the norm triangle
inequality and disjoint splitting D_i = F union (D_i \ F). -/
theorem s36e_area_tendsto (hΓ : IsFuchsian Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (H : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hsub : ∀ i, H i ≤ Γ) (hmono : Monotone H)
    (hcover : ∀ γ ∈ Γ, ∃ i, γ ∈ H i)
    (D : ℕ → Set ℂ) (hD : ∀ i, IsFundamentalDomainH (H i) (D i))
    (hFD : ∀ i, F ⊆ D i)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf)
    (hfA : phiArea f upperHalf < ⊤)
    {φ : ℂ → ℂ} (hθ : ∀ z ∈ upperHalf, φ z = h36p_theta Γ f z) :
    Tendsto (fun i => phiArea (h36p_theta (H i) f) (D i))
      atTop (𝓝 (phiArea φ F)) := by
  let ψ : ℕ → ℂ → ℂ := fun i => h36p_theta (H i) f
  let θ : ℂ → ℂ := h36p_theta Γ f
  have hθd : DifferentiableOn ℂ θ upperHalf := h36p_b_theta_diff hΓ hf hfA
  have hψd : ∀ i, DifferentiableOn ℂ (ψ i) upperHalf := by
    intro i
    have hHi : IsFuchsian (H i) := fun C hC =>
      (hΓ C hC).subset (fun γ hγ => ⟨hsub i hγ.1, hγ.2⟩)
    exact h36p_b_theta_diff hHi hf hfA
  have herr := s36e_theta_L1_fixed hΓ hF H hsub hmono hcover hf hfA
  have hfixed : Tendsto (fun i => phiArea (ψ i) F) atTop (𝓝 (phiArea θ F)) := by
    apply s36e_tendsto_of_add_error herr
    · intro i
      exact s36e_phiArea_le_add hF.2.1 hF.1 (hψd i) hθd
    · intro i
      have h := s36e_phiArea_le_add hF.2.1 hF.1 hθd (hψd i)
      have heq : phiArea (θ - ψ i) F = phiArea (ψ i - θ) F := by
        apply lintegral_congr
        intro z
        exact congrArg ENNReal.ofReal (norm_sub_rev (θ z) (ψ i z))
      rwa [heq] at h
  have htail := s36e_theta_mass_escape hΓ hF H hsub hmono hcover D hD hFD hf hfA
  have hsplit : ∀ i, phiArea (ψ i) F + phiArea (ψ i) (D i \ F) =
      phiArea (ψ i) (D i) := by
    intro i
    have h := lintegral_inter_add_sdiff (μ := volume) (fun z => ENNReal.ofReal ‖ψ i z‖) (D i) hF.2.1
    rw [inter_eq_right.2 (hFD i)] at h
    exact h
  have harea : phiArea φ F = phiArea θ F :=
    setLIntegral_congr_fun hF.2.1 (fun z hz =>
      congrArg (fun w : ℂ => ENNReal.ofReal ‖w‖) (hθ z (hF.1 hz)))
  rw [harea]
  have hsum := hfixed.add htail
  rw [add_zero] at hsum
  exact hsum.congr hsplit

end LiZhongQC
