import LiZhongQC.Lemmas.S22gbInv

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

section GaussBonnetTransfer

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S] [CompactSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- The surface measure restricted to a chart sheet is the pushforward of the chart area. -/
theorem s22gb_restrict_sheet {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) (x : S) {ψ : ℂ → ℂ} {Dom : Set ℂ}
    (hDo : IsOpen Dom) (hDm : MeasurableSet Dom) (hDt : Dom ⊆ (chartAt ℂ x).target)
    (hψan : ∀ z ∈ Dom, AnalyticAt ℂ ψ z) (hψd : ∀ z ∈ Dom, deriv ψ z ≠ 0)
    (hψH : ∀ z ∈ Dom, ψ z ∈ upperHalf)
    (hψe : ∀ z ∈ Dom, s22gm_projectionExtension p (ψ z) = (chartAt ℂ x).symm z) :
    (s22gm_surfaceArea p F).restrict ((chartAt ℂ x).symm '' Dom) =
      Measure.map (fun z => s22gm_projectionExtension p (ψ z)) (s22gc_chartArea ψ Dom) := by
  have hinj : InjOn ψ Dom := by
    intro z1 h1 z2 h2 h
    have := congrArg (s22gm_projectionExtension p) h
    rw [hψe z1 h1, hψe z2 h2] at this
    exact (chartAt ℂ x).symm.injOn (hDt h1) (hDt h2) this
  have himg : IsOpen (ψ '' Dom) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z, hz, rfl⟩
    have hs := (hψan z hz).hasStrictDerivAt
    have hmap := hs.map_nhds_eq (hψd z hz)
    rw [← hmap]
    exact image_mem_map (hDo.mem_nhds hz)
  have hHsub : ψ '' Dom ⊆ upperHalf := by
    rintro _ ⟨z, hz, rfl⟩
    exact hψH z hz
  have hpinj : InjOn (s22gm_projectionExtension p) (ψ '' Dom) := by
    rintro _ ⟨z1, h1, rfl⟩ _ ⟨z2, h2, rfl⟩ h
    rw [hψe z1 h1, hψe z2 h2] at h
    rw [(chartAt ℂ x).symm.injOn (hDt h1) (hDt h2) h]
  have hrest := s22gc_surfaceArea_restrict_chart hp hF hDm hψan hinj himg hHsub hpinj
  have hset : s22gm_projectionExtension p '' (ψ '' Dom) = (chartAt ℂ x).symm '' Dom := by
    rw [← image_comp]
    exact image_congr (fun z hz => hψe z hz)
  rw [hset] at hrest
  exact hrest

/-- Integration of a measurable function supported in one analytic chart sheet is integration
in the chart against the hyperbolic area density of the lift. -/
theorem s22gb_transfer {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) (x : S) {ψ : ℂ → ℂ} {Dom : Set ℂ}
    (hDo : IsOpen Dom) (hDm : MeasurableSet Dom) (hDt : Dom ⊆ (chartAt ℂ x).target)
    (hψan : ∀ z ∈ Dom, AnalyticAt ℂ ψ z) (hψd : ∀ z ∈ Dom, deriv ψ z ≠ 0)
    (hψH : ∀ z ∈ Dom, ψ z ∈ upperHalf)
    (hψe : ∀ z ∈ Dom, s22gm_projectionExtension p (ψ z) = (chartAt ℂ x).symm z)
    (g : S → ℝ) (hg : Measurable g)
    (hg0 : ∀ y, y ∉ (chartAt ℂ x).symm '' Dom → g y = 0) :
    ∫ y, g y ∂(s22gm_surfaceArea p F) =
      ∫ z in Dom, g ((chartAt ℂ x).symm z) * s22gc_areaDensity ψ z := by
  have hrest := s22gb_restrict_sheet hp hF x hDo hDm hDt hψan hψd hψH hψe
  have h1 : ∫ y, g y ∂(s22gm_surfaceArea p F) =
      ∫ y in (chartAt ℂ x).symm '' Dom, g y ∂(s22gm_surfaceArea p F) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hg0).symm
  rw [h1, hrest]
  have hφ : AEMeasurable (fun z => s22gm_projectionExtension p (ψ z)) (s22gc_chartArea ψ Dom) := by
    have := s22gc_projected_chart_aemeasurable hp hDm (fun z hz => (hψan z hz).continuousAt) hψH
    exact this.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [integral_map hφ hg.aestronglyMeasurable]
  have hdens : AEMeasurable (fun z => ENNReal.ofReal (s22gc_areaDensity ψ z))
      (volume.restrict Dom) := s22gc_areaDensity_aemeasurable hDm hψan hψH
  rw [s22gc_chartArea, integral_withDensity_eq_integral_toReal_smul₀ hdens
    (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun hDm fun z hz => ?_
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (s22gc_areaDensity_nonneg ψ z), hψe z hz]
  ring

/-- Lower integral version of the transfer. -/
theorem s22gb_lintegral_transfer {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) (x : S) {ψ : ℂ → ℂ} {Dom : Set ℂ}
    (hDo : IsOpen Dom) (hDm : MeasurableSet Dom) (hDt : Dom ⊆ (chartAt ℂ x).target)
    (hψan : ∀ z ∈ Dom, AnalyticAt ℂ ψ z) (hψd : ∀ z ∈ Dom, deriv ψ z ≠ 0)
    (hψH : ∀ z ∈ Dom, ψ z ∈ upperHalf)
    (hψe : ∀ z ∈ Dom, s22gm_projectionExtension p (ψ z) = (chartAt ℂ x).symm z)
    (g : S → ℝ≥0∞) (hg : Measurable g)
    (hg0 : ∀ y, y ∉ (chartAt ℂ x).symm '' Dom → g y = 0) :
    ∫⁻ y, g y ∂(s22gm_surfaceArea p F) =
      ∫⁻ z in Dom, g ((chartAt ℂ x).symm z) * ENNReal.ofReal (s22gc_areaDensity ψ z) := by
  have hrest := s22gb_restrict_sheet hp hF x hDo hDm hDt hψan hψd hψH hψe
  have h1 : ∫⁻ y, g y ∂(s22gm_surfaceArea p F) =
      ∫⁻ y in (chartAt ℂ x).symm '' Dom, g y ∂(s22gm_surfaceArea p F) := by
    rw [setLIntegral_eq_of_support_subset]
    intro y hy
    by_contra hn
    exact hy (hg0 y hn)
  rw [h1, hrest]
  have hφ : AEMeasurable (fun z => s22gm_projectionExtension p (ψ z)) (s22gc_chartArea ψ Dom) := by
    have := s22gc_projected_chart_aemeasurable hp hDm (fun z hz => (hψan z hz).continuousAt) hψH
    exact this.mono_ac (withDensity_absolutelyContinuous _ _)
  have hφ' : AEMeasurable (fun z => s22gm_projectionExtension p (ψ z)) (volume.restrict Dom) :=
    s22gc_projected_chart_aemeasurable hp hDm (fun z hz => (hψan z hz).continuousAt) hψH
  rw [lintegral_map' hg.aemeasurable hφ]
  have hdens : AEMeasurable (fun z => ENNReal.ofReal (s22gc_areaDensity ψ z))
      (volume.restrict Dom) := s22gc_areaDensity_aemeasurable hDm hψan hψH
  rw [s22gc_chartArea, lintegral_withDensity_eq_lintegral_mul₀
    (g := fun z => g (s22gm_projectionExtension p (ψ z))) hdens
    (hg.comp_aemeasurable hφ')]
  refine setLIntegral_congr_fun hDm fun z hz => ?_
  simp only [Pi.mul_apply, hψe z hz]
  exact mul_comm _ _

/-- The surface measure of a chart sheet. -/
theorem s22gb_sheet_measure {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) (x : S) {ψ : ℂ → ℂ} {Dom : Set ℂ}
    (hDo : IsOpen Dom) (hDm : MeasurableSet Dom) (hDt : Dom ⊆ (chartAt ℂ x).target)
    (hψan : ∀ z ∈ Dom, AnalyticAt ℂ ψ z) (hψd : ∀ z ∈ Dom, deriv ψ z ≠ 0)
    (hψH : ∀ z ∈ Dom, ψ z ∈ upperHalf)
    (hψe : ∀ z ∈ Dom, s22gm_projectionExtension p (ψ z) = (chartAt ℂ x).symm z) :
    s22gm_surfaceArea p F ((chartAt ℂ x).symm '' Dom) =
      ∫⁻ z in Dom, ENNReal.ofReal (s22gc_areaDensity ψ z) := by
  have hsheet : MeasurableSet ((chartAt ℂ x).symm '' Dom) :=
    ((chartAt ℂ x).symm.isOpen_image_of_subset_source hDo hDt).measurableSet
  have h := s22gb_lintegral_transfer hp hF x hDo hDm hDt hψan hψd hψH hψe
    (((chartAt ℂ x).symm '' Dom).indicator 1) (measurable_one.indicator hsheet)
    (fun y hy => indicator_of_notMem hy _)
  rw [lintegral_indicator_one hsheet] at h
  rw [h]
  refine setLIntegral_congr_fun hDm fun z hz => ?_
  rw [indicator_of_mem (mem_image_of_mem _ hz)]
  simp

end GaussBonnetTransfer

end LiZhongQC
