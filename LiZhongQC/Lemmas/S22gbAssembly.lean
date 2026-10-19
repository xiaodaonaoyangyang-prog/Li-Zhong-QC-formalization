import LiZhongQC.Lemmas.S22gbCancel

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

section GaussBonnetAssembly

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S] [CompactSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- Abstract Stokes assembly over a finite smooth partition of unity subordinate to chart sheets.
Each piece contributes its Stokes value `s i`, the cross terms cancel by `s22gb_cancel`. -/
theorem s22gb_assembly {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {q : S → ℂ → ℂ}
    (hq : IsDiffFamily 1 0 q) {α : S → ℂ → ℂ → ℝ}
    (hα : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target →
      AnalyticAt ℂ (q x) z → q x z ≠ 0 →
      ∀ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z → deriv ψ z ≠ 0 → ψ z ∈ upperHalf →
        (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z] (fun w => (chartAt ℂ x).symm w) →
        α x =ᶠ[𝓝 z] s22cd_canonicalGauge ψ (q x))
    (hsm : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target → MeromorphicAt (q x) z →
      meromorphicOrderAt (q x) z = 0 → ∀ v : ℂ, ContDiffAt ℝ 1 (fun w => α x w v) z)
    {ι : Type*} [Fintype ι] (ρ : ι → S → ℝ)
    (hρs : ∀ i, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (ρ i))
    (hρ0 : ∀ i y, 0 ≤ ρ i y) (hρsum : ∀ y, ∑ i, ρ i y = 1)
    (xs : ι → S) (Dom : ι → Set ℂ) (ψs : ι → ℂ → ℂ)
    (hDo : ∀ i, IsOpen (Dom i)) (hDt : ∀ i, Dom i ⊆ (chartAt ℂ (xs i)).target)
    (hψan : ∀ i, ∀ z ∈ Dom i, AnalyticAt ℂ (ψs i) z)
    (hψd : ∀ i, ∀ z ∈ Dom i, deriv (ψs i) z ≠ 0)
    (hψH : ∀ i, ∀ z ∈ Dom i, ψs i z ∈ upperHalf)
    (hψe : ∀ i, ∀ z ∈ Dom i,
      s22gm_projectionExtension p (ψs i z) = (chartAt ℂ (xs i)).symm z)
    (hts : ∀ i, tsupport (ρ i) ⊆ (chartAt ℂ (xs i)).symm '' Dom i)
    (hDbd : ∀ i, ∃ C : ℝ, ∀ z ∈ Dom i, s22gc_areaDensity (ψs i) z ≤ C)
    (hDvol : ∀ i, volume (Dom i) < ⊤)
    (A : Set S) (hAo : IsOpen A)
    (hAreg : ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ A →
      MeromorphicAt (q x) z ∧ meromorphicOrderAt (q x) z = 0)
    (W : ι → ℂ → ℝ)
    (hW : ∀ i z, W i z = fderiv ℝ (fun w => ρ i ((chartAt ℂ (xs i)).symm w)) z 1 *
        α (xs i) z I - fderiv ℝ (fun w => ρ i ((chartAt ℂ (xs i)).symm w)) z I * α (xs i) z 1)
    (hWc : ∀ i, ContinuousOn (W i) (Dom i ∩ (chartAt ℂ (xs i)).symm ⁻¹' A))
    (hWbd : ∀ i, ∃ C : ℝ, ∀ z ∈ Dom i, (chartAt ℂ (xs i)).symm z ∈ A → |W i z| ≤ C)
    (s : ι → ℝ)
    (hstokes : ∀ i, (∫ z in Dom i ∩ (chartAt ℂ (xs i)).symm ⁻¹' A,
      (ρ i ((chartAt ℂ (xs i)).symm z) * s22gc_areaDensity (ψs i) z + W i z)) = s i) :
    s22gm_surfaceArea p F A ≠ ⊤ ∧ (s22gm_surfaceArea p F A).toReal = ∑ i, s i := by
  classical
  set μ := s22gm_surfaceArea p F with hμ
  have hAm : MeasurableSet A := hAo.measurableSet
  set sheet : ι → Set S := fun i => (chartAt ℂ (xs i)).symm '' Dom i with hsheet
  have hsheet_open : ∀ i, IsOpen (sheet i) := fun i =>
    (chartAt ℂ (xs i)).symm.isOpen_image_of_subset_source (hDo i) (hDt i)
  have hDm : ∀ i, MeasurableSet (Dom i) := fun i => (hDo i).measurableSet
  have hDpos : ∀ i, ∀ z ∈ Dom i, 0 < s22gc_areaDensity (ψs i) z := fun i z hz =>
    s22gc_areaDensity_pos (hψd i z hz) (show 0 < (ψs i z).im from hψH i z hz)
  have hU_open : ∀ i, IsOpen (Dom i ∩ (chartAt ℂ (xs i)).symm ⁻¹' A) := by
    intro i
    have h := (chartAt ℂ (xs i)).continuousOn_symm.isOpen_inter_preimage
      (chartAt ℂ (xs i)).open_target hAo
    have : Dom i ∩ (chartAt ℂ (xs i)).symm ⁻¹' A =
        Dom i ∩ ((chartAt ℂ (xs i)).target ∩ (chartAt ℂ (xs i)).symm ⁻¹' A) := by
      ext z
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, hDt i h1, h2⟩
      · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
    rw [this]
    exact (hDo i).inter h
  -- each sheet has finite measure
  have hsm_fin : ∀ i, μ (sheet i) ≠ ⊤ := by
    intro i
    rw [hμ, hsheet, s22gb_sheet_measure hp hF (xs i) (hDo i) (hDm i) (hDt i) (hψan i) (hψd i)
      (hψH i) (hψe i)]
    obtain ⟨C, hC⟩ := hDbd i
    refine ne_of_lt ?_
    calc ∫⁻ z in Dom i, ENNReal.ofReal (s22gc_areaDensity (ψs i) z)
        ≤ ∫⁻ z in Dom i, ENNReal.ofReal C :=
          setLIntegral_mono measurable_const (fun z hz => ENNReal.ofReal_le_ofReal (hC z hz))
      _ = ENNReal.ofReal C * volume (Dom i) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hDvol i)
  have hcover : (univ : Set S) ⊆ ⋃ i, sheet i := by
    intro y _
    by_contra hy
    simp only [mem_iUnion, not_exists] at hy
    have h0 : ∑ i, ρ i y = 0 := Finset.sum_eq_zero fun i _ => by
      by_contra hne
      exact hy i (hts i (subset_tsupport _ (Function.mem_support.2 hne)))
    rw [hρsum] at h0
    exact one_ne_zero h0
  have hfin : IsFiniteMeasure μ := ⟨by
    calc μ univ ≤ μ (⋃ i, sheet i) := measure_mono hcover
      _ ≤ ∑ i, μ (sheet i) := measure_iUnion_fintype_le _ _
      _ < ⊤ := ENNReal.sum_lt_top.2 (fun i _ => lt_top_iff_ne_top.2 (hsm_fin i))⟩
  haveI := hfin
  set D : ι → ℂ → ℝ := fun i => s22gc_areaDensity (ψs i) with hD
  set h : ι → S → ℝ := fun i y =>
    W i (chartAt ℂ (xs i) y) / D i (chartAt ℂ (xs i) y) with hh
  set g1 : ι → S → ℝ := fun i => A.indicator (ρ i) with hg1
  set g2 : ι → S → ℝ := fun i => A.indicator ((sheet i).indicator (h i)) with hg2
  have hg1m : ∀ i, Measurable (g1 i) := fun i => ((hρs i).continuous.measurable).indicator hAm
  have hg2m : ∀ i, Measurable (g2 i) := by
    intro i
    have hO : IsOpen (A ∩ sheet i) := hAo.inter (hsheet_open i)
    have hcont : ContinuousOn (h i) (A ∩ sheet i) := by
      intro y hy
      obtain ⟨hyA, z, hz, rfl⟩ := hy
      have hzt : z ∈ (chartAt ℂ (xs i)).target := hDt i hz
      have hR : chartAt ℂ (xs i) ((chartAt ℂ (xs i)).symm z) = z := (chartAt ℂ (xs i)).right_inv hzt
      have hchart : ContinuousAt (chartAt ℂ (xs i)) ((chartAt ℂ (xs i)).symm z) :=
        (chartAt ℂ (xs i)).continuousAt ((chartAt ℂ (xs i)).map_target hzt)
      have hWat : ContinuousAt (W i) z :=
        (hWc i).continuousAt ((hU_open i).mem_nhds ⟨hz, hyA⟩)
      have hDat : ContinuousAt (D i) z :=
        s22gc_areaDensity_continuousAt (hψan i z hz) (show 0 < (ψs i z).im from hψH i z hz)
      have a1 : ContinuousAt (fun y => W i (chartAt ℂ (xs i) y)) ((chartAt ℂ (xs i)).symm z) :=
        ContinuousAt.comp_of_eq hWat hchart hR
      have a2 : ContinuousAt (fun y => D i (chartAt ℂ (xs i) y)) ((chartAt ℂ (xs i)).symm z) :=
        ContinuousAt.comp_of_eq hDat hchart hR
      refine ContinuousAt.continuousWithinAt (a1.div a2 ?_)
      rw [hR]
      exact (hDpos i z hz).ne'
    have e : g2 i = (A ∩ sheet i).piecewise (h i) (fun _ => 0) := by
      funext y
      by_cases hy : y ∈ A ∩ sheet i
      · rw [Set.piecewise_eq_of_mem _ _ _ hy]
        simp only [hg2, indicator_of_mem hy.1, indicator_of_mem hy.2]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hy]
        by_cases hyA : y ∈ A
        · have : y ∉ sheet i := fun hs => hy ⟨hyA, hs⟩
          simp only [hg2, indicator_of_mem hyA, indicator_of_notMem this]
        · simp only [hg2, indicator_of_notMem hyA]
    rw [e]
    exact ContinuousOn.measurable_piecewise hcont continuousOn_const hO.measurableSet
  have hρle : ∀ i y, ρ i y ≤ 1 := fun i y => by
    rw [← hρsum y]
    exact Finset.single_le_sum (fun j _ => hρ0 j y) (Finset.mem_univ i)
  have hg1i : ∀ i, Integrable (g1 i) μ := fun i =>
    Integrable.of_bound (hg1m i).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun y => by
      by_cases hy : y ∈ A
      · simp only [hg1, indicator_of_mem hy, Real.norm_eq_abs, abs_of_nonneg (hρ0 i y)]
        exact hρle i y
      · simp [hg1, indicator_of_notMem hy])
  have hvan1 : ∀ i y, y ∉ sheet i → g1 i y = 0 := by
    intro i y hy
    have : y ∉ tsupport (ρ i) := fun h' => hy (hts i h')
    by_cases hyA : y ∈ A
    · simp only [hg1, indicator_of_mem hyA]
      exact image_eq_zero_of_notMem_tsupport this
    · simp [hg1, indicator_of_notMem hyA]
  have hvan2 : ∀ i y, y ∉ sheet i → g2 i y = 0 := by
    intro i y hy
    by_cases hyA : y ∈ A
    · simp only [hg2, indicator_of_mem hyA, indicator_of_notMem hy]
    · simp [hg2, indicator_of_notMem hyA]
  -- value of `g2` in the chart
  have hg2val : ∀ i, ∀ z ∈ Dom i, g2 i ((chartAt ℂ (xs i)).symm z) =
      if (chartAt ℂ (xs i)).symm z ∈ A then W i z / D i z else 0 := by
    intro i z hz
    have hzt : z ∈ (chartAt ℂ (xs i)).target := hDt i hz
    have hR : chartAt ℂ (xs i) ((chartAt ℂ (xs i)).symm z) = z := (chartAt ℂ (xs i)).right_inv hzt
    have hsh : (chartAt ℂ (xs i)).symm z ∈ sheet i := mem_image_of_mem _ hz
    by_cases hyA : (chartAt ℂ (xs i)).symm z ∈ A
    · simp only [hg2, indicator_of_mem hyA, indicator_of_mem hsh, hh, hR, if_pos hyA]
    · simp only [hg2, indicator_of_notMem hyA, if_neg hyA]
  have hg2i : ∀ i, Integrable (g2 i) μ := by
    intro i
    refine ⟨(hg2m i).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have hG := s22gb_lintegral_transfer hp hF (xs i) (hDo i) (hDm i) (hDt i) (hψan i) (hψd i)
      (hψH i) (hψe i) (fun y => ENNReal.ofReal ‖g2 i y‖)
      (ENNReal.measurable_ofReal.comp (hg2m i).norm)
      (fun y hy => by simp [hvan2 i y hy])
    rw [hG]
    obtain ⟨C, hC⟩ := hWbd i
    refine lt_of_le_of_lt (setLIntegral_mono (g := fun _ => ENNReal.ofReal C) measurable_const
      (fun z hz => ?_)) ?_
    · rw [hg2val i z hz]
      by_cases hyA : (chartAt ℂ (xs i)).symm z ∈ A
      · rw [if_pos hyA, Real.norm_eq_abs, abs_div, abs_of_pos (hDpos i z hz),
          ← ENNReal.ofReal_mul (div_nonneg (abs_nonneg _) (hDpos i z hz).le), div_mul_cancel₀ _ (hDpos i z hz).ne']
        exact ENNReal.ofReal_le_ofReal (hC z hz hyA)
      · rw [if_neg hyA]
        simp
    · rw [setLIntegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hDvol i)
  -- the Stokes identity of each piece
  have hpiece : ∀ i, (∫ y, g1 i y ∂μ) + (∫ y, g2 i y ∂μ) = s i := by
    intro i
    rw [← integral_add (hg1i i) (hg2i i)]
    have hT := s22gb_transfer hp hF (xs i) (hDo i) (hDm i) (hDt i) (hψan i) (hψd i) (hψH i)
      (hψe i) (fun y => g1 i y + g2 i y) ((hg1m i).add (hg2m i))
      (fun y hy => by simp [hvan1 i y hy, hvan2 i y hy])
    rw [hT, ← hstokes i]
    have hUm : MeasurableSet (Dom i ∩ (chartAt ℂ (xs i)).symm ⁻¹' A) := (hU_open i).measurableSet
    have hpt : ∀ z ∈ Dom i, (g1 i ((chartAt ℂ (xs i)).symm z) + g2 i ((chartAt ℂ (xs i)).symm z)) *
        s22gc_areaDensity (ψs i) z =
        (Dom i ∩ (chartAt ℂ (xs i)).symm ⁻¹' A).indicator
          (fun z => ρ i ((chartAt ℂ (xs i)).symm z) * s22gc_areaDensity (ψs i) z + W i z) z := by
      intro z hz
      rw [hg2val i z hz]
      by_cases hyA : (chartAt ℂ (xs i)).symm z ∈ A
      · rw [if_pos hyA, indicator_of_mem (show z ∈ Dom i ∩ (chartAt ℂ (xs i)).symm ⁻¹' A from ⟨hz, hyA⟩)]
        simp only [hg1, indicator_of_mem hyA]
        have := (hDpos i z hz).ne'
        simp only [hD] at *
        field_simp
      · rw [if_neg hyA, indicator_of_notMem (show z ∉ Dom i ∩ (chartAt ℂ (xs i)).symm ⁻¹' A from
          fun h' => hyA h'.2)]
        simp [hg1, indicator_of_notMem hyA]
    rw [setIntegral_congr_fun (hDm i) hpt, setIntegral_indicator hUm,
      inter_eq_right.2 inter_subset_left]
  -- the two sums
  have hsum1 : ∑ i, ∫ y, g1 i y ∂μ = (μ A).toReal := by
    rw [← integral_finset_sum _ (fun i _ => hg1i i)]
    have : (fun y => ∑ i, g1 i y) = A.indicator 1 := by
      funext y
      by_cases hy : y ∈ A
      · simp only [hg1, indicator_of_mem hy, Pi.one_apply]
        exact hρsum y
      · simp [hg1, indicator_of_notMem hy]
    rw [show (∫ y, ∑ i, g1 i y ∂μ) = ∫ y, (fun y => ∑ i, g1 i y) y ∂μ from rfl, this,
      integral_indicator_one hAm]
    rfl
  have hsum2 : ∑ i, ∫ y, g2 i y ∂μ = 0 := by
    rw [← integral_finset_sum _ (fun i _ => hg2i i)]
    have : (fun y => ∑ i, g2 i y) = fun _ => (0 : ℝ) := by
      funext y
      by_cases hy : y ∈ A
      · have hc := s22gb_cancel hp hq hα hsm ρ hρs hρsum xs Dom ψs hDo hDt hψan hψd hψH hψe hts A
          hAreg W hW y hy
        simpa only [hg2, indicator_of_mem hy] using hc
      · simp [hg2, indicator_of_notMem hy]
    rw [show (∫ y, ∑ i, g2 i y ∂μ) = ∫ y, (fun y => ∑ i, g2 i y) y ∂μ from rfl, this]
    simp
  refine ⟨measure_ne_top μ A, ?_⟩
  have hall : ∑ i, ((∫ y, g1 i y ∂μ) + ∫ y, g2 i y ∂μ) = ∑ i, s i :=
    Finset.sum_congr rfl (fun i _ => hpiece i)
  rw [Finset.sum_add_distrib, hsum1, hsum2, add_zero] at hall
  exact hall

end GaussBonnetAssembly

end LiZhongQC
