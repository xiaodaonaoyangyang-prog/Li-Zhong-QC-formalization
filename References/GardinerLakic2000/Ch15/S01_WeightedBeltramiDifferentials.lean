import References.GardinerLakic2000.Ch14.S11_TeichmullerMetricAT

/-!
# Gardiner–Lakic 2000, Ch. 15 §15.1 Weighted Beltrami differentials (with the chapter introduction)

Source `teichmuller.txt`, lines 11229–11377 (Chapter 15, introduction and §15.1).

* Definition (`d([id], [f]) = ½ log K₀`, `d([[id]], [[f]]) = ½ log H`, l. 11233, 11243) — exists:
  `GardinerLakic2000.teichDist` `GardinerLakic2000.asymDist`
* Definition (`h*`, `H*`, `H`, l. 11250–11258) — exists: `GardinerLakic2000.boundaryDilatationStarK`
  `GardinerLakic2000.boundaryDilatationH` `GardinerLakic2000.hStarOf`
* Definition (asymptotically extremal map, l. 11258) — `IsAsymExtremal`
* Definition (the infinitesimal problem for `Z/Z₀`, l. 11262–11266) — `IsInfAsymExtremal`
* Definition (`L∞(E, F, α)`, `L₁(E, F, α)`, `A(E, F, α)` and their norms, l. 11269–11275) — `IsVanishingOn`,
  `weightedNormInf`, `weightedNormL1`
* Unlabelled (weighted representatives exist, Hahn–Banach and Riesz, l. 11275; used in Lemmas 1 and 2) —
  `para15_1_weighted_rep`
* Lemma 1 (l. 11277) — `lemma15_1`

Not items: (15.1)–(15.4) (proof of Lemma 1); the Hahn–Banach remark for `Z` (l. 11262, it is A's Theorem 3.2).
Modelling (leader calibration of Part E, E0.1): surface level as D §14.8–14.11. A subset `E` is "vanished on" when
the restriction `μχ_E` (C: `restrictBeltrami`) has norm `0`; `∬_S |φ|` is C: `setIntegralQD`. `A(E, F, α)` is `A(R)`
(A: `integrableHolQDSet`) with the weighted norm `weightedNormL1 E F α` (restriction to `R ∖ E` does not change a
holomorphic `φ`); `‖L‖` of `L ∈ A(E, F, α)*` is A: `dualNormOn` for that norm, and `L = [μ]` is
`φ ↦ pairingRS φ μ`. `b(ν)` is A: `infBoundaryDilatation` of the functional of `ν`. In Lemma 1 the printed
`b(ν)‖` has a stray bar in both OCRs (GL1:3955) [OCR]; read `‖ν‖∞ − b(ν)`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsFuchsian IsUniformization)

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

/-- **Definition** (asymptotically extremal, §15 introduction, l. 11258). `μ` is asymptotically extremal in its class:
`H*(μ) = H([μ])`. -/
def IsAsymExtremal (p : UpperHalfPlane → R) (μ : beltramiBall R) : Prop :=
  boundaryDilatationStarK μ.1 = boundaryDilatationH p (Quot.mk (teichRel p) μ)

/-- **Definition** (§15 introduction, l. 11262–11266). `μ` is an asymptotically extremal representative of the class
of `V` in `Z/Z₀`: it represents `V` modulo `Z₀` and `b*(μ) = b(V)`. -/
def IsInfAsymExtremal (V : (R → ℂ → ℂ) → ℂ) (μ : R → ℂ → ℂ) : Prop :=
  μ ∈ beltramiSpace R ∧ (fun φ => pairingRS φ μ) - V ∈ zZeroSpace R ∧
    boundaryDilatationStar μ = infBoundaryDilatation V

/-- Helper (§15.1, l. 11269). The Beltrami differential `μ` vanishes on `E ⊆ R`. -/
def IsVanishingOn (μ : R → ℂ → ℂ) (E : Set R) : Prop := beltramiNormRS (restrictBeltrami μ E) = 0

/-- **Definition** (§15.1, l. 11269). The norm of `L∞(E, F, α)`:
`‖μ‖ = max {‖μ|_{R∖F}‖∞, α⁻¹ ‖μ|_{F∖E}‖∞}`. -/
def weightedNormInf (E F : Set R) (α : ℝ) (μ : R → ℂ → ℂ) : ℝ≥0∞ :=
  max (beltramiNormRS (restrictBeltrami μ Fᶜ)) (ENNReal.ofReal α⁻¹ * beltramiNormRS (restrictBeltrami μ (F \ E)))

/-- **Definition** (§15.1, l. 11275). The norm of `L₁(E, F, α)` and `A(E, F, α)`:
`‖f‖ = ∬_{R∖F} |f| + α ∬_{F∖E} |f|`. -/
def weightedNormL1 (E F : Set R) (α : ℝ) (φ : R → ℂ → ℂ) : ℝ≥0∞ :=
  setIntegralQD φ Fᶜ + ENNReal.ofReal α * setIntegralQD φ (F \ E)

/-- Helper for `para15_1_weighted_rep`: the part of a chart target over a closed set is measurable (relatively closed
in the open target). -/
theorem gl151_measurableSet_chart {K : Set R} (hK : IsClosed K) (y : R) :
    MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' K) := by
  have h : (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' K =
      (chartAt ℂ y).target \ ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' Kᶜ) := by
    ext z
    simp only [mem_inter_iff, mem_diff, mem_preimage, mem_compl_iff]
    tauto
  rw [h]
  exact (chartAt ℂ y).open_target.measurableSet.diff
    ((chartAt ℂ y).isOpen_inter_preimage_symm hK.isOpen_compl).measurableSet

/-- Helper for `para15_1_weighted_rep`: for a set `K` with measurable parts in the charts, the restriction `μχ_K` of
a Beltrami differential is measurable in every chart, `|μ| ≤ ‖μχ_K‖∞` a.e. over `K`, and `‖μχ_K‖∞ < ∞`. -/
theorem gl151_restrict {μ : R → ℂ → ℂ} (hμ : μ ∈ beltramiSpace R) {K : Set R}
    (hK : ∀ y : R, MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' K)) :
    (∀ y : R, AEStronglyMeasurable (restrictBeltrami μ K y) (volume.restrict (chartAt ℂ y).target) ∧
      ∀ᵐ z ∂(volume.restrict (chartAt ℂ y).target), (chartAt ℂ y).symm z ∈ K →
        ‖μ y z‖ₑ ≤ beltramiNormRS (restrictBeltrami μ K)) ∧ beltramiNormRS (restrictBeltrami μ K) ≠ ⊤ := by
  classical
  obtain ⟨k, -, hbd⟩ := hμ
  have hm : ∀ y : R, AEStronglyMeasurable (restrictBeltrami μ K y) (volume.restrict (chartAt ℂ y).target) := by
    intro y
    refine ((hbd y).1.indicator (hK y)).congr ((ae_restrict_iff' (chartAt ℂ y).open_target.measurableSet).2
      (Eventually.of_forall fun z hz => ?_))
    show ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' K).indicator (μ y) z =
      if (chartAt ℂ y).symm z ∈ K then μ y z else 0
    by_cases hzK : (chartAt ℂ y).symm z ∈ K
    · rw [indicator_of_mem (show z ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' K from ⟨hz, hzK⟩),
        ite_eq_left hzK]
    · rw [indicator_of_notMem (show z ∉ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' K from fun h => hzK h.2),
        ite_eq_right hzK]
  refine ⟨fun y => ⟨hm y, ?_⟩, ?_⟩
  · filter_upwards [ae_le_eLpNormEssSup (μ := volume.restrict (chartAt ℂ y).target)
      (f := restrictBeltrami μ K y)] with z hz hzK
    rw [← eLpNorm_exponent_top (hm y)] at hz
    have e : restrictBeltrami μ K y z = μ y z := by
      show (if (chartAt ℂ y).symm z ∈ K then μ y z else 0) = μ y z
      exact ite_eq_left hzK
    rw [e] at hz
    exact hz.trans (le_iSup (fun y => eLpNorm (restrictBeltrami μ K y) ⊤ (volume.restrict (chartAt ℂ y).target)) y)
  · refine ne_top_of_le_ne_top (b := ENNReal.ofReal k) ENNReal.ofReal_ne_top (iSup_le fun y => ?_)
    rw [eLpNorm_exponent_top (hm y)]
    refine eLpNormEssSup_le_of_ae_bound ?_
    filter_upwards [(hbd y).2] with z hz
    show ‖(if (chartAt ℂ y).symm z ∈ K then μ y z else 0)‖ ≤ k
    by_cases hzK : (chartAt ℂ y).symm z ∈ K
    · rw [ite_eq_left hzK]
      exact hz
    · rw [ite_eq_right hzK, norm_zero]
      exact (norm_nonneg _).trans hz

/-- Helper for `para15_1_weighted_rep` (§15.1). The pairing is bounded by the weighted norms: for `μ` vanishing on `E`,
`|(φ, μ)| ≤ ‖μ‖_{E,F,α} ‖φ‖_{E,F,α}` (split the integral over `R ∖ F`, `F ∖ E` and `E`; compact sets of the
Hausdorff surface are closed, so the restrictions are measurable). -/
theorem gl151_pairing_le [T2Space R] [IsManifold 𝓘(ℂ) ω R] {E F : Set R} (hE : IsCompact E) (hF : IsCompact F)
    (hEF : E ⊆ F) {α : ℝ} (hα : 0 < α) {μ φ : R → ℂ → ℂ} (hμ : μ ∈ beltramiSpace R) (hμE : IsVanishingOn μ E)
    (hφ : φ ∈ integrableHolQDSet R) :
    ‖pairingRS φ μ‖ ≤ (weightedNormInf E F α μ).toReal * (weightedNormL1 E F α φ).toReal := by
  classical
  letI : ∀ p : Prop, Decidable p := fun p => Classical.propDecidable p
  have hFc := hF.isClosed
  have hEc := hE.isClosed
  have hmFc : ∀ y : R, MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' Fᶜ) := fun y =>
    ((chartAt ℂ y).isOpen_inter_preimage_symm hFc.isOpen_compl).measurableSet
  have hmFE : ∀ y : R, MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (F \ E)) := fun y => by
    have h : (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (F \ E) = ((chartAt ℂ y).target ∩
        (chartAt ℂ y).symm ⁻¹' F) ∩ ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' Eᶜ) := by
      ext z
      simp only [mem_inter_iff, mem_diff, mem_preimage, mem_compl_iff]
      tauto
    rw [h]
    exact (gl151_measurableSet_chart hFc y).inter
      ((chartAt ℂ y).isOpen_inter_preimage_symm hEc.isOpen_compl).measurableSet
  obtain ⟨h1, h1t⟩ := gl151_restrict hμ hmFc
  obtain ⟨h2, h2t⟩ := gl151_restrict hμ hmFE
  obtain ⟨h3, -⟩ := gl151_restrict hμ (gl151_measurableSet_chart hEc)
  rw [show beltramiNormRS (restrictBeltrami μ E) = 0 from hμE] at h3
  -- `‖μ|_{R∖F}‖ ≤ W`, `‖μ|_{F∖E}‖ ≤ α W` for the weighted norm `W`
  have hW1 : beltramiNormRS (restrictBeltrami μ Fᶜ) ≤ weightedNormInf E F α μ := le_max_left _ _
  have hW2 : beltramiNormRS (restrictBeltrami μ (F \ E)) ≤ ENNReal.ofReal α * weightedNormInf E F α μ := by
    calc beltramiNormRS (restrictBeltrami μ (F \ E))
        = ENNReal.ofReal α * (ENNReal.ofReal α⁻¹ * beltramiNormRS (restrictBeltrami μ (F \ E))) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hα.le, mul_inv_cancel₀ hα.ne', ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal α * weightedNormInf E F α μ := mul_le_mul_right (le_max_right _ _) _
  have hWt : weightedNormInf E F α μ ≠ ⊤ :=
    (max_lt (lt_top_iff_ne_top.2 h1t) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 h2t))).ne
  -- the chosen partition
  have h := gl31_exists_partition_of_ne_top hφ.2.ne
  have hP := h.choose_spec.choose_spec
  -- the bound on each piece
  have hind : ∀ (K : Set R), (∀ y : R, MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' K)) → ∀ i,
      AEMeasurable (fun z => (if (chartAt ℂ (h.choose i)).symm z ∈ K then (1 : ℝ≥0∞) else 0) *
        ENNReal.ofReal ‖φ (h.choose i) z‖)
        (volume.restrict (chartAt ℂ (h.choose i) '' h.choose_spec.choose i)) := by
    intro K hK i
    have hGt : chartAt ℂ (h.choose i) '' h.choose_spec.choose i ⊆ (chartAt ℂ (h.choose i)).target :=
      image_subset_iff.2 fun q hq => (chartAt ℂ (h.choose i)).map_source ((hP.1 i).1 hq)
    have hφm : AEMeasurable (fun z => ENNReal.ofReal ‖φ (h.choose i) z‖)
        (volume.restrict (chartAt ℂ (h.choose i) '' h.choose_spec.choose i)) :=
      (((hφ.1.2 (h.choose i)).continuousOn.mono hGt).aemeasurable (μ := volume) (hP.1 i).2).norm.ennreal_ofReal
    refine ((hφm.indicator (hK (h.choose i))).congr ((ae_restrict_iff' (hP.1 i).2).2
      (Eventually.of_forall fun z hz => ?_)))
    beta_reduce
    by_cases hzK : (chartAt ℂ (h.choose i)).symm z ∈ K
    · rw [indicator_of_mem (show z ∈ (chartAt ℂ (h.choose i)).target ∩ (chartAt ℂ (h.choose i)).symm ⁻¹' K from
        ⟨hGt hz, hzK⟩), ite_eq_left hzK, one_mul]
    · rw [indicator_of_notMem (show z ∉ (chartAt ℂ (h.choose i)).target ∩ (chartAt ℂ (h.choose i)).symm ⁻¹' K from
        fun h' => hzK h'.2), ite_eq_right hzK, zero_mul]
  have hpt : ∀ i, ∫⁻ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i, ‖φ (h.choose i) z * μ (h.choose i) z‖ₑ ≤
      weightedNormInf E F α μ * (∫⁻ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i,
        (if (chartAt ℂ (h.choose i)).symm z ∈ Fᶜ then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal ‖φ (h.choose i) z‖) +
      ENNReal.ofReal α * weightedNormInf E F α μ * ∫⁻ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i,
        (if (chartAt ℂ (h.choose i)).symm z ∈ F \ E then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal ‖φ (h.choose i) z‖ := by
    intro i
    have hGt : chartAt ℂ (h.choose i) '' h.choose_spec.choose i ⊆ (chartAt ℂ (h.choose i)).target :=
      image_subset_iff.2 fun q hq => (chartAt ℂ (h.choose i)).map_source ((hP.1 i).1 hq)
    calc ∫⁻ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i, ‖φ (h.choose i) z * μ (h.choose i) z‖ₑ
        ≤ ∫⁻ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i,
          (weightedNormInf E F α μ * ((if (chartAt ℂ (h.choose i)).symm z ∈ Fᶜ then (1 : ℝ≥0∞) else 0) *
            ENNReal.ofReal ‖φ (h.choose i) z‖) + ENNReal.ofReal α * weightedNormInf E F α μ *
            ((if (chartAt ℂ (h.choose i)).symm z ∈ F \ E then (1 : ℝ≥0∞) else 0) *
              ENNReal.ofReal ‖φ (h.choose i) z‖)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hGt ((h1 (h.choose i)).2),
            ae_restrict_of_ae_restrict_of_subset hGt ((h2 (h.choose i)).2),
            ae_restrict_of_ae_restrict_of_subset hGt ((h3 (h.choose i)).2)] with z hz1 hz2 hz3
          rw [enorm_mul, ← ofReal_norm]
          by_cases hzF : (chartAt ℂ (h.choose i)).symm z ∈ F
          · by_cases hzE : (chartAt ℂ (h.choose i)).symm z ∈ E
            · rw [le_antisymm (hz3 hzE) zero_le, mul_zero]
              exact zero_le
            · have hFE : (chartAt ℂ (h.choose i)).symm z ∈ F \ E := ⟨hzF, hzE⟩
              rw [ite_eq_right (fun h' : (chartAt ℂ (h.choose i)).symm z ∈ Fᶜ => h' hzF), ite_eq_left hFE,
                zero_mul, mul_zero, zero_add, one_mul, mul_comm (ENNReal.ofReal ‖φ (h.choose i) z‖)]
              exact mul_le_mul_left ((hz2 hFE).trans hW2) _
          · rw [ite_eq_left (show (chartAt ℂ (h.choose i)).symm z ∈ Fᶜ from hzF),
              ite_eq_right (fun h' : (chartAt ℂ (h.choose i)).symm z ∈ F \ E => hzF h'.1),
              zero_mul, mul_zero, add_zero, one_mul, mul_comm (ENNReal.ofReal ‖φ (h.choose i) z‖)]
            exact mul_le_mul_left ((hz1 hzF).trans hW1) _
      _ = _ := by
          refine (lintegral_add_left' ((hind Fᶜ hmFc i).const_mul _) _).trans ?_
          rw [lintegral_const_mul'' _ (hind Fᶜ hmFc i), lintegral_const_mul'' _ (hind (F \ E) hmFE i)]
  -- sum over the partition chosen in `pairingRS`; partition independence of the surface integrals
  have hS : ∀ K : Set R, setIntegralQD φ K = ∑' i, ∫⁻ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i,
      (if (chartAt ℂ (h.choose i)).symm z ∈ K then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal ‖φ (h.choose i) z‖ :=
    fun K => LiZhongQC.s26v_surfaceIntegral_eq_tsum hφ.1 (fun p => if p ∈ K then (1 : ℝ≥0∞) else 0) hP
  have hbound : ‖pairingRS φ μ‖ₑ ≤ weightedNormInf E F α μ * weightedNormL1 E F α φ := by
    rw [gl31_pairingRS_eq φ μ h]
    calc _ ≤ ∑' i, ‖∫ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i,
          φ (h.choose i) z * μ (h.choose i) z‖ₑ := enorm_tsum_le_tsum_enorm
      _ ≤ ∑' i, ∫⁻ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i,
          ‖φ (h.choose i) z * μ (h.choose i) z‖ₑ :=
          ENNReal.tsum_le_tsum fun i => enorm_integral_le_lintegral_enorm _
      _ ≤ _ := ENNReal.tsum_le_tsum hpt
      _ = weightedNormInf E F α μ * weightedNormL1 E F α φ := by
          show _ = weightedNormInf E F α μ * (setIntegralQD φ Fᶜ + ENNReal.ofReal α * setIntegralQD φ (F \ E))
          rw [hS Fᶜ, hS (F \ E), ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
          ring
  -- the weighted `L¹` norm is finite (at most `‖φ‖` up to the weight)
  have hW1t : weightedNormL1 E F α φ ≠ ⊤ := by
    have hle : ∀ K : Set R, setIntegralQD φ K ≤ LiZhongQC.quadDiffNorm φ := fun K => by
      rw [hS K]
      have e := LiZhongQC.s26v_surfaceIntegral_eq_tsum hφ.1 (fun _ => (1 : ℝ≥0∞)) hP
      simp only [one_mul] at e
      rw [show LiZhongQC.quadDiffNorm φ = _ from e]
      refine ENNReal.tsum_le_tsum fun i => lintegral_mono fun z => ?_
      by_cases hzK : (chartAt ℂ (h.choose i)).symm z ∈ K
      · rw [ite_eq_left hzK, one_mul]
      · rw [ite_eq_right hzK, zero_mul]
        exact zero_le
    exact (ENNReal.add_lt_top.2 ⟨(hle _).trans_lt hφ.2,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((hle _).trans_lt hφ.2)⟩).ne
  calc ‖pairingRS φ μ‖ = (‖pairingRS φ μ‖ₑ).toReal := (toReal_enorm _).symm
    _ ≤ (weightedNormInf E F α μ * weightedNormL1 E F α φ).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hWt hW1t) hbound
    _ = (weightedNormInf E F α μ).toReal * (weightedNormL1 E F α φ).toReal := ENNReal.toReal_mul

/-- Helper for `gl151_rep_exists` (§15.1). The weighted `L¹` model of `A(R)` on a chart partition `(x, P)`: as
`gl31_model`, with the chart function `φ_{xᵢ}` replaced by `W(φ_{xᵢ}⁻¹ z) φ_{xᵢ}(z)`, `W : R → ℂ` a bounded weight
that is measurable in every chart. `∫_S |E φ| = Σᵢ ∬_{φ_{xᵢ}(Pᵢ)} |W∘φ_{xᵢ}⁻¹| |φ_{xᵢ}|` for holomorphic `φ`; a bounded
`ν` on `S` pulls back to chart functions `gᵢ` of the same bound with
`∬_S ν E φ = Σᵢ ∬_{φ_{xᵢ}(Pᵢ)} (W∘φ_{xᵢ}⁻¹) φ_{xᵢ} gᵢ` for `φ ∈ A(R)`. -/
theorem gl151_wmodel [IsManifold 𝓘(ℂ) ω R] {x : ℕ → R} {P : ℕ → Set R} (hP : LiZhongQC.IsChartPartition R x P)
    {W : R → ℂ} {M : ℝ} (hWb : ∀ q, ‖W q‖ ≤ M)
    (hWm : ∀ y : R, AEStronglyMeasurable (fun z => W ((chartAt ℂ y).symm z))
      (volume.restrict (chartAt ℂ y).target)) :
    ∃ (S : Set ℂ) (E : (R → ℂ → ℂ) → ℂ → ℂ), MeasurableSet S ∧
      (∀ φ ψ, E (φ + ψ) = E φ + E ψ) ∧ (∀ (c : ℂ) φ, E (c • φ) = c • E φ) ∧
      (∀ φ ∈ LiZhongQC.holQuadDiffSubmodule R,
        AEStronglyMeasurable (E φ) (volume.restrict S) ∧ ∫⁻ w in S, ‖E φ w‖ₑ =
          ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖W ((chartAt ℂ (x i)).symm z)‖ₑ * ‖φ (x i) z‖ₑ) ∧
      ∀ ν : ℂ → ℂ, AEStronglyMeasurable ν (volume.restrict S) → ∀ c : ℝ, (∀ᵐ w ∂(volume.restrict S), ‖ν w‖ ≤ c) →
        ∃ g : ℕ → ℂ → ℂ, (∀ i, AEStronglyMeasurable (g i) (volume.restrict (chartAt ℂ (x i) '' P i))) ∧
          (∀ i, ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)), ‖g i z‖ ≤ c) ∧
          ∀ φ ∈ integrableHolQDSet R,
            ∫ w in S, ν w * E φ w =
              ∑' i, ∫ z in chartAt ℂ (x i) '' P i, (W ((chartAt ℂ (x i)).symm z) * φ (x i) z) * g i z := by
  obtain ⟨ι, piece, t, hpm, hpU, hpd, htd⟩ := gl31_cells hP
  have hQm : ∀ m, MeasurableSet ((fun w => w + t m) '' piece m) := fun m => by
    rw [image_add_right]
    exact measurable_add_const (-t m) (hpm m).1
  have hSm : MeasurableSet (⋃ m, (fun w => w + t m) '' piece m) := MeasurableSet.iUnion hQm
  have hemb : ∀ m, MeasurableEmbedding fun z : ℂ => z + t m := fun m => measurableEmbedding_addRight (t m)
  have hmpr : ∀ m, MeasurePreserving (fun z : ℂ => z + t m) (volume.restrict (piece m))
      (volume.restrict ((fun w => w + t m) '' piece m)) := fun m =>
    (measurePreserving_add_right volume (t m)).restrict_image_emb (hemb m) (piece m)
  have hfib : ∀ i, chartAt ℂ (x i) '' P i = ⋃ m : ι ⁻¹' {i}, piece m := fun i => by
    rw [hpU i]
    ext w
    simp only [mem_iUnion, exists_prop, Subtype.exists, mem_preimage, mem_singleton_iff]
  have hval : ∀ (F : ℕ → ℂ → ℂ) m, ∀ w ∈ (fun w => w + t m) '' piece m,
      ∑' m', ((fun w => w + t m') '' piece m').indicator (F m') w = F m w := by
    intro F m w hw
    rw [tsum_eq_single m fun m' hm' => indicator_of_notMem (fun hw' => Set.disjoint_left.1 (htd hm') hw' hw) _,
      indicator_of_mem hw]
  have hval0 : ∀ (F : ℕ → ℂ → ℂ) w, w ∉ ⋃ m, (fun w => w + t m) '' piece m →
      ∑' m', ((fun w => w + t m') '' piece m').indicator (F m') w = 0 := fun F w hw =>
    (tsum_congr fun m => indicator_of_notMem (fun h => hw (mem_iUnion.2 ⟨m, h⟩)) _).trans tsum_zero
  obtain ⟨E, hEdef⟩ : ∃ E : (R → ℂ → ℂ) → ℂ → ℂ, E = fun φ w =>
      ∑' m, ((fun w => w + t m) '' piece m).indicator
        (fun w => W ((chartAt ℂ (x (ι m))).symm (w - t m)) * φ (x (ι m)) (w - t m)) w := ⟨_, rfl⟩
  have hE : ∀ φ m, ∀ w ∈ (fun w => w + t m) '' piece m,
      E φ w = W ((chartAt ℂ (x (ι m))).symm (w - t m)) * φ (x (ι m)) (w - t m) := by
    intro φ m w hw
    rw [hEdef]
    exact hval (fun m w => W ((chartAt ℂ (x (ι m))).symm (w - t m)) * φ (x (ι m)) (w - t m)) m w hw
  have hE0 : ∀ φ w, w ∉ ⋃ m, (fun w => w + t m) '' piece m → E φ w = 0 := by
    intro φ w hw
    rw [hEdef]
    exact hval0 (fun m w => W ((chartAt ℂ (x (ι m))).symm (w - t m)) * φ (x (ι m)) (w - t m)) w hw
  have hGt : ∀ i, chartAt ℂ (x i) '' P i ⊆ (chartAt ℂ (x i)).target := fun i =>
    image_subset_iff.2 fun y hy => (chartAt ℂ (x i)).map_source ((hP.1 i).1 hy)
  have hcont : ∀ φ ∈ LiZhongQC.holQuadDiffSubmodule R, ∀ i,
      AEStronglyMeasurable (φ (x i)) (volume.restrict (chartAt ℂ (x i) '' P i)) := fun φ hφ i =>
    ((hφ.2 (x i)).continuousOn.mono (hGt i)).aestronglyMeasurable (hP.1 i).2
  have hcontW : ∀ φ ∈ LiZhongQC.holQuadDiffSubmodule R, ∀ i,
      AEStronglyMeasurable (fun z => W ((chartAt ℂ (x i)).symm z) * φ (x i) z)
        (volume.restrict (chartAt ℂ (x i) '' P i)) := fun φ hφ i =>
    ((hWm (x i)).mono_measure (Measure.restrict_mono (hGt i) le_rfl)).mul (hcont φ hφ i)
  have hnorm : ∀ φ ∈ LiZhongQC.holQuadDiffSubmodule R,
      LiZhongQC.quadDiffNorm φ = ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖φ (x i) z‖ₑ := by
    intro φ hφ
    have e := LiZhongQC.s26v_surfaceIntegral_eq_tsum hφ (fun _ => (1 : ℝ≥0∞)) hP
    simp only [one_mul, ofReal_norm] at e
    exact e
  refine ⟨⋃ m, (fun w => w + t m) '' piece m, E, hSm, fun φ ψ => ?_, fun c φ => ?_, fun φ hφ => ?_, ?_⟩
  · funext w
    by_cases hw : w ∈ ⋃ m, (fun w => w + t m) '' piece m
    · obtain ⟨m, hm⟩ := mem_iUnion.1 hw
      simp only [Pi.add_apply, hE (φ + ψ) m w hm, hE φ m w hm, hE ψ m w hm]
      ring
    · simp only [Pi.add_apply, hE0 (φ + ψ) w hw, hE0 φ w hw, hE0 ψ w hw, add_zero]
  · funext w
    by_cases hw : w ∈ ⋃ m, (fun w => w + t m) '' piece m
    · obtain ⟨m, hm⟩ := mem_iUnion.1 hw
      simp only [Pi.smul_apply, hE (c • φ) m w hm, hE φ m w hm, smul_eq_mul]
      ring
    · simp only [Pi.smul_apply, hE0 (c • φ) w hw, hE0 φ w hw, smul_zero]
  · have hci := gl31_cells_integral hpm hpU hpd htd (fun i z => W ((chartAt ℂ (x i)).symm z) * φ (x i) z)
    have hEe : E φ = fun w =>
        ∑' m, ((fun w => w + t m) '' piece m).indicator
          (fun w => W ((chartAt ℂ (x (ι m))).symm (w - t m)) * φ (x (ι m)) (w - t m)) w := by
      rw [hEdef]
    refine ⟨?_, ?_⟩
    · rw [hEe]
      exact (hci.2 (hcontW φ hφ)).1
    · rw [hEe, hci.1]
      exact tsum_congr fun i => lintegral_congr fun z => enorm_mul _ _
  · intro ν hν c hc
    obtain ⟨g, hgdef⟩ : ∃ g : ℕ → ℂ → ℂ, g = fun i z =>
        ∑' m, if ι m = i then (piece m).indicator (fun z => ν (z + t m)) z else 0 := ⟨_, rfl⟩
    have hg : ∀ i m, ι m = i → ∀ z ∈ piece m, g i z = ν (z + t m) := by
      intro i m hmi z hz
      rw [hgdef]
      refine (tsum_eq_single m fun m' hm' => ?_).trans (by rw [ite_eq_left hmi, indicator_of_mem hz])
      by_cases h' : ι m' = i
      · rw [ite_eq_left h']
        exact indicator_of_notMem (fun hz' => Set.disjoint_left.1 (hpd hm' (h'.trans hmi.symm)) hz' hz) _
      · rw [ite_eq_right h']
    have hνm : ∀ m, AEStronglyMeasurable (fun z => ν (z + t m)) (volume.restrict (piece m)) := fun m =>
      (hν.mono_measure (Measure.restrict_mono (subset_iUnion (fun m => (fun w => w + t m) '' piece m) m)
        le_rfl)).comp_quasiMeasurePreserving (hmpr m).quasiMeasurePreserving
    have hνb : ∀ m, ∀ᵐ z ∂(volume.restrict (piece m)), ‖ν (z + t m)‖ ≤ c := fun m =>
      (hmpr m).quasiMeasurePreserving.ae
        (ae_restrict_of_ae_restrict_of_subset (subset_iUnion (fun m => (fun w => w + t m) '' piece m) m) hc)
    have hgm : ∀ i, AEStronglyMeasurable (g i) (volume.restrict (chartAt ℂ (x i) '' P i)) := by
      intro i
      rw [hfib i]
      refine aestronglyMeasurable_iUnion_iff.2 fun m => (hνm m).congr ?_
      exact (ae_restrict_iff' (hpm m).1).2 (Eventually.of_forall fun z hz => (hg i m m.2 z hz).symm)
    have hgb : ∀ i, ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)), ‖g i z‖ ≤ c := by
      intro i
      rw [hfib i]
      refine (ae_restrict_iUnion_iff _ _).2 fun m => ?_
      filter_upwards [hνb m, ae_restrict_mem (hpm m).1] with z hz hzm
      rw [hg i m m.2 z hzm]
      exact hz
    refine ⟨g, hgm, hgb, fun φ hφ => ?_⟩
    have hci := gl31_cells_integral hpm hpU hpd htd
      (fun i z => (W ((chartAt ℂ (x i)).symm z) * φ (x i) z) * g i z)
    have hfm : ∀ i, AEStronglyMeasurable (fun z => (W ((chartAt ℂ (x i)).symm z) * φ (x i) z) * g i z)
        (volume.restrict (chartAt ℂ (x i) '' P i)) := fun i => (hcontW φ hφ.1 i).mul (hgm i)
    have hfin : ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖(W ((chartAt ℂ (x i)).symm z) * φ (x i) z) * g i z‖ₑ < ⊤ := by
      calc _ ≤ ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal M * ENNReal.ofReal c * ‖φ (x i) z‖ₑ :=
            ENNReal.tsum_le_tsum fun i => lintegral_mono_ae (by
              filter_upwards [hgb i] with z hz
              have hW1 : ‖W ((chartAt ℂ (x i)).symm z)‖ₑ ≤ ENNReal.ofReal M := by
                rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hWb _)
              have hg1 : ‖g i z‖ₑ ≤ ENNReal.ofReal c := by
                rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal hz
              calc ‖(W ((chartAt ℂ (x i)).symm z) * φ (x i) z) * g i z‖ₑ
                  = ‖W ((chartAt ℂ (x i)).symm z)‖ₑ * ‖φ (x i) z‖ₑ * ‖g i z‖ₑ := by rw [enorm_mul, enorm_mul]
                _ ≤ ENNReal.ofReal M * ‖φ (x i) z‖ₑ * ENNReal.ofReal c := by gcongr
                _ = ENNReal.ofReal M * ENNReal.ofReal c * ‖φ (x i) z‖ₑ := by ring)
        _ = ENNReal.ofReal M * ENNReal.ofReal c * LiZhongQC.quadDiffNorm φ := by
            rw [hnorm φ hφ.1, ← ENNReal.tsum_mul_left]
            exact tsum_congr fun i => lintegral_const_mul' _ _
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hφ.2
    refine (setIntegral_congr_fun hSm fun w hw => ?_).trans ((hci.2 hfm).2 hfin)
    obtain ⟨m, hm⟩ := mem_iUnion.1 hw
    rw [hE φ m w hm, hval _ m w hm]
    obtain ⟨z, hz, rfl⟩ := hm
    simp only [add_sub_cancel_right, hg (ι m) m rfl z hz]
    ring


/-- Helper for `gl151_rep_exists` (§15.1). The weight `W = 1` on `R ∖ F`, `α` on `F ∖ E`, `0` on `E` is measurable in
every chart (for closed `E`, `F`). -/
theorem gl151_weight_meas {E F : Set R} (hE : IsClosed E) (hF : IsClosed F) {α : ℝ} {W : R → ℂ}
    (hW1 : ∀ q, q ∉ F → W q = 1) (hW2 : ∀ q, q ∈ F → q ∉ E → W q = (α : ℂ)) (hW3 : ∀ q, q ∈ E → W q = 0) (y : R) :
    AEStronglyMeasurable (fun z => W ((chartAt ℂ y).symm z)) (volume.restrict (chartAt ℂ y).target) := by
  classical
  have hTF := gl151_measurableSet_chart hF y
  have hTE := gl151_measurableSet_chart hE y
  refine (Measurable.aestronglyMeasurable (f := ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' F).piecewise
    (((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' E).piecewise (fun _ => (0 : ℂ)) (fun _ => (α : ℂ)))
    (fun _ => (1 : ℂ))) (Measurable.piecewise hTF (Measurable.piecewise hTE measurable_const measurable_const)
      measurable_const)).congr ((ae_restrict_iff' (chartAt ℂ y).open_target.measurableSet).2
    (Eventually.of_forall fun z hz => ?_))
  beta_reduce
  by_cases hzF : (chartAt ℂ y).symm z ∈ F
  · rw [Set.piecewise_eq_of_mem _ _ _ (show z ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' F from ⟨hz, hzF⟩)]
    by_cases hzE : (chartAt ℂ y).symm z ∈ E
    · rw [Set.piecewise_eq_of_mem _ _ _ (show z ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' E from ⟨hz, hzE⟩),
        hW3 _ hzE]
    · rw [Set.piecewise_eq_of_notMem _ _ _
        (show z ∉ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' E from fun h => hzE h.2), hW2 _ hzF hzE]
  · rw [Set.piecewise_eq_of_notMem _ _ _
      (show z ∉ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' F from fun h => hzF h.2), hW1 _ hzF]

open scoped Classical in
/-- Helper for `gl151_rep_exists` (§15.1). The part of `K` in the chart images of a partition: the function
`𝟙_K(φ_{xᵢ}⁻¹ z) |φ_{xᵢ}(z)|` is a.e.-measurable on `φ_{xᵢ}(Pᵢ)` when `K` has measurable parts in all charts. -/
theorem gl151_ind_meas [IsManifold 𝓘(ℂ) ω R] {x : ℕ → R} {P : ℕ → Set R}
    (hP : LiZhongQC.IsChartPartition R x P) {φ : R → ℂ → ℂ}
    (hφ : φ ∈ LiZhongQC.holQuadDiffSubmodule R) {K : Set R}
    (hK : ∀ y : R, MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' K)) (i : ℕ) :
    AEMeasurable (fun z => (if (chartAt ℂ (x i)).symm z ∈ K then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal ‖φ (x i) z‖)
      (volume.restrict (chartAt ℂ (x i) '' P i)) := by
  classical
  have hGt : chartAt ℂ (x i) '' P i ⊆ (chartAt ℂ (x i)).target :=
    image_subset_iff.2 fun q hq => (chartAt ℂ (x i)).map_source ((hP.1 i).1 hq)
  have hφm : AEMeasurable (fun z => ENNReal.ofReal ‖φ (x i) z‖) (volume.restrict (chartAt ℂ (x i) '' P i)) :=
    (((hφ.2 (x i)).continuousOn.mono hGt).aemeasurable (μ := volume) (hP.1 i).2).norm.ennreal_ofReal
  refine ((hφm.indicator (hK (x i))).congr ((ae_restrict_iff' (hP.1 i).2).2
    (Eventually.of_forall fun z hz => ?_)))
  beta_reduce
  by_cases hzK : (chartAt ℂ (x i)).symm z ∈ K
  · rw [indicator_of_mem (show z ∈ (chartAt ℂ (x i)).target ∩ (chartAt ℂ (x i)).symm ⁻¹' K from ⟨hGt hz, hzK⟩),
      ite_eq_left hzK, one_mul]
  · rw [indicator_of_notMem (show z ∉ (chartAt ℂ (x i)).target ∩ (chartAt ℂ (x i)).symm ⁻¹' K from
      fun h' => hzK h'.2), ite_eq_right hzK, zero_mul]

/-- Helper for `gl151_rep_exists` (§15.1). The surface integral `‖φ‖` of a holomorphic `φ` is the sum over any chart
partition `(x, P)` of the chart integrals. -/
theorem gl151_qdn_eq [IsManifold 𝓘(ℂ) ω R] {x : ℕ → R} {P : ℕ → Set R}
    (hP : LiZhongQC.IsChartPartition R x P) {φ : R → ℂ → ℂ}
    (hφ : φ ∈ LiZhongQC.holQuadDiffSubmodule R) :
    LiZhongQC.quadDiffNorm φ = ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖φ (x i) z‖ₑ := by
  have e := LiZhongQC.s26v_surfaceIntegral_eq_tsum hφ (fun _ => (1 : ℝ≥0∞)) hP
  simp only [one_mul, ofReal_norm] at e
  exact e

/-- Helper for `gl151_rep_exists` (§15.1). The weighted norm `‖φ‖_{E,F,α}` of a holomorphic `φ` is the sum over a chart
partition `(x, P)` of `∬_{φ_{xᵢ}(Pᵢ)} |W∘φ_{xᵢ}⁻¹| |φ_{xᵢ}|`, `W = 1, α, 0` on `R ∖ F`, `F ∖ E`, `E`. -/
theorem gl151_wnorm_eq [IsManifold 𝓘(ℂ) ω R] {E F : Set R} (hE : IsClosed E) (hF : IsClosed F) {α : ℝ}
    (hα : 0 < α) {W : R → ℂ} (hW1 : ∀ q, q ∉ F → W q = 1) (hW2 : ∀ q, q ∈ F → q ∉ E → W q = (α : ℂ))
    (hW3 : ∀ q, q ∈ E → W q = 0) {x : ℕ → R} {P : ℕ → Set R}
    (hP : LiZhongQC.IsChartPartition R x P) {φ : R → ℂ → ℂ} (hφ : φ ∈ LiZhongQC.holQuadDiffSubmodule R) :
    weightedNormL1 E F α φ =
      ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖W ((chartAt ℂ (x i)).symm z)‖ₑ * ‖φ (x i) z‖ₑ := by
  classical
  letI : ∀ p : Prop, Decidable p := fun p => Classical.propDecidable p
  have hmFc : ∀ y : R, MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' Fᶜ) := fun y =>
    ((chartAt ℂ y).isOpen_inter_preimage_symm hF.isOpen_compl).measurableSet
  have hmFE : ∀ y : R, MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (F \ E)) := fun y => by
    have h : (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (F \ E) = ((chartAt ℂ y).target ∩
        (chartAt ℂ y).symm ⁻¹' F) ∩ ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' Eᶜ) := by
      ext z
      simp only [mem_inter_iff, mem_diff, mem_preimage, mem_compl_iff]
      tauto
    rw [h]
    exact (gl151_measurableSet_chart hF y).inter
      ((chartAt ℂ y).isOpen_inter_preimage_symm hE.isOpen_compl).measurableSet
  have hS : ∀ K : Set R, setIntegralQD φ K = ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i,
      (if (chartAt ℂ (x i)).symm z ∈ K then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal ‖φ (x i) z‖ :=
    fun K => LiZhongQC.s26v_surfaceIntegral_eq_tsum hφ (fun p => if p ∈ K then (1 : ℝ≥0∞) else 0) hP
  show setIntegralQD φ Fᶜ + ENNReal.ofReal α * setIntegralQD φ (F \ E) = _
  rw [hS Fᶜ, hS (F \ E), ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine tsum_congr fun i => ?_
  rw [← lintegral_const_mul'' _ (gl151_ind_meas hP hφ hmFE i),
    ← lintegral_add_left' (gl151_ind_meas hP hφ hmFc i)]
  refine lintegral_congr fun z => ?_
  rw [← ofReal_norm (φ (x i) z)]
  by_cases hzF : (chartAt ℂ (x i)).symm z ∈ F
  · by_cases hzE : (chartAt ℂ (x i)).symm z ∈ E
    · rw [hW3 _ hzE, ite_eq_right (fun h' : (chartAt ℂ (x i)).symm z ∈ Fᶜ => h' hzF),
        ite_eq_right (fun h' : (chartAt ℂ (x i)).symm z ∈ F \ E => h'.2 hzE)]
      simp
    · rw [hW2 _ hzF hzE, ite_eq_right (fun h' : (chartAt ℂ (x i)).symm z ∈ Fᶜ => h' hzF),
        ite_eq_left (show (chartAt ℂ (x i)).symm z ∈ F \ E from ⟨hzF, hzE⟩),
        ← ofReal_norm ((α : ℂ)), Complex.norm_real, Real.norm_of_nonneg hα.le]
      ring
  · rw [hW1 _ hzF, ite_eq_left (show (chartAt ℂ (x i)).symm z ∈ Fᶜ from hzF),
      ite_eq_right (fun h' : (chartAt ℂ (x i)).symm z ∈ F \ E => hzF h'.1)]
    simp

/-- Helper for `gl151_rep_exists` (§15.1). A bound `b` on `μ` a.e. over `K` bounds the norm of `μχ_K`. -/
theorem gl151_restrict_le [IsManifold 𝓘(ℂ) ω R] {μ : R → ℂ → ℂ} (hμ : μ ∈ beltramiSpace R) {K : Set R}
    (hK : ∀ y : R, MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' K)) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ y : R, ∀ᵐ z ∂(volume.restrict (chartAt ℂ y).target), (chartAt ℂ y).symm z ∈ K → ‖μ y z‖ ≤ b) :
    beltramiNormRS (restrictBeltrami μ K) ≤ ENNReal.ofReal b := by
  classical
  refine iSup_le fun y => ?_
  rw [eLpNorm_exponent_top ((gl151_restrict hμ hK).1 y).1]
  refine eLpNormEssSup_le_of_ae_bound ?_
  filter_upwards [hb y] with z hz
  show ‖(if (chartAt ℂ y).symm z ∈ K then μ y z else 0)‖ ≤ b
  by_cases hzK : (chartAt ℂ y).symm z ∈ K
  · rw [ite_eq_left hzK]
    exact hz hzK
  · rw [ite_eq_right hzK, norm_zero]
    exact hb0

/-- Helper for `gl151_rep_exists` (§15.1). Multiplying a Beltrami differential by a bounded weight `W : R → ℂ` that is
measurable in every chart gives a Beltrami differential (the weight is a function on `R`, so the transformation law
is preserved). -/
theorem gl151_weighted_mem {μ₀ : R → ℂ → ℂ} (hμ₀ : μ₀ ∈ beltramiSpace R) {W : R → ℂ} {M : ℝ}
    (hWb : ∀ q, ‖W q‖ ≤ M)
    (hWm : ∀ y : R, AEStronglyMeasurable (fun z => W ((chartAt ℂ y).symm z))
      (volume.restrict (chartAt ℂ y).target)) :
    (fun y z => W ((chartAt ℂ y).symm z) * μ₀ y z) ∈ beltramiSpace R := by
  obtain ⟨k, hdiff, hcoef⟩ := hμ₀
  refine ⟨M * max k 0, ?_, fun y => ⟨(hWm y).mul (hcoef y).1, ?_⟩⟩
  · intro x y
    have hset : MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source) :=
      ((chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x).open_source).measurableSet
    filter_upwards [hdiff x y, ae_restrict_mem hset] with z hz hzm
    have hT : (chartAt ℂ x).symm (LiZhongQC.chartTransition x y z) = (chartAt ℂ y).symm z :=
      (chartAt ℂ x).left_inv hzm.2
    show W ((chartAt ℂ y).symm z) * μ₀ y z = W ((chartAt ℂ x).symm (LiZhongQC.chartTransition x y z)) *
      μ₀ x (LiZhongQC.chartTransition x y z) * deriv (LiZhongQC.chartTransition x y) z ^ (-1 : ℤ) *
      conj (deriv (LiZhongQC.chartTransition x y) z) ^ (1 : ℤ)
    rw [hT, hz]
    ring
  · filter_upwards [(hcoef y).2] with z hz
    show ‖W ((chartAt ℂ y).symm z) * μ₀ y z‖ ≤ M * max k 0
    rw [norm_mul]
    exact mul_le_mul (hWb _) (hz.trans (le_max_left _ _)) (norm_nonneg _)
      ((norm_nonneg _).trans (hWb ((chartAt ℂ y).symm z)))


/-- Helper for `gl151_rep_exists` (§15.1). The weighted Hahn–Banach representation on a fixed chart partition `(x, P)`:
the weighted `L¹` model `gl151_wmodel` with the weight `W = 1, α, 0` on `R ∖ F`, `F ∖ E`, `E`, `gl3_dual_repr` for the
functional on the image, the pull-back `g` of its density, and `μ = W · μ₀` for the extension `μ₀` of `g`
(`gl31_beltrami_extend`). -/
theorem gl151_rep_core [T2Space R] [IsManifold 𝓘(ℂ) ω R] {E F : Set R} (hE : IsCompact E) (hF : IsCompact F)
    (hEF : E ⊆ F) {α : ℝ} (hα : 0 < α) {L : (R → ℂ → ℂ) → ℂ}
    (hL : IsBoundedFunctionalOn (integrableHolQDSet R) (weightedNormL1 E F α) L) {x : ℕ → R} {P : ℕ → Set R}
    (hP : LiZhongQC.IsChartPartition R x P) :
    ∃ μ ∈ beltramiSpace R, IsVanishingOn μ E ∧
      (∀ φ ∈ integrableHolQDSet R, L φ = ∑' i, ∫ z in chartAt ℂ (x i) '' P i, φ (x i) z * μ (x i) z) ∧
      weightedNormInf E F α μ ≤ ENNReal.ofReal (dualNormOn (integrableHolQDSet R) (weightedNormL1 E F α) L) := by
  classical
  set D := dualNormOn (integrableHolQDSet R) (weightedNormL1 E F α) L with hDdef
  have hD0 : 0 ≤ D := Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
  obtain ⟨hLadd, hLsmul, C, hC⟩ := hL
  -- the weight
  obtain ⟨W, hW⟩ : ∃ W : R → ℂ, ∀ q, W q = if q ∈ F then (if q ∈ E then 0 else (α : ℂ)) else 1 :=
    ⟨_, fun _ => rfl⟩
  have hW1 : ∀ q, q ∉ F → W q = 1 := fun q hq => by rw [hW, if_neg hq]
  have hW2 : ∀ q, q ∈ F → q ∉ E → W q = (α : ℂ) := fun q hq hq' => by rw [hW, if_pos hq, if_neg hq']
  have hW3 : ∀ q, q ∈ E → W q = 0 := fun q hq => by rw [hW, if_pos (hEF hq), if_pos hq]
  have hWb : ∀ q, ‖W q‖ ≤ max 1 α := by
    intro q
    by_cases hqF : q ∈ F
    · by_cases hqE : q ∈ E
      · rw [hW3 q hqE, norm_zero]
        exact zero_le_one.trans (le_max_left _ _)
      · rw [hW2 q hqF hqE, Complex.norm_real, Real.norm_of_nonneg hα.le]
        exact le_max_right _ _
    · rw [hW1 q hqF, norm_one]
      exact le_max_left _ _
  have hWm := gl151_weight_meas hE.isClosed hF.isClosed hW1 hW2 hW3
  obtain ⟨S, Ew, hSm, hadd, hsmul, hnormEw, hback⟩ := gl151_wmodel hP hWb hWm
  -- closure of `A(R)` under the linear operations, from the unweighted model
  obtain ⟨S1, E1, hSm1, hadd1, hsmul1, hnorm1, -⟩ := gl31_model hP
  have hAadd : ∀ φ ∈ integrableHolQDSet R, ∀ ψ ∈ integrableHolQDSet R, φ + ψ ∈ integrableHolQDSet R := by
    intro φ hφ ψ hψ
    have hm := (LiZhongQC.holQuadDiffSubmodule R).add_mem hφ.1 hψ.1
    refine ⟨hm, ?_⟩
    rw [← (hnorm1 _ hm).2, hadd1]
    calc ∫⁻ w in S1, ‖(E1 φ + E1 ψ) w‖ₑ ≤ ∫⁻ w in S1, (‖E1 φ w‖ₑ + ‖E1 ψ w‖ₑ) :=
          lintegral_mono fun w => enorm_add_le _ _
      _ = (∫⁻ w in S1, ‖E1 φ w‖ₑ) + ∫⁻ w in S1, ‖E1 ψ w‖ₑ := lintegral_add_left' (hnorm1 φ hφ.1).1.enorm _
      _ < ⊤ := by
          rw [(hnorm1 φ hφ.1).2, (hnorm1 ψ hψ.1).2]
          exact ENNReal.add_lt_top.2 ⟨hφ.2, hψ.2⟩
  have hAsmul : ∀ c : ℂ, ∀ φ ∈ integrableHolQDSet R, c • φ ∈ integrableHolQDSet R := by
    intro c φ hφ
    have hm := (LiZhongQC.holQuadDiffSubmodule R).smul_mem c hφ.1
    refine ⟨hm, ?_⟩
    rw [← (hnorm1 _ hm).2, hsmul1]
    simp only [Pi.smul_apply, smul_eq_mul, enorm_mul]
    rw [lintegral_const_mul' _ _ enorm_ne_top, (hnorm1 φ hφ.1).2]
    exact ENNReal.mul_lt_top enorm_lt_top hφ.2
  -- the weighted norm is the `L¹` norm of the image, and it is finite
  have hwnorm : ∀ φ ∈ integrableHolQDSet R, ∫⁻ w in S, ‖Ew φ w‖ₑ = weightedNormL1 E F α φ := fun φ hφ => by
    rw [(hnormEw φ hφ.1).2, gl151_wnorm_eq hE.isClosed hF.isClosed hα hW1 hW2 hW3 hP hφ.1]
  have hwlt : ∀ φ ∈ integrableHolQDSet R, weightedNormL1 E F α φ < ⊤ := by
    intro φ hφ
    rw [gl151_wnorm_eq hE.isClosed hF.isClosed hα hW1 hW2 hW3 hP hφ.1]
    calc _ ≤ ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal (max 1 α) * ‖φ (x i) z‖ₑ :=
          ENNReal.tsum_le_tsum fun i => lintegral_mono fun z => by
            refine mul_le_mul_left ?_ _
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hWb _)
      _ = ENNReal.ofReal (max 1 α) * LiZhongQC.quadDiffNorm φ := by
          rw [gl151_qdn_eq hP hφ.1, ← ENNReal.tsum_mul_left]
          exact tsum_congr fun i => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφ.2
  have harea : ∀ φ ∈ integrableHolQDSet R, LiZhongQC.phiArea (Ew φ) S = weightedNormL1 E F α φ := by
    intro φ hφ
    rw [← hwnorm φ hφ]
    show ∫⁻ z in S, ENNReal.ofReal ‖Ew φ z‖ = _
    simp only [ofReal_norm]
  have hE0 : Ew 0 = 0 := by
    have e := hsmul 0 0
    rwa [zero_smul, zero_smul] at e
  have hsub : ∀ φ ψ, Ew (φ - ψ) = Ew φ - Ew ψ := fun φ ψ => by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ, hadd, hsmul, neg_one_smul, ← sub_eq_add_neg]
  -- `L` is well defined on the image `Ew(A(R))`
  have hwd : ∀ φ ∈ integrableHolQDSet R, ∀ ψ ∈ integrableHolQDSet R, Ew φ = Ew ψ → L φ = L ψ := by
    intro φ hφ ψ hψ he
    have hmem : φ - ψ ∈ integrableHolQDSet R := by
      rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ]
      exact hAadd φ hφ _ (hAsmul _ ψ hψ)
    have h0 : weightedNormL1 E F α (φ - ψ) = 0 := by
      rw [← hwnorm _ hmem, hsub, he, sub_self]
      simp
    have hL0 : L (φ - ψ) = 0 := by
      have e := hC _ hmem
      rw [h0, ENNReal.toReal_zero, mul_zero] at e
      exact norm_le_zero_iff.1 e
    rw [← sub_add_cancel φ ψ, hLadd _ hmem _ hψ, hL0, zero_add]
  obtain ⟨V', hV'def⟩ : ∃ V' : (ℂ → ℂ) → ℂ, V' = fun f =>
      if hf : ∃ φ ∈ integrableHolQDSet R, Ew φ = f then L hf.choose else 0 := ⟨_, rfl⟩
  have hV' : ∀ φ ∈ integrableHolQDSet R, V' (Ew φ) = L φ := by
    intro φ hφ
    have hex : ∃ ψ ∈ integrableHolQDSet R, Ew ψ = Ew φ := ⟨φ, hφ, rfl⟩
    simp only [hV'def]
    rw [dite_eq_left hex]
    exact hwd _ hex.choose_spec.1 _ hφ hex.choose_spec.2
  have hA'int : ∀ f ∈ Ew '' integrableHolQDSet R, IntegrableOn f S := by
    rintro _ ⟨φ, hφ, rfl⟩
    refine ⟨(hnormEw φ hφ.1).1, ?_⟩
    show ∫⁻ w, ‖Ew φ w‖ₑ ∂(volume.restrict S) < ⊤
    rw [hwnorm φ hφ]
    exact hwlt φ hφ
  have hA'0 : (0 : ℂ → ℂ) ∈ Ew '' integrableHolQDSet R := by
    refine ⟨0, ⟨(LiZhongQC.holQuadDiffSubmodule R).zero_mem, ?_⟩, hE0⟩
    have hE10 : E1 0 = 0 := by
      have e := hsmul1 0 0
      rwa [zero_smul, zero_smul] at e
    rw [← (hnorm1 0 (LiZhongQC.holQuadDiffSubmodule R).zero_mem).2, hE10]
    simp
  have hA'add : ∀ f ∈ Ew '' integrableHolQDSet R, ∀ f' ∈ Ew '' integrableHolQDSet R,
      f + f' ∈ Ew '' integrableHolQDSet R := by
    rintro _ ⟨φ, hφ, rfl⟩ _ ⟨ψ, hψ, rfl⟩
    exact ⟨φ + ψ, hAadd φ hφ ψ hψ, hadd φ ψ⟩
  have hA'smul : ∀ c : ℂ, ∀ f ∈ Ew '' integrableHolQDSet R, c • f ∈ Ew '' integrableHolQDSet R := by
    rintro c _ ⟨φ, hφ, rfl⟩
    exact ⟨c • φ, hAsmul c φ hφ, hsmul c φ⟩
  have hV'b : IsBoundedFunctionalOn (Ew '' integrableHolQDSet R) (fun f => LiZhongQC.phiArea f S) V' := by
    refine ⟨?_, ?_, C, ?_⟩
    · rintro _ ⟨φ, hφ, rfl⟩ _ ⟨ψ, hψ, rfl⟩
      rw [← hadd, hV' _ (hAadd φ hφ ψ hψ), hV' φ hφ, hV' ψ hψ, hLadd φ hφ ψ hψ]
    · rintro c _ ⟨φ, hφ, rfl⟩
      rw [← hsmul, hV' _ (hAsmul c φ hφ), hV' φ hφ, hLsmul c φ hφ]
    · rintro _ ⟨φ, hφ, rfl⟩
      show ‖V' (Ew φ)‖ ≤ C * (LiZhongQC.phiArea (Ew φ) S).toReal
      rw [hV' φ hφ, harea φ hφ]
      exact hC φ hφ
  obtain ⟨ν, hνm, hνb, hνrep⟩ := gl3_dual_repr hSm hA'int hA'0 hA'add hA'smul hV'b
  have hle : dualNormOn (Ew '' integrableHolQDSet R) (fun f => LiZhongQC.phiArea f S) V' ≤ D := by
    refine Real.iSup_le (fun f => Real.iSup_le (fun hf => ?_) hD0) hD0
    obtain ⟨⟨φ, hφ, rfl⟩, h1⟩ := hf
    rw [hV' φ hφ]
    have hφ1 : weightedNormL1 E F α φ = 1 := by
      rw [← harea φ hφ]
      exact h1
    have hbdd : BddAbove (range fun a => ⨆ (_ : a ∈ integrableHolQDSet R ∧ weightedNormL1 E F α a = 1), ‖L a‖) := by
      refine ⟨max C 0, ?_⟩
      rintro _ ⟨χ, rfl⟩
      refine Real.iSup_le (fun hχ => ?_) (le_max_right _ _)
      have e := hC χ hχ.1
      rw [hχ.2, ENNReal.toReal_one, mul_one] at e
      exact e.trans (le_max_left _ _)
    calc ‖L φ‖ = ⨆ (_ : φ ∈ integrableHolQDSet R ∧ weightedNormL1 E F α φ = 1), ‖L φ‖ :=
          (ciSup_pos (f := fun _ => ‖L φ‖) ⟨hφ, hφ1⟩).symm
      _ ≤ D := le_ciSup hbdd φ
  -- pull `ν` back to the charts of the partition and extend
  obtain ⟨g, hgm, hgb, hgrep⟩ := hback ν hνm D (by
    filter_upwards [hνb] with z hz
    exact hz.trans hle)
  obtain ⟨μ₀, hμ₀, hμ₀g, hμ₀n⟩ := gl31_beltrami_extend hP g hD0 hgm hgb
  have hμ : (fun y z => W ((chartAt ℂ y).symm z) * μ₀ y z) ∈ beltramiSpace R :=
    gl151_weighted_mem hμ₀ hWb hWm
  -- `|μ₀| ≤ D` a.e. in every chart
  have hm₀ : ∀ y : R, AEStronglyMeasurable (μ₀ y) (volume.restrict (chartAt ℂ y).target) := by
    obtain ⟨k₀, -, hc₀⟩ := hμ₀
    exact fun y => (hc₀ y).1
  have hμ0b : ∀ y : R, ∀ᵐ z ∂(volume.restrict (chartAt ℂ y).target), ‖μ₀ y z‖ ≤ D := by
    intro y
    filter_upwards [ae_le_eLpNormEssSup (μ := volume.restrict (chartAt ℂ y).target) (f := μ₀ y)] with z hz
    rw [← eLpNorm_exponent_top (hm₀ y)] at hz
    have hz' : ‖μ₀ y z‖ₑ ≤ ENNReal.ofReal D :=
      hz.trans ((le_iSup (fun y => eLpNorm (μ₀ y) ⊤ (volume.restrict (chartAt ℂ y).target)) y).trans hμ₀n)
    rw [← ofReal_norm] at hz'
    exact (ENNReal.ofReal_le_ofReal_iff hD0).1 hz'
  have hmFc : ∀ y : R, MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' Fᶜ) := fun y =>
    ((chartAt ℂ y).isOpen_inter_preimage_symm hF.isClosed.isOpen_compl).measurableSet
  have hmFE : ∀ y : R, MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (F \ E)) := fun y => by
    have h : (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (F \ E) = ((chartAt ℂ y).target ∩
        (chartAt ℂ y).symm ⁻¹' F) ∩ ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' Eᶜ) := by
      ext z
      simp only [mem_inter_iff, mem_diff, mem_preimage, mem_compl_iff]
      tauto
    rw [h]
    exact (gl151_measurableSet_chart hF.isClosed y).inter
      ((chartAt ℂ y).isOpen_inter_preimage_symm hE.isClosed.isOpen_compl).measurableSet
  refine ⟨fun y z => W ((chartAt ℂ y).symm z) * μ₀ y z, hμ, ?_, ?_, ?_⟩
  · -- vanishing on `E`
    have h := gl151_restrict_le hμ (fun y => gl151_measurableSet_chart hE.isClosed y) (b := 0) le_rfl
      (fun y => Eventually.of_forall fun z hzE => by
        show ‖W ((chartAt ℂ y).symm z) * μ₀ y z‖ ≤ 0
        rw [hW3 _ hzE, zero_mul, norm_zero])
    exact le_antisymm (by simpa using h) bot_le
  · -- the representation
    intro φ hφ
    rw [← hV' φ hφ, hνrep _ ⟨φ, hφ, rfl⟩, hgrep φ hφ]
    refine tsum_congr fun i => setIntegral_congr_fun (hP.1 i).2 fun z hz => ?_
    show (W ((chartAt ℂ (x i)).symm z) * φ (x i) z) * g i z =
      φ (x i) z * (W ((chartAt ℂ (x i)).symm z) * μ₀ (x i) z)
    rw [hμ₀g i z hz]
    ring
  · -- the weighted norm
    have h1 := gl151_restrict_le hμ hmFc (b := D) hD0 (fun y => by
      filter_upwards [hμ0b y] with z hz hzF
      show ‖W ((chartAt ℂ y).symm z) * μ₀ y z‖ ≤ D
      rw [hW1 _ hzF, one_mul]
      exact hz)
    have h2 := gl151_restrict_le hμ hmFE (b := α * D) (mul_nonneg hα.le hD0) (fun y => by
      filter_upwards [hμ0b y] with z hz hzFE
      show ‖W ((chartAt ℂ y).symm z) * μ₀ y z‖ ≤ α * D
      rw [hW2 _ hzFE.1 hzFE.2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hα.le]
      exact mul_le_mul_of_nonneg_left hz hα.le)
    show max (beltramiNormRS (restrictBeltrami _ Fᶜ)) (ENNReal.ofReal α⁻¹ *
      beltramiNormRS (restrictBeltrami _ (F \ E))) ≤ _
    refine max_le h1 ?_
    calc ENNReal.ofReal α⁻¹ * beltramiNormRS (restrictBeltrami (fun y z => W ((chartAt ℂ y).symm z) * μ₀ y z)
          (F \ E)) ≤ ENNReal.ofReal α⁻¹ * ENNReal.ofReal (α * D) := mul_le_mul_right h2 _
      _ = ENNReal.ofReal D := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 hα.le), ← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul]

/-- Helper for `para15_1_weighted_rep` (§15.1). Hahn–Banach for the weighted norm: a bounded functional on
`A(E, F, α)` is `[μ]` for a Beltrami differential `μ` vanishing on `E` with `‖μ‖_{E,F,α} ≤ ‖L‖` (`gl3_dual_repr` in the
cell picture of `gl31_cells` with the weight `1` on `R ∖ F`, `α` on `F ∖ E` and `0` on `E`; the representing function
is pulled back by `gl31_beltrami_extend` and multiplied by the weight). -/
theorem gl151_rep_exists [T2Space R] [IsManifold 𝓘(ℂ) ω R] {E F : Set R} (hE : IsCompact E) (hF : IsCompact F)
    (hEF : E ⊆ F) {α : ℝ} (hα : 0 < α) {L : (R → ℂ → ℂ) → ℂ}
    (hL : IsBoundedFunctionalOn (integrableHolQDSet R) (weightedNormL1 E F α) L) :
    ∃ μ ∈ beltramiSpace R, IsVanishingOn μ E ∧ (∀ φ ∈ integrableHolQDSet R, L φ = pairingRS φ μ) ∧
      weightedNormInf E F α μ ≤ ENNReal.ofReal (dualNormOn (integrableHolQDSet R) (weightedNormL1 E F α) L) := by
  classical
  by_cases h : ∃ (x : ℕ → R) (P : ℕ → Set R), LiZhongQC.IsChartPartition R x P
  · obtain ⟨μ, hμ, hμE, hrep, hle⟩ := gl151_rep_core hE hF hEF hα hL h.choose_spec.choose_spec
    refine ⟨μ, hμ, hμE, fun φ hφ => ?_, hle⟩
    rw [hrep φ hφ, pairingRS, dite_eq_left h]
  · -- no chart partition: `A(R)` is empty (every norm is `⊤`) and `μ = 0` works
    have hA : ∀ φ, φ ∉ integrableHolQDSet R := fun φ hφ => by exact h (gl31_exists_partition_of_ne_top hφ.2.ne)
    have h0 : (0 : R → ℂ → ℂ) ∈ beltramiSpace R := by
      refine ⟨0, fun x y => ae_of_all _ fun z => ?_, fun x => ⟨aestronglyMeasurable_const, ae_of_all _ fun z => ?_⟩⟩
      · simp
      · simp
    have hn0 : ∀ K : Set R, beltramiNormRS (restrictBeltrami (0 : R → ℂ → ℂ) K) = 0 := fun K => by
      refine le_antisymm (iSup_le fun y => ?_) bot_le
      have e : restrictBeltrami (0 : R → ℂ → ℂ) K y = 0 := by
        funext z
        simp [restrictBeltrami]
      rw [e]
      simp
    refine ⟨0, h0, hn0 E, fun φ hφ => absurd hφ (hA φ), ?_⟩
    show max (beltramiNormRS (restrictBeltrami 0 Fᶜ)) (ENNReal.ofReal α⁻¹ *
      beltramiNormRS (restrictBeltrami 0 (F \ E))) ≤ _
    rw [hn0, hn0]
    simp

/-- **Unlabelled** (§15.1, l. 11275; used in Lemmas 1 and 2). By the Hahn–Banach and Riesz representation theorems,
every bounded linear functional `L` on `A(E, F, α)` has a weighted representative: `μ ∈ L∞(E, F, α)` with `L = [μ]`
and `‖L‖ = ‖μ‖`. -/
theorem para15_1_weighted_rep [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {E F : Set R} (hE : IsCompact E)
    (hF : IsCompact F) (hEF : E ⊆ F) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {L : (R → ℂ → ℂ) → ℂ}
    (hL : IsBoundedFunctionalOn (integrableHolQDSet R) (weightedNormL1 E F α) L) :
    ∃ μ ∈ beltramiSpace R, IsVanishingOn μ E ∧ (∀ φ ∈ integrableHolQDSet R, L φ = pairingRS φ μ) ∧
      (weightedNormInf E F α μ).toReal = dualNormOn (integrableHolQDSet R) (weightedNormL1 E F α) L := by
  -- `α ≤ 1` and `ConnectedSpace R` are not needed: the weighted Hahn–Banach works for every `α > 0`
  have _hα1 := hα1
  obtain ⟨μ, hμ, hμE, hrep, hle⟩ := gl151_rep_exists hE hF hEF hα hL
  have hD0 : 0 ≤ dualNormOn (integrableHolQDSet R) (weightedNormL1 E F α) L :=
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
  refine ⟨μ, hμ, hμE, hrep, le_antisymm (ENNReal.toReal_le_of_le_ofReal hD0 hle) ?_⟩
  -- every representative has weighted norm at least `‖L‖`
  refine Real.iSup_le (fun φ => Real.iSup_le (fun hφ => ?_) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
  rw [hrep φ hφ.1]
  calc ‖pairingRS φ μ‖ ≤ (weightedNormInf E F α μ).toReal * (weightedNormL1 E F α φ).toReal :=
        gl151_pairing_le hE hF hEF hα hμ hμE hφ.1
    _ = (weightedNormInf E F α μ).toReal := by rw [hφ.2, ENNReal.toReal_one, mul_one]

/-- **Lemma 1** (§15.1, l. 11277). Let `ν` be a Beltrami differential and `0 < α < 1`. For every `ε > 0` there is a
compact `E₀` such that for every compact `E ⊇ E₀` there is a compact `F ⊇ E` for which `L = [νχ_{R∖F}]` on
`A(E, F, α)` satisfies `‖L‖ < ‖ν‖∞ / (1 + α(‖ν‖∞ − b(ν))/(‖ν‖∞ + b(ν))) + ε`. -/
theorem lemma15_1 [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {ν : R → ℂ → ℂ} (hν : ν ∈ beltramiSpace R)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ E₀ : Set R, IsCompact E₀ ∧ ∀ E : Set R, IsCompact E → E₀ ⊆ E → ∃ F : Set R, IsCompact F ∧ E ⊆ F ∧
      dualNormOn (integrableHolQDSet R) (weightedNormL1 E F α) (fun φ => pairingRS φ (restrictBeltrami ν Fᶜ)) <
        (beltramiNormRS ν).toReal / (1 + α * ((beltramiNormRS ν).toReal -
          (infBoundaryDilatation fun φ => pairingRS φ ν).toReal) / ((beltramiNormRS ν).toReal +
          (infBoundaryDilatation fun φ => pairingRS φ ν).toReal)) + ε := by
  sorry

end GardinerLakic2000
