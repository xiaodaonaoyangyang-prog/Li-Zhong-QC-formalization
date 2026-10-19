import LiZhongQC.Lemmas.GeodesicLeftEndpoints
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real
noncomputable section
namespace LiZhongQC

/-- Equality in the Euclidean broken-line inequality is a radial segment,
with the coefficient in the actual interval [0,1]. -/
theorem s25gb_flat_triangle_radial {a b : ℂ} (hb : b ≠ 0)
    (h : ‖a‖ + ‖b - a‖ ≤ ‖b‖) :
    ∃ c ∈ Icc (0 : ℝ) 1, a = c • b := by
  by_cases ha : a = 0
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simpa using ha⟩
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnb : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hnorm : ‖a‖ ≤ ‖b‖ := by linarith [norm_nonneg (b - a)]
  have hsub : b / a - 1 = (b - a) / a := by field_simp
  have hratio : 1 + ‖b / a - 1‖ ≤ ‖b / a‖ := by
    rw [hsub, norm_div, norm_div]
    calc
      1 + ‖b - a‖ / ‖a‖ = (‖a‖ + ‖b - a‖) / ‖a‖ := by field_simp
      _ ≤ ‖b‖ / ‖a‖ := div_le_div_of_nonneg_right h hna.le
  have he := s25ep_norm_triangle_equality hratio
  have hba : b = ((‖b‖ / ‖a‖ : ℝ) : ℂ) * a := by
    apply (div_eq_iff ha).1
    simpa only [norm_div] using he
  refine ⟨‖a‖ / ‖b‖, ⟨by positivity, (div_le_one hnb).2 hnorm⟩, ?_⟩
  have hcancel : (‖a‖ / ‖b‖) • (((‖b‖ / ‖a‖ : ℝ) : ℂ) * a) = a := by
    rw [← Complex.real_smul, smul_smul]
    have hquot : (‖a‖ / ‖b‖) * (‖b‖ / ‖a‖) = 1 := by field_simp
    rw [hquot, one_smul]
  exact ((congrArg (fun z : ℂ => (‖a‖ / ‖b‖) • z) hba).trans hcancel).symm

/-- The distance to any fixed point is a valid model potential for degree
zero. This is used on each half of a flat minimizing segment. -/
theorem s25gb_flat_distance_potential (a : ℂ) :
    ∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
      |‖y - a‖ - ‖x - a‖| ≤
        ((((0 : ℕ) : ℝ) + 2) / 2 * ‖x‖ ^ ((((0 : ℕ) : ℝ) + 2) / 2 - 1) + ε) * ‖y - x‖ := by
  intro x ε hε
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hnorm : |‖y - a‖ - ‖x - a‖| ≤ ‖y - x‖ := by
    simpa using abs_norm_sub_norm_le (y - a) (x - a)
  norm_num
  exact hnorm.trans (by nlinarith [norm_nonneg (y - x)])

/-- An actual minimizing segment in a flat natural chart is no longer than
the sum of the two radial endpoint costs. The installed flat connector is
transported back through the chart. -/
theorem s25gb_flat_minimizing_upper {φ ζ : ℂ → ℂ} {D W : Set ℂ} {r : ℝ}
    (hr : 0 < r) (hW : IsOpen W) (hWD : W ⊆ D)
    (hζ : IsConformalOnto ζ W (ball (0 : ℂ) r))
    (hq : ∀ z ∈ W, φ z = (((0 : ℕ) : ℂ) + 2) ^ 2 / 4 * deriv ζ z ^ 2)
    (γ : LRCurve) {s t : ℝ} (hs : γ.toFun s ∈ W) (ht : γ.toFun t ∈ W)
    (hmin : phiSegmentLength φ γ s t = metricDist D (phiDensity φ) (γ.toFun s) (γ.toFun t)) :
    phiSegmentLength φ γ s t ≤ ENNReal.ofReal (‖ζ (γ.toFun s)‖ + ‖ζ (γ.toFun t)‖) := by
  have hq' : ∀ z ∈ W, φ z = ((((0 : ℕ) : ℂ) + 2) / 2) ^ 2 * ζ z ^ (0 : ℕ) * deriv ζ z ^ 2 := by
    intro z hz
    have h := hq z hz
    norm_num at h ⊢
    exact h
  obtain ⟨G, hG, hGa, hGb, hGle, σ, hσ, hlen⟩ :=
    s25e_cone_flat 0 rfl hr (hζ.mapsTo hs) (hζ.mapsTo ht)
  have hupper : phiSegmentLength φ γ s t ≤
      phiLength (fun w : ℂ => ((((0 : ℕ) : ℂ) + 2) / 2) ^ 2 * w ^ (0 : ℕ)) σ := by
    rw [hmin]
    apply (s25za_dist_mono hWD (phiDensity φ) (γ.toFun s) (γ.toFun t)).trans
    rw [s25za_chart_distance 0 hW isOpen_ball hζ hq' hs ht]
    exact iInf₂_le σ hσ
  exact (hupper.trans hlen).trans (ENNReal.ofReal_le_ofReal (by simpa using hGle))

/-- Degree-zero version of the actual right radiality theorem. Equality of
the original curve's length with its distance forces equality in the ordinary
Euclidean triangle inequality in the common natural chart. -/
theorem s25gb_flat_minimizing_radial {φ ζ : ℂ → ℂ} {D W : Set ℂ} {r : ℝ}
    (hW : IsOpen W) (hWD : W ⊆ D) (hζ : IsConformalOnto ζ W (ball (0 : ℂ) r))
    (hq : ∀ z ∈ W, φ z = ((((0 : ℕ) : ℂ) + 2) / 2) ^ 2 * ζ z ^ (0 : ℕ) * deriv ζ z ^ 2)
    (γ : LRCurve) {K : ℝ≥0} {s t : ℝ} (hst : s ≤ t)
    (hK : LipschitzOnWith K γ.toFun (Icc s t)) (hmap : MapsTo γ.toFun (Icc s t) W)
    (hz : ζ (γ.toFun s) = 0) (hb : ζ (γ.toFun t) ≠ 0)
    (hmin : phiSegmentLength φ γ s t = metricDist D (phiDensity φ) (γ.toFun s) (γ.toFun t)) :
    ∀ u ∈ Icc s t, ∃ c ∈ Icc (0 : ℝ) 1, ζ (γ.toFun u) = c • ζ (γ.toFun t) := by
  have hr : 0 < r := by
    have h := hζ.mapsTo (hmap ⟨le_rfl, hst⟩)
    rwa [hz, mem_ball_zero_iff, norm_zero] at h
  have hupper := s25gb_flat_minimizing_upper hr hW hWD hζ
    (fun z hz' => by
      have h := hq z hz'
      norm_num at h ⊢
      exact h) γ (hmap ⟨le_rfl, hst⟩) (hmap ⟨hst, le_rfl⟩) hmin
  rw [hz, norm_zero, zero_add] at hupper
  intro u hu
  let a := ζ (γ.toFun u)
  let b := ζ (γ.toFun t)
  have hL := s25za_potential_segment 0 hW hζ hq (s25e_radial_hG 0) γ hu.1
    (hK.mono (Icc_subset_Icc le_rfl hu.2))
    (hmap.mono (Icc_subset_Icc le_rfl hu.2) (Subset.refl _))
  have hR := s25za_potential_segment 0 hW hζ hq (s25gb_flat_distance_potential a) γ hu.2
    (hK.mono (Icc_subset_Icc hu.1 le_rfl))
    (hmap.mono (Icc_subset_Icc hu.1 le_rfl) (Subset.refl _))
  have hL' : ENNReal.ofReal ‖a‖ ≤ phiSegmentLength φ γ s u := by
    simpa [hz, a] using hL
  have hR' : ENNReal.ofReal ‖b - a‖ ≤ phiSegmentLength φ γ u t := by
    simpa [a, b] using hR
  have hsum : ENNReal.ofReal (‖a‖ + ‖b - a‖) ≤ ENNReal.ofReal ‖b‖ := by
    rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact (add_le_add hL' hR').trans (by rwa [← s25g_segLen_add φ γ hu.1 hu.2])
  exact s25gb_flat_triangle_radial hb ((ENNReal.ofReal_le_ofReal_iff (norm_nonneg b)).1 hsum)

/-- Degree-zero version with the origin at the final parameter. -/
theorem s25gb_flat_minimizing_radial_left {φ ζ : ℂ → ℂ} {D W : Set ℂ} {r : ℝ}
    (hW : IsOpen W) (hWD : W ⊆ D) (hζ : IsConformalOnto ζ W (ball (0 : ℂ) r))
    (hq : ∀ z ∈ W, φ z = ((((0 : ℕ) : ℂ) + 2) / 2) ^ 2 * ζ z ^ (0 : ℕ) * deriv ζ z ^ 2)
    (γ : LRCurve) {K : ℝ≥0} {s t : ℝ} (hst : s ≤ t)
    (hK : LipschitzOnWith K γ.toFun (Icc s t)) (hmap : MapsTo γ.toFun (Icc s t) W)
    (hz : ζ (γ.toFun t) = 0) (hb : ζ (γ.toFun s) ≠ 0)
    (hmin : phiSegmentLength φ γ s t = metricDist D (phiDensity φ) (γ.toFun s) (γ.toFun t)) :
    ∀ u ∈ Icc s t, ∃ c ∈ Icc (0 : ℝ) 1, ζ (γ.toFun u) = c • ζ (γ.toFun s) := by
  have hr : 0 < r := by
    have h := hζ.mapsTo (hmap ⟨hst, le_rfl⟩)
    rwa [hz, mem_ball_zero_iff, norm_zero] at h
  have hupper := s25gb_flat_minimizing_upper hr hW hWD hζ
    (fun z hz' => by
      have h := hq z hz'
      norm_num at h ⊢
      exact h) γ (hmap ⟨le_rfl, hst⟩) (hmap ⟨hst, le_rfl⟩) hmin
  rw [hz, norm_zero, add_zero] at hupper
  intro u hu
  let a := ζ (γ.toFun u)
  let b := ζ (γ.toFun s)
  have hL := s25za_potential_segment 0 hW hζ hq (s25gb_flat_distance_potential b) γ hu.1
    (hK.mono (Icc_subset_Icc le_rfl hu.2))
    (hmap.mono (Icc_subset_Icc le_rfl hu.2) (Subset.refl _))
  have hR := s25za_potential_segment 0 hW hζ hq
    (s25ep_neg_potential (s25e_radial_hG 0)) γ hu.2
    (hK.mono (Icc_subset_Icc hu.1 le_rfl))
    (hmap.mono (Icc_subset_Icc hu.1 le_rfl) (Subset.refl _))
  have hL' : ENNReal.ofReal ‖b - a‖ ≤ phiSegmentLength φ γ s u := by
    simpa [a, b, norm_sub_rev] using hL
  have hR' : ENNReal.ofReal ‖a‖ ≤ phiSegmentLength φ γ u t := by
    simpa [hz, a] using hR
  have hsum : ENNReal.ofReal (‖a‖ + ‖b - a‖) ≤ ENNReal.ofReal ‖b‖ := by
    rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), add_comm]
    exact (add_le_add hL' hR').trans (by rwa [← s25g_segLen_add φ γ hu.1 hu.2])
  exact s25gb_flat_triangle_radial hb ((ENNReal.ofReal_le_ofReal_iff (norm_nonneg b)).1 hsum)

/-- Unified right radiality in all nonnegative-degree natural models. -/
theorem s25gb_model_minimizing_radial (m : ℕ)
    {φ ζ : ℂ → ℂ} {D W : Set ℂ} {r : ℝ}
    (hW : IsOpen W) (hWD : W ⊆ D) (hζ : IsConformalOnto ζ W (ball (0 : ℂ) r))
    (hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (γ : LRCurve) {K : ℝ≥0} {s t : ℝ} (hst : s ≤ t)
    (hK : LipschitzOnWith K γ.toFun (Icc s t)) (hmap : MapsTo γ.toFun (Icc s t) W)
    (hz : ζ (γ.toFun s) = 0) (hb : ζ (γ.toFun t) ≠ 0)
    (hmin : phiSegmentLength φ γ s t = metricDist D (phiDensity φ) (γ.toFun s) (γ.toFun t)) :
    ∀ u ∈ Icc s t, ∃ c ∈ Icc (0 : ℝ) 1, ζ (γ.toFun u) = c • ζ (γ.toFun t) := by
  by_cases hm : m = 0
  · subst m
    exact s25gb_flat_minimizing_radial hW hWD hζ hq γ hst hK hmap hz hb hmin
  · exact s25ep_minimizing_radial m (by omega) hW hWD hζ hq γ hst hK hmap hz hb hmin

/-- Unified left radiality in all nonnegative-degree natural models. -/
theorem s25gb_model_minimizing_radial_left (m : ℕ)
    {φ ζ : ℂ → ℂ} {D W : Set ℂ} {r : ℝ}
    (hW : IsOpen W) (hWD : W ⊆ D) (hζ : IsConformalOnto ζ W (ball (0 : ℂ) r))
    (hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (γ : LRCurve) {K : ℝ≥0} {s t : ℝ} (hst : s ≤ t)
    (hK : LipschitzOnWith K γ.toFun (Icc s t)) (hmap : MapsTo γ.toFun (Icc s t) W)
    (hz : ζ (γ.toFun t) = 0) (hb : ζ (γ.toFun s) ≠ 0)
    (hmin : phiSegmentLength φ γ s t = metricDist D (phiDensity φ) (γ.toFun s) (γ.toFun t)) :
    ∀ u ∈ Icc s t, ∃ c ∈ Icc (0 : ℝ) 1, ζ (γ.toFun u) = c • ζ (γ.toFun s) := by
  by_cases hm : m = 0
  · subst m
    exact s25gb_flat_minimizing_radial_left hW hWD hζ hq γ hst hK hmap hz hb hmin
  · exact s25ep_minimizing_radial_left m (by omega) hW hWD hζ hq γ hst hK hmap hz hb hmin

end LiZhongQC

