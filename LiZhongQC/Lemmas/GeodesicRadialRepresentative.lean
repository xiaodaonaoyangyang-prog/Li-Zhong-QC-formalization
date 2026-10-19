import LiZhongQC.Lemmas.GeodesicRegularCorners
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real
noncomputable section
namespace LiZhongQC

/-- Radiality of an embedded smooth representative gives both its positive
physical tangent and every sufficiently small point of the coordinate ray.
This exposes the ray data needed at an exceptional join. -/
theorem s25gb_radial_representative {σ : ℝ → ℂ} {ζ : ℂ → ℂ} {W : Set ℂ}
    (hW : IsOpen W) (hζ : DifferentiableOn ℂ ζ W) (hζi : InjOn ζ W)
    (hσ : ContDiffOn ℝ 1 σ (Icc 0 1)) (hσi : InjOn σ (Icc (0 : ℝ) 1))
    (hmap : MapsTo σ (Icc (0 : ℝ) 1) W)
    (hz : ζ (σ 0) = 0) (hb : ζ (σ 1) ≠ 0)
    (hζd : deriv ζ (σ 0) ≠ 0) (hd : derivWithin σ (Icc 0 1) 0 ≠ 0)
    (hrad : ∀ t ∈ Icc (0 : ℝ) 1, ∃ c ∈ Icc (0 : ℝ) 1,
      ζ (σ t) = c • ζ (σ 1)) :
    ∃ (v : ℂ) (k B : ℝ), ‖v‖ = 1 ∧ 0 < k ∧ 0 < B ∧
      deriv ζ (σ 0) * derivWithin σ (Icc 0 1) 0 = (k : ℂ) * v ∧
      ∀ q ∈ Ioo (0 : ℝ) B, ∃ t ∈ Ioo (0 : ℝ) 1,
        σ t ∈ W ∧ ζ (σ t) = (q : ℂ) * v := by
  let B : ℝ := ‖ζ (σ 1)‖
  let v : ℂ := B⁻¹ • ζ (σ 1)
  let θ : ℝ → ℝ := fun t => ‖ζ (σ t)‖
  have hB : 0 < B := norm_pos_iff.2 hb
  have hv : ‖v‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hB.le)]
    exact inv_mul_cancel₀ hB.ne'
  have hv0 : v ≠ 0 := by intro he; simpa [he] using hv
  have hθ0 : θ 0 = 0 := by simp only [θ, hz, norm_zero]
  have hθ1 : θ 1 = B := rfl
  have hθc : ContinuousOn θ (Icc (0 : ℝ) 1) :=
    (hζ.continuousOn.comp hσ.continuousOn hmap).norm
  have hcoord : ∀ t ∈ Icc (0 : ℝ) 1, ζ (σ t) = (θ t : ℂ) * v := by
    intro t ht
    obtain ⟨c, hc, he⟩ := hrad t ht
    have hθ : θ t = c * B := by
      change ‖ζ (σ t)‖ = c * B
      rw [he, norm_smul, Real.norm_of_nonneg hc.1]
    rw [hθ, ← Complex.real_smul]
    change ζ (σ t) = (c * B) • (B⁻¹ • ζ (σ 1))
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hB.ne', mul_one]
    exact he
  have hθi : InjOn θ (Icc (0 : ℝ) 1) := by
    intro s hs t ht he
    apply hσi hs ht
    apply hζi (hmap hs) (hmap ht)
    rw [hcoord s hs, hcoord t ht, he]
  have hθm : StrictMonoOn θ (Icc (0 : ℝ) 1) :=
    hθc.strictMonoOn_of_injOn_Icc zero_le_one (by rw [hθ0, hθ1]; exact hB.le) hθi
  have hline : ∀ t ∈ Icc (0 : ℝ) 1, ζ (σ t) = 0 + (θ t : ℂ) * v := by
    intro t ht
    simpa only [zero_add] using hcoord t ht
  obtain ⟨k, hk, hkd⟩ := s25gb_ordered_chart_tangent zero_lt_one
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
    (fx_p2_hasDerivWithinAt_of_contDiffOn hσ 0 ⟨le_rfl, zero_le_one⟩)
    hd hv0 (hζ.differentiableAt (hW.mem_nhds (hmap ⟨le_rfl, zero_le_one⟩)))
    hζd hθm.monotoneOn hline
  refine ⟨v, k, B, hv, hk, hB, hkd, ?_⟩
  intro q hq
  have hsurj := intermediate_value_Icc zero_le_one hθc
  rw [hθ0, hθ1] at hsurj
  obtain ⟨t, ht, he⟩ := hsurj ⟨hq.1.le, hq.2.le⟩
  have ht0 : 0 < t := by
    by_contra hn
    have ht' : t = 0 := le_antisymm (le_of_not_gt hn) ht.1
    rw [ht', hθ0] at he
    linarith [hq.1]
  have ht1 : t < 1 := by
    by_contra hn
    have ht' : t = 1 := le_antisymm ht.2 (le_of_not_gt hn)
    rw [ht', hθ1] at he
    linarith [hq.2]
  exact ⟨t, ⟨ht0, ht1⟩, hmap ht, by rw [hcoord t ht, he]⟩

end LiZhongQC


