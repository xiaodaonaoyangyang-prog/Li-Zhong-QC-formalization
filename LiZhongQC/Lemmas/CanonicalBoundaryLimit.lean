import LiZhongQC.Lemmas.CanonicalConnectionGauge
import LiZhongQC.Lemmas.ShrinkingBoundary

open Complex Set Filter Topology MeasureTheory
open scoped Real

noncomputable section
namespace LiZhongQC

/-- The shrinking positive contour around a zero or pole contributes
-2*pi times its order to the canonical gauge. Consequently an inner boundary
of the punctured surface, with the reversed orientation, contributes +2*pi
times the order. The regular connection boundary tends to zero by continuity.
All meromorphic regularity on the small contours is derived here. -/
theorem s22sl_canonicalGauge_boundary_limit {ψ f : ℂ → ℂ} {c : ℂ} {m : ℤ}
    (hψ : AnalyticAt ℂ ψ c) (hd : deriv ψ c ≠ 0) (hy : (ψ c).im ≠ 0)
    (hf : MeromorphicAt f c) (hm : meromorphicOrderAt f c = (m : ℤ)) :
    Tendsto
      (fun r : ℝ => s22cd_rectBoundary (s22cd_canonicalGauge ψ f)
        (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(2 * π * (m : ℝ)))) := by
  have hψreg : ∀ᶠ z in 𝓝 c,
      AnalyticAt ℂ ψ z ∧ deriv ψ z ≠ 0 ∧ (ψ z).im ≠ 0 := by
    filter_upwards [hψ.eventually_analyticAt,
      hψ.deriv.continuousAt.eventually_ne hd,
      (Complex.continuous_im.continuousAt.comp hψ.continuousAt).eventually_ne hy] with z ha hd' hy'
    exact ⟨ha, hd', hy'⟩
  have hfne : ∀ᶠ z in 𝓝[≠] c, f z ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf).mp
      (by rw [hm]; exact WithTop.coe_ne_top)
  have hreg : ∀ᶠ z in 𝓝[≠] c,
      (AnalyticAt ℂ ψ z ∧ deriv ψ z ≠ 0 ∧ (ψ z).im ≠ 0) ∧
        AnalyticAt ℂ f z ∧ f z ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds hψreg, hf.eventually_analyticAt, hfne]
      with z hψz hfz hn
    exact ⟨hψz, hfz, hn⟩
  have he :
      (fun r : ℝ => s22cd_rectBoundary (s22cd_canonicalGauge ψ f)
        (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r : ℝ =>
        s22cd_rectBoundary (s22gt_chartConnection ψ)
          (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I)) -
        s22cd_rectBoundary (s22gt_phaseForm f)
          (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I))) := by
    filter_upwards [s22sl_eventually_on_square_frame hreg] with r hr
    change s22cd_rectBoundary
      (fun z v => s22gt_chartConnection ψ z v - s22gt_phaseForm f z v) _ _ = _
    apply s22cd_rectBoundary_sub
    · intro v z hz
      exact (s22cd_chartConnection_continuousAt (hr z hz).1.1
        (hr z hz).1.2.1 (hr z hz).1.2.2 v).continuousWithinAt
    · intro v z hz
      exact (s22cd_phase_continuousAt (hr z hz).2.1
        (hr z hz).2.2 v).continuousWithinAt
  have hc := s22sl_continuous_boundary_tendsto_zero
    (s22cd_chartConnection_continuousAt hψ hd hy 1)
    (s22cd_chartConnection_continuousAt hψ hd hy I)
  have hp := s22sl_meromorphic_phase_boundary_limit hf hm
  change Tendsto
    (fun r : ℝ => s22cd_rectBoundary (s22gt_phaseForm f)
      (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I)))
    (𝓝[>] (0 : ℝ)) (𝓝 (2 * π * (m : ℝ))) at hp
  have hl := hc.sub hp
  simp only [zero_sub] at hl
  exact hl.congr' he.symm

/-- The total contribution of finitely many reversed inner boundaries is
2*pi times the sum of the genuine local meromorphic orders. -/
theorem s22sl_finite_inner_boundary_limit {ι : Type*} (s : Finset ι)
    (ψ f : ι → ℂ → ℂ) (c : ι → ℂ) (m : ι → ℤ)
    (hψ : ∀ i ∈ s, AnalyticAt ℂ (ψ i) (c i))
    (hd : ∀ i ∈ s, deriv (ψ i) (c i) ≠ 0)
    (hy : ∀ i ∈ s, (ψ i (c i)).im ≠ 0)
    (hf : ∀ i ∈ s, MeromorphicAt (f i) (c i))
    (hm : ∀ i ∈ s, meromorphicOrderAt (f i) (c i) = (m i : ℤ)) :
    Tendsto
      (fun r : ℝ => ∑ i ∈ s, -s22cd_rectBoundary (s22cd_canonicalGauge (ψ i) (f i))
        (c i - (r : ℂ) * (1 + I)) (c i + (r : ℂ) * (1 + I)))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * π * ∑ i ∈ s, (m i : ℝ))) := by
  have h := tendsto_finsetSum s (fun i hi =>
    (s22sl_canonicalGauge_boundary_limit (hψ i hi) (hd i hi)
      (hy i hi) (hf i hi) (hm i hi)).neg)
  simpa only [neg_neg, ← Finset.mul_sum] using h

end LiZhongQC
