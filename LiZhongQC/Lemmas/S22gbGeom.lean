import LiZhongQC.Lemmas.S22gbPiece

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

section GaussBonnetGeom

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S] [CompactSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- A lift of the chart inverse on a whole disc around the centre of every preferred chart. -/
theorem s22gb_lift_ball {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) (y : S) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ψ : ℂ → ℂ, Metric.ball (chartAt ℂ y y) ε ⊆ (chartAt ℂ y).target ∧
      ∀ w ∈ Metric.ball (chartAt ℂ y y) ε, AnalyticAt ℂ ψ w ∧ deriv ψ w ≠ 0 ∧ ψ w ∈ upperHalf ∧
        (fun u => s22gm_projectionExtension p (ψ u)) =ᶠ[𝓝 w] fun u => (chartAt ℂ y).symm u := by
  have hct : chartAt ℂ y y ∈ (chartAt ℂ y).target :=
    (chartAt ℂ y).map_source (mem_chart_source ℂ y)
  obtain ⟨ψ, hψan, hψd, hψH, hψe⟩ := s22gb_local_lift hp y hct
  have hopen := isOpen_upperHalf'
  have hev : ∀ᶠ w in 𝓝 (chartAt ℂ y y), w ∈ (chartAt ℂ y).target ∧ AnalyticAt ℂ ψ w ∧
      deriv ψ w ≠ 0 ∧ ψ w ∈ upperHalf ∧
      (fun u => s22gm_projectionExtension p (ψ u)) =ᶠ[𝓝 w] fun u => (chartAt ℂ y).symm u := by
    filter_upwards [(chartAt ℂ y).open_target.mem_nhds hct, hψan.eventually_analyticAt,
      hψan.deriv.continuousAt.eventually_ne hψd,
      hψan.continuousAt.preimage_mem_nhds (hopen.mem_nhds hψH), hψe.eventually_nhds]
      with w h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  exact ⟨ε, hε, ψ, fun w hw => (hball w hw).1, fun w hw => (hball w hw).2⟩

/-- The closed square of half-side `δ` around `c`. -/
theorem s22gb_sq_subset_ball {c : ℂ} {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 2 * δ < ε) :
    wv_rectK (c - (δ : ℂ) * (1 + I)) (c + (δ : ℂ) * (1 + I)) ⊆ Metric.ball c ε := by
  intro z hz
  rw [Metric.mem_ball]
  exact lt_of_le_of_lt (s22sl_square_dist_le hδ hz) hε

theorem s22gb_osq_subset_sq {c : ℂ} {δ : ℝ} (hδ : 0 ≤ δ) :
    wv_rectO (c - (δ : ℂ) * (1 + I)) (c + (δ : ℂ) * (1 + I)) ⊆
      wv_rectK (c - (δ : ℂ) * (1 + I)) (c + (δ : ℂ) * (1 + I)) := by
  intro z hz
  rw [s22gb_mem_rectO] at hz
  rw [s22gb_mem_rectK (by simp <;> linarith) (by simp <;> linarith)]
  exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1.le, hz.2.2.le⟩

theorem s22gb_center_mem_osq (c : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    c ∈ wv_rectO (c - (δ : ℂ) * (1 + I)) (c + (δ : ℂ) * (1 + I)) := by
  rw [s22gb_mem_rectO]
  simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im]
  refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem s22gb_sq_corners {c : ℂ} {δ : ℝ} :
    (c - (δ : ℂ) * (1 + I)).re = c.re - δ ∧ (c + (δ : ℂ) * (1 + I)).re = c.re + δ ∧
    (c - (δ : ℂ) * (1 + I)).im = c.im - δ ∧ (c + (δ : ℂ) * (1 + I)).im = c.im + δ := by
  simp [Complex.mul_re, Complex.mul_im]

theorem s22gb_sq_subset_osq {c : ℂ} {r : ℝ} (hr : 0 < r) :
    wv_rectK (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I)) ⊆
      wv_rectO (c - ((2 * r : ℝ) : ℂ) * (1 + I)) (c + ((2 * r : ℝ) : ℂ) * (1 + I)) := by
  intro z hz
  obtain ⟨a1, a2, a3, a4⟩ := s22gb_sq_corners (c := c) (δ := r)
  obtain ⟨b1, b2, b3, b4⟩ := s22gb_sq_corners (c := c) (δ := 2 * r)
  rw [s22gb_mem_rectK (by rw [a1, a2]; linarith) (by rw [a3, a4]; linarith), a1, a2, a3, a4] at hz
  rw [s22gb_mem_rectO, b1, b2, b3, b4]
  exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, by linarith [hz.2.1], by linarith [hz.2.2]⟩

end GaussBonnetGeom

end LiZhongQC
