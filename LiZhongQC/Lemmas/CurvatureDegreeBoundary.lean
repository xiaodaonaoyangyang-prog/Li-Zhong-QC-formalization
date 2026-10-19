import LiZhongQC.Lemmas.WeierstrassValues
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped Real Interval

noncomputable section
namespace LiZhongQC

/-- Positively oriented boundary integral of a real one-form on a coordinate
rectangle. This is an actual sum of four interval integrals. -/
def s22cd_rectBoundary (α : ℂ → ℂ → ℝ) (z w : ℂ) : ℝ :=
  (∫ x : ℝ in z.re..w.re, α (x + z.im * I) 1) -
    (∫ x : ℝ in z.re..w.re, α (x + w.im * I) 1) +
    (∫ y : ℝ in z.im..w.im, α (w.re + y * I) I) -
    (∫ y : ℝ in z.im..w.im, α (z.re + y * I) I)

/-- A real phase boundary integral is the imaginary part of the complex
contour integral. Continuity ensures that every component is integrable. -/
theorem s22cd_rectBoundary_im {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (wv_rectF z w)) :
    s22cd_rectBoundary (fun ζ v => (f ζ * v).im) z w =
      (wv_rectBdry f z w).im := by
  have hb := Complex.imCLM.intervalIntegral_comp_comm (wv_ii_bot hf)
  have ht := Complex.imCLM.intervalIntegral_comp_comm (wv_ii_top hf)
  have hr := Complex.reCLM.intervalIntegral_comp_comm (wv_ii_right hf)
  have hl := Complex.reCLM.intervalIntegral_comp_comm (wv_ii_left hf)
  change (∫ x : ℝ in z.re..w.re, (f (x + z.im * I)).im) =
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)).im at hb
  change (∫ x : ℝ in z.re..w.re, (f (x + w.im * I)).im) =
    (∫ x : ℝ in z.re..w.re, f (x + w.im * I)).im at ht
  change (∫ y : ℝ in z.im..w.im, (f (w.re + y * I)).re) =
    (∫ y : ℝ in z.im..w.im, f (w.re + y * I)).re at hr
  change (∫ y : ℝ in z.im..w.im, (f (z.re + y * I)).re) =
    (∫ y : ℝ in z.im..w.im, f (z.re + y * I)).re at hl
  simp only [s22cd_rectBoundary, wv_rectBdry, mul_one, smul_eq_mul,
    Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add]
  rw [hb, ht, hr, hl]

/-- Boundary regularity of the logarithmic derivative follows from the actual
analytic, nonvanishing coefficient, including for a meromorphic interior. -/
theorem s22cd_logDeriv_continuousOn {f : ℂ → ℂ} {A : Set ℂ}
    (hf : ∀ z ∈ A, AnalyticAt ℂ f z ∧ f z ≠ 0) :
    ContinuousOn (logDeriv f) A := by
  intro z hz
  change ContinuousWithinAt (fun ζ => deriv f ζ / f ζ) A z
  exact ((hf z hz).1.deriv.continuousAt.div
    (hf z hz).1.continuousAt (hf z hz).2).continuousWithinAt

/-- Local curvature-degree boundary contribution, including poles with their
negative multiplicities. No logarithm branch or integrability is assumed. -/
theorem s22cd_phase_boundary_divisor {f : ℂ → ℂ} {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im)
    (hf : MeromorphicOn f (wv_rectK z w))
    (hord : ∀ u ∈ wv_rectK z w, meromorphicOrderAt f u ≠ ⊤)
    (hbd : ∀ ζ ∈ wv_rectF z w, AnalyticAt ℂ f ζ ∧ f ζ ≠ 0) :
    s22cd_rectBoundary (fun ζ v => (deriv f ζ / f ζ * v).im) z w =
      2 * π *
        ∑ p ∈ ((MeromorphicOn.divisor f (wv_rectK z w)).finiteSupport
          (wv_isCompact_rectK z w)).toFinset,
          (MeromorphicOn.divisor f (wv_rectK z w) p : ℝ) := by
  change s22cd_rectBoundary (fun ζ v => (logDeriv f ζ * v).im) z w = _
  rw [s22cd_rectBoundary_im (s22cd_logDeriv_continuousOn hbd),
    wv_rectBdry_logDeriv hre him hf hord hbd]
  simp [Complex.mul_im, Complex.mul_re]

/-- The boundary integral only uses the values on the four sides. -/
theorem s22cd_rectBoundary_congr {α β : ℂ → ℂ → ℝ} {z w : ℂ}
    (he : ∀ ζ ∈ wv_rectF z w, ∀ v, α ζ v = β ζ v) :
    s22cd_rectBoundary α z w = s22cd_rectBoundary β z w := by
  unfold s22cd_rectBoundary
  rw [integral_congr (fun x hx => he _ (wv_bot_mem_rectF hx) 1),
    integral_congr (fun x hx => he _ (wv_top_mem_rectF hx) 1),
    integral_congr (fun y hy => he _ (wv_right_mem_rectF hy) I),
    integral_congr (fun y hy => he _ (wv_left_mem_rectF hy) I)]

/-- If the coefficients vanish on the frame, the actual boundary integral
vanishes. This will be used for compactly supported partition terms. -/
theorem s22cd_rectBoundary_zero {α : ℂ → ℂ → ℝ} {z w : ℂ}
    (hz : ∀ ζ ∈ wv_rectF z w, ∀ v, α ζ v = 0) :
    s22cd_rectBoundary α z w = 0 := by
  rw [s22cd_rectBoundary_congr hz]
  simp [s22cd_rectBoundary]

/-- Subtraction of genuine real forms commutes with rectangle integration
once both coordinate coefficients are continuous on the frame. -/
theorem s22cd_rectBoundary_sub {α β : ℂ → ℂ → ℝ} {z w : ℂ}
    (hα : ∀ v, ContinuousOn (fun ζ => α ζ v) (wv_rectF z w))
    (hβ : ∀ v, ContinuousOn (fun ζ => β ζ v) (wv_rectF z w)) :
    s22cd_rectBoundary (fun ζ v => α ζ v - β ζ v) z w =
      s22cd_rectBoundary α z w - s22cd_rectBoundary β z w := by
  have hb (γ : ℂ → ℂ → ℝ)
      (hc : ∀ v, ContinuousOn (fun ζ => γ ζ v) (wv_rectF z w)) :
      IntervalIntegrable (fun x : ℝ => γ (x + z.im * I) 1) volume z.re w.re :=
    ((hc 1).comp (continuous_ofReal.add continuous_const).continuousOn
      (fun _ hx => wv_bot_mem_rectF hx)).intervalIntegrable
  have ht (γ : ℂ → ℂ → ℝ)
      (hc : ∀ v, ContinuousOn (fun ζ => γ ζ v) (wv_rectF z w)) :
      IntervalIntegrable (fun x : ℝ => γ (x + w.im * I) 1) volume z.re w.re :=
    ((hc 1).comp (continuous_ofReal.add continuous_const).continuousOn
      (fun _ hx => wv_top_mem_rectF hx)).intervalIntegrable
  have hr (γ : ℂ → ℂ → ℝ)
      (hc : ∀ v, ContinuousOn (fun ζ => γ ζ v) (wv_rectF z w)) :
      IntervalIntegrable (fun y : ℝ => γ (w.re + y * I) I) volume z.im w.im :=
    ((hc I).comp (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      (fun _ hy => wv_right_mem_rectF hy)).intervalIntegrable
  have hl (γ : ℂ → ℂ → ℝ)
      (hc : ∀ v, ContinuousOn (fun ζ => γ ζ v) (wv_rectF z w)) :
      IntervalIntegrable (fun y : ℝ => γ (z.re + y * I) I) volume z.im w.im :=
    ((hc I).comp (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      (fun _ hy => wv_left_mem_rectF hy)).intervalIntegrable
  simp only [s22cd_rectBoundary,
    integral_sub (hb α hα) (hb β hβ), integral_sub (ht α hα) (ht β hβ),
    integral_sub (hr α hα) (hr β hβ), integral_sub (hl α hα) (hl β hβ)]
  ring

/-- Real-coordinate Stokes on a rectangle. The integrability needed by
Bochner integration is proved from continuity of the curl on the compact
rectangle. The hypotheses are local differentiability data, not a Stokes
identity or a global finiteness assumption. -/
theorem s22cd_rectangle_stokes
    (P Q : ℝ × ℝ → ℝ) (P' Q' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ)
    (a b : ℝ × ℝ) (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (hQ : ContinuousOn Q (Icc a b))
    (hdP : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt P (P' x) x)
    (hdQ : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt Q (Q' x) x)
    (hc : ContinuousOn (fun x => Q' x (1, 0) - P' x (0, 1)) (Icc a b)) :
    (∫ x in Icc a b, Q' x (1, 0) - P' x (0, 1)) =
      (∫ x in a.1..b.1, P (x, a.2)) -
      (∫ x in a.1..b.1, P (x, b.2)) +
      (∫ y in a.2..b.2, Q (b.1, y)) -
      (∫ y in a.2..b.2, Q (a.1, y)) := by
  have hi : IntegrableOn
      (fun x => Q' x (1, 0) + (-P' x) (0, 1)) (Icc a b) := by
    simpa only [ContinuousLinearMap.neg_apply, sub_eq_add_neg] using
      hc.integrableOn_compact isCompact_Icc
  have h := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    Q (fun x => -P x) Q' (fun x => -P' x) a b hab hQ hP.neg hdQ
    (fun x hx => (hdP x hx).neg) hi
  simp only [ContinuousLinearMap.neg_apply, sub_eq_add_neg, intervalIntegral.integral_neg,
    neg_neg] at h ⊢
  linarith

/-- Stokes for a coordinate form supported away from the rectangle boundary.
This is the local zero-boundary lemma for a partition-of-unity proof. -/
theorem s22cd_rectangle_stokes_zero
    (P Q : ℝ × ℝ → ℝ) (P' Q' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ)
    (a b : ℝ × ℝ) (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (hQ : ContinuousOn Q (Icc a b))
    (hdP : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt P (P' x) x)
    (hdQ : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt Q (Q' x) x)
    (hc : ContinuousOn (fun x => Q' x (1, 0) - P' x (0, 1)) (Icc a b))
    (hbot : ∀ x ∈ Icc a.1 b.1, P (x, a.2) = 0)
    (htop : ∀ x ∈ Icc a.1 b.1, P (x, b.2) = 0)
    (hright : ∀ y ∈ Icc a.2 b.2, Q (b.1, y) = 0)
    (hleft : ∀ y ∈ Icc a.2 b.2, Q (a.1, y) = 0) :
    (∫ x in Icc a b, Q' x (1, 0) - P' x (0, 1)) = 0 := by
  rw [s22cd_rectangle_stokes P Q P' Q' a b hab hP hQ hdP hdQ hc]
  have hb : (∫ x in a.1..b.1, P (x, a.2)) = 0 := by
    rw [integral_congr (fun x hx => hbot x ((uIcc_of_le hab.1) ▸ hx))]
    simp
  have ht : (∫ x in a.1..b.1, P (x, b.2)) = 0 := by
    rw [integral_congr (fun x hx => htop x ((uIcc_of_le hab.1) ▸ hx))]
    simp
  have hr : (∫ y in a.2..b.2, Q (b.1, y)) = 0 := by
    rw [integral_congr (fun y hy => hright y ((uIcc_of_le hab.2) ▸ hy))]
    simp
  have hl : (∫ y in a.2..b.2, Q (a.1, y)) = 0 := by
    rw [integral_congr (fun y hy => hleft y ((uIcc_of_le hab.2) ▸ hy))]
    simp
  rw [hb, ht, hr, hl]
  ring

/-- The isolated polar factor has exactly its signed integer boundary mass.
This also fixes the orientation and the sign used for pole contributions. -/
theorem s22cd_polar_boundary {z w p : ℂ} (m : ℤ)
    (hre₁ : z.re < p.re) (hre₂ : p.re < w.re)
    (him₁ : z.im < p.im) (him₂ : p.im < w.im) :
    s22cd_rectBoundary (fun ζ v => (((m : ℂ) / (ζ - p)) * v).im) z w =
      2 * π * (m : ℝ) := by
  have hn : ∀ ζ ∈ wv_rectF z w, ζ - p ≠ 0 := by
    intro ζ hζ he
    have hep : ζ = p := sub_eq_zero.mp he
    subst ζ
    exact hζ.2 ⟨⟨hre₁, hre₂⟩, ⟨him₁, him₂⟩⟩
  have hc : ContinuousOn (fun ζ : ℂ => (m : ℂ) / (ζ - p)) (wv_rectF z w) :=
    continuousOn_const.div (continuous_id.sub continuous_const).continuousOn hn
  rw [s22cd_rectBoundary_im hc]
  have he : (fun ζ : ℂ => (m : ℂ) / (ζ - p)) =
      (fun ζ => (m : ℂ) * (ζ - p)⁻¹) := by
    funext ζ
    rw [div_eq_mul_inv]
  rw [he, wv_rectBdry_const_mul]
  have hres : wv_rectBdry (fun ζ => (ζ - p)⁻¹) z w = 2 * π * I :=
    wv_integral_boundary_rect_inv_sub hre₁ hre₂ him₁ him₂
  rw [hres]
  simp [Complex.mul_im, Complex.mul_re]
  <;> ring

end LiZhongQC
