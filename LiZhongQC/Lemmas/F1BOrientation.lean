import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.F1BExposedGeometry

/-! B2c auxiliary (orientation): Euclidean orientation facts for hyperbolic circles.
(b) at a transversal intersection of two circles, the arc of circle 1 arriving at the point and the
arc of circle 2 leaving it are both outside, or both inside, the other disk;
(c) two distinct equal-radius hyperbolic circles whose centres are not at distance `2R` meet
transversally. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- (b) Opposite orientation at a transversal crossing: going backwards (clockwise) from `p` on
circle 1 and forwards (counterclockwise) from `p` on circle 2, both small arcs are strictly outside
the other closed disk, or both strictly inside the other open disk. -/
theorem ft1gor_crossing_orientation {C₁ C₂ p : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hp₁ : ‖p - C₁‖ = r₁) (hp₂ : ‖p - C₂‖ = r₂)
    (hlo : |r₁ - r₂| < ‖C₁ - C₂‖) (hhi : ‖C₁ - C₂‖ < r₁ + r₂) :
    ∃ ε > 0,
      (∀ s ∈ Ioo (0 : ℝ) ε, r₂ < ‖C₁ + (p - C₁) * exp (-((s : ℂ) * I)) - C₂‖ ∧
        r₁ < ‖C₂ + (p - C₂) * exp ((s : ℂ) * I) - C₁‖) ∨
      (∀ s ∈ Ioo (0 : ℝ) ε, ‖C₁ + (p - C₁) * exp (-((s : ℂ) * I)) - C₂‖ < r₂ ∧
        ‖C₂ + (p - C₂) * exp ((s : ℂ) * I) - C₁‖ < r₁) := by
  set a : ℂ := p - C₁ with ha
  set b : ℂ := p - C₂ with hb
  have hw : C₁ - C₂ = b - a := by rw [ha, hb]; ring
  clear_value a b
  set W : ℝ := ‖C₁ - C₂‖ with hW
  have hr1sq : a.re ^ 2 + a.im ^ 2 = r₁ ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hp₁
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    linear_combination h
  have hr2sq : b.re ^ 2 + b.im ^ 2 = r₂ ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hp₂
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    linear_combination h
  have hWsq : (b.re - a.re) ^ 2 + (b.im - a.im) ^ 2 = W ^ 2 := by
    rw [hW, hw, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have hW0 : 0 ≤ W := norm_nonneg _
  set A : ℝ := (b.re - a.re) * a.re + (b.im - a.im) * a.im with hA
  set A' : ℝ := (b.re - a.re) * b.re + (b.im - a.im) * b.im with hA'
  set B : ℝ := (b.re - a.re) * a.im - (b.im - a.im) * a.re with hB
  clear_value W A A' B
  have hlo1 := (abs_lt.1 hlo).1
  have hlo2 := (abs_lt.1 hlo).2
  have hB0 : B ≠ 0 := by
    intro hB0
    have hlag : A ^ 2 + B ^ 2 = W ^ 2 * r₁ ^ 2 := by
      rw [← hWsq, ← hr1sq, hA, hB]
      ring
    rw [hB0] at hlag
    have hr2A : r₂ ^ 2 = W ^ 2 + r₁ ^ 2 + 2 * A := by
      rw [← hWsq, ← hr1sq, ← hr2sq, hA]
      ring
    have hprod : (A - W * r₁) * (A + W * r₁) = 0 := by linear_combination hlag
    rcases mul_eq_zero.1 hprod with h | h
    · have hAe : A = W * r₁ := by linarith
      rw [hAe] at hr2A
      have hlt : r₂ < W + r₁ := by linarith
      nlinarith
    · have hAe : A = -(W * r₁) := by linarith
      rw [hAe] at hr2A
      have h1 : W - r₁ < r₂ := by linarith
      have h2 : r₁ - W < r₂ := by linarith
      nlinarith
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_d2
  have hpi3 := Real.pi_gt_three
  set ε : ℝ := min 1 (|B| / (|A| + |A'| + 1)) with hε
  have hBpos : 0 < |B| := abs_pos.2 hB0
  have hden : 0 < |A| + |A'| + 1 := by positivity
  have hε0 : 0 < ε := lt_min one_pos (div_pos hBpos hden)
  have htrig : ∀ s : ℝ, Real.cos s ^ 2 + Real.sin s ^ 2 = 1 := fun s => Real.cos_sq_add_sin_sq s
  have hE1re : ∀ s : ℝ, (exp (-((s : ℂ) * I))).re = Real.cos s := fun s => by
    rw [show -((s : ℂ) * I) = ((-s : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_ofReal_mul_I_re,
      Real.cos_neg]
  have hE1im : ∀ s : ℝ, (exp (-((s : ℂ) * I))).im = -Real.sin s := fun s => by
    rw [show -((s : ℂ) * I) = ((-s : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_ofReal_mul_I_im,
      Real.sin_neg]
  have hf : ∀ s : ℝ, ‖C₁ + a * exp (-((s : ℂ) * I)) - C₂‖ ^ 2 =
      r₂ ^ 2 - 2 * (1 - Real.cos s) * A + 2 * Real.sin s * B := by
    intro s
    have e : C₁ + a * exp (-((s : ℂ) * I)) - C₂ = (b - a) + a * exp (-((s : ℂ) * I)) := by
      rw [← hw]
      ring
    rw [e, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, hE1re, hE1im]
    rw [hA, hB]
    linear_combination (a.re ^ 2 + a.im ^ 2) * htrig s + hr2sq
  have hg : ∀ s : ℝ, ‖C₂ + b * exp ((s : ℂ) * I) - C₁‖ ^ 2 =
      r₁ ^ 2 + 2 * (1 - Real.cos s) * A' + 2 * Real.sin s * B := by
    intro s
    have e : C₂ + b * exp ((s : ℂ) * I) - C₁ = b * exp ((s : ℂ) * I) - (b - a) := by
      rw [← hw]
      ring
    rw [e, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    rw [hA', hB]
    linear_combination (b.re ^ 2 + b.im ^ 2) * htrig s + hr1sq
  have hsmall : ∀ s ∈ Ioo (0 : ℝ) ε, (1 - Real.cos s) * |A| < Real.sin s * |B| ∧
      (1 - Real.cos s) * |A'| < Real.sin s * |B| := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hs1 : s < 1 := lt_of_lt_of_le hs.2 (min_le_left _ _)
    have hsB : s < |B| / (|A| + |A'| + 1) := lt_of_lt_of_le hs.2 (min_le_right _ _)
    have hsB' : s * (|A| + |A'| + 1) < |B| := by rwa [lt_div_iff₀ hden] at hsB
    have hcos : 1 - s ^ 2 / 2 ≤ Real.cos s := Real.one_sub_sq_div_two_le_cos
    have hsin : 2 / Real.pi * s ≤ Real.sin s := Real.mul_le_sin hs0.le (by linarith)
    have h2pi : (1 : ℝ) / 2 < 2 / Real.pi := by rw [lt_div_iff₀ hpi]; linarith
    have h3 : s / 2 < Real.sin s := by
      have h4 : 1 / 2 * s < 2 / Real.pi * s := mul_lt_mul_of_pos_right h2pi hs0
      linarith
    have hsinB : s / 2 * |B| < Real.sin s * |B| := mul_lt_mul_of_pos_right h3 hBpos
    have hA0 := abs_nonneg A
    have hA'0 := abs_nonneg A'
    constructor
    · have h1 : (1 - Real.cos s) * |A| ≤ s ^ 2 / 2 * |A| :=
        mul_le_mul_of_nonneg_right (by linarith) hA0
      have h2 : s ^ 2 / 2 * |A| ≤ s / 2 * |B| := by
        have h5 : s * |A| ≤ |B| := by nlinarith
        have h6 : s ^ 2 / 2 * |A| = s / 2 * (s * |A|) := by ring
        rw [h6]
        exact mul_le_mul_of_nonneg_left h5 (by linarith)
      linarith
    · have h1 : (1 - Real.cos s) * |A'| ≤ s ^ 2 / 2 * |A'| :=
        mul_le_mul_of_nonneg_right (by linarith) hA'0
      have h2 : s ^ 2 / 2 * |A'| ≤ s / 2 * |B| := by
        have h5 : s * |A'| ≤ |B| := by nlinarith
        have h6 : s ^ 2 / 2 * |A'| = s / 2 * (s * |A'|) := by ring
        rw [h6]
        exact mul_le_mul_of_nonneg_left h5 (by linarith)
      linarith
  refine ⟨ε, hε0, ?_⟩
  rcases lt_or_gt_of_ne hB0 with hneg | hpos
  · right
    intro s hs
    obtain ⟨h1, h2⟩ := hsmall s hs
    have hc1 : 0 ≤ 1 - Real.cos s := by linarith [Real.cos_le_one s]
    rw [abs_of_neg hneg] at h1 h2
    have hA1 : -|A| ≤ A := neg_abs_le A
    have hA2 : -|A'| ≤ A' := neg_abs_le A'
    have hA3 : A ≤ |A| := le_abs_self A
    have hA4 : A' ≤ |A'| := le_abs_self A'
    have k1 : -((1 - Real.cos s) * |A|) ≤ (1 - Real.cos s) * A := by
      have := mul_le_mul_of_nonneg_left hA1 hc1
      linarith
    have k2 : (1 - Real.cos s) * A' ≤ (1 - Real.cos s) * |A'| := mul_le_mul_of_nonneg_left hA4 hc1
    constructor
    · have hlt : ‖C₁ + a * exp (-((s : ℂ) * I)) - C₂‖ ^ 2 < r₂ ^ 2 := by
        rw [hf]
        linarith
      exact lt_of_pow_lt_pow_left₀ 2 hr₂.le hlt
    · have hlt : ‖C₂ + b * exp ((s : ℂ) * I) - C₁‖ ^ 2 < r₁ ^ 2 := by
        rw [hg]
        linarith
      exact lt_of_pow_lt_pow_left₀ 2 hr₁.le hlt
  · left
    intro s hs
    obtain ⟨h1, h2⟩ := hsmall s hs
    have hc1 : 0 ≤ 1 - Real.cos s := by linarith [Real.cos_le_one s]
    rw [abs_of_pos hpos] at h1 h2
    have hA3 : A ≤ |A| := le_abs_self A
    have hA2 : -|A'| ≤ A' := neg_abs_le A'
    have k1 : (1 - Real.cos s) * A ≤ (1 - Real.cos s) * |A| := mul_le_mul_of_nonneg_left hA3 hc1
    have k2 : -((1 - Real.cos s) * |A'|) ≤ (1 - Real.cos s) * A' := by
      have := mul_le_mul_of_nonneg_left hA2 hc1
      linarith
    constructor
    · have hlt : r₂ ^ 2 < ‖C₁ + a * exp (-((s : ℂ) * I)) - C₂‖ ^ 2 := by
        rw [hf]
        linarith
      exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt
    · have hlt : r₁ ^ 2 < ‖C₂ + b * exp ((s : ℂ) * I) - C₁‖ ^ 2 := by
        rw [hg]
        linarith
      exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt

/-- (c) Two distinct equal-radius hyperbolic circles that meet, with centres not at distance `2R`,
meet transversally (strict Euclidean triangle inequalities for centres and radii). -/
theorem ft1gor_spheres_transversal {R : ℝ} (hR : 0 < R) (z₁ z₂ : UpperHalfPlane) (hne : z₁ ≠ z₂)
    (h2R : dist z₁ z₂ ≠ 2 * R) (p : UpperHalfPlane) (hp₁ : dist p z₁ = R) (hp₂ : dist p z₂ = R) :
    |z₁.im * Real.sinh R - z₂.im * Real.sinh R| < ‖(z₁.center R : ℂ) - (z₂.center R : ℂ)‖ ∧
      ‖(z₁.center R : ℂ) - (z₂.center R : ℂ)‖ < z₁.im * Real.sinh R + z₂.im * Real.sinh R := by
  set C₁ : ℂ := (z₁.center R : ℂ) with hC₁
  set C₂ : ℂ := (z₂.center R : ℂ) with hC₂
  have h1 : dist (p : ℂ) C₁ = z₁.im * Real.sinh R :=
    UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.1 hp₁
  have h2 : dist (p : ℂ) C₂ = z₂.im * Real.sinh R :=
    UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.1 hp₂
  have n1 : ‖(p : ℂ) - C₁‖ = z₁.im * Real.sinh R := by rw [← dist_eq_norm]; exact h1
  have n2 : ‖(p : ℂ) - C₂‖ = z₂.im * Real.sinh R := by rw [← dist_eq_norm]; exact h2
  have hle_hi : ‖C₁ - C₂‖ ≤ z₁.im * Real.sinh R + z₂.im * Real.sinh R := by
    calc ‖C₁ - C₂‖ ≤ ‖C₁ - (p : ℂ)‖ + ‖(p : ℂ) - C₂‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = z₁.im * Real.sinh R + z₂.im * Real.sinh R := by rw [norm_sub_rev, n1, n2]
  have hle_lo : |z₁.im * Real.sinh R - z₂.im * Real.sinh R| ≤ ‖C₁ - C₂‖ := by
    have h := abs_norm_sub_norm_le ((p : ℂ) - C₂) ((p : ℂ) - C₁)
    have e : (p : ℂ) - C₂ - ((p : ℂ) - C₁) = C₁ - C₂ := by ring
    rw [n1, n2, e, abs_sub_comm] at h
    exact h
  have hs : 0 < Real.sinh R := Real.sinh_pos_iff.2 hR
  have hcs : Real.sinh R < Real.cosh R := Real.sinh_lt_cosh R
  have hch : 0 < Real.cosh R := Real.cosh_pos R
  refine ⟨lt_of_le_of_ne hle_lo ?_, lt_of_le_of_ne hle_hi ?_⟩
  · intro heq
    have him : |(C₁ - C₂).im| ≤ ‖C₁ - C₂‖ := Complex.abs_im_le_norm _
    have hime : (C₁ - C₂).im = (z₁.im - z₂.im) * Real.cosh R := by
      rw [Complex.sub_im, hC₁, hC₂, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im,
        UpperHalfPlane.center_im, UpperHalfPlane.center_im]
      ring
    have hs' : z₁.im * Real.sinh R - z₂.im * Real.sinh R = (z₁.im - z₂.im) * Real.sinh R := by ring
    rw [hime, ← heq, hs', abs_mul, abs_mul, abs_of_pos hch, abs_of_pos hs] at him
    have hy : |z₁.im - z₂.im| = 0 := by
      have h0 := abs_nonneg (z₁.im - z₂.im)
      have h3 : |z₁.im - z₂.im| * (Real.cosh R - Real.sinh R) ≤ 0 := by linarith
      by_contra hne'
      have h4 : 0 < |z₁.im - z₂.im| := lt_of_le_of_ne h0 (Ne.symm hne')
      have h5 : 0 < |z₁.im - z₂.im| * (Real.cosh R - Real.sinh R) := mul_pos h4 (by linarith)
      linarith
    have hy' : z₁.im = z₂.im := by
      have := abs_eq_zero.1 hy
      linarith
    have hn0 : ‖C₁ - C₂‖ = 0 := by
      rw [← heq, hy', sub_self, abs_zero]
    have hre : (C₁ - C₂).re = 0 := by
      have := Complex.abs_re_le_norm (C₁ - C₂)
      rw [hn0] at this
      exact abs_nonpos_iff.1 this
    rw [Complex.sub_re, hC₁, hC₂, UpperHalfPlane.coe_re, UpperHalfPlane.coe_re,
      UpperHalfPlane.center_re, UpperHalfPlane.center_re] at hre
    apply hne
    apply UpperHalfPlane.ext
    apply Complex.ext
    · show z₁.re = z₂.re
      linarith
    · show z₁.im = z₂.im
      exact hy'
  · intro heq
    apply h2R
    exact ft1gb_external_tangent_radius hR.le (by rw [heq]; ring)

end LiZhongQC
