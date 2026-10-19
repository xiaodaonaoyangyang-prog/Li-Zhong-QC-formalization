import LiZhongQC.Lemmas.HyperbolicSurfaceArea

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

noncomputable section
namespace LiZhongQC

universe u

/-! Local hyperbolic geometry in a complex coordinate.
The functions below are coordinate representatives. Positivity and all geometric
claims are restricted to unramified analytic maps with image in the upper
half-plane. No value at a pole or critical point is used geometrically. -/

/-- Length density pulled back from the upper half-plane by a local coordinate
lift. The derivative is the complex derivative. -/
def s22gc_lengthDensity (ψ : ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖deriv ψ z‖ / (ψ z).im

/-- The coefficient of Euclidean oriented area in a lifted coordinate. -/
def s22gc_areaDensity (ψ : ℂ → ℂ) (z : ℂ) : ℝ :=
  s22gc_lengthDensity ψ z ^ 2

/-- Coordinate representative of the real hyperbolic metric. -/
def s22gc_metric (ψ : ℂ → ℂ) (z v w : ℂ) : ℝ :=
  s22gc_areaDensity ψ z * (v.re * w.re + v.im * w.im)

/-- Coordinate representative of the oriented hyperbolic area two-form. -/
def s22gc_areaForm (ψ : ℂ → ℂ) (z v w : ℂ) : ℝ :=
  s22gc_areaDensity ψ z * (v.re * w.im - v.im * w.re)

/-- Euclidean Laplacian, expressed using the two real coordinate axes. -/
def s22gc_axisLaplacian (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  deriv (deriv (fun t : ℝ => u (z + (t : ℂ)))) 0 +
    deriv (deriv (fun t : ℝ => u (z + (t : ℂ) * I))) 0

/-- Gaussian curvature of the conformal metric, in its standard local formula.
The theorem below computes this expression; curvature minus one is not part of
the definition. -/
def s22gc_curvature (ψ : ℂ → ℂ) (z : ℂ) : ℝ :=
  -s22gc_axisLaplacian (fun w => Real.log (s22gc_lengthDensity ψ w)) z /
    s22gc_areaDensity ψ z

/-- Curvature two-form, with sign K dA. -/
def s22gc_curvatureForm (ψ : ℂ → ℂ) (z v w : ℂ) : ℝ :=
  s22gc_curvature ψ z * s22gc_areaForm ψ z v w

theorem s22gc_lengthDensity_pos {ψ : ℂ → ℂ} {z : ℂ}
    (hd : deriv ψ z ≠ 0) (him : 0 < (ψ z).im) :
    0 < s22gc_lengthDensity ψ z := by
  exact div_pos (norm_pos_iff.2 hd) him

theorem s22gc_areaDensity_nonneg (ψ : ℂ → ℂ) (z : ℂ) :
    0 ≤ s22gc_areaDensity ψ z :=
  sq_nonneg _

theorem s22gc_areaDensity_pos {ψ : ℂ → ℂ} {z : ℂ}
    (hd : deriv ψ z ≠ 0) (him : 0 < (ψ z).im) :
    0 < s22gc_areaDensity ψ z :=
  sq_pos_of_pos (s22gc_lengthDensity_pos hd him)

/-- The determinant of multiplication by a complex number is its squared norm. -/
theorem s22gc_wedge_mul (a v w : ℂ) :
    (a * v).re * (a * w).im - (a * v).im * (a * w).re =
      ‖a‖ ^ 2 * (v.re * w.im - v.im * w.re) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im]
  ring

theorem s22gc_dot_mul (a v w : ℂ) :
    (a * v).re * (a * w).re + (a * v).im * (a * w).im =
      ‖a‖ ^ 2 * (v.re * w.re + v.im * w.im) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im]
  ring

theorem s22gc_metric_symm (ψ : ℂ → ℂ) (z v w : ℂ) :
    s22gc_metric ψ z v w = s22gc_metric ψ z w v := by
  simp only [s22gc_metric]
  ring

theorem s22gc_metric_add_left (ψ : ℂ → ℂ) (z u v w : ℂ) :
    s22gc_metric ψ z (u + v) w =
      s22gc_metric ψ z u w + s22gc_metric ψ z v w := by
  simp only [s22gc_metric, Complex.add_re, Complex.add_im]
  ring

theorem s22gc_metric_smul_left (ψ : ℂ → ℂ) (z v w : ℂ) (a : ℝ) :
    s22gc_metric ψ z (a • v) w = a * s22gc_metric ψ z v w := by
  simp only [s22gc_metric, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

theorem s22gc_metric_add_right (ψ : ℂ → ℂ) (z u v w : ℂ) :
    s22gc_metric ψ z u (v + w) =
      s22gc_metric ψ z u v + s22gc_metric ψ z u w := by
  simp only [s22gc_metric, Complex.add_re, Complex.add_im]
  ring

theorem s22gc_metric_smul_right (ψ : ℂ → ℂ) (z v w : ℂ) (a : ℝ) :
    s22gc_metric ψ z v (a • w) = a * s22gc_metric ψ z v w := by
  simp only [s22gc_metric, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

theorem s22gc_metric_self (ψ : ℂ → ℂ) (z v : ℂ) :
    s22gc_metric ψ z v v = s22gc_areaDensity ψ z * ‖v‖ ^ 2 := by
  rw [s22gc_metric, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

theorem s22gc_metric_positive {ψ : ℂ → ℂ} {z v : ℂ}
    (hd : deriv ψ z ≠ 0) (him : 0 < (ψ z).im) (hv : v ≠ 0) :
    0 < s22gc_metric ψ z v v := by
  rw [s22gc_metric_self]
  exact mul_pos (s22gc_areaDensity_pos hd him) (sq_pos_of_pos (norm_pos_iff.2 hv))

theorem s22gc_areaForm_alternating (ψ : ℂ → ℂ) (z v : ℂ) :
    s22gc_areaForm ψ z v v = 0 := by
  simp [s22gc_areaForm, mul_comm]

theorem s22gc_areaForm_swap (ψ : ℂ → ℂ) (z v w : ℂ) :
    s22gc_areaForm ψ z w v = -s22gc_areaForm ψ z v w := by
  simp only [s22gc_areaForm]
  ring

theorem s22gc_areaForm_add_left (ψ : ℂ → ℂ) (z u v w : ℂ) :
    s22gc_areaForm ψ z (u + v) w =
      s22gc_areaForm ψ z u w + s22gc_areaForm ψ z v w := by
  simp only [s22gc_areaForm, Complex.add_re, Complex.add_im]
  ring

theorem s22gc_areaForm_add_right (ψ : ℂ → ℂ) (z u v w : ℂ) :
    s22gc_areaForm ψ z u (v + w) =
      s22gc_areaForm ψ z u v + s22gc_areaForm ψ z u w := by
  simp only [s22gc_areaForm, Complex.add_re, Complex.add_im]
  ring

theorem s22gc_areaForm_smul_left (ψ : ℂ → ℂ) (z v w : ℂ) (a : ℝ) :
    s22gc_areaForm ψ z (a • v) w = a * s22gc_areaForm ψ z v w := by
  simp only [s22gc_areaForm, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

theorem s22gc_areaForm_smul_right (ψ : ℂ → ℂ) (z v w : ℂ) (a : ℝ) :
    s22gc_areaForm ψ z v (a • w) = a * s22gc_areaForm ψ z v w := by
  simp only [s22gc_areaForm, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

theorem s22gc_areaForm_basis (ψ : ℂ → ℂ) (z : ℂ) :
    s22gc_areaForm ψ z 1 I = s22gc_areaDensity ψ z := by
  simp [s22gc_areaForm]

/-- Area and metric use the same positive conformal coefficient. -/
theorem s22gc_metric_area_gram (ψ : ℂ → ℂ) (z v w : ℂ) :
    s22gc_metric ψ z v v * s22gc_metric ψ z w w -
        s22gc_metric ψ z v w ^ 2 = s22gc_areaForm ψ z v w ^ 2 := by
  simp only [s22gc_metric, s22gc_areaForm]
  ring

/-- The chosen orientation agrees with the complex orientation. -/
theorem s22gc_areaForm_complex_orientation {ψ : ℂ → ℂ} {z v : ℂ}
    (hd : deriv ψ z ≠ 0) (him : 0 < (ψ z).im) (hv : v ≠ 0) :
    0 < s22gc_areaForm ψ z v (I * v) := by
  have he : s22gc_areaForm ψ z v (I * v) = s22gc_metric ψ z v v := by
    simp [s22gc_areaForm, s22gc_metric, Complex.mul_re, Complex.mul_im]
  rw [he]
  exact s22gc_metric_positive hd him hv

/-- Genuine second derivatives, rather than an assigned Laplacian value. -/
theorem s22gc_log_density_second_derivatives {ψ : ℂ → ℂ} {z d : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hd : deriv ψ z ≠ 0)
    (him : 0 < (ψ z).im) (hdunit : ‖d‖ = 1) :
    ∃ c₁ c₂ : ℝ,
      td_Twice (fun t : ℝ => Real.log (s22gc_lengthDensity ψ (z + t * d))) c₁ ∧
      td_Twice (fun t : ℝ => Real.log (s22gc_lengthDensity ψ (z + t * (I * d)))) c₂ ∧
      c₁ + c₂ = s22gc_areaDensity ψ z := by
  exact td_curvature hψ hd him hdunit

theorem s22gc_log_density_axis_sum {ψ : ℂ → ℂ} {z d : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hd : deriv ψ z ≠ 0)
    (him : 0 < (ψ z).im) (hdunit : ‖d‖ = 1) :
    deriv (deriv (fun t : ℝ =>
      Real.log (s22gc_lengthDensity ψ (z + t * d)))) 0 +
    deriv (deriv (fun t : ℝ =>
      Real.log (s22gc_lengthDensity ψ (z + t * (I * d))))) 0 =
      s22gc_areaDensity ψ z := by
  obtain ⟨c₁, c₂, h₁, h₂, hsum⟩ :=
    s22gc_log_density_second_derivatives hψ hd him hdunit
  rw [td_twice_deriv2 h₁, td_twice_deriv2 h₂]
  exact hsum

/-- Liouville's local equation for the hyperbolic conformal factor. -/
theorem s22gc_laplacian_log_density {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hd : deriv ψ z ≠ 0)
    (him : 0 < (ψ z).im) :
    s22gc_axisLaplacian (fun w => Real.log (s22gc_lengthDensity ψ w)) z =
      s22gc_areaDensity ψ z := by
  simpa only [s22gc_axisLaplacian, mul_one] using
    s22gc_log_density_axis_sum hψ hd him (d := (1 : ℂ)) (by simp)

/-- Curvature is computed from the metric; the positive denominator prevents
the totalized division at zero from entering the argument. -/
theorem s22gc_curvature_eq_neg_one {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hd : deriv ψ z ≠ 0)
    (him : 0 < (ψ z).im) :
    s22gc_curvature ψ z = -1 := by
  rw [s22gc_curvature, s22gc_laplacian_log_density hψ hd him,
    neg_div, div_self (s22gc_areaDensity_pos hd him).ne']

theorem s22gc_curvatureForm_eq_neg_areaForm {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hd : deriv ψ z ≠ 0)
    (him : 0 < (ψ z).im) (v w : ℂ) :
    s22gc_curvatureForm ψ z v w = -s22gc_areaForm ψ z v w := by
  rw [s22gc_curvatureForm, s22gc_curvature_eq_neg_one hψ hd him, neg_one_mul]

theorem s22gc_negative_curvature_density {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hd : deriv ψ z ≠ 0)
    (him : 0 < (ψ z).im) :
    -s22gc_curvature ψ z * s22gc_areaDensity ψ z =
      s22gc_areaDensity ψ z := by
  rw [s22gc_curvature_eq_neg_one hψ hd him]
  ring

theorem s22gc_negative_curvatureForm_basis {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hd : deriv ψ z ≠ 0)
    (him : 0 < (ψ z).im) :
    -s22gc_curvatureForm ψ z 1 I = s22gc_areaDensity ψ z := by
  rw [s22gc_curvatureForm_eq_neg_areaForm hψ hd him, neg_neg,
    s22gc_areaForm_basis]

/-! Holomorphic coordinate transformations. -/

theorem s22gc_lengthDensity_comp {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ (χ z)) (hχ : DifferentiableAt ℂ χ z) :
    s22gc_lengthDensity (ψ ∘ χ) z =
      s22gc_lengthDensity ψ (χ z) * ‖deriv χ z‖ := by
  simp only [s22gc_lengthDensity, deriv_comp z hψ hχ, norm_mul,
    Function.comp_apply]
  ring

theorem s22gc_areaDensity_comp {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ (χ z)) (hχ : DifferentiableAt ℂ χ z) :
    s22gc_areaDensity (ψ ∘ χ) z =
      s22gc_areaDensity ψ (χ z) * ‖deriv χ z‖ ^ 2 := by
  simp only [s22gc_areaDensity, s22gc_lengthDensity_comp hψ hχ, mul_pow]

/-- Pullback of the actual bilinear metric, including tangent vectors. -/
theorem s22gc_metric_comp {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ (χ z)) (hχ : DifferentiableAt ℂ χ z)
    (v w : ℂ) :
    s22gc_metric (ψ ∘ χ) z v w =
      s22gc_metric ψ (χ z) (deriv χ z * v) (deriv χ z * w) := by
  rw [s22gc_metric, s22gc_metric, s22gc_areaDensity_comp hψ hχ,
    s22gc_dot_mul]
  ring

/-- Pullback of oriented area; the complex Jacobian preserves orientation. -/
theorem s22gc_areaForm_comp {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ (χ z)) (hχ : DifferentiableAt ℂ χ z)
    (v w : ℂ) :
    s22gc_areaForm (ψ ∘ χ) z v w =
      s22gc_areaForm ψ (χ z) (deriv χ z * v) (deriv χ z * w) := by
  rw [s22gc_areaForm, s22gc_areaForm, s22gc_areaDensity_comp hψ hχ,
    s22gc_wedge_mul]
  ring

theorem s22gc_comp_deriv_ne_zero {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ (χ z)) (hχ : DifferentiableAt ℂ χ z)
    (hdψ : deriv ψ (χ z) ≠ 0) (hdχ : deriv χ z ≠ 0) :
    deriv (ψ ∘ χ) z ≠ 0 := by
  rw [deriv_comp z hψ hχ]
  exact mul_ne_zero hdψ hdχ

theorem s22gc_curvature_comp {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ (χ z)) (hχ : AnalyticAt ℂ χ z)
    (hdψ : deriv ψ (χ z) ≠ 0) (hdχ : deriv χ z ≠ 0)
    (him : 0 < (ψ (χ z)).im) :
    s22gc_curvature (ψ ∘ χ) z = s22gc_curvature ψ (χ z) := by
  rw [s22gc_curvature_eq_neg_one (hψ.comp hχ)
      (s22gc_comp_deriv_ne_zero hψ.differentiableAt hχ.differentiableAt hdψ hdχ) him,
    s22gc_curvature_eq_neg_one hψ hdψ him]

theorem s22gc_curvatureForm_comp {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ (χ z)) (hχ : AnalyticAt ℂ χ z)
    (hdψ : deriv ψ (χ z) ≠ 0) (hdχ : deriv χ z ≠ 0)
    (him : 0 < (ψ (χ z)).im) (v w : ℂ) :
    s22gc_curvatureForm (ψ ∘ χ) z v w =
      s22gc_curvatureForm ψ (χ z) (deriv χ z * v) (deriv χ z * w) := by
  rw [s22gc_curvatureForm, s22gc_curvatureForm,
    s22gc_curvature_comp hψ hχ hdψ hdχ him,
    s22gc_areaForm_comp hψ.differentiableAt hχ.differentiableAt]

/-- The curvature Laplacian transforms with the area Jacobian. -/
theorem s22gc_laplacian_log_density_comp {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ (χ z)) (hχ : AnalyticAt ℂ χ z)
    (hdψ : deriv ψ (χ z) ≠ 0) (hdχ : deriv χ z ≠ 0)
    (him : 0 < (ψ (χ z)).im) :
    s22gc_axisLaplacian (fun w => Real.log (s22gc_lengthDensity (ψ ∘ χ) w)) z =
      s22gc_axisLaplacian (fun w => Real.log (s22gc_lengthDensity ψ w)) (χ z) *
        ‖deriv χ z‖ ^ 2 := by
  rw [s22gc_laplacian_log_density (hψ.comp hχ)
      (s22gc_comp_deriv_ne_zero hψ.differentiableAt hχ.differentiableAt hdψ hdχ) him,
    s22gc_laplacian_log_density hψ hdψ him,
    s22gc_areaDensity_comp hψ.differentiableAt hχ.differentiableAt]

/-! Identity coordinate and the density used by the surface measure. -/

theorem s22gc_identity_lengthDensity (z : ℂ) :
    s22gc_lengthDensity (fun w : ℂ => w) z = 1 / z.im := by
  simp [s22gc_lengthDensity]

theorem s22gc_identity_areaDensity (z : ℂ) :
    s22gc_areaDensity (fun w : ℂ => w) z = 1 / z.im ^ 2 := by
  rw [s22gc_areaDensity, s22gc_identity_lengthDensity, div_pow, one_pow]

theorem s22gc_identity_curvature {z : ℂ} (hz : z ∈ upperHalf) :
    s22gc_curvature (fun w : ℂ => w) z = -1 := by
  exact s22gc_curvature_eq_neg_one analyticAt_id (by simp) hz

theorem s22gc_identity_negative_curvatureForm {z : ℂ} (hz : z ∈ upperHalf) :
    -s22gc_curvatureForm (fun w : ℂ => w) z 1 I = 1 / z.im ^ 2 := by
  rw [s22gc_negative_curvatureForm_basis (ψ := fun w : ℂ => w)
    analyticAt_id (by simp) hz,
    s22gc_identity_areaDensity]

/-! Invariance under a real determinant-one Möbius transformation. -/

theorem s22gc_mobius_deriv_norm (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : z ∈ upperHalf) :
    ‖deriv (h36p_m γ) z‖ = 1 / ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ^ 2 := by
  rw [(h36p_m_hasDerivAt γ hz).deriv, norm_div, norm_one, norm_pow]

theorem s22gc_mobius_deriv_ne_zero (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : z ∈ upperHalf) :
    deriv (h36p_m γ) z ≠ 0 := by
  rw [(h36p_m_hasDerivAt γ hz).deriv]
  exact one_div_ne_zero (pow_ne_zero _ (k24_d_den_ne_zero (b33_d_det γ)
    (ne_of_gt (show 0 < z.im from hz))))

theorem s22gc_mobius_im (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} :
    (h36p_m γ z).im = z.im / ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ^ 2 := by
  change (((γ 0 0 : ℂ) * z + γ 0 1) /
    ((γ 1 0 : ℂ) * z + γ 1 1)).im = _
  rw [utm_im_mobius (b33_d_det γ), Complex.normSq_eq_norm_sq]

theorem s22gc_mobius_lengthDensity (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : z ∈ upperHalf) :
    s22gc_lengthDensity (h36p_m γ) z =
      s22gc_lengthDensity (fun w : ℂ => w) z := by
  have hy : z.im ≠ 0 := ne_of_gt (show 0 < z.im from hz)
  have hn : ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ≠ 0 :=
    norm_ne_zero_iff.2 (k24_d_den_ne_zero (b33_d_det γ) hy)
  rw [s22gc_lengthDensity, s22gc_mobius_deriv_norm γ hz,
    s22gc_mobius_im, s22gc_identity_lengthDensity]
  field_simp [hy, hn]

theorem s22gc_lengthDensity_postcompose_mobius
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ z) (him : ψ z ∈ upperHalf) :
    s22gc_lengthDensity (h36p_m γ ∘ ψ) z = s22gc_lengthDensity ψ z := by
  rw [s22gc_lengthDensity_comp (h36p_m_hasDerivAt γ him).differentiableAt hψ,
    s22gc_mobius_lengthDensity γ him, s22gc_identity_lengthDensity,
    s22gc_lengthDensity]
  ring

theorem s22gc_areaDensity_postcompose_mobius
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ z) (him : ψ z ∈ upperHalf) :
    s22gc_areaDensity (h36p_m γ ∘ ψ) z = s22gc_areaDensity ψ z := by
  rw [s22gc_areaDensity, s22gc_areaDensity,
    s22gc_lengthDensity_postcompose_mobius γ hψ him]

theorem s22gc_metric_postcompose_mobius
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ z) (him : ψ z ∈ upperHalf) (v w : ℂ) :
    s22gc_metric (h36p_m γ ∘ ψ) z v w = s22gc_metric ψ z v w := by
  rw [s22gc_metric, s22gc_metric, s22gc_areaDensity_postcompose_mobius γ hψ him]

theorem s22gc_areaForm_postcompose_mobius
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ z) (him : ψ z ∈ upperHalf) (v w : ℂ) :
    s22gc_areaForm (h36p_m γ ∘ ψ) z v w = s22gc_areaForm ψ z v w := by
  rw [s22gc_areaForm, s22gc_areaForm, s22gc_areaDensity_postcompose_mobius γ hψ him]

theorem s22gc_lengthDensity_germ_congr {ψ χ : ℂ → ℂ} {z : ℂ}
    (he : ψ =ᶠ[𝓝 z] χ) :
    s22gc_lengthDensity ψ z = s22gc_lengthDensity χ z := by
  rw [s22gc_lengthDensity, s22gc_lengthDensity, he.deriv_eq, he.self_of_nhds]

theorem s22gc_areaDensity_germ_congr {ψ χ : ℂ → ℂ} {z : ℂ}
    (he : ψ =ᶠ[𝓝 z] χ) :
    s22gc_areaDensity ψ z = s22gc_areaDensity χ z := by
  rw [s22gc_areaDensity, s22gc_areaDensity, s22gc_lengthDensity_germ_congr he]

theorem s22gc_metric_germ_congr {ψ χ : ℂ → ℂ} {z : ℂ}
    (he : ψ =ᶠ[𝓝 z] χ) (v w : ℂ) :
    s22gc_metric ψ z v w = s22gc_metric χ z v w := by
  rw [s22gc_metric, s22gc_metric, s22gc_areaDensity_germ_congr he]

theorem s22gc_areaForm_germ_congr {ψ χ : ℂ → ℂ} {z : ℂ}
    (he : ψ =ᶠ[𝓝 z] χ) (v w : ℂ) :
    s22gc_areaForm ψ z v w = s22gc_areaForm χ z v w := by
  rw [s22gc_areaForm, s22gc_areaForm, s22gc_areaDensity_germ_congr he]

/-- A Möbius transformation is analytic at every point of the upper half-plane. -/
theorem s22gc_mobius_analyticAt (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : z ∈ upperHalf) :
    AnalyticAt ℂ (h36p_m γ) z := by
  change AnalyticAt ℂ (fun w : ℂ =>
    ((γ 0 0 : ℂ) * w + γ 0 1) / ((γ 1 0 : ℂ) * w + γ 1 1)) z
  exact ((analyticAt_const.mul analyticAt_id).add analyticAt_const).div
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const)
    (k24_d_den_ne_zero (b33_d_det γ) (ne_of_gt (show 0 < z.im from hz)))

theorem s22gc_curvatureForm_postcompose_mobius
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hd : deriv ψ z ≠ 0)
    (him : ψ z ∈ upperHalf) (v w : ℂ) :
    s22gc_curvatureForm (h36p_m γ ∘ ψ) z v w =
      s22gc_curvatureForm ψ z v w := by
  have hm := s22gc_mobius_analyticAt γ him
  rw [s22gc_curvatureForm_eq_neg_areaForm (hm.comp hψ)
      (s22gc_comp_deriv_ne_zero hm.differentiableAt hψ.differentiableAt
        (s22gc_mobius_deriv_ne_zero γ him) hd) (h36p_m_mem γ him),
    s22gc_curvatureForm_eq_neg_areaForm hψ hd him,
    s22gc_areaForm_postcompose_mobius γ hψ.differentiableAt him]

theorem s22gc_lengthDensity_continuousAt {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (him : 0 < (ψ z).im) :
    ContinuousAt (s22gc_lengthDensity ψ) z := by
  exact hψ.deriv.continuousAt.norm.div
    (Complex.continuous_im.continuousAt.comp hψ.continuousAt) him.ne'

theorem s22gc_areaDensity_continuousAt {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (him : 0 < (ψ z).im) :
    ContinuousAt (s22gc_areaDensity ψ) z :=
  (s22gc_lengthDensity_continuousAt hψ him).pow 2

theorem s22gc_log_density_continuousAt {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hd : deriv ψ z ≠ 0)
    (him : 0 < (ψ z).im) :
    ContinuousAt (fun w => Real.log (s22gc_lengthDensity ψ w)) z :=
  (s22gc_lengthDensity_continuousAt hψ him).log
    (s22gc_lengthDensity_pos hd him).ne'

/-! Descent: local lifts of the same surface map differ by one deck
transformation on a neighbourhood. A pointwise orbit statement alone would
not suffice to compare derivatives, so the neighbourhood statement is proved. -/

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]

theorem s22gc_exists_injective_sheet [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {z : ℂ} (hz : z ∈ upperHalf) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ upperHalf ∧
      InjOn (s22gm_projectionExtension p) U := by
  obtain ⟨V, hVo, hzV, hi⟩ :=
    hp.1.isLocalHomeomorph.isLocallyInjective (⟨z, hz⟩ : UpperHalfPlane)
  refine ⟨UpperHalfPlane.coe '' V,
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hVo, ⟨⟨z, hz⟩, hzV, rfl⟩, ?_, ?_⟩
  · rintro w ⟨τ, _, rfl⟩
    exact τ.coe_im_pos
  · rintro w ⟨τ, hτ, rfl⟩ v ⟨σ, hσ, rfl⟩ he
    apply congrArg UpperHalfPlane.coe
    apply hi hτ hσ
    simpa only [s22gm_projectionExtension_coe] using he

/-- Local lifts agree up to a single element of Γ, with no faithfulness
assumption on the SL action and no fixed choice of lift. -/
theorem s22gc_lift_germ_deck [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : ContinuousAt ψ z) (hχ : ContinuousAt χ z)
    (hψH : ψ z ∈ upperHalf) (hχH : χ z ∈ upperHalf)
    (he : (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z]
      (fun w => s22gm_projectionExtension p (χ w))) :
    ∃ γ ∈ Γ, χ =ᶠ[𝓝 z] h36p_m γ ∘ ψ := by
  have he0 : p (⟨ψ z, hψH⟩ : UpperHalfPlane) =
      p (⟨χ z, hχH⟩ : UpperHalfPlane) := by
    simpa only [s22gm_projectionExtension,
      UpperHalfPlane.ofComplex_apply_of_im_pos hψH,
      UpperHalfPlane.ofComplex_apply_of_im_pos hχH] using he.self_of_nhds
  obtain ⟨γ, hγ, hγz⟩ :=
    (hp.2.2.2 ⟨ψ z, hψH⟩ ⟨χ z, hχH⟩).1 he0
  have hγz' : h36p_m γ (ψ z) = χ z := by
    have he' := h36p_m_coe γ ⟨ψ z, hψH⟩
    rw [hγz] at he'
    exact he'
  obtain ⟨U, hUo, hzU, hUH, hinj⟩ := s22gc_exists_injective_sheet hp hχH
  have hχU : ∀ᶠ w in 𝓝 z, χ w ∈ U := hχ (hUo.mem_nhds hzU)
  have hγU : ∀ᶠ w in 𝓝 z, h36p_m γ (ψ w) ∈ U := by
    have hc := (h36p_m_hasDerivAt γ hψH).continuousAt.comp hψ
    have hzU' : (h36p_m γ ∘ ψ) z ∈ U := by
      change h36p_m γ (ψ z) ∈ U
      rw [hγz']
      exact hzU
    exact hc (hUo.mem_nhds hzU')
  have hψev : ∀ᶠ w in 𝓝 z, ψ w ∈ upperHalf :=
    hψ (isOpen_upperHalf.mem_nhds hψH)
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hχU, hγU, hψev, he] with w hwχ hwγ hwH hwe
  apply hinj hwχ hwγ
  exact hwe.symm.trans (s22gm_projectionExtension_invariant hp hγ hwH).symm

/-- The metric coefficient is independent of the choice of analytic lift
of a fixed local surface parametrization. -/
theorem s22gc_lift_lengthDensity_eq [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ z) (hχ : ContinuousAt χ z)
    (hψH : ψ z ∈ upperHalf) (hχH : χ z ∈ upperHalf)
    (he : (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z]
      (fun w => s22gm_projectionExtension p (χ w))) :
    s22gc_lengthDensity χ z = s22gc_lengthDensity ψ z := by
  obtain ⟨γ, _, hγ⟩ :=
    s22gc_lift_germ_deck hp hψ.continuousAt hχ hψH hχH he
  rw [s22gc_lengthDensity_germ_congr hγ,
    s22gc_lengthDensity_postcompose_mobius γ hψ hψH]

theorem s22gc_lift_areaDensity_eq [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ z) (hχ : ContinuousAt χ z)
    (hψH : ψ z ∈ upperHalf) (hχH : χ z ∈ upperHalf)
    (he : (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z]
      (fun w => s22gm_projectionExtension p (χ w))) :
    s22gc_areaDensity χ z = s22gc_areaDensity ψ z := by
  rw [s22gc_areaDensity, s22gc_areaDensity,
    s22gc_lift_lengthDensity_eq hp hψ hχ hψH hχH he]

theorem s22gc_lift_metric_eq [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ z) (hχ : ContinuousAt χ z)
    (hψH : ψ z ∈ upperHalf) (hχH : χ z ∈ upperHalf)
    (he : (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z]
      (fun w => s22gm_projectionExtension p (χ w))) (v w : ℂ) :
    s22gc_metric χ z v w = s22gc_metric ψ z v w := by
  rw [s22gc_metric, s22gc_metric,
    s22gc_lift_areaDensity_eq hp hψ hχ hψH hχH he]

theorem s22gc_lift_areaForm_eq [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ z) (hχ : ContinuousAt χ z)
    (hψH : ψ z ∈ upperHalf) (hχH : χ z ∈ upperHalf)
    (he : (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z]
      (fun w => s22gm_projectionExtension p (χ w))) (v w : ℂ) :
    s22gc_areaForm χ z v w = s22gc_areaForm ψ z v w := by
  rw [s22gc_areaForm, s22gc_areaForm,
    s22gc_lift_areaDensity_eq hp hψ hχ hψH hχH he]

theorem s22gc_lift_curvatureForm_eq [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hχ : AnalyticAt ℂ χ z)
    (hdψ : deriv ψ z ≠ 0) (hdχ : deriv χ z ≠ 0)
    (hψH : ψ z ∈ upperHalf) (hχH : χ z ∈ upperHalf)
    (he : (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z]
      (fun w => s22gm_projectionExtension p (χ w))) (v w : ℂ) :
    s22gc_curvatureForm χ z v w = s22gc_curvatureForm ψ z v w := by
  rw [s22gc_curvatureForm_eq_neg_areaForm hχ hdχ hχH,
    s22gc_curvatureForm_eq_neg_areaForm hψ hdψ hψH,
    s22gc_lift_areaForm_eq hp hψ.differentiableAt hχ.continuousAt hψH hχH he]

/-- The compatibility statement for two different surface coordinates:
if their projected parametrizations agree after a holomorphic coordinate
change, the local metrics transform by its differential. -/
theorem s22gc_surface_coordinate_metric [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {ψ χ η : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ (η z)) (hη : DifferentiableAt ℂ η z)
    (hχ : ContinuousAt χ z)
    (hψH : ψ (η z) ∈ upperHalf) (hχH : χ z ∈ upperHalf)
    (he : (fun w => s22gm_projectionExtension p (ψ (η w))) =ᶠ[𝓝 z]
      (fun w => s22gm_projectionExtension p (χ w))) (v w : ℂ) :
    s22gc_metric χ z v w =
      s22gc_metric ψ (η z) (deriv η z * v) (deriv η z * w) := by
  rw [s22gc_lift_metric_eq hp (hψ.comp z hη) hχ hψH hχH he,
    s22gc_metric_comp hψ hη]

theorem s22gc_surface_coordinate_areaForm [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {ψ χ η : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ (η z)) (hη : DifferentiableAt ℂ η z)
    (hχ : ContinuousAt χ z)
    (hψH : ψ (η z) ∈ upperHalf) (hχH : χ z ∈ upperHalf)
    (he : (fun w => s22gm_projectionExtension p (ψ (η w))) =ᶠ[𝓝 z]
      (fun w => s22gm_projectionExtension p (χ w))) (v w : ℂ) :
    s22gc_areaForm χ z v w =
      s22gc_areaForm ψ (η z) (deriv η z * v) (deriv η z * w) := by
  rw [s22gc_lift_areaForm_eq hp (hψ.comp z hη) hχ hψH hχH he,
    s22gc_areaForm_comp hψ hη]

/-! Integration: identify the geometric area coefficient with the existing
Borel measure. The change-of-variables theorem retains extended integrals,
so no finiteness or integrability premise is hidden here. -/

/-- Complex holomorphic change of variables with its real Jacobian. -/
theorem s22gc_lintegral_holomorphic_image {U : Set ℂ} (hUm : MeasurableSet U)
    {ψ : ℂ → ℂ} (hψ : ∀ z ∈ U, DifferentiableAt ℂ ψ z)
    (hinj : InjOn ψ U) (g : ℂ → ℝ≥0∞) :
    (∫⁻ w in ψ '' U, g w) =
      ∫⁻ z in U, g (ψ z) * ENNReal.ofReal (‖deriv ψ z‖ ^ 2) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hUm
    (fun z hz => ((hψ z hz).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    hinj]
  refine setLIntegral_congr_fun hUm fun z _ => ?_
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg (‖deriv ψ z‖))]
  exact mul_comm _ _

/-- Hyperbolic area on the image of a local holomorphic coordinate lift. -/
theorem s22gc_lintegral_hyperbolic_image {U : Set ℂ} (hUm : MeasurableSet U)
    {ψ : ℂ → ℂ} (hψ : ∀ z ∈ U, DifferentiableAt ℂ ψ z)
    (hinj : InjOn ψ U) (g : ℂ → ℝ≥0∞) :
    (∫⁻ w in ψ '' U, g w * ENNReal.ofReal (1 / w.im ^ 2)) =
      ∫⁻ z in U, g (ψ z) * ENNReal.ofReal (s22gc_areaDensity ψ z) := by
  rw [s22gc_lintegral_holomorphic_image hUm hψ hinj]
  refine setLIntegral_congr_fun hUm fun z _ => ?_
  rw [mul_assoc, ← ENNReal.ofReal_mul
    (by positivity : 0 ≤ 1 / (ψ z).im ^ 2)]
  congr 2
  simp only [s22gc_areaDensity, s22gc_lengthDensity, div_pow]
  ring

/-- The local area formula in an arbitrary holomorphic parametrization of an
injective covering sheet. Openness of the image is the chart-domain condition. -/
theorem s22gc_surface_lintegral_chart [ChartedSpace ℂ S] [T2Space S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {F U : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hUm : MeasurableSet U)
    {ψ : ℂ → ℂ} (hψ : ∀ z ∈ U, DifferentiableAt ℂ ψ z)
    (hinj : InjOn ψ U) (himage : IsOpen (ψ '' U))
    (hH : ψ '' U ⊆ upperHalf)
    (hpinj : InjOn (s22gm_projectionExtension p) (ψ '' U))
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y in s22gm_projectionExtension p '' (ψ '' U),
      f y ∂s22gm_surfaceArea p F) =
      ∫⁻ z in U, f (s22gm_projectionExtension p (ψ z)) *
        ENNReal.ofReal (s22gc_areaDensity ψ z) := by
  rw [s22gm_lintegral_open_sheet hp hF himage hH hpinj hf]
  exact s22gc_lintegral_hyperbolic_image hUm hψ hinj
    (fun w => f (s22gm_projectionExtension p w))

/-- In an analytic unramified coordinate, integration of the negative curvature
two-form is exactly integration against surface hyperbolic area. -/
theorem s22gc_surface_lintegral_negative_curvature [ChartedSpace ℂ S] [T2Space S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {F U : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hUm : MeasurableSet U)
    {ψ : ℂ → ℂ} (hψ : ∀ z ∈ U, AnalyticAt ℂ ψ z)
    (hd : ∀ z ∈ U, deriv ψ z ≠ 0)
    (hinj : InjOn ψ U) (himage : IsOpen (ψ '' U))
    (hH : ψ '' U ⊆ upperHalf)
    (hpinj : InjOn (s22gm_projectionExtension p) (ψ '' U))
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y in s22gm_projectionExtension p '' (ψ '' U),
      f y ∂s22gm_surfaceArea p F) =
      ∫⁻ z in U, f (s22gm_projectionExtension p (ψ z)) *
        ENNReal.ofReal (-s22gc_curvatureForm ψ z 1 I) := by
  rw [s22gc_surface_lintegral_chart hp hF hUm
    (fun z hz => (hψ z hz).differentiableAt) hinj himage hH hpinj hf]
  refine setLIntegral_congr_fun hUm fun z hz => ?_
  rw [s22gc_negative_curvatureForm_basis (hψ z hz) (hd z hz) (hH ⟨z, hz, rfl⟩)]

/-- The same result with the Laplacian coefficient displayed explicitly.
This is the differential expression that a later Stokes argument must integrate. -/
theorem s22gc_surface_lintegral_laplacian [ChartedSpace ℂ S] [T2Space S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {F U : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hUm : MeasurableSet U)
    {ψ : ℂ → ℂ} (hψ : ∀ z ∈ U, AnalyticAt ℂ ψ z)
    (hd : ∀ z ∈ U, deriv ψ z ≠ 0)
    (hinj : InjOn ψ U) (himage : IsOpen (ψ '' U))
    (hH : ψ '' U ⊆ upperHalf)
    (hpinj : InjOn (s22gm_projectionExtension p) (ψ '' U))
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y in s22gm_projectionExtension p '' (ψ '' U),
      f y ∂s22gm_surfaceArea p F) =
      ∫⁻ z in U, f (s22gm_projectionExtension p (ψ z)) *
        ENNReal.ofReal
          (s22gc_axisLaplacian (fun w => Real.log (s22gc_lengthDensity ψ w)) z) := by
  rw [s22gc_surface_lintegral_chart hp hF hUm
    (fun z hz => (hψ z hz).differentiableAt) hinj himage hH hpinj hf]
  refine setLIntegral_congr_fun hUm fun z hz => ?_
  rw [s22gc_laplacian_log_density (hψ z hz) (hd z hz) (hH ⟨z, hz, rfl⟩)]

/-- Area on a complex chart domain. Its density is determined by the local
metric, and its values outside the domain are discarded. -/
def s22gc_chartArea (ψ : ℂ → ℂ) (U : Set ℂ) : Measure ℂ :=
  (volume.restrict U).withDensity (fun z => ENNReal.ofReal (s22gc_areaDensity ψ z))

theorem s22gc_areaDensity_aemeasurable {U : Set ℂ} (hUm : MeasurableSet U)
    {ψ : ℂ → ℂ} (hψ : ∀ z ∈ U, AnalyticAt ℂ ψ z)
    (hH : ∀ z ∈ U, 0 < (ψ z).im) :
    AEMeasurable (fun z => ENNReal.ofReal (s22gc_areaDensity ψ z))
      (volume.restrict U) := by
  have hc : ContinuousOn (s22gc_areaDensity ψ) U :=
    fun z hz => (s22gc_areaDensity_continuousAt (hψ z hz) (hH z hz)).continuousWithinAt
  exact measurable_id.ennreal_ofReal.comp_aemeasurable (hc.aemeasurable hUm)

theorem s22gc_projected_chart_aemeasurable [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {U : Set ℂ} (hUm : MeasurableSet U)
    {ψ : ℂ → ℂ} (hψ : ∀ z ∈ U, ContinuousAt ψ z)
    (hH : ∀ z ∈ U, ψ z ∈ upperHalf) :
    AEMeasurable (fun z => s22gm_projectionExtension p (ψ z)) (volume.restrict U) := by
  have hc : ContinuousOn (fun z => s22gm_projectionExtension p (ψ z)) U := by
    intro z hz
    have hq := (s22gm_projectionExtension_continuousOn hp.1.continuous
      (ψ z) (hH z hz)).continuousAt (isOpen_upperHalf.mem_nhds (hH z hz))
    exact (hq.comp (hψ z hz)).continuousWithinAt
  exact hc.aemeasurable hUm

/-- Replacing a coordinate lift off the chart domain does not change its area
measure, provided its germs on the domain are the same. -/
theorem s22gc_chartArea_germ_congr {U : Set ℂ} (hUm : MeasurableSet U)
    {ψ χ : ℂ → ℂ} (he : ∀ z ∈ U, ψ =ᶠ[𝓝 z] χ) :
    s22gc_chartArea ψ U = s22gc_chartArea χ U := by
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hUm] with z hz
  rw [s22gc_areaDensity_germ_congr (he z hz)]

/-- The locally defined area measure is equally the negative-curvature
measure. This is an equality of measures, not only an equality of total masses. -/
theorem s22gc_chartArea_eq_curvature_density {U : Set ℂ} (hUm : MeasurableSet U)
    {ψ : ℂ → ℂ} (hψ : ∀ z ∈ U, AnalyticAt ℂ ψ z)
    (hd : ∀ z ∈ U, deriv ψ z ≠ 0) (hH : ∀ z ∈ U, 0 < (ψ z).im) :
    s22gc_chartArea ψ U = (volume.restrict U).withDensity
      (fun z => ENNReal.ofReal (-s22gc_curvatureForm ψ z 1 I)) := by
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hUm] with z hz
  rw [s22gc_negative_curvatureForm_basis (hψ z hz) (hd z hz) (hH z hz)]

/-- The analytic chart measure pushes forward to precisely the restriction of
the intrinsic surface measure. Local measurability suffices: arbitrary extensions
of the chart outside its domain need not be measurable. -/
theorem s22gc_surfaceArea_restrict_chart [ChartedSpace ℂ S] [T2Space S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {F U : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hUm : MeasurableSet U)
    {ψ : ℂ → ℂ} (hψ : ∀ z ∈ U, AnalyticAt ℂ ψ z)
    (hinj : InjOn ψ U) (himage : IsOpen (ψ '' U))
    (hH : ψ '' U ⊆ upperHalf)
    (hpinj : InjOn (s22gm_projectionExtension p) (ψ '' U)) :
    (s22gm_surfaceArea p F).restrict (s22gm_projectionExtension p '' (ψ '' U)) =
      Measure.map (fun z => s22gm_projectionExtension p (ψ z)) (s22gc_chartArea ψ U) := by
  have hH' : ∀ z ∈ U, ψ z ∈ upperHalf := fun z hz => hH ⟨z, hz, rfl⟩
  have hr := s22gc_areaDensity_aemeasurable hUm hψ hH'
  have hq := s22gc_projected_chart_aemeasurable hp hUm
    (fun z hz => (hψ z hz).continuousAt) hH'
  have hq' : AEMeasurable (fun z => s22gm_projectionExtension p (ψ z))
      (s22gc_chartArea ψ U) :=
    hq.mono_ac (withDensity_absolutelyContinuous _ _)
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [s22gc_surface_lintegral_chart hp hF hUm
    (fun z hz => (hψ z hz).differentiableAt) hinj himage hH hpinj hf,
    lintegral_map' hf.aemeasurable hq']
  change (∫⁻ z in U, f (s22gm_projectionExtension p (ψ z)) *
    ENNReal.ofReal (s22gc_areaDensity ψ z)) =
    ∫⁻ z, f (s22gm_projectionExtension p (ψ z))
      ∂(volume.restrict U).withDensity (fun z => ENNReal.ofReal (s22gc_areaDensity ψ z))
  symm
  simpa only [Function.comp_apply, Pi.mul_apply, mul_comm] using
    (lintegral_withDensity_eq_lintegral_mul₀ hr (hf.comp_aemeasurable hq))

theorem s22gc_surfaceArea_restrict_curvature [ChartedSpace ℂ S] [T2Space S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {F U : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hUm : MeasurableSet U)
    {ψ : ℂ → ℂ} (hψ : ∀ z ∈ U, AnalyticAt ℂ ψ z)
    (hd : ∀ z ∈ U, deriv ψ z ≠ 0)
    (hinj : InjOn ψ U) (himage : IsOpen (ψ '' U))
    (hH : ψ '' U ⊆ upperHalf)
    (hpinj : InjOn (s22gm_projectionExtension p) (ψ '' U)) :
    (s22gm_surfaceArea p F).restrict (s22gm_projectionExtension p '' (ψ '' U)) =
      Measure.map (fun z => s22gm_projectionExtension p (ψ z))
        ((volume.restrict U).withDensity
          (fun z => ENNReal.ofReal (-s22gc_curvatureForm ψ z 1 I))) := by
  rw [s22gc_surfaceArea_restrict_chart hp hF hUm hψ hinj himage hH hpinj,
    s22gc_chartArea_eq_curvature_density hUm hψ hd (fun z hz => hH ⟨z, hz, rfl⟩)]

/-- Every surface point is covered by an open injective upper-half-plane sheet.
This derives the supply of local domains from uniformization itself. -/
theorem s22gc_surface_point_sheet [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) (y : S) :
    ∃ U : Set ℂ, IsOpen U ∧ U ⊆ upperHalf ∧
      InjOn (s22gm_projectionExtension p) U ∧
      y ∈ s22gm_projectionExtension p '' U := by
  obtain ⟨τ, rfl⟩ := hp.2.2.1 y
  obtain ⟨U, hUo, hτU, hUH, hi⟩ :=
    s22gc_exists_injective_sheet hp τ.coe_im_pos
  exact ⟨U, hUo, hUH, hi, ⟨(τ : ℂ), hτU, s22gm_projectionExtension_coe p τ⟩⟩

/-- Compactness gives finitely many genuine injective sheets covering the
surface; no finite-area conclusion is used in constructing them. -/
theorem s22gc_finite_sheet_cover [ChartedSpace ℂ S] [CompactSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    ∃ (U : S → Set ℂ) (t : Finset S),
      (∀ y, IsOpen (U y) ∧ U y ⊆ upperHalf ∧
        InjOn (s22gm_projectionExtension p) (U y)) ∧
      Set.univ ⊆ ⋃ y ∈ t, s22gm_projectionExtension p '' U y := by
  classical
  choose U hUo hUH hi hy using s22gc_surface_point_sheet hp
  have hcover : (Set.univ : Set S) ⊆ ⋃ y : S, s22gm_projectionExtension p '' U y := by
    intro y _
    exact mem_iUnion.2 ⟨y, hy y⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun y : S => s22gm_projectionExtension p '' U y)
    (fun y => s22gm_projectionExtension_image_isOpen hp (hUo y) (hUH y)) hcover
  exact ⟨U, t, fun y => ⟨hUo y, hUH y, hi y⟩, ht⟩

/-! Global assembly of local integrals. These lemmas take an ordinary
nonnegative measurable partition of unity subordinate to the sheets.
The numerical curvature-degree/Stokes identity is neither assumed nor proved
here. The partition identity below is only the usual sum of weights equal to one. -/

theorem s22gc_lintegral_eq_restrict_of_zero_off
    {μ : Measure S} {A : Set S} (hA : MeasurableSet A)
    {f : S → ℝ≥0∞} (hzero : ∀ y ∉ A, f y = 0) :
    (∫⁻ y, f y ∂μ) = ∫⁻ y in A, f y ∂μ := by
  classical
  rw [← lintegral_indicator hA]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ A
  · rw [indicator_of_mem hy]
  · rw [indicator_of_notMem hy, hzero y hy]

theorem s22gc_lintegral_partition {ι : Type*} [Countable ι]
    (μ : Measure S) {a : ι → S → ℝ≥0∞}
    (ha : ∀ i, Measurable (a i)) (hsum : ∀ y, ∑' i, a i y = 1)
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂μ) = ∑' i, ∫⁻ y, a i y * f y ∂μ := by
  rw [← lintegral_tsum (μ := μ) (f := fun i y => a i y * f y)
    (fun i => ((ha i).mul hf).aemeasurable)]
  apply lintegral_congr
  intro y
  rw [ENNReal.tsum_mul_right, hsum y, one_mul]

/-- A global integral is assembled from coordinate area integrals. All
Jacobian factors are the proven metric coefficients. -/
theorem s22gc_surface_lintegral_partition [ChartedSpace ℂ S] [T2Space S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    {ι : Type*} [Countable ι] (U : ι → Set ℂ) (ψ : ι → ℂ → ℂ)
    (hUm : ∀ i, MeasurableSet (U i))
    (hψ : ∀ i, ∀ z ∈ U i, DifferentiableAt ℂ (ψ i) z)
    (hinj : ∀ i, InjOn (ψ i) (U i))
    (himage : ∀ i, IsOpen (ψ i '' U i))
    (hH : ∀ i, ψ i '' U i ⊆ upperHalf)
    (hpinj : ∀ i, InjOn (s22gm_projectionExtension p) (ψ i '' U i))
    (a : ι → S → ℝ≥0∞) (ha : ∀ i, Measurable (a i))
    (hsum : ∀ y, ∑' i, a i y = 1)
    (hsupp : ∀ i y, y ∉ s22gm_projectionExtension p '' (ψ i '' U i) → a i y = 0)
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂s22gm_surfaceArea p F) =
      ∑' i, ∫⁻ z in U i,
        (a i (s22gm_projectionExtension p (ψ i z)) *
          f (s22gm_projectionExtension p (ψ i z))) *
          ENNReal.ofReal (s22gc_areaDensity (ψ i) z) := by
  rw [s22gc_lintegral_partition _ ha hsum hf]
  apply tsum_congr
  intro i
  have hA := (s22gm_projectionExtension_image_isOpen hp (himage i) (hH i)).measurableSet
  rw [s22gc_lintegral_eq_restrict_of_zero_off hA
    (f := fun y => a i y * f y) (fun y hy => by rw [hsupp i y hy, zero_mul])]
  exact s22gc_surface_lintegral_chart hp hF (hUm i) (hψ i)
    (hinj i) (himage i) (hH i) (hpinj i) ((ha i).mul hf)

/-- Global area tested against f equals the sum of local negative-curvature
integrals in any subordinate measurable partition. This is the assembled local
curvature identity; it contains no Euler characteristic or degree premise. -/
theorem s22gc_surface_lintegral_curvature_partition [ChartedSpace ℂ S] [T2Space S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    {ι : Type*} [Countable ι] (U : ι → Set ℂ) (ψ : ι → ℂ → ℂ)
    (hUm : ∀ i, MeasurableSet (U i))
    (hψ : ∀ i, ∀ z ∈ U i, AnalyticAt ℂ (ψ i) z)
    (hd : ∀ i, ∀ z ∈ U i, deriv (ψ i) z ≠ 0)
    (hinj : ∀ i, InjOn (ψ i) (U i))
    (himage : ∀ i, IsOpen (ψ i '' U i))
    (hH : ∀ i, ψ i '' U i ⊆ upperHalf)
    (hpinj : ∀ i, InjOn (s22gm_projectionExtension p) (ψ i '' U i))
    (a : ι → S → ℝ≥0∞) (ha : ∀ i, Measurable (a i))
    (hsum : ∀ y, ∑' i, a i y = 1)
    (hsupp : ∀ i y, y ∉ s22gm_projectionExtension p '' (ψ i '' U i) → a i y = 0)
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂s22gm_surfaceArea p F) =
      ∑' i, ∫⁻ z in U i,
        (a i (s22gm_projectionExtension p (ψ i z)) *
          f (s22gm_projectionExtension p (ψ i z))) *
          ENNReal.ofReal (-s22gc_curvatureForm (ψ i) z 1 I) := by
  rw [s22gc_surface_lintegral_partition hp hF U ψ hUm
    (fun i z hz => (hψ i z hz).differentiableAt) hinj himage hH hpinj a ha hsum hsupp hf]
  apply tsum_congr
  intro i
  refine setLIntegral_congr_fun (hUm i) fun z hz => ?_
  rw [s22gc_negative_curvatureForm_basis (hψ i z hz) (hd i z hz)
    (hH i ⟨z, hz, rfl⟩)]

/-- The total-area specialization is still an extended integral identity.
It does not assert finiteness or replace the missing topological computation. -/
theorem s22gc_total_area_negative_curvature {p : UpperHalfPlane → S}
    (hp : Continuous p) {F : Set ℂ} (hFm : MeasurableSet F) (hFH : F ⊆ upperHalf) :
    s22gm_surfaceArea p F Set.univ =
      ∫⁻ z in F, ENNReal.ofReal
        (-s22gc_curvatureForm (fun w : ℂ => w) z 1 I) := by
  rw [s22gm_surfaceArea_univ hp]
  refine setLIntegral_congr_fun hFm fun z hz => ?_
  rw [s22gc_identity_negative_curvatureForm (hFH hz)]

/-! An explicit orthonormal coframe connection in the upper-half-plane
coordinate. The derivative of its connection form supplies the local exact
two-form needed for a later Stokes calculation. -/

/-- Exterior derivative of a coordinate one-form, evaluated on two vectors. -/
def s22gc_exteriorDerivative (α : ℂ → ℂ → ℝ) (z v w : ℂ) : ℝ :=
  (deriv (fun t : ℝ => α (z + (t : ℂ)) I) 0 -
    deriv (fun t : ℝ => α (z + (t : ℂ) * I) 1) 0) *
    (v.re * w.im - v.im * w.re)

/-- The connection form for the orthonormal coframe dx/y, dy/y, with the
convention that its negative exterior derivative is K dA. -/
def s22gc_connectionForm (z v : ℂ) : ℝ := v.re / z.im

theorem s22gc_connection_horizontal_derivative (z : ℂ) :
    HasDerivAt (fun t : ℝ => s22gc_connectionForm (z + (t : ℂ)) I) 0 0 := by
  simpa only [s22gc_connectionForm, Complex.I_re, zero_div] using
    (hasDerivAt_const (0 : ℝ) (0 : ℝ))

theorem s22gc_connection_vertical_derivative {z : ℂ} (hz : z ∈ upperHalf) :
    HasDerivAt (fun t : ℝ => s22gc_connectionForm (z + (t : ℂ) * I) 1)
      (-(1 / z.im ^ 2)) 0 := by
  have hy : z.im ≠ 0 := ne_of_gt (show 0 < z.im from hz)
  have h : HasDerivAt (fun t : ℝ => (z.im + t)⁻¹) (-(z.im ^ 2)⁻¹) 0 := by
    convert! (hasDerivAt_inv hy).comp_of_eq (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).const_add z.im) (by simp) using 1 <;>
      simp only [Function.comp_apply, mul_one, one_mul]
  simpa [s22gc_connectionForm, one_div, Complex.mul_im] using h

/-- The connection's exterior derivative is the positive hyperbolic area form. -/
theorem s22gc_exterior_connection_eq_area {z : ℂ} (hz : z ∈ upperHalf) (v w : ℂ) :
    s22gc_exteriorDerivative s22gc_connectionForm z v w =
      s22gc_areaForm (fun ζ : ℂ => ζ) z v w := by
  rw [s22gc_exteriorDerivative,
    (s22gc_connection_horizontal_derivative z).deriv,
    (s22gc_connection_vertical_derivative hz).deriv,
    s22gc_areaForm, s22gc_identity_areaDensity]
  ring

/-- Local exactness with the curvature sign fixed explicitly. -/
theorem s22gc_curvatureForm_eq_negative_exterior {z : ℂ} (hz : z ∈ upperHalf)
    (v w : ℂ) :
    s22gc_curvatureForm (fun ζ : ℂ => ζ) z v w =
      -s22gc_exteriorDerivative s22gc_connectionForm z v w := by
  rw [s22gc_exterior_connection_eq_area hz,
    s22gc_curvatureForm_eq_neg_areaForm (ψ := fun ζ : ℂ => ζ)
      analyticAt_id (by simp) hz]

/-- The first orthonormal coframe component is the connection form in this
coordinate; its structure equation is d(dx/y) = (dx/y) wedge (dy/y). -/
theorem s22gc_first_structure_equation {z : ℂ} (hz : z ∈ upperHalf) (v w : ℂ) :
    s22gc_exteriorDerivative s22gc_connectionForm z v w =
      s22gc_connectionForm z v * (w.im / z.im) -
        s22gc_connectionForm z w * (v.im / z.im) := by
  rw [s22gc_exterior_connection_eq_area hz, s22gc_areaForm,
    s22gc_identity_areaDensity]
  simp only [s22gc_connectionForm, div_eq_mul_inv, inv_pow]
  ring

/-- The second orthonormal coframe component has zero exterior derivative. -/
theorem s22gc_second_structure_equation (z v w : ℂ) :
    s22gc_exteriorDerivative (fun ζ u => u.im / ζ.im) z v w = 0 := by
  have hx : (fun t : ℝ => I.im / (z + (t : ℂ)).im) =
      (fun _ : ℝ => 1 / z.im) := by
    funext t
    simp
  have hy : (fun t : ℝ => (1 : ℂ).im / (z + (t : ℂ) * I).im) =
      (fun _ : ℝ => 0) := by
    funext t
    simp
  change (deriv (fun t : ℝ => I.im / (z + (t : ℂ)).im) 0 -
    deriv (fun t : ℝ => (1 : ℂ).im / (z + (t : ℂ) * I).im) 0) *
    (v.re * w.im - v.im * w.re) = 0
  rw [hx, hy]
  simp

/-- The coframe reconstructs the metric used throughout this file. -/
theorem s22gc_metric_coframe (z v w : ℂ) :
    s22gc_metric (fun ζ : ℂ => ζ) z v w =
      s22gc_connectionForm z v * s22gc_connectionForm z w +
        (v.im / z.im) * (w.im / z.im) := by
  rw [s22gc_metric, s22gc_identity_areaDensity]
  simp only [s22gc_connectionForm, div_eq_mul_inv, inv_pow]
  ring

/-- The local exact curvature coefficient integrates to the previously
constructed surface area, without invoking Stokes or assigning an area value. -/
theorem s22gc_surface_lintegral_exterior_connection [ChartedSpace ℂ S] [T2Space S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {F U : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hUo : IsOpen U)
    (hUH : U ⊆ upperHalf) (hinj : InjOn (s22gm_projectionExtension p) U)
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y in s22gm_projectionExtension p '' U, f y ∂s22gm_surfaceArea p F) =
      ∫⁻ z in U, f (s22gm_projectionExtension p z) *
        ENNReal.ofReal (s22gc_exteriorDerivative s22gc_connectionForm z 1 I) := by
  rw [s22gm_lintegral_open_sheet hp hF hUo hUH hinj hf]
  refine setLIntegral_congr_fun hUo.measurableSet fun z hz => ?_
  rw [s22gc_exterior_connection_eq_area (hUH hz), s22gc_areaForm_basis,
    s22gc_identity_areaDensity]

end LiZhongQC

