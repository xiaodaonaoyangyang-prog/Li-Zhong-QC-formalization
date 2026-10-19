import LiZhongQC.Lemmas.HyperbolicConnectionTransition
import LiZhongQC.Lemmas.CurvatureDegreeBoundary

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

noncomputable section
namespace LiZhongQC

universe u

/-- The hyperbolic connection expressed in the frame of a meromorphic
canonical differential. It is used only off the coefficient's zeros and
poles. The subtraction is fixed by the two actual transition laws. -/
def s22cd_canonicalGauge (ψ f : ℂ → ℂ) (z v : ℂ) : ℝ :=
  s22gt_chartConnection ψ z v - s22gt_phaseForm f z v

/-- The phase of the coefficient of a pulled-back canonical differential
has exactly the same inhomogeneous term as the coordinate connection. -/
theorem s22cd_phase_canonical_pullback {f η : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f (η z)) (hη : AnalyticAt ℂ η z)
    (hn : f (η z) ≠ 0) (hd : deriv η z ≠ 0) (v : ℂ) :
    s22gt_phaseForm (fun ζ => f (η ζ) * deriv η ζ) z v =
      s22gt_phaseForm f (η z) (deriv η z * v) +
        s22gt_phaseForm (deriv η) z v := by
  have h1 := s22gt_phaseForm_mul (h := f ∘ η) (k := deriv η) (z := z)
    (hf.comp hη).differentiableAt hη.deriv.differentiableAt hn hd v
  refine h1.trans ?_
  rw [s22gt_phaseForm_comp hf.differentiableAt hη.differentiableAt v]

/-- Cancellation of frame rotations: the canonical gauge transforms as an
ordinary real one-form, away from zeros and poles of the differential. -/
theorem s22cd_canonicalGauge_comp {ψ f η : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ (η z)) (hf : AnalyticAt ℂ f (η z))
    (hη : AnalyticAt ℂ η z) (hdψ : deriv ψ (η z) ≠ 0)
    (hdf : f (η z) ≠ 0) (hdη : deriv η z ≠ 0) (v : ℂ) :
    s22cd_canonicalGauge (ψ ∘ η) (fun ζ => f (η ζ) * deriv η ζ) z v =
      s22cd_canonicalGauge ψ f (η z) (deriv η z * v) := by
  rw [s22cd_canonicalGauge,
    s22gt_chartConnection_comp hψ hη hdψ hdη v,
    s22cd_phase_canonical_pullback hf hη hdf hdη v,
    s22cd_canonicalGauge]
  ring

theorem s22cd_canonicalGauge_germ_congr {ψ χ f g : ℂ → ℂ} {z : ℂ}
    (hψ : ψ =ᶠ[𝓝 z] χ) (hf : f =ᶠ[𝓝 z] g) (v : ℂ) :
    s22cd_canonicalGauge ψ f z v = s22cd_canonicalGauge χ g z v := by
  rw [s22cd_canonicalGauge, s22cd_canonicalGauge,
    s22gt_chartConnection_germ_congr hψ v, s22gt_phaseForm_germ_congr hf v]

/-- The local differential itself supplies the coefficient germ law.
No gluing property of the gauge is included in this hypothesis. -/
theorem s22cd_diffFamily_germ
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {q : S → ℂ → ℂ} (hq : IsDiffFamily 1 0 q) {x y : S} {z : ℂ}
    (hz : z ∈ (chartAt ℂ y).target)
    (hx : (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source) :
    q y =ᶠ[𝓝 z]
      (fun ζ => q x (chartTransition x y ζ) * deriv (chartTransition x y) ζ) := by
  have hpre : ∀ᶠ ζ in 𝓝 z,
      (chartAt ℂ y).symm ζ ∈ (chartAt ℂ x).source :=
    ((chartAt ℂ y).continuousAt_symm hz).preimage_mem_nhds
      ((chartAt ℂ x).open_source.mem_nhds hx)
  filter_upwards [(chartAt ℂ y).open_target.mem_nhds hz, hpre] with ζ hζ hζx
  simpa only [zpow_one, zpow_zero, mul_one] using hq.2 x y ζ hζ hζx

/-- The boundary period of the phase term is computed by the actual local
divisor, with poles counted negatively. -/
theorem s22cd_canonical_phase_period {f : ℂ → ℂ} {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im)
    (hf : MeromorphicOn f (wv_rectK z w))
    (hord : ∀ u ∈ wv_rectK z w, meromorphicOrderAt f u ≠ ⊤)
    (hbd : ∀ ζ ∈ wv_rectF z w, AnalyticAt ℂ f ζ ∧ f ζ ≠ 0) :
    s22cd_rectBoundary (s22gt_phaseForm f) z w =
      2 * π *
        ∑ p ∈ ((MeromorphicOn.divisor f (wv_rectK z w)).finiteSupport
          (wv_isCompact_rectK z w)).toFinset,
          (MeromorphicOn.divisor f (wv_rectK z w) p : ℝ) :=
  s22cd_phase_boundary_divisor hre him hf hord hbd

/-- Directional derivative of a phase form. This supplies differentiability
before taking derivatives of sums or differences of forms. -/
theorem s22cd_phase_line_derivative {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hn : f z ≠ 0) (d v : ℂ) :
    HasDerivAt (fun t : ℝ => s22gt_phaseForm f (z + (t : ℂ) * d) v)
      ((deriv (fun ζ => deriv f ζ / f ζ) z * d * v).im) 0 := by
  let F : ℂ → ℂ := fun ζ => deriv f ζ / f ζ
  have hF : AnalyticAt ℂ F z := hf.deriv.div hf hn
  have hline : HasDerivAt (fun t : ℝ => F (z + (t : ℂ) * d))
      (deriv F z * d) 0 := by
    have h := hF.differentiableAt.hasDerivAt.comp_of_eq (0 : ℝ)
      (td_hasDerivAt_line z d 0) (by simp)
    exact h
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hline.mul_const v)

/-- Directional derivative of the lifted upper-half-plane connection before
the frame correction. Both numerator and denominator are differentiated. -/
theorem s22cd_lifted_connection_line_derivative {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hy : (ψ z).im ≠ 0) (d v : ℂ) :
    HasDerivAt
      (fun t : ℝ => s22gc_connectionForm (ψ (z + (t : ℂ) * d))
        (deriv ψ (z + (t : ℂ) * d) * v))
      (((deriv (deriv ψ) z * d * v).re * (ψ z).im -
        (deriv ψ z * v).re * (deriv ψ z * d).im) / (ψ z).im ^ 2) 0 := by
  have hline : HasDerivAt (fun t : ℝ => ψ (z + (t : ℂ) * d))
      (deriv ψ z * d) 0 := by
    have h := hψ.differentiableAt.hasDerivAt.comp_of_eq (0 : ℝ)
      (td_hasDerivAt_line z d 0) (by simp)
    exact h
  have hdline : HasDerivAt (fun t : ℝ => deriv ψ (z + (t : ℂ) * d))
      (deriv (deriv ψ) z * d) 0 := by
    have h := hψ.deriv.differentiableAt.hasDerivAt.comp_of_eq (0 : ℝ)
      (td_hasDerivAt_line z d 0) (by simp)
    exact h
  have hn : HasDerivAt (fun t : ℝ => (deriv ψ (z + (t : ℂ) * d) * v).re)
      ((deriv (deriv ψ) z * d * v).re) 0 :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hdline.mul_const v)
  have hden : HasDerivAt (fun t : ℝ => (ψ (z + (t : ℂ) * d)).im)
      ((deriv ψ z * d).im) 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
  have hy0 : (ψ (z + ((0 : ℝ) : ℂ) * d)).im ≠ 0 := by simpa using hy
  have e := hn.div hden hy0
  refine e.congr_deriv ?_
  simp

/-- Exact `d = 1` and `d = I` versions of the lifted connection derivative. -/
theorem s22cd_lifted_connection_dx {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hy : (ψ z).im ≠ 0) :
    HasDerivAt
      (fun t : ℝ => s22gc_connectionForm (ψ (z + (t : ℂ)))
        (deriv ψ (z + (t : ℂ)) * I))
      (((deriv (deriv ψ) z * I).re * (ψ z).im -
        (deriv ψ z * I).re * (deriv ψ z).im) / (ψ z).im ^ 2) 0 := by
  simpa only [mul_one] using s22cd_lifted_connection_line_derivative hψ hy 1 I

theorem s22cd_lifted_connection_dy {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hy : (ψ z).im ≠ 0) :
    HasDerivAt
      (fun t : ℝ => s22gc_connectionForm (ψ (z + (t : ℂ) * I))
        (deriv ψ (z + (t : ℂ) * I) * 1))
      (((deriv (deriv ψ) z * I).re * (ψ z).im -
        (deriv ψ z).re * (deriv ψ z * I).im) / (ψ z).im ^ 2) 0 := by
  refine (s22cd_lifted_connection_line_derivative hψ hy I 1).congr_deriv ?_
  simp only [mul_one]

/-- Exact `d = 1` and `d = I` versions of the phase derivative. -/
theorem s22cd_phase_dx {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hn : f z ≠ 0) :
    HasDerivAt (fun t : ℝ => s22gt_phaseForm f (z + (t : ℂ)) I)
      ((deriv (fun ζ => deriv f ζ / f ζ) z * I).im) 0 := by
  simpa only [mul_one] using s22cd_phase_line_derivative hf hn 1 I

theorem s22cd_phase_dy {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hn : f z ≠ 0) :
    HasDerivAt (fun t : ℝ => s22gt_phaseForm f (z + (t : ℂ) * I) 1)
      ((deriv (fun ζ => deriv f ζ / f ζ) z * I).im) 0 := by
  simpa only [mul_one] using s22cd_phase_line_derivative hf hn I 1

/-- The exterior derivative of the lifted connection is the pulled-back
hyperbolic area form. This is an explicit local calculation. -/
theorem s22cd_exterior_lifted_connection {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hy : (ψ z).im ≠ 0) (v w : ℂ) :
    s22gc_exteriorDerivative
      (fun ζ u => s22gc_connectionForm (ψ ζ) (deriv ψ ζ * u)) z v w =
      s22gc_areaForm ψ z v w := by
  have hx := s22cd_lifted_connection_dx hψ hy
  have hyy := s22cd_lifted_connection_dy hψ hy
  simp only [s22gc_exteriorDerivative]
  rw [hx.deriv, hyy.deriv]
  rw [s22gc_areaForm, s22gc_areaDensity, s22gc_lengthDensity, div_pow]
  have hn : ‖deriv ψ z‖ ^ 2 = (deriv ψ z).re ^ 2 + (deriv ψ z).im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using
      (Complex.normSq_eq_norm_sq (deriv ψ z)).symm
  rw [hn]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add, sub_zero, zero_sub]
  ring

/-- Curvature identity in every analytic unramified lift coordinate.
The closed phase correction contributes zero. -/
theorem s22cd_exterior_chartConnection {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hd : deriv ψ z ≠ 0)
    (hy : (ψ z).im ≠ 0) (v w : ℂ) :
    s22gc_exteriorDerivative (s22gt_chartConnection ψ) z v w =
      s22gc_areaForm ψ z v w := by
  have hx := s22cd_lifted_connection_dx hψ hy
  have hyy := s22cd_lifted_connection_dy hψ hy
  have hpx := s22cd_phase_dx hψ.deriv hd
  have hpy := s22cd_phase_dy hψ.deriv hd
  have hdx : HasDerivAt (fun t : ℝ => s22gt_chartConnection ψ (z + (t : ℂ)) I)
      ((((deriv (deriv ψ) z * I).re * (ψ z).im -
        (deriv ψ z * I).re * (deriv ψ z).im) / (ψ z).im ^ 2) +
        (deriv (fun ζ => deriv (deriv ψ) ζ / deriv ψ ζ) z * I).im) 0 := hx.add hpx
  have hdy : HasDerivAt (fun t : ℝ => s22gt_chartConnection ψ (z + (t : ℂ) * I) 1)
      ((((deriv (deriv ψ) z * I).re * (ψ z).im -
        (deriv ψ z).re * (deriv ψ z * I).im) / (ψ z).im ^ 2) +
        (deriv (fun ζ => deriv (deriv ψ) ζ / deriv ψ ζ) z * I).im) 0 := hyy.add hpy
  have hl := s22cd_exterior_lifted_connection hψ hy v w
  simp only [s22gc_exteriorDerivative] at hl
  rw [hx.deriv, hyy.deriv] at hl
  have hpc := s22gt_phaseForm_closed hψ.deriv hd v w
  rw [s22gc_exteriorDerivative, hpx.deriv, hpy.deriv] at hpc
  rw [s22gc_exteriorDerivative, hdx.deriv, hdy.deriv]
  linarith

/-- Removing the canonical phase preserves curvature off its divisor.
Together with the overlap law this is the local form used in global Stokes. -/
theorem s22cd_exterior_canonicalGauge {ψ f : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hd : deriv ψ z ≠ 0)
    (hy : (ψ z).im ≠ 0) (hf : AnalyticAt ℂ f z) (hn : f z ≠ 0) (v w : ℂ) :
    s22gc_exteriorDerivative (s22cd_canonicalGauge ψ f) z v w =
      s22gc_areaForm ψ z v w := by
  have hx := s22cd_lifted_connection_dx hψ hy
  have hyy := s22cd_lifted_connection_dy hψ hy
  have hpx := s22cd_phase_dx hψ.deriv hd
  have hpy := s22cd_phase_dy hψ.deriv hd
  have hqx := s22cd_phase_dx hf hn
  have hqy := s22cd_phase_dy hf hn
  have hdx : HasDerivAt (fun t : ℝ => s22cd_canonicalGauge ψ f (z + (t : ℂ)) I)
      (((((deriv (deriv ψ) z * I).re * (ψ z).im -
        (deriv ψ z * I).re * (deriv ψ z).im) / (ψ z).im ^ 2) +
        (deriv (fun ζ => deriv (deriv ψ) ζ / deriv ψ ζ) z * I).im) -
        (deriv (fun ζ => deriv f ζ / f ζ) z * I).im) 0 := (hx.add hpx).sub hqx
  have hdy : HasDerivAt (fun t : ℝ => s22cd_canonicalGauge ψ f (z + (t : ℂ) * I) 1)
      (((((deriv (deriv ψ) z * I).re * (ψ z).im -
        (deriv ψ z).re * (deriv ψ z * I).im) / (ψ z).im ^ 2) +
        (deriv (fun ζ => deriv (deriv ψ) ζ / deriv ψ ζ) z * I).im) -
        (deriv (fun ζ => deriv f ζ / f ζ) z * I).im) 0 := (hyy.add hpy).sub hqy
  have hl := s22cd_exterior_lifted_connection hψ hy v w
  simp only [s22gc_exteriorDerivative] at hl
  rw [hx.deriv, hyy.deriv] at hl
  have hpc := s22gt_phaseForm_closed hψ.deriv hd v w
  rw [s22gc_exteriorDerivative, hpx.deriv, hpy.deriv] at hpc
  have hqc := s22gt_phaseForm_closed hf hn v w
  rw [s22gc_exteriorDerivative, hqx.deriv, hqy.deriv] at hqc
  rw [s22gc_exteriorDerivative, hdx.deriv, hdy.deriv]
  linarith

/-- The phase form is continuous at every regular nonzero coefficient. -/
theorem s22cd_phase_continuousAt {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hn : f z ≠ 0) (v : ℂ) :
    ContinuousAt (fun ζ => s22gt_phaseForm f ζ v) z := by
  have hc : ContinuousAt (fun ζ => deriv f ζ / f ζ) z :=
    hf.deriv.continuousAt.div hf.continuousAt hn
  exact Complex.continuous_im.continuousAt.comp (hc.mul continuousAt_const)

/-- Continuity of the coordinate connection on its actual regular domain. -/
theorem s22cd_chartConnection_continuousAt {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hd : deriv ψ z ≠ 0)
    (hy : (ψ z).im ≠ 0) (v : ℂ) :
    ContinuousAt (fun ζ => s22gt_chartConnection ψ ζ v) z := by
  have h1 : ContinuousAt (fun ζ => (deriv ψ ζ * v).re) z := by
    have := hψ.deriv.continuousAt
    fun_prop
  have h2 : ContinuousAt (fun ζ => (ψ ζ).im) z := by
    have := hψ.continuousAt
    fun_prop
  exact (h1.div h2 hy).add (s22cd_phase_continuousAt hψ.deriv hd v)

/-- Exact local boundary defect for the canonical gauge. This combines
ordinary interval integration with the meromorphic divisor calculation;
the smooth connection term has not been silently dropped. -/
theorem s22cd_canonicalGauge_boundary {ψ f : ℂ → ℂ} {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im)
    (hψ : ∀ ζ ∈ wv_rectF z w,
      AnalyticAt ℂ ψ ζ ∧ deriv ψ ζ ≠ 0 ∧ (ψ ζ).im ≠ 0)
    (hf : MeromorphicOn f (wv_rectK z w))
    (hord : ∀ u ∈ wv_rectK z w, meromorphicOrderAt f u ≠ ⊤)
    (hbd : ∀ ζ ∈ wv_rectF z w, AnalyticAt ℂ f ζ ∧ f ζ ≠ 0) :
    s22cd_rectBoundary (s22cd_canonicalGauge ψ f) z w =
      s22cd_rectBoundary (s22gt_chartConnection ψ) z w -
      2 * π *
        ∑ p ∈ ((MeromorphicOn.divisor f (wv_rectK z w)).finiteSupport
          (wv_isCompact_rectK z w)).toFinset,
          (MeromorphicOn.divisor f (wv_rectK z w) p : ℝ) := by
  have hc : ∀ v, ContinuousOn
      (fun ζ => s22gt_chartConnection ψ ζ v) (wv_rectF z w) := by
    intro v ζ hζ
    exact (s22cd_chartConnection_continuousAt
      (hψ ζ hζ).1 (hψ ζ hζ).2.1 (hψ ζ hζ).2.2 v).continuousWithinAt
  have hphase : ∀ v, ContinuousOn
      (fun ζ => s22gt_phaseForm f ζ v) (wv_rectF z w) := by
    intro v ζ hζ
    exact (s22cd_phase_continuousAt (hbd ζ hζ).1 (hbd ζ hζ).2 v).continuousWithinAt
  change s22cd_rectBoundary
    (fun ζ v => s22gt_chartConnection ψ ζ v - s22gt_phaseForm f ζ v) z w = _
  rw [s22cd_rectBoundary_sub hc hphase,
    s22cd_canonical_phase_period hre him hf hord hbd]

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]

/-- The canonical gauge is independent of covering lifts and obeys the
tensorial overlap law. The two germ hypotheses say that the local lifts
represent the same surface map and that the coefficients represent the same
differential; neither contains a connection or an integral. -/
theorem s22cd_surface_canonicalGauge_overlap [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {ψ χ η f g : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ (η z)) (hη : AnalyticAt ℂ η z)
    (hf : AnalyticAt ℂ f (η z))
    (hdψ : deriv ψ (η z) ≠ 0) (hdη : deriv η z ≠ 0) (hn : f (η z) ≠ 0)
    (hχ : ContinuousAt χ z)
    (hψH : ψ (η z) ∈ upperHalf) (hχH : χ z ∈ upperHalf)
    (he : (fun ζ => s22gm_projectionExtension p (ψ (η ζ))) =ᶠ[𝓝 z]
      (fun ζ => s22gm_projectionExtension p (χ ζ)))
    (hg : g =ᶠ[𝓝 z] (fun ζ => f (η ζ) * deriv η ζ)) (v : ℂ) :
    s22cd_canonicalGauge χ g z v =
      s22cd_canonicalGauge ψ f (η z) (deriv η z * v) := by
  rw [s22cd_canonicalGauge,
    s22gt_surface_connection_overlap hp hψ hη hdψ hdη hχ hψH hχH he v,
    s22gt_phaseForm_germ_congr hg v,
    s22cd_phase_canonical_pullback hf hη hn hdη v, s22cd_canonicalGauge]
  ring

end LiZhongQC
