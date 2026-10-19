import LiZhongQC.Lemmas.HyperbolicLocalCurvature

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

noncomputable section
namespace LiZhongQC

universe u

/-- The real phase one-form of a nonvanishing holomorphic transition function.
It uses its logarithmic derivative, so no global argument branch is chosen. -/
def s22gt_phaseForm (h : ℂ → ℂ) (z v : ℂ) : ℝ :=
  ((deriv h z / h z) * v).im

/-- The coordinate connection for the hyperbolic orthonormal frame. The first
term is the lifted upper-half-plane connection, and the second is its frame
rotation correction. -/
def s22gt_chartConnection (ψ : ℂ → ℂ) (z v : ℂ) : ℝ :=
  s22gc_connectionForm (ψ z) (deriv ψ z * v) +
    s22gt_phaseForm (deriv ψ) z v

theorem s22gt_phaseForm_add (h : ℂ → ℂ) (z v w : ℂ) :
    s22gt_phaseForm h z (v + w) =
      s22gt_phaseForm h z v + s22gt_phaseForm h z w := by
  simp only [s22gt_phaseForm, mul_add, Complex.add_im]

theorem s22gt_phaseForm_smul (h : ℂ → ℂ) (z v : ℂ) (a : ℝ) :
    s22gt_phaseForm h z (a • v) = a * s22gt_phaseForm h z v := by
  simp only [s22gt_phaseForm, mul_smul_comm, Complex.smul_im, smul_eq_mul]

/-- Multiplication of transition functions adds their connection corrections. -/
theorem s22gt_phaseForm_mul {h k : ℂ → ℂ} {z : ℂ}
    (hh : DifferentiableAt ℂ h z) (hk : DifferentiableAt ℂ k z)
    (hn : h z ≠ 0) (kn : k z ≠ 0) (v : ℂ) :
    s22gt_phaseForm (fun w => h w * k w) z v =
      s22gt_phaseForm h z v + s22gt_phaseForm k z v := by
  have he : (deriv h z * k z + h z * deriv k z) / (h z * k z) =
      deriv h z / h z + deriv k z / k z := by
    field_simp [hn, kn] <;> ring
  simp only [s22gt_phaseForm, deriv_fun_mul hh hk, he, add_mul, Complex.add_im]

/-- Pullback of a transition correction under a holomorphic coordinate map. -/
theorem s22gt_phaseForm_comp {h χ : ℂ → ℂ} {z : ℂ}
    (hh : DifferentiableAt ℂ h (χ z)) (hχ : DifferentiableAt ℂ χ z) (v : ℂ) :
    s22gt_phaseForm (h ∘ χ) z v =
      s22gt_phaseForm h (χ z) (deriv χ z * v) := by
  simp only [s22gt_phaseForm, deriv_comp z hh hχ, Function.comp_apply]
  congr 1
  ring

theorem s22gt_phaseForm_germ_congr {h k : ℂ → ℂ} {z : ℂ}
    (he : h =ᶠ[𝓝 z] k) (v : ℂ) :
    s22gt_phaseForm h z v = s22gt_phaseForm k z v := by
  rw [s22gt_phaseForm, s22gt_phaseForm, he.deriv_eq, he.self_of_nhds]

/-- A holomorphic transition correction is closed. This is a proved
Cauchy-Riemann calculation, not an assumption about curvature. -/
theorem s22gt_phaseForm_closed {h : ℂ → ℂ} {z : ℂ}
    (hh : AnalyticAt ℂ h z) (hn : h z ≠ 0) (v w : ℂ) :
    s22gc_exteriorDerivative (s22gt_phaseForm h) z v w = 0 := by
  let Q : ℂ → ℂ := fun ζ => deriv h ζ / h ζ
  have hQ : AnalyticAt ℂ Q z := hh.deriv.div hh hn
  have hx : HasDerivAt (fun t : ℝ => Q (z + (t : ℂ))) (deriv Q z) 0 := by
    convert! hQ.differentiableAt.hasDerivAt.comp_of_eq (0 : ℝ)
      (td_hasDerivAt_line z 1 0) (by simp) using 1 <;>
      simp only [Function.comp_def, mul_one]
  have hy : HasDerivAt (fun t : ℝ => Q (z + (t : ℂ) * I)) (deriv Q z * I) 0 := by
    convert! hQ.differentiableAt.hasDerivAt.comp_of_eq (0 : ℝ)
      (td_hasDerivAt_line z I 0) (by simp) using 1 <;>
      simp only [Function.comp_apply]
  have hxr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hx
  have hyi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hy
  change HasDerivAt (fun t : ℝ => (Q (z + (t : ℂ))).re) (deriv Q z).re 0 at hxr
  change HasDerivAt (fun t : ℝ => (Q (z + (t : ℂ) * I)).im)
    (deriv Q z * I).im 0 at hyi
  have hex : (fun t : ℝ => s22gt_phaseForm h (z + (t : ℂ)) I) =
      (fun t : ℝ => (Q (z + (t : ℂ))).re) := by
    funext t
    simp [s22gt_phaseForm, Q, Complex.mul_im]
  have hey : (fun t : ℝ => s22gt_phaseForm h (z + (t : ℂ) * I) 1) =
      (fun t : ℝ => (Q (z + (t : ℂ) * I)).im) := by
    funext t
    simp [s22gt_phaseForm, Q]
  rw [s22gc_exteriorDerivative, hex, hey, hxr.deriv, hyi.deriv]
  simp [Complex.mul_im]

/-- The phase correction has an analytic local potential. Rotating the value
into the positive real axis permits use of a single logarithm branch locally. -/
theorem s22gt_phaseForm_local_potential {h : ℂ → ℂ} {z : ℂ}
    (hh : AnalyticAt ℂ h z) (hn : h z ≠ 0) :
    ∃ L : ℂ → ℂ, AnalyticAt ℂ L z ∧
      ∀ v : ℂ, s22gt_phaseForm h z v = (deriv L z * v).im := by
  let a : ℂ := conj (h z) / (‖h z‖ : ℂ)
  have hnorm : 0 < ‖h z‖ := norm_pos_iff.2 hn
  have hnC : (‖h z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hnorm.ne'
  have haz : a * h z = (‖h z‖ : ℂ) := by
    dsimp [a]
    rw [div_mul_eq_mul_div, mul_comm (conj (h z)), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    field_simp [hnC] <;> ring
  have ha : a ≠ 0 := by
    intro he
    rw [he, zero_mul] at haz
    exact hnC haz.symm
  have hs : a * h z ∈ Complex.slitPlane := by
    rw [haz]
    exact Complex.ofReal_mem_slitPlane.2 hnorm
  let L : ℂ → ℂ := fun ζ => Complex.log (a * h ζ)
  have hL : AnalyticAt ℂ L z := (analyticAt_const.mul hh).clog hs
  have hd : deriv L z = deriv h z / h z := by
    have hdL := (Complex.hasDerivAt_log hs).comp z
      (hh.differentiableAt.hasDerivAt.const_mul a)
    have he : (a * h z)⁻¹ * (a * deriv h z) = deriv h z / h z := by
      field_simp [ha, hn]
    simpa only [L, Function.comp_def, he] using! hdL.deriv
  refine ⟨L, hL, ?_⟩
  intro v
  rw [hd]
  rfl

/-- The derivative chain rule on a neighbourhood, needed before differentiating
again. Pointwise equality alone would not justify the second derivative. -/
theorem s22gt_deriv_comp_germ {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ (χ z)) (hχ : AnalyticAt ℂ χ z) :
    deriv (ψ ∘ χ) =ᶠ[𝓝 z] (fun ζ => deriv ψ (χ ζ) * deriv χ ζ) := by
  have heψ := hχ.continuousAt.eventually hψ.eventually_analyticAt
  filter_upwards [hχ.eventually_analyticAt, heψ] with ζ hχζ hψζ
  exact deriv_comp ζ hψζ.differentiableAt hχζ.differentiableAt

theorem s22gt_second_deriv_comp {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ (χ z)) (hχ : AnalyticAt ℂ χ z) :
    deriv (deriv (ψ ∘ χ)) z =
      (deriv (deriv ψ) (χ z) * deriv χ z) * deriv χ z +
        deriv ψ (χ z) * deriv (deriv χ) z := by
  rw [(s22gt_deriv_comp_germ hψ hχ).deriv_eq]
  exact ((hψ.deriv.differentiableAt.hasDerivAt.comp z
    hχ.differentiableAt.hasDerivAt).mul hχ.deriv.differentiableAt.hasDerivAt).deriv

/-- The additive Čech cocycle law for changes of orthonormal coordinate frames.
On triple overlaps this is the phase of the derivative chain rule. -/
theorem s22gt_transition_cocycle {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ (χ z)) (hχ : AnalyticAt ℂ χ z)
    (hdψ : deriv ψ (χ z) ≠ 0) (hdχ : deriv χ z ≠ 0) (v : ℂ) :
    s22gt_phaseForm (deriv (ψ ∘ χ)) z v =
      s22gt_phaseForm (deriv ψ) (χ z) (deriv χ z * v) +
        s22gt_phaseForm (deriv χ) z v := by
  have he :
      ((deriv (deriv ψ) (χ z) * deriv χ z) * deriv χ z +
        deriv ψ (χ z) * deriv (deriv χ) z) /
          (deriv ψ (χ z) * deriv χ z) =
      deriv (deriv ψ) (χ z) / deriv ψ (χ z) * deriv χ z +
        deriv (deriv χ) z / deriv χ z := by
    field_simp [hdψ, hdχ]
    <;> ring
  simp only [s22gt_phaseForm]
  rw [s22gt_second_deriv_comp hψ hχ,
    deriv_comp z hψ.differentiableAt hχ.differentiableAt, he]
  simp only [add_mul, Complex.add_im, mul_assoc]

theorem s22gt_connectionForm_add (z v w : ℂ) :
    s22gc_connectionForm z (v + w) =
      s22gc_connectionForm z v + s22gc_connectionForm z w := by
  simp only [s22gc_connectionForm, Complex.add_re, add_div]

/-- The connection transformation law has the required inhomogeneous
logarithmic-derivative term. This is the local gluing law for a connection,
rather than the tensor transformation law for a global one-form. -/
theorem s22gt_chartConnection_comp {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ (χ z)) (hχ : AnalyticAt ℂ χ z)
    (hdψ : deriv ψ (χ z) ≠ 0) (hdχ : deriv χ z ≠ 0) (v : ℂ) :
    s22gt_chartConnection (ψ ∘ χ) z v =
      s22gt_chartConnection ψ (χ z) (deriv χ z * v) +
        s22gt_phaseForm (deriv χ) z v := by
  simp only [s22gt_chartConnection,
    deriv_comp z hψ.differentiableAt hχ.differentiableAt,
    Function.comp_apply, s22gt_transition_cocycle hψ hχ hdψ hdχ v, mul_assoc]
  ring

/-- Coordinate corrections on an unramified analytic overlap are closed. -/
theorem s22gt_transition_closed {χ : ℂ → ℂ} {z : ℂ}
    (hχ : AnalyticAt ℂ χ z) (hdχ : deriv χ z ≠ 0) (v w : ℂ) :
    s22gc_exteriorDerivative (s22gt_phaseForm (deriv χ)) z v w = 0 :=
  s22gt_phaseForm_closed hχ.deriv hdχ v w

/-! Deck changes preserve the corrected connection. This calculation is
specific to the hyperbolic geometry, not a formal imposed gluing condition. -/

theorem s22gt_mobius_second_deriv (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : z ∈ upperHalf) :
    deriv (deriv (h36p_m γ)) z =
      -(2 * (γ 1 0 : ℂ)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 3 := by
  have hden := k24_d_den_ne_zero (b33_d_det γ)
    (ne_of_gt (show 0 < z.im from hz))
  have hdet : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) -
      (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
    exact_mod_cast b33_d_det γ
  have he : deriv (h36p_m γ) =ᶠ[𝓝 z]
      (fun w => 1 / ((γ 1 0 : ℂ) * w + γ 1 1) ^ 2) := by
    filter_upwards [isOpen_upperHalf.mem_nhds hz] with w hw
    exact (h36p_m_hasDerivAt γ hw).deriv
  rw [he.deriv_eq]
  simpa only [hdet, mul_one] using
    (hasDerivAt_mobius_deriv (a := (γ 0 0 : ℂ)) (b := (γ 0 1 : ℂ)) hden).deriv

theorem s22gt_mobius_log_deriv (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : z ∈ upperHalf) :
    deriv (deriv (h36p_m γ)) z / deriv (h36p_m γ) z =
      -(2 * (γ 1 0 : ℂ)) / ((γ 1 0 : ℂ) * z + γ 1 1) := by
  have hden := k24_d_den_ne_zero (b33_d_det γ)
    (ne_of_gt (show 0 < z.im from hz))
  rw [s22gt_mobius_second_deriv γ hz, (h36p_m_hasDerivAt γ hz).deriv]
  field_simp [hden]
  <;> ring

/-- Algebraic identity controlling the inhomogeneous frame correction. -/
theorem s22gt_mobius_connection_identity (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : z ∈ upperHalf) :
    deriv (h36p_m γ) z * ((‖(γ 1 0 : ℂ) * z + γ 1 1‖ ^ 2 : ℝ) : ℂ) =
      1 + I * (z.im : ℂ) *
        (deriv (deriv (h36p_m γ)) z / deriv (h36p_m γ) z) := by
  let D : ℂ := (γ 1 0 : ℂ) * z + γ 1 1
  have hden : D ≠ 0 := k24_d_den_ne_zero (b33_d_det γ)
    (ne_of_gt (show 0 < z.im from hz))
  have hn : ((‖D‖ ^ 2 : ℝ) : ℂ) = D * conj D := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hc : conj D = D - 2 * I * (γ 1 0 : ℂ) * (z.im : ℂ) := by
    apply Complex.ext <;> simp [D, Complex.mul_re, Complex.mul_im] <;> ring
  rw [s22gt_mobius_log_deriv γ hz, (h36p_m_hasDerivAt γ hz).deriv]
  change (1 / D ^ 2) * ((‖D‖ ^ 2 : ℝ) : ℂ) =
    1 + I * (z.im : ℂ) * (-(2 * (γ 1 0 : ℂ)) / D)
  rw [hn, hc]
  field_simp [hden]
  <;> ring

/-- The frame correction exactly cancels the change of the lifted connection
under a deck transformation. The plus sign is fixed by this identity. -/
theorem s22gt_mobius_chartConnection (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : z ∈ upperHalf) (v : ℂ) :
    s22gt_chartConnection (h36p_m γ) z v = s22gc_connectionForm z v := by
  let a : ℂ := deriv (h36p_m γ) z
  let b : ℂ := deriv (deriv (h36p_m γ)) z / deriv (h36p_m γ) z
  let n : ℝ := ‖(γ 1 0 : ℂ) * z + γ 1 1‖
  have hy : z.im ≠ 0 := ne_of_gt (show 0 < z.im from hz)
  have hn : n ≠ 0 := norm_ne_zero_iff.2 (k24_d_den_ne_zero (b33_d_det γ) hy)
  have hc : a * ((n ^ 2 : ℝ) : ℂ) = 1 + I * (z.im : ℂ) * b :=
    s22gt_mobius_connection_identity γ hz
  have hr : n ^ 2 * (a * v).re = v.re - z.im * (b * v).im := by
    have he := congrArg (fun t : ℂ => (t * v).re) hc
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im] at he ⊢
    nlinarith [he]
  change (a * v).re / (h36p_m γ z).im + (b * v).im = v.re / z.im
  rw [s22gc_mobius_im]
  change (a * v).re / (z.im / n ^ 2) + (b * v).im = v.re / z.im
  field_simp [hy, hn]
  <;> simp only [Complex.mul_im] at hr ⊢
  <;> nlinarith [hr]

theorem s22gt_chartConnection_postcompose_mobius
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hd : deriv ψ z ≠ 0) (him : ψ z ∈ upperHalf)
    (v : ℂ) :
    s22gt_chartConnection (h36p_m γ ∘ ψ) z v = s22gt_chartConnection ψ z v := by
  rw [s22gt_chartConnection_comp (s22gc_mobius_analyticAt γ him) hψ
    (s22gc_mobius_deriv_ne_zero γ him) hd v]
  simpa only [s22gt_chartConnection] using congrArg
    (fun x : ℝ => x + s22gt_phaseForm (deriv ψ) z v)
    (s22gt_mobius_chartConnection γ him (deriv ψ z * v))

theorem s22gt_chartConnection_germ_congr {ψ χ : ℂ → ℂ} {z : ℂ}
    (he : ψ =ᶠ[𝓝 z] χ) (v : ℂ) :
    s22gt_chartConnection ψ z v = s22gt_chartConnection χ z v := by
  rw [s22gt_chartConnection, s22gt_chartConnection,
    s22gt_phaseForm_germ_congr he.deriv v, he.deriv_eq, he.self_of_nhds]

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]

/-- The coordinate connection depends only on the local surface
parametrization, not on its chosen lift to the upper half-plane. -/
theorem s22gt_lift_chartConnection_eq [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {ψ χ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z) (hd : deriv ψ z ≠ 0) (hχ : ContinuousAt χ z)
    (hψH : ψ z ∈ upperHalf) (hχH : χ z ∈ upperHalf)
    (he : (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z]
      (fun w => s22gm_projectionExtension p (χ w))) (v : ℂ) :
    s22gt_chartConnection χ z v = s22gt_chartConnection ψ z v := by
  obtain ⟨γ, _, hγ⟩ :=
    s22gc_lift_germ_deck hp hψ.continuousAt hχ hψH hχH he
  rw [s22gt_chartConnection_germ_congr hγ v,
    s22gt_chartConnection_postcompose_mobius γ hψ hd hψH v]

/-- Actual overlap law for the surface connection, combining coordinate
change with independently chosen covering lifts. -/
theorem s22gt_surface_connection_overlap [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {ψ χ η : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ (η z)) (hη : AnalyticAt ℂ η z)
    (hdψ : deriv ψ (η z) ≠ 0) (hdη : deriv η z ≠ 0)
    (hχ : ContinuousAt χ z)
    (hψH : ψ (η z) ∈ upperHalf) (hχH : χ z ∈ upperHalf)
    (he : (fun w => s22gm_projectionExtension p (ψ (η w))) =ᶠ[𝓝 z]
      (fun w => s22gm_projectionExtension p (χ w))) (v : ℂ) :
    s22gt_chartConnection χ z v =
      s22gt_chartConnection ψ (η z) (deriv η z * v) +
        s22gt_phaseForm (deriv η) z v := by
  rw [s22gt_lift_chartConnection_eq hp (hψ.comp hη)
    (s22gc_comp_deriv_ne_zero hψ.differentiableAt hη.differentiableAt hdψ hdη)
    hχ hψH hχH he v,
    s22gt_chartConnection_comp hψ hη hdψ hdη v]

end LiZhongQC

