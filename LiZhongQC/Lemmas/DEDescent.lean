import DouadyEarle.Extension
import LiZhongQC.Ch06.S23_QCOnSurfaces

/-!
# The Douady–Earle extension on `ℍ` (`s24q_`, for §24.2)

Bridge from the vendored `DouadyEarle` library (Douady–Earle, Theorem 1: `extension_isHomeomorphOn`,
`extension_analyticOn_disk`, `extension_jacobian_pos`, `extension_naturality`) to the upper half plane: the
Cayley transport of the extension of an orientation preserving circle homeomorphism is a `C¹` homeomorphism of
`ℍ` with `|μ| < 1` (`s24q_de_upper`), equivariant whenever its boundary map is (`s24q_de_equivariant`), with
`sup |μ| < 1` for a group uniformizing a compact surface (`s24q_sup_lt_one`), hence quasiconformal on `ℍ`
(`s24q_isKQC_of_bound`).  Used by `exists_qc_in_homotopy_class` (S24).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

/-- The Cayley map `C(z) = (z - i)/(z + i)` has derivative `2i/(z + i)²`. -/
theorem s24q_h_hasDerivAt_cayley {z : ℂ} (hz : z + I ≠ 0) : HasDerivAt cayley (2 * I / (z + I) ^ 2) z := by
  have h := ((hasDerivAt_id z).sub_const I).div ((hasDerivAt_id z).add_const I) hz
  have e : cayley = fun w => (id w - I) / (id w + I) := rfl
  rw [e]
  convert h using 1
  simp only [id]
  field_simp
  ring

/-- The inverse Cayley map `C⁻¹(w) = i(1 + w)/(1 - w)` has derivative `2i/(1 - w)²`. -/
theorem s24q_h_hasDerivAt_cayleyInv {w : ℂ} (hw : (1 : ℂ) - w ≠ 0) :
    HasDerivAt cayleyInv (2 * I / (1 - w) ^ 2) w := by
  have h := (((hasDerivAt_id w).const_add 1).const_mul I).div ((hasDerivAt_id w).const_sub 1) hw
  have e : cayleyInv = fun v => I * (1 + id v) / (1 - id v) := rfl
  rw [e]
  convert h using 1
  simp only [id]
  field_simp
  ring

/-- The Cayley map is `C¹` on `ℍ` (as a map of `ℝ²`). -/
theorem s24q_h_cayley_contDiffOn : ContDiffOn ℝ 1 cayley upperHalf := by
  have h : ContDiffOn ℂ 1 (fun z : ℂ => (z - I) / (z + I)) upperHalf :=
    (contDiffOn_id.sub contDiffOn_const).div (contDiffOn_id.add contDiffOn_const)
      fun z hz => cayley_den_ne_zero hz
  exact h.restrict_scalars ℝ

/-- The inverse Cayley map is `C¹` on the unit disc (as a map of `ℝ²`). -/
theorem s24q_h_cayleyInv_contDiffOn : ContDiffOn ℝ 1 cayleyInv (ball 0 1) := by
  have h : ContDiffOn ℂ 1 (fun w : ℂ => I * (1 + w) / (1 - w)) (ball 0 1) :=
    (contDiffOn_const.mul (contDiffOn_const.add contDiffOn_id)).div (contDiffOn_const.sub contDiffOn_id)
      fun w hw => cayleyInv_den_ne_zero (mem_ball_zero_iff.mp hw)
  exact h.restrict_scalars ℝ

/-- The Douady–Earle extension of an orientation preserving circle homeomorphism, transported to `ℍ` by the Cayley
map, is a `C¹` homeomorphism of `ℍ` with `|∂̄E| < |∂E|`. -/
theorem s24q_de_upper (φ : Circle → Circle) (hφ : Function.Bijective φ) (hφc : Continuous φ)
    (hor : HasIncreasingLift φ) :
    ∃ E : UpperHalfPlane ≃ₜ UpperHalfPlane, (∀ τ : UpperHalfPlane, cayley (E τ) = extension φ (cayley τ)) ∧
      ContDiffOn ℝ 1 (liftToC E) upperHalf ∧ ∀ z ∈ upperHalf, ‖dzbar (liftToC E) z‖ < ‖dz (liftToC E) z‖ := by
  obtain ⟨hbij, hcont, ext_inv, hinvc, hinv⟩ := extension_isHomeomorphOn φ hφ hφc
  have hΦd : ∀ w : ℂ, ‖w‖ < 1 → ‖extension φ w‖ < 1 := extension_mem_disk φ hφ hφc
  have hcb : ∀ τ : UpperHalfPlane, ‖cayley (τ : ℂ)‖ < 1 := fun τ =>
    mem_ball_zero_iff.mp (cayley_mem_unitDisc τ.coe_im_pos)
  -- the inverse of the extension maps the open disc into itself (the circle goes to the circle)
  have hid : ∀ w : ℂ, ‖w‖ < 1 → ‖ext_inv w‖ < 1 := by
    intro w hw
    have hwc : w ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hw.le
    obtain ⟨x, hx, rfl⟩ := hbij.surjOn hwc
    rw [hinv.1 hx]
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hx) with hlt | heq
    · exact hlt
    · exfalso
      have hm : x ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.2 heq
      have e : extension φ x = (φ ⟨x, hm⟩ : ℂ) := extension_eq_boundary φ ⟨x, hm⟩
      have h1 : ‖extension φ x‖ = 1 := by
        rw [e]
        exact Circle.norm_coe _
      linarith
  let toF : UpperHalfPlane → UpperHalfPlane := fun τ =>
    UpperHalfPlane.mk (cayleyInv (extension φ (cayley τ))) (cayleyInv_mem_upperHalf (hΦd _ (hcb τ)))
  let invF : UpperHalfPlane → UpperHalfPlane := fun τ =>
    UpperHalfPlane.mk (cayleyInv (ext_inv (cayley τ))) (cayleyInv_mem_upperHalf (hid _ (hcb τ)))
  have hleft : ∀ τ, invF (toF τ) = τ := by
    intro τ
    apply UpperHalfPlane.ext
    show cayleyInv (ext_inv (cayley (cayleyInv (extension φ (cayley τ))))) = τ
    rw [cayley_cayleyInv (hΦd _ (hcb τ)), hinv.1 (mem_closedBall_zero_iff.mpr (hcb τ).le),
      cayleyInv_cayley τ.coe_im_pos]
  have hright : ∀ τ, toF (invF τ) = τ := by
    intro τ
    apply UpperHalfPlane.ext
    show cayleyInv (extension φ (cayley (cayleyInv (ext_inv (cayley τ))))) = τ
    rw [cayley_cayleyInv (hid _ (hcb τ)), hinv.2 (mem_closedBall_zero_iff.mpr (hcb τ).le),
      cayleyInv_cayley τ.coe_im_pos]
  have hcC : ContinuousOn cayley upperHalf := s24q_h_cayley_contDiffOn.continuousOn
  have hcI : ContinuousOn cayleyInv (ball 0 1) := s24q_h_cayleyInv_contDiffOn.continuousOn
  have h1 : Continuous fun τ : UpperHalfPlane => cayley (τ : ℂ) :=
    hcC.comp_continuous UpperHalfPlane.continuous_coe fun τ => τ.coe_im_pos
  have hcont_toF : Continuous toF := by
    rw [UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff]
    show Continuous fun τ : UpperHalfPlane => cayleyInv (extension φ (cayley τ))
    have h2 : Continuous fun τ : UpperHalfPlane => extension φ (cayley τ) :=
      hcont.comp_continuous h1 fun τ => mem_closedBall_zero_iff.mpr (hcb τ).le
    exact hcI.comp_continuous h2 fun τ => mem_ball_zero_iff.mpr (hΦd _ (hcb τ))
  have hcont_invF : Continuous invF := by
    rw [UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff]
    show Continuous fun τ : UpperHalfPlane => cayleyInv (ext_inv (cayley τ))
    have h2 : Continuous fun τ : UpperHalfPlane => ext_inv (cayley τ) :=
      hinvc.comp_continuous h1 fun τ => mem_closedBall_zero_iff.mpr (hcb τ).le
    exact hcI.comp_continuous h2 fun τ => mem_ball_zero_iff.mpr (hid _ (hcb τ))
  let E : UpperHalfPlane ≃ₜ UpperHalfPlane :=
    { toFun := toF, invFun := invF, left_inv := hleft, right_inv := hright,
      continuous_toFun := hcont_toF, continuous_invFun := hcont_invF }
  -- on `ℍ`, `liftToC E` is `G = C⁻¹ ∘ extension φ ∘ C`
  set G : ℂ → ℂ := fun z => cayleyInv (extension φ (cayley z)) with hGdef
  have heq : ∀ z ∈ upperHalf, liftToC E z = G z := by
    intro z hz
    have hcoe : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = z := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    rw [h23l_liftToC_eq _ hz]
    show cayleyInv (extension φ (cayley ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ))) = G z
    rw [hcoe]
  have hΦan := extension_analyticOn_disk φ hφ hφc
  have hΦc1 : ContDiffOn ℝ 1 (extension φ) (ball 0 1) := hΦan.contDiffOn isOpen_ball.uniqueDiffOn
  have hmC : MapsTo cayley upperHalf (ball 0 1) := fun z hz => cayley_mem_unitDisc hz
  have hmΦ : MapsTo (extension φ) (ball 0 1) (ball 0 1) := fun w hw =>
    mem_ball_zero_iff.mpr (hΦd w (mem_ball_zero_iff.mp hw))
  have hGc1 : ContDiffOn ℝ 1 G upperHalf :=
    s24q_h_cayleyInv_contDiffOn.comp (hΦc1.comp s24q_h_cayley_contDiffOn hmC) (hmΦ.comp hmC)
  refine ⟨E, fun τ => ?_, hGc1.congr heq, fun z hz => ?_⟩
  · show cayley (cayleyInv (extension φ (cayley τ))) = extension φ (cayley τ)
    exact cayley_cayleyInv (hΦd _ (hcb τ))
  -- the dilatation: holomorphic pre- and post-composition multiply `∂` and `∂̄` by the same nonzero modulus
  have hloc : liftToC E =ᶠ[𝓝 z] G := Filter.eventually_of_mem (isOpen_upperHalf.mem_nhds hz) heq
  have hfd : fderiv ℝ (liftToC E) z = fderiv ℝ G z := hloc.fderiv_eq
  have hdz : dz (liftToC E) z = dz G z := by unfold dz; rw [hfd]
  have hdzbar : dzbar (liftToC E) z = dzbar G z := by unfold dzbar; rw [hfd]
  have hz' : 0 < z.im := hz
  have hw : ‖cayley z‖ < 1 := mem_ball_zero_iff.mp (cayley_mem_unitDisc hz)
  have hv : ‖extension φ (cayley z)‖ < 1 := hΦd _ hw
  have hdC := s24q_h_hasDerivAt_cayley (cayley_den_ne_zero hz')
  have hdI := s24q_h_hasDerivAt_cayleyInv (cayleyInv_den_ne_zero hv)
  have hcz : DifferentiableAt ℂ cayley z := hdC.differentiableAt
  have hΦw : DifferentiableAt ℝ (extension φ) (cayley z) :=
    (hΦc1.differentiableOn one_ne_zero _ (cayley_mem_unitDisc hz)).differentiableAt
      (isOpen_ball.mem_nhds (cayley_mem_unitDisc hz))
  have hcomp : DifferentiableAt ℝ (extension φ ∘ cayley) z := hΦw.comp z (hcz.restrictScalars ℝ)
  obtain ⟨e1, e2⟩ := eq6_5 (g := cayleyInv) hcomp hdI.differentiableAt
  obtain ⟨e3, e4⟩ := eq6_4 (g := extension φ) hcz hΦw
  have hG : G = cayleyInv ∘ (extension φ ∘ cayley) := rfl
  have hc1 : 0 < ‖deriv cayleyInv (extension φ (cayley z))‖ := by
    rw [hdI.deriv]
    exact norm_pos_iff.2 (div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (pow_ne_zero _ (cayleyInv_den_ne_zero hv)))
  have hc2 : 0 < ‖deriv cayley z‖ := by
    rw [hdC.deriv]
    exact norm_pos_iff.2 (div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (pow_ne_zero _ (cayley_den_ne_zero hz')))
  have hjac : ‖dzbar (extension φ) (cayley z)‖ < ‖dz (extension φ) (cayley z)‖ := by
    have hj := extension_jacobian_pos φ hφ hφc hor (cayley z) hw
    unfold dz dzbar
    rw [norm_div, norm_div]
    exact div_lt_div_of_pos_right hj (by norm_num)
  rw [hdz, hdzbar, hG, e1, e2, e3, e4, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_conj]
  exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hjac hc2) hc1

/-- The Cayley conjugate `z ↦ (αz + β)/(β̄z + ᾱ)` of `A ∈ SL(2, ℝ)` (`α = (a + d) + i(b - c)`, `β = (a - d) - i(b + c)`)
is an orientation preserving disc automorphism: it is `λ g_{-β/α}` with `λ = α/ᾱ`, since `|α|² - |β|² = 4`. -/
theorem s24q_h_DM_isDiskAutPlus (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    IsDiskAutPlus (fun z : ℂ => ((((A 0 0 + A 1 1 : ℝ) : ℂ) + ((A 0 1 - A 1 0 : ℝ) : ℂ) * I) * z +
          (((A 0 0 - A 1 1 : ℝ) : ℂ) - ((A 0 1 + A 1 0 : ℝ) : ℂ) * I)) /
        ((((A 0 0 - A 1 1 : ℝ) : ℂ) + ((A 0 1 + A 1 0 : ℝ) : ℂ) * I) * z +
          (((A 0 0 + A 1 1 : ℝ) : ℂ) - ((A 0 1 - A 1 0 : ℝ) : ℂ) * I))) := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have h := A.det_coe
    rw [Matrix.det_fin_two] at h
    exact h
  set α : ℂ := ((A 0 0 + A 1 1 : ℝ) : ℂ) + ((A 0 1 - A 1 0 : ℝ) : ℂ) * I with hα
  set β : ℂ := ((A 0 0 - A 1 1 : ℝ) : ℂ) - ((A 0 1 + A 1 0 : ℝ) : ℂ) * I with hβ
  have hαc : conj α = ((A 0 0 + A 1 1 : ℝ) : ℂ) - ((A 0 1 - A 1 0 : ℝ) : ℂ) * I := by
    rw [hα, map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
    ring
  have hβc : conj β = ((A 0 0 - A 1 1 : ℝ) : ℂ) + ((A 0 1 + A 1 0 : ℝ) : ℂ) * I := by
    rw [hβ, map_sub, map_mul, conj_ofReal, conj_ofReal, conj_I]
    ring
  rw [← hαc, ← hβc]
  have hnorm : normSq α = normSq β + 4 := by
    rw [hα, hβ, normSq_apply, normSq_apply]
    simp only [add_re, sub_re, add_im, sub_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im]
    nlinarith [hdet]
  have hα0 : α ≠ 0 := by
    intro h
    rw [h, map_zero] at hnorm
    nlinarith [normSq_nonneg β]
  have hαc0 : conj α ≠ 0 := (map_ne_zero _).2 hα0
  have hlt : ‖β‖ < ‖α‖ := by
    have h1 : ‖β‖ ^ 2 < ‖α‖ ^ 2 := by
      rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, hnorm]
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
  refine ⟨α / conj α, -β / α, ?_, ?_, fun z => ?_⟩
  · rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hα0)]
  · rw [norm_div, norm_neg, div_lt_one (norm_pos_iff.2 hα0)]
    exact hlt
  · simp only [diskAut]
    have e1 : z - -β / α = (α * z + β) / α := by field_simp; ring
    have e2 : (1 : ℂ) - star (-β / α) * z = (conj β * z + conj α) / conj α := by
      rw [star_div₀, star_neg]
      simp only [Complex.star_def]
      field_simp
      ring
    rw [e1, e2, div_div_div_eq, div_mul_div_comm,
      show α * ((α * z + β) * conj α) = (α * z + β) * (α * conj α) by ring,
      show conj α * (α * (conj β * z + conj α)) = (conj β * z + conj α) * (α * conj α) by ring,
      mul_div_mul_right _ _ (mul_ne_zero hα0 hαc0)]

/-- The Cayley map intertwines the action of `A ∈ SL(2, ℝ)` on `ℍ` with its Cayley conjugate on the disc. -/
theorem s24q_h_cayley_smul (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    cayley ((A • τ : UpperHalfPlane) : ℂ) =
      ((((A 0 0 + A 1 1 : ℝ) : ℂ) + ((A 0 1 - A 1 0 : ℝ) : ℂ) * I) * cayley τ +
          (((A 0 0 - A 1 1 : ℝ) : ℂ) - ((A 0 1 + A 1 0 : ℝ) : ℂ) * I)) /
        ((((A 0 0 - A 1 1 : ℝ) : ℂ) + ((A 0 1 + A 1 0 : ℝ) : ℂ) * I) * cayley τ +
          (((A 0 0 + A 1 1 : ℝ) : ℂ) - ((A 0 1 - A 1 0 : ℝ) : ℂ) * I)) := by
  have hτ : (τ : ℂ) ∈ upperHalf := τ.coe_im_pos
  have hden := h23l_b_den_ne A hτ
  have hτI : (τ : ℂ) + I ≠ 0 := cayley_den_ne_zero τ.coe_im_pos
  rw [h23l_b_coe_smul]
  have eN : ((((A 0 0 + A 1 1 : ℝ) : ℂ) + ((A 0 1 - A 1 0 : ℝ) : ℂ) * I) * cayley τ +
      (((A 0 0 - A 1 1 : ℝ) : ℂ) - ((A 0 1 + A 1 0 : ℝ) : ℂ) * I)) =
      2 * (((A 0 0 : ℂ) * τ + A 0 1) - I * ((A 1 0 : ℂ) * τ + A 1 1)) / ((τ : ℂ) + I) := by
    unfold cayley
    push_cast
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  have eD : ((((A 0 0 - A 1 1 : ℝ) : ℂ) + ((A 0 1 + A 1 0 : ℝ) : ℂ) * I) * cayley τ +
      (((A 0 0 + A 1 1 : ℝ) : ℂ) - ((A 0 1 - A 1 0 : ℝ) : ℂ) * I)) =
      2 * (((A 0 0 : ℂ) * τ + A 0 1) + I * ((A 1 0 : ℂ) * τ + A 1 1)) / ((τ : ℂ) + I) := by
    unfold cayley
    push_cast
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  rw [eN, eD, div_div_div_cancel_right₀ hτI, mul_div_mul_left _ _ two_ne_zero]
  have eL : ((A 0 0 : ℂ) * τ + A 0 1) / ((A 1 0 : ℂ) * τ + A 1 1) - I =
      (((A 0 0 : ℂ) * τ + A 0 1) - I * ((A 1 0 : ℂ) * τ + A 1 1)) / ((A 1 0 : ℂ) * τ + A 1 1) := by
    rw [eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden]
  have eL' : ((A 0 0 : ℂ) * τ + A 0 1) / ((A 1 0 : ℂ) * τ + A 1 1) + I =
      (((A 0 0 : ℂ) * τ + A 0 1) + I * ((A 1 0 : ℂ) * τ + A 1 1)) / ((A 1 0 : ℂ) * τ + A 1 1) := by
    rw [eq_div_iff hden, add_mul, div_mul_cancel₀ _ hden]
  unfold cayley
  rw [eL, eL', div_div_div_cancel_right₀ hden]

/-- Conformal naturality on `ℍ`: if the boundary map commutes with the Cayley conjugates of `γ` and `δ` (the disc
automorphism of `A = (a b; c d)` is `z ↦ (αz + β)/(β̄z + ᾱ)`, `α = (a + d) + i(b - c)`, `β = (a - d) - i(b + c)`),
the transported extension satisfies `E ∘ γ = δ ∘ E`. -/
theorem s24q_de_equivariant {φ : Circle → Circle} (hφ : Function.Bijective φ) (hφc : Continuous φ)
    {E : UpperHalfPlane ≃ₜ UpperHalfPlane} (hE : ∀ τ : UpperHalfPlane, cayley (E τ) = extension φ (cayley τ))
    {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hbd : ∀ ζ ζ' : Circle,
      (ζ' : ℂ) = ((((γ 0 0 + γ 1 1 : ℝ) : ℂ) + ((γ 0 1 - γ 1 0 : ℝ) : ℂ) * I) * ζ +
          (((γ 0 0 - γ 1 1 : ℝ) : ℂ) - ((γ 0 1 + γ 1 0 : ℝ) : ℂ) * I)) /
        ((((γ 0 0 - γ 1 1 : ℝ) : ℂ) + ((γ 0 1 + γ 1 0 : ℝ) : ℂ) * I) * ζ +
          (((γ 0 0 + γ 1 1 : ℝ) : ℂ) - ((γ 0 1 - γ 1 0 : ℝ) : ℂ) * I)) →
      (φ ζ' : ℂ) = ((((δ 0 0 + δ 1 1 : ℝ) : ℂ) + ((δ 0 1 - δ 1 0 : ℝ) : ℂ) * I) * (φ ζ) +
          (((δ 0 0 - δ 1 1 : ℝ) : ℂ) - ((δ 0 1 + δ 1 0 : ℝ) : ℂ) * I)) /
        ((((δ 0 0 - δ 1 1 : ℝ) : ℂ) + ((δ 0 1 + δ 1 0 : ℝ) : ℂ) * I) * (φ ζ) +
          (((δ 0 0 + δ 1 1 : ℝ) : ℂ) - ((δ 0 1 - δ 1 0 : ℝ) : ℂ) * I))) :
    ∀ τ, E (γ • τ) = δ • E τ := by
  intro τ
  have hgδ := s24q_h_DM_isDiskAutPlus δ
  have hgγ := s24q_h_DM_isDiskAutPlus γ
  obtain ⟨h', hh'p, hleft, hright⟩ := isDiskAutPlus_inv _ hgγ
  -- the boundary map is invariant under conjugation by the Cayley conjugates of `γ` and `δ`
  have hφeq : diskAutToCircle _ (Or.inl hgδ) ∘ φ ∘ diskAutToCircle h' (Or.inl hh'p) = φ := by
    funext ζ
    apply Subtype.ext
    have hζ : (ζ : ℂ) = ((((γ 0 0 + γ 1 1 : ℝ) : ℂ) + ((γ 0 1 - γ 1 0 : ℝ) : ℂ) * I) *
          (diskAutToCircle h' (Or.inl hh'p) ζ : ℂ) + (((γ 0 0 - γ 1 1 : ℝ) : ℂ) - ((γ 0 1 + γ 1 0 : ℝ) : ℂ) * I)) /
        ((((γ 0 0 - γ 1 1 : ℝ) : ℂ) + ((γ 0 1 + γ 1 0 : ℝ) : ℂ) * I) *
          (diskAutToCircle h' (Or.inl hh'p) ζ : ℂ) + (((γ 0 0 + γ 1 1 : ℝ) : ℂ) - ((γ 0 1 - γ 1 0 : ℝ) : ℂ) * I)) :=
      (hright (ζ : ℂ) (Circle.norm_coe ζ).le).symm
    exact (hbd _ ζ hζ).symm
  have hτ1 : ‖cayley (τ : ℂ)‖ ≤ 1 := (mem_ball_zero_iff.mp (cayley_mem_unitDisc τ.coe_im_pos)).le
  have hz1 : ‖cayley ((γ • τ : UpperHalfPlane) : ℂ)‖ ≤ 1 :=
    (mem_ball_zero_iff.mp (cayley_mem_unitDisc (γ • τ).coe_im_pos)).le
  have hnat := extension_naturality φ _ h' (diskAutToCircle _ (Or.inl hgδ))
    (diskAutToCircle h' (Or.inl hh'p)) (Or.inl hgδ) (Or.inl hh'p) (fun ζ => rfl) (fun ζ => rfl) hφ hφc
    (bijective_diskAutToCircle_of_isDiskAut _ _) (bijective_diskAutToCircle_of_isDiskAut _ _)
    (cayley ((γ • τ : UpperHalfPlane) : ℂ)) hz1
  rw [hφeq, s24q_h_cayley_smul γ τ, hleft _ hτ1, ← s24q_h_cayley_smul γ τ, ← hE τ,
    ← s24q_h_cayley_smul δ (E τ), ← hE (γ • τ)] at hnat
  apply UpperHalfPlane.ext
  have := congrArg cayleyInv hnat
  rwa [cayleyInv_cayley (E (γ • τ)).coe_im_pos, cayleyInv_cayley (δ • E τ).coe_im_pos] at this

/-- A `C¹` self-map of `ℍ` with `|μ| < 1`, equivariant for a uniformizing group of a compact surface, has
`sup_ℍ |μ| < 1` (`|μ|` is continuous and `Γ₀`-invariant, and a compact set of `ℍ` covers the surface). -/
theorem s24q_sup_lt_one {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [CompactSpace X]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → X}
    (hp₀ : IsUniformization Γ₀ p₀) {E : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hC1 : ContDiffOn ℝ 1 (liftToC E) upperHalf)
    (hlt : ∀ z ∈ upperHalf, ‖dzbar (liftToC E) z‖ < ‖dz (liftToC E) z‖)
    (heq : ∀ γ ∈ Γ₀, ∃ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ τ, E (γ • τ) = δ • E τ) :
    ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ ∀ z ∈ upperHalf, ‖complexDilatation (liftToC E) z‖ ≤ k := by
  -- a compact `K ⊆ ℍ` with `p₀ K = X`
  have hsurj := hp₀.2.2.1
  choose σ hσ using hsurj
  have hC : ∀ τ : UpperHalfPlane, ∃ C : Set UpperHalfPlane, IsCompact C ∧ C ∈ 𝓝 τ := fun τ =>
    exists_compact_mem_nhds τ
  choose C hCc hCn using hC
  obtain ⟨t, -, ht⟩ := (isCompact_univ (X := X)).elim_nhds_subcover (fun x => p₀ '' C (σ x)) fun x _ => by
    have h := hp₀.1.isOpenMap.image_mem_nhds (hCn (σ x))
    rwa [hσ x] at h
  set K : Set UpperHalfPlane := ⋃ x ∈ t, C (σ x) with hKdef
  have hK : IsCompact K := t.isCompact_biUnion fun x _ => hCc (σ x)
  have hcover : ∀ τ : UpperHalfPlane, ∃ κ ∈ K, p₀ κ = p₀ τ := by
    intro τ
    obtain ⟨x, hx, hmem⟩ := mem_iUnion₂.1 (ht (mem_univ (p₀ τ)))
    obtain ⟨κ, hκ, hκτ⟩ := hmem
    exact ⟨κ, mem_iUnion₂.2 ⟨x, hx, hκ⟩, hκτ⟩
  -- `|μ|` is continuous on `ℍ`
  have hfd : ContinuousOn (fderiv ℝ (liftToC E)) upperHalf :=
    hC1.continuousOn_fderiv_of_isOpen isOpen_upperHalf le_rfl
  have hdzc : ContinuousOn (dz (liftToC E)) upperHalf := by
    unfold dz
    exact (((hfd.clm_apply continuousOn_const).sub
      (continuousOn_const.mul (hfd.clm_apply continuousOn_const))).div_const _)
  have hdzbarc : ContinuousOn (dzbar (liftToC E)) upperHalf := by
    unfold dzbar
    exact (((hfd.clm_apply continuousOn_const).add
      (continuousOn_const.mul (hfd.clm_apply continuousOn_const))).div_const _)
  have hdz0 : ∀ z ∈ upperHalf, dz (liftToC E) z ≠ 0 := fun z hz h => by
    have := hlt z hz
    rw [h, norm_zero] at this
    exact absurd this (not_lt.2 (norm_nonneg _))
  have hμc : ContinuousOn (fun z => ‖complexDilatation (liftToC E) z‖) upperHalf := by
    unfold complexDilatation
    exact (hdzbarc.div hdzc hdz0).norm
  have hμlt : ∀ z ∈ upperHalf, ‖complexDilatation (liftToC E) z‖ < 1 := by
    intro z hz
    unfold complexDilatation
    rw [norm_div, div_lt_one (norm_pos_iff.2 (hdz0 z hz))]
    exact hlt z hz
  set m : UpperHalfPlane → ℝ := fun τ => ‖complexDilatation (liftToC E) τ‖ with hmdef
  have hmc : Continuous m :=
    hμc.comp_continuous UpperHalfPlane.continuous_coe fun τ => τ.coe_im_pos
  -- `|μ|` is `Γ₀`-invariant
  have hinv : ∀ γ ∈ Γ₀, ∀ κ : UpperHalfPlane, m (γ • κ) = m κ := by
    intro γ hγ κ
    obtain ⟨δ, hδ⟩ := heq γ hγ
    have h := h23l_dilatation_conj hδ κ.coe_im_pos
    have hden := h23l_b_den_ne γ κ.coe_im_pos
    have hfac : ‖(((γ 1 0 : ℂ) * κ + γ 1 1) ^ 2 / conj (((γ 1 0 : ℂ) * κ + γ 1 1) ^ 2))‖ = 1 := by
      rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 (pow_ne_zero _ hden))]
    simp only [hmdef]
    rw [h, norm_mul, hfac, mul_one, h23l_b_coe_smul]
  have hne : K.Nonempty := by
    obtain ⟨κ, hκ, -⟩ := hcover (Classical.arbitrary UpperHalfPlane)
    exact ⟨κ, hκ⟩
  obtain ⟨κ₀, hκ₀, hmax⟩ := hK.exists_isMaxOn hne hmc.continuousOn
  refine ⟨m κ₀, norm_nonneg _, hμlt _ κ₀.coe_im_pos, fun z hz => ?_⟩
  set τ : UpperHalfPlane := UpperHalfPlane.mk z hz with hτdef
  obtain ⟨κ, hκ, hκτ⟩ := hcover τ
  obtain ⟨γ, hγ, hγκ⟩ := (hp₀.2.2.2 κ τ).1 hκτ
  have hmτ : m τ = m κ := by rw [← hγκ, hinv γ hγ κ]
  have : ‖complexDilatation (liftToC E) z‖ = m τ := rfl
  rw [this, hmτ]
  exact hmax hκ

/-- A `C¹` homeomorphism of `ℍ` with `|μ| ≤ k < 1` is `(1 + k)/(1 - k)`-quasiconformal on `ℍ`
(`isKQC_of_isC1Quasiconformal`). -/
theorem s24q_isKQC_of_bound {E : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hC1 : ContDiffOn ℝ 1 (liftToC E) upperHalf)
    (hlt : ∀ z ∈ upperHalf, ‖dzbar (liftToC E) z‖ < ‖dz (liftToC E) z‖) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ z ∈ upperHalf, ‖complexDilatation (liftToC E) z‖ ≤ k) :
    IsKQC (liftToC E) upperHalf ((1 + k) / (1 - k)) := by
  have hk1' : 0 < 1 - k := by linarith
  have hinv : ∀ w ∈ upperHalf, Function.invFunOn (liftToC E) upperHalf w = liftToC E.symm w := by
    intro w hw
    have hw' : 0 < w.im := hw
    have hmem : liftToC E.symm w ∈ upperHalf := by
      rw [h23l_liftToC_eq _ hw]
      exact (E.symm _).coe_im_pos
    have hval : liftToC E (liftToC E.symm w) = w := by
      rw [h23l_liftToC_eq _ hw, h23l_liftToC_coe, Homeomorph.apply_symm_apply,
        UpperHalfPlane.ofComplex_apply_of_im_pos hw']
    have hex : ∃ a ∈ upperHalf, liftToC E a = w := ⟨_, hmem, hval⟩
    exact (h23l_liftToC_injOn E) (Function.invFunOn_mem hex) hmem
      ((Function.invFunOn_eq hex).trans hval.symm)
  have himg : liftToC E '' upperHalf = upperHalf := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [h23l_liftToC_eq _ hz]
      exact (E _).coe_im_pos
    · intro hw
      refine ⟨liftToC E.symm w, ?_, ?_⟩
      · rw [h23l_liftToC_eq _ hw]
        exact (E.symm _).coe_im_pos
      · rw [h23l_liftToC_eq _ hw, h23l_liftToC_coe, Homeomorph.apply_symm_apply,
          UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < w.im from hw)]
  refine isKQC_of_isC1Quasiconformal ⟨isOpen_upperHalf, ?_, hC1,
    ⟨h23l_liftToC_continuousOn E.continuous, h23l_liftToC_injOn E, rfl, ?_⟩, fun z hz => ⟨hlt z hz, ?_⟩⟩
  · rw [le_div_iff₀ hk1']
    linarith
  · rw [himg]
    exact ((h23l_liftToC_continuousOn E.symm.continuous).congr hinv)
  · have hm := hb z hz
    have hm0 := norm_nonneg (complexDilatation (liftToC E) z)
    unfold dilatationQuotient
    rw [div_le_div_iff₀ (by linarith) hk1']
    nlinarith

end LiZhongQC
