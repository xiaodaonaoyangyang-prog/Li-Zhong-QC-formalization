import LiZhongQC.ClusterSets

/-!
# Rigidity of conformal maps between rectangles

The uniqueness half of **Theorem 1.1**: a conformal map of the rectangle `R(0, a, a+bi, bi)` onto
`R(0, a', a'+b'i, b'i)` which extends to a homeomorphism of the closures sending vertices to the
corresponding vertices is the similarity `z ↦ (a'/a) z`, and `a'/a = b'/b`.

This file is upstream of `Ch01/S01_Quadrilateral.lean`, which is to import it for
`thm1_1_rectangle_unique`; it therefore speaks only of `rectangle a b` (from `Basic.lean`) and of
plain subsets of `ℂ`.  (`Lemmas/Quadrilateral.lean` imports S01 and cannot be used here.)

## Route

The book, and the write-up `proof in LZ.txt` §7.2, extend the map by repeated reflection to an
injective entire function and conclude with "an injective entire function is affine", which rests
on the Casorati–Weierstrass theorem; Mathlib does not have it.  We use instead that the reflected
extension `G` of `g` satisfies `G (z + 2a) = G z + 2a'` and `G (z + 2bi) = G z + 2b'i`, so `G'` is
a doubly periodic entire function, hence bounded, hence constant by Liouville's theorem.

The statement is split in two independent halves:
* `rect_rigidity_of_sideLines` (analysis): holomorphic inside, continuous on the closure, and each
  closed side mapped into the line of the corresponding side, already forces `g z = (a'/a) z`.  No
  injectivity or vertex hypothesis is needed: the vertex values follow from the side lines.
* `rect_sideLines_of_homeo` (topology): a map of the closed rectangles that is injective and onto,
  maps the open rectangle onto the open rectangle and sends the four vertices to the four vertices
  sends each closed side into the line of the corresponding side.
-/

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace LiZhongQC

/-! ### Generic tools: folding induction, a product continuity criterion, Morera across a line,
Liouville for quasi-periodic functions -/

/-- **Folding induction.**  A property of real numbers that holds on `[0, a]` and is preserved by
`x ↦ -x` and `x ↦ x + 2a` holds everywhere. -/
theorem forall_of_fold_Icc {a : ℝ} (ha : 0 < a) {P : ℝ → Prop} (h0 : ∀ x ∈ Icc (0 : ℝ) a, P x)
    (hneg : ∀ x, P x → P (-x)) (hadd : ∀ x, P x → P (x + 2 * a)) : ∀ x, P x := by
  have hsub : ∀ x, P x → P (x - 2 * a) := fun x hx => by
    have h := hneg _ (hadd _ (hneg x hx))
    rwa [show -(-x + 2 * a) = x - 2 * a by ring] at h
  have hint : ∀ n : ℤ, ∀ x, P x → P (x + n * (2 * a)) := by
    intro n
    refine Int.induction_on n ?_ ?_ ?_
    · intro x hx
      simpa using hx
    · intro i ih x hx
      convert hadd _ (ih x hx) using 1
      push_cast
      ring
    · intro i ih x hx
      convert hsub _ (ih x hx) using 1
      push_cast
      ring
  intro x
  have h2a : 0 < 2 * a := by positivity
  have hn1 : (⌊x / (2 * a)⌋ : ℝ) * (2 * a) ≤ x := by
    have := Int.floor_le (x / (2 * a))
    rwa [le_div_iff₀ h2a] at this
  have hn2 : x < (⌊x / (2 * a)⌋ : ℝ) * (2 * a) + 2 * a := by
    have := Int.lt_floor_add_one (x / (2 * a))
    rw [div_lt_iff₀ h2a] at this
    linarith
  by_cases hle : x - (⌊x / (2 * a)⌋ : ℝ) * (2 * a) ≤ a
  · have h := hint ⌊x / (2 * a)⌋ _ (h0 (x - (⌊x / (2 * a)⌋ : ℝ) * (2 * a)) ⟨by linarith, hle⟩)
    rwa [sub_add_cancel] at h
  · have h1 : P (2 * a - (x - (⌊x / (2 * a)⌋ : ℝ) * (2 * a))) := h0 _ ⟨by linarith, by linarith⟩
    have h2 := hint (⌊x / (2 * a)⌋ + 1) _ (hneg _ h1)
    convert h2 using 1
    push_cast
    ring

/-- `Real.sign` is continuous away from `0`. -/
theorem continuousAt_realSign_of_ne_zero {t : ℝ} (ht : t ≠ 0) : ContinuousAt Real.sign t := by
  rcases lt_or_gt_of_ne ht with h | h
  · have hev : (fun _ => (-1 : ℝ)) =ᶠ[𝓝 t] Real.sign := by
      filter_upwards [eventually_lt_nhds h] with y hy
      exact (Real.sign_of_neg hy).symm
    show Tendsto Real.sign (𝓝 t) (𝓝 (Real.sign t))
    rw [Real.sign_of_neg h]
    exact tendsto_const_nhds.congr' hev
  · have hev : (fun _ => (1 : ℝ)) =ᶠ[𝓝 t] Real.sign := by
      filter_upwards [eventually_gt_nhds h] with y hy
      exact (Real.sign_of_pos hy).symm
    show Tendsto Real.sign (𝓝 t) (𝓝 (Real.sign t))
    rw [Real.sign_of_pos h]
    exact tendsto_const_nhds.congr' hev

/-- A product `s · r` is continuous if `|s| ≤ 1`, `r` is continuous, and at every point either `s`
is continuous or `r` vanishes. -/
theorem continuous_mul_of_abs_le_one {X : Type*} [TopologicalSpace X] {s r : X → ℝ}
    (hr : Continuous r) (hs : ∀ x, |s x| ≤ 1) (h : ∀ x, ContinuousAt s x ∨ r x = 0) :
    Continuous fun x => s x * r x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases h x with hsx | hrx
  · exact hsx.mul hr.continuousAt
  · show Tendsto (fun y => s y * r y) (𝓝 x) (𝓝 (s x * r x))
    rw [hrx, mul_zero]
    refine squeeze_zero_norm (a := fun y => ‖r y‖) (fun y => ?_) ?_
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact hs y)
    · have := (hr.tendsto x).norm
      rwa [hrx, norm_zero] at this

/-- **Morera across a line.**  A function continuous on an open set `U` and complex differentiable
at every point of `U` off the line `p + ℝ q` is holomorphic on `U`. -/
theorem differentiableOn_of_continuousOn_of_differentiableAt_off_line {U : Set ℂ}
    (hU : IsOpen U) {F : ℂ → ℂ} (hc : ContinuousOn F U) (p q : ℂ) (hq : q ≠ 0)
    (hd : ∀ z ∈ U, ((z - p) / q).im ≠ 0 → DifferentiableAt ℂ F z) :
    DifferentiableOn ℂ F U := by
  have hAc : Continuous fun ζ : ℂ => p + q * ζ := by fun_prop
  have hVo : IsOpen ((fun ζ : ℂ => p + q * ζ) ⁻¹' U) := hU.preimage hAc
  have hinv1 : ∀ ζ : ℂ, (p + q * ζ - p) / q = ζ := fun ζ => by
    rw [add_sub_cancel_left, mul_div_cancel_left₀ ζ hq]
  have hinv2 : ∀ z : ℂ, p + q * ((z - p) / q) = z := fun z => by
    rw [mul_div_cancel₀ (z - p) hq, add_sub_cancel]
  have hFhc : ContinuousOn (fun ζ => F (p + q * ζ)) ((fun ζ : ℂ => p + q * ζ) ⁻¹' U) :=
    hc.comp hAc.continuousOn fun ζ hζ => hζ
  have hFhd : ∀ ζ ∈ (fun ζ : ℂ => p + q * ζ) ⁻¹' U, ζ.im ≠ 0 →
      DifferentiableAt ℂ (fun ζ => F (p + q * ζ)) ζ := by
    intro ζ hζ h0
    have hFz := hd (p + q * ζ) hζ (by rw [hinv1]; exact h0)
    exact hFz.comp ζ (by fun_prop : DifferentiableAt ℂ (fun ζ : ℂ => p + q * ζ) ζ)
  have hcons : IsConservativeOn (fun ζ => F (p + q * ζ)) ((fun ζ : ℂ => p + q * ζ) ⁻¹' U) := by
    intro z w hzw
    have hrect : uIcc z.re w.re ×ℂ uIcc z.im w.im ⊆ (fun ζ : ℂ => p + q * ζ) ⁻¹' U := hzw
    rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
    refine integral_boundary_rect_eq_zero_of_differentiableAt_off_real_axis _ z w
      (hFhc.mono hrect) ?_
    intro r hr hr0
    obtain ⟨hr1, hr2⟩ := mem_reProdIm.1 hr
    exact hFhd r (hrect (mem_reProdIm.2 ⟨mem_uIcc_of_mem_Ioo_min_max hr1,
      mem_uIcc_of_mem_Ioo_min_max hr2⟩)) hr0
  have hFhD : DifferentiableOn ℂ (fun ζ => F (p + q * ζ)) ((fun ζ : ℂ => p + q * ζ) ⁻¹' U) :=
    (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hVo).1 ⟨hcons, hFhc⟩
  intro z hz
  have hζ : (z - p) / q ∈ (fun ζ : ℂ => p + q * ζ) ⁻¹' U := by
    show p + q * ((z - p) / q) ∈ U
    rw [hinv2]
    exact hz
  have h1 := hFhD.differentiableAt (hVo.mem_nhds hζ)
  have h3 : DifferentiableAt ℂ ((fun ζ => F (p + q * ζ)) ∘ fun z => (z - p) / q) z :=
    h1.comp z (by fun_prop)
  have h4 : ((fun ζ => F (p + q * ζ)) ∘ fun z => (z - p) / q) = F := by
    funext w
    simp only [Function.comp_apply, hinv2]
  rw [h4] at h3
  exact h3.differentiableWithinAt

/-- **Liouville for quasi-periodic functions.**  An entire function with `G (z + 2a) = G z + A` and
`G (z + 2bi) = G z + B` is affine. -/
theorem exists_eq_mul_add_of_quasiPeriodic {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) {A B : ℂ} (h1 : ∀ z, G (z + 2 * a) = G z + A)
    (h2 : ∀ z, G (z + 2 * b * I) = G z + B) :
    ∃ c : ℂ, ∀ z, G z = c * z + G 0 := by
  have hG'd : Differentiable ℂ (deriv G) := by
    have := (hG.differentiableOn (s := univ)).deriv isOpen_univ
    exact fun z => (this z (mem_univ z)).differentiableAt (isOpen_univ.mem_nhds (mem_univ z))
  have hp1 : Function.Periodic (deriv G) (2 * (a : ℂ)) := by
    intro z
    have h := congrArg (fun F : ℂ → ℂ => deriv F z)
      (funext h1 : (fun z => G (z + 2 * a)) = fun z => G z + A)
    simp only [deriv_comp_add_const, deriv_add_const] at h
    exact h
  have hp2 : Function.Periodic (deriv G) (2 * (b : ℂ) * I) := by
    intro z
    have h := congrArg (fun F : ℂ → ℂ => deriv F z)
      (funext h2 : (fun z => G (z + 2 * b * I)) = fun z => G z + B)
    simp only [deriv_comp_add_const, deriv_add_const] at h
    exact h
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (2 * a + 2 * b)).exists_bound_of_continuousOn
    hG'd.continuous.continuousOn
  have hbound : ∀ z, ‖deriv G z‖ ≤ M := by
    intro z
    have h2a : 0 < 2 * a := by positivity
    have h2b : 0 < 2 * b := by positivity
    have hm1 := Int.floor_le (z.re / (2 * a))
    have hm2 := Int.lt_floor_add_one (z.re / (2 * a))
    have hn1 := Int.floor_le (z.im / (2 * b))
    have hn2 := Int.lt_floor_add_one (z.im / (2 * b))
    rw [le_div_iff₀ h2a] at hm1
    rw [div_lt_iff₀ h2a] at hm2
    rw [le_div_iff₀ h2b] at hn1
    rw [div_lt_iff₀ h2b] at hn2
    have he : deriv G (z - (⌊z.re / (2 * a)⌋ : ℂ) * (2 * (a : ℂ))
        - (⌊z.im / (2 * b)⌋ : ℂ) * (2 * (b : ℂ) * I)) = deriv G z := by
      rw [(hp2.int_mul _).sub_eq, (hp1.int_mul _).sub_eq]
    have hre : (z - (⌊z.re / (2 * a)⌋ : ℂ) * (2 * (a : ℂ))
        - (⌊z.im / (2 * b)⌋ : ℂ) * (2 * (b : ℂ) * I)).re
        = z.re - (⌊z.re / (2 * a)⌋ : ℝ) * (2 * a) := by simp
    have him : (z - (⌊z.re / (2 * a)⌋ : ℂ) * (2 * (a : ℂ))
        - (⌊z.im / (2 * b)⌋ : ℂ) * (2 * (b : ℂ) * I)).im
        = z.im - (⌊z.im / (2 * b)⌋ : ℝ) * (2 * b) := by simp
    rw [← he]
    refine hM _ ?_
    rw [mem_closedBall_zero_iff]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hre, him, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  have hconst : ∀ z, deriv G z = deriv G 0 := fun z =>
    hG'd.apply_eq_apply_of_bounded (isBounded_iff_forall_norm_le.2 ⟨M, by
      rintro _ ⟨w, rfl⟩
      exact hbound w⟩) z 0
  refine ⟨deriv G 0, fun z => ?_⟩
  have hH : Differentiable ℂ (fun z => G z - z * deriv G 0) :=
    hG.sub (differentiable_id.mul_const _)
  have hH' : ∀ z, deriv (fun z => G z - z * deriv G 0) z = 0 := by
    intro z
    have hd : HasDerivAt (fun z => G z - z * deriv G 0) (deriv G z - deriv G 0) z :=
      (hG z).hasDerivAt.sub (hasDerivAt_mul_const (deriv G 0))
    rw [hd.deriv, hconst z, sub_self]
  have := is_const_of_deriv_eq_zero hH hH' z 0
  simp only [zero_mul, sub_zero] at this
  rw [← this]
  ring

/-- Off the grid `aℤ`, `sin (π t / a) ≠ 0`, detected with a single candidate multiple. -/
theorem sin_ne_zero_of_abs_sub_lt {a t : ℝ} (ha : 0 < a) {k : ℤ} (hk : |t - k * a| < a)
    (hne : t ≠ k * a) : Real.sin (Real.pi * t / a) ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 h0
  have h1 : Real.pi * t = Real.pi * (n * a) := by
    rw [(div_eq_iff ha.ne').1 hn.symm]
    ring
  have ht : t = n * a := mul_left_cancel₀ Real.pi_ne_zero h1
  rw [ht, ← sub_mul, abs_mul, abs_of_pos ha] at hk
  have hnk : |((n - k : ℤ) : ℝ)| < 1 := by
    push_cast
    exact (mul_lt_iff_lt_one_left ha).1 hk
  have hnk' : |n - k| < 1 := by exact_mod_cast hnk
  have : n = k := by
    have := Int.abs_lt_one_iff.1 hnk'
    omega
  exact hne (by rw [ht, this])

theorem pi_mul_add_two_mul_div {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    Real.pi * (t + 2 * c) / c = Real.pi * t / c + 2 * Real.pi := by
  field_simp

/-! ### The rectangle and its folding -/

theorem rectangle_eq_Ioo_reProdIm_Ioo (a b : ℝ) : rectangle a b = Ioo 0 a ×ℂ Ioo 0 b := by
  ext z
  simp only [rectangle, mem_setOf_eq, mem_reProdIm, mem_Ioo, and_assoc]

theorem closure_rectangle_eq_reProdIm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    closure (rectangle a b) = Icc 0 a ×ℂ Icc 0 b := by
  rw [rectangle_eq_Ioo_reProdIm_Ioo, closure_reProdIm, closure_Ioo ha.ne, closure_Ioo hb.ne]

/-- The triangle wave of period `2a` equal to `x` on `[0, a]` (proof machinery for
`rect_rigidity_of_sideLines`). -/
def rectTriangleWave (a x : ℝ) : ℝ := a / Real.pi * Real.arccos (Real.cos (Real.pi * x / a))

/-- The square wave `sign (sin (π x / a))`, equal to `1` on `(0, a)` (proof machinery for
`rect_rigidity_of_sideLines`). -/
def rectSquareWave (a x : ℝ) : ℝ := Real.sign (Real.sin (Real.pi * x / a))

/-- The folding of `ℂ` onto the closed rectangle `[0, a] × [0, b]` (proof machinery for
`rect_rigidity_of_sideLines`). -/
def rectFold (a b : ℝ) (z : ℂ) : ℂ := ⟨rectTriangleWave a z.re, rectTriangleWave b z.im⟩

/-- The extension of `g` from `[0, a] × [0, b]` to `ℂ` by reflection in the side lines of the
target rectangle `[0, a'] × [0, b']` (proof machinery for `rect_rigidity_of_sideLines`). -/
def rectUnfold (a b a' b' : ℝ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  ⟨a' / a * z.re + rectSquareWave a z.re *
      ((g (rectFold a b z)).re - a' / a * rectTriangleWave a z.re),
    b' / b * z.im + rectSquareWave b z.im *
      ((g (rectFold a b z)).im - b' / b * rectTriangleWave b z.im)⟩

theorem continuous_rectTriangleWave (a : ℝ) : Continuous (rectTriangleWave a) := by
  have h : Continuous fun x : ℝ => a / Real.pi * Real.arccos (Real.cos (Real.pi * x / a)) :=
    continuous_const.mul (Real.continuous_arccos.comp (by fun_prop))
  exact h

theorem rectTriangleWave_nonneg {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 ≤ rectTriangleWave a x :=
  mul_nonneg (div_nonneg ha.le Real.pi_pos.le) (Real.arccos_nonneg _)

theorem rectTriangleWave_le {a : ℝ} (ha : 0 < a) (x : ℝ) : rectTriangleWave a x ≤ a := by
  unfold rectTriangleWave
  calc a / Real.pi * Real.arccos (Real.cos (Real.pi * x / a)) ≤ a / Real.pi * Real.pi :=
        mul_le_mul_of_nonneg_left (Real.arccos_le_pi _) (div_nonneg ha.le Real.pi_pos.le)
    _ = a := div_mul_cancel₀ a Real.pi_ne_zero

theorem rectTriangleWave_of_mem_Icc {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : x ∈ Icc 0 a) :
    rectTriangleWave a x = x := by
  unfold rectTriangleWave
  rw [Real.arccos_cos (div_nonneg (mul_nonneg Real.pi_pos.le hx.1) ha.le)
    ((div_le_iff₀ ha).2 (mul_le_mul_of_nonneg_left hx.2 Real.pi_pos.le))]
  field_simp

theorem rectTriangleWave_neg (a x : ℝ) : rectTriangleWave a (-x) = rectTriangleWave a x := by
  unfold rectTriangleWave
  rw [show Real.pi * -x / a = -(Real.pi * x / a) by ring, Real.cos_neg]

theorem rectTriangleWave_add {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    rectTriangleWave a (x + 2 * a) = rectTriangleWave a x := by
  unfold rectTriangleWave
  rw [pi_mul_add_two_mul_div ha, Real.cos_add_two_pi]

theorem rectTriangleWave_eq_zero_or_eq_of_sin_eq_zero {a : ℝ} {x : ℝ}
    (h : Real.sin (Real.pi * x / a) = 0) : rectTriangleWave a x = 0 ∨ rectTriangleWave a x = a := by
  have hc : Real.cos (Real.pi * x / a) * Real.cos (Real.pi * x / a) = 1 := by
    have := Real.sin_sq_add_cos_sq (Real.pi * x / a)
    rw [h] at this
    nlinarith
  unfold rectTriangleWave
  rcases mul_self_eq_one_iff.1 hc with h1 | h1
  · left
    rw [h1, Real.arccos_one, mul_zero]
  · right
    rw [h1, Real.arccos_neg_one]
    exact div_mul_cancel₀ a Real.pi_ne_zero

theorem rectSquareWave_neg (a x : ℝ) : rectSquareWave a (-x) = -rectSquareWave a x := by
  unfold rectSquareWave
  rw [show Real.pi * -x / a = -(Real.pi * x / a) by ring, Real.sin_neg, Real.sign_neg]

theorem rectSquareWave_add {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    rectSquareWave a (x + 2 * a) = rectSquareWave a x := by
  unfold rectSquareWave
  rw [pi_mul_add_two_mul_div ha, Real.sin_add_two_pi]

theorem abs_rectSquareWave_le (a x : ℝ) : |rectSquareWave a x| ≤ 1 := by
  unfold rectSquareWave
  rcases Real.sign_apply_eq (Real.sin (Real.pi * x / a)) with h | h | h <;> rw [h] <;> norm_num

theorem rectSquareWave_of_mem_Ioo {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : x ∈ Ioo 0 a) :
    rectSquareWave a x = 1 :=
  Real.sign_of_pos (Real.sin_pos_of_pos_of_lt_pi (div_pos (mul_pos Real.pi_pos hx.1) ha)
    ((div_lt_iff₀ ha).2 (mul_lt_mul_of_pos_left hx.2 Real.pi_pos)))

theorem rectSquareWave_zero (a : ℝ) : rectSquareWave a 0 = 0 := by
  simp [rectSquareWave]

theorem rectSquareWave_self {a : ℝ} (ha : a ≠ 0) : rectSquareWave a a = 0 := by
  unfold rectSquareWave
  rw [mul_div_assoc, div_self ha, mul_one, Real.sin_pi, Real.sign_zero]

theorem continuousAt_rectSquareWave {a x : ℝ} (h : Real.sin (Real.pi * x / a) ≠ 0) :
    ContinuousAt (rectSquareWave a) x := by
  have h1 : ContinuousAt Real.sign (Real.sin (Real.pi * x / a)) :=
    continuousAt_realSign_of_ne_zero h
  have h2 : Continuous fun x : ℝ => Real.sin (Real.pi * x / a) := by fun_prop
  exact ContinuousAt.comp (f := fun x : ℝ => Real.sin (Real.pi * x / a)) h1 h2.continuousAt

theorem continuous_rectFold (a b : ℝ) : Continuous (rectFold a b) := by
  have h1 := (continuous_rectTriangleWave a).comp continuous_re
  have h2 := (continuous_rectTriangleWave b).comp continuous_im
  have h : rectFold a b = fun z => ((rectTriangleWave a z.re : ℝ) : ℂ) +
      ((rectTriangleWave b z.im : ℝ) : ℂ) * I := by
    funext z
    exact Complex.mk_eq_add_mul_I _ _
  rw [h]
  exact (continuous_ofReal.comp h1).add ((continuous_ofReal.comp h2).mul continuous_const)

theorem rectFold_mem {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    rectFold a b z ∈ closure (rectangle a b) := by
  rw [closure_rectangle_eq_reProdIm ha hb]
  exact mem_reProdIm.2 ⟨⟨rectTriangleWave_nonneg ha _, rectTriangleWave_le ha _⟩,
    ⟨rectTriangleWave_nonneg hb _, rectTriangleWave_le hb _⟩⟩

/-! ### The functional equations of the unfolded map -/

theorem rectUnfold_add_two_mul {a b a' b' : ℝ} (ha : a ≠ 0) (g : ℂ → ℂ) (z : ℂ) :
    rectUnfold a b a' b' g (z + 2 * a) = rectUnfold a b a' b' g z + 2 * a' := by
  have hre : (z + 2 * (a : ℂ)).re = z.re + 2 * a := by simp
  have him : (z + 2 * (a : ℂ)).im = z.im := by simp
  have hf : rectFold a b (z + 2 * a) = rectFold a b z := by
    apply Complex.ext
    · show rectTriangleWave a (z + 2 * (a : ℂ)).re = rectTriangleWave a z.re
      rw [hre, rectTriangleWave_add ha]
    · show rectTriangleWave b (z + 2 * (a : ℂ)).im = rectTriangleWave b z.im
      rw [him]
  apply Complex.ext
  · show a' / a * (z + 2 * (a : ℂ)).re + rectSquareWave a (z + 2 * (a : ℂ)).re *
        ((g (rectFold a b (z + 2 * a))).re - a' / a * rectTriangleWave a (z + 2 * (a : ℂ)).re)
      = (rectUnfold a b a' b' g z + 2 * (a' : ℂ)).re
    rw [hre, hf, rectTriangleWave_add ha, rectSquareWave_add ha]
    simp only [Complex.add_re, rectUnfold, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    field_simp
    ring
  · show b' / b * (z + 2 * (a : ℂ)).im + rectSquareWave b (z + 2 * (a : ℂ)).im *
        ((g (rectFold a b (z + 2 * a))).im - b' / b * rectTriangleWave b (z + 2 * (a : ℂ)).im)
      = (rectUnfold a b a' b' g z + 2 * (a' : ℂ)).im
    rw [him, hf]
    simp [rectUnfold]

theorem rectUnfold_add_two_mul_I {a b a' b' : ℝ} (hb : b ≠ 0) (g : ℂ → ℂ) (z : ℂ) :
    rectUnfold a b a' b' g (z + 2 * b * I) = rectUnfold a b a' b' g z + 2 * b' * I := by
  have hre : (z + 2 * (b : ℂ) * I).re = z.re := by simp
  have him : (z + 2 * (b : ℂ) * I).im = z.im + 2 * b := by simp
  have hf : rectFold a b (z + 2 * b * I) = rectFold a b z := by
    apply Complex.ext
    · show rectTriangleWave a (z + 2 * (b : ℂ) * I).re = rectTriangleWave a z.re
      rw [hre]
    · show rectTriangleWave b (z + 2 * (b : ℂ) * I).im = rectTriangleWave b z.im
      rw [him, rectTriangleWave_add hb]
  apply Complex.ext
  · show a' / a * (z + 2 * (b : ℂ) * I).re + rectSquareWave a (z + 2 * (b : ℂ) * I).re *
        ((g (rectFold a b (z + 2 * b * I))).re - a' / a * rectTriangleWave a (z + 2 * (b : ℂ) * I).re)
      = (rectUnfold a b a' b' g z + 2 * (b' : ℂ) * I).re
    rw [hre, hf]
    simp [rectUnfold]
  · show b' / b * (z + 2 * (b : ℂ) * I).im + rectSquareWave b (z + 2 * (b : ℂ) * I).im *
        ((g (rectFold a b (z + 2 * b * I))).im - b' / b * rectTriangleWave b (z + 2 * (b : ℂ) * I).im)
      = (rectUnfold a b a' b' g z + 2 * (b' : ℂ) * I).im
    rw [him, hf, rectTriangleWave_add hb, rectSquareWave_add hb]
    simp only [Complex.add_im, rectUnfold, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im, zero_mul,
      mul_zero, mul_one, sub_zero, add_zero]
    field_simp
    ring

theorem rectUnfold_conj {a b a' b' : ℝ} (g : ℂ → ℂ) (z : ℂ) :
    rectUnfold a b a' b' g (conj z) = conj (rectUnfold a b a' b' g z) := by
  have hf : rectFold a b (conj z) = rectFold a b z := by
    apply Complex.ext
    · show rectTriangleWave a (conj z).re = rectTriangleWave a z.re
      rw [Complex.conj_re]
    · show rectTriangleWave b (conj z).im = rectTriangleWave b z.im
      rw [Complex.conj_im, rectTriangleWave_neg]
  apply Complex.ext
  · show a' / a * (conj z).re + rectSquareWave a (conj z).re *
        ((g (rectFold a b (conj z))).re - a' / a * rectTriangleWave a (conj z).re)
      = (conj (rectUnfold a b a' b' g z)).re
    rw [hf, Complex.conj_re, Complex.conj_re]
    rfl
  · show b' / b * (conj z).im + rectSquareWave b (conj z).im *
        ((g (rectFold a b (conj z))).im - b' / b * rectTriangleWave b (conj z).im)
      = (conj (rectUnfold a b a' b' g z)).im
    rw [hf, Complex.conj_im, Complex.conj_im, rectTriangleWave_neg, rectSquareWave_neg]
    show _ = -(b' / b * z.im + rectSquareWave b z.im *
        ((g (rectFold a b z)).im - b' / b * rectTriangleWave b z.im))
    ring

theorem rectUnfold_neg_conj {a b a' b' : ℝ} (g : ℂ → ℂ) (z : ℂ) :
    rectUnfold a b a' b' g (-conj z) = -conj (rectUnfold a b a' b' g z) := by
  have hf : rectFold a b (-conj z) = rectFold a b z := by
    apply Complex.ext
    · show rectTriangleWave a (-conj z).re = rectTriangleWave a z.re
      rw [Complex.neg_re, Complex.conj_re, rectTriangleWave_neg]
    · show rectTriangleWave b (-conj z).im = rectTriangleWave b z.im
      rw [Complex.neg_im, Complex.conj_im, neg_neg]
  apply Complex.ext
  · show a' / a * (-conj z).re + rectSquareWave a (-conj z).re *
        ((g (rectFold a b (-conj z))).re - a' / a * rectTriangleWave a (-conj z).re)
      = (-conj (rectUnfold a b a' b' g z)).re
    rw [hf, Complex.neg_re, Complex.conj_re, Complex.neg_re, Complex.conj_re, rectTriangleWave_neg,
      rectSquareWave_neg]
    show _ = -(a' / a * z.re + rectSquareWave a z.re *
        ((g (rectFold a b z)).re - a' / a * rectTriangleWave a z.re))
    ring
  · show b' / b * (-conj z).im + rectSquareWave b (-conj z).im *
        ((g (rectFold a b (-conj z))).im - b' / b * rectTriangleWave b (-conj z).im)
      = (-conj (rectUnfold a b a' b' g z)).im
    rw [hf, Complex.neg_im, Complex.conj_im, Complex.neg_im, Complex.conj_im, neg_neg, neg_neg]
    rfl

/-! ### The unfolded map extends `g`, and is continuous -/

theorem rectUnfold_eq_of_mem {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b) {g : ℂ → ℂ}
    (hbot : ∀ x ∈ Icc (0 : ℝ) a, (g (x : ℂ)).im = 0)
    (htop : ∀ x ∈ Icc (0 : ℝ) a, (g ((x : ℂ) + (b : ℂ) * I)).im = b')
    (hleft : ∀ y ∈ Icc (0 : ℝ) b, (g ((y : ℂ) * I)).re = 0)
    (hright : ∀ y ∈ Icc (0 : ℝ) b, (g ((a : ℂ) + (y : ℂ) * I)).re = a')
    {z : ℂ} (hz : z ∈ closure (rectangle a b)) : rectUnfold a b a' b' g z = g z := by
  rw [closure_rectangle_eq_reProdIm ha hb] at hz
  obtain ⟨hx, hy⟩ := mem_reProdIm.1 hz
  have hf : rectFold a b z = z :=
    Complex.ext (rectTriangleWave_of_mem_Icc ha hx) (rectTriangleWave_of_mem_Icc hb hy)
  apply Complex.ext
  · show a' / a * z.re + rectSquareWave a z.re *
        ((g (rectFold a b z)).re - a' / a * rectTriangleWave a z.re) = (g z).re
    rw [hf, rectTriangleWave_of_mem_Icc ha hx]
    rcases eq_or_lt_of_le hx.1 with h0 | h0
    · have hz0 : ((z.im : ℝ) : ℂ) * I = z := Complex.ext (by simp [← h0]) (by simp)
      have hg : (g z).re = 0 := by
        have := hleft z.im hy
        rwa [hz0] at this
      rw [← h0, rectSquareWave_zero, hg]
      ring
    · rcases eq_or_lt_of_le hx.2 with h1 | h1
      · have hza : (a : ℂ) + ((z.im : ℝ) : ℂ) * I = z := Complex.ext (by simp [h1]) (by simp)
        have hg : (g z).re = a' := by
          have := hright z.im hy
          rwa [hza] at this
        rw [h1, rectSquareWave_self ha.ne', hg, zero_mul, add_zero, div_mul_cancel₀ _ ha.ne']
      · rw [rectSquareWave_of_mem_Ioo ha ⟨h0, h1⟩]
        ring
  · show b' / b * z.im + rectSquareWave b z.im *
        ((g (rectFold a b z)).im - b' / b * rectTriangleWave b z.im) = (g z).im
    rw [hf, rectTriangleWave_of_mem_Icc hb hy]
    rcases eq_or_lt_of_le hy.1 with h0 | h0
    · have hz0 : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [← h0])
      have hg : (g z).im = 0 := by
        have := hbot z.re hx
        rwa [hz0] at this
      rw [← h0, rectSquareWave_zero, hg]
      ring
    · rcases eq_or_lt_of_le hy.2 with h1 | h1
      · have hzb : ((z.re : ℝ) : ℂ) + (b : ℂ) * I = z := Complex.ext (by simp) (by simp [h1])
        have hg : (g z).im = b' := by
          have := htop z.re hx
          rwa [hzb] at this
        rw [h1, rectSquareWave_self hb.ne', hg, zero_mul, add_zero, div_mul_cancel₀ _ hb.ne']
      · rw [rectSquareWave_of_mem_Ioo hb ⟨h0, h1⟩]
        ring

theorem continuous_rectUnfold {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b) {g : ℂ → ℂ}
    (hc : ContinuousOn g (closure (rectangle a b)))
    (hbot : ∀ x ∈ Icc (0 : ℝ) a, (g (x : ℂ)).im = 0)
    (htop : ∀ x ∈ Icc (0 : ℝ) a, (g ((x : ℂ) + (b : ℂ) * I)).im = b')
    (hleft : ∀ y ∈ Icc (0 : ℝ) b, (g ((y : ℂ) * I)).re = 0)
    (hright : ∀ y ∈ Icc (0 : ℝ) b, (g ((a : ℂ) + (y : ℂ) * I)).re = a') :
    Continuous (rectUnfold a b a' b' g) := by
  have hgF : Continuous fun z => g (rectFold a b z) :=
    hc.comp_continuous (continuous_rectFold a b) (rectFold_mem ha hb)
  have hTa : Continuous fun z : ℂ => rectTriangleWave a z.re :=
    (continuous_rectTriangleWave a).comp continuous_re
  have hTb : Continuous fun z : ℂ => rectTriangleWave b z.im :=
    (continuous_rectTriangleWave b).comp continuous_im
  have hTam : ∀ z : ℂ, rectTriangleWave a z.re ∈ Icc 0 a :=
    fun z => ⟨rectTriangleWave_nonneg ha _, rectTriangleWave_le ha _⟩
  have hTbm : ∀ z : ℂ, rectTriangleWave b z.im ∈ Icc 0 b :=
    fun z => ⟨rectTriangleWave_nonneg hb _, rectTriangleWave_le hb _⟩
  have hp₁ : Continuous fun z : ℂ => rectSquareWave a z.re *
      ((g (rectFold a b z)).re - a' / a * rectTriangleWave a z.re) := by
    refine continuous_mul_of_abs_le_one (s := fun z : ℂ => rectSquareWave a z.re)
      ((continuous_re.comp hgF).sub (continuous_const.mul hTa))
      (fun z => abs_rectSquareWave_le a z.re) fun z => ?_
    by_cases h : Real.sin (Real.pi * z.re / a) = 0
    · right
      show (g (rectFold a b z)).re - a' / a * rectTriangleWave a z.re = 0
      rcases rectTriangleWave_eq_zero_or_eq_of_sin_eq_zero h with h0 | h0
      · have hF : rectFold a b z = ((rectTriangleWave b z.im : ℝ) : ℂ) * I :=
          Complex.ext (by simp [rectFold, h0]) (by simp [rectFold])
        rw [hF, hleft _ (hTbm z), h0]
        ring
      · have hF : rectFold a b z = (a : ℂ) + ((rectTriangleWave b z.im : ℝ) : ℂ) * I :=
          Complex.ext (by simp [rectFold, h0]) (by simp [rectFold])
        rw [hF, hright _ (hTbm z), h0]
        field_simp
        ring
    · left
      exact (continuousAt_rectSquareWave h).comp continuous_re.continuousAt
  have hp₂ : Continuous fun z : ℂ => rectSquareWave b z.im *
      ((g (rectFold a b z)).im - b' / b * rectTriangleWave b z.im) := by
    refine continuous_mul_of_abs_le_one (s := fun z : ℂ => rectSquareWave b z.im)
      ((continuous_im.comp hgF).sub (continuous_const.mul hTb))
      (fun z => abs_rectSquareWave_le b z.im) fun z => ?_
    by_cases h : Real.sin (Real.pi * z.im / b) = 0
    · right
      show (g (rectFold a b z)).im - b' / b * rectTriangleWave b z.im = 0
      rcases rectTriangleWave_eq_zero_or_eq_of_sin_eq_zero h with h0 | h0
      · have hF : rectFold a b z = ((rectTriangleWave a z.re : ℝ) : ℂ) :=
          Complex.ext (by simp [rectFold]) (by simp [rectFold, h0])
        rw [hF, hbot _ (hTam z), h0]
        ring
      · have hF : rectFold a b z = ((rectTriangleWave a z.re : ℝ) : ℂ) + (b : ℂ) * I :=
          Complex.ext (by simp [rectFold]) (by simp [rectFold, h0])
        rw [hF, htop _ (hTam z), h0]
        field_simp
        ring
    · left
      exact (continuousAt_rectSquareWave h).comp continuous_im.continuousAt
  have heq : rectUnfold a b a' b' g = fun z =>
      ((a' / a * z.re + rectSquareWave a z.re *
        ((g (rectFold a b z)).re - a' / a * rectTriangleWave a z.re) : ℝ) : ℂ) +
      ((b' / b * z.im + rectSquareWave b z.im *
        ((g (rectFold a b z)).im - b' / b * rectTriangleWave b z.im) : ℝ) : ℂ) * I := by
    funext z
    exact Complex.mk_eq_add_mul_I _ _
  rw [heq]
  exact (continuous_ofReal.comp ((continuous_const.mul continuous_re).add hp₁)).add
    ((continuous_ofReal.comp ((continuous_const.mul continuous_im).add hp₂)).mul continuous_const)

/-! ### The unfolded map is entire -/

/-- The unfolded map is holomorphic off the grid lines `Re z ∈ aℤ`, `Im z ∈ bℤ`: on the base cell it
is `g`, and every open cell is carried to the base cell by the symmetries of `rectUnfold`. -/
theorem differentiableAt_rectUnfold_of_sin_ne_zero {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b)
    {g : ℂ → ℂ} (hd : DifferentiableOn ℂ g (rectangle a b))
    (hbot : ∀ x ∈ Icc (0 : ℝ) a, (g (x : ℂ)).im = 0)
    (htop : ∀ x ∈ Icc (0 : ℝ) a, (g ((x : ℂ) + (b : ℂ) * I)).im = b')
    (hleft : ∀ y ∈ Icc (0 : ℝ) b, (g ((y : ℂ) * I)).re = 0)
    (hright : ∀ y ∈ Icc (0 : ℝ) b, (g ((a : ℂ) + (y : ℂ) * I)).re = a') (z : ℂ)
    (hx : Real.sin (Real.pi * z.re / a) ≠ 0) (hy : Real.sin (Real.pi * z.im / b) ≠ 0) :
    DifferentiableAt ℂ (rectUnfold a b a' b' g) z := by
  -- transport of differentiability along the four symmetries
  have hT1 : ∀ w, DifferentiableAt ℂ (rectUnfold a b a' b' g) w →
      DifferentiableAt ℂ (rectUnfold a b a' b' g) (w + 2 * a) := by
    intro w hw
    have h1 : DifferentiableAt ℂ (rectUnfold a b a' b' g) ((w + 2 * a) - 2 * a) := by
      rwa [add_sub_cancel_right]
    have h2 : DifferentiableAt ℂ (fun u => rectUnfold a b a' b' g (u - 2 * a) + 2 * a')
        (w + 2 * a) :=
      (h1.comp (w + 2 * a)
        (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => u - 2 * (a : ℂ)) (w + 2 * a))).add_const _
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    have := rectUnfold_add_two_mul (b := b) (a' := a') (b' := b') ha.ne' g (u - 2 * a)
    rw [sub_add_cancel] at this
    exact this
  have hT2 : ∀ w, DifferentiableAt ℂ (rectUnfold a b a' b' g) w →
      DifferentiableAt ℂ (rectUnfold a b a' b' g) (w + 2 * b * I) := by
    intro w hw
    have h1 : DifferentiableAt ℂ (rectUnfold a b a' b' g) ((w + 2 * b * I) - 2 * b * I) := by
      rwa [add_sub_cancel_right]
    have h2 : DifferentiableAt ℂ (fun u => rectUnfold a b a' b' g (u - 2 * b * I) + 2 * b' * I)
        (w + 2 * b * I) :=
      (h1.comp (w + 2 * b * I) (by fun_prop :
        DifferentiableAt ℂ (fun u : ℂ => u - 2 * (b : ℂ) * I) (w + 2 * b * I))).add_const _
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    have := rectUnfold_add_two_mul_I (a := a) (a' := a') (b' := b') hb.ne' g (u - 2 * b * I)
    rw [sub_add_cancel] at this
    exact this
  have hC : ∀ w, DifferentiableAt ℂ (rectUnfold a b a' b' g) w →
      DifferentiableAt ℂ (rectUnfold a b a' b' g) (conj w) := by
    intro w hw
    refine hw.conj_conj.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    show rectUnfold a b a' b' g u = conj (rectUnfold a b a' b' g (conj u))
    rw [rectUnfold_conj, Complex.conj_conj]
  have hN : ∀ w, DifferentiableAt ℂ (rectUnfold a b a' b' g) w →
      DifferentiableAt ℂ (rectUnfold a b a' b' g) (-conj w) := by
    intro w hw
    have h1 : DifferentiableAt ℂ (conj ∘ rectUnfold a b a' b' g ∘ conj) (-(-conj w)) := by
      rw [neg_neg]
      exact hw.conj_conj
    have h2 : DifferentiableAt ℂ (fun u => -(conj ∘ rectUnfold a b a' b' g ∘ conj) (-u)) (-conj w) :=
      (h1.comp (-conj w) (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => -u) (-conj w))).neg
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    show rectUnfold a b a' b' g u = -conj (rectUnfold a b a' b' g (conj (-u)))
    rw [map_neg, rectUnfold_neg_conj, map_neg, Complex.conj_conj, neg_neg]
  -- elementary facts about `sin (π t / c)`
  have hsneg : ∀ c t : ℝ, Real.sin (Real.pi * -t / c) = -Real.sin (Real.pi * t / c) := fun c t => by
    rw [show Real.pi * -t / c = -(Real.pi * t / c) by ring, Real.sin_neg]
  have hsadd : ∀ c t : ℝ, c ≠ 0 → Real.sin (Real.pi * (t + 2 * c) / c) = Real.sin (Real.pi * t / c) :=
    fun c t hc => by rw [pi_mul_add_two_mul_div hc, Real.sin_add_two_pi]
  have hs0 : ∀ c : ℝ, Real.sin (Real.pi * 0 / c) = 0 := fun c => by simp
  have hsc : ∀ c : ℝ, c ≠ 0 → Real.sin (Real.pi * c / c) = 0 := fun c hc => by
    rw [mul_div_assoc, div_self hc, mul_one, Real.sin_pi]
  have hRo : IsOpen (rectangle a b) := by
    rw [rectangle_eq_Ioo_reProdIm_Ioo]
    exact isOpen_Ioo.reProdIm isOpen_Ioo
  -- the base cell
  have hbase : ∀ x ∈ Icc (0 : ℝ) a, ∀ y ∈ Icc (0 : ℝ) b, Real.sin (Real.pi * x / a) ≠ 0 →
      Real.sin (Real.pi * y / b) ≠ 0 → DifferentiableAt ℂ (rectUnfold a b a' b' g) ⟨x, y⟩ := by
    intro x hx y hy hsx hsy
    have hx0 : x ≠ 0 := fun h => by rw [h] at hsx; exact hsx (hs0 a)
    have hxa : x ≠ a := fun h => by rw [h] at hsx; exact hsx (hsc a ha.ne')
    have hy0 : y ≠ 0 := fun h => by rw [h] at hsy; exact hsy (hs0 b)
    have hyb : y ≠ b := fun h => by rw [h] at hsy; exact hsy (hsc b hb.ne')
    have hmem : (⟨x, y⟩ : ℂ) ∈ rectangle a b :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hxa,
        lt_of_le_of_ne hy.1 (Ne.symm hy0), lt_of_le_of_ne hy.2 hyb⟩
    have hev : rectUnfold a b a' b' g =ᶠ[𝓝 (⟨x, y⟩ : ℂ)] g := by
      filter_upwards [hRo.mem_nhds hmem] with u hu
      exact rectUnfold_eq_of_mem ha hb hbot htop hleft hright (subset_closure hu)
    exact (hd.differentiableAt (hRo.mem_nhds hmem)).congr_of_eventuallyEq hev
  -- fold in the imaginary direction
  have hfoldy : ∀ x ∈ Icc (0 : ℝ) a, ∀ y : ℝ, Real.sin (Real.pi * x / a) ≠ 0 →
      Real.sin (Real.pi * y / b) ≠ 0 → DifferentiableAt ℂ (rectUnfold a b a' b' g) ⟨x, y⟩ := by
    intro x hx
    refine forall_of_fold_Icc hb (P := fun y => Real.sin (Real.pi * x / a) ≠ 0 →
      Real.sin (Real.pi * y / b) ≠ 0 → DifferentiableAt ℂ (rectUnfold a b a' b' g) ⟨x, y⟩)
      (fun y hy => hbase x hx y hy) ?_ ?_
    · intro y hP hsx hsy
      have h1 := hC _ (hP hsx (by rw [hsneg] at hsy; exact neg_ne_zero.1 hsy))
      have he : conj (⟨x, y⟩ : ℂ) = ⟨x, -y⟩ := Complex.ext (by simp) (by simp)
      rwa [he] at h1
    · intro y hP hsx hsy
      have h1 := hT2 _ (hP hsx (by rwa [hsadd b y hb.ne'] at hsy))
      have he : (⟨x, y⟩ : ℂ) + 2 * b * I = ⟨x, y + 2 * b⟩ := Complex.ext (by simp) (by simp)
      rwa [he] at h1
  -- fold in the real direction
  have hall : ∀ x y : ℝ, Real.sin (Real.pi * x / a) ≠ 0 →
      Real.sin (Real.pi * y / b) ≠ 0 → DifferentiableAt ℂ (rectUnfold a b a' b' g) ⟨x, y⟩ := by
    refine forall_of_fold_Icc ha (P := fun x => ∀ y : ℝ, Real.sin (Real.pi * x / a) ≠ 0 →
      Real.sin (Real.pi * y / b) ≠ 0 → DifferentiableAt ℂ (rectUnfold a b a' b' g) ⟨x, y⟩)
      (fun x hx => hfoldy x hx) ?_ ?_
    · intro x hP y hsx hsy
      have h1 := hN _ (hP y (by rw [hsneg] at hsx; exact neg_ne_zero.1 hsx) hsy)
      have he : -conj (⟨x, y⟩ : ℂ) = ⟨-x, y⟩ := Complex.ext (by simp) (by simp)
      rwa [he] at h1
    · intro x hP y hsx hsy
      have h1 := hT1 _ (hP y (by rwa [hsadd a x ha.ne'] at hsx) hsy)
      have he : (⟨x, y⟩ : ℂ) + 2 * a = ⟨x + 2 * a, y⟩ := Complex.ext (by simp) (by simp)
      rwa [he] at h1
  have := hall z.re z.im hx hy
  rwa [Complex.eta] at this

/-- The unfolded map is entire: it is continuous and holomorphic off the grid lines, so it is
holomorphic by Morera's theorem across one vertical line and then across one horizontal line. -/
theorem differentiable_rectUnfold {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b) {g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ g (rectangle a b)) (hc : ContinuousOn g (closure (rectangle a b)))
    (hbot : ∀ x ∈ Icc (0 : ℝ) a, (g (x : ℂ)).im = 0)
    (htop : ∀ x ∈ Icc (0 : ℝ) a, (g ((x : ℂ) + (b : ℂ) * I)).im = b')
    (hleft : ∀ y ∈ Icc (0 : ℝ) b, (g ((y : ℂ) * I)).re = 0)
    (hright : ∀ y ∈ Icc (0 : ℝ) b, (g ((a : ℂ) + (y : ℂ) * I)).re = a') :
    Differentiable ℂ (rectUnfold a b a' b' g) := by
  have hGc := continuous_rectUnfold (a' := a') (b' := b') ha hb hc hbot htop hleft hright
  have hcell := differentiableAt_rectUnfold_of_sin_ne_zero (a' := a') (b' := b') ha hb hd hbot htop
    hleft hright
  have hfloor : ∀ c : ℝ, 0 < c → ∀ t : ℝ, |t - (⌊t / c⌋ : ℝ) * c| < c := by
    intro c hc t
    have h1 := Int.floor_le (t / c)
    have h2 := Int.lt_floor_add_one (t / c)
    rw [le_div_iff₀ hc] at h1
    rw [div_lt_iff₀ hc] at h2
    rw [abs_lt]
    constructor <;> linarith
  -- off the horizontal grid lines, via Morera across one vertical line
  have hV : ∀ z : ℂ, Real.sin (Real.pi * z.im / b) ≠ 0 →
      DifferentiableAt ℂ (rectUnfold a b a' b' g) z := by
    intro z hz
    have hUo : IsOpen {w : ℂ | |w.re - (⌊z.re / a⌋ : ℝ) * a| < a ∧
        Real.sin (Real.pi * w.im / b) ≠ 0} :=
      (isOpen_lt (f := fun w : ℂ => |w.re - (⌊z.re / a⌋ : ℝ) * a|) (g := fun _ => a)
        (by fun_prop) continuous_const).and
        (isOpen_ne_fun (f := fun w : ℂ => Real.sin (Real.pi * w.im / b)) (g := fun _ => (0 : ℝ))
          (by fun_prop) continuous_const)
    have hzU : z ∈ {w : ℂ | |w.re - (⌊z.re / a⌋ : ℝ) * a| < a ∧
        Real.sin (Real.pi * w.im / b) ≠ 0} := ⟨hfloor a ha z.re, hz⟩
    have hD := differentiableOn_of_continuousOn_of_differentiableAt_off_line hUo hGc.continuousOn
      (((⌊z.re / a⌋ : ℝ) * a : ℝ) : ℂ) I I_ne_zero fun w hw hw0 => by
        refine hcell w (sin_ne_zero_of_abs_sub_lt ha hw.1 fun hwre => hw0 ?_) hw.2
        rw [Complex.div_I]
        simp [hwre]
    exact hD.differentiableAt (hUo.mem_nhds hzU)
  -- everywhere, via Morera across one horizontal line
  intro z
  have hUo : IsOpen {w : ℂ | |w.im - (⌊z.im / b⌋ : ℝ) * b| < b} :=
    isOpen_lt (f := fun w : ℂ => |w.im - (⌊z.im / b⌋ : ℝ) * b|) (g := fun _ => b) (by fun_prop)
      continuous_const
  have hzU : z ∈ {w : ℂ | |w.im - (⌊z.im / b⌋ : ℝ) * b| < b} := hfloor b hb z.im
  have hD := differentiableOn_of_continuousOn_of_differentiableAt_off_line hUo hGc.continuousOn
    ((((⌊z.im / b⌋ : ℝ) * b : ℝ) : ℂ) * I) 1 one_ne_zero fun w hw hw0 => by
      refine hV w (sin_ne_zero_of_abs_sub_lt hb hw fun hwim => hw0 ?_)
      simp [hwim]
  exact hD.differentiableAt (hUo.mem_nhds hzU)

/-- **Rigidity from the side lines.**  Let `g` be holomorphic on the open rectangle
`R = (0, a) × (0, b)` and continuous on its closure, and let each closed side of `R` be mapped into
the line through the corresponding side of `R' = (0, a') × (0, b')`: the bottom side into `Im w = 0`,
the top side into `Im w = b'`, the left side into `Re w = 0` and the right side into `Re w = a'`.
Then `a'/a = b'/b` and `g z = (a'/a) z` on the closed rectangle.

Route: reflection in the four side lines (`schwarz_reflection_segment`, after an affine change of
variable) extends `g` to an entire `G` with `G (z + 2a) = G z + 2a'` and `G (z + 2bi) = G z + 2b'i`
(the vertices are removable singularities); `G'` is doubly periodic, hence constant by Liouville. -/
theorem rect_rigidity_of_sideLines {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b) (_ha' : 0 < a')
    (_hb' : 0 < b') {g : ℂ → ℂ} (hd : DifferentiableOn ℂ g (rectangle a b))
    (hc : ContinuousOn g (closure (rectangle a b)))
    (hbot : ∀ x ∈ Icc (0 : ℝ) a, (g (x : ℂ)).im = 0)
    (htop : ∀ x ∈ Icc (0 : ℝ) a, (g ((x : ℂ) + (b : ℂ) * I)).im = b')
    (hleft : ∀ y ∈ Icc (0 : ℝ) b, (g ((y : ℂ) * I)).re = 0)
    (hright : ∀ y ∈ Icc (0 : ℝ) b, (g ((a : ℂ) + (y : ℂ) * I)).re = a') :
    a' / a = b' / b ∧ ∀ z ∈ closure (rectangle a b), g z = ((a' / a : ℝ) : ℂ) * z := by
  -- the reflected extension is entire and quasi-periodic, hence affine
  have hGd := differentiable_rectUnfold (a' := a') (b' := b') ha hb hd hc hbot htop hleft hright
  obtain ⟨c, hcG⟩ := exists_eq_mul_add_of_quasiPeriodic ha hb hGd
    (rectUnfold_add_two_mul ha.ne' g) (rectUnfold_add_two_mul_I hb.ne' g)
  have hK : ∀ z ∈ closure (rectangle a b), rectUnfold a b a' b' g z = g z :=
    fun z hz => rectUnfold_eq_of_mem ha hb hbot htop hleft hright hz
  have hmem : ∀ z : ℂ, z.re ∈ Icc 0 a → z.im ∈ Icc 0 b → z ∈ closure (rectangle a b) := by
    intro z hx hy
    rw [closure_rectangle_eq_reProdIm ha hb]
    exact mem_reProdIm.2 ⟨hx, hy⟩
  -- the values of `g` at three vertices
  have hg0 : g 0 = 0 := Complex.ext (by simpa using hleft 0 ⟨le_rfl, hb.le⟩)
    (by simpa using hbot 0 ⟨le_rfl, ha.le⟩)
  have hga : g a = a' := Complex.ext (by simpa using hright 0 ⟨le_rfl, hb.le⟩)
    (by simpa using hbot a ⟨ha.le, le_rfl⟩)
  have hgb : g (b * I) = b' * I := Complex.ext (by simpa using hleft b ⟨hb.le, le_rfl⟩)
    (by simpa using htop 0 ⟨le_rfl, ha.le⟩)
  have h0K : (0 : ℂ) ∈ closure (rectangle a b) :=
    hmem 0 (by simp [ha.le]) (by simp [hb.le])
  have haK : (a : ℂ) ∈ closure (rectangle a b) :=
    hmem a (by simp [ha.le]) (by simp [hb.le])
  have hbK : (b : ℂ) * I ∈ closure (rectangle a b) :=
    hmem (b * I) (by simp [ha.le]) (by simp [hb.le])
  have hG0 : rectUnfold a b a' b' g 0 = 0 := by rw [hK 0 h0K, hg0]
  have hca : c * a = a' := by
    have := hcG a
    rw [hK _ haK, hga, hG0, add_zero] at this
    exact this.symm
  have hcb : c * (b * I) = b' * I := by
    have := hcG (b * I)
    rw [hK _ hbK, hgb, hG0, add_zero] at this
    exact this.symm
  have hc_eq : c = ((a' / a : ℝ) : ℂ) := by
    have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
    rw [Complex.ofReal_div, eq_div_iff ha0, hca]
  refine ⟨?_, fun z hz => ?_⟩
  · have h1 : c * b = b' := by
      rw [← mul_assoc] at hcb
      exact mul_right_cancel₀ I_ne_zero hcb
    rw [hc_eq, ← Complex.ofReal_mul, Complex.ofReal_inj] at h1
    rw [eq_div_iff hb.ne']
    exact h1
  · rw [← hK z hz, hcG z, hG0, add_zero, hc_eq]

/-- The closed rectangle: `closure (rectangle a b) = {0 ≤ Re z ≤ a, 0 ≤ Im z ≤ b}`. -/
theorem mem_closure_rectangle_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {z : ℂ} :
    z ∈ closure (rectangle a b) ↔ 0 ≤ z.re ∧ z.re ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b := by
  have hR : rectangle a b = Ioo 0 a ×ℂ Ioo 0 b := by
    ext z
    simp only [rectangle, mem_setOf_eq, mem_reProdIm, mem_Ioo, and_assoc]
  rw [hR, closure_reProdIm, closure_Ioo ha.ne, closure_Ioo hb.ne, mem_reProdIm, mem_Icc, mem_Icc,
    and_assoc]

/-- The half-turn `z ↦ a + bi - z` about the centre preserves the open rectangle. -/
theorem rect_rot_mem_iff {a b : ℝ} {z : ℂ} :
    (a : ℂ) + (b : ℂ) * I - z ∈ rectangle a b ↔ z ∈ rectangle a b := by
  have e1 : ((a : ℂ) + (b : ℂ) * I - z).re = a - z.re := by simp
  have e2 : ((a : ℂ) + (b : ℂ) * I - z).im = b - z.im := by simp
  show (0 < ((a : ℂ) + (b : ℂ) * I - z).re ∧ ((a : ℂ) + (b : ℂ) * I - z).re < a ∧
      0 < ((a : ℂ) + (b : ℂ) * I - z).im ∧ ((a : ℂ) + (b : ℂ) * I - z).im < b) ↔
    (0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b)
  rw [e1, e2]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The half-turn `z ↦ a + bi - z` preserves the closed rectangle. -/
theorem rect_rot_mem_closure_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {z : ℂ} :
    (a : ℂ) + (b : ℂ) * I - z ∈ closure (rectangle a b) ↔ z ∈ closure (rectangle a b) := by
  have e1 : ((a : ℂ) + (b : ℂ) * I - z).re = a - z.re := by simp
  have e2 : ((a : ℂ) + (b : ℂ) * I - z).im = b - z.im := by simp
  rw [mem_closure_rectangle_iff ha hb, mem_closure_rectangle_iff ha hb, e1, e2]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The transposition `z ↦ i conj z` (which swaps real and imaginary parts) exchanges
`rectangle a b` and `rectangle b a`. -/
theorem rect_transpose_mem_iff {a b : ℝ} {z : ℂ} :
    I * conj z ∈ rectangle a b ↔ z ∈ rectangle b a := by
  have e1 : (I * conj z).re = z.im := by simp
  have e2 : (I * conj z).im = z.re := by simp
  show (0 < (I * conj z).re ∧ (I * conj z).re < a ∧ 0 < (I * conj z).im ∧ (I * conj z).im < b) ↔
    (0 < z.re ∧ z.re < b ∧ 0 < z.im ∧ z.im < a)
  rw [e1, e2]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h3, h4, h1, h2⟩

/-- The transposition `z ↦ i conj z` exchanges the closed rectangles. -/
theorem rect_transpose_mem_closure_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {z : ℂ} :
    I * conj z ∈ closure (rectangle a b) ↔ z ∈ closure (rectangle b a) := by
  have e1 : (I * conj z).re = z.im := by simp
  have e2 : (I * conj z).im = z.re := by simp
  rw [mem_closure_rectangle_iff ha hb, mem_closure_rectangle_iff hb ha, e1, e2]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h3, h4, h1, h2⟩

/-- Transport of the hypotheses of `rect_sideLines_of_homeo` along a pair of continuous
involutions `φ`, `ψ` of the plane exchanging the rectangles: `ψ ∘ g ∘ φ` again maps the open
rectangle onto the open rectangle, is continuous and injective on the closed rectangle and maps
it onto the closed rectangle. -/
theorem rect_homeo_conj {a b a' b' c d c' d' : ℝ} {g φ ψ : ℂ → ℂ}
    (hφ : Continuous φ) (hφφ : ∀ z, φ (φ z) = z)
    (hφR : ∀ z, φ z ∈ rectangle a b ↔ z ∈ rectangle c d)
    (hφcl : ∀ z, φ z ∈ closure (rectangle a b) ↔ z ∈ closure (rectangle c d))
    (hψ : Continuous ψ) (hψψ : ∀ w, ψ (ψ w) = w)
    (hψR : ∀ w, ψ w ∈ rectangle a' b' ↔ w ∈ rectangle c' d')
    (hψcl : ∀ w, ψ w ∈ closure (rectangle a' b') ↔ w ∈ closure (rectangle c' d'))
    (hopen : g '' rectangle a b = rectangle a' b')
    (hc : ContinuousOn g (closure (rectangle a b))) (hinj : InjOn g (closure (rectangle a b)))
    (himg : g '' closure (rectangle a b) = closure (rectangle a' b')) :
    (ψ ∘ g ∘ φ) '' rectangle c d = rectangle c' d' ∧
      ContinuousOn (ψ ∘ g ∘ φ) (closure (rectangle c d)) ∧
      InjOn (ψ ∘ g ∘ φ) (closure (rectangle c d)) ∧
      (ψ ∘ g ∘ φ) '' closure (rectangle c d) = closure (rectangle c' d') := by
  have hφimg : ∀ S : Set ℂ, φ '' S = φ ⁻¹' S := fun S =>
    congrFun (Set.image_eq_preimage_of_inverse hφφ hφφ) S
  have hψimg : ∀ S : Set ℂ, ψ '' S = ψ ⁻¹' S := fun S =>
    congrFun (Set.image_eq_preimage_of_inverse hψψ hψψ) S
  have hφR' : φ '' rectangle c d = rectangle a b := by
    rw [hφimg]; ext z; rw [mem_preimage, ← hφR (φ z), hφφ z]
  have hφcl' : φ '' closure (rectangle c d) = closure (rectangle a b) := by
    rw [hφimg]; ext z; rw [mem_preimage, ← hφcl (φ z), hφφ z]
  have hψR' : ψ '' rectangle a' b' = rectangle c' d' := by
    rw [hψimg]; ext w; exact hψR w
  have hψcl' : ψ '' closure (rectangle a' b') = closure (rectangle c' d') := by
    rw [hψimg]; ext w; exact hψcl w
  have hmaps : MapsTo φ (closure (rectangle c d)) (closure (rectangle a b)) :=
    fun z hz => (hφcl z).2 hz
  have hφinj : Function.Injective φ := Function.Involutive.injective hφφ
  have hψinj : Function.Injective ψ := Function.Involutive.injective hψψ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Set.image_comp, Set.image_comp, hφR', hopen, hψR']
  · exact hψ.comp_continuousOn (hc.comp hφ.continuousOn hmaps)
  · exact hψinj.injOn.comp (hinj.comp hφinj.injOn hmaps) (mapsTo_univ _ _)
  · rw [Set.image_comp, Set.image_comp, hφcl', himg, hψcl']

/-- **The bottom side goes to the bottom side.**  The core of `rect_sideLines_of_homeo`: under
its hypotheses the closed bottom side `[0, a]` is mapped into the real axis.

Route: `g` maps `∂R = closure R \ R` into `∂R'`, and the image of `[0, a]` avoids the two top
vertices of `R'` (injectivity).  The set `∂R' ∖ {a'+b'i, b'i}` is the disjoint union of the open top
side and the "U-shaped" rest `U = ∂R' ∩ {Im w < b'}`, both relatively open, so by connectedness
the image of `[0, a]`, which contains `g 0 = 0 ∈ U`, lies in `U`.  The continuous "unrolling"
`s w = Re w + Im w (2 Re w / a' − 1)` (which is `−Im w` on the left side, `Re w` on the bottom side
and `a' + Im w` on the right side) is injective on `U`, so `s ∘ g` is continuous and injective on
`[0, a]` with `s (g 0) = 0 ≤ a' = s (g a)`, hence strictly increasing; thus `0 ≤ s (g x) ≤ a'` for
`x ∈ [0, a]`, which on `U` forces `Im (g x) = 0`. -/
theorem rect_bottom_of_homeo {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a')
    (hb' : 0 < b') {g : ℂ → ℂ} (hopen : g '' rectangle a b = rectangle a' b')
    (hc : ContinuousOn g (closure (rectangle a b))) (hinj : InjOn g (closure (rectangle a b)))
    (himg : g '' closure (rectangle a b) = closure (rectangle a' b'))
    (h0 : g 0 = 0) (h1 : g (a : ℂ) = (a' : ℂ))
    (h2 : g ((a : ℂ) + (b : ℂ) * I) = (a' : ℂ) + (b' : ℂ) * I)
    (h3 : g ((b : ℂ) * I) = (b' : ℂ) * I) :
    ∀ x ∈ Icc (0 : ℝ) a, (g (x : ℂ)).im = 0 := by
  -- boundary points go to boundary points
  have hbd : ∀ z ∈ closure (rectangle a b), z ∉ rectangle a b →
      g z ∈ closure (rectangle a' b') ∧ g z ∉ rectangle a' b' := by
    intro z hz hzR
    refine ⟨by rw [← himg]; exact mem_image_of_mem g hz, fun hgz => ?_⟩
    rw [← hopen] at hgz
    obtain ⟨z', hz', hzz'⟩ := hgz
    have hzz : z' = z := hinj (subset_closure hz') hz hzz'
    exact hzR (hzz ▸ hz')
  -- the closed bottom side and the two top vertices lie in the closed rectangle
  have hx_cl : ∀ x ∈ Icc (0 : ℝ) a, (x : ℂ) ∈ closure (rectangle a b) := fun x hx =>
    (mem_closure_rectangle_iff ha hb).2 ⟨by simpa using hx.1, by simpa using hx.2, by simp,
      by simp [hb.le]⟩
  have hx_not : ∀ x : ℝ, (x : ℂ) ∉ rectangle a b := fun x h => by
    simp [rectangle] at h
  have hv2 : (a : ℂ) + (b : ℂ) * I ∈ closure (rectangle a b) :=
    (mem_closure_rectangle_iff ha hb).2 ⟨by simp [ha.le], by simp, by simp [hb.le], by simp⟩
  have hv3 : (b : ℂ) * I ∈ closure (rectangle a b) :=
    (mem_closure_rectangle_iff ha hb).2 ⟨by simp, by simp [ha.le], by simp [hb.le], by simp⟩
  -- the image of the bottom side avoids the two top vertices of `R'`
  have hne2 : ∀ x ∈ Icc (0 : ℝ) a, g (x : ℂ) ≠ (a' : ℂ) + (b' : ℂ) * I := by
    intro x hx heq
    rw [← h2] at heq
    have h := congrArg Complex.im (hinj (hx_cl x hx) hv2 heq)
    simp at h
    exact hb.ne h
  have hne3 : ∀ x ∈ Icc (0 : ℝ) a, g (x : ℂ) ≠ (b' : ℂ) * I := by
    intro x hx heq
    rw [← h3] at heq
    have h := congrArg Complex.im (hinj (hx_cl x hx) hv3 heq)
    simp at h
    exact hb.ne h
  -- description of the boundary points of `R'`
  have hbd' : ∀ w, w ∈ closure (rectangle a' b') → w ∉ rectangle a' b' →
      (0 ≤ w.re ∧ w.re ≤ a' ∧ 0 ≤ w.im ∧ w.im ≤ b') ∧
        (w.re = 0 ∨ w.re = a' ∨ w.im = 0 ∨ w.im = b') := by
    intro w hw hwR
    have hw' := (mem_closure_rectangle_iff ha' hb').1 hw
    refine ⟨hw', ?_⟩
    by_contra hcon
    push Not at hcon
    exact hwR ⟨lt_of_le_of_ne hw'.1 hcon.1.symm, lt_of_le_of_ne hw'.2.1 hcon.2.1,
      lt_of_le_of_ne hw'.2.2.1 hcon.2.2.1.symm, lt_of_le_of_ne hw'.2.2.2 hcon.2.2.2⟩
  have hbx : ∀ x ∈ Icc (0 : ℝ) a,
      (0 ≤ (g x).re ∧ (g x).re ≤ a' ∧ 0 ≤ (g x).im ∧ (g x).im ≤ b') ∧
        ((g x).re = 0 ∨ (g x).re = a' ∨ (g x).im = 0 ∨ (g x).im = b') := fun x hx =>
    hbd' _ (hbd _ (hx_cl x hx) (hx_not x)).1 (hbd _ (hx_cl x hx) (hx_not x)).2
  -- Step A: by connectedness the image of the bottom side stays below the top side
  have hpc : ContinuousOn (fun x : ℝ => g x) (Icc 0 a) :=
    hc.comp continuous_ofReal.continuousOn hx_cl
  have hpre : IsPreconnected ((fun x : ℝ => g x) '' Icc 0 a) := isPreconnected_Icc.image _ hpc
  have hV : IsOpen {w : ℂ | 0 < w.re ∧ w.re < a' ∧ b' / 2 < w.im} :=
    (isOpen_lt continuous_const continuous_re).and
      ((isOpen_lt continuous_re continuous_const).and (isOpen_lt continuous_const continuous_im))
  have hW : IsOpen {w : ℂ | w.im < b'} := isOpen_lt continuous_im continuous_const
  have hsub : (fun x : ℝ => g x) '' Icc 0 a ⊆
      {w : ℂ | 0 < w.re ∧ w.re < a' ∧ b' / 2 < w.im} ∪ {w : ℂ | w.im < b'} := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [mem_union, mem_setOf_eq]
    obtain ⟨⟨hr0, hra, hi0, hib⟩, -⟩ := hbx x hx
    by_cases him : (g x).im < b'
    · exact Or.inr him
    · have him' : (g x).im = b' := le_antisymm hib (not_lt.mp him)
      left
      refine ⟨?_, ?_, by linarith⟩
      · rcases hr0.lt_or_eq with h | h
        · exact h
        · exact absurd (Complex.ext (by simp [← h]) (by simp [him'])) (hne3 x hx)
      · rcases hra.lt_or_eq with h | h
        · exact h
        · exact absurd (Complex.ext (by simp [h]) (by simp [him'])) (hne2 x hx)
  have hdisj : (fun x : ℝ => g x) '' Icc 0 a ∩
      ({w : ℂ | 0 < w.re ∧ w.re < a' ∧ b' / 2 < w.im} ∩ {w : ℂ | w.im < b'}) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro _ ⟨⟨x, hx, rfl⟩, hV', hW'⟩
    simp only [mem_setOf_eq] at hV' hW'
    obtain ⟨hre0, hrea, him⟩ := hV'
    obtain ⟨-, hcases⟩ := hbx x hx
    rcases hcases with h | h | h | h <;> linarith
  have himlt : ∀ x ∈ Icc (0 : ℝ) a, (g x).im < b' := by
    rcases (isPreconnected_iff_subset_of_disjoint.1 hpre) _ _ hV hW hsub hdisj with h | h
    · exfalso
      have h0' := h (mem_image_of_mem (fun x : ℝ => g x) (left_mem_Icc.2 ha.le))
      simp [h0] at h0'
    · intro x hx
      exact h (mem_image_of_mem (fun x : ℝ => g x) hx)
  -- Step B: the unrolled coordinate `s` on the U-shaped rest of the boundary
  set s : ℂ → ℝ := fun w => w.re + w.im * (2 * w.re / a' - 1) with hs
  have hscont : Continuous s := by rw [hs]; fun_prop
  have hU : ∀ x ∈ Icc (0 : ℝ) a, (0 ≤ (g x).re ∧ (g x).re ≤ a' ∧ 0 ≤ (g x).im) ∧
      (((g x).re = 0 ∧ s (g x) = -(g x).im) ∨ ((g x).im = 0 ∧ s (g x) = (g x).re) ∨
        ((g x).re = a' ∧ s (g x) = a' + (g x).im)) := by
    intro x hx
    obtain ⟨⟨hr0, hra, hi0, hib⟩, hcases⟩ := hbx x hx
    refine ⟨⟨hr0, hra, hi0⟩, ?_⟩
    rcases hcases with h | h | h | h
    · left
      refine ⟨h, ?_⟩
      simp only [hs, h]
      ring
    · right; right
      refine ⟨h, ?_⟩
      simp only [hs, h]
      field_simp
      ring
    · right; left
      refine ⟨h, ?_⟩
      simp only [hs, h]
      ring
    · exact absurd h (himlt x hx).ne
  have hinjsp : InjOn (fun x : ℝ => s (g x)) (Icc 0 a) := by
    intro x hx y hy hxy
    have hxy' : s (g x) = s (g y) := hxy
    obtain ⟨⟨hx1, hx2, hx3⟩, hxc⟩ := hU x hx
    obtain ⟨⟨hy1, hy2, hy3⟩, hyc⟩ := hU y hy
    have hgxy : g x = g y := by
      rcases hxc with ⟨hr, hs1⟩ | ⟨hi, hs1⟩ | ⟨hr, hs1⟩ <;>
        rcases hyc with ⟨hr', hs2⟩ | ⟨hi', hs2⟩ | ⟨hr', hs2⟩ <;>
        (rw [hs1, hs2] at hxy'; exact Complex.ext (by linarith) (by linarith))
    exact Complex.ofReal_inj.1 (hinj (hx_cl x hx) (hx_cl y hy) hgxy)
  have hspc : ContinuousOn (fun x : ℝ => s (g x)) (Icc 0 a) := hscont.comp_continuousOn hpc
  have hs0 : s 0 = 0 := by simp [hs]
  have hsa : s (a' : ℂ) = a' := by simp [hs]
  have hmono : StrictMonoOn (fun x : ℝ => s (g x)) (Icc 0 a) := by
    refine ContinuousOn.strictMonoOn_of_injOn_Icc ha.le ?_ hspc hinjsp
    show s (g ((0 : ℝ) : ℂ)) ≤ s (g (a : ℂ))
    rw [Complex.ofReal_zero, h0, h1, hs0, hsa]
    exact ha'.le
  -- conclusion
  intro x hx
  have hlo : s (g ((0 : ℝ) : ℂ)) ≤ s (g x) := hmono.monotoneOn (left_mem_Icc.2 ha.le) hx hx.1
  have hhi : s (g x) ≤ s (g (a : ℂ)) := hmono.monotoneOn hx (right_mem_Icc.2 ha.le) hx.2
  rw [Complex.ofReal_zero, h0, hs0] at hlo
  rw [h1, hsa] at hhi
  obtain ⟨⟨hx1, hx2, hx3⟩, hxc⟩ := hU x hx
  rcases hxc with ⟨hr, hs1⟩ | ⟨hi, hs1⟩ | ⟨hr, hs1⟩
  · rw [hs1] at hlo; linarith
  · exact hi
  · rw [hs1] at hhi; linarith

/-- **Bottom and top sides.**  Under the hypotheses of `rect_sideLines_of_homeo`, the closed
bottom side is mapped into `Im w = 0` and the closed top side into `Im w = b'`.  The top side is
handled by conjugating with the half-turns `z ↦ a + bi − z`, `w ↦ a' + b'i − w`, which exchange the
bottom and top sides and permute the vertices compatibly. -/
theorem rect_bottom_top_of_homeo {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a')
    (hb' : 0 < b') {g : ℂ → ℂ} (hopen : g '' rectangle a b = rectangle a' b')
    (hc : ContinuousOn g (closure (rectangle a b))) (hinj : InjOn g (closure (rectangle a b)))
    (himg : g '' closure (rectangle a b) = closure (rectangle a' b'))
    (h0 : g 0 = 0) (h1 : g (a : ℂ) = (a' : ℂ))
    (h2 : g ((a : ℂ) + (b : ℂ) * I) = (a' : ℂ) + (b' : ℂ) * I)
    (h3 : g ((b : ℂ) * I) = (b' : ℂ) * I) :
    (∀ x ∈ Icc (0 : ℝ) a, (g (x : ℂ)).im = 0) ∧
      (∀ x ∈ Icc (0 : ℝ) a, (g ((x : ℂ) + (b : ℂ) * I)).im = b') := by
  refine ⟨rect_bottom_of_homeo ha hb ha' hb' hopen hc hinj himg h0 h1 h2 h3, ?_⟩
  -- conjugate by the half-turns
  obtain ⟨hopen', hc', hinj', himg'⟩ :=
    rect_homeo_conj (φ := fun z => (a : ℂ) + (b : ℂ) * I - z)
      (ψ := fun w => (a' : ℂ) + (b' : ℂ) * I - w) (by fun_prop) (fun z => by simp)
      (fun z => rect_rot_mem_iff) (fun z => rect_rot_mem_closure_iff ha hb) (by fun_prop)
      (fun w => by simp) (fun w => rect_rot_mem_iff) (fun w => rect_rot_mem_closure_iff ha' hb')
      hopen hc hinj himg
  have hv0 : ((fun w => (a' : ℂ) + (b' : ℂ) * I - w) ∘ g ∘ fun z => (a : ℂ) + (b : ℂ) * I - z) 0
      = 0 := by
    show (a' : ℂ) + (b' : ℂ) * I - g ((a : ℂ) + (b : ℂ) * I - 0) = 0
    rw [sub_zero, h2, sub_self]
  have hv1 : ((fun w => (a' : ℂ) + (b' : ℂ) * I - w) ∘ g ∘ fun z => (a : ℂ) + (b : ℂ) * I - z)
      (a : ℂ) = (a' : ℂ) := by
    show (a' : ℂ) + (b' : ℂ) * I - g ((a : ℂ) + (b : ℂ) * I - a) = a'
    rw [show (a : ℂ) + (b : ℂ) * I - a = (b : ℂ) * I by ring, h3]
    ring
  have hv2 : ((fun w => (a' : ℂ) + (b' : ℂ) * I - w) ∘ g ∘ fun z => (a : ℂ) + (b : ℂ) * I - z)
      ((a : ℂ) + (b : ℂ) * I) = (a' : ℂ) + (b' : ℂ) * I := by
    show (a' : ℂ) + (b' : ℂ) * I - g ((a : ℂ) + (b : ℂ) * I - ((a : ℂ) + (b : ℂ) * I))
      = (a' : ℂ) + (b' : ℂ) * I
    rw [sub_self, h0, sub_zero]
  have hv3 : ((fun w => (a' : ℂ) + (b' : ℂ) * I - w) ∘ g ∘ fun z => (a : ℂ) + (b : ℂ) * I - z)
      ((b : ℂ) * I) = (b' : ℂ) * I := by
    show (a' : ℂ) + (b' : ℂ) * I - g ((a : ℂ) + (b : ℂ) * I - (b : ℂ) * I) = (b' : ℂ) * I
    rw [show (a : ℂ) + (b : ℂ) * I - (b : ℂ) * I = a by ring, h1]
    ring
  have htop := rect_bottom_of_homeo ha hb ha' hb' hopen' hc' hinj' himg' hv0 hv1 hv2 hv3
  intro x hx
  have h := htop (a - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  simp only [Function.comp_apply] at h
  rw [show (a : ℂ) + (b : ℂ) * I - ((a - x : ℝ) : ℂ) = (x : ℂ) + (b : ℂ) * I by push_cast; ring]
    at h
  simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, mul_one,
    zero_add] at h
  linarith

/-- **Sides go to sides.**  If `g` is continuous and injective on the closed rectangle
`closure R`, maps it onto `closure R'`, maps the open rectangle `R` onto `R'`, and sends the vertices
`0, a, a+bi, bi` to `0, a', a'+b'i, b'i`, then each closed side of `R` is mapped into the line of the
corresponding side of `R'`.

Route: `g` maps `∂R = closure R \ R` onto `∂R'`; the closed bottom side is an arc from `0` to `a'`
in `∂R'` avoiding the two top vertices, and the only such arc is the bottom side of `R'`; likewise
for the other three sides. -/
theorem rect_sideLines_of_homeo {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a')
    (hb' : 0 < b') {g : ℂ → ℂ} (hopen : g '' rectangle a b = rectangle a' b')
    (hc : ContinuousOn g (closure (rectangle a b))) (hinj : InjOn g (closure (rectangle a b)))
    (himg : g '' closure (rectangle a b) = closure (rectangle a' b'))
    (h0 : g 0 = 0) (h1 : g (a : ℂ) = (a' : ℂ))
    (h2 : g ((a : ℂ) + (b : ℂ) * I) = (a' : ℂ) + (b' : ℂ) * I)
    (h3 : g ((b : ℂ) * I) = (b' : ℂ) * I) :
    (∀ x ∈ Icc (0 : ℝ) a, (g (x : ℂ)).im = 0) ∧
      (∀ x ∈ Icc (0 : ℝ) a, (g ((x : ℂ) + (b : ℂ) * I)).im = b') ∧
      (∀ y ∈ Icc (0 : ℝ) b, (g ((y : ℂ) * I)).re = 0) ∧
      (∀ y ∈ Icc (0 : ℝ) b, (g ((a : ℂ) + (y : ℂ) * I)).re = a') := by
  obtain ⟨hbot, htop⟩ := rect_bottom_top_of_homeo ha hb ha' hb' hopen hc hinj himg h0 h1 h2 h3
  -- the transposition `τ z = i conj z` exchanges `rectangle a b` and `rectangle b a`, the bottom
  -- side of the latter being the left side of the former and its top side the right side
  obtain ⟨hopen', hc', hinj', himg'⟩ :=
    rect_homeo_conj (φ := fun z => I * conj z) (ψ := fun w => I * conj w) (by fun_prop)
      (fun z => by apply Complex.ext <;> simp) (fun z => rect_transpose_mem_iff)
      (fun z => rect_transpose_mem_closure_iff ha hb) (by fun_prop)
      (fun w => by apply Complex.ext <;> simp) (fun w => rect_transpose_mem_iff)
      (fun w => rect_transpose_mem_closure_iff ha' hb') hopen hc hinj himg
  have hv0 : ((fun w => I * conj w) ∘ g ∘ fun z => I * conj z) 0 = 0 := by
    simp [h0]
  have hv1 : ((fun w => I * conj w) ∘ g ∘ fun z => I * conj z) (b : ℂ) = (b' : ℂ) := by
    show I * conj (g (I * conj (b : ℂ))) = b'
    rw [show I * conj (b : ℂ) = (b : ℂ) * I by rw [Complex.conj_ofReal, mul_comm], h3]
    apply Complex.ext <;> simp
  have hv2 : ((fun w => I * conj w) ∘ g ∘ fun z => I * conj z) ((b : ℂ) + (a : ℂ) * I)
      = (b' : ℂ) + (a' : ℂ) * I := by
    show I * conj (g (I * conj ((b : ℂ) + (a : ℂ) * I))) = (b' : ℂ) + (a' : ℂ) * I
    rw [show I * conj ((b : ℂ) + (a : ℂ) * I) = (a : ℂ) + (b : ℂ) * I by
      apply Complex.ext <;> simp, h2]
    apply Complex.ext <;> simp
  have hv3 : ((fun w => I * conj w) ∘ g ∘ fun z => I * conj z) ((a : ℂ) * I) = (a' : ℂ) * I := by
    show I * conj (g (I * conj ((a : ℂ) * I))) = (a' : ℂ) * I
    rw [show I * conj ((a : ℂ) * I) = (a : ℂ) by apply Complex.ext <;> simp, h1]
    apply Complex.ext <;> simp
  obtain ⟨hleft, hright⟩ :=
    rect_bottom_top_of_homeo hb ha hb' ha' hopen' hc' hinj' himg' hv0 hv1 hv2 hv3
  refine ⟨hbot, htop, ?_, ?_⟩
  · intro y hy
    have h := hleft y hy
    simp only [Function.comp_apply] at h
    rw [show I * conj (y : ℂ) = (y : ℂ) * I by rw [Complex.conj_ofReal, mul_comm]] at h
    simpa using h
  · intro y hy
    have h := hright y hy
    simp only [Function.comp_apply] at h
    rw [show I * conj ((y : ℂ) + (a : ℂ) * I) = (a : ℂ) + (y : ℂ) * I by
      apply Complex.ext <;> simp] at h
    simpa using h

/-- **Rigidity of rectangles.**  A conformal map of `R(0, a, a+bi, bi)` onto `R(0, a', a'+b'i, b'i)`
that is continuous and injective on the closed rectangle, maps it onto the closed rectangle and
sends vertices to the corresponding vertices is `z ↦ (a'/a) z`, and `a'/a = b'/b`. -/
theorem rect_rigidity {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b')
    {g : ℂ → ℂ} (hg : IsConformalOnto g (rectangle a b) (rectangle a' b'))
    (hc : ContinuousOn g (closure (rectangle a b))) (hinj : InjOn g (closure (rectangle a b)))
    (himg : g '' closure (rectangle a b) = closure (rectangle a' b'))
    (h0 : g 0 = 0) (h1 : g (a : ℂ) = (a' : ℂ))
    (h2 : g ((a : ℂ) + (b : ℂ) * I) = (a' : ℂ) + (b' : ℂ) * I)
    (h3 : g ((b : ℂ) * I) = (b' : ℂ) * I) :
    a' / a = b' / b ∧ ∀ z ∈ closure (rectangle a b), g z = ((a' / a : ℝ) : ℂ) * z := by
  obtain ⟨hbot, htop, hleft, hright⟩ :=
    rect_sideLines_of_homeo ha hb ha' hb' hg.2.2 hc hinj himg h0 h1 h2 h3
  exact rect_rigidity_of_sideLines ha hb ha' hb' hg.1 hc hbot htop hleft hright

end LiZhongQC
