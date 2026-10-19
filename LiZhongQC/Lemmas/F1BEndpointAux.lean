import LiZhongQC.Lemmas.FoundationQuotient

/-! B2c auxiliary (existence side): Euclidean orientation facts for hyperbolic circles.
(a) the SL(2,ℝ) action maps a positively oriented `Circle.path` arc of a hyperbolic circle onto a
positively oriented `Circle.path` arc of the image circle, endpoints to endpoints.
(b), (c) live in F1BOrientation. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- A real interval of length strictly between `0` and `2π` exponentiates onto the
anticlockwise `Circle.path` between its endpoint images. -/
theorem ft1bx_exp_Icc_eq_range_path {u v : ℝ} (h0 : u < v) (h2 : v < u + 2 * π) :
    Circle.exp '' Icc u v = Set.range (Circle.path (Circle.exp u) (Circle.exp v)) := by
  have hangle : Circle.angleDiff (Circle.exp u) (Circle.exp v) = v - u := by
    have h1 : Circle.exp (Circle.angleDiff (Circle.exp u) (Circle.exp v)) = Circle.exp (v - u) := by
      have h := Circle.exp_angleDiff_mul (x := Circle.exp u) (y := Circle.exp v)
      have h' : Circle.exp (v - u) * Circle.exp u = Circle.exp v := by
        rw [← Circle.exp_add, sub_add_cancel]
      exact mul_right_cancel (h.trans h'.symm)
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h1
    have hn := Circle.angleDiff_nonneg (Circle.exp u) (Circle.exp v)
    have hl := Circle.angleDiff_lt_two_pi (Circle.exp u) (Circle.exp v)
    have hm1 : (m : ℝ) < 1 := by
      by_contra h
      have h' := not_lt.1 h
      nlinarith [Real.pi_pos]
    have hm2 : (-1 : ℝ) < m := by
      by_contra h
      have h' := not_lt.1 h
      nlinarith [Real.pi_pos]
    have hm0 : m = 0 := by
      have a : m < 1 := by exact_mod_cast hm1
      have b : -1 < m := by exact_mod_cast hm2
      omega
    rw [hm, hm0]
    simp
  have harg : ∃ k : ℤ, ((Circle.exp u : ℂ)).arg = u + k * (2 * π) := by
    have h := Circle.exp_arg (Circle.exp u)
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.1 h
    exact ⟨k, hk⟩
  obtain ⟨k, hk⟩ := harg
  rw [Circle.range_path, hangle, hk,
    show v - u + (u + k * (2 * π)) = v + k * (2 * π) by ring, ← Set.image_add_const_Icc,
    Set.image_image]
  congr 1
  funext t
  exact (Circle.periodic_exp.int_mul k t).symm

/-- An increasing continuous lift with period `2π` maps anticlockwise arcs onto
anticlockwise arcs. -/
theorem ft1bx_arc_image_of_lift (g : Circle → Circle) (φ : ℝ → ℝ) (hφc : Continuous φ)
    (hφm : StrictMono φ) (hφp : ∀ θ, φ (θ + 2 * π) = φ θ + 2 * π)
    (hg : ∀ θ, g (Circle.exp θ) = Circle.exp (φ θ)) {x y : Circle} (hxy : x ≠ y) :
    g '' Set.range (Circle.path x y) = Set.range (Circle.path (g x) (g y)) := by
  set α : ℝ := ((x : ℂ)).arg
  set L : ℝ := Circle.angleDiff x y
  have hL0 : 0 < L := Circle.angleDiff_pos hxy
  have hL2 : L < 2 * π := Circle.angleDiff_lt_two_pi x y
  have hx : Circle.exp α = x := Circle.exp_arg x
  have hy : Circle.exp (L + α) = y := by
    rw [Circle.exp_add, hx]
    exact Circle.exp_angleDiff_mul
  have himg : φ '' Icc α (L + α) = Icc (φ α) (φ (L + α)) :=
    hφc.continuousOn.image_Icc_of_monotoneOn (by linarith) (hφm.monotone.monotoneOn _)
  have h1 : φ α < φ (L + α) := hφm (by linarith)
  have h2 : φ (L + α) < φ α + 2 * π := by
    rw [← hφp]
    exact hφm (by linarith)
  rw [Circle.range_path, Set.image_image]
  have hcomp : (fun t => g (Circle.exp t)) = Circle.exp ∘ φ := funext fun t => hg t
  rw [hcomp, Set.image_comp, himg, ft1bx_exp_Icc_eq_range_path h1 h2, ← hg, ← hg, hx, hy]

/-- The Euclidean center of a hyperbolic circle, in coordinates. -/
theorem ft1bx_center_coe (c : UpperHalfPlane) (R : ℝ) :
    ((c.center R : UpperHalfPlane) : ℂ) = (c.re : ℂ) + ((c.im * Real.cosh R : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- Points of the Euclidean circle of a hyperbolic circle lie in the upper half-plane. -/
theorem ft1bx_circle_im_pos (c : UpperHalfPlane) {R : ℝ} (hR : 0 < R) (w : Circle) :
    0 < ((c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * (w : ℂ)).im := by
  rw [ft1bx_center_coe]
  have hw : |(w : ℂ).im| ≤ 1 := by
    have := Complex.abs_im_le_norm (w : ℂ)
    rwa [Circle.norm_coe] at this
  have hcs : Real.sinh R < Real.cosh R := Real.sinh_lt_cosh R
  have hs : 0 < Real.sinh R := Real.sinh_pos_iff.2 hR
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, zero_add, mul_one]
  have hw1 : -1 ≤ (w : ℂ).im := by linarith [neg_abs_le (w : ℂ).im]
  have hpos : 0 < c.im * Real.sinh R := mul_pos c.im_pos hs
  have h1 : c.im * Real.sinh R * (-1) ≤ c.im * Real.sinh R * (w : ℂ).im :=
    mul_le_mul_of_nonneg_left hw1 hpos.le
  have h2 : c.im * Real.sinh R < c.im * Real.cosh R := mul_lt_mul_of_pos_left hcs c.im_pos
  linarith

/-- Composition of the arc property. -/
theorem ft1bx_arc_comp (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {R : ℝ}
    (h₁ : ∀ (c : UpperHalfPlane) (x y : Circle), x ≠ y → ∃ x' y' : Circle, x' ≠ y' ∧
      (∀ τ : UpperHalfPlane, (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * x →
        ((γ₁ • τ : UpperHalfPlane) : ℂ) =
          ((γ₁ • c).center R : ℂ) + (((γ₁ • c).im * Real.sinh R : ℝ) : ℂ) * x') ∧
      (∀ τ : UpperHalfPlane, (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * y →
        ((γ₁ • τ : UpperHalfPlane) : ℂ) =
          ((γ₁ • c).center R : ℂ) + (((γ₁ • c).im * Real.sinh R : ℝ) : ℂ) * y') ∧
      (fun τ : UpperHalfPlane => γ₁ • τ) '' {τ : UpperHalfPlane | ∃ t : unitInterval,
        (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * (Circle.path x y t : ℂ)} =
        {τ : UpperHalfPlane | ∃ t : unitInterval, (τ : ℂ) = ((γ₁ • c).center R : ℂ) +
          (((γ₁ • c).im * Real.sinh R : ℝ) : ℂ) * (Circle.path x' y' t : ℂ)})
    (h₂ : ∀ (c : UpperHalfPlane) (x y : Circle), x ≠ y → ∃ x' y' : Circle, x' ≠ y' ∧
      (∀ τ : UpperHalfPlane, (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * x →
        ((γ₂ • τ : UpperHalfPlane) : ℂ) =
          ((γ₂ • c).center R : ℂ) + (((γ₂ • c).im * Real.sinh R : ℝ) : ℂ) * x') ∧
      (∀ τ : UpperHalfPlane, (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * y →
        ((γ₂ • τ : UpperHalfPlane) : ℂ) =
          ((γ₂ • c).center R : ℂ) + (((γ₂ • c).im * Real.sinh R : ℝ) : ℂ) * y') ∧
      (fun τ : UpperHalfPlane => γ₂ • τ) '' {τ : UpperHalfPlane | ∃ t : unitInterval,
        (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * (Circle.path x y t : ℂ)} =
        {τ : UpperHalfPlane | ∃ t : unitInterval, (τ : ℂ) = ((γ₂ • c).center R : ℂ) +
          (((γ₂ • c).im * Real.sinh R : ℝ) : ℂ) * (Circle.path x' y' t : ℂ)}) :
    ∀ (c : UpperHalfPlane) (x y : Circle), x ≠ y → ∃ x' y' : Circle, x' ≠ y' ∧
      (∀ τ : UpperHalfPlane, (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * x →
        (((γ₁ * γ₂) • τ : UpperHalfPlane) : ℂ) =
          (((γ₁ * γ₂) • c).center R : ℂ) + ((((γ₁ * γ₂) • c).im * Real.sinh R : ℝ) : ℂ) * x') ∧
      (∀ τ : UpperHalfPlane, (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * y →
        (((γ₁ * γ₂) • τ : UpperHalfPlane) : ℂ) =
          (((γ₁ * γ₂) • c).center R : ℂ) + ((((γ₁ * γ₂) • c).im * Real.sinh R : ℝ) : ℂ) * y') ∧
      (fun τ : UpperHalfPlane => (γ₁ * γ₂) • τ) '' {τ : UpperHalfPlane | ∃ t : unitInterval,
        (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * (Circle.path x y t : ℂ)} =
        {τ : UpperHalfPlane | ∃ t : unitInterval, (τ : ℂ) = (((γ₁ * γ₂) • c).center R : ℂ) +
          ((((γ₁ * γ₂) • c).im * Real.sinh R : ℝ) : ℂ) * (Circle.path x' y' t : ℂ)} := by
  intro c x y hxy
  obtain ⟨x₂, y₂, hxy₂, hx₂, hy₂, hset₂⟩ := h₂ c x y hxy
  obtain ⟨x₁, y₁, hxy₁, hx₁, hy₁, hset₁⟩ := h₁ (γ₂ • c) x₂ y₂ hxy₂
  refine ⟨x₁, y₁, hxy₁, fun τ hτ => ?_, fun τ hτ => ?_, ?_⟩
  · rw [mul_smul, mul_smul]
    exact hx₁ _ (hx₂ τ hτ)
  · rw [mul_smul, mul_smul]
    exact hy₁ _ (hy₂ τ hτ)
  · rw [mul_smul, ← hset₁, ← hset₂, Set.image_image]
    congr 1
    funext τ
    exact mul_smul γ₁ γ₂ τ

/-- An element acting as a positive affine map `z ↦ λ z + b` has the arc property with
unchanged circle parameters. -/
theorem ft1bx_arc_affine (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {R : ℝ} (hR : 0 < R)
    {l b : ℝ}
    (hγ : ∀ z : UpperHalfPlane, ((γ • z : UpperHalfPlane) : ℂ) = (l : ℂ) * z + b) :
    ∀ (c : UpperHalfPlane) (x y : Circle), x ≠ y → ∃ x' y' : Circle, x' ≠ y' ∧
      (∀ τ : UpperHalfPlane, (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * x →
        ((γ • τ : UpperHalfPlane) : ℂ) =
          ((γ • c).center R : ℂ) + (((γ • c).im * Real.sinh R : ℝ) : ℂ) * x') ∧
      (∀ τ : UpperHalfPlane, (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * y →
        ((γ • τ : UpperHalfPlane) : ℂ) =
          ((γ • c).center R : ℂ) + (((γ • c).im * Real.sinh R : ℝ) : ℂ) * y') ∧
      (fun τ : UpperHalfPlane => γ • τ) '' {τ : UpperHalfPlane | ∃ t : unitInterval,
        (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * (Circle.path x y t : ℂ)} =
        {τ : UpperHalfPlane | ∃ t : unitInterval, (τ : ℂ) = ((γ • c).center R : ℂ) +
          (((γ • c).im * Real.sinh R : ℝ) : ℂ) * (Circle.path x' y' t : ℂ)} := by
  intro c x y hxy
  have hc : ((γ • c : UpperHalfPlane) : ℂ) = (l : ℂ) * c + b := hγ c
  have hre : (γ • c).re = l * c.re + b := by
    have := congrArg Complex.re hc
    simpa using this
  have him : (γ • c).im = l * c.im := by
    have := congrArg Complex.im hc
    simpa using this
  have hC : ((γ • c).center R : ℂ) = (l : ℂ) * (c.center R : ℂ) + b := by
    rw [ft1bx_center_coe, ft1bx_center_coe, hre, him]
    push_cast
    ring
  have hr : (((γ • c).im * Real.sinh R : ℝ) : ℂ) = (l : ℂ) * ((c.im * Real.sinh R : ℝ) : ℂ) := by
    rw [him]
    push_cast
    ring
  have key : ∀ (τ : UpperHalfPlane) (w : ℂ),
      (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * w →
      ((γ • τ : UpperHalfPlane) : ℂ) =
        ((γ • c).center R : ℂ) + (((γ • c).im * Real.sinh R : ℝ) : ℂ) * w := by
    intro τ w hτ
    rw [hγ, hτ, hC, hr]
    ring
  refine ⟨x, y, hxy, fun τ hτ => key τ x hτ, fun τ hτ => key τ y hτ, ?_⟩
  ext τ
  constructor
  · rintro ⟨σ, ⟨t, ht⟩, rfl⟩
    exact ⟨t, key σ _ ht⟩
  · rintro ⟨t, ht⟩
    let σ : UpperHalfPlane := ⟨(c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) *
      (Circle.path x y t : ℂ), ft1bx_circle_im_pos c hR _⟩
    refine ⟨σ, ⟨t, rfl⟩, ?_⟩
    apply UpperHalfPlane.ext
    rw [key σ _ rfl, ht]

/-- The arc property only depends on the action. -/
theorem ft1bx_arc_congr {γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ} {R : ℝ}
    (h : ∀ z : UpperHalfPlane, γ • z = γ' • z)
    (h' : ∀ (c : UpperHalfPlane) (x y : Circle), x ≠ y → ∃ x' y' : Circle, x' ≠ y' ∧
      (∀ τ : UpperHalfPlane, (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * x →
        ((γ' • τ : UpperHalfPlane) : ℂ) =
          ((γ' • c).center R : ℂ) + (((γ' • c).im * Real.sinh R : ℝ) : ℂ) * x') ∧
      (∀ τ : UpperHalfPlane, (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * y →
        ((γ' • τ : UpperHalfPlane) : ℂ) =
          ((γ' • c).center R : ℂ) + (((γ' • c).im * Real.sinh R : ℝ) : ℂ) * y') ∧
      (fun τ : UpperHalfPlane => γ' • τ) '' {τ : UpperHalfPlane | ∃ t : unitInterval,
        (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * (Circle.path x y t : ℂ)} =
        {τ : UpperHalfPlane | ∃ t : unitInterval, (τ : ℂ) = ((γ' • c).center R : ℂ) +
          (((γ' • c).im * Real.sinh R : ℝ) : ℂ) * (Circle.path x' y' t : ℂ)}) :
    ∀ (c : UpperHalfPlane) (x y : Circle), x ≠ y → ∃ x' y' : Circle, x' ≠ y' ∧
      (∀ τ : UpperHalfPlane, (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * x →
        ((γ • τ : UpperHalfPlane) : ℂ) =
          ((γ • c).center R : ℂ) + (((γ • c).im * Real.sinh R : ℝ) : ℂ) * x') ∧
      (∀ τ : UpperHalfPlane, (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * y →
        ((γ • τ : UpperHalfPlane) : ℂ) =
          ((γ • c).center R : ℂ) + (((γ • c).im * Real.sinh R : ℝ) : ℂ) * y') ∧
      (fun τ : UpperHalfPlane => γ • τ) '' {τ : UpperHalfPlane | ∃ t : unitInterval,
        (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * (Circle.path x y t : ℂ)} =
        {τ : UpperHalfPlane | ∃ t : unitInterval, (τ : ℂ) = ((γ • c).center R : ℂ) +
          (((γ • c).im * Real.sinh R : ℝ) : ℂ) * (Circle.path x' y' t : ℂ)} := by
  simp only [h]
  exact h'

/-- A real positive affine map is realized by an element of `SL(2, ℝ)`. -/
theorem ft1bx_exists_affine {l : ℝ} (hl : 0 < l) (b : ℝ) :
    ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ z : UpperHalfPlane,
      ((γ • z : UpperHalfPlane) : ℂ) = (l : ℂ) * z + b := by
  set s : ℝ := Real.sqrt l
  have hs : 0 < s := Real.sqrt_pos.2 hl
  have hs2 : s * s = l := Real.mul_self_sqrt hl.le
  let γ : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨!![s, b / s; 0, s⁻¹], by
    rw [Matrix.det_fin_two_of, mul_inv_cancel₀ hs.ne']; ring⟩
  refine ⟨γ, fun z => ?_⟩
  have e00 : (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = s := rfl
  have e01 : (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = b / s := rfl
  have e10 : (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := rfl
  have e11 : (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = s⁻¹ := rfl
  rw [h36t_coe_smul, e00, e01, e10, e11]
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hlC : (l : ℂ) = (s : ℂ) * s := by rw [← hs2]; push_cast; ring
  push_cast
  rw [hlC]
  field_simp
  ring

/-- The boundary angle map of the inversion on a hyperbolic circle is increasing: its lift
`θ ↦ θ - 2 arg (C + r e^{iθ})` has derivative `(|C|² - r²)/|Z|² > 0`. -/
theorem ft1bx_inversion_lift (c : UpperHalfPlane) {R : ℝ} (hR : 0 < R) :
    Continuous (fun θ : ℝ => θ - 2 * Complex.arg ((c.center R : ℂ) +
        ((c.im * Real.sinh R : ℝ) : ℂ) * Complex.exp (θ * Complex.I))) ∧
    StrictMono (fun θ : ℝ => θ - 2 * Complex.arg ((c.center R : ℂ) +
        ((c.im * Real.sinh R : ℝ) : ℂ) * Complex.exp (θ * Complex.I))) := by
  set C : ℂ := (c.center R : ℂ)
  set r : ℝ := c.im * Real.sinh R
  let Z : ℝ → ℂ := fun θ => C + (r : ℂ) * Complex.exp (θ * Complex.I)
  have hZim : ∀ θ : ℝ, 0 < (Z θ).im := fun θ => by
    have h := ft1bx_circle_im_pos c hR (Circle.exp θ)
    rwa [Circle.coe_exp] at h
  have hslit : ∀ θ : ℝ, Z θ ∈ Complex.slitPlane := fun θ => Or.inr (hZim θ).ne'
  have hZc : Continuous Z := by
    exact continuous_const.add (continuous_const.mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)))
  have hargc : Continuous (fun θ => Complex.arg (Z θ)) :=
    continuous_iff_continuousAt.2 fun θ =>
      (Complex.continuousAt_arg (hslit θ)).comp hZc.continuousAt
  refine ⟨continuous_id.sub (continuous_const.mul hargc), ?_⟩
  have hZd : ∀ θ : ℝ, HasDerivAt Z ((r : ℂ) * (Complex.exp (θ * Complex.I) * Complex.I)) θ := by
    intro θ
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I θ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I
    exact ((h1.cexp).const_mul (r : ℂ)).const_add C
  have hargd : ∀ θ : ℝ, HasDerivAt (fun t => Complex.arg (Z t))
      (((r : ℂ) * (Complex.exp (θ * Complex.I) * Complex.I)) / Z θ).im θ := by
    intro θ
    have h := (hZd θ).clog_real (hslit θ)
    have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ h
    simp only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] at h2
    exact h2
  have hφd : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => t - 2 * Complex.arg (Z t))
      (1 - 2 * (((r : ℂ) * (Complex.exp (θ * Complex.I) * Complex.I)) / Z θ).im) θ :=
    fun θ => (hasDerivAt_id θ).sub ((hargd θ).const_mul 2)
  apply strictMono_of_deriv_pos
  intro θ
  rw [(hφd θ).deriv]
  -- coordinates
  have hC : C = (c.re : ℂ) + ((c.im * Real.cosh R : ℝ) : ℂ) * Complex.I := ft1bx_center_coe c R
  have hZre : (Z θ).re = c.re + r * Real.cos θ := by
    simp only [Z, hC, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  have hZim' : (Z θ).im = c.im * Real.cosh R + r * Real.sin θ := by
    simp only [Z, hC, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  have hns : 0 < Complex.normSq (Z θ) := Complex.normSq_pos.2 (fun h => by
    have := hZim θ; rw [h] at this; simp at this)
  have hDre : ((r : ℂ) * (Complex.exp (θ * Complex.I) * Complex.I)).re = -(r * Real.sin θ) := by
    simp [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hDim : ((r : ℂ) * (Complex.exp (θ * Complex.I) * Complex.I)).im = r * Real.cos θ := by
    simp [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [Complex.div_im, hDre, hDim, hZre, hZim']
  have hnsZ : Complex.normSq (Z θ) = (c.re + r * Real.cos θ) ^ 2 +
      (c.im * Real.cosh R + r * Real.sin θ) ^ 2 := by
    rw [Complex.normSq_apply, hZre, hZim']
    ring
  rw [hnsZ] at hns ⊢
  have hcs : Real.cosh R ^ 2 - Real.sinh R ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq R
  have htrig : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hkey : 2 * (r * Real.cos θ * (c.re + r * Real.cos θ) -
      -(r * Real.sin θ) * (c.im * Real.cosh R + r * Real.sin θ)) <
      (c.re + r * Real.cos θ) ^ 2 + (c.im * Real.cosh R + r * Real.sin θ) ^ 2 := by
    have hpos : 0 < c.re ^ 2 + c.im ^ 2 := by nlinarith [c.im_pos, sq_nonneg c.re]
    have : (c.re + r * Real.cos θ) ^ 2 + (c.im * Real.cosh R + r * Real.sin θ) ^ 2 -
        2 * (r * Real.cos θ * (c.re + r * Real.cos θ) -
          -(r * Real.sin θ) * (c.im * Real.cosh R + r * Real.sin θ)) =
        c.re ^ 2 + c.im ^ 2 := by
      simp only [r]
      linear_combination c.im ^ 2 * hcs - (c.im * Real.sinh R) ^ 2 * htrig
    linarith
  rw [← sub_div]
  have h2 : 2 * ((r * Real.cos θ * (c.re + r * Real.cos θ) -
      -(r * Real.sin θ) * (c.im * Real.cosh R + r * Real.sin θ)) /
      ((c.re + r * Real.cos θ) ^ 2 + (c.im * Real.cosh R + r * Real.sin θ) ^ 2)) < 1 := by
    rw [mul_div_assoc', div_lt_one hns]
    exact hkey
  linarith

/-- The inversion `z ↦ -1/z` has the arc property. -/
theorem ft1bx_arc_inversion (σ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {R : ℝ} (hR : 0 < R)
    (hσ : ∀ z : UpperHalfPlane, ((σ • z : UpperHalfPlane) : ℂ) = -1 / (z : ℂ)) :
    ∀ (c : UpperHalfPlane) (x y : Circle), x ≠ y → ∃ x' y' : Circle, x' ≠ y' ∧
      (∀ τ : UpperHalfPlane, (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * x →
        ((σ • τ : UpperHalfPlane) : ℂ) =
          ((σ • c).center R : ℂ) + (((σ • c).im * Real.sinh R : ℝ) : ℂ) * x') ∧
      (∀ τ : UpperHalfPlane, (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * y →
        ((σ • τ : UpperHalfPlane) : ℂ) =
          ((σ • c).center R : ℂ) + (((σ • c).im * Real.sinh R : ℝ) : ℂ) * y') ∧
      (fun τ : UpperHalfPlane => σ • τ) '' {τ : UpperHalfPlane | ∃ t : unitInterval,
        (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * (Circle.path x y t : ℂ)} =
        {τ : UpperHalfPlane | ∃ t : unitInterval, (τ : ℂ) = ((σ • c).center R : ℂ) +
          (((σ • c).im * Real.sinh R : ℝ) : ℂ) * (Circle.path x' y' t : ℂ)} := by
  intro c x y hxy
  set C : ℂ := (c.center R : ℂ) with hCdef
  set r : ℝ := c.im * Real.sinh R with hrdef
  set N : ℝ := Complex.normSq (c : ℂ) with hNdef
  have hN : 0 < N := Complex.normSq_pos.2 (UpperHalfPlane.ne_zero c)
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hr : 0 < r := mul_pos c.im_pos (Real.sinh_pos_iff.2 hR)
  have hZim : ∀ w : Circle, 0 < (C + (r : ℂ) * (w : ℂ)).im := fun w => ft1bx_circle_im_pos c hR w
  have hZ : ∀ w : Circle, C + (r : ℂ) * (w : ℂ) ≠ 0 := fun w h => by
    have := hZim w; rw [h] at this; simp at this
  let g : Circle → Circle := fun w => w * Circle.ofConjDivSelf _ (hZ w)
  have hgc : ∀ w : Circle, ((g w : Circle) : ℂ) =
      (w : ℂ) * (conj (C + (r : ℂ) * (w : ℂ)) / (C + (r : ℂ) * (w : ℂ))) := fun w => rfl
  -- the image circle
  have hσc : ((σ • c : UpperHalfPlane) : ℂ) = -1 / (c : ℂ) := hσ c
  have hre : (σ • c).re = -c.re / N := by
    have := congrArg Complex.re hσc
    simpa [Complex.div_re, hNdef] using this
  have him : (σ • c).im = c.im / N := by
    have := congrArg Complex.im hσc
    simp [Complex.div_im] at this
    rw [this, hNdef]
    ring
  have hC' : ((σ • c).center R : ℂ) = -conj C / N := by
    rw [ft1bx_center_coe, hre, him, hCdef, ft1bx_center_coe]
    apply Complex.ext <;> simp [Complex.div_re, Complex.div_im] <;> field_simp
  have hr' : (((σ • c).im * Real.sinh R : ℝ) : ℂ) = (r : ℂ) / N := by
    rw [him, hrdef]
    push_cast
    ring
  have hCnorm : Complex.normSq C = N + r ^ 2 := by
    rw [hCdef, ft1bx_center_coe, hNdef, hrdef, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, Complex.add_im, Complex.mul_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    have := Real.cosh_sq_sub_sinh_sq R
    linear_combination c.im ^ 2 * this
  -- the inversion on the circle
  have himage : ∀ w : Circle, -1 / (C + (r : ℂ) * (w : ℂ)) =
      ((σ • c).center R : ℂ) + (((σ • c).im * Real.sinh R : ℝ) : ℂ) * ((g w : Circle) : ℂ) := by
    intro w
    rw [hC', hr', hgc]
    have hu : (w : ℂ) * conj (w : ℂ) = 1 := by
      rw [Complex.mul_conj, Circle.normSq_coe]; simp
    have hZw := hZ w
    have e1 : -conj C * (C + (r : ℂ) * (w : ℂ)) + (r : ℂ) * (w : ℂ) * conj (C + (r : ℂ) * (w : ℂ)) =
        -(N : ℂ) := by
      have hcc : conj C * C = (Complex.normSq C : ℂ) := (Complex.normSq_eq_conj_mul_self).symm
      calc -conj C * (C + (r : ℂ) * (w : ℂ)) + (r : ℂ) * (w : ℂ) * conj (C + (r : ℂ) * (w : ℂ))
          = -(conj C * C) + (r : ℂ) ^ 2 * ((w : ℂ) * conj (w : ℂ)) := by
            simp only [map_add, map_mul, Complex.conj_ofReal]
            ring
        _ = -(N : ℂ) := by
            rw [hcc, hu, hCnorm]
            push_cast
            ring
    calc -1 / (C + (r : ℂ) * (w : ℂ)) = -(N : ℂ) / ((N : ℂ) * (C + (r : ℂ) * (w : ℂ))) := by
          field_simp
      _ = (-conj C * (C + (r : ℂ) * (w : ℂ)) +
            (r : ℂ) * (w : ℂ) * conj (C + (r : ℂ) * (w : ℂ))) /
            ((N : ℂ) * (C + (r : ℂ) * (w : ℂ))) := by rw [e1]
      _ = -conj C / N + (r : ℂ) / N *
            ((w : ℂ) * (conj (C + (r : ℂ) * (w : ℂ)) / (C + (r : ℂ) * (w : ℂ)))) := by
          field_simp
  -- the angle lift of `g`
  obtain ⟨hφc, hφm⟩ := ft1bx_inversion_lift c hR
  have hφp : ∀ θ : ℝ, (θ + 2 * π) - 2 * Complex.arg (C + (r : ℂ) *
      Complex.exp (((θ + 2 * π : ℝ) : ℂ) * Complex.I)) =
      (θ - 2 * Complex.arg (C + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) + 2 * π := by
    intro θ
    have : Complex.exp (((θ + 2 * π : ℝ) : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) := by
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    rw [this]
    ring
  have hg : ∀ θ : ℝ, g (Circle.exp θ) = Circle.exp (θ - 2 * Complex.arg (C + (r : ℂ) *
      Complex.exp ((θ : ℂ) * Complex.I))) := by
    intro θ
    apply Circle.ext
    rw [hgc, Circle.coe_exp, Circle.coe_exp]
    set Z : ℂ := C + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hZdef
    have hZ0 : Z ≠ 0 := by
      have := hZ (Circle.exp θ)
      rwa [Circle.coe_exp] at this
    have hnorm : (‖Z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hZ0)
    have hpol : Z = (‖Z‖ : ℂ) * Complex.exp ((Complex.arg Z : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I Z).symm
    have hconj : conj Z = (‖Z‖ : ℂ) * Complex.exp (-((Complex.arg Z : ℂ) * Complex.I)) := by
      conv_lhs => rw [hpol]
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
        Complex.conj_I]
      ring_nf
    have hratio : conj Z / Z = Complex.exp (-(2 * (Complex.arg Z : ℂ) * Complex.I)) := by
      rw [hconj]
      generalize hn : (‖Z‖ : ℂ) = n at hpol hnorm ⊢
      generalize ha : (Complex.arg Z : ℂ) = a at hpol ⊢
      conv_lhs => rw [hpol]
      rw [mul_div_mul_left _ _ hnorm, ← Complex.exp_sub]
      congr 1
      ring
    rw [hratio, ← Complex.exp_add]
    push_cast
    ring_nf
  have hlift := ft1bx_arc_image_of_lift g _ hφc hφm (fun θ => hφp θ) (fun θ => hg θ) hxy
  -- assemble
  have hpt : ∀ (τ : UpperHalfPlane) (w : Circle), (τ : ℂ) = C + (r : ℂ) * (w : ℂ) →
      ((σ • τ : UpperHalfPlane) : ℂ) =
        ((σ • c).center R : ℂ) + (((σ • c).im * Real.sinh R : ℝ) : ℂ) * ((g w : Circle) : ℂ) := by
    intro τ w hτ
    rw [hσ, hτ, himage]
  have hginj : Function.Injective g := by
    intro w w' hww
    let τ : UpperHalfPlane := ⟨C + (r : ℂ) * (w : ℂ), hZim w⟩
    let τ' : UpperHalfPlane := ⟨C + (r : ℂ) * (w' : ℂ), hZim w'⟩
    have h1 : σ • τ = σ • τ' := by
      apply UpperHalfPlane.ext
      rw [hpt τ w rfl, hpt τ' w' rfl, hww]
    have h2 : τ = τ' := smul_left_cancel σ h1
    have h3 : C + (r : ℂ) * (w : ℂ) = C + (r : ℂ) * (w' : ℂ) := congrArg UpperHalfPlane.coe h2
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    apply Circle.ext
    exact mul_left_cancel₀ hrC (add_left_cancel h3)
  refine ⟨g x, g y, hginj.ne hxy, fun τ hτ => hpt τ x hτ, fun τ hτ => hpt τ y hτ, ?_⟩
  ext τ
  constructor
  · rintro ⟨ρ₀, ⟨t, ht⟩, rfl⟩
    have hmem : g (Circle.path x y t) ∈ Set.range (Circle.path (g x) (g y)) := by
      rw [← hlift]
      exact ⟨_, ⟨t, rfl⟩, rfl⟩
    obtain ⟨s, hs⟩ := hmem
    exact ⟨s, by rw [hpt ρ₀ _ ht, hs]⟩
  · rintro ⟨s, hs⟩
    have hmem : Circle.path (g x) (g y) s ∈ g '' Set.range (Circle.path x y) := by
      rw [hlift]
      exact ⟨s, rfl⟩
    obtain ⟨_, ⟨t, rfl⟩, hts⟩ := hmem
    let ρ₀ : UpperHalfPlane := ⟨C + (r : ℂ) * (Circle.path x y t : ℂ), hZim _⟩
    refine ⟨ρ₀, ⟨t, rfl⟩, ?_⟩
    apply UpperHalfPlane.ext
    rw [hpt ρ₀ _ rfl, hts, hs]

/-- The inversion `z ↦ -1/z` is realized by an element of `SL(2, ℝ)`. -/
theorem ft1bx_exists_inversion : ∃ σ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
    ∀ z : UpperHalfPlane, ((σ • z : UpperHalfPlane) : ℂ) = -1 / (z : ℂ) := by
  let σ : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨!![0, -1; 1, 0], by
    rw [Matrix.det_fin_two_of]; ring⟩
  refine ⟨σ, fun z => ?_⟩
  have e00 : (σ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 0 := rfl
  have e01 : (σ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -1 := rfl
  have e10 : (σ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 1 := rfl
  have e11 : (σ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 0 := rfl
  rw [h36t_coe_smul, e00, e01, e10, e11]
  push_cast
  ring

/-- Every element of `SL(2, ℝ)` has the arc property: affine ∘ inversion ∘ affine. -/
theorem ft1bx_arc_all (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {R : ℝ} (hR : 0 < R) :
    ∀ (c : UpperHalfPlane) (x y : Circle), x ≠ y → ∃ x' y' : Circle, x' ≠ y' ∧
      (∀ τ : UpperHalfPlane, (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * x →
        ((γ • τ : UpperHalfPlane) : ℂ) =
          ((γ • c).center R : ℂ) + (((γ • c).im * Real.sinh R : ℝ) : ℂ) * x') ∧
      (∀ τ : UpperHalfPlane, (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * y →
        ((γ • τ : UpperHalfPlane) : ℂ) =
          ((γ • c).center R : ℂ) + (((γ • c).im * Real.sinh R : ℝ) : ℂ) * y') ∧
      (fun τ : UpperHalfPlane => γ • τ) '' {τ : UpperHalfPlane | ∃ t : unitInterval,
        (τ : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * (Circle.path x y t : ℂ)} =
        {τ : UpperHalfPlane | ∃ t : unitInterval, (τ : ℂ) = ((γ • c).center R : ℂ) +
          (((γ • c).im * Real.sinh R : ℝ) : ℂ) * (Circle.path x' y' t : ℂ)} := by
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 1 := by
    have := γ.det_coe
    rwa [Matrix.det_fin_two] at this
  set a := (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0
  set b := (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 1
  set c := (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0
  set d := (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1
  by_cases hc : c = 0
  · have hdetC : (a : ℂ) * d = 1 := by
      rw [hc, mul_zero, sub_zero] at hdet
      exact_mod_cast hdet
    have hd : (d : ℂ) ≠ 0 := fun h => by rw [h, mul_zero] at hdetC; exact zero_ne_one hdetC
    have hγf : ∀ z : UpperHalfPlane, ((γ • z : UpperHalfPlane) : ℂ) =
        ((a ^ 2 : ℝ) : ℂ) * z + ((a * b : ℝ) : ℂ) := by
      intro z
      rw [h36t_coe_smul]
      change ((a : ℂ) * z + b) / ((c : ℂ) * z + d) = _
      rw [hc]
      push_cast
      rw [div_eq_iff (by simpa using hd)]
      linear_combination (-((a : ℂ) * z + b)) * hdetC
    exact ft1bx_arc_affine γ hR hγf
  · have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have hdetC : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
    have hc2 : 0 < 1 / c ^ 2 := one_div_pos.2 (lt_of_le_of_ne (sq_nonneg c) (Ne.symm (pow_ne_zero 2 hc)))
    obtain ⟨A₁, hA₁⟩ := ft1bx_exists_affine one_pos (d / c)
    obtain ⟨A₂, hA₂⟩ := ft1bx_exists_affine hc2 (a / c)
    obtain ⟨σ, hσ⟩ := ft1bx_exists_inversion
    have hcomp := ft1bx_arc_comp A₂ (σ * A₁) (ft1bx_arc_affine A₂ hR hA₂)
      (ft1bx_arc_comp σ A₁ (ft1bx_arc_inversion σ hR hσ) (ft1bx_arc_affine A₁ hR hA₁))
    refine ft1bx_arc_congr (fun z => ?_) hcomp
    apply UpperHalfPlane.ext
    rw [mul_smul, mul_smul, hA₂, hσ, hA₁, h36t_coe_smul]
    change ((a : ℂ) * z + b) / ((c : ℂ) * z + d) = _
    have hcz : (c : ℂ) * z + d ≠ 0 := fun h => by
      have := congrArg Complex.im h
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero, Complex.zero_im] at this
      exact hc (by
        rcases mul_eq_zero.1 this with h1 | h1
        · exact h1
        · exact absurd h1 z.im_pos.ne')
    have h1 : (((1 : ℝ) : ℂ) * (z : ℂ) + ((d / c : ℝ) : ℂ)) = ((c : ℂ) * z + d) / c := by
      push_cast
      field_simp
    have h2 : ((1 / c ^ 2 : ℝ) : ℂ) * (-1 / (((c : ℂ) * z + d) / c)) + ((a / c : ℝ) : ℂ) =
        ((a : ℂ) * ((c : ℂ) * z + d) - 1) / ((c : ℂ) * ((c : ℂ) * z + d)) := by
      push_cast
      field_simp
      ring
    have h3 : (a : ℂ) * ((c : ℂ) * z + d) - 1 = (c : ℂ) * ((a : ℂ) * z + b) := by
      linear_combination hdetC
    rw [h1, h2, h3, mul_div_mul_left _ _ hcC]

/-- (a) Möbius preserves positive orientation of hyperbolic circle arcs. -/
theorem ft1bx_smul_circle_arc (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {R : ℝ} (hR : 0 < R)
    (c : UpperHalfPlane) (x y : Circle) (hxy : x ≠ y) (p : unitInterval → UpperHalfPlane)
    (hp : ∀ t, (p t : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * (Circle.path x y t : ℂ)) :
    ∃ x' y' : Circle, x' ≠ y' ∧
      ((γ • p 0 : UpperHalfPlane) : ℂ) =
        ((γ • c).center R : ℂ) + (((γ • c).im * Real.sinh R : ℝ) : ℂ) * (x' : ℂ) ∧
      ((γ • p 1 : UpperHalfPlane) : ℂ) =
        ((γ • c).center R : ℂ) + (((γ • c).im * Real.sinh R : ℝ) : ℂ) * (y' : ℂ) ∧
      Set.range (fun t => γ • p t) = {τ : UpperHalfPlane | ∃ t : unitInterval,
        (τ : ℂ) = ((γ • c).center R : ℂ) +
          (((γ • c).im * Real.sinh R : ℝ) : ℂ) * (Circle.path x' y' t : ℂ)} := by
  obtain ⟨x', y', hxy', hx', hy', hset⟩ := ft1bx_arc_all γ hR c x y hxy
  refine ⟨x', y', hxy', hx' (p 0) ?_, hy' (p 1) ?_, ?_⟩
  · rw [hp, (Circle.path x y).source]
  · rw [hp, (Circle.path x y).target]
  · rw [← hset]
    ext τ
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨p t, ⟨t, hp t⟩, rfl⟩
    · rintro ⟨ρ, ⟨t, ht⟩, rfl⟩
      refine ⟨t, ?_⟩
      show γ • p t = γ • ρ
      rw [show p t = ρ from UpperHalfPlane.ext (by rw [hp t, ht])]

end LiZhongQC
