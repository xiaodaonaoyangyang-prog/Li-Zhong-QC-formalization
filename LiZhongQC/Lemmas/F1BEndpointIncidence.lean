import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.F1BGraphBasic
import LiZhongQC.Lemmas.F1BExposedGeometry
import LiZhongQC.Lemmas.F1BEndpointAux
import LiZhongQC.Lemmas.F1BOrientation

/-! F1 B2c: oriented endpoint incidence of the exposed arcs of the central orbit circle.

Existence. At the end (start) of an arc, the frontier continues forwards (backwards) along an active
orbit circle: along the central circle when it is the only active one, and otherwise along the
second active circle, by the opposite orientation of the two crossing arcs (F1BOrientation) and the
transversality of equal-radius circles (`hpair`). The continuation is covered by translated arcs
(`ft1gb_translate_central_frontier`); local finiteness and closedness give a translated arc through
the endpoint, interior rigidity makes it an endpoint of that arc, and preservation of positive
Circle.path orientation by the SL action (F1BEndpointAux) picks the correct endpoint.
Uniqueness. A central translate cannot leave a crossing point (forward and backward central germs
lie on opposite sides of the second circle), so every outgoing arc lies on the same active circle;
freeness gives the group element up to sign and two arcs with a common start coincide.
The header of `ft1gb_oriented_endpoint_incidence` is byte-identical to the frozen v3 sub-stub
(B2c_header_v3.txt, 9ee098bf). -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Values of `Circle.path` as rotations of the start point. -/
theorem s36b2c_path_eq (x y : Circle) (t : unitInterval) :
    Circle.path x y t = x * Circle.exp ((t : ℝ) * Circle.angleDiff x y) := by
  rw [Circle.path_apply, Path.segment_apply, AffineMap.lineMap_apply_ring', Circle.exp_add]
  simp only [Circle.exp_arg]
  rw [mul_comm]
  congr 2
  ring

/-- Small forward rotations of the start point lie in the arc interior. -/
theorem s36b2c_path_fwd {x y : Circle} (hxy : x ≠ y) {s : ℝ} (hs : 0 < s)
    (hsD : s < Circle.angleDiff x y) :
    ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ Circle.path x y t = x * Circle.exp s := by
  have hD := Circle.angleDiff_pos hxy
  refine ⟨⟨s / Circle.angleDiff x y, div_nonneg hs.le hD.le,
    (div_le_one hD).2 hsD.le⟩, div_pos hs hD, (div_lt_one hD).2 hsD, ?_⟩
  rw [s36b2c_path_eq]
  congr 2
  show s / Circle.angleDiff x y * Circle.angleDiff x y = s
  field_simp

/-- Small backward rotations of the end point lie in the arc interior. -/
theorem s36b2c_path_bwd {x y : Circle} (hxy : x ≠ y) {s : ℝ} (hs : 0 < s)
    (hsD : s < Circle.angleDiff x y) :
    ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ Circle.path x y t = y * Circle.exp (-s) := by
  have hD := Circle.angleDiff_pos hxy
  refine ⟨⟨1 - s / Circle.angleDiff x y, by
      have := (div_lt_one hD).2 hsD
      linarith, by
      have := div_pos hs hD
      linarith⟩, by
      have := (div_lt_one hD).2 hsD
      show 0 < 1 - s / Circle.angleDiff x y
      linarith, by
      have := div_pos hs hD
      show 1 - s / Circle.angleDiff x y < 1
      linarith, ?_⟩
  have hy : y = Circle.exp (Circle.angleDiff x y) * x := Circle.exp_angleDiff_mul.symm
  rw [s36b2c_path_eq]
  conv_rhs => rw [hy, mul_comm (Circle.exp _) x, mul_assoc, ← Circle.exp_add]
  congr 2
  show (1 - s / Circle.angleDiff x y) * Circle.angleDiff x y = Circle.angleDiff x y + -s
  field_simp
  ring

/-- Small forward rotations of the end point are not on the arc. -/
theorem s36b2c_path_not_fwd {x y : Circle} {s : ℝ} (hs : 0 < s)
    (hsD : s < 2 * π - Circle.angleDiff x y) (t : unitInterval) :
    Circle.path x y t ≠ y * Circle.exp s := by
  intro h
  have hy : y = Circle.exp (Circle.angleDiff x y) * x := Circle.exp_angleDiff_mul.symm
  rw [s36b2c_path_eq] at h
  have h' : x * Circle.exp ((t : ℝ) * Circle.angleDiff x y) =
      x * Circle.exp (Circle.angleDiff x y + s) := by
    rw [h, Circle.exp_add, ← mul_assoc, mul_comm x, ← hy]
  have h2 := mul_left_cancel h'
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h2
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hD0 := Circle.angleDiff_nonneg x y
  have hle : (t : ℝ) * Circle.angleDiff x y ≤ Circle.angleDiff x y := by nlinarith
  have hge : 0 ≤ (t : ℝ) * Circle.angleDiff x y := by positivity
  have hpi := Real.pi_pos
  rcases lt_trichotomy m 0 with hm0 | hm0 | hm0
  · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hm0
    nlinarith
  · subst hm0
    simp at hm
    linarith
  · have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    nlinarith

/-- Small backward rotations of the start point are not on the arc. -/
theorem s36b2c_path_not_bwd {x y : Circle} {s : ℝ} (hs : 0 < s)
    (hsD : s < 2 * π - Circle.angleDiff x y) (t : unitInterval) :
    Circle.path x y t ≠ x * Circle.exp (-s) := by
  intro h
  rw [s36b2c_path_eq] at h
  have h2 := mul_left_cancel h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h2
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hD0 := Circle.angleDiff_nonneg x y
  have hle : (t : ℝ) * Circle.angleDiff x y ≤ Circle.angleDiff x y := by nlinarith
  have hge : 0 ≤ (t : ℝ) * Circle.angleDiff x y := by positivity
  have hpi := Real.pi_pos
  rcases lt_trichotomy m 0 with hm0 | hm0 | hm0
  · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hm0
    nlinarith
  · subst hm0
    simp at hm
    linarith
  · have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    nlinarith

/-- Closed form of the squared-distance change along a rotated circle point. -/
theorem s36b2c_rot_sq (C₁ C₂ p : ℂ) (s : ℝ) :
    ‖C₁ + (p - C₁) * Complex.exp ((s : ℂ) * I) - C₂‖ ^ 2 - ‖p - C₂‖ ^ 2 =
      2 * (‖p - C₁‖ ^ 2 - ((p - C₁).re * (p - C₂).re + (p - C₁).im * (p - C₂).im)) *
          (1 - Real.cos s) +
        2 * ((p - C₁).re * (p - C₂).im - (p - C₁).im * (p - C₂).re) * Real.sin s := by
  have he : Complex.exp ((s : ℂ) * I) = (Real.cos s : ℂ) + (Real.sin s : ℂ) * I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hsc := Real.sin_sq_add_cos_sq s
  rw [he, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  set a := p.re - C₁.re
  set b := p.im - C₁.im
  linear_combination (a ^ 2 + b ^ 2) * hsc

/-- Two transversal circles: the cross term is nonzero. -/
theorem s36b2c_cross_ne {C₁ C₂ p : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hp₁ : ‖p - C₁‖ = r₁) (hp₂ : ‖p - C₂‖ = r₂)
    (hlo : |r₁ - r₂| < ‖C₁ - C₂‖) (hhi : ‖C₁ - C₂‖ < r₁ + r₂) :
    (p - C₁).re * (p - C₂).im - (p - C₁).im * (p - C₂).re ≠ 0 := by
  intro h0
  have e1 : ‖p - C₁‖ ^ 2 = (p - C₁).re ^ 2 + (p - C₁).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have e2 : ‖p - C₂‖ ^ 2 = (p - C₂).re ^ 2 + (p - C₂).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hC : C₁ - C₂ = (p - C₂) - (p - C₁) := by ring
  have e3 : ‖C₁ - C₂‖ ^ 2 = ((p - C₂).re - (p - C₁).re) ^ 2 + ((p - C₂).im - (p - C₁).im) ^ 2 := by
    rw [hC, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]; ring
  set a := (p - C₁).re
  set b := (p - C₁).im
  set c := (p - C₂).re
  set d := (p - C₂).im
  set ρ := a * c + b * d
  have hid : ρ ^ 2 = r₁ ^ 2 * r₂ ^ 2 := by
    rw [← hp₁, ← hp₂, e1, e2]
    have : (a * d - b * c) ^ 2 = 0 := by rw [h0]; ring
    nlinarith
  have hd : ‖C₁ - C₂‖ ^ 2 = r₁ ^ 2 + r₂ ^ 2 - 2 * ρ := by
    rw [e3, ← hp₁, ← hp₂, e1, e2]; ring
  have hn := norm_nonneg (C₁ - C₂)
  have hlo2 : (r₁ - r₂) ^ 2 < ‖C₁ - C₂‖ ^ 2 := by
    rw [← sq_abs]; exact pow_lt_pow_left₀ hlo (abs_nonneg _) two_ne_zero
  have hhi2 : ‖C₁ - C₂‖ ^ 2 < (r₁ + r₂) ^ 2 := pow_lt_pow_left₀ hhi hn two_ne_zero
  have hρ : (ρ - r₁ * r₂) * (ρ + r₁ * r₂) = 0 := by nlinarith
  rcases mul_eq_zero.1 hρ with h | h
  · nlinarith
  · nlinarith

/-- (b') Along one circle, transversal to a second at `p`, the small forward and backward arcs lie
strictly on opposite sides of the second circle. -/
theorem s36b2c_fwd_bwd_opposite {C₁ C₂ p : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hp₁ : ‖p - C₁‖ = r₁) (hp₂ : ‖p - C₂‖ = r₂)
    (hlo : |r₁ - r₂| < ‖C₁ - C₂‖) (hhi : ‖C₁ - C₂‖ < r₁ + r₂) :
    ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      ¬ (r₂ < ‖C₁ + (p - C₁) * Complex.exp ((s : ℂ) * I) - C₂‖ ∧
          r₂ < ‖C₁ + (p - C₁) * Complex.exp (((-s : ℝ) : ℂ) * I) - C₂‖) ∧
      ¬ (‖C₁ + (p - C₁) * Complex.exp ((s : ℂ) * I) - C₂‖ < r₂ ∧
          ‖C₁ + (p - C₁) * Complex.exp (((-s : ℝ) : ℂ) * I) - C₂‖ < r₂) := by
  have hL := s36b2c_cross_ne hr₁ hr₂ hp₁ hp₂ hlo hhi
  have ef0 := s36b2c_rot_sq C₁ C₂ p
  set K := 2 * (‖p - C₁‖ ^ 2 - ((p - C₁).re * (p - C₂).re + (p - C₁).im * (p - C₂).im))
  set L := 2 * ((p - C₁).re * (p - C₂).im - (p - C₁).im * (p - C₂).re)
  have hL' : 0 < |L| := abs_pos.2 (by simp only [L]; exact mul_ne_zero two_ne_zero hL)
  set ε := min (π / 2) (|L| / (π * (|K| + 1)))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 ε := Ioo_mem_nhdsGT hε
  filter_upwards [hev] with s hs
  obtain ⟨hs0, hsε⟩ := hs
  have hs1 : s ≤ π / 2 := (lt_of_lt_of_le hsε (min_le_left _ _)).le
  have hs2 : s < |L| / (π * (|K| + 1)) := lt_of_lt_of_le hsε (min_le_right _ _)
  have hsin : 2 / π * s ≤ Real.sin s := Real.mul_le_sin hs0.le hs1
  have hcos : 1 - s ^ 2 / 2 ≤ Real.cos s := Real.one_sub_sq_div_two_le_cos
  have hcos1 : Real.cos s ≤ 1 := Real.cos_le_one s
  have hpi := Real.pi_pos
  have key : |K| * (1 - Real.cos s) < |L| * Real.sin s := by
    have h1 : |K| * (1 - Real.cos s) ≤ |K| * (s ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K)
    have h2 : s * (π * (|K| + 1)) < |L| := by
      rw [lt_div_iff₀ (by positivity)] at hs2; exact hs2
    have h3 : |L| * (2 / π * s) ≤ |L| * Real.sin s :=
      mul_le_mul_of_nonneg_left hsin (abs_nonneg L)
    have h4 : |K| * (s ^ 2 / 2) < |L| * (2 / π * s) := by
      rw [show |L| * (2 / π * s) = (2 * s / π) * |L| by ring]
      have h5 : |K| * (s ^ 2 / 2) ≤ (2 * s / π) * (s * (π * (|K| + 1))) / 4 := by
        rw [show (2 * s / π) * (s * (π * (|K| + 1))) / 4 = s ^ 2 * (|K| + 1) / 2 by
          field_simp <;> norm_num]
        nlinarith [abs_nonneg K, sq_nonneg s]
      have h6 : (2 * s / π) * (s * (π * (|K| + 1))) / 4 < (2 * s / π) * |L| := by
        have : 0 < 2 * s / π := by positivity
        nlinarith
      linarith
    linarith
  have ef := ef0 s
  have eb := ef0 (-s)
  rw [Real.cos_neg, Real.sin_neg] at eb
  rw [hp₂] at ef eb
  have hneg : L * (-Real.sin s) = -(L * Real.sin s) := by ring
  rw [hneg] at eb
  have hsin0 : 0 ≤ Real.sin s := le_trans (by positivity) hsin
  have hc0 : 0 ≤ 1 - Real.cos s := by linarith
  have hK1 : K * (1 - Real.cos s) ≤ |K| * (1 - Real.cos s) :=
    mul_le_mul_of_nonneg_right (le_abs_self K) hc0
  have hK2 : -(|K| * (1 - Real.cos s)) ≤ K * (1 - Real.cos s) := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le K) hc0
    linarith
  have hn1 := norm_nonneg (C₁ + (p - C₁) * Complex.exp ((s : ℂ) * I) - C₂)
  have hn2 := norm_nonneg (C₁ + (p - C₁) * Complex.exp (((-s : ℝ) : ℂ) * I) - C₂)
  rcases le_total 0 L with hL0 | hL0
  · rw [abs_of_nonneg hL0] at key
    constructor
    · rintro ⟨_, h2⟩
      have : r₂ ^ 2 < ‖C₁ + (p - C₁) * Complex.exp (((-s : ℝ) : ℂ) * I) - C₂‖ ^ 2 :=
        pow_lt_pow_left₀ h2 hr₂.le two_ne_zero
      linarith
    · rintro ⟨h1, _⟩
      have : ‖C₁ + (p - C₁) * Complex.exp ((s : ℂ) * I) - C₂‖ ^ 2 < r₂ ^ 2 :=
        pow_lt_pow_left₀ h1 hn1 two_ne_zero
      have hLs : 0 ≤ L * Real.sin s := mul_nonneg hL0 hsin0
      linarith
  · rw [abs_of_nonpos hL0] at key
    have hLs : L * Real.sin s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hL0 hsin0
    constructor
    · rintro ⟨h1, _⟩
      have : r₂ ^ 2 < ‖C₁ + (p - C₁) * Complex.exp ((s : ℂ) * I) - C₂‖ ^ 2 :=
        pow_lt_pow_left₀ h1 hr₂.le two_ne_zero
      have : -L * Real.sin s = -(L * Real.sin s) := by ring
      linarith
    · rintro ⟨_, h2⟩
      have : ‖C₁ + (p - C₁) * Complex.exp (((-s : ℝ) : ℂ) * I) - C₂‖ ^ 2 < r₂ ^ 2 :=
        pow_lt_pow_left₀ h2 hn2 two_ne_zero
      have : -L * Real.sin s = -(L * Real.sin s) := by ring
      linarith

/-- Orbit centres not at distance `R` from `q` stay at distance `> R` near `q`. -/
theorem s36b2c_near {R : ℝ}
    (hLf : ∀ L : Set UpperHalfPlane, IsCompact L →
      {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧
        ((fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R ∩ L).Nonempty}.Finite)
    (q : UpperHalfPlane) :
    ∀ᶠ x in 𝓝 q, ∀ γ ∈ Γ, R < dist q (γ • UpperHalfPlane.I) →
      R < dist x (γ • UpperHalfPlane.I) := by
  have hF := hLf (closedBall q 1) (isCompact_closedBall q 1)
  have h1 : ∀ᶠ x in 𝓝 q, ∀ γ ∈ {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧
        ((fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R ∩
          closedBall q 1).Nonempty},
      R < dist q (γ • UpperHalfPlane.I) → R < dist x (γ • UpperHalfPlane.I) := by
    rw [Filter.eventually_all_finite hF]
    intro γ _
    by_cases hq : R < dist q (γ • UpperHalfPlane.I)
    · have ho : IsOpen {x : UpperHalfPlane | R < dist x (γ • UpperHalfPlane.I)} :=
        isOpen_lt continuous_const (continuous_id.dist continuous_const)
      filter_upwards [ho.mem_nhds hq] with x hx _
      exact hx
    · exact Filter.Eventually.of_forall (fun x h => absurd h hq)
  filter_upwards [h1, ball_mem_nhds q one_pos] with x hx hxq γ hγ hqγ
  by_cases hm : γ ∈ {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧
        ((fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R ∩
          closedBall q 1).Nonempty}
  · exact hx γ hm hqγ
  · by_contra hle
    rw [not_lt] at hle
    apply hm
    refine ⟨hγ, x, ⟨γ⁻¹ • x, ?_, smul_inv_smul γ x⟩, ?_⟩
    · rw [mem_closedBall]
      calc dist (γ⁻¹ • x) UpperHalfPlane.I
          = dist (γ • (γ⁻¹ • x)) (γ • UpperHalfPlane.I) := (dist_smul γ _ _).symm
        _ = dist x (γ • UpperHalfPlane.I) := by rw [smul_inv_smul]
        _ ≤ R := hle
    · rw [mem_closedBall]
      exact (mem_ball.1 hxq).le


/-- Cancellation of a common centre and a nonzero real radius. -/
theorem s36b2c_cancel {C : ℂ} {r : ℝ} (hr : r ≠ 0) {u v : Circle}
    (h : C + (r : ℂ) * (u : ℂ) = C + (r : ℂ) * (v : ℂ)) : u = v := by
  apply Circle.ext
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hr) (add_left_cancel h)

/-- Cover step. Suppose that just after `s = 0` the rotated points `P s` of the circle of the orbit
centre `β • I`, starting at the arc endpoint `q = a m t₁`, are frontier points whose only active
centre is `β • I`. Then `q` is the `β`-translate of the start (forward rotation) or of the end
(backward rotation) of some arc. -/
theorem s36b2c_cover (hfree : ActsFreely Γ) {R : ℝ} (hR : 0 < R) {U : Set UpperHalfPlane}
    (V : Finset UpperHalfPlane) (hV : ∀ p : UpperHalfPlane, p ∈ V ↔ dist p UpperHalfPlane.I = R ∧
      ∃ γ ∈ Γ, γ • UpperHalfPlane.I ≠ UpperHalfPlane.I ∧ dist p (γ • UpperHalfPlane.I) = R)
    (n : ℕ) (a : Fin n → unitInterval → UpperHalfPlane)
    (hshape : (∀ i, Topology.IsEmbedding (a i) ∧ Set.range (a i) ⊆ sphere UpperHalfPlane.I R ∧
      ∃ x y : Circle, x ≠ y ∧ ∀ t : unitInterval,
        (a i t : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
          (Real.sinh R : ℂ) * (Circle.path x y t : ℂ)))
    (hsep : ∀ i j (t s : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      a i t = a j s → i = j ∧ t = s)
    (havoid : ∀ i (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → a i t ∉ V)
    (htr : frontier U = ⋃ γ ∈ Γ, ⋃ i,
      (fun τ : UpperHalfPlane => γ • τ) '' Set.range (a i))
    {β : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hβ : β ∈ Γ) (w : Circle) (m : Fin n)
    (t₁ : unitInterval) (ht₁ : (t₁ : ℝ) = 0 ∨ (t₁ : ℝ) = 1)
    (hqw : (a m t₁ : ℂ) = ((β • UpperHalfPlane.I).center R : ℂ) +
      (((β • UpperHalfPlane.I).im * Real.sinh R : ℝ) : ℂ) * (w : ℂ))
    (σ : ℝ) (P : ℝ → UpperHalfPlane) (hPc : Continuous P)
    (hP : ∀ s, (P s : ℂ) = ((β • UpperHalfPlane.I).center R : ℂ) +
      (((β • UpperHalfPlane.I).im * Real.sinh R : ℝ) : ℂ) * ((w * Circle.exp (σ * s) : Circle) : ℂ))
    (hPf : ∀ᶠ s in 𝓝[>] (0 : ℝ), P s ∈ frontier U ∧
      ∀ δ ∈ Γ, dist (P s) (δ • UpperHalfPlane.I) = R → δ • UpperHalfPlane.I = β • UpperHalfPlane.I) :
    ∃ k, (σ = 1 → a m t₁ = β • a k 0) ∧ (σ = -1 → a m t₁ = β • a k 1) := by
  set C : ℂ := ((β • UpperHalfPlane.I).center R : ℂ) with hC
  set r : ℝ := (β • UpperHalfPlane.I).im * Real.sinh R with hr
  have hr0 : 0 < r := mul_pos (UpperHalfPlane.im_pos _) (Real.sinh_pos_iff.2 hR)
  have hsph : ∀ i, Set.range (a i) ⊆ sphere UpperHalfPlane.I R := fun i => (hshape i).2.1
  -- every frontier point near `q` on this circle lies on a `β`-translate of an arc
  have step1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∃ k,
      P s ∈ (fun τ : UpperHalfPlane => β • τ) '' Set.range (a k) := by
    filter_upwards [hPf] with s hs
    obtain ⟨hf, hact⟩ := hs
    rw [htr] at hf
    simp only [mem_iUnion] at hf
    obtain ⟨γ, hγ, i, hmem⟩ := hf
    obtain ⟨τ, hτr, hτ⟩ := hmem
    obtain ⟨t, rfl⟩ := hτr
    have hd : dist (P s) (γ • UpperHalfPlane.I) = R := by
      rw [← hτ, dist_smul]
      exact mem_sphere.1 (hsph i ⟨t, rfl⟩)
    have hγβ := hact γ hγ hd
    have h1 : (β⁻¹ * γ) • UpperHalfPlane.I = UpperHalfPlane.I := by
      rw [mul_smul, hγβ, inv_smul_smul]
    refine ⟨i, a i t, ⟨t, rfl⟩, ?_⟩
    rcases hfree _ (Γ.mul_mem (Γ.inv_mem hβ) hγ) UpperHalfPlane.I h1 with h | h
    · rw [← hτ, inv_mul_eq_one.1 h]
    · rw [← hτ, inv_mul_eq_iff_eq_mul.1 h]
      show β • a i t = (β * -1) • a i t
      rw [mul_smul, ft0_neg_one_smul]
  -- one arc is met arbitrarily close to `s = 0`
  have step2 : ∃ k, ∃ᶠ s in 𝓝[>] (0 : ℝ),
      P s ∈ (fun τ : UpperHalfPlane => β • τ) '' Set.range (a k) := by
    by_contra hne
    simp only [not_exists, Filter.not_frequently] at hne
    have hall := Filter.eventually_all.2 hne
    obtain ⟨s, hs1, k, hk⟩ := (hall.and step1).exists
    exact hs1 k hk
  obtain ⟨k, hk⟩ := step2
  have hKc : IsClosed ((fun τ : UpperHalfPlane => β • τ) '' Set.range (a k)) :=
    ((isCompact_range (hshape k).1.continuous).image (continuous_const_smul β)).isClosed
  have hP0 : P 0 = a m t₁ := by
    apply UpperHalfPlane.ext
    rw [hP 0, hqw, mul_zero, Circle.exp_zero, mul_one]
  have hT : Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 (a m t₁)) := by
    rw [← hP0]; exact hPc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨τ0, hτ0r, hτ0⟩ := hKc.mem_of_frequently_of_tendsto hk hT
  obtain ⟨t0, rfl⟩ := hτ0r
  -- the parameter `t0` is an endpoint
  have hend : (t0 : ℝ) = 0 ∨ (t0 : ℝ) = 1 := by
    by_contra hint
    push Not at hint
    have h0 : 0 < (t0 : ℝ) := lt_of_le_of_ne t0.2.1 (Ne.symm hint.1)
    have h1 : (t0 : ℝ) < 1 := lt_of_le_of_ne t0.2.2 hint.2
    obtain ⟨_, _, hts⟩ := ft1gb_arc_interior_rigidity hfree R V hV n a hsph havoid hsep k m β hβ
      t0 h0 h1 t₁ hτ0
    rw [hts] at h0 h1
    rcases ht₁ with h | h <;> rw [h] at h0 h1 <;> linarith
  -- orientation of the translated arc
  obtain ⟨x, y, hxy, hform⟩ := (hshape k).2.2
  have hpk : ∀ t, (a k t : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
      ((UpperHalfPlane.I.im * Real.sinh R : ℝ) : ℂ) * (Circle.path x y t : ℂ) := by
    intro t
    rw [hform t, UpperHalfPlane.I_im, one_mul]
  obtain ⟨x', y', hx'y', hb0, hb1, hrange⟩ := ft1bx_smul_circle_arc β hR UpperHalfPlane.I x y hxy
    (a k) hpk
  have hD := Circle.angleDiff_lt_two_pi x' y'
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 (2 * π - Circle.angleDiff x' y') :=
    Ioo_mem_nhdsGT (by linarith)
  obtain ⟨s, hsK, hs⟩ := (hk.and_eventually hev).exists
  obtain ⟨_, ⟨t', rfl⟩, ht'⟩ := hsK
  have hsr : P s ∈ Set.range (fun t => β • a k t) := ⟨t', ht'⟩
  rw [hrange] at hsr
  obtain ⟨t'', ht''⟩ := hsr
  rw [hP s] at ht''
  refine ⟨k, ?_, ?_⟩
  · intro hσ1
    rcases hend with he | he
    · have : t0 = 0 := Subtype.ext he
      rw [this] at hτ0; exact hτ0.symm
    · exfalso
      have ht01 : t0 = 1 := Subtype.ext he
      rw [ht01] at hτ0
      have hwy : w = y' := s36b2c_cancel hr0.ne' (hqw.symm.trans (by rw [← hτ0, hb1]))
      rw [hσ1, one_mul, hwy] at ht''
      exact s36b2c_path_not_fwd hs.1 hs.2 t'' (s36b2c_cancel hr0.ne' ht'').symm
  · intro hσ1
    rcases hend with he | he
    · exfalso
      have ht00 : t0 = 0 := Subtype.ext he
      rw [ht00] at hτ0
      have hwx : w = x' := s36b2c_cancel hr0.ne' (hqw.symm.trans (by rw [← hτ0, hb0]))
      rw [hσ1, neg_one_mul, hwx] at ht''
      exact s36b2c_path_not_bwd hs.1 hs.2 t'' (s36b2c_cancel hr0.ne' ht'').symm
    · have : t0 = 1 := Subtype.ext he
      rw [this] at hτ0; exact hτ0.symm


/-- A complex number of norm one as a point of `Circle`. -/
theorem s36b2c_circle_of (z : ℂ) (h : ‖z‖ = 1) : ∃ u : Circle, (u : ℂ) = z :=
  ⟨⟨z, mem_sphere_zero_iff_norm.2 h⟩, rfl⟩

/-- Points of the Euclidean model of a hyperbolic circle have positive imaginary part. -/
theorem s36b2c_circ_im {R : ℝ} (hR : 0 < R) (c : UpperHalfPlane) (u : Circle) :
    0 < ((c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * (u : ℂ)).im := by
  rw [Complex.add_im, Complex.im_ofReal_mul, UpperHalfPlane.coe_im, UpperHalfPlane.center_im]
  have hu : |(u : ℂ).im| ≤ 1 := by
    have := Complex.abs_im_le_norm (u : ℂ)
    rwa [Circle.norm_coe] at this
  have hs : 0 < Real.sinh R := Real.sinh_pos_iff.2 hR
  have hcs : Real.sinh R < Real.cosh R := Real.sinh_lt_cosh R
  have hc := c.im_pos
  have h1 : -1 ≤ (u : ℂ).im := (abs_le.1 hu).1
  have h2 : c.im * Real.sinh R * (-1) ≤ c.im * Real.sinh R * (u : ℂ).im :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith

/-- A point at hyperbolic distance `R` from `c` in the Euclidean model. -/
theorem s36b2c_on_circle {R : ℝ} (hR : 0 < R) (c q : UpperHalfPlane) (h : dist q c = R) :
    ∃ u : Circle, (q : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * (u : ℂ) := by
  have hr : 0 < c.im * Real.sinh R := mul_pos c.im_pos (Real.sinh_pos_iff.2 hR)
  have hd := UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.1 h
  rw [Complex.dist_eq] at hd
  obtain ⟨u, hu⟩ := s36b2c_circle_of (((q : ℂ) - (c.center R : ℂ)) / ((c.im * Real.sinh R : ℝ) : ℂ))
    (by rw [norm_div, hd, Complex.norm_real, Real.norm_of_nonneg hr.le, div_self hr.ne'])
  refine ⟨u, ?_⟩
  rw [hu, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 hr.ne')]
  ring

/-- The rotated points of a hyperbolic circle as a continuous path in `ℍ`. -/
theorem s36b2c_pt {R : ℝ} (hR : 0 < R) (c : UpperHalfPlane) (w : Circle) (σ : ℝ) :
    ∃ P : ℝ → UpperHalfPlane, Continuous P ∧ ∀ s, (P s : ℂ) = (c.center R : ℂ) +
      ((c.im * Real.sinh R : ℝ) : ℂ) * ((w * Circle.exp (σ * s) : Circle) : ℂ) := by
  have h1 : Continuous (fun s : ℝ => w * Circle.exp (σ * s)) :=
    continuous_const.mul (Circle.exp.continuous.comp (continuous_const.mul continuous_id))
  have h2 : Continuous (fun s : ℝ => (c.center R : ℂ) +
      ((c.im * Real.sinh R : ℝ) : ℂ) * ((w * Circle.exp (σ * s) : Circle) : ℂ)) :=
    continuous_const.add (continuous_const.mul (continuous_subtype_val.comp h1))
  exact ⟨fun s => UpperHalfPlane.mk _ (s36b2c_circ_im hR c (w * Circle.exp (σ * s))),
    h2.upperHalfPlaneMk _, fun s => rfl⟩

/-- Points of the Euclidean model are at hyperbolic distance `R` from the centre. -/
theorem s36b2c_pt_dist {R : ℝ} (hR : 0 < R) (c : UpperHalfPlane) (u : Circle) (P : UpperHalfPlane)
    (hP : (P : ℂ) = (c.center R : ℂ) + ((c.im * Real.sinh R : ℝ) : ℂ) * (u : ℂ)) :
    dist P c = R := by
  have hr : 0 < c.im * Real.sinh R := mul_pos c.im_pos (Real.sinh_pos_iff.2 hR)
  rw [UpperHalfPlane.dist_eq_iff_dist_coe_center_eq, Complex.dist_eq, hP, add_sub_cancel_left,
    norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]

/-- Rotation about the centre in complex and in `Circle` form. -/
theorem s36b2c_rot_eq {C q : ℂ} {r : ℝ} {w : Circle} (h : q = C + (r : ℂ) * (w : ℂ)) (θ : ℝ) :
    C + (q - C) * Complex.exp ((θ : ℂ) * I) = C + (r : ℂ) * ((w * Circle.exp θ : Circle) : ℂ) := by
  rw [h, Circle.coe_mul, Circle.coe_exp]
  ring

/-- Active orbit centres at a point of the central circle: the centre `I` and possibly one more. -/
theorem s36b2c_active {R : ℝ}
    (hlevel : ∀ τ : UpperHalfPlane,
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.Finite ∧
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.ncard ≤ 2)
    (q : UpperHalfPlane) (hq : dist q UpperHalfPlane.I = R) :
    ∃ c₂ : UpperHalfPlane,
      (∀ δ ∈ Γ, dist q (δ • UpperHalfPlane.I) = R →
        δ • UpperHalfPlane.I = UpperHalfPlane.I ∨ δ • UpperHalfPlane.I = c₂) ∧
      (c₂ = UpperHalfPlane.I ∨ ∃ β ∈ Γ, c₂ = β • UpperHalfPlane.I ∧
        β • UpperHalfPlane.I ≠ UpperHalfPlane.I ∧ dist q (β • UpperHalfPlane.I) = R) := by
  obtain ⟨a', b', ha', hb', hiff⟩ := ft1gb_two_active_centres (Γ := Γ) R
    ⟨1, Γ.one_mem, by rw [one_smul]; exact hq⟩ (hlevel q).1 (hlevel q).2
  obtain ⟨⟨γa, hγa, rfl⟩, hda⟩ := ha'
  obtain ⟨⟨γb, hγb, rfl⟩, hdb⟩ := hb'
  have hI := (hiff UpperHalfPlane.I).1 ⟨⟨1, Γ.one_mem, (one_smul _ _).symm⟩, hq⟩
  rcases hI with hI | hI
  · refine ⟨γb • UpperHalfPlane.I, fun δ hδ hd => ?_, ?_⟩
    · rcases (hiff (δ • UpperHalfPlane.I)).1 ⟨⟨δ, hδ, rfl⟩, hd⟩ with h | h
      · left; rw [h, ← hI]
      · right; exact h
    · by_cases h : γb • UpperHalfPlane.I = UpperHalfPlane.I
      · left; exact h
      · right; exact ⟨γb, hγb, rfl, h, hdb⟩
  · refine ⟨γa • UpperHalfPlane.I, fun δ hδ hd => ?_, ?_⟩
    · rcases (hiff (δ • UpperHalfPlane.I)).1 ⟨⟨δ, hδ, rfl⟩, hd⟩ with h | h
      · right; exact h
      · left; rw [h, ← hI]
    · by_cases h : γa • UpperHalfPlane.I = UpperHalfPlane.I
      · left; exact h
      · right; exact ⟨γa, hγa, rfl, h, hda⟩

/-- Frontier builder: points on the circle of an active centre `β • I`, near a frontier point `q`,
staying strictly outside the only other active circle, are frontier points with a single active
centre. -/
theorem s36b2c_builder {R : ℝ} {U : Set UpperHalfPlane}
    (hfront : frontier U = {p : UpperHalfPlane |
      (∃ γ ∈ Γ, dist p (γ • UpperHalfPlane.I) = R) ∧
      ∀ γ ∈ Γ, R ≤ dist p (γ • UpperHalfPlane.I)})
    (hLf : ∀ L : Set UpperHalfPlane, IsCompact L →
      {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧
        ((fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R ∩ L).Nonempty}.Finite)
    {q : UpperHalfPlane} (hq : ∀ γ ∈ Γ, R ≤ dist q (γ • UpperHalfPlane.I))
    {β : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hβ : β ∈ Γ) (c₂ : UpperHalfPlane)
    (hact : ∀ δ ∈ Γ, dist q (δ • UpperHalfPlane.I) = R →
      δ • UpperHalfPlane.I = β • UpperHalfPlane.I ∨ δ • UpperHalfPlane.I = c₂)
    (P : ℝ → UpperHalfPlane) (hPc : Continuous P) (hP0 : P 0 = q)
    (hon : ∀ s, dist (P s) (β • UpperHalfPlane.I) = R)
    (hc₂ : c₂ = β • UpperHalfPlane.I ∨ ∀ᶠ s in 𝓝[>] (0 : ℝ), R < dist (P s) c₂) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), P s ∈ frontier U ∧
      ∀ δ ∈ Γ, dist (P s) (δ • UpperHalfPlane.I) = R →
        δ • UpperHalfPlane.I = β • UpperHalfPlane.I := by
  have hT : Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 q) := by
    rw [← hP0]; exact hPc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hN := hT.eventually (s36b2c_near hLf q)
  have hc : ∀ᶠ s in 𝓝[>] (0 : ℝ), c₂ = β • UpperHalfPlane.I ∨ R < dist (P s) c₂ := by
    rcases hc₂ with h | h
    · exact Filter.Eventually.of_forall (fun _ => Or.inl h)
    · exact h.mono (fun _ h => Or.inr h)
  filter_upwards [hN, hc] with s hs hcs
  have key : ∀ δ ∈ Γ, dist (P s) (δ • UpperHalfPlane.I) = R →
      δ • UpperHalfPlane.I = β • UpperHalfPlane.I := by
    intro δ hδ hd
    rcases (hq δ hδ).lt_or_eq with hlt | heq
    · have := hs δ hδ hlt
      linarith
    · rcases hact δ hδ heq.symm with h | h
      · exact h
      · rcases hcs with h3 | h3
        · rw [h, h3]
        · rw [h] at hd
          linarith
  refine ⟨?_, key⟩
  rw [hfront]
  refine ⟨⟨β, hβ, hon s⟩, fun γ hγ => ?_⟩
  rcases (hq γ hγ).lt_or_eq with hlt | heq
  · exact (hs γ hγ hlt).le
  · rcases hact γ hγ heq.symm with h | h
    · rw [h, hon s]
    · rcases hcs with h3 | h3
      · rw [h, h3, hon s]
      · rw [h]; exact h3.le

/-- Two arcs with the same start point are the same arc. -/
theorem s36b2c_same_start {R : ℝ} (hR : 0 < R) (n : ℕ) (a : Fin n → unitInterval → UpperHalfPlane)
    (hshape : (∀ i, Topology.IsEmbedding (a i) ∧ Set.range (a i) ⊆ sphere UpperHalfPlane.I R ∧
      ∃ x y : Circle, x ≠ y ∧ ∀ t : unitInterval,
        (a i t : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
          (Real.sinh R : ℂ) * (Circle.path x y t : ℂ)))
    (hsep : ∀ i j (t s : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      a i t = a j s → i = j ∧ t = s)
    {j k : Fin n} (h : a j 0 = a k 0) : j = k := by
  obtain ⟨xj, yj, hj, fj⟩ := (hshape j).2.2
  obtain ⟨xk, yk, hk, fk⟩ := (hshape k).2.2
  have hs0 : Real.sinh R ≠ 0 := (Real.sinh_pos_iff.2 hR).ne'
  have hx : xj = xk := by
    have e1 := fj 0
    have e2 := fk 0
    rw [Path.source] at e1 e2
    rw [h, e2] at e1
    exact (s36b2c_cancel hs0 e1).symm
  have hDj := Circle.angleDiff_pos hj
  have hDk := Circle.angleDiff_pos hk
  set s := min (Circle.angleDiff xj yj) (Circle.angleDiff xk yk) / 2
  have hs : 0 < s := by positivity
  have hsj : s < Circle.angleDiff xj yj := by
    have := min_le_left (Circle.angleDiff xj yj) (Circle.angleDiff xk yk); simp only [s]; linarith
  have hsk : s < Circle.angleDiff xk yk := by
    have := min_le_right (Circle.angleDiff xj yj) (Circle.angleDiff xk yk); simp only [s]; linarith
  obtain ⟨tj, hj0, hj1, htj⟩ := s36b2c_path_fwd hj hs hsj
  obtain ⟨tk, _, _, htk⟩ := s36b2c_path_fwd hk hs hsk
  have heq : a j tj = a k tk := by
    apply UpperHalfPlane.ext
    rw [fj, fk, htj, htk, hx]
  exact (hsep j k tj tk hj0 hj1 heq).1

/-- Forward occupancy at the start of an arc. -/
theorem s36b2c_fwd_occ {R : ℝ} (n : ℕ) (a : Fin n → unitInterval → UpperHalfPlane)
    (hshape : (∀ i, Topology.IsEmbedding (a i) ∧ Set.range (a i) ⊆ sphere UpperHalfPlane.I R ∧
      ∃ x y : Circle, x ≠ y ∧ ∀ t : unitInterval,
        (a i t : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
          (Real.sinh R : ℂ) * (Circle.path x y t : ℂ)))
    (j : Fin n) :
    ∃ x : Circle, (a j 0 : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
        ((UpperHalfPlane.I.im * Real.sinh R : ℝ) : ℂ) * (x : ℂ) ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ), ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
        (a j t : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
          ((UpperHalfPlane.I.im * Real.sinh R : ℝ) : ℂ) * ((x * Circle.exp s : Circle) : ℂ) := by
  obtain ⟨x, y, hxy, f⟩ := (hshape j).2.2
  refine ⟨x, ?_, ?_⟩
  · rw [f 0, Path.source, UpperHalfPlane.I_im, one_mul]
  · filter_upwards [Ioo_mem_nhdsGT (Circle.angleDiff_pos hxy)] with s hs
    obtain ⟨t, h0, h1, ht⟩ := s36b2c_path_fwd hxy hs.1 hs.2
    exact ⟨t, h0, h1, by rw [f t, ht, UpperHalfPlane.I_im, one_mul]⟩

/-- Backward occupancy at the end of an arc. -/
theorem s36b2c_bwd_occ {R : ℝ} (n : ℕ) (a : Fin n → unitInterval → UpperHalfPlane)
    (hshape : (∀ i, Topology.IsEmbedding (a i) ∧ Set.range (a i) ⊆ sphere UpperHalfPlane.I R ∧
      ∃ x y : Circle, x ≠ y ∧ ∀ t : unitInterval,
        (a i t : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
          (Real.sinh R : ℂ) * (Circle.path x y t : ℂ)))
    (i : Fin n) :
    ∃ y : Circle, (a i 1 : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
        ((UpperHalfPlane.I.im * Real.sinh R : ℝ) : ℂ) * (y : ℂ) ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ), ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
        (a i t : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
          ((UpperHalfPlane.I.im * Real.sinh R : ℝ) : ℂ) * ((y * Circle.exp (-s) : Circle) : ℂ) := by
  obtain ⟨x, y, hxy, f⟩ := (hshape i).2.2
  refine ⟨y, ?_, ?_⟩
  · rw [f 1, Path.target, UpperHalfPlane.I_im, one_mul]
  · filter_upwards [Ioo_mem_nhdsGT (Circle.angleDiff_pos hxy)] with s hs
    obtain ⟨t, h0, h1, ht⟩ := s36b2c_path_bwd hxy hs.1 hs.2
    exact ⟨t, h0, h1, by rw [f t, ht, UpperHalfPlane.I_im, one_mul]⟩

/-- Interior arc points are strictly outside every other active orbit circle. -/
theorem s36b2c_out_of_interior {R : ℝ} {U : Set UpperHalfPlane}
    (hfront : frontier U = {p : UpperHalfPlane |
      (∃ γ ∈ Γ, dist p (γ • UpperHalfPlane.I) = R) ∧
      ∀ γ ∈ Γ, R ≤ dist p (γ • UpperHalfPlane.I)})
    (V : Finset UpperHalfPlane) (hV : ∀ p : UpperHalfPlane, p ∈ V ↔ dist p UpperHalfPlane.I = R ∧
      ∃ γ ∈ Γ, γ • UpperHalfPlane.I ≠ UpperHalfPlane.I ∧ dist p (γ • UpperHalfPlane.I) = R)
    (n : ℕ) (a : Fin n → unitInterval → UpperHalfPlane)
    (hsph : ∀ i, Set.range (a i) ⊆ sphere UpperHalfPlane.I R)
    (havoid : ∀ i (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → a i t ∉ V)
    (ha : ∀ i, Set.range (a i) ⊆ frontier U)
    {β : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hβ : β ∈ Γ)
    (hβI : β • UpperHalfPlane.I ≠ UpperHalfPlane.I) (m : Fin n) (t : unitInterval)
    (h0 : 0 < (t : ℝ)) (h1 : (t : ℝ) < 1) :
    (β • UpperHalfPlane.I).im * Real.sinh R <
      ‖(a m t : ℂ) - ((β • UpperHalfPlane.I).center R : ℂ)‖ := by
  have hf := ha m ⟨t, rfl⟩
  rw [hfront] at hf
  have hne : dist (a m t) (β • UpperHalfPlane.I) ≠ R := fun h =>
    havoid m t h0 h1 ((hV _).2 ⟨mem_sphere.1 (hsph m ⟨t, rfl⟩), β, hβ, hβI, h⟩)
  have hlt : R < dist (a m t) (β • UpperHalfPlane.I) := lt_of_le_of_ne (hf.2 β hβ) (Ne.symm hne)
  rw [UpperHalfPlane.lt_dist_iff_lt_dist_coe_center, Complex.dist_eq] at hlt
  exact hlt


/-- Endpoint step. At an endpoint `q = a m t₁` of an arc whose interior occupies the rotation
direction `-σ` of the central circle, there is a translated arc leaving `q` (`σ = 1`) or arriving
at `q` (`σ = -1`). One active centre: continue along the central circle. Two active centres:
by opposite orientation at a transversal crossing, continue along the other active circle. -/
theorem s36b2c_endpoint (hfree : ActsFreely Γ) {R : ℝ} (hR : 0 < R) {U : Set UpperHalfPlane}
    (hLf : ∀ L : Set UpperHalfPlane, IsCompact L →
      {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧
        ((fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R ∩ L).Nonempty}.Finite)
    (hpair : ∀ γ ∈ Γ, ∀ δ ∈ Γ,
      γ • UpperHalfPlane.I ≠ δ • UpperHalfPlane.I →
        dist (γ • UpperHalfPlane.I) (δ • UpperHalfPlane.I) ≠ 2 * R)
    (hlevel : ∀ τ : UpperHalfPlane,
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.Finite ∧
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.ncard ≤ 2)
    (hfront : frontier U = {p : UpperHalfPlane |
      (∃ γ ∈ Γ, dist p (γ • UpperHalfPlane.I) = R) ∧
      ∀ γ ∈ Γ, R ≤ dist p (γ • UpperHalfPlane.I)})
    (V : Finset UpperHalfPlane) (hV : ∀ p : UpperHalfPlane, p ∈ V ↔ dist p UpperHalfPlane.I = R ∧
      ∃ γ ∈ Γ, γ • UpperHalfPlane.I ≠ UpperHalfPlane.I ∧ dist p (γ • UpperHalfPlane.I) = R)
    (n : ℕ) (a : Fin n → unitInterval → UpperHalfPlane)
    (hshape : (∀ i, Topology.IsEmbedding (a i) ∧ Set.range (a i) ⊆ sphere UpperHalfPlane.I R ∧
      ∃ x y : Circle, x ≠ y ∧ ∀ t : unitInterval,
        (a i t : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
          (Real.sinh R : ℂ) * (Circle.path x y t : ℂ)))
    (hsep : ∀ i j (t s : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      a i t = a j s → i = j ∧ t = s)
    (havoid : ∀ i (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → a i t ∉ V)
    (ha : ∀ i, Set.range (a i) ⊆ frontier U)
    (htr : frontier U = ⋃ γ ∈ Γ, ⋃ i,
      (fun τ : UpperHalfPlane => γ • τ) '' Set.range (a i))
    (m : Fin n) (t₁ : unitInterval) (ht₁ : (t₁ : ℝ) = 0 ∨ (t₁ : ℝ) = 1) (w : Circle)
    (hqw : (a m t₁ : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
      ((UpperHalfPlane.I.im * Real.sinh R : ℝ) : ℂ) * (w : ℂ))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hocc : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
      (a m t : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
        ((UpperHalfPlane.I.im * Real.sinh R : ℝ) : ℂ) * ((w * Circle.exp (-σ * s) : Circle) : ℂ)) :
    ∃ k β, β ∈ Γ ∧ (σ = 1 → a m t₁ = β • a k 0) ∧ (σ = -1 → a m t₁ = β • a k 1) := by
  have hsph : ∀ i, Set.range (a i) ⊆ sphere UpperHalfPlane.I R := fun i => (hshape i).2.1
  have hqf : a m t₁ ∈ frontier U := ha m ⟨t₁, rfl⟩
  have hq : ∀ γ ∈ Γ, R ≤ dist (a m t₁) (γ • UpperHalfPlane.I) := by
    have h := hqf
    rw [hfront] at h
    exact h.2
  have hqI : dist (a m t₁) UpperHalfPlane.I = R := mem_sphere.1 (hsph m ⟨t₁, rfl⟩)
  obtain ⟨c₂, hact, hc⟩ := s36b2c_active hlevel (a m t₁) hqI
  rcases hc with hc | ⟨β, hβ, hcβ, hβI, hdβ⟩
  · -- only the central circle is active at `q`
    have hqw' : (a m t₁ : ℂ) =
        (((1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • UpperHalfPlane.I).center R : ℂ) +
        ((((1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • UpperHalfPlane.I).im * Real.sinh R : ℝ) : ℂ) *
          (w : ℂ) := by
      rw [one_smul]; exact hqw
    obtain ⟨P, hPc, hP⟩ := s36b2c_pt hR ((1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) •
      UpperHalfPlane.I) w σ
    have hP0 : P 0 = a m t₁ :=
      UpperHalfPlane.ext (by rw [hP 0, hqw', mul_zero, Circle.exp_zero, mul_one])
    have hon : ∀ s, dist (P s) ((1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • UpperHalfPlane.I) = R :=
      fun s => s36b2c_pt_dist hR _ _ _ (hP s)
    have hPf := s36b2c_builder hfront hLf hq Γ.one_mem c₂ (fun δ hδ hd => by
        rcases hact δ hδ hd with h | h
        · left; rw [h, one_smul]
        · right; exact h) P hPc hP0 hon (Or.inl (by rw [hc, one_smul]))
    obtain ⟨k, h1, h2⟩ := s36b2c_cover hfree hR V hV n a hshape hsep havoid htr Γ.one_mem w m t₁ ht₁
      hqw' σ P hPc hP hPf
    exact ⟨k, 1, Γ.one_mem, h1, h2⟩
  · -- two active circles: the central one and the circle of `β • I`
    subst hcβ
    have hrβ : 0 < (β • UpperHalfPlane.I).im * Real.sinh R :=
      mul_pos (UpperHalfPlane.im_pos _) (Real.sinh_pos_iff.2 hR)
    have hrI : 0 < UpperHalfPlane.I.im * Real.sinh R :=
      mul_pos (UpperHalfPlane.im_pos _) (Real.sinh_pos_iff.2 hR)
    obtain ⟨w', hw'⟩ := s36b2c_on_circle hR (β • UpperHalfPlane.I) (a m t₁) hdβ
    obtain ⟨P, hPc, hP⟩ := s36b2c_pt hR (β • UpperHalfPlane.I) w' σ
    have hP0 : P 0 = a m t₁ :=
      UpperHalfPlane.ext (by rw [hP 0, hw', mul_zero, Circle.exp_zero, mul_one])
    have hon : ∀ s, dist (P s) (β • UpperHalfPlane.I) = R :=
      fun s => s36b2c_pt_dist hR _ _ _ (hP s)
    have hq1 : ‖(a m t₁ : ℂ) - (UpperHalfPlane.I.center R : ℂ)‖ =
        UpperHalfPlane.I.im * Real.sinh R := by
      rw [← Complex.dist_eq]; exact UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.1 hqI
    have hq2 : ‖(a m t₁ : ℂ) - ((β • UpperHalfPlane.I).center R : ℂ)‖ =
        (β • UpperHalfPlane.I).im * Real.sinh R := by
      rw [← Complex.dist_eq]; exact UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.1 hdβ
    have h2R : dist UpperHalfPlane.I (β • UpperHalfPlane.I) ≠ 2 * R := by
      have h := hpair 1 Γ.one_mem β hβ (by rw [one_smul]; exact Ne.symm hβI)
      rwa [one_smul] at h
    obtain ⟨hlo, hhi⟩ := ft1gor_spheres_transversal hR UpperHalfPlane.I (β • UpperHalfPlane.I)
      (Ne.symm hβI) h2R (a m t₁) hqI hdβ
    have hout : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), (β • UpperHalfPlane.I).im * Real.sinh R <
        ‖(UpperHalfPlane.I.center R : ℂ) + ((UpperHalfPlane.I.im * Real.sinh R : ℝ) : ℂ) *
          ((w * Circle.exp (-σ * s) : Circle) : ℂ) - ((β • UpperHalfPlane.I).center R : ℂ)‖ := by
      filter_upwards [hocc] with s hs
      obtain ⟨t, h0, h1, ht⟩ := hs
      have h := s36b2c_out_of_interior hfront V hV n a hsph havoid ha hβ hβI m t h0 h1
      rw [ht] at h
      exact h
    have hPout : ∀ᶠ s in 𝓝[>] (0 : ℝ), R < dist (P s) UpperHalfPlane.I := by
      rcases hσ with rfl | rfl
      · obtain ⟨ε, hε, hor⟩ := ft1gor_crossing_orientation hrI hrβ hq1 hq2 hlo hhi
        have hbw : ∀ s : ℝ, (UpperHalfPlane.I.center R : ℂ) + ((a m t₁ : ℂ) -
            (UpperHalfPlane.I.center R : ℂ)) * Complex.exp (-((s : ℂ) * I)) =
            (UpperHalfPlane.I.center R : ℂ) + ((UpperHalfPlane.I.im * Real.sinh R : ℝ) : ℂ) *
              ((w * Circle.exp (-1 * s) : Circle) : ℂ) := by
          intro s
          have e : -((s : ℂ) * I) = ((-1 * s : ℝ) : ℂ) * I := by push_cast; ring
          rw [e, s36b2c_rot_eq hqw]
        have hfw : ∀ s : ℝ, ((β • UpperHalfPlane.I).center R : ℂ) + ((a m t₁ : ℂ) -
            ((β • UpperHalfPlane.I).center R : ℂ)) * Complex.exp ((s : ℂ) * I) = (P s : ℂ) := by
          intro s
          have e : (s : ℂ) * I = ((1 * s : ℝ) : ℂ) * I := by push_cast; ring
          rw [e, s36b2c_rot_eq hw', hP s]
        rcases hor with hor | hor
        · filter_upwards [Ioo_mem_nhdsGT hε] with s hs
          have h := (hor s hs).2
          rw [hfw] at h
          rw [UpperHalfPlane.lt_dist_iff_lt_dist_coe_center, Complex.dist_eq]
          exact h
        · exfalso
          obtain ⟨s, hs1, hs2⟩ := (hout.and (Ioo_mem_nhdsGT hε)).exists
          have h := (hor s hs2).1
          rw [hbw] at h
          linarith
      · obtain ⟨ε, hε, hor⟩ := ft1gor_crossing_orientation hrβ hrI hq2 hq1
          (by rw [abs_sub_comm, norm_sub_rev]; exact hlo) (by rw [norm_sub_rev, add_comm]; exact hhi)
        have hbw : ∀ s : ℝ, ((β • UpperHalfPlane.I).center R : ℂ) + ((a m t₁ : ℂ) -
            ((β • UpperHalfPlane.I).center R : ℂ)) * Complex.exp (-((s : ℂ) * I)) = (P s : ℂ) := by
          intro s
          have e : -((s : ℂ) * I) = ((-1 * s : ℝ) : ℂ) * I := by push_cast; ring
          rw [e, s36b2c_rot_eq hw', hP s]
        have hfw : ∀ s : ℝ, (UpperHalfPlane.I.center R : ℂ) + ((a m t₁ : ℂ) -
            (UpperHalfPlane.I.center R : ℂ)) * Complex.exp ((s : ℂ) * I) =
            (UpperHalfPlane.I.center R : ℂ) + ((UpperHalfPlane.I.im * Real.sinh R : ℝ) : ℂ) *
              ((w * Circle.exp (- -1 * s) : Circle) : ℂ) := by
          intro s
          have e : (s : ℂ) * I = ((- -1 * s : ℝ) : ℂ) * I := by push_cast; ring
          rw [e, s36b2c_rot_eq hqw]
        rcases hor with hor | hor
        · filter_upwards [Ioo_mem_nhdsGT hε] with s hs
          have h := (hor s hs).1
          rw [hbw] at h
          rw [UpperHalfPlane.lt_dist_iff_lt_dist_coe_center, Complex.dist_eq]
          exact h
        · exfalso
          obtain ⟨s, hs1, hs2⟩ := (hout.and (Ioo_mem_nhdsGT hε)).exists
          have h := (hor s hs2).2
          rw [hfw] at h
          linarith
    have hPf := s36b2c_builder hfront hLf hq hβ UpperHalfPlane.I (fun δ hδ hd => by
        rcases hact δ hδ hd with h | h
        · right; exact h
        · left; exact h) P hPc hP0 hon (Or.inr hPout)
    obtain ⟨k, h1, h2⟩ := s36b2c_cover hfree hR V hV n a hshape hsep havoid htr hβ w' m t₁ ht₁
      hw' σ P hPc hP hPf
    exact ⟨k, β, hβ, h1, h2⟩

/-- An arc ending at a crossing point of two active circles cannot be followed by a central
translate of an arc: its forward and backward germs on the central circle would both be strictly
outside the other active circle. -/
theorem s36b2c_not_central (hfree : ActsFreely Γ) {R : ℝ} (hR : 0 < R) {U : Set UpperHalfPlane}
    (hpair : ∀ γ ∈ Γ, ∀ δ ∈ Γ,
      γ • UpperHalfPlane.I ≠ δ • UpperHalfPlane.I →
        dist (γ • UpperHalfPlane.I) (δ • UpperHalfPlane.I) ≠ 2 * R)
    (hfront : frontier U = {p : UpperHalfPlane |
      (∃ γ ∈ Γ, dist p (γ • UpperHalfPlane.I) = R) ∧
      ∀ γ ∈ Γ, R ≤ dist p (γ • UpperHalfPlane.I)})
    (V : Finset UpperHalfPlane) (hV : ∀ p : UpperHalfPlane, p ∈ V ↔ dist p UpperHalfPlane.I = R ∧
      ∃ γ ∈ Γ, γ • UpperHalfPlane.I ≠ UpperHalfPlane.I ∧ dist p (γ • UpperHalfPlane.I) = R)
    (n : ℕ) (a : Fin n → unitInterval → UpperHalfPlane)
    (hshape : (∀ i, Topology.IsEmbedding (a i) ∧ Set.range (a i) ⊆ sphere UpperHalfPlane.I R ∧
      ∃ x y : Circle, x ≠ y ∧ ∀ t : unitInterval,
        (a i t : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
          (Real.sinh R : ℂ) * (Circle.path x y t : ℂ)))
    (havoid : ∀ i (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → a i t ∉ V)
    (ha : ∀ i, Set.range (a i) ⊆ frontier U)
    {i j : Fin n} {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (hj : a i 1 = γ • a j 0) (hγI : γ • UpperHalfPlane.I = UpperHalfPlane.I)
    {β : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hβ : β ∈ Γ)
    (hβI : β • UpperHalfPlane.I ≠ UpperHalfPlane.I)
    (hdβ : dist (a i 1) (β • UpperHalfPlane.I) = R) : False := by
  have hsph : ∀ i, Set.range (a i) ⊆ sphere UpperHalfPlane.I R := fun i => (hshape i).2.1
  have hj0 : a j 0 = a i 1 := by
    rcases hfree γ hγ UpperHalfPlane.I hγI with rfl | rfl
    · rw [hj, one_smul]
    · rw [hj, ft0_neg_one_smul]
  have hrβ : 0 < (β • UpperHalfPlane.I).im * Real.sinh R :=
    mul_pos (UpperHalfPlane.im_pos _) (Real.sinh_pos_iff.2 hR)
  have hrI : 0 < UpperHalfPlane.I.im * Real.sinh R :=
    mul_pos (UpperHalfPlane.im_pos _) (Real.sinh_pos_iff.2 hR)
  obtain ⟨y, hy, hbo⟩ := s36b2c_bwd_occ n a hshape i
  obtain ⟨x, hx, hfo⟩ := s36b2c_fwd_occ n a hshape j
  rw [hj0] at hx
  have hxy : x = y := s36b2c_cancel hrI.ne' (hx.symm.trans hy)
  rw [hxy] at hfo
  have hqI : dist (a i 1) UpperHalfPlane.I = R := mem_sphere.1 (hsph i ⟨1, rfl⟩)
  have hq1 : ‖(a i 1 : ℂ) - (UpperHalfPlane.I.center R : ℂ)‖ =
      UpperHalfPlane.I.im * Real.sinh R := by
    rw [← Complex.dist_eq]; exact UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.1 hqI
  have hq2 : ‖(a i 1 : ℂ) - ((β • UpperHalfPlane.I).center R : ℂ)‖ =
      (β • UpperHalfPlane.I).im * Real.sinh R := by
    rw [← Complex.dist_eq]; exact UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.1 hdβ
  have h2R : dist UpperHalfPlane.I (β • UpperHalfPlane.I) ≠ 2 * R := by
    have h := hpair 1 Γ.one_mem β hβ (by rw [one_smul]; exact Ne.symm hβI)
    rwa [one_smul] at h
  obtain ⟨hlo, hhi⟩ := ft1gor_spheres_transversal hR UpperHalfPlane.I (β • UpperHalfPlane.I)
    (Ne.symm hβI) h2R (a i 1) hqI hdβ
  have hopp := s36b2c_fwd_bwd_opposite hrI hrβ hq1 hq2 hlo hhi
  have hf : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), (β • UpperHalfPlane.I).im * Real.sinh R <
      ‖(UpperHalfPlane.I.center R : ℂ) + ((a i 1 : ℂ) - (UpperHalfPlane.I.center R : ℂ)) *
        Complex.exp ((s : ℂ) * I) - ((β • UpperHalfPlane.I).center R : ℂ)‖ := by
    filter_upwards [hfo] with s hs
    obtain ⟨t, h0, h1, ht⟩ := hs
    have h := s36b2c_out_of_interior hfront V hV n a hsph havoid ha hβ hβI j t h0 h1
    rw [ht] at h
    rw [s36b2c_rot_eq hy]
    exact h
  have hb : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), (β • UpperHalfPlane.I).im * Real.sinh R <
      ‖(UpperHalfPlane.I.center R : ℂ) + ((a i 1 : ℂ) - (UpperHalfPlane.I.center R : ℂ)) *
        Complex.exp (((-s : ℝ) : ℂ) * I) - ((β • UpperHalfPlane.I).center R : ℂ)‖ := by
    filter_upwards [hbo] with s hs
    obtain ⟨t, h0, h1, ht⟩ := hs
    have h := s36b2c_out_of_interior hfront V hV n a hsph havoid ha hβ hβI i t h0 h1
    rw [ht] at h
    rw [s36b2c_rot_eq hy]
    exact h
  obtain ⟨s, hs1, hs2, hs3⟩ := (hopp.and (hf.and hb)).exists
  exact hs1.1 ⟨hs2, hs3⟩

/-- Uniqueness of the outgoing translated arc, up to the sign of the group element. -/
theorem s36b2c_uniq (hfree : ActsFreely Γ) {R : ℝ} (hR : 0 < R) {U : Set UpperHalfPlane}
    (hpair : ∀ γ ∈ Γ, ∀ δ ∈ Γ,
      γ • UpperHalfPlane.I ≠ δ • UpperHalfPlane.I →
        dist (γ • UpperHalfPlane.I) (δ • UpperHalfPlane.I) ≠ 2 * R)
    (hlevel : ∀ τ : UpperHalfPlane,
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.Finite ∧
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.ncard ≤ 2)
    (hfront : frontier U = {p : UpperHalfPlane |
      (∃ γ ∈ Γ, dist p (γ • UpperHalfPlane.I) = R) ∧
      ∀ γ ∈ Γ, R ≤ dist p (γ • UpperHalfPlane.I)})
    (V : Finset UpperHalfPlane) (hV : ∀ p : UpperHalfPlane, p ∈ V ↔ dist p UpperHalfPlane.I = R ∧
      ∃ γ ∈ Γ, γ • UpperHalfPlane.I ≠ UpperHalfPlane.I ∧ dist p (γ • UpperHalfPlane.I) = R)
    (n : ℕ) (a : Fin n → unitInterval → UpperHalfPlane)
    (hshape : (∀ i, Topology.IsEmbedding (a i) ∧ Set.range (a i) ⊆ sphere UpperHalfPlane.I R ∧
      ∃ x y : Circle, x ≠ y ∧ ∀ t : unitInterval,
        (a i t : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
          (Real.sinh R : ℂ) * (Circle.path x y t : ℂ)))
    (hsep : ∀ i j (t s : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      a i t = a j s → i = j ∧ t = s)
    (havoid : ∀ i (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → a i t ∉ V)
    (ha : ∀ i, Set.range (a i) ⊆ frontier U)
    {i j k : Fin n} {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) (hδ : δ ∈ Γ)
    (hj : a i 1 = γ • a j 0) (hk : a i 1 = δ • a k 0) :
    k = j ∧ (δ = γ ∨ δ = -γ) := by
  have hsph : ∀ i, Set.range (a i) ⊆ sphere UpperHalfPlane.I R := fun i => (hshape i).2.1
  have hqI : dist (a i 1) UpperHalfPlane.I = R := mem_sphere.1 (hsph i ⟨1, rfl⟩)
  have hdγ : dist (a i 1) (γ • UpperHalfPlane.I) = R := by
    rw [hj, dist_smul]; exact mem_sphere.1 (hsph j ⟨0, rfl⟩)
  have hdδ : dist (a i 1) (δ • UpperHalfPlane.I) = R := by
    rw [hk, dist_smul]; exact mem_sphere.1 (hsph k ⟨0, rfl⟩)
  obtain ⟨c₂, hact, hc⟩ := s36b2c_active hlevel (a i 1) hqI
  have hγδ : γ • UpperHalfPlane.I = δ • UpperHalfPlane.I := by
    rcases hc with hc | ⟨β, hβ, hcβ, hβI, hdβ⟩
    · have h1 : γ • UpperHalfPlane.I = UpperHalfPlane.I :=
        (hact γ hγ hdγ).elim id (fun h => h.trans hc)
      have h2 : δ • UpperHalfPlane.I = UpperHalfPlane.I :=
        (hact δ hδ hdδ).elim id (fun h => h.trans hc)
      rw [h1, h2]
    · have h1 : γ • UpperHalfPlane.I = c₂ := (hact γ hγ hdγ).resolve_left (fun h =>
        s36b2c_not_central hfree hR hpair hfront V hV n a hshape havoid ha hγ hj h hβ hβI hdβ)
      have h2 : δ • UpperHalfPlane.I = c₂ := (hact δ hδ hdδ).resolve_left (fun h =>
        s36b2c_not_central hfree hR hpair hfront V hV n a hshape havoid ha hδ hk h hβ hβI hdβ)
      rw [h1, h2]
  have h1 : (δ⁻¹ * γ) • UpperHalfPlane.I = UpperHalfPlane.I := by
    rw [mul_smul, hγδ, inv_smul_smul]
  rcases hfree _ (Γ.mul_mem (Γ.inv_mem hδ) hγ) UpperHalfPlane.I h1 with h | h
  · have hδγ : δ = γ := inv_mul_eq_one.1 h
    have hjk : a j 0 = a k 0 := by
      rw [hδγ] at hk
      exact (smul_left_cancel_iff γ).1 (hj.symm.trans hk)
    exact ⟨(s36b2c_same_start hR n a hshape hsep hjk).symm, Or.inl hδγ⟩
  · have hγ' : γ = δ * -1 := inv_mul_eq_iff_eq_mul.1 h
    have e : γ • a j 0 = δ • a j 0 := by rw [hγ', mul_smul, ft0_neg_one_smul]
    have hjk : a j 0 = a k 0 := (smul_left_cancel_iff δ).1 (e.symm.trans (hj.symm.trans hk))
    refine ⟨(s36b2c_same_start hR n a hshape hsep hjk).symm, Or.inr ?_⟩
    rw [hγ', mul_neg_one, neg_neg]

/-- B2c. The oriented endpoint geometry produces one outgoing germ, unique up to
sign, and an incoming germ at every selected start. Positive Circle.path
orientation is part of the actual parametrizations, not an assumed invariant
orientation on a quotient graph. This theorem must prove preservation of that
orientation by the actual SL action and the one- or two-active-circle cases. -/
theorem ft1gb_oriented_endpoint_incidence (hfree : ActsFreely Γ)
    {R : ℝ} (hR : 0 < R) {U : Set UpperHalfPlane}
    (hU : U = ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) ''
      closedBall UpperHalfPlane.I R)
    (hLf : ∀ L : Set UpperHalfPlane, IsCompact L →
      {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧
        ((fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R ∩ L).Nonempty}.Finite)
    (hpair : ∀ γ ∈ Γ, ∀ δ ∈ Γ,
      γ • UpperHalfPlane.I ≠ δ • UpperHalfPlane.I →
        dist (γ • UpperHalfPlane.I) (δ • UpperHalfPlane.I) ≠ 2 * R)
    (hlevel : ∀ τ : UpperHalfPlane,
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.Finite ∧
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.ncard ≤ 2)
    (hUi : ∀ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' U = U)
    (hUc : IsClosed U)
    (hfront : frontier U = {p : UpperHalfPlane |
      (∃ γ ∈ Γ, dist p (γ • UpperHalfPlane.I) = R) ∧
      ∀ γ ∈ Γ, R ≤ dist p (γ • UpperHalfPlane.I)})
    (hflat : ∀ p ∈ frontier U, ∃ e : OpenPartialHomeomorph UpperHalfPlane ℂ,
      p ∈ e.source ∧ e p = 0 ∧ e.target = ball 0 1 ∧
        ∀ x ∈ e.source, x ∈ U ↔ 0 ≤ (e x).im)
    (V : Finset UpperHalfPlane) (hV : ∀ p : UpperHalfPlane, p ∈ V ↔ dist p UpperHalfPlane.I = R ∧
      ∃ γ ∈ Γ, γ • UpperHalfPlane.I ≠ UpperHalfPlane.I ∧ dist p (γ • UpperHalfPlane.I) = R)
    (n : ℕ) (a : Fin n → unitInterval → UpperHalfPlane)
    (hshape : (∀ i, Topology.IsEmbedding (a i) ∧ Set.range (a i) ⊆ sphere UpperHalfPlane.I R ∧
      ∃ x y : Circle, x ≠ y ∧ ∀ t : unitInterval,
        (a i t : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
          (Real.sinh R : ℂ) * (Circle.path x y t : ℂ)))
    (hsep : ∀ i j (t s : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      a i t = a j s → i = j ∧ t = s)
    (havoid : ∀ i (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → a i t ∉ V)
    (ha : ∀ i, Set.range (a i) ⊆ frontier U)
    (hcover : sphere UpperHalfPlane.I R ∩ frontier U = ⋃ i, Set.range (a i)) :
    (∀ i, ∃ j γ, γ ∈ Γ ∧ a i 1 = γ • a j 0 ∧
      ∀ k δ, δ ∈ Γ → a i 1 = δ • a k 0 → k = j ∧ (δ = γ ∨ δ = -γ)) ∧
    (∀ j, ∃ i γ, γ ∈ Γ ∧ a i 1 = γ • a j 0) := by
  -- `hU`, `hUc` and `hflat` are not needed: the frontier formula `hfront` and the arc data carry
  -- all the geometry used here. The statement stays true without them.
  have _hU := hU
  have _hUc := hUc
  have _hflat := hflat
  have htr := ft1gb_translate_central_frontier R hUi
    (fun p hp => by rw [hfront] at hp; exact hp.1) n a ha hcover
  refine ⟨fun i => ?_, fun j => ?_⟩
  · obtain ⟨y, hy, hbo⟩ := s36b2c_bwd_occ n a hshape i
    obtain ⟨k, β, hβ, h1, -⟩ := s36b2c_endpoint hfree hR hLf hpair hlevel hfront V hV n a hshape
      hsep havoid ha htr i 1 (Or.inr Set.Icc.coe_one) y hy 1 (Or.inl rfl)
      (by filter_upwards [hbo] with s hs; simpa only [neg_mul, one_mul] using hs)
    exact ⟨k, β, hβ, h1 rfl, fun k' δ hδ hk' =>
      s36b2c_uniq hfree hR hpair hlevel hfront V hV n a hshape hsep havoid ha hβ hδ (h1 rfl) hk'⟩
  · obtain ⟨x, hx, hfo⟩ := s36b2c_fwd_occ n a hshape j
    obtain ⟨k, β, hβ, -, h2⟩ := s36b2c_endpoint hfree hR hLf hpair hlevel hfront V hV n a hshape
      hsep havoid ha htr j 0 (Or.inl Set.Icc.coe_zero) x hx (-1) (Or.inr rfl)
      (by filter_upwards [hfo] with s hs; simpa only [neg_neg, one_mul] using hs)
    exact ⟨k, β⁻¹, Γ.inv_mem hβ, by rw [h2 rfl, inv_smul_smul]⟩

end LiZhongQC
