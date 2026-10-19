import LiZhongQC.Lemmas.S36BersRepairBase

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **D.** `W(z) = (z-a)(z-b)(z-c) ∬_ℍ κ k_z` is holomorphic on `𝕃`, with `W''' = 6 ∬_ℍ κ/(ζ - z)⁴` (the integrand is
`1/(ζ - z)` plus a quadratic polynomial in `z`; differentiation under the integral). -/
theorem s36b_W_deriv {κ : ℂ → ℂ} (hκm : AEStronglyMeasurable κ (volume.restrict upperHalf)) {M : ℝ}
    (hκM : ∀ᵐ z ∂(volume.restrict upperHalf), ‖κ z‖ ≤ M) {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    DifferentiableOn ℂ (fun z : ℂ => (z - a) * (z - b) * (z - c) *
        ∫ ζ in upperHalf, κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z)))) lowerHalf ∧
      ∀ z ∈ lowerHalf, iteratedDeriv 3 (fun z : ℂ => (z - a) * (z - b) * (z - c) *
          ∫ ζ in upperHalf, κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z)))) z =
        6 * ∫ ζ in upperHalf, κ ζ / (ζ - z) ^ 4 := by
  have hU : MeasurableSet upperHalf :=
    (isOpen_lt continuous_const continuous_im : IsOpen {w : ℂ | 0 < w.im}).measurableSet
  have hL : IsOpen lowerHalf := isOpen_lt continuous_im continuous_const
  have hh := s36b_h_integrable hκm hκM hab hac hbc
  set h : ℂ → ℂ := fun ζ => κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) with hhdef
  set J : ℕ → ℂ → ℂ := fun n z => ∫ ζ in upperHalf, h ζ / (ζ - z) ^ n with hJdef
  have hW : (fun z : ℂ => (z - a) * (z - b) * (z - c) *
      ∫ ζ in upperHalf, κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z)))) =
      fun z => (z - a) * (z - b) * (z - c) * J 1 z := by
    funext z
    congr 1
    refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
    simp only [hhdef, pow_one, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  rw [hW]
  have hd : ∀ (n : ℕ), ∀ z ∈ lowerHalf, HasDerivAt (J n) ((n : ℂ) * J (n + 1) z) z :=
    fun n z hz => (s36b_J_deriv hh n hz).2
  have hi : ∀ (n : ℕ), ∀ z ∈ lowerHalf, Integrable (fun ζ => h ζ / (ζ - z) ^ n) (volume.restrict upperHalf) :=
    fun n z hz => (s36b_J_deriv hh n hz).1
  set P0 : ℂ → ℂ := fun z => (z - a) * (z - b) * (z - c) with hP0def
  set P1 : ℂ → ℂ := fun z => (z - b) * (z - c) + (z - a) * (z - c) + (z - a) * (z - b) with hP1def
  set P2 : ℂ → ℂ := fun z => 2 * ((z - a) + (z - b) + (z - c)) with hP2def
  have dP0 : ∀ z, HasDerivAt P0 (P1 z) z := by
    intro z
    have ha := (hasDerivAt_id' z).sub_const (a : ℂ)
    have hb := (hasDerivAt_id' z).sub_const (b : ℂ)
    have hc := (hasDerivAt_id' z).sub_const (c : ℂ)
    convert (ha.mul hb).mul hc using 1 <;> dsimp [P0, P1] <;> ring
  have dP1 : ∀ z, HasDerivAt P1 (P2 z) z := by
    intro z
    have ha := (hasDerivAt_id' z).sub_const (a : ℂ)
    have hb := (hasDerivAt_id' z).sub_const (b : ℂ)
    have hc := (hasDerivAt_id' z).sub_const (c : ℂ)
    convert ((hb.mul hc).add (ha.mul hc)).add (ha.mul hb) using 1 <;>
      dsimp [P1, P2] <;> ring
  have dP2 : ∀ z, HasDerivAt P2 6 z := by
    intro z
    have ha := (hasDerivAt_id' z).sub_const (a : ℂ)
    have hb := (hasDerivAt_id' z).sub_const (b : ℂ)
    have hc := (hasDerivAt_id' z).sub_const (c : ℂ)
    exact (((ha.add hb).add hc).const_mul (2 : ℂ)).congr_deriv (by norm_num)
  set W₁ : ℂ → ℂ := fun z => P1 z * J 1 z + P0 z * J 2 z with hW₁
  set W₂ : ℂ → ℂ := fun z => P2 z * J 1 z + 2 * P1 z * J 2 z + 2 * P0 z * J 3 z with hW₂
  set W₃ : ℂ → ℂ := fun z => 6 * J 1 z + 3 * P2 z * J 2 z + 6 * P1 z * J 3 z + 6 * P0 z * J 4 z with hW₃
  have hW0d : ∀ z ∈ lowerHalf, HasDerivAt (fun z => P0 z * J 1 z) (W₁ z) z := fun z hz =>
    ((dP0 z).mul (hd 1 z hz)).congr_deriv (by simp only [hW₁]; push_cast; ring)
  have hW1d : ∀ z ∈ lowerHalf, HasDerivAt W₁ (W₂ z) z := fun z hz =>
    (((dP1 z).mul (hd 1 z hz)).add ((dP0 z).mul (hd 2 z hz))).congr_deriv (by simp only [hW₂]; push_cast; ring)
  have hW2d : ∀ z ∈ lowerHalf, HasDerivAt W₂ (W₃ z) z := fun z hz =>
    ((((dP2 z).mul (hd 1 z hz)).add (((dP1 z).const_mul 2).mul (hd 2 z hz))).add
      (((dP0 z).const_mul 2).mul (hd 3 z hz))).congr_deriv (by simp only [hW₃]; push_cast; ring)
  refine ⟨fun z hz => (hW0d z hz).differentiableAt.differentiableWithinAt, fun z hz => ?_⟩
  have e1 : ∀ w ∈ lowerHalf, deriv (fun z => P0 z * J 1 z) w = W₁ w := fun w hw => (hW0d w hw).deriv
  have e2 : ∀ w ∈ lowerHalf, deriv (deriv (fun z => P0 z * J 1 z)) w = W₂ w := fun w hw => by
    rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hL.mem_nhds hw) e1)]
    exact (hW1d w hw).deriv
  have e3 : deriv (deriv (deriv (fun z => P0 z * J 1 z))) z = W₃ z := by
    rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hL.mem_nhds hz) e2)]
    exact (hW2d z hz).deriv
  have e0 : iteratedDeriv 3 (fun z => P0 z * J 1 z) z = deriv (deriv (deriv (fun z => P0 z * J 1 z))) z := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  show iteratedDeriv 3 (fun z => P0 z * J 1 z) z = _
  rw [e0, e3]
  -- `κ/(ζ - z)⁴ = h P(ζ)/(ζ - z)⁴` and Taylor's formula for the cubic `P` at `z`
  have hz' : z.im < 0 := hz
  have hpt : ∀ ζ ∈ upperHalf, κ ζ / (ζ - z) ^ 4 =
      h ζ / (ζ - z) ^ 1 + P2 z / 2 * (h ζ / (ζ - z) ^ 2) + P1 z * (h ζ / (ζ - z) ^ 3) +
        P0 z * (h ζ / (ζ - z) ^ 4) := by
    intro ζ hζ
    have hζi : 0 < ζ.im := hζ
    have hne : ∀ s : ℝ, ζ - s ≠ 0 := fun s h0 => by
      have := congrArg Complex.im h0
      simp at this
      linarith
    have hz0 : ζ - z ≠ 0 := fun h0 => by
      have := congrArg Complex.im h0
      simp at this
      linarith
    have ha := hne a
    have hb := hne b
    have hc := hne c
    simp only [hhdef, hP0def, hP1def, hP2def]
    field_simp
    ring
  have hsum : ∫ ζ in upperHalf, κ ζ / (ζ - z) ^ 4 =
      J 1 z + P2 z / 2 * J 2 z + P1 z * J 3 z + P0 z * J 4 z := by
    have h2 := (hi 2 z hz).const_mul (P2 z / 2)
    have h3 := (hi 3 z hz).const_mul (P1 z)
    have h4 := (hi 4 z hz).const_mul (P0 z)
    have hs4 : (∫ ζ in upperHalf, (h ζ / (ζ - z) ^ 1 + P2 z / 2 * (h ζ / (ζ - z) ^ 2) +
        P1 z * (h ζ / (ζ - z) ^ 3) + P0 z * (h ζ / (ζ - z) ^ 4))) =
        (∫ ζ in upperHalf, (h ζ / (ζ - z) ^ 1 + P2 z / 2 * (h ζ / (ζ - z) ^ 2) +
          P1 z * (h ζ / (ζ - z) ^ 3))) + ∫ ζ in upperHalf, P0 z * (h ζ / (ζ - z) ^ 4) :=
      integral_add (((hi 1 z hz).add h2).add h3) h4
    have hs3 : (∫ ζ in upperHalf, (h ζ / (ζ - z) ^ 1 + P2 z / 2 * (h ζ / (ζ - z) ^ 2) +
          P1 z * (h ζ / (ζ - z) ^ 3))) =
        (∫ ζ in upperHalf, (h ζ / (ζ - z) ^ 1 + P2 z / 2 * (h ζ / (ζ - z) ^ 2))) +
          ∫ ζ in upperHalf, P1 z * (h ζ / (ζ - z) ^ 3) :=
      integral_add ((hi 1 z hz).add h2) h3
    have hs2 : (∫ ζ in upperHalf, (h ζ / (ζ - z) ^ 1 + P2 z / 2 * (h ζ / (ζ - z) ^ 2))) =
        (∫ ζ in upperHalf, h ζ / (ζ - z) ^ 1) + ∫ ζ in upperHalf, P2 z / 2 * (h ζ / (ζ - z) ^ 2) :=
      integral_add (hi 1 z hz) h2
    rw [setIntegral_congr_fun hU hpt, hs4, hs3, hs2,
      integral_const_mul, integral_const_mul, integral_const_mul]
    all_goals rfl
  rw [hsum]
  simp only [hW₃]
  ring

/-- **C.** `W` is continuous on the closed lower half-plane, the base points `a, b, c` included (there `W = 0`; the
integral itself is not claimed continuous at `a, b, c`). Local part: Cauchy transform bound `lemma11_2`; far part:
dominated convergence. -/
theorem s36b_W_cont {κ : ℂ → ℂ} (hκm : AEStronglyMeasurable κ (volume.restrict upperHalf)) {M : ℝ}
    (hκM : ∀ᵐ z ∂(volume.restrict upperHalf), ‖κ z‖ ≤ M) {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ContinuousOn (fun z : ℂ => (z - a) * (z - b) * (z - c) *
        ∫ ζ in upperHalf, κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z)))) {z : ℂ | z.im ≤ 0} := by
  refine fun z₀ _ => ContinuousAt.continuousWithinAt ?_
  have hU : MeasurableSet upperHalf :=
    (isOpen_lt continuous_const continuous_im : IsOpen {w : ℂ | 0 < w.im}).measurableSet
  obtain ⟨G, hG, hGle⟩ := s36b_inv3_le hab hac hbc
  have hh := s36b_h_integrable hκm hκM hab hac hbc
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hκ' : ∀ᵐ ζ ∂(volume.restrict upperHalf), ‖κ ζ‖ ≤ M' := hκM.mono fun ζ h => h.trans (le_max_left _ _)
  have hne : ∀ ζ ∈ upperHalf, ∀ s : ℝ, ζ - s ≠ 0 := fun ζ hζ s h0 => by
    have h1 : (0 : ℝ) < ζ.im := hζ
    have := congrArg Complex.im h0
    simp at this
    linarith
  set B : Set ℂ := upperHalf ∩ ball z₀ 2 with hB
  set C : Set ℂ := upperHalf \ ball z₀ 2 with hC
  have hBm : MeasurableSet B := hU.inter measurableSet_ball
  have hCm : MeasurableSet C := hU.diff measurableSet_ball
  have hBU : B ⊆ upperHalf := inter_subset_left
  have hCU : C ⊆ upperHalf := diff_subset
  have hκB : ∀ᵐ ζ ∂(volume.restrict B), ‖κ ζ‖ ≤ M' := ae_restrict_of_ae_restrict_of_subset hBU hκ'
  have hκmB : AEStronglyMeasurable κ (volume.restrict B) := hκm.mono_measure (Measure.restrict_mono hBU le_rfl)
  set e₁ : ℂ := (a : ℂ) + b + c with he₁
  set e₂ : ℂ := (a : ℂ) * b + b * c + c * a with he₂
  set R : ℝ := ‖z₀‖ + 2 with hR
  -- bounded polynomial factors on `B`
  have hBn : ∀ ζ ∈ B, ‖ζ‖ ≤ R := fun ζ hζ => by
    have h1 : ‖ζ - z₀‖ < 2 := by rw [← dist_eq_norm]; exact hζ.2
    calc ‖ζ‖ = ‖(ζ - z₀) + z₀‖ := by ring_nf
      _ ≤ ‖ζ - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ ≤ R := by rw [hR]; linarith
  have hpolyB : ∀ (g : ℂ → ℂ) (K : ℝ), Measurable g → (∀ ζ ∈ B, ‖g ζ‖ ≤ K) →
      IntegrableOn (fun ζ => κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * g ζ) B := by
    intro g K hg hgK
    refine ((hh.mono_measure (Measure.restrict_mono hBU le_rfl)).norm.mul_const K).mono'
      ((hh.1.mono_measure (Measure.restrict_mono hBU le_rfl)).mul hg.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem hBm] with ζ hζ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hgK ζ hζ) (norm_nonneg _)
  have hA0 := hpolyB (fun _ => 1) 1 measurable_const (fun _ _ => by simp)
  have hA1 := hpolyB (fun ζ => ζ - e₁) (R + ‖e₁‖) (by fun_prop) (fun ζ hζ =>
    (norm_sub_le _ _).trans (by linarith [hBn ζ hζ]))
  have hA2 := hpolyB (fun ζ => ζ ^ 2 - e₁ * ζ + e₂) (R ^ 2 + ‖e₁‖ * R + ‖e₂‖) (by fun_prop) (fun ζ hζ => by
    have h1 := hBn ζ hζ
    calc ‖ζ ^ 2 - e₁ * ζ + e₂‖ ≤ ‖ζ ^ 2 - e₁ * ζ‖ + ‖e₂‖ := norm_add_le _ _
      _ ≤ ‖ζ ^ 2‖ + ‖e₁ * ζ‖ + ‖e₂‖ := by linarith [norm_sub_le (ζ ^ 2) (e₁ * ζ)]
      _ = ‖ζ‖ ^ 2 + ‖e₁‖ * ‖ζ‖ + ‖e₂‖ := by rw [norm_pow, norm_mul]
      _ ≤ R ^ 2 + ‖e₁‖ * R + ‖e₂‖ := by
          have h0 := norm_nonneg ζ
          nlinarith [norm_nonneg e₁])
  -- the three pieces
  set T1 : ℂ → ℂ := fun z => ∫ ζ in B, κ ζ / (ζ - z) with hT1
  set A0 : ℂ := ∫ ζ in B, κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun _ => (1 : ℂ)) ζ with hA0d
  set A1 : ℂ := ∫ ζ in B, κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun ζ => ζ - e₁) ζ with hA1d
  set A2 : ℂ := ∫ ζ in B, κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun ζ => ζ ^ 2 - e₁ * ζ + e₂) ζ
    with hA2d
  set T3 : ℂ → ℂ := fun z => ∫ ζ in C, κ ζ * ((z - a) * (z - b) * (z - c) *
    (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z)))) with hT3
  have hT1c : Continuous T1 :=
    s36b_cauchy_cont hBm (inter_subset_right : B ⊆ ball z₀ 2) hκmB hκB
  have hT3c : ContinuousAt T3 z₀ := by
    set K₀ : ℝ := (‖z₀‖ + 1 + |a|) * (‖z₀‖ + 1 + |b|) * (‖z₀‖ + 1 + |c|) with hK₀
    refine continuousAt_of_dominated (bound := fun ζ => M' * (K₀ * G ζ)) ?_ ?_
      ((hG.restrict.const_mul K₀).const_mul M') ?_
    · exact Filter.Eventually.of_forall fun z =>
        (hκm.mono_measure (Measure.restrict_mono hCU le_rfl)).mul (Measurable.aestronglyMeasurable (by fun_prop))
    · filter_upwards [ball_mem_nhds z₀ one_pos] with z hz
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hCU hκ', ae_restrict_mem hCm] with ζ h1 h2
      have hz1 : ‖z - z₀‖ < 1 := by rw [← dist_eq_norm]; exact hz
      have hζ2 : 2 ≤ ‖ζ - z₀‖ := by
        have := h2.2
        rw [Metric.mem_ball, dist_eq_norm, not_lt] at this
        exact this
      have hd : 1 ≤ ‖ζ - z‖ := by
        have ht : ‖ζ - z₀‖ ≤ ‖ζ - z‖ + ‖z - z₀‖ := by
          calc ‖ζ - z₀‖ = ‖(ζ - z) + (z - z₀)‖ := by congr 1; ring
            _ ≤ ‖ζ - z‖ + ‖z - z₀‖ := norm_add_le _ _
        linarith
      have hzn : ‖z‖ ≤ ‖z₀‖ + 1 := by
        calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
          _ ≤ ‖z₀‖ + 1 := by linarith
      have hP : ‖(z - a) * (z - b) * (z - c)‖ ≤ K₀ := by
        rw [norm_mul, norm_mul]
        have hs : ∀ s : ℝ, ‖z - s‖ ≤ ‖z₀‖ + 1 + |s| := fun s =>
          (norm_sub_le _ _).trans (by rw [Complex.norm_real, Real.norm_eq_abs]; linarith)
        exact mul_le_mul (mul_le_mul (hs a) (hs b) (norm_nonneg _) (by positivity)) (hs c) (norm_nonneg _)
          (by positivity)
      have hk : ‖1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z))‖ ≤ G ζ := by
        have e : 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z)) = 1 / ((ζ - a) * (ζ - b) * (ζ - c)) * (1 / (ζ - z)) := by
          simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
          ring
        rw [e, norm_mul]
        have h3 : ‖1 / (ζ - z)‖ ≤ 1 := by
          rw [norm_div, norm_one]
          exact div_le_one_of_le₀ hd (norm_nonneg _)
        calc ‖1 / ((ζ - a) * (ζ - b) * (ζ - c))‖ * ‖1 / (ζ - z)‖ ≤ G ζ * 1 :=
              mul_le_mul (hGle ζ (hCU h2)) h3 (norm_nonneg _) ((norm_nonneg _).trans (hGle ζ (hCU h2)))
          _ = G ζ := mul_one _
      rw [norm_mul, norm_mul]
      exact mul_le_mul h1 (mul_le_mul hP hk (norm_nonneg _) (by positivity)) (by positivity) hM'0
    · filter_upwards [ae_restrict_mem hCm] with ζ h2
      have hζ2 : ζ - z₀ ≠ 0 := by
        intro h0
        have := h2.2
        rw [Metric.mem_ball, dist_eq_norm, h0, norm_zero] at this
        exact this (by norm_num)
      have hPζ : (ζ - a) * (ζ - b) * (ζ - c) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (hne ζ (hCU h2) a) (hne ζ (hCU h2) b)) (hne ζ (hCU h2) c)
      exact continuousAt_const.mul ((by fun_prop : ContinuousAt (fun z : ℂ => (z - a) * (z - b) * (z - c)) z₀).mul
        (continuousAt_const.div (by fun_prop) (mul_ne_zero hPζ hζ2)))
  -- `W = T1 - (z² A0 + z A1 + A2) + T3` near `z₀`
  have hdecomp : ∀ z ∈ ball z₀ 1, (z - a) * (z - b) * (z - c) *
      ∫ ζ in upperHalf, κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z))) =
      T1 z - (z ^ 2 * A0 + z * A1 + A2) + T3 z := by
    intro z hz
    have hz1 : ‖z - z₀‖ < 1 := by rw [← dist_eq_norm]; exact hz
    -- integrability of `κ / (ζ - z)` on `B`
    have hBz : B ⊆ ball z 3 := fun ζ hζ => by
      have h1 : ‖ζ - z₀‖ < 2 := by rw [← dist_eq_norm]; exact hζ.2
      rw [Metric.mem_ball, dist_eq_norm]
      have := norm_sub_le (ζ - z₀) (z - z₀)
      rw [sub_sub_sub_cancel_right] at this
      linarith
    have hI1 : IntegrableOn (fun ζ => κ ζ / (ζ - z)) B := by
      refine (((s36b_inv_ball_int z (by norm_num : (0 : ℝ) < 3)).mono_set hBz).const_mul M').mono'
        (hκmB.mul (Measurable.aestronglyMeasurable (by fun_prop : Measurable fun ζ : ℂ => (ζ - z)⁻¹)) |>.congr
          (ae_of_all _ fun ζ => (div_eq_mul_inv _ _).symm)) ?_
      filter_upwards [hκB] with ζ h1
      rw [norm_div, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hptB : ∀ᵐ ζ ∂(volume.restrict B), κ ζ * ((z - a) * (z - b) * (z - c) *
        (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z)))) =
        κ ζ / (ζ - z) - (z ^ 2 * (κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun _ => (1 : ℂ)) ζ) +
          z * (κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun ζ => ζ - e₁) ζ) +
          κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun ζ => ζ ^ 2 - e₁ * ζ + e₂) ζ) := by
      filter_upwards [ae_restrict_mem hBm, ae_restrict_of_ae ((Set.countable_singleton z).ae_notMem volume)]
        with ζ hζ hζz
      have hz0 : ζ - z ≠ 0 := sub_ne_zero.2 (by simpa using hζz)
      have ha := hne ζ (hBU hζ) a
      have hb := hne ζ (hBU hζ) b
      have hc := hne ζ (hBU hζ) c
      simp only [he₁, he₂]
      field_simp
      ring
    have hIB : IntegrableOn (fun ζ => κ ζ * ((z - a) * (z - b) * (z - c) *
        (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z))))) B :=
      (hI1.sub (((hA0.const_mul _).add (hA1.const_mul _)).add hA2)).congr (hptB.mono fun ζ h => h.symm)
    have hIC : IntegrableOn (fun ζ => κ ζ * ((z - a) * (z - b) * (z - c) *
        (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z))))) C := by
      set K₀ : ℝ := (‖z₀‖ + 1 + |a|) * (‖z₀‖ + 1 + |b|) * (‖z₀‖ + 1 + |c|)
      refine ((hG.restrict.const_mul K₀).const_mul M').mono'
        ((hκm.mono_measure (Measure.restrict_mono hCU le_rfl)).mul
          (Measurable.aestronglyMeasurable (by fun_prop))) ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hCU hκ', ae_restrict_mem hCm] with ζ h1 h2
      have hζ2 : 2 ≤ ‖ζ - z₀‖ := by
        have := h2.2
        rw [Metric.mem_ball, dist_eq_norm, not_lt] at this
        exact this
      have hd : 1 ≤ ‖ζ - z‖ := by
        have ht : ‖ζ - z₀‖ ≤ ‖ζ - z‖ + ‖z - z₀‖ := by
          calc ‖ζ - z₀‖ = ‖(ζ - z) + (z - z₀)‖ := by congr 1; ring
            _ ≤ ‖ζ - z‖ + ‖z - z₀‖ := norm_add_le _ _
        linarith
      have hzn : ‖z‖ ≤ ‖z₀‖ + 1 := by
        calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
          _ ≤ ‖z₀‖ + 1 := by linarith
      have hP : ‖(z - a) * (z - b) * (z - c)‖ ≤ K₀ := by
        rw [norm_mul, norm_mul]
        have hs : ∀ s : ℝ, ‖z - s‖ ≤ ‖z₀‖ + 1 + |s| := fun s =>
          (norm_sub_le _ _).trans (by rw [Complex.norm_real, Real.norm_eq_abs]; linarith)
        exact mul_le_mul (mul_le_mul (hs a) (hs b) (norm_nonneg _) (by positivity)) (hs c) (norm_nonneg _)
          (by positivity)
      have hk : ‖1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z))‖ ≤ G ζ := by
        have e : 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z)) = 1 / ((ζ - a) * (ζ - b) * (ζ - c)) * (1 / (ζ - z)) := by
          simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
          ring
        rw [e, norm_mul]
        have h3 : ‖1 / (ζ - z)‖ ≤ 1 := by
          rw [norm_div, norm_one]
          exact div_le_one_of_le₀ hd (norm_nonneg _)
        calc ‖1 / ((ζ - a) * (ζ - b) * (ζ - c))‖ * ‖1 / (ζ - z)‖ ≤ G ζ * 1 :=
              mul_le_mul (hGle ζ (hCU h2)) h3 (norm_nonneg _) ((norm_nonneg _).trans (hGle ζ (hCU h2)))
          _ = G ζ := mul_one _
      rw [norm_mul, norm_mul]
      exact mul_le_mul h1 (mul_le_mul hP hk (norm_nonneg _) (by positivity)) (by positivity) hM'0
    rw [← integral_const_mul]
    have e1 : ∫ ζ in upperHalf, (z - a) * (z - b) * (z - c) * (κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z)))) =
        ∫ ζ in upperHalf, κ ζ * ((z - a) * (z - b) * (z - c) * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z)))) :=
      integral_congr_ae (ae_of_all _ fun ζ => by ring)
    rw [e1, ← integral_inter_add_diff measurableSet_ball ((hIB.union hIC).mono_set (by
      intro ζ hζ
      by_cases h : ζ ∈ ball z₀ 2
      · exact Or.inl ⟨hζ, h⟩
      · exact Or.inr ⟨hζ, h⟩))]
    rw [show upperHalf ∩ ball z₀ 2 = B from rfl, show upperHalf \ ball z₀ 2 = C from rfl,
      integral_congr_ae hptB]
    have hs0 : (∫ ζ in B, (κ ζ / (ζ - z) -
        (z ^ 2 * (κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun _ => (1 : ℂ)) ζ) +
          z * (κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun ζ => ζ - e₁) ζ) +
          κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun ζ => ζ ^ 2 - e₁ * ζ + e₂) ζ))) =
        (∫ ζ in B, κ ζ / (ζ - z)) -
          ∫ ζ in B, (z ^ 2 * (κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun _ => (1 : ℂ)) ζ) +
            z * (κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun ζ => ζ - e₁) ζ) +
            κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun ζ => ζ ^ 2 - e₁ * ζ + e₂) ζ) :=
      integral_sub hI1 (((hA0.const_mul (z ^ 2)).add (hA1.const_mul z)).add hA2)
    have hs1 : (∫ ζ in B, (z ^ 2 * (κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun _ => (1 : ℂ)) ζ) +
            z * (κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun ζ => ζ - e₁) ζ) +
            κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun ζ => ζ ^ 2 - e₁ * ζ + e₂) ζ)) =
        (∫ ζ in B, (z ^ 2 * (κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun _ => (1 : ℂ)) ζ) +
            z * (κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun ζ => ζ - e₁) ζ))) + A2 :=
      integral_add ((hA0.const_mul (z ^ 2)).add (hA1.const_mul z)) hA2
    have hs2 : (∫ ζ in B, (z ^ 2 * (κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun _ => (1 : ℂ)) ζ) +
            z * (κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c))) * (fun ζ => ζ - e₁) ζ))) =
        z ^ 2 * A0 + z * A1 :=
      (integral_add (hA0.const_mul (z ^ 2)) (hA1.const_mul z)).trans
        (congrArg₂ (· + ·) (integral_const_mul _ _) (integral_const_mul _ _))
    rw [hs0, hs1, hs2]
    all_goals rfl
  have hev : (fun z => T1 z - (z ^ 2 * A0 + z * A1 + A2) + T3 z) =ᶠ[𝓝 z₀]
      fun z : ℂ => (z - a) * (z - b) * (z - c) *
        ∫ ζ in upperHalf, κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z))) :=
    Filter.eventually_of_mem (ball_mem_nhds z₀ one_pos) fun z hz => (hdecomp z hz).symm
  refine ContinuousAt.congr ?_ hev
  exact (hT1c.continuousAt.sub (by fun_prop)).add hT3c

/-- **C'.** Boundary relation on all of `ℝ`: from `G₊(t) + conj G₋(t) = 0` on the dense set `D` (off `a, b, c`),
`W₊ = -conj W₋` on `ℝ` (the factor `(t-a)(t-b)(t-c)` is real; continuity `s36b_W_cont`). -/
theorem s36b_W_bdry {κp κm : ℂ → ℂ} (hmp : AEStronglyMeasurable κp (volume.restrict upperHalf))
    (hmm : AEStronglyMeasurable κm (volume.restrict upperHalf)) {M : ℝ}
    (hbp : ∀ᵐ z ∂(volume.restrict upperHalf), ‖κp z‖ ≤ M) (hbm : ∀ᵐ z ∂(volume.restrict upperHalf), ‖κm z‖ ≤ M)
    {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {D : Set ℝ} (hD : Dense D)
    (h : ∀ t ∈ D, t ≠ a → t ≠ b → t ≠ c →
      (∫ ζ in upperHalf, κp ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t)))) +
        conj (∫ ζ in upperHalf, κm ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t)))) = 0) :
    ∀ x : ℝ, (fun z : ℂ => (z - a) * (z - b) * (z - c) *
        ∫ ζ in upperHalf, κp ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z)))) (x : ℂ) =
      -conj ((fun z : ℂ => (z - a) * (z - b) * (z - c) *
        ∫ ζ in upperHalf, κm ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z)))) (x : ℂ)) := by
  have hWp := s36b_W_cont hmp hbp hab hac hbc
  have hWm := s36b_W_cont hmm hbm hab hac hbc
  set Wp : ℂ → ℂ := fun z : ℂ => (z - a) * (z - b) * (z - c) *
    ∫ ζ in upperHalf, κp ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z))) with hWpd
  set Wm : ℂ → ℂ := fun z : ℂ => (z - a) * (z - b) * (z - c) *
    ∫ ζ in upperHalf, κm ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z))) with hWmd
  have hreal : ∀ x : ℝ, (x : ℂ) ∈ {z : ℂ | z.im ≤ 0} := fun x => by simp
  have hcp : Continuous fun x : ℝ => Wp x := hWp.comp_continuous Complex.continuous_ofReal hreal
  have hcm : Continuous fun x : ℝ => Wm x := hWm.comp_continuous Complex.continuous_ofReal hreal
  have hF : Continuous fun x : ℝ => Wp x + conj (Wm x) := hcp.add (Complex.continuous_conj.comp hcm)
  have hD' : Dense (D \ {a, b, c}) := hD.sdiff_finite (Set.toFinite _)
  have hzero : EqOn (fun x : ℝ => Wp x + conj (Wm x)) (fun _ => 0) (D \ {a, b, c}) := by
    intro t ht
    obtain ⟨htD, ht⟩ := ht
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht
    obtain ⟨hta, htb, htc⟩ := ht
    have h0 := h t htD hta htb htc
    have e : ∀ X : ℂ, conj (((t : ℂ) - a) * (t - b) * (t - c) * X) = ((t : ℂ) - a) * (t - b) * (t - c) * conj X :=
      fun X => by simp [map_mul, map_sub]
    simp only [hWpd, hWmd]
    rw [e, ← mul_add, h0, mul_zero]
  have hext := Continuous.ext_on hD' hF continuous_const hzero
  intro x
  have hx : Wp x + conj (Wm x) = 0 := congrFun hext x
  exact eq_neg_of_add_eq_zero_left hx

end LiZhongQC
