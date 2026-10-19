import LiZhongQC.Ch11.S36_Hamilton
import LiZhongQC.ClusterSets

/-!
# Two-sided Bers approximation (S36 G1b input), interface with `sorry` stubs

GL Ch. 3 Thm 10 (l. 2981–3035) on `ℍ ∪ ℍ*`, with the zero-area case `Λ = ℝ̂` of Thm 9 replaced by
`h36p_orth_integrable`. The kernel is `k_t(ζ) = 1/((ζ-a)(ζ-b)(ζ-c)(ζ-t))` (finite base points `a, b, c`).
Route: Hahn–Banach on `F ⊔ conj F` (`s36b_hb`), extension and unfolding (`s36b_unfold`), then
`W(z) = (z-a)(z-b)(z-c) ∬_ℍ κ k_z` on the closed lower half-plane (`s36b_W_deriv`, `s36b_W_cont`, `s36b_W_bdry`),
gluing to an entire function (`s36b_glue`), the circle lemma (`s36b_circle_mean`, `s36b_circle_zero`) and the area
bound `s36b_kernel4_le`, assembled in `s36b_core`. Piece X (`s36b_theta_mero`, `s36b_theta_mero_infty`): the
Poincaré series of `k_t` is meromorphic across the ordinary points of `ℝ̂` with at most simple poles.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- The simple-pole profile `(1 + |ζ|)⁻² |ζ - p|⁻¹` is integrable on `ℂ` (`1/|ζ - p|` on the unit disc about `p`,
`(2 + |p|)(1 + |ζ|)⁻³` outside). -/
theorem s36b_prof_integrable (p : ℂ) : Integrable (fun ζ : ℂ => ((1 + ‖ζ‖) ^ 2)⁻¹ * ‖ζ - p‖⁻¹) := by
  have hball : IntegrableOn (fun ζ : ℂ => ‖ζ - p‖⁻¹) (ball p 1) := by
    refine ⟨(by fun_prop : Measurable fun ζ : ℂ => ‖ζ - p‖⁻¹).aestronglyMeasurable, ?_⟩
    have h := lintegral_ball_sub_enorm_rpow_neg (a := 1) (by norm_num) one_pos p
    show ∫⁻ ζ in ball p 1, ‖‖ζ - p‖⁻¹‖ₑ < ⊤
    have e : ∀ ζ : ℂ, ‖‖ζ - p‖⁻¹‖ₑ ≤ ‖ζ - p‖ₑ ^ (-1 : ℝ) := by
      intro ζ
      rw [ENNReal.rpow_neg_one]
      by_cases h0 : ζ - p = 0
      · simp [h0]
      · rw [enorm_inv (norm_ne_zero_iff.2 h0), enorm_norm]
    calc ∫⁻ ζ in ball p 1, ‖‖ζ - p‖⁻¹‖ₑ ≤ ∫⁻ ζ in ball p 1, ‖ζ - p‖ₑ ^ (-1 : ℝ) := lintegral_mono e
      _ = _ := h
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hg : Integrable (fun ζ : ℂ => (ball p 1).indicator (fun ζ : ℂ => ‖ζ - p‖⁻¹) ζ +
      (2 + ‖p‖) * ((1 + ‖ζ‖) ^ 3)⁻¹) :=
    (hball.integrable_indicator measurableSet_ball).add (b36_p_profile_integrable.const_mul _)
  refine hg.mono' (by fun_prop : Measurable fun ζ : ℂ => ((1 + ‖ζ‖) ^ 2)⁻¹ * ‖ζ - p‖⁻¹).aestronglyMeasurable
    (ae_of_all _ fun ζ => ?_)
  have h1 : 0 < 1 + ‖ζ‖ := by positivity
  rw [Real.norm_of_nonneg (by positivity)]
  by_cases hζ : ζ ∈ ball p 1
  · rw [indicator_of_mem hζ]
    have h2 : ((1 + ‖ζ‖) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [norm_nonneg ζ])
    have h3 : 0 ≤ (2 + ‖p‖) * ((1 + ‖ζ‖) ^ 3)⁻¹ := by positivity
    have h4 : 0 ≤ ‖ζ - p‖⁻¹ := by positivity
    nlinarith
  · rw [indicator_of_notMem hζ, zero_add]
    have hd : 1 ≤ ‖ζ - p‖ := by
      rw [Metric.mem_ball, dist_eq_norm] at hζ
      linarith
    have hn : ‖ζ‖ ≤ ‖ζ - p‖ + ‖p‖ := by
      calc ‖ζ‖ = ‖(ζ - p) + p‖ := by ring_nf
        _ ≤ ‖ζ - p‖ + ‖p‖ := norm_add_le _ _
    have hdp : 0 < ‖ζ - p‖ := by linarith
    rw [← mul_inv, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have key : 1 + ‖ζ‖ ≤ (2 + ‖p‖) * ‖ζ - p‖ := by nlinarith [norm_nonneg p, norm_nonneg ζ]
    nlinarith [mul_le_mul_of_nonneg_left key (sq_nonneg (1 + ‖ζ‖))]

/-- Partial fractions of the 4-pole kernel against an auxiliary point `q`: the Lagrange weights have vanishing
moments of order `0, 1`, so `1/∏(ζ - pᵢ) = Σ Kᵢ (ζ - q)⁻² (ζ - pᵢ)⁻¹`, `Kᵢ = (pᵢ - q)²/∏_{j ≠ i}(pᵢ - pⱼ)`. -/
theorem s36b_pf4 {p₁ p₂ p₃ p₄ q ζ : ℂ} (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h14 : p₁ ≠ p₄) (h23 : p₂ ≠ p₃)
    (h24 : p₂ ≠ p₄) (h34 : p₃ ≠ p₄) (hq : ζ ≠ q) (hζ₁ : ζ ≠ p₁) (hζ₂ : ζ ≠ p₂) (hζ₃ : ζ ≠ p₃) (hζ₄ : ζ ≠ p₄) :
    1 / ((ζ - p₁) * (ζ - p₂) * (ζ - p₃) * (ζ - p₄)) =
      (p₁ - q) ^ 2 / ((p₁ - p₂) * (p₁ - p₃) * (p₁ - p₄)) * (((ζ - q) ^ 2)⁻¹ * (ζ - p₁)⁻¹) +
      (p₂ - q) ^ 2 / ((p₂ - p₁) * (p₂ - p₃) * (p₂ - p₄)) * (((ζ - q) ^ 2)⁻¹ * (ζ - p₂)⁻¹) +
      (p₃ - q) ^ 2 / ((p₃ - p₁) * (p₃ - p₂) * (p₃ - p₄)) * (((ζ - q) ^ 2)⁻¹ * (ζ - p₃)⁻¹) +
      (p₄ - q) ^ 2 / ((p₄ - p₁) * (p₄ - p₂) * (p₄ - p₃)) * (((ζ - q) ^ 2)⁻¹ * (ζ - p₄)⁻¹) := by
  have a1 := sub_ne_zero.2 h12
  have a2 := sub_ne_zero.2 h13
  have a3 := sub_ne_zero.2 h14
  have a4 := sub_ne_zero.2 h23
  have a5 := sub_ne_zero.2 h24
  have a6 := sub_ne_zero.2 h34
  have b1 := sub_ne_zero.2 h12.symm
  have b2 := sub_ne_zero.2 h13.symm
  have b3 := sub_ne_zero.2 h14.symm
  have b4 := sub_ne_zero.2 h23.symm
  have b5 := sub_ne_zero.2 h24.symm
  have b6 := sub_ne_zero.2 h34.symm
  have c0 := sub_ne_zero.2 hq
  have c1 := sub_ne_zero.2 hζ₁
  have c2 := sub_ne_zero.2 hζ₂
  have c3 := sub_ne_zero.2 hζ₃
  have c4 := sub_ne_zero.2 hζ₄
  field_simp
  ring

/-- One partial-fraction term on the closed upper half-plane: `|ζ + i|⁻² |ζ - p|⁻¹ ≤ 2 (1 + |ζ|)⁻² |ζ - p|⁻¹`. -/
theorem s36b_term_le (p : ℂ) {ζ : ℂ} (hζ : 0 ≤ ζ.im) :
    ‖((ζ - -I) ^ 2)⁻¹ * (ζ - p)⁻¹‖ ≤ 2 * (((1 + ‖ζ‖) ^ 2)⁻¹ * ‖ζ - p‖⁻¹) := by
  rw [norm_mul, norm_inv, norm_inv, norm_pow, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hs : (1 + ‖ζ‖) ^ 2 ≤ 2 * ‖ζ - -I‖ ^ 2 := by
    have e1 : ‖ζ - -I‖ ^ 2 = ζ.re ^ 2 + (ζ.im + 1) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have e2 : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    nlinarith [sq_nonneg (1 - ‖ζ‖), norm_nonneg ζ]
  have hpos : 0 < (1 + ‖ζ‖) ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  have hq : 0 < ‖ζ - -I‖ ^ 2 := by nlinarith
  rw [inv_mul_eq_div, div_le_iff₀ hq]
  linarith

/-- Conjugation symmetry of Poincaré series: `Θf(z̄) = conj Θf(z)` when `f(w̄) = conj f(w)`. -/
theorem s36b_theta_conj (f : ℂ → ℂ) (hf : ∀ w, f (conj w) = conj (f w)) (z : ℂ) :
    h36p_theta Γ f (conj z) = conj (h36p_theta Γ f z) := by
  unfold h36p_theta
  rw [Complex.conj_tsum]
  refine tsum_congr fun γ => ?_
  rw [map_div₀, map_pow, ← hf]
  simp only [map_div₀, map_add, map_mul, Complex.conj_ofReal]

/-- `|ζ - z|⁻¹` is integrable on every disc. -/
theorem s36b_inv_ball_int (z : ℂ) {r : ℝ} (hr : 0 < r) : IntegrableOn (fun ζ : ℂ => ‖ζ - z‖⁻¹) (ball z r) := by
  refine ⟨(by fun_prop : Measurable fun ζ : ℂ => ‖ζ - z‖⁻¹).aestronglyMeasurable, ?_⟩
  have h := lintegral_ball_sub_enorm_rpow_neg (a := 1) (by norm_num) hr z
  show ∫⁻ ζ in ball z r, ‖‖ζ - z‖⁻¹‖ₑ < ⊤
  have e : ∀ ζ : ℂ, ‖‖ζ - z‖⁻¹‖ₑ ≤ ‖ζ - z‖ₑ ^ (-1 : ℝ) := by
    intro ζ
    rw [ENNReal.rpow_neg_one]
    by_cases h0 : ζ - z = 0
    · simp [h0]
    · rw [enorm_inv (norm_ne_zero_iff.2 h0), enorm_norm]
  calc ∫⁻ ζ in ball z r, ‖‖ζ - z‖⁻¹‖ₑ ≤ ∫⁻ ζ in ball z r, ‖ζ - z‖ₑ ^ (-1 : ℝ) := lintegral_mono e
    _ = _ := h
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- A Holder bound with a fixed real coefficient implies continuity.
The coefficient is an explicit parameter so no Lp or indicator expression
is unfolded while elaborating the limit proof. -/
theorem s36b_continuous_of_holder_bound {f : ℂ → ℂ} (C α : ℝ)
    (hα : 0 < α) (hf : ∀ w z : ℂ, ‖f w - f z‖ ≤ C * ‖w - z‖ ^ α) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 ?_
  intro z
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hn : Tendsto (fun w : ℂ => ‖w - z‖) (𝓝 z) (𝓝 (0 : ℝ)) := by
    have hnorm : Continuous (fun w : ℂ => ‖w - z‖) := (continuous_id.sub continuous_const).norm
    simpa only [sub_self, norm_zero] using hnorm.tendsto z
  have hp : Tendsto (fun w : ℂ => ‖w - z‖ ^ α) (𝓝 z) (𝓝 (0 : ℝ)) := by
    have hc : ContinuousAt (fun t : ℝ => t ^ α) 0 :=
      Real.continuousAt_rpow_const 0 α (Or.inr hα.le)
    have ht : Tendsto (fun w : ℂ => ‖w - z‖ ^ α) (𝓝 z) (𝓝 ((0 : ℝ) ^ α)) :=
      hc.tendsto.comp hn
    simpa only [Real.zero_rpow hα.ne'] using ht
  have hbound : Tendsto (fun w : ℂ => C * ‖w - z‖ ^ α) (𝓝 z) (𝓝 (0 : ℝ)) := by
    have ht : Tendsto (fun w : ℂ => C * ‖w - z‖ ^ α) (𝓝 z) (𝓝 (C * 0)) :=
      hp.const_mul C
    simpa only [mul_zero] using ht
  exact squeeze_zero (fun w => norm_nonneg (f w - f z)) (fun w => hf w z) hbound

/-- Bounded measurable data on a bounded set give an L4 indicator.
Keep the finite-measure instance inside this producer, out of the continuity
assembly theorem. -/
theorem s36b_indicator_memLp_four {κ : ℂ → ℂ} {S : Set ℂ}
    (hSm : MeasurableSet S) {R : ℝ} {c : ℂ} (hSR : S ⊆ ball c R)
    (hκm : AEStronglyMeasurable κ (volume.restrict S)) {M : ℝ}
    (hκM : ∀ᵐ z ∂(volume.restrict S), ‖κ z‖ ≤ M) :
    MemLp (S.indicator κ) (ENNReal.ofReal 4) volume := by
  letI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.2
      (ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hSR))
  have hlocal : MemLp κ (ENNReal.ofReal 4) (volume.restrict S) :=
    MemLp.of_bound hκm M hκM
  exact (memLp_indicator_iff_restrict hSm).2 hlocal

/-- The p=4 Cauchy transform is continuous; the input function is abstract,
so its indicator construction and finite-measure proof remain opaque. -/
theorem s36b_cauchyT_continuous_lp4 {omegaFn : ℂ → ℂ}
    (hω : MemLp omegaFn (ENNReal.ofReal 4) volume) :
    Continuous (cauchyT omegaFn) := by
  obtain ⟨M₂, hM₂⟩ := lemma11_2 (p := 4) (by norm_num)
  have hb : ∀ w z : ℂ, ‖cauchyT omegaFn w - cauchyT omegaFn z‖ ≤
      (M₂ * (eLpNorm omegaFn (ENNReal.ofReal 4) volume).toReal) *
        ‖w - z‖ ^ (((4 : ℝ) - 2) / 4) :=
    fun w z => hM₂ omegaFn hω w z
  exact s36b_continuous_of_holder_bound
    (f := cauchyT omegaFn) (M₂ * (eLpNorm omegaFn (ENNReal.ofReal 4) volume).toReal)
    (((4 : ℝ) - 2) / 4) (by norm_num) hb

/-- Indicator/set-integral conversion for the Cauchy transform, pointwise.
This identity does not assume integrability; both integrals use the same
Bochner convention. -/
theorem s36b_cauchyT_indicator_eq {κ : ℂ → ℂ} {S : Set ℂ}
    (hSm : MeasurableSet S) (z : ℂ) :
    (∫ ζ in S, κ ζ / (ζ - z)) = -(π : ℂ) * cauchyT (S.indicator κ) z := by
  have hi : (fun ζ : ℂ => S.indicator κ ζ / (ζ - z)) =
      S.indicator (fun ζ => κ ζ / (ζ - z)) := by
    funext ζ
    by_cases hζ : ζ ∈ S
    · simp only [indicator_of_mem hζ]
    · simp only [indicator_of_notMem hζ, zero_div]
  have he : (∫ ζ : ℂ, S.indicator κ ζ / (ζ - z)) =
      ∫ ζ in S, κ ζ / (ζ - z) := by
    rw [hi, integral_indicator hSm]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  change (∫ ζ in S, κ ζ / (ζ - z)) =
    -(π : ℂ) * (-(1 / π : ℂ) * ∫ ζ : ℂ, S.indicator κ ζ / (ζ - z))
  rw [he, ← mul_assoc, neg_mul_neg, mul_one_div_cancel hpi, one_mul]

/-- The Cauchy transform of a bounded function supported in a bounded measurable set is continuous
(Hölder bound `lemma11_2` with `p = 4`). -/
theorem s36b_cauchy_cont {κ : ℂ → ℂ} {S : Set ℂ} (hSm : MeasurableSet S) {R : ℝ} {c : ℂ} (hSR : S ⊆ ball c R)
    (hκm : AEStronglyMeasurable κ (volume.restrict S)) {M : ℝ} (hκM : ∀ᵐ z ∂(volume.restrict S), ‖κ z‖ ≤ M) :
    Continuous fun z => ∫ ζ in S, κ ζ / (ζ - z) := by

  have hω : MemLp (S.indicator κ) (ENNReal.ofReal 4) volume :=
    s36b_indicator_memLp_four hSm hSR hκm hκM
  have hT : Continuous (cauchyT (S.indicator κ)) :=
    s36b_cauchyT_continuous_lp4 hω
  have he : (fun z : ℂ => ∫ ζ in S, κ ζ / (ζ - z)) =
      fun z => -(π : ℂ) * cauchyT (S.indicator κ) z :=
    funext (s36b_cauchyT_indicator_eq hSm)
  rw [he]
  exact continuous_const.mul hT

/-- Partial fractions of the 3-pole kernel against `q` (Lagrange weights with vanishing moments of order `0, 1`). -/
theorem s36b_pf3 {p₁ p₂ p₃ q ζ : ℂ} (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃) (hq : ζ ≠ q)
    (hζ₁ : ζ ≠ p₁) (hζ₂ : ζ ≠ p₂) (hζ₃ : ζ ≠ p₃) :
    1 / ((ζ - p₁) * (ζ - p₂) * (ζ - p₃)) =
      (p₁ - q) ^ 2 / ((p₁ - p₂) * (p₁ - p₃)) * (((ζ - q) ^ 2)⁻¹ * (ζ - p₁)⁻¹) +
      (p₂ - q) ^ 2 / ((p₂ - p₁) * (p₂ - p₃)) * (((ζ - q) ^ 2)⁻¹ * (ζ - p₂)⁻¹) +
      (p₃ - q) ^ 2 / ((p₃ - p₁) * (p₃ - p₂)) * (((ζ - q) ^ 2)⁻¹ * (ζ - p₃)⁻¹) := by
  have a1 := sub_ne_zero.2 h12
  have a2 := sub_ne_zero.2 h13
  have a4 := sub_ne_zero.2 h23
  have b1 := sub_ne_zero.2 h12.symm
  have b2 := sub_ne_zero.2 h13.symm
  have b4 := sub_ne_zero.2 h23.symm
  have c0 := sub_ne_zero.2 hq
  have c1 := sub_ne_zero.2 hζ₁
  have c2 := sub_ne_zero.2 hζ₂
  have c3 := sub_ne_zero.2 hζ₃
  field_simp
  ring

/-- The 3-pole kernel `1/((ζ-a)(ζ-b)(ζ-c))` (distinct reals) is dominated on `ℍ` by an integrable function. -/
theorem s36b_inv3_le {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ G : ℂ → ℝ, Integrable G ∧ ∀ ζ ∈ upperHalf, ‖1 / ((ζ - a) * (ζ - b) * (ζ - c))‖ ≤ G ζ := by
  have hab' : (a : ℂ) ≠ b := by exact_mod_cast hab
  have hac' : (a : ℂ) ≠ c := by exact_mod_cast hac
  have hbc' : (b : ℂ) ≠ c := by exact_mod_cast hbc
  refine ⟨fun ζ =>
    2 * ‖((a : ℂ) - -I) ^ 2 / (((a : ℂ) - b) * ((a : ℂ) - c))‖ * (((1 + ‖ζ‖) ^ 2)⁻¹ * ‖ζ - a‖⁻¹) +
    2 * ‖((b : ℂ) - -I) ^ 2 / (((b : ℂ) - a) * ((b : ℂ) - c))‖ * (((1 + ‖ζ‖) ^ 2)⁻¹ * ‖ζ - b‖⁻¹) +
    2 * ‖((c : ℂ) - -I) ^ 2 / (((c : ℂ) - a) * ((c : ℂ) - b))‖ * (((1 + ‖ζ‖) ^ 2)⁻¹ * ‖ζ - c‖⁻¹),
    (((s36b_prof_integrable _).const_mul _).add ((s36b_prof_integrable _).const_mul _)).add
      ((s36b_prof_integrable _).const_mul _), fun ζ hζ => ?_⟩
  have him : 0 ≤ ζ.im := le_of_lt hζ
  have hne : ∀ s : ℝ, ζ ≠ (s : ℂ) := fun s h => by
    have h1 : (0 : ℝ) < ζ.im := hζ
    rw [h] at h1
    simp at h1
  have hqI : ζ ≠ -I := by
    intro h
    have h1 : (0 : ℝ) < ζ.im := hζ
    rw [h] at h1
    norm_num at h1
  rw [s36b_pf3 hab' hac' hbc' hqI (hne a) (hne b) (hne c)]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
    (rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (s36b_term_le _ him) (norm_nonneg _)).trans_eq (by ring))

/-- `h = κ/((ζ-a)(ζ-b)(ζ-c))` is integrable on `ℍ` for bounded measurable `κ`. -/
theorem s36b_h_integrable {κ : ℂ → ℂ} (hκm : AEStronglyMeasurable κ (volume.restrict upperHalf)) {M : ℝ}
    (hκM : ∀ᵐ z ∂(volume.restrict upperHalf), ‖κ z‖ ≤ M) {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Integrable (fun ζ => κ ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c)))) (volume.restrict upperHalf) := by
  obtain ⟨G, hG, hGle⟩ := s36b_inv3_le hab hac hbc
  have hU : MeasurableSet upperHalf :=
    (isOpen_lt continuous_const continuous_im : IsOpen {w : ℂ | 0 < w.im}).measurableSet
  have hm : Measurable (fun ζ : ℂ => 1 / ((ζ - (a : ℂ)) * (ζ - (b : ℂ)) * (ζ - (c : ℂ)))) := by
    fun_prop
  refine (hG.restrict.const_mul (max M 0)).mono' (hκm.mul hm.aestronglyMeasurable) ?_
  filter_upwards [hκM, ae_restrict_mem hU] with ζ h1 h2
  rw [norm_mul]
  exact mul_le_mul (h1.trans (le_max_left _ _)) (hGle ζ h2) (norm_nonneg _) (le_max_right _ _)

/-- Holomorphy of `J_n(z) = ∬_ℍ h(ζ)/(ζ - z)ⁿ` on `𝕃`, with `J_n' = n J_{n+1}`, for integrable `h`. -/
theorem s36b_J_deriv {h : ℂ → ℂ} (hh : Integrable h (volume.restrict upperHalf)) (n : ℕ) {z₀ : ℂ}
    (hz₀ : z₀ ∈ lowerHalf) :
    Integrable (fun ζ => h ζ / (ζ - z₀) ^ n) (volume.restrict upperHalf) ∧
      HasDerivAt (fun z => ∫ ζ in upperHalf, h ζ / (ζ - z) ^ n)
        ((n : ℂ) * ∫ ζ in upperHalf, h ζ / (ζ - z₀) ^ (n + 1)) z₀ := by
  have hz0 : z₀.im < 0 := hz₀
  set η : ℝ := -z₀.im / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hU : MeasurableSet upperHalf :=
    (isOpen_lt continuous_const continuous_im : IsOpen {w : ℂ | 0 < w.im}).measurableSet
  have key : ∀ ζ ∈ upperHalf, ∀ z ∈ ball z₀ η, η ≤ ‖ζ - z‖ := by
    intro ζ hζ z hz
    have hζi : 0 < ζ.im := hζ
    have h1 : |z.im - z₀.im| < η := by
      have := abs_im_le_norm (z - z₀)
      rw [sub_im] at this
      rw [Metric.mem_ball, dist_eq_norm] at hz
      linarith
    have h2 : |(ζ - z).im| ≤ ‖ζ - z‖ := abs_im_le_norm _
    rw [sub_im] at h2
    have h3 := le_abs_self (ζ.im - z.im)
    have h4 := (abs_lt.1 h1).2
    linarith
  have hne : ∀ ζ ∈ upperHalf, ∀ z ∈ ball z₀ η, ζ - z ≠ 0 := fun ζ hζ z hz =>
    norm_pos_iff.1 (lt_of_lt_of_le hη (key ζ hζ z hz))
  have haesm : ∀ (m : ℕ) (z : ℂ), AEStronglyMeasurable (fun ζ => h ζ / (ζ - z) ^ m) (volume.restrict upperHalf) :=
    fun m z => (hh.1.mul (Measurable.aestronglyMeasurable (by fun_prop :
      Measurable fun ζ : ℂ => ((ζ - z) ^ m)⁻¹))).congr (ae_of_all _ fun ζ => (div_eq_mul_inv _ _).symm)
  have hbd : ∀ (m : ℕ), ∀ ζ ∈ upperHalf, ∀ z ∈ ball z₀ η, ‖h ζ / (ζ - z) ^ m‖ ≤ ‖h ζ‖ / η ^ m := by
    intro m ζ hζ z hz
    rw [norm_div, norm_pow]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hη m) (pow_le_pow_left₀ hη.le (key ζ hζ z hz) m)
  have hint : ∀ (m : ℕ), ∀ z ∈ ball z₀ η, Integrable (fun ζ => h ζ / (ζ - z) ^ m) (volume.restrict upperHalf) := by
    intro m z hz
    refine (hh.norm.div_const (η ^ m)).mono' (haesm m z) ?_
    filter_upwards [ae_restrict_mem hU] with ζ hζ
    exact hbd m ζ hζ z hz
  refine ⟨hint n z₀ (mem_ball_self hη), ?_⟩
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict upperHalf)
    (F := fun z ζ => h ζ / (ζ - z) ^ n) (F' := fun z ζ => (n : ℂ) * (h ζ / (ζ - z) ^ (n + 1))) (x₀ := z₀)
    (bound := fun ζ => (n : ℝ) * (‖h ζ‖ / η ^ (n + 1))) (ball_mem_nhds z₀ hη)
    (Filter.Eventually.of_forall fun z => haesm n z) (hint n z₀ (mem_ball_self hη))
    ((haesm (n + 1) z₀).const_mul _) ?_ ((hh.norm.div_const _).const_mul _) ?_
  · rw [integral_const_mul] at hD
    exact hD.2
  · filter_upwards [ae_restrict_mem hU] with ζ hζ z hz
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hbd (n + 1) ζ hζ z hz) (Nat.cast_nonneg n)
  · filter_upwards [ae_restrict_mem hU] with ζ hζ z hz
    have hz' := hne ζ hζ z hz
    have h1 : HasDerivAt (fun w => (ζ - w) ^ n) ((n : ℂ) * (ζ - z) ^ (n - 1) * (-1)) z :=
      ((hasDerivAt_id' z).const_sub ζ).pow n
    have h2 := (h1.inv (pow_ne_zero n hz')).const_mul (h ζ)
    have e : (fun w => h ζ / (ζ - w) ^ n) = fun w => h ζ * ((ζ - w) ^ n)⁻¹ :=
      funext fun w => div_eq_mul_inv _ _
    rw [e]
    refine h2.congr_deriv ?_
    rcases n with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]
      field_simp
      ring

/-- A finite combination of `L¹` classes is represented a.e. by the same combination of the functions. -/
theorem s36b_coe_sum {μ : Measure ℂ} {ι : Type*} (s : Finset ι) (a : ι → ℂ) (g : ι → ℂ → ℂ)
    (hg : ∀ i, Integrable (g i) μ) :
    (⇑(∑ i ∈ s, a i • (hg i).toL1 (g i)) : ℂ → ℂ) =ᵐ[μ] fun z => ∑ i ∈ s, a i * g i z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ 1 μ] with z hz
    simp only [Finset.sum_empty]
    exact hz
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (a i • (hg i).toL1 (g i)) (∑ j ∈ s, a j • (hg j).toL1 (g j)),
      Lp.coeFn_smul (a i) ((hg i).toL1 (g i)), (hg i).coeFn_toL1, ih] with z h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]

/-- **K1.** For distinct reals `a, b, c, t`, the kernel `k_t` is holomorphic and integrable on `ℍ`, and its Poincaré
series lies in `A(Γ, F)` (`h36p_poincare`). -/
theorem s36b_kernel_mem (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {a b c t : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hta : t ≠ a) (htb : t ≠ b) (htc : t ≠ c) :
    DifferentiableOn ℂ (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) upperHalf ∧
      phiArea (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) upperHalf < ⊤ ∧
      h36p_theta Γ (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) ∈ integrableAutomorphicQD Γ F := by
  have hU : MeasurableSet upperHalf := (isOpen_lt continuous_const continuous_im : IsOpen {w : ℂ | 0 < w.im}).measurableSet
  have hne : ∀ ζ ∈ upperHalf, ∀ s : ℝ, ζ ≠ (s : ℂ) := fun ζ hζ s h => by
    have h1 : (0 : ℝ) < ζ.im := hζ
    rw [h] at h1
    simp at h1
  have hd : DifferentiableOn ℂ (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) upperHalf := by
    intro ζ hζ
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (differentiableAt_const _).div (by fun_prop) ?_
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.2 (hne ζ hζ a)) (sub_ne_zero.2 (hne ζ hζ b)))
      (sub_ne_zero.2 (hne ζ hζ c))) (sub_ne_zero.2 (hne ζ hζ t))
  have hab' : (a : ℂ) ≠ b := by exact_mod_cast hab
  have hac' : (a : ℂ) ≠ c := by exact_mod_cast hac
  have hbc' : (b : ℂ) ≠ c := by exact_mod_cast hbc
  have hat' : (a : ℂ) ≠ t := by exact_mod_cast hta.symm
  have hbt' : (b : ℂ) ≠ t := by exact_mod_cast htb.symm
  have hct' : (c : ℂ) ≠ t := by exact_mod_cast htc.symm
  set G : ℂ → ℝ := fun ζ =>
    2 * ‖((a : ℂ) - -I) ^ 2 / (((a : ℂ) - b) * ((a : ℂ) - c) * ((a : ℂ) - t))‖ * (((1 + ‖ζ‖) ^ 2)⁻¹ * ‖ζ - a‖⁻¹) +
    2 * ‖((b : ℂ) - -I) ^ 2 / (((b : ℂ) - a) * ((b : ℂ) - c) * ((b : ℂ) - t))‖ * (((1 + ‖ζ‖) ^ 2)⁻¹ * ‖ζ - b‖⁻¹) +
    2 * ‖((c : ℂ) - -I) ^ 2 / (((c : ℂ) - a) * ((c : ℂ) - b) * ((c : ℂ) - t))‖ * (((1 + ‖ζ‖) ^ 2)⁻¹ * ‖ζ - c‖⁻¹) +
    2 * ‖((t : ℂ) - -I) ^ 2 / (((t : ℂ) - a) * ((t : ℂ) - b) * ((t : ℂ) - c))‖ * (((1 + ‖ζ‖) ^ 2)⁻¹ * ‖ζ - t‖⁻¹)
    with hG
  have hGi : Integrable G :=
    ((((s36b_prof_integrable _).const_mul _).add ((s36b_prof_integrable _).const_mul _)).add
      ((s36b_prof_integrable _).const_mul _)).add ((s36b_prof_integrable _).const_mul _)
  have hbd : ∀ ζ ∈ upperHalf, ‖1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))‖ ≤ G ζ := by
    intro ζ hζ
    have him : 0 ≤ ζ.im := le_of_lt hζ
    have hqI : ζ ≠ -I := by
      intro h
      have h1 : (0 : ℝ) < ζ.im := hζ
      rw [h] at h1
      norm_num at h1
    rw [s36b_pf4 hab' hac' hat' hbc' hbt' hct' hqI (hne ζ hζ a) (hne ζ hζ b) (hne ζ hζ c) (hne ζ hζ t)]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ?_ ?_)) ?_)) ?_) <;>
    (rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (s36b_term_le _ him) (norm_nonneg _)).trans_eq (by ring))
  have hA : phiArea (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) upperHalf < ⊤ := by
    unfold phiArea
    calc ∫⁻ ζ in upperHalf, ENNReal.ofReal ‖1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))‖
        ≤ ∫⁻ ζ in upperHalf, ENNReal.ofReal (G ζ) :=
          setLIntegral_mono' hU fun ζ hζ => ENNReal.ofReal_le_ofReal (hbd ζ hζ)
      _ < ⊤ := hGi.restrict.lintegral_lt_top
  exact ⟨hd, hA, (h36p_poincare hΓ hF hd hA).1⟩

/-- **K2.** The kernel has real coefficients: `k_t(ζ̄) = conj k_t(ζ)`. -/
theorem s36b_kernel_conj (a b c t : ℝ) (w : ℂ) :
    (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) (conj w) =
      conj ((fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) w) := by
  simp only [map_div₀, map_one, map_mul, map_sub, Complex.conj_ofReal]

/-- **K3.** The Poincaré series of `k_t` is integrable on `F` and on `conj F` (conjugation symmetry
`Θk_t(z̄) = conj Θk_t(z)`). -/
theorem s36b_theta_integrable (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {a b c t : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hta : t ≠ a) (htb : t ≠ b) (htc : t ≠ c) :
    Integrable (h36p_theta Γ (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t)))) (volume.restrict F) ∧
      Integrable (h36p_theta Γ (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))))
        (volume.restrict ((starRingEnd ℂ) '' F)) := by
  obtain ⟨-, -, hmem⟩ := s36b_kernel_mem hΓ hF hab hac hbc hta htb htc
  have hFH : F ⊆ upperHalf := hF.1
  have hFm : MeasurableSet F := hF.2.1
  have h1 := h36p_b_integrableOn_A hFH hFm hmem
  refine ⟨h1, ?_⟩
  have hsym := s36b_theta_conj (Γ := Γ) (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t)))
    (s36b_kernel_conj a b c t)
  have himg : (starRingEnd ℂ) '' F = (starRingEnd ℂ) ⁻¹' F :=
    congrFun (Set.image_eq_preimage_of_inverse (f := ⇑(starRingEnd ℂ)) (g := ⇑(starRingEnd ℂ))
      Complex.conj_conj Complex.conj_conj) F
  rw [himg]
  have hm : MeasurableSet ((starRingEnd ℂ) ⁻¹' F) := Complex.continuous_conj.measurable hFm
  have hcont : ContinuousOn (h36p_theta Γ (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))))
      ((starRingEnd ℂ) ⁻¹' F) := by
    have h2 : ContinuousOn (fun z => conj (h36p_theta Γ (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t)))
        (conj z))) ((starRingEnd ℂ) ⁻¹' F) :=
      Complex.continuous_conj.comp_continuousOn ((hmem.1.continuousOn.mono hFH).comp
        Complex.continuous_conj.continuousOn (fun z hz => hz))
    refine h2.congr (fun z _ => ?_)
    simp only
    rw [hsym, Complex.conj_conj]
  refine ⟨hcont.aestronglyMeasurable hm, ?_⟩
  have e := gzE_conj_measurePreserving.setLIntegral_comp_preimage_emb
    Complex.conjLIE.toHomeomorph.measurableEmbedding
    (fun y => ‖h36p_theta Γ (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) (conj y)‖ₑ) F
  simp only [Complex.conj_conj] at e
  show ∫⁻ z in (starRingEnd ℂ) ⁻¹' F,
    ‖h36p_theta Γ (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) z‖ₑ < ⊤
  calc ∫⁻ z in (starRingEnd ℂ) ⁻¹' F,
        ‖h36p_theta Γ (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) z‖ₑ
      = ∫⁻ y in F, ‖h36p_theta Γ (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) (conj y)‖ₑ := e
    _ = ∫⁻ y in F, ‖h36p_theta Γ (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) y‖ₑ := by
        refine lintegral_congr fun y => ?_
        rw [hsym, ← ofReal_norm, ← ofReal_norm, Complex.norm_conj]
    _ < ⊤ := h1.2

/-- **H.** Hahn–Banach on `L¹(F) × L¹(conj F)`: if every bounded pair `(ν₁, ν₂)` annihilating all `ψ_t`, `t ∈ D`,
annihilates `(φ, 0)`, then `φ` is approximated on `F` by combinations of the `ψ_t` that are small on `conj F`
(template `h36p_duality_F`, `h35a_L1_dual_repr`). -/
theorem s36b_hb {F : Set ℂ} (hFm : MeasurableSet F) (hFH : F ⊆ upperHalf) {D : Set ℝ} {ψ : ℝ → ℂ → ℂ}
    (hψ : ∀ t ∈ D, Integrable (ψ t) (volume.restrict F) ∧
      Integrable (ψ t) (volume.restrict ((starRingEnd ℂ) '' F)))
    {φ : ℂ → ℂ} (hφ : Integrable φ (volume.restrict F))
    (hann : ∀ ν₁ ν₂ : ℂ → ℂ, AEStronglyMeasurable ν₁ (volume.restrict F) →
      AEStronglyMeasurable ν₂ (volume.restrict ((starRingEnd ℂ) '' F)) → ∀ M : ℝ,
      (∀ᵐ z ∂(volume.restrict F), ‖ν₁ z‖ ≤ M) →
      (∀ᵐ z ∂(volume.restrict ((starRingEnd ℂ) '' F)), ‖ν₂ z‖ ≤ M) →
      (∀ t ∈ D, (∫ z in F, ν₁ z * ψ t z) + (∫ z in (starRingEnd ℂ) '' F, ν₂ z * ψ t z) = 0) →
      ∫ z in F, ν₁ z * φ z = 0)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (T : Finset ℝ) (w : ℝ → ℂ), (∀ t ∈ T, t ∈ D) ∧
      phiArea (fun z => φ z - ∑ t ∈ T, w t * ψ t z) F < ε ∧
      phiArea (fun z => ∑ t ∈ T, w t * ψ t z) ((starRingEnd ℂ) '' F) < ε := by
  classical
  have himgG : (starRingEnd ℂ) '' F = (starRingEnd ℂ) ⁻¹' F :=
    congrFun (Set.image_eq_preimage_of_inverse (f := ⇑(starRingEnd ℂ)) (g := ⇑(starRingEnd ℂ))
      Complex.conj_conj Complex.conj_conj) F
  have hGm : MeasurableSet ((starRingEnd ℂ) '' F) := by
    rw [himgG]
    exact Complex.continuous_conj.measurable hFm
  have hpA : ∀ (S : Set ℂ) (h : ℂ → ℂ), Integrable h (volume.restrict S) →
      phiArea h S = ENNReal.ofReal (∫ z in S, ‖h z‖) := by
    intro S h hh
    unfold phiArea
    rw [ofReal_integral_norm_eq_lintegral_enorm hh]
    simp only [ofReal_norm]
  by_cases htop : ε = ⊤
  · refine ⟨∅, 0, by simp, ?_, ?_⟩
    · simp only [Finset.sum_empty, sub_zero, htop]
      rw [hpA F φ hφ]
      exact ENNReal.ofReal_lt_top
    · simp only [Finset.sum_empty, htop]
      unfold phiArea
      simp
  have hδ : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  -- the weighted finite measures `P S = ρ · volume|_S`, `ρ = (1 + |z|)⁻³`
  set ρ : ℂ → ℝ := fun z => ((1 + ‖z‖) ^ 3)⁻¹ with hρdef
  have hρpos : ∀ z, 0 < ρ z := fun z => by simp only [hρdef]; positivity
  have hρm : Measurable ρ := by simp only [hρdef]; fun_prop
  set P : Set ℂ → Measure ℂ := fun S => (volume.restrict S).withDensity (fun z => ENNReal.ofReal (ρ z)) with hPdef
  have hfin : ∀ S, IsFiniteMeasure (P S) := fun S =>
    isFiniteMeasure_withDensity_ofReal (b36_p_profile_integrable.integrableOn (s := S)).2
  haveI := hfin F
  haveI := hfin ((starRingEnd ℂ) '' F)
  have hSP : ∀ S, volume.restrict S ≪ P S := fun S =>
    withDensity_absolutelyContinuous' hρm.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun z => (ENNReal.ofReal_pos.2 (hρpos z)).ne')
  have hPint : ∀ S (g : ℂ → ℂ), ∫ z, g z ∂(P S) = ∫ z in S, (ρ z : ℂ) * g z := by
    intro S g
    rw [hPdef, integral_withDensity_eq_integral_toReal_smul hρm.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [ENNReal.toReal_ofReal (hρpos z).le, Complex.real_smul]
  have hPintR : ∀ S (g : ℂ → ℝ), ∫ z, g z ∂(P S) = ∫ z in S, ρ z * g z := by
    intro S g
    rw [hPdef, integral_withDensity_eq_integral_toReal_smul hρm.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [ENNReal.toReal_ofReal (hρpos z).le, smul_eq_mul]
  have hPi : ∀ S (g : ℂ → ℂ), Integrable g (P S) ↔ Integrable (fun z => (ρ z : ℂ) * g z) (volume.restrict S) := by
    intro S g
    rw [hPdef, integrable_withDensity_iff_integrable_smul' hρm.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integrable_congr (ae_of_all _ fun z => ?_)
    simp only [ENNReal.toReal_ofReal (hρpos z).le, Complex.real_smul]
  have hdiv : ∀ h : ℂ → ℂ, ∀ z, (ρ z : ℂ) * (h z / ρ z) = h z := fun h z => by
    have : (ρ z : ℂ) ≠ 0 := by exact_mod_cast (hρpos z).ne'
    field_simp
  have hnorm : ∀ h : ℂ → ℂ, ∀ z, ρ z * ‖h z / ρ z‖ = ‖h z‖ := fun h z => by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hρpos z).le]
    field_simp [(hρpos z).ne']
  have hint : ∀ S (h : ℂ → ℂ), Integrable h (volume.restrict S) → Integrable (fun z => h z / ρ z) (P S) := by
    intro S h hh
    rw [hPi]
    exact hh.congr (ae_of_all _ fun z => (hdiv h z).symm)
  have hL1 : ∀ S (h : ℂ → ℂ) (u : Lp ℂ 1 (P S)), (u : ℂ → ℂ) =ᵐ[P S] (fun z => h z / ρ z) →
      ‖u‖ = ∫ z in S, ‖h z‖ := by
    intro S h u hu
    rw [L1.norm_eq_integral_norm]
    have e : ∫ z, ‖(u : ℂ → ℂ) z‖ ∂(P S) = ∫ z, ‖h z / ρ z‖ ∂(P S) :=
      integral_congr_ae (hu.mono fun z hz => by simp only [hz])
    rw [e, hPintR]
    exact integral_congr_ae (ae_of_all _ fun z => hnorm h z)
  have hpair : ∀ S (h ν : ℂ → ℂ), ∫ z, ν z * (h z / ρ z) ∂(P S) = ∫ z in S, ν z * h z := by
    intro S h ν
    rw [hPint]
    exact integral_congr_ae (ae_of_all _ fun z => by simp only; rw [mul_left_comm, hdiv])
  -- the family `v_t` and the target `x` in `L¹(P F) × L¹(P (conj F))`
  set v : D → Lp ℂ 1 (P F) × Lp ℂ 1 (P ((starRingEnd ℂ) '' F)) := fun t =>
    ((hint F _ (hψ t.1 t.2).1).toL1 (fun z => ψ t z / ρ z),
      (hint _ _ (hψ t.1 t.2).2).toL1 (fun z => ψ t z / ρ z)) with hv
  set x : Lp ℂ 1 (P F) × Lp ℂ 1 (P ((starRingEnd ℂ) '' F)) :=
    ((hint F φ hφ).toL1 (fun z => φ z / ρ z), 0) with hxdef
  set W : Submodule ℂ (Lp ℂ 1 (P F) × Lp ℂ 1 (P ((starRingEnd ℂ) '' F))) := Submodule.span ℂ (Set.range v)
    with hW
  have hx : x ∈ closure (W : Set (Lp ℂ 1 (P F) × Lp ℂ 1 (P ((starRingEnd ℂ) '' F)))) := by
    by_contra hx
    have hn : ‖(Submodule.Quotient.mk x : _ ⧸ W)‖ ≠ 0 := fun h0 =>
      hx ((QuotientAddGroup.norm_mk_eq_zero_iff_mem_closure (S := W.toAddSubgroup) (m := x)).1 h0)
    obtain ⟨g, -, hg⟩ := exists_dual_vector ℂ (Submodule.Quotient.mk x : _ ⧸ W) hn
    set L := g.comp W.mkQL with hL
    set L₁ := L.comp (ContinuousLinearMap.inl ℂ (Lp ℂ 1 (P F)) (Lp ℂ 1 (P ((starRingEnd ℂ) '' F)))) with hL₁
    set L₂ := L.comp (ContinuousLinearMap.inr ℂ (Lp ℂ 1 (P F)) (Lp ℂ 1 (P ((starRingEnd ℂ) '' F)))) with hL₂
    obtain ⟨ν₁, hν₁m, hν₁b, hν₁r⟩ := h35a_L1_dual_repr L₁
    obtain ⟨ν₂, hν₂m, hν₂b, hν₂r⟩ := h35a_L1_dual_repr L₂
    have hsplit : ∀ p : Lp ℂ 1 (P F) × Lp ℂ 1 (P ((starRingEnd ℂ) '' F)), L p = L₁ p.1 + L₂ p.2 := by
      intro p
      have e : p = (p.1, 0) + (0, p.2) := by simp
      conv_lhs => rw [e]
      rw [map_add]
      rfl
    have hkill : ∀ t : D, L (v t) = 0 := by
      intro t
      rw [hL, ContinuousLinearMap.comp_apply, Submodule.mkQL_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero W).2 (Submodule.subset_span ⟨t, rfl⟩), map_zero]
    have h0 := hann ν₁ ν₂ (hν₁m.mono_ac (hSP F)) (hν₂m.mono_ac (hSP _)) (max ‖L₁‖ ‖L₂‖)
      ((hSP F).ae_le (hν₁b.mono fun z hz => hz.trans (le_max_left _ _)))
      ((hSP _).ae_le (hν₂b.mono fun z hz => hz.trans (le_max_right _ _))) (fun t ht => by
        have e := hkill ⟨t, ht⟩
        rw [hsplit, hv] at e
        simp only at e
        rw [hν₁r, hν₂r, hpair, hpair] at e
        exact e)
    have hLx : L x = 0 := by
      rw [hsplit, hxdef]
      simp only [map_zero, add_zero]
      rw [hν₁r, hpair]
      exact h0
    have hLx' : L x = (‖(Submodule.Quotient.mk x : _ ⧸ W)‖ : ℂ) := by
      rw [hL, ContinuousLinearMap.comp_apply, Submodule.mkQL_apply]
      exact hg
    rw [hLx] at hLx'
    exact hn (by exact_mod_cast hLx'.symm)
  -- extract a finite combination
  obtain ⟨w', hwW, hwd⟩ := Metric.mem_closure_iff.1 hx ε.toReal hδ
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hwW
  have hsumT : ∀ z, ∑ t ∈ c.support.map (Function.Embedding.subtype _),
      (fun t => if h : t ∈ D then c ⟨t, h⟩ else 0) t * ψ t z = ∑ i ∈ c.support, c i * ψ i z := by
    intro z
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Function.Embedding.coe_subtype, Subtype.coe_eta, dif_pos i.2]
  have hw1 : w'.1 = ∑ i ∈ c.support, c i • (v i).1 := by
    rw [← hc, Finsupp.sum, Prod.fst_sum]
    rfl
  have hw2 : w'.2 = ∑ i ∈ c.support, c i • (v i).2 := by
    rw [← hc, Finsupp.sum, Prod.snd_sum]
    rfl
  have hd12 : ‖x.1 - w'.1‖ < ε.toReal ∧ ‖x.2 - w'.2‖ < ε.toReal := by
    rw [dist_eq_norm, Prod.norm_def, max_lt_iff] at hwd
    exact hwd
  have hc1 := s36b_coe_sum (μ := P F) c.support (fun i => c i) (fun i z => ψ i z / ρ z)
    (fun i => hint F _ (hψ i.1 i.2).1)
  have hc2 := s36b_coe_sum (μ := P ((starRingEnd ℂ) '' F)) c.support (fun i => c i) (fun i z => ψ i z / ρ z)
    (fun i => hint _ _ (hψ i.1 i.2).2)
  have hIF : Integrable (fun z => φ z - ∑ i ∈ c.support, c i * ψ i z) (volume.restrict F) :=
    hφ.sub (integrable_finset_sum _ fun i _ => (hψ i.1 i.2).1.const_mul _)
  have hIG : Integrable (fun z => ∑ i ∈ c.support, c i * ψ i z) (volume.restrict ((starRingEnd ℂ) '' F)) :=
    integrable_finset_sum _ fun i _ => (hψ i.1 i.2).2.const_mul _
  refine ⟨c.support.map (Function.Embedding.subtype _), fun t => if h : t ∈ D then c ⟨t, h⟩ else 0, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 ht
    exact i.2
  · simp only [hsumT]
    rw [hpA F _ hIF, ← ENNReal.ofReal_toReal htop]
    refine (ENNReal.ofReal_lt_ofReal_iff hδ).2 ?_
    rw [← hL1 F (fun z => φ z - ∑ i ∈ c.support, c i * ψ i z) (x.1 - w'.1)]
    · exact hd12.1
    · rw [hw1]
      filter_upwards [Lp.coeFn_sub x.1 (∑ i ∈ c.support, c i • (v i).1), (hint F φ hφ).coeFn_toL1, hc1]
        with z e1 e2 e3
      rw [e1, Pi.sub_apply, hxdef]
      simp only
      rw [e2]
      rw [e3, sub_div, Finset.sum_div]
      simp only [mul_div_assoc]
  · simp only [hsumT]
    rw [hpA _ _ hIG, ← ENNReal.ofReal_toReal htop]
    refine (ENNReal.ofReal_lt_ofReal_iff hδ).2 ?_
    rw [← hL1 _ (fun z => ∑ i ∈ c.support, c i * ψ i z) (w'.2)]
    · have : ‖x.2 - w'.2‖ = ‖w'.2‖ := by rw [hxdef]; simp
      rw [← this]
      exact hd12.2
    · rw [hw2]
      filter_upwards [hc2] with z e3
      rw [e3, Finset.sum_div]
      simp only [mul_div_assoc]

/-- **U.** Extension (3.38) and unfolding (3.39) on both halves: `ν₁` on `F` gives a bounded `Γ`-compatible `κ₊` on
`ℍ`, and `z ↦ conj ν₂(z̄)` gives `κ₋`; for integrable holomorphic `f` on `ℍ`,
`∬_F ν₁ Θf = m ∬_ℍ κ₊ f`, and, when `f(w̄) = conj f(w)`, `∬_{conj F} ν₂ Θf = m · conj ∬_ℍ κ₋ f`
(`h36p_extend`, pairing identity of `h36p_poincare`). -/
theorem s36b_unfold (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {ν₁ ν₂ : ℂ → ℂ}
    (hν₁ : AEStronglyMeasurable ν₁ (volume.restrict F))
    (hν₂ : AEStronglyMeasurable ν₂ (volume.restrict ((starRingEnd ℂ) '' F))) {M : ℝ} (hM : 0 ≤ M)
    (hb₁ : ∀ᵐ z ∂(volume.restrict F), ‖ν₁ z‖ ≤ M)
    (hb₂ : ∀ᵐ z ∂(volume.restrict ((starRingEnd ℂ) '' F)), ‖ν₂ z‖ ≤ M) :
    ∃ κp κm : ℂ → ℂ, AEStronglyMeasurable κp (volume.restrict upperHalf) ∧
      (∀ᵐ z ∂(volume.restrict upperHalf), ‖κp z‖ ≤ M) ∧
      AEStronglyMeasurable κm (volume.restrict upperHalf) ∧
      (∀ᵐ z ∂(volume.restrict upperHalf), ‖κm z‖ ≤ M) ∧
      ∀ f : ℂ → ℂ, DifferentiableOn ℂ f upperHalf → phiArea f upperHalf < ⊤ →
        (∫ z in F, ν₁ z * h36p_theta Γ f z) =
            (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) * (∫ ζ in upperHalf, κp ζ * f ζ) ∧
          ((∀ w, f (conj w) = conj (f w)) →
            (∫ z in (starRingEnd ℂ) '' F, ν₂ z * h36p_theta Γ f z) =
              (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) * conj (∫ ζ in upperHalf, κm ζ * f ζ)) := by
  have hme : MeasurableEmbedding (fun z : ℂ => conj z) := Complex.conjLIE.toHomeomorph.measurableEmbedding
  have himg : (starRingEnd ℂ) '' F = (starRingEnd ℂ) ⁻¹' F :=
    congrFun (Set.image_eq_preimage_of_inverse (f := ⇑(starRingEnd ℂ)) (g := ⇑(starRingEnd ℂ))
      Complex.conj_conj Complex.conj_conj) F
  have hmpF : MeasurePreserving (fun z : ℂ => conj z) (volume.restrict F)
      (volume.restrict ((starRingEnd ℂ) ⁻¹' F)) := by
    have := gzE_conj_measurePreserving.restrict_preimage_emb hme ((starRingEnd ℂ) ⁻¹' F)
    have hpre : (fun z : ℂ => conj z) ⁻¹' ((starRingEnd ℂ) ⁻¹' F) = F := by
      ext z
      simp
    rwa [hpre] at this
  rw [himg] at hν₂ hb₂
  -- the reflected coefficient `λ(z) = conj ν₂(z̄)` on `F`
  have hlm : AEStronglyMeasurable (fun z => conj (ν₂ (conj z))) (volume.restrict F) :=
    Complex.continuous_conj.comp_aestronglyMeasurable (hν₂.comp_measurePreserving hmpF)
  have hlb : ∀ᵐ z ∂(volume.restrict F), ‖conj (ν₂ (conj z))‖ ≤ M := by
    filter_upwards [hmpF.quasiMeasurePreserving.ae hb₂] with z hz
    rwa [Complex.norm_conj]
  obtain ⟨κp, hκpm, -, hκpΓ, hκpb, hκpe⟩ := h36p_extend hΓ hF hM hν₁ hb₁
  obtain ⟨κm, hκmm, -, hκmΓ, hκmb, hκme⟩ := h36p_extend hΓ hF hM hlm hlb
  refine ⟨κp, κm, hκpm.restrict, hκpb, hκmm.restrict, hκmb, fun f hf hfA => ⟨?_, fun hc => ?_⟩⟩
  · rw [(h36p_poincare hΓ hF hf hfA).2 κp hκpm.restrict ⟨M, hκpb⟩ hκpΓ]
    unfold beltramiPairing
    exact integral_congr_ae (hκpe.mono fun z hz => by simp only [hz])
  · have e1 : ∫ z in F, ν₂ (conj z) * h36p_theta Γ f (conj z) =
        ∫ y in (starRingEnd ℂ) ⁻¹' F, ν₂ y * h36p_theta Γ f y :=
      hmpF.integral_comp hme (fun y => ν₂ y * h36p_theta Γ f y)
    rw [himg, ← e1]
    have e2 := (h36p_poincare hΓ hF hf hfA).2 κm hκmm.restrict ⟨M, hκmb⟩ hκmΓ
    have e3 : ∫ z in F, κm z * h36p_theta Γ f z = ∫ z in F, conj (ν₂ (conj z)) * h36p_theta Γ f z :=
      integral_congr_ae (hκme.mono fun z hz => by simp only [hz])
    have e4 : (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) * conj (∫ ζ in upperHalf, κm ζ * f ζ) =
        conj ((Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) * ∫ ζ in upperHalf, κm ζ * f ζ) := by
      rw [map_mul, map_natCast]
    rw [e4, e2]
    unfold beltramiPairing
    rw [e3, ← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only
    rw [map_mul, Complex.conj_conj, s36b_theta_conj f hc z]

end LiZhongQC
