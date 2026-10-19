import LiZhongQC.Ch06.S23_QCOnSurfaces
import LiZhongQC.Lemmas.RingCharacterization

/-!
# Local winding `+1` transported through conformal charts (`s24q_lw_`)

Shared helper of `LowGenusQC` and `NielsenBoundary` (§24.2): if `F` is conjugate, through two injective holomorphic
charts `ψ₀` (on `U ∋ z₀`) and `ψ₁` (on `V ∋ F z₀`), to a sense preserving injective map `h` on `D`, then `F` has local
winding `+1` at `z₀` (the shape output by `rc_hloc_of_sensePreserving` and consumed by `s24q_torus_det_pos`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

/-- Homotopy invariance of the winding of `h` along source loops: if `u s` is a homotopy of loops around `0`
inside a set where `h` is continuous and injective, the winding of `t ↦ h (a + u s t) - h a` does not depend on `s`. -/
theorem s24q_lw_h_homotopy {h : ℂ → ℂ} {D : Set ℂ} {a : ℂ}
    (hhc : ContinuousOn h D) (hhi : InjOn h D) {u : ℝ → ℝ → ℂ}
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc 0 1))
    (hper : ∀ s ∈ Icc (0 : ℝ) 1, u s 1 = u s 0)
    (hne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, u s t ≠ 0)
    (haD : a ∈ D) (hD : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, a + u s t ∈ D)
    {L₀ L₁ : ℝ → ℂ} (hL₀ : ContinuousOn L₀ (Icc 0 1)) (hL₁ : ContinuousOn L₁ (Icc 0 1))
    (hL₀e : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L₀ t) = h (a + u 0 t) - h a)
    (hL₁e : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L₁ t) = h (a + u 1 t) - h a) :
    L₀ 1 - L₀ 0 = L₁ 1 - L₁ 0 := by
  refine lift_change_eq_of_homotopy (H := fun s t => h (a + u s t)) (w := h a) ?_ ?_ ?_ hL₀ hL₁ hL₀e hL₁e
  · have hcomp : ContinuousOn (fun p : ℝ × ℝ => a + Function.uncurry u p) (Icc 0 1 ×ˢ Icc 0 1) :=
      continuousOn_const.add hu
    refine hhc.comp hcomp ?_
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    exact hD s hs t ht
  · intro s hs
    simp only [hper s hs]
  · intro s hs t ht heq
    have := hhi (hD s hs t ht) haD heq
    exact hne s hs t ht (by simpa using this)


theorem s24q_lw_winding_conj {F h ψ₀ ψ₁ : ℂ → ℂ} {z₀ : ℂ} {U V D : Set ℂ}
    (hU : IsOpen U) (hz₀ : z₀ ∈ U) (hV : IsOpen V) (hD : IsOpen D)
    (hψ₀ : DifferentiableOn ℂ ψ₀ U) (hψ₀i : Set.InjOn ψ₀ U)
    (hψ₁ : DifferentiableOn ℂ ψ₁ V) (hψ₁i : Set.InjOn ψ₁ V)
    (hFc : ContinuousAt F z₀) (hFz : F z₀ ∈ V) (hψD : Set.MapsTo ψ₀ U D)
    (hcomm : ∀ z ∈ U, F z ∈ V → ψ₁ (F z) = h (ψ₀ z))
    (hhc : ContinuousOn h D) (hhi : Set.InjOn h D) (hhs : IsSensePreserving h D) :
    ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) = F (z₀ + ρ * Complex.exp (2 * π * Complex.I * t)) - F z₀) →
        Lg 1 - Lg 0 = 2 * π * Complex.I := by
  classical
  set a : ℂ := ψ₀ z₀ with ha
  have haD : a ∈ D := hψD hz₀
  have hκ₀ : deriv ψ₀ z₀ ≠ 0 := deriv_ne_zero_of_injOn hU hψ₀ hψ₀i hz₀
  have hκ₁ : deriv ψ₁ (F z₀) ≠ 0 := deriv_ne_zero_of_injOn hV hψ₁ hψ₁i hFz
  set κ₀ := deriv ψ₀ z₀ with hκ₀def
  set κ₁ := deriv ψ₁ (F z₀) with hκ₁def
  have hd₀ : HasDerivAt ψ₀ κ₀ z₀ := (hψ₀.differentiableAt (hU.mem_nhds hz₀)).hasDerivAt
  have hd₁ : HasDerivAt ψ₁ κ₁ (F z₀) := (hψ₁.differentiableAt (hV.mem_nhds hFz)).hasDerivAt
  obtain ⟨ρ₂, hρ₂, hrc⟩ := rc_hloc_of_sensePreserving hD hhc hhi hhs haD
  have hκ₀pos : 0 < ‖κ₀‖ := norm_pos_iff.mpr hκ₀
  have hκ₁pos : 0 < ‖κ₁‖ := norm_pos_iff.mpr hκ₁
  obtain ⟨rD, hrD, hrDsub⟩ := Metric.isOpen_iff.mp hD a haD
  -- eventual properties near `z₀`
  have hev₀ : ∀ᶠ z in 𝓝 z₀, ‖ψ₀ z - a - (z - z₀) * κ₀‖ ≤ (‖κ₀‖ / 2) * ‖z - z₀‖ := by
    have := hd₀.isLittleO.def (half_pos hκ₀pos)
    filter_upwards [this] with z hz
    simpa [smul_eq_mul] using hz
  have hev₁ : ∀ᶠ z in 𝓝 z₀, ‖ψ₁ (F z) - ψ₁ (F z₀) - (F z - F z₀) * κ₁‖ ≤ (‖κ₁‖ / 2) * ‖F z - F z₀‖ := by
    have := hd₁.isLittleO.def (half_pos hκ₁pos)
    have h2 := hFc.tendsto.eventually this
    filter_upwards [h2] with z hz
    simpa [smul_eq_mul] using hz
  have hevU : ∀ᶠ z in 𝓝 z₀, z ∈ U := hU.mem_nhds hz₀
  have hevV : ∀ᶠ z in 𝓝 z₀, F z ∈ V := hFc.tendsto.eventually (hV.mem_nhds hFz)
  have hevball : ∀ᶠ z in 𝓝 z₀, dist (ψ₀ z) a < rD := by
    have hc : ContinuousAt ψ₀ z₀ := (hψ₀.differentiableAt (hU.mem_nhds hz₀)).continuousAt
    exact hc.tendsto.eventually (Metric.ball_mem_nhds a hrD)
  obtain ⟨r, hr, hP⟩ := Metric.eventually_nhds_iff.mp
    (hev₀.and (hev₁.and (hevU.and (hevV.and hevball))))
  refine ⟨min r (min (ρ₂ / ‖κ₀‖) (rD / ‖κ₀‖)), lt_min hr (lt_min (div_pos hρ₂ hκ₀pos) (div_pos hrD hκ₀pos)), ?_⟩
  intro ρ hρ0 hρ1 Lg hLg hLe
  have hρr : ρ < r := lt_of_lt_of_le hρ1 (min_le_left _ _)
  have hρρ₂ : ‖κ₀‖ * ρ < ρ₂ := by
    have := lt_of_lt_of_le hρ1 ((min_le_right _ _).trans (min_le_left _ _))
    rw [lt_div_iff₀ hκ₀pos] at this; linarith
  have hρD : ‖κ₀‖ * ρ < rD := by
    have := lt_of_lt_of_le hρ1 ((min_le_right _ _).trans (min_le_right _ _))
    rw [lt_div_iff₀ hκ₀pos] at this; linarith
  -- circles
  let E : ℝ → ℂ := fun x => Complex.exp ((x : ℂ) * Complex.I)
  have hEn : ∀ x, ‖E x‖ = 1 := fun x => Complex.norm_exp_ofReal_mul_I x
  have hE : ∀ t : ℝ, Complex.exp (2 * π * Complex.I * t) = E (2 * π * t) := by
    intro t; simp only [E]; congr 1; push_cast; ring
  have hE1 : ∀ x : ℝ, E (2 * π * (1 + x)) = E (2 * π * x) := by
    intro x
    simp only [E]
    have : ((2 * π * (1 + x) : ℝ) : ℂ) * Complex.I = (2 * π * Complex.I) + ((2 * π * x : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]
  let c : ℝ → ℂ := fun t => z₀ + ρ * E (2 * π * t)
  have hcc : Continuous c := by
    have : Continuous E := by simp only [E]; fun_prop
    simp only [c]; fun_prop
  have hc1 : c 1 = c 0 := by
    have := hE1 0
    simp only [c, mul_one, add_zero, mul_zero] at this ⊢
    rw [this]
  have hcz : ∀ t, ‖c t - z₀‖ = ρ := by
    intro t; simp only [c, add_sub_cancel_left, norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  have hcd : ∀ t, dist (c t) z₀ < r := fun t => by rw [dist_eq_norm, hcz]; exact hρr
  have hcne : ∀ t, c t ≠ z₀ := fun t h => by
    have := hcz t; rw [h, sub_self, norm_zero] at this; exact absurd this.symm hρ0.ne'
  have hLe' : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (Lg t) = F (c t) - F z₀ := by
    intro t ht; rw [hLe t ht]; simp only [c, hE]
  have hψ₁z : ψ₁ (F z₀) = h a := hcomm z₀ hz₀ hFz
  let G' : ℝ → ℂ := fun t => ψ₁ (F (c t)) - ψ₁ (F z₀)
  have hG'eq : ∀ t, G' t = h (ψ₀ (c t)) - h a := by
    intro t
    simp only [G']
    rw [hcomm (c t) (hP (hcd t)).2.2.1 (hP (hcd t)).2.2.2.1, hψ₁z]
  have hcU : ∀ t, c t ∈ U := fun t => (hP (hcd t)).2.2.1
  have hψ₀c : ContinuousOn (fun t => ψ₀ (c t)) (Icc 0 1) :=
    hψ₀.continuousOn.comp hcc.continuousOn (fun t _ => hcU t)
  have hG'cont : ContinuousOn G' (Icc 0 1) := by
    have : ContinuousOn (fun t => h (ψ₀ (c t)) - h a) (Icc 0 1) :=
      (hhc.comp hψ₀c (fun t _ => hψD (hcU t))).sub continuousOn_const
    exact this.congr fun t _ => hG'eq t
  have hG'ne : ∀ t, G' t ≠ 0 := by
    intro t heq
    rw [hG'eq t, sub_eq_zero] at heq
    exact hcne t (hψ₀i (hcU t) hz₀ (hhi (hψD (hcU t)) haD heq))
  obtain ⟨M', hM'c, hM'e⟩ := exists_continuousOn_log_lift (γ := G') (w := 0) hG'cont
    (fun t _ => hG'ne t)
  -- Step A: transfer of the winding through `ψ₁`
  have hStepA : M' 1 - M' 0 = Lg 1 - Lg 0 := by
    have hβc : ContinuousOn (fun t => κ₁ * (F (c t) - F z₀)) (Icc 0 1) := by
      have : ContinuousOn (fun t => κ₁ * Complex.exp (Lg t)) (Icc 0 1) :=
        continuousOn_const.mul (Complex.continuous_exp.comp_continuousOn hLg)
      exact this.congr fun t ht => by simp only [hLe' t ht]
    refine lift_change_eq_of_norm_sub_lt (γ := G') (β := fun t => κ₁ * (F (c t) - F z₀))
      (L := M') (M := fun t => Lg t + Complex.log κ₁) hG'cont hβc ?_ ?_ ?_ hM'c (hLg.add continuousOn_const) ?_ ?_
      |>.trans (by simp)
    · simp only [G', hc1]
    · simp only [hc1]
    · intro t ht
      have hne : F (c t) - F z₀ ≠ 0 := by rw [← hLe' t ht]; exact Complex.exp_ne_zero _
      have h1 := (hP (hcd t)).2.1
      have h2 : G' t - κ₁ * (F (c t) - F z₀) = ψ₁ (F (c t)) - ψ₁ (F z₀) - (F (c t) - F z₀) * κ₁ := by
        simp only [G']; ring
      rw [h2, norm_mul]
      have hpos : 0 < ‖F (c t) - F z₀‖ := norm_pos_iff.mpr hne
      calc _ ≤ ‖κ₁‖ / 2 * ‖F (c t) - F z₀‖ := h1
        _ < ‖κ₁‖ * ‖F (c t) - F z₀‖ := by nlinarith
    · intro t ht
      rw [hM'e t ht, sub_zero]
    · intro t ht
      rw [Complex.exp_add, hLe' t ht, Complex.exp_log hκ₁]; ring
  -- Step B: transfer of the winding through `ψ₀`
  have hEc : Continuous E := by simp only [E]; fun_prop
  let e : ℝ → ℂ := fun t => ψ₀ (c t) - a
  let k : ℝ → ℂ := fun t => (κ₀ * ρ) * E (2 * π * t)
  have hk : ∀ t, k t = (c t - z₀) * κ₀ := by intro t; simp only [k, c]; ring
  have hkn : ∀ t, ‖k t‖ = ‖κ₀‖ * ρ := by
    intro t; simp only [k, norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  have hee : ∀ t, ‖e t - k t‖ ≤ ‖κ₀‖ / 2 * ρ := by
    intro t
    have h1 := (hP (hcd t)).1
    rw [hcz t] at h1
    have : e t - k t = ψ₀ (c t) - a - (c t - z₀) * κ₀ := by simp only [e, hk]
    rw [this]; exact h1
  have hen : ∀ t, ‖e t‖ < rD := fun t => by
    have := (hP (hcd t)).2.2.2.2
    rwa [dist_eq_norm] at this
  have hec : ContinuousOn e (Icc 0 1) := hψ₀c.sub continuousOn_const
  have hkc : Continuous k := by simp only [k]; fun_prop
  have hEp : E (2 * π * 1) = E (2 * π * 0) := by simpa using hE1 0
  let u : ℝ → ℝ → ℂ := fun s t => (1 - (s : ℂ)) * e t + (s : ℂ) * k t
  have hu : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc 0 1) := by
    have he2 : ContinuousOn (fun p : ℝ × ℝ => e p.2) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
      hec.comp continuous_snd.continuousOn (fun p hp => hp.2)
    have hk2 : ContinuousOn (fun p : ℝ × ℝ => k p.2) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
      (hkc.comp continuous_snd).continuousOn
    have hs1 : Continuous fun p : ℝ × ℝ => (1 - (p.1 : ℂ)) := by fun_prop
    have hs2 : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) := by fun_prop
    exact (hs1.continuousOn.mul he2).add (hs2.continuousOn.mul hk2)
  have hper : ∀ s ∈ Icc (0 : ℝ) 1, u s 1 = u s 0 := by
    intro s _
    have : e 1 = e 0 := by simp only [e, hc1]
    have h2 : k 1 = k 0 := by simp only [k, hEp]
    simp only [u, this, h2]
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, u s t ≠ 0 := by
    intro s hs t _ h0
    have h1 : u s t = k t + (1 - (s : ℂ)) * (e t - k t) := by simp only [u]; ring
    rw [h1] at h0
    have h2 : ‖k t‖ = ‖(1 - (s : ℂ)) * (e t - k t)‖ :=
      (congrArg (fun x => ‖x‖) (show k t = -((1 - (s : ℂ)) * (e t - k t)) by linear_combination h0)).trans
        (norm_neg _)
    rw [hkn t, norm_mul] at h2
    have h3 : ‖(1 - (s : ℂ))‖ = 1 - s := by
      have : (1 - (s : ℂ)) = ((1 - s : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
    rw [h3] at h2
    have := hee t
    nlinarith [hs.1, hs.2, norm_nonneg (e t - k t), mul_pos hκ₀pos hρ0]
  have hDm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, a + u s t ∈ D := by
    intro s hs t _
    apply hrDsub
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    have h3 : ‖(1 - (s : ℂ))‖ = 1 - s := by
      have : (1 - (s : ℂ)) = ((1 - s : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
    have h4 : ‖(s : ℂ)‖ = s := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc ‖u s t‖ ≤ ‖(1 - (s : ℂ)) * e t‖ + ‖(s : ℂ) * k t‖ := norm_add_le _ _
      _ = (1 - s) * ‖e t‖ + s * (‖κ₀‖ * ρ) := by rw [norm_mul, norm_mul, h3, h4, hkn]
      _ ≤ max ‖e t‖ (‖κ₀‖ * ρ) := by
          nlinarith [le_max_left ‖e t‖ (‖κ₀‖ * ρ), le_max_right ‖e t‖ (‖κ₀‖ * ρ), hs.1, hs.2,
            mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 (le_max_left ‖e t‖ (‖κ₀‖ * ρ))),
            mul_nonneg hs.1 (sub_nonneg.2 (le_max_right ‖e t‖ (‖κ₀‖ * ρ)))]
      _ < rD := max_lt (hen t) hρD
  have hkD : ∀ t, a + k t ∈ D := fun t =>
    hrDsub (by rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hkn]; exact hρD)
  have hkne : ∀ t, k t ≠ 0 := fun t h0 => by
    have := hkn t
    rw [h0, norm_zero] at this
    exact (mul_pos hκ₀pos hρ0).ne this
  have hNcont : ContinuousOn (fun t => h (a + k t) - h a) (Icc 0 1) :=
    (hhc.comp (continuousOn_const.add hkc.continuousOn) (fun t _ => hkD t)).sub continuousOn_const
  have hNne : ∀ t ∈ Icc (0 : ℝ) 1, h (a + k t) - h a ≠ 0 := fun t _ h0 =>
    hkne t (by simpa using hhi (hkD t) haD (sub_eq_zero.mp h0))
  obtain ⟨N, hNc, hNe⟩ := exists_continuousOn_log_lift (γ := fun t => h (a + k t) - h a) (w := 0)
    hNcont hNne
  have hB1 : M' 1 - M' 0 = N 1 - N 0 := by
    refine s24q_lw_h_homotopy hhc hhi hu hper hne haD hDm hM'c hNc ?_ ?_
    · intro t ht
      have : a + u 0 t = ψ₀ (c t) := by simp only [u, e]; simp
      rw [this, hM'e t ht, sub_zero, hG'eq]
    · intro t ht
      have : u 1 t = k t := by simp [u]
      rw [this, hNe t ht, sub_zero]
  -- rotation of the circle
  have hEadd : ∀ x y : ℝ, E (x + y) = E x * E y := by
    intro x y; simp only [E]; rw [← Complex.exp_add]; congr 1; push_cast; ring
  let θ : ℝ := Complex.arg κ₀ / (2 * π)
  have hκE : κ₀ = (‖κ₀‖ : ℂ) * E (Complex.arg κ₀) := (Complex.norm_mul_exp_arg_mul_I κ₀).symm
  let v : ℝ → ℝ → ℂ := fun s t => ((‖κ₀‖ * ρ : ℝ) : ℂ) * E (2 * π * (t + (1 - s) * θ))
  have hv0 : ∀ t, v 0 t = k t := by
    intro t
    have h2 : 2 * π * (t + (1 - 0) * θ) = 2 * π * t + Complex.arg κ₀ := by
      simp only [θ]; field_simp; ring
    simp only [v, h2, hEadd, k]
    conv_rhs => rw [hκE]
    push_cast; ring
  have hv1 : ∀ t, v 1 t = ((‖κ₀‖ * ρ : ℝ) : ℂ) * Complex.exp (2 * π * Complex.I * t) := by
    intro t; simp only [v, sub_self, zero_mul, add_zero, hE]
  have hvc : ContinuousOn (Function.uncurry v) (Icc 0 1 ×ˢ Icc 0 1) := by
    have : Continuous (Function.uncurry v) := by
      simp only [v, E]; fun_prop
    exact this.continuousOn
  have hvper : ∀ s ∈ Icc (0 : ℝ) 1, v s 1 = v s 0 := by
    intro s _
    simp only [v, zero_add]
    rw [hE1]
  have hvn : ∀ s t, ‖v s t‖ = ‖κ₀‖ * ρ := by
    intro s t
    show ‖((‖κ₀‖ * ρ : ℝ) : ℂ) * E (2 * π * (t + (1 - s) * θ))‖ = _
    rw [norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hκ₀pos hρ0)]
  have hvne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, v s t ≠ 0 := fun s _ t _ h0 => by
    have := hvn s t
    rw [h0, norm_zero] at this
    exact (mul_pos hκ₀pos hρ0).ne this
  have hvD : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, a + v s t ∈ D := fun s _ t _ =>
    hrDsub (by rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hvn]; exact hρD)
  have hvt1 : Continuous (fun t => v 1 t) := by simp only [v, E]; fun_prop
  have hN'cont : ContinuousOn (fun t => h (a + v 1 t) - h a) (Icc 0 1) :=
    (hhc.comp (continuousOn_const.add hvt1.continuousOn)
      (fun t ht => hvD 1 ⟨zero_le_one, le_refl _⟩ t ht)).sub continuousOn_const
  obtain ⟨N', hN'c, hN'e⟩ := exists_continuousOn_log_lift (γ := fun t => h (a + v 1 t) - h a) (w := 0)
    hN'cont (fun t ht h0 => hvne 1 ⟨zero_le_one, le_refl _⟩ t ht
      (by simpa using hhi (hvD 1 ⟨zero_le_one, le_refl _⟩ t ht) haD (sub_eq_zero.mp h0)))
  have hB2 : N 1 - N 0 = N' 1 - N' 0 := by
    refine s24q_lw_h_homotopy hhc hhi hvc hvper hvne haD hvD hNc hN'c ?_ ?_
    · intro t ht
      rw [hv0, hNe t ht, sub_zero]
    · intro t ht
      rw [hN'e t ht, sub_zero]
  have hB3 : N' 1 - N' 0 = 2 * π * Complex.I := by
    refine hrc (‖κ₀‖ * ρ) (mul_pos hκ₀pos hρ0) hρρ₂ N' hN'c ?_
    intro t ht
    rw [hN'e t ht, sub_zero, hv1]
  rw [← hStepA, hB1, hB2, hB3]

end LiZhongQC
