import LiZhongQC.Lemmas.GeodesicLeftEndpoints
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC

/-- Each inverse radial arm has one fixed quadratic-differential direction.
Its quadratic velocity is a positive real multiple of v^(m+2). -/
theorem s25ep_inverse_radial_straight {φ ζ ψ : ℂ → ℂ} {z₀ : ℂ} {r R B : ℝ}
    {m : ℕ} (hR : 0 < R) (hB : 0 < B) (hBR : B ≤ R) (hψ0 : ψ 0 = z₀)
    (hchart : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
      φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (hψ : ∀ w ∈ closedBall (0 : ℂ) R, ψ w ∈ ball z₀ r ∧ ζ (ψ w) = w ∧
      AnalyticAt ℂ ψ w ∧ HasDerivAt ψ (deriv ζ (ψ w))⁻¹ w)
    {v : ℂ} (hv : ‖v‖ = 1) :
    IsPhiStraightArc φ (fun t : ℝ => ψ (t • v)) 0 B := by
  let c : ℝ := ((m : ℝ) + 2) / 2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcast : (((m : ℂ) + 2) / 2) = (c : ℂ) := by
    dsimp only [c]
    push_cast
    rfl
  have hv0 : v ≠ 0 := by
    intro he
    rw [he, norm_zero] at hv
    exact zero_ne_one hv
  have hd : ∀ w ∈ closedBall (0 : ℂ) R, deriv ζ (ψ w) ≠ 0 :=
    fun w hw => (hchart _ (ball_subset_closedBall (hψ w hw).1)).2.1
  have harc := s25ep_inverse_radial_arc hR hψ0 hψ hd hv
  let C : ℂ := v ^ (m + 2)
  have hC : C ≠ 0 := pow_ne_zero _ hv0
  have hrot : C * exp (-(arg C : ℂ) * I) = (‖C‖ : ℂ) := by
    have he : C = (‖C‖ : ℂ) * exp ((arg C : ℂ) * I) :=
      (Complex.norm_mul_exp_arg_mul_I C).symm
    conv_lhs => arg 1; rw [he]
    rw [mul_assoc, ← Complex.exp_add,
      show (arg C : ℂ) * I + -(arg C : ℂ) * I = 0 by ring,
      Complex.exp_zero, mul_one]
  refine ⟨arg C, ?_⟩
  intro t ht
  have htR : t ∈ Icc (0 : ℝ) R := ⟨ht.1.le, ht.2.le.trans hBR⟩
  have hi := harc.2.2.2.1 t htR
  have hz := hchart _ (ball_subset_closedBall hi.1)
  have hvel : φ (ψ (t • v)) * deriv (fun t : ℝ => ψ (t • v)) t ^ 2 =
      ((c ^ 2 * t ^ m : ℝ) : ℂ) * C := by
    rw [hz.2.2, hi.2.2.1.deriv, hi.2.1, hcast, Complex.real_smul]
    dsimp only [C]
    push_cast
    rw [mul_pow, pow_add]
    have hdn : deriv ζ (ψ (t • v)) ≠ 0 := hz.2.1
    field_simp [hdn]
    <;> ring
  have hpos : 0 < c ^ 2 * t ^ m := mul_pos (sq_pos_of_pos hc) (pow_pos ht.1 _)
  refine ⟨hi.2.2.1.differentiableAt, hi.2.2.2, ?_, ?_⟩
  · rw [hvel]
    exact mul_ne_zero (Complex.ofReal_ne_zero.2 hpos.ne') hC
  · rw [hvel, mul_assoc, hrot, ← Complex.ofReal_mul]
    exact Complex.arg_ofReal_of_nonneg (mul_nonneg hpos.le (norm_nonneg C))

/-- The right radial reparametrization also carries its fixed phi-straight direction. -/
theorem s25ep_right_reparam_straight {φ ζ ψ : ℂ → ℂ} {m : ℕ} {z₀ : ℂ} {r R : ℝ}
    (hR : 0 < R) (hψ0 : ψ 0 = z₀)
    (hinj : InjOn ζ (closedBall z₀ r))
    (han : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z)
    (hchart : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
      φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (hψ : ∀ w ∈ closedBall (0 : ℂ) R, ψ w ∈ ball z₀ r ∧ ζ (ψ w) = w ∧
      AnalyticAt ℂ ψ w ∧ HasDerivAt ψ (deriv ζ (ψ w))⁻¹ w)
    (hd : ∀ w ∈ closedBall (0 : ℂ) R, deriv ζ (ψ w) ≠ 0)
    {f : ℝ → ℂ} {s t : ℝ} (hst : s < t)
    (hf : ContinuousOn f (Icc s t)) (hfi : InjOn f (Icc s t))
    (hmap : MapsTo f (Icc s t) (closedBall z₀ r))
    (hz : ζ (f s) = 0) (hb : ζ (f t) ≠ 0) (hbR : ‖ζ (f t)‖ ≤ R)
    (hrad : ∀ u ∈ Icc s t, ∃ lam ∈ Icc (0 : ℝ) 1, ζ (f u) = lam • ζ (f t)) :
    ∃ (v : ℂ) (B : ℝ) (σ : ℝ → ℂ) (θ : ℝ → ℝ),
      ‖v‖ = 1 ∧ 0 < B ∧ B ≤ R ∧ σ 0 = z₀ ∧ σ B = f t ∧
      IsPhiStraightArc φ σ 0 B ∧ ContDiffOn ℝ 1 σ (Icc 0 B) ∧ InjOn σ (Icc 0 B) ∧
      (∀ q ∈ Icc 0 B, HasDerivAt σ (v * (deriv ζ (σ q))⁻¹) q ∧ deriv σ q ≠ 0) ∧
      ContinuousOn θ (Icc s t) ∧ StrictMonoOn θ (Icc s t) ∧
      BijOn θ (Icc s t) (Icc 0 B) ∧ θ s = 0 ∧ θ t = B ∧
      (∀ u ∈ Icc s t, f u = σ (θ u)) ∧ f '' Icc s t = σ '' Icc 0 B := by
  let b : ℂ := ζ (f t)
  let B : ℝ := ‖b‖
  let v : ℂ := B⁻¹ • b
  let θ : ℝ → ℝ := fun u => ‖ζ (f u)‖
  let σ : ℝ → ℂ := fun q => ψ (q • v)
  have hB : 0 < B := norm_pos_iff.2 hb
  have hv : ‖v‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hB.le)]
    exact inv_mul_cancel₀ hB.ne'
  have hθs : θ s = 0 := by simp only [θ, hz, norm_zero]
  have hθt : θ t = B := rfl
  have hθc : ContinuousOn θ (Icc s t) := by
    apply ContinuousOn.norm
    apply ContinuousOn.comp _ hf hmap
    intro z hz'
    exact (han z hz').continuousAt.continuousWithinAt
  have hcoord : ∀ u ∈ Icc s t, ζ (f u) = θ u • v := by
    intro u hu
    obtain ⟨lam, hlam, he⟩ := hrad u hu
    have hθ : θ u = lam * B := by
      change ‖ζ (f u)‖ = lam * B
      rw [he, norm_smul, Real.norm_of_nonneg hlam.1]
    rw [hθ]
    change ζ (f u) = (lam * B) • (B⁻¹ • b)
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hB.ne', mul_one]
    exact he
  have hθmap : MapsTo θ (Icc s t) (Icc 0 B) := by
    intro u hu
    obtain ⟨lam, hlam, he⟩ := hrad u hu
    refine ⟨norm_nonneg _, ?_⟩
    change ‖ζ (f u)‖ ≤ B
    rw [he, norm_smul, Real.norm_of_nonneg hlam.1]
    exact mul_le_of_le_one_left hB.le hlam.2
  have hθi : InjOn θ (Icc s t) := by
    intro u hu w hw he
    apply hfi hu hw
    apply hinj (hmap hu) (hmap hw)
    rw [hcoord u hu, hcoord w hw, he]
  have hθmono : StrictMonoOn θ (Icc s t) :=
    hθc.strictMonoOn_of_injOn_Icc hst.le (by rw [hθs, hθt]; exact hB.le) hθi
  have hθsurj : SurjOn θ (Icc s t) (Icc 0 B) := by
    have hi := intermediate_value_Icc hst.le hθc
    rw [hθs, hθt] at hi
    exact hi
  have harc := s25ep_inverse_radial_arc hR hψ0 hψ hd hv
  have hsub : Icc (0 : ℝ) B ⊆ Icc 0 R := Icc_subset_Icc le_rfl hbR
  have hfun : ∀ u ∈ Icc s t, f u = σ (θ u) := by
    intro u hu
    have hq := hsub (hθmap hu)
    have hi := harc.2.2.2.1 (θ u) hq
    apply hinj (hmap hu) (ball_subset_closedBall hi.1)
    exact (hcoord u hu).trans hi.2.1.symm
  refine ⟨v, B, σ, θ, hv, hB, hbR, harc.1, ?_,
    s25ep_inverse_radial_straight hR hB hbR hψ0 hchart hψ hv, harc.2.1.mono hsub,
    harc.2.2.1.mono hsub, ?_, hθc, hθmono, ⟨hθmap, hθi, hθsurj⟩,
    hθs, hθt, hfun, ?_⟩
  · exact (hfun t ⟨hst.le, le_rfl⟩).symm
  · intro q hq
    exact (harc.2.2.2.1 q (hsub hq)).2.2
  · apply Subset.antisymm
    · rintro z ⟨u, hu, rfl⟩
      exact ⟨θ u, hθmap hu, (hfun u hu).symm⟩
    · rintro z ⟨q, hq, rfl⟩
      obtain ⟨u, hu, he⟩ := hθsurj hq
      exact ⟨u, hu, by rw [hfun u hu, he]⟩

/-- The actual right endpoint supplies a complete regular phi-straight side with its exact trace. -/
theorem s25ep_actual_right_endpoint_straight {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht₁ : t₀ < 1) (hzero : φ (γ.toFun t₀) = 0) :
    ∃ (ε B : ℝ) (σ : ℝ → ℂ) (θ : ℝ → ℝ),
      0 < ε ∧ t₀ + ε < 1 ∧ 0 < B ∧ σ 0 = γ.toFun t₀ ∧ σ B = γ.toFun (t₀ + ε) ∧
      IsPhiStraightArc φ σ 0 B ∧ ContDiffOn ℝ 1 σ (Icc 0 B) ∧ InjOn σ (Icc 0 B) ∧
      (∀ q ∈ Icc 0 B, DifferentiableAt ℝ σ q ∧ deriv σ q ≠ 0) ∧
      ContinuousOn θ (Icc t₀ (t₀ + ε)) ∧ StrictMonoOn θ (Icc t₀ (t₀ + ε)) ∧
      BijOn θ (Icc t₀ (t₀ + ε)) (Icc 0 B) ∧ θ t₀ = 0 ∧ θ (t₀ + ε) = B ∧
      (∀ u ∈ Icc t₀ (t₀ + ε), γ.toFun u = σ (θ u)) ∧
      γ.toFun '' Icc t₀ (t₀ + ε) = σ '' Icc 0 B := by
  have hz₀ : γ.toFun t₀ ∈ unitDisc := hγ.2.1 ⟨t₀, ht₀, rfl⟩
  obtain ⟨m, ζ, ψ, r, R, hm, hr, hR, hrD, hζ0, hψ0, hinj, hchart, hψ⟩ :=
    s25ep_chart_at_zero hφ hne hz₀ hzero
  obtain ⟨W, hW, hW0, hWr, hζ, -⟩ := s25ep_open_chart hr hR hζ0 hinj
    (fun z hz => (hchart z hz).1) (fun w hw => ⟨(hψ w hw).1, (hψ w hw).2.1⟩)
  have hWD : W ⊆ unitDisc := hWr.trans (ball_subset_closedBall.trans hrD)
  have hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2 :=
    fun z hz => (hchart z (ball_subset_closedBall (hWr hz))).2.2
  obtain ⟨δ, hδ, hγi, hγW, hmin⟩ := s25ep_minimizing_window hφ hne hγ hp ht₀ hW hW0
  obtain ⟨ε, hε, hεmax⟩ := exists_between (lt_min hδ (sub_pos.2 ht₁))
  have heδ : ε < δ := hεmax.trans_le (min_le_left _ _)
  have he1 : ε < 1 - t₀ := hεmax.trans_le (min_le_right _ _)
  have hsub : Icc t₀ (t₀ + ε) ⊆ Icc (0 : ℝ) 1 ∩ Ioo (t₀ - δ) (t₀ + δ) := by
    intro u hu
    exact ⟨⟨ht₀.1.trans hu.1, by linarith [hu.2]⟩,
      ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩
  have hst : t₀ < t₀ + ε := by linarith
  have hsI : t₀ ∈ Icc t₀ (t₀ + ε) := ⟨le_rfl, hst.le⟩
  have htI : t₀ + ε ∈ Icc t₀ (t₀ + ε) := ⟨hst.le, le_rfl⟩
  have hmap : MapsTo γ.toFun (Icc t₀ (t₀ + ε)) W := hγW.mono hsub (Subset.refl _)
  have hfi : InjOn γ.toFun (Icc t₀ (t₀ + ε)) := hγi.mono hsub
  have hb : ζ (γ.toFun (t₀ + ε)) ≠ 0 := by
    intro he
    have hf := hζ.2.1 (hmap htI) (hmap hsI) (he.trans hζ0.symm)
    exact (ne_of_gt hst) (hfi htI hsI hf)
  obtain ⟨K, hK⟩ := hγ.1
  have hKs := hK.mono (hsub.trans inter_subset_left)
  have hrad := s25ep_minimizing_radial m hm hW hWD hζ hq γ hst.le hKs hmap hζ0 hb
    (hmin t₀ (hsub hsI) (t₀ + ε) (hsub htI) hst)
  have hbR : ‖ζ (γ.toFun (t₀ + ε))‖ ≤ R := (mem_ball_zero_iff.1 (hζ.mapsTo (hmap htI))).le
  have hd : ∀ w ∈ closedBall (0 : ℂ) R, deriv ζ (ψ w) ≠ 0 :=
    fun w hw => (hchart _ (ball_subset_closedBall (hψ w hw).1)).2.1
  obtain ⟨v, B, σ, θ, hv, hB, hBR, hσ0, hσB, hσstr, hσc, hσi, hσd,
    hθc, hθm, hθb, hθ0, hθB, hfun, himage⟩ :=
    s25ep_right_reparam_straight hR hψ0 hinj (fun z hz => (hchart z hz).1) hchart hψ hd
      hst hKs.continuousOn hfi (fun u hu => ball_subset_closedBall (hWr (hmap hu)))
      hζ0 hb hbR hrad
  exact ⟨ε, B, σ, θ, hε, by linarith, hB, hσ0, hσB, hσstr, hσc, hσi,
    fun q hq => ⟨(hσd q hq).1.differentiableAt, (hσd q hq).2⟩,
    hθc, hθm, hθb, hθ0, hθB, hfun, himage⟩

/-- The left radial reparametrization also carries its fixed phi-straight direction. -/
theorem s25ep_left_reparam_straight {φ ζ ψ : ℂ → ℂ} {m : ℕ} {z₀ : ℂ} {r R : ℝ}
    (hR : 0 < R) (hψ0 : ψ 0 = z₀)
    (hinj : InjOn ζ (closedBall z₀ r))
    (han : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z)
    (hchart : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
      φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (hψ : ∀ w ∈ closedBall (0 : ℂ) R, ψ w ∈ ball z₀ r ∧ ζ (ψ w) = w ∧
      AnalyticAt ℂ ψ w ∧ HasDerivAt ψ (deriv ζ (ψ w))⁻¹ w)
    (hd : ∀ w ∈ closedBall (0 : ℂ) R, deriv ζ (ψ w) ≠ 0)
    {f : ℝ → ℂ} {s t : ℝ} (hst : s < t)
    (hf : ContinuousOn f (Icc s t)) (hfi : InjOn f (Icc s t))
    (hmap : MapsTo f (Icc s t) (closedBall z₀ r))
    (hz : ζ (f t) = 0) (hb : ζ (f s) ≠ 0) (hbR : ‖ζ (f s)‖ ≤ R)
    (hrad : ∀ u ∈ Icc s t, ∃ lam ∈ Icc (0 : ℝ) 1, ζ (f u) = lam • ζ (f s)) :
    ∃ (v : ℂ) (B : ℝ) (σ : ℝ → ℂ) (θ : ℝ → ℝ),
      ‖v‖ = 1 ∧ 0 < B ∧ B ≤ R ∧ σ 0 = z₀ ∧ σ B = f s ∧
      IsPhiStraightArc φ σ 0 B ∧ ContDiffOn ℝ 1 σ (Icc 0 B) ∧ InjOn σ (Icc 0 B) ∧
      (∀ q ∈ Icc 0 B, HasDerivAt σ (v * (deriv ζ (σ q))⁻¹) q ∧ deriv σ q ≠ 0) ∧
      ContinuousOn θ (Icc s t) ∧ StrictAntiOn θ (Icc s t) ∧
      BijOn θ (Icc s t) (Icc 0 B) ∧ θ s = B ∧ θ t = 0 ∧
      (∀ u ∈ Icc s t, f u = σ (θ u)) ∧ f '' Icc s t = σ '' Icc 0 B := by
  let b : ℂ := ζ (f s)
  let B : ℝ := ‖b‖
  let v : ℂ := B⁻¹ • b
  let θ : ℝ → ℝ := fun u => ‖ζ (f u)‖
  let σ : ℝ → ℂ := fun q => ψ (q • v)
  have hB : 0 < B := norm_pos_iff.2 hb
  have hv : ‖v‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hB.le)]
    exact inv_mul_cancel₀ hB.ne'
  have hθs : θ s = B := rfl
  have hθt : θ t = 0 := by simp only [θ, hz, norm_zero]
  have hθc : ContinuousOn θ (Icc s t) := by
    apply ContinuousOn.norm
    apply ContinuousOn.comp _ hf hmap
    intro z hz'
    exact (han z hz').continuousAt.continuousWithinAt
  have hcoord : ∀ u ∈ Icc s t, ζ (f u) = θ u • v := by
    intro u hu
    obtain ⟨lam, hlam, he⟩ := hrad u hu
    have hθ : θ u = lam * B := by
      change ‖ζ (f u)‖ = lam * B
      rw [he, norm_smul, Real.norm_of_nonneg hlam.1]
    rw [hθ]
    change ζ (f u) = (lam * B) • (B⁻¹ • b)
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hB.ne', mul_one]
    exact he
  have hθmap : MapsTo θ (Icc s t) (Icc 0 B) := by
    intro u hu
    obtain ⟨lam, hlam, he⟩ := hrad u hu
    refine ⟨norm_nonneg _, ?_⟩
    change ‖ζ (f u)‖ ≤ B
    rw [he, norm_smul, Real.norm_of_nonneg hlam.1]
    exact mul_le_of_le_one_left hB.le hlam.2
  have hθi : InjOn θ (Icc s t) := by
    intro u hu w hw he
    apply hfi hu hw
    apply hinj (hmap hu) (hmap hw)
    rw [hcoord u hu, hcoord w hw, he]
  have hθmono : StrictAntiOn θ (Icc s t) :=
    hθc.strictAntiOn_of_injOn_Icc hst.le (by rw [hθs, hθt]; exact hB.le) hθi
  have hθsurj : SurjOn θ (Icc s t) (Icc 0 B) := by
    have hi := intermediate_value_Icc' hst.le hθc
    rw [hθs, hθt] at hi
    exact hi
  have harc := s25ep_inverse_radial_arc hR hψ0 hψ hd hv
  have hsub : Icc (0 : ℝ) B ⊆ Icc 0 R := Icc_subset_Icc le_rfl hbR
  have hfun : ∀ u ∈ Icc s t, f u = σ (θ u) := by
    intro u hu
    have hq := hsub (hθmap hu)
    have hi := harc.2.2.2.1 (θ u) hq
    apply hinj (hmap hu) (ball_subset_closedBall hi.1)
    exact (hcoord u hu).trans hi.2.1.symm
  refine ⟨v, B, σ, θ, hv, hB, hbR, harc.1, ?_,
    s25ep_inverse_radial_straight hR hB hbR hψ0 hchart hψ hv, harc.2.1.mono hsub,
    harc.2.2.1.mono hsub, ?_, hθc, hθmono, ⟨hθmap, hθi, hθsurj⟩,
    hθs, hθt, hfun, ?_⟩
  · exact (hfun s ⟨le_rfl, hst.le⟩).symm
  · intro q hq
    exact (harc.2.2.2.1 q (hsub hq)).2.2
  · apply Subset.antisymm
    · rintro z ⟨u, hu, rfl⟩
      exact ⟨θ u, hθmap hu, (hfun u hu).symm⟩
    · rintro z ⟨q, hq, rfl⟩
      obtain ⟨u, hu, he⟩ := hθsurj hq
      exact ⟨u, hu, by rw [hfun u hu, he]⟩

/-- The actual left endpoint supplies a complete regular phi-straight side with its exact trace. -/
theorem s25ep_actual_left_endpoint_straight {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht₁ : 0 < t₀) (hzero : φ (γ.toFun t₀) = 0) :
    ∃ (ε B : ℝ) (σ : ℝ → ℂ) (θ : ℝ → ℝ),
      0 < ε ∧ 0 < t₀ - ε ∧ 0 < B ∧ σ 0 = γ.toFun t₀ ∧ σ B = γ.toFun (t₀ - ε) ∧
      IsPhiStraightArc φ σ 0 B ∧ ContDiffOn ℝ 1 σ (Icc 0 B) ∧ InjOn σ (Icc 0 B) ∧
      (∀ q ∈ Icc 0 B, DifferentiableAt ℝ σ q ∧ deriv σ q ≠ 0) ∧
      ContinuousOn θ (Icc (t₀ - ε) t₀) ∧ StrictAntiOn θ (Icc (t₀ - ε) t₀) ∧
      BijOn θ (Icc (t₀ - ε) t₀) (Icc 0 B) ∧ θ t₀ = 0 ∧ θ (t₀ - ε) = B ∧
      (∀ u ∈ Icc (t₀ - ε) t₀, γ.toFun u = σ (θ u)) ∧
      γ.toFun '' Icc (t₀ - ε) t₀ = σ '' Icc 0 B := by
  have hz₀ : γ.toFun t₀ ∈ unitDisc := hγ.2.1 ⟨t₀, ht₀, rfl⟩
  obtain ⟨m, ζ, ψ, r, R, hm, hr, hR, hrD, hζ0, hψ0, hinj, hchart, hψ⟩ :=
    s25ep_chart_at_zero hφ hne hz₀ hzero
  obtain ⟨W, hW, hW0, hWr, hζ, -⟩ := s25ep_open_chart hr hR hζ0 hinj
    (fun z hz => (hchart z hz).1) (fun w hw => ⟨(hψ w hw).1, (hψ w hw).2.1⟩)
  have hWD : W ⊆ unitDisc := hWr.trans (ball_subset_closedBall.trans hrD)
  have hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2 :=
    fun z hz => (hchart z (ball_subset_closedBall (hWr hz))).2.2
  obtain ⟨δ, hδ, hγi, hγW, hmin⟩ := s25ep_minimizing_window hφ hne hγ hp ht₀ hW hW0
  obtain ⟨ε, hε, hεmax⟩ := exists_between (lt_min hδ ht₁)
  have heδ : ε < δ := hεmax.trans_le (min_le_left _ _)
  have he0 : ε < t₀ := hεmax.trans_le (min_le_right _ _)
  have hsub : Icc (t₀ - ε) t₀ ⊆ Icc (0 : ℝ) 1 ∩ Ioo (t₀ - δ) (t₀ + δ) := by
    intro u hu
    exact ⟨⟨by linarith [hu.1], hu.2.trans ht₀.2⟩,
      ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩
  have hst : t₀ - ε < t₀ := by linarith
  have hsI : t₀ - ε ∈ Icc (t₀ - ε) t₀ := ⟨le_rfl, hst.le⟩
  have htI : t₀ ∈ Icc (t₀ - ε) t₀ := ⟨hst.le, le_rfl⟩
  have hmap : MapsTo γ.toFun (Icc (t₀ - ε) t₀) W := hγW.mono hsub (Subset.refl _)
  have hfi : InjOn γ.toFun (Icc (t₀ - ε) t₀) := hγi.mono hsub
  have hb : ζ (γ.toFun (t₀ - ε)) ≠ 0 := by
    intro he
    have hf := hζ.2.1 (hmap hsI) (hmap htI) (he.trans hζ0.symm)
    exact (ne_of_lt hst) (hfi hsI htI hf)
  obtain ⟨K, hK⟩ := hγ.1
  have hKs := hK.mono (hsub.trans inter_subset_left)
  have hrad := s25ep_minimizing_radial_left m hm hW hWD hζ hq γ hst.le hKs hmap hζ0 hb
    (hmin (t₀ - ε) (hsub hsI) t₀ (hsub htI) hst)
  have hbR : ‖ζ (γ.toFun (t₀ - ε))‖ ≤ R := (mem_ball_zero_iff.1 (hζ.mapsTo (hmap hsI))).le
  have hd : ∀ w ∈ closedBall (0 : ℂ) R, deriv ζ (ψ w) ≠ 0 :=
    fun w hw => (hchart _ (ball_subset_closedBall (hψ w hw).1)).2.1
  obtain ⟨v, B, σ, θ, hv, hB, hBR, hσ0, hσB, hσstr, hσc, hσi, hσd,
    hθc, hθm, hθb, hθB, hθ0, hfun, himage⟩ :=
    s25ep_left_reparam_straight hR hψ0 hinj (fun z hz => (hchart z hz).1) hchart hψ hd
      hst hKs.continuousOn hfi (fun u hu => ball_subset_closedBall (hWr (hmap hu)))
      hζ0 hb hbR hrad
  exact ⟨ε, B, σ, θ, hε, by linarith, hB, hσ0, hσB, hσstr, hσc, hσi,
    fun q hq => ⟨(hσd q hq).1.differentiableAt, (hσd q hq).2⟩,
    hθc, hθm, hθb, hθ0, hθB, hfun, himage⟩

end LiZhongQC

