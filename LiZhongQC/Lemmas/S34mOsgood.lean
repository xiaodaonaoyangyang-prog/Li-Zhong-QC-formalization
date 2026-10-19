import Mathlib

/-!
# Osgood's lemma (R83 S34 bank module, 精英下属5)

A function on an open subset of `ℂⁿ`, valued in a complex Banach space, which is continuous and holomorphic in each
variable separately is analytic (`s34m_osgood`).  Helpers: `s34m_ph` (a `C(X, E)`-valued family, continuous on a
closed disc and pointwise holomorphic, is analytic: it is its own Banach-valued Cauchy integral) and `s34m_pairing`
(the integration pairing on `C([0, 2π], ℂ) × C([0, 2π], F)` as a continuous bilinear map).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace LiZhongQC

/-- **Parametric holomorphy.**  A family `Φ : ℂ → C(X, E)` (`X` compact) which is continuous on a closed disc and
holomorphic at each point `x ∈ X` is analytic (as a `C(X, E)`-valued map) on the open disc: it is its own Banach-valued
Cauchy integral. -/
theorem s34m_ph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {Φ : ℂ → C(X, E)} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ContinuousOn Φ (closedBall c R)) (hd : ∀ x, DifferentiableOn ℂ (fun w => Φ w x) (ball c R)) :
    AnalyticOnNhd ℂ Φ (ball c R) := by
  set R' : ℝ≥0 := ⟨R, hR.le⟩ with hR'
  have hci : CircleIntegrable Φ c R := (hc.mono sphere_subset_closedBall).circleIntegrable hR.le
  have hps := hasFPowerSeriesOn_cauchy_integral (R := R') hci (by
    rw [← NNReal.coe_pos]
    exact hR)
  have heq : ∀ w ∈ ball c R, Φ w = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • Φ z := by
    intro w hw
    ext x
    have hint : CircleIntegrable (fun z => (z - w)⁻¹ • Φ z) c R := by
      refine ContinuousOn.circleIntegrable hR.le ?_
      refine ((continuousOn_id.sub continuousOn_const).inv₀ ?_).smul (hc.mono sphere_subset_closedBall)
      intro z hz h0
      have h0' : z - w = 0 := h0
      rw [sub_eq_zero] at h0'
      rw [mem_sphere] at hz
      rw [mem_ball] at hw
      rw [h0'] at hz
      linarith
    have hcomm : (∮ z in C(c, R), (z - w)⁻¹ • Φ z) x = ∮ z in C(c, R), (z - w)⁻¹ • Φ z x := by
      have := (ContinuousMap.evalCLM ℂ x).intervalIntegral_comp_comm ((circleIntegrable_iff R).1 hint)
      simpa [circleIntegral] using this.symm
    rw [ContinuousMap.smul_apply, hcomm]
    exact (two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty hw
      ((continuous_eval_const x).comp_continuousOn hc)
      (fun z hz => (hd x z hz.1).differentiableAt (isOpen_ball.mem_nhds hz.1))).symm
  intro w hw
  exact (hps.analyticAt_of_mem (y := w) (by rw [Metric.eball_coe]; exact hw)).congr
    (by filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'' using (heq w' hw'').symm)

/-- The integration pairing `(q, h) ↦ ∫₀^{2π} q(θ) h(θ) dθ` of `C([0, 2π], ℂ) × C([0, 2π], F)` into `F`, as a
continuous bilinear map. -/
theorem s34m_pairing (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] :
    ∃ J : C(Icc (0 : ℝ) (2 * π), ℂ) →L[ℂ] C(Icc (0 : ℝ) (2 * π), F) →L[ℂ] F, ∀ q h,
      J q h = ∫ θ in (0 : ℝ)..2 * π, IccExtend Real.two_pi_pos.le q θ • IccExtend Real.two_pi_pos.le h θ := by
  have hci : ∀ (q : C(Icc (0 : ℝ) (2 * π), ℂ)) (h : C(Icc (0 : ℝ) (2 * π), F)),
      IntervalIntegrable (fun θ => IccExtend Real.two_pi_pos.le q θ • IccExtend Real.two_pi_pos.le h θ)
        volume 0 (2 * π) := fun q h =>
    ((continuous_IccExtend_iff.2 q.continuous).smul (continuous_IccExtend_iff.2 h.continuous)).intervalIntegrable _ _
  refine ⟨LinearMap.mkContinuous₂ (LinearMap.mk₂ ℂ
    (fun q h => ∫ θ in (0 : ℝ)..2 * π, IccExtend Real.two_pi_pos.le q θ • IccExtend Real.two_pi_pos.le h θ)
    (fun q₁ q₂ h => by
      rw [← intervalIntegral.integral_add (hci q₁ h) (hci q₂ h)]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [IccExtend, Function.comp_apply, ContinuousMap.add_apply, add_smul])
    (fun c q h => by
      rw [← intervalIntegral.integral_smul]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [IccExtend, Function.comp_apply, ContinuousMap.smul_apply, smul_eq_mul, mul_smul])
    (fun q h₁ h₂ => by
      rw [← intervalIntegral.integral_add (hci q h₁) (hci q h₂)]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [IccExtend, Function.comp_apply, ContinuousMap.add_apply, smul_add])
    (fun c q h => by
      rw [← intervalIntegral.integral_smul]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [IccExtend, Function.comp_apply, ContinuousMap.smul_apply, smul_comm c])) (2 * π) ?_,
    fun q h => rfl⟩
  intro q h
  show ‖∫ θ in (0 : ℝ)..2 * π, IccExtend Real.two_pi_pos.le q θ • IccExtend Real.two_pi_pos.le h θ‖ ≤
    2 * π * ‖q‖ * ‖h‖
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π) (C := ‖q‖ * ‖h‖)
    (f := fun θ => IccExtend Real.two_pi_pos.le q θ • IccExtend Real.two_pi_pos.le h θ) (fun θ _ => by
      rw [norm_smul]
      exact mul_le_mul (ContinuousMap.norm_coe_le_norm q _) (ContinuousMap.norm_coe_le_norm h _)
        (norm_nonneg _) (norm_nonneg _))
  rw [sub_zero, abs_of_pos Real.two_pi_pos] at hb
  linarith

/-- **Osgood's lemma.**  A function on an open subset of `ℂⁿ` which is continuous and holomorphic in each variable
separately is analytic. -/
theorem s34m_osgood {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : (Fin n → ℂ) → F} {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hc : ContinuousOn f U)
    (hs : ∀ x ∈ U, ∀ i, DifferentiableAt ℂ (fun s : ℂ => f (Function.update x i s)) (x i)) :
    AnalyticOnNhd ℂ f U := by
  induction n generalizing F with
  | zero =>
    intro x₀ _
    have hf : (fun _ => f x₀) = f := funext fun x => congrArg f (Subsingleton.elim x₀ x)
    rw [← hf]
    exact analyticAt_const
  | succ n ih =>
    classical
    intro x₀ hx₀
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
    have hr0 : 0 < ε / 2 := by positivity
    set r := ε / 2 with hr
    have hK : closedBall x₀ r ⊆ U := (closedBall_subset_ball (by linarith)).trans hball
    set s₀ := x₀ 0 with hs₀
    set y₀ : Fin n → ℂ := Fin.tail x₀ with hy₀
    have hcons : ∀ (a : ℂ) (y : Fin n → ℂ), ‖a - s₀‖ ≤ r → ‖y - y₀‖ ≤ r → Fin.cons a y ∈ U := by
      intro a y ha hy
      apply hK
      rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hr0.le]
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha
      · have := (pi_norm_le_iff_of_nonneg hr0.le).1 hy j
        simpa [y₀, Fin.tail] using this
    have hcm : ∀ θ : ℝ, ‖circleMap s₀ r θ - s₀‖ = r := fun θ => by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr0]
    have hyb : ∀ y ∈ closedBall y₀ r, ‖y - y₀‖ ≤ r := fun y hy => by
      rwa [mem_closedBall, dist_eq_norm] at hy
    -- the `C([0, 2π], F)`-valued function `g y = (θ ↦ f(circleMap s₀ r θ, y))`
    have hgc : ∀ y ∈ closedBall y₀ r,
        Continuous (fun θ : Icc (0 : ℝ) (2 * π) => f (Fin.cons (circleMap s₀ r θ) y)) := fun y hy =>
      hc.comp_continuous (((continuous_circleMap s₀ r).comp continuous_subtype_val).finCons continuous_const)
        fun θ => hcons _ _ (hcm _).le (hyb y hy)
    let g : (Fin n → ℂ) → C(Icc (0 : ℝ) (2 * π), F) := fun y =>
      if h : y ∈ closedBall y₀ r then ⟨fun θ => f (Fin.cons (circleMap s₀ r θ) y), hgc y h⟩ else 0
    have hg_apply : ∀ y ∈ closedBall y₀ r, ∀ θ : Icc (0 : ℝ) (2 * π),
        g y θ = f (Fin.cons (circleMap s₀ r θ) y) := by
      intro y hy θ
      simp only [g, hy, dite_true]
      rfl
    have hgcont : ContinuousOn g (closedBall y₀ r) := by
      rw [continuousOn_iff_continuous_domRestrict]
      let H : C(closedBall y₀ r × Icc (0 : ℝ) (2 * π), F) :=
        ⟨fun p => f (Fin.cons (circleMap s₀ r p.2) p.1.1),
          hc.comp_continuous (((continuous_circleMap s₀ r).comp (continuous_subtype_val.comp continuous_snd)).finCons
            (continuous_subtype_val.comp continuous_fst)) fun p => hcons _ _ (hcm _).le (hyb p.1.1 p.1.2)⟩
      convert H.curry.continuous using 1
      funext y
      ext θ
      simp only [domRestrict_apply, ContinuousMap.curry_apply]
      exact hg_apply y.1 y.2 θ
    have hgsep : ∀ y ∈ ball y₀ r, ∀ i,
        DifferentiableAt ℂ (fun w : ℂ => g (Function.update y i w)) (y i) := by
      intro y hy i
      rw [mem_ball, dist_eq_norm] at hy
      have hδ0 : 0 < (r - ‖y - y₀‖) / 2 := by
        have : 0 < r - ‖y - y₀‖ := by linarith
        positivity
      set δ := (r - ‖y - y₀‖) / 2 with hδ
      have hyj : ∀ j, ‖y j - y₀ j‖ ≤ ‖y - y₀‖ := fun j => by
        simpa using norm_le_pi_norm (y - y₀) j
      have hupd : ∀ w ∈ closedBall (y i) δ, Function.update y i w ∈ closedBall y₀ r := by
        intro w hw
        rw [mem_closedBall, dist_eq_norm] at hw
        rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hr0.le]
        intro j
        by_cases hj : j = i
        · subst hj
          rw [Pi.sub_apply, Function.update_self]
          calc ‖w - y₀ j‖ = ‖(w - y j) + (y j - y₀ j)‖ := by rw [sub_add_sub_cancel]
            _ ≤ ‖w - y j‖ + ‖y j - y₀ j‖ := norm_add_le _ _
            _ ≤ r := by linarith [hyj j]
        · rw [Pi.sub_apply, Function.update_of_ne hj]
          linarith [hyj j]
      have hΦc : ContinuousOn (fun w : ℂ => g (Function.update y i w)) (closedBall (y i) δ) :=
        hgcont.comp (continuous_const.update i continuous_id : Continuous fun w : ℂ => Function.update y i w).continuousOn hupd
      have hΦd : ∀ θ : Icc (0 : ℝ) (2 * π),
          DifferentiableOn ℂ (fun w : ℂ => g (Function.update y i w) θ) (ball (y i) δ) := by
        intro θ w hw
        have hwc : w ∈ closedBall (y i) δ := ball_subset_closedBall hw
        have hx : Fin.cons (circleMap s₀ r θ) (Function.update y i w) ∈ U :=
          hcons _ _ (hcm _).le (hyb _ (hupd w hwc))
        have hd := hs _ hx i.succ
        have e1 : (fun s => f (Function.update (Fin.cons (circleMap s₀ r θ) (Function.update y i w)) i.succ s)) =
            fun s => f (Fin.cons (circleMap s₀ r θ) (Function.update y i s)) := by
          funext s
          rw [← Fin.cons_update, Function.update_idem]
        have e2 : (Fin.cons (circleMap s₀ r θ) (Function.update y i w) : Fin (n + 1) → ℂ) i.succ = w := by
          simp
        rw [e1, e2] at hd
        refine (hd.differentiableWithinAt).congr (fun w' hw' => ?_) ?_
        · rw [hg_apply _ (hupd w' (ball_subset_closedBall hw'))]
        · rw [hg_apply _ (hupd w hwc)]
      exact ((s34m_ph hδ0 hΦc hΦd) (y i) (mem_ball_self hδ0)).differentiableAt
    have hgA : AnalyticAt ℂ g y₀ :=
      ih isOpen_ball (hgcont.mono ball_subset_closedBall) hgsep y₀ (mem_ball_self hr0)
    -- the Cauchy kernel `Q s = (θ ↦ (2πi)⁻¹ (circleMap 0 r θ) i (circleMap s₀ r θ - s)⁻¹)`
    have hne : ∀ s ∈ ball s₀ r, ∀ θ : ℝ, circleMap s₀ r θ - s ≠ 0 := by
      intro s hs θ h0
      rw [sub_eq_zero] at h0
      have h1 := hcm θ
      rw [h0] at h1
      rw [mem_ball, dist_eq_norm] at hs
      linarith
    have hQc : ∀ s ∈ ball s₀ r, Continuous (fun θ : Icc (0 : ℝ) (2 * π) =>
        (2 * π * I : ℂ)⁻¹ * (circleMap 0 r θ * I) * (circleMap s₀ r θ - s)⁻¹) := fun s hs =>
      (continuous_const.mul (((continuous_circleMap 0 r).comp continuous_subtype_val).mul continuous_const)).mul
        ((((continuous_circleMap s₀ r).comp continuous_subtype_val).sub continuous_const).inv₀ fun θ => hne s hs θ)
    let Q : ℂ → C(Icc (0 : ℝ) (2 * π), ℂ) := fun s =>
      if h : s ∈ ball s₀ r then
        ⟨fun θ => (2 * π * I : ℂ)⁻¹ * (circleMap 0 r θ * I) * (circleMap s₀ r θ - s)⁻¹, hQc s h⟩ else 0
    have hQ_apply : ∀ s ∈ ball s₀ r, ∀ θ : Icc (0 : ℝ) (2 * π),
        Q s θ = (2 * π * I : ℂ)⁻¹ * (circleMap 0 r θ * I) * (circleMap s₀ r θ - s)⁻¹ := by
      intro s hs θ
      simp only [Q, hs, dite_true]
      rfl
    have hr2 : 0 < r / 2 := by positivity
    have hsub : closedBall s₀ (r / 2) ⊆ ball s₀ r := closedBall_subset_ball (by linarith)
    have hQcont : ContinuousOn Q (closedBall s₀ (r / 2)) := by
      rw [continuousOn_iff_continuous_domRestrict]
      let H : C(closedBall s₀ (r / 2) × Icc (0 : ℝ) (2 * π), ℂ) :=
        ⟨fun p => (2 * π * I : ℂ)⁻¹ * (circleMap 0 r p.2 * I) * (circleMap s₀ r p.2 - p.1.1)⁻¹,
          (continuous_const.mul (((continuous_circleMap 0 r).comp (continuous_subtype_val.comp continuous_snd)).mul
            continuous_const)).mul ((((continuous_circleMap s₀ r).comp (continuous_subtype_val.comp
              continuous_snd)).sub (continuous_subtype_val.comp continuous_fst)).inv₀
                fun p => hne _ (hsub p.1.2) _)⟩
      convert H.curry.continuous using 1
      funext s
      ext θ
      simp only [domRestrict_apply, ContinuousMap.curry_apply]
      exact hQ_apply s.1 (hsub s.2) θ
    have hQd : ∀ θ : Icc (0 : ℝ) (2 * π), DifferentiableOn ℂ (fun s => Q s θ) (ball s₀ (r / 2)) := by
      intro θ s hs
      have hs' : s ∈ ball s₀ r := hsub (ball_subset_closedBall hs)
      have hD : DifferentiableAt ℂ (fun s' : ℂ =>
          (2 * π * I : ℂ)⁻¹ * (circleMap 0 r θ * I) * (circleMap s₀ r θ - s')⁻¹) s :=
        (((differentiableAt_const (circleMap s₀ r θ)).sub differentiableAt_id).inv (hne s hs' θ)).const_mul _
      exact hD.differentiableWithinAt.congr (fun s' hs'' => hQ_apply s' (hsub (ball_subset_closedBall hs'')) θ)
        (hQ_apply s hs' θ)
    have hQA : AnalyticAt ℂ Q s₀ := s34m_ph hr2 hQcont hQd s₀ (mem_ball_self hr2)
    -- the Cauchy formula in the first variable
    obtain ⟨J, hJ⟩ := s34m_pairing F
    have hcauchy : ∀ s ∈ ball s₀ r, ∀ y ∈ ball y₀ r, f (Fin.cons s y) = J (Q s) (g y) := by
      intro s hs1 y hy
      have hy' : y ∈ closedBall y₀ r := ball_subset_closedBall hy
      have hFc : ContinuousOn (fun z : ℂ => f (Fin.cons z y)) (closedBall s₀ r) :=
        hc.comp (Continuous.finCons (A := fun _ => ℂ) continuous_id continuous_const).continuousOn fun z hz =>
          hcons _ _ (by rwa [mem_closedBall, dist_eq_norm] at hz) (hyb y hy')
      have hFd : ∀ z ∈ ball s₀ r \ ∅, DifferentiableAt ℂ (fun z : ℂ => f (Fin.cons z y)) z := by
        intro z hz
        have hx : Fin.cons z y ∈ U :=
          hcons _ _ (by have := hz.1; rw [mem_ball, dist_eq_norm] at this; exact this.le) (hyb y hy')
        have hd := hs _ hx 0
        simp only [Fin.update_cons_zero, Fin.cons_zero] at hd
        exact hd
      rw [← two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty hs1
        hFc hFd, hJ, circleIntegral, ← intervalIntegral.integral_smul]
      refine intervalIntegral.integral_congr fun θ hθ => ?_
      rw [uIcc_of_le Real.two_pi_pos.le] at hθ
      simp only [IccExtend_of_mem _ _ hθ, hQ_apply s hs1, hg_apply y hy', deriv_circleMap, smul_smul]
      congr 1
      ring
    -- assembly
    have h0A : AnalyticAt ℂ (fun x : Fin (n + 1) → ℂ => x 0) x₀ :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) 0).analyticAt x₀
    have htA : AnalyticAt ℂ (fun x : Fin (n + 1) → ℂ => Fin.tail x) x₀ :=
      (ContinuousLinearMap.pi fun j : Fin n =>
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) j.succ).analyticAt x₀
    have hA : AnalyticAt ℂ (fun x : Fin (n + 1) → ℂ => J (Q (x 0)) (g (Fin.tail x))) x₀ :=
      AnalyticAt.comp (g := fun p : C(Icc (0 : ℝ) (2 * π), ℂ) × C(Icc (0 : ℝ) (2 * π), F) => J p.1 p.2)
        (f := fun x : Fin (n + 1) → ℂ => (Q (x 0), g (Fin.tail x))) (J.analyticAt_bilinear (Q s₀, g y₀))
        ((AnalyticAt.comp (g := Q) (f := fun x : Fin (n + 1) → ℂ => x 0) (x := x₀) hQA h0A).prod
          (AnalyticAt.comp (g := g) (f := fun x : Fin (n + 1) → ℂ => Fin.tail x) (x := x₀) hgA htA))
    refine hA.congr ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr0)] with x hx
    rw [mem_ball, dist_eq_norm] at hx
    have h1 : x 0 ∈ ball s₀ r := by
      rw [mem_ball, dist_eq_norm]
      exact lt_of_le_of_lt (by simpa using norm_le_pi_norm (x - x₀) 0) hx
    have h2 : Fin.tail x ∈ ball y₀ r := by
      rw [mem_ball, dist_eq_norm, pi_norm_lt_iff hr0]
      intro j
      exact lt_of_le_of_lt (by simpa [y₀, Fin.tail] using norm_le_pi_norm (x - x₀) j.succ) hx
    rw [← hcauchy _ h1 _ h2, Fin.cons_self_tail]

end LiZhongQC
