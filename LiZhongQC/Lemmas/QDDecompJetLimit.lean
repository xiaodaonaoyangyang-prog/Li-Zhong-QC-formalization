import LiZhongQC.Lemmas.QDReflectAcrossArc
import Mathlib.Analysis.Complex.BorelCaratheodory

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold

/-!
# First-jet Kellogg–Warschawski at the seam: the limit of `κ'` (round78 S6a, prefix `s31qj_`)

In the setting of `s31qi_reflect_across_arc` (without `Qc`), `κ'` has a limit at every point of the segment
(`s31qj_deriv_limit`).

* Rescale at `w = x' + i y`: `g(ξ) = τ̄ (κ(x' + y ξ) - κ x') / y` on the half disc of radius `R = y^{-1/3}`, where `τ` is
  the unit tangent at `κ x'`.  Then `|Im g| ≤ K L² y R²` on the diameter (quadratic deviation of the `C^∞` curve from
  its tangent, `s31qj_curve_normal`) and `|g| ≤ L R` (the bound (B), `s31qk_deriv_bounded`).
* The flat estimate `s31qj_flat` gives `|g''(i)| ≤ 400 ε + 128 A / R²`.  It subtracts an affine function and the
  Poisson integral of odd data, bounds the remainder by the maximum principle, and then estimates second derivatives
  from the imaginary part by Borel–Carathéodory and Cauchy.  Hence `|κ''(w)| ≤ C (Im w)^{-2/3}` (`s31qj_kappa_second`).
* Hardy–Littlewood integration (vertical and horizontal increments) makes `κ'` Cauchy at each segment point
  (`s31qj_limit`).
-/

noncomputable section
namespace LiZhongQC

/-- **Second derivative from the imaginary part.**  A holomorphic `f` on `B(c, ρ)` with `|Im f| ≤ M` there has
`|f''(c)| ≤ 32 M / ρ²` (Borel–Carathéodory for `i (f(c + ·) - f c)`, then Cauchy's estimate on `B(0, ρ/2)`). -/
theorem s31qj_deriv2_le {f : ℂ → ℂ} {c : ℂ} {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball c ρ)) (him : ∀ z ∈ ball c ρ, |(f z).im| ≤ M) :
    ‖deriv (deriv f) c‖ ≤ 32 * M / ρ ^ 2 := by
  set F : ℂ → ℂ := fun z => I * (f (c + z) - f c) with hF
  have hmem : ∀ z ∈ ball (0 : ℂ) ρ, c + z ∈ ball c ρ := fun z hz => by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; rwa [mem_ball_zero_iff] at hz
  have hFd : DifferentiableOn ℂ F (ball 0 ρ) := by
    intro z hz
    have h1 : DifferentiableAt ℂ f (c + z) := hf.differentiableAt (isOpen_ball.mem_nhds (hmem z hz))
    have h2 : DifferentiableAt ℂ (fun z => f (c + z)) z :=
      h1.comp z ((differentiableAt_const c).add differentiableAt_id)
    exact ((h2.sub_const (f c)).const_mul I).differentiableWithinAt
  have hFre : MapsTo F (ball 0 ρ) {z | z.re ≤ 2 * M} := by
    intro z hz
    simp only [mem_ofPred_eq, hF, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, sub_im]
    have h1 := him _ (hmem z hz)
    have h2 := him c (mem_ball_self hρ)
    rw [abs_le] at h1 h2
    linarith [h1.1, h2.2]
  have hBC : ∀ z ∈ ball (0 : ℂ) ρ, ‖F z‖ ≤ 2 * (2 * M) * ‖z‖ / (ρ - ‖z‖) := fun z hz =>
    Complex.borelCaratheodory_zero (by positivity) hFd hFre hρ hz (by simp [hF])
  have hρ2 : 0 < ρ / 2 := half_pos hρ
  have hsph : ∀ z ∈ sphere (0 : ℂ) (ρ / 2), ‖F z‖ ≤ 4 * M := by
    intro z hz
    have hzn : ‖z‖ = ρ / 2 := by simpa using hz
    have hzb : z ∈ ball (0 : ℂ) ρ := by rw [mem_ball_zero_iff, hzn]; linarith
    have := hBC z hzb
    rw [hzn] at this
    calc ‖F z‖ ≤ 2 * (2 * M) * (ρ / 2) / (ρ - ρ / 2) := this
      _ = 4 * M := by field_simp; ring
  have hdcc : DiffContOnCl ℂ F (ball 0 (ρ / 2)) :=
    (hFd.mono (closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith)))).diffContOnCl
  have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hρ2 hdcc hsph
  -- `F'' (0) = I f''(c)`
  have hfa : AnalyticOnNhd ℂ f (ball c ρ) := hf.analyticOnNhd isOpen_ball
  have hd1 : ∀ᶠ z in 𝓝 (0 : ℂ), deriv F z = I * deriv f (c + z) := by
    have : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ ball (0 : ℂ) ρ := isOpen_ball.mem_nhds (mem_ball_self hρ)
    filter_upwards [this] with z hz
    have h1 : HasDerivAt f (deriv f (c + z)) (c + z) :=
      (hf.differentiableAt (isOpen_ball.mem_nhds (hmem z hz))).hasDerivAt
    have h3 : HasDerivAt (fun z : ℂ => c + z) 1 z := by
      simpa using (hasDerivAt_id z).const_add c
    have h2 : HasDerivAt (fun z => f (c + z)) (deriv f (c + z)) z := by
      have := h1.comp z h3
      rw [mul_one] at this
      exact this
    exact ((h2.sub_const (f c)).const_mul I).deriv.trans (by ring)
  have hd2 : deriv (deriv F) 0 = I * deriv (deriv f) c := by
    rw [Filter.EventuallyEq.deriv_eq (show deriv F =ᶠ[𝓝 0] (fun z => I * deriv f (c + z)) from hd1)]
    have h1 : DifferentiableAt ℂ (deriv f) c :=
      (hfa.deriv c (mem_ball_self hρ)).differentiableAt
    have h3 : HasDerivAt (fun z : ℂ => c + z) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_add c
    have h2 : HasDerivAt (fun z => deriv f (c + z)) (deriv (deriv f) c) 0 := by
      have h4 : HasDerivAt (deriv f) (deriv (deriv f) c) (c + 0) := by rw [add_zero]; exact h1.hasDerivAt
      have := h4.comp (0 : ℂ) h3
      rw [mul_one] at this
      exact this
    exact (h2.const_mul I).deriv
  have hit : iteratedDeriv 2 F 0 = I * deriv (deriv f) c := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd2]
  rw [hit, norm_mul, Complex.norm_I, one_mul] at hC
  calc ‖deriv (deriv f) c‖ ≤ (Nat.factorial 2 : ℝ) * (4 * M) / (ρ / 2) ^ 2 := hC
    _ = 32 * M / ρ ^ 2 := by norm_num; field_simp; ring

/-- **One-sided maximum principle for `Im k`** on a bounded open preconnected set with a slit boundary point (from
`norm_le_of_frontier_limsup_le_of_bounded` applied to `exp (-i k)`). -/
theorem s31qj_im_le_aux {U : Set ℂ} (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : IsPreconnected U)
    {p c0 : ℂ} (hp : p ∈ frontier U) (hslit : ∀ z ∈ U, c0 * (z - p) ∈ slitPlane) {k : ℂ → ℂ}
    (hk : DifferentiableOn ℂ k U) {K : ℝ} (hK : ∀ z ∈ U, (k z).im ≤ K) {M : ℝ}
    (hbd : ∀ q ∈ frontier U, ∃ v : ℝ, v ≤ M ∧ Tendsto (fun z => (k z).im) (𝓝[U] q) (𝓝 v)) :
    ∀ z ∈ U, (k z).im ≤ M := by
  set h : ℂ → ℂ := fun z => exp (-I * k z) with hh
  have hnorm : ∀ z, ‖h z‖ = Real.exp (k z).im := fun z => by
    simp only [hh, Complex.norm_exp, neg_mul, neg_re, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, neg_neg]
  have hd : DifferentiableOn ℂ h U := fun z hz =>
    (((hk z hz).const_mul (-I)).cexp)
  have hK' : ∀ z ∈ U, ‖h z‖ ≤ Real.exp K := fun z hz => by
    rw [hnorm]; exact Real.exp_le_exp.2 (hK z hz)
  have key := norm_le_of_frontier_limsup_le_of_bounded hUo hUb hUc hp hslit hd hK' (M := Real.exp M)
    (Real.exp_pos M).le (fun q hq _ ε hε => by
      obtain ⟨v, hvM, hv⟩ := hbd q hq
      have h1 : Tendsto (fun z => Real.exp (k z).im) (𝓝[U] q) (𝓝 (Real.exp v)) :=
        (Real.continuous_exp.tendsto v).comp hv
      have h2 : Real.exp v < Real.exp M + ε := by
        have := Real.exp_le_exp.2 hvM; linarith
      filter_upwards [h1.eventually (gt_mem_nhds h2)] with z hz
      rw [hnorm]; exact hz.le)
  intro z hz
  have := key z hz
  rw [hnorm] at this
  exact Real.exp_le_exp.1 this

/-- **Maximum principle for `|Im k|`.** -/
theorem s31qj_abs_im_le {U : Set ℂ} (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : IsPreconnected U)
    {p c0 : ℂ} (hp : p ∈ frontier U) (hslit : ∀ z ∈ U, c0 * (z - p) ∈ slitPlane) {k : ℂ → ℂ}
    (hk : DifferentiableOn ℂ k U) {K : ℝ} (hK : ∀ z ∈ U, |(k z).im| ≤ K) {M : ℝ}
    (hbd : ∀ q ∈ frontier U, ∃ v : ℝ, |v| ≤ M ∧ Tendsto (fun z => (k z).im) (𝓝[U] q) (𝓝 v)) :
    ∀ z ∈ U, |(k z).im| ≤ M := by
  have h1 := s31qj_im_le_aux hUo hUb hUc hp hslit hk (K := K) (fun z hz => (le_abs_self _).trans (hK z hz))
    (M := M) (fun q hq => by
      obtain ⟨v, hv, ht⟩ := hbd q hq
      exact ⟨v, (le_abs_self v).trans hv, ht⟩)
  have h2 := s31qj_im_le_aux hUo hUb hUc hp hslit (k := fun z => -k z) (fun z hz => (hk z hz).neg) (K := K)
    (fun z hz => by
      simp only [neg_im]; exact (neg_le_abs _).trans (hK z hz))
    (M := M) (fun q hq => by
      obtain ⟨v, hv, ht⟩ := hbd q hq
      refine ⟨-v, (neg_le_abs v).trans hv, ?_⟩
      simp only [neg_im]
      exact ht.neg)
  intro z hz
  have a := h1 z hz
  have b := h2 z hz
  simp only [neg_im] at b
  exact abs_le.2 ⟨by linarith, a⟩

/-- The closed upper half disc `{‖z‖ ≤ R, Im z ≥ 0}` is closed. -/
theorem s31qj_isClosed_halfdisc (R : ℝ) : IsClosed {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} :=
  (isClosed_le continuous_norm continuous_const).inter (isClosed_le continuous_const continuous_im)

/-- Frontier points of the open upper half disc lie on the semicircle or on the diameter. -/
theorem s31qj_frontier_halfdisc {R : ℝ} {q : ℂ} (hq : q ∈ frontier {z : ℂ | ‖z‖ < R ∧ 0 < z.im}) :
    ‖q‖ ≤ R ∧ 0 ≤ q.im ∧ (‖q‖ = R ∨ q.im = 0) := by
  rw [(s31qk_isOpen_upper R).frontier_eq] at hq
  have hcl : closure {z : ℂ | ‖z‖ < R ∧ 0 < z.im} ⊆ {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} :=
    closure_minimal (fun z hz => ⟨hz.1.le, hz.2.le⟩) (s31qj_isClosed_halfdisc R)
  obtain ⟨h1, h2⟩ := hcl hq.1
  refine ⟨h1, h2, ?_⟩
  by_contra hne
  push Not at hne
  exact hq.2 ⟨lt_of_le_of_ne h1 hne.1, lt_of_le_of_ne h2 (Ne.symm hne.2)⟩

/-- `0` is a frontier point of the open upper half disc. -/
theorem s31qj_zero_mem_frontier {R : ℝ} (hR : 0 < R) : (0 : ℂ) ∈ frontier {z : ℂ | ‖z‖ < R ∧ 0 < z.im} := by
  rw [(s31qk_isOpen_upper R).frontier_eq]
  refine ⟨Metric.mem_closure_iff.2 fun ε hε => ?_, fun h => by simp at h⟩
  set s : ℝ := min ε R / 2 with hs
  have hs0 : 0 < s := by positivity
  have hsε : s < ε := by have := min_le_left ε R; linarith
  have hsR : s < R := by have := min_le_right ε R; linarith
  refine ⟨(s : ℂ) * I, ⟨?_, ?_⟩, ?_⟩
  · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]; exact hsR
  · simpa using hs0
  · rw [dist_eq_norm, zero_sub, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs0]; exact hsε

/-- Upper half disc points are in the slit plane after multiplication by `-i`. -/
theorem s31qj_slit {R : ℝ} : ∀ z ∈ {z : ℂ | ‖z‖ < R ∧ 0 < z.im}, -I * (z - 0) ∈ slitPlane := by
  intro z hz
  refine Or.inl ?_
  simp only [sub_zero, neg_mul, neg_re, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, neg_neg]
  exact hz.2

/-- Second derivative of a sum, for functions holomorphic on an open neighbourhood. -/
theorem s31qj_deriv2_add {f₁ f₂ : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) {z₀ : ℂ} (hz₀ : z₀ ∈ s)
    (h₁ : DifferentiableOn ℂ f₁ s) (h₂ : DifferentiableOn ℂ f₂ s) :
    deriv (deriv (fun z => f₁ z + f₂ z)) z₀ = deriv (deriv f₁) z₀ + deriv (deriv f₂) z₀ := by
  have hev : deriv (fun z => f₁ z + f₂ z) =ᶠ[𝓝 z₀] fun z => deriv f₁ z + deriv f₂ z := by
    filter_upwards [hs.mem_nhds hz₀] with z hz
    exact deriv_add (h₁.differentiableAt (hs.mem_nhds hz)) (h₂.differentiableAt (hs.mem_nhds hz))
  rw [hev.deriv_eq]
  have a₁ := ((h₁.analyticOnNhd hs).deriv z₀ hz₀).differentiableAt
  have a₂ := ((h₂.analyticOnNhd hs).deriv z₀ hz₀).differentiableAt
  exact deriv_add a₁ a₂

/-- A point of the circle `‖z‖ = R` on the real axis is `±R`. -/
theorem s31qj_real_on_sphere {R : ℝ} {z : ℂ} (hz : ‖z‖ = R) (him : z.im = 0) :
    z = (R : ℂ) ∨ z = ((-R : ℝ) : ℂ) := by
  have hz' : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
  have hre : |z.re| = R := by
    rw [hz', Complex.norm_real, Real.norm_eq_abs] at hz; exact hz
  rcases abs_eq_abs.1 (hre.trans (abs_of_nonneg (hre ▸ abs_nonneg _)).symm) with h | h
  · left; rw [hz', h]
  · right; rw [hz', h]

/-- **Odd continuous data on the circle.**  If `v` is continuous on the closed upper half disc and vanishes at `±R`,
its odd reflection is continuous on the circle `‖z‖ = R`. -/
theorem s31qj_odd_continuousOn {R : ℝ} {v : ℂ → ℝ} (hv : ContinuousOn v {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hvR : v R = 0) (hvR' : v ((-R : ℝ) : ℂ) = 0) :
    ContinuousOn (reflectExtendOdd v) (sphere (0 : ℂ) R) := by
  have hv0 : ∀ z : ℂ, ‖z‖ = R → z.im = 0 → v z = 0 := fun z hz him => by
    rcases s31qj_real_on_sphere hz him with h | h <;> rw [h] <;> assumption
  set Sp : Set ℂ := sphere (0 : ℂ) R ∩ {z | 0 ≤ z.im} with hSp
  set Sm : Set ℂ := sphere (0 : ℂ) R ∩ {z | z.im ≤ 0} with hSm
  have hcover : sphere (0 : ℂ) R = Sp ∪ Sm := by
    ext z; constructor
    · intro hz; rcases le_total 0 z.im with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
    · rintro (h | h) <;> exact h.1
  have hnorm : ∀ z ∈ sphere (0 : ℂ) R, ‖z‖ = R := fun z hz => by simpa using hz
  have h1 : ContinuousOn (reflectExtendOdd v) Sp := by
    refine (hv.mono fun z (hz : z ∈ Sp) => ⟨(hnorm z hz.1).le, hz.2⟩).congr fun z hz => ?_
    have hzi : 0 ≤ z.im := hz.2
    rcases hzi.lt_or_eq with h | h
    · exact reflectExtendOdd_of_pos v h
    · rw [reflectExtendOdd_of_eq_zero v h.symm, hv0 z (hnorm z hz.1) h.symm]
  have h2 : ContinuousOn (reflectExtendOdd v) Sm := by
    have hc : ContinuousOn (fun z => -v (conj z)) Sm := by
      refine (hv.comp Complex.continuous_conj.continuousOn fun z hz => ?_).neg
      refine ⟨?_, ?_⟩
      · rw [Complex.norm_conj]; exact (hnorm z hz.1).le
      · have hzi : z.im ≤ 0 := hz.2
        rw [Complex.conj_im]; linarith
    refine hc.congr fun z hz => ?_
    have hzi : z.im ≤ 0 := hz.2
    rcases hzi.lt_or_eq with h | h
    · exact reflectExtendOdd_of_neg v h
    · rw [reflectExtendOdd_of_eq_zero v h]
      have : v (conj z) = 0 := hv0 _ (by rw [Complex.norm_conj]; exact hnorm z hz.1) (by rw [Complex.conj_im, h]; simp)
      show (0 : ℝ) = -v (conj z)
      rw [this, neg_zero]
  rw [hcover]
  exact h1.union_of_isClosed h2 (isClosed_sphere.inter (isClosed_le continuous_const continuous_im))
    (isClosed_sphere.inter (isClosed_le continuous_im continuous_const))

/-- The Poisson integral of data bounded by `B` on the circle is bounded by `B` inside. -/
theorem s31qj_poisson_le {R B : ℝ} (hR : 0 < R) {V : ℂ → ℝ} (hV : ContinuousOn V (sphere (0 : ℂ) R))
    (hB : ∀ z ∈ sphere (0 : ℂ) R, V z ≤ B) {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) :
    Real.circleAverage (fun z => poissonKernel 0 w z * V z) 0 R ≤ B := by
  have hR' : |R| = R := abs_of_pos hR
  have havg : Real.circleAverage (poissonKernel 0 w • fun _ : ℂ => (1 : ℝ)) 0 R = 1 :=
    (InnerProductSpace.harmonicOnNhd_const (1 : ℝ)).circleAverage_poissonKernel_smul hw
  have heq : (fun z => poissonKernel 0 w z * B) = B • (poissonKernel 0 w • fun _ : ℂ => (1 : ℝ)) := by
    ext z; simp [mul_comm]
  have hconst : ContinuousOn (fun _ : ℂ => B) (sphere (0 : ℂ) R) := continuousOn_const
  calc Real.circleAverage (fun z => poissonKernel 0 w z * V z) 0 R
      ≤ Real.circleAverage (fun z => poissonKernel 0 w z * B) 0 R := by
        apply Real.circleAverage_mono (circleIntegrable_poissonKernel_mul hR.le hw hV)
          (circleIntegrable_poissonKernel_mul hR.le hw hconst)
        intro z hz
        rw [hR'] at hz
        exact mul_le_mul_of_nonneg_left (hB z hz) (poissonKernel_nonneg_of_mem_sphere hz hw)
    _ = B := by rw [heq, Real.circleAverage_smul, havg, smul_eq_mul, mul_one]

/-- Arithmetic for the corner interpolation: the affine function through `(±R, b±)` is bounded by `2ε` on `[-R, R]`. -/
theorem s31qj_affine_bound {R ε a b x : ℝ} (hR : 0 < R) (ha : |a| ≤ ε) (hb : |b| ≤ ε) (hx : |x| ≤ R) :
    |(a + b) / 2 + (a - b) / (2 * R) * x| ≤ 2 * ε := by
  have h1 : |(a + b) / 2| ≤ ε := by
    rw [abs_div, abs_two]; have := abs_add_le a b; linarith
  have h2 : |(a - b) / (2 * R) * x| ≤ ε := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * R)]
    have h3 : |a - b| ≤ 2 * ε := by have := abs_sub a b; linarith
    calc |a - b| / (2 * R) * |x| ≤ (2 * ε) / (2 * R) * R := by
          apply mul_le_mul (div_le_div_of_nonneg_right h3 (by positivity)) hx (abs_nonneg _)
          have : 0 ≤ ε := (abs_nonneg a).trans ha
          positivity
      _ = ε := by field_simp
  calc _ ≤ |(a + b) / 2| + |(a - b) / (2 * R) * x| := abs_add_le _ _
    _ ≤ 2 * ε := by linarith

/-- **The flat estimate.**  Let `g` be holomorphic on the open upper half disc of radius `R ≥ 4`, continuous on its
closure, with `|g| ≤ A` there and `|Im g| ≤ ε` on the diameter.  Then `|g''(i)| ≤ 400 ε + 128 A / R²`.
(Subtract the affine harmonic function through the corners and the Poisson integral of the odd reflection of the
remaining data on the semicircle; the rest has imaginary part `≤ 3ε` by the maximum principle; second derivatives by
`s31qj_deriv2_le`.) -/
theorem s31qj_flat {g : ℂ → ℂ} {R A ε : ℝ} (hR : 4 ≤ R) (hε : 0 < ε)
    (hgd : DifferentiableOn ℂ g {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hgc : ContinuousOn g {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hA : ∀ z : ℂ, ‖z‖ ≤ R → 0 ≤ z.im → ‖g z‖ ≤ A)
    (hseg : ∀ x : ℝ, |x| ≤ R → |(g x).im| ≤ ε) :
    ‖deriv (deriv g) I‖ ≤ 400 * ε + 128 * A / R ^ 2 := by
  have hR0 : 0 < R := by linarith
  set U : Set ℂ := {z : ℂ | ‖z‖ < R ∧ 0 < z.im} with hU
  set Uc : Set ℂ := {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} with hUc
  have hUU : U ⊆ Uc := fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hUb : U ⊆ ball (0 : ℂ) R := fun z hz => mem_ball_zero_iff.2 hz.1
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (by simp; linarith) (by simp))
  set h : ℂ → ℝ := fun z => (g z).im with hh
  have hhc : ContinuousOn h Uc := Complex.continuous_im.comp_continuousOn hgc
  have hhA : ∀ z ∈ Uc, |h z| ≤ A := fun z hz => (Complex.abs_im_le_norm _).trans (hA z hz.1 hz.2)
  -- the affine correction through the corners
  set a : ℝ := h R with ha
  set b : ℝ := h ((-R : ℝ) : ℂ) with hb
  have haε : |a| ≤ ε := hseg R (by rw [abs_of_pos hR0])
  have hbε : |b| ≤ ε := hseg (-R) (by rw [abs_neg, abs_of_pos hR0])
  set α : ℝ := (a + b) / 2 with hα
  set β : ℝ := (a - b) / (2 * R) with hβ
  set ℓ : ℂ → ℝ := fun z => α + β * z.re with hℓ
  have hℓb : ∀ z : ℂ, ‖z‖ ≤ R → |ℓ z| ≤ 2 * ε := fun z hz =>
    s31qj_affine_bound hR0 haε hbε ((Complex.abs_re_le_norm z).trans hz)
  set v : ℂ → ℝ := fun z => h z - ℓ z with hv
  have hvc : ContinuousOn v Uc := hhc.sub (by fun_prop)
  have hvR : v R = 0 := by
    simp only [hv, hℓ, Complex.ofReal_re, hα, hβ]; rw [← ha]; field_simp; ring
  have hvR' : v ((-R : ℝ) : ℂ) = 0 := by
    simp only [hv, hℓ, Complex.ofReal_re, hα, hβ]; rw [← hb]; field_simp; ring
  set V : ℂ → ℝ := reflectExtendOdd v with hV
  have hVc : ContinuousOn V (sphere (0 : ℂ) R) := s31qj_odd_continuousOn hvc hvR hvR'
  have hVb : ∀ z ∈ sphere (0 : ℂ) R, |V z| ≤ A + 2 * ε := by
    intro z hz
    have hzn : ‖z‖ = R := by simpa using hz
    have hvb : ∀ w ∈ Uc, |v w| ≤ A + 2 * ε := fun w hw => by
      have := abs_sub (h w) (ℓ w); linarith [hhA w hw, hℓb w hw.1]
    rcases lt_trichotomy z.im 0 with hi | hi | hi
    · rw [hV, reflectExtendOdd_of_neg v hi, abs_neg]
      exact hvb _ ⟨by rw [Complex.norm_conj, hzn], by rw [Complex.conj_im]; linarith⟩
    · rw [hV, reflectExtendOdd_of_eq_zero v hi, abs_zero]; positivity
    · rw [hV, reflectExtendOdd_of_pos v hi]; exact hvb _ ⟨hzn.le, hi.le⟩
  -- the Poisson integral `P` of the odd data
  set P : ℂ → ℝ := fun w => Real.circleAverage (fun z => poissonKernel 0 w z * V z) 0 R with hP
  have hPh : InnerProductSpace.HarmonicOnNhd P (ball 0 R) := harmonicOnNhd_poissonIntegral hR0 hVc
  have hPreal : ∀ x : ℝ, P x = 0 := fun x => by
    have h1 := poissonIntegral_conj_eq_neg (x := 0) (by simp) (r := R) (V := V)
      (fun z => reflectExtendOdd_conj v z) (x : ℂ)
    rw [Complex.conj_ofReal] at h1
    change P x = -P x at h1
    linarith
  have hPb : ∀ w ∈ ball (0 : ℂ) R, |P w| ≤ A + 2 * ε := by
    intro w hw
    have h1 := s31qj_poisson_le hR0 hVc (fun z hz => (le_abs_self _).trans (hVb z hz)) hw
    have h2 := s31qj_poisson_le hR0 hVc.neg (fun z hz => (neg_le_abs _).trans (hVb z hz)) hw
    have h3 : Real.circleAverage (fun z => poissonKernel 0 w z * -V z) 0 R = -P w := by
      have e : (fun z => poissonKernel 0 w z * -V z) = (-1 : ℝ) • (fun z => poissonKernel 0 w z * V z) := by
        ext z; simp
      rw [e, Real.circleAverage_smul, neg_one_smul]
    simp only [Pi.neg_apply] at h2
    rw [h3] at h2
    exact abs_le.2 ⟨by linarith, h1⟩
  have hPt : ∀ ζ ∈ sphere (0 : ℂ) R, Tendsto P (𝓝[ball 0 R] ζ) (𝓝 (V ζ)) := fun ζ hζ =>
    tendsto_poissonIntegral_nhdsWithin hR0 hVc hζ
  obtain ⟨F, hFa, hFre⟩ := hPh.exists_analyticOnNhd_ball_re_eq
  -- the remainder `k`
  set k : ℂ → ℂ := fun z => g z - I * F z - I * ((α : ℂ) + (β : ℂ) * z) with hk
  have hkim : ∀ z ∈ ball (0 : ℂ) R, (k z).im = h z - P z - ℓ z := fun z hz => by
    have := hFre hz
    simp only at this
    simp only [hk, hh, hℓ, sub_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add, add_re, ofReal_re, ofReal_im,
      mul_re, sub_zero]
    rw [this]
  have hFd : DifferentiableOn ℂ F (ball 0 R) := hFa.differentiableOn
  have hkd : DifferentiableOn ℂ k U := by
    refine (hgd.sub ((hFd.mono hUb).const_mul I)).sub ?_
    exact (((differentiableOn_const _).add ((differentiableOn_const _).mul differentiableOn_id)).const_mul I)
  have hkK : ∀ z ∈ U, |(k z).im| ≤ 2 * A + 4 * ε := fun z hz => by
    rw [hkim z (hUb hz)]
    have h1 := hhA z (hUU hz)
    have h2 := hPb z (hUb hz)
    have h3 := hℓb z hz.1.le
    calc |h z - P z - ℓ z| ≤ |h z| + |P z| + |ℓ z| := by
          have := abs_sub (h z - P z) (ℓ z); have := abs_sub (h z) (P z); linarith
      _ ≤ 2 * A + 4 * ε := by linarith
  -- boundary behaviour of `Im k`
  have hbd : ∀ q ∈ frontier U, ∃ w : ℝ, |w| ≤ 3 * ε ∧ Tendsto (fun z => (k z).im) (𝓝[U] q) (𝓝 w) := by
    intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := s31qj_frontier_halfdisc hq
    have hqUc : q ∈ Uc := ⟨hq1, hq2⟩
    have hev : (fun z => h z - P z - ℓ z) =ᶠ[𝓝[U] q] fun z => (k z).im := by
      filter_upwards [self_mem_nhdsWithin] with z hz using (hkim z (hUb hz)).symm
    have hht : Tendsto h (𝓝[U] q) (𝓝 (h q)) := ((hhc q hqUc).mono hUU).tendsto
    have hℓt : Tendsto ℓ (𝓝[U] q) (𝓝 (ℓ q)) :=
      ((by fun_prop : Continuous ℓ).tendsto q).mono_left nhdsWithin_le_nhds
    by_cases hqR : ‖q‖ = R
    · have hqs : q ∈ sphere (0 : ℂ) R := by simpa using hqR
      have hPq : Tendsto P (𝓝[U] q) (𝓝 (V q)) := (hPt q hqs).mono_left (nhdsWithin_mono _ hUb)
      have hVq : V q = v q := by
        rcases hq2.lt_or_eq with hi | hi
        · exact reflectExtendOdd_of_pos v hi
        · rw [hV, reflectExtendOdd_of_eq_zero v hi.symm]
          rcases s31qj_real_on_sphere hqR hi.symm with e | e
          · rw [e]; exact hvR.symm
          · rw [e]; exact hvR'.symm
      refine ⟨0, by rw [abs_zero]; positivity, ?_⟩
      have := (hht.sub hPq).sub hℓt
      rw [hVq, show h q - v q - ℓ q = 0 by simp [hv]] at this
      exact this.congr' hev
    · have hqi : q.im = 0 := hq3.resolve_left hqR
      have hqlt : ‖q‖ < R := lt_of_le_of_ne hq1 hqR
      have hqb : q ∈ ball (0 : ℂ) R := mem_ball_zero_iff.2 hqlt
      have hPq : Tendsto P (𝓝[U] q) (𝓝 (P q)) :=
        ((hPh.continuousOn q hqb).continuousAt (isOpen_ball.mem_nhds hqb)).tendsto.mono_left nhdsWithin_le_nhds
      have hqeq : q = (q.re : ℂ) := by apply Complex.ext <;> simp [hqi]
      have hP0 : P q = 0 := by rw [hqeq]; exact hPreal q.re
      have hhq : |h q| ≤ ε := by
        rw [hqeq]; exact hseg q.re ((Complex.abs_re_le_norm q).trans hq1)
      refine ⟨h q - P q - ℓ q, ?_, ((hht.sub hPq).sub hℓt).congr' hev⟩
      rw [hP0, sub_zero]
      have := hℓb q hq1
      have := abs_sub (h q) (ℓ q)
      linarith
  have hUconv : Convex ℝ U := by
    have e : U = ball (0 : ℂ) R ∩ {z : ℂ | 0 < z.im} := by ext z; simp [hU, mem_ball_zero_iff]
    rw [e]; exact (convex_ball _ _).inter (convex_halfSpace_im_gt (r := 0))
  have hkb : ∀ z ∈ U, |(k z).im| ≤ 3 * ε :=
    s31qj_abs_im_le (s31qk_isOpen_upper R) (Metric.isBounded_ball.subset hUb) hUconv.isPreconnected
      (s31qj_zero_mem_frontier hR0) s31qj_slit hkd hkK hbd
  -- second derivatives at `i`
  have hball1 : ball I (1 / 2) ⊆ U := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    refine ⟨?_, ?_⟩
    · calc ‖z‖ = ‖(z - I) + I‖ := by ring_nf
        _ ≤ ‖z - I‖ + ‖I‖ := norm_add_le _ _
        _ < R := by rw [Complex.norm_I]; linarith
    · have := Complex.abs_im_le_norm (z - I)
      rw [Complex.sub_im, Complex.I_im] at this
      linarith [neg_abs_le (z.im - 1)]
  have hk2 : ‖deriv (deriv k) I‖ ≤ 32 * (3 * ε) / (1 / 2) ^ 2 :=
    s31qj_deriv2_le (by norm_num) (by positivity) (hkd.mono hball1) fun z hz => hkb z (hball1 hz)
  have hballR : ball I (R / 2) ⊆ ball (0 : ℂ) R := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_ball_zero_iff]
    calc ‖z‖ = ‖(z - I) + I‖ := by ring_nf
      _ ≤ ‖z - I‖ + ‖I‖ := norm_add_le _ _
      _ < R := by rw [Complex.norm_I]; linarith
  have hF2 : ‖deriv (deriv (fun z => I * F z)) I‖ ≤ 32 * (A + 2 * ε) / (R / 2) ^ 2 := by
    refine s31qj_deriv2_le (by positivity) (by positivity) ((hFd.mono hballR).const_mul I) fun z hz => ?_
    have : (I * F z).im = P z := by
      have := hFre (hballR hz); simp only at this
      simp [mul_im, this]
    rw [this]; exact hPb z (hballR hz)
  -- assemble
  have hIU : I ∈ U := hball1 (mem_ball_self (by norm_num))
  have hlin : DifferentiableOn ℂ (fun z : ℂ => I * ((α : ℂ) + (β : ℂ) * z)) U :=
    (((differentiableOn_const _).add ((differentiableOn_const _).mul differentiableOn_id)).const_mul I)
  have hgeq : g = fun z => (k z + I * F z) + I * ((α : ℂ) + (β : ℂ) * z) := by
    ext z; simp only [hk]; ring
  have hlin2 : deriv (deriv (fun z : ℂ => I * ((α : ℂ) + (β : ℂ) * z))) I = 0 := by
    have : deriv (fun z : ℂ => I * ((α : ℂ) + (β : ℂ) * z)) = fun _ => I * β := by
      ext z
      have h1 : HasDerivAt (fun z : ℂ => I * ((α : ℂ) + (β : ℂ) * z)) (I * β) z := by
        have := ((hasDerivAt_id z).const_mul (β : ℂ)).const_add (α : ℂ)
        simpa using this.const_mul I
      exact h1.deriv
    rw [this, deriv_const]
  have hsum : deriv (deriv g) I = deriv (deriv k) I + deriv (deriv (fun z => I * F z)) I := by
    have e1 := s31qj_deriv2_add (f₁ := fun z => k z + I * F z) (f₂ := fun z : ℂ => I * ((α : ℂ) + (β : ℂ) * z))
      (s31qk_isOpen_upper R) hIU (hkd.add ((hFd.mono hUb).const_mul I)) hlin
    have e2 := s31qj_deriv2_add (f₁ := k) (f₂ := fun z => I * F z) (s31qk_isOpen_upper R) hIU hkd
      ((hFd.mono hUb).const_mul I)
    beta_reduce at e1 e2
    rw [hgeq, e1, hlin2, add_zero, e2]
  rw [hsum]
  have hR2 : 16 ≤ R ^ 2 := by nlinarith
  have e1 : 32 * (A + 2 * ε) / (R / 2) ^ 2 = 128 * A / R ^ 2 + 256 * ε / R ^ 2 := by field_simp; ring
  have e2 : 256 * ε / R ^ 2 ≤ 16 * ε := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  calc ‖deriv (deriv k) I + deriv (deriv (fun z => I * F z)) I‖
      ≤ ‖deriv (deriv k) I‖ + ‖deriv (deriv (fun z => I * F z)) I‖ := norm_add_le _ _
    _ ≤ 32 * (3 * ε) / (1 / 2) ^ 2 + 32 * (A + 2 * ε) / (R / 2) ^ 2 := add_le_add hk2 hF2
    _ ≤ 400 * ε + 128 * A / R ^ 2 := by rw [e1]; norm_num; linarith

/-- **Quadratic deviation from the tangent.**  For a smooth regular `1`-periodic simple closed curve there are `K, ρ > 0`
with `|Im ((c t - c s) · conj τ_s)| ≤ K |c t - c s|²` whenever `|c t - c s| < ρ`, where `τ_s = c'(s)/|c'(s)|`. -/
theorem s31qj_curve_normal {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0)
    (hper : ∀ t, c (t + 1) = c t) (hinj : InjOn c (Ico 0 1)) :
    ∃ K ρ : ℝ, 0 < K ∧ 0 < ρ ∧ ∀ s t : ℝ, ‖c t - c s‖ < ρ →
      |((c t - c s) * conj (deriv c s / (‖deriv c s‖ : ℂ))).im| ≤ K * ‖c t - c s‖ ^ 2 := by
  have hp : Function.Periodic c 1 := hper
  obtain ⟨δ, M, hδ, hM, -, htay, hbil⟩ := s31qk_curve_bilip hc hc' hper
  set η : ℝ := min (δ / (2 * M)) (1 / 2) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  obtain ⟨ε, hε, hgap⟩ := s31qk_curve_gap hc.continuous hper hinj hη0
  refine ⟨M * (2 / δ) ^ 2, ε, by positivity, hε, fun s t hst => ?_⟩
  -- reduce `t` to `s + d`, `|d| ≤ 1/2`
  set k : ℤ := round (t - s) with hk
  set d : ℝ := t - s - k with hd
  have hd2 : |d| ≤ 1 / 2 := by simpa [hd] using abs_sub_round (t - s)
  have hct : c t = c (s + d) := by
    have := (hp.int_mul k) (s + d)
    rw [mul_one, show s + d + k = t by rw [hd]; ring] at this
    exact this
  rw [hct] at hst ⊢
  have hdη : |d| < η := by
    by_contra h
    push Not at h
    have := hgap s d h hd2
    linarith
  have hdb : |d| ≤ δ / (2 * M) := hdη.le.trans (min_le_left _ _)
  have hlow := hbil s d hdb
  -- the tangential part has zero imaginary part
  set E : ℂ := c (s + d) - c s - (d : ℂ) * deriv c s with hE
  have hEb : ‖E‖ ≤ M * d ^ 2 := htay s d
  have hne : (‖deriv c s‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hc' s))
  have htan : ((d : ℂ) * deriv c s * conj (deriv c s / (‖deriv c s‖ : ℂ))).im = 0 := by
    rw [map_div₀, Complex.conj_ofReal, mul_div_assoc', mul_assoc, Complex.mul_conj,
      ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_im]
  have hτ : ‖conj (deriv c s / (‖deriv c s‖ : ℂ))‖ = 1 := by
    rw [Complex.norm_conj, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 (hc' s))]
  have hsplit : c (s + d) - c s = (d : ℂ) * deriv c s + E := by rw [hE]; ring
  rw [hsplit, add_mul, Complex.add_im, htan, zero_add]
  have hd' : |d| ≤ (2 / δ) * ‖(d : ℂ) * deriv c s + E‖ := by
    rw [← hsplit]
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    linarith
  calc |(E * conj (deriv c s / (‖deriv c s‖ : ℂ))).im| ≤ ‖E * conj (deriv c s / (‖deriv c s‖ : ℂ))‖ :=
        Complex.abs_im_le_norm _
    _ = ‖E‖ := by rw [norm_mul, hτ, mul_one]
    _ ≤ M * d ^ 2 := hEb
    _ = M * |d| ^ 2 := by rw [sq_abs]
    _ ≤ M * ((2 / δ) * ‖(d : ℂ) * deriv c s + E‖) ^ 2 := by
        gcongr
    _ = M * (2 / δ) ^ 2 * ‖(d : ℂ) * deriv c s + E‖ ^ 2 := by ring

/-- **Lipschitz bound on the closed half disc** from a derivative bound on the open one and continuity. -/
theorem s31qj_lip_closed {x₀ : ℝ} {δ C : ℝ} {κ : ℂ → ℂ}
    (hκc : ContinuousOn κ {z : ℂ | ‖z - x₀‖ < δ ∧ 0 ≤ z.im})
    (hκd : ∀ z : ℂ, ‖z - x₀‖ < δ → 0 < z.im → DifferentiableAt ℂ κ z)
    (hC : ∀ z : ℂ, ‖z - x₀‖ < δ → 0 < z.im → ‖deriv κ z‖ ≤ C) :
    ∀ z₁ z₂ : ℂ, ‖z₁ - x₀‖ < δ → 0 ≤ z₁.im → ‖z₂ - x₀‖ < δ → 0 ≤ z₂.im → ‖κ z₁ - κ z₂‖ ≤ C * ‖z₁ - z₂‖ := by
  intro z₁ z₂ h₁ i₁ h₂ i₂
  set U : Set ℂ := {z : ℂ | ‖z - x₀‖ < δ ∧ 0 < z.im} with hU
  have hUc : Convex ℝ U := by
    have e : U = ball (x₀ : ℂ) δ ∩ {z : ℂ | 0 < z.im} := by ext z; simp [hU, dist_eq_norm]
    rw [e]; exact (convex_ball _ _).inter (convex_halfSpace_im_gt (r := 0))
  have hlip : ∀ a ∈ U, ∀ b ∈ U, ‖κ a - κ b‖ ≤ C * ‖a - b‖ := fun a ha b hb =>
    hUc.norm_image_sub_le_of_norm_hasDerivWithin_le (f := κ) (f' := deriv κ)
      (fun u (hu : u ∈ U) => (hκd u hu.1 hu.2).hasDerivAt.hasDerivWithinAt) (fun u (hu : u ∈ U) => hC u hu.1 hu.2) hb ha
  set m : ℝ := δ - max ‖z₁ - x₀‖ ‖z₂ - x₀‖ with hm
  have hm0 : 0 < m := by rw [hm]; exact sub_pos.2 (max_lt h₁ h₂)
  -- shifted points
  have hshift : ∀ z : ℂ, ‖z - x₀‖ < δ → 0 ≤ z.im → ‖z - x₀‖ ≤ δ - m → ∀ η : ℝ, 0 < η → η < m →
      z + η * I ∈ U := by
    intro z hz hzi hzm η hη hηm
    refine ⟨?_, by simp; linarith⟩
    calc ‖z + η * I - x₀‖ ≤ ‖z - x₀‖ + ‖(η : ℂ) * I‖ := by
          rw [show z + η * I - x₀ = (z - x₀) + η * I by ring]; exact norm_add_le _ _
      _ = ‖z - x₀‖ + η := by rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
      _ < δ := by linarith
  have hzm₁ : ‖z₁ - x₀‖ ≤ δ - m := by rw [hm]; linarith [le_max_left ‖z₁ - x₀‖ ‖z₂ - x₀‖]
  have hzm₂ : ‖z₂ - x₀‖ ≤ δ - m := by rw [hm]; linarith [le_max_right ‖z₁ - x₀‖ ‖z₂ - x₀‖]
  have htend : ∀ z : ℂ, ‖z - x₀‖ < δ → 0 ≤ z.im →
      Tendsto (fun η : ℝ => κ (z + η * I)) (𝓝[>] 0) (𝓝 (κ z)) := by
    intro z hz hzi
    have h1 : Tendsto (fun η : ℝ => z + η * I) (𝓝[>] 0) (𝓝[{z : ℂ | ‖z - x₀‖ < δ ∧ 0 ≤ z.im}] z) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun η : ℝ => z + η * I) (𝓝 0) (𝓝 z) := by
          have := ((Complex.continuous_ofReal.tendsto 0).mul_const I).const_add z
          simpa using this
        exact this.mono_left nhdsWithin_le_nhds
      · have hev : ∀ᶠ η : ℝ in 𝓝[>] 0, η < δ - ‖z - x₀‖ :=
          nhdsWithin_le_nhds (gt_mem_nhds (by linarith))
        filter_upwards [hev, self_mem_nhdsWithin] with η hη hη0
        have hη0' : (0 : ℝ) < η := hη0
        refine ⟨?_, by simp; linarith⟩
        calc ‖z + η * I - x₀‖ ≤ ‖z - x₀‖ + ‖(η : ℂ) * I‖ := by
              rw [show z + η * I - x₀ = (z - x₀) + η * I by ring]; exact norm_add_le _ _
          _ = ‖z - x₀‖ + η := by
              rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη0']
          _ < δ := by linarith
    exact (hκc z ⟨hz, hzi⟩).tendsto.comp h1
  have hlim := ((htend z₁ h₁ i₁).sub (htend z₂ h₂ i₂)).norm
  refine le_of_tendsto hlim ?_
  have hev : ∀ᶠ η : ℝ in 𝓝[>] 0, η < m := nhdsWithin_le_nhds (gt_mem_nhds hm0)
  filter_upwards [hev, self_mem_nhdsWithin] with η hη hη0
  have := hlip _ (hshift z₁ h₁ i₁ hzm₁ η hη0 hη) _ (hshift z₂ h₂ i₂ hzm₂ η hη0 hη)
  rwa [show z₁ + η * I - (z₂ + η * I) = z₁ - z₂ by ring] at this

/-- Second derivative of an affine rescaling `ξ ↦ a (κ (b + y ξ) - k₀)`. -/
theorem s31qj_deriv2_affine {κ : ℂ → ℂ} {O : Set ℂ} (hO : IsOpen O) (hκ : DifferentiableOn ℂ κ O)
    (a b k₀ y : ℂ) {ξ₀ : ℂ} (hξ₀ : b + y * ξ₀ ∈ O) :
    deriv (deriv (fun ξ => a * (κ (b + y * ξ) - k₀))) ξ₀ = a * y ^ 2 * deriv (deriv κ) (b + y * ξ₀) := by
  have hφ : ∀ ξ : ℂ, HasDerivAt (fun ξ => b + y * ξ) y ξ := fun ξ => by
    simpa using ((hasDerivAt_id ξ).const_mul y).const_add b
  have hpre : IsOpen ((fun ξ => b + y * ξ) ⁻¹' O) := hO.preimage (by fun_prop)
  have hev : deriv (fun ξ => a * (κ (b + y * ξ) - k₀)) =ᶠ[𝓝 ξ₀] fun ξ => a * (deriv κ (b + y * ξ) * y) := by
    filter_upwards [hpre.mem_nhds hξ₀] with ξ hξ
    have h1 : HasDerivAt κ (deriv κ (b + y * ξ)) (b + y * ξ) :=
      (hκ.differentiableAt (hO.mem_nhds hξ)).hasDerivAt
    have h2 : HasDerivAt (fun ξ => κ (b + y * ξ)) (deriv κ (b + y * ξ) * y) ξ := h1.comp ξ (hφ ξ)
    exact ((h2.sub_const k₀).const_mul a).deriv
  rw [hev.deriv_eq]
  have h3 : DifferentiableAt ℂ (deriv κ) (b + y * ξ₀) :=
    (((hκ.analyticOnNhd hO).deriv) _ hξ₀).differentiableAt
  have h5 : HasDerivAt (deriv κ) (deriv (deriv κ) (b + y * ξ₀)) ((fun ξ => b + y * ξ) ξ₀) := h3.hasDerivAt
  have h4 : HasDerivAt (fun ξ => deriv κ (b + y * ξ)) (deriv (deriv κ) (b + y * ξ₀) * y) ξ₀ := by
    have h6 := HasDerivAt.comp (h₂ := deriv κ) ξ₀ h5 (hφ ξ₀)
    exact h6
  rw [((h4.mul_const y).const_mul a).deriv]
  ring

/-- **The scaled estimate.**  Let `s ∈ (0, 1/4]`, `y = s³`, `|τ| = 1`.  If `κ` is holomorphic near the rescaled open
half disc `x' + y·{‖ξ‖ < 1/s, Im ξ > 0}`, continuous on the rescaled closed one, `C'`-Lipschitz from `x'` there, and
`|Im ((κ(x' + y u) - κ x') τ̄)| ≤ K (C' y |u|)²` on the rescaled diameter, then
`|κ''(x' + i y)| ≤ (400 K C'² + 128 C') / s²`. -/
theorem s31qj_scaled {κ : ℂ → ℂ} {O S : Set ℂ} (hO : IsOpen O) (hκd : DifferentiableOn ℂ κ O)
    (hκc : ContinuousOn κ S) {x' y s C' K : ℝ} {τ : ℂ} (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hy : y = s ^ 3)
    (hτ : ‖τ‖ = 1) (hK : 0 < K) (hC' : 0 < C')
    (hmapO : ∀ ξ : ℂ, ‖ξ‖ < 1 / s → 0 < ξ.im → (x' : ℂ) + y * ξ ∈ O)
    (hmapS : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 / s → 0 ≤ ξ.im → (x' : ℂ) + y * ξ ∈ S)
    (hlip : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 / s → 0 ≤ ξ.im → ‖κ ((x' : ℂ) + y * ξ) - κ x'‖ ≤ C' * y * ‖ξ‖)
    (hseg : ∀ u : ℝ, |u| ≤ 1 / s → |((κ ((x' : ℂ) + y * u) - κ x') * conj τ).im| ≤ K * (C' * y * |u|) ^ 2) :
    ‖deriv (deriv κ) ((x' : ℂ) + y * I)‖ ≤ (400 * K * C' ^ 2 + 128 * C') / s ^ 2 := by
  have hy0 : 0 < y := by rw [hy]; positivity
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy0.ne'
  set R : ℝ := 1 / s with hR
  have hR4 : 4 ≤ R := by rw [hR, le_div_iff₀ hs]; linarith
  set a : ℂ := conj τ / (y : ℂ) with ha
  set g : ℂ → ℂ := fun ξ => a * (κ ((x' : ℂ) + (y : ℂ) * ξ) - κ x') with hg
  have hnorm_a : ‖a‖ = 1 / y := by
    rw [ha, norm_div, Complex.norm_conj, hτ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
  have hgd : DifferentiableOn ℂ g {z : ℂ | ‖z‖ < R ∧ 0 < z.im} := by
    intro ξ hξ
    have h1 : DifferentiableAt ℂ κ ((x' : ℂ) + y * ξ) := hκd.differentiableAt (hO.mem_nhds (hmapO ξ hξ.1 hξ.2))
    have h2 : DifferentiableAt ℂ (fun ξ => κ ((x' : ℂ) + (y : ℂ) * ξ)) ξ :=
      h1.comp ξ ((differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id))
    exact ((h2.sub_const _).const_mul a).differentiableWithinAt
  have hgc : ContinuousOn g {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} := by
    refine continuousOn_const.mul ((hκc.comp (by fun_prop) fun ξ (hξ : ξ ∈ {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) => hmapS ξ hξ.1 hξ.2).sub continuousOn_const)
  have hA : ∀ z : ℂ, ‖z‖ ≤ R → 0 ≤ z.im → ‖g z‖ ≤ C' * R := by
    intro z hz hzi
    rw [hg, norm_mul, hnorm_a]
    have := hlip z hz hzi
    calc 1 / y * ‖κ ((x' : ℂ) + y * z) - κ x'‖ ≤ 1 / y * (C' * y * ‖z‖) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = C' * ‖z‖ := by field_simp
      _ ≤ C' * R := mul_le_mul_of_nonneg_left hz hC'.le
  have hsegg : ∀ u : ℝ, |u| ≤ R → |(g u).im| ≤ K * C' ^ 2 * s := by
    intro u hu
    have h1 := hseg u hu
    have e : g u = ((κ ((x' : ℂ) + y * u) - κ x') * conj τ) / (y : ℂ) := by
      rw [hg, ha]; ring
    rw [e, Complex.div_ofReal_im, abs_div, abs_of_pos hy0]
    rw [div_le_iff₀ hy0]
    have hu2 : u ^ 2 ≤ R ^ 2 := by rw [← sq_abs u]; exact pow_le_pow_left₀ (abs_nonneg u) hu 2
    have hRs : R ^ 2 * s ^ 2 = 1 := by rw [hR]; field_simp
    calc |((κ ((x' : ℂ) + y * u) - κ x') * conj τ).im| ≤ K * (C' * y * |u|) ^ 2 := h1
      _ = K * C' ^ 2 * y * (y * u ^ 2) := by rw [mul_pow, mul_pow, sq_abs]; ring
      _ ≤ K * C' ^ 2 * y * (y * R ^ 2) := by gcongr
      _ = K * C' ^ 2 * s * y := by
          rw [hy]; linear_combination K * C' ^ 2 * s ^ 4 * hRs
  have hflat := s31qj_flat hR4 (by positivity : 0 < K * C' ^ 2 * s) hgd hgc hA hsegg
  -- `g''(i) = a y² κ''(x' + i y)`
  have hO' : (x' : ℂ) + y * I ∈ O := hmapO I (by rw [Complex.norm_I, hR, lt_div_iff₀ hs]; linarith) (by simp)
  have hgg : deriv (deriv g) I = a * (y : ℂ) ^ 2 * deriv (deriv κ) ((x' : ℂ) + y * I) :=
    s31qj_deriv2_affine hO hκd a (x' : ℂ) (κ x') (y : ℂ) hO'
  rw [hgg, norm_mul, norm_mul, hnorm_a, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0] at hflat
  have hRs : R = 1 / s := hR
  have key : y * ‖deriv (deriv κ) ((x' : ℂ) + y * I)‖ ≤ (400 * K * C' ^ 2 + 128 * C') * s := by
    have e1 : 1 / y * y ^ 2 * ‖deriv (deriv κ) ((x' : ℂ) + y * I)‖ = y * ‖deriv (deriv κ) ((x' : ℂ) + y * I)‖ := by
      field_simp
    have e2 : 128 * (C' * R) / R ^ 2 = 128 * C' * s := by rw [hRs]; field_simp
    rw [e1, e2] at hflat
    calc y * ‖deriv (deriv κ) ((x' : ℂ) + y * I)‖ ≤ 400 * (K * C' ^ 2 * s) + 128 * C' * s := hflat
      _ = (400 * K * C' ^ 2 + 128 * C') * s := by ring
  rw [le_div_iff₀ (by positivity)]
  have h1 : s * (‖deriv (deriv κ) ((x' : ℂ) + y * I)‖ * s ^ 2) ≤ s * (400 * K * C' ^ 2 + 128 * C') := by
    calc s * (‖deriv (deriv κ) ((x' : ℂ) + y * I)‖ * s ^ 2) = y * ‖deriv (deriv κ) ((x' : ℂ) + y * I)‖ := by
          rw [hy]; ring
      _ ≤ (400 * K * C' ^ 2 + 128 * C') * s := key
      _ = s * (400 * K * C' ^ 2 + 128 * C') := by ring
  exact le_of_mul_le_mul_left h1 hs

/-- The cube root `y^{1/3}` cubes back to `y`. -/
theorem s31qj_cbrt_pow {y : ℝ} (hy : 0 ≤ y) : (y ^ ((1 : ℝ) / 3)) ^ 3 = y := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; norm_num

/-- `y^{-2/3} = 1 / (y^{1/3})²` for `y > 0`. -/
theorem s31qj_rpow_neg_two_thirds {y : ℝ} (hy : 0 < y) :
    y ^ ((1 : ℝ) / 3 - 1) = 1 / (y ^ ((1 : ℝ) / 3)) ^ 2 := by
  rw [show (1 : ℝ) / 3 - 1 = -((1 / 3) * 2) by norm_num, Real.rpow_neg hy.le, Real.rpow_mul hy.le, Real.rpow_two]
  exact (one_div _).symm

/-- **`|κ''| ≤ C₂ (Im w)^{-2/3}`** near each point of the segment, in the setting of `s31qi_reflect_across_arc`
(`s31qj_scaled` at scale `y = Im w`, `s = y^{1/3}`, with the Lipschitz bound from (B) and the quadratic deviation of
the `C^∞` curve from its tangent). -/
theorem s31qj_kappa_second
    {Jd : Set ℂ} (hJd : IsJordanDomain Jd)
    {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0) (hper : ∀ t, c (t + 1) = c t)
    (hinj : InjOn c (Ico 0 1)) (hcf : c '' Ico 0 1 = frontier Jd)
    {r : ℝ} {κ : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hcont : ContinuousOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hκinj : InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hup : MapsTo κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} (closure Jd)ᶜ)
    (hreal : MapsTo κ {z : ℂ | ‖z‖ < r ∧ z.im = 0} (frontier Jd))
    (hlocal : ∃ V : Set ℂ, IsOpen V ∧ κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} = V ∩ Jdᶜ)
    {t : ℝ} (ht : |t| < r) :
    ∃ C₂ δ : ℝ, 0 ≤ C₂ ∧ 0 < δ ∧ (∀ z : ℂ, ‖z - t‖ < δ → ‖z‖ < r) ∧ ∀ w : ℂ, ‖w - t‖ < δ → 0 < w.im →
      ‖deriv (deriv κ) w‖ ≤ C₂ / (w.im ^ ((1 : ℝ) / 3)) ^ 2 := by
  obtain ⟨C, δ0, hδ0, hCb⟩ := s31qk_deriv_bounded hJd hc hc' hper hinj hcf hhol hcont hκinj hup hreal hlocal ht
  set C' : ℝ := max C 1 with hC'
  have hC'0 : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set δ1 : ℝ := min δ0 ((r - |t|) / 2) with hδ1
  have hδ10 : 0 < δ1 := lt_min hδ0 (by linarith)
  have hδ1r : ∀ z : ℂ, ‖z - t‖ < δ1 → ‖z‖ < r := fun z hz => by
    have h1 : ‖z‖ ≤ ‖z - t‖ + |t| := by
      calc ‖z‖ = ‖(z - t) + (t : ℂ)‖ := by ring_nf
        _ ≤ ‖z - t‖ + ‖(t : ℂ)‖ := norm_add_le _ _
        _ = ‖z - t‖ + |t| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h2 : δ1 ≤ (r - |t|) / 2 := min_le_right _ _
    linarith
  set O : Set ℂ := {z : ℂ | ‖z - t‖ < δ1 ∧ 0 < z.im} with hO
  set S : Set ℂ := {z : ℂ | ‖z - t‖ < δ1 ∧ 0 ≤ z.im} with hS
  have hOo : IsOpen O :=
    (isOpen_lt (f := fun z : ℂ => ‖z - t‖) (by fun_prop) continuous_const).inter
      (isOpen_lt continuous_const continuous_im)
  have hκd : DifferentiableOn ℂ κ O := hhol.mono fun z hz => ⟨hδ1r z hz.1, hz.2⟩
  have hκc : ContinuousOn κ S := hcont.mono fun z hz => ⟨hδ1r z hz.1, hz.2⟩
  have hdiff : ∀ z : ℂ, ‖z - t‖ < δ1 → 0 < z.im → DifferentiableAt ℂ κ z := fun z hz hzi =>
    hκd.differentiableAt (hOo.mem_nhds ⟨hz, hzi⟩)
  have hbound : ∀ z : ℂ, ‖z - t‖ < δ1 → 0 < z.im → ‖deriv κ z‖ ≤ C' := fun z hz hzi =>
    (hCb z (hz.trans_le (min_le_left _ _)) (hδ1r z hz) hzi).trans (le_max_left _ _)
  have hlip := s31qj_lip_closed (x₀ := t) hκc hdiff hbound
  obtain ⟨K, ρc, hK, hρc, hcurve⟩ := s31qj_curve_normal hc hc' hper hinj
  set σ : ℝ := min (1 / 4) (min (δ1 / 4) (ρc / (2 * C'))) with hσ
  have hσ0 : 0 < σ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hσ4 : σ ≤ 1 / 4 := min_le_left _ _
  have hσδ : σ ≤ δ1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hσρ : σ ≤ ρc / (2 * C') := (min_le_right _ _).trans (min_le_right _ _)
  set δ : ℝ := min (σ ^ 3) (δ1 / 2) with hδ
  have hδ0' : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨400 * K * C' ^ 2 + 128 * C', δ, by positivity, hδ0',
    fun z hz => hδ1r z (hz.trans_le ((min_le_right _ _).trans (by linarith))), fun w hwt hwi => ?_⟩
  set x' : ℝ := w.re with hx'
  set y : ℝ := w.im with hy
  set s : ℝ := y ^ ((1 : ℝ) / 3) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hwi _
  have hs3 : y = s ^ 3 := (s31qj_cbrt_pow hwi.le).symm
  have hyδ : y < δ := by
    have := Complex.abs_im_le_norm (w - t)
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans_lt (this.trans_lt hwt)
  have hsσ : s < σ := by
    have h1 : s ^ 3 < σ ^ 3 := by rw [← hs3]; exact hyδ.trans_le (min_le_left _ _)
    exact lt_of_pow_lt_pow_left₀ 3 hσ0.le h1
  have hs4 : s ≤ 1 / 4 := hsσ.le.trans hσ4
  have hss : s ^ 2 ≤ s := by nlinarith
  have hxt : |x' - t| < δ1 / 2 := by
    have := Complex.abs_re_le_norm (w - t)
    rw [Complex.sub_re, Complex.ofReal_re] at this
    exact this.trans_lt (hwt.trans_le (min_le_right _ _))
  have hw : w = (x' : ℂ) + y * I := (Complex.re_add_im w).symm
  -- the rescaled points
  have hpt : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 / s → ‖(x' : ℂ) + y * ξ - t‖ < δ1 := by
    intro ξ hξ
    have h1 : ‖(y : ℂ) * ξ‖ ≤ s ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwi]
      calc y * ‖ξ‖ ≤ y * (1 / s) := mul_le_mul_of_nonneg_left hξ hwi.le
        _ = s ^ 2 := by rw [hs3]; field_simp
    calc ‖(x' : ℂ) + y * ξ - t‖ ≤ ‖((x' - t : ℝ) : ℂ)‖ + ‖(y : ℂ) * ξ‖ := by
          rw [show (x' : ℂ) + y * ξ - t = ((x' - t : ℝ) : ℂ) + y * ξ by push_cast; ring]; exact norm_add_le _ _
      _ < δ1 := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          have : s ≤ δ1 / 4 := hsσ.le.trans hσδ
          linarith
  have hptim : ∀ ξ : ℂ, ((x' : ℂ) + y * ξ).im = y * ξ.im := fun ξ => by simp
  have hx'S : (x' : ℂ) ∈ S := ⟨by simpa using (hpt 0 (by rw [norm_zero]; positivity)), by simp⟩
  -- the base point on the curve
  have hx'r : (x' : ℂ) ∈ {z : ℂ | ‖z‖ < r ∧ z.im = 0} := ⟨hδ1r _ hx'S.1, by simp⟩
  obtain ⟨s₀, -, hs₀⟩ : κ x' ∈ c '' Ico 0 1 := by rw [hcf]; exact hreal hx'r
  set τ : ℂ := deriv c s₀ / (‖deriv c s₀‖ : ℂ) with hτ
  have hτ1 : ‖τ‖ = 1 := by
    rw [hτ, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 (hc' s₀))]
  have hlipξ : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 / s → 0 ≤ ξ.im → ‖κ ((x' : ℂ) + y * ξ) - κ x'‖ ≤ C' * y * ‖ξ‖ := by
    intro ξ hξ hξi
    have := hlip _ _ (hpt ξ hξ) (by rw [hptim]; positivity) hx'S.1 (by simp)
    rw [show (x' : ℂ) + y * ξ - x' = y * ξ by ring, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hwi] at this
    linarith
  have hsegκ : ∀ u : ℝ, |u| ≤ 1 / s →
      |((κ ((x' : ℂ) + y * u) - κ x') * conj τ).im| ≤ K * (C' * y * |u|) ^ 2 := by
    intro u hu
    have hun : ‖(u : ℂ)‖ ≤ 1 / s := by rwa [Complex.norm_real, Real.norm_eq_abs]
    have hz : (x' : ℂ) + y * u ∈ {z : ℂ | ‖z‖ < r ∧ z.im = 0} := ⟨hδ1r _ (hpt _ hun), by simp⟩
    obtain ⟨t₁, -, ht₁⟩ : κ ((x' : ℂ) + y * u) ∈ c '' Ico 0 1 := by rw [hcf]; exact hreal hz
    have hl := hlipξ u hun (by simp)
    rw [Complex.norm_real, Real.norm_eq_abs] at hl
    have hsmall : ‖c t₁ - c s₀‖ < ρc := by
      rw [ht₁, hs₀]
      have h1 : C' * y * |u| ≤ C' * s ^ 2 := by
        calc C' * y * |u| ≤ C' * y * (1 / s) := mul_le_mul_of_nonneg_left hu (by positivity)
          _ = C' * s ^ 2 := by rw [hs3]; field_simp
      have h2 : C' * s ≤ ρc / 2 := by
        have := hsσ.le.trans hσρ
        rw [le_div_iff₀ (by positivity)] at this
        linarith
      have h3 : C' * s ^ 2 ≤ C' * s := mul_le_mul_of_nonneg_left hss hC'0.le
      linarith
    have := hcurve s₀ t₁ hsmall
    rw [ht₁, hs₀, ← hτ] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hK.le)
    exact pow_le_pow_left₀ (norm_nonneg _) hl 2
  have key := s31qj_scaled hOo hκd hκc hs0 hs4 hs3 hτ1 hK hC'0
    (fun ξ hξ hξi => ⟨hpt ξ hξ.le, by rw [hptim]; positivity⟩)
    (fun ξ hξ hξi => ⟨hpt ξ hξ, by rw [hptim]; positivity⟩) hlipξ hsegκ
  rw [← hw] at key
  exact key

/-- **Vertical increments** under `|f'| ≤ C (Im z)^{-2/3}`: `|f(x + ib) - f(x + ia)| ≤ 3C (b^{1/3} - a^{1/3})`. -/
theorem s31qj_vertical {f : ℂ → ℂ} {x₀ δ C : ℝ}
    (hf : DifferentiableOn ℂ f {z : ℂ | ‖z - x₀‖ < δ ∧ 0 < z.im})
    (hb : ∀ z : ℂ, ‖z - x₀‖ < δ → 0 < z.im → ‖deriv f z‖ ≤ C / (z.im ^ ((1 : ℝ) / 3)) ^ 2)
    {x a b : ℝ} (hx : |x - x₀| + b < δ) (ha : 0 < a) (hab : a ≤ b) :
    ‖f (x + b * I) - f (x + a * I)‖ ≤ 3 * C * (b ^ ((1 : ℝ) / 3) - a ^ ((1 : ℝ) / 3)) := by
  have hopen : IsOpen {z : ℂ | ‖z - x₀‖ < δ ∧ 0 < z.im} :=
    (isOpen_lt (f := fun z : ℂ => ‖z - x₀‖) (by fun_prop) continuous_const).inter
      (isOpen_lt continuous_const continuous_im)
  have hmem : ∀ u : ℝ, u ∈ Icc a b → ((x : ℂ) + u * I) ∈ {z : ℂ | ‖z - x₀‖ < δ ∧ 0 < z.im} := by
    intro u hu
    have hu0 : 0 < u := ha.trans_le hu.1
    refine ⟨?_, by simpa using hu0⟩
    calc ‖(x : ℂ) + u * I - x₀‖ ≤ ‖((x - x₀ : ℝ) : ℂ)‖ + ‖(u : ℂ) * I‖ := by
          rw [show (x : ℂ) + u * I - x₀ = ((x - x₀ : ℝ) : ℂ) + u * I by push_cast; ring]; exact norm_add_le _ _
      _ = |x - x₀| + u := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hu0]
      _ < δ := by linarith [hu.2]
  set φ : ℝ → ℂ := fun u => f (x + u * I) - f (x + a * I) with hφ
  have hderiv : ∀ u ∈ Icc a b, HasDerivAt φ (deriv f (x + u * I) * I) u := by
    intro u hu
    have h1 : HasDerivAt f (deriv f (x + u * I)) ((fun w : ℂ => (x : ℂ) + w * I) (u : ℂ)) :=
      (hf.differentiableAt (hopen.mem_nhds (hmem u hu))).hasDerivAt
    have h2 : HasDerivAt (fun w : ℂ => (x : ℂ) + w * I) I (u : ℂ) := by
      simpa using ((hasDerivAt_id (u : ℂ)).mul_const I).const_add (x : ℂ)
    have h3 := HasDerivAt.comp (h₂ := f) (u : ℂ) h1 h2
    have h4 := (h3.comp_ofReal).sub_const (f (x + a * I))
    exact h4
  have hcont : ContinuousOn φ (Icc a b) := fun u hu => (hderiv u hu).continuousAt.continuousWithinAt
  set B : ℝ → ℝ := fun u => 3 * C * (u ^ ((1 : ℝ) / 3) - a ^ ((1 : ℝ) / 3)) with hB
  have hBd : ∀ u ∈ Icc a b, HasDerivAt B (3 * C * ((1 / 3) * u ^ ((1 : ℝ) / 3 - 1))) u := by
    intro u hu
    have h1 := Real.hasDerivAt_rpow_const (p := (1 : ℝ) / 3) (Or.inl (ha.trans_le hu.1).ne')
    exact (h1.sub_const _).const_mul (3 * C)
  have hres := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (f := φ) (a := a) (b := b) hcont
    (fun u hu => (hderiv u (Ico_subset_Icc_self hu)).hasDerivWithinAt) (B := B)
    (by simp [hφ, hB]) (fun u hu => (hBd u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hBd u (Ico_subset_Icc_self hu)).hasDerivWithinAt)
    (fun u hu => by
      have hu' := Ico_subset_Icc_self hu
      have hu0 : 0 < u := ha.trans_le hu'.1
      rw [norm_mul, Complex.norm_I, mul_one]
      have := hb _ (hmem u hu').1 (hmem u hu').2
      have him : ((x : ℂ) + u * I).im = u := by simp
      rw [him] at this
      rw [s31qj_rpow_neg_two_thirds hu0] at *
      calc ‖deriv f (x + u * I)‖ ≤ C / (u ^ ((1 : ℝ) / 3)) ^ 2 := this
        _ = 3 * C * (1 / 3 * (1 / (u ^ ((1 : ℝ) / 3)) ^ 2)) := by ring)
    ⟨hab, le_rfl⟩
  simpa [hφ, hB] using hres

/-- A point of `[x₁, x₂]` is no farther from `x₀` than the farther endpoint. -/
theorem s31qj_uIcc_abs {x₀ x₁ x₂ u : ℝ} (hu : u ∈ uIcc x₁ x₂) :
    |u - x₀| ≤ max |x₁ - x₀| |x₂ - x₀| := by
  rcases Set.mem_uIcc.1 hu with h | h <;> rw [abs_le] <;> constructor <;>
    linarith [le_max_left |x₁ - x₀| |x₂ - x₀|, le_max_right |x₁ - x₀| |x₂ - x₀|, le_abs_self (x₁ - x₀),
      le_abs_self (x₂ - x₀), neg_abs_le (x₁ - x₀), neg_abs_le (x₂ - x₀), h.1, h.2]

/-- **Horizontal increments** at height `η`. -/
theorem s31qj_horizontal {f : ℂ → ℂ} {x₀ δ C : ℝ}
    (hf : DifferentiableOn ℂ f {z : ℂ | ‖z - x₀‖ < δ ∧ 0 < z.im})
    (hb : ∀ z : ℂ, ‖z - x₀‖ < δ → 0 < z.im → ‖deriv f z‖ ≤ C / (z.im ^ ((1 : ℝ) / 3)) ^ 2)
    {x₁ x₂ η : ℝ} (h₁ : |x₁ - x₀| + η < δ) (h₂ : |x₂ - x₀| + η < δ) (hη : 0 < η) :
    ‖f (x₂ + η * I) - f (x₁ + η * I)‖ ≤ C / (η ^ ((1 : ℝ) / 3)) ^ 2 * |x₂ - x₁| := by
  have hopen : IsOpen {z : ℂ | ‖z - x₀‖ < δ ∧ 0 < z.im} :=
    (isOpen_lt (f := fun z : ℂ => ‖z - x₀‖) (by fun_prop) continuous_const).inter
      (isOpen_lt continuous_const continuous_im)
  have hmem : ∀ u ∈ uIcc x₁ x₂, ((u : ℂ) + η * I) ∈ {z : ℂ | ‖z - x₀‖ < δ ∧ 0 < z.im} := by
    intro u hu
    have h3 := s31qj_uIcc_abs (x₀ := x₀) hu
    refine ⟨?_, by simpa using hη⟩
    calc ‖(u : ℂ) + η * I - x₀‖ ≤ ‖((u - x₀ : ℝ) : ℂ)‖ + ‖(η : ℂ) * I‖ := by
          rw [show (u : ℂ) + η * I - x₀ = ((u - x₀ : ℝ) : ℂ) + η * I by push_cast; ring]; exact norm_add_le _ _
      _ = |u - x₀| + η := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hη]
      _ < δ := by
          rcases le_total |x₁ - x₀| |x₂ - x₀| with h | h
          · rw [max_eq_right h] at h3; linarith
          · rw [max_eq_left h] at h3; linarith
  set ψ : ℝ → ℂ := fun u => f (u + η * I) with hψ
  have hderiv : ∀ u ∈ uIcc x₁ x₂, HasDerivAt ψ (deriv f (u + η * I)) u := by
    intro u hu
    have h1 : HasDerivAt f (deriv f (u + η * I)) ((fun w : ℂ => w + (η : ℂ) * I) (u : ℂ)) :=
      (hf.differentiableAt (hopen.mem_nhds (hmem u hu))).hasDerivAt
    have h2 : HasDerivAt (fun w : ℂ => w + (η : ℂ) * I) 1 (u : ℂ) := (hasDerivAt_id _).add_const _
    have h3 := HasDerivAt.comp (h₂ := f) (u : ℂ) h1 h2
    rw [mul_one] at h3
    exact h3.comp_ofReal
  have hbd : ∀ u ∈ uIcc x₁ x₂, ‖deriv f (u + η * I)‖ ≤ C / (η ^ ((1 : ℝ) / 3)) ^ 2 := by
    intro u hu
    have := hb _ (hmem u hu).1 (hmem u hu).2
    have him : ((u : ℂ) + η * I).im = η := by simp
    rwa [him] at this
  have key := (convex_uIcc x₁ x₂).norm_image_sub_le_of_norm_hasDerivWithin_le (f := ψ)
    (fun u hu => (hderiv u hu).hasDerivWithinAt) hbd left_mem_uIcc right_mem_uIcc
  rwa [Real.norm_eq_abs] at key

/-- **Hardy–Littlewood.**  If `f` is holomorphic on the half disc `{|z - x₀| < δ, Im z > 0}` with
`|f'(z)| ≤ C (Im z)^{-2/3}`, then `f` has a limit at `x₀`. -/
theorem s31qj_limit {f : ℂ → ℂ} {x₀ δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hf : DifferentiableOn ℂ f {z : ℂ | ‖z - x₀‖ < δ ∧ 0 < z.im})
    (hb : ∀ z : ℂ, ‖z - x₀‖ < δ → 0 < z.im → ‖deriv f z‖ ≤ C / (z.im ^ ((1 : ℝ) / 3)) ^ 2) :
    ∃ L : ℂ, Tendsto f (𝓝[{z : ℂ | ‖z - x₀‖ < δ ∧ 0 < z.im}] (x₀ : ℂ)) (𝓝 L) := by
  set U : Set ℂ := {z : ℂ | ‖z - x₀‖ < δ ∧ 0 < z.im} with hU
  have hcl : (x₀ : ℂ) ∈ closure U := by
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    set s : ℝ := min ε δ / 2 with hs
    have hs0 : 0 < s := by positivity
    refine ⟨(x₀ : ℂ) + s * I, ⟨?_, by simpa using hs0⟩, ?_⟩
    · rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs0]
      have := min_le_right ε δ; linarith
    · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs0]
      have := min_le_left ε δ; linarith
  have : (𝓝[U] (x₀ : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  refine cauchy_map_iff_exists_tendsto.1 (Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩)
  set q : ℝ := ε / (8 * C + 1) with hq
  have hq0 : 0 < q := by positivity
  set η : ℝ := min (δ / 8) (q ^ 3) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have hηδ : η ≤ δ / 8 := min_le_left _ _
  set e : ℝ := η ^ ((1 : ℝ) / 3) with he
  have he0 : 0 < e := Real.rpow_pos_of_pos hη0 _
  have he3 : η = e ^ 3 := (s31qj_cbrt_pow hη0.le).symm
  have heq : e ≤ q := by
    have h1 : e ^ 3 ≤ q ^ 3 := by rw [← he3]; exact min_le_right _ _
    exact le_of_pow_le_pow_left₀ (by norm_num) hq0.le h1
  have hε8 : 8 * C * e < ε := by
    have h1 : 8 * C * e ≤ 8 * C * q := mul_le_mul_of_nonneg_left heq (by positivity)
    have h2 : 8 * C * q < ε := by
      rw [hq, mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  refine ⟨f '' {z : ℂ | z ∈ U ∧ ‖z - x₀‖ < η}, Filter.image_mem_map ?_, ?_⟩
  · have h1 : {z : ℂ | ‖z - x₀‖ < η} ∈ 𝓝 (x₀ : ℂ) := by
      have : {z : ℂ | ‖z - x₀‖ < η} = ball (x₀ : ℂ) η := by ext z; simp [dist_eq_norm]
      rw [this]; exact ball_mem_nhds _ hη0
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h1] with z hz1 hz2 using ⟨hz1, hz2⟩
  · rintro _ ⟨z₁, ⟨hz₁U, hz₁⟩, rfl⟩ _ ⟨z₂, ⟨hz₂U, hz₂⟩, rfl⟩
    have hpiece : ∀ z : ℂ, z ∈ U → ‖z - x₀‖ < η →
        ‖f ((z.re : ℂ) + η * I) - f z‖ ≤ 3 * C * e ∧ |z.re - x₀| < η := by
      intro z hzU hz
      have hre : |z.re - x₀| < η := by
        have := Complex.abs_re_le_norm (z - x₀)
        rw [Complex.sub_re, Complex.ofReal_re] at this
        linarith
      have him : z.im < η := by
        have := Complex.abs_im_le_norm (z - x₀)
        rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
        exact (le_abs_self _).trans_lt (this.trans_lt hz)
      have hv := s31qj_vertical hf hb (x := z.re) (a := z.im) (b := η) (by linarith) hzU.2 him.le
      have hz' : (z.re : ℂ) + z.im * I = z := Complex.re_add_im z
      rw [hz'] at hv
      refine ⟨hv.trans ?_, hre⟩
      have h0 : 0 ≤ z.im ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hzU.2.le _
      nlinarith [mul_nonneg hC h0]
    obtain ⟨v₁, r₁⟩ := hpiece z₁ hz₁U hz₁
    obtain ⟨v₂, r₂⟩ := hpiece z₂ hz₂U hz₂
    have hh := s31qj_horizontal hf hb (x₁ := z₁.re) (x₂ := z₂.re) (η := η) (by linarith) (by linarith) hη0
    have hx : |z₂.re - z₁.re| ≤ 2 * η := by
      have := abs_sub_le z₂.re x₀ z₁.re
      rw [abs_sub_comm x₀ z₁.re] at this
      linarith
    have hhb : C / e ^ 2 * |z₂.re - z₁.re| ≤ 2 * C * e := by
      calc C / e ^ 2 * |z₂.re - z₁.re| ≤ C / e ^ 2 * (2 * η) := mul_le_mul_of_nonneg_left hx (by positivity)
        _ = 2 * C * e := by rw [he3]; field_simp
    rw [dist_eq_norm]
    have hsplit : f z₁ - f z₂ = -(f ((z₁.re : ℂ) + η * I) - f z₁) - (f ((z₂.re : ℂ) + η * I) -
        f ((z₁.re : ℂ) + η * I)) + (f ((z₂.re : ℂ) + η * I) - f z₂) := by ring
    rw [hsplit]
    calc ‖-(f ((z₁.re : ℂ) + η * I) - f z₁) - (f ((z₂.re : ℂ) + η * I) - f ((z₁.re : ℂ) + η * I)) +
          (f ((z₂.re : ℂ) + η * I) - f z₂)‖
        ≤ ‖f ((z₁.re : ℂ) + η * I) - f z₁‖ + ‖f ((z₂.re : ℂ) + η * I) - f ((z₁.re : ℂ) + η * I)‖ +
          ‖f ((z₂.re : ℂ) + η * I) - f z₂‖ := by
          have h1 := norm_add_le (-(f ((z₁.re : ℂ) + η * I) - f z₁) - (f ((z₂.re : ℂ) + η * I) -
            f ((z₁.re : ℂ) + η * I))) (f ((z₂.re : ℂ) + η * I) - f z₂)
          have h2 := norm_sub_le (-(f ((z₁.re : ℂ) + η * I) - f z₁)) (f ((z₂.re : ℂ) + η * I) -
            f ((z₁.re : ℂ) + η * I))
          rw [norm_neg] at h2
          linarith
      _ ≤ 3 * C * e + 2 * C * e + 3 * C * e := by
          gcongr
          exact hh.trans hhb
      _ < ε := by linarith

/-- **The limit of `κ'`** at each point of the segment, in the setting of `s31qi_reflect_across_arc`
(`s31qj_kappa_second` and Hardy–Littlewood `s31qj_limit` for `κ'`). -/
theorem s31qj_deriv_limit
    {Jd : Set ℂ} (hJd : IsJordanDomain Jd)
    {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0) (hper : ∀ t, c (t + 1) = c t)
    (hinj : InjOn c (Ico 0 1)) (hcf : c '' Ico 0 1 = frontier Jd)
    {r : ℝ} {κ : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hcont : ContinuousOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hκinj : InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hup : MapsTo κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} (closure Jd)ᶜ)
    (hreal : MapsTo κ {z : ℂ | ‖z‖ < r ∧ z.im = 0} (frontier Jd))
    (hlocal : ∃ V : Set ℂ, IsOpen V ∧ κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} = V ∩ Jdᶜ)
    {t : ℝ} (ht : |t| < r) :
    ∃ L : ℂ, Tendsto (deriv κ) (𝓝[{z : ℂ | ‖z‖ < r ∧ 0 < z.im}] (t : ℂ)) (𝓝 L) := by
  obtain ⟨C₂, δ, hC₂, hδ, hδr, hb⟩ :=
    s31qj_kappa_second hJd hc hc' hper hinj hcf hhol hcont hκinj hup hreal hlocal ht
  set U : Set ℂ := {z : ℂ | ‖z - t‖ < δ ∧ 0 < z.im} with hU
  have hUsub : U ⊆ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} := fun z hz => ⟨hδr z hz.1, hz.2⟩
  have hd : DifferentiableOn ℂ (deriv κ) U := by
    have ha : AnalyticOnNhd ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} := hhol.analyticOnNhd (s31qk_isOpen_upper r)
    exact (ha.deriv.mono hUsub).differentiableOn
  obtain ⟨L, hL⟩ := s31qj_limit hδ hC₂ hd hb
  refine ⟨L, ?_⟩
  have hball : ball (t : ℂ) δ ∈ 𝓝 (t : ℂ) := ball_mem_nhds _ hδ
  rw [nhdsWithin_restrict _ (mem_ball_self hδ) isOpen_ball]
  have e : {z : ℂ | ‖z‖ < r ∧ 0 < z.im} ∩ ball (t : ℂ) δ = U := by
    ext z
    simp only [hU, mem_inter_iff, mem_setOf_eq, mem_ball, dist_eq_norm]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hδr z h.1, h.2⟩, h.1⟩⟩
  rw [e]
  exact hL

end LiZhongQC
