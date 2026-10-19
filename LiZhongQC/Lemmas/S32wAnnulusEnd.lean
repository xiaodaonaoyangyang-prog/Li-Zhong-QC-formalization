import LiZhongQC.Lemmas.FiniteTypeTeichData
import LiZhongQC.ClusterSets

/-!
# §32.2 (W1.1, planar core): a quasiconformal map of an annulus end extends to the boundary circle

`s32w_qc_annulus_end_extends`: a `K`-quasiconformal map `f` of `A(1, R) = {1 < |z| < R}` into `A(1, R')` under which
the inner circles correspond (`hend`, `hend'`) extends continuously to `A(1, R) ∪ S¹`, mapping `S¹` bijectively onto
`S¹` (Lehto–Virtanen I.8.2 for two circles).

Route (approved R82, instead of the modulus route): the circle-symmetric solution `χ` of the Beltrami equation for
the dilatation of `f` (`s82td_circle_solution`, FiniteTypeTeichData) factors `f = ψ ∘ χ` with `ψ` holomorphic and
injective on a collar `A(1, 1 + ε)` (`bg_conformal_of_dilatation_eq`), and `|ψ| → 1` at the circle.  Near a point
`z₀ ∈ S¹`, in the coordinate `t ↦ z₀ e^{-it}`, a holomorphic logarithm `L` of `ψ` (on a convex half-disc) gives
`Φ = -iL` with `Im Φ = -log |ψ| → 0`, so `Φ` extends across the real segment (`schwarz_reflection_segment_of_im_tendsto_zero`)
and `ψ = exp(iΦ)` extends continuously with `|ψ| = 1` on the circle.  The same for `f⁻¹` (end condition `hend'`)
gives the inverse on the circle.  Helpers carry the prefix `s32wae_`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- A continuous logarithm of a holomorphic function on an open set is holomorphic. -/
theorem s32wae_log_differentiableOn {s : Set ℂ} (hs : IsOpen s) {g L : ℂ → ℂ} (hg : DifferentiableOn ℂ g s)
    (hL : ContinuousOn L s) (hexp : ∀ x ∈ s, Complex.exp (L x) = g x) : DifferentiableOn ℂ L s := by
  intro x hx
  have hgx : g x ≠ 0 := by rw [← hexp x hx]; exact Complex.exp_ne_zero _
  have hLx : ContinuousAt L x := hL.continuousAt (hs.mem_nhds hx)
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ s ∧ ‖L y - L x‖ < Real.pi := by
    have h1 : ∀ᶠ y in 𝓝 x, ‖L y - L x‖ < Real.pi := by
      have := hLx.tendsto
      have h2 : Tendsto (fun y => L y - L x) (𝓝 x) (𝓝 0) := by
        simpa using this.sub_const (L x)
      exact (h2.norm.eventually (gt_mem_nhds (by simpa using Real.pi_pos))).mono fun y hy => by simpa using hy
    exact (hs.eventually_mem hx).and h1
  have heq : L =ᶠ[𝓝 x] fun y => L x + Complex.log (g y / g x) := by
    filter_upwards [hnear] with y hy
    obtain ⟨hys, hyπ⟩ := hy
    have him : |(L y - L x).im| < Real.pi := lt_of_le_of_lt (Complex.abs_im_le_norm _) hyπ
    have h1 : g y / g x = Complex.exp (L y - L x) := by
      rw [Complex.exp_sub, hexp y hys, hexp x hx]
    rw [h1, Complex.log_exp (by linarith [abs_lt.1 him]) (by linarith [abs_lt.1 him])]
    ring
  have hd : DifferentiableAt ℂ (fun y => L x + Complex.log (g y / g x)) x := by
    have h1 : DifferentiableAt ℂ (fun y => g y / g x) x := (hg.differentiableAt (hs.mem_nhds hx)).div_const _
    have h2 : g x / g x ∈ Complex.slitPlane := by rw [div_self hgx]; exact Complex.one_mem_slitPlane
    exact (differentiableAt_const _).add (h1.clog h2)
  exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt

/-- Points of the open collar accumulate at every point of the circle inside any open set. -/
theorem s32wae_mem_closure {V : Set ℂ} (hV : IsOpen V) {z : ℂ} (hzV : z ∈ V) (hz : ‖z‖ = 1) {ε : ℝ}
    (hε : 0 < ε) : z ∈ closure (annulus 1 (1 + ε) ∩ V) := by
  rw [Metric.mem_closure_iff]
  intro η hη
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.1 hV z hzV
  set t : ℝ := min (min η ρ) ε / 2 with ht
  have ht0 : 0 < t := by positivity
  have htη : t < η := by have := min_le_left (min η ρ) ε; have := min_le_left η ρ; linarith
  have htρ : t < ρ := by have := min_le_left (min η ρ) ε; have := min_le_right η ρ; linarith
  have htε : t < ε := by have := min_le_right (min η ρ) ε; linarith
  have hnorm : ‖z * (1 + t)‖ = 1 + t := by
    rw [norm_mul, hz, one_mul]
    rw [show (1 + (t : ℂ)) = ((1 + t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hdist : dist z (z * (1 + t)) = t := by
    rw [dist_eq_norm, show z - z * (1 + t) = -(z * t) by ring, norm_neg, norm_mul, hz, one_mul, Complex.norm_real,
      Real.norm_of_nonneg ht0.le]
  refine ⟨z * (1 + t), ⟨⟨by rw [hnorm]; linarith, by rw [hnorm]; linarith⟩, hρV ?_⟩, by rw [hdist]; exact htη⟩
  rw [mem_ball, dist_comm, hdist]
  exact htρ

/-- **Local extension at a circle point.**  A holomorphic map `ψ` of the collar `A(1, 1 + ε)` with `|ψ| > 1` and
`|ψ(w)| → 1` as `|w| → 1` extends near every point of the circle to a continuous map with values of modulus `1` on the
circle (Schwarz reflection of `-i log ψ` in the coordinate `t ↦ z₀ e^{-it}`). -/
theorem s32wae_local_extend {ψ : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε) (hψd : DifferentiableOn ℂ ψ (annulus 1 (1 + ε)))
    (hψ1 : ∀ w ∈ annulus 1 (1 + ε), 1 < ‖ψ w‖)
    (hψe : ∀ η > 0, ∃ δ > 0, ∀ w ∈ annulus 1 (1 + ε), ‖w‖ < 1 + δ → ‖ψ w‖ < 1 + η)
    (z₀ : ℂ) (hz₀ : ‖z₀‖ = 1) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ ∃ g : ℂ → ℂ, ContinuousOn g U ∧ EqOn g ψ (U ∩ annulus 1 (1 + ε)) ∧
      ∀ z ∈ U, ‖z‖ = 1 → ‖g z‖ = 1 := by
  classical
  have hz₀0 : z₀ ≠ 0 := by intro h; rw [h, norm_zero] at hz₀; exact zero_ne_one hz₀
  have hlog : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  set s : ℝ := min (Real.log (1 + ε)) 1 with hs
  have hs0 : 0 < s := lt_min hlog one_pos
  have hsl : s ≤ Real.log (1 + ε) := min_le_left _ _
  set Ω : Set ℂ := ball (0 : ℂ) s with hΩ
  have hΩs : IsRealSymmetric Ω := by
    refine ⟨isOpen_ball, ?_⟩
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [hΩ, mem_ball_zero_iff, Complex.norm_conj]
      exact mem_ball_zero_iff.1 hu
    · intro ht
      refine ⟨conj t, ?_, Complex.conj_conj t⟩
      rw [hΩ, mem_ball_zero_iff, Complex.norm_conj]
      exact mem_ball_zero_iff.1 ht
  -- the coordinate `E(t) = z₀ e^{-it}`
  set E : ℂ → ℂ := fun t => z₀ * Complex.exp (-I * t) with hE
  have hEn : ∀ t, ‖E t‖ = Real.exp t.im := by
    intro t
    rw [hE]
    simp only
    rw [norm_mul, hz₀, one_mul, Complex.norm_exp]
    congr 1
    simp
  have hEc : Continuous E := continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul continuous_id))
  have hEA : ∀ t ∈ upperPart Ω, E t ∈ annulus 1 (1 + ε) := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have him : t.im < s := lt_of_le_of_lt (Complex.im_le_norm t) (mem_ball_zero_iff.1 ht1)
    refine ⟨?_, ?_⟩
    · rw [hEn]
      have := Real.exp_lt_exp.2 ht2; rwa [Real.exp_zero] at this
    · rw [hEn]
      calc Real.exp t.im < Real.exp s := Real.exp_lt_exp.2 him
        _ ≤ Real.exp (Real.log (1 + ε)) := Real.exp_le_exp.2 hsl
        _ = 1 + ε := Real.exp_log (by linarith)
  have hAo : IsOpen (annulus 1 (1 + ε)) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hUo : IsOpen (upperPart Ω) := hΩs.isOpen.inter (isOpen_lt continuous_const Complex.continuous_im)
  -- a holomorphic logarithm of `ψ ∘ E` on the half-disc
  have hconv : Convex ℝ (upperPart Ω) := by
    have h1 : Convex ℝ {z : ℂ | 0 < z.im} := (convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm
    exact (convex_ball (0 : ℂ) s).inter h1
  have hne : (upperPart Ω).Nonempty := by
    refine ⟨(s / 2 : ℝ) * I, ?_, ?_⟩
    · rw [hΩ, mem_ball_zero_iff, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    · simp
      positivity
  have hgd : DifferentiableOn ℂ (fun t => ψ (E t)) (upperPart Ω) := by
    intro t ht
    have h1 : DifferentiableAt ℂ ψ (E t) := hψd.differentiableAt (hAo.mem_nhds (hEA t ht))
    have h2 : DifferentiableAt ℂ E t := by
      rw [hE]
      fun_prop
    exact (h1.comp t h2).differentiableWithinAt
  obtain ⟨L, hLc, hLe⟩ := ar_cov_exists_log_on_convex hconv hne hgd.continuousOn
    (fun t ht h0 => by have := hψ1 _ (hEA t ht); rw [h0, norm_zero] at this; linarith)
  have hLd : DifferentiableOn ℂ L (upperPart Ω) := s32wae_log_differentiableOn hUo hgd hLc hLe
  set Φ : ℂ → ℂ := fun t => -I * L t with hΦ
  have hΦd : DifferentiableOn ℂ Φ (upperPart Ω) := fun t ht =>
    ((differentiableAt_const _).mul ((hLd t ht).differentiableAt (hUo.mem_nhds ht))).differentiableWithinAt
  have hΦim : ∀ t ∈ upperPart Ω, (Φ t).im = -Real.log ‖ψ (E t)‖ := by
    intro t ht
    rw [← hLe t ht, Complex.norm_exp, Real.log_exp]
    simp [hΦ, Complex.mul_im]
  -- `Im Φ → 0` at the real segment
  have him : ∀ x ∈ realPart Ω, Tendsto (fun z => (Φ z).im) (𝓝[upperPart Ω] x) (𝓝 0) := by
    intro x hx
    have hEx : ‖E x‖ = 1 := by rw [hEn, hx.2, Real.exp_zero]
    have hlim : Tendsto (fun t => ‖ψ (E t)‖) (𝓝[upperPart Ω] x) (𝓝 1) := by
      rw [Metric.tendsto_nhds]
      intro η hη
      obtain ⟨δ, hδ, hδψ⟩ := hψe η hη
      have hc : ∀ᶠ t in 𝓝[upperPart Ω] x, ‖E t‖ < 1 + δ := by
        have h1 : Tendsto (fun t => ‖E t‖) (𝓝 x) (𝓝 1) := by
          have := (continuous_norm.comp hEc).continuousAt.tendsto (x := x)
          rwa [Function.comp_apply, hEx] at this
        exact nhdsWithin_le_nhds (h1.eventually (gt_mem_nhds (by linarith)))
      filter_upwards [hc, self_mem_nhdsWithin] with t h1 h2
      have h3 := hψ1 _ (hEA t h2)
      have h4 := hδψ _ (hEA t h2) h1
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have h0 : Tendsto (fun t => -Real.log ‖ψ (E t)‖) (𝓝[upperPart Ω] x) (𝓝 (-Real.log 1)) :=
      ((Real.continuousAt_log one_ne_zero).tendsto.comp hlim).neg
    rw [Real.log_one, neg_zero] at h0
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hΦim t ht).symm
  obtain ⟨Φt, hΦtd, hΦteq⟩ := schwarz_reflection_segment_of_im_tendsto_zero hΩs hΦd him
  -- `Im Φt = 0` on the real segment
  have hreal : ∀ x ∈ realPart Ω, (Φt x).im = 0 := by
    intro x hx
    have hxΩ : x ∈ Ω := hx.1
    have hcont : ContinuousAt (fun z => (Φt z).im) x :=
      Complex.continuous_im.continuousAt.comp ((hΦtd x hxΩ).differentiableAt (hΩs.isOpen.mem_nhds hxΩ)).continuousAt
    have hnb : (𝓝[upperPart Ω] x).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
      intro η hη
      have hxs : ‖x‖ < s := mem_ball_zero_iff.1 hxΩ
      set τ : ℝ := min η (s - ‖x‖) / 2 with hτ
      have hτ0 : 0 < τ := half_pos (lt_min hη (sub_pos.2 hxs))
      have hτη : τ < η := by have := min_le_left η (s - ‖x‖); linarith
      have hτs : τ < s - ‖x‖ := by have := min_le_right η (s - ‖x‖); linarith
      refine ⟨x + τ * I, ⟨?_, ?_⟩, ?_⟩
      · rw [hΩ, mem_ball_zero_iff]
        calc ‖x + τ * I‖ ≤ ‖x‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
          _ = ‖x‖ + τ := by rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hτ0.le]
          _ < s := by linarith
      · have hx0 : x.im = 0 := hx.2
        simp [hx0, hτ0]
      · rw [dist_eq_norm, show x - (x + τ * I) = -((τ : ℂ) * I) by ring, norm_neg, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_of_nonneg hτ0.le]
        exact hτη
    have h1 : Tendsto (fun z => (Φt z).im) (𝓝[upperPart Ω] x) (𝓝 (Φt x).im) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun z => (Φt z).im) (𝓝[upperPart Ω] x) (𝓝 0) := by
      refine (him x hx).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [hΦteq hz]
    have := hnb
    exact tendsto_nhds_unique h1 h2
  -- the inverse coordinate `T(w) = i log(w/z₀)` near `z₀`
  set T : ℂ → ℂ := fun w => I * Complex.log (w / z₀) with hT
  have hslit : ∀ w ∈ ball z₀ (1 / 2), w / z₀ ∈ Complex.slitPlane := by
    intro w hw
    have h1 : ‖w / z₀ - 1‖ < 1 / 2 := by
      rw [show w / z₀ - 1 = (w - z₀) / z₀ by field_simp, norm_div, hz₀, div_one, ← dist_eq_norm]
      exact mem_ball.1 hw
    have h2 := Complex.abs_re_le_norm (w / z₀ - 1)
    rw [Complex.sub_re, Complex.one_re] at h2
    exact Complex.mem_slitPlane_iff.2 (Or.inl (by linarith [(abs_le.1 (h2.trans h1.le)).1]))
  have hne0 : ∀ w ∈ ball z₀ (1 / 2), w / z₀ ≠ 0 := fun w hw => Complex.slitPlane_ne_zero (hslit w hw)
  have hTc : ContinuousOn T (ball z₀ (1 / 2)) := fun w hw =>
    (continuousAt_const.mul ((continuousAt_id.div_const z₀).clog (hslit w hw))).continuousWithinAt
  have hTim : ∀ w ∈ ball z₀ (1 / 2), (T w).im = Real.log ‖w‖ := by
    intro w hw
    simp only [hT, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, Complex.log_re]
    rw [norm_div, hz₀, div_one]
  have hET : ∀ w ∈ ball z₀ (1 / 2), E (T w) = w := by
    intro w hw
    simp only [hE, hT]
    rw [show -I * (I * Complex.log (w / z₀)) = Complex.log (w / z₀) by ring_nf; rw [Complex.I_sq]; ring,
      Complex.exp_log (hne0 w hw), mul_div_cancel₀ _ hz₀0]
  set U : Set ℂ := ball z₀ (1 / 2) ∩ T ⁻¹' Ω with hU
  have hUo' : IsOpen U := hTc.isOpen_inter_preimage isOpen_ball hΩs.isOpen
  have hz₀U : z₀ ∈ U := by
    refine ⟨mem_ball_self (by norm_num), ?_⟩
    show I * Complex.log (z₀ / z₀) ∈ Ω
    rw [div_self hz₀0, Complex.log_one, mul_zero]
    exact mem_ball_self hs0
  refine ⟨U, hUo', hz₀U, fun w => Complex.exp (I * Φt (T w)), ?_, ?_, ?_⟩
  · exact (continuousOn_const.mul (hΦtd.continuousOn.comp (hTc.mono inter_subset_left) fun w hw => hw.2)).cexp
  · intro w hw
    obtain ⟨⟨hwb, hwΩ⟩, hwA⟩ := hw
    have hup : T w ∈ upperPart Ω := by
      refine ⟨hwΩ, ?_⟩
      rw [hTim w hwb]
      exact Real.log_pos hwA.1
    show Complex.exp (I * Φt (T w)) = ψ w
    rw [hΦteq hup]
    show Complex.exp (I * (-I * L (T w))) = ψ w
    rw [show I * (-I * L (T w)) = L (T w) by ring_nf; rw [Complex.I_sq]; ring, hLe _ hup, hET w hwb]
  · intro w hw hw1
    obtain ⟨hwb, hwΩ⟩ := hw
    have hre : T w ∈ realPart Ω := ⟨hwΩ, by rw [hTim w hwb, hw1, Real.log_one]⟩
    show ‖Complex.exp (I * Φt (T w))‖ = 1
    rw [Complex.norm_exp]
    have : (I * Φt (T w)).re = -(Φt (T w)).im := by simp [Complex.mul_re]
    rw [this, hreal _ hre, neg_zero, Real.exp_zero]

/-- **Boundary extension of a collar map.**  A holomorphic map `ψ` of the collar `A(1, 1 + ε)` with `|ψ| > 1` and
`|ψ(w)| → 1` as `|w| → 1` extends to a map continuous on `A(1, 1 + ε) ∪ S¹` with `|ψ| = 1` on `S¹` (the limit along
the collar, read off the local extensions `s32wae_local_extend`). -/
theorem s32wae_conformal_extend {ψ : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε) (hψd : DifferentiableOn ℂ ψ (annulus 1 (1 + ε)))
    (hψ1 : ∀ w ∈ annulus 1 (1 + ε), 1 < ‖ψ w‖)
    (hψe : ∀ η > 0, ∃ δ > 0, ∀ w ∈ annulus 1 (1 + ε), ‖w‖ < 1 + δ → ‖ψ w‖ < 1 + η) :
    ∃ Ψ : ℂ → ℂ, EqOn Ψ ψ (annulus 1 (1 + ε)) ∧ ContinuousOn Ψ (annulus 1 (1 + ε) ∪ sphere 0 1) ∧
      ∀ z ∈ sphere (0 : ℂ) 1, ‖Ψ z‖ = 1 := by
  classical
  set A : Set ℂ := annulus 1 (1 + ε) with hA
  have hAo : IsOpen A := (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hloc := s32wae_local_extend hε hψd hψ1 hψe
  have hnb : ∀ w : ℂ, ‖w‖ = 1 → (𝓝[A] w).NeBot := by
    intro w hw
    rw [← mem_closure_iff_nhdsWithin_neBot]
    simpa using s32wae_mem_closure isOpen_univ (mem_univ w) hw hε
  -- the limit along the collar, read off a local extension
  have hlim : ∀ U : Set ℂ, IsOpen U → ∀ g : ℂ → ℂ, ContinuousOn g U → EqOn g ψ (U ∩ A) →
      ∀ w ∈ U, Tendsto ψ (𝓝[A] w) (𝓝 (g w)) := by
    intro U hU g hgc hgψ w hwU
    have h1 : Tendsto g (𝓝[A] w) (𝓝 (g w)) :=
      ((hgc w hwU).continuousAt (hU.mem_nhds hwU)).tendsto.mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [inter_mem_nhdsWithin A (hU.mem_nhds hwU)] with v hv
    exact hgψ ⟨hv.2, hv.1⟩
  set Ψ : ℂ → ℂ := fun z => if ‖z‖ = 1 then limUnder (𝓝[A] z) ψ else ψ z with hΨ
  have hΨA : EqOn Ψ ψ A := by
    intro z hz
    show (if ‖z‖ = 1 then limUnder (𝓝[A] z) ψ else ψ z) = ψ z
    rw [if_neg hz.1.ne']
  have hval : ∀ U : Set ℂ, IsOpen U → ∀ g : ℂ → ℂ, ContinuousOn g U → EqOn g ψ (U ∩ A) →
      ∀ w ∈ U, ‖w‖ = 1 → Ψ w = g w := by
    intro U hU g hgc hgψ w hwU hw
    have := hnb w hw
    show (if ‖w‖ = 1 then limUnder (𝓝[A] w) ψ else ψ w) = g w
    rw [if_pos hw]
    exact (hlim U hU g hgc hgψ w hwU).limUnder_eq
  refine ⟨Ψ, hΨA, ?_, ?_⟩
  · intro z hz
    rcases hz with hzA | hzS
    · have h1 : ContinuousAt ψ z := (hψd.continuousOn z hzA).continuousAt (hAo.mem_nhds hzA)
      refine (h1.congr ?_).continuousWithinAt
      filter_upwards [hAo.mem_nhds hzA] with v hv
      exact (hΨA hv).symm
    · have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hzS
      obtain ⟨U, hU, hzU, g, hgc, hgψ, -⟩ := hloc z hz1
      have h1 : ContinuousWithinAt g (A ∪ sphere 0 1) z :=
        ((hgc z hzU).continuousAt (hU.mem_nhds hzU)).continuousWithinAt
      refine h1.congr_of_eventuallyEq ?_ (hval U hU g hgc hgψ z hzU hz1)
      filter_upwards [inter_mem_nhdsWithin (A ∪ sphere 0 1) (hU.mem_nhds hzU)] with v hv
      obtain ⟨hvA | hvS, hvU⟩ := hv
      · rw [hΨA hvA]
        exact (hgψ ⟨hvU, hvA⟩).symm
      · exact hval U hU g hgc hgψ v hvU (mem_sphere_zero_iff_norm.1 hvS)
  · intro z hz
    have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hz
    obtain ⟨U, hU, hzU, g, hgc, hgψ, hg1⟩ := hloc z hz1
    rw [hval U hU g hgc hgψ z hzU hz1]
    exact hg1 z hzU hz1

/-- A continuous map sending `{|z| > 1}` into `{|w| > 1}` sends points with `|z| ≤ R` near the circle only from
points near the circle: `|g z| < 1 + δ` forces `|z| < 1 + δ₀` (compactness of `{1 + δ₀ ≤ |z| ≤ R}`). -/
theorem s32wae_end_transfer {g : ℂ → ℂ} (hg : Continuous g) (hout : ∀ z, 1 < ‖z‖ → 1 < ‖g z‖) (R : ℝ) {δ₀ : ℝ}
    (hδ₀ : 0 < δ₀) : ∃ δ > 0, ∀ z, ‖z‖ ≤ R → ‖g z‖ < 1 + δ → ‖z‖ < 1 + δ₀ := by
  set C : Set ℂ := closedBall 0 R ∩ {z | 1 + δ₀ ≤ ‖z‖} with hC
  have hCc : IsCompact C := (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_norm)
  have hgC : IsClosed (g '' C) := (hCc.image hg).isClosed
  have hsub : closedBall (0 : ℂ) 1 ⊆ (g '' C)ᶜ := by
    rintro w hw ⟨z, hzC, rfl⟩
    have h0 : 1 + δ₀ ≤ ‖z‖ := hzC.2
    have h1 := hout z (by linarith)
    have h2 : ‖g z‖ ≤ 1 := mem_closedBall_zero_iff.1 hw
    linarith
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_cthickening_subset_open hgC.isOpen_compl hsub
  rw [cthickening_closedBall hδ.le zero_le_one] at hδsub
  refine ⟨δ, hδ, fun z hzR hgz => ?_⟩
  by_contra hcon
  exact hδsub (mem_closedBall_zero_iff.2 (by linarith)) ⟨z, ⟨mem_closedBall_zero_iff.2 hzR, not_lt.1 hcon⟩, rfl⟩

/-- Two collar maps that are mutually inverse near the circle have mutually inverse boundary extensions: if `ψ`
maps points of `A(1, 1 + ε)` near the circle into `A(1, 1 + ε')` and `ω ∘ ψ = id` there, then `Ω (Ψ ζ) = ζ` for the
continuous extensions `Ψ`, `Ω` and every `ζ ∈ S¹` with `Ψ ζ ∈ S¹`. -/
theorem s32wae_inverse_on_circle {ψ ω Ψ Ωx : ℂ → ℂ} {ε ε' : ℝ} (hε : 0 < ε)
    (hΨc : ContinuousOn Ψ (annulus 1 (1 + ε) ∪ sphere 0 1)) (hΨe : EqOn Ψ ψ (annulus 1 (1 + ε)))
    (hΩc : ContinuousOn Ωx (annulus 1 (1 + ε') ∪ sphere 0 1)) (hΩe : EqOn Ωx ω (annulus 1 (1 + ε')))
    (hmap : ∃ δ > 0, ∀ w ∈ annulus 1 (1 + ε), ‖w‖ < 1 + δ → ψ w ∈ annulus 1 (1 + ε') ∧ ω (ψ w) = w)
    {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) (hΨζ : Ψ ζ ∈ sphere (0 : ℂ) 1) : Ωx (Ψ ζ) = ζ := by
  obtain ⟨δ, hδ, hδm⟩ := hmap
  set A : Set ℂ := annulus 1 (1 + ε) with hA
  have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
  have hnb : (𝓝[A] ζ).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    simpa using s32wae_mem_closure isOpen_univ (mem_univ ζ) hζ1 hε
  have hnear : ∀ᶠ w in 𝓝[A] ζ, w ∈ A ∧ ‖w‖ < 1 + δ := by
    have h1 : {w : ℂ | ‖w‖ < 1 + δ} ∈ 𝓝 ζ :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds (show ‖ζ‖ < 1 + δ by rw [hζ1]; linarith)
    exact eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds h1)
  have hΨt : Tendsto ψ (𝓝[A] ζ) (𝓝 (Ψ ζ)) := by
    have h1 : Tendsto Ψ (𝓝[A] ζ) (𝓝 (Ψ ζ)) :=
      (hΨc ζ (Or.inr hζ)).tendsto.mono_left (nhdsWithin_mono _ subset_union_left)
    refine h1.congr' ?_
    filter_upwards [hnear] with w hw
    exact hΨe hw.1
  have hψt : Tendsto ψ (𝓝[A] ζ) (𝓝[annulus 1 (1 + ε') ∪ sphere 0 1] (Ψ ζ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hΨt, ?_⟩
    filter_upwards [hnear] with w hw
    exact Or.inl (hδm w hw.1 hw.2).1
  have h2 : Tendsto (fun w => Ωx (ψ w)) (𝓝[A] ζ) (𝓝 (Ωx (Ψ ζ))) := (hΩc _ (Or.inr hΨζ)).tendsto.comp hψt
  have h3 : Tendsto (fun w => Ωx (ψ w)) (𝓝[A] ζ) (𝓝 ζ) := by
    refine (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto id (𝓝[A] ζ) (𝓝 ζ)).congr' ?_
    filter_upwards [hnear] with w hw
    show w = Ωx (ψ w)
    rw [hΩe (hδm w hw.1 hw.2).1, (hδm w hw.1 hw.2).2]
  exact tendsto_nhds_unique h2 h3

/-- **§32.2 (W1.1, planar core).**  A `K`-quasiconformal map of `A(1, R)` into `A(1, R')` under which the inner
circles correspond extends continuously to `A(1, R) ∪ S¹`, mapping `S¹` bijectively onto `S¹`.  Proof: `f = ψ ∘ h` with
`h` the circle-symmetric solution of the Beltrami equation for `μ_f` (`s82td_circle_solution`) and `ψ` conformal on a
collar (`bg_conformal_of_dilatation_eq`); `ψ` and its inverse extend to the circle (`s32wae_conformal_extend`) and
the extensions are mutually inverse there (`s32wae_inverse_on_circle`). -/
theorem s32w_qc_annulus_end_extends {R R' K : ℝ} (hR : 1 < R) (hR' : 1 < R') {f : ℂ → ℂ}
    (hf : IsKQC f (annulus 1 R) K) (hmap : MapsTo f (annulus 1 R) (annulus 1 R'))
    (hend : ∀ ε > 0, ∃ δ > 0, ∀ z ∈ annulus 1 R, ‖z‖ < 1 + δ → ‖f z‖ < 1 + ε)
    (hend' : ∀ δ > 0, ∃ ε > 0, ∀ w ∈ annulus 1 R', ‖w‖ < 1 + ε → ∃ z ∈ annulus 1 R, ‖z‖ < 1 + δ ∧ f z = w) :
    ∃ F : ℂ → ℂ, EqOn F f (annulus 1 R) ∧ ContinuousOn F (annulus 1 R ∪ sphere 0 1) ∧
      F '' sphere 0 1 = sphere 0 1 ∧ InjOn F (sphere 0 1) := by
  classical
  set A : Set ℂ := annulus 1 R with hAdef
  have hAo : IsOpen A := hf.1
  have hK1 : (1 : ℝ) ≤ K := hf.2.1
  have hk0 : 0 ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hk1 : (K - 1) / (K + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  obtain ⟨hμ, -⟩ := thm10_2_genHomeoSolution_of_isKQC hf
  obtain ⟨h, Kh, hdisc, hhK, hdil⟩ := s82td_circle_solution hR hk0 hk1 hμ
  have hhA : IsKQC h A Kh := ac_t_isKQC_restrict hhK hAo (subset_univ _)
  have hconf : IsConformalOnto (f ∘ Function.invFunOn h A) (h '' A) (f '' A) :=
    bg_conformal_of_dilatation_eq hhA hf (hdil.mono fun w hw => hw.symm)
  set ψ : ℂ → ℂ := f ∘ Function.invFunOn h A with hψdef
  have hψh : ∀ z ∈ A, ψ (h z) = f z := by
    intro z hz
    show f (Function.invFunOn h A (h z)) = f z
    rw [h.injective.injOn.leftInvOn_invFunOn hz]
  -- `h` preserves the circle and the exterior
  have hpre : h ⁻¹' closedBall 0 1 = closedBall 0 1 := by
    ext w
    simp only [mem_preimage, mem_closedBall_zero_iff]
    exact hdisc w
  have hball : h ⁻¹' ball 0 1 = ball 0 1 := by
    rw [← interior_closedBall (0 : ℂ) one_ne_zero, h.preimage_interior, hpre]
  have hlt : ∀ w, ‖h w‖ < 1 ↔ ‖w‖ < 1 := by
    intro w
    have h1 : w ∈ h ⁻¹' ball 0 1 ↔ w ∈ ball (0 : ℂ) 1 := by rw [hball]
    rw [mem_preimage, mem_ball_zero_iff, mem_ball_zero_iff] at h1
    exact h1
  have hS : ∀ w, ‖h w‖ = 1 ↔ ‖w‖ = 1 := by
    intro w
    have h1 := hdisc w
    have h2 := hlt w
    constructor
    · intro hw
      refine le_antisymm (h1.1 hw.le) (not_lt.1 fun h3 => ?_)
      have := h2.2 h3
      linarith
    · intro hw
      refine le_antisymm (h1.2 hw.le) (not_lt.1 fun h3 => ?_)
      have := h2.1 h3
      linarith
  have hout : ∀ w, 1 < ‖w‖ → 1 < ‖h w‖ := fun w hw =>
    lt_of_not_ge fun h3 => by have := (hdisc w).1 h3; linarith
  have hout' : ∀ w, 1 < ‖w‖ → 1 < ‖h.symm w‖ := fun w hw =>
    lt_of_not_ge fun h3 => by have := (hdisc (h.symm w)).2 h3; rw [h.apply_symm_apply] at this; linarith
  -- the source collar `A(1, ρ) ⊆ h(A)`
  have hV : IsOpen (h '' ball (0 : ℂ) R) := h.isOpenMap _ isOpen_ball
  have hcV : closedBall (0 : ℂ) 1 ⊆ h '' ball 0 R := by
    intro w hw
    refine ⟨h.symm w, mem_ball_zero_iff.2 ?_, h.apply_symm_apply w⟩
    have := (hdisc (h.symm w)).1 (by rw [h.apply_symm_apply]; exact mem_closedBall_zero_iff.1 hw)
    linarith
  obtain ⟨ρ, hρ1, hρV⟩ := s31sh_larger_closed_disc hV hcV
  have hρe : (0 : ℝ) < ρ - 1 := by linarith
  have hcol : ∀ w ∈ annulus 1 (1 + (ρ - 1)), ∃ z ∈ A, h z = w := by
    intro w hw
    have hw1 : 1 < ‖w‖ := hw.1
    have hw2 : ‖w‖ < 1 + (ρ - 1) := hw.2
    obtain ⟨z, hz, rfl⟩ := hρV (mem_closedBall_zero_iff.2 (by linarith))
    refine ⟨z, ⟨lt_of_not_ge fun h3 => ?_, mem_ball_zero_iff.1 hz⟩, rfl⟩
    have := (hdisc z).2 h3
    linarith
  have hcolA : ∀ w ∈ annulus 1 (1 + (ρ - 1)), w ∈ h '' A := fun w hw => by
    obtain ⟨z, hz, rfl⟩ := hcol w hw
    exact mem_image_of_mem h hz
  -- `ψ` on the source collar
  have hψd : DifferentiableOn ℂ ψ (annulus 1 (1 + (ρ - 1))) := hconf.1.mono hcolA
  have hψ1 : ∀ w ∈ annulus 1 (1 + (ρ - 1)), 1 < ‖ψ w‖ := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hcol w hw
    rw [hψh z hz]
    exact (hmap hz).1
  have hψe : ∀ η > 0, ∃ δ > 0, ∀ w ∈ annulus 1 (1 + (ρ - 1)), ‖w‖ < 1 + δ → ‖ψ w‖ < 1 + η := by
    intro η hη
    obtain ⟨δ₀, hδ₀, hδ₀f⟩ := hend η hη
    obtain ⟨δ, hδ, hδt⟩ := s32wae_end_transfer h.continuous hout R hδ₀
    refine ⟨δ, hδ, fun w hw hwδ => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hcol w hw
    rw [hψh z hz]
    have hzR : ‖z‖ < R := hz.2
    exact hδ₀f z hz (hδt z hzR.le hwδ)
  -- the target collar `A(1, 1 + e) ⊆ f(A)` and the inverse `ω`
  obtain ⟨ε₁, hε₁, hε₁f⟩ := hend' (R - 1) (by linarith)
  set e : ℝ := min ε₁ (R' - 1) with he
  have he0 : 0 < e := lt_min hε₁ (by linarith)
  have hcolT : ∀ w ∈ annulus 1 (1 + e), w ∈ annulus 1 R' ∧ ‖w‖ < 1 + ε₁ := by
    intro w hw
    have hw1 : 1 < ‖w‖ := hw.1
    have hw2 : ‖w‖ < 1 + e := hw.2
    have := min_le_left ε₁ (R' - 1)
    have := min_le_right ε₁ (R' - 1)
    exact ⟨⟨hw1, by linarith⟩, by linarith⟩
  have hcolTA : ∀ w ∈ annulus 1 (1 + e), w ∈ f '' A := by
    intro w hw
    obtain ⟨z, hz, -, hzw⟩ := hε₁f w (hcolT w hw).1 (hcolT w hw).2
    exact ⟨z, hz, hzw⟩
  have hhAo : IsOpen (h '' A) := h.isOpenMap A hAo
  have hω : IsConformalOnto (Function.invFunOn ψ (h '' A)) (f '' A) (h '' A) := hconf.symm hhAo
  set ω : ℂ → ℂ := Function.invFunOn ψ (h '' A) with hωdef
  have hωf : ∀ z ∈ A, ω (f z) = h z := by
    intro z hz
    rw [← hψh z hz]
    exact hconf.2.1.leftInvOn_invFunOn (mem_image_of_mem h hz)
  have hψω : ∀ w ∈ f '' A, ψ (ω w) = w := by
    intro w hw
    have : w ∈ ψ '' (h '' A) := by rw [hconf.2.2]; exact hw
    exact Function.invFunOn_eq this
  have hωd : DifferentiableOn ℂ ω (annulus 1 (1 + e)) := hω.1.mono hcolTA
  have hωmem : ∀ w ∈ annulus 1 (1 + e), ω w ∈ h '' A := by
    intro w hw
    have := mem_image_of_mem ω (hcolTA w hw)
    rwa [hω.2.2] at this
  have hω1 : ∀ w ∈ annulus 1 (1 + e), 1 < ‖ω w‖ := by
    intro w hw
    obtain ⟨z, hz, hzw⟩ := hωmem w hw
    rw [← hzw]
    exact hout z hz.1
  obtain ⟨R'', hR''⟩ := ((isCompact_closedBall (0 : ℂ) R).image h.continuous).isBounded.subset_closedBall 0
  have hωe : ∀ η > 0, ∃ δ > 0, ∀ w ∈ annulus 1 (1 + e), ‖w‖ < 1 + δ → ‖ω w‖ < 1 + η := by
    intro η hη
    obtain ⟨δ₁, hδ₁, hδ₁t⟩ := s32wae_end_transfer h.symm.continuous hout' R'' hη
    obtain ⟨ε₂, hε₂, hε₂f⟩ := hend' δ₁ hδ₁
    refine ⟨ε₂, hε₂, fun w hw hwε => ?_⟩
    obtain ⟨z, hz, hzδ, rfl⟩ := hε₂f w (hcolT w hw).1 hwε
    rw [hωf z hz]
    have hzR : ‖z‖ < R := hz.2
    have hhz : ‖h z‖ ≤ R'' := mem_closedBall_zero_iff.1 (hR'' (mem_image_of_mem h (mem_closedBall_zero_iff.2 hzR.le)))
    exact hδ₁t (h z) hhz (by rw [h.symm_apply_apply]; exact hzδ)
  -- the boundary extensions and their inverse relation
  obtain ⟨Ψ, hΨe, hΨc, hΨ1⟩ := s32wae_conformal_extend hρe hψd hψ1 hψe
  obtain ⟨Ωx, hΩe, hΩc, hΩ1⟩ := s32wae_conformal_extend he0 hωd hω1 hωe
  have hmap1 : ∃ δ > 0, ∀ w ∈ annulus 1 (1 + (ρ - 1)), ‖w‖ < 1 + δ → ψ w ∈ annulus 1 (1 + e) ∧ ω (ψ w) = w := by
    obtain ⟨δ, hδ, hδψ⟩ := hψe e he0
    refine ⟨δ, hδ, fun w hw hwδ => ⟨⟨hψ1 w hw, hδψ w hw hwδ⟩, ?_⟩⟩
    obtain ⟨z, hz, rfl⟩ := hcol w hw
    rw [hψh z hz, hωf z hz]
  have hmap2 : ∃ δ > 0, ∀ w ∈ annulus 1 (1 + e), ‖w‖ < 1 + δ → ω w ∈ annulus 1 (1 + (ρ - 1)) ∧ ψ (ω w) = w := by
    obtain ⟨δ, hδ, hδω⟩ := hωe (ρ - 1) hρe
    exact ⟨δ, hδ, fun w hw hwδ => ⟨⟨hω1 w hw, hδω w hw hwδ⟩, hψω w (hcolTA w hw)⟩⟩
  have hΨS : ∀ z ∈ sphere (0 : ℂ) 1, Ψ z ∈ sphere (0 : ℂ) 1 := fun z hz =>
    mem_sphere_zero_iff_norm.2 (hΨ1 z hz)
  have hΩS : ∀ z ∈ sphere (0 : ℂ) 1, Ωx z ∈ sphere (0 : ℂ) 1 := fun z hz =>
    mem_sphere_zero_iff_norm.2 (hΩ1 z hz)
  have hinv1 : ∀ ζ ∈ sphere (0 : ℂ) 1, Ωx (Ψ ζ) = ζ := fun ζ hζ =>
    s32wae_inverse_on_circle hρe hΨc hΨe hΩc hΩe hmap1 hζ (hΨS ζ hζ)
  have hinv2 : ∀ ζ ∈ sphere (0 : ℂ) 1, Ψ (Ωx ζ) = ζ := fun ζ hζ =>
    s32wae_inverse_on_circle he0 hΩc hΩe hΨc hΨe hmap2 hζ (hΩS ζ hζ)
  have hhS : ∀ z ∈ sphere (0 : ℂ) 1, h z ∈ sphere (0 : ℂ) 1 := fun z hz =>
    mem_sphere_zero_iff_norm.2 ((hS z).2 (mem_sphere_zero_iff_norm.1 hz))
  -- the extension
  set F : ℂ → ℂ := fun z => if ‖z‖ = 1 then Ψ (h z) else f z with hF
  have hFS : ∀ z ∈ sphere (0 : ℂ) 1, F z = Ψ (h z) := fun z hz => by
    show (if ‖z‖ = 1 then Ψ (h z) else f z) = Ψ (h z)
    rw [if_pos (mem_sphere_zero_iff_norm.1 hz)]
  have hFA : EqOn F f A := by
    intro z hz
    show (if ‖z‖ = 1 then Ψ (h z) else f z) = f z
    rw [if_neg (show (1 : ℝ) < ‖z‖ from hz.1).ne']
  refine ⟨F, hFA, ?_, ?_, ?_⟩
  · intro z hz
    rcases hz with hzA | hzS
    · have h1 : ContinuousAt f z := (hf.2.2.1.1 z hzA).continuousAt (hAo.mem_nhds hzA)
      refine (h1.congr ?_).continuousWithinAt
      filter_upwards [hAo.mem_nhds hzA] with v hv
      exact (hFA hv).symm
    · have hz1 : ‖h z‖ = 1 := mem_sphere_zero_iff_norm.1 (hhS z hzS)
      have hnear : ∀ᶠ v in 𝓝[A ∪ sphere 0 1] z, v ∈ A ∪ sphere 0 1 ∧ ‖h v‖ < 1 + (ρ - 1) := by
        have h1 : {v : ℂ | ‖h v‖ < 1 + (ρ - 1)} ∈ 𝓝 z :=
          (isOpen_lt (continuous_norm.comp h.continuous) continuous_const).mem_nhds
            (show ‖h z‖ < 1 + (ρ - 1) by rw [hz1]; linarith)
        exact eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds h1)
      have hG : ContinuousWithinAt (fun v => Ψ (h v)) (A ∪ sphere 0 1) z := by
        have h2 : Tendsto h (𝓝[A ∪ sphere 0 1] z) (𝓝[annulus 1 (1 + (ρ - 1)) ∪ sphere 0 1] (h z)) := by
          refine tendsto_nhdsWithin_iff.2 ⟨(h.continuous.tendsto z).mono_left nhdsWithin_le_nhds, ?_⟩
          filter_upwards [hnear] with v hv
          obtain ⟨hvA | hvS, hvρ⟩ := hv
          · exact Or.inl ⟨hout v hvA.1, hvρ⟩
          · exact Or.inr (hhS v hvS)
        exact (hΨc (h z) (Or.inr (hhS z hzS))).tendsto.comp h2
      refine hG.congr_of_eventuallyEq ?_ (hFS z hzS)
      filter_upwards [hnear] with v hv
      obtain ⟨hvA | hvS, hvρ⟩ := hv
      · rw [hFA hvA, ← hψh v hvA]
        exact (hΨe ⟨hout v hvA.1, hvρ⟩).symm
      · exact hFS v hvS
  · apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [hFS z hz]
      exact hΨS _ (hhS z hz)
    · intro ξ hξ
      have h1 : Ωx ξ ∈ sphere (0 : ℂ) 1 := hΩS ξ hξ
      have h2 : h.symm (Ωx ξ) ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, ← hS, h.apply_symm_apply]
        exact mem_sphere_zero_iff_norm.1 h1
      refine ⟨h.symm (Ωx ξ), h2, ?_⟩
      rw [hFS _ h2, h.apply_symm_apply]
      exact hinv2 ξ hξ
  · intro a ha b hb hab
    rw [hFS a ha, hFS b hb] at hab
    have := congrArg Ωx hab
    rw [hinv1 _ (hhS a ha), hinv1 _ (hhS b hb)] at this
    exact h.injective this

end LiZhongQC
