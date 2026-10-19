import LiZhongQC.ClusterSets
import LiZhongQC.Lemmas.Koebe
import LiZhongQC.RiemannMapping

/-!
# Reflection of a boundary-real quadratic coefficient across a `C^∞` boundary arc (round78 QD lane)

Proof of the frozen stub `s31qi_reflect_across_arc` of the QD interface (statement and docstring copied verbatim).
Helpers carry the prefix `s31qk_`.

* (B) `s31qk_deriv_bounded`: `|κ'|` is bounded near the segment (Harnack's inequality for `Im ∘ κ⁻¹` on exterior tangent
  discs at the nearest boundary point, then Koebe's one-quarter theorem).
* At a segment point where `Qc ∘ κ = 0` the pulled-back coefficient tends to `0` (`s31qk_zero_case`); where it does not
  vanish, the natural parameter `G = ∫ √(Qc ∘ κ) κ'` has `Im (λ̄ G)` constant on the segment (chord estimate along the
  `C^∞` curve, `s31qk_key_estimate`, `s31qk_boundary_const`), so it reflects and `Q = G'²` is real there
  (`s31qk_nonzero_case'`).
* `Im Q → 0` along the whole segment; odd reflection and a harmonic conjugate give `G` (`s31qk_reflect`).
-/

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- **Harnack's inequality** on a disc (lower bound): a harmonic function, nonnegative on the circle `|z - b| = R`,
satisfies `u w ≥ (R - |w - b|)/(R + |w - b|) · u b` inside. -/
theorem s31qk_harnack {u : ℂ → ℝ} {b w : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : InnerProductSpace.HarmonicOnNhd u (closedBall b R)) (hpos : ∀ z ∈ sphere b R, 0 ≤ u z)
    (hw : w ∈ ball b R) :
    (R - ‖w - b‖) / (R + ‖w - b‖) * u b ≤ u w := by
  have hR' : |R| = R := abs_of_pos hR
  have h1 := hu.circleAverage_poissonKernel_smul hw
  have h2 : Real.circleAverage u b R = u b := by
    have hu' : InnerProductSpace.HarmonicOnNhd u (closedBall b |R|) := by rw [hR']; exact hu
    exact hu'.circleAverage_eq
  have hint : CircleIntegrable u b R :=
    (hu.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR.le
  have hcP : ContinuousOn (poissonKernel b w) (sphere b R) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel, herglotzRieszKernel_fun_def]
    refine Complex.continuous_re.comp_continuousOn (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    intro z hz h0
    have hz' : ‖z - b‖ = R := by simpa [dist_eq_norm] using hz
    have hw' : ‖w - b‖ < R := by simpa [dist_eq_norm] using hw
    have : z - b = w - b := sub_eq_zero.1 h0
    rw [this] at hz'
    linarith
  have hint2 : CircleIntegrable (poissonKernel b w • u) b R :=
    (hcP.smul (hu.continuousOn.mono sphere_subset_closedBall)).circleIntegrable hR.le
  set k : ℝ := (R - ‖w - b‖) / (R + ‖w - b‖) with hk
  calc k * u b = Real.circleAverage (k • u) b R := by
        rw [Real.circleAverage_smul, h2, smul_eq_mul]
    _ ≤ Real.circleAverage (poissonKernel b w • u) b R := by
        apply Real.circleAverage_mono (hint.const_smul (a := k)) hint2
        intro z hz
        rw [hR'] at hz
        simp only [Pi.smul_apply, smul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (hpos z hz)
        rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply, herglotzRieszKernel_def]
        exact le_re_herglotzRieszKernel hz hw
    _ = u w := h1

/-- A periodic continuous real function attains its global bounds on `[0, 1]`. -/
theorem s31qk_periodic_bounds {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    ∃ a b : ℝ, (∀ t, f t ≤ f b) ∧ ∀ t, f a ≤ f t := by
  obtain ⟨b, -, hb⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one) hf.continuousOn
  obtain ⟨a, -, ha⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hf.continuousOn
  refine ⟨a, b, fun t => ?_, fun t => ?_⟩
  · obtain ⟨y, hy, hty⟩ := hp.exists_mem_Ico₀ one_pos t
    rw [hty]; exact hb (Ico_subset_Icc_self hy)
  · obtain ⟨y, hy, hty⟩ := hp.exists_mem_Ico₀ one_pos t
    rw [hty]; exact ha (Ico_subset_Icc_self hy)

/-- Uniform bounds for a smooth `1`-periodic regular curve: `δ ≤ |c'| ≤ M` and the second-order Taylor bound
`|c(s + d) - c s - d c'(s)| ≤ M d²`. -/
theorem s31qk_curve_bounds {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0)
    (hper : ∀ t, c (t + 1) = c t) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ (∀ t, δ ≤ ‖deriv c t‖) ∧ (∀ t, ‖deriv c t‖ ≤ M) ∧
      ∀ s d : ℝ, ‖c (s + d) - c s - (d : ℂ) * deriv c s‖ ≤ M * d ^ 2 := by
  have hp : Function.Periodic c 1 := hper
  have hp1 : Function.Periodic (deriv c) 1 := fun t => by
    have h := congrArg deriv (funext hper : (fun t => c (t + 1)) = c)
    rw [← congrFun h t, deriv_comp_add_const]
  have hp2 : Function.Periodic (deriv (deriv c)) 1 := fun t => by
    have h := congrArg deriv (funext hp1 : (fun t => deriv c (t + 1)) = deriv c)
    rw [← congrFun h t, deriv_comp_add_const]
  have hc1 : ContDiff ℝ ∞ (deriv c) := ContDiff.iterate_deriv 1 hc
  have hc2 : ContDiff ℝ ∞ (deriv (deriv c)) := ContDiff.iterate_deriv 2 hc
  obtain ⟨a₁, b₁, hb₁, ha₁⟩ := s31qk_periodic_bounds hc1.continuous.norm (fun t => by
    simp only [hp1 t])
  obtain ⟨-, b₂, hb₂, -⟩ := s31qk_periodic_bounds hc2.continuous.norm (fun t => by
    simp only [hp2 t])
  set M : ℝ := max (max ‖deriv c b₁‖ ‖deriv (deriv c) b₂‖) 1 with hM
  have hM1 : ‖deriv c b₁‖ ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hM2 : ‖deriv (deriv c) b₂‖ ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨‖deriv c a₁‖, M, norm_pos_iff.2 (hc' a₁), lt_of_lt_of_le one_pos (le_max_right _ _),
    ha₁, fun t => (hb₁ t).trans hM1, fun s d => ?_⟩
  -- `c'` is `M`-Lipschitz
  have hlip : ∀ x y : ℝ, ‖deriv c y - deriv c x‖ ≤ M * ‖y - x‖ := fun x y =>
    Convex.norm_image_sub_le_of_norm_deriv_le (s := univ)
      (fun z _ => (hc1.differentiable (by simp)).differentiableAt) (fun z _ => (hb₂ z).trans hM2)
      convex_univ (mem_univ _) (mem_univ _)
  -- `g x = c x - x c'(s)` has `|g'| ≤ M |d|` between `s` and `s + d`
  set g : ℝ → ℂ := fun x => c x - (x : ℂ) * deriv c s with hg
  have hgd : ∀ x, HasDerivAt g (deriv c x - deriv c s) x := fun x => by
    have h1 := (hc.differentiable (by simp)).differentiableAt (x := x) |>.hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * deriv c s) (deriv c s) x := by
      simpa using ((hasDerivAt_id (x : ℝ)).ofReal_comp).mul_const (deriv c s)
    exact h1.sub h2
  have hbd : ∀ x ∈ uIcc s (s + d), ‖deriv g x‖ ≤ M * |d| := by
    intro x hx
    rw [(hgd x).deriv]
    refine (hlip s x).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [Real.norm_eq_abs]
    rcases le_total 0 d with h | h
    · rw [uIcc_of_le (by linarith)] at hx
      rw [abs_of_nonneg (by linarith [hx.1]), abs_of_nonneg h]; linarith [hx.2]
    · rw [uIcc_of_ge (by linarith)] at hx
      rw [abs_of_nonpos (by linarith [hx.2]), abs_of_nonpos h]; linarith [hx.1]
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := g)
    (fun x _ => (hgd x).differentiableAt) hbd (convex_uIcc s (s + d)) left_mem_uIcc right_mem_uIcc
  have e : g (s + d) - g s = c (s + d) - c s - (d : ℂ) * deriv c s := by
    simp only [hg]; push_cast; ring
  rw [e, add_sub_cancel_left, Real.norm_eq_abs] at key
  calc _ ≤ M * |d| * |d| := key
    _ = M * d ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- A `1`-periodic map that is injective on `[0, 1)` does not take equal values at points whose distance is not an
integer. -/
theorem s31qk_periodic_ne {c : ℝ → ℂ} (hper : ∀ t, c (t + 1) = c t) (hinj : InjOn c (Ico 0 1)) {x y : ℝ}
    (h0 : 0 < |x - y|) (h1 : |x - y| < 1) : c x ≠ c y := by
  have hp : Function.Periodic c 1 := hper
  have hf : ∀ z : ℝ, c z = c (Int.fract z) := fun z => by
    have := (hp.int_mul ⌊z⌋) (Int.fract z)
    rw [mul_one, Int.fract_add_floor] at this
    exact this
  intro hxy
  rw [hf x, hf y] at hxy
  have hfr := hinj ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩ ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩ hxy
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.1 hfr
  rw [hz] at h0 h1
  have h0' : ((0 : ℤ) : ℝ) < ((|z| : ℤ) : ℝ) := by rw [Int.cast_abs]; simpa using h0
  have h1' : ((|z| : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by rw [Int.cast_abs]; simpa using h1
  have a0 : (0 : ℤ) < |z| := Int.cast_lt.1 h0'
  have a1 : |z| < 1 := Int.cast_lt.1 h1'
  omega

/-- **Injectivity gap** of a periodic simple closed curve: points at parameter distance in `[η, 1/2]` are at least
`ε` apart. -/
theorem s31qk_curve_gap {c : ℝ → ℂ} (hcont : Continuous c) (hper : ∀ t, c (t + 1) = c t)
    (hinj : InjOn c (Ico 0 1)) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ s d : ℝ, η ≤ |d| → |d| ≤ 1 / 2 → ε ≤ ‖c (s + d) - c s‖ := by
  have hp : Function.Periodic c 1 := hper
  set K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ {d : ℝ | η ≤ |d| ∧ |d| ≤ 1 / 2} with hK
  have hKc : IsCompact K := by
    refine isCompact_Icc.prod ?_
    refine (isCompact_Icc (a := (-1 / 2 : ℝ)) (b := 1 / 2)).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_abs).inter (isClosed_le continuous_abs continuous_const)
    · intro d hd
      exact ⟨by linarith [neg_abs_le d, hd.2], by linarith [le_abs_self d, hd.2]⟩
  set F : ℝ × ℝ → ℝ := fun q => ‖c (q.1 + q.2) - c q.1‖ with hF
  have hFc : Continuous F := by fun_prop
  have hFpos : ∀ q ∈ K, 0 < F q := by
    intro q hq
    refine norm_pos_iff.2 (sub_ne_zero.2 (s31qk_periodic_ne hper hinj ?_ ?_))
    · rw [add_sub_cancel_left]; exact lt_of_lt_of_le hη hq.2.1
    · rw [add_sub_cancel_left]; linarith [hq.2.2]
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, fun s d h1 h2 => ?_⟩
    have : ((0 : ℝ), d) ∈ K := ⟨⟨le_rfl, zero_le_one⟩, h1, h2⟩
    rw [hKe] at this; exact absurd this (Set.notMem_empty _)
  obtain ⟨q₀, hq₀, hmin⟩ := hKc.exists_isMinOn hKne hFc.continuousOn
  refine ⟨F q₀, hFpos q₀ hq₀, fun s d h1 h2 => ?_⟩
  have e1 : c (s + d) = c (Int.fract s + d) := by
    have := (hp.int_mul ⌊s⌋) (Int.fract s + d)
    rw [mul_one, show Int.fract s + d + ⌊s⌋ = s + d by rw [Int.fract]; ring] at this
    exact this
  have e2 : c s = c (Int.fract s) := by
    have := (hp.int_mul ⌊s⌋) (Int.fract s)
    rw [mul_one, Int.fract_add_floor] at this
    exact this
  have hmem : (Int.fract s, d) ∈ K :=
    ⟨⟨Int.fract_nonneg s, (Int.fract_lt_one s).le⟩, h1, h2⟩
  have := hmin hmem
  simp only [hF] at this
  rw [e1, e2]
  exact this

/-- **Uniform tangent discs.**  For a smooth regular `1`-periodic simple closed curve there is `ρ₀ > 0` such that
for every parameter `s`, every unit normal `e` (`e ⊥ c'(s)`) and every `ρ ≤ ρ₀`, the open disc of radius `ρ` centred
at `c s + ρ e` misses the curve. -/
theorem s31qk_tangent_disc {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0)
    (hper : ∀ t, c (t + 1) = c t) (hinj : InjOn c (Ico 0 1)) :
    ∃ ρ₀ > 0, ∀ s : ℝ, ∀ e : ℂ, ‖e‖ = 1 → (e * conj (deriv c s)).re = 0 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∀ t : ℝ, ρ ≤ ‖c t - (c s + ρ * e)‖ := by
  have hp : Function.Periodic c 1 := hper
  obtain ⟨δ, M, hδ, hM, hlow, hup, htay⟩ := s31qk_curve_bounds hc hc' hper
  set η : ℝ := min (1 / 2) (δ ^ 2 / (4 * M ^ 2)) with hη
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  obtain ⟨ε, hε, hgap⟩ := s31qk_curve_gap hc.continuous hper hinj hη0
  refine ⟨min (ε / 2) (δ ^ 2 / (4 * M)), lt_min (by positivity) (by positivity), ?_⟩
  intro s e he hperp ρ hρ hρ₀ t
  have hρε : ρ ≤ ε / 2 := hρ₀.trans (min_le_left _ _)
  have hρM : ρ ≤ δ ^ 2 / (4 * M) := hρ₀.trans (min_le_right _ _)
  -- reduce `t` to `s + d` with `|d| ≤ 1/2`
  set k : ℤ := round (t - s) with hk
  set d : ℝ := t - s - k with hd
  have hd2 : |d| ≤ 1 / 2 := by simpa [hd] using abs_sub_round (t - s)
  have hct : c t = c (s + d) := by
    have := (hp.int_mul k) (s + d)
    rw [mul_one, show s + d + k = t by rw [hd]; ring] at this
    exact this
  rw [hct]
  by_cases hdη : η ≤ |d|
  · have h := hgap s d hdη hd2
    have : ‖c (s + d) - c s‖ ≤ ‖c (s + d) - (c s + ρ * e)‖ + ‖(ρ : ℂ) * e‖ := by
      calc ‖c (s + d) - c s‖ = ‖(c (s + d) - (c s + ρ * e)) + (ρ : ℂ) * e‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] at this
    linarith
  · push Not at hdη
    have hdM : |d| ≤ δ ^ 2 / (4 * M ^ 2) := hdη.le.trans (min_le_right _ _)
    set E : ℂ := c (s + d) - c s - (d : ℂ) * deriv c s with hE
    have hEb : ‖E‖ ≤ M * d ^ 2 := htay s d
    set x : ℂ := (d : ℂ) * deriv c s - (ρ : ℂ) * e with hx
    have hv : c (s + d) - (c s + ρ * e) = x + E := by rw [hx, hE]; ring
    rw [hv]
    -- `‖x‖² = d² |c'|² + ρ²` (orthogonality)
    have horth : (((ρ : ℂ) * e) * conj ((d : ℂ) * deriv c s)).re = 0 := by
      have : ((ρ : ℂ) * e) * conj ((d : ℂ) * deriv c s) = ((ρ * d : ℝ) : ℂ) * (e * conj (deriv c s)) := by
        simp only [map_mul, Complex.conj_ofReal]; push_cast; ring
      rw [this, Complex.re_ofReal_mul, hperp, mul_zero]
    have hx2 : ‖x‖ ^ 2 = d ^ 2 * ‖deriv c s‖ ^ 2 + ρ ^ 2 := by
      rw [hx, norm_sub_sq_real, Complex.inner, horth, norm_mul, norm_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, he, abs_of_pos hρ, mul_pow, sq_abs]
      ring
    have hxn : ‖x‖ ≤ |d| * M + ρ := by
      calc ‖x‖ ≤ ‖(d : ℂ) * deriv c s‖ + ‖(ρ : ℂ) * e‖ := norm_sub_le _ _
        _ = |d| * ‖deriv c s‖ + ρ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, he,
            abs_of_pos hρ, mul_one]
        _ ≤ |d| * M + ρ := by gcongr; exact hup s
    have hinner : -(‖x‖ * ‖E‖) ≤ inner ℝ x E := by
      have := abs_real_inner_le_norm x E
      linarith [neg_abs_le (inner ℝ x E)]
    have hsq : ρ ^ 2 ≤ ‖x + E‖ ^ 2 := by
      rw [norm_add_sq_real, hx2]
      have hδc : δ ^ 2 ≤ ‖deriv c s‖ ^ 2 := by
        have := hlow s; nlinarith
      have hd0 : 0 ≤ |d| := abs_nonneg d
      have hE0 : 0 ≤ ‖E‖ := norm_nonneg _
      have h1 : ‖x‖ * ‖E‖ ≤ (|d| * M + ρ) * (M * d ^ 2) :=
        mul_le_mul hxn hEb hE0 (by positivity)
      have h2 : 2 * M ^ 2 * |d| ≤ δ ^ 2 / 2 := by
        have := hdM; rw [le_div_iff₀ (by positivity)] at this; nlinarith
      have h3 : 2 * M * ρ ≤ δ ^ 2 / 2 := by
        have := hρM; rw [le_div_iff₀ (by positivity)] at this; nlinarith
      have hsum : 2 * M ^ 2 * |d| + 2 * M * ρ ≤ δ ^ 2 := by linarith
      have key : (|d| * M + ρ) * (M * d ^ 2) * 2 ≤ d ^ 2 * δ ^ 2 := by
        calc (|d| * M + ρ) * (M * d ^ 2) * 2 = d ^ 2 * (2 * M ^ 2 * |d| + 2 * M * ρ) := by ring
          _ ≤ d ^ 2 * δ ^ 2 := mul_le_mul_of_nonneg_left hsum (sq_nonneg d)
      have hδd : d ^ 2 * δ ^ 2 ≤ d ^ 2 * ‖deriv c s‖ ^ 2 := mul_le_mul_of_nonneg_left hδc (sq_nonneg d)
      linarith [sq_nonneg ‖E‖]
    exact (pow_le_pow_iff_left₀ hρ.le (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)).1 hsq

/-- The range of a `1`-periodic curve is its image of `[0, 1)`. -/
theorem s31qk_range_eq {c : ℝ → ℂ} (hper : ∀ t, c (t + 1) = c t) : range c = c '' Ico 0 1 := by
  have hp : Function.Periodic c 1 := hper
  apply Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    obtain ⟨y, hy, hty⟩ := hp.exists_mem_Ico₀ one_pos t
    exact ⟨y, hy, hty.symm⟩
  · exact image_subset_range _ _

/-- **Nearest point** on a smooth periodic curve: the distance from `ζ` is attained at some `s`, and there
`ζ - c s` is normal to the curve. -/
theorem s31qk_nearest {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hper : ∀ t, c (t + 1) = c t) (ζ : ℂ) :
    ∃ s : ℝ, (∀ t, ‖ζ - c s‖ ≤ ‖ζ - c t‖) ∧ ((ζ - c s) * conj (deriv c s)).re = 0 := by
  have hp : Function.Periodic (fun t => ‖ζ - c t‖) 1 := fun t => by simp only [hper t]
  obtain ⟨a, -, -, ha⟩ := s31qk_periodic_bounds (by fun_prop : Continuous fun t => ‖ζ - c t‖) hp
  refine ⟨a, ha, ?_⟩
  have hd : HasDerivAt (fun t => ζ - c t) (-deriv c a) a := by
    simpa using ((hc.differentiable (by simp)).differentiableAt (x := a)).hasDerivAt.const_sub ζ
  have hmin : IsLocalMin (fun t => ‖ζ - c t‖ ^ 2) a :=
    Filter.Eventually.of_forall fun t => pow_le_pow_left₀ (norm_nonneg _) (ha t) 2
  have h0 := hmin.hasDerivAt_eq_zero hd.norm_sq
  rw [Complex.inner] at h0
  have : ((-deriv c a) * conj (ζ - c a)).re = -((ζ - c a) * conj (deriv c a)).re := by
    rw [← Complex.conj_re ((ζ - c a) * conj (deriv c a))]
    simp only [map_mul, Complex.conj_conj, neg_mul, Complex.neg_re]
    ring_nf
  linarith

/-- A preconnected set missing the frontier of an open set `A` and meeting the exterior `(closure A)ᶜ` lies in it. -/
theorem s31qk_subset_exterior {A S : Set ℂ} (hA : IsOpen A) (hS : IsPreconnected S)
    (hF : Disjoint S (frontier A)) {y : ℂ} (hyS : y ∈ S) (hy : y ∉ closure A) : S ⊆ (closure A)ᶜ := by
  have hcov : S ⊆ (closure A)ᶜ ∪ A := by
    intro z hz
    by_cases hzA : z ∈ A
    · exact Or.inr hzA
    · left
      intro hzc
      exact Set.disjoint_left.1 hF hz ⟨hzc, by rwa [hA.interior_eq]⟩
  exact hS.subset_left_of_subset_union isClosed_closure.isOpen_compl hA
    (Set.disjoint_left.2 fun z hz hzA => hz (subset_closure hzA)) hcov ⟨y, hyS, hy⟩

/-- **Exterior tangent disc at the nearest point.**  Let `A` be open with `frontier A = range c` for a smooth regular
periodic simple closed curve `c`, and `ζ ∉ closure A`.  With `s` a nearest parameter, `d = |ζ - c s|` and
`e = (ζ - c s)/d`, the discs of radius `ρ ≤ ρ₀` centred at `c s + ρ e` lie in `(closure A)ᶜ`. -/
theorem s31qk_exterior_disc {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0)
    (hper : ∀ t, c (t + 1) = c t) (hinj : InjOn c (Ico 0 1)) {A : Set ℂ} (hA : IsOpen A)
    (hfr : frontier A = range c) :
    ∃ ρ₀ > 0, ∀ ζ : ℂ, ζ ∉ closure A → ∃ s : ℝ, 0 < ‖ζ - c s‖ ∧ (∀ t, ‖ζ - c s‖ ≤ ‖ζ - c t‖) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
        ball (c s + ρ * ((ζ - c s) / (‖ζ - c s‖ : ℂ))) ρ ⊆ (closure A)ᶜ ∧
        ∀ t, ρ ≤ ‖c t - (c s + ρ * ((ζ - c s) / (‖ζ - c s‖ : ℂ)))‖ := by
  obtain ⟨ρ₀, hρ₀, htd⟩ := s31qk_tangent_disc hc hc' hper hinj
  refine ⟨ρ₀, hρ₀, fun ζ hζ => ?_⟩
  obtain ⟨s, hmin, hperp⟩ := s31qk_nearest hc hper ζ
  have hfrc : frontier A ⊆ closure A := frontier_subset_closure
  have hd0 : 0 < ‖ζ - c s‖ := by
    refine norm_pos_iff.2 (sub_ne_zero.2 fun h => hζ (hfrc ?_))
    rw [hfr, h]; exact mem_range_self s
  set d : ℝ := ‖ζ - c s‖ with hd
  set e : ℂ := (ζ - c s) / (d : ℂ) with he
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd0.ne'
  have hen : ‖e‖ = 1 := by
    rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0, ← hd, div_self hd0.ne']
  have heperp : (e * conj (deriv c s)).re = 0 := by
    rw [he, div_mul_eq_mul_div, Complex.div_ofReal_re, hperp, zero_div]
  have hζe : ζ = c s + (d : ℂ) * e := by rw [he, mul_div_cancel₀ _ hdC]; ring
  refine ⟨s, hd0, hmin, fun ρ hρ hρρ => ⟨?_, htd s e hen heperp ρ hρ hρρ⟩⟩
  -- `ball ζ d` misses the curve and contains `ζ`, so it is exterior
  have hbζ : ball ζ d ⊆ (closure A)ᶜ := by
    refine s31qk_subset_exterior hA (convex_ball ζ d).isPreconnected ?_ (mem_ball_self hd0) hζ
    refine Set.disjoint_left.2 fun z hz hzF => ?_
    rw [hfr] at hzF
    obtain ⟨t, rfl⟩ := hzF
    have := hmin t
    rw [mem_ball, dist_eq_norm, norm_sub_rev] at hz
    linarith
  -- the tangent disc misses the curve and meets `ball ζ d`
  set τ : ℝ := min ρ d with hτ
  have hτ0 : 0 < τ := lt_min hρ hd0
  have hy1 : c s + (τ : ℂ) * e ∈ ball (c s + ρ * e) ρ := by
    rw [mem_ball, dist_eq_norm, show c s + (τ : ℂ) * e - (c s + ρ * e) = ((τ - ρ : ℝ) : ℂ) * e by push_cast; ring,
      norm_mul, hen, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [min_le_left ρ d]
  have hy2 : c s + (τ : ℂ) * e ∈ ball ζ d := by
    rw [mem_ball, dist_eq_norm, hζe, show c s + (τ : ℂ) * e - (c s + d * e) = ((τ - d : ℝ) : ℂ) * e by push_cast; ring,
      norm_mul, hen, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [min_le_right ρ d]
  refine s31qk_subset_exterior hA (convex_ball _ ρ).isPreconnected ?_ hy1 (hbζ hy2)
  refine Set.disjoint_left.2 fun z hz hzF => ?_
  rw [hfr] at hzF
  obtain ⟨t, rfl⟩ := hzF
  have := htd s e hen heperp ρ hρ hρρ t
  rw [mem_ball, dist_eq_norm] at hz
  linarith

/-- The open upper half disc `{|z| < r, Im z > 0}` is open. -/
theorem s31qk_isOpen_upper (r : ℝ) : IsOpen {z : ℂ | ‖z‖ < r ∧ 0 < z.im} :=
  (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const continuous_im)

/-- **The harmonic function `Im ∘ κ⁻¹`.**  For `κ` holomorphic and injective on the open upper half disc `B⁺`, the
function `U = Im ∘ κ⁻¹` is harmonic and positive on `κ(B⁺)` and `U (κ z) = Im z`. -/
theorem s31qk_inverse_im {r : ℝ} {κ : ℂ → ℂ} (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hinj : InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im}) (hopen : IsOpen (κ '' {z : ℂ | ‖z‖ < r ∧ 0 < z.im})) :
    InnerProductSpace.HarmonicOnNhd
        (fun ζ => (Function.invFunOn κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} ζ).im)
        (κ '' {z : ℂ | ‖z‖ < r ∧ 0 < z.im}) ∧
      (∀ ζ ∈ κ '' {z : ℂ | ‖z‖ < r ∧ 0 < z.im},
        0 < (Function.invFunOn κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} ζ).im) ∧
      ∀ z ∈ {z : ℂ | ‖z‖ < r ∧ 0 < z.im}, (Function.invFunOn κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} (κ z)).im = z.im := by
  set B : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 < z.im} with hB
  have hconf : IsConformalOnto κ B (κ '' B) := ⟨hhol, hinj, rfl⟩
  have hsymm := hconf.symm (s31qk_isOpen_upper r)
  refine ⟨fun ζ hζ => ?_, fun ζ hζ => ?_, fun z hz => by rw [hinj.leftInvOn_invFunOn hz]⟩
  · exact (hsymm.1.analyticAt (hopen.mem_nhds hζ)).harmonicAt_im
  · rw [← hB] at hsymm
    have : Function.invFunOn κ B ζ ∈ B := by
      have h := mem_image_of_mem (Function.invFunOn κ B) hζ
      rwa [hsymm.2.2] at h
    exact this.2

/-- **The comparison step of (B).**  At a point `t` of the segment, `κ w` lies within `C · Im w` of the boundary
curve for `w` near `t` (Harnack's inequality for `Im ∘ κ⁻¹` on an exterior tangent disc at the nearest point). -/
theorem s31qk_dist_le_im
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
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ w : ℂ, ‖w - t‖ < δ → ‖w‖ < r → 0 < w.im →
      ∃ p ∈ frontier Jd, ‖κ w - p‖ ≤ C * w.im := by
  have hJo : IsOpen Jd := hJd.1
  have hfr : frontier Jd = range c := by rw [s31qk_range_eq hper, hcf]
  set B : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 < z.im} with hB
  set Bc : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} with hBc
  obtain ⟨V, hVo, hVeq⟩ := hlocal
  have hBBc : B ⊆ Bc := fun z hz => ⟨hz.1, hz.2.le⟩
  -- `κ(B⁺) = V ∩ (closure Jd)ᶜ`, open
  have hclos : closure Jd = Jd ∪ frontier Jd := by
    rw [frontier, hJo.interior_eq, union_sdiff_cancel subset_closure]
  have himg : κ '' B = V ∩ (closure Jd)ᶜ := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have h1 : κ z ∈ V ∩ Jdᶜ := hVeq ▸ mem_image_of_mem κ (hBBc hz)
      exact ⟨h1.1, hup hz⟩
    · rintro ζ ⟨hζV, hζc⟩
      have hζJ : ζ ∉ Jd := fun h => hζc (subset_closure h)
      obtain ⟨z, hz, rfl⟩ : ζ ∈ κ '' Bc := by rw [hVeq]; exact ⟨hζV, hζJ⟩
      rcases hz.2.lt_or_eq with h | h
      · exact ⟨z, ⟨hz.1, h⟩, rfl⟩
      · exact absurd (frontier_subset_closure (hreal ⟨hz.1, h.symm⟩)) hζc
  have himgo : IsOpen (κ '' B) := by rw [himg]; exact hVo.inter isClosed_closure.isOpen_compl
  obtain ⟨hUh, hUpos, hUκ⟩ := s31qk_inverse_im hhol (hκinj.mono hBBc) himgo
  set U : ℂ → ℝ := fun ζ => (Function.invFunOn κ B ζ).im with hU
  -- the base point
  have htmem : (t : ℂ) ∈ Bc := ⟨by rwa [Complex.norm_real, Real.norm_eq_abs], by simp⟩
  have hp₀F : κ t ∈ frontier Jd := hreal ⟨by rwa [Complex.norm_real, Real.norm_eq_abs], by simp⟩
  have hp₀V : κ t ∈ V := (hVeq ▸ mem_image_of_mem κ htmem : κ t ∈ V ∩ Jdᶜ).1
  obtain ⟨ρ₁, hρ₁, hρ₁V⟩ := Metric.isOpen_iff.1 hVo _ hp₀V
  obtain ⟨ρ₀, hρ₀, hext⟩ := s31qk_exterior_disc hc hc' hper hinj hJo hfr
  set ρ : ℝ := min ρ₀ (ρ₁ / 4) with hρ
  have hρ0 : 0 < ρ := lt_min hρ₀ (by positivity)
  have hρρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρρ₁ : ρ ≤ ρ₁ / 4 := min_le_right _ _
  -- the compact set of centres
  set K₀ : Set ℂ := closedBall (κ t) (2 * ρ) ∩ {ζ | ∀ q ∈ frontier Jd, ρ ≤ ‖ζ - q‖} ∩ Jdᶜ with hK₀
  have hK₀c : IsCompact K₀ := by
    refine ((isCompact_closedBall _ _).inter_right ?_).inter_right hJo.isClosed_compl
    simp only [ofPred_forall]
    exact isClosed_iInter fun q => isClosed_iInter fun _ => isClosed_le continuous_const (by fun_prop)
  have hK₀sub : K₀ ⊆ κ '' B := by
    intro ζ hζ
    rw [himg]
    refine ⟨hρ₁V ?_, ?_⟩
    · rw [mem_ball]; have := hζ.1.1; rw [mem_closedBall] at this; linarith
    · rw [hclos]
      rintro (h | h)
      · exact hζ.2 h
      · have := hζ.1.2 ζ h; rw [sub_self, norm_zero] at this; linarith
  obtain ⟨m, hm, hmK⟩ : ∃ m : ℝ, 0 < m ∧ ∀ ζ ∈ K₀, m ≤ U ζ := by
    rcases K₀.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun ζ hζ => by rw [he] at hζ; exact absurd hζ (Set.notMem_empty _)⟩
    obtain ⟨ζ₀, hζ₀, hmin⟩ := hK₀c.exists_isMinOn hne (hUh.continuousOn.mono hK₀sub)
    exact ⟨U ζ₀, hUpos ζ₀ (hK₀sub hζ₀), fun ζ hζ => hmin hζ⟩
  -- continuity of `κ` at `t`
  obtain ⟨δ, hδ, hδκ⟩ := Metric.continuousWithinAt_iff.1 (hcont (t : ℂ) htmem) (ρ / 2) (by positivity)
  refine ⟨4 * ρ / m, δ, by positivity, hδ, fun w hwt hwr hwi => ?_⟩
  have hwB : w ∈ B := ⟨hwr, hwi⟩
  have hζ : κ w ∉ closure Jd := hup hwB
  have hζp : ‖κ w - κ t‖ < ρ / 2 := by
    have := hδκ (hBBc hwB) (by rwa [dist_eq_norm]); rwa [dist_eq_norm] at this
  obtain ⟨s, hd0, hmin, hdisc⟩ := hext (κ w) hζ
  obtain ⟨hD, hDF⟩ := hdisc ρ hρ0 hρρ₀
  set d : ℝ := ‖κ w - c s‖ with hd
  set e : ℂ := (κ w - c s) / (d : ℂ) with he
  set b : ℂ := c s + ρ * e with hb
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd0.ne'
  have hen : ‖e‖ = 1 := by
    rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0, ← hd, div_self hd0.ne']
  -- `d < ρ/2`: compare with `κ t = c t'`
  have hdρ : d < ρ / 2 := by
    obtain ⟨t', ht'⟩ : κ t ∈ range c := hfr ▸ hp₀F
    have := hmin t'
    rw [← ht'] at hζp
    linarith
  have hζe : κ w = c s + (d : ℂ) * e := by rw [he, mul_div_cancel₀ _ hdC]; ring
  -- the disc `ball b ρ` lies in `κ(B⁺)`
  have hbp : ‖b - κ t‖ < 2 * ρ := by
    have h1 : b - κ t = (ρ : ℂ) * e - (d : ℂ) * e + (κ w - κ t) := by rw [hb, hζe]; ring
    rw [h1]
    calc _ ≤ ‖(ρ : ℂ) * e - (d : ℂ) * e‖ + ‖κ w - κ t‖ := norm_add_le _ _
      _ = (ρ - d) + ‖κ w - κ t‖ := by
          rw [← sub_mul, norm_mul, hen, mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith)]
      _ < 2 * ρ := by linarith
  have hDsub : ball b ρ ⊆ κ '' B := by
    intro z hz
    rw [himg]
    refine ⟨hρ₁V ?_, hD hz⟩
    rw [mem_ball, dist_eq_norm] at hz ⊢
    calc ‖z - κ t‖ ≤ ‖z - b‖ + ‖b - κ t‖ := by
          rw [show z - κ t = (z - b) + (b - κ t) by ring]; exact norm_add_le _ _
      _ < ρ + 2 * ρ := by linarith
      _ ≤ ρ₁ := by linarith
  have hbK : b ∈ K₀ := by
    refine ⟨⟨?_, fun q hq => ?_⟩, fun hbJ => ?_⟩
    · rw [mem_closedBall, dist_eq_norm]; linarith
    · rw [hfr] at hq
      obtain ⟨t'', rfl⟩ := hq
      have := hDF t''
      rw [norm_sub_rev]; exact this
    · exact hD (mem_ball_self hρ0) (subset_closure hbJ)
  -- Harnack on `closedBall b (ρ - d/2)`
  set R' : ℝ := ρ - d / 2 with hR'
  have hR'0 : 0 < R' := by linarith
  have hζb : ‖κ w - b‖ = ρ - d := by
    rw [hζe, hb, show c s + (d : ℂ) * e - (c s + ρ * e) = ((d - ρ : ℝ) : ℂ) * e by push_cast; ring, norm_mul, hen,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  have hclb : closedBall b R' ⊆ κ '' B := (closedBall_subset_ball (by linarith)).trans hDsub
  have hharn := s31qk_harnack hR'0 (fun x hx => hUh x (hclb hx))
    (fun z hz => (hUpos z (hclb (sphere_subset_closedBall hz))).le)
    (show κ w ∈ ball b R' by rw [mem_ball, dist_eq_norm, hζb]; linarith)
  rw [hζb] at hharn
  have hUw : U (κ w) = w.im := hUκ w hwB
  have hUb : m ≤ U b := hmK b hbK
  refine ⟨c s, hfr ▸ mem_range_self s, ?_⟩
  -- `d m / (4ρ) ≤ (d/2)/(2ρ - 3d/2) · U b ≤ U(κ w) = Im w`
  have hcoef : d / (4 * ρ) ≤ (R' - (ρ - d)) / (R' + (ρ - d)) := by
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    rw [hR']; nlinarith
  have hcoef0 : 0 ≤ d / (4 * ρ) := by positivity
  have h1 : d / (4 * ρ) * m ≤ w.im := by
    calc d / (4 * ρ) * m ≤ (R' - (ρ - d)) / (R' + (ρ - d)) * U b :=
          mul_le_mul hcoef hUb hm.le (hcoef0.trans hcoef)
      _ ≤ U (κ w) := hharn
      _ = w.im := hUw
  rw [show ‖κ w - c s‖ = d from rfl]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  nlinarith

/-- **Koebe step of (B).**  For `w` in the upper half disc with `|w| + Im w < r` and a point `p` not in `κ(B⁺)`,
`Im w · |κ'(w)| ≤ 4 |κ w - p|`. -/
theorem s31qk_koebe_step {r : ℝ} {κ : ℂ → ℂ} (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hinj : InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im}) {w p : ℂ} (hw : 0 < w.im) (hwr : ‖w‖ + w.im < r)
    (hp : p ∉ κ '' {z : ℂ | ‖z‖ < r ∧ 0 < z.im}) :
    w.im * ‖deriv κ w‖ ≤ 4 * ‖κ w - p‖ := by
  set B : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 < z.im} with hB
  have hball : ∀ u ∈ ball (0 : ℂ) 1, w + (w.im : ℂ) * u ∈ B := by
    intro u hu
    rw [mem_ball_zero_iff] at hu
    have hn : ‖(w.im : ℂ) * u‖ < w.im := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
      exact mul_lt_of_lt_one_right hw hu
    refine ⟨?_, ?_⟩
    · calc ‖w + (w.im : ℂ) * u‖ ≤ ‖w‖ + ‖(w.im : ℂ) * u‖ := norm_add_le _ _
        _ < r := by linarith
    · have h1 : |((w.im : ℂ) * u).im| ≤ ‖(w.im : ℂ) * u‖ := Complex.abs_im_le_norm _
      rw [Complex.add_im]
      linarith [neg_abs_le ((w.im : ℂ) * u).im]
  set ψ : ℂ → ℂ := fun u => κ (w + (w.im : ℂ) * u) - κ w with hψ
  have hwB : w ∈ B := by simpa using hball 0 (mem_ball_self one_pos)
  have hκd : DifferentiableAt ℂ κ w := hhol.differentiableAt ((s31qk_isOpen_upper r).mem_nhds hwB)
  have hψd : DifferentiableOn ℂ ψ (ball 0 1) := by
    intro u hu
    have h1 : DifferentiableAt ℂ κ (w + (w.im : ℂ) * u) :=
      hhol.differentiableAt ((s31qk_isOpen_upper r).mem_nhds (hball u hu))
    exact ((h1.comp u ((differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id))).sub
      (differentiableAt_const _)).differentiableWithinAt
  have hwim0 : (w.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw.ne'
  have hψinj : InjOn ψ (ball 0 1) := by
    intro u hu v hv huv
    have h := hinj (hball u hu) (hball v hv) (sub_left_inj.1 huv)
    have := add_left_cancel h
    exact mul_left_cancel₀ hwim0 this
  have hψ0 : ψ 0 = 0 := by simp [hψ]
  have hq : p - κ w ∉ ψ '' ball 0 1 := by
    rintro ⟨u, hu, hψu⟩
    apply hp
    refine ⟨w + (w.im : ℂ) * u, hball u hu, ?_⟩
    have := congrArg (· + κ w) hψu
    simpa [hψ] using this
  have hk := koebe_quarter_of_not_mem hψd hψinj hψ0 hq
  have hder : deriv ψ 0 = deriv κ w * (w.im : ℂ) := by
    have h1 : HasDerivAt (fun u : ℂ => w + (w.im : ℂ) * u) (w.im : ℂ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (w.im : ℂ)).const_add w
    have h2 : HasDerivAt κ (deriv κ w) (w + (w.im : ℂ) * 0) := by
      rw [mul_zero, add_zero]; exact hκd.hasDerivAt
    exact ((h2.comp 0 h1).sub_const (κ w)).deriv
  rw [hder, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw, norm_sub_rev] at hk
  linarith

/-- **(B): `|κ'|` is bounded near each point of the segment.** -/
theorem s31qk_deriv_bounded
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
    ∃ C δ : ℝ, 0 < δ ∧ ∀ w : ℂ, ‖w - t‖ < δ → ‖w‖ < r → 0 < w.im → ‖deriv κ w‖ ≤ C := by
  obtain ⟨C, δ, hC, hδ, hdist⟩ :=
    s31qk_dist_le_im hJd hc hc' hper hinj hcf hhol hcont hκinj hup hreal hlocal ht
  have hBB : {z : ℂ | ‖z‖ < r ∧ 0 < z.im} ⊆ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} := fun z hz => ⟨hz.1, hz.2.le⟩
  refine ⟨4 * C, min δ ((r - |t|) / 2), lt_min hδ (by linarith), fun w hwt hwr hwi => ?_⟩
  obtain ⟨p, hpF, hp⟩ := hdist w (hwt.trans_le (min_le_left _ _)) hwr hwi
  have hwt' : ‖w - t‖ < (r - |t|) / 2 := hwt.trans_le (min_le_right _ _)
  have hsum : ‖w‖ + w.im < r := by
    have h1 : ‖w‖ ≤ ‖w - t‖ + |t| := by
      calc ‖w‖ = ‖(w - t) + (t : ℂ)‖ := by ring_nf
        _ ≤ ‖w - t‖ + ‖(t : ℂ)‖ := norm_add_le _ _
        _ = ‖w - t‖ + |t| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h2 : w.im ≤ ‖w - t‖ := by
      have := Complex.abs_im_le_norm (w - t)
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
      exact (le_abs_self _).trans this
    linarith
  have hpnot : p ∉ κ '' {z : ℂ | ‖z‖ < r ∧ 0 < z.im} := by
    rintro ⟨z, hz, rfl⟩
    exact hup hz (frontier_subset_closure hpF)
  have hk := s31qk_koebe_step hhol (hκinj.mono hBB) hwi hsum hpnot
  have : w.im * ‖deriv κ w‖ ≤ w.im * (4 * C) := by nlinarith
  exact le_of_mul_le_mul_left this hwi

/-- A disc centred on the real axis is open and symmetric about it. -/
theorem s31qk_isRealSymmetric_ball (x₀ : ℝ) (ε : ℝ) : IsRealSymmetric (ball (x₀ : ℂ) ε) := by
  refine ⟨isOpen_ball, ?_⟩
  show conj '' ball (x₀ : ℂ) ε = ball (x₀ : ℂ) ε
  have key : ∀ z : ℂ, ‖conj z - x₀‖ = ‖z - x₀‖ := fun z => by
    have : conj z - (x₀ : ℂ) = conj (z - x₀) := by rw [map_sub, Complex.conj_ofReal]
    rw [this, Complex.norm_conj]
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_ball, dist_eq_norm] at hz ⊢
    rwa [key]
  · intro hw
    refine ⟨conj w, ?_, Complex.conj_conj w⟩
    rw [mem_ball, dist_eq_norm] at hw ⊢
    rwa [key]

/-- A holomorphic function with identically vanishing imaginary part on a nonempty connected open set is a real
constant there. -/
theorem s31qk_const_of_im_zero {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) (hne : U.Nonempty)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (him : ∀ z ∈ U, (g z).im = 0) :
    ∃ a : ℝ, ∀ z ∈ U, g z = a := by
  rcases (hg.analyticOnNhd hU).is_constant_or_isOpen hUc with ⟨w, hw⟩ | hopen
  · obtain ⟨z₀, hz₀⟩ := hne
    refine ⟨w.re, fun z hz => ?_⟩
    rw [hw z hz]
    apply Complex.ext
    · simp
    · have := him z₀ hz₀; rw [hw z₀ hz₀] at this; simp [this]
  · exfalso
    obtain ⟨z₀, hz₀⟩ := hne
    have ho := hopen U subset_rfl hU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 ho (g z₀) (mem_image_of_mem g hz₀)
    have hmem : g z₀ + (ε / 2 : ℝ) * I ∈ g '' U := hball (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith)
    obtain ⟨z₁, hz₁, hgz₁⟩ := hmem
    have h1 := him z₁ hz₁
    rw [hgz₁] at h1
    simp [him z₀ hz₀] at h1
    linarith

/-- **Schwarz reflection on a disc centred on the real axis**: a holomorphic `f` on the upper half disc whose
imaginary part tends to `0` at every real point of the disc agrees there with an analytic `F` on the whole disc,
real on the real diameter. -/
theorem s31qk_reflect {x₀ : ℝ} {ε : ℝ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (upperPart (ball (x₀ : ℂ) ε)))
    (hbd : ∀ x ∈ realPart (ball (x₀ : ℂ) ε), Tendsto (fun z => (f z).im) (𝓝[upperPart (ball (x₀ : ℂ) ε)] x) (𝓝 0)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball (x₀ : ℂ) ε) ∧ EqOn F f (upperPart (ball (x₀ : ℂ) ε)) ∧
      (∀ z ∈ ball (x₀ : ℂ) ε, z.im = 0 → (F z).im = 0) ∧
      ∀ z ∈ ball (x₀ : ℂ) ε, F (conj z) = conj (F z) := by
  have hΩ := s31qk_isRealSymmetric_ball x₀ ε
  have hUo : IsOpen (upperPart (ball (x₀ : ℂ) ε)) := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hv : InnerProductSpace.HarmonicOnNhd (fun z => (f z).im) (upperPart (ball (x₀ : ℂ) ε)) :=
    fun z hz => (hf.analyticAt (hUo.mem_nhds hz)).harmonicAt_im
  have hvt := schwarz_reflection_harmonic hΩ hv hbd
  obtain ⟨K, hK, hKre⟩ := hvt.exists_analyticOnNhd_ball_re_eq
  -- `F₀ = I K` has imaginary part `ṽ`
  set F₀ : ℂ → ℂ := fun z => I * K z with hF₀
  have hF₀im : ∀ z ∈ ball (x₀ : ℂ) ε, (F₀ z).im = reflectExtendOdd (fun z => (f z).im) z := fun z hz => by
    simp only [hF₀, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
    exact hKre hz
  have hF₀a : AnalyticOnNhd ℂ F₀ (ball (x₀ : ℂ) ε) := fun z hz => analyticAt_const.mul (hK z hz)
  -- `f - F₀` is a real constant on the upper half disc
  rcases (upperPart (ball (x₀ : ℂ) ε)).eq_empty_or_nonempty with he | hne
  · -- then `ε ≤ 0` and the disc is empty
    have hb : ball (x₀ : ℂ) ε = ∅ := by
      by_contra hb
      obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.2 hb
      have hε : 0 < ε := lt_of_le_of_lt dist_nonneg hw
      have : (x₀ : ℂ) + (ε / 2 : ℝ) * I ∈ upperPart (ball (x₀ : ℂ) ε) := by
        refine ⟨?_, by simp; positivity⟩
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith
      rw [he] at this; exact this
    have hb' : ∀ z, z ∉ ball (x₀ : ℂ) ε := fun z h => by rw [hb] at h; exact h
    exact ⟨F₀, hF₀a, fun z hz => absurd hz.1 (hb' z), fun z hz _ => absurd hz (hb' z), fun z hz => absurd hz (hb' z)⟩
  have hconv : Convex ℝ (upperPart (ball (x₀ : ℂ) ε)) :=
    (convex_ball _ _).inter (convex_halfSpace_im_gt (r := 0))
  obtain ⟨a, ha⟩ := s31qk_const_of_im_zero hUo hconv.isPreconnected hne
    (g := fun z => f z - F₀ z) (hf.sub (hF₀a.differentiableOn.mono fun z hz => hz.1))
    (fun z hz => by
      rw [Complex.sub_im, hF₀im z hz.1, reflectExtendOdd_of_pos _ hz.2, sub_self])
  set F : ℂ → ℂ := fun z => F₀ z + a with hF
  have hFa : AnalyticOnNhd ℂ F (ball (x₀ : ℂ) ε) := fun z hz => (hF₀a z hz).add analyticAt_const
  have hFim : ∀ z ∈ ball (x₀ : ℂ) ε, (F z).im = reflectExtendOdd (fun z => (f z).im) z := fun z hz => by
    simp only [hF, Complex.add_im, Complex.ofReal_im, add_zero]
    exact hF₀im z hz
  have hreal : ∀ z ∈ ball (x₀ : ℂ) ε, z.im = 0 → (F z).im = 0 := fun z hz hz0 => by
    rw [hFim z hz, reflectExtendOdd_of_eq_zero _ hz0]
  -- symmetry: `F - conj ∘ F ∘ conj` is a real constant on the disc, and vanishes at the centre
  have hconjmem : ∀ z ∈ ball (x₀ : ℂ) ε, conj z ∈ ball (x₀ : ℂ) ε := fun z hz => by
    have : conj z ∈ conjSet (ball (x₀ : ℂ) ε) := mem_image_of_mem _ hz
    rwa [hΩ.conj_eq] at this
  have hHd : DifferentiableOn ℂ (conj ∘ F ∘ conj) (ball (x₀ : ℂ) ε) := fun z hz => by
    have h1 : DifferentiableAt ℂ F (conj z) := (hFa _ (hconjmem z hz)).differentiableAt
    have h2 := h1.conj_conj
    rw [Complex.conj_conj] at h2
    exact h2.differentiableWithinAt
  have hx₀b : (x₀ : ℂ) ∈ ball (x₀ : ℂ) ε := by
    obtain ⟨w, hw⟩ := hne
    exact mem_ball_self (lt_of_le_of_lt dist_nonneg hw.1)
  obtain ⟨b, hb⟩ := s31qk_const_of_im_zero isOpen_ball (convex_ball _ _).isPreconnected ⟨_, hx₀b⟩
    (g := fun z => F z - (conj ∘ F ∘ conj) z) (hFa.differentiableOn.sub hHd)
    (fun z hz => by
      simp only [Function.comp, Complex.sub_im, Complex.conj_im, hFim z hz, hFim _ (hconjmem z hz),
        reflectExtendOdd_conj]
      ring)
  have hb0 : (b : ℂ) = 0 := by
    have := hb _ hx₀b
    simp only [Function.comp, Complex.conj_ofReal] at this
    rw [← this]
    have h0 : (F x₀).im = 0 := hreal _ hx₀b (Complex.ofReal_im x₀)
    apply Complex.ext <;> simp [h0]
  refine ⟨F, hFa, fun z hz => ?_, hreal, fun z hz => ?_⟩
  · show F₀ z + a = f z
    have := ha z hz
    rw [← this]; ring
  · have := hb z hz
    rw [hb0, sub_eq_zero] at this
    simp only [Function.comp] at this
    rw [this, Complex.conj_conj]

/-- The local square root `w ↦ q₀^{1/2} (w/q₀)^{1/2}` squares to `w`. -/
theorem s31qk_sqrt_sq {q₀ : ℂ} (hq : q₀ ≠ 0) (w : ℂ) :
    (q₀ ^ (2⁻¹ : ℂ) * (w / q₀) ^ (2⁻¹ : ℂ)) ^ 2 = w := by
  rw [mul_pow, Complex.cpow_ofNat_inv_pow, Complex.cpow_ofNat_inv_pow, mul_div_cancel₀ _ hq]

/-- Near `q₀`, `w/q₀` lies in the slit plane. -/
theorem s31qk_div_mem_slitPlane {q₀ w : ℂ} (h : ‖w / q₀ - 1‖ < 1) : w / q₀ ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  left
  have h1 := Complex.abs_re_le_norm (w / q₀ - 1)
  rw [Complex.sub_re, Complex.one_re] at h1
  linarith [neg_abs_le ((w / q₀).re - 1)]

/-- A complex number whose square is a positive real is real. -/
theorem s31qk_im_eq_zero_of_sq {w : ℂ} (him : (w ^ 2).im = 0) (hre : 0 < (w ^ 2).re) : w.im = 0 := by
  rw [sq, Complex.mul_im] at him
  rw [sq, Complex.mul_re] at hre
  have hab : w.re * w.im = 0 := by linarith
  rcases mul_eq_zero.1 hab with h | h
  · rw [h] at hre; nlinarith [sq_nonneg w.im]
  · exact h

/-- A complex number whose square is a negative real is purely imaginary. -/
theorem s31qk_re_eq_zero_of_sq {w : ℂ} (him : (w ^ 2).im = 0) (hre : (w ^ 2).re < 0) : w.re = 0 := by
  rw [sq, Complex.mul_im] at him
  rw [sq, Complex.mul_re] at hre
  have hab : w.re * w.im = 0 := by linarith
  rcases mul_eq_zero.1 hab with h | h
  · exact h
  · rw [h] at hre; nlinarith [sq_nonneg w.re]

/-- **Local parameters**: points of a periodic simple closed curve close to `c s₀` have a parameter close to `s₀`. -/
theorem s31qk_curve_window {c : ℝ → ℂ} (hcont : Continuous c) (hper : ∀ t, c (t + 1) = c t)
    (hinj : InjOn c (Ico 0 1)) (s₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ ε' > 0, ∀ t : ℝ, ‖c t - c s₀‖ < ε' → ∃ s : ℝ, |s - s₀| < η ∧ c s = c t := by
  have hp : Function.Periodic c 1 := hper
  set η' : ℝ := min η (1 / 2) with hη'
  have hη'0 : 0 < η' := lt_min hη (by norm_num)
  obtain ⟨ε, hε, hgap⟩ := s31qk_curve_gap hcont hper hinj hη'0
  refine ⟨ε, hε, fun t ht => ?_⟩
  set k : ℤ := round (t - s₀) with hk
  set d : ℝ := t - s₀ - k with hd
  have hd2 : |d| ≤ 1 / 2 := by simpa [hd] using abs_sub_round (t - s₀)
  have hct : c t = c (s₀ + d) := by
    have := (hp.int_mul k) (s₀ + d)
    rw [mul_one, show s₀ + d + k = t by rw [hd]; ring] at this
    exact this
  refine ⟨s₀ + d, ?_, hct.symm⟩
  rw [add_sub_cancel_left]
  by_contra hcon
  push Not at hcon
  have := hgap s₀ d ((min_le_left _ _).trans hcon) hd2
  rw [← hct] at this
  linarith

/-- **Local bi-Lipschitz bound** for a smooth regular periodic curve: `|c(s + d) - c s| ≥ (δ/2)|d|` for small `d`. -/
theorem s31qk_curve_bilip {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0)
    (hper : ∀ t, c (t + 1) = c t) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ (∀ t, ‖deriv c t‖ ≤ M) ∧
      (∀ s d : ℝ, ‖c (s + d) - c s - (d : ℂ) * deriv c s‖ ≤ M * d ^ 2) ∧
      ∀ s d : ℝ, |d| ≤ δ / (2 * M) → δ / 2 * |d| ≤ ‖c (s + d) - c s‖ := by
  obtain ⟨δ, M, hδ, hM, hlow, hup, htay⟩ := s31qk_curve_bounds hc hc' hper
  refine ⟨δ, M, hδ, hM, hup, htay, fun s d hd => ?_⟩
  have h1 : ‖(d : ℂ) * deriv c s‖ ≤ ‖c (s + d) - c s‖ + ‖c (s + d) - c s - (d : ℂ) * deriv c s‖ := by
    calc ‖(d : ℂ) * deriv c s‖ = ‖(c (s + d) - c s) - (c (s + d) - c s - (d : ℂ) * deriv c s)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
  have h2 := htay s d
  have h3 : δ * |d| ≤ |d| * ‖deriv c s‖ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hlow s) (abs_nonneg d)
  have h4 : M * d ^ 2 ≤ δ / 2 * |d| := by
    rw [← sq_abs]
    have : M * |d| ≤ δ / 2 := by
      have := mul_le_mul_of_nonneg_left hd hM.le
      rwa [mul_div_assoc', mul_comm M δ, mul_div_mul_comm, div_self hM.ne', mul_one] at this
    nlinarith [abs_nonneg d]
  linarith

/-- **Telescoping over a uniform partition**: if every step of the uniform partition of `[a, b]` into `N` pieces
changes `φ` by at most `e`, then `|φ b - φ a| ≤ N e`. -/
theorem s31qk_telescope {φ : ℝ → ℝ} {a b e : ℝ} {N : ℕ} (hN : 0 < N)
    (hstep : ∀ k < N, |φ (a + (k + 1) * ((b - a) / N)) - φ (a + k * ((b - a) / N))| ≤ e) :
    |φ b - φ a| ≤ N * e := by
  set h : ℝ := (b - a) / N with hh
  have hb : a + (N : ℕ) * h = b := by
    rw [hh, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hN.ne')]; ring
  have htel : φ b - φ a = ∑ k ∈ Finset.range N, (φ (a + ((k : ℕ) + 1 : ℝ) * h) - φ (a + (k : ℕ) * h)) := by
    have := Finset.sum_range_sub (fun k : ℕ => φ (a + (k : ℝ) * h)) N
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero] at this
    rw [this, hb]
  rw [htel]
  calc |∑ k ∈ Finset.range N, (φ (a + ((k : ℕ) + 1 : ℝ) * h) - φ (a + (k : ℕ) * h))|
      ≤ ∑ k ∈ Finset.range N, |φ (a + ((k : ℕ) + 1 : ℝ) * h) - φ (a + (k : ℕ) * h)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range N, e := Finset.sum_le_sum fun k hk => hstep k (Finset.mem_range.1 hk)
    _ = N * e := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Mean value on a horizontal segment.**  If `f` is complex differentiable at every point of the horizontal
segment `{x + i y : x ∈ [a, b]}` with `|f'| ≤ K` there, then `|f(b + iy) - f(a + iy)| ≤ K (b - a)`. -/
theorem s31qk_horizontal_mvt {f : ℂ → ℂ} {a b y K : ℝ} (hab : a ≤ b)
    (hd : ∀ x ∈ Icc a b, DifferentiableAt ℂ f (x + y * I)) (hK : ∀ x ∈ Icc a b, ‖deriv f (x + y * I)‖ ≤ K) :
    ‖f (b + y * I) - f (a + y * I)‖ ≤ K * (b - a) := by
  set g : ℝ → ℂ := fun x => f (x + y * I) with hg
  have hgd : ∀ x ∈ Icc a b, HasDerivAt g (deriv f (x + y * I)) x := fun x hx => by
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) + y * I) 1 x := by
      simpa using (hasDerivAt_id (x : ℝ)).ofReal_comp.add_const ((y : ℂ) * I)
    have h2 := (hd x hx).hasDerivAt.comp x h1
    rw [mul_one] at h2
    exact h2
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (C := K)
    (fun x hx => (hgd x hx).hasDerivWithinAt) (fun x hx => hK x (Ico_subset_Icc_self hx)) b (right_mem_Icc.2 hab)
  simpa [hg] using this

/-- **The axis of `r c'`**: if `w² ` is real and within `|A₀|` of the real number `A₀ ≠ 0`, then `w` lies on the axis
`λ ℝ`, `λ = 1` for `A₀ > 0` and `λ = i` for `A₀ < 0`, i.e. `Im (conj λ · w) = 0`. -/
theorem s31qk_axis {w : ℂ} {A₀ : ℝ} (hA₀ : A₀ ≠ 0) (him : (w ^ 2).im = 0) (hclose : ‖w ^ 2 - A₀‖ < |A₀|) :
    (conj (if 0 < A₀ then (1 : ℂ) else I) * w).im = 0 := by
  have hre : |(w ^ 2).re - A₀| < |A₀| := by
    have := Complex.abs_re_le_norm (w ^ 2 - A₀)
    rw [Complex.sub_re, Complex.ofReal_re] at this
    linarith
  by_cases hpos : 0 < A₀
  · rw [if_pos hpos, map_one, one_mul]
    rw [abs_of_pos hpos] at hre
    exact s31qk_im_eq_zero_of_sq him (by linarith [neg_abs_le ((w ^ 2).re - A₀)])
  · rw [if_neg hpos, Complex.conj_I]
    have hneg : A₀ < 0 := lt_of_le_of_ne (not_lt.1 hpos) hA₀
    rw [abs_of_neg hneg] at hre
    have h := s31qk_re_eq_zero_of_sq him (by linarith [le_abs_self ((w ^ 2).re - A₀)])
    simp [Complex.mul_im, h]

/-- The closed half disc `{|z - x₀| ≤ ε, Im z ≥ 0}` is compact. -/
theorem s31qk_isCompact_halfdisc (x₀ ε : ℝ) : IsCompact {z : ℂ | ‖z - x₀‖ ≤ ε ∧ 0 ≤ z.im} := by
  refine (isCompact_closedBall (x₀ : ℂ) ε).of_isClosed_subset ?_ fun z hz => ?_
  · exact (isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).inter
      (isClosed_le continuous_const continuous_im)
  · rw [mem_closedBall, dist_eq_norm]; exact hz.1

/-- Arithmetic of the key estimate. -/
theorem s31qk_key_arith {θ ε C R M' e₁ e₂ e₃ L : ℝ} {N : ℕ} (hθ : 0 < θ) (hC0 : 0 ≤ C) (hR0 : 0 ≤ R)
    (hM'0 : 0 ≤ M') (hN : 0 < (N : ℝ)) (hL0 : 0 ≤ L) (hLε : L ≤ ε) (he₁ : e₁ * (ε * C + 1) = θ / 4)
    (he₁0 : 0 ≤ e₁) (he₂ : e₂ * (ε * C + 1) = θ / 4) (he₂0 : 0 ≤ e₂) (he₃ : (N : ℝ) * (2 * R * e₃) ≤ θ / 4)
    (hNM : M' * ε ^ 2 / N ≤ θ / 4) :
    (N : ℝ) * (e₁ * C * (L / N) + M' * (L / N) ^ 2 + e₂ * C * (L / N) + 2 * R * e₃) ≤ θ := by
  have _hR := hR0
  have hNh : (N : ℝ) * (L / N) = L := mul_div_cancel₀ _ hN.ne'
  have h1 : (N : ℝ) * (e₁ * C * (L / N)) = e₁ * (C * L) := by
    rw [show (N : ℝ) * (e₁ * C * (L / N)) = e₁ * C * ((N : ℝ) * (L / N)) by ring, hNh]; ring
  have h2 : (N : ℝ) * (M' * (L / N) ^ 2) = M' * L ^ 2 / N := by field_simp
  have h3 : (N : ℝ) * (e₂ * C * (L / N)) = e₂ * (C * L) := by
    rw [show (N : ℝ) * (e₂ * C * (L / N)) = e₂ * C * ((N : ℝ) * (L / N)) by ring, hNh]; ring
  have hCL : C * L ≤ ε * C + 1 := by nlinarith
  have hb1 : e₁ * (C * L) ≤ θ / 4 := he₁ ▸ mul_le_mul_of_nonneg_left hCL he₁0
  have hb3 : e₂ * (C * L) ≤ θ / 4 := he₂ ▸ mul_le_mul_of_nonneg_left hCL he₂0
  have hb2 : M' * L ^ 2 / N ≤ θ / 4 :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hLε 2) hM'0) hN.le).trans hNM
  rw [mul_add, mul_add, mul_add, h1, h2, h3]
  linarith

/-- **The key estimate** (abstract form).  On the half disc `{|z - x₀| < ε, Im z > 0}` let `G' = ρ κ'` with `|κ'| ≤ C`,
`|ρ| ≤ R`, `ρ` and `κ` continuous up to the diameter, and let the boundary chords satisfy
`|Im (λ̄ ρ(a) (κ b - κ a))| ≤ M' (b - a)²`.  Then `Im (λ̄ (G(b + iy) - G(a + iy)))` tends to `0` as `y → 0`, uniformly
for `a, b` in the middle half of the diameter. -/
theorem s31qk_key_estimate {x₀ ε R C M' : ℝ} {lam : ℂ} {ρ κ G : ℂ → ℂ} (hε : 0 < ε) (hC0 : 0 ≤ C)
    (hR0 : 0 ≤ R) (hM'0 : 0 ≤ M')
    (hρc : ContinuousOn ρ {z : ℂ | ‖z - x₀‖ ≤ ε ∧ 0 ≤ z.im})
    (hκc : ContinuousOn κ {z : ℂ | ‖z - x₀‖ ≤ ε ∧ 0 ≤ z.im})
    (hG : ∀ z : ℂ, ‖z - x₀‖ < ε → 0 < z.im → HasDerivAt G (ρ z * deriv κ z) z)
    (hκd : ∀ z : ℂ, ‖z - x₀‖ < ε → 0 < z.im → DifferentiableAt ℂ κ z)
    (hC : ∀ z : ℂ, ‖z - x₀‖ < ε → 0 < z.im → ‖deriv κ z‖ ≤ C)
    (hR : ∀ z : ℂ, ‖z - x₀‖ ≤ ε → 0 ≤ z.im → ‖ρ z‖ ≤ R)
    (hchord : ∀ a b : ℝ, |a - x₀| ≤ ε → |b - x₀| ≤ ε → |(conj lam * (ρ a * (κ b - κ a))).im| ≤ M' * (b - a) ^ 2)
    (hlam : ‖lam‖ = 1) :
    ∀ θ > 0, ∃ y₀ > 0, ∀ y : ℝ, 0 < y → y < y₀ → ∀ a b : ℝ, |a - x₀| ≤ ε / 2 → |b - x₀| ≤ ε / 2 →
      |(conj lam * (G (b + y * I) - G (a + y * I))).im| ≤ θ := by
  intro θ hθ
  set K : Set ℂ := {z : ℂ | ‖z - x₀‖ ≤ ε ∧ 0 ≤ z.im} with hK
  have hKc : IsCompact K := s31qk_isCompact_halfdisc x₀ ε
  have hρu := Metric.uniformContinuousOn_iff.1 (hKc.uniformContinuousOn_of_continuous hρc)
  have hκu := Metric.uniformContinuousOn_iff.1 (hKc.uniformContinuousOn_of_continuous hκc)
  -- the tolerances
  set e₁ : ℝ := θ / (4 * (ε * C + 1)) with he₁
  have he₁0 : 0 < e₁ := by positivity
  obtain ⟨d₁, hd₁, hρ₁⟩ := hρu e₁ he₁0
  -- the number of pieces
  obtain ⟨N, hN⟩ := exists_nat_gt (ε / d₁ + M' * ε ^ 2 * 4 / θ + 1)
  have hN0 : 0 < N := by
    have : (0 : ℝ) < N := lt_trans (by positivity) hN
    exact_mod_cast this
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hNd : ε / N < d₁ := by
    rw [div_lt_iff₀ hNpos]
    have h1 : ε / d₁ < N := by linarith [show 0 ≤ M' * ε ^ 2 * 4 / θ by positivity]
    rw [div_lt_iff₀ hd₁] at h1
    linarith
  have hNM : M' * ε ^ 2 / N ≤ θ / 4 := by
    rw [div_le_iff₀ hNpos]
    have h1 : M' * ε ^ 2 * 4 / θ < N := by linarith [show 0 ≤ ε / d₁ by positivity]
    rw [div_lt_iff₀ hθ] at h1
    nlinarith
  set e₂ : ℝ := θ / (4 * (ε * C + 1)) with he₂
  have he₂0 : 0 < e₂ := by positivity
  obtain ⟨d₂, hd₂, hρ₂⟩ := hρu e₂ he₂0
  set e₃ : ℝ := θ / (8 * N * (R + 1)) with he₃
  have he₃0 : 0 < e₃ := by positivity
  obtain ⟨d₃, hd₃, hκ₃⟩ := hκu e₃ he₃0
  refine ⟨min (min d₂ d₃) (ε / 2), lt_min (lt_min hd₂ hd₃) (by positivity), fun y hy hyy a b ha hb => ?_⟩
  have hyd₂ : y < d₂ := hyy.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hyd₃ : y < d₃ := hyy.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hyε : y < ε / 2 := hyy.trans_le (min_le_right _ _)
  -- membership facts
  have hnormxy : ∀ x : ℝ, ‖((x : ℂ) + y * I) - x₀‖ ≤ |x - x₀| + y := fun x => by
    calc ‖((x : ℂ) + y * I) - x₀‖ = ‖((x - x₀ : ℝ) : ℂ) + (y : ℂ) * I‖ := by push_cast; ring_nf
      _ ≤ ‖((x - x₀ : ℝ) : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
      _ = |x - x₀| + y := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hy]
  have himxy : ∀ x : ℝ, ((x : ℂ) + y * I).im = y := fun x => by simp
  -- WLOG `a ≤ b`
  wlog hab : a ≤ b generalizing a b
  · have := this b a hb ha (le_of_not_ge hab)
    rw [show G (a + y * I) - G (b + y * I) = -(G (b + y * I) - G (a + y * I)) by ring, mul_neg, Complex.neg_im,
      abs_neg] at this
    exact this
  -- the one-step bound on `[α, β] ⊆ [a, b]`
  have hstep : ∀ α β : ℝ, a ≤ α → α ≤ β → β ≤ b → β - α ≤ ε / N →
      |(conj lam * (G (β + y * I) - G (α + y * I))).im| ≤
        e₁ * C * (β - α) + M' * (β - α) ^ 2 + e₂ * C * (β - α) + 2 * R * e₃ := by
    intro α β haα hαβ hβb hβα
    have hxmem : ∀ x ∈ Icc α β, ‖((x : ℂ) + y * I) - x₀‖ < ε ∧ 0 < ((x : ℂ) + y * I).im := fun x hx => by
      have : |x - x₀| ≤ ε / 2 := by
        rw [abs_le] at ha hb ⊢; constructor <;> linarith [hx.1, hx.2]
      refine ⟨(hnormxy x).trans_lt (by linarith), by rw [himxy]; exact hy⟩
    have hKxy : ∀ x ∈ Icc α β, ((x : ℂ) + y * I) ∈ K := fun x hx =>
      ⟨(hxmem x hx).1.le, (hxmem x hx).2.le⟩
    have hα : α ∈ Icc α β := left_mem_Icc.2 hαβ
    have hβ : β ∈ Icc α β := right_mem_Icc.2 hαβ
    -- (i) linearization at height `y`
    have hlin : ‖(G (β + y * I) - G (α + y * I)) - ρ (α + y * I) * (κ (β + y * I) - κ (α + y * I))‖ ≤
        e₁ * C * (β - α) := by
      set H : ℂ → ℂ := fun z => G z - ρ (α + y * I) * κ z with hH
      have hHd : ∀ x ∈ Icc α β, HasDerivAt H ((ρ ((x : ℂ) + y * I) - ρ (α + y * I)) * deriv κ ((x : ℂ) + y * I))
          ((x : ℂ) + y * I) := fun x hx => by
        have h1 := hG _ (hxmem x hx).1 (hxmem x hx).2
        have h2 := ((hκd _ (hxmem x hx).1 (hxmem x hx).2).hasDerivAt).const_mul (ρ (α + y * I))
        have := h1.sub h2
        rw [show ρ ((x : ℂ) + y * I) * deriv κ ((x : ℂ) + y * I) - ρ (α + y * I) * deriv κ ((x : ℂ) + y * I) =
          (ρ ((x : ℂ) + y * I) - ρ (α + y * I)) * deriv κ ((x : ℂ) + y * I) by ring] at this
        exact this
      have hbound : ∀ x ∈ Icc α β, ‖deriv H ((x : ℂ) + y * I)‖ ≤ e₁ * C := fun x hx => by
        rw [(hHd x hx).deriv, norm_mul]
        refine mul_le_mul ?_ (hC _ (hxmem x hx).1 (hxmem x hx).2) (norm_nonneg _) he₁0.le
        have h := hρ₁ _ (hKxy x hx) _ (hKxy α hα) (by
          rw [dist_eq_norm, show ((x : ℂ) + y * I) - (α + y * I) = ((x - α : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
          calc x - α ≤ β - α := by linarith [hx.2]
            _ ≤ ε / N := hβα
            _ < d₁ := hNd)
        rw [dist_eq_norm] at h
        exact h.le
      have := s31qk_horizontal_mvt hαβ (fun x hx => (hHd x hx).differentiableAt) hbound
      simp only [hH] at this
      calc _ = ‖G (β + y * I) - ρ (α + y * I) * κ (β + y * I) - (G (α + y * I) - ρ (α + y * I) * κ (α + y * I))‖ := by
            ring_nf
        _ ≤ e₁ * C * (β - α) := this
    -- (ii) the horizontal chord of `κ` at height `y`
    have hκy : ‖κ (β + y * I) - κ (α + y * I)‖ ≤ C * (β - α) :=
      s31qk_horizontal_mvt hαβ (fun x hx => hκd _ (hxmem x hx).1 (hxmem x hx).2)
        (fun x hx => hC _ (hxmem x hx).1 (hxmem x hx).2)
    -- (iii) comparison with the diameter
    have hαK : (α : ℂ) ∈ K := ⟨by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_le] at ha hb ⊢; constructor <;> linarith, by simp⟩
    have hβK : (β : ℂ) ∈ K := ⟨by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_le] at ha hb ⊢; constructor <;> linarith, by simp⟩
    have hdy : ∀ x : ℝ, dist ((x : ℂ) + y * I) (x : ℂ) = y := fun x => by
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hy]
    have hρα : ‖ρ (α + y * I) - ρ α‖ ≤ e₂ := by
      have := hρ₂ _ (hKxy α hα) _ hαK (by rw [hdy]; exact hyd₂)
      rw [dist_eq_norm] at this; exact this.le
    have hκα : ‖κ (α + y * I) - κ α‖ ≤ e₃ := by
      have := hκ₃ _ (hKxy α hα) _ hαK (by rw [hdy]; exact hyd₃)
      rw [dist_eq_norm] at this; exact this.le
    have hκβ : ‖κ (β + y * I) - κ β‖ ≤ e₃ := by
      have := hκ₃ _ (hKxy β hβ) _ hβK (by rw [hdy]; exact hyd₃)
      rw [dist_eq_norm] at this; exact this.le
    have hch := hchord α β (by rw [abs_le] at ha hb ⊢; constructor <;> linarith)
      (by rw [abs_le] at ha hb ⊢; constructor <;> linarith)
    have hRα : ‖ρ α‖ ≤ R := hR _ hαK.1 hαK.2
    have hcomp : ‖ρ (α + y * I) * (κ (β + y * I) - κ (α + y * I)) - ρ α * (κ β - κ α)‖ ≤
        e₂ * (C * (β - α)) + R * (2 * e₃) := by
      have e : ρ (α + y * I) * (κ (β + y * I) - κ (α + y * I)) - ρ α * (κ β - κ α) =
          (ρ (α + y * I) - ρ α) * (κ (β + y * I) - κ (α + y * I)) +
            ρ α * ((κ (β + y * I) - κ β) - (κ (α + y * I) - κ α)) := by ring
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]; exact mul_le_mul hρα hκy (norm_nonneg _) he₂0.le
      · rw [norm_mul]
        refine mul_le_mul hRα ((norm_sub_le _ _).trans (by linarith)) (norm_nonneg _) hR0
    -- assemble the step
    have hlam' : ‖conj lam‖ = 1 := by rw [Complex.norm_conj, hlam]
    have himle : ∀ w : ℂ, |(conj lam * w).im| ≤ ‖w‖ := fun w => by
      refine (Complex.abs_im_le_norm _).trans ?_
      rw [norm_mul, hlam', one_mul]
    have e2 : conj lam * (G (β + y * I) - G (α + y * I)) =
        conj lam * ((G (β + y * I) - G (α + y * I)) - ρ (α + y * I) * (κ (β + y * I) - κ (α + y * I))) +
        conj lam * (ρ (α + y * I) * (κ (β + y * I) - κ (α + y * I)) - ρ α * (κ β - κ α)) +
        conj lam * (ρ α * (κ β - κ α)) := by ring
    rw [e2, Complex.add_im, Complex.add_im]
    have t1 := himle ((G (β + y * I) - G (α + y * I)) - ρ (α + y * I) * (κ (β + y * I) - κ (α + y * I)))
    have t2 := himle (ρ (α + y * I) * (κ (β + y * I) - κ (α + y * I)) - ρ α * (κ β - κ α))
    calc _ ≤ |(conj lam * ((G (β + y * I) - G (α + y * I)) - ρ (α + y * I) * (κ (β + y * I) - κ (α + y * I)))).im| +
          |(conj lam * (ρ (α + y * I) * (κ (β + y * I) - κ (α + y * I)) - ρ α * (κ β - κ α))).im| +
          |(conj lam * (ρ α * (κ β - κ α))).im| := abs_add_three _ _ _
      _ ≤ e₁ * C * (β - α) + (e₂ * (C * (β - α)) + R * (2 * e₃)) + M' * (β - α) ^ 2 := by
          linarith [t1.trans hlin, t2.trans hcomp, hch]
      _ = _ := by ring
  -- sum over the uniform partition
  set φ : ℝ → ℝ := fun x => (conj lam * G (x + y * I)).im with hφ
  have hba : b - a ≤ ε := by rw [abs_le] at ha hb; linarith
  have hh : (b - a) / N ≤ ε / N := div_le_div_of_nonneg_right hba hNpos.le
  have hh0 : 0 ≤ (b - a) / N := div_nonneg (by linarith) hNpos.le
  have htel := s31qk_telescope (φ := φ) (a := a) (b := b) (N := N) hN0
    (e := e₁ * C * ((b - a) / N) + M' * ((b - a) / N) ^ 2 + e₂ * C * ((b - a) / N) + 2 * R * e₃) (by
      intro k hk
      have hk' : ((k : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have h1 := hstep (a + k * ((b - a) / N)) (a + (k + 1) * ((b - a) / N))
        (le_add_of_nonneg_right (mul_nonneg hk0 hh0))
        (by have := mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ k + 1 by linarith) hh0; linarith)
        (by
          have : (k + 1 : ℝ) * ((b - a) / N) ≤ N * ((b - a) / N) := mul_le_mul_of_nonneg_right hk' hh0
          rw [mul_div_cancel₀ _ hNpos.ne'] at this; linarith)
        (by rw [show a + ((k : ℝ) + 1) * ((b - a) / N) - (a + k * ((b - a) / N)) = (b - a) / N by ring]; exact hh)
      have e : a + ((k : ℝ) + 1) * ((b - a) / N) - (a + k * ((b - a) / N)) = (b - a) / N := by ring
      rw [e, mul_sub, Complex.sub_im] at h1
      exact h1)
  have he₁e : e₁ * (ε * C + 1) = θ / 4 := by
    rw [he₁, div_mul_eq_mul_div, mul_div_mul_right _ _ (by positivity : (ε * C + 1) ≠ 0)]
  have he₂e : e₂ * (ε * C + 1) = θ / 4 := by
    rw [he₂, div_mul_eq_mul_div, mul_div_mul_right _ _ (by positivity : (ε * C + 1) ≠ 0)]
  have he₃e : (N : ℝ) * (2 * R * e₃) ≤ θ / 4 := by
    have e : (N : ℝ) * (2 * R * e₃) = θ / 4 * (R / (R + 1)) := by rw [he₃]; field_simp; ring
    rw [e]
    have : R / (R + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    exact mul_le_of_le_one_right (by positivity) this
  have hfinal := s31qk_key_arith hθ hC0 hR0 hM'0 hNpos (by linarith : 0 ≤ b - a) hba he₁e he₁0.le he₂e he₂0.le
    he₃e hNM
  have := htel.trans hfinal
  rw [mul_sub, Complex.sub_im]
  exact this

/-- **The boundary constant.**  If `G` is `L`-Lipschitz on the half disc `{|z - x₀| < ε, Im z > 0}` and
`Im (λ̄ (G(b + iy) - G(a + iy))) → 0` uniformly as in `s31qk_key_estimate`, then `Im (λ̄ G)` has one and the same limit
`C₀` at every point of the middle half of the diameter. -/
theorem s31qk_boundary_const {x₀ ε L : ℝ} {lam : ℂ} {G g : ℂ → ℂ} (hε : 0 < ε) (hL : 0 ≤ L)
    (hG : ∀ z : ℂ, ‖z - x₀‖ < ε → 0 < z.im → HasDerivAt G (g z) z)
    (hg : ∀ z : ℂ, ‖z - x₀‖ < ε → 0 < z.im → ‖g z‖ ≤ L) (hlam : ‖lam‖ = 1)
    (hKE : ∀ θ > 0, ∃ y₀ > 0, ∀ y : ℝ, 0 < y → y < y₀ → ∀ a b : ℝ, |a - x₀| ≤ ε / 2 → |b - x₀| ≤ ε / 2 →
      |(conj lam * (G (b + y * I) - G (a + y * I))).im| ≤ θ) :
    ∃ C₀ : ℝ, ∀ x : ℝ, |x - x₀| < ε / 2 →
      Tendsto (fun z => (conj lam * G z).im) (𝓝[{z : ℂ | ‖z - x₀‖ < ε / 2 ∧ 0 < z.im}] (x : ℂ)) (𝓝 C₀) := by
  set U : Set ℂ := {z : ℂ | ‖z - x₀‖ < ε ∧ 0 < z.im} with hU
  have hUc : Convex ℝ U := by
    have h1 : Convex ℝ {z : ℂ | ‖z - x₀‖ < ε} := by
      have : {z : ℂ | ‖z - x₀‖ < ε} = ball (x₀ : ℂ) ε := by ext z; simp [dist_eq_norm]
      rw [this]; exact convex_ball _ _
    exact h1.inter (convex_halfSpace_im_gt (r := 0))
  -- `G` is `L`-Lipschitz on `U`
  have hlip : ∀ z ∈ U, ∀ w ∈ U, ‖G z - G w‖ ≤ L * ‖z - w‖ := fun z hz w hw =>
    hUc.norm_image_sub_le_of_norm_hasDerivWithin_le (f := G) (f' := g)
      (fun u hu => (hG u hu.1 hu.2).hasDerivWithinAt) (fun u hu => hg u hu.1 hu.2) hw hz
  have hlam' : ‖conj lam‖ = 1 := by rw [Complex.norm_conj, hlam]
  set φ : ℂ → ℝ := fun z => (conj lam * G z).im with hφ
  have hφlip : ∀ z ∈ U, ∀ w ∈ U, |φ z - φ w| ≤ L * ‖z - w‖ := fun z hz w hw => by
    simp only [hφ, ← Complex.sub_im, ← mul_sub]
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_mul, hlam', one_mul]
    exact hlip z hz w hw
  -- the points `x₀ + i y`
  have hvmem : ∀ y : ℝ, 0 < y → y < ε → ((x₀ : ℂ) + y * I) ∈ U := fun y hy hyε => by
    refine ⟨?_, by simpa using hy⟩
    rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
    exact hyε
  have hvdist : ∀ y y' : ℝ, ‖((x₀ : ℂ) + y * I) - (x₀ + y' * I)‖ = |y - y'| := fun y y' => by
    rw [show ((x₀ : ℂ) + y * I) - (x₀ + y' * I) = ((y - y' : ℝ) : ℂ) * I by push_cast; ring, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs]
  -- the sequence `u n = φ (x₀ + i yₙ)`, `yₙ = ε / (2 (n + 2))`
  set yy : ℕ → ℝ := fun n => ε / (2 * ((n : ℝ) + 2)) with hyy
  have hyy0 : ∀ n, 0 < yy n := fun n => by simp only [hyy]; positivity
  have hyyε : ∀ n, yy n < ε := fun n => by
    simp only [hyy]
    rw [div_lt_iff₀ (by positivity)]
    have : (1 : ℝ) < 2 * ((n : ℝ) + 2) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    nlinarith
  set u : ℕ → ℝ := fun n => φ ((x₀ : ℂ) + yy n * I) with hu
  have hucauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro e he
    obtain ⟨N, hN⟩ := exists_nat_gt (L * ε / e)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have h1 := hφlip _ (hvmem _ (hyy0 n) (hyyε n)) _ (hvmem _ (hyy0 N) (hyyε N))
    rw [hvdist] at h1
    have h2 : yy n ≤ yy N := by
      simp only [hyy]
      apply div_le_div_of_nonneg_left hε.le (by positivity)
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h3 : |yy n - yy N| ≤ yy N := by
      rw [abs_le]; constructor <;> linarith [hyy0 n]
    have h4 : L * yy N < e := by
      simp only [hyy]
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ he] at hN
      have : (N : ℝ) < 2 * ((N : ℝ) + 2) := by have := Nat.cast_nonneg (α := ℝ) N; linarith
      nlinarith
    calc |u n - u N| ≤ L * |yy n - yy N| := h1
      _ ≤ L * yy N := mul_le_mul_of_nonneg_left h3 hL
      _ < e := h4
  obtain ⟨C₀, hC₀⟩ := cauchySeq_tendsto_of_complete hucauchy
  refine ⟨C₀, fun x hx => ?_⟩
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro e he
  obtain ⟨y₀, hy₀, hKE'⟩ := hKE (e / 3) (by positivity)
  -- choose `n` with `u n` close to `C₀` and `L yₙ` small
  have hev1 : ∀ᶠ n in atTop, dist (u n) C₀ < e / 3 := (Metric.tendsto_nhds.1 hC₀) _ (by positivity)
  have hyyt : Tendsto yy atTop (𝓝 0) := by
    simp only [hyy]
    refine tendsto_const_nhds.div_atTop ?_
    exact Tendsto.const_mul_atTop (by norm_num) (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hev2 : ∀ᶠ n in atTop, L * yy n < e / 6 := by
    have := (hyyt.const_mul L)
    rw [mul_zero] at this
    exact (this.eventually (gt_mem_nhds (by positivity)))
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  set d : ℝ := min (min y₀ (ε / 2 - |x - x₀|)) (e / (6 * (L + 1))) with hd
  have hd0 : 0 < d := lt_min (lt_min hy₀ (by linarith)) (by positivity)
  refine ⟨d, hd0, fun z hz hzx => ?_⟩
  have hzd : ‖z - x‖ < d := by rwa [dist_eq_norm] at hzx
  have hzim : z.im < d := by
    have := Complex.abs_im_le_norm (z - x)
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans_lt (this.trans_lt hzd)
  have hzre : |z.re - x₀| ≤ ε / 2 := by
    have h1 := Complex.abs_re_le_norm (z - x)
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    have h2 : |z.re - x₀| ≤ |z.re - x| + |x - x₀| := by
      rw [show z.re - x₀ = (z.re - x) + (x - x₀) by ring]; exact abs_add_le _ _
    have h3 : d ≤ ε / 2 - |x - x₀| := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hzeq : z = (z.re : ℂ) + z.im * I := (Complex.re_add_im z).symm
  -- the three pieces
  have hp1 : |φ z - φ ((x₀ : ℂ) + z.im * I)| ≤ e / 3 := by
    have := hKE' z.im hz.2 (hzim.trans_le ((min_le_left _ _).trans (min_le_left _ _))) x₀ z.re
      (by simp; linarith) hzre
    rw [← hzeq] at this
    simp only [hφ, ← Complex.sub_im, ← mul_sub]
    exact this
  have hzU : z.im < ε := by
    have h3 : d ≤ ε / 2 - |x - x₀| := (min_le_left _ _).trans (min_le_right _ _)
    linarith [abs_nonneg (x - x₀)]
  have hp2 : |φ ((x₀ : ℂ) + z.im * I) - u n| ≤ e / 3 := by
    have h1 := hφlip _ (hvmem _ hz.2 hzU) _ (hvmem _ (hyy0 n) (hyyε n))
    rw [hvdist] at h1
    have h2 : |z.im - yy n| ≤ z.im + yy n := by
      rw [abs_le]; constructor <;> linarith [hyy0 n, hz.2]
    have h3 : L * z.im ≤ e / 6 := by
      have : z.im ≤ e / (6 * (L + 1)) := hzim.le.trans (min_le_right _ _)
      calc L * z.im ≤ (L + 1) * (e / (6 * (L + 1))) := mul_le_mul (by linarith) this hz.2.le (by linarith)
        _ = e / 6 := by field_simp
    calc |φ ((x₀ : ℂ) + z.im * I) - u n| ≤ L * |z.im - yy n| := h1
      _ ≤ L * (z.im + yy n) := mul_le_mul_of_nonneg_left h2 hL
      _ ≤ e / 3 := by linarith
  rw [Real.dist_eq] at hn1 ⊢
  calc |φ z - C₀| = |(φ z - φ ((x₀ : ℂ) + z.im * I)) + (φ ((x₀ : ℂ) + z.im * I) - u n) + (u n - C₀)| := by ring_nf
    _ ≤ |φ z - φ ((x₀ : ℂ) + z.im * I)| + |φ ((x₀ : ℂ) + z.im * I) - u n| + |u n - C₀| := abs_add_three _ _ _
    _ < e := by linarith

/-- `κ` is `C`-Lipschitz on the diameter when `|κ'| ≤ C` on the half disc and `κ` is continuous up to the diameter. -/
theorem s31qk_lip_diameter {x₀ ε C : ℝ} {κ : ℂ → ℂ}
    (hκc : ContinuousOn κ {z : ℂ | ‖z - x₀‖ ≤ ε ∧ 0 ≤ z.im})
    (hκd : ∀ z : ℂ, ‖z - x₀‖ < ε → 0 < z.im → DifferentiableAt ℂ κ z)
    (hC : ∀ z : ℂ, ‖z - x₀‖ < ε → 0 < z.im → ‖deriv κ z‖ ≤ C) :
    ∀ a b : ℝ, |a - x₀| < ε → |b - x₀| < ε → ‖κ b - κ a‖ ≤ C * |b - a| := by
  intro a b ha hb
  wlog hab : a ≤ b generalizing a b
  · rw [norm_sub_rev, abs_sub_comm]; exact this b a hb ha (le_of_not_ge hab)
  set m : ℝ := ε - max |a - x₀| |b - x₀| with hm
  have hm0 : 0 < m := by rw [hm]; exact sub_pos.2 (max_lt ha hb)
  have hnorm : ∀ x : ℝ, ∀ y : ℝ, 0 ≤ y → ‖((x : ℂ) + y * I) - x₀‖ ≤ |x - x₀| + y := fun x y hy => by
    calc ‖((x : ℂ) + y * I) - x₀‖ = ‖((x - x₀ : ℝ) : ℂ) + (y : ℂ) * I‖ := by push_cast; ring_nf
      _ ≤ ‖((x - x₀ : ℝ) : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
      _ = |x - x₀| + y := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hy]
  -- the bound at height `y ∈ (0, m)`
  have hev : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), ‖κ ((b : ℂ) + (y : ℂ) * I) - κ ((a : ℂ) + (y : ℂ) * I)‖ ≤ C * |b - a| := by
    filter_upwards [Ioo_mem_nhdsGT hm0] with y hy
    rw [abs_of_nonneg (by linarith)]
    refine s31qk_horizontal_mvt hab (fun x hx => hκd _ ?_ ?_) (fun x hx => hC _ ?_ ?_)
    all_goals first
      | (have hx' : |x - x₀| ≤ max |a - x₀| |b - x₀| := by
            rw [abs_le]; constructor
            · linarith [hx.1, neg_abs_le (a - x₀), le_max_left |a - x₀| |b - x₀|]
            · linarith [hx.2, le_abs_self (b - x₀), le_max_right |a - x₀| |b - x₀|]
         exact (hnorm x y hy.1.le).trans_lt (by linarith [hy.2]))
      | simpa using hy.1
  -- the limit `y → 0`
  have hlim : ∀ x : ℝ, |x - x₀| < ε → Tendsto (fun y : ℝ => κ ((x : ℂ) + y * I)) (𝓝[>] 0) (𝓝 (κ x)) := by
    intro x hx
    have hxK : (x : ℂ) ∈ {z : ℂ | ‖z - x₀‖ ≤ ε ∧ 0 ≤ z.im} :=
      ⟨by rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hx.le, by simp⟩
    refine (hκc _ hxK).tendsto.comp ?_
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Continuous fun y : ℝ => (x : ℂ) + y * I := by fun_prop
      have h := (this.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using h
    · have hm' : 0 < ε - |x - x₀| := by linarith
      filter_upwards [Ioo_mem_nhdsGT hm'] with y hy
      exact ⟨(hnorm x y hy.1.le).trans (by linarith [hy.2]), by simpa using hy.1.le⟩
  have ht := ((hlim b hb).sub (hlim a ha)).norm
  exact le_of_tendsto ht hev

/-- **The step where `Qc ∘ κ ≠ 0`** (proof of `s31qk_nonzero_case`, stated separately). -/
theorem s31qk_nonzero_case'
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
    {Qc : ℂ → ℂ}
    (hQd : DifferentiableOn ℂ Qc (κ '' {z : ℂ | ‖z‖ < r ∧ 0 < z.im}))
    (hQc : ContinuousOn Qc (κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im}))
    (hQr : ∀ (γ : ℝ → ℂ) (a b : ℝ), ContDiffOn ℝ 1 γ (Icc a b) → γ '' Icc a b ⊆ frontier Jd →
      ∀ t ∈ Ioo a b, (Qc (γ t) * deriv γ t ^ 2).im = 0)
    {x₀ : ℝ} (hx₀ : |x₀| < r) (hq : Qc (κ x₀) ≠ 0) :
    Tendsto (fun z => (Qc (κ z) * deriv κ z ^ 2).im) (𝓝[{z : ℂ | ‖z‖ < r ∧ 0 < z.im}] (x₀ : ℂ)) (𝓝 0) := by
  set B : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 < z.im} with hB
  set Bc : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} with hBc
  have hBo : IsOpen B := s31qk_isOpen_upper r
  have hfr : frontier Jd = range c := by rw [s31qk_range_eq hper, hcf]
  have hx₀m : (x₀ : ℂ) ∈ Bc := ⟨by rwa [Complex.norm_real, Real.norm_eq_abs], by simp⟩
  set q₀ : ℂ := Qc (κ x₀) with hq₀
  have hq₀n : 0 < ‖q₀‖ := norm_pos_iff.2 hq
  obtain ⟨s₀, hs₀⟩ : κ x₀ ∈ range c :=
    hfr ▸ hreal ⟨by rwa [Complex.norm_real, Real.norm_eq_abs], by simp⟩
  obtain ⟨δc, M, hδc, hM, hupc, htay, hbil⟩ := s31qk_curve_bilip hc hc' hper
  -- the reality clause along `c`
  have hQs : ∀ s : ℝ, (Qc (c s) * deriv c s ^ 2).im = 0 := fun s =>
    hQr c (s - 1) (s + 1) ((hc.of_le (by simp)).contDiffOn)
      (by rintro _ ⟨t, -, rfl⟩; rw [hfr]; exact mem_range_self t) s ⟨by linarith, by linarith⟩
  set A₀ : ℝ := (q₀ * deriv c s₀ ^ 2).re with hA₀
  have hA₀eq : q₀ * deriv c s₀ ^ 2 = (A₀ : ℂ) := by
    apply Complex.ext
    · simp [hA₀]
    · have := hQs s₀; rw [hs₀] at this; simpa using this
  have hA₀ne : A₀ ≠ 0 := by
    intro h0
    rw [h0, Complex.ofReal_zero] at hA₀eq
    exact mul_ne_zero hq (pow_ne_zero 2 (hc' s₀)) hA₀eq
  have hA₀pos : 0 < |A₀| := abs_pos.2 hA₀ne
  set lam : ℂ := if 0 < A₀ then 1 else I with hlamdef
  have hlam : ‖lam‖ = 1 := by
    by_cases h : 0 < A₀
    · simp [hlamdef, h]
    · simp [hlamdef, h]
  -- continuity of `c'²` at `s₀`
  have hc1 : Continuous (deriv c) := hc.continuous_deriv (by simp)
  have hcsq : ContinuousAt (fun s => deriv c s ^ 2) s₀ := (hc1.pow 2).continuousAt
  obtain ⟨η₂, hη₂, hη₂c⟩ := Metric.continuousAt_iff.1 hcsq (|A₀| / (2 * (‖q₀‖ + 1))) (by positivity)
  set η : ℝ := min η₂ (δc / (4 * M)) with hη
  have hη0 : 0 < η := lt_min hη₂ (by positivity)
  obtain ⟨εw, hεw, hwin⟩ := s31qk_curve_window hc.continuous hper hinj s₀ hη0
  -- continuity of `κ` and `Qc ∘ κ` at `x₀` within `Bc`
  set θ₁ : ℝ := min (|A₀| / (2 * (M ^ 2 + 1))) (‖q₀‖ / 2) with hθ₁
  have hθ₁0 : 0 < θ₁ := lt_min (by positivity) (by positivity)
  have hQκc : ContinuousOn (fun z => Qc (κ z)) Bc := hQc.comp hcont (mapsTo_image κ Bc)
  obtain ⟨ε₁, hε₁, hε₁c⟩ := Metric.continuousWithinAt_iff.1 (hQκc _ hx₀m) θ₁ hθ₁0
  obtain ⟨ε₂, hε₂, hε₂c⟩ := Metric.continuousWithinAt_iff.1 (hcont _ hx₀m) εw hεw
  -- the derivative bound (B)
  obtain ⟨C, δB, hδB, hCb⟩ :=
    s31qk_deriv_bounded hJd hc hc' hper hinj hcf hhol hcont hκinj hup hreal hlocal hx₀
  set ε : ℝ := min (min (ε₁ / 2) (ε₂ / 2)) (min (δB / 2) ((r - |x₀|) / 2)) with hεdef
  have hε0 : 0 < ε := lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by linarith))
  have hεε₁ : ε < ε₁ := by linarith [show ε ≤ ε₁ / 2 from (min_le_left _ _).trans (min_le_left _ _)]
  have hεε₂ : ε < ε₂ := by linarith [show ε ≤ ε₂ / 2 from (min_le_left _ _).trans (min_le_right _ _)]
  have hεδ : ε < δB := by linarith [show ε ≤ δB / 2 from (min_le_right _ _).trans (min_le_left _ _)]
  have hεr : ε ≤ (r - |x₀|) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set K : Set ℂ := {z : ℂ | ‖z - x₀‖ ≤ ε ∧ 0 ≤ z.im} with hK
  have hnz : ∀ z : ℂ, ‖z‖ ≤ |x₀| + ‖z - x₀‖ := fun z => by
    calc ‖z‖ = ‖(x₀ : ℂ) + (z - x₀)‖ := by ring_nf
      _ ≤ ‖(x₀ : ℂ)‖ + ‖z - x₀‖ := norm_add_le _ _
      _ = |x₀| + ‖z - x₀‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hKBc : ∀ z ∈ K, z ∈ Bc := fun z hz => ⟨by linarith [hnz z, hz.1], hz.2⟩
  have hKdist : ∀ z ∈ K, dist z x₀ < ε₁ ∧ dist z x₀ < ε₂ := fun z hz => by
    rw [dist_eq_norm]; exact ⟨by linarith [hz.1], by linarith [hz.1]⟩
  have hQnear : ∀ z ∈ K, ‖Qc (κ z) - q₀‖ < θ₁ := fun z hz => by
    have := hε₁c (hKBc z hz) (hKdist z hz).1; rwa [dist_eq_norm] at this
  have hκnear : ∀ z ∈ K, ‖κ z - κ x₀‖ < εw := fun z hz => by
    have := hε₂c (hKBc z hz) (hKdist z hz).2; rwa [dist_eq_norm] at this
  have hslit : ∀ z ∈ K, Qc (κ z) / q₀ ∈ slitPlane := fun z hz => by
    refine s31qk_div_mem_slitPlane ?_
    rw [show Qc (κ z) / q₀ - 1 = (Qc (κ z) - q₀) / q₀ by field_simp, norm_div, div_lt_one hq₀n]
    exact (hQnear z hz).trans_le ((min_le_right _ _).trans (by linarith))
  -- the local square root `ρ`
  set ρ : ℂ → ℂ := fun z => q₀ ^ (2⁻¹ : ℂ) * (Qc (κ z) / q₀) ^ (2⁻¹ : ℂ) with hρ
  have hρsq : ∀ z, ρ z ^ 2 = Qc (κ z) := fun z => s31qk_sqrt_sq hq _
  have hρc : ContinuousOn ρ K :=
    continuousOn_const.mul (((hQκc.mono hKBc).div_const q₀).cpow_const hslit)
  set R : ℝ := 2 * ‖q₀‖ + 1 with hR
  have hRb : ∀ z ∈ K, ‖ρ z‖ ≤ R := fun z hz => by
    have h1 : ‖ρ z‖ ^ 2 = ‖Qc (κ z)‖ := by rw [← norm_pow, hρsq]
    have h2 : ‖Qc (κ z)‖ ≤ 2 * ‖q₀‖ := by
      have := hQnear z hz
      have h3 : θ₁ ≤ ‖q₀‖ / 2 := min_le_right _ _
      calc ‖Qc (κ z)‖ = ‖(Qc (κ z) - q₀) + q₀‖ := by ring_nf
        _ ≤ ‖Qc (κ z) - q₀‖ + ‖q₀‖ := norm_add_le _ _
        _ ≤ 2 * ‖q₀‖ := by linarith
    nlinarith [norm_nonneg (ρ z)]
  -- the open half disc `U`
  set U : Set ℂ := {z : ℂ | ‖z - x₀‖ < ε ∧ 0 < z.im} with hU
  have hUo : IsOpen U :=
    (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).inter
      (isOpen_lt continuous_const continuous_im)
  have hUK : U ⊆ K := fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hUB : U ⊆ B := fun z hz => ⟨(hKBc z (hUK hz)).1, hz.2⟩
  have hUconv : Convex ℝ U := by
    have h1 : {z : ℂ | ‖z - x₀‖ < ε} = ball (x₀ : ℂ) ε := by ext z; simp [dist_eq_norm]
    have : U = ball (x₀ : ℂ) ε ∩ {z : ℂ | 0 < z.im} := by rw [hU, ← h1]; rfl
    rw [this]; exact (convex_ball _ _).inter (convex_halfSpace_im_gt (r := 0))
  have hUne : U.Nonempty := ⟨(x₀ : ℂ) + (ε / 2 : ℝ) * I, by
    refine ⟨?_, by simp; positivity⟩
    rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith⟩
  have hκdU : ∀ z ∈ U, DifferentiableAt ℂ κ z := fun z hz =>
    hhol.differentiableAt (hBo.mem_nhds (hUB hz))
  have hCU : ∀ z ∈ U, ‖deriv κ z‖ ≤ C := fun z hz => by
    exact hCb z (hz.1.trans hεδ) (hUB hz).1 hz.2
  have hρd : DifferentiableOn ℂ ρ U := by
    have h1 : DifferentiableOn ℂ (fun z => Qc (κ z)) U :=
      hQd.comp (hhol.mono hUB) (fun z hz => mem_image_of_mem κ (hUB hz))
    exact (differentiableOn_const _).mul ((h1.div_const q₀).cpow_const fun z hz => hslit z (hUK hz))
  have hκ'd : DifferentiableOn ℂ (deriv κ) U :=
    ((hhol.analyticOnNhd hBo).deriv.differentiableOn).mono hUB
  -- the natural parameter `G`, a primitive of `S = ρ κ'`
  haveI : ContractibleSpace U := hUconv.contractibleSpace hUne
  obtain ⟨G, hGd, hGder⟩ := RMT.exists_primitive_of_simplyConnected hUo (hUconv.isConnected hUne) (hρd.mul hκ'd)
  have hG : ∀ z : ℂ, ‖z - x₀‖ < ε → 0 < z.im → HasDerivAt G (ρ z * deriv κ z) z := fun z h1 h2 => by
    have hz : z ∈ U := ⟨h1, h2⟩
    have := (hGd.differentiableAt (hUo.mem_nhds hz)).hasDerivAt
    rwa [hGder z hz] at this
  -- κ is Lipschitz on the diameter
  have hκK : ContinuousOn κ K := hcont.mono hKBc
  have hK3 : ∀ z : ℂ, ‖z - x₀‖ ≤ 3 * ε / 2 → 0 ≤ z.im → z ∈ Bc := fun z h1 h2 =>
    ⟨by linarith [hnz z, show 0 < ε from hε0], h2⟩
  have hlipd := s31qk_lip_diameter (ε := 3 * ε / 2) (hcont.mono fun z hz => hK3 z hz.1 hz.2)
    (fun z h1 h2 => hhol.differentiableAt (hBo.mem_nhds ⟨(hK3 z h1.le h2.le).1, h2⟩))
    (fun z h1 h2 => hCb z (by linarith [show ε ≤ δB / 2 from (min_le_right _ _).trans (min_le_left _ _)])
      (hK3 z h1.le h2.le).1 h2)
  -- parameters of diameter points
  have hpar : ∀ a : ℝ, |a - x₀| ≤ ε → ∃ s : ℝ, |s - s₀| < η ∧ c s = κ a := by
    intro a ha
    have haK : (a : ℂ) ∈ K := ⟨by rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact ha, by simp⟩
    obtain ⟨t, ht⟩ : κ a ∈ range c :=
      hfr ▸ hreal ⟨(hKBc _ haK).1, by simp⟩
    obtain ⟨s, hs, hcs⟩ := hwin t (by rw [ht, hs₀]; exact hκnear _ haK)
    exact ⟨s, hs, hcs.trans ht⟩
  -- the chord estimate
  set M' : ℝ := R * M * (2 * C / δc) ^ 2 with hM'
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hCU _ hUne.some_mem)
  have hchord : ∀ a b : ℝ, |a - x₀| ≤ ε → |b - x₀| ≤ ε →
      |(conj lam * (ρ a * (κ b - κ a))).im| ≤ M' * (b - a) ^ 2 := by
    intro a b ha hb
    obtain ⟨sa, hsa, hcsa⟩ := hpar a ha
    obtain ⟨sb, hsb, hcsb⟩ := hpar b hb
    have haK : (a : ℂ) ∈ K := ⟨by rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact ha, by simp⟩
    -- the axis
    have hw : (conj lam * (ρ a * deriv c sa)).im = 0 := by
      refine s31qk_axis hA₀ne ?_ ?_
      · rw [mul_pow, hρsq, ← hcsa]; exact hQs sa
      · have hsa2 : ‖deriv c sa ^ 2 - deriv c s₀ ^ 2‖ < |A₀| / (2 * (‖q₀‖ + 1)) := by
          have := hη₂c (show dist sa s₀ < η₂ by rw [Real.dist_eq]; exact hsa.trans_le (min_le_left _ _))
          rwa [dist_eq_norm] at this
        have hQa : ‖Qc (κ a) - q₀‖ < |A₀| / (2 * (M ^ 2 + 1)) := (hQnear _ haK).trans_le (min_le_left _ _)
        have e : (ρ a * deriv c sa) ^ 2 - (A₀ : ℂ) =
            (Qc (κ a) - q₀) * deriv c sa ^ 2 + q₀ * (deriv c sa ^ 2 - deriv c s₀ ^ 2) := by
          rw [mul_pow, hρsq, ← hA₀eq]; ring
        rw [e]
        have hcs : ‖deriv c sa ^ 2‖ ≤ M ^ 2 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hupc sa) 2
        calc ‖(Qc (κ a) - q₀) * deriv c sa ^ 2 + q₀ * (deriv c sa ^ 2 - deriv c s₀ ^ 2)‖
            ≤ ‖Qc (κ a) - q₀‖ * M ^ 2 + ‖q₀‖ * ‖deriv c sa ^ 2 - deriv c s₀ ^ 2‖ := by
              refine (norm_add_le _ _).trans (add_le_add ?_ (norm_mul _ _).le)
              rw [norm_mul]; exact mul_le_mul_of_nonneg_left hcs (norm_nonneg _)
          _ < |A₀| / (2 * (M ^ 2 + 1)) * (M ^ 2 + 1) + (‖q₀‖ + 1) * (|A₀| / (2 * (‖q₀‖ + 1))) := by
              have h1 : ‖Qc (κ a) - q₀‖ * M ^ 2 ≤ |A₀| / (2 * (M ^ 2 + 1)) * (M ^ 2 + 1) := by
                have : M ^ 2 ≤ M ^ 2 + 1 := by linarith
                exact mul_le_mul hQa.le this (by positivity) (by positivity)
              have h2 : ‖q₀‖ * ‖deriv c sa ^ 2 - deriv c s₀ ^ 2‖ < (‖q₀‖ + 1) * (|A₀| / (2 * (‖q₀‖ + 1))) :=
                lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
                  (mul_lt_mul_of_pos_left hsa2 (by positivity))
              linarith
          _ = |A₀| := by field_simp; ring
    -- parameter difference
    have hds : |sb - sa| ≤ δc / (2 * M) := by
      have h1 : |sb - sa| ≤ |sb - s₀| + |sa - s₀| := by
        rw [show sb - sa = (sb - s₀) - (sa - s₀) by ring]; exact abs_sub _ _
      have h2 : η ≤ δc / (4 * M) := min_le_right _ _
      have h3 : δc / (4 * M) + δc / (4 * M) = δc / (2 * M) := by field_simp; ring
      linarith
    have hbl := hbil sa (sb - sa) hds
    rw [add_sub_cancel, hcsb, hcsa] at hbl
    have hab' : ‖κ b - κ a‖ ≤ C * |b - a| := hlipd a b (by linarith) (by linarith)
    · have hdsb : |sb - sa| ≤ 2 * C / δc * |b - a| := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδc]
        nlinarith [abs_nonneg (sb - sa)]
      -- Taylor
      have ht := htay sa (sb - sa)
      rw [add_sub_cancel, hcsb, hcsa] at ht
      set E : ℂ := κ b - κ a - ((sb - sa : ℝ) : ℂ) * deriv c sa with hE
      have e : conj lam * (ρ a * (κ b - κ a)) =
          ((sb - sa : ℝ) : ℂ) * (conj lam * (ρ a * deriv c sa)) + conj lam * (ρ a * E) := by rw [hE]; ring
      rw [e, Complex.add_im, Complex.im_ofReal_mul, hw, mul_zero, zero_add]
      have hRa : ‖ρ a‖ ≤ R := hRb _ haK
      calc |(conj lam * (ρ a * E)).im| ≤ ‖conj lam * (ρ a * E)‖ := Complex.abs_im_le_norm _
        _ = ‖ρ a‖ * ‖E‖ := by rw [norm_mul, Complex.norm_conj, hlam, one_mul, norm_mul]
        _ ≤ R * (M * (sb - sa) ^ 2) := mul_le_mul hRa ht (norm_nonneg _) (by positivity)
        _ = R * M * |sb - sa| ^ 2 := by rw [sq_abs]; ring
        _ ≤ R * M * (2 * C / δc * |b - a|) ^ 2 := by gcongr
        _ = M' * (b - a) ^ 2 := by rw [hM', mul_pow, sq_abs]; ring
  -- the key estimate and the boundary constant
  have hKE := s31qk_key_estimate hε0 hC0 (by positivity) (by positivity) hρc hκK hG
    (fun z h1 h2 => hκdU z ⟨h1, h2⟩) (fun z h1 h2 => hCU z ⟨h1, h2⟩) (fun z h1 h2 => hRb z ⟨h1, h2⟩) hchord hlam
  obtain ⟨C₀, hC₀⟩ := s31qk_boundary_const hε0 (by positivity : (0 : ℝ) ≤ R * C) hG
    (fun z h1 h2 => by
      rw [norm_mul]; exact mul_le_mul (hRb z ⟨h1.le, h2.le⟩) (hCU z ⟨h1, h2⟩) (norm_nonneg _) (by positivity))
    hlam hKE
  -- reflection of `λ̄ G - i C₀` across the diameter of `ball x₀ (ε/2)`
  have hW : upperPart (ball (x₀ : ℂ) (ε / 2)) = {z : ℂ | ‖z - x₀‖ < ε / 2 ∧ 0 < z.im} := by
    ext z; simp [upperPart, dist_eq_norm]
  have hWU : ∀ z ∈ upperPart (ball (x₀ : ℂ) (ε / 2)), z ∈ U := fun z hz => by
    rw [hW] at hz; exact ⟨by linarith [hz.1], hz.2⟩
  have hfd : DifferentiableOn ℂ (fun z => conj lam * G z - (C₀ : ℂ) * I) (upperPart (ball (x₀ : ℂ) (ε / 2))) :=
    ((differentiableOn_const _).mul (hGd.mono hWU)).sub (differentiableOn_const _)
  have hfbd : ∀ x ∈ realPart (ball (x₀ : ℂ) (ε / 2)),
      Tendsto (fun z => (conj lam * G z - (C₀ : ℂ) * I).im) (𝓝[upperPart (ball (x₀ : ℂ) (ε / 2))] x) (𝓝 0) := by
    intro x hx
    have hxre : x = (x.re : ℂ) := Complex.ext (by simp) (by simp [hx.2])
    have hxd : |x.re - x₀| < ε / 2 := by
      have := hx.1
      rw [mem_ball, dist_eq_norm, hxre, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
      exact this
    have h := (hC₀ x.re hxd).sub_const C₀
    rw [sub_self] at h
    rw [hW, hxre]
    refine h.congr fun z => ?_
    simp
  obtain ⟨F, hFa, hFeq, hFreal, -⟩ := s31qk_reflect hfd hfbd
  -- `G = λ (F + i C₀)`, so `S = G' = λ F'` and `Q = S² = λ² F'²` on the upper half disc
  have hlam2 : conj lam * lam = 1 := by
    rw [mul_comm, Complex.mul_conj', hlam]; simp
  have hGF : ∀ z ∈ upperPart (ball (x₀ : ℂ) (ε / 2)), G z = lam * (F z + (C₀ : ℂ) * I) := fun z hz => by
    rw [hFeq hz]
    simp only
    rw [show lam * (conj lam * G z - ↑C₀ * I + ↑C₀ * I) = (conj lam * lam) * G z by ring, hlam2, one_mul]
  have hWo : IsOpen (upperPart (ball (x₀ : ℂ) (ε / 2))) := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hQF : ∀ z ∈ upperPart (ball (x₀ : ℂ) (ε / 2)), Qc (κ z) * deriv κ z ^ 2 = lam ^ 2 * deriv F z ^ 2 := by
    intro z hz
    have hzU := hWU z hz
    have h1 : deriv G z = ρ z * deriv κ z := (hG z hzU.1 hzU.2).deriv
    have h2 : G =ᶠ[𝓝 z] fun w => lam * (F w + (C₀ : ℂ) * I) :=
      Filter.eventually_of_mem (hWo.mem_nhds hz) fun w hw => hGF w hw
    have hFd : DifferentiableAt ℂ F z := (hFa z hz.1).differentiableAt
    have h3 : deriv G z = lam * deriv F z := by
      rw [h2.deriv_eq]
      have := ((hFd.hasDerivAt.add_const ((C₀ : ℂ) * I)).const_mul lam).deriv
      rw [this]
    rw [← hρsq, show ρ z ^ 2 * deriv κ z ^ 2 = (ρ z * deriv κ z) ^ 2 by ring, ← h1, h3]; ring
  -- `F'(x₀)` is real
  have hx₀b : (x₀ : ℂ) ∈ ball (x₀ : ℂ) (ε / 2) := mem_ball_self (by positivity)
  have hFdx : HasDerivAt F (deriv F x₀) x₀ := (hFa _ hx₀b).differentiableAt.hasDerivAt
  have hreal' : (deriv F x₀).im = 0 := by
    have h1 : HasDerivAt (fun t : ℝ => F t) (deriv F x₀) x₀ := hFdx.comp_ofReal
    have h2 : HasDerivAt (fun t : ℝ => ((F t).re : ℂ)) (((deriv F x₀).re : ℝ) : ℂ) x₀ :=
      hFdx.real_of_complex.ofReal_comp
    have h3 : HasDerivAt (fun t : ℝ => F t) (((deriv F x₀).re : ℝ) : ℂ) x₀ := by
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds (show x₀ - ε / 2 < x₀ by linarith) (show x₀ < x₀ + ε / 2 by linarith)] with t ht
      have hb : (t : ℂ) ∈ ball (x₀ : ℂ) (ε / 2) := by
        rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
        constructor <;> linarith [ht.1, ht.2]
      exact Complex.ext (by simp) (by simp [hFreal _ hb (Complex.ofReal_im t)])
    rw [h1.unique h3, Complex.ofReal_im]
  -- the limit
  have hlimQ : Tendsto (fun z => Qc (κ z) * deriv κ z ^ 2) (𝓝[B] (x₀ : ℂ)) (𝓝 (lam ^ 2 * deriv F x₀ ^ 2)) := by
    have hcont' : ContinuousAt (fun z => lam ^ 2 * deriv F z ^ 2) x₀ :=
      ((((hFa.deriv) _ hx₀b).continuousAt).pow 2).const_mul _
    refine (hcont'.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (x₀ : ℂ) (by positivity : 0 < ε / 2))]
      with z hzB hzb
    exact (hQF z ⟨hzb, hzB.2⟩).symm
  have him0 : (lam ^ 2 * deriv F x₀ ^ 2).im = 0 := by
    have hl : (lam ^ 2).im = 0 := by
      by_cases h : 0 < A₀ <;> simp [hlamdef, h]
    have hd : (deriv F x₀ ^ 2).im = 0 := by rw [sq, Complex.mul_im, hreal']; ring
    rw [Complex.mul_im, hl, hd]; ring
  have := (Complex.continuous_im.tendsto _).comp hlimQ
  rw [him0] at this
  exact this

/-- At a point of the segment where `Qc ∘ κ` vanishes, the pulled-back coefficient tends to `0`: `Qc ∘ κ` is continuous
and `|κ'|` is bounded there (B). -/
theorem s31qk_zero_case
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
    {Qc : ℂ → ℂ} (hQc : ContinuousOn Qc (κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im}))
    {x₀ : ℝ} (hx₀ : |x₀| < r) (hq : Qc (κ x₀) = 0) :
    Tendsto (fun z => Qc (κ z) * deriv κ z ^ 2) (𝓝[{z : ℂ | ‖z‖ < r ∧ 0 < z.im}] (x₀ : ℂ)) (𝓝 0) := by
  obtain ⟨C, δ, hδ, hC⟩ :=
    s31qk_deriv_bounded hJd hc hc' hper hinj hcf hhol hcont hκinj hup hreal hlocal hx₀
  have hx₀m : (x₀ : ℂ) ∈ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} := ⟨by rwa [Complex.norm_real, Real.norm_eq_abs], by simp⟩
  -- `Qc ∘ κ → 0`
  have hQκ : Tendsto (fun z => Qc (κ z)) (𝓝[{z : ℂ | ‖z‖ < r ∧ 0 < z.im}] (x₀ : ℂ)) (𝓝 0) := by
    have h1 : ContinuousWithinAt (fun z => Qc (κ z)) {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} (x₀ : ℂ) :=
      (hQc (κ x₀) (mem_image_of_mem κ hx₀m)).comp (hcont _ hx₀m) (mapsTo_image κ _)
    have h2 := h1.tendsto
    rw [hq] at h2
    exact h2.mono_left (nhdsWithin_mono _ fun z hz => ⟨hz.1, hz.2.le⟩)
  -- `|κ'|² ≤ C²` eventually
  have hev : ∀ᶠ z in 𝓝[{z : ℂ | ‖z‖ < r ∧ 0 < z.im}] (x₀ : ℂ), ‖deriv κ z ^ 2‖ ≤ max C 0 ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (x₀ : ℂ) hδ)] with z hz hzb
    rw [norm_pow]
    have := hC z (by rwa [mem_ball, dist_eq_norm] at hzb) hz.1 hz.2
    exact pow_le_pow_left₀ (norm_nonneg _) (this.trans (le_max_left _ _)) 2
  exact hQκ.zero_mul_isBoundedUnder_le ⟨_, Filter.eventually_map.2 hev⟩

/-- **The local step where `Qc ∘ κ ≠ 0`** (natural parameter): the imaginary part of the pulled-back coefficient
tends to `0` at the segment point `x₀`. -/
theorem s31qk_nonzero_case
    {Jd : Set ℂ} (hJd : IsJordanDomain Jd) (hbd : Bornology.IsBounded Jd)
    {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0) (hper : ∀ t, c (t + 1) = c t)
    (hinj : InjOn c (Ico 0 1)) (hcf : c '' Ico 0 1 = frontier Jd)
    {r : ℝ} {κ : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hcont : ContinuousOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hκinj : InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hup : MapsTo κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} (closure Jd)ᶜ)
    (hreal : MapsTo κ {z : ℂ | ‖z‖ < r ∧ z.im = 0} (frontier Jd))
    (hlocal : ∃ V : Set ℂ, IsOpen V ∧ κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} = V ∩ Jdᶜ)
    {Qc : ℂ → ℂ}
    (hQd : DifferentiableOn ℂ Qc (κ '' {z : ℂ | ‖z‖ < r ∧ 0 < z.im}))
    (hQc : ContinuousOn Qc (κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im}))
    (hQr : ∀ (γ : ℝ → ℂ) (a b : ℝ), ContDiffOn ℝ 1 γ (Icc a b) → γ '' Icc a b ⊆ frontier Jd →
      ∀ t ∈ Ioo a b, (Qc (γ t) * deriv γ t ^ 2).im = 0)
    {x₀ : ℝ} (hx₀ : |x₀| < r) (hq : Qc (κ x₀) ≠ 0) :
    Tendsto (fun z => (Qc (κ z) * deriv κ z ^ 2).im) (𝓝[{z : ℂ | ‖z‖ < r ∧ 0 < z.im}] (x₀ : ℂ)) (𝓝 0) := by
  have _hbd := hbd
  exact s31qk_nonzero_case' hJd hc hc' hper hinj hcf hhol hcont hκinj hup hreal hlocal hQd hQc hQr hx₀ hq

/-- **Reflection across a `C^∞` boundary arc** (the frozen stub `s31qi_reflect_across_arc` of the QD interface). -/
theorem s31qk_reflect_across_arc
    {Jd : Set ℂ} (hJd : IsJordanDomain Jd) (hbd : Bornology.IsBounded Jd)
    {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0) (hper : ∀ t, c (t + 1) = c t)
    (hinj : InjOn c (Ico 0 1)) (hcf : c '' Ico 0 1 = frontier Jd)
    {r : ℝ} (hr : 0 < r) {κ : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hcont : ContinuousOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hκinj : InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hup : MapsTo κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} (closure Jd)ᶜ)
    (hreal : MapsTo κ {z : ℂ | ‖z‖ < r ∧ z.im = 0} (frontier Jd))
    (hlocal : ∃ V : Set ℂ, IsOpen V ∧ κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} = V ∩ Jdᶜ)
    {Qc : ℂ → ℂ}
    (hQd : DifferentiableOn ℂ Qc (κ '' {z : ℂ | ‖z‖ < r ∧ 0 < z.im}))
    (hQc : ContinuousOn Qc (κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im}))
    (hQr : ∀ (γ : ℝ → ℂ) (a b : ℝ), ContDiffOn ℝ 1 γ (Icc a b) → γ '' Icc a b ⊆ frontier Jd →
      ∀ t ∈ Ioo a b, (Qc (γ t) * deriv γ t ^ 2).im = 0) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (ball 0 r) ∧
      (∀ z : ℂ, ‖z‖ < r → G (conj z) = conj (G z)) ∧
      ∀ z : ℂ, ‖z‖ < r → 0 < z.im → G z = Qc (κ z) * deriv κ z ^ 2 := by
  have _hr := hr
  set B : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 < z.im} with hB
  have hball0 : ball (((0 : ℝ)) : ℂ) r = ball 0 r := by rw [Complex.ofReal_zero]
  have hBeq : upperPart (ball (((0 : ℝ)) : ℂ) r) = B := by
    ext z; simp [upperPart, hB, mem_ball, dist_zero_right]
  have hBo : IsOpen B := s31qk_isOpen_upper r
  have hf : DifferentiableOn ℂ (fun z => Qc (κ z) * deriv κ z ^ 2) B := by
    have h1 : DifferentiableOn ℂ (fun z => Qc (κ z)) B := hQd.comp hhol (mapsTo_image κ B)
    have h2 : DifferentiableOn ℂ (deriv κ) B := (hhol.analyticOnNhd hBo).deriv.differentiableOn
    exact h1.mul (h2.pow 2)
  have hbd' : ∀ x ∈ realPart (ball (((0 : ℝ)) : ℂ) r),
      Tendsto (fun z => (Qc (κ z) * deriv κ z ^ 2).im) (𝓝[upperPart (ball (((0 : ℝ)) : ℂ) r)] x) (𝓝 0) := by
    intro x hx
    rw [hBeq]
    have hxre : x = (x.re : ℂ) := Complex.ext (by simp) (by simp [hx.2])
    have hxr : |x.re| < r := by
      have := hx.1
      rw [mem_ball, dist_eq_norm, Complex.ofReal_zero, sub_zero, hxre, Complex.norm_real, Real.norm_eq_abs] at this
      exact this
    rw [hxre]
    by_cases hq : Qc (κ x.re) = 0
    · have h := s31qk_zero_case hJd hc hc' hper hinj hcf hhol hcont hκinj hup hreal hlocal hQc hxr hq
      have := (Complex.continuous_im.tendsto 0).comp h
      rw [Complex.zero_im] at this
      exact this
    · exact s31qk_nonzero_case hJd hbd hc hc' hper hinj hcf hhol hcont hκinj hup hreal hlocal hQd hQc hQr hxr hq
  obtain ⟨F, hFa, hFeq, -, hFsym⟩ := s31qk_reflect (by rw [hBeq]; exact hf) hbd'
  rw [hball0] at hFa hFsym
  refine ⟨F, hFa, fun z hz => hFsym z (mem_ball_zero_iff.2 hz), fun z hz hzi => ?_⟩
  exact hFeq (by rw [hBeq]; exact ⟨hz, hzi⟩)

/-- (A) Reflection of a boundary-real quadratic coefficient across a `C^∞` boundary arc.  `Jd` is a
bounded Jordan domain with `C^∞` regular boundary parametrization `c` (exactly the data of
`IsClosedDiscIn`), `κ` is a homeomorphism of the closed half disc onto a relatively open piece of the
EXTERIOR `Jdᶜ` of `Jd`, conformal in the interior, sending the real segment to `frontier Jd`.  `Qc` is a
holomorphic coefficient on the image of the open half disc, continuous up to the boundary arc and real
along every `C¹` boundary curve in the sense of `IsAdmissibleQD`: `Im (Qc (γ t) * (γ' t)^2) = 0`.
Conclusion: the pulled-back coefficient `Qc (κ z) * (κ' z)^2` extends holomorphically across the
whole real segment, by a function symmetric under conjugation (no bound on or nonvanishing of `κ'` is
asserted). -/
theorem s31qi_reflect_across_arc
    {Jd : Set ℂ} (hJd : IsJordanDomain Jd) (hbd : Bornology.IsBounded Jd)
    {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0) (hper : ∀ t, c (t + 1) = c t)
    (hinj : InjOn c (Ico 0 1)) (hcf : c '' Ico 0 1 = frontier Jd)
    {r : ℝ} (hr : 0 < r) {κ : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hcont : ContinuousOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hκinj : InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hup : MapsTo κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} (closure Jd)ᶜ)
    (hreal : MapsTo κ {z : ℂ | ‖z‖ < r ∧ z.im = 0} (frontier Jd))
    (hlocal : ∃ V : Set ℂ, IsOpen V ∧ κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} = V ∩ Jdᶜ)
    {Qc : ℂ → ℂ}
    (hQd : DifferentiableOn ℂ Qc (κ '' {z : ℂ | ‖z‖ < r ∧ 0 < z.im}))
    (hQc : ContinuousOn Qc (κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im}))
    (hQr : ∀ (γ : ℝ → ℂ) (a b : ℝ), ContDiffOn ℝ 1 γ (Icc a b) → γ '' Icc a b ⊆ frontier Jd →
      ∀ t ∈ Ioo a b, (Qc (γ t) * deriv γ t ^ 2).im = 0) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (ball 0 r) ∧
      (∀ z : ℂ, ‖z‖ < r → G (conj z) = conj (G z)) ∧
      ∀ z : ℂ, ‖z‖ < r → 0 < z.im → G z = Qc (κ z) * deriv κ z ^ 2 := by
  exact s31qk_reflect_across_arc hJd hbd hc hc' hper hinj hcf hr hhol hcont hκinj hup hreal hlocal hQd hQc hQr
end LiZhongQC
