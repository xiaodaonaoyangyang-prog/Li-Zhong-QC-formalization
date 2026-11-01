import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
import LiZhongQC.Lemmas.QDDimension
import LiZhongQC.Lemmas.UniformizedTeichmuller

/-!
# §32 Teichmüller data of surfaces of finite type: the sorry-free helpers (`s82td_`)

Archive module, split off `FiniteTypeTeichSpace` (leader decision R82, 2026-10-16) so that it can be banked
independently of the installed `sorry` in `thm32_3_uniqueness_gnm`/`thm32_4_existence_gnm`.

* the identity theorem for holomorphic quadratic differentials; a homeomorphism carrying two Teichmüller structures
  has the same `k` and proportional initial differentials; a Teichmüller map with `k = 0` is biholomorphic;
* the finite dimension of `Q̃(S₀)` (`s82td_finrank_interior`);
* the realization of an admissible differential and `0 < k < 1` by an admissible Teichmüller map (`s82td_realize`):
  closed case, punctures (pole charts), holes (a new atlas on the closed surface with one hole chart per hole: the
  circle-symmetric solution of the Beltrami equation for the Teichmüller dilatation, on a hole coordinate built from the
  exterior uniformizer).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-! ## Helpers (`s82td_`) -/

/-- Transfer of local vanishing through the transformation law: if `Q x` vanishes near `τ(w)`,
`τ = φ_x ∘ φ_y⁻¹`, then `Q y` vanishes near `w`. -/
theorem s82td_hol_transfer {Q : S₀ → ℂ → ℂ} (hQ : IsHolQuadDiff Q) (x y : S₀) {w : ℂ}
    (hw : w ∈ (chartAt ℂ y).target) (hwx : (chartAt ℂ y).symm w ∈ (chartAt ℂ x).source)
    (h : ∀ᶠ u in 𝓝 (chartTransition x y w), Q x u = 0) : ∀ᶠ z in 𝓝 w, Q y z = 0 := by
  have hlaw : IsDiffFamily 2 0 Q := hQ.1
  have hsymm : ContinuousAt (chartAt ℂ y).symm w := (chartAt ℂ y).continuousAt_symm hw
  have hτ : ContinuousAt (chartTransition x y) w :=
    ((chartAt ℂ x).continuousAt hwx).comp hsymm
  have h1 : ∀ᶠ z in 𝓝 w, z ∈ (chartAt ℂ y).target := (chartAt ℂ y).open_target.mem_nhds hw
  have h2 : ∀ᶠ z in 𝓝 w, (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source :=
    hsymm.preimage_mem_nhds ((chartAt ℂ x).open_source.mem_nhds hwx)
  have h3 : ∀ᶠ z in 𝓝 w, Q x (chartTransition x y z) = 0 := hτ.eventually h
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  rw [hlaw.2 x y z hz1 hz2, hz3]
  simp

/-- A holomorphic quadratic differential that vanishes near some point of a ball inside a chart target vanishes on
the whole ball. -/
theorem s82td_hol_ball {Q : S₀ → ℂ → ℂ} (hQ : IsHolQuadDiff Q) (x : S₀) {c : ℂ} {r : ℝ}
    (hB : ball c r ⊆ (chartAt ℂ x).target) {w : ℂ} (hwB : w ∈ ball c r)
    (h : ∀ᶠ u in 𝓝 w, Q x u = 0) : EqOn (Q x) 0 (ball c r) := by
  have han : AnalyticOnNhd ℂ (Q x) (ball c r) :=
    ((hQ.2 x).mono hB).analyticOnNhd isOpen_ball
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball c r).isPreconnected hwB
    (h.filter_mono nhdsWithin_le_nhds).frequently

/-- A ball around the chart centre inside the chart target. -/
theorem s82td_center_ball (x : S₀) :
    ∃ r : ℝ, 0 < r ∧ ball (chartAt ℂ x x) r ⊆ (chartAt ℂ x).target :=
  Metric.isOpen_iff.1 (chartAt ℂ x).open_target _ ((chartAt ℂ x).map_source (mem_chart_source ℂ x))

/-- The neighbourhood of `x` mapped into a ball of the chart at `x`. -/
theorem s82td_ball_nhds (x : S₀) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ y in 𝓝 x, y ∈ (chartAt ℂ x).source ∧ chartAt ℂ x y ∈ ball (chartAt ℂ x x) r := by
  have hc : ContinuousAt (chartAt ℂ x) x := (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
  filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x),
    hc.preimage_mem_nhds (ball_mem_nhds _ hr)] with y hy1 hy2
  exact ⟨hy1, hy2⟩

/-- **[stub S3] Identity theorem for holomorphic quadratic differentials.**  On a connected surface, a
holomorphic quadratic differential vanishing near the centre of the chart at one point is zero. -/
theorem s82td_hol_eq_zero {Q : S₀ → ℂ → ℂ} (hQ : IsHolQuadDiff Q) (p : S₀)
    (h : ∀ᶠ z in 𝓝 (chartAt ℂ p p), Q p z = 0) : Q = 0 := by
  set A : Set S₀ := {x | ∀ᶠ z in 𝓝 (chartAt ℂ x x), Q x z = 0} with hA
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨r, hr, hB⟩ := s82td_center_ball x
    have hE := s82td_hol_ball hQ x hB (mem_ball_self hr) hx
    filter_upwards [s82td_ball_nhds x hr] with y hy
    show ∀ᶠ z in 𝓝 (chartAt ℂ y y), Q y z = 0
    refine s82td_hol_transfer hQ x y ((chartAt ℂ y).map_source (mem_chart_source ℂ y)) ?_ ?_
    · rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
      exact hy.1
    · have hc : chartTransition x y (chartAt ℂ y y) = chartAt ℂ x y := by
        show chartAt ℂ x ((chartAt ℂ y).symm (chartAt ℂ y y)) = _
        rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
      rw [hc]
      filter_upwards [isOpen_ball.mem_nhds hy.2] with u hu
      exact hE hu
  have hclosed : IsClosed A := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    have hx' : x ∉ A := hx
    obtain ⟨r, hr, hB⟩ := s82td_center_ball x
    filter_upwards [s82td_ball_nhds x hr] with y hy
    show y ∉ A
    intro hyA
    have h1 : ∀ᶠ u in 𝓝 (chartAt ℂ x y), Q x u = 0 := by
      refine s82td_hol_transfer hQ y x (hB hy.2) ?_ ?_
      · rw [(chartAt ℂ x).left_inv hy.1]
        exact mem_chart_source ℂ y
      · have hc : chartTransition y x (chartAt ℂ x y) = chartAt ℂ y y := by
          show chartAt ℂ y ((chartAt ℂ x).symm (chartAt ℂ x y)) = _
          rw [(chartAt ℂ x).left_inv hy.1]
        rw [hc]
        exact hyA
    have hE := s82td_hol_ball hQ x hB hy.2 h1
    refine hx' ?_
    show ∀ᶠ z in 𝓝 (chartAt ℂ x x), Q x z = 0
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with u hu
    exact hE hu
  have hAu : A = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨p, h⟩
  funext x z
  by_cases hz : z ∈ (chartAt ℂ x).target
  · have hyA : (chartAt ℂ x).symm z ∈ A := by
      rw [hAu]
      exact mem_univ _
    have h1 := s82td_hol_transfer hQ ((chartAt ℂ x).symm z) x hz (mem_chart_source ℂ _) hyA
    exact h1.self_of_nhds
  · exact hQ.1.1 x z hz

/-- **[stub S4] A common regular point.**  Two non-zero holomorphic quadratic differentials on a connected
surface have a common regular point. -/
theorem s82td_common_regular {q q₂ : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hq₂ : IsHolQuadDiff q₂)
    (h : q ≠ 0) (h₂ : q₂ ≠ 0) : ∃ p : S₀, IsRegularPoint q p ∧ IsRegularPoint q₂ p := by
  -- a regular point of `q`: otherwise `q` vanishes at every chart centre, hence everywhere by the transformation law
  have hex1 : ∃ p₀, IsRegularPoint q p₀ := by
    by_contra hno
    push_neg at hno
    apply h
    funext x z
    by_cases hz : z ∈ (chartAt ℂ x).target
    · set y := (chartAt ℂ x).symm z with hy_def
      have hy : q y (chartAt ℂ y y) = 0 := by
        have := hno y
        simpa only [IsRegularPoint, not_not] using this
      have hT : chartTransition y x z = chartAt ℂ y y := rfl
      rw [hq.1.2 y x z hz (mem_chart_source ℂ y), hT, hy]
      simp
    · exact hq.1.1 x z hz
  obtain ⟨p₀, hp₀⟩ := hex1
  have hc0 : chartAt ℂ p₀ p₀ ∈ (chartAt ℂ p₀).target := (chartAt ℂ p₀).map_source (mem_chart_source ℂ p₀)
  have htarget : ∀ᶠ w in 𝓝 (chartAt ℂ p₀ p₀), w ∈ (chartAt ℂ p₀).target :=
    (chartAt ℂ p₀).open_target.mem_nhds hc0
  have hcont : ContinuousAt (q p₀) (chartAt ℂ p₀ p₀) :=
    ((hq.2 p₀).differentiableAt ((chartAt ℂ p₀).open_target.mem_nhds hc0)).continuousAt
  have hne : ∀ᶠ w in 𝓝 (chartAt ℂ p₀ p₀), q p₀ w ≠ 0 := hcont.eventually_ne hp₀
  -- `q₂` does not vanish near the centre (identity theorem)
  have hfreq : ∃ᶠ w in 𝓝 (chartAt ℂ p₀ p₀), q₂ p₀ w ≠ 0 := by
    refine Filter.not_eventually.1 ?_
    intro hev
    exact h₂ (s82td_hol_eq_zero hq₂ p₀ (hev.mono fun w hw => by simpa using hw))
  obtain ⟨w, hw3, hw1, hw2⟩ := (hfreq.and_eventually (hne.and htarget)).exists
  set y := (chartAt ℂ p₀).symm w with hy_def
  have hys : y ∈ (chartAt ℂ p₀).source := (chartAt ℂ p₀).map_target hw2
  have hcy : chartAt ℂ y y ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source (mem_chart_source ℂ y)
  have hsy : (chartAt ℂ y).symm (chartAt ℂ y y) ∈ (chartAt ℂ p₀).source := by
    rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
    exact hys
  have hT : chartTransition p₀ y (chartAt ℂ y y) = w := by
    show chartAt ℂ p₀ ((chartAt ℂ y).symm (chartAt ℂ y y)) = w
    rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
    exact (chartAt ℂ p₀).right_inv hw2
  have hd := (s23_transition p₀ y hcy hsy).2
  have key : ∀ Q : S₀ → ℂ → ℂ, IsHolQuadDiff Q → Q p₀ w ≠ 0 → IsRegularPoint Q y := by
    intro Q hQ hQw
    show Q y (chartAt ℂ y y) ≠ 0
    rw [hQ.1.2 p₀ y _ hcy hsy, hT]
    simp [hQw, hd]
  exact ⟨y, key q hq hw1, key q₂ hq₂ hw3⟩

/-- The stretch `ζ ↦ (ζ + kζ̄)/(1 - k)` is real linear, so it is its own derivative. -/
theorem s82td_stretch_hasFDerivAt (k : ℝ) (x : ℂ) :
    HasFDerivAt (teichStretch k)
      (((1 - k)⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ ℂ + k • (Complex.conjCLE : ℂ →L[ℝ] ℂ))) x := by
  have h : teichStretch k =
      ⇑(((1 - k)⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ ℂ + k • (Complex.conjCLE : ℂ →L[ℝ] ℂ))) := by
    funext ζ
    simp only [teichStretch, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_add',
      ContinuousLinearMap.coe_id', Pi.smul_apply, Pi.add_apply, id_eq, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, Complex.real_smul]
    push_cast
    ring
  rw [h]
  exact ContinuousLinearMap.hasFDerivAt _

/-- The real derivative at `c` of a map `L` with `ζ' ∘ L = S_k ∘ ζ` near `c` (`ζ'` with nonzero strict
derivative `a` at `L c`, `ζ` with derivative `b` at `c`): its values at `1` and `i`. -/
theorem s82td_local_fderiv {L ζ ζ' : ℂ → ℂ} {c a b : ℂ} {k : ℝ} (hk : k < 1)
    (hζ : HasDerivAt ζ b c) (hζ' : HasStrictDerivAt ζ' a (L c)) (ha : a ≠ 0) (hL : ContinuousAt L c)
    (hrel : ∀ᶠ z in 𝓝 c, ζ' (L z) = teichStretch k (ζ z)) :
    ∃ M : ℂ →L[ℝ] ℂ, HasFDerivAt L M c ∧ M 1 = a⁻¹ * ((b + k * conj b) / (1 - k)) ∧
      M I = I * (a⁻¹ * ((b - k * conj b) / (1 - k))) := by
  have hk1 : (1 - k : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.2 (by linarith)
  set G := hζ'.localInverse ζ' a (L c) ha
  have hG : HasStrictDerivAt G a⁻¹ (ζ' (L c)) := hζ'.to_localInverse ha
  have hinv : ∀ᶠ w in 𝓝 (L c), G (ζ' w) = w := hζ'.eventually_left_inverse ha
  have hc : ζ' (L c) = teichStretch k (ζ c) := hrel.self_of_nhds
  have hS := s82td_stretch_hasFDerivAt k (ζ c)
  have hζR := hζ.hasFDerivAt.restrictScalars ℝ
  have hGR : HasFDerivAt G (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) a⁻¹)).restrictScalars ℝ)
      (teichStretch k (ζ c)) := by
    rw [← hc]
    exact hG.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hcomp := hGR.comp c (hS.comp c hζR)
  have heq : L =ᶠ[𝓝 c] G ∘ (teichStretch k ∘ ζ) := by
    filter_upwards [hrel, hL.tendsto.eventually hinv] with z hz1 hz2
    show L z = G (teichStretch k (ζ z))
    rw [← hz1, hz2]
  refine ⟨_, hcomp.congr_of_eventuallyEq heq, ?_, ?_⟩
  · simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.coe_smul',
      ContinuousLinearMap.coe_add', ContinuousLinearMap.coe_id', Pi.smul_apply, Pi.add_apply, id_eq,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, Complex.real_smul, smul_eq_mul,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    push_cast
    field_simp
    try ring
  · simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.coe_smul',
      ContinuousLinearMap.coe_add', ContinuousLinearMap.coe_id', Pi.smul_apply, Pi.add_apply, id_eq,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, Complex.real_smul, smul_eq_mul, map_mul,
      Complex.conj_I, Complex.conj_ofReal, ContinuousLinearMap.toSpanSingleton_apply]
    push_cast
    field_simp
    try ring

/-- The algebra of two stretches on one real derivative: `k₂ = k`, and for `k > 0` the ratio `b₂/b` is real, so
`b₂² = r b²` with `r > 0`. -/
theorem s82td_two_stretch_alg {a a₂ b b₂ : ℂ} {k k₂ : ℝ} (hk0 : 0 ≤ k) (hk : k < 1) (hk₂0 : 0 ≤ k₂)
    (hk₂ : k₂ < 1) (ha : a ≠ 0) (ha₂ : a₂ ≠ 0) (hb : b ≠ 0)
    (h1 : a⁻¹ * ((b + k * conj b) / (1 - k)) = a₂⁻¹ * ((b₂ + k₂ * conj b₂) / (1 - k₂)))
    (h2 : a⁻¹ * ((b - k * conj b) / (1 - k)) = a₂⁻¹ * ((b₂ - k₂ * conj b₂) / (1 - k₂))) :
    k₂ = k ∧ (0 < k → ∃ r : ℝ, 0 < r ∧ b₂ ^ 2 = r * b ^ 2) := by
  have hk1 : (1 - k : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.2 (by linarith)
  have hk₂1 : (1 - k₂ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.2 (by linarith)
  -- `b₂ = λ b` and `k₂ b̄₂ = λ k b̄` with `λ = a₂ (1 - k₂) / (a (1 - k))`
  set l : ℂ := a₂ * (1 - k₂) / (a * (1 - k)) with hl
  have hA : b₂ = l * b := by
    have e : a⁻¹ * (b / (1 - k)) = a₂⁻¹ * (b₂ / (1 - k₂)) := by linear_combination (h1 + h2) / 2
    rw [hl]
    field_simp at e ⊢
    linear_combination -e
  have hB : (k₂ : ℂ) * conj b₂ = l * (k * conj b) := by
    have e : a⁻¹ * (k * conj b / (1 - k)) = a₂⁻¹ * (k₂ * conj b₂ / (1 - k₂)) := by
      linear_combination (h1 - h2) / 2
    rw [hl]
    field_simp at e ⊢
    linear_combination -e
  have hl0 : l ≠ 0 := by
    rw [hl]
    exact div_ne_zero (mul_ne_zero ha₂ hk₂1) (mul_ne_zero ha hk1)
  have hcb : conj b ≠ 0 := (map_ne_zero _).2 hb
  -- `k₂ l̄ = l k`
  have hC : (k₂ : ℂ) * conj l = l * k := by
    rw [hA, map_mul] at hB
    have : ((k₂ : ℂ) * conj l - l * k) * conj b = 0 := by linear_combination hB
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hcb)
  have hkk : k₂ = k := by
    have := congrArg (fun z : ℂ => ‖z‖) hC
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk0,
      abs_of_nonneg hk₂0] at this
    have hln : 0 < ‖l‖ := norm_pos_iff.2 hl0
    nlinarith
  refine ⟨hkk, fun hkpos => ?_⟩
  rw [hkk] at hC
  have hreal : conj l = l := by
    have hk' : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hkpos.ne'
    have : (k : ℂ) * (conj l - l) = 0 := by linear_combination hC
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hk')
  have hlre : (l.re : ℂ) = l := Complex.conj_eq_iff_re.1 hreal
  have hre0 : l.re ≠ 0 := by
    intro h0
    apply hl0
    rw [← hlre, h0, Complex.ofReal_zero]
  refine ⟨l.re ^ 2, by positivity, ?_⟩
  rw [hA]
  push_cast
  rw [hlre]
  ring

/-- **Pointwise comparison at a common regular point.**  If `f` is a Teichmüller map for `(q, k)` and for `(q₂, k₂)`
and `p` is regular for both, then `k₂ = k` and, for `k > 0`, `q₂ = r q` at the chart centre with `r > 0`. -/
theorem s82td_center_ratio {f : S₀ ≃ₜ S} {q q₂ : S₀ → ℂ → ℂ} {q' q₂' : S → ℂ → ℂ} {k k₂ : ℝ}
    (hT : IsTeichmullerMap f q q' k) (hT₂ : IsTeichmullerMap f q₂ q₂' k₂) {p : S₀}
    (hp : IsRegularPoint q p) (hp₂ : IsRegularPoint q₂ p) :
    k₂ = k ∧ (0 < k → ∃ r : ℝ, 0 < r ∧ q₂ p (chartAt ℂ p p) = r * q p (chartAt ℂ p p)) := by
  obtain ⟨-, ζ, ζ', hζ, hζ', hrel⟩ := hT.regular p hp
  obtain ⟨-, ζ₂, ζ₂', hζ₂, hζ₂', hrel₂⟩ := hT₂.regular p hp₂
  set c := chartAt ℂ p p
  have hLc : localMapExpr f p c = chartAt ℂ (f p) (f p) := by
    show chartAt ℂ (f p) (f ((chartAt ℂ p).symm (chartAt ℂ p p))) = _
    rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
  have hL : ContinuousAt (localMapExpr f p) c := by
    have h1 : ContinuousAt (chartAt ℂ p).symm c :=
      (chartAt ℂ p).continuousAt_symm ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
    have h2 : ContinuousAt (chartAt ℂ (f p)) (f ((chartAt ℂ p).symm c)) := by
      rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
      exact (chartAt ℂ (f p)).continuousAt (mem_chart_source ℂ (f p))
    exact ContinuousAt.comp (f := fun z => f ((chartAt ℂ p).symm z)) h2 (ContinuousAt.comp (g := ⇑f) (f := ⇑(chartAt ℂ p).symm) f.continuous.continuousAt h1)
  have hd := hζ.1.differentiableAt.hasDerivAt
  have hd₂ := hζ₂.1.differentiableAt.hasDerivAt
  have hs' : HasStrictDerivAt ζ' (deriv ζ' (localMapExpr f p c)) (localMapExpr f p c) := by
    rw [hLc]
    exact hζ'.1.hasStrictDerivAt
  have hs₂' : HasStrictDerivAt ζ₂' (deriv ζ₂' (localMapExpr f p c)) (localMapExpr f p c) := by
    rw [hLc]
    exact hζ₂'.1.hasStrictDerivAt
  have ha : deriv ζ' (localMapExpr f p c) ≠ 0 := by
    rw [hLc]
    exact hζ'.2.2.1
  have ha₂ : deriv ζ₂' (localMapExpr f p c) ≠ 0 := by
    rw [hLc]
    exact hζ₂'.2.2.1
  obtain ⟨M, hM, hM1, hMI⟩ := s82td_local_fderiv hT.k_lt_one hd hs' ha hL hrel
  obtain ⟨M₂, hM₂, hM₂1, hM₂I⟩ := s82td_local_fderiv hT₂.k_lt_one hd₂ hs₂' ha₂ hL hrel₂
  have hMM := hM.unique hM₂
  have h1 := hM1.symm.trans ((congrArg (fun N : ℂ →L[ℝ] ℂ => N 1) hMM).trans hM₂1)
  have h2 : _ := mul_left_cancel₀ Complex.I_ne_zero
    (hMI.symm.trans ((congrArg (fun N : ℂ →L[ℝ] ℂ => N I) hMM).trans hM₂I))
  obtain ⟨hkk, hr⟩ := s82td_two_stretch_alg hT.k_nonneg hT.k_lt_one hT₂.k_nonneg hT₂.k_lt_one ha ha₂
    hζ.2.2.1 h1 h2
  refine ⟨hkk, fun hk => ?_⟩
  obtain ⟨r, hr0, hrr⟩ := hr hk
  refine ⟨r, hr0, ?_⟩
  rw [← hζ.2.2.2.self_of_nhds, ← hζ₂.2.2.2.self_of_nhds]
  exact hrr

/-- A holomorphic function with real values near `z₀` is constant near `z₀` (open mapping). -/
theorem s82td_real_analytic_const {R : ℂ → ℂ} {z₀ : ℂ} (hR : AnalyticAt ℂ R z₀)
    (hre : ∀ᶠ z in 𝓝 z₀, (R z).im = 0) : ∀ᶠ z in 𝓝 z₀, R z = R z₀ := by
  rcases hR.eventually_constant_or_nhds_le_map_nhds with h | h
  · exact h
  · exfalso
    have hmem : {u : ℂ | u.im = 0} ∈ 𝓝 (R z₀) := h (Filter.mem_map.2 hre)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
    have hin : R z₀ + ((ε / 2 : ℝ) : ℂ) * I ∈ ball (R z₀) ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    have him := hball hin
    simp only [mem_setOf_eq, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero] at him
    have h0 : (R z₀).im = 0 := hre.self_of_nhds
    linarith

/-- Regularity at `y = φ_p⁻¹(w)` from the value of `Q p` at `w` (transformation law, nonzero transition
derivative). -/
theorem s82td_regular_of_chart {Q : S₀ → ℂ → ℂ} (hQ : IsHolQuadDiff Q) (p : S₀) {w : ℂ}
    (hw : w ∈ (chartAt ℂ p).target) (hQw : Q p w ≠ 0) : IsRegularPoint Q ((chartAt ℂ p).symm w) := by
  set y := (chartAt ℂ p).symm w with hy_def
  have hys : y ∈ (chartAt ℂ p).source := (chartAt ℂ p).map_target hw
  have hcy : chartAt ℂ y y ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source (mem_chart_source ℂ y)
  have hsy : (chartAt ℂ y).symm (chartAt ℂ y y) ∈ (chartAt ℂ p).source := by
    rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
    exact hys
  have hT : chartTransition p y (chartAt ℂ y y) = w := by
    show chartAt ℂ p ((chartAt ℂ y).symm (chartAt ℂ y y)) = w
    rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
    exact (chartAt ℂ p).right_inv hw
  have hd := (s23_transition p y hcy hsy).2
  show Q y (chartAt ℂ y y) ≠ 0
  rw [hQ.1.2 p y _ hcy hsy, hT]
  simp [hQw, hd]

/-- The value of `Q p` at `w` is the value at the centre of the chart at `y = φ_p⁻¹(w)` times the common factor
`τ'(w)²`, `τ = φ_y ∘ φ_p⁻¹`. -/
theorem s82td_value_of_center {Q : S₀ → ℂ → ℂ} (hQ : IsHolQuadDiff Q) (p : S₀) {w : ℂ}
    (hw : w ∈ (chartAt ℂ p).target) :
    Q p w = Q ((chartAt ℂ p).symm w) (chartAt ℂ ((chartAt ℂ p).symm w) ((chartAt ℂ p).symm w)) *
      deriv (chartTransition ((chartAt ℂ p).symm w) p) w ^ 2 := by
  rw [hQ.1.2 ((chartAt ℂ p).symm w) p w hw (mem_chart_source ℂ _), zpow_zero, mul_one, zpow_two, ← pow_two]
  rfl

/-- **[stub S1] Two Teichmüller structures on one map, locally.**  If `f` is a Teichmüller map for `(q, k)` and
for `(q₂, k₂)` and `p` is regular for `q` and `q₂`, then `k₂ = k` and, when `k > 0`, `q₂ = c q` near `p` for a
constant `c > 0`: the Beltrami coefficient of `f` near `p` is `k ζ̄_z/ζ_z = k₂ ζ̄₂_z/ζ₂_z` (`ζ`, `ζ₂` the natural
parameters), so `|·|` gives `k = k₂` and, for `k > 0`, `q₂/q = (ζ₂_z/ζ_z)²` is real and positive, hence locally
constant. -/
theorem s82td_local_ratio {f : S₀ ≃ₜ S} {q q₂ : S₀ → ℂ → ℂ} {q' q₂' : S → ℂ → ℂ} {k k₂ : ℝ}
    (hT : IsTeichmullerMap f q q' k) (hT₂ : IsTeichmullerMap f q₂ q₂' k₂) {p : S₀}
    (hp : IsRegularPoint q p) (hp₂ : IsRegularPoint q₂ p) :
    k₂ = k ∧ (0 < k → ∃ c : ℝ, 0 < c ∧ ∀ᶠ z in 𝓝 (chartAt ℂ p p), q₂ p z = c * q p z) := by
  obtain ⟨hkk, hr⟩ := s82td_center_ratio hT hT₂ hp hp₂
  refine ⟨hkk, fun hk => ?_⟩
  have hc0 : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have htn : (chartAt ℂ p).target ∈ 𝓝 (chartAt ℂ p p) := (chartAt ℂ p).open_target.mem_nhds hc0
  have han : AnalyticAt ℂ (q p) (chartAt ℂ p p) := (hT.initial.2 p).analyticAt htn
  have han₂ : AnalyticAt ℂ (q₂ p) (chartAt ℂ p p) := (hT₂.initial.2 p).analyticAt htn
  have hq0 : q p (chartAt ℂ p p) ≠ 0 := hp
  have hne : ∀ᶠ w in 𝓝 (chartAt ℂ p p), q p w ≠ 0 := han.continuousAt.eventually_ne hq0
  have hRan : AnalyticAt ℂ (fun w => q₂ p w / q p w) (chartAt ℂ p p) := han₂.div han hq0
  -- the ratio is real near the centre: at `w` it is the ratio at the centre of the chart at `φ_p⁻¹(w)`
  have hre : ∀ᶠ w in 𝓝 (chartAt ℂ p p), (q₂ p w / q p w).im = 0 := by
    filter_upwards [htn, hne] with w hw hqw
    by_cases hq₂w : q₂ p w = 0
    · rw [hq₂w, zero_div, Complex.zero_im]
    · obtain ⟨-, hry⟩ := s82td_center_ratio hT hT₂ (s82td_regular_of_chart hT.initial p hw hqw)
        (s82td_regular_of_chart hT₂.initial p hw hq₂w)
      obtain ⟨r, -, hrw⟩ := hry hk
      have e : q₂ p w = r * q p w := by
        rw [s82td_value_of_center hT₂.initial p hw, s82td_value_of_center hT.initial p hw, hrw]
        ring
      rw [e, mul_div_assoc, div_self hqw, mul_one, Complex.ofReal_im]
  have hconst := s82td_real_analytic_const hRan hre
  obtain ⟨r, hr0, hrc⟩ := hr hk
  refine ⟨r, hr0, ?_⟩
  filter_upwards [hconst, hne] with w hw hqw
  have hw' : q₂ p w / q p w = r := by
    rw [hw, hrc, mul_div_assoc, div_self hq0, mul_one]
  rw [← hw', div_mul_cancel₀ _ hqw]

/-- With `k = 0` a Teichmüller map is holomorphic at a regular point of `q`: in natural parameters it is
`ζ' ∘ f = ζ`, so `f = ζ'⁻¹ ∘ ζ` locally. -/
theorem s82td_k0_mdiff_regular {f : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ}
    (hT : IsTeichmullerMap f q q' 0) {p : S₀} (hp : IsRegularPoint q p) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f p := by
  obtain ⟨-, ζ, ζ', hζ, hζ', hrel⟩ := hT.regular p hp
  have hS0 : ∀ x : ℂ, teichStretch 0 x = x := fun x => by simp [teichStretch]
  have hLc : localMapExpr f p (chartAt ℂ p p) = chartAt ℂ (f p) (f p) := by
    show chartAt ℂ (f p) (f ((chartAt ℂ p).symm (chartAt ℂ p p))) = _
    rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
  have hL : ContinuousAt (localMapExpr f p) (chartAt ℂ p p) := by
    have h1 : ContinuousAt (chartAt ℂ p).symm (chartAt ℂ p p) :=
      (chartAt ℂ p).continuousAt_symm ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
    have h2 : ContinuousAt (chartAt ℂ (f p)) (f ((chartAt ℂ p).symm (chartAt ℂ p p))) := by
      rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
      exact (chartAt ℂ (f p)).continuousAt (mem_chart_source ℂ (f p))
    exact ContinuousAt.comp (f := fun z => f ((chartAt ℂ p).symm z)) h2 (ContinuousAt.comp (g := ⇑f) (f := ⇑(chartAt ℂ p).symm) f.continuous.continuousAt h1)
  have hs' : HasStrictDerivAt ζ' (deriv ζ' (localMapExpr f p (chartAt ℂ p p)))
      (localMapExpr f p (chartAt ℂ p p)) := by
    rw [hLc]
    exact hζ'.1.hasStrictDerivAt
  have ha : deriv ζ' (localMapExpr f p (chartAt ℂ p p)) ≠ 0 := by
    rw [hLc]
    exact hζ'.2.2.1
  have hG := hs'.to_localInverse ha
  have hinv := hs'.eventually_left_inverse ha
  have hc : ζ' (localMapExpr f p (chartAt ℂ p p)) = ζ (chartAt ℂ p p) := by
    rw [hrel.self_of_nhds, hS0]
  have heq : localMapExpr f p =ᶠ[𝓝 (chartAt ℂ p p)]
      hs'.localInverse ζ' _ _ ha ∘ ζ := by
    filter_upwards [hrel, hL.tendsto.eventually hinv] with z hz1 hz2
    show localMapExpr f p z = hs'.localInverse ζ' _ _ ha (ζ z)
    rw [← hS0 (ζ z), ← hz1, hz2]
  have hd : DifferentiableAt ℂ (localMapExpr f p) (chartAt ℂ p p) :=
    have hGd : DifferentiableAt ℂ (hs'.localInverse ζ' _ _ ha) (ζ (chartAt ℂ p p)) := by
      rw [← hc]
      exact (HasStrictDerivAt.hasDerivAt hG).differentiableAt
    (hGd.comp _ hζ.1.differentiableAt).congr_of_eventuallyEq heq
  rw [s23_mdifferentiableAt_iff (mem_chart_source ℂ p) (mem_chart_source ℂ (f p))]
  exact ⟨f.continuous.continuousAt, hd⟩

/-- **[stub S5] A Teichmüller map with `k = 0` is biholomorphic**: in natural parameters it is the identity at
regular points, and the zeros of `q` are isolated, so the local expressions are holomorphic off a discrete set
and continuous (removable singularities); the inverse of a holomorphic homeomorphism is holomorphic. -/
theorem s82td_k0_biholomorphic {f : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ}
    (hT : IsTeichmullerMap f q q' 0) : IsBiholomorphic f := by
  have hmd : ∀ p : S₀, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f p := by
    intro p
    by_cases hp : IsRegularPoint q p
    · exact s82td_k0_mdiff_regular hT hp
    · -- `p` is an isolated zero of `q`: removable singularity of the local expression
      have hc0 : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
      have htn : (chartAt ℂ p).target ∈ 𝓝 (chartAt ℂ p p) := (chartAt ℂ p).open_target.mem_nhds hc0
      have han : AnalyticAt ℂ (q p) (chartAt ℂ p p) := (hT.initial.2 p).analyticAt htn
      have hiso : ∀ᶠ z in 𝓝[≠] chartAt ℂ p p, q p z ≠ 0 := by
        rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
        · exact absurd (s82td_hol_eq_zero hT.initial p h) hT.initial_ne
        · exact h
      have h1 : ContinuousAt (chartAt ℂ p).symm (chartAt ℂ p p) := (chartAt ℂ p).continuousAt_symm hc0
      have hcontf : ContinuousAt (fun z => f ((chartAt ℂ p).symm z)) (chartAt ℂ p p) :=
        ContinuousAt.comp (g := ⇑f) (f := ⇑(chartAt ℂ p).symm) f.continuous.continuousAt h1
      have hfs : f ((chartAt ℂ p).symm (chartAt ℂ p p)) ∈ (chartAt ℂ (f p)).source := by
        rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
        exact mem_chart_source ℂ (f p)
      have hsrc : ∀ᶠ z in 𝓝 (chartAt ℂ p p),
          z ∈ (chartAt ℂ p).target ∧ f ((chartAt ℂ p).symm z) ∈ (chartAt ℂ (f p)).source :=
        Filter.inter_mem htn (hcontf.preimage_mem_nhds ((chartAt ℂ (f p)).open_source.mem_nhds hfs))
      have hdiff : ∀ᶠ z in 𝓝[≠] chartAt ℂ p p, DifferentiableAt ℂ (localMapExpr f p) z := by
        filter_upwards [hiso, nhdsWithin_le_nhds hsrc] with z hz hzz
        have hy := s82td_k0_mdiff_regular hT (s82td_regular_of_chart hT.initial p hzz.1 hz)
        have h2 := (s23_mdifferentiableAt_iff (x := p) (y := f p) ((chartAt ℂ p).map_target hzz.1) hzz.2).1 hy
        rw [(chartAt ℂ p).right_inv hzz.1] at h2
        exact h2.2
      have hs : {z | z ≠ chartAt ℂ p p → DifferentiableAt ℂ (localMapExpr f p) z} ∈ 𝓝 (chartAt ℂ p p) :=
        eventually_nhdsWithin_iff.1 hdiff
      have hLcont : ContinuousAt (localMapExpr f p) (chartAt ℂ p p) := by
        have h2 : ContinuousAt (chartAt ℂ (f p)) (f ((chartAt ℂ p).symm (chartAt ℂ p p))) :=
          (chartAt ℂ (f p)).continuousAt hfs
        exact ContinuousAt.comp (f := fun z => f ((chartAt ℂ p).symm z)) h2 hcontf
      have hDs := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hs).1
        ⟨fun z hz => (hz.1 hz.2).differentiableWithinAt, hLcont⟩
      have hLd : DifferentiableAt ℂ (localMapExpr f p) (chartAt ℂ p p) := hDs.differentiableAt hs
      rw [s23_mdifferentiableAt_iff (mem_chart_source ℂ p) (mem_chart_source ℂ (f p))]
      exact ⟨f.continuous.continuousAt, hLd⟩
  have hM : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := hmd
  refine ⟨hM, f.symm, ?_, f.symm_apply_apply, f.apply_symm_apply⟩
  have hinv := s31inv_invFun_mdifferentiableOn (M := S₀) (N := S) f.injective hM
  have hfe : Function.invFun f = f.symm := by
    funext y
    obtain ⟨x, rfl⟩ := f.surjective y
    rw [Function.leftInverse_invFun f.injective x, f.symm_apply_apply]
  have h2 : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f.symm univ := by
    rw [← hfe, ← f.surjective.range_eq]
    exact hinv
  intro y
  exact (h2 y (mem_univ y)).mdifferentiableAt Filter.univ_mem

/-- **[S6] Teichmüller data are determined by the map.**  Two Teichmüller structures `(q, k)`, `(q₂, k₂)` on the
same map with `k > 0` have `k₂ = k` and `q₂ = c q`, `c > 0`. -/
theorem s82td_data_unique {f : S₀ ≃ₜ S} {q q₂ : S₀ → ℂ → ℂ} {q' q₂' : S → ℂ → ℂ} {k k₂ : ℝ}
    (hT : IsTeichmullerMap f q q' k) (hT₂ : IsTeichmullerMap f q₂ q₂' k₂) (hk : 0 < k) :
    k₂ = k ∧ ∃ c : ℝ, 0 < c ∧ q₂ = (c : ℂ) • q := by
  obtain ⟨p, hp, hp₂⟩ := s82td_common_regular hT.initial hT₂.initial hT.initial_ne hT₂.initial_ne
  obtain ⟨hkk, hc⟩ := s82td_local_ratio hT hT₂ hp hp₂
  obtain ⟨c, hc0, hloc⟩ := hc hk
  refine ⟨hkk, c, hc0, ?_⟩
  have hQ : IsHolQuadDiff (q₂ - (c : ℂ) • q) :=
    (holQuadDiffSubmodule S₀).sub_mem hT₂.initial ((holQuadDiffSubmodule S₀).smul_mem _ hT.initial)
  have h0 := s82td_hol_eq_zero hQ p (hloc.mono fun z hz => by
    show q₂ p z - (c : ℂ) * q p z = 0
    rw [hz, sub_self])
  exact sub_eq_zero.1 h0

/-- **[S7] The dimension of the interior admissible differentials**: the pull-back to the interior is injective on
`Q̃(S₀)`, so `dim_ℝ` of its image is `6g - 6 + 2n + 3m` (Theorem 31.1). -/
theorem s82td_finrank_interior {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) :
    (Module.finrank ℝ (admissibleQDInterior F₀) : ℤ) = 6 * g - 6 + 2 * n + 3 * m := by
  have hinj : Function.Injective ((pullbackQDLinear F₀).domRestrict (admissibleQDSpace F₀)) := by
    intro a b hab
    apply Subtype.ext
    have hab' : pullbackQD F₀ a.1 = pullbackQD F₀ b.1 := hab
    have hs : a.1 - b.1 ∈ admissibleQDSpace F₀ := (admissibleQDSpace F₀).sub_mem a.2 b.2
    have h0 : pullbackQD F₀ (a.1 - b.1) = 0 := by
      have := map_sub (pullbackQDLinear F₀) a.1 b.1
      rw [show (pullbackQDLinear F₀) a.1 = pullbackQD F₀ a.1 from rfl,
        show (pullbackQDLinear F₀) b.1 = pullbackQD F₀ b.1 from rfl, hab', sub_self] at this
      exact this
    exact sub_eq_zero.1 (s32p_pullbackQD_eq_zero F₀ hs h0)
  have h1 := (LinearEquiv.ofInjective _ hinj).finrank_eq
  have h2 := (LinearEquiv.ofEq _ _ (LinearMap.range_domRestrict (admissibleQDSpace F₀) (pullbackQDLinear F₀))).finrank_eq
  have h3 : Module.finrank ℝ (admissibleQDInterior F₀) = Module.finrank ℝ (admissibleQDSpace F₀) :=
    (h1.trans h2).symm
  rw [h3]
  exact thm31_1_admissibleQD_finrank F₀ hex

/-- **[stub C3] A biholomorphic Teichmüller map has `k = 0`**: its real derivative at a regular point is complex
linear, while that of a Teichmüller map has antilinear part `k ζ̄_z/(1-k)` times a nonzero factor. -/
theorem s82td_biholomorphic_k_eq_zero {f : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ}
    (hb : IsBiholomorphic f) (hT : IsTeichmullerMap f q q' k) : k = 0 := by
  obtain ⟨p, hp, -⟩ := s82td_common_regular hT.initial hT.initial hT.initial_ne hT.initial_ne
  obtain ⟨-, ζ, ζ', hζ, hζ', hrel⟩ := hT.regular p hp
  have hLc : localMapExpr f p (chartAt ℂ p p) = chartAt ℂ (f p) (f p) := by
    show chartAt ℂ (f p) (f ((chartAt ℂ p).symm (chartAt ℂ p p))) = _
    rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
  have hLd : DifferentiableAt ℂ (localMapExpr f p) (chartAt ℂ p p) :=
    ((s23_mdifferentiableAt_iff (mem_chart_source ℂ p) (mem_chart_source ℂ (f p))).1 (hb.1 p)).2
  have hs' : HasStrictDerivAt ζ' (deriv ζ' (localMapExpr f p (chartAt ℂ p p)))
      (localMapExpr f p (chartAt ℂ p p)) := by
    rw [hLc]
    exact hζ'.1.hasStrictDerivAt
  have ha : deriv ζ' (localMapExpr f p (chartAt ℂ p p)) ≠ 0 := by
    rw [hLc]
    exact hζ'.2.2.1
  obtain ⟨M, hM, hM1, hMI⟩ := s82td_local_fderiv hT.k_lt_one hζ.1.differentiableAt.hasDerivAt hs' ha
    hLd.continuousAt hrel
  have hMM := hM.unique (hLd.hasDerivAt.hasFDerivAt.restrictScalars ℝ)
  have h1 : M 1 = deriv (localMapExpr f p) (chartAt ℂ p p) := by
    rw [hMM]
    simp
  have hI : M I = I * deriv (localMapExpr f p) (chartAt ℂ p p) := by
    rw [hMM]
    simp
  have hk1 : (1 - k : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.2 (by linarith [hT.k_lt_one])
  have key := mul_left_cancel₀ Complex.I_ne_zero (hMI.symm.trans (hI.trans (by rw [← h1, hM1])))
  have key2 := mul_left_cancel₀ (inv_ne_zero ha) key
  rw [div_left_inj' hk1] at key2
  have hkb : (k : ℂ) * conj (deriv ζ (chartAt ℂ p p)) = 0 := by linear_combination (-(1 : ℂ) / 2) * key2
  have hcb : conj (deriv ζ (chartAt ℂ p p)) ≠ 0 := (map_ne_zero _).2 hζ.2.2.1
  exact Complex.ofReal_eq_zero.1 ((mul_eq_zero.1 hkb).resolve_right hcb)

/-- **Removable singularity on surfaces.**  A continuous map between Riemann surfaces that is holomorphic at every
point of a punctured neighbourhood of `y` is holomorphic at `y`. -/
theorem s82td_mdiff_of_punctured {X₁ X₂ : Type u} [TopologicalSpace X₁] [ChartedSpace ℂ X₁] [T2Space X₁]
    [IsManifold 𝓘(ℂ) ω X₁] [TopologicalSpace X₂] [ChartedSpace ℂ X₂] [IsManifold 𝓘(ℂ) ω X₂] {F : X₁ → X₂}
    (hF : Continuous F) {y : X₁} (h : ∀ᶠ y' in 𝓝[≠] y, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F y') :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F y := by
  have hc0 : chartAt ℂ y y ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source (mem_chart_source ℂ y)
  have htn : (chartAt ℂ y).target ∈ 𝓝 (chartAt ℂ y y) := (chartAt ℂ y).open_target.mem_nhds hc0
  have h1 : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) := (chartAt ℂ y).continuousAt_symm hc0
  have hyy : (chartAt ℂ y).symm (chartAt ℂ y y) = y := (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hcontf : ContinuousAt (fun w => F ((chartAt ℂ y).symm w)) (chartAt ℂ y y) :=
    ContinuousAt.comp (g := F) (f := (chartAt ℂ y).symm) hF.continuousAt h1
  have hfs : F ((chartAt ℂ y).symm (chartAt ℂ y y)) ∈ (chartAt ℂ (F y)).source := by
    rw [hyy]
    exact mem_chart_source ℂ (F y)
  have hsrc : ∀ᶠ w in 𝓝 (chartAt ℂ y y),
      w ∈ (chartAt ℂ y).target ∧ F ((chartAt ℂ y).symm w) ∈ (chartAt ℂ (F y)).source :=
    Filter.inter_mem htn (hcontf.preimage_mem_nhds ((chartAt ℂ (F y)).open_source.mem_nhds hfs))
  -- the punctured neighbourhood of the centre is mapped into the punctured neighbourhood of `y`
  have htend : Tendsto (chartAt ℂ y).symm (𝓝[≠] chartAt ℂ y y) (𝓝[≠] y) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := h1.tendsto
      rw [hyy] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds htn] with w hw hwt
      intro hwy
      apply hw
      have := congrArg (chartAt ℂ y) hwy
      rwa [(chartAt ℂ y).right_inv hwt] at this
  have hpunct : ∀ᶠ w in 𝓝[≠] chartAt ℂ y y, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F ((chartAt ℂ y).symm w) :=
    htend.eventually h
  have hdiff : ∀ᶠ w in 𝓝[≠] chartAt ℂ y y,
      DifferentiableAt ℂ (fun w => chartAt ℂ (F y) (F ((chartAt ℂ y).symm w))) w := by
    filter_upwards [hpunct, nhdsWithin_le_nhds hsrc] with w hw hww
    have h2 := (s23_mdifferentiableAt_iff (x := y) (y := F y) ((chartAt ℂ y).map_target hww.1) hww.2).1 hw
    rw [(chartAt ℂ y).right_inv hww.1] at h2
    exact h2.2
  have hs : {w | w ≠ chartAt ℂ y y →
      DifferentiableAt ℂ (fun w => chartAt ℂ (F y) (F ((chartAt ℂ y).symm w))) w} ∈ 𝓝 (chartAt ℂ y y) :=
    eventually_nhdsWithin_iff.1 hdiff
  have hLcont : ContinuousAt (fun w => chartAt ℂ (F y) (F ((chartAt ℂ y).symm w))) (chartAt ℂ y y) :=
    ContinuousAt.comp (f := fun w => F ((chartAt ℂ y).symm w)) ((chartAt ℂ (F y)).continuousAt hfs) hcontf
  have hDs := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hs).1
    ⟨fun z hz => (hz.1 hz.2).differentiableWithinAt, hLcont⟩
  rw [s23_mdifferentiableAt_iff (mem_chart_source ℂ y) (mem_chart_source ℂ (F y))]
  exact ⟨hF.continuousAt, hDs.differentiableAt hs⟩

/-- Same data, at the image of a regular point: in natural parameters `ζ₂' ∘ f₂ = ε ζ₁' ∘ f₁` (`ε = ±1`), so
`f₂ ∘ f₁⁻¹ = ζ₂'⁻¹ ∘ (ε ζ₁')` near `f₁ p`. -/
theorem s82td_same_data_mdiff_regular {X₁ X₂ : Type u} [TopologicalSpace X₁] [ChartedSpace ℂ X₁]
    [IsManifold 𝓘(ℂ) ω X₁] [TopologicalSpace X₂] [ChartedSpace ℂ X₂] [IsManifold 𝓘(ℂ) ω X₂]
    {f₁ : S₀ ≃ₜ X₁} {f₂ : S₀ ≃ₜ X₂} {q : S₀ → ℂ → ℂ} {q₁' : X₁ → ℂ → ℂ} {q₂' : X₂ → ℂ → ℂ} {k : ℝ}
    (h₁ : IsTeichmullerMap f₁ q q₁' k) (h₂ : IsTeichmullerMap f₂ q q₂' k) {p : S₀} (hp : IsRegularPoint q p) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (f₁.symm.trans f₂) (f₁ p) := by
  obtain ⟨-, ζ, ζ₁', hζ, hζ₁', hrel₁⟩ := h₁.regular p hp
  obtain ⟨-, ζ₂, ζ₂', hζ₂, hζ₂', hrel₂⟩ := h₂.regular p hp
  have hkey := eq25_3_natural_parameter_unique hζ₂.1 hζ.1 hζ₂.2.1 hζ.2.1 hζ₂.2.2.2 hζ.2.2.2 hp
  obtain ⟨ε, hε, hεe⟩ : ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∀ᶠ z in 𝓝 (chartAt ℂ p p), ζ₂ z = ε * ζ z := by
    rcases hkey with h | h
    · exact ⟨1, Or.inl rfl, h.mono fun z hz => by rw [hz, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, h.mono fun z hz => by rw [hz, neg_one_mul]⟩
  have hS : ∀ x, teichStretch k (ε * x) = ε * teichStretch k x := by
    intro x
    have := eq26_4 k ε hε 0 x
    rw [add_zero] at this
    rw [this]
    simp [teichStretch]
  have hc₁ : chartAt ℂ (f₁ p) (f₁ p) ∈ (chartAt ℂ (f₁ p)).target :=
    (chartAt ℂ (f₁ p)).map_source (mem_chart_source ℂ (f₁ p))
  have hyy : (chartAt ℂ (f₁ p)).symm (chartAt ℂ (f₁ p) (f₁ p)) = f₁ p :=
    (chartAt ℂ (f₁ p)).left_inv (mem_chart_source ℂ (f₁ p))
  have hs1 : ContinuousAt (chartAt ℂ (f₁ p)).symm (chartAt ℂ (f₁ p) (f₁ p)) :=
    (chartAt ℂ (f₁ p)).continuousAt_symm hc₁
  have hzs : f₁.symm ((chartAt ℂ (f₁ p)).symm (chartAt ℂ (f₁ p) (f₁ p))) = p := by
    rw [hyy, f₁.symm_apply_apply]
  have hcz : ContinuousAt (fun w => f₁.symm ((chartAt ℂ (f₁ p)).symm w)) (chartAt ℂ (f₁ p) (f₁ p)) :=
    ContinuousAt.comp (g := ⇑f₁.symm) (f := (chartAt ℂ (f₁ p)).symm) f₁.symm.continuous.continuousAt hs1
  have hzc : ContinuousAt (fun w => chartAt ℂ p (f₁.symm ((chartAt ℂ (f₁ p)).symm w)))
      (chartAt ℂ (f₁ p) (f₁ p)) := by
    refine ContinuousAt.comp (f := fun w => f₁.symm ((chartAt ℂ (f₁ p)).symm w)) ?_ hcz
    rw [hzs]
    exact (chartAt ℂ p).continuousAt (mem_chart_source ℂ p)
  have hz0 : chartAt ℂ p (f₁.symm ((chartAt ℂ (f₁ p)).symm (chartAt ℂ (f₁ p) (f₁ p)))) = chartAt ℂ p p := by
    rw [hzs]
  have hsrc : ∀ᶠ w in 𝓝 (chartAt ℂ (f₁ p) (f₁ p)),
      w ∈ (chartAt ℂ (f₁ p)).target ∧ f₁.symm ((chartAt ℂ (f₁ p)).symm w) ∈ (chartAt ℂ p).source := by
    refine Filter.inter_mem ((chartAt ℂ (f₁ p)).open_target.mem_nhds hc₁) (hcz.preimage_mem_nhds ?_)
    rw [hzs]
    exact (chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p)
  have hz_ev : ∀ {P : ℂ → Prop}, (∀ᶠ x in 𝓝 (chartAt ℂ p p), P x) →
      ∀ᶠ w in 𝓝 (chartAt ℂ (f₁ p) (f₁ p)), P (chartAt ℂ p (f₁.symm ((chartAt ℂ (f₁ p)).symm w))) := by
    intro P hP
    rw [← hz0] at hP
    exact hzc.tendsto.eventually hP
  have hL₁ : ∀ᶠ w in 𝓝 (chartAt ℂ (f₁ p) (f₁ p)),
      localMapExpr f₁ p (chartAt ℂ p (f₁.symm ((chartAt ℂ (f₁ p)).symm w))) = w := by
    filter_upwards [hsrc] with w hw
    show chartAt ℂ (f₁ p) (f₁ ((chartAt ℂ p).symm (chartAt ℂ p (f₁.symm ((chartAt ℂ (f₁ p)).symm w))))) = w
    rw [(chartAt ℂ p).left_inv hw.2, f₁.apply_symm_apply, (chartAt ℂ (f₁ p)).right_inv hw.1]
  have hL₂ : ∀ᶠ w in 𝓝 (chartAt ℂ (f₁ p) (f₁ p)),
      localMapExpr f₂ p (chartAt ℂ p (f₁.symm ((chartAt ℂ (f₁ p)).symm w))) =
        chartAt ℂ (f₂ p) ((f₁.symm.trans f₂) ((chartAt ℂ (f₁ p)).symm w)) := by
    filter_upwards [hsrc] with w hw
    show chartAt ℂ (f₂ p) (f₂ ((chartAt ℂ p).symm (chartAt ℂ p (f₁.symm ((chartAt ℂ (f₁ p)).symm w))))) = _
    rw [(chartAt ℂ p).left_inv hw.2]
    rfl
  have hrel : ∀ᶠ w in 𝓝 (chartAt ℂ (f₁ p) (f₁ p)),
      ζ₂' (chartAt ℂ (f₂ p) ((f₁.symm.trans f₂) ((chartAt ℂ (f₁ p)).symm w))) = ε * ζ₁' w := by
    filter_upwards [hL₁, hL₂, hz_ev hrel₁, hz_ev hrel₂, hz_ev hεe] with w h1 h2 h3 h4 h5
    rw [← h2, h4, h5, hS, ← h3, h1]
  have hFc : chartAt ℂ (f₂ p) ((f₁.symm.trans f₂) ((chartAt ℂ (f₁ p)).symm (chartAt ℂ (f₁ p) (f₁ p)))) =
      chartAt ℂ (f₂ p) (f₂ p) := by
    rw [hyy]
    simp
  have hFlcont : ContinuousAt (fun w => chartAt ℂ (f₂ p) ((f₁.symm.trans f₂) ((chartAt ℂ (f₁ p)).symm w)))
      (chartAt ℂ (f₁ p) (f₁ p)) := by
    have hcF : ContinuousAt (fun w => (f₁.symm.trans f₂) ((chartAt ℂ (f₁ p)).symm w)) (chartAt ℂ (f₁ p) (f₁ p)) :=
      ContinuousAt.comp (g := ⇑(f₁.symm.trans f₂)) (f := (chartAt ℂ (f₁ p)).symm)
        (f₁.symm.trans f₂).continuous.continuousAt hs1
    refine ContinuousAt.comp (f := fun w => (f₁.symm.trans f₂) ((chartAt ℂ (f₁ p)).symm w)) ?_ hcF
    have : (f₁.symm.trans f₂) ((chartAt ℂ (f₁ p)).symm (chartAt ℂ (f₁ p) (f₁ p))) = f₂ p := by
      rw [hyy]
      simp
    rw [this]
    exact (chartAt ℂ (f₂ p)).continuousAt (mem_chart_source ℂ (f₂ p))
  have hs₂ : HasStrictDerivAt ζ₂' (deriv ζ₂' (chartAt ℂ (f₂ p) (f₂ p))) (chartAt ℂ (f₂ p) (f₂ p)) :=
    hζ₂'.1.hasStrictDerivAt
  have ha₂ : deriv ζ₂' (chartAt ℂ (f₂ p) (f₂ p)) ≠ 0 := hζ₂'.2.2.1
  have hG := HasStrictDerivAt.to_localInverse hs₂ ha₂
  have hinv := hs₂.eventually_left_inverse ha₂
  have hval : ζ₂' (chartAt ℂ (f₂ p) (f₂ p)) = ε * ζ₁' (chartAt ℂ (f₁ p) (f₁ p)) := by
    have := hrel.self_of_nhds
    rwa [hFc] at this
  have hFlt : Tendsto (fun w => chartAt ℂ (f₂ p) ((f₁.symm.trans f₂) ((chartAt ℂ (f₁ p)).symm w)))
      (𝓝 (chartAt ℂ (f₁ p) (f₁ p))) (𝓝 (chartAt ℂ (f₂ p) (f₂ p))) := by
    convert hFlcont.tendsto using 2
    exact hFc.symm
  have heq : (fun w => chartAt ℂ (f₂ p) ((f₁.symm.trans f₂) ((chartAt ℂ (f₁ p)).symm w))) =ᶠ[𝓝 (chartAt ℂ (f₁ p) (f₁ p))]
      (hs₂.localInverse ζ₂' _ _ ha₂) ∘ (fun w => ε * ζ₁' w) := by
    filter_upwards [hrel, hFlt.eventually hinv] with w h1 h2
    show _ = hs₂.localInverse ζ₂' _ _ ha₂ (ε * ζ₁' w)
    rw [← h1]
    exact h2.symm
  have hGd : DifferentiableAt ℂ (hs₂.localInverse ζ₂' _ _ ha₂) (ε * ζ₁' (chartAt ℂ (f₁ p) (f₁ p))) := by
    rw [← hval]
    exact (HasStrictDerivAt.hasDerivAt hG).differentiableAt
  have hm : DifferentiableAt ℂ (fun w => ε * ζ₁' w) (chartAt ℂ (f₁ p) (f₁ p)) :=
    (differentiableAt_const ε).mul hζ₁'.1.differentiableAt
  have hd : DifferentiableAt ℂ (fun w => chartAt ℂ (f₂ p) ((f₁.symm.trans f₂) ((chartAt ℂ (f₁ p)).symm w)))
      (chartAt ℂ (f₁ p) (f₁ p)) :=
    (DifferentiableAt.comp (f := fun w => ε * ζ₁' w) _ hGd hm).congr_of_eventuallyEq heq
  have hFy : (f₁.symm.trans f₂) (f₁ p) = f₂ p := by simp
  rw [s23_mdifferentiableAt_iff (mem_chart_source ℂ (f₁ p)) (mem_chart_source ℂ ((f₁.symm.trans f₂) (f₁ p)))]
  refine ⟨(f₁.symm.trans f₂).continuous.continuousAt, ?_⟩
  rw [hFy]
  exact hd

/-- Same data: `f₂ ∘ f₁⁻¹` is holomorphic (regular images by `s82td_same_data_mdiff_regular`, the images of the
isolated zeros by `s82td_mdiff_of_punctured`). -/
theorem s82td_same_data_mdiff {X₁ X₂ : Type u} [TopologicalSpace X₁] [ChartedSpace ℂ X₁] [T2Space X₁]
    [IsManifold 𝓘(ℂ) ω X₁] [TopologicalSpace X₂] [ChartedSpace ℂ X₂] [IsManifold 𝓘(ℂ) ω X₂]
    {f₁ : S₀ ≃ₜ X₁} {f₂ : S₀ ≃ₜ X₂} {q : S₀ → ℂ → ℂ} {q₁' : X₁ → ℂ → ℂ} {q₂' : X₂ → ℂ → ℂ} {k : ℝ}
    (h₁ : IsTeichmullerMap f₁ q q₁' k) (h₂ : IsTeichmullerMap f₂ q q₂' k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f₁.symm.trans f₂) := by
  intro y
  obtain ⟨p, rfl⟩ := f₁.surjective y
  by_cases hp : IsRegularPoint q p
  · exact s82td_same_data_mdiff_regular h₁ h₂ hp
  · refine s82td_mdiff_of_punctured (f₁.symm.trans f₂).continuous ?_
    -- near `p` every other point is regular (isolated zeros), and `f₁` maps punctured neighbourhoods to
    -- punctured neighbourhoods
    have hc0 : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    have htn : (chartAt ℂ p).target ∈ 𝓝 (chartAt ℂ p p) := (chartAt ℂ p).open_target.mem_nhds hc0
    have han : AnalyticAt ℂ (q p) (chartAt ℂ p p) := (h₁.initial.2 p).analyticAt htn
    have hiso : ∀ᶠ z in 𝓝[≠] chartAt ℂ p p, q p z ≠ 0 := by
      rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
      · exact absurd (s82td_hol_eq_zero h₁.initial p h) h₁.initial_ne
      · exact h
    have hreg : ∀ᶠ p' in 𝓝[≠] p, IsRegularPoint q p' := by
      have hφ : Tendsto (chartAt ℂ p) (𝓝[≠] p) (𝓝[≠] chartAt ℂ p p) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (((chartAt ℂ p).continuousAt (mem_chart_source ℂ p)).tendsto.mono_left nhdsWithin_le_nhds) ?_
        filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))] with p' hp' hps
        intro he
        apply hp'
        exact (chartAt ℂ p).injOn hps (mem_chart_source ℂ p) he
      filter_upwards [hφ.eventually hiso, hφ.eventually (nhdsWithin_le_nhds htn),
        nhdsWithin_le_nhds ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))] with p' h1 h2 h3
      have := s82td_regular_of_chart h₁.initial p h2 h1
      rwa [(chartAt ℂ p).left_inv h3] at this
    have hf₁ : Tendsto f₁.symm (𝓝[≠] f₁ p) (𝓝[≠] p) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := f₁.symm.continuous.continuousAt (x := f₁ p)
        rw [ContinuousAt, f₁.symm_apply_apply] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        intro he
        have he' : f₁.symm y = p := he
        apply hy
        show y = f₁ p
        rw [← he', f₁.apply_symm_apply]
    filter_upwards [hf₁.eventually hreg] with y hy
    have := s82td_same_data_mdiff_regular h₁ h₂ hy
    rwa [f₁.apply_symm_apply] at this

/-- **[stub C2] Same Teichmüller data give conformally equivalent targets**: if `f₁ : S₀ → X₁` and `f₂ : S₀ → X₂`
are Teichmüller maps with the same initial differential `q` and the same `k`, then `f₂ ∘ f₁⁻¹` is biholomorphic (in
natural parameters `ζ₂' ∘ f₂ = ±ζ₁' ∘ f₁ + c` at regular points; the images of the zeros are isolated, removable). -/
theorem s82td_same_data_biholomorphic {X₁ X₂ : Type u} [TopologicalSpace X₁] [ChartedSpace ℂ X₁] [T2Space X₁]
    [IsManifold 𝓘(ℂ) ω X₁] [TopologicalSpace X₂] [ChartedSpace ℂ X₂] [T2Space X₂] [IsManifold 𝓘(ℂ) ω X₂]
    {f₁ : S₀ ≃ₜ X₁} {f₂ : S₀ ≃ₜ X₂} {q : S₀ → ℂ → ℂ} {q₁' : X₁ → ℂ → ℂ} {q₂' : X₂ → ℂ → ℂ} {k : ℝ}
    (h₁ : IsTeichmullerMap f₁ q q₁' k) (h₂ : IsTeichmullerMap f₂ q q₂' k) : IsBiholomorphic (f₁.symm.trans f₂) := by
  refine ⟨s82td_same_data_mdiff h₁ h₂, f₂.symm.trans f₁, s82td_same_data_mdiff h₂ h₁, fun x => ?_, fun x => ?_⟩
  · simp
  · simp

/-- **[stub C1] `Q̃(S₀)` restricted to the interior is finite dimensional.** -/
theorem s82td_finiteDimensional {g n m : ℕ} (hex : ¬ IsExceptionalType g n m) (F₀ : FiniteTypeStructure S₀ g n m) :
    FiniteDimensional ℝ (admissibleQDInterior F₀) := by
  have hfr := s82td_finrank_interior hex F₀
  by_cases hpos : 0 < Module.finrank ℝ (admissibleQDInterior F₀)
  · exact Module.finite_of_finrank_pos hpos
  · -- dimension `0`: the only non-exceptional type is `(0, 3, 0)`, and for `m = 0` finiteness is §31.1
    have h0 : Module.finrank ℝ (admissibleQDInterior F₀) = 0 := by omega
    rw [h0] at hfr
    have hm : m = 0 := by
      unfold IsExceptionalType at hex
      simp only [Prod.mk.injEq] at hex
      omega
    subst hm
    haveI := k31p_finite_admissible F₀
    have hle : admissibleQDSpace F₀ ≤
        (Submodule.span ℂ (admissibleQDSpace F₀ : Set (F₀.X.carrier → ℂ → ℂ))).restrictScalars ℝ :=
      fun x hx => Submodule.subset_span hx
    haveI : Module.Finite ℂ
        ((Submodule.span ℂ (admissibleQDSpace F₀ : Set (F₀.X.carrier → ℂ → ℂ))).restrictScalars ℝ) :=
      Module.Finite.equiv (Submodule.restrictScalarsEquiv (S := ℝ) (R := ℂ) (M := F₀.X.carrier → ℂ → ℂ)
        (Submodule.span ℂ (admissibleQDSpace F₀ : Set (F₀.X.carrier → ℂ → ℂ)))).symm
    haveI : FiniteDimensional ℝ
        ((Submodule.span ℂ (admissibleQDSpace F₀ : Set (F₀.X.carrier → ℂ → ℂ))).restrictScalars ℝ) :=
      Module.Finite.trans ℂ _
    haveI : FiniteDimensional ℝ (admissibleQDSpace F₀) := Submodule.finiteDimensional_of_le hle
    show FiniteDimensional ℝ ((admissibleQDSpace F₀).map (pullbackQDLinear F₀))
    infer_instance

/-- **[W4, closed case] Realization for `n = m = 0`**: `S₀` is compact (`ι` is onto the closed surface), and the
Teichmüller deformation `S_{q,k}` of §26.2 (`exists_teichDeformation`) with the trivial structure of type `(g, 0, 0)`
is the marked surface. -/
theorem s82td_realize_closed {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (hn : n = 0) (hm : m = 0)
    {q : S₀ → ℂ → ℂ} (hq : q ∈ admissibleQDInterior F₀) (hq0 : q ≠ 0) {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ∃ (A : MarkedFiniteTypeRS S₀ g n m) (q' : A.X.carrier → ℂ → ℂ), IsAdmissibleTeichmullerMap F₀ A.marking q q' k := by
  subst hn
  subst hm
  have hP : F₀.P = ∅ := Finset.card_eq_zero.1 F₀.card_P
  have hsurj : Function.Surjective F₀.ι := by
    intro x
    have hx : x ∈ range F₀.ι := by
      rw [F₀.range_ι, hP]
      simp
    exact hx
  let eι : S₀ ≃ₜ F₀.X.carrier :=
    (Equiv.ofBijective F₀.ι ⟨F₀.embedding.injective, hsurj⟩).toHomeomorphOfContinuousOpen
      F₀.embedding.continuous F₀.embedding.isOpenMap
  haveI : CompactSpace S₀ := eι.symm.compactSpace
  have hqh : IsHolQuadDiff q := (admissibleQDInterior_holomorphic F₀).1 q hq
  obtain ⟨X, e, q', hD⟩ := exists_teichDeformation hqh hq0 hk0.le hk1
  have hT := teichDeformation_isTeichmullerMap hD
  have hgen : HasGenus X.carrier g := hasGenus_of_homeomorph F₀.genus (eι.symm.trans e)
  let Fx : FiniteTypeStructure X.carrier g 0 0 :=
    { X := X
      P := ∅
      D := fun j => Fin.elim0 j
      ι := id
      genus := hgen
      card_P := rfl
      disc := fun j => Fin.elim0 j
      disjoint := fun i => Fin.elim0 i
      disjoint_P := fun j => Fin.elim0 j
      embedding := Topology.IsOpenEmbedding.id
      holomorphic := mdifferentiable_id
      range_ι := by simp }
  exact ⟨⟨⟨X.carrier, Fx⟩, e, hT.qc⟩, q', hq, hT⟩

/-! ### W4(B): punctures (`m = 0`) -/

/-- A local holomorphic square root near `w₁ = t₁² ≠ 0`: a function `R` with `R(w)² = w` near `w₁`, `R(w₁) = t₁`,
and derivative `(2t₁)⁻¹` at `w₁`. -/
theorem s82td_local_sqrt {t₁ : ℂ} (ht₁ : t₁ ≠ 0) :
    ∃ R : ℂ → ℂ, HasDerivAt R (2 * t₁)⁻¹ (t₁ ^ 2) ∧ R (t₁ ^ 2) = t₁ ∧ ∀ᶠ w in 𝓝 (t₁ ^ 2), R w ^ 2 = w := by
  have hd : HasStrictDerivAt (fun t : ℂ => t ^ 2) (2 * t₁) t₁ := by
    simpa using (hasStrictDerivAt_pow 2 t₁)
  have hd0 : (2 * t₁) ≠ 0 := mul_ne_zero two_ne_zero ht₁
  refine ⟨hd.localInverse (fun t : ℂ => t ^ 2) _ _ hd0, (HasStrictDerivAt.to_localInverse hd hd0).hasDerivAt,
    (hd.eventually_left_inverse hd0).self_of_nhds, ?_⟩
  exact hd.eventually_right_inverse hd0

/-- An odd function on a ball is determined on squares: `T(ρ)² = T(ρ')²` when `ρ² = ρ'²`, both in the ball. -/
theorem s82td_odd_sq {T : ℂ → ℂ} {δ : ℝ} (hodd : ∀ t ∈ ball (0 : ℂ) δ, T t = -T (-t)) {ρ ρ' : ℂ}
    (hρ : ρ' ∈ ball (0 : ℂ) δ) (h : ρ ^ 2 = ρ' ^ 2) : T ρ ^ 2 = T ρ' ^ 2 := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h1 | h1
  · rw [h1]
  · have hm : -ρ' ∈ ball (0 : ℂ) δ := by rwa [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff]
    rw [h1, hodd (-ρ') hm, neg_neg, neg_sq]

/-- **[stub B1] Natural parameter at a simple pole**: if `h = c/(z - z₀) + r` near `z₀` with `c ≠ 0` and `r`
analytic, there is `ζ` analytic at `z₀` with `ζ(z₀) = 0`, `ζ'(z₀) ≠ 0` and `h = ζ'²/(4ζ)` off `z₀`, i.e.
`h dz² = ¼ ζ⁻¹ dζ²`. -/
theorem s82td_pole_natural {h r : ℂ → ℂ} {z₀ c : ℂ} (hc : c ≠ 0) (hr : AnalyticAt ℂ r z₀)
    (hev : ∀ᶠ z in 𝓝[≠] z₀, h z = c / (z - z₀) + r z) :
    ∃ ζ : ℂ → ℂ, AnalyticAt ℂ ζ z₀ ∧ ζ z₀ = 0 ∧ deriv ζ z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] z₀, ζ z ≠ 0 ∧ h z = deriv ζ z ^ 2 / (4 * ζ z) := by
  -- the coefficient lifted by `z = z₀ + t²`: `h(z₀ + t²) (2t)² = 4c + 4t² r(z₀ + t²)`, regular at `t = 0`
  set H : ℂ → ℂ := fun t => 4 * c + 4 * t ^ 2 * r (z₀ + t ^ 2) with hH
  have hran : AnalyticAt ℂ (fun t : ℂ => r (z₀ + t ^ 2)) 0 := by
    have h1 : AnalyticAt ℂ (fun t : ℂ => z₀ + t ^ 2) 0 := analyticAt_const.add (analyticAt_id.pow 2)
    exact AnalyticAt.comp_of_eq hr h1 (by simp)
  have hHan : AnalyticAt ℂ H 0 := analyticAt_const.add ((analyticAt_const.mul (analyticAt_id.pow 2)).mul hran)
  have hH0 : H 0 ≠ 0 := by simp [hH, hc]
  obtain ⟨T, hTa, hT0, hTd, hTev⟩ := eq25_2_natural_parameter hHan hH0
  -- `T` is odd near `0` (`H` is even, and a natural parameter is unique up to sign)
  have hHeven : ∀ t, H (-t) = H t := fun t => by simp [hH, neg_sq]
  have hT'a : AnalyticAt ℂ (fun t => -T (-t)) 0 := by
    exact (AnalyticAt.comp_of_eq hTa analyticAt_id.neg (by simp)).neg
  have hT'0 : (fun t => -T (-t)) 0 = 0 := by simp [hT0]
  have hT'ev : ∀ᶠ t in 𝓝 (0 : ℂ), deriv (fun t => -T (-t)) t ^ 2 = H t := by
    have hneg : Tendsto (fun t : ℂ => -t) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : ℂ))
    filter_upwards [hneg.eventually hTev] with t ht
    rw [show (fun t => -T (-t)) = -(fun t => T (-t)) from rfl, deriv.neg, deriv_comp_neg, neg_neg, ht,
      hHeven]
  have hodd : ∀ᶠ t in 𝓝 (0 : ℂ), T t = -T (-t) := by
    rcases eq25_3_natural_parameter_unique hTa hT'a hT0 hT'0 hTev hT'ev hH0 with h | h
    · exact h
    · exfalso
      have h' : T =ᶠ[𝓝 0] fun t => T (-t) := h.mono fun t ht => by simpa using ht
      have hd := h'.deriv_eq
      rw [deriv_comp_neg, neg_zero] at hd
      apply hTd
      linear_combination hd / 2
  -- a ball on which everything holds
  have hTD := hTa.differentiableAt.hasDerivAt
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), T t ≠ 0 := hTD.eventually_ne hTd
  have hshift : Tendsto (fun t : ℂ => z₀ + t ^ 2) (𝓝[≠] 0) (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcz : Continuous (fun t : ℂ => z₀ + t ^ 2) := continuous_const.add (continuous_pow 2)
      have := hcz.tendsto 0
      rw [show z₀ + (0 : ℂ) ^ 2 = z₀ by simp] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      intro he
      apply ht
      have : t ^ 2 = 0 := by
        have := congrArg (fun z => z - z₀) he
        simpa using this
      exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this
  have hshift' : Tendsto (fun t : ℂ => z₀ + t ^ 2) (𝓝 0) (𝓝 z₀) := by
    have hcz : Continuous (fun t : ℂ => z₀ + t ^ 2) := continuous_const.add (continuous_pow 2)
    have := hcz.tendsto 0
    rwa [show z₀ + (0 : ℂ) ^ 2 = z₀ by simp] at this
  have hall : ∀ᶠ t in 𝓝 (0 : ℂ), T t = -T (-t) ∧ AnalyticAt ℂ T t ∧ deriv T t ^ 2 = H t ∧
      (t ≠ 0 → T t ≠ 0) ∧ (t ≠ 0 → h (z₀ + t ^ 2) = c / (z₀ + t ^ 2 - z₀) + r (z₀ + t ^ 2)) := by
    filter_upwards [hodd, hTa.eventually_analyticAt, hTev, eventually_nhdsWithin_iff.1 hne,
      eventually_nhdsWithin_iff.1 (hshift.eventually hev)] with t h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hall
  -- the function `ζ(z) = T(√(z - z₀))²`
  have hsq : ∀ w : ℂ, (w ^ (2⁻¹ : ℂ)) ^ 2 = w := by
    intro w
    have hs := Complex.cpow_nat_inv_pow w (n := 2) two_ne_zero
    push_cast at hs
    exact hs
  have hinball : ∀ ρ : ℂ, ‖ρ ^ 2‖ < δ ^ 2 → ρ ∈ ball (0 : ℂ) δ := by
    intro ρ hρ
    rw [mem_ball_zero_iff]
    rw [norm_pow] at hρ
    by_contra hc'
    push_neg at hc'
    nlinarith [norm_nonneg ρ]
  set ζ : ℂ → ℂ := fun z => T ((z - z₀) ^ (2⁻¹ : ℂ)) ^ 2 with hζdef
  have hbranch : ∀ z ρ, ‖z - z₀‖ < δ ^ 2 → ρ ^ 2 = z - z₀ → ζ z = T ρ ^ 2 := by
    intro z ρ hz hρ
    have hb : ρ ∈ ball (0 : ℂ) δ := hinball ρ (by rw [hρ]; exact hz)
    exact s82td_odd_sq (fun t ht => (hball t ht).1) hb ((hsq _).trans hρ.symm)
  -- the derivative off `z₀`
  have hderiv : ∀ z₁, z₁ ≠ z₀ → ‖z₁ - z₀‖ < δ ^ 2 → ∃ t₁ : ℂ, t₁ ≠ 0 ∧ t₁ ∈ ball (0 : ℂ) δ ∧ t₁ ^ 2 = z₁ - z₀ ∧
      HasDerivAt ζ (2 * T t₁ * (deriv T t₁ * (2 * t₁)⁻¹)) z₁ := by
    intro z₁ hz₁ hzδ
    set t₁ := (z₁ - z₀) ^ (2⁻¹ : ℂ) with ht₁def
    have ht₁sq : t₁ ^ 2 = z₁ - z₀ := hsq _
    have ht₁0 : t₁ ≠ 0 := by
      intro h0
      apply hz₁
      rw [h0] at ht₁sq
      linear_combination -ht₁sq
    have ht₁b : t₁ ∈ ball (0 : ℂ) δ := hinball t₁ (by rw [ht₁sq]; exact hzδ)
    obtain ⟨R, hRd, hR1, hRev⟩ := s82td_local_sqrt ht₁0
    rw [ht₁sq] at hRd hR1 hRev
    have hopen : ∀ᶠ z in 𝓝 z₁, ‖z - z₀‖ < δ ^ 2 :=
      (isOpen_lt (continuous_norm.comp (continuous_sub_right z₀)) continuous_const).mem_nhds hzδ
    have hsub : Tendsto (fun z => z - z₀) (𝓝 z₁) (𝓝 (z₁ - z₀)) := (continuous_sub_right z₀).tendsto z₁
    have heq : (fun z => T (R (z - z₀)) ^ 2) =ᶠ[𝓝 z₁] ζ := by
      filter_upwards [hsub.eventually hRev, hopen] with z hz1 hz2
      exact (hbranch z (R (z - z₀)) hz2 hz1).symm
    have hR' : HasDerivAt (fun z => R (z - z₀)) (2 * t₁)⁻¹ z₁ := hRd.comp_sub_const z₁ z₀
    have hTt : HasDerivAt T (deriv T t₁) (R (z₁ - z₀)) := by
      rw [hR1]
      exact (hball t₁ ht₁b).2.1.differentiableAt.hasDerivAt
    have hc2 := (hTt.comp z₁ hR').pow 2
    refine ⟨t₁, ht₁0, ht₁b, ht₁sq, ?_⟩
    have hc3 := hc2.congr_of_eventuallyEq heq.symm
    convert hc3 using 1
    simp only [Function.comp_apply, hR1]
    push_cast
    ring
  -- `ζ` is holomorphic near `z₀` (removable singularity)
  have hball2 : ball z₀ (δ ^ 2) ∈ 𝓝 z₀ := ball_mem_nhds z₀ (by positivity)
  have hcont0 : ContinuousAt ζ z₀ := by
    have hc : ContinuousAt (fun z : ℂ => (z - z₀) ^ (2⁻¹ : ℂ)) z₀ := by
      have h1 : ContinuousAt (fun w : ℂ => w ^ (2⁻¹ : ℂ)) (z₀ - z₀) := by
        rw [sub_self]
        exact continuousAt_cpow_const_of_re_pos (Or.inl le_rfl) (by norm_num)
      exact ContinuousAt.comp (f := fun z => z - z₀) h1 (continuous_sub_right z₀).continuousAt
    have h00 : (z₀ - z₀) ^ (2⁻¹ : ℂ) = 0 := by rw [sub_self, Complex.zero_cpow (by norm_num)]
    have hT0c : ContinuousAt T ((z₀ - z₀) ^ (2⁻¹ : ℂ)) := by
      rw [h00]
      exact hTa.continuousAt
    exact (ContinuousAt.comp (f := fun z : ℂ => (z - z₀) ^ (2⁻¹ : ℂ)) hT0c hc).pow 2
  have hdon : DifferentiableOn ℂ ζ (ball z₀ (δ ^ 2) \ {z₀}) := by
    intro z hz
    obtain ⟨t₁, -, -, -, hd⟩ := hderiv z hz.2 (by simpa [dist_eq_norm] using hz.1)
    exact hd.differentiableAt.differentiableWithinAt
  have hDs := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hball2).1 ⟨hdon, hcont0⟩
  have hζa : AnalyticAt ℂ ζ z₀ := hDs.analyticAt hball2
  have hζ0 : ζ z₀ = 0 := by
    show T ((z₀ - z₀) ^ (2⁻¹ : ℂ)) ^ 2 = 0
    rw [sub_self, Complex.zero_cpow (by norm_num), hT0]
    norm_num
  -- `ζ'(z₀) = T'(0)² ≠ 0`, through slopes
  have hslope : slope ζ z₀ = fun z => slope T 0 ((z - z₀) ^ (2⁻¹ : ℂ)) ^ 2 := by
    funext z
    rw [slope_def_field, slope_def_field, hζ0, hT0, sub_zero, sub_zero, sub_zero, div_pow]
    show T ((z - z₀) ^ (2⁻¹ : ℂ)) ^ 2 / (z - z₀) = T ((z - z₀) ^ (2⁻¹ : ℂ)) ^ 2 / ((z - z₀) ^ (2⁻¹ : ℂ)) ^ 2
    rw [hsq]
  have hρ : Tendsto (fun z : ℂ => (z - z₀) ^ (2⁻¹ : ℂ)) (𝓝[≠] z₀) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h1 : ContinuousAt (fun w : ℂ => w ^ (2⁻¹ : ℂ)) (z₀ - z₀) := by
        rw [sub_self]
        exact continuousAt_cpow_const_of_re_pos (Or.inl le_rfl) (by norm_num)
      have h2 := (ContinuousAt.comp (f := fun z => z - z₀) h1 (continuous_sub_right z₀).continuousAt).tendsto
      rw [Function.comp_apply, sub_self, Complex.zero_cpow (by norm_num)] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      intro h0
      apply hz
      have := hsq (z - z₀)
      rw [show (z - z₀) ^ (2⁻¹ : ℂ) = 0 from h0] at this
      have h3 : z - z₀ = 0 := by rw [← this]; norm_num
      exact sub_eq_zero.1 h3
  have hlim1 : Tendsto (slope ζ z₀) (𝓝[≠] z₀) (𝓝 (deriv ζ z₀)) :=
    hζa.differentiableAt.hasDerivAt.tendsto_slope
  have hlim2 : Tendsto (slope ζ z₀) (𝓝[≠] z₀) (𝓝 (deriv T 0 ^ 2)) := by
    rw [hslope]
    exact ((hTD.tendsto_slope.comp hρ).pow 2)
  have hdz : deriv ζ z₀ = deriv T 0 ^ 2 := tendsto_nhds_unique hlim1 hlim2
  refine ⟨ζ, hζa, hζ0, by rw [hdz]; exact pow_ne_zero 2 hTd, ?_⟩
  -- the identity `h = ζ'²/(4ζ)` off `z₀`
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hball2] with z hz hzb
  have hzδ : ‖z - z₀‖ < δ ^ 2 := by simpa [dist_eq_norm] using hzb
  obtain ⟨t₁, ht₁0, ht₁b, ht₁sq, hd⟩ := hderiv z hz hzδ
  have hζz : ζ z = T t₁ ^ 2 := hbranch z t₁ hzδ ht₁sq
  obtain ⟨-, -, hTH, hTne, hhz⟩ := hball t₁ ht₁b
  have hT1 : T t₁ ≠ 0 := hTne ht₁0
  have hz' : z = z₀ + t₁ ^ 2 := by rw [ht₁sq]; ring
  refine ⟨by rw [hζz]; exact pow_ne_zero 2 hT1, ?_⟩
  rw [hd.deriv, hζz]
  have hh := hhz ht₁0
  rw [← hz'] at hh
  rw [hh]
  have hrz : r z = r (z₀ + t₁ ^ 2) := by rw [← hz']
  have hH1 : deriv T t₁ ^ 2 = 4 * c + 4 * t₁ ^ 2 * r z := by rw [hTH, hrz]
  have hzz : z - z₀ = t₁ ^ 2 := ht₁sq.symm
  rw [hzz]
  have e1 : (2 * T t₁ * (deriv T t₁ * (2 * t₁)⁻¹)) ^ 2 / (4 * T t₁ ^ 2) = deriv T t₁ ^ 2 / (4 * t₁ ^ 2) := by
    field_simp
    try ring
  rw [e1, hH1]
  field_simp
  try ring

/-- For an odd `G`, `G(√w)²` does not depend on the choice of the square root. -/
theorem s82td_sqrt_branch {G : ℂ → ℂ} (hodd : ∀ t, G (-t) = -G t) {w r : ℂ} (h : r ^ 2 = w) :
    G (w ^ (2⁻¹ : ℂ)) ^ 2 = G r ^ 2 := by
  have hs := Complex.cpow_nat_inv_pow w (n := 2) two_ne_zero
  push_cast at hs
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hs.trans h.symm) with h1 | h1
  · rw [h1]
  · rw [h1, hodd, neg_sq]

/-- For a continuous odd `G`, `w ↦ G(√w)²` is continuous: near `w₀ ≠ 0` it is `G(R w)²` for a continuous local
square root `R`, and at `0` it tends to `G(0)² = 0`. -/
theorem s82td_sqrt_continuous {G : ℂ → ℂ} (hG : Continuous G) (hodd : ∀ t, G (-t) = -G t) :
    Continuous (fun w : ℂ => G (w ^ (2⁻¹ : ℂ)) ^ 2) := by
  have hG0 : G 0 = 0 := by
    have h := hodd 0
    rw [neg_zero] at h
    linear_combination h / 2
  rw [continuous_iff_continuousAt]
  intro w₀
  by_cases hw₀ : w₀ = 0
  · subst hw₀
    have hc : ContinuousAt (fun w : ℂ => w ^ (2⁻¹ : ℂ)) 0 :=
      continuousAt_cpow_const_of_re_pos (Or.inl le_rfl) (by norm_num)
    have h00 : (0 : ℂ) ^ (2⁻¹ : ℂ) = 0 := Complex.zero_cpow (by norm_num)
    have h1 : ContinuousAt (fun w : ℂ => G (w ^ (2⁻¹ : ℂ))) 0 := by
      refine ContinuousAt.comp (f := fun w : ℂ => w ^ (2⁻¹ : ℂ)) ?_ hc
      exact hG.continuousAt
    exact h1.pow 2
  · set t₀ := w₀ ^ (2⁻¹ : ℂ) with ht₀
    have hsq : t₀ ^ 2 = w₀ := by
      have hs := Complex.cpow_nat_inv_pow w₀ (n := 2) two_ne_zero
      push_cast at hs
      exact hs
    have ht0 : t₀ ≠ 0 := by
      intro h
      apply hw₀
      rw [← hsq, h]
      norm_num
    have hd : HasStrictDerivAt (fun t : ℂ => t ^ 2) (2 * t₀) t₀ := by
      simpa using (hasStrictDerivAt_pow 2 t₀)
    have hd0 : (2 * t₀) ≠ 0 := mul_ne_zero two_ne_zero ht0
    have hR := HasStrictDerivAt.to_localInverse hd hd0
    have hri := hd.eventually_right_inverse hd0
    have hRc : ContinuousAt (hd.localInverse (fun t : ℂ => t ^ 2) _ _ hd0) w₀ := by
      have := (HasStrictDerivAt.hasDerivAt hR).continuousAt
      rwa [hsq] at this
    have hri' : ∀ᶠ y in 𝓝 w₀, hd.localInverse (fun t : ℂ => t ^ 2) _ _ hd0 y ^ 2 = y := by
      rw [← hsq]
      exact hri
    have heq : (fun w : ℂ => G (w ^ (2⁻¹ : ℂ)) ^ 2) =ᶠ[𝓝 w₀]
        fun w => G (hd.localInverse (fun t : ℂ => t ^ 2) _ _ hd0 w) ^ 2 := by
      filter_upwards [hri'] with w hw
      exact s82td_sqrt_branch hodd hw
    refine ContinuousAt.congr ?_ heq.symm
    exact (ContinuousAt.comp (f := hd.localInverse (fun t : ℂ => t ^ 2) _ _ hd0) hG.continuousAt hRc).pow 2

/-- **[stub B2] The stretch at a simple pole**: a homeomorphism `𝒫` of `ℂ` with `𝒫(t²) = S_k(t)²` (well defined
since the stretch `S_k` is odd). -/
theorem s82td_pole_stretch {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) :
    ∃ P : ℂ ≃ₜ ℂ, P 0 = 0 ∧ ∀ t : ℂ, P (t ^ 2) = teichStretch k t ^ 2 := by
  set T := s26d_a_T hk₀ hk 0 with hT_def
  have hT : ∀ x, T x = teichStretch k x := fun x => by
    show teichStretchZero k 0 x = _
    rw [s26d_a_teichStretchZero_zero]
  have hSodd : ∀ t, teichStretch k (-t) = -teichStretch k t := by
    intro t
    simp only [teichStretch, map_neg]
    ring
  have hTodd : ∀ x, T.symm (-x) = -T.symm x := by
    intro x
    apply T.injective
    rw [T.apply_symm_apply, hT, hSodd, ← hT, T.apply_symm_apply]
  have hsq : ∀ w : ℂ, (w ^ (2⁻¹ : ℂ)) ^ 2 = w := by
    intro w
    have hs := Complex.cpow_nat_inv_pow w (n := 2) two_ne_zero
    push_cast at hs
    exact hs
  have hP : ∀ t : ℂ, teichStretch k ((t ^ 2) ^ (2⁻¹ : ℂ)) ^ 2 = teichStretch k t ^ 2 :=
    fun t => s82td_sqrt_branch hSodd rfl
  have hQ : ∀ t : ℂ, T.symm ((t ^ 2) ^ (2⁻¹ : ℂ)) ^ 2 = T.symm t ^ 2 :=
    fun t => s82td_sqrt_branch hTodd rfl
  have hPQ : ∀ w : ℂ, teichStretch k ((T.symm (w ^ (2⁻¹ : ℂ)) ^ 2) ^ (2⁻¹ : ℂ)) ^ 2 = w := by
    intro w
    rw [hP, ← hT, T.apply_symm_apply, hsq]
  have hQP : ∀ w : ℂ, T.symm ((teichStretch k (w ^ (2⁻¹ : ℂ)) ^ 2) ^ (2⁻¹ : ℂ)) ^ 2 = w := by
    intro w
    rw [hQ, ← hT, T.symm_apply_apply, hsq]
  refine ⟨⟨⟨fun w => teichStretch k (w ^ (2⁻¹ : ℂ)) ^ 2, fun w => T.symm (w ^ (2⁻¹ : ℂ)) ^ 2, hQP, hPQ⟩,
    s82td_sqrt_continuous (s26d_a_continuous_teichStretch k) hSodd,
    s82td_sqrt_continuous T.symm.continuous hTodd⟩, ?_, hP⟩
  show teichStretch k ((0 : ℂ) ^ (2⁻¹ : ℂ)) ^ 2 = 0
  rw [Complex.zero_cpow (by norm_num)]
  simp [teichStretch]

/-- An analytic square root near `t₁² ≠ 0`: `R(w) = t₁ (w/t₁²)^{1/2}`, with `R(t₁²) = t₁`, `R' ≠ 0`, `R(w)² = w`, and
`R(t²) = t` for `t` near `t₁`. -/
theorem s82td_sqrt_analytic {t₁ : ℂ} (ht₁ : t₁ ≠ 0) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R (t₁ ^ 2) ∧ R (t₁ ^ 2) = t₁ ∧ deriv R (t₁ ^ 2) ≠ 0 ∧ (∀ w, R w ^ 2 = w) ∧
      ∀ᶠ t in 𝓝 t₁, R (t ^ 2) = t := by
  have ht₂ : t₁ ^ 2 ≠ 0 := pow_ne_zero 2 ht₁
  have hsq : ∀ w : ℂ, (w ^ (2⁻¹ : ℂ)) ^ 2 = w := by
    intro w
    have hs := Complex.cpow_nat_inv_pow w (n := 2) two_ne_zero
    push_cast at hs
    exact hs
  set R : ℂ → ℂ := fun w => t₁ * (w / t₁ ^ 2) ^ (2⁻¹ : ℂ) with hR
  have hRsq : ∀ w, R w ^ 2 = w := by
    intro w
    show (t₁ * (w / t₁ ^ 2) ^ (2⁻¹ : ℂ)) ^ 2 = w
    rw [mul_pow, hsq]
    field_simp
  have hR1 : R (t₁ ^ 2) = t₁ := by
    show t₁ * (t₁ ^ 2 / t₁ ^ 2) ^ (2⁻¹ : ℂ) = t₁
    rw [div_self ht₂, Complex.one_cpow, mul_one]
  have hRa : AnalyticAt ℂ R (t₁ ^ 2) := by
    refine analyticAt_const.mul (AnalyticAt.cpow
      (analyticAt_id.div_const : AnalyticAt ℂ (fun w : ℂ => w / t₁ ^ 2) (t₁ ^ 2)) analyticAt_const ?_)
    show t₁ ^ 2 / t₁ ^ 2 ∈ Complex.slitPlane
    rw [div_self ht₂]
    exact Complex.one_mem_slitPlane
  have hRd : deriv R (t₁ ^ 2) ≠ 0 := by
    intro h0
    have h1 : HasDerivAt (fun w => R w ^ 2) (((2 : ℕ) : ℂ) * R (t₁ ^ 2) ^ (2 - 1) * deriv R (t₁ ^ 2)) (t₁ ^ 2) :=
      hRa.differentiableAt.hasDerivAt.pow 2
    have h2 : (fun w => R w ^ 2) = id := funext hRsq
    rw [h2, h0, mul_zero] at h1
    exact zero_ne_one (h1.unique (hasDerivAt_id _))
  refine ⟨R, hRa, hR1, hRd, hRsq, ?_⟩
  -- the branch through `t₁`
  have hcont : ContinuousAt (fun t : ℂ => R (t ^ 2)) t₁ :=
    ContinuousAt.comp (g := R) (f := fun t : ℂ => t ^ 2) hRa.continuousAt (continuous_pow 2).continuousAt
  have hpos : 0 < ‖t₁‖ / 2 := by positivity
  have h1 : ∀ᶠ t in 𝓝 t₁, ‖R (t ^ 2) - t₁‖ < ‖t₁‖ / 2 := by
    have := Metric.tendsto_nhds.1 hcont.tendsto (‖t₁‖ / 2) hpos
    filter_upwards [this] with t ht
    rwa [dist_eq_norm, hR1] at ht
  have h2 : ∀ᶠ t in 𝓝 t₁, ‖t - t₁‖ < ‖t₁‖ / 2 := by
    filter_upwards [Metric.ball_mem_nhds t₁ hpos] with t ht
    rwa [mem_ball, dist_eq_norm] at ht
  filter_upwards [h1, h2] with t ht1 ht2
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 ((hRsq (t ^ 2)).trans rfl) with h | h
  · exact h
  · exfalso
    rw [h] at ht1
    have h3 : ‖t₁ + t₁‖ ≤ ‖-t - t₁‖ + ‖t - t₁‖ := by
      calc ‖t₁ + t₁‖ = ‖-(-t - t₁) - (t - t₁)‖ := by congr 1; ring
        _ ≤ ‖-(-t - t₁)‖ + ‖t - t₁‖ := norm_sub_le _ _
        _ = ‖-t - t₁‖ + ‖t - t₁‖ := by rw [norm_neg]
    have h4 : ‖t₁ + t₁‖ = 2 * ‖t₁‖ := by
      rw [← two_mul, norm_mul]
      norm_num
    linarith

/-- **Holomorphic compatibility from matched branches.**  If near `y` both charts satisfy `N₁ ∘ φ₁ = S_k ∘ W₁` and
`N₂ ∘ φ₂ = S_k ∘ W₂` (`N₁` holomorphic with `N₁' ≠ 0`, `N₂` holomorphic), and the natural parameters agree up to sign
and a constant, `W₁ = ε W₂ + c`, then `φ₁ ∘ φ₂⁻¹` is holomorphic at `φ₂ y` (as in `s26d_a_transition`). -/
theorem s82td_compat_of_branches {X : Type*} [TopologicalSpace X] {φ₁ φ₂ : OpenPartialHomeomorph X ℂ} {y : X}
    (hy₁ : y ∈ φ₁.source) (hy₂ : y ∈ φ₂.source) {k : ℝ} {N₁ N₂ : ℂ → ℂ} {W₁ W₂ : X → ℂ} {ε c : ℂ}
    (hε : ε = 1 ∨ ε = -1) (hN₁ : AnalyticAt ℂ N₁ (φ₁ y)) (hN₁' : deriv N₁ (φ₁ y) ≠ 0)
    (hN₂ : AnalyticAt ℂ N₂ (φ₂ y)) (h₁ : ∀ᶠ y' in 𝓝 y, N₁ (φ₁ y') = teichStretch k (W₁ y'))
    (h₂ : ∀ᶠ y' in 𝓝 y, N₂ (φ₂ y') = teichStretch k (W₂ y')) (hW : ∀ᶠ y' in 𝓝 y, W₁ y' = ε * W₂ y' + c) :
    DifferentiableAt ℂ (fun w => φ₁ (φ₂.symm w)) (φ₂ y) := by
  have hrel : ∀ᶠ y' in 𝓝 y, N₁ (φ₁ y') = ε * N₂ (φ₂ y') + teichStretch k c := by
    filter_upwards [h₁, h₂, hW] with y' a b d
    rw [a, b, ← eq26_4 k ε hε]
    exact congrArg (teichStretch k) d
  have hw : φ₂ y ∈ φ₂.target := φ₂.map_source hy₂
  have hsy : φ₂.symm (φ₂ y) = y := φ₂.left_inv hy₂
  have ht : Tendsto φ₂.symm (𝓝 (φ₂ y)) (𝓝 y) := by
    have := (φ₂.continuousAt_symm hw).tendsto
    rwa [hsy] at this
  have hrelw : ∀ᶠ v in 𝓝 (φ₂ y), N₁ (φ₁ (φ₂.symm v)) = ε * N₂ v + teichStretch k c := by
    filter_upwards [ht.eventually hrel, φ₂.open_target.mem_nhds hw] with v hv1 hv2
    rwa [φ₂.right_inv hv2] at hv1
  have hτc : ContinuousAt (fun v => φ₁ (φ₂.symm v)) (φ₂ y) := by
    refine ContinuousAt.comp (g := φ₁) (f := φ₂.symm) ?_ (φ₂.continuousAt_symm hw)
    rw [hsy]
    exact φ₁.continuousAt hy₁
  have hN1 : AnalyticAt ℂ N₁ ((fun v => φ₁ (φ₂.symm v)) (φ₂ y)) := by
    show AnalyticAt ℂ N₁ (φ₁ (φ₂.symm (φ₂ y)))
    rw [hsy]
    exact hN₁
  have hN1' : deriv N₁ ((fun v => φ₁ (φ₂.symm v)) (φ₂ y)) ≠ 0 := by
    show deriv N₁ (φ₁ (φ₂.symm (φ₂ y))) ≠ 0
    rw [hsy]
    exact hN₁'
  have hF : DifferentiableAt ℂ (fun v => ε * N₂ v + teichStretch k c) (φ₂ y) :=
    ((differentiableAt_const ε).mul hN₂.differentiableAt).add_const _
  exact s26d_a_differentiableAt_of_comp hτc hN1 hN1' hF hrelw

/-- Uniqueness of natural parameters, read on `X` through `ι`: two functions on `X` whose pull-backs are natural
parameters of `q` at a regular point `x` agree up to sign and a constant near `ι x`. -/
theorem s82td_iota_natural_unique {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) {q : S₀ → ℂ → ℂ} {x : S₀}
    (hx : IsRegularPoint q x) {W W' : F₀.X.carrier → ℂ}
    (hW : AnalyticAt ℂ (fun z => W (F₀.ι ((chartAt ℂ x).symm z))) (chartAt ℂ x x))
    (hWd : ∀ᶠ z in 𝓝 (chartAt ℂ x x), deriv (fun z => W (F₀.ι ((chartAt ℂ x).symm z))) z ^ 2 = q x z)
    (hW' : AnalyticAt ℂ (fun z => W' (F₀.ι ((chartAt ℂ x).symm z))) (chartAt ℂ x x))
    (hWd' : ∀ᶠ z in 𝓝 (chartAt ℂ x x), deriv (fun z => W' (F₀.ι ((chartAt ℂ x).symm z))) z ^ 2 = q x z) :
    ∃ ε c : ℂ, (ε = 1 ∨ ε = -1) ∧ ∀ᶠ y in 𝓝 (F₀.ι x), W y = ε * W' y + c := by
  obtain ⟨ε, c, hε, h⟩ := s26d_a_natural_unique (W := fun y => W (F₀.ι y)) (W' := fun y => W' (F₀.ι y)) hx hW hWd
    hW' hWd'
  refine ⟨ε, c, hε, ?_⟩
  rw [← F₀.embedding.map_nhds_eq x]
  exact Filter.eventually_map.2 h

/-- **Matched branches for the transported §26.2 charts.**  At a regular point `x` in the source of `ψ_s`, there are
`N` holomorphic with `N' ≠ 0` at `ψ_s(x)` and `W` on `X` with `N ∘ Ψ_s = S_k ∘ W` near `ι x` (`Ψ_s = ψ_s ∘ ι⁻¹`) and
`W ∘ ι` a natural parameter of `q` at `x`. -/
theorem s82td_psi_branch {g n m' : ℕ} (F₀ : FiniteTypeStructure S₀ g n m') {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) {m : S₀ → ℕ} {ζ : S₀ → ℂ → ℂ} {Z : S₀ → OpenPartialHomeomorph ℂ ℂ}
    (hD : ∀ s, s26d_a_Data q s (m s) (ζ s) (Z s)) (s : S₀) {x : S₀}
    (hx : x ∈ (s26d_a_psi hk₀ hk m Z s).source) (hreg : IsRegularPoint q x) :
    ∃ (N : ℂ → ℂ) (W : F₀.X.carrier → ℂ), AnalyticAt ℂ N (s26d_a_psi hk₀ hk m Z s x) ∧
      deriv N (s26d_a_psi hk₀ hk m Z s x) ≠ 0 ∧
      (∀ᶠ y in 𝓝 (F₀.ι x), N (((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans
        (s26d_a_psi hk₀ hk m Z s)) y) = teichStretch k (W y)) ∧
      AnalyticAt ℂ (fun z => W (F₀.ι ((chartAt ℂ x).symm z))) (chartAt ℂ x x) ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ x x), deriv (fun z => W (F₀.ι ((chartAt ℂ x).symm z))) z ^ 2 = q x z := by
  obtain ⟨hx1, hx2⟩ := (s26d_a_psi_source hk₀ hk m Z s x).1 hx
  obtain ⟨h, N, hh, hhd, hN, hNd0, -, hNT⟩ :=
    s26d_a_branches hk₀ hk (m s) (s26d_a_ne_zero_of_mem hk₀ hk hD s hx hreg)
  obtain ⟨hWa, hWd⟩ := s26d_a_W_natural hq (hD s) hx1 hx2 hh hhd
  have hψx : s26d_a_psi hk₀ hk m Z s x = teichStretchZero k (m s) (ζ s (chartAt ℂ s x)) := by
    rw [s26d_a_psi_apply, (hD s).coe]
  set ιe := F₀.embedding.toOpenPartialHomeomorph F₀.ι with hιe
  have hleft : ∀ y : S₀, ιe.symm (F₀.ι y) = y := fun y => F₀.embedding.toOpenPartialHomeomorph_left_inv F₀.ι
  refine ⟨N, fun y => h (ζ s (chartAt ℂ s (ιe.symm y))), by rw [hψx]; exact hN, by rw [hψx]; exact hNd0, ?_, ?_, ?_⟩
  · -- `N ∘ ψ_s = S_k ∘ h ∘ ζ_s ∘ φ_s` near `x`, transported by `ι`
    have hc : Tendsto (fun y => ζ s (chartAt ℂ s y)) (𝓝 x) (𝓝 (ζ s (chartAt ℂ s x))) :=
      ((hD s).analytic _ hx2).continuousAt.tendsto.comp ((chartAt ℂ s).continuousAt hx1).tendsto
    have hS : ∀ᶠ y in 𝓝 x, N (s26d_a_psi hk₀ hk m Z s y) = teichStretch k (h (ζ s (chartAt ℂ s y))) := by
      filter_upwards [hc.eventually hNT] with y hy
      rw [s26d_a_psi_apply, (hD s).coe]
      exact hy
    rw [← F₀.embedding.map_nhds_eq x]
    refine Filter.eventually_map.2 (hS.mono fun y hy => ?_)
    show N ((s26d_a_psi hk₀ hk m Z s) (ιe.symm (F₀.ι y))) = teichStretch k (h (ζ s (chartAt ℂ s (ιe.symm (F₀.ι y)))))
    rw [hleft]
    exact hy
  · have : (fun z => h (ζ s (chartAt ℂ s (ιe.symm (F₀.ι ((chartAt ℂ x).symm z)))))) =
        fun z => h (ζ s (chartAt ℂ s ((chartAt ℂ x).symm z))) := by
      funext z
      rw [hleft]
    rw [this]
    exact hWa
  · have : (fun z => h (ζ s (chartAt ℂ s (ιe.symm (F₀.ι ((chartAt ℂ x).symm z)))))) =
        fun z => h (ζ s (chartAt ℂ s ((chartAt ℂ x).symm z))) := by
      funext z
      rw [hleft]
    rw [this]
    exact hWd

/-- The coordinate change `τ = φ_p ∘ ι ∘ φ_x⁻¹` has nonzero derivative at `φ_x(x)` (its inverse `φ_x ∘ ι⁻¹ ∘ φ_p⁻¹`
is holomorphic, `ι` being a holomorphic open embedding). -/
theorem s82td_tau_deriv_ne_zero {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (p : F₀.X.carrier) (x : S₀)
    (hx : F₀.ι x ∈ (chartAt ℂ p).source) :
    deriv (fun v => chartAt ℂ p (F₀.ι ((chartAt ℂ x).symm v))) (chartAt ℂ x x) ≠ 0 := by
  have hc : chartAt ℂ x x ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have hxx : (chartAt ℂ x).symm (chartAt ℂ x x) = x := (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have hτ : DifferentiableAt ℂ (fun v => chartAt ℂ p (F₀.ι ((chartAt ℂ x).symm v))) (chartAt ℂ x x) :=
    s32p_T_differentiableAt F₀ p x hc (by rw [hxx]; exact hx)
  set ιe := F₀.embedding.toOpenPartialHomeomorph F₀.ι with hιe
  have hleft : ∀ y : S₀, ιe.symm (F₀.ι y) = y := fun y => F₀.embedding.toOpenPartialHomeomorph_left_inv F₀.ι
  have hinvm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ιe.symm (F₀.ι x) :=
    s31qr_open_embedding_inverse F₀.embedding F₀.holomorphic (mem_range_self x)
  have hk : DifferentiableAt ℂ (fun u => chartAt ℂ x (ιe.symm ((chartAt ℂ p).symm u))) (chartAt ℂ p (F₀.ι x)) := by
    have h1 := (s23_mdifferentiableAt_iff (x := p) (y := x) hx (by rw [hleft]; exact mem_chart_source ℂ x)).1 hinvm
    exact h1.2
  have hτc : (fun v => chartAt ℂ p (F₀.ι ((chartAt ℂ x).symm v))) (chartAt ℂ x x) = chartAt ℂ p (F₀.ι x) := by
    show chartAt ℂ p (F₀.ι ((chartAt ℂ x).symm (chartAt ℂ x x))) = _
    rw [hxx]
  refine s23_deriv_ne_zero hτ (by rw [hxx]; exact hk) ?_
  have hcont : ContinuousAt (fun v => F₀.ι ((chartAt ℂ x).symm v)) (chartAt ℂ x x) :=
    ContinuousAt.comp (g := F₀.ι) (f := (chartAt ℂ x).symm) F₀.embedding.continuous.continuousAt
      ((chartAt ℂ x).continuousAt_symm hc)
  have hsrc : ∀ᶠ v in 𝓝 (chartAt ℂ x x), F₀.ι ((chartAt ℂ x).symm v) ∈ (chartAt ℂ p).source := by
    refine hcont.preimage_mem_nhds ((chartAt ℂ p).open_source.mem_nhds ?_)
    show F₀.ι ((chartAt ℂ x).symm (chartAt ℂ x x)) ∈ _
    rw [hxx]
    exact hx
  filter_upwards [hsrc, (chartAt ℂ x).open_target.mem_nhds hc] with v hv1 hv2
  show chartAt ℂ x (ιe.symm ((chartAt ℂ p).symm (chartAt ℂ p (F₀.ι ((chartAt ℂ x).symm v))))) = v
  rw [(chartAt ℂ p).left_inv hv1, hleft, (chartAt ℂ x).right_inv hv2]

/-- Near a puncture, chart points avoid the (closed, finitely many) holes. -/
theorem s82td_eventually_notD {g n mh : ℕ} (F₀ : FiniteTypeStructure S₀ g n mh) {p : F₀.X.carrier}
    (hp : p ∈ F₀.P) : ∀ᶠ z in 𝓝 (chartAt ℂ p p), (chartAt ℂ p).symm z ∉ ⋃ j, F₀.D j := by
  have hcl : IsClosed (⋃ j, F₀.D j) :=
    isClosed_iUnion_of_finite fun j => (s31eg_disc_compact (F₀.disc j)).isClosed
  have hzp := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  refine ((chartAt ℂ p).continuousAt_symm hzp).preimage_mem_nhds (hcl.isOpen_compl.mem_nhds ?_)
  rw [mem_compl_iff, (chartAt ℂ p).left_inv (mem_chart_source ℂ p), mem_iUnion]
  rintro ⟨j, hj⟩
  exact Set.disjoint_left.1 (F₀.disjoint_P j) hj (Finset.mem_coe.2 hp)

/-- **A chart at a puncture from a local model.**  Let `ζ` be holomorphic with `ζ' ≠ 0` at `φ_p(p)` and `T` a
homeomorphism of `ℂ` such that off `φ_p(p)` the coefficient `q̂_p` does not vanish and has matched branches
(`N ∘ T = S_k ∘ h` near `ζ(z)`, `(h ∘ ζ)'² = q̂_p`).  Then `χ = T ∘ ζ ∘ φ_p` (on a small neighbourhood of `p` without
other punctures) is a chart of `X` at `p` with matched branches at every other point `y = ι x'`, where `x'` is a
regular point of `q = ι^* q̂` and the branch `W` pulls back to a natural parameter of `q` at `x'`. -/
theorem s82td_chart_of_model {g n mh : ℕ} (F₀ : FiniteTypeStructure S₀ g n mh) {qh : F₀.X.carrier → ℂ → ℂ}
    (hqh : qh ∈ admissibleQDSpace F₀) {k : ℝ} {p : F₀.X.carrier} {ζ : ℂ → ℂ} (T : ℂ ≃ₜ ℂ)
    (hζa : AnalyticAt ℂ ζ (chartAt ℂ p p)) (hζd : deriv ζ (chartAt ℂ p p) ≠ 0)
    (hmodel : ∀ᶠ z in 𝓝[≠] chartAt ℂ p p, qh p z ≠ 0 ∧ ∃ h N : ℂ → ℂ, AnalyticAt ℂ h (ζ z) ∧
      AnalyticAt ℂ N (T (ζ z)) ∧ deriv N (T (ζ z)) ≠ 0 ∧ (∀ᶠ ξ in 𝓝 (ζ z), N (T ξ) = teichStretch k (h ξ)) ∧
      ∀ᶠ w in 𝓝 z, deriv (fun w => h (ζ w)) w ^ 2 = qh p w) (hp : p ∈ F₀.P) :
    ∃ χ : OpenPartialHomeomorph F₀.X.carrier ℂ, p ∈ χ.source ∧ (∀ x ∈ χ.source, x ∈ F₀.P → x = p) ∧
      (∀ x ∈ χ.source, ∀ j, x ∉ F₀.D j) ∧ ∀ y ∈ χ.source, y ≠ p → ∃ (x' : S₀) (N : ℂ → ℂ) (W : F₀.X.carrier → ℂ), F₀.ι x' = y ∧
        IsRegularPoint (pullbackQD F₀ qh) x' ∧ AnalyticAt ℂ N (χ y) ∧ deriv N (χ y) ≠ 0 ∧
        (∀ᶠ y' in 𝓝 y, N (χ y') = teichStretch k (W y')) ∧
        AnalyticAt ℂ (fun z => W (F₀.ι ((chartAt ℂ x').symm z))) (chartAt ℂ x' x') ∧
        ∀ᶠ z in 𝓝 (chartAt ℂ x' x'),
          deriv (fun z => W (F₀.ι ((chartAt ℂ x').symm z))) z ^ 2 = pullbackQD F₀ qh x' z := by
  classical
  set zp := chartAt ℂ p p with hzp_def
  have hzp : zp ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have hpp : (chartAt ℂ p).symm zp = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  -- the inverse function theorem for `ζ`
  let i : ℂ ≃L[ℂ] ℂ := .unitsEquivAut ℂ (.mk0 _ hζd)
  have hfd : HasStrictFDerivAt ζ i.toContinuousLinearMap zp := hζa.hasStrictDerivAt
  set L := hfd.toOpenPartialHomeomorph ζ with hL
  have hLc : ⇑L = ζ := hfd.toOpenPartialHomeomorph_coe
  have hzL : zp ∈ L.source := hfd.mem_toOpenPartialHomeomorph_source
  -- the good neighbourhood
  have hfin : IsClosed (↑(F₀.P.erase p) : Set F₀.X.carrier) := (F₀.P.erase p).finite_toSet.isClosed
  have hnotP : ∀ᶠ z in 𝓝 zp, (chartAt ℂ p).symm z ∉ (↑(F₀.P.erase p) : Set F₀.X.carrier) := by
    have hcs := ((chartAt ℂ p).continuousAt_symm hzp).preimage_mem_nhds (hfin.isOpen_compl.mem_nhds ?_)
    · exact hcs
    · rw [hpp]
      simp
  have hG : {z | z ∈ (chartAt ℂ p).target ∧ z ∈ L.source ∧ AnalyticAt ℂ ζ z ∧
      (chartAt ℂ p).symm z ∉ (↑(F₀.P.erase p) : Set F₀.X.carrier) ∧ (chartAt ℂ p).symm z ∉ ⋃ j, F₀.D j ∧
      (z ≠ zp → qh p z ≠ 0 ∧ ∃ h N : ℂ → ℂ, AnalyticAt ℂ h (ζ z) ∧
        AnalyticAt ℂ N (T (ζ z)) ∧ deriv N (T (ζ z)) ≠ 0 ∧ (∀ᶠ ξ in 𝓝 (ζ z), N (T ξ) = teichStretch k (h ξ)) ∧
        ∀ᶠ w in 𝓝 z, deriv (fun w => h (ζ w)) w ^ 2 = qh p w)} ∈ 𝓝 zp := by
    filter_upwards [(chartAt ℂ p).open_target.mem_nhds hzp, L.open_source.mem_nhds hzL,
      hζa.eventually_analyticAt, hnotP, s82td_eventually_notD F₀ hp, eventually_nhdsWithin_iff.1 hmodel]
      with z h1 h2 h3 h4 h4' h5
    exact ⟨h1, h2, h3, h4, h4', h5⟩
  obtain ⟨V, hVG, hVo, hzV⟩ := _root_.mem_nhds_iff.1 hG
  set χ : OpenPartialHomeomorph F₀.X.carrier ℂ := ((chartAt ℂ p).trans (L.restrOpen V hVo)).transHomeomorph T
    with hχ
  have hχsrc : ∀ y, y ∈ χ.source ↔ y ∈ (chartAt ℂ p).source ∧ chartAt ℂ p y ∈ L.source ∩ V := fun y => Iff.rfl
  have hχapp : ∀ y, χ y = T (ζ (chartAt ℂ p y)) := fun y => by
    show T (L (chartAt ℂ p y)) = _
    rw [hLc]
  -- a point of the source in `P` is `p`
  have hPp : ∀ x ∈ χ.source, x ∈ F₀.P → x = p := by
    intro x hx hxP
    obtain ⟨hx1, -, hx2⟩ := (hχsrc x).1 hx
    have hG' := hVG hx2
    by_contra hne
    apply hG'.2.2.2.1
    rw [(chartAt ℂ p).left_inv hx1]
    exact Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hne, hxP⟩)
  have hDχ : ∀ x ∈ χ.source, ∀ j, x ∉ F₀.D j := by
    intro x hx j hxj
    obtain ⟨hx1, -, hx2⟩ := (hχsrc x).1 hx
    apply (hVG hx2).2.2.2.2.1
    rw [(chartAt ℂ p).left_inv hx1]
    exact mem_iUnion.2 ⟨j, hxj⟩
  refine ⟨χ, (hχsrc p).2 ⟨mem_chart_source ℂ p, hzL, hzV⟩, hPp, hDχ, ?_⟩
  intro y hy hyp
  obtain ⟨hy1, -, hy2⟩ := (hχsrc y).1 hy
  obtain ⟨-, -, hya, -, -, hmod⟩ := hVG hy2
  have hzne : chartAt ℂ p y ≠ zp := by
    intro he
    apply hyp
    have := congrArg (chartAt ℂ p).symm he
    rwa [(chartAt ℂ p).left_inv hy1, hpp] at this
  obtain ⟨hq0, h, N, hh, hN, hN0, hNT, hhd⟩ := hmod hzne
  -- `y = ι x'`
  have hyP : y ∉ F₀.P := fun h' => hyp (hPp y hy h')
  have hyr : y ∈ range F₀.ι := by
    rw [F₀.range_ι]
    rintro (h | h)
    · exact hyP (Finset.mem_coe.1 h)
    · obtain ⟨j, hj⟩ := mem_iUnion.1 h
      exact hDχ y hy j hj
  obtain ⟨x', rfl⟩ := hyr
  have hcx : chartAt ℂ x' x' ∈ (chartAt ℂ x').target := (chartAt ℂ x').map_source (mem_chart_source ℂ x')
  have hxx : (chartAt ℂ x').symm (chartAt ℂ x' x') = x' := (chartAt ℂ x').left_inv (mem_chart_source ℂ x')
  -- the coordinate change `τ`
  set τ : ℂ → ℂ := fun v => chartAt ℂ p (F₀.ι ((chartAt ℂ x').symm v)) with hτ
  have hO : (chartAt ℂ x').target ∩ (chartAt ℂ x').symm ⁻¹' (F₀.ι ⁻¹' (chartAt ℂ p).source) ∈
      𝓝 (chartAt ℂ x' x') := by
    refine ((chartAt ℂ x').isOpen_inter_preimage_symm
      (F₀.embedding.continuous.isOpen_preimage _ (chartAt ℂ p).open_source)).mem_nhds ⟨hcx, ?_⟩
    show F₀.ι ((chartAt ℂ x').symm (chartAt ℂ x' x')) ∈ (chartAt ℂ p).source
    rw [hxx]
    exact hy1
  have hτd : ∀ v ∈ (chartAt ℂ x').target ∩ (chartAt ℂ x').symm ⁻¹' (F₀.ι ⁻¹' (chartAt ℂ p).source),
      DifferentiableAt ℂ τ v := fun v hv => s32p_T_differentiableAt F₀ p x' hv.1 hv.2
  have hτa : AnalyticAt ℂ τ (chartAt ℂ x' x') :=
    DifferentiableOn.analyticAt (fun v hv => (hτd v hv).differentiableWithinAt) hO
  have hτc : τ (chartAt ℂ x' x') = chartAt ℂ p (F₀.ι x') := by
    show chartAt ℂ p (F₀.ι ((chartAt ℂ x').symm (chartAt ℂ x' x'))) = _
    rw [hxx]
  have hτt : Tendsto τ (𝓝 (chartAt ℂ x' x')) (𝓝 (chartAt ℂ p (F₀.ι x'))) := by
    rw [← hτc]
    exact hτa.continuousAt.tendsto
  have hhζ : AnalyticAt ℂ (fun w => h (ζ w)) (chartAt ℂ p (F₀.ι x')) :=
    AnalyticAt.comp (g := h) (f := ζ) hh hya
  refine ⟨x', N, fun y' => h (ζ (chartAt ℂ p y')), rfl, ?_, by rw [hχapp]; exact hN, by rw [hχapp]; exact hN0,
    ?_, ?_, ?_⟩
  · -- regularity of `x'`
    show pullbackQD F₀ qh x' (chartAt ℂ x' x') ≠ 0
    rw [s32p_pullbackQD_local F₀ hqh x' p hcx (by rw [hxx]; exact hy1)]
    rw [hxx]
    exact mul_ne_zero hq0 (pow_ne_zero 2 (s82td_tau_deriv_ne_zero F₀ p x' hy1))
  · -- the matched branch near `ι x'`
    have hc : Tendsto (fun y' => ζ (chartAt ℂ p y')) (𝓝 (F₀.ι x')) (𝓝 (ζ (chartAt ℂ p (F₀.ι x')))) :=
      hya.continuousAt.tendsto.comp ((chartAt ℂ p).continuousAt hy1).tendsto
    filter_upwards [hc.eventually hNT] with y' hy'
    rw [hχapp]
    exact hy'
  · -- analyticity of the pulled-back branch
    exact AnalyticAt.comp_of_eq (g := fun w => h (ζ w)) hhζ hτa hτc
  · -- its squared derivative is `q`
    filter_upwards [hO, hτt.eventually hhd, hτt.eventually hhζ.eventually_analyticAt] with v hvO hv1 hv2
    have hd : HasDerivAt (fun z => h (ζ (chartAt ℂ p (F₀.ι ((chartAt ℂ x').symm z)))))
        (deriv (fun w => h (ζ w)) (τ v) * deriv τ v) v :=
      hv2.differentiableAt.hasDerivAt.comp v (hτd v hvO).hasDerivAt
    rw [hd.deriv, mul_pow, hv1, s32p_pullbackQD_local F₀ hqh x' p hvO.1 hvO.2]

/-- Points near `z₀`, other than `z₀`, carry a property on a whole neighbourhood when the property holds on a punctured
neighbourhood of `z₀`. -/
theorem s82td_punctured_open {P : ℂ → Prop} {z₀ : ℂ} (h : ∀ᶠ z in 𝓝[≠] z₀, P z) :
    ∀ᶠ z in 𝓝[≠] z₀, ∀ᶠ w in 𝓝 z, P w := by
  have h1 := eventually_eventually_nhds.2 (eventually_nhdsWithin_iff.1 h)
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with z hz hzne
  filter_upwards [hz, isOpen_ne.mem_nhds hzne] with w hw1 hw2
  exact hw1 hw2

/-- The stretch `S_k` vanishes only at `0`. -/
theorem s82td_teichStretch_ne_zero {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) {t : ℂ} (ht : t ≠ 0) :
    teichStretch k t ≠ 0 := by
  intro h0
  have hk1 : (1 - k : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.2 (by linarith)
  have h1 : t + k * conj t = 0 := by
    have := h0
    simp only [teichStretch, div_eq_zero_iff, hk1, or_false] at this
    exact this
  have h2 : ‖t‖ = k * ‖t‖ := by
    have := congrArg norm (eq_neg_of_add_eq_zero_left h1)
    rw [norm_neg, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk₀] at this
    exact this
  have h3 : 0 < ‖t‖ := norm_pos_iff.2 ht
  nlinarith

/-- **Local model at a genuine simple pole** (`c ≠ 0`): with the pole natural parameter `ζ` (B1, `f = ζ'²/(4ζ)`) and
the pole stretch `𝒫` (B2), the branches are `h = √·` near `ζ(z) ≠ 0` and `N = √·` near `𝒫(ζ z) = S_k(h ζ z)²`. -/
theorem s82td_pole_model {f r : ℂ → ℂ} {z₀ c : ℂ} (hc : c ≠ 0) (hr : AnalyticAt ℂ r z₀)
    (hev : ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + r z) {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) :
    ∃ (ζ : ℂ → ℂ) (T : ℂ ≃ₜ ℂ), AnalyticAt ℂ ζ z₀ ∧ deriv ζ z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 ∧ ∃ h N : ℂ → ℂ, AnalyticAt ℂ h (ζ z) ∧
        AnalyticAt ℂ N (T (ζ z)) ∧ deriv N (T (ζ z)) ≠ 0 ∧ (∀ᶠ ξ in 𝓝 (ζ z), N (T ξ) = teichStretch k (h ξ)) ∧
        ∀ᶠ w in 𝓝 z, deriv (fun w => h (ζ w)) w ^ 2 = f w := by
  obtain ⟨ζ, hζa, hζ0, hζd, hζev⟩ := s82td_pole_natural (h := f) hc hr hev
  obtain ⟨P, hP0, hPsq⟩ := s82td_pole_stretch hk₀ hk
  refine ⟨ζ, P, hζa, hζd, ?_⟩
  have hdne : ∀ᶠ z in 𝓝 z₀, deriv ζ z ≠ 0 := hζa.deriv.continuousAt.eventually_ne hζd
  have hloc := s82td_punctured_open hζev
  filter_upwards [hloc, hζev, nhdsWithin_le_nhds hdne, nhdsWithin_le_nhds hζa.eventually_analyticAt]
    with z hzev hz hzd hza
  obtain ⟨hζz, hfz⟩ := hz
  refine ⟨by rw [hfz]; exact div_ne_zero (pow_ne_zero 2 hzd) (mul_ne_zero (by norm_num) hζz), ?_⟩
  -- the branch `h` of `√ξ` near `ζ z`
  set t₀ := ζ z ^ (2⁻¹ : ℂ) with ht₀
  have ht₀sq : t₀ ^ 2 = ζ z := by
    have hs := Complex.cpow_nat_inv_pow (ζ z) (n := 2) two_ne_zero
    push_cast at hs
    exact hs
  have ht₀0 : t₀ ≠ 0 := by
    intro h0
    apply hζz
    rw [← ht₀sq, h0]
    norm_num
  obtain ⟨h, hha, hh1, -, hhsq, -⟩ := s82td_sqrt_analytic ht₀0
  rw [ht₀sq] at hha hh1
  -- the branch `N` of `√u` near `𝒫(ζ z) = S_k(t₀)²`
  set s₀ := teichStretch k t₀ with hs₀
  have hs₀0 : s₀ ≠ 0 := s82td_teichStretch_ne_zero hk₀ hk ht₀0
  obtain ⟨N, hNa, hN1, hNd, -, hNleft⟩ := s82td_sqrt_analytic hs₀0
  have hPz : P (ζ z) = s₀ ^ 2 := by rw [← ht₀sq, hPsq]
  refine ⟨h, N, hha, by rw [hPz]; exact hNa, by rw [hPz]; exact hNd, ?_, ?_⟩
  · -- `N(𝒫 ξ) = S_k(h ξ)` near `ζ z`
    have hcont : ContinuousAt (fun ξ => teichStretch k (h ξ)) (ζ z) :=
      ContinuousAt.comp (g := teichStretch k) (f := h) (s26d_a_continuous_teichStretch k).continuousAt
        hha.continuousAt
    have hcz : teichStretch k (h (ζ z)) = s₀ := by rw [hh1]
    have ht : Tendsto (fun ξ => teichStretch k (h ξ)) (𝓝 (ζ z)) (𝓝 s₀) := by
      rw [← hcz]
      exact hcont.tendsto
    filter_upwards [ht.eventually hNleft] with ξ hξ
    have hPξ : P ξ = teichStretch k (h ξ) ^ 2 := by
      have := hPsq (h ξ)
      rwa [hhsq] at this
    rw [hPξ]
    exact hξ
  · -- `(h ∘ ζ)'² = ζ'²/(4ζ) = f` near `z`
    have hct : Tendsto ζ (𝓝 z) (𝓝 (ζ z)) := hza.continuousAt.tendsto
    filter_upwards [hzev, hct.eventually hha.eventually_analyticAt, hza.eventually_analyticAt,
      hct.eventually (isOpen_ne.mem_nhds hζz)] with w hw1 hw2 hw3 hw4
    obtain ⟨-, hfw⟩ := hw1
    have hd : HasDerivAt (fun w => h (ζ w)) (deriv h (ζ w) * deriv ζ w) w :=
      hw2.differentiableAt.hasDerivAt.comp w hw3.differentiableAt.hasDerivAt
    -- `h² = id` gives `2 h h' = 1`
    have hhd : deriv h (ζ w) * (2 * h (ζ w)) = 1 := by
      have h1 : HasDerivAt (fun ξ => h ξ ^ 2) (((2 : ℕ) : ℂ) * h (ζ w) ^ (2 - 1) * deriv h (ζ w)) (ζ w) :=
        hw2.differentiableAt.hasDerivAt.pow 2
      have h2 : (fun ξ => h ξ ^ 2) = id := funext hhsq
      rw [h2] at h1
      have := h1.unique (hasDerivAt_id _)
      push_cast at this
      linear_combination this
    have hsqw : h (ζ w) ^ 2 = ζ w := hhsq _
    have e2 : deriv h (ζ w) ^ 2 * (4 * h (ζ w) ^ 2) = 1 := by
      linear_combination (deriv h (ζ w) * (2 * h (ζ w)) + 1) * hhd
    rw [hsqw] at e2
    rw [hd.deriv, hfw, eq_div_iff (mul_ne_zero (by norm_num) hw4)]
    linear_combination deriv ζ w ^ 2 * e2

/-- **Local model at a removable puncture** (`c = 0`): `f = r` near `z₀` off `z₀`, with `r` holomorphic and not
identically zero, has a finite order `m₀`, a natural parameter `ζ` of (25.2)/(25.5), and the §26.2 branches of
`s26d_a_branches` with `T = teichStretchZero k m₀`. -/
theorem s82td_removable_model {f r : ℂ → ℂ} {z₀ : ℂ} (hr : AnalyticAt ℂ r z₀) (hnz : ¬ ∀ᶠ z in 𝓝 z₀, r z = 0)
    (hev : ∀ᶠ z in 𝓝[≠] z₀, f z = r z) {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) :
    ∃ (ζ : ℂ → ℂ) (T : ℂ ≃ₜ ℂ), AnalyticAt ℂ ζ z₀ ∧ deriv ζ z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 ∧ ∃ h N : ℂ → ℂ, AnalyticAt ℂ h (ζ z) ∧
        AnalyticAt ℂ N (T (ζ z)) ∧ deriv N (T (ζ z)) ≠ 0 ∧ (∀ᶠ ξ in 𝓝 (ζ z), N (T ξ) = teichStretch k (h ξ)) ∧
        ∀ᶠ w in 𝓝 z, deriv (fun w => h (ζ w)) w ^ 2 = f w := by
  obtain ⟨n₀, g, hg, hg0, hfg⟩ := hr.exists_eventuallyEq_pow_smul_nonzero_iff.2 hnz
  simp only [smul_eq_mul] at hfg
  obtain ⟨ζ, hζa, hζ0, hζd, hζid⟩ : ∃ ζ : ℂ → ℂ, AnalyticAt ℂ ζ z₀ ∧ ζ z₀ = 0 ∧ deriv ζ z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 z₀, r z = ((n₀ + 2 : ℂ) / 2) ^ 2 * ζ z ^ n₀ * deriv ζ z ^ 2 := by
    rcases Nat.eq_zero_or_pos n₀ with hn | hn
    · subst hn
      have hr0 : r z₀ ≠ 0 := by
        have := hfg.self_of_nhds
        rw [this, pow_zero, one_mul]
        exact hg0
      obtain ⟨ζ, h1, h2, h3, h4⟩ := eq25_2_natural_parameter hr hr0
      refine ⟨ζ, h1, h2, h3, h4.mono fun z hz => ?_⟩
      rw [← hz]
      norm_num
    · exact eq25_5_natural_parameter_zero hn hg hg0 hfg
  refine ⟨ζ, s26d_a_T hk₀ hk n₀, hζa, hζd, ?_⟩
  -- `r` and `ζ` do not vanish off `z₀` near `z₀`
  have hrne : ∀ᶠ z in 𝓝[≠] z₀, r z ≠ 0 := by
    rcases hr.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd h hnz
    · exact h
  have hζne : ∀ᶠ z in 𝓝[≠] z₀, ζ z ≠ 0 := by
    have := hζa.differentiableAt.hasDerivAt.eventually_ne hζd (c := 0)
    exact this
  have hloc := s82td_punctured_open (hev.and (eventually_nhdsWithin_of_eventually_nhds hζid))
  filter_upwards [hloc, hev, hrne, hζne, nhdsWithin_le_nhds hζa.eventually_analyticAt] with z hzloc hfz hrz hζz hza
  refine ⟨by rw [hfz]; exact hrz, ?_⟩
  obtain ⟨h, N, hh, hhd, hN, hNd0, -, hNT⟩ := s26d_a_branches hk₀ hk n₀ (s := ζ z) (Or.inr hζz)
  refine ⟨h, N, hh, hN, hNd0, hNT, ?_⟩
  have hct : Tendsto ζ (𝓝 z) (𝓝 (ζ z)) := hza.continuousAt.tendsto
  filter_upwards [hzloc, hct.eventually hhd, hct.eventually hh.eventually_analyticAt, hza.eventually_analyticAt]
    with w hw1 hw2 hw3 hw4
  obtain ⟨hfw, hrw⟩ := hw1
  have hd : HasDerivAt (fun w => h (ζ w)) (deriv h (ζ w) * deriv ζ w) w :=
    hw3.differentiableAt.hasDerivAt.comp w hw4.differentiableAt.hasDerivAt
  rw [hd.deriv, mul_pow, hw2, hfw, hrw]
  try ring

/-- Near a puncture `q̂` does not vanish identically: otherwise `q = ι^* q̂` would vanish near a point `x'` of `S₀`,
whose §26.2 datum has a finite order. -/
theorem s82td_removable_nonzero {g n mh : ℕ} (F₀ : FiniteTypeStructure S₀ g n mh) {qh : F₀.X.carrier → ℂ → ℂ}
    (hqh : qh ∈ admissibleQDSpace F₀) {m : S₀ → ℕ} {ζ : S₀ → ℂ → ℂ} {Z : S₀ → OpenPartialHomeomorph ℂ ℂ}
    (hD : ∀ s, s26d_a_Data (pullbackQD F₀ qh) s (m s) (ζ s) (Z s)) {p : F₀.X.carrier} (hp : p ∈ F₀.P) :
    ¬ ∀ᶠ z in 𝓝[≠] chartAt ℂ p p, qh p z = 0 := by
  classical
  intro hz
  have hzp : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have hpp : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hfin : IsClosed (↑(F₀.P.erase p) : Set F₀.X.carrier) := (F₀.P.erase p).finite_toSet.isClosed
  have hnotP : ∀ᶠ z in 𝓝 (chartAt ℂ p p), (chartAt ℂ p).symm z ∉ (↑(F₀.P.erase p) : Set F₀.X.carrier) := by
    refine ((chartAt ℂ p).continuousAt_symm hzp).preimage_mem_nhds (hfin.isOpen_compl.mem_nhds ?_)
    rw [hpp]
    simp
  have ha1 : ∀ᶠ z in 𝓝[≠] chartAt ℂ p p, z ∈ (chartAt ℂ p).target :=
    nhdsWithin_le_nhds ((chartAt ℂ p).open_target.mem_nhds hzp)
  have ha2 : ∀ᶠ z in 𝓝[≠] chartAt ℂ p p, (chartAt ℂ p).symm z ∉ (↑(F₀.P.erase p) : Set F₀.X.carrier) :=
    nhdsWithin_le_nhds hnotP
  have ha3 : ∀ᶠ z in 𝓝[≠] chartAt ℂ p p, z ∈ ({chartAt ℂ p p}ᶜ : Set ℂ) := self_mem_nhdsWithin
  have ha4 : ∀ᶠ z in 𝓝[≠] chartAt ℂ p p, (chartAt ℂ p).symm z ∉ ⋃ j, F₀.D j :=
    nhdsWithin_le_nhds (s82td_eventually_notD F₀ hp)
  have hall := ((ha1.and (ha2.and (s82td_punctured_open hz))).and ha3).and ha4
  obtain ⟨z, ⟨⟨hzt, hzP, hz0⟩, hzne⟩, hzD⟩ := hall.exists
  have hyP : (chartAt ℂ p).symm z ∉ F₀.P := by
    intro hP
    by_cases hyp : (chartAt ℂ p).symm z = p
    · apply hzne
      have := congrArg (chartAt ℂ p) hyp
      rwa [(chartAt ℂ p).right_inv hzt] at this
    · exact hzP (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hyp, hP⟩))
  have hyr : (chartAt ℂ p).symm z ∈ range F₀.ι := by
    rw [F₀.range_ι]
    rintro (h | h)
    · exact hyP (Finset.mem_coe.1 h)
    · exact hzD h
  obtain ⟨x', hx'⟩ := hyr
  have hy1 : F₀.ι x' ∈ (chartAt ℂ p).source := by rw [hx']; exact (chartAt ℂ p).map_target hzt
  have hcx : chartAt ℂ x' x' ∈ (chartAt ℂ x').target := (chartAt ℂ x').map_source (mem_chart_source ℂ x')
  have hxx : (chartAt ℂ x').symm (chartAt ℂ x' x') = x' := (chartAt ℂ x').left_inv (mem_chart_source ℂ x')
  have hcont : ContinuousAt (fun v => F₀.ι ((chartAt ℂ x').symm v)) (chartAt ℂ x' x') :=
    ContinuousAt.comp (g := F₀.ι) (f := (chartAt ℂ x').symm) F₀.embedding.continuous.continuousAt
      ((chartAt ℂ x').continuousAt_symm hcx)
  have hsrc : ∀ᶠ v in 𝓝 (chartAt ℂ x' x'), F₀.ι ((chartAt ℂ x').symm v) ∈ (chartAt ℂ p).source := by
    refine hcont.preimage_mem_nhds ((chartAt ℂ p).open_source.mem_nhds ?_)
    show F₀.ι ((chartAt ℂ x').symm (chartAt ℂ x' x')) ∈ _
    rw [hxx]
    exact hy1
  have hτc : ContinuousAt (fun v => chartAt ℂ p (F₀.ι ((chartAt ℂ x').symm v))) (chartAt ℂ x' x') := by
    refine ContinuousAt.comp (g := chartAt ℂ p) (f := fun v => F₀.ι ((chartAt ℂ x').symm v)) ?_ hcont
    show ContinuousAt (chartAt ℂ p) (F₀.ι ((chartAt ℂ x').symm (chartAt ℂ x' x')))
    rw [hxx]
    exact (chartAt ℂ p).continuousAt hy1
  have hτv : chartAt ℂ p (F₀.ι ((chartAt ℂ x').symm (chartAt ℂ x' x'))) = z := by
    rw [hxx, hx', (chartAt ℂ p).right_inv hzt]
  have hτt : Tendsto (fun v => chartAt ℂ p (F₀.ι ((chartAt ℂ x').symm v))) (𝓝 (chartAt ℂ x' x')) (𝓝 z) := by
    have := hτc.tendsto
    rwa [hτv] at this
  have hq0 : ∀ᶠ v in 𝓝 (chartAt ℂ x' x'), pullbackQD F₀ qh x' v = 0 := by
    filter_upwards [hsrc, (chartAt ℂ x').open_target.mem_nhds hcx, hτt.eventually hz0] with v hv1 hv2 hv3
    rw [s32p_pullbackQD_local F₀ hqh x' p hv2 hv1, hv3, zero_mul]
  have htop : meromorphicOrderAt (pullbackQD F₀ qh x') (chartAt ℂ x' x') = ⊤ :=
    meromorphicOrderAt_eq_top_iff.2 (nhdsWithin_le_nhds hq0)
  have hord : meromorphicOrderAt (pullbackQD F₀ qh x') (chartAt ℂ x' x') = (m x' : ℤ) := (hD x').order
  rw [htop] at hord
  exact WithTop.top_ne_coe hord

/-- **[stub B3] The new chart at a puncture**: for `p ∈ P` there is a chart `χ` of the closed surface `X` at `p`
(containing no other puncture and meeting no hole) that is holomorphically compatible with every §26.2 chart `ψ_s` of `S₀` transported
to `X` by `ι`. -/
theorem s82td_puncture_chart {g n mh : ℕ} (F₀ : FiniteTypeStructure S₀ g n mh) {qh : F₀.X.carrier → ℂ → ℂ}
    (hqh : qh ∈ admissibleQDSpace F₀) {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) {m : S₀ → ℕ} {ζ : S₀ → ℂ → ℂ}
    {Z : S₀ → OpenPartialHomeomorph ℂ ℂ} (hD : ∀ s, s26d_a_Data (pullbackQD F₀ qh) s (m s) (ζ s) (Z s))
    {p : F₀.X.carrier} (hp : p ∈ F₀.P) :
    ∃ χ : OpenPartialHomeomorph F₀.X.carrier ℂ, p ∈ χ.source ∧ (∀ x ∈ χ.source, x ∈ F₀.P → x = p) ∧
      (∀ s : S₀, ∀ w ∈ χ.target, χ.symm w ∈
          ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk m Z s)).source →
        DifferentiableAt ℂ (fun w =>
          ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk m Z s)) (χ.symm w)) w) ∧
      (∀ s : S₀, ∀ w ∈ ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk m Z s)).target,
        ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk m Z s)).symm w ∈ χ.source →
        DifferentiableAt ℂ (fun w =>
          χ (((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk m Z s)).symm w)) w) ∧
      ∀ x ∈ χ.source, ∀ j, x ∉ F₀.D j := by
  have hq : IsHolQuadDiff (pullbackQD F₀ qh) := s32p_pullbackQD_isHolQuadDiff F₀ hqh
  set ιe := F₀.embedding.toOpenPartialHomeomorph F₀.ι with hιe
  have hleft : ∀ y : S₀, ιe.symm (F₀.ι y) = y := fun y => F₀.embedding.toOpenPartialHomeomorph_left_inv F₀.ι
  -- the local form of `q̂` at the puncture
  obtain ⟨-, c, r, hr, hev⟩ := hqh.2.2.1 p p hp (mem_chart_source ℂ p)
  -- a local model at `p`
  obtain ⟨ζ, T, hζa, hζd, hmodel⟩ : ∃ (ζ : ℂ → ℂ) (T : ℂ ≃ₜ ℂ), AnalyticAt ℂ ζ (chartAt ℂ p p) ∧
      deriv ζ (chartAt ℂ p p) ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] chartAt ℂ p p, qh p z ≠ 0 ∧ ∃ h N : ℂ → ℂ, AnalyticAt ℂ h (ζ z) ∧
        AnalyticAt ℂ N (T (ζ z)) ∧ deriv N (T (ζ z)) ≠ 0 ∧ (∀ᶠ ξ in 𝓝 (ζ z), N (T ξ) = teichStretch k (h ξ)) ∧
        ∀ᶠ w in 𝓝 z, deriv (fun w => h (ζ w)) w ^ 2 = qh p w := by
    by_cases hc : c = 0
    · subst hc
      have hev' : ∀ᶠ z in 𝓝[≠] chartAt ℂ p p, qh p z = r z := hev.mono fun z hz => by rw [hz]; simp
      refine s82td_removable_model hr ?_ hev' hk₀ hk
      -- `r` does not vanish near `φ_p(p)`: otherwise `q = ι^* q̂` vanishes near a point of `S₀`, against the data
      intro hr0
      apply s82td_removable_nonzero F₀ hqh hD hp
      filter_upwards [hev', nhdsWithin_le_nhds hr0] with z h1 h2
      rw [h1, h2]
    · exact s82td_pole_model hc hr hev hk₀ hk
  obtain ⟨χ, hpχ, hPp, hDχ, hbr⟩ := s82td_chart_of_model F₀ hqh T hζa hζd hmodel hp
  -- points of the transported charts are not punctures
  have hΨsrc : ∀ (s : S₀) (y : F₀.X.carrier), y ∈ (ιe.symm.trans (s26d_a_psi hk₀ hk m Z s)).source →
      ∃ x' : S₀, F₀.ι x' = y ∧ x' ∈ (s26d_a_psi hk₀ hk m Z s).source := by
    intro s y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hyr : y ∈ range F₀.ι := by
      have : y ∈ ιe.target := hy1
      rwa [F₀.embedding.toOpenPartialHomeomorph_target] at this
    obtain ⟨x', rfl⟩ := hyr
    refine ⟨x', rfl, ?_⟩
    have : ιe.symm (F₀.ι x') ∈ (s26d_a_psi hk₀ hk m Z s).source := hy2
    rwa [hleft] at this
  have hΨapp : ∀ (s x' : S₀), (ιe.symm.trans (s26d_a_psi hk₀ hk m Z s)) (F₀.ι x') = s26d_a_psi hk₀ hk m Z s x' := by
    intro s x'
    show s26d_a_psi hk₀ hk m Z s (ιe.symm (F₀.ι x')) = _
    rw [hleft]
  have hpne : ∀ x' : S₀, F₀.ι x' ≠ p := by
    intro x' h
    have : p ∈ range F₀.ι := ⟨x', h⟩
    rw [F₀.range_ι] at this
    exact this (Or.inl (Finset.mem_coe.2 hp))
  refine ⟨χ, hpχ, hPp, ?_, ?_, hDχ⟩
  · intro s w hw hws
    obtain ⟨x', hx'y, hx'src⟩ := hΨsrc s _ hws
    have hy : χ.symm w ∈ χ.source := χ.map_target hw
    obtain ⟨x'', N, W, hx'', hreg, hN, hN0, hNW, hWa, hWd⟩ := hbr _ hy (by rw [← hx'y]; exact hpne x')
    have hxx : x'' = x' := F₀.embedding.injective (hx''.trans hx'y.symm)
    subst hxx
    obtain ⟨N', W', hN', hN'0, hN'W, hW'a, hW'd⟩ := s82td_psi_branch F₀ hq hk₀ hk hD s hx'src hreg
    obtain ⟨ε, c', hε, hWW⟩ := s82td_iota_natural_unique F₀ hreg hW'a hW'd hWa hWd
    rw [hx''] at hN'W hWW
    have h := s82td_compat_of_branches (φ₁ := ιe.symm.trans (s26d_a_psi hk₀ hk m Z s)) (φ₂ := χ) hws hy hε
      (by rw [← hx'', hΨapp]; exact hN') (by rw [← hx'', hΨapp]; exact hN'0) hN hN'W hNW hWW
    rwa [χ.right_inv hw] at h
  · intro s w hw hwχ
    have hy : (ιe.symm.trans (s26d_a_psi hk₀ hk m Z s)).symm w ∈ (ιe.symm.trans (s26d_a_psi hk₀ hk m Z s)).source :=
      (ιe.symm.trans (s26d_a_psi hk₀ hk m Z s)).map_target hw
    obtain ⟨x', hx'y, hx'src⟩ := hΨsrc s _ hy
    obtain ⟨x'', N, W, hx'', hreg, hN, hN0, hNW, hWa, hWd⟩ := hbr _ hwχ (by rw [← hx'y]; exact hpne x')
    have hxx : x'' = x' := F₀.embedding.injective (hx''.trans hx'y.symm)
    subst hxx
    obtain ⟨N', W', hN', hN'0, hN'W, hW'a, hW'd⟩ := s82td_psi_branch F₀ hq hk₀ hk hD s hx'src hreg
    obtain ⟨ε, c', hε, hWW⟩ := s82td_iota_natural_unique F₀ hreg hWa hWd hW'a hW'd
    rw [hx''] at hN'W hWW
    have h := s82td_compat_of_branches (φ₁ := χ) (φ₂ := ιe.symm.trans (s26d_a_psi hk₀ hk m Z s)) hwχ hy hε
      hN hN0 (by rw [← hx'', hΨapp]; exact hN') hNW hN'W hWW
    rwa [(ιe.symm.trans (s26d_a_psi hk₀ hk m Z s)).right_inv hw] at h

/-- **[stub B4] Charted package** (copy of the charted part of `s26d_a_package`, without the differential): a family of
charts `ψ p` of a compact connected Hausdorff `Y` with holomorphic transitions defines a closed Riemann surface on
the point set of `Y` (`e` the identity of the point set) with preferred charts `ψ p`. -/
theorem s82td_charted_package {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [CompactSpace Y]
    (ψ : Y → OpenPartialHomeomorph Y ℂ) (hmem : ∀ p, p ∈ (ψ p).source)
    (hcompat : ∀ p p', ∀ w ∈ (ψ p').target, (ψ p').symm w ∈ (ψ p).source →
      DifferentiableAt ℂ (fun w => ψ p ((ψ p').symm w)) w) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : ChartedSpace ℂ X), T2Space X ∧ ConnectedSpace X ∧
      CompactSpace X ∧ IsManifold 𝓘(ℂ) ω X ∧ ∃ e : Y ≃ₜ X, ∀ p,
        (∀ x, chartAt ℂ (e p) (e x) = ψ p x) ∧ (chartAt ℂ (e p)).source = e '' (ψ p).source ∧
          (chartAt ℂ (e p)).target = (ψ p).target ∧ ∀ w, (chartAt ℂ (e p)).symm w = e ((ψ p).symm w) := by
  let τ : TopologicalSpace (s26d_a_X Y) := ‹TopologicalSpace Y›
  let cs : ChartedSpace ℂ (s26d_a_X Y) := ChartedSpace.mk (Set.range ψ) ψ hmem (fun p => ⟨p, rfl⟩)
  have hman : IsManifold 𝓘(ℂ) ω (s26d_a_X Y) := by
    apply isManifold_of_contDiffOn
    rintro e e' ⟨p', rfl⟩ ⟨p, rfl⟩
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
      Function.comp_id, preimage_id_eq, id_eq, range_id, inter_univ]
    have hopen : IsOpen ((ψ p').symm.trans (ψ p)).source := ((ψ p').symm.trans (ψ p)).open_source
    refine (DifferentiableOn.analyticOnNhd (fun w hw => ?_) hopen).contDiffOn_of_completeSpace
    rw [OpenPartialHomeomorph.trans_source] at hw
    exact (hcompat p p' w hw.1 hw.2).differentiableWithinAt
  refine ⟨s26d_a_X Y, τ, cs, ‹T2Space Y›, ‹ConnectedSpace Y›, ‹CompactSpace Y›, hman,
    ⟨Equiv.refl _, continuous_id, continuous_id⟩, fun p => ⟨fun x => rfl, ?_, rfl, fun w => rfl⟩⟩
  exact (Set.image_id _).symm

/-- **[copy of `s26u_local`, non-closed target; leader-approved copy R82]** The local form at a point where `q_x ≠ 0`:
the local expression of `e` is `K`-q.c. near `z₀` (the hypotheses are the `IsTeichDeformation` fields it uses). -/
theorem s82td_u_local {q : S₀ → ℂ → ℂ} {k : ℝ} {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {e : S₀ ≃ₜ X} {q' : X → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (hk₀ : 0 ≤ k)
    (hk : k < 1) (hregf : ∀ p : S₀, IsRegularPoint q p → IsRegularPoint q' (e p) ∧
      ∃ ζ ζ' : ℂ → ℂ, IsNaturalParameterAt q p ζ ∧ IsNaturalParameterAt q' (e p) ζ' ∧
        ∀ᶠ z in 𝓝 (chartAt ℂ p p), ζ' (localMapExpr e p z) = teichStretch k (ζ z)) (x : S₀) {z₀ : ℂ}
    (hz₀ : z₀ ∈ localMapDomain e x) (hq0 : q x z₀ ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ U ⊆ localMapDomain e x ∧
      IsKQC (localMapExpr e x) U ((1 + k) / (1 - k)) := by
  have hz₀t : z₀ ∈ (chartAt ℂ x).target := hz₀.1
  set p := (chartAt ℂ x).symm z₀ with hp
  have hep : e p ∈ (chartAt ℂ (e x)).source := hz₀.2
  have hreg : IsRegularPoint q p := (s26u_isRegularPoint_iff hq x hz₀t).2 hq0
  obtain ⟨-, ζ, ζ', hζ, hζ', hrel⟩ := hregf p hreg
  obtain ⟨hτan, hτd⟩ := s26u_transition_analyticAt hq x p hz₀t (mem_chart_source ℂ p) hq0
  have hτz : chartTransition p x z₀ = chartAt ℂ p p := rfl
  have hζan : AnalyticAt ℂ ζ (chartTransition p x z₀) := by
    rw [hτz]
    exact hζ.1
  have hAan : AnalyticAt ℂ (ζ ∘ chartTransition p x) z₀ := hζan.comp hτan
  have hAd : deriv (ζ ∘ chartTransition p x) z₀ ≠ 0 := by
    rw [deriv_comp z₀ hζan.differentiableAt hτan.differentiableAt, hτz]
    exact mul_ne_zero hζ.2.2.1 hτd
  have hgt : localMapExpr e x z₀ ∈ (chartAt ℂ (e x)).target := (chartAt ℂ (e x)).map_source hep
  have hgs : (chartAt ℂ (e x)).symm (localMapExpr e x z₀) = e p := (chartAt ℂ (e x)).left_inv hep
  have hgs' : (chartAt ℂ (e x)).symm (localMapExpr e x z₀) ∈ (chartAt ℂ (e p)).source := by
    rw [hgs]
    exact mem_chart_source ℂ (e p)
  have hσan : AnalyticAt ℂ (chartTransition (e p) (e x)) (localMapExpr e x z₀) :=
    DifferentiableOn.analyticAt
      (by exact fun w hw => (s23_transition (e p) (e x) hw.1 hw.2).1.differentiableWithinAt)
      (((chartAt ℂ (e x)).isOpen_inter_preimage_symm (chartAt ℂ (e p)).open_source).mem_nhds ⟨hgt, hgs'⟩)
  have hσd : deriv (chartTransition (e p) (e x)) (localMapExpr e x z₀) ≠ 0 :=
    (s23_transition (e p) (e x) hgt hgs').2
  have hσz : chartTransition (e p) (e x) (localMapExpr e x z₀) = chartAt ℂ (e p) (e p) := by
    simp only [chartTransition, hgs]
  have hζ'an : AnalyticAt ℂ ζ' (chartTransition (e p) (e x) (localMapExpr e x z₀)) := by
    rw [hσz]
    exact hζ'.1
  have hBan : AnalyticAt ℂ (ζ' ∘ chartTransition (e p) (e x)) (localMapExpr e x z₀) := hζ'an.comp hσan
  have hBd : deriv (ζ' ∘ chartTransition (e p) (e x)) (localMapExpr e x z₀) ≠ 0 := by
    rw [deriv_comp _ hζ'an.differentiableAt hσan.differentiableAt, hσz]
    exact mul_ne_zero hζ'.2.2.1 hσd
  have hgc : ContinuousAt (localMapExpr e x) z₀ := by
    have h1 : ContinuousAt (fun z => e ((chartAt ℂ x).symm z)) z₀ :=
      e.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz₀t)
    exact ContinuousAt.comp (g := chartAt ℂ (e x)) (f := fun z => e ((chartAt ℂ x).symm z))
      ((chartAt ℂ (e x)).continuousAt hep) h1
  have hΩ : localMapDomain e x ∈ 𝓝 z₀ := (s23_localMapDomain_isOpen e.continuous x).mem_nhds hz₀
  have hτc : Tendsto (chartTransition p x) (𝓝 z₀) (𝓝 (chartAt ℂ p p)) := by
    rw [← hτz]
    exact hτan.continuousAt.tendsto
  have hBg : ∀ᶠ w in 𝓝 z₀, (ζ' ∘ chartTransition (e p) (e x)) (localMapExpr e x w) =
      teichStretch k ((ζ ∘ chartTransition p x) w) := by
    filter_upwards [hτc.eventually hrel, hΩ, ((chartAt ℂ x).isOpen_inter_preimage_symm
      (chartAt ℂ p).open_source).mem_nhds ⟨hz₀t, mem_chart_source ℂ p⟩] with w hw1 hw2 hw3
    simp only [Function.comp_apply]
    rw [← hw1]
    congr 1
    simp only [chartTransition, localMapExpr]
    rw [(chartAt ℂ (e x)).left_inv hw2.2, (chartAt ℂ p).left_inv hw3.2]
  exact s26u_isKQC_local_of_conj (s26u_teichStretch_isKQC hk₀ hk) hAan hAd hBan hBd hgc
    hBg hΩ

/-- **[copy of `s26u_isKQC_chart`, non-closed target]** **Each local expression of the deformation map is `K`-q.c.**  `S₀` is connected and T2 (it is
homeomorphic to `X` via `e`), so the zeros of `q_x` in the chart target are countable
(`s26u_zeros_countable`); away from them `e` is locally `K`-q.c. (`s26u_local`), and the countable
set is removable (`s13x_removable`). -/
theorem s82td_u_isKQC_chart {q : S₀ → ℂ → ℂ} {k : ℝ} {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {e : S₀ ≃ₜ X} {q' : X → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (hk₀ : 0 ≤ k)
    (hk : k < 1) (hregf : ∀ p : S₀, IsRegularPoint q p → IsRegularPoint q' (e p) ∧
      ∃ ζ ζ' : ℂ → ℂ, IsNaturalParameterAt q p ζ ∧ IsNaturalParameterAt q' (e p) ζ' ∧
        ∀ᶠ z in 𝓝 (chartAt ℂ p p), ζ' (localMapExpr e p z) = teichStretch k (ζ z)) (x : S₀) :
    IsKQC (localMapExpr e x) (localMapDomain e x) ((1 + k) / (1 - k)) := by
  have hΩ := s23_localMapDomain_isOpen e.continuous x
  have hcont : ContinuousOn (localMapExpr e x) (localMapDomain e x) := fun z hz => by
    have h1 : ContinuousAt (fun z => e ((chartAt ℂ x).symm z)) z :=
      e.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz.1)
    have h2 : e ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (e x)).source := hz.2
    exact (ContinuousAt.comp (g := chartAt ℂ (e x)) (f := fun z => e ((chartAt ℂ x).symm z))
      ((chartAt ℂ (e x)).continuousAt h2) h1).continuousWithinAt
  have hinj : InjOn (localMapExpr e x) (localMapDomain e x) := by
    intro w₁ hw₁ w₂ hw₂ heq
    have h1 : e ((chartAt ℂ x).symm w₁) = e ((chartAt ℂ x).symm w₂) :=
      (chartAt ℂ (e x)).injOn hw₁.2 hw₂.2 heq
    exact (chartAt ℂ x).symm.injOn hw₁.1 hw₂.1 (e.injective h1)
  have hLc : (localMapDomain e x ∩ {z | q x z = 0}).Countable := by
    refine Set.Countable.mono ?_ (s26u_zeros_countable hq hne x)
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  refine s13x_removable (L := localMapDomain e x ∩ {z | q x z = 0}) hΩ
    (s26u_one_le_K hk₀ hk) (qcl_f_isHomeomorphOnto_of_injOn hΩ hcont hinj)
    (hLc.measure_zero _) (Eventually.of_forall fun a => ?_) (Eventually.of_forall fun b => ?_)
    fun z hz => s82td_u_local hq hne hk₀ hk hregf x hz.1 fun h0 => hz.2 ⟨hz.1, h0⟩
  · refine hLc.preimage (f := fun y : ℝ => (a : ℂ) + (y : ℂ) * I) fun y₁ y₂ hy => ?_
    have := congrArg Complex.im hy
    simpa using this
  · refine hLc.preimage (f := fun x : ℝ => (x : ℂ) + (b : ℂ) * I) fun x₁ x₂ hx => ?_
    have := congrArg Complex.re hx
    simpa using this

/-- **[copy of `s26u_isKQCRS`, non-closed target]** The deformation map is `K`-quasiconformal, `K = (1+k)/(1-k)`. -/
theorem s82td_u_isKQCRS {q : S₀ → ℂ → ℂ} {k : ℝ} {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {e : S₀ ≃ₜ X} {q' : X → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (hk₀ : 0 ≤ k)
    (hk : k < 1) (hregf : ∀ p : S₀, IsRegularPoint q p → IsRegularPoint q' (e p) ∧
      ∃ ζ ζ' : ℂ → ℂ, IsNaturalParameterAt q p ζ ∧ IsNaturalParameterAt q' (e p) ζ' ∧
        ∀ᶠ z in 𝓝 (chartAt ℂ p p), ζ' (localMapExpr e p z) = teichStretch k (ζ z)) :
    IsKQCRS e ((1 + k) / (1 - k)) :=
  ⟨s26u_one_le_K hk₀ hk, fun x => s82td_u_isKQC_chart hq hne hk₀ hk hregf x⟩

/-- **The deformation map from the §26.2 charts** (the second half of `s26d_a_exists`, for any target surface): if
the preferred charts of `Y` at the points `e p` are the new charts `ψ_p` and `q'(e p)` is the coefficient
`((m_p+2)/2)² w^{m_p}` on their targets, then `e` is a Teichmüller map for `(q, q', k)`. -/
theorem s82td_teich_of_charts {Y : Type u} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) {m : S₀ → ℕ}
    {ζ : S₀ → ℂ → ℂ} {Z : S₀ → OpenPartialHomeomorph ℂ ℂ} (hD : ∀ p, s26d_a_Data q p (m p) (ζ p) (Z p))
    (e : S₀ ≃ₜ Y) (hchart : ∀ p x, chartAt ℂ (e p) (e x) = s26d_a_psi hk₀ hk m Z p x) (q' : Y → ℂ → ℂ)
    (hq' : IsHolQuadDiff q')
    (hq'Q : ∀ p, q' (e p) = (s26d_a_psi hk₀ hk m Z p).target.indicator (fun w => ((m p + 2 : ℂ) / 2) ^ 2 * w ^ m p)) :
    IsTeichmullerMap e q q' k := by
  set ψ := s26d_a_psi hk₀ hk m Z with hψ
  have hQt : ∀ p, ∀ w ∈ (ψ p).target, q' (e p) w = ((m p + 2 : ℂ) / 2) ^ 2 * w ^ m p := fun p w hw => by
    rw [hq'Q p]
    exact Set.indicator_of_mem hw _
  have hc : ∀ p, chartAt ℂ (e p) (e p) = 0 := fun p => by
    rw [hchart p p]
    exact (s26d_a_psi_center hk₀ hk hD p).2
  have htarget : ∀ p, (ψ p).target ∈ 𝓝 (0 : ℂ) := fun p => by
    have h1 := (ψ p).map_source (s26d_a_psi_center hk₀ hk hD p).1
    rw [(s26d_a_psi_center hk₀ hk hD p).2] at h1
    exact (ψ p).open_target.mem_nhds h1
  have hloc : ∀ p, ∀ᶠ z in 𝓝 (chartAt ℂ p p), localMapExpr e p z = teichStretchZero k (m p) (ζ p z) :=
    fun p => by
      filter_upwards [(chartAt ℂ p).open_target.mem_nhds ((chartAt ℂ p).map_source (mem_chart_source ℂ p))]
        with z hz
      show chartAt ℂ (e p) (e ((chartAt ℂ p).symm z)) = _
      rw [hchart p, s26d_a_psi_chart hk₀ hk hD p hz]
  have hnat : ∀ p, IsNaturalParameterAtZero q' (e p) (m p) id := fun p => by
    refine ⟨analyticAt_id, by rw [hc p]; rfl, by rw [deriv_id]; exact one_ne_zero, ?_⟩
    rw [hc p]
    filter_upwards [htarget p] with z hz
    rw [hQt p z hz, deriv_id, id_eq, one_pow, mul_one]
  have hregular : ∀ p : S₀, IsRegularPoint q p → IsRegularPoint q' (e p) ∧
      ∃ ζ₁ ζ' : ℂ → ℂ, IsNaturalParameterAt q p ζ₁ ∧ IsNaturalParameterAt q' (e p) ζ' ∧
        ∀ᶠ z in 𝓝 (chartAt ℂ p p), ζ' (localMapExpr e p z) = teichStretch k (ζ₁ z) := by
    intro p hp
    have hm : m p = 0 := (hD p).regular_iff.1 hp
    have hnp := hnat p
    have hnq := (hD p).natural
    rw [hm] at hnp hnq
    refine ⟨?_, ζ p, id, ⟨hnq.1, hnq.2.1, hnq.2.2.1, hnq.2.2.2.mono fun z hz => ?_⟩,
      ⟨hnp.1, hnp.2.1, hnp.2.2.1, hnp.2.2.2.mono fun z hz => ?_⟩, (hloc p).mono fun z hz => ?_⟩
    · show q' (e p) (chartAt ℂ (e p) (e p)) ≠ 0
      rw [hc p, hQt p 0 (mem_of_mem_nhds (htarget p)), hm]
      norm_num
    · rw [hz]
      norm_num
    · rw [hz]
      norm_num
    · rw [id_eq, hz, hm, s26d_a_teichStretchZero_zero]
  refine ⟨⟨_, s82td_u_isKQCRS hq hne hk₀ hk hregular⟩, hq, hne, hq', hk₀, hk, hregular, fun p n hn => ?_⟩
  -- zeros of order `n`: `n = m p`
  have hnm : n = m p := by
    have h1 := hn.symm.trans (hD p).order
    exact_mod_cast h1
  subst hnm
  show meromorphicOrderAt (q' (e p)) (chartAt ℂ (e p) (e p)) = ((m p : ℕ) : ℤ)
  have hev : q' (e p) =ᶠ[𝓝 0] fun z => ((m p + 2 : ℂ) / 2) ^ 2 * z ^ m p := by
    filter_upwards [htarget p] with z hz
    exact hQt p z hz
  have han : AnalyticAt ℂ (q' (e p)) 0 :=
    (analyticAt_const.mul (analyticAt_id.pow _)).congr hev.symm
  rw [hc p, meromorphicOrderAt_eq_int_iff han.meromorphicAt]
  refine ⟨fun _ => ((m p + 2 : ℂ) / 2) ^ 2, analyticAt_const, ?_,
    (hev.filter_mono nhdsWithin_le_nhds).mono fun z hz => ?_⟩
  · refine pow_ne_zero _ (div_ne_zero ?_ two_ne_zero)
    exact_mod_cast (by omega : (m p + 2 : ℕ) ≠ 0)
  · rw [hz, sub_zero, zpow_natCast, smul_eq_mul, mul_comm]

/-- **[stub W4(B)] Realization with punctures and no holes** (`m = 0`, `n ≠ 0`): deform the closed surface `X` of
`F₀` by the meromorphic `qh` (simple poles at the punctures, pole charts `t ↦ T_k(t)²` of the order `-1` model) and
take the punctured deformed surface. -/
theorem s82td_realize_punctured {g n m : ℕ} (hex : ¬ IsExceptionalType g n m) (F₀ : FiniteTypeStructure S₀ g n m)
    (hm : m = 0) (hn : n ≠ 0) {q : S₀ → ℂ → ℂ} (hq : q ∈ admissibleQDInterior F₀) (hq0 : q ≠ 0) {k : ℝ}
    (hk0 : 0 < k) (hk1 : k < 1) :
    ∃ (A : MarkedFiniteTypeRS S₀ g n m) (q' : A.X.carrier → ℂ → ℂ), IsAdmissibleTeichmullerMap F₀ A.marking q q' k := by
  subst hm
  classical
  obtain ⟨qh, hqh, rfl⟩ := Submodule.mem_map.1 hq
  have hqq : pullbackQDLinear F₀ qh = pullbackQD F₀ qh := rfl
  rw [hqq] at hq0 ⊢
  have hqhol : IsHolQuadDiff (pullbackQD F₀ qh) := s32p_pullbackQD_isHolQuadDiff F₀ hqh
  choose mf ζf Zf hD using s26d_a_data_exists hqhol hq0
  set ψ := s26d_a_psi hk0.le hk1 mf Zf with hψ
  set ιe := F₀.embedding.toOpenPartialHomeomorph F₀.ι with hιe
  have hleft : ∀ s : S₀, ιe.symm (F₀.ι s) = s := fun s => F₀.embedding.toOpenPartialHomeomorph_left_inv F₀.ι
  have hrangeP : ∀ x : F₀.X.carrier, x ∈ range F₀.ι ↔ x ∉ F₀.P := by
    intro x
    rw [F₀.range_ι]
    simp
  -- the charts: puncture charts at `P`, transported §26.2 charts elsewhere
  have hB3 : ∀ p, p ∈ F₀.P → ∃ χ : OpenPartialHomeomorph F₀.X.carrier ℂ, p ∈ χ.source ∧
      (∀ x ∈ χ.source, x ∈ F₀.P → x = p) ∧
      (∀ s : S₀, ∀ w ∈ χ.target, χ.symm w ∈ (ιe.symm.trans (ψ s)).source →
        DifferentiableAt ℂ (fun w => (ιe.symm.trans (ψ s)) (χ.symm w)) w) ∧
      (∀ s : S₀, ∀ w ∈ (ιe.symm.trans (ψ s)).target, (ιe.symm.trans (ψ s)).symm w ∈ χ.source →
        DifferentiableAt ℂ (fun w => χ ((ιe.symm.trans (ψ s)).symm w)) w) ∧
      ∀ x ∈ χ.source, ∀ j, x ∉ F₀.D j :=
    fun p hp => s82td_puncture_chart F₀ hqh hk0.le hk1 hD hp
  haveI : Nonempty (OpenPartialHomeomorph F₀.X.carrier ℂ) := ⟨chartAt ℂ (Classical.arbitrary F₀.X.carrier)⟩
  choose! χf hχf using hB3
  set ψ' : F₀.X.carrier → OpenPartialHomeomorph F₀.X.carrier ℂ :=
    fun x => if x ∈ F₀.P then χf x else ιe.symm.trans (ψ (ιe.symm x)) with hψ'
  have hψ'P : ∀ x, x ∈ F₀.P → ψ' x = χf x := fun x hx => if_pos hx
  have hψ'ι : ∀ s : S₀, ψ' (F₀.ι s) = ιe.symm.trans (ψ s) := fun s => by
    rw [show ψ' (F₀.ι s) = ιe.symm.trans (ψ (ιe.symm (F₀.ι s))) from if_neg ((hrangeP _).1 (mem_range_self s)), hleft]
  have hΨapp : ∀ s y : S₀, (ιe.symm.trans (ψ s)) (F₀.ι y) = ψ s y := fun s y => by
    show ψ s (ιe.symm (F₀.ι y)) = _
    rw [hleft]
  have hΨsrc : ∀ (s : S₀) (y : F₀.X.carrier), y ∈ (ιe.symm.trans (ψ s)).source →
      ∃ x' : S₀, F₀.ι x' = y ∧ x' ∈ (ψ s).source := by
    intro s y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hyr : y ∈ range F₀.ι := by
      have : y ∈ ιe.target := hy1
      rwa [F₀.embedding.toOpenPartialHomeomorph_target] at this
    obtain ⟨x', rfl⟩ := hyr
    refine ⟨x', rfl, ?_⟩
    have : ιe.symm (F₀.ι x') ∈ (ψ s).source := hy2
    rwa [hleft] at this
  have hmem : ∀ x, x ∈ (ψ' x).source := by
    intro x
    by_cases hx : x ∈ F₀.P
    · rw [hψ'P x hx]
      exact (hχf x hx).1
    · obtain ⟨s, rfl⟩ := (hrangeP x).2 hx
      rw [hψ'ι]
      refine ⟨?_, ?_⟩
      · show F₀.ι s ∈ ιe.target
        rw [F₀.embedding.toOpenPartialHomeomorph_target]
        exact mem_range_self s
      · show ιe.symm (F₀.ι s) ∈ (ψ s).source
        rw [hleft]
        exact (s26d_a_psi_center hk0.le hk1 hD s).1
  -- transitions between transported charts are the §26.2 transitions
  have hΨΨ : ∀ (s s' : S₀) (w : ℂ), w ∈ (ιe.symm.trans (ψ s')).target →
      (ιe.symm.trans (ψ s')).symm w ∈ (ιe.symm.trans (ψ s)).source →
      DifferentiableAt ℂ (fun w => (ιe.symm.trans (ψ s)) ((ιe.symm.trans (ψ s')).symm w)) w := by
    intro s s' w hw hws
    have hw' : w ∈ (ψ s').target := hw.1
    have hsymm : ∀ v, (ιe.symm.trans (ψ s')).symm v = F₀.ι ((ψ s').symm v) := fun v => by
      show ιe ((ψ s').symm v) = _
      rw [hιe, F₀.embedding.toOpenPartialHomeomorph_apply]
    have hws' : (ψ s').symm w ∈ (ψ s).source := by
      obtain ⟨x', hx', hx'src⟩ := hΨsrc s _ hws
      rw [hsymm] at hx'
      rwa [← F₀.embedding.injective hx']
    have hfun : (fun w => (ιe.symm.trans (ψ s)) ((ιe.symm.trans (ψ s')).symm w)) =
        fun w => ψ s ((ψ s').symm w) := by
      funext v
      rw [hsymm, hΨapp]
    rw [hfun]
    exact (s26d_a_transition hqhol hk0.le hk1 hD s s' hw' hws').1
  have hcompat : ∀ p p', ∀ w ∈ (ψ' p').target, (ψ' p').symm w ∈ (ψ' p).source →
      DifferentiableAt ℂ (fun w => ψ' p ((ψ' p').symm w)) w := by
    intro p p' w hw hwp
    by_cases hp : p ∈ F₀.P <;> by_cases hp' : p' ∈ F₀.P
    · -- two puncture charts
      rw [hψ'P p hp] at hwp ⊢
      rw [hψ'P p' hp'] at hw hwp ⊢
      by_cases hpp : p = p'
      · subst hpp
        have hid : (fun v => χf p ((χf p).symm v)) =ᶠ[𝓝 w] fun v => v := by
          filter_upwards [(χf p).open_target.mem_nhds hw] with v hv
          exact (χf p).right_inv hv
        exact differentiableAt_id.congr_of_eventuallyEq hid
      · -- the common point is not a puncture: factor through a transported chart
        set y := (χf p').symm w with hy
        have hy' : y ∈ (χf p').source := (χf p').map_target hw
        have hyP : y ∉ F₀.P := by
          intro hyP
          exact hpp (((hχf p hp).2.1 y hwp hyP).symm.trans ((hχf p' hp').2.1 y hy' hyP))
        obtain ⟨s, hs⟩ := (hrangeP y).2 hyP
        have hys : y ∈ (ιe.symm.trans (ψ s)).source := by
          have := hmem y
          rw [← hs, hψ'ι] at this
          rw [← hs]
          exact this
        have h1 := (hχf p' hp').2.2.1 s w hw (by rw [← hy]; exact hys)
        have hv : (ιe.symm.trans (ψ s)) y ∈ (ιe.symm.trans (ψ s)).target :=
          (ιe.symm.trans (ψ s)).map_source hys
        have hvs : (ιe.symm.trans (ψ s)).symm ((ιe.symm.trans (ψ s)) y) = y :=
          (ιe.symm.trans (ψ s)).left_inv hys
        have h2 := (hχf p hp).2.2.2.1 s _ hv (by rw [hvs]; exact hwp)
        have h3 : DifferentiableAt ℂ (fun v => χf p ((ιe.symm.trans (ψ s)).symm v))
            ((fun w => (ιe.symm.trans (ψ s)) ((χf p').symm w)) w) := h2
        have heq : (fun w => χf p ((χf p').symm w)) =ᶠ[𝓝 w]
            (fun v => χf p ((ιe.symm.trans (ψ s)).symm v)) ∘ fun w => (ιe.symm.trans (ψ s)) ((χf p').symm w) := by
          have hc : ContinuousAt (χf p').symm w := (χf p').continuousAt_symm hw
          filter_upwards [hc.preimage_mem_nhds ((ιe.symm.trans (ψ s)).open_source.mem_nhds hys)] with v hv
          simp only [Function.comp_apply]
          rw [(ιe.symm.trans (ψ s)).left_inv hv]
        exact (h3.comp w h1).congr_of_eventuallyEq heq
    · -- puncture chart after a transported chart
      obtain ⟨s', rfl⟩ := (hrangeP p').2 hp'
      rw [hψ'P p hp] at hwp ⊢
      rw [hψ'ι] at hw hwp ⊢
      exact (hχf p hp).2.2.2.1 s' w hw hwp
    · obtain ⟨s, rfl⟩ := (hrangeP p).2 hp
      rw [hψ'ι] at hwp ⊢
      rw [hψ'P p' hp'] at hw hwp ⊢
      exact (hχf p' hp').2.2.1 s w hw hwp
    · obtain ⟨s, rfl⟩ := (hrangeP p).2 hp
      obtain ⟨s', rfl⟩ := (hrangeP p').2 hp'
      rw [hψ'ι] at hwp ⊢
      rw [hψ'ι] at hw hwp ⊢
      exact hΨΨ s s' w hw hwp
  -- the deformed closed surface
  obtain ⟨X', τX, csX, hT2, hconn, hcpt, hman, e, he⟩ := s82td_charted_package ψ' hmem hcompat
  let XR : ClosedRS.{u} := ⟨X'⟩
  have hgen : HasGenus XR.carrier g := hasGenus_of_homeomorph F₀.genus (e : F₀.X.carrier ≃ₜ XR.carrier)
  set P' : Finset XR.carrier := F₀.P.map e.toEquiv.toEmbedding with hP'
  have hP'card : P'.card = n := by rw [hP', Finset.card_map, F₀.card_P]
  have hP'mem : ∀ x : F₀.X.carrier, e x ∈ P' ↔ x ∈ F₀.P := by
    intro x
    rw [hP', Finset.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := e.injective hyx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  haveI : ConnectedSpace (puncturedOpens P') := s31hy_connected_punctured P'
  obtain ⟨Fy⟩ := s31dm_punctured_fts (Xd := XR) P' hgen hP'card
  -- the marking `s ↦ e(ι s)`
  have hemb : Topology.IsEmbedding (fun s => e (F₀.ι s)) := e.isEmbedding.comp F₀.embedding.isEmbedding
  have hrange : range (fun s => e (F₀.ι s)) = ((puncturedOpens P' : TopologicalSpace.Opens XR.carrier) : Set XR.carrier) := by
    ext x
    obtain ⟨x₀, rfl⟩ := e.surjective x
    show (∃ s, e (F₀.ι s) = e x₀) ↔ e x₀ ∉ (↑P' : Set XR.carrier)
    rw [Finset.mem_coe, hP'mem]
    constructor
    · rintro ⟨s, hs⟩
      rw [← (hrangeP x₀)]
      exact ⟨s, e.injective hs⟩
    · intro h
      obtain ⟨s, hs⟩ := (hrangeP x₀).2 h
      exact ⟨s, by rw [hs]⟩
  set f : S₀ ≃ₜ puncturedOpens P' := hemb.toHomeomorph.trans (Homeomorph.setCongr hrange) with hf
  have hfv : ∀ s, (f s : XR.carrier) = e (F₀.ι s) := fun s => rfl
  -- charts of the punctured surface at `f s`
  have hchartv : ∀ s x, chartAt ℂ (f s) (f x) = ψ s x := by
    intro s x
    show chartAt ℂ ((f s : XR.carrier)) ((f x : XR.carrier)) = _
    rw [hfv, hfv, (he (F₀.ι s)).1, hψ'ι, hΨapp]
  have hchartS : ∀ s, chartAt ℂ (f s : XR.carrier) = chartAt ℂ (e (F₀.ι s)) := fun s => by rw [hfv]
  have htgt : ∀ s, (chartAt ℂ (f s)).target = (ψ s).target := by
    intro s
    have h1 : (chartAt ℂ (f s)).target =
        (chartAt ℂ (f s : XR.carrier)).target ∩ (chartAt ℂ (f s : XR.carrier)).symm ⁻¹' (puncturedOpens P' : Set XR.carrier) := by
      rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_def,
        OpenPartialHomeomorph.trans_target, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
    rw [h1, hchartS, (he (F₀.ι s)).2.2.1, hψ'ι]
    ext w
    constructor
    · rintro ⟨⟨hw1, -⟩, -⟩
      exact hw1
    · intro hw
      refine ⟨⟨hw, ?_⟩, ?_⟩
      · show (ψ s).symm w ∈ ιe.source
        rw [F₀.embedding.toOpenPartialHomeomorph_source]
        exact mem_univ _
      · rw [mem_preimage, (he (F₀.ι s)).2.2.2, hψ'ι]
        show e (ιe ((ψ s).symm w)) ∈ (puncturedOpens P' : Set XR.carrier)
        rw [← hrange]
        refine ⟨(ψ s).symm w, ?_⟩
        rw [hιe, F₀.embedding.toOpenPartialHomeomorph_apply]
  -- the terminal differential on the punctured surface
  set q'' : puncturedOpens P' → ℂ → ℂ := fun y => (chartAt ℂ y).target.indicator
    (fun w => ((mf (f.symm y) + 2 : ℂ) / 2) ^ 2 * w ^ mf (f.symm y)) with hq''
  have hq''Q : ∀ s, q'' (f s) = (ψ s).target.indicator (fun w => ((mf s + 2 : ℂ) / 2) ^ 2 * w ^ mf s) := by
    intro s
    show (chartAt ℂ (f s)).target.indicator _ = _
    rw [htgt, f.symm_apply_apply]
  have hsymmv : ∀ s, ∀ w ∈ (ψ s).target, ((chartAt ℂ (f s)).symm w : XR.carrier) = e (F₀.ι ((ψ s).symm w)) := by
    intro s w hw
    have hw' : w ∈ ((chartAt ℂ (f s : XR.carrier)).subtypeRestr ⟨f s⟩).target := by
      have : w ∈ (chartAt ℂ (f s)).target := by rw [htgt]; exact hw
      exact this
    have h1 := OpenPartialHomeomorph.subtypeRestr_symm_apply (chartAt ℂ (f s : XR.carrier)) ⟨f s⟩ hw'
    simp only [Function.comp_apply] at h1
    show (((chartAt ℂ (f s : XR.carrier)).subtypeRestr ⟨f s⟩).symm w : XR.carrier) = _
    rw [h1, hchartS, (he (F₀.ι s)).2.2.2, hψ'ι]
    show e (ιe ((ψ s).symm w)) = _
    rw [hιe, F₀.embedding.toOpenPartialHomeomorph_apply]
  have hsymmf : ∀ s, ∀ w ∈ (ψ s).target, (chartAt ℂ (f s)).symm w = f ((ψ s).symm w) := by
    intro s w hw
    apply Subtype.ext
    rw [hsymmv s w hw, hfv]
  have hq''hol : IsHolQuadDiff q'' := by
    refine ⟨⟨fun y z hz => Set.indicator_of_notMem hz _, fun y y' z hz hzy => ?_⟩, fun y => ?_⟩
    · obtain ⟨s, rfl⟩ := f.surjective y
      obtain ⟨s', rfl⟩ := f.surjective y'
      have hz' : z ∈ (ψ s').target := by rw [← htgt]; exact hz
      have hτ : ∀ v ∈ (ψ s').target, chartTransition (f s) (f s') v = ψ s ((ψ s').symm v) := by
        intro v hv
        show chartAt ℂ (f s) ((chartAt ℂ (f s')).symm v) = _
        rw [hsymmf s' v hv, hchartv]
      have hws : (ψ s').symm z ∈ (ψ s).source := by
        have h1 : ((chartAt ℂ (f s')).symm z : XR.carrier) ∈ (chartAt ℂ (f s : XR.carrier)).source := by
          have h0 := hzy
          rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source] at h0
          exact h0
        rw [hsymmv s' z hz', hchartS, (he (F₀.ι s)).2.1, hψ'ι] at h1
        obtain ⟨y₀, hy₀, hy₀e⟩ := h1
        have hy₀' : y₀ = F₀.ι ((ψ s').symm z) := e.injective hy₀e
        rw [hy₀'] at hy₀
        obtain ⟨x', hx', hx'src⟩ := hΨsrc s _ hy₀
        rwa [← F₀.embedding.injective hx']
      obtain ⟨-, hlaw⟩ := s26d_a_transition hqhol hk0.le hk1 hD s s' hz' hws
      have hderiv : deriv (chartTransition (f s) (f s')) z = deriv (fun w => ψ s ((ψ s').symm w)) z := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [(ψ s').open_target.mem_nhds hz'] with v hv
        exact hτ v hv
      rw [hq''Q, hq''Q, Set.indicator_of_mem hz', hτ z hz', Set.indicator_of_mem ((ψ s).map_source hws), hderiv,
        zpow_zero, mul_one, zpow_two, ← pow_two]
      exact hlaw
    · obtain ⟨s, rfl⟩ := f.surjective y
      rw [hq''Q, htgt]
      exact ((differentiable_const _).mul (differentiable_pow _)).differentiableOn.congr
        fun w hw => Set.indicator_of_mem hw _
  have hT := s82td_teich_of_charts hqhol hq0 hk0.le hk1 hD f hchartv q'' hq''hol hq''Q
  exact ⟨⟨⟨puncturedOpens P', Fy⟩, f, hT.qc⟩, q'', hq, hT⟩

/-- **[stub C1] Cone extension**: a homeomorphism `b` of the unit circle extends to a homeomorphism of the closed
unit disc (`z ↦ ‖z‖ b(z/‖z‖)`). -/
theorem s82td_cone_extension {b : ℂ → ℂ} (hb : ContinuousOn b (sphere (0 : ℂ) 1))
    (hbij : BijOn b (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1)) :
    ∃ τ : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1,
      ∀ (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1), ‖z‖ = 1 → (τ ⟨z, hz⟩ : ℂ) = b z := by
  classical
  have hn : ∀ u ∈ sphere (0 : ℂ) 1, ‖b u‖ = 1 := fun u hu => mem_sphere_zero_iff_norm.1 (hbij.mapsTo hu)
  have hsph : ∀ z : ℂ, z ≠ 0 → z / (‖z‖ : ℂ) ∈ sphere (0 : ℂ) 1 := by
    intro z hz
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hz)]
  let c : ℂ → ℂ := fun z => if z = 0 then 0 else (‖z‖ : ℂ) * b (z / (‖z‖ : ℂ))
  have hcn : ∀ z, ‖c z‖ = ‖z‖ := by
    intro z
    by_cases hz : z = 0
    · simp [c, hz]
    · simp only [c, if_neg hz]
      rw [norm_mul, Complex.norm_real, norm_norm, hn _ (hsph z hz), mul_one]
  have hcc : Continuous c := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = 0
    · subst hz
      have h0 : c 0 = 0 := by simp [c]
      rw [ContinuousAt, h0]
      apply tendsto_zero_iff_norm_tendsto_zero.2
      have : (fun w => ‖c w‖) = fun w => ‖w‖ := funext hcn
      rw [this]
      exact tendsto_norm_zero
    · have hev : c =ᶠ[𝓝 z] fun w => (‖w‖ : ℂ) * b (w / (‖w‖ : ℂ)) := by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        simp only [c, if_neg (show w ≠ 0 from hw)]
      refine ContinuousAt.congr ?_ hev.symm
      have hnc : ContinuousAt (fun w : ℂ => (‖w‖ : ℂ)) z :=
        (Complex.continuous_ofReal.comp continuous_norm).continuousAt
      have h1 : ContinuousAt (fun w : ℂ => w / (‖w‖ : ℂ)) z :=
        continuousAt_id.div hnc (by simpa using hz)
      have h1s : ∀ᶠ w in 𝓝 z, w / (‖w‖ : ℂ) ∈ sphere (0 : ℂ) 1 := by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        exact hsph w hw
      have h2 : ContinuousAt (fun w => b (w / (‖w‖ : ℂ))) z :=
        (hb _ (hsph z hz)).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨h1, h1s⟩)
      exact hnc.mul h2
  have hmem : ∀ z : closedBall (0 : ℂ) 1, c z.1 ∈ closedBall (0 : ℂ) 1 := by
    intro z
    rw [mem_closedBall_zero_iff, hcn]
    exact mem_closedBall_zero_iff.1 z.2
  let τ0 : closedBall (0 : ℂ) 1 → closedBall (0 : ℂ) 1 := fun z => ⟨c z.1, hmem z⟩
  have hinj : Function.Injective τ0 := by
    intro z w h
    have h' : c z.1 = c w.1 := congrArg Subtype.val h
    have hzw : ‖z.1‖ = ‖w.1‖ := by rw [← hcn, h', hcn]
    by_cases hz : z.1 = 0
    · have hw : w.1 = 0 := by rw [← norm_eq_zero, ← hzw, hz, norm_zero]
      exact Subtype.ext (hz.trans hw.symm)
    · have hw : w.1 ≠ 0 := fun h0 => hz (by rw [← norm_eq_zero, hzw, h0, norm_zero])
      have e1 : (‖z.1‖ : ℂ) * b (z.1 / (‖z.1‖ : ℂ)) = (‖w.1‖ : ℂ) * b (w.1 / (‖w.1‖ : ℂ)) := by
        have h1 : c z.1 = (‖z.1‖ : ℂ) * b (z.1 / (‖z.1‖ : ℂ)) := if_neg hz
        have h2 : c w.1 = (‖w.1‖ : ℂ) * b (w.1 / (‖w.1‖ : ℂ)) := if_neg hw
        rw [← h1, ← h2, h']
      have hs := hsph _ hz
      rw [hzw] at e1 hs
      have hne : (‖w.1‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw
      have u := hbij.injOn hs (hsph _ hw) (mul_left_cancel₀ hne e1)
      exact Subtype.ext ((div_left_inj' hne).1 u)
  have hsurj : Function.Surjective τ0 := by
    intro y
    by_cases hy : y.1 = 0
    · refine ⟨⟨0, mem_closedBall_self zero_le_one⟩, Subtype.ext ?_⟩
      show c 0 = y.1
      rw [hy]
      simp [c]
    · obtain ⟨v, hv, hbv⟩ := hbij.surjOn (hsph _ hy)
      have hv1 : ‖v‖ = 1 := mem_sphere_zero_iff_norm.1 hv
      have hne : (‖y.1‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hy
      have hzn : ‖(‖y.1‖ : ℂ) * v‖ = ‖y.1‖ := by rw [norm_mul, Complex.norm_real, norm_norm, hv1, mul_one]
      have hz0 : (‖y.1‖ : ℂ) * v ≠ 0 := by
        rw [← norm_ne_zero_iff, hzn]
        exact norm_ne_zero_iff.2 hy
      have hzv : (‖y.1‖ : ℂ) * v / ((‖(‖y.1‖ : ℂ) * v‖ : ℝ) : ℂ) = v := by
        rw [hzn, mul_div_cancel_left₀ v hne]
      refine ⟨⟨(‖y.1‖ : ℂ) * v, ?_⟩, Subtype.ext ?_⟩
      · rw [mem_closedBall_zero_iff, hzn]
        exact mem_closedBall_zero_iff.1 y.2
      · show c ((‖y.1‖ : ℂ) * v) = y.1
        have h1 : c ((‖y.1‖ : ℂ) * v) = ((‖(‖y.1‖ : ℂ) * v‖ : ℝ) : ℂ) *
            b ((‖y.1‖ : ℂ) * v / ((‖(‖y.1‖ : ℂ) * v‖ : ℝ) : ℂ)) := if_neg hz0
        rw [h1, hzv, hbv, hzn, mul_div_cancel₀ _ hne]
  haveI : CompactSpace (closedBall (0 : ℂ) 1) := isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  have hτc : Continuous (Equiv.ofBijective τ0 ⟨hinj, hsurj⟩) :=
    (hcc.comp continuous_subtype_val).subtype_mk _
  refine ⟨hτc.homeoOfEquivCompactToT2, fun z hz h1 => ?_⟩
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  show c z = b z
  have h2 : c z = (‖z‖ : ℂ) * b (z / (‖z‖ : ℂ)) := if_neg hz0
  rw [h2, h1, Complex.ofReal_one, div_one, one_mul]

/-- The Blaschke factor `M_a` on the closed unit disc: its denominator does not vanish, it preserves the circle and the
open disc (both ways), and `M_{-a}` inverts it. -/
theorem s82td_blaschke_closed {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    (1 : ℂ) - conj a * z ≠ 0 ∧ (‖blaschke a z‖ = 1 ↔ ‖z‖ = 1) ∧ (‖blaschke a z‖ < 1 ↔ ‖z‖ < 1) ∧
      blaschke (-a) (blaschke a z) = z := by
  have haz : ‖conj a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖a‖ * ‖z‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg a)
      _ < 1 := by rw [mul_one]; exact ha
  have hden : (1 : ℂ) - conj a * z ≠ 0 := by
    intro h
    have h1 : conj a * z = 1 := (sub_eq_zero.1 h).symm
    rw [h1, norm_one] at haz
    exact lt_irrefl _ haz
  have hpos : 0 < Complex.normSq (1 - conj a * z) := Complex.normSq_pos.2 hden
  have hkey := normSq_blaschke_key a z
  have hB : Complex.normSq (blaschke a z) = Complex.normSq (z - a) / Complex.normSq (1 - conj a * z) := by
    rw [blaschke, map_div₀]
  have haa : Complex.normSq a < 1 := LiZhongQC.normSq_lt_one_iff.2 ha
  have hn1 : ∀ w : ℂ, ‖w‖ = 1 ↔ Complex.normSq w = 1 := fun w => by
    rw [Complex.normSq_eq_norm_sq, pow_eq_one_iff_of_nonneg (norm_nonneg w) two_ne_zero]
  refine ⟨hden, ?_, ?_, ?_⟩
  · rw [hn1, hn1, hB, div_eq_one_iff_eq hpos.ne']
    constructor
    · intro h
      rw [h, sub_self] at hkey
      rcases mul_eq_zero.1 hkey.symm with h' | h'
      · linarith
      · linarith
    · intro h
      rw [h, sub_self, zero_mul, sub_eq_zero] at hkey
      exact hkey.symm
  · rw [← LiZhongQC.normSq_lt_one_iff, ← LiZhongQC.normSq_lt_one_iff, hB, div_lt_one hpos]
    constructor
    · intro h
      by_contra hc
      push_neg at hc
      nlinarith
    · intro h
      nlinarith
  · have hne : (1 : ℂ) - conj a * a ≠ 0 := by
      intro hcon
      have hre := congrArg Complex.re hcon
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
        Complex.zero_re] at hre
      rw [Complex.normSq_apply] at haa
      nlinarith
    have hden' : (1 : ℂ) - z * conj a ≠ 0 := by rw [mul_comm]; exact hden
    have key : (1 : ℂ) - conj (-a) * blaschke a z = (1 - conj a * a) / (1 - conj a * z) := by
      simp only [blaschke, map_neg, neg_mul, sub_neg_eq_add]
      field_simp
      ring
    have keynum : blaschke a z - -a = z * (1 - conj a * a) / (1 - conj a * z) := by
      simp only [blaschke, sub_neg_eq_add]
      field_simp
      ring
    have hden2 : (1 : ℂ) - conj (-a) * blaschke a z ≠ 0 := by
      rw [key]
      exact div_ne_zero hne hden
    rw [blaschke, div_eq_iff hden2, keynum, key, mul_div_assoc]

/-- A local inverse of an injective holomorphic map is holomorphic. -/
theorem s82td_inverse_differentiableAt {g G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hinj : InjOn g U) {z : ℂ} (hz : z ∈ U) (hG : ∀ᶠ v in 𝓝 (g z), G v ∈ U ∧ g (G v) = v) :
    DifferentiableAt ℂ G (g z) := by
  have hs : HasStrictDerivAt g (deriv g z) z := (hg.analyticAt (hU.mem_nhds hz)).hasStrictDerivAt
  have hne := deriv_ne_zero_of_injOn hU hg hinj hz
  have hL := hs.to_localInverse hne
  have hLr := hs.eventually_right_inverse hne
  have hLl := hs.eventually_left_inverse hne
  have hLz : hs.localInverse g (deriv g z) z hne (g z) = z := hLl.self_of_nhds
  have hLU : ∀ᶠ v in 𝓝 (g z), hs.localInverse g (deriv g z) z hne v ∈ U :=
    hL.hasDerivAt.continuousAt.preimage_mem_nhds (by rw [hLz]; exact hU.mem_nhds hz)
  have heq : G =ᶠ[𝓝 (g z)] hs.localInverse g (deriv g z) z hne := by
    filter_upwards [hG, hLr, hLU] with v h1 h2 h3
    exact hinj h1.1 h3 (h1.2.trans h2.symm)
  exact hL.hasDerivAt.differentiableAt.congr_of_eventuallyEq heq

/-- The exterior coordinate of a bounded Jordan domain `J`, read on `ℂ` from the closed-disc coordinate `e` of the
closed exterior: continuous on `Jᶜ`, the analytic formula off `closure J`, the circle exactly on `frontier J`,
injective, missing only the value `a = e(∞)`, and bounded away from the circle on closed sets avoiding `closure J`. -/
theorem s82td_ext_coordinate {J : Set ℂ} (hJ : IsJordanDomain J) (hb : Bornology.IsBounded J) {f : ℂ → ℂ}
    (e : ↥((toExt J)ᶜ) ≃ₜ closedBall (0 : ℂ) 1)
    (hef : ∀ z ∈ (closure J)ᶜ, ∀ hz : (z : ExtPlane) ∈ (toExt J)ᶜ, (e ⟨(z : ExtPlane), hz⟩).val = f z)
    (hei : ∀ z : ↥((toExt J)ᶜ), ‖(e z).val‖ < 1 ↔ z.val ∈ (closure (toExt J))ᶜ)
    (heb : ∀ z : ↥((toExt J)ᶜ), ‖(e z).val‖ = 1 ↔ z.val ∈ frontier (toExt J)) :
    ∃ (ê : ℂ → ℂ) (a : ℂ), ‖a‖ < 1 ∧ ContinuousOn ê Jᶜ ∧ (∀ z ∈ (closure J)ᶜ, ê z = f z) ∧
      (∀ z ∈ Jᶜ, ‖ê z‖ ≤ 1) ∧ (∀ z ∈ Jᶜ, ‖ê z‖ = 1 ↔ z ∈ frontier J) ∧ InjOn ê Jᶜ ∧
      (∀ z ∈ Jᶜ, ê z ≠ a) ∧ (∀ u : ℂ, ‖u‖ ≤ 1 → u ≠ a → ∃ z ∈ Jᶜ, ê z = u) ∧
      ∀ K : Set ℂ, IsClosed K → Disjoint K (closure J) → ∃ ρ : ℝ, ρ < 1 ∧ ∀ z ∈ K, ‖ê z‖ ≤ ρ := by
  classical
  have hJo : IsOpen J := hJ.1
  have hmem : ∀ z : ℂ, z ∈ Jᶜ → (z : ExtPlane) ∈ (toExt J)ᶜ := fun z hz h => hz (coe_mem_toExt_iff.1 h)
  have hinf : (OnePoint.infty : ExtPlane) ∈ (toExt J)ᶜ := by
    rintro ⟨z, -, hz⟩
    exact OnePoint.coe_ne_infty z hz
  have hcl : closure (toExt J) = toExt (closure J) := closure_toExt_of_isBounded' hb
  have hfr : frontier (toExt J) = toExt (frontier J) := frontier_toExt_of_isBounded' hb hJo
  set ê : ℂ → ℂ := fun z => if hz : (z : ExtPlane) ∈ (toExt J)ᶜ then (e ⟨z, hz⟩).val else 0 with hêdef
  have hêv : ∀ z (hz : z ∈ Jᶜ), ê z = (e ⟨z, hmem z hz⟩).val := fun z hz => dif_pos (hmem z hz)
  set a : ℂ := (e ⟨OnePoint.infty, hinf⟩).val with hadef
  have ha : ‖a‖ < 1 := by
    refine (hei _).2 ?_
    rw [hcl]
    rintro ⟨z, -, hz⟩
    exact OnePoint.coe_ne_infty z hz
  refine ⟨ê, a, ha, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine continuousOn_iff_continuous_restrict.2 ?_
    have hc : Continuous fun z : ↥Jᶜ => (e ⟨(z.1 : ExtPlane), hmem z.1 z.2⟩).val :=
      continuous_subtype_val.comp (e.continuous.comp
        ((OnePoint.continuous_coe.comp continuous_subtype_val).subtype_mk _))
    convert hc using 1
    funext z
    exact hêv z.1 z.2
  · intro z hz
    have hz' : z ∈ Jᶜ := fun h => hz (subset_closure h)
    rw [hêv z hz']
    exact hef z hz _
  · intro z hz
    rw [hêv z hz]
    exact mem_closedBall_zero_iff.1 (e _).2
  · intro z hz
    rw [hêv z hz, heb, hfr]
    exact coe_mem_toExt_iff
  · intro z hz w hw h
    rw [hêv z hz, hêv w hw] at h
    have h1 := e.injective (Subtype.ext h)
    exact OnePoint.coe_injective (congrArg Subtype.val h1)
  · intro z hz h
    rw [hêv z hz] at h
    have h1 := e.injective (Subtype.ext h)
    exact OnePoint.coe_ne_infty z (congrArg Subtype.val h1)
  · intro u hu hua
    set p := e.symm ⟨u, mem_closedBall_zero_iff.2 hu⟩ with hp
    have hpu : (e p).val = u := by rw [hp, e.apply_symm_apply]
    have hpinf : p.val ≠ OnePoint.infty := by
      intro h
      apply hua
      rw [← hpu, hadef]
      congr 2
      exact Subtype.ext h
    obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.1 hpinf
    have hzJ : z ∈ Jᶜ := by
      intro h
      apply p.2
      rw [← hz]
      exact coe_mem_toExt_iff.2 h
    refine ⟨z, hzJ, ?_⟩
    rw [hêv z hzJ, ← hpu]
    congr 2
    exact Subtype.ext hz
  · intro K hK hKJ
    have hKo : IsOpen (toExt Kᶜ) := isOpen_toExt_iff.2 hK.isOpen_compl
    let S : Set ↥((toExt J)ᶜ) := {p | p.val ∉ toExt Kᶜ}
    have hSc : IsClosed S := (hKo.preimage continuous_subtype_val).isClosed_compl
    have hJc : IsClosed ((toExt J)ᶜ : Set ExtPlane) := (isOpen_toExt_iff.2 hJo).isClosed_compl
    haveI : CompactSpace ↥((toExt J)ᶜ) := isCompact_iff_compactSpace.1 hJc.isCompact
    have hSk : IsCompact S := hSc.isCompact
    have hSn : (S).Nonempty := ⟨⟨OnePoint.infty, hinf⟩, by
      rintro ⟨z, -, hz⟩
      exact OnePoint.coe_ne_infty z hz⟩
    have hcont : ContinuousOn (fun p : ↥((toExt J)ᶜ) => ‖(e p).val‖) S :=
      (continuous_norm.comp (continuous_subtype_val.comp e.continuous)).continuousOn
    obtain ⟨p₀, hp₀S, hp₀⟩ := hSk.exists_isMaxOn hSn hcont
    refine ⟨‖(e p₀).val‖, ?_, ?_⟩
    · refine (hei p₀).2 ?_
      rw [hcl]
      rintro ⟨z, hz, hzp⟩
      apply hp₀S
      rw [← hzp]
      refine coe_mem_toExt_iff.2 fun hzK => ?_
      exact Set.disjoint_left.1 hKJ hzK hz
    · intro z hz
      have hzJ : z ∈ Jᶜ := fun h => Set.disjoint_left.1 hKJ hz (subset_closure h)
      rw [hêv z hzJ]
      refine hp₀ (show (⟨(z : ExtPlane), hmem z hzJ⟩ : ↥((toExt J)ᶜ)) ∈ S from ?_)
      intro h
      exact coe_mem_toExt_iff.1 h hz

/-- `conj x = x⁻¹` on the unit circle. -/
theorem s82td_conj_eq_inv {x : ℂ} (hx : ‖x‖ = 1) : conj x = x⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hx]
  simp

/-- **The planar hole coordinate.**  For a bounded Jordan domain `J` with the exterior coordinate of
`s78ra_fixed_hole_uniformizer` and an open `O ⊇ closure J`, there is a homeomorphism `Ω` of an open set `⊆ O` onto
`ball 0 r`, `r > 1`, with `closure J = {‖Ω‖ ≤ 1}`, holomorphic (with holomorphic inverse) off `closure J`: outside it is
`(M_a ∘ f)⁻¹` (`f` the exterior uniformizer, `a` its value at `∞`); inside it is the cone extension (C1) of the
boundary map read through the Riemann map of `J` (`s13x_th_exists_disc_uniformizer`). -/
theorem s82td_planar_hole {J : Set ℂ} (hJ : IsJordanDomain J) (hb : Bornology.IsBounded J) {f : ℂ → ℂ}
    (e : ↥((toExt J)ᶜ) ≃ₜ closedBall (0 : ℂ) 1)
    (hf : DifferentiableOn ℂ f (closure J)ᶜ) (hfi : InjOn f (closure J)ᶜ)
    (hef : ∀ z ∈ (closure J)ᶜ, ∀ hz : (z : ExtPlane) ∈ (toExt J)ᶜ, (e ⟨(z : ExtPlane), hz⟩).val = f z)
    (hei : ∀ z : ↥((toExt J)ᶜ), ‖(e z).val‖ < 1 ↔ z.val ∈ (closure (toExt J))ᶜ)
    (heb : ∀ z : ↥((toExt J)ᶜ), ‖(e z).val‖ = 1 ↔ z.val ∈ frontier (toExt J))
    {O : Set ℂ} (hO : IsOpen O) (hJO : closure J ⊆ O) :
    ∃ (Ω : OpenPartialHomeomorph ℂ ℂ) (r : ℝ), 1 < r ∧ Ω.target = ball (0 : ℂ) r ∧ Ω.source ⊆ O ∧
      closure J ⊆ Ω.source ∧ (∀ z ∈ Ω.source, z ∈ closure J ↔ ‖Ω z‖ ≤ 1) ∧
      (∀ z ∈ Ω.source, z ∉ closure J → DifferentiableAt ℂ Ω z) ∧
      (∀ w ∈ Ω.target, 1 < ‖w‖ → DifferentiableAt ℂ Ω.symm w) := by
  classical
  have hJo : IsOpen J := hJ.1
  obtain ⟨ê, a, ha, hêc, hêf, hê1, hêfr, hêi, hêa, hês, hêK⟩ := s82td_ext_coordinate hJ hb e hef hei heb
  have hfrJ : ∀ z, z ∈ frontier J → z ∈ closure J ∧ z ∉ J := fun z hz =>
    ⟨frontier_subset_closure hz, fun h => (hJo.frontier_eq ▸ hz).2 h⟩
  -- `ê` is `< 1` exactly off `closure J`
  have hêlt : ∀ z ∈ Jᶜ, ‖ê z‖ < 1 ↔ z ∉ closure J := by
    intro z hz
    constructor
    · intro h hzc
      have : z ∈ frontier J := by
        rw [hJo.frontier_eq]
        exact ⟨hzc, hz⟩
      exact absurd ((hêfr z hz).2 this) (ne_of_lt h)
    · intro h
      refine lt_of_le_of_ne (hê1 z hz) fun h1 => h ((hfrJ z ((hêfr z hz).1 h1)).1)
  -- the Blaschke factor `B = M_a`
  have hBc := fun {u : ℂ} (hu : ‖u‖ ≤ 1) => s82td_blaschke_closed ha hu
  have hB0 : ∀ u : ℂ, ‖u‖ ≤ 1 → u ≠ a → blaschke a u ≠ 0 := by
    intro u hu hua h
    apply hua
    have h1 := (hBc hu).1
    rw [blaschke, div_eq_zero_iff] at h
    rcases h with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h h1
  have hBd : ∀ u : ℂ, ‖u‖ ≤ 1 → DifferentiableAt ℂ (blaschke a) u := by
    intro u hu
    exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - a) u).div
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 1 - conj a * w) u) (hBc hu).1
  -- the Riemann map of `J` and its homeomorphic extension, read on `ℂ`
  obtain ⟨φ, ⟨hφd, hφi, hφim⟩, Φ, hΦ1, hΦc, hΦi, hΦim⟩ := s13x_th_exists_disc_uniformizer hJ
  have hcl : closure (toExt J) = toExt (closure J) := closure_toExt_of_isBounded' hb
  have hΦim' : Φ '' toExt (closure J) = toExt (closedBall (0 : ℂ) 1) := by
    rw [← hcl, hΦim, abN_closure_toExt_unitDisc]
  let C : OpenPartialHomeomorph ℂ ExtPlane :=
    OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : ℂ → ExtPlane)
  have hCt : C.target = range ((↑) : ℂ → ExtPlane) :=
    OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_target ((↑) : ℂ → ExtPlane)
  have hCi : ∀ z : ℂ, C.symm (z : ExtPlane) = z := fun z =>
    C.left_inv (show z ∈ C.source from by
      rw [OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_source]
      exact mem_univ z)
  set ρ : ℂ → ℂ := fun z => C.symm (Φ (z : ExtPlane)) with hρdef
  have hρv : ∀ z ∈ closure J, (ρ z : ExtPlane) = Φ z ∧ ‖ρ z‖ ≤ 1 := by
    intro z hz
    have h1 : Φ (z : ExtPlane) ∈ toExt (closedBall (0 : ℂ) 1) := hΦim' ▸ mem_image_of_mem Φ (coe_mem_toExt_iff.2 hz)
    obtain ⟨u, hu, hue⟩ := h1
    have h2 : ρ z = u := by
      show C.symm (Φ (z : ExtPlane)) = u
      rw [← hue, hCi]
    rw [h2]
    exact ⟨hue, mem_closedBall_zero_iff.1 hu⟩
  have hρc : ContinuousOn ρ (closure J) := by
    refine C.continuousOn_symm.comp (hΦc.comp OnePoint.continuous_coe.continuousOn ?_) ?_
    · intro z hz
      rw [hcl]
      exact coe_mem_toExt_iff.2 hz
    · intro z hz
      show Φ (z : ExtPlane) ∈ C.target
      rw [hCt, ← (hρv z hz).1]
      exact mem_range_self _
  have hρi : InjOn ρ (closure J) := by
    intro z hz w hw h
    have h1 : Φ (z : ExtPlane) = Φ (w : ExtPlane) := by rw [← (hρv z hz).1, ← (hρv w hw).1, h]
    have h2 := hΦi (by rw [hcl]; exact coe_mem_toExt_iff.2 hz) (by rw [hcl]; exact coe_mem_toExt_iff.2 hw) h1
    exact OnePoint.coe_injective h2
  have hρJ : ∀ z ∈ J, ρ z = φ z := by
    intro z hz
    show C.symm (Φ (z : ExtPlane)) = φ z
    rw [hΦ1 z hz, hCi]
  have hρs : ∀ u : ℂ, ‖u‖ ≤ 1 → ∃ z ∈ closure J, ρ z = u := by
    intro u hu
    have h1 : (u : ExtPlane) ∈ Φ '' toExt (closure J) := by
      rw [hΦim']
      exact coe_mem_toExt_iff.2 (mem_closedBall_zero_iff.2 hu)
    obtain ⟨p, ⟨z, hz, rfl⟩, hpu⟩ := h1
    refine ⟨z, hz, ?_⟩
    show C.symm (Φ (z : ExtPlane)) = u
    rw [hpu, hCi]
  have hρfr : ∀ z ∈ closure J, ‖ρ z‖ = 1 ↔ z ∈ frontier J := by
    intro z hz
    rw [hJo.frontier_eq]
    constructor
    · intro h
      refine ⟨hz, fun hzJ => ?_⟩
      have h1 : φ z ∈ unitDisc := hφim ▸ mem_image_of_mem φ hzJ
      have h2 : ‖φ z‖ < 1 := mem_ball_zero_iff.1 h1
      rw [← hρJ z hzJ, h] at h2
      exact lt_irrefl _ h2
    · intro h
      refine le_antisymm (hρv z hz).2 (not_lt.1 fun hlt => h.2 ?_)
      have h1 : ρ z ∈ φ '' J := by rw [hφim]; exact mem_ball_zero_iff.2 hlt
      obtain ⟨w, hw, hwz⟩ := h1
      have h2 : ρ w = ρ z := by rw [hρJ w hw, hwz]
      rw [← hρi (subset_closure hw) hz h2]
      exact hw
  -- the inverse of `ρ` on the closed disc
  set ρi : ℂ → ℂ := Function.invFunOn ρ (closure J) with hρidef
  have hρiv : ∀ u : ℂ, ‖u‖ ≤ 1 → ρi u ∈ closure J ∧ ρ (ρi u) = u := by
    intro u hu
    obtain ⟨z, hz, hzu⟩ := hρs u hu
    exact ⟨Function.invFunOn_mem ⟨z, hz, hzu⟩, Function.invFunOn_eq ⟨z, hz, hzu⟩⟩
  have hρiρ : ∀ z ∈ closure J, ρi (ρ z) = z := fun z hz => hρi.leftInvOn_invFunOn hz
  have hρic : ContinuousOn ρi (closedBall (0 : ℂ) 1) := by
    have hJk : IsCompact (closure J) := hb.isCompact_closure
    haveI : CompactSpace ↥(closure J) := isCompact_iff_compactSpace.1 hJk
    let R0 : ↥(closure J) → ↥(closedBall (0 : ℂ) 1) := fun z =>
      ⟨ρ z.1, mem_closedBall_zero_iff.2 (hρv z.1 z.2).2⟩
    have hR0b : Function.Bijective R0 := by
      refine ⟨fun z w h => Subtype.ext (hρi z.2 w.2 (congrArg Subtype.val h)), fun u => ?_⟩
      obtain ⟨z, hz, hzu⟩ := hρs u.1 (mem_closedBall_zero_iff.1 u.2)
      exact ⟨⟨z, hz⟩, Subtype.ext hzu⟩
    have hR0c : Continuous (Equiv.ofBijective R0 hR0b) :=
      (continuousOn_iff_continuous_restrict.1 hρc).subtype_mk _
    let R := hR0c.homeoOfEquivCompactToT2
    refine continuousOn_iff_continuous_restrict.2 ?_
    convert continuous_subtype_val.comp R.symm.continuous using 1
    funext u
    have h1 : R (R.symm u) = u := R.apply_symm_apply u
    have h2 : ρ (R.symm u).val = u.val := congrArg Subtype.val h1
    show ρi u.val = (R.symm u).val
    rw [← h2, hρiρ _ (R.symm u).2]
  -- the boundary map and its cone extension
  set b : ℂ → ℂ := fun u => conj (blaschke a (ê (ρi u))) with hbdef
  have hρifr : ∀ u : ℂ, ‖u‖ = 1 → ρi u ∈ frontier J := by
    intro u hu
    have h1 := hρiv u hu.le
    rw [← hρfr _ h1.1, h1.2, hu]
  have hJc_of_fr : ∀ z, z ∈ frontier J → z ∈ Jᶜ := fun z hz => (hfrJ z hz).2
  have hbs : BijOn b (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) := by
    have hmaps : ∀ u ∈ sphere (0 : ℂ) 1, ‖b u‖ = 1 := by
      intro u hu
      have hu1 := mem_sphere_zero_iff_norm.1 hu
      have h1 := hρifr u hu1
      have h2 : ‖ê (ρi u)‖ = 1 := (hêfr _ (hJc_of_fr _ h1)).2 h1
      show ‖conj (blaschke a (ê (ρi u)))‖ = 1
      rw [Complex.norm_conj]
      exact ((hBc h2.le).2.1).2 h2
    refine ⟨fun u hu => mem_sphere_zero_iff_norm.2 (hmaps u hu), ?_, ?_⟩
    · intro u hu v hv h
      have hu1 := mem_sphere_zero_iff_norm.1 hu
      have hv1 := mem_sphere_zero_iff_norm.1 hv
      have h1 : blaschke a (ê (ρi u)) = blaschke a (ê (ρi v)) := by
        have := congrArg conj h
        simpa only [hbdef, Complex.conj_conj] using this
      have hu2 := hê1 _ (hJc_of_fr _ (hρifr u hu1))
      have hv2 := hê1 _ (hJc_of_fr _ (hρifr v hv1))
      have h2 : ê (ρi u) = ê (ρi v) := by
        rw [← (hBc hu2).2.2.2, h1, (hBc hv2).2.2.2]
      have h3 := hêi (hJc_of_fr _ (hρifr u hu1)) (hJc_of_fr _ (hρifr v hv1)) h2
      rw [← (hρiv u hu1.le).2, ← (hρiv v hv1.le).2, h3]
    · intro v hv
      have hv1 := mem_sphere_zero_iff_norm.1 hv
      have hcv : ‖conj v‖ = 1 := by rw [Complex.norm_conj]; exact hv1
      have hna : ‖-a‖ < 1 := by rw [norm_neg]; exact ha
      have ht := s82td_blaschke_closed hna hcv.le
      set t := blaschke (-a) (conj v) with htdef
      have ht1 : ‖t‖ = 1 := ht.2.1.2 hcv
      have hta : t ≠ a := fun h => by
        rw [h] at ht1
        rw [ht1] at ha
        exact lt_irrefl _ ha
      obtain ⟨z, hzJ, hzt⟩ := hês t ht1.le hta
      have hzfr : z ∈ frontier J := (hêfr z hzJ).1 (by rw [hzt]; exact ht1)
      have hzc := (hfrJ z hzfr).1
      refine ⟨ρ z, mem_sphere_zero_iff_norm.2 ((hρfr z hzc).2 hzfr), ?_⟩
      show conj (blaschke a (ê (ρi (ρ z)))) = v
      have hBB : blaschke a t = conj v := by
        have h' := ht.2.2.2
        rw [neg_neg] at h'
        exact h'
      rw [hρiρ z hzc, hzt, hBB, Complex.conj_conj]
  have hbc : ContinuousOn b (sphere (0 : ℂ) 1) := by
    intro u hu
    have hu1 := mem_sphere_zero_iff_norm.1 hu
    have h1 := hρifr u hu1
    have hzJ := hJc_of_fr _ h1
    have hA : ContinuousWithinAt ρi (sphere (0 : ℂ) 1) u :=
      (hρic u (sphere_subset_closedBall hu)).mono sphere_subset_closedBall
    have hE : ContinuousWithinAt (fun u => ê (ρi u)) (sphere (0 : ℂ) 1) u :=
      (hêc _ hzJ).comp hA fun v hv => hJc_of_fr _ (hρifr v (mem_sphere_zero_iff_norm.1 hv))
    have hB : ContinuousAt (blaschke a) (ê (ρi u)) := (hBd _ (hê1 _ hzJ)).continuousAt
    have h2 : ContinuousWithinAt (fun u => blaschke a (ê (ρi u))) (sphere (0 : ℂ) 1) u :=
      ContinuousAt.comp_continuousWithinAt (g := blaschke a) (f := fun u => ê (ρi u)) hB hE
    exact ContinuousAt.comp_continuousWithinAt (g := fun x => conj x) Complex.continuous_conj.continuousAt h2
  obtain ⟨τ, hτ⟩ := s82td_cone_extension hbc hbs
  set τc : ℂ → ℂ := fun u => if h : u ∈ closedBall (0 : ℂ) 1 then (τ ⟨u, h⟩).val else 0 with hτcdef
  have hτcv : ∀ u (hu : u ∈ closedBall (0 : ℂ) 1), τc u = (τ ⟨u, hu⟩).val := fun u hu => dif_pos hu
  have hτcc : ContinuousOn τc (closedBall (0 : ℂ) 1) := by
    refine continuousOn_iff_continuous_restrict.2 ?_
    convert continuous_subtype_val.comp τ.continuous using 1
    funext u
    exact hτcv u.1 u.2
  -- the glued coordinate `om`
  set om : ℂ → ℂ := fun z => if z ∈ closure J then τc (ρ z) else (blaschke a (ê z))⁻¹ with homdef
  have homin : ∀ z ∈ closure J, om z = τc (ρ z) := fun z hz => if_pos hz
  have homout : ∀ z, z ∉ closure J → om z = (blaschke a (ê z))⁻¹ := fun z hz => if_neg hz
  have hJc' : ∀ z, z ∉ closure J → z ∈ Jᶜ := fun z hz h => hz (subset_closure h)
  have hBlt : ∀ z, z ∉ closure J → ‖blaschke a (ê z)‖ < 1 ∧ blaschke a (ê z) ≠ 0 := by
    intro z hz
    have h1 := (hêlt z (hJc' z hz)).2 hz
    exact ⟨((hBc h1.le).2.2.1).2 h1, hB0 _ h1.le (hêa z (hJc' z hz))⟩
  have homnorm : ∀ z, z ∈ closure J ↔ ‖om z‖ ≤ 1 := by
    intro z
    constructor
    · intro hz
      rw [homin z hz, hτcv _ (mem_closedBall_zero_iff.2 (hρv z hz).2)]
      exact mem_closedBall_zero_iff.1 (τ _).2
    · intro h
      by_contra hz
      rw [homout z hz, norm_inv] at h
      obtain ⟨h1, h2⟩ := hBlt z hz
      have h3 : 1 < ‖blaschke a (ê z)‖⁻¹ := (one_lt_inv₀ (norm_pos_iff.2 h2)).2 h1
      linarith
  have homc : Continuous om := by
    refine continuous_if ?_ ?_ ?_
    · intro z hz
      have hz' : z ∈ frontier J := frontier_closure_subset hz
      have hzc := (hfrJ z hz').1
      have hρ1 : ‖ρ z‖ = 1 := (hρfr z hzc).2 hz'
      rw [hτcv _ (mem_closedBall_zero_iff.2 hρ1.le), hτ _ _ hρ1]
      show conj (blaschke a (ê (ρi (ρ z)))) = (blaschke a (ê z))⁻¹
      rw [hρiρ z hzc]
      have hzJ := hJc_of_fr _ hz'
      have h1 : ‖ê z‖ = 1 := (hêfr z hzJ).2 hz'
      exact s82td_conj_eq_inv (((hBc h1.le).2.1).2 h1)
    · show ContinuousOn _ (closure (closure J))
      rw [closure_closure]
      exact hτcc.comp hρc fun z hz => mem_closedBall_zero_iff.2 (hρv z hz).2
    · have hsub : closure {z : ℂ | ¬ z ∈ closure J} ⊆ Jᶜ := by
        intro z hz hzJ
        have h1 : z ∈ closure (closure J)ᶜ := hz
        rw [closure_compl] at h1
        exact h1 (interior_maximal subset_closure hJo hzJ)
      intro z hz
      have hzJ := hsub hz
      have hn := hê1 z hzJ
      have hne : blaschke a (ê z) ≠ 0 := hB0 _ hn (hêa z hzJ)
      have h1 : ContinuousWithinAt ê (closure {z : ℂ | ¬ z ∈ closure J}) z := (hêc z hzJ).mono hsub
      exact ((hBd _ hn).continuousAt.inv₀ hne).comp_continuousWithinAt h1
  have homi : Function.Injective om := by
    intro z w h
    by_cases hz : z ∈ closure J
    · have hw : w ∈ closure J := (homnorm w).2 (h ▸ (homnorm z).1 hz)
      rw [homin z hz, homin w hw, hτcv _ (mem_closedBall_zero_iff.2 (hρv z hz).2),
        hτcv _ (mem_closedBall_zero_iff.2 (hρv w hw).2)] at h
      have h1 := τ.injective (Subtype.ext h)
      exact hρi hz hw (congrArg Subtype.val h1)
    · have hw : w ∉ closure J := fun hw => hz ((homnorm z).2 (h.symm ▸ (homnorm w).1 hw))
      rw [homout z hz, homout w hw, inv_inj] at h
      have hz1 := hê1 z (hJc' z hz)
      have hw1 := hê1 w (hJc' w hw)
      have h2 : ê z = ê w := by rw [← (hBc hz1).2.2.2, h, (hBc hw1).2.2.2]
      exact hêi (hJc' z hz) (hJc' w hw) h2
  have homs : Function.Surjective om := by
    intro w
    by_cases hw : ‖w‖ ≤ 1
    · obtain ⟨u, hu⟩ := τ.surjective ⟨w, mem_closedBall_zero_iff.2 hw⟩
      obtain ⟨z, hz, hzu⟩ := hρs u.1 (mem_closedBall_zero_iff.1 u.2)
      refine ⟨z, ?_⟩
      rw [homin z hz, hzu, hτcv _ u.2, hu]
    · push_neg at hw
      have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
      have hwi : ‖w⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hw
      have hna : ‖-a‖ < 1 := by rw [norm_neg]; exact ha
      have ht := s82td_blaschke_closed hna hwi.le
      set t := blaschke (-a) w⁻¹ with htdef
      have ht1 : ‖t‖ < 1 := ht.2.2.1.2 hwi
      have hBt : blaschke a t = w⁻¹ := by
        have h' := ht.2.2.2
        rw [neg_neg] at h'
        exact h'
      have hta : t ≠ a := by
        intro h
        rw [h, blaschke_self] at hBt
        exact inv_ne_zero hw0 hBt.symm
      obtain ⟨z, hzJ, hzt⟩ := hês t ht1.le hta
      have hz : z ∉ closure J := (hêlt z hzJ).1 (by rw [hzt]; exact ht1)
      refine ⟨z, ?_⟩
      rw [homout z hz, hzt, hBt, inv_inv]
  -- the radius
  obtain ⟨R, hR⟩ := (hb.closure).subset_ball (0 : ℂ)
  set O' : Set ℂ := O ∩ ball (0 : ℂ) R with hO'
  have hO'o : IsOpen O' := hO.inter isOpen_ball
  have hJO' : closure J ⊆ O' := fun z hz => ⟨hJO hz, hR hz⟩
  obtain ⟨ρ₀, hρ₀, hρ₀K⟩ := hêK O'ᶜ hO'o.isClosed_compl (Set.disjoint_left.2 fun z hz hzJ => hz (hJO' hzJ))
  set ρ₀' : ℝ := max ρ₀ 0 with hρ₀'
  have hρ₀'1 : ρ₀' < 1 := max_lt hρ₀ one_pos
  have hcb : IsCompact (closedBall (0 : ℂ) ρ₀') := isCompact_closedBall 0 ρ₀'
  have hcbn : (closedBall (0 : ℂ) ρ₀').Nonempty := ⟨0, mem_closedBall_self (le_max_right _ _)⟩
  have hBcon : ContinuousOn (fun u => ‖blaschke a u‖) (closedBall (0 : ℂ) ρ₀') := by
    intro u hu
    have hu1 : ‖u‖ ≤ 1 := (mem_closedBall_zero_iff.1 hu).trans hρ₀'1.le
    exact (continuous_norm.continuousAt.comp (hBd u hu1).continuousAt).continuousWithinAt
  obtain ⟨u₀, hu₀, hu₀max⟩ := hcb.exists_isMaxOn hcbn hBcon
  have hu₀1 : ‖u₀‖ < 1 := lt_of_le_of_lt (mem_closedBall_zero_iff.1 hu₀) hρ₀'1
  set s : ℝ := max ‖blaschke a u₀‖ (1 / 2) with hsdef
  have hs1 : s < 1 := max_lt (((hBc hu₀1.le).2.2.1).2 hu₀1) (by norm_num)
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  set r : ℝ := (1 + s⁻¹) / 2 with hrdef
  have hs1' : 1 < s⁻¹ := (one_lt_inv₀ hs0).2 hs1
  have hr1 : 1 < r := by rw [hrdef]; linarith
  have hrs : r < s⁻¹ := by rw [hrdef]; linarith
  have hfar : ∀ z, z ∉ O' → r < ‖om z‖ := by
    intro z hz
    have hzc : z ∉ closure J := fun h => hz (hJO' h)
    obtain ⟨h1, h2⟩ := hBlt z hzc
    have h3 : ‖ê z‖ ≤ ρ₀' := (hρ₀K z hz).trans (le_max_left _ _)
    have h4 : ‖blaschke a (ê z)‖ ≤ s :=
      (hu₀max (mem_closedBall_zero_iff.2 h3)).trans (le_max_left _ _)
    rw [homout z hzc, norm_inv]
    exact lt_of_lt_of_le hrs ((inv_le_inv₀ hs0 (norm_pos_iff.2 h2)).2 h4)
  -- the inverse is continuous on the closed ball of radius `r` (compactness)
  have hK2 : IsCompact (om ⁻¹' closedBall (0 : ℂ) r) := by
    refine (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset (isClosed_closedBall.preimage homc) ?_
    intro z hz
    by_contra h
    have h1 : z ∉ O' := fun h' => h (ball_subset_closedBall h'.2)
    have := hfar z h1
    rw [mem_preimage, mem_closedBall_zero_iff] at hz
    linarith
  have hominv : ContinuousOn (Function.invFun om) (closedBall (0 : ℂ) r) := by
    haveI : CompactSpace ↥(om ⁻¹' closedBall (0 : ℂ) r) := isCompact_iff_compactSpace.1 hK2
    let T0 : ↥(om ⁻¹' closedBall (0 : ℂ) r) → ↥(closedBall (0 : ℂ) r) := fun z => ⟨om z.1, z.2⟩
    have hT0b : Function.Bijective T0 := by
      refine ⟨fun z w h => Subtype.ext (homi (congrArg Subtype.val h)), fun w => ?_⟩
      obtain ⟨z, hz⟩ := homs w.1
      exact ⟨⟨z, show om z ∈ closedBall (0 : ℂ) r from hz ▸ w.2⟩, Subtype.ext hz⟩
    have hT0c : Continuous (Equiv.ofBijective T0 hT0b) :=
      (homc.comp continuous_subtype_val).subtype_mk _
    let T := hT0c.homeoOfEquivCompactToT2
    refine continuousOn_iff_continuous_restrict.2 ?_
    convert continuous_subtype_val.comp T.symm.continuous using 1
    funext w
    have h1 : T (T.symm w) = w := T.apply_symm_apply w
    have h2 : om (T.symm w).val = w.val := congrArg Subtype.val h1
    show Function.invFun om w.val = (T.symm w).val
    rw [← h2, Function.leftInverse_invFun homi]
  let Ω : OpenPartialHomeomorph ℂ ℂ :=
    { toFun := om
      invFun := Function.invFun om
      source := om ⁻¹' ball (0 : ℂ) r
      target := ball (0 : ℂ) r
      map_source' := fun z hz => hz
      map_target' := fun w hw => by
        show om (Function.invFun om w) ∈ ball (0 : ℂ) r
        rw [Function.invFun_eq (homs w)]
        exact hw
      left_inv' := fun z _ => Function.leftInverse_invFun homi z
      right_inv' := fun w _ => Function.invFun_eq (homs w)
      open_source := isOpen_ball.preimage homc
      open_target := isOpen_ball
      continuousOn_toFun := homc.continuousOn
      continuousOn_invFun := hominv.mono ball_subset_closedBall }
  have hΩv : ∀ z, Ω z = om z := fun z => rfl
  have hΩsv : ∀ w, Ω.symm w = Function.invFun om w := fun w => rfl
  -- holomorphy off `closure J`
  have hg : DifferentiableOn ℂ (fun z => (blaschke a (f z))⁻¹) (closure J)ᶜ := by
    intro z hz
    have hzo : (closure J)ᶜ ∈ 𝓝 z := isClosed_closure.isOpen_compl.mem_nhds hz
    obtain ⟨h1, h2⟩ := hBlt z hz
    rw [hêf z hz] at h1 h2
    have hfz : ‖f z‖ ≤ 1 := by rw [← hêf z hz]; exact hê1 z (hJc' z hz)
    exact (((hBd _ hfz).comp z (hf.differentiableAt hzo)).inv h2).differentiableWithinAt
  have homg : ∀ z, z ∉ closure J → om z = (blaschke a (f z))⁻¹ := fun z hz => by rw [homout z hz, hêf z hz]
  have hgi : InjOn (fun z => (blaschke a (f z))⁻¹) (closure J)ᶜ := by
    intro z hz w hw h
    exact homi (by rw [homg z hz, homg w hw]; exact h)
  refine ⟨Ω, r, hr1, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    by_contra h
    have h1 : z ∉ O' := fun h' => h h'.1
    have h2 := hfar z h1
    have h3 : ‖om z‖ < r := mem_ball_zero_iff.1 hz
    linarith
  · intro z hz
    show om z ∈ ball (0 : ℂ) r
    rw [mem_ball_zero_iff]
    exact lt_of_le_of_lt ((homnorm z).1 hz) hr1
  · intro z _
    exact homnorm z
  · intro z _ hz
    have hzo : (closure J)ᶜ ∈ 𝓝 z := isClosed_closure.isOpen_compl.mem_nhds hz
    have heq : (fun z => (blaschke a (f z))⁻¹) =ᶠ[𝓝 z] om := by
      filter_upwards [hzo] with w hw
      exact (homg w hw).symm
    exact ((hg z hz).differentiableAt hzo).congr_of_eventuallyEq heq.symm
  · intro w hw hw1
    have hw' : w ∈ ball (0 : ℂ) r := hw
    set z := Function.invFun om w with hz
    have homz : om z = w := Function.invFun_eq (homs w)
    have hzc : z ∉ closure J := fun h => by
      have := (homnorm z).1 h
      rw [homz] at this
      linarith
    have hgz : (blaschke a (f z))⁻¹ = w := by rw [← homg z hzc, homz]
    have hev : ∀ᶠ v in 𝓝 w, Function.invFun om v ∈ (closure J)ᶜ ∧
        (fun z => (blaschke a (f z))⁻¹) (Function.invFun om v) = v := by
      have h1 : {v : ℂ | 1 < ‖v‖} ∈ 𝓝 w := (isOpen_lt continuous_const continuous_norm : IsOpen {v : ℂ | (1 : ℝ) < ‖v‖}).mem_nhds hw1
      filter_upwards [h1] with v hv
      have homv : om (Function.invFun om v) = v := Function.invFun_eq (homs v)
      have hvc : Function.invFun om v ∉ closure J := fun h => by
        have := (homnorm _).1 h
        rw [homv] at this
        exact absurd hv (not_lt.2 this)
      exact ⟨hvc, by rw [← homg _ hvc, homv]⟩
    have h := s82td_inverse_differentiableAt isClosed_closure.isOpen_compl hg hgi hzc (hgz ▸ hev)
    exact hgz ▸ h

/-- **One hole coordinate** inside a given open neighbourhood `U` of the hole: the planar hole coordinate
(`s82td_planar_hole`) composed with the chart of `s78ra_fixed_hole_uniformizer`. -/
theorem s82td_hole_coordinate_in {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (j : Fin m)
    {U : Set F₀.X.carrier} (hU : IsOpen U) (hDU : F₀.D j ⊆ U) :
    ∃ (W : OpenPartialHomeomorph F₀.X.carrier ℂ) (r : ℝ), 1 < r ∧ W.target = ball (0 : ℂ) r ∧
      F₀.D j ⊆ W.source ∧ W.source ⊆ U ∧ (∀ y ∈ W.source, y ∈ F₀.D j ↔ ‖W y‖ ≤ 1) ∧
      (∀ y ∈ W.source, y ∉ (↑F₀.P : Set F₀.X.carrier)) ∧
      (∀ y ∈ W.source, y ∉ F₀.D j → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) W y) ∧
      (∀ w ∈ W.target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) W.symm w) := by
  obtain ⟨x, J, N, hJ, hb, hN, hDN, hNs, hJt, hDJ, hNP, -, -, -, f, e, hf, hfi, hef, hei, heb⟩ :=
    s78ra_fixed_hole_uniformizer F₀ j
  set φ := chartAt ℂ x with hφ
  have hV : IsOpen (N ∩ U) := hN.inter hU
  set O : Set ℂ := φ.target ∩ φ.symm ⁻¹' (N ∩ U) with hOdef
  have hO : IsOpen O := φ.isOpen_inter_preimage_symm hV
  have hJO : closure J ⊆ O := by
    intro z hz
    refine ⟨hJt hz, ?_⟩
    rw [← hDJ] at hz
    obtain ⟨d, hd, rfl⟩ := hz
    show φ.symm (φ d) ∈ N ∩ U
    rw [φ.left_inv (hNs (hDN hd))]
    exact ⟨hDN hd, hDU hd⟩
  obtain ⟨Ω, r, hr, hΩt, hΩO, hJΩ, hiff, hΩd, hΩs⟩ := s82td_planar_hole hJ hb e hf hfi hef hei heb hO hJO
  have hsrc : ∀ y, y ∈ (φ.trans Ω).source ↔ y ∈ φ.source ∧ φ y ∈ Ω.source := fun y => by
    rw [OpenPartialHomeomorph.trans_source]
    rfl
  have hDφ : ∀ y ∈ φ.source, y ∈ F₀.D j ↔ φ y ∈ closure J := by
    intro y hy
    constructor
    · intro h
      rw [← hDJ]
      exact mem_image_of_mem φ h
    · intro h
      rw [← hDJ] at h
      obtain ⟨d, hd, hdy⟩ := h
      rw [← φ.injOn (hNs (hDN hd)) hy hdy]
      exact hd
  have hsubV : ∀ y ∈ (φ.trans Ω).source, y ∈ N ∩ U := by
    intro y hy
    obtain ⟨h1, h2⟩ := (hsrc y).1 hy
    have h3 := (hΩO h2).2
    rwa [mem_preimage, φ.left_inv h1] at h3
  refine ⟨φ.trans Ω, r, hr, ?_, ?_, fun y hy => (hsubV y hy).2, ?_, fun y hy => hNP y (hsubV y hy).1, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_target, hΩt]
    ext w
    constructor
    · intro h
      exact h.1
    · intro h
      refine ⟨h, ?_⟩
      have h1 : Ω.symm w ∈ Ω.source := Ω.map_target (hΩt ▸ h)
      exact (hΩO h1).1
  · intro d hd
    have hds : d ∈ φ.source := hNs (hDN hd)
    exact (hsrc d).2 ⟨hds, hJΩ ((hDφ d hds).1 hd)⟩
  · intro y hy
    obtain ⟨h1, h2⟩ := (hsrc y).1 hy
    rw [hDφ y h1]
    exact hiff (φ y) h2
  · intro y hy hyD
    obtain ⟨h1, h2⟩ := (hsrc y).1 hy
    have hyc : φ y ∉ closure J := fun h => hyD ((hDφ y h1).2 h)
    have hφm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ y := mdifferentiableAt_atlas (chart_mem_atlas ℂ x) h1
    have hΩm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) Ω (φ y) := (hΩd (φ y) h2 hyc).mdifferentiableAt
    exact hΩm.comp y hφm
  · intro w hw hw1
    have hw' : w ∈ Ω.target := by
      rw [OpenPartialHomeomorph.trans_target] at hw
      exact hw.1
    have hmem : Ω.symm w ∈ φ.target := (hΩO (Ω.map_target hw')).1
    have hΩm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) Ω.symm w := (hΩs w hw' hw1).mdifferentiableAt
    have hφm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ.symm (Ω.symm w) :=
      mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ x) hmem
    exact hφm.comp w hΩm

/-- **[stub C2] Hole coordinates**: around each hole `D j` of `F₀` there is a coordinate `W j` of the closed surface
(a topological chart, not in the atlas) onto the disc `‖w‖ < r j`, `r j > 1`, with `D j = {‖W j‖ ≤ 1}`, holomorphic off
`D j` (the exterior uniformizer `s78ra_fixed_hole_uniformizer`, inverted); inside `D j` it is a cone-extended homeomorphism
(Schoenflies `s31sh_jordan_disc_coordinates`). The sources avoid the punctures and are pairwise disjoint. -/
theorem s82td_hole_coordinates {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) :
    ∃ (W : Fin m → OpenPartialHomeomorph F₀.X.carrier ℂ) (r : Fin m → ℝ),
      (∀ j, 1 < r j ∧ (W j).target = ball (0 : ℂ) (r j) ∧ F₀.D j ⊆ (W j).source ∧
        (∀ y ∈ (W j).source, y ∈ F₀.D j ↔ ‖W j y‖ ≤ 1) ∧
        (∀ y ∈ (W j).source, y ∉ (↑F₀.P : Set F₀.X.carrier)) ∧
        (∀ y ∈ (W j).source, y ∉ F₀.D j → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j) y) ∧
        (∀ w ∈ (W j).target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j).symm w)) ∧
      Pairwise fun i j => Disjoint (W i).source (W j).source := by
  classical
  obtain ⟨U, hU, hUU⟩ := s31sd_disjoint_open_neighborhoods F₀.D
    (fun j => (s31eg_disc_compact (F₀.disc j)).isClosed) F₀.disjoint
  choose W r hW using fun j => s82td_hole_coordinate_in F₀ j (hU j).1 (hU j).2
  refine ⟨W, r, fun j => ⟨(hW j).1, (hW j).2.1, (hW j).2.2.1, (hW j).2.2.2.2.1, (hW j).2.2.2.2.2.1,
    (hW j).2.2.2.2.2.2.1, (hW j).2.2.2.2.2.2.2⟩, ?_⟩
  intro i j hij
  exact (hUU hij).mono (hW i).2.2.2.1 (hW j).2.2.2.1

/-- The circle reflection `σ(w) = conj (w⁻¹)` conjugating a homeomorphism `φ` of `ℂ` fixing `0` is continuous (at `0`
via `φ` being proper). -/
theorem s82td_sigma_continuous (φ : ℂ ≃ₜ ℂ) (h0 : φ 0 = 0) :
    Continuous (fun w : ℂ => (conj (φ (conj w⁻¹)))⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · subst hw
    rw [← continuousWithinAt_compl_self]
    have hv : (conj (φ (conj (0 : ℂ)⁻¹)))⁻¹ = 0 := by simp [h0]
    rw [ContinuousWithinAt, hv]
    let cH : ℂ ≃ₜ ℂ := Complex.conjLIE.toHomeomorph
    have hcH : ∀ z, cH z = conj z := fun z => Complex.conjLIE_apply z
    have t1 : Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_nhdsNE_zero
    have t2 : Tendsto (fun w : ℂ => conj w⁻¹) (𝓝[≠] 0) (cocompact ℂ) :=
      ((show Tendsto cH (cocompact ℂ) (cocompact ℂ) from cH.map_cocompact.le).comp t1).congr fun z => hcH _
    have t3 : Tendsto (fun w : ℂ => φ (conj w⁻¹)) (𝓝[≠] 0) (cocompact ℂ) := (show Tendsto φ (cocompact ℂ) (cocompact ℂ) from φ.map_cocompact.le).comp t2
    have t4 : Tendsto (fun w : ℂ => conj (φ (conj w⁻¹))) (𝓝[≠] 0) (cocompact ℂ) :=
      ((show Tendsto cH (cocompact ℂ) (cocompact ℂ) from cH.map_cocompact.le).comp t3).congr fun z => hcH _
    have t5 : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    exact t5.comp t4
  · have hne : conj (φ (conj w⁻¹)) ≠ 0 := by
      rw [map_ne_zero, ← h0, Ne, φ.injective.eq_iff, map_eq_zero, inv_eq_zero]
      exact hw
    have h1 : ContinuousAt (fun w : ℂ => conj w⁻¹) w :=
      Complex.continuous_conj.continuousAt.comp (continuousAt_inv₀ hw)
    have h2 : ContinuousAt (fun w : ℂ => conj (φ (conj w⁻¹))) w :=
      (Complex.continuous_conj.comp φ.continuous).continuousAt.comp h1
    exact h2.inv₀ hne

/-- The circle-reflection conjugate `σ ∘ φ ∘ σ` of a homeomorphism `φ` of `ℂ` fixing `0` is a homeomorphism of `ℂ`
(with inverse `σ ∘ φ⁻¹ ∘ σ`). -/
theorem s82td_sigma_homeo (φ : ℂ ≃ₜ ℂ) (h0 : φ 0 = 0) :
    ∃ G : ℂ ≃ₜ ℂ, ∀ w, G w = (conj (φ (conj w⁻¹)))⁻¹ := by
  have h0' : φ.symm 0 = 0 := by rw [Homeomorph.symm_apply_eq, h0]
  refine ⟨{ toFun := fun w => (conj (φ (conj w⁻¹)))⁻¹
            invFun := fun w => (conj (φ.symm (conj w⁻¹)))⁻¹
            left_inv := fun w => by simp [map_inv₀]
            right_inv := fun w => by simp [map_inv₀]
            continuous_toFun := s82td_sigma_continuous φ h0
            continuous_invFun := s82td_sigma_continuous φ.symm h0' }, fun w => rfl⟩

/-- A homeomorphism of `ℂ` is a homeomorphism of `ℂ` onto `ℂ` in the sense of `IsHomeomorphOnto`. -/
theorem s82td_isHomeomorphOnto_of_homeomorph (G : ℂ ≃ₜ ℂ) : IsHomeomorphOnto G univ univ := by
  refine ⟨G.continuous.continuousOn, G.injective.injOn, by rw [image_univ, G.range_coe], ?_⟩
  have h : Function.invFunOn G univ = G.symm := by
    funext y
    apply G.injective
    rw [Function.invFunOn_eq ⟨G.symm y, mem_univ _, G.apply_symm_apply y⟩, G.apply_symm_apply]
  rw [h]
  exact G.symm.continuous.continuousOn

/-- An a.e. property pulls back by the circle reflection `w ↦ conj (w⁻¹)` (a smooth map off `0` maps null sets to
null sets). -/
theorem s82td_ae_sigma {P : ℂ → Prop} (h : ∀ᵐ z, P z) : ∀ᵐ w, P (conj w⁻¹) := by
  have hN : volume {z : ℂ | ¬ P z} = 0 := ae_iff.1 h
  have hdiff : DifferentiableOn ℝ (fun w : ℂ => conj w⁻¹) ({z : ℂ | ¬ P z} \ {0}) := by
    intro z hz
    have hz0 : z ≠ 0 := hz.2
    have h1 := Complex.conjCLE.differentiableAt.comp z ((differentiableAt_inv (𝕜 := ℂ) hz0).restrictScalars ℝ)
    exact (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => rfl)).differentiableWithinAt
  have himg : volume ((fun w : ℂ => conj w⁻¹) '' ({z : ℂ | ¬ P z} \ {0})) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff
      (measure_mono_null diff_subset hN)
  refine ae_iff.2 (measure_mono_null ?_ (measure_union_null himg (measure_singleton (0 : ℂ))))
  intro w hw
  by_cases hw0 : w = 0
  · exact Or.inr hw0
  · refine Or.inl ⟨conj w⁻¹, ⟨hw, ?_⟩, ?_⟩
    · intro h0
      apply hw0
      have : conj w⁻¹ = 0 := h0
      rwa [map_eq_zero, inv_eq_zero] at this
    · simp [map_inv₀]

/-- The complex dilatation of the circle-reflection conjugate `w ↦ (conj (f (conj w⁻¹)))⁻¹`:
`μ(w) = conj (μ_f (conj w⁻¹)) · w² / conj w²` (the transformation law of (−1,1)-forms under `σ`). -/
theorem s82td_sigma_dilatation {f : ℂ → ℂ} {w : ℂ} (hw : w ≠ 0) (hf : DifferentiableAt ℝ f (conj w⁻¹))
    (hf0 : f (conj w⁻¹) ≠ 0) :
    complexDilatation (fun w => (conj (f (conj w⁻¹)))⁻¹) w =
      conj (complexDilatation f (conj w⁻¹)) * (w ^ 2 / conj w ^ 2) := by
  set F : ℂ → ℂ := fun z => conj (f (conj z)) with hF
  have hFd : DifferentiableAt ℝ F w⁻¹ :=
    Complex.conjCLE.differentiableAt.comp _ (hf.comp _ Complex.conjCLE.differentiableAt)
  have hinv : DifferentiableAt ℂ (fun x : ℂ => x⁻¹) w := differentiableAt_inv hw
  have hinv' : deriv (fun x : ℂ => x⁻¹) w ≠ 0 := by
    rw [deriv_inv]
    exact neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 hw))
  have hFw : F w⁻¹ ≠ 0 := by
    show conj (f (conj w⁻¹)) ≠ 0
    rw [map_ne_zero]
    exact hf0
  have hc1 : DifferentiableAt ℝ (F ∘ fun x : ℂ => x⁻¹) w := hFd.comp w (hinv.restrictScalars ℝ)
  have hc2 : DifferentiableAt ℂ (fun x : ℂ => x⁻¹) ((F ∘ fun x : ℂ => x⁻¹) w) := differentiableAt_inv hFw
  have hc3 : deriv (fun x : ℂ => x⁻¹) ((F ∘ fun x : ℂ => x⁻¹) w) ≠ 0 := by
    rw [deriv_inv]
    exact neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 hFw))
  show complexDilatation ((fun x : ℂ => x⁻¹) ∘ (F ∘ fun x : ℂ => x⁻¹)) w = _
  rw [complexDilatation_comp_conformal_left hc1 hc2 hc3, complexDilatation_comp_conformal_right hinv hinv' hFd,
    hF, bg_dilatation_conj f w⁻¹, deriv_inv, map_inv₀ (starRingEnd ℂ) w]
  have hcw : conj w ≠ 0 := (map_ne_zero _).2 hw
  congr 1
  simp only [map_neg, map_inv₀, map_pow]
  field_simp

/-- Conjugating a quasiconformal homeomorphism `φ` of `ℂ` fixing `0` by the circle reflection keeps it
`K`-quasiconformal on `ℂ` (locally `inv ∘ (conj ∘ φ ∘ conj) ∘ inv` off `0`; the point `0` is removable). -/
theorem s82td_sigma_isKQC (φ : ℂ ≃ₜ ℂ) (h0 : φ 0 = 0) {K : ℝ} (hK : IsKQC φ univ K) :
    IsKQC (fun w : ℂ => (conj (φ (conj w⁻¹)))⁻¹) univ K := by
  obtain ⟨G, hG⟩ := s82td_sigma_homeo φ h0
  have hGe : (fun w : ℂ => (conj (φ (conj w⁻¹)))⁻¹) = G := (funext hG).symm
  have hhom : IsHomeomorphOnto (fun w : ℂ => (conj (φ (conj w⁻¹)))⁻¹) univ
      ((fun w : ℂ => (conj (φ (conj w⁻¹)))⁻¹) '' univ) := by
    rw [hGe, image_univ, G.range_coe]
    exact s82td_isHomeomorphOnto_of_homeomorph G
  have hFK : IsKQC (fun z => conj (φ (conj z))) univ K := by
    have := abR_x_isKQC_conj hK
    rwa [preimage_univ] at this
  refine s13x_removable (L := {0}) isOpen_univ hK.2.1 hhom (measure_singleton 0) ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun x => (Set.countable_singleton (0 : ℝ)).mono ?_
    intro y hy
    have h := congrArg Complex.im (mem_singleton_iff.1 hy)
    simpa using h
  · refine Filter.Eventually.of_forall fun y => (Set.countable_singleton (0 : ℝ)).mono ?_
    intro x hx
    have h := congrArg Complex.re (mem_singleton_iff.1 hx)
    simpa using h
  · intro z hz
    have hz0 : z ≠ 0 := hz.2
    have hFz : (fun z => conj (φ (conj z))) z⁻¹ ≠ 0 := by
      show conj (φ (conj z⁻¹)) ≠ 0
      rw [map_ne_zero, ← h0, Ne, φ.injective.eq_iff, map_eq_zero, inv_eq_zero]
      exact hz0
    obtain ⟨U, hU, hzU, -, hUK⟩ := s26w_isKQC_local_comp (g := fun w : ℂ => (conj (φ (conj w⁻¹)))⁻¹)
      (τ := fun x : ℂ => x⁻¹) (σ := fun x : ℂ => x⁻¹) hFK (mem_univ _) (analyticAt_inv hz0)
      (by rw [deriv_inv]; exact neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 hz0)))
      (analyticAt_inv hFz) (by rw [deriv_inv]; exact neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 hFz)))
      (Filter.Eventually.of_forall fun w => rfl) Filter.univ_mem
    exact ⟨U, hU, hzU, subset_univ _, hUK⟩

/-- **[stub C3] Circle-symmetric solution of the Beltrami equation**: for a Beltrami coefficient `ν` on the annulus
`1 < ‖w‖ < r`, there is a quasiconformal homeomorphism `h` of the plane with dilatation `ν` a.e. on the annulus that
preserves the closed unit disc. (Proof: extend `ν` by the reflection `w ↦ 1/w̄`, `ν̃(w) = conj (ν (1/w̄)) · w² / w̄²`
inside, `0` elsewhere; `h` is the normalized solution of `thm13_7_normalized_existence`; `w ↦ 1/conj (h (1/w̄))` is again
a normalized solution, so equals `h` by uniqueness; hence `h` maps the circle to itself and, fixing `0`, the disc to
itself.) -/
theorem s82td_circle_solution {ν : ℂ → ℂ} {r k : ℝ} (hr : 1 < r) (hk₀ : 0 ≤ k) (hk : k < 1)
    (hν : IsBeltramiCoeff ν {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r} k) :
    ∃ (h : ℂ ≃ₜ ℂ) (K : ℝ), (∀ w, ‖h w‖ ≤ 1 ↔ ‖w‖ ≤ 1) ∧ IsKQC h univ K ∧
      ∀ᵐ w ∂(volume.restrict {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r}), complexDilatation h w = ν w := by
  classical
  have hAo : IsOpen {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  obtain ⟨hνm, hνb⟩ := hν
  -- a measurable version of `ν`, bounded by `k` everywhere
  set ν₁ := hνm.mk ν with hν₁
  have hν₁m : StronglyMeasurable ν₁ := hνm.stronglyMeasurable_mk
  have hνν₁ : ν =ᵐ[volume.restrict {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r}] ν₁ := hνm.ae_eq_mk
  set ν₂ : ℂ → ℂ := fun z => if ‖ν₁ z‖ ≤ k then ν₁ z else 0 with hν₂
  have hν₂b : ∀ z, ‖ν₂ z‖ ≤ k := by
    intro z
    by_cases h : ‖ν₁ z‖ ≤ k
    · simp only [hν₂, if_pos h]
      exact h
    · simp only [hν₂, if_neg h, norm_zero]
      exact hk₀
  have hν₂m : Measurable ν₂ :=
    Measurable.ite (measurableSet_le hν₁m.measurable.norm measurable_const) hν₁m.measurable measurable_const
  have hνν₂ : ν =ᵐ[volume.restrict {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r}] ν₂ := by
    filter_upwards [hνν₁, hνb] with z h1 h2
    have h3 : ‖ν₁ z‖ ≤ k := h1 ▸ h2
    simp only [hν₂, if_pos h3]
    exact h1
  -- the reflection `σ w = conj w⁻¹`
  have hσσ : ∀ w : ℂ, conj (conj w⁻¹)⁻¹ = w := fun w => by simp [map_inv₀]
  have hσn : ∀ w : ℂ, ‖conj w⁻¹‖ = ‖w‖⁻¹ := fun w => by rw [Complex.norm_conj, norm_inv]
  have hσm : Measurable (fun w : ℂ => conj w⁻¹) := Complex.continuous_conj.measurable.comp measurable_inv
  -- the symmetric coefficient
  set μ : ℂ → ℂ := fun w => if w ∈ {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r} then ν₂ w
    else if conj w⁻¹ ∈ {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r} then conj (ν₂ (conj w⁻¹)) * (w ^ 2 / conj w ^ 2) else 0
    with hμ
  have hunit : ∀ w : ℂ, w ≠ 0 → ‖w ^ 2 / conj w ^ 2‖ = 1 := by
    intro w hw
    rw [norm_div, norm_pow, norm_pow, Complex.norm_conj, div_self (pow_ne_zero 2 (norm_ne_zero_iff.2 hw))]
  have hσA0 : ∀ w : ℂ, conj w⁻¹ ∈ {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r} → w ≠ 0 := by
    intro w hw h0
    rw [h0, inv_zero, map_zero] at hw
    have := hw.1
    rw [norm_zero] at this
    linarith
  have hμb : ∀ w, ‖μ w‖ ≤ k := by
    intro w
    by_cases h1 : w ∈ {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r}
    · simp only [hμ, if_pos h1]
      exact hν₂b w
    · by_cases h2 : conj w⁻¹ ∈ {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r}
      · simp only [hμ, if_neg h1, if_pos h2]
        rw [norm_mul, Complex.norm_conj, hunit w (hσA0 w h2), mul_one]
        exact hν₂b _
      · simp only [hμ, if_neg h1, if_neg h2, norm_zero]
        exact hk₀
  have hμm : Measurable μ := by
    refine Measurable.ite hAo.measurableSet hν₂m (Measurable.ite (hσm hAo.measurableSet) ?_ measurable_const)
    exact (Complex.continuous_conj.measurable.comp (hν₂m.comp hσm)).mul
      ((measurable_id.pow_const 2).div (Complex.continuous_conj.measurable.pow_const 2))
  -- `μ` is invariant under the transformation law of `σ`
  have hμsym : ∀ w : ℂ, w ≠ 0 → μ w = conj (μ (conj w⁻¹)) * (w ^ 2 / conj w ^ 2) := by
    intro w hw
    have hcw : conj w ≠ 0 := (map_ne_zero _).2 hw
    by_cases h1 : w ∈ {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r}
    · have h2 : conj w⁻¹ ∉ {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r} := by
        intro h
        have h' := h.1
        rw [hσn] at h'
        have := h1.1
        have hpos : 0 < ‖w‖ := by linarith
        rw [lt_inv_comm₀ one_pos hpos, inv_one] at h'
        linarith
      have h3 : conj (conj w⁻¹)⁻¹ ∈ {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r} := by rw [hσσ]; exact h1
      simp only [hμ, if_pos h1, if_neg h2, if_pos h3, hσσ]
      simp only [map_mul, map_div₀, map_pow, Complex.conj_conj, map_inv₀]
      field_simp
    · by_cases h2 : conj w⁻¹ ∈ {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r}
      · simp only [hμ, if_neg h1, if_pos h2]
      · have h3 : conj (conj w⁻¹)⁻¹ ∉ {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r} := by rw [hσσ]; exact h1
        simp only [hμ, if_neg h1, if_neg h2, if_neg h3, map_zero, zero_mul]
  -- the normalized solution `f`
  have hμB : IsBeltramiCoeff μ univ k := ⟨hμm.aestronglyMeasurable, Filter.Eventually.of_forall hμb⟩
  obtain ⟨f, hfN, hfK, huniq⟩ := thm13_7_normalized_existence hk₀ hk hμB
  obtain ⟨-, hfs, hf0, hf1, hfd⟩ := hfN
  have hH := hfK.2.2.1
  rw [hfs] at hH
  let φ : ℂ ≃ₜ ℂ :=
    { toFun := f
      invFun := Function.invFunOn f univ
      left_inv := fun z => hH.2.1.leftInvOn_invFunOn (mem_univ z)
      right_inv := fun y => Function.invFunOn_eq (by
        have : y ∈ f '' univ := by rw [hfs]; exact mem_univ y
        obtain ⟨a, ha, hay⟩ := this
        exact ⟨a, ha, hay⟩)
      continuous_toFun := continuousOn_univ.1 hH.1
      continuous_invFun := continuousOn_univ.1 hH.2.2.2 }
  have hφ : ∀ z, φ z = f z := fun z => rfl
  have hfinj : ∀ z, f z = 0 → z = 0 := fun z hz => φ.injective (by rw [hφ, hφ, hz, hf0])
  -- `σ ∘ f ∘ σ` is again the normalized solution, hence equals `f`
  have hgN : IsNormalizedSolution (fun w : ℂ => (conj (f (conj w⁻¹)))⁻¹) μ := by
    obtain ⟨G, hG⟩ := s82td_sigma_homeo φ hf0
    have hGe : (fun w : ℂ => (conj (f (conj w⁻¹)))⁻¹) = G := (funext hG).symm
    refine ⟨⟨_, s82td_sigma_isKQC φ hf0 hfK⟩, by rw [hGe, image_univ, G.range_coe], by simp [hf0],
      by simp [hf1], ?_⟩
    have hfdσ := s82td_ae_sigma hfd
    have hdiff : ∀ᵐ z, DifferentiableAt ℝ f z := by
      have := thm9_3_differentiable_ae hfK
      rwa [Measure.restrict_univ] at this
    have hdσ := s82td_ae_sigma hdiff
    have hne : ∀ᵐ w : ℂ, w ≠ 0 := by
      have := measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := (volume : Measure ℂ)) (0 : ℂ))
      filter_upwards [this] with w hw
      exact hw
    filter_upwards [hfdσ, hdσ, hne] with w h1 h2 h3
    have hf0' : f (conj w⁻¹) ≠ 0 := by
      intro h
      have := hfinj _ h
      rw [map_eq_zero, inv_eq_zero] at this
      exact h3 this
    rw [s82td_sigma_dilatation h3 h2 hf0', h1, ← hμsym w h3]
  have hgf : (fun w : ℂ => (conj (f (conj w⁻¹)))⁻¹) = f := huniq _ hgN
  have hsymf : ∀ w, f w = (conj (f (conj w⁻¹)))⁻¹ := fun w => (congrFun hgf w).symm
  have hnf : ∀ w, ‖f w‖ = ‖f (conj w⁻¹)‖⁻¹ := fun w => by
    conv_lhs => rw [hsymf w]
    rw [norm_inv, Complex.norm_conj]
  -- `f` preserves the circle, both ways
  have hfix : ∀ x : ℂ, ‖x‖ = 1 → (conj x)⁻¹ = x := by
    intro x hx
    have hx0 : x ≠ 0 := norm_ne_zero_iff.1 (by rw [hx]; exact one_ne_zero)
    have h : conj x * x = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hx]
      simp
    exact inv_eq_of_mul_eq_one_right h
  have hcirc : ∀ z, ‖f z‖ = 1 → ‖z‖ = 1 := by
    intro z hz
    have h1 : f (conj z⁻¹) = f z := by
      rw [hsymf (conj z⁻¹), hσσ]
      exact hfix _ hz
    have h2 : conj z⁻¹ = z := φ.injective h1
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, hf0, norm_zero] at hz
      exact zero_ne_one hz
    have h3 := congrArg norm h2
    rw [hσn] at h3
    have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have h4 : ‖z‖ * ‖z‖ = 1 := by
      calc ‖z‖ * ‖z‖ = ‖z‖⁻¹ * ‖z‖ := by rw [h3]
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    nlinarith
  have hball : ∀ z, ‖z‖ < 1 → ‖f z‖ < 1 := by
    have hpc : IsPreconnected (f '' ball (0 : ℂ) 1) :=
      (isPreconnected_ball).image f φ.continuous.continuousOn
    have hsub : f '' ball (0 : ℂ) 1 ⊆ ball (0 : ℂ) 1 := by
      refine hpc.subset_left_of_subset_union isOpen_ball
        (isOpen_lt continuous_const continuous_norm : IsOpen {z : ℂ | (1 : ℝ) < ‖z‖}) ?_ ?_ ?_
      · refine Set.disjoint_left.2 fun x hx hx' => ?_
        rw [mem_ball_zero_iff] at hx
        exact lt_asymm hx hx'
      · rintro _ ⟨z, hz, rfl⟩
        rw [mem_ball_zero_iff] at hz
        rcases lt_trichotomy ‖f z‖ 1 with h | h | h
        · exact Or.inl (mem_ball_zero_iff.2 h)
        · exact absurd (hcirc z h) (ne_of_lt hz)
        · exact Or.inr h
      · exact ⟨0, ⟨0, mem_ball_self one_pos, hf0⟩, by rw [mem_ball_zero_iff, norm_zero]; exact one_pos⟩
    intro z hz
    exact mem_ball_zero_iff.1 (hsub ⟨z, mem_ball_zero_iff.2 hz, rfl⟩)
  have hiff : ∀ w, ‖φ w‖ ≤ 1 ↔ ‖w‖ ≤ 1 := by
    intro w
    rw [hφ]
    constructor
    · intro h
      by_contra hw
      push_neg at hw
      have hw0 : w ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hw
        linarith
      have h1 : ‖conj w⁻¹‖ < 1 := by
        rw [hσn]
        exact inv_lt_one_of_one_lt₀ hw
      have h2 := hball _ h1
      have h3 : f (conj w⁻¹) ≠ 0 := by
        intro h0
        have := hfinj _ h0
        rw [map_eq_zero, inv_eq_zero] at this
        exact hw0 this
      have h4 : 1 < ‖f w‖ := by
        rw [hnf w]
        exact one_lt_inv₀ (norm_pos_iff.2 h3) |>.2 h2
      linarith
    · intro h
      rcases lt_or_eq_of_le h with h' | h'
      · exact (hball w h').le
      · have hw1 : (conj w⁻¹) = w := by
          rw [map_inv₀]
          exact hfix w h'
        have h5 : f w = (conj (f w))⁻¹ := by
          conv_lhs => rw [hsymf w, hw1]
        have hf0w : f w ≠ 0 := by
          intro h0
          have := hfinj _ h0
          rw [this, norm_zero] at h'
          exact zero_ne_one h'
        have h6 : f w * conj (f w) = 1 := by
          calc f w * conj (f w) = (conj (f w))⁻¹ * conj (f w) := by rw [← h5]
            _ = 1 := inv_mul_cancel₀ ((map_ne_zero _).2 hf0w)
        have h7 : ‖f w‖ * ‖f w‖ = 1 := by
          have := congrArg norm h6
          rwa [norm_mul, Complex.norm_conj, norm_one] at this
        nlinarith [norm_nonneg (f w)]
  refine ⟨φ, (1 + k) / (1 - k), hiff, hfK, ?_⟩
  filter_upwards [ae_restrict_of_ae hfd, hνν₂, ae_restrict_mem hAo.measurableSet] with w h1 h2 h3
  show complexDilatation f w = ν w
  rw [h1, h2]
  simp only [hμ]
  exact if_pos h3

/-- The coefficient of a quadratic differential in a holomorphic coordinate `G⁻¹` does not depend on the chart used
to read it (the transformation law and the chain rule). -/
theorem s82td_coord_law {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {qh : X → ℂ → ℂ} (hlaw : IsDiffFamily 2 0 qh) {G : ℂ → X} {t : ℂ} (hG : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) G t)
    (x : X) (hx : G t ∈ (chartAt ℂ x).source) :
    qh (G t) (chartAt ℂ (G t) (G t)) * deriv (fun v => chartAt ℂ (G t) (G v)) t ^ 2 =
      qh x (chartAt ℂ x (G t)) * deriv (fun v => chartAt ℂ x (G v)) t ^ 2 := by
  have hst : chartAt ℂ (G t) (G t) ∈ (chartAt ℂ (G t)).target :=
    (chartAt ℂ (G t)).map_source (mem_chart_source ℂ (G t))
  have hss : (chartAt ℂ (G t)).symm (chartAt ℂ (G t) (G t)) = G t :=
    (chartAt ℂ (G t)).left_inv (mem_chart_source ℂ (G t))
  have hl : qh (G t) (chartAt ℂ (G t) (G t)) = qh x (chartTransition x (G t) (chartAt ℂ (G t) (G t))) *
      deriv (chartTransition x (G t)) (chartAt ℂ (G t) (G t)) ^ 2 := by
    rw [hlaw.2 x (G t) _ hst (by rw [hss]; exact hx)]
    norm_num
  have hT : chartTransition x (G t) (chartAt ℂ (G t) (G t)) = chartAt ℂ x (G t) := by
    show chartAt ℂ x ((chartAt ℂ (G t)).symm (chartAt ℂ (G t) (G t))) = chartAt ℂ x (G t)
    rw [hss]
  rw [hT] at hl
  have hTd : DifferentiableAt ℂ (chartTransition x (G t)) (chartAt ℂ (G t) (G t)) :=
    s23_transition_differentiableAt x (G t) hst (by rw [hss]; exact hx)
  have hgd : DifferentiableAt ℂ (fun v => chartAt ℂ (G t) (G v)) t :=
    mdifferentiableAt_iff_differentiableAt.1
      ((mdifferentiableAt_atlas (chart_mem_atlas ℂ (G t)) (mem_chart_source ℂ (G t))).comp t hG)
  have hev : (fun v => chartAt ℂ x (G v)) =ᶠ[𝓝 t] chartTransition x (G t) ∘ fun v => chartAt ℂ (G t) (G v) := by
    filter_upwards [hG.continuousAt.preimage_mem_nhds
      ((chartAt ℂ (G t)).open_source.mem_nhds (mem_chart_source ℂ (G t)))] with v hv
    show chartAt ℂ x (G v) = chartAt ℂ x ((chartAt ℂ (G t)).symm (chartAt ℂ (G t) (G v)))
    rw [(chartAt ℂ (G t)).left_inv hv]
  have hder : deriv (fun v => chartAt ℂ x (G v)) t =
      deriv (chartTransition x (G t)) (chartAt ℂ (G t) (G t)) * deriv (fun v => chartAt ℂ (G t) (G v)) t := by
    rw [hev.deriv_eq]
    exact (hTd.hasDerivAt.comp t hgd.hasDerivAt).deriv
  rw [hder, hl]
  ring

/-- **The coefficient `Q` of `q̂` in a hole coordinate, locally.**  Near a point `t` of the collar `1 < ‖t‖` of the
coordinate `W` with `W⁻¹ t = ι x`, the coordinate change `τ = φ_x ∘ ι⁻¹ ∘ W⁻¹` is holomorphic and `Q = q_x(τ) τ'²`
with `q = ι^* q̂`. -/
theorem s82td_Q_local {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) {qh : F₀.X.carrier → ℂ → ℂ}
    (hqh : qh ∈ admissibleQDSpace F₀) (W : OpenPartialHomeomorph F₀.X.carrier ℂ)
    (hWι : ∀ y ∈ W.source, y ∈ range F₀.ι ↔ 1 < ‖W y‖)
    (hWs : ∀ w ∈ W.target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) W.symm w)
    {t : ℂ} (ht : t ∈ W.target) (ht1 : 1 < ‖t‖) {x : S₀} (hx : F₀.ι x = W.symm t) :
    ∀ᶠ v in 𝓝 t, v ∈ W.target ∧ 1 < ‖v‖ ∧
      DifferentiableAt ℂ (fun v => chartAt ℂ x ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm (W.symm v))) v ∧
      chartAt ℂ x ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm (W.symm v)) ∈ (chartAt ℂ x).target ∧
      F₀.ι ((chartAt ℂ x).symm (chartAt ℂ x ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm (W.symm v)))) =
        W.symm v ∧
      qh (W.symm v) (chartAt ℂ (W.symm v) (W.symm v)) * deriv (fun u => chartAt ℂ (W.symm v) (W.symm u)) v ^ 2 =
        pullbackQD F₀ qh x (chartAt ℂ x ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm (W.symm v))) *
          deriv (fun u => chartAt ℂ x ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm (W.symm u))) v ^ 2 := by
  haveI : Nonempty S₀ := ⟨x⟩
  set ιe := F₀.embedding.toOpenPartialHomeomorph F₀.ι with hιe
  have hιt : ιe.target = range F₀.ι := F₀.embedding.toOpenPartialHomeomorph_target F₀.ι
  have hrange : ∀ y ∈ range F₀.ι, F₀.ι (ιe.symm y) = y := fun y hy => ιe.right_inv (hιt ▸ hy)
  have hrange_of : ∀ u ∈ W.target, 1 < ‖u‖ → W.symm u ∈ range F₀.ι := fun u hu hu1 =>
    (hWι _ (W.map_target hu)).2 (by rw [W.right_inv hu]; exact hu1)
  set X0 := W.symm t with hX0
  have hA : ∀ᶠ v in 𝓝 t, v ∈ W.target ∧ 1 < ‖v‖ :=
    (W.open_target.inter (isOpen_lt continuous_const continuous_norm : IsOpen {v : ℂ | (1 : ℝ) < ‖v‖})).mem_nhds
      ⟨ht, ht1⟩
  have hcont : ContinuousAt W.symm t := W.continuousAt_symm ht
  have hX0s : ∀ᶠ v in 𝓝 t, W.symm v ∈ (chartAt ℂ X0).source :=
    hcont.preimage_mem_nhds ((chartAt ℂ X0).open_source.mem_nhds (mem_chart_source ℂ X0))
  have hιx : ιe.symm X0 = x := by
    show ιe.symm (W.symm t) = x
    rw [← hX0, ← hx]
    exact ιe.left_inv (by rw [F₀.embedding.toOpenPartialHomeomorph_source]; exact mem_univ x)
  have hιc : ContinuousAt (fun v => ιe.symm (W.symm v)) t := by
    have h1 : X0 ∈ ιe.target := by
      show W.symm t ∈ ιe.target
      rw [hιt, ← hX0, ← hx]
      exact mem_range_self x
    exact (ιe.continuousAt_symm h1).comp hcont
  have hxs : ∀ᶠ v in 𝓝 t, ιe.symm (W.symm v) ∈ (chartAt ℂ x).source := by
    refine hιc.preimage_mem_nhds ((chartAt ℂ x).open_source.mem_nhds ?_)
    show ιe.symm X0 ∈ (chartAt ℂ x).source
    rw [hιx]
    exact mem_chart_source ℂ x
  have hτd : ∀ u, u ∈ W.target → 1 < ‖u‖ → ιe.symm (W.symm u) ∈ (chartAt ℂ x).source →
      DifferentiableAt ℂ (fun v => chartAt ℂ x (ιe.symm (W.symm v))) u := by
    intro u hu hu1 hux
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ιe.symm (W.symm u) :=
      s31qr_open_embedding_inverse F₀.embedding F₀.holomorphic (hrange_of u hu hu1)
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) (ιe.symm (W.symm u)) :=
      mdifferentiableAt_atlas (chart_mem_atlas ℂ x) hux
    exact mdifferentiableAt_iff_differentiableAt.1 ((h2.comp _ h1).comp u (hWs u hu hu1))
  have hall := hA.and (hX0s.and hxs)
  filter_upwards [hall.eventually_nhds] with v hv
  obtain ⟨⟨hvt, hv1⟩, hvX0, hvx⟩ := hv.self_of_nhds
  have hvr := hrange_of v hvt hv1
  have hιv : F₀.ι ((chartAt ℂ x).symm (chartAt ℂ x (ιe.symm (W.symm v)))) = W.symm v := by
    rw [(chartAt ℂ x).left_inv hvx]
    exact hrange _ hvr
  refine ⟨hvt, hv1, hτd v hvt hv1 hvx, (chartAt ℂ x).map_source hvx, hιv, ?_⟩
  have hlaw := s82td_coord_law hqh.1 (hWs v hvt hv1) X0 hvX0
  have hpb := s32p_pullbackQD_local F₀ hqh x X0 ((chartAt ℂ x).map_source hvx) (by rw [hιv]; exact hvX0)
  have hTd := s32p_T_differentiableAt F₀ X0 x ((chartAt ℂ x).map_source hvx) (by rw [hιv]; exact hvX0)
  have hev : (fun u => chartAt ℂ X0 (W.symm u)) =ᶠ[𝓝 v]
      (fun v' => chartAt ℂ X0 (F₀.ι ((chartAt ℂ x).symm v'))) ∘ fun u => chartAt ℂ x (ιe.symm (W.symm u)) := by
    filter_upwards [hv] with u hu
    obtain ⟨⟨hut, hu1⟩, -, hux⟩ := hu
    show chartAt ℂ X0 (W.symm u) = chartAt ℂ X0 (F₀.ι ((chartAt ℂ x).symm (chartAt ℂ x (ιe.symm (W.symm u)))))
    rw [(chartAt ℂ x).left_inv hux, hrange _ (hrange_of u hut hu1)]
  have hder : deriv (fun u => chartAt ℂ X0 (W.symm u)) v =
      deriv (fun v' => chartAt ℂ X0 (F₀.ι ((chartAt ℂ x).symm v'))) (chartAt ℂ x (ιe.symm (W.symm v))) *
        deriv (fun u => chartAt ℂ x (ιe.symm (W.symm u))) v := by
    rw [hev.deriv_eq]
    exact (hTd.hasDerivAt.comp v (hτd v hvt hv1 hvx).hasDerivAt).deriv
  rw [hlaw, hpb, hιv, hder]
  ring

/-- `conj (a²) / ‖a²‖ = conj a / a` for `a ≠ 0`. -/
theorem s82td_conj_sq_div {a : ℂ} (ha : a ≠ 0) : conj (a ^ 2) / ((‖a ^ 2‖ : ℝ) : ℂ) = conj a / a := by
  have hca : conj a ≠ 0 := (map_ne_zero _).2 ha
  have h1 : ((‖a ^ 2‖ : ℝ) : ℂ) = a * conj a := by
    rw [norm_pow, Complex.mul_conj']
    push_cast
    ring
  rw [h1, map_pow]
  field_simp

/-- **Compatibility at a regular point.**  Let `y₀ = ι x₀` lie in the source of the transported §26.2 chart `Ψ_s`
and of the hole coordinate `W`, with `x₀ ≠ s` (a regular point of `q`).  Near `t₀ = W y₀`, `N ∘ Ψ_s ∘ W⁻¹ = S_k ∘ G`
with `G` holomorphic, `G' ≠ 0`, `G'² = Q`; so `S_k ∘ G` and `h` are quasiconformal with the dilatation `ν` near `t₀`
and `bg_conformal_of_dilatation_eq` makes both transitions between `h ∘ W` and `Ψ_s` holomorphic at `y₀`. -/
theorem s82td_hole_compat_reg {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) {qh : F₀.X.carrier → ℂ → ℂ}
    (hqh : qh ∈ admissibleQDSpace F₀) {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) {md : S₀ → ℕ} {ζ : S₀ → ℂ → ℂ}
    {Z : S₀ → OpenPartialHomeomorph ℂ ℂ} (hD : ∀ s, s26d_a_Data (pullbackQD F₀ qh) s (md s) (ζ s) (Z s))
    (W : OpenPartialHomeomorph F₀.X.carrier ℂ) {r : ℝ} (hWt : W.target = ball (0 : ℂ) r)
    (hWι : ∀ y ∈ W.source, y ∈ range F₀.ι ↔ 1 < ‖W y‖)
    (hWd : ∀ y ∈ W.source, 1 < ‖W y‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) W y)
    (hWs : ∀ w ∈ W.target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) W.symm w)
    {ν : ℂ → ℂ}
    (hν : ∀ t, 1 < ‖t‖ → ‖t‖ < r → ν t = (k : ℂ) *
      conj (qh (W.symm t) (chartAt ℂ (W.symm t) (W.symm t)) * deriv (fun u => chartAt ℂ (W.symm t) (W.symm u)) t ^ 2) /
      ((‖qh (W.symm t) (chartAt ℂ (W.symm t) (W.symm t)) *
        deriv (fun u => chartAt ℂ (W.symm t) (W.symm u)) t ^ 2‖ : ℝ) : ℂ))
    (h : ℂ ≃ₜ ℂ) {K : ℝ} (hK : IsKQC h univ K)
    (hhd : ∀ᵐ w ∂(volume.restrict {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r}), complexDilatation h w = ν w)
    (s : S₀) {y₀ : F₀.X.carrier}
    (hy₀Ψ : y₀ ∈ ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).source)
    (hy₀W : y₀ ∈ W.source) (hy₀s : y₀ ≠ F₀.ι s) :
    DifferentiableAt ℂ (fun w => ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans
        (s26d_a_psi hk₀ hk md Z s)) ((W.trans h.toOpenPartialHomeomorph).symm w))
      ((W.trans h.toOpenPartialHomeomorph) y₀) ∧
    DifferentiableAt ℂ (fun w => (W.trans h.toOpenPartialHomeomorph)
        (((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).symm w))
      (((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)) y₀) := by
  classical
  haveI : Nonempty S₀ := ⟨s⟩
  set ιe := F₀.embedding.toOpenPartialHomeomorph F₀.ι with hιe
  set ψ := s26d_a_psi hk₀ hk md Z s with hψ
  set Ψ := ιe.symm.trans ψ with hΨ
  have hιt : ιe.target = range F₀.ι := F₀.embedding.toOpenPartialHomeomorph_target F₀.ι
  have hιl : ∀ x', ιe.symm (F₀.ι x') = x' := fun x' =>
    ιe.left_inv (by rw [F₀.embedding.toOpenPartialHomeomorph_source]; exact mem_univ x')
  have hq := s32p_pullbackQD_isHolQuadDiff F₀ hqh
  -- the point `x₀`
  have hy₀r : y₀ ∈ range F₀.ι := by
    have : y₀ ∈ ιe.target := hy₀Ψ.1
    rwa [hιt] at this
  obtain ⟨x₀, hx₀⟩ := hy₀r
  have hx₀ψ : x₀ ∈ ψ.source := by
    have h1 : ιe.symm y₀ ∈ ψ.source := hy₀Ψ.2
    rwa [← hx₀, hιl] at h1
  have hx₀s : x₀ ≠ s := fun h' => hy₀s (by rw [← hx₀, h'])
  have hreg := s26d_a_regular_of_mem hq hk₀ hk hD s hx₀ψ hx₀s
  obtain ⟨N, Wb, hNa, hN0, hNW, hWba, hWbd⟩ := s82td_psi_branch F₀ hq hk₀ hk hD s hx₀ψ hreg
  have hΨy₀ : Ψ y₀ = ψ x₀ := by
    show ψ (ιe.symm y₀) = ψ x₀
    rw [← hx₀, hιl]
  -- the point `t₀`
  set t₀ := W y₀ with ht₀
  have ht₀t : t₀ ∈ W.target := W.map_source hy₀W
  have ht₀1 : 1 < ‖t₀‖ := (hWι y₀ hy₀W).1 ⟨x₀, hx₀⟩
  have ht₀r : ‖t₀‖ < r := by
    have := ht₀t
    rw [hWt, mem_ball_zero_iff] at this
    exact this
  have hWy₀ : W.symm t₀ = y₀ := W.left_inv hy₀W
  -- `G = Wb ∘ W⁻¹` and the coordinate change `τ`
  set G₀ : ℂ → ℂ := fun z => Wb (F₀.ι ((chartAt ℂ x₀).symm z)) with hG₀
  set τ : ℂ → ℂ := fun v => chartAt ℂ x₀ (ιe.symm (W.symm v)) with hτ
  set G : ℂ → ℂ := fun v => Wb (W.symm v) with hG
  have hτt₀ : τ t₀ = chartAt ℂ x₀ x₀ := by
    show chartAt ℂ x₀ (ιe.symm (W.symm t₀)) = _
    rw [hWy₀, ← hx₀, hιl]
  have hloc := s82td_Q_local F₀ hqh W hWι hWs ht₀t ht₀1 (x := x₀) (by rw [hWy₀, hx₀])
  have hτc : ContinuousAt τ t₀ := by
    obtain ⟨-, -, hd, -⟩ := hloc.self_of_nhds
    exact hd.continuousAt
  have hG₀a : ∀ᶠ v in 𝓝 t₀, AnalyticAt ℂ G₀ (τ v) ∧
      deriv G₀ (τ v) ^ 2 = pullbackQD F₀ qh x₀ (τ v) := by
    have h1 := hWba.eventually_analyticAt.and hWbd
    rw [← hτt₀] at h1
    exact hτc.eventually h1
  -- the good neighbourhood of `t₀`
  have hNWv : ∀ᶠ v in 𝓝 t₀, N (Ψ (W.symm v)) = teichStretch k (G v) := by
    have h1 : Tendsto W.symm (𝓝 t₀) (𝓝 (F₀.ι x₀)) := by
      have := (W.continuousAt_symm ht₀t).tendsto
      rwa [hWy₀, ← hx₀] at this
    exact h1.eventually hNW
  have hgood := (hloc.and hG₀a).and hNWv
  -- `G = G₀ ∘ τ` near every good point, hence `G` holomorphic with `G'² = Q`
  have hGv : ∀ᶠ v in 𝓝 t₀, DifferentiableAt ℂ G v ∧
      deriv G v ^ 2 = qh (W.symm v) (chartAt ℂ (W.symm v) (W.symm v)) *
        deriv (fun u => chartAt ℂ (W.symm v) (W.symm u)) v ^ 2 ∧
      deriv G v = deriv G₀ (τ v) * deriv τ v := by
    filter_upwards [hgood.eventually_nhds] with v hv
    obtain ⟨⟨⟨-, -, hτv, -, hιv, hQv⟩, hG₀v, hG₀d⟩, -⟩ := hv.self_of_nhds
    have hev : G =ᶠ[𝓝 v] G₀ ∘ τ := by
      filter_upwards [hv] with u hu
      obtain ⟨⟨⟨-, -, -, -, hιu, -⟩, -, -⟩, -⟩ := hu
      show Wb (W.symm u) = Wb (F₀.ι ((chartAt ℂ x₀).symm (τ u)))
      rw [hιu]
    have hd : HasDerivAt (G₀ ∘ τ) (deriv G₀ (τ v) * deriv τ v) v :=
      hG₀v.differentiableAt.hasDerivAt.comp v hτv.hasDerivAt
    have hd' : HasDerivAt G (deriv G₀ (τ v) * deriv τ v) v := hd.congr_of_eventuallyEq hev
    refine ⟨hd'.differentiableAt, ?_, hd'.deriv⟩
    rw [hd'.deriv, mul_pow, hG₀d, hQv]
  -- `G' ≠ 0` at `t₀`
  have hτ'0 : deriv τ t₀ ≠ 0 := by
    -- `W ∘ ι ∘ φ_{x₀}⁻¹` inverts `τ` near `t₀`
    set L : ℂ → ℂ := fun z => W (F₀.ι ((chartAt ℂ x₀).symm z)) with hL
    have hLm : DifferentiableAt ℂ L (τ t₀) := by
      have hz : τ t₀ ∈ (chartAt ℂ x₀).target := by
        rw [hτt₀]
        exact (chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀)
      have hm1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x₀).symm (τ t₀) :=
        mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ x₀) hz
      have hpt : F₀.ι ((chartAt ℂ x₀).symm (τ t₀)) = y₀ := by
        rw [hτt₀, (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀), hx₀]
      have hm2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) W (F₀.ι ((chartAt ℂ x₀).symm (τ t₀))) := by
        rw [hpt]
        exact hWd y₀ hy₀W ht₀1
      exact mdifferentiableAt_iff_differentiableAt.1 ((hm2.comp _ (F₀.holomorphic _)).comp _ hm1)
    have hLτ : L ∘ τ =ᶠ[𝓝 t₀] id := by
      filter_upwards [hloc] with v hv
      obtain ⟨hvt, -, -, -, hιv, -⟩ := hv
      show W (F₀.ι ((chartAt ℂ x₀).symm (τ v))) = v
      rw [hιv, W.right_inv hvt]
    obtain ⟨-, -, hτd, -⟩ := hloc.self_of_nhds
    have h1 : HasDerivAt (L ∘ τ) (deriv L (τ t₀) * deriv τ t₀) t₀ := hLm.hasDerivAt.comp t₀ hτd.hasDerivAt
    have h2 : HasDerivAt (L ∘ τ) 1 t₀ := (hasDerivAt_id t₀).congr_of_eventuallyEq hLτ
    have h3 := h1.unique h2
    intro h0
    rw [h0, mul_zero] at h3
    exact zero_ne_one h3
  have hG₀'0 : deriv G₀ (τ t₀) ≠ 0 := by
    have hreg' : pullbackQD F₀ qh x₀ (chartAt ℂ x₀ x₀) ≠ 0 := hreg
    rw [hτt₀]
    intro h0
    apply hreg'
    rw [← hWbd.self_of_nhds]
    show deriv G₀ (chartAt ℂ x₀ x₀) ^ 2 = 0
    rw [h0]
    ring
  have hG'0 : deriv G t₀ ≠ 0 := by
    rw [hGv.self_of_nhds.2.2]
    exact mul_ne_zero hG₀'0 hτ'0
  have hGa : AnalyticAt ℂ G t₀ := by
    obtain ⟨U, hU, hUd⟩ := (hGv.mono fun v hv => hv.1).exists_mem
    exact DifferentiableOn.analyticAt (fun v hv => (hUd v hv).differentiableWithinAt) hU
  have hG'ne : ∀ᶠ v in 𝓝 t₀, deriv G v ≠ 0 :=
    hGa.deriv.continuousAt.eventually_ne hG'0
  -- the quasiconformal model `S_k ∘ G` on a small open set `U ∋ t₀`
  have hNbhd : {v | (v ∈ W.target ∧ 1 < ‖v‖ ∧ ‖v‖ < r) ∧ (DifferentiableAt ℂ G v ∧
      deriv G v ^ 2 = qh (W.symm v) (chartAt ℂ (W.symm v) (W.symm v)) *
        deriv (fun u => chartAt ℂ (W.symm v) (W.symm u)) v ^ 2 ∧
      deriv G v = deriv G₀ (τ v) * deriv τ v) ∧ deriv G v ≠ 0 ∧
      N (Ψ (W.symm v)) = teichStretch k (G v)} ∈ 𝓝 t₀ := by
    have hr' : ∀ᶠ v in 𝓝 t₀, ‖v‖ < r := (isOpen_lt continuous_norm continuous_const).mem_nhds ht₀r
    filter_upwards [hloc, hr', hGv, hG'ne, hNWv] with v h1 h2 h3 h4 h5
    exact ⟨⟨h1.1, h1.2.1, h2⟩, h3, h4, h5⟩
  obtain ⟨U, hUo, ht₀U, hUN, hUK⟩ := s26w_isKQC_local_comp (g := fun v => teichStretch k (G v))
    (τ := G) (σ := id) (F := teichStretch k) (s26u_teichStretch_isKQC hk₀ hk) (mem_univ _) hGa hG'0
    analyticAt_id (by rw [deriv_id]; exact one_ne_zero) (Filter.Eventually.of_forall fun v => rfl) hNbhd
  have hUA : U ⊆ {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r} := fun v hv => ⟨(hUN hv).1.2.1, (hUN hv).1.2.2⟩
  have hhU : IsKQC h U K := ac_t_isKQC_restrict hK hUo (subset_univ U)
  have hdil : ∀ v ∈ U, complexDilatation (fun v => teichStretch k (G v)) v = ν v := by
    intro v hv
    obtain ⟨⟨-, hv1, hvr⟩, ⟨hGd, hGsq, -⟩, hG'v, -⟩ := hUN hv
    have hc : complexDilatation (teichStretch k ∘ G) v =
        complexDilatation (teichStretch k) (G v) * (conj (deriv G v) / deriv G v) :=
      complexDilatation_comp_conformal_right hGd hG'v
        (s82td_stretch_hasFDerivAt k (G v)).differentiableAt
    show complexDilatation (teichStretch k ∘ G) v = ν v
    rw [hc, s26b_teichStretch_dilatation hk, hν v hv1 hvr, ← hGsq, mul_div_assoc, s82td_conj_sq_div hG'v]
  have hae : ∀ᵐ v ∂(volume.restrict U), complexDilatation h v = complexDilatation (fun v => teichStretch k (G v)) v := by
    have h1 : ∀ᵐ v ∂(volume.restrict U), complexDilatation h v = ν v :=
      ae_restrict_of_ae_restrict_of_subset hUA hhd
    filter_upwards [h1, ae_restrict_mem hUo.measurableSet] with v hv1 hv2
    rw [hv1, hdil v hv2]
  have hae' : ∀ᵐ v ∂(volume.restrict U),
      complexDilatation (fun v => teichStretch k (G v)) v = complexDilatation h v := by
    filter_upwards [hae] with v hv
    exact hv.symm
  -- the local inverse of `N`
  have hNs : HasStrictDerivAt N (deriv N (ψ x₀)) (ψ x₀) := hNa.hasStrictDerivAt
  have hNinv := hNs.to_localInverse hN0
  have hNl := hNs.eventually_left_inverse hN0
  set Ninv := hNs.localInverse N (deriv N (ψ x₀)) (ψ x₀) hN0 with hNinvdef
  have hΨWc : ContinuousAt (fun v => Ψ (W.symm v)) t₀ := by
    have h1 : W.symm t₀ ∈ Ψ.source := by rw [hWy₀]; exact hy₀Ψ
    exact (Ψ.continuousAt h1).comp (W.continuousAt_symm ht₀t)
  have hΨWt : Tendsto (fun v => Ψ (W.symm v)) (𝓝 t₀) (𝓝 (ψ x₀)) := by
    have := hΨWc.tendsto
    rwa [hWy₀, hΨy₀] at this
  have hΨeq : ∀ᶠ v in 𝓝 t₀, Ψ (W.symm v) = Ninv (teichStretch k (G v)) := by
    filter_upwards [hΨWt.eventually hNl, hNWv] with v h1 h2
    rw [← h2]
    exact h1.symm
  have hNt₀ : N (ψ x₀) = teichStretch k (G t₀) := by
    have := hNWv.self_of_nhds
    rwa [hWy₀, hΨy₀] at this
  constructor
  · -- `Ψ ∘ (h ∘ W)⁻¹` at `h t₀`
    obtain ⟨hc1, -, -⟩ := bg_conformal_of_dilatation_eq hhU hUK hae'
    have hhUo : IsOpen (h '' U) := h.isOpenMap U hUo
    have hht₀ : h t₀ ∈ h '' U := mem_image_of_mem h ht₀U
    have hinv : ∀ w ∈ h '' U, Function.invFunOn h U w = h.symm w := by
      rintro _ ⟨v, hv, rfl⟩
      rw [h.symm_apply_apply]
      exact h.injective.injOn.leftInvOn_invFunOn hv
    have hd1 : DifferentiableAt ℂ ((fun v => teichStretch k (G v)) ∘ Function.invFunOn h U) (h t₀) :=
      (hc1 _ hht₀).differentiableAt (hhUo.mem_nhds hht₀)
    have hv1 : ((fun v => teichStretch k (G v)) ∘ Function.invFunOn h U) (h t₀) = N (ψ x₀) := by
      show teichStretch k (G (Function.invFunOn h U (h t₀))) = _
      rw [hinv _ hht₀, h.symm_apply_apply, hNt₀]
    have hd2 : DifferentiableAt ℂ Ninv (((fun v => teichStretch k (G v)) ∘ Function.invFunOn h U) (h t₀)) := by
      rw [hv1]
      exact hNinv.hasDerivAt.differentiableAt
    have hcomp := hd2.comp (h t₀) hd1
    have hev : (fun w => Ψ ((W.trans h.toOpenPartialHomeomorph).symm w)) =ᶠ[𝓝 (h t₀)]
        Ninv ∘ ((fun v => teichStretch k (G v)) ∘ Function.invFunOn h U) := by
      have h1 : Tendsto h.symm (𝓝 (h t₀)) (𝓝 t₀) := by
        have := h.symm.continuous.continuousAt.tendsto (x := h t₀)
        rwa [h.symm_apply_apply] at this
      filter_upwards [h1.eventually hΨeq, hhUo.mem_nhds hht₀] with w hw1 hw2
      show Ψ (W.symm (h.symm w)) = Ninv (teichStretch k (G (Function.invFunOn h U w)))
      rw [hinv w hw2]
      exact hw1
    show DifferentiableAt ℂ (fun w => Ψ ((W.trans h.toOpenPartialHomeomorph).symm w)) (h (W y₀))
    exact hcomp.congr_of_eventuallyEq hev
  · -- `(h ∘ W) ∘ Ψ⁻¹` at `Ψ y₀`
    obtain ⟨hc2, -, -⟩ := bg_conformal_of_dilatation_eq hUK hhU hae
    have hΨt : Ψ y₀ ∈ Ψ.target := Ψ.map_source hy₀Ψ
    have hWΨ : ContinuousAt (fun z => W (Ψ.symm z)) (Ψ y₀) := by
      have h1 : Ψ.symm (Ψ y₀) ∈ W.source := by rw [Ψ.left_inv hy₀Ψ]; exact hy₀W
      exact (W.continuousAt h1).comp (Ψ.continuousAt_symm hΨt)
    have hWΨt : Tendsto (fun z => W (Ψ.symm z)) (𝓝 (Ψ y₀)) (𝓝 t₀) := by
      have := hWΨ.tendsto
      rwa [Ψ.left_inv hy₀Ψ] at this
    -- near `Ψ y₀`: `W ∘ Ψ⁻¹` lands in `U` and inverts `Ψ ∘ W⁻¹`
    have hnear : ∀ᶠ z in 𝓝 (Ψ y₀), z ∈ Ψ.target ∧ Ψ.symm z ∈ W.source ∧ W (Ψ.symm z) ∈ U := by
      have h1 : ∀ᶠ z in 𝓝 (Ψ y₀), Ψ.symm z ∈ W.source := by
        have h2 := (Ψ.continuousAt_symm hΨt).preimage_mem_nhds (W.open_source.mem_nhds
          (by rw [Ψ.left_inv hy₀Ψ]; exact hy₀W))
        exact h2
      filter_upwards [Ψ.open_target.mem_nhds hΨt, h1, hWΨt.eventually (hUo.mem_nhds ht₀U)] with z hz1 hz2 hz3
      exact ⟨hz1, hz2, hz3⟩
    have hval : ∀ᶠ z in 𝓝 (Ψ y₀), N z = teichStretch k (G (W (Ψ.symm z))) := by
      filter_upwards [hnear] with z hz
      obtain ⟨hz1, hz2, hz3⟩ := hz
      have h4 := (hUN hz3).2.2.2
      rw [W.left_inv hz2, Ψ.right_inv hz1] at h4
      exact h4
    have hmaps : MapsTo N {z | z ∈ Ψ.target ∧ Ψ.symm z ∈ W.source ∧ W (Ψ.symm z) ∈ U ∧
        N z = teichStretch k (G (W (Ψ.symm z)))} ((fun v => teichStretch k (G v)) '' U) := by
      rintro z ⟨-, -, hz3, hz4⟩
      rw [hz4]
      exact mem_image_of_mem _ hz3
    have hS : {z | z ∈ Ψ.target ∧ Ψ.symm z ∈ W.source ∧ W (Ψ.symm z) ∈ U ∧
        N z = teichStretch k (G (W (Ψ.symm z)))} ∈ 𝓝 (Ψ y₀) := by
      filter_upwards [hnear, hval] with z hz hz'
      exact ⟨hz.1, hz.2.1, hz.2.2, hz'⟩
    have hNd : DifferentiableAt ℂ N (Ψ y₀) := by
      rw [hΨy₀]
      exact hNa.differentiableAt
    have hmem : N (Ψ y₀) ∈ (fun v => teichStretch k (G v)) '' U := by
      rw [hΨy₀, hNt₀]
      exact mem_image_of_mem _ ht₀U
    have hcomp := (hc2 _ hmem).comp (Ψ y₀) hNd.differentiableWithinAt hmaps
    have hcomp' := hcomp.differentiableAt hS
    have hinj : InjOn (fun v => teichStretch k (G v)) U := hUK.2.2.1.2.1
    have hev : (fun w => (W.trans h.toOpenPartialHomeomorph) (Ψ.symm w)) =ᶠ[𝓝 (Ψ y₀)]
        (h ∘ Function.invFunOn (fun v => teichStretch k (G v)) U) ∘ N := by
      filter_upwards [hS] with z hz
      obtain ⟨-, -, hz3, hz4⟩ := hz
      show h (W (Ψ.symm z)) = h (Function.invFunOn (fun v => teichStretch k (G v)) U (N z))
      rw [hz4, hinj.leftInvOn_invFunOn hz3]
    exact hcomp'.congr_of_eventuallyEq hev

/-- **[stub C4] Compatibility of a hole chart**: for a hole coordinate `W` (holomorphic, with holomorphic inverse,
exactly on the part `1 < ‖W‖`, which is the part in `ι(S₀)`), the Teichmüller dilatation of the deformation written in
the coordinate `W`, `ν = k · conj Q / ‖Q‖` with `Q` the coefficient of `qh` in the coordinate `W⁻¹`, is a Beltrami
coefficient on the annulus; and for every quasiconformal `h` of the plane with dilatation `ν` a.e. on the annulus, the
chart `h ∘ W` is holomorphically compatible with every §26.2 chart `ψ_s` of `S₀` transported to `X` by `ι`
(`bg_conformal_of_dilatation_eq`, both ways). -/
theorem s82td_hole_chart_compat {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) {qh : F₀.X.carrier → ℂ → ℂ}
    (hqh : qh ∈ admissibleQDSpace F₀) {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) {md : S₀ → ℕ} {ζ : S₀ → ℂ → ℂ}
    {Z : S₀ → OpenPartialHomeomorph ℂ ℂ} (hD : ∀ s, s26d_a_Data (pullbackQD F₀ qh) s (md s) (ζ s) (Z s))
    (W : OpenPartialHomeomorph F₀.X.carrier ℂ) {r : ℝ} (hr : 1 < r) (hWt : W.target = ball (0 : ℂ) r)
    (hWι : ∀ y ∈ W.source, y ∈ range F₀.ι ↔ 1 < ‖W y‖)
    (hWd : ∀ y ∈ W.source, 1 < ‖W y‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) W y)
    (hWs : ∀ w ∈ W.target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) W.symm w) :
    ∃ ν : ℂ → ℂ, IsBeltramiCoeff ν {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r} k ∧
      ∀ (h : ℂ ≃ₜ ℂ) (K : ℝ), IsKQC h univ K →
        (∀ᵐ w ∂(volume.restrict {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r}), complexDilatation h w = ν w) →
        (∀ s : S₀, ∀ w ∈ (W.trans h.toOpenPartialHomeomorph).target, (W.trans h.toOpenPartialHomeomorph).symm w ∈
            ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).source →
          DifferentiableAt ℂ (fun w => ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans
            (s26d_a_psi hk₀ hk md Z s)) ((W.trans h.toOpenPartialHomeomorph).symm w)) w) ∧
        (∀ s : S₀, ∀ w ∈ ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).target,
          ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).symm w ∈
            (W.trans h.toOpenPartialHomeomorph).source →
          DifferentiableAt ℂ (fun w => (W.trans h.toOpenPartialHomeomorph)
            (((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).symm w)) w) := by
  classical
  have hAo : IsOpen {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hAm := hAo.measurableSet
  -- the coefficient `Q` of `q̂` in the coordinate `W⁻¹` and the Teichmüller dilatation `ν`
  set Q : ℂ → ℂ := fun t => qh (W.symm t) (chartAt ℂ (W.symm t) (W.symm t)) *
    deriv (fun u => chartAt ℂ (W.symm t) (W.symm u)) t ^ 2 with hQdef
  set ν : ℂ → ℂ := fun t => if 1 < ‖t‖ ∧ ‖t‖ < r then (k : ℂ) * conj (Q t) / ((‖Q t‖ : ℝ) : ℂ) else 0
    with hνdef
  have hνv : ∀ t, 1 < ‖t‖ → ‖t‖ < r → ν t = (k : ℂ) * conj (Q t) / ((‖Q t‖ : ℝ) : ℂ) :=
    fun t h1 h2 => if_pos ⟨h1, h2⟩
  have hq := s32p_pullbackQD_isHolQuadDiff F₀ hqh
  have hq' : IsDiffFamily 2 0 (pullbackQD F₀ qh) ∧
      ∀ x : S₀, DifferentiableOn ℂ (pullbackQD F₀ qh x) (chartAt ℂ x).target := hq
  -- `Q` is continuous on the annulus
  have hQc : ContinuousOn Q {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r} := by
    intro t ht
    have htt : t ∈ W.target := by
      rw [hWt]
      exact mem_ball_zero_iff.2 ht.2
    have hr' : W.symm t ∈ range F₀.ι := (hWι _ (W.map_target htt)).2 (by rw [W.right_inv htt]; exact ht.1)
    obtain ⟨x, hx⟩ := hr'
    have hloc := s82td_Q_local F₀ hqh W hWι hWs htt ht.1 hx
    set τ : ℂ → ℂ := fun v => chartAt ℂ x ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm (W.symm v)) with hτ
    obtain ⟨-, -, -, hτt, -, -⟩ := hloc.self_of_nhds
    obtain ⟨U, hU, hUd⟩ := (hloc.mono fun v hv => hv.2.2.1).exists_mem
    have hτa : AnalyticAt ℂ τ t := DifferentiableOn.analyticAt (fun v hv => (hUd v hv).differentiableWithinAt) hU
    have hqx : ContinuousAt (pullbackQD F₀ qh x) (τ t) :=
      ((hq'.2 x).differentiableAt ((chartAt ℂ x).open_target.mem_nhds hτt)).continuousAt
    have hc : ContinuousAt (fun v => pullbackQD F₀ qh x (τ v) * deriv τ v ^ 2) t :=
      (hqx.comp hτa.continuousAt).mul (hτa.deriv.continuousAt.pow 2)
    have heq : Q =ᶠ[𝓝 t] fun v => pullbackQD F₀ qh x (τ v) * deriv τ v ^ 2 :=
      hloc.mono fun v hv => hv.2.2.2.2.2
    exact (hc.congr heq.symm).continuousWithinAt
  have hνB : IsBeltramiCoeff ν {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r} k := by
    refine ⟨?_, ?_⟩
    · have hQm : AEStronglyMeasurable Q (volume.restrict {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r}) :=
        hQc.aestronglyMeasurable hAm
      have hgm : Measurable (fun u : ℂ => (k : ℂ) * conj u * ((‖u‖ : ℝ) : ℂ)⁻¹) :=
        (measurable_const.mul Complex.continuous_conj.measurable).mul
          (Complex.measurable_ofReal.comp measurable_norm).inv
      refine (hgm.comp_aemeasurable hQm.aemeasurable).aestronglyMeasurable.congr ?_
      filter_upwards [ae_restrict_mem hAm] with t ht
      show (k : ℂ) * conj (Q t) * ((‖Q t‖ : ℝ) : ℂ)⁻¹ = ν t
      rw [hνv t ht.1 ht.2, div_eq_mul_inv]
    · refine Filter.Eventually.of_forall fun t => ?_
      by_cases ht : 1 < ‖t‖ ∧ ‖t‖ < r
      · rw [hνv t ht.1 ht.2]
        by_cases hQ : Q t = 0
        · rw [hQ, map_zero, mul_zero, zero_div, norm_zero]
          exact hk₀
        · rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Complex.norm_real, norm_norm,
            Real.norm_of_nonneg hk₀, mul_div_assoc, div_self (norm_ne_zero_iff.2 hQ), mul_one]
      · show ‖(if 1 < ‖t‖ ∧ ‖t‖ < r then (k : ℂ) * conj (Q t) / ((‖Q t‖ : ℝ) : ℂ) else 0)‖ ≤ k
        rw [if_neg ht, norm_zero]
        exact hk₀
  refine ⟨ν, hνB, fun h K hK hhd => ⟨?_, ?_⟩⟩
  · intro s w hw hws
    have hreg := fun (y₀ : F₀.X.carrier) hy₀Ψ hy₀W hy₀s =>
      s82td_hole_compat_reg F₀ hqh hk₀ hk hD W hWt hWι hWd hWs hνv h hK hhd s (y₀ := y₀) hy₀Ψ hy₀W hy₀s
    have hyW : (W.trans h.toOpenPartialHomeomorph).symm w ∈ W.source :=
      ((W.trans h.toOpenPartialHomeomorph).map_target hw).1
    have hwy := (W.trans h.toOpenPartialHomeomorph).right_inv hw
    by_cases hys : (W.trans h.toOpenPartialHomeomorph).symm w ≠ F₀.ι s
    · have h1 := (hreg _ hws hyW hys).1
      rwa [hwy] at h1
    · push_neg at hys
      have hO : IsOpen ((W.trans h.toOpenPartialHomeomorph).target ∩
          (W.trans h.toOpenPartialHomeomorph).symm ⁻¹'
            ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).source) :=
        (W.trans h.toOpenPartialHomeomorph).isOpen_inter_preimage_symm
          ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).open_source
      have hwO := hO.mem_nhds (show w ∈ _ from ⟨hw, hws⟩)
      refine ((Complex.differentiableOn_compl_singleton_and_continuousAt_iff hwO).1 ⟨?_, ?_⟩).differentiableAt hwO
      · intro w' hw'
        obtain ⟨⟨hw't, hw'Ψ⟩, hw'ne⟩ := hw'
        have hy' : (W.trans h.toOpenPartialHomeomorph).symm w' ≠ F₀.ι s := by
          intro h'
          apply hw'ne
          have h2 := congrArg (W.trans h.toOpenPartialHomeomorph) (h'.trans hys.symm)
          rw [(W.trans h.toOpenPartialHomeomorph).right_inv hw't, hwy] at h2
          exact h2
        have h1 := (hreg _ hw'Ψ ((W.trans h.toOpenPartialHomeomorph).map_target hw't).1 hy').1
        rw [(W.trans h.toOpenPartialHomeomorph).right_inv hw't] at h1
        exact h1.differentiableWithinAt
      · exact (((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans
          (s26d_a_psi hk₀ hk md Z s)).continuousAt hws).comp
          ((W.trans h.toOpenPartialHomeomorph).continuousAt_symm hw)
  · intro s w hw hwΦ
    have hreg := fun (y₀ : F₀.X.carrier) hy₀Ψ hy₀W hy₀s =>
      s82td_hole_compat_reg F₀ hqh hk₀ hk hD W hWt hWι hWd hWs hνv h hK hhd s (y₀ := y₀) hy₀Ψ hy₀W hy₀s
    have hyΨ : ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).symm w ∈
        ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).source :=
      ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).map_target hw
    have hwy := ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).right_inv hw
    by_cases hys : ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).symm w ≠
        F₀.ι s
    · have h1 := (hreg _ hyΨ hwΦ.1 hys).2
      rwa [hwy] at h1
    · push_neg at hys
      have hO : IsOpen (((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).target ∩
          ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).symm ⁻¹'
            (W.trans h.toOpenPartialHomeomorph).source) :=
        ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).isOpen_inter_preimage_symm
          (W.trans h.toOpenPartialHomeomorph).open_source
      have hwO := hO.mem_nhds (show w ∈ _ from ⟨hw, hwΦ⟩)
      refine ((Complex.differentiableOn_compl_singleton_and_continuousAt_iff hwO).1 ⟨?_, ?_⟩).differentiableAt hwO
      · intro w' hw'
        obtain ⟨⟨hw't, hw'Φ⟩, hw'ne⟩ := hw'
        have hy' : ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).symm w' ≠
            F₀.ι s := by
          intro h'
          apply hw'ne
          have h2 := congrArg ((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s))
            (h'.trans hys.symm)
          rw [((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).right_inv hw't,
            hwy] at h2
          exact h2
        have h1 := (hreg _ (((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans
          (s26d_a_psi hk₀ hk md Z s)).map_target hw't) hw'Φ.1 hy').2
        rw [((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).right_inv hw't] at h1
        exact h1.differentiableWithinAt
      · exact ((W.trans h.toOpenPartialHomeomorph).continuousAt hwΦ).comp
          (((F₀.embedding.toOpenPartialHomeomorph F₀.ι).symm.trans (s26d_a_psi hk₀ hk md Z s)).continuousAt_symm hw)

/-- The unit circle `t ↦ exp(2πit)`: a smooth, regular, `1`-periodic parametrization of `frontier Δ`, injective on
`[0, 1)`. -/
theorem s82td_circle_param : ∃ c : ℝ → ℂ, ContDiff ℝ ∞ c ∧ (∀ t, deriv c t ≠ 0) ∧ (∀ t, c (t + 1) = c t) ∧
    InjOn c (Ico 0 1) ∧ c '' Ico 0 1 = frontier unitDisc := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (2 * π * I * t))
      (Complex.exp (2 * π * I * t) * (2 * π * I)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => 2 * π * I * (t : ℂ)) (2 * π * I * 1) t :=
      (hasDerivAt_id t).ofReal_comp.const_mul (2 * π * I)
    rw [mul_one] at h1
    exact h1.cexp
  refine ⟨fun t => Complex.exp (2 * π * I * t), ?_, ?_, ?_, ?_, ?_⟩
  · exact (Complex.contDiff_exp (𝕜 := ℝ)).comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
  · intro t
    rw [(hd t).deriv]
    refine mul_ne_zero (Complex.exp_ne_zero _) ?_
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  · intro t
    show Complex.exp (2 * π * I * ((t + 1 : ℝ) : ℂ)) = Complex.exp (2 * π * I * t)
    rw [Complex.ofReal_add, Complex.ofReal_one, mul_add, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I,
      mul_one]
  · intro s hs t ht h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    have hI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h2 : ((s : ℂ) - t - n) * (2 * π * I) = 0 := by linear_combination hn
    have h2' : (s : ℂ) - t - n = 0 := (mul_eq_zero.1 h2).resolve_right hI
    have h2'' : ((s - t - n : ℝ) : ℂ) = 0 := by push_cast; exact h2'
    have h2''' : s - t - n = 0 := by exact_mod_cast h2''
    have h3 : s = t + n := by linarith
    have hn0 : n = 0 := by
      have h4 : (n : ℝ) < 1 := by linarith [hs.1, hs.2, ht.1, ht.2]
      have h5 : (-1 : ℝ) < n := by linarith [hs.1, hs.2, ht.1, ht.2]
      have h6 : n < 1 := by exact_mod_cast h4
      have h7 : -1 < n := by exact_mod_cast h5
      omega
    rw [h3, hn0]
    simp
  · rw [show unitDisc = ball (0 : ℂ) 1 from rfl, frontier_ball (0 : ℂ) one_ne_zero]
    ext z
    constructor
    · rintro ⟨t, -, rfl⟩
      show Complex.exp (2 * π * I * (t : ℂ)) ∈ sphere (0 : ℂ) 1
      rw [mem_sphere_zero_iff_norm]
      have : (2 * π * I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    · intro hz
      have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hz
      have hze : z = Complex.exp (Complex.arg z * I) := by
        have h := Complex.norm_mul_exp_arg_mul_I z
        rw [hz1, Complex.ofReal_one, one_mul] at h
        exact h.symm
      have hpi : 0 < π := Real.pi_pos
      have hpi' : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hlin : (2 * π * I * ((Complex.arg z / (2 * π) : ℝ) : ℂ)) = (Complex.arg z : ℂ) * I := by
        push_cast
        field_simp
        try ring
      by_cases ha : 0 ≤ Complex.arg z
      · refine ⟨Complex.arg z / (2 * π), ⟨div_nonneg ha (by linarith), ?_⟩, ?_⟩
        · rw [div_lt_one (by linarith)]
          linarith [Complex.arg_le_pi z]
        · show Complex.exp (2 * π * I * ((Complex.arg z / (2 * π) : ℝ) : ℂ)) = z
          rw [hlin]
          exact hze.symm
      · push_neg at ha
        refine ⟨Complex.arg z / (2 * π) + 1, ⟨?_, ?_⟩, ?_⟩
        · have h1 : -π < Complex.arg z := Complex.neg_pi_lt_arg z
          have h2 : -(1 / 2 : ℝ) < Complex.arg z / (2 * π) := by
            rw [lt_div_iff₀ (by linarith)]
            linarith
          linarith
        · have h2 : Complex.arg z / (2 * π) < 0 := div_neg_of_neg_of_pos ha (by linarith)
          linarith
        · show Complex.exp (2 * π * I * ((Complex.arg z / (2 * π) + 1 : ℝ) : ℂ)) = z
          rw [Complex.ofReal_add, Complex.ofReal_one, mul_add, mul_one, Complex.exp_add,
            Complex.exp_two_pi_mul_I, mul_one, hlin]
          exact hze.symm

/-- A set mapped by a chart onto the closed unit disc (inside the chart target) is a closed disc with smooth
boundary in the sense of `IsClosedDiscIn`. -/
theorem s82td_isClosedDiscIn_of_chart {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {D : Set X} (x : X)
    (hDs : D ⊆ (chartAt ℂ x).source) (hDb : chartAt ℂ x '' D = closedBall (0 : ℂ) 1)
    (hbt : closedBall (0 : ℂ) 1 ⊆ (chartAt ℂ x).target) : IsClosedDiscIn D := by
  have hcl : closure unitDisc = closedBall (0 : ℂ) 1 := closure_ball (0 : ℂ) one_ne_zero
  obtain ⟨c, hc1, hc2, hc3, hc4, hc5⟩ := s82td_circle_param
  exact ⟨x, hDs, unitDisc, isJordanDomain_unitDisc, isBounded_ball, hcl ▸ hbt, hcl ▸ hDb, c, hc1, hc2, hc3, hc4,
    hc5⟩

/-- Factoring a transition through a third chart `Ψ` at the common point. -/
theorem s82td_compat_factor {X : Type*} [TopologicalSpace X] {φ₁ φ₂ Ψ : OpenPartialHomeomorph X ℂ} {w : ℂ}
    (hw : w ∈ φ₂.target) (hΨ : φ₂.symm w ∈ Ψ.source)
    (hd1 : DifferentiableAt ℂ (fun v => φ₁ (Ψ.symm v)) (Ψ (φ₂.symm w)))
    (hd2 : DifferentiableAt ℂ (fun v => Ψ (φ₂.symm v)) w) :
    DifferentiableAt ℂ (fun v => φ₁ (φ₂.symm v)) w := by
  have heq : (fun v => φ₁ (φ₂.symm v)) =ᶠ[𝓝 w] (fun v => φ₁ (Ψ.symm v)) ∘ fun v => Ψ (φ₂.symm v) := by
    filter_upwards [(φ₂.continuousAt_symm hw).preimage_mem_nhds (Ψ.open_source.mem_nhds hΨ)] with v hv
    simp only [Function.comp_apply]
    rw [Ψ.left_inv hv]
  exact (hd1.comp w hd2).congr_of_eventuallyEq heq

/-- **[stub W4(C)] Realization with holes** (`m ≠ 0`): give the closed surface `X` of `F₀` a new atlas: the
§26.2 charts of the deformation on `ι(S₀)`, the puncture charts, and one hole chart `h_j ∘ W_j` per hole
(C2, C3, C4: the circle-symmetric solution of the Beltrami equation for the Teichmüller dilatation on the collar);
the deformed surface is the complement of the punctures and the (unchanged) discs. -/
theorem s82td_realize_holes {g n m : ℕ} (hex : ¬ IsExceptionalType g n m) (F₀ : FiniteTypeStructure S₀ g n m)
    (hm : m ≠ 0) {q : S₀ → ℂ → ℂ} (hq : q ∈ admissibleQDInterior F₀) (hq0 : q ≠ 0) {k : ℝ}
    (hk0 : 0 < k) (hk1 : k < 1) :
    ∃ (A : MarkedFiniteTypeRS S₀ g n m) (q' : A.X.carrier → ℂ → ℂ), IsAdmissibleTeichmullerMap F₀ A.marking q q' k := by
  classical
  obtain ⟨qh, hqh, rfl⟩ := Submodule.mem_map.1 hq
  have hqq : pullbackQDLinear F₀ qh = pullbackQD F₀ qh := rfl
  rw [hqq] at hq0 ⊢
  have hqhol : IsHolQuadDiff (pullbackQD F₀ qh) := s32p_pullbackQD_isHolQuadDiff F₀ hqh
  choose mf ζf Zf hD using s26d_a_data_exists hqhol hq0
  set ψ := s26d_a_psi hk0.le hk1 mf Zf with hψ
  set ιe := F₀.embedding.toOpenPartialHomeomorph F₀.ι with hιe
  have hleft : ∀ s : S₀, ιe.symm (F₀.ι s) = s := fun s => F₀.embedding.toOpenPartialHomeomorph_left_inv F₀.ι
  have hrangeX : ∀ x : F₀.X.carrier, x ∈ range F₀.ι ↔ x ∉ F₀.P ∧ ∀ j, x ∉ F₀.D j := by
    intro x
    rw [F₀.range_ι]
    simp
  have hDP : ∀ j, ∀ x ∈ F₀.D j, x ∉ F₀.P := fun j x hx hxP =>
    Set.disjoint_left.1 (F₀.disjoint_P j) hx (Finset.mem_coe.2 hxP)
  -- the hole charts `h_j ∘ W_j` (C2, C4, C3)
  obtain ⟨W, r, hW, hWdisj⟩ := s82td_hole_coordinates F₀
  have hDW : ∀ i j, ∀ y ∈ (W j).source, y ∈ F₀.D i → i = j := by
    intro i j y hy hyi
    by_contra hij
    exact Set.disjoint_left.1 (hWdisj hij) ((hW i).2.2.1 hyi) hy
  have hWι : ∀ j, ∀ y ∈ (W j).source, y ∈ range F₀.ι ↔ 1 < ‖W j y‖ := by
    intro j y hy
    rw [hrangeX, ← not_le, ← (hW j).2.2.2.1 y hy]
    constructor
    · intro h
      exact h.2 j
    · intro h
      exact ⟨(hW j).2.2.2.2.1 y hy, fun i hi => h (hDW i j y hy hi ▸ hi)⟩
  have hc4 : ∀ j, ∃ ν : ℂ → ℂ, IsBeltramiCoeff ν {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r j} k ∧
      ∀ (h : ℂ ≃ₜ ℂ) (K : ℝ), IsKQC h univ K →
        (∀ᵐ w ∂(volume.restrict {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r j}), complexDilatation h w = ν w) →
        (∀ s : S₀, ∀ w ∈ ((W j).trans h.toOpenPartialHomeomorph).target,
            ((W j).trans h.toOpenPartialHomeomorph).symm w ∈ (ιe.symm.trans (ψ s)).source →
          DifferentiableAt ℂ (fun w => (ιe.symm.trans (ψ s)) (((W j).trans h.toOpenPartialHomeomorph).symm w)) w) ∧
        (∀ s : S₀, ∀ w ∈ (ιe.symm.trans (ψ s)).target,
          (ιe.symm.trans (ψ s)).symm w ∈ ((W j).trans h.toOpenPartialHomeomorph).source →
          DifferentiableAt ℂ (fun w => ((W j).trans h.toOpenPartialHomeomorph) ((ιe.symm.trans (ψ s)).symm w)) w) :=
    fun j => s82td_hole_chart_compat F₀ hqh hk0.le hk1 hD (W j) (hW j).1 (hW j).2.1 (hWι j)
      (fun y hy h1 => (hW j).2.2.2.2.2.1 y hy fun hyD => absurd ((hW j).2.2.2.1 y hy |>.1 hyD) (not_le.2 h1))
      (hW j).2.2.2.2.2.2
  choose ν hνB hνc using hc4
  have hc3 := fun j => s82td_circle_solution (hW j).1 hk0.le hk1 (hνB j)
  choose hh K hhiff hhK hhd using hc3
  set Hc : Fin m → OpenPartialHomeomorph F₀.X.carrier ℂ := fun j => (W j).trans (hh j).toOpenPartialHomeomorph
    with hHc
  have hHcompat := fun j => hνc j (hh j) (K j) (hhK j) (hhd j)
  have hHsrc : ∀ j y, y ∈ (Hc j).source ↔ y ∈ (W j).source := fun j y => by
    show y ∈ ((W j).trans (hh j).toOpenPartialHomeomorph).source ↔ _
    rw [OpenPartialHomeomorph.trans_source]
    simp
  have hHapp : ∀ j y, Hc j y = hh j (W j y) := fun j y => rfl
  -- the puncture charts (B3, any hole count)
  have hB3 : ∀ p, p ∈ F₀.P → ∃ χ : OpenPartialHomeomorph F₀.X.carrier ℂ, p ∈ χ.source ∧
      (∀ x ∈ χ.source, x ∈ F₀.P → x = p) ∧
      (∀ s : S₀, ∀ w ∈ χ.target, χ.symm w ∈ (ιe.symm.trans (ψ s)).source →
        DifferentiableAt ℂ (fun w => (ιe.symm.trans (ψ s)) (χ.symm w)) w) ∧
      (∀ s : S₀, ∀ w ∈ (ιe.symm.trans (ψ s)).target, (ιe.symm.trans (ψ s)).symm w ∈ χ.source →
        DifferentiableAt ℂ (fun w => χ ((ιe.symm.trans (ψ s)).symm w)) w) ∧
      ∀ x ∈ χ.source, ∀ j, x ∉ F₀.D j :=
    fun p hp => s82td_puncture_chart F₀ hqh hk0.le hk1 hD hp
  haveI : Nonempty (OpenPartialHomeomorph F₀.X.carrier ℂ) := ⟨chartAt ℂ (Classical.arbitrary F₀.X.carrier)⟩
  choose! χf hχf using hB3
  -- the atlas
  set ψ' : F₀.X.carrier → OpenPartialHomeomorph F₀.X.carrier ℂ := fun x =>
    if x ∈ F₀.P then χf x else if hx : ∃ j, x ∈ F₀.D j then Hc hx.choose else ιe.symm.trans (ψ (ιe.symm x))
    with hψ'
  have hψ'P : ∀ x, x ∈ F₀.P → ψ' x = χf x := fun x hx => if_pos hx
  have hψ'D : ∀ j, ∀ x ∈ F₀.D j, ψ' x = Hc j := by
    intro j x hx
    have hxP := hDP j x hx
    have hex : ∃ j, x ∈ F₀.D j := ⟨j, hx⟩
    have h1 : ψ' x = Hc hex.choose := by
      show (if x ∈ F₀.P then χf x else if hx : ∃ j, x ∈ F₀.D j then Hc hx.choose
        else ιe.symm.trans (ψ (ιe.symm x))) = _
      rw [if_neg hxP, dif_pos hex]
    rw [h1, hDW _ j x ((hW j).2.2.1 hx) hex.choose_spec]
  have hψ'ι : ∀ s : S₀, ψ' (F₀.ι s) = ιe.symm.trans (ψ s) := by
    intro s
    obtain ⟨h1, h2⟩ := (hrangeX _).1 (mem_range_self s)
    have hex : ¬ ∃ j, F₀.ι s ∈ F₀.D j := fun ⟨j, hj⟩ => h2 j hj
    show (if F₀.ι s ∈ F₀.P then χf (F₀.ι s) else if hx : ∃ j, F₀.ι s ∈ F₀.D j then Hc hx.choose
      else ιe.symm.trans (ψ (ιe.symm (F₀.ι s)))) = _
    rw [if_neg h1, dif_neg hex, hleft]
  have hΨapp : ∀ s y : S₀, (ιe.symm.trans (ψ s)) (F₀.ι y) = ψ s y := fun s y => by
    show ψ s (ιe.symm (F₀.ι y)) = _
    rw [hleft]
  have hΨsrc : ∀ (s : S₀) (y : F₀.X.carrier), y ∈ (ιe.symm.trans (ψ s)).source →
      ∃ x' : S₀, F₀.ι x' = y ∧ x' ∈ (ψ s).source := by
    intro s y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hyr : y ∈ range F₀.ι := by
      have : y ∈ ιe.target := hy1
      rwa [F₀.embedding.toOpenPartialHomeomorph_target] at this
    obtain ⟨x', rfl⟩ := hyr
    refine ⟨x', rfl, ?_⟩
    have : ιe.symm (F₀.ι x') ∈ (ψ s).source := hy2
    rwa [hleft] at this
  have hΨmem : ∀ s : S₀, F₀.ι s ∈ (ιe.symm.trans (ψ s)).source := by
    intro s
    refine ⟨?_, ?_⟩
    · show F₀.ι s ∈ ιe.target
      rw [F₀.embedding.toOpenPartialHomeomorph_target]
      exact mem_range_self s
    · show ιe.symm (F₀.ι s) ∈ (ψ s).source
      rw [hleft]
      exact (s26d_a_psi_center hk0.le hk1 hD s).1
  -- every point is a puncture, a point of a hole, or a point `ι s`
  have hkind : ∀ x : F₀.X.carrier, x ∈ F₀.P ∨ (∃ j, x ∈ F₀.D j) ∨ ∃ s, F₀.ι s = x := by
    intro x
    by_cases hx : x ∈ F₀.P
    · exact Or.inl hx
    · by_cases hd : ∃ j, x ∈ F₀.D j
      · exact Or.inr (Or.inl hd)
      · push_neg at hd
        obtain ⟨s, hs⟩ := (hrangeX x).2 ⟨hx, hd⟩
        exact Or.inr (Or.inr ⟨s, hs⟩)
  have hmem : ∀ x, x ∈ (ψ' x).source := by
    intro x
    rcases hkind x with hx | ⟨j, hj⟩ | ⟨s, rfl⟩
    · rw [hψ'P x hx]
      exact (hχf x hx).1
    · rw [hψ'D j x hj, hHsrc]
      exact (hW j).2.2.1 hj
    · rw [hψ'ι]
      exact hΨmem s
  -- transitions between transported charts are the §26.2 transitions
  have hΨΨ : ∀ (s s' : S₀) (w : ℂ), w ∈ (ιe.symm.trans (ψ s')).target →
      (ιe.symm.trans (ψ s')).symm w ∈ (ιe.symm.trans (ψ s)).source →
      DifferentiableAt ℂ (fun w => (ιe.symm.trans (ψ s)) ((ιe.symm.trans (ψ s')).symm w)) w := by
    intro s s' w hw hws
    have hw' : w ∈ (ψ s').target := hw.1
    have hsymm : ∀ v, (ιe.symm.trans (ψ s')).symm v = F₀.ι ((ψ s').symm v) := fun v => by
      show ιe ((ψ s').symm v) = _
      rw [hιe, F₀.embedding.toOpenPartialHomeomorph_apply]
    have hws' : (ψ s').symm w ∈ (ψ s).source := by
      obtain ⟨x', hx', hx'src⟩ := hΨsrc s _ hws
      rw [hsymm] at hx'
      rwa [← F₀.embedding.injective hx']
    have hfun : (fun w => (ιe.symm.trans (ψ s)) ((ιe.symm.trans (ψ s')).symm w)) =
        fun w => ψ s ((ψ s').symm w) := by
      funext v
      rw [hsymm, hΨapp]
    rw [hfun]
    exact (s26d_a_transition hqhol hk0.le hk1 hD s s' hw' hws').1
  -- every chart of the atlas is compatible with every transported chart, both ways
  have hint1 : ∀ p s, ∀ w ∈ (ιe.symm.trans (ψ s)).target, (ιe.symm.trans (ψ s)).symm w ∈ (ψ' p).source →
      DifferentiableAt ℂ (fun w => ψ' p ((ιe.symm.trans (ψ s)).symm w)) w := by
    intro p s w hw hwp
    rcases hkind p with hp | ⟨j, hj⟩ | ⟨s', rfl⟩
    · rw [hψ'P p hp] at hwp ⊢
      exact (hχf p hp).2.2.2.1 s w hw hwp
    · rw [hψ'D j p hj] at hwp ⊢
      exact (hHcompat j).2 s w hw hwp
    · rw [hψ'ι] at hwp ⊢
      exact hΨΨ s' s w hw hwp
  have hint2 : ∀ p s, ∀ w ∈ (ψ' p).target, (ψ' p).symm w ∈ (ιe.symm.trans (ψ s)).source →
      DifferentiableAt ℂ (fun w => (ιe.symm.trans (ψ s)) ((ψ' p).symm w)) w := by
    intro p s w hw hws
    rcases hkind p with hp | ⟨j, hj⟩ | ⟨s', rfl⟩
    · rw [hψ'P p hp] at hw hws ⊢
      exact (hχf p hp).2.2.1 s w hw hws
    · rw [hψ'D j p hj] at hw hws ⊢
      exact (hHcompat j).1 s w hw hws
    · rw [hψ'ι] at hw hws ⊢
      exact hΨΨ s s' w hw hws
  -- a point of `P` lies only in its own puncture chart; a point of `D j` only in the hole chart `j`
  have hsrcP : ∀ p y, y ∈ (ψ' p).source → y ∈ F₀.P → ψ' p = χf y := by
    intro p y hy hyP
    rcases hkind p with hp | ⟨j, hj⟩ | ⟨s, rfl⟩
    · rw [hψ'P p hp] at hy ⊢
      rw [(hχf p hp).2.1 y hy hyP]
    · rw [hψ'D j p hj, hHsrc] at hy
      exact absurd hyP ((hW j).2.2.2.2.1 y hy)
    · rw [hψ'ι] at hy
      obtain ⟨x', rfl, -⟩ := hΨsrc s y hy
      exact absurd hyP ((hrangeX _).1 (mem_range_self x')).1
  have hsrcD : ∀ p y j, y ∈ (ψ' p).source → y ∈ F₀.D j → ψ' p = Hc j := by
    intro p y j hy hyj
    rcases hkind p with hp | ⟨i, hi⟩ | ⟨s, rfl⟩
    · rw [hψ'P p hp] at hy
      exact absurd hyj ((hχf p hp).2.2.2.2 y hy j)
    · rw [hψ'D i p hi] at hy ⊢
      rw [hHsrc] at hy
      rw [hDW j i y hy hyj]
    · rw [hψ'ι] at hy
      obtain ⟨x', rfl, -⟩ := hΨsrc s y hy
      exact absurd hyj (((hrangeX _).1 (mem_range_self x')).2 j)
  have hcompat : ∀ p p', ∀ w ∈ (ψ' p').target, (ψ' p').symm w ∈ (ψ' p).source →
      DifferentiableAt ℂ (fun w => ψ' p ((ψ' p').symm w)) w := by
    intro p p' w hw hwp
    have hy' : (ψ' p').symm w ∈ (ψ' p').source := (ψ' p').map_target hw
    rcases hkind ((ψ' p').symm w) with hyP | ⟨j, hyj⟩ | ⟨s, hs⟩
    · have h1 := hsrcP p _ hwp hyP
      have h2 := hsrcP p' _ hy' hyP
      rw [h1]
      have hid : (fun v => χf ((ψ' p').symm w) ((ψ' p').symm v)) =ᶠ[𝓝 w] fun v => v := by
        filter_upwards [(ψ' p').open_target.mem_nhds hw] with v hv
        rw [← h2]
        exact (ψ' p').right_inv hv
      exact differentiableAt_id.congr_of_eventuallyEq hid
    · have h1 := hsrcD p _ j hwp hyj
      have h2 := hsrcD p' _ j hy' hyj
      rw [h1]
      have hid : (fun v => Hc j ((ψ' p').symm v)) =ᶠ[𝓝 w] fun v => v := by
        filter_upwards [(ψ' p').open_target.mem_nhds hw] with v hv
        rw [← h2]
        exact (ψ' p').right_inv hv
      exact differentiableAt_id.congr_of_eventuallyEq hid
    · have hΨ : (ψ' p').symm w ∈ (ιe.symm.trans (ψ s)).source := by rw [← hs]; exact hΨmem s
      have hv : (ιe.symm.trans (ψ s)) ((ψ' p').symm w) ∈ (ιe.symm.trans (ψ s)).target :=
        (ιe.symm.trans (ψ s)).map_source hΨ
      have hvs : (ιe.symm.trans (ψ s)).symm ((ιe.symm.trans (ψ s)) ((ψ' p').symm w)) = (ψ' p').symm w :=
        (ιe.symm.trans (ψ s)).left_inv hΨ
      exact s82td_compat_factor hw hΨ (hint1 p s _ hv (by rw [hvs]; exact hwp)) (hint2 p' s w hw hΨ)
  -- the deformed closed surface
  obtain ⟨X', τX, csX, hT2, hconn, hcpt, hman, e, he⟩ := s82td_charted_package ψ' hmem hcompat
  let XR : ClosedRS.{u} := ⟨X'⟩
  have hgen : HasGenus XR.carrier g := hasGenus_of_homeomorph F₀.genus (e : F₀.X.carrier ≃ₜ XR.carrier)
  set P' : Finset XR.carrier := F₀.P.map e.toEquiv.toEmbedding with hP'
  have hP'card : P'.card = n := by rw [hP', Finset.card_map, F₀.card_P]
  have hP'mem : ∀ x : F₀.X.carrier, e x ∈ P' ↔ x ∈ F₀.P := by
    intro x
    rw [hP', Finset.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := e.injective hyx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hP'coe : (↑P' : Set XR.carrier) = e '' ↑F₀.P := by
    ext x
    obtain ⟨x₀, rfl⟩ := e.surjective x
    rw [Finset.mem_coe, hP'mem, (e.injective.mem_set_image), Finset.mem_coe]
  set D' : Fin m → Set XR.carrier := fun j => e '' F₀.D j with hD'
  have hD'mem : ∀ j (x : F₀.X.carrier), e x ∈ D' j ↔ x ∈ F₀.D j := fun j x => e.injective.mem_set_image
  have hD'cl : ∀ j, IsClosed (D' j) := fun j =>
    ((s31eg_disc_compact (F₀.disc j)).image e.continuous).isClosed
  have hOo : IsOpen ((↑P' ∪ ⋃ j, D' j)ᶜ : Set XR.carrier) :=
    (P'.finite_toSet.isClosed.union (isClosed_iUnion_of_finite hD'cl)).isOpen_compl
  let O : TopologicalSpace.Opens XR.carrier := ⟨(↑P' ∪ ⋃ j, D' j)ᶜ, hOo⟩
  have hOmem : ∀ x : F₀.X.carrier, e x ∈ (O : Set XR.carrier) ↔ x ∈ range F₀.ι := by
    intro x
    rw [hrangeX]
    show e x ∉ (↑P' ∪ ⋃ j, D' j) ↔ _
    simp only [mem_union, mem_iUnion, not_or, not_exists, Finset.mem_coe, hP'mem, hD'mem]
  -- the marking `s ↦ e(ι s)`
  have hemb : Topology.IsEmbedding (fun s => e (F₀.ι s)) := e.isEmbedding.comp F₀.embedding.isEmbedding
  have hrange : range (fun s => e (F₀.ι s)) = (O : Set XR.carrier) := by
    ext x
    obtain ⟨x₀, rfl⟩ := e.surjective x
    rw [hOmem]
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨s, e.injective hs⟩
    · rintro ⟨s, hs⟩
      exact ⟨s, congrArg e hs⟩
  set f : S₀ ≃ₜ O := hemb.toHomeomorph.trans (Homeomorph.setCongr hrange) with hf
  have hfv : ∀ s, (f s : XR.carrier) = e (F₀.ι s) := fun s => rfl
  haveI : ConnectedSpace O := f.surjective.connectedSpace f.continuous
  -- the finite-type structure of the deformed surface
  have hdisc : ∀ j, IsClosedDiscIn (D' j) := by
    intro j
    obtain ⟨x, -, J, hJ, -, -, hDJ, -⟩ := F₀.disc j
    obtain ⟨d₀, hd₀⟩ : (F₀.D j).Nonempty := by
      have h1 : (closure J).Nonempty := hJ.2.1.nonempty.closure
      rw [← hDJ] at h1
      exact h1.of_image
    have hch : ∀ y, chartAt ℂ (e d₀) (e y) = Hc j y := by
      intro y
      rw [(he d₀).1, hψ'D j d₀ hd₀]
    have hsrc : (chartAt ℂ (e d₀)).source = e '' (Hc j).source := by
      rw [(he d₀).2.1, hψ'D j d₀ hd₀]
    have htg : (chartAt ℂ (e d₀)).target = (Hc j).target := by
      rw [(he d₀).2.2.1, hψ'D j d₀ hd₀]
    have hDs : F₀.D j ⊆ (Hc j).source := fun y hy => (hHsrc j y).2 ((hW j).2.2.1 hy)
    have hDb : Hc j '' F₀.D j = closedBall (0 : ℂ) 1 := by
      ext w
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [hHapp, mem_closedBall_zero_iff, hhiff j]
        exact ((hW j).2.2.2.1 y ((hW j).2.2.1 hy)).1 hy
      · intro hw
        have hw1 : ‖(hh j).symm w‖ ≤ 1 := by
          rw [← hhiff j, Homeomorph.apply_symm_apply]
          exact mem_closedBall_zero_iff.1 hw
        have hwt : (hh j).symm w ∈ (W j).target := by
          rw [(hW j).2.1, mem_ball_zero_iff]
          linarith [(hW j).1]
        refine ⟨(W j).symm ((hh j).symm w), ?_, ?_⟩
        · have hs := (W j).map_target hwt
          refine ((hW j).2.2.2.1 _ hs).2 ?_
          rw [(W j).right_inv hwt]
          exact hw1
        · rw [hHapp, (W j).right_inv hwt, Homeomorph.apply_symm_apply]
    have hbt : closedBall (0 : ℂ) 1 ⊆ (Hc j).target := by
      intro w hw
      rw [← hDb] at hw
      obtain ⟨y, hy, rfl⟩ := hw
      exact (Hc j).map_source (hDs hy)
    refine s82td_isClosedDiscIn_of_chart (e d₀) ?_ ?_ ?_
    · rw [hsrc]
      exact image_mono hDs
    · rw [← hDb]
      ext w
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, (hch y).symm⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨e y, ⟨y, hy, rfl⟩, hch y⟩
    · rw [htg]
      exact hbt
  have Fy : FiniteTypeStructure O g n m :=
    { X := XR
      P := P'
      D := D'
      ι := Subtype.val
      genus := hgen
      card_P := hP'card
      disc := hdisc
      disjoint := fun i j hij => (Set.disjoint_image_iff e.injective).2 (F₀.disjoint hij)
      disjoint_P := fun j => by
        rw [hP'coe]
        exact (Set.disjoint_image_iff e.injective).2 (F₀.disjoint_P j)
      embedding := O.isOpen.isOpenEmbedding_subtypeVal
      holomorphic := (contMDiff_subtype_val (n := ω) (U := O)).mdifferentiable (by simp)
      range_ι := Subtype.range_coe }
  -- charts of the deformed surface at `f s`
  have hchartv : ∀ s x, chartAt ℂ (f s) (f x) = ψ s x := by
    intro s x
    show chartAt ℂ ((f s : XR.carrier)) ((f x : XR.carrier)) = _
    rw [hfv, hfv, (he (F₀.ι s)).1, hψ'ι, hΨapp]
  have hchartS : ∀ s, chartAt ℂ (f s : XR.carrier) = chartAt ℂ (e (F₀.ι s)) := fun s => by rw [hfv]
  have htgt : ∀ s, (chartAt ℂ (f s)).target = (ψ s).target := by
    intro s
    have h1 : (chartAt ℂ (f s)).target =
        (chartAt ℂ (f s : XR.carrier)).target ∩ (chartAt ℂ (f s : XR.carrier)).symm ⁻¹' (O : Set XR.carrier) := by
      rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_def,
        OpenPartialHomeomorph.trans_target, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
    rw [h1, hchartS, (he (F₀.ι s)).2.2.1, hψ'ι]
    ext w
    constructor
    · rintro ⟨⟨hw1, -⟩, -⟩
      exact hw1
    · intro hw
      refine ⟨⟨hw, ?_⟩, ?_⟩
      · show (ψ s).symm w ∈ ιe.source
        rw [F₀.embedding.toOpenPartialHomeomorph_source]
        exact mem_univ _
      · rw [mem_preimage, (he (F₀.ι s)).2.2.2, hψ'ι]
        show e (ιe ((ψ s).symm w)) ∈ (O : Set XR.carrier)
        rw [← hrange]
        refine ⟨(ψ s).symm w, ?_⟩
        rw [hιe, F₀.embedding.toOpenPartialHomeomorph_apply]
  -- the terminal differential on the deformed surface
  set q'' : O → ℂ → ℂ := fun y => (chartAt ℂ y).target.indicator
    (fun w => ((mf (f.symm y) + 2 : ℂ) / 2) ^ 2 * w ^ mf (f.symm y)) with hq''
  have hq''Q : ∀ s, q'' (f s) = (ψ s).target.indicator (fun w => ((mf s + 2 : ℂ) / 2) ^ 2 * w ^ mf s) := by
    intro s
    show (chartAt ℂ (f s)).target.indicator _ = _
    rw [htgt, f.symm_apply_apply]
  have hsymmv : ∀ s, ∀ w ∈ (ψ s).target, ((chartAt ℂ (f s)).symm w : XR.carrier) = e (F₀.ι ((ψ s).symm w)) := by
    intro s w hw
    have hw' : w ∈ ((chartAt ℂ (f s : XR.carrier)).subtypeRestr ⟨f s⟩).target := by
      have : w ∈ (chartAt ℂ (f s)).target := by rw [htgt]; exact hw
      exact this
    have h1 := OpenPartialHomeomorph.subtypeRestr_symm_apply (chartAt ℂ (f s : XR.carrier)) ⟨f s⟩ hw'
    simp only [Function.comp_apply] at h1
    show (((chartAt ℂ (f s : XR.carrier)).subtypeRestr ⟨f s⟩).symm w : XR.carrier) = _
    rw [h1, hchartS, (he (F₀.ι s)).2.2.2, hψ'ι]
    show e (ιe ((ψ s).symm w)) = _
    rw [hιe, F₀.embedding.toOpenPartialHomeomorph_apply]
  have hsymmf : ∀ s, ∀ w ∈ (ψ s).target, (chartAt ℂ (f s)).symm w = f ((ψ s).symm w) := by
    intro s w hw
    apply Subtype.ext
    rw [hsymmv s w hw, hfv]
  have hq''hol : IsHolQuadDiff q'' := by
    refine ⟨⟨fun y z hz => Set.indicator_of_notMem hz _, fun y y' z hz hzy => ?_⟩, fun y => ?_⟩
    · obtain ⟨s, rfl⟩ := f.surjective y
      obtain ⟨s', rfl⟩ := f.surjective y'
      have hz' : z ∈ (ψ s').target := by rw [← htgt]; exact hz
      have hτ : ∀ v ∈ (ψ s').target, chartTransition (f s) (f s') v = ψ s ((ψ s').symm v) := by
        intro v hv
        show chartAt ℂ (f s) ((chartAt ℂ (f s')).symm v) = _
        rw [hsymmf s' v hv, hchartv]
      have hws : (ψ s').symm z ∈ (ψ s).source := by
        have h1 : ((chartAt ℂ (f s')).symm z : XR.carrier) ∈ (chartAt ℂ (f s : XR.carrier)).source := by
          have h0 := hzy
          rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source] at h0
          exact h0
        rw [hsymmv s' z hz', hchartS, (he (F₀.ι s)).2.1, hψ'ι] at h1
        obtain ⟨y₀, hy₀, hy₀e⟩ := h1
        have hy₀' : y₀ = F₀.ι ((ψ s').symm z) := e.injective hy₀e
        rw [hy₀'] at hy₀
        obtain ⟨x', hx', hx'src⟩ := hΨsrc s _ hy₀
        rwa [← F₀.embedding.injective hx']
      obtain ⟨-, hlaw⟩ := s26d_a_transition hqhol hk0.le hk1 hD s s' hz' hws
      have hderiv : deriv (chartTransition (f s) (f s')) z = deriv (fun w => ψ s ((ψ s').symm w)) z := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [(ψ s').open_target.mem_nhds hz'] with v hv
        exact hτ v hv
      rw [hq''Q, hq''Q, Set.indicator_of_mem hz', hτ z hz', Set.indicator_of_mem ((ψ s).map_source hws), hderiv,
        zpow_zero, mul_one, zpow_two, ← pow_two]
      exact hlaw
    · obtain ⟨s, rfl⟩ := f.surjective y
      rw [hq''Q, htgt]
      exact ((differentiable_const _).mul (differentiable_pow _)).differentiableOn.congr
        fun w hw => Set.indicator_of_mem hw _
  have hT := s82td_teich_of_charts hqhol hq0 hk0.le hk1 hD f hchartv q'' hq''hol hq''Q
  exact ⟨⟨⟨O, Fy⟩, f, hT.qc⟩, q'', hq, hT⟩

/-- **[W4] Realization** (blueprint L32309): every non-zero admissible `q` and `0 < k < 1` are the data of an
admissible Teichmüller map marking a surface of type `(g, n, m)`. -/
theorem s82td_realize {g n m : ℕ} (hex : ¬ IsExceptionalType g n m) (F₀ : FiniteTypeStructure S₀ g n m)
    {q : S₀ → ℂ → ℂ} (hq : q ∈ admissibleQDInterior F₀) (hq0 : q ≠ 0) {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ∃ (A : MarkedFiniteTypeRS S₀ g n m) (q' : A.X.carrier → ℂ → ℂ), IsAdmissibleTeichmullerMap F₀ A.marking q q' k := by
  by_cases hm : m = 0
  · by_cases hn : n = 0
    · exact s82td_realize_closed F₀ hn hm hq hq0 hk0 hk1
    · exact s82td_realize_punctured hex F₀ hm hn hq hq0 hk0 hk1
  · exact s82td_realize_holes hex F₀ hm hq hq0 hk0 hk1

end LiZhongQC
