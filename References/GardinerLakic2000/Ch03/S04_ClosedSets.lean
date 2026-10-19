import References.GardinerLakic2000.Ch03.S03_PredualSpace

/-!
# Gardiner–Lakic 2000, Ch. 3 §3.4 Closed sets

Source `teichmuller.txt`, lines 2403–2611 (Chapter 3, §3.4).

* Definition 3 (`A(Λ)`, `Λ ⊆ ℂ̄` closed, l. 2406) — `aSpaceClosed`
* Theorem 6 (l. 2426) — `thm3_6`
* Definition 4 (`A(Ω)`, l. 2437) — `aSpaceOpen`
* Definition 5 (`Z(Ω)` and `Z(Λ)`, the dual spaces, l. 2448) — `zSpaceOpen`, `zSpaceClosed`
* Formula (3.16) (the pairing `(μ, φ) = ∬_ℂ μφ`, l. 2454) — exists: `LiZhongQC.beltramiPairing` (over the whole
  plane)
* Unlabelled (`Z(Λ) ≅ L∞(ℂ)/N` isometrically, l. 2460; used in §3.5) — `para3_4_z_quotient`
* Formula (3.17) (`φ_z(w) = −(1/π) z(z − 1)/(w(w − 1)(w − z))`, l. 2466) — `phiZ`
* Unlabelled (`φ_z ∈ A(Λ)` and `‖φ_z‖ = ρ_{01∞}(z)⁻¹` by Agard's formula, l. 2470; used in §3.6, §3.10) —
  `para3_4_phiZ_norm`
* Formula (3.18) (`V_μ(z) = (μ, φ_z)`, l. 2484; cited in Ch. 16) — exists: `LiZhongQC.normalizedCauchyTOn` (over the
  whole plane: V_μ is normalizedCauchyTOn applied to the plane and μ)
* Theorem 7 (l. 2511; cited in §3.5, §3.7) — `thm3_7_a`, `thm3_7_b`, `thm3_7_c`, `thm3_7_d`

Not items: the growth `O(|z|⁻⁴)` at `∞` (l. 2412–2424, U−); `A(Λ) = ℂ φ_z` for four points and the rational
decomposition left to the reader (l. 2462, 2472, U−); (3.19), (3.20) and the tangent-vector remarks (l. 2490–2509,
U−). Modelling: `Λ : Set ExtPlane` closed, `Ω` its complement; elements of `A(Λ)` are functions `φ : ℂ → ℂ`,
integrable over `ℂ`, holomorphic on `Ω ∩ ℂ`, and, when `∞ ∈ Ω`, holomorphic at `∞` in the chart `w = 1/z`
(`w ↦ φ(1/w)/w⁴` agrees near `0` with a function analytic at `0`) [reading of l. 2412–2422]. `A(Ω)` is the subset of
`A(Ωᶜ)` of functions vanishing on `Ωᶜ ∩ ℂ` (the book's direct sum over the components, l. 2439), so that
`A(Ω) ⊆ A(Λ)`. The norm is `∬_ℂ |φ|` (`LiZhongQC.phiArea φ univ`). The book's standing assumption "`Λ` has four or more
points, among them `0, 1, ∞`" (l. 2404, 2462) is a hypothesis where used.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (ExtPlane phiArea beltramiPairing normalizedCauchyTOn IsBeltramiCoeff dzbar)

/-- **Definition 3** (§3.4, l. 2406). `A(Λ)`: the integrable quadratic differentials of the extended plane holomorphic
on `Ω = ℂ̄ ∖ Λ` (including at `∞` when `∞ ∈ Ω`), with the norm `∬_ℂ |φ|`. -/
def aSpaceClosed (Λ : Set ExtPlane) : Set (ℂ → ℂ) :=
  {φ | Integrable φ ∧ DifferentiableOn ℂ φ {z : ℂ | (z : ExtPlane) ∉ Λ} ∧
    ((OnePoint.infty : ExtPlane) ∉ Λ →
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ ∀ᶠ w in 𝓝[≠] (0 : ℂ), g w = φ w⁻¹ / w ^ 4)}

/-- Helper for `thm3_6`: an `L¹(U)`-convergent sequence of holomorphic functions on an open `U` converges locally
uniformly on `U` (area mean value + uniform Cauchy) to a holomorphic `G`, and `G` is the `L¹`-limit a.e. (Fatou). -/
theorem gl3_l1_holo_limit {U : Set ℂ} (hU : IsOpen U) {f : ℕ → ℂ → ℂ} (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    {ψ : ℂ → ℂ} (hψ : AEStronglyMeasurable ψ (volume.restrict U))
    (hlim : Tendsto (fun n => ∫⁻ z in U, ENNReal.ofReal ‖f n z - ψ z‖) atTop (𝓝 0)) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧ (∀ z ∈ U, Tendsto (fun n => f n z) atTop (𝓝 (G z))) ∧
      ψ =ᵐ[volume.restrict U] G := by
  set J : ℕ → ℝ≥0∞ := fun n => ∫⁻ z in U, ENNReal.ofReal ‖f n z - ψ z‖ with hJ
  have hmeasn : ∀ n, AEMeasurable (fun z => ENNReal.ofReal ‖f n z - ψ z‖) (volume.restrict U) := fun n =>
    (((hf n).continuousOn.aestronglyMeasurable hU.measurableSet).sub hψ).norm.aemeasurable.ennreal_ofReal
  -- the area mean value bound for `fₙ − fₘ`
  have hmv : ∀ n m : ℕ, ∀ z : ℂ, ∀ s : ℝ, 0 < s → closedBall z s ⊆ U →
      ENNReal.ofReal (π * s ^ 2) * ENNReal.ofReal ‖f n z - f m z‖ ≤ J n + J m := by
    intro n m z s hs hsub
    refine (LiZhongQC.h36p_meanvalue ((hf n).sub (hf m)) hs hsub).trans ?_
    calc ∫⁻ y in ball z s, ENNReal.ofReal ‖(f n - f m) y‖ ≤ ∫⁻ y in U, ENNReal.ofReal ‖(f n - f m) y‖ :=
          lintegral_mono_set (ball_subset_closedBall.trans hsub)
      _ ≤ ∫⁻ y in U, (ENNReal.ofReal ‖f n y - ψ y‖ + ENNReal.ofReal ‖f m y - ψ y‖) := by
          refine lintegral_mono fun y => ?_
          rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := norm_sub_le (f n y - ψ y) (f m y - ψ y)
          rw [sub_sub_sub_cancel_right] at this
          simpa only [Pi.sub_apply] using this
      _ = J n + J m := lintegral_add_left' (hmeasn n) _
  -- uniformly Cauchy on small discs
  have hcauchy : ∀ x ∈ U, ∃ s > 0, ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∀ y ∈ ball x s, ‖f n y - f m y‖ < ε := by
    intro x hx
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
    refine ⟨r / 4, by positivity, fun ε hε => ?_⟩
    have hc : 0 < π * (r / 4) ^ 2 * ε / 2 := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hc)))
    refine ⟨N, fun n hn m hm y hy => ?_⟩
    have hsub : closedBall y (r / 4) ⊆ U := by
      intro u hu
      refine hrU ?_
      rw [mem_ball] at hy ⊢
      rw [mem_closedBall] at hu
      have := dist_triangle u y x
      linarith
    have h1 := hmv n m y (r / 4) (by positivity) hsub
    have h2 : J n + J m < ENNReal.ofReal (π * (r / 4) ^ 2 * ε / 2) + ENNReal.ofReal (π * (r / 4) ^ 2 * ε / 2) :=
      ENNReal.add_lt_add (hN n hn) (hN m hm)
    rw [← ENNReal.ofReal_add hc.le hc.le] at h2
    rw [← ENNReal.ofReal_mul (by positivity)] at h1
    have h3 := h1.trans_lt h2
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h3
    have hpos : 0 < π * (r / 4) ^ 2 := by positivity
    nlinarith
  have hcs : ∀ z ∈ U, CauchySeq fun n => f n z := by
    intro z hz
    obtain ⟨s, hs, hC⟩ := hcauchy z hz
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    exact ⟨N, fun m hm n hn => by rw [dist_eq_norm]; exact hN m hm n hn z (mem_ball_self hs)⟩
  set G : ℂ → ℂ := fun z => limUnder atTop fun n => f n z with hG
  have hGlim : ∀ z ∈ U, Tendsto (fun n => f n z) atTop (𝓝 (G z)) := fun z hz => (hcs z hz).tendsto_limUnder
  have hloc : TendstoLocallyUniformlyOn f G atTop U := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε x hx
    obtain ⟨s, hs, hC⟩ := hcauchy x hx
    obtain ⟨N, hN⟩ := hC (ε / 2) (half_pos hε)
    refine ⟨U ∩ ball x s, inter_mem_nhdsWithin U (ball_mem_nhds x hs), eventually_atTop.2 ⟨N, fun n hn y hy => ?_⟩⟩
    have h1 : Tendsto (fun m => ‖f n y - f m y‖) atTop (𝓝 ‖f n y - G y‖) :=
      ((continuous_const.sub continuous_id).norm.tendsto (G y)).comp (hGlim y hy.1)
    have h2 : ‖f n y - G y‖ ≤ ε / 2 :=
      le_of_tendsto h1 (eventually_atTop.2 ⟨N, fun m hm => (hN n hn m hm y hy.2).le⟩)
    rw [dist_comm, dist_eq_norm]
    linarith
  have hGd : DifferentiableOn ℂ G U := hloc.differentiableOn (Eventually.of_forall hf) hU
  -- `G = ψ` a.e. on `U` (Fatou)
  have hfatou := lintegral_liminf_le' (u := atTop) hmeasn
  have hpt : ∀ᵐ z ∂(volume.restrict U),
      liminf (fun n => ENNReal.ofReal ‖f n z - ψ z‖) atTop = ENNReal.ofReal ‖G z - ψ z‖ := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    exact (((ENNReal.continuous_ofReal.comp (continuous_id.sub continuous_const).norm).tendsto (G z)).comp
      (hGlim z hz)).liminf_eq
  have hmeasG : AEMeasurable (fun z => ENNReal.ofReal ‖G z - ψ z‖) (volume.restrict U) :=
    ((hGd.continuousOn.aestronglyMeasurable hU.measurableSet).sub hψ).norm.aemeasurable.ennreal_ofReal
  have h0 : ∫⁻ z in U, ENNReal.ofReal ‖G z - ψ z‖ = 0 := by
    rw [← lintegral_congr_ae hpt]
    refine le_antisymm (hfatou.trans ?_) zero_le
    rw [hlim.liminf_eq]
  refine ⟨G, hGd, hGlim, ?_⟩
  filter_upwards [(lintegral_eq_zero_iff' hmeasG).1 h0] with z hz
  have : ‖G z - ψ z‖ = 0 := le_antisymm (ENNReal.ofReal_eq_zero.1 hz) (norm_nonneg _)
  exact (sub_eq_zero.1 (norm_eq_zero.1 this)).symm

/-- Helper for `thm3_6`: `z ↦ 1/z` maps the punctured disc `0 < |w| < 1/R` conformally onto `|z| > R`. -/
theorem gl3_inv_conformal {R : ℝ} (hR : 0 < R) :
    LiZhongQC.IsConformalOnto (fun w : ℂ => w⁻¹) (ball 0 R⁻¹ \ {0}) {z : ℂ | R < ‖z‖} := by
  refine ⟨fun w hw => (differentiableAt_inv hw.2).differentiableWithinAt, inv_injective.injOn, ?_⟩
  ext z
  constructor
  · rintro ⟨w, ⟨hw, hw0⟩, rfl⟩
    have hw0' : w ≠ 0 := hw0
    rw [mem_ball_zero_iff] at hw
    show R < ‖w⁻¹‖
    rw [norm_inv]
    exact (lt_inv_comm₀ hR (norm_pos_iff.2 hw0')).2 hw
  · intro hz
    have hz' : R < ‖z‖ := hz
    have hz0 : z ≠ 0 := norm_pos_iff.1 (hR.trans hz')
    refine ⟨z⁻¹, ⟨?_, inv_ne_zero hz0⟩, inv_inv z⟩
    rw [mem_ball_zero_iff, norm_inv]
    exact inv_strictAnti₀ hR hz'

/-- **Theorem 6** (§3.4, l. 2426). `A(Λ)` is a Banach space: it is closed in `L¹(ℂ)` (an `L¹`-limit of elements of
`A(Λ)` agrees a.e. with an element of `A(Λ)`). -/
theorem thm3_6 {Λ : Set ExtPlane} (hΛ : IsClosed Λ) {φ : ℕ → ℂ → ℂ} (hφ : ∀ n, φ n ∈ aSpaceClosed Λ)
    {ψ : ℂ → ℂ} (hψ : Integrable ψ) (hlim : Tendsto (fun n => phiArea (φ n - ψ) univ) atTop (𝓝 0)) :
    ∃ φ₀ ∈ aSpaceClosed Λ, φ₀ =ᵐ[volume] ψ := by
  classical
  -- a strongly measurable version of `ψ`
  set ψm := hψ.1.mk ψ with hψm
  have hψm_meas : StronglyMeasurable ψm := hψ.1.stronglyMeasurable_mk
  have hψeq : ψ =ᵐ[volume] ψm := hψ.1.ae_eq_mk
  set Ω : Set ℂ := {z : ℂ | (z : ExtPlane) ∉ Λ} with hΩdef
  have hΩ : IsOpen Ω := hΛ.isOpen_compl.preimage OnePoint.continuous_coe
  -- the `L¹` distance to `ψm` over a set is at most `phiArea (φₙ − ψ)`
  have hle : ∀ n (S : Set ℂ), ∫⁻ z in S, ENNReal.ofReal ‖φ n z - ψm z‖ ≤ phiArea (φ n - ψ) univ := by
    intro n S
    rw [phiArea, Measure.restrict_univ]
    refine (setLIntegral_le_lintegral S _).trans (le_of_eq (lintegral_congr_ae ?_))
    filter_upwards [hψeq] with z hz
    rw [Pi.sub_apply, hz]
  have hlimS : ∀ S : Set ℂ, Tendsto (fun n => ∫⁻ z in S, ENNReal.ofReal ‖φ n z - ψm z‖) atTop (𝓝 0) :=
    fun S => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le)
      (fun n => hle n S)
  obtain ⟨G, hGd, hGlim, hGae⟩ := gl3_l1_holo_limit hΩ (fun n => (hφ n).2.1)
    hψm_meas.aestronglyMeasurable.restrict (hlimS Ω)
  set φ₀ : ℂ → ℂ := Ω.piecewise G ψm with hφ₀
  have hφ₀Ω : ∀ z ∈ Ω, φ₀ z = G z := fun z hz => piecewise_eq_of_mem _ _ _ hz
  have hφ₀ae : φ₀ =ᵐ[volume] ψ := by
    have h1 := (ae_restrict_iff' hΩ.measurableSet).1 hGae
    filter_upwards [h1, hψeq] with z hz hzψ
    rw [hzψ]
    by_cases hzΩ : z ∈ Ω
    · rw [hφ₀Ω z hzΩ, hz hzΩ]
    · rw [hφ₀, piecewise_eq_of_notMem _ _ _ hzΩ]
  refine ⟨φ₀, ⟨hψ.congr hφ₀ae.symm, hGd.congr hφ₀Ω, fun hinf => ?_⟩, hφ₀ae⟩
  -- the condition at `∞`: a neighbourhood `|z| > R` of `∞` lies in `Ω`
  obtain ⟨R, hR, hRΩ⟩ : ∃ R > 0, ∀ z : ℂ, R < ‖z‖ → z ∈ Ω := by
    have hnhds : Λᶜ ∈ 𝓝 (OnePoint.infty : ExtPlane) := hΛ.isOpen_compl.mem_nhds hinf
    obtain ⟨K, ⟨-, hKk⟩, hKsub⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.1 hnhds
    obtain ⟨R₀, hR₀⟩ := hKk.isBounded.subset_closedBall 0
    refine ⟨max R₀ 1, by positivity, fun z hz => ?_⟩
    have hzK : z ∉ K := fun h => by
      have := mem_closedBall_zero_iff.1 (hR₀ h)
      have := le_max_left R₀ 1
      linarith
    exact hKsub (Or.inl ⟨z, hzK, rfl⟩)
  choose g hg hgeq using fun n => (hφ n).2.2 hinf
  set r := R⁻¹ with hr
  have hr0 : 0 < r := inv_pos.2 hR
  have hinvΩ : ∀ w : ℂ, w ∈ ball (0 : ℂ) r → w ≠ 0 → w⁻¹ ∈ Ω := by
    intro w hw hw0
    refine hRΩ _ ?_
    rw [norm_inv]
    exact (lt_inv_comm₀ hR (norm_pos_iff.2 hw0)).2 (mem_ball_zero_iff.1 hw)
  -- the functions `fₙ(w) = φₙ(1/w)/w⁴`, holomorphic in `|w| < 1/R` after filling in `w = 0`
  set f' : ℕ → ℂ → ℂ := fun n w => if w = 0 then g n 0 else φ n w⁻¹ / w ^ 4 with hf'
  have hf'd : ∀ n, DifferentiableOn ℂ (f' n) (ball 0 r) := by
    intro n w hw
    by_cases hw0 : w = 0
    · subst hw0
      have hev : f' n =ᶠ[𝓝 0] g n := by
        have h := eventually_nhdsWithin_iff.1 (hgeq n)
        filter_upwards [h] with u hu
        by_cases hu0 : u = 0
        · simp [hf', hu0]
        · simp only [hf', hu0, ite_false]
          exact (hu hu0).symm
      exact ((hg n).differentiableAt.congr_of_eventuallyEq hev).differentiableWithinAt
    · have hev : f' n =ᶠ[𝓝 w] fun u => φ n u⁻¹ / u ^ 4 := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hw0] with u hu
        simp only [hf', show u ≠ 0 from hu, ite_false]
      have hφd : DifferentiableAt ℂ (φ n) w⁻¹ :=
        ((hφ n).2.1 _ (hinvΩ w hw hw0)).differentiableAt (hΩ.mem_nhds (hinvΩ w hw hw0))
      refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
      exact (hφd.comp w (differentiableAt_inv hw0)).div (differentiableAt_pow 4) (pow_ne_zero 4 hw0)
  set ψ' : ℂ → ℂ := fun w => ψm w⁻¹ / w ^ 4 with hψ'
  have hψ'm : Measurable ψ' := (hψm_meas.measurable.comp measurable_inv).div (measurable_id.pow_const 4)
  -- `∫_{|w|<1/R} |fₙ − ψ'| = ∫_{|z|>R} |φₙ − ψm| → 0` (change of variables `z = 1/w`)
  have hP : IsOpen (ball (0 : ℂ) r \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hcv : ∀ n, ∫⁻ w in ball (0 : ℂ) r, ENNReal.ofReal ‖f' n w - ψ' w‖ =
      ∫⁻ z in {z : ℂ | R < ‖z‖}, ENNReal.ofReal ‖φ n z - ψm z‖ := by
    intro n
    rw [LiZhongQC.lintegral_image_conformal hP (gl3_inv_conformal hR) (fun z => ENNReal.ofReal ‖φ n z - ψm z‖)]
    have hae : ball (0 : ℂ) r \ {0} =ᵐ[volume] ball (0 : ℂ) r := sdiff_null_ae_eq_self (measure_singleton 0)
    rw [← setLIntegral_congr hae]
    refine setLIntegral_congr_fun hP.measurableSet fun w hw => ?_
    have hw0 : w ≠ 0 := hw.2
    simp only [hf', hψ', hw0, ite_false, deriv_inv]
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity), ← sub_div,
      norm_div, norm_neg, norm_inv, norm_pow, norm_pow]
    congr 1
    have : 0 < ‖w‖ := norm_pos_iff.2 hw0
    field_simp
  have hlim' : Tendsto (fun n => ∫⁻ w in ball (0 : ℂ) r, ENNReal.ofReal ‖f' n w - ψ' w‖) atTop (𝓝 0) := by
    simp only [hcv]
    exact hlimS _
  obtain ⟨G', hG'd, hG'lim, -⟩ := gl3_l1_holo_limit isOpen_ball hf'd hψ'm.aestronglyMeasurable hlim'
  refine ⟨G', hG'd.analyticAt (ball_mem_nhds 0 hr0), ?_⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [ball_mem_nhds (0 : ℂ) hr0] with w hw hw0
  have hw0' : w ≠ 0 := hw0
  have h1 := hG'lim w hw
  have h2 : Tendsto (fun n => f' n w) atTop (𝓝 (G w⁻¹ / w ^ 4)) := by
    simp only [hf', hw0', ite_false]
    exact (hGlim _ (hinvΩ w hw hw0')).div_const _
  rw [tendsto_nhds_unique h1 h2, hφ₀Ω _ (hinvΩ w hw hw0')]

/-- **Definition 4** (§3.4, l. 2437). `A(Ω) = ⊕_j A(Ω_j)` for an open `Ω ⊆ ℂ̄`: the integrable holomorphic quadratic
differentials on `Ω` (extended by `0` off `Ω`), with the norm `∬_Ω |φ|`. -/
def aSpaceOpen (Ω : Set ExtPlane) : Set (ℂ → ℂ) :=
  {φ | φ ∈ aSpaceClosed Ωᶜ ∧ ∀ z : ℂ, (z : ExtPlane) ∉ Ω → φ z = 0}

/-- **Definition 5** (§3.4, l. 2448). `Z(Λ)`, the dual space of `A(Λ)`. -/
def zSpaceClosed (Λ : Set ExtPlane) : Set ((ℂ → ℂ) → ℂ) :=
  {V | IsBoundedFunctionalOn (aSpaceClosed Λ) (fun φ => phiArea φ univ) V}

/-- **Definition 5** (§3.4, l. 2448). `Z(Ω)`, the dual space of `A(Ω)`. -/
def zSpaceOpen (Ω : Set ExtPlane) : Set ((ℂ → ℂ) → ℂ) :=
  {V | IsBoundedFunctionalOn (aSpaceOpen Ω) (fun φ => phiArea φ univ) V}

/-- Helper for `para3_4_z_quotient` (§3.4): `A(Λ)` is closed under the linear operations (integrability,
holomorphy off `Λ` and the condition at `∞` are all linear). -/
theorem gl3_zq_closed (Λ : Set ExtPlane) :
    (0 : ℂ → ℂ) ∈ aSpaceClosed Λ ∧ (∀ φ ∈ aSpaceClosed Λ, ∀ ψ ∈ aSpaceClosed Λ, φ + ψ ∈ aSpaceClosed Λ) ∧
      ∀ c : ℂ, ∀ φ ∈ aSpaceClosed Λ, c • φ ∈ aSpaceClosed Λ := by
  refine ⟨⟨integrable_zero _ _ _, differentiableOn_const 0, fun _ => ⟨0, analyticAt_const,
    Eventually.of_forall fun w => by simp⟩⟩, ?_, ?_⟩
  · rintro φ ⟨hφi, hφd, hφinf⟩ ψ ⟨hψi, hψd, hψinf⟩
    refine ⟨hφi.add hψi, hφd.add hψd, fun h => ?_⟩
    obtain ⟨g, hg, hge⟩ := hφinf h
    obtain ⟨g', hg', hge'⟩ := hψinf h
    refine ⟨fun w => g w + g' w, hg.add hg', ?_⟩
    filter_upwards [hge, hge'] with w h1 h2
    simp only [Pi.add_apply, h1, h2, add_div]
  · rintro c φ ⟨hφi, hφd, hφinf⟩
    refine ⟨hφi.smul c, hφd.const_smul c, fun h => ?_⟩
    obtain ⟨g, hg, hge⟩ := hφinf h
    refine ⟨fun w => c * g w, analyticAt_const.mul hg, ?_⟩
    filter_upwards [hge] with w h1
    simp only [Pi.smul_apply, smul_eq_mul, h1, mul_div_assoc]

/-- **Unlabelled** (§3.4, l. 2460). `Z(Λ)` is isometrically isomorphic to `L∞(ℂ)/N`, `N` the Beltrami differentials
orthogonal to `A(Λ)`: every `V ∈ Z(Λ)` is `φ ↦ ∬ μφ` for some bounded `μ` with `‖μ‖∞ = ‖V‖`, and no representative
has smaller norm. -/
theorem para3_4_z_quotient {Λ : Set ExtPlane} (hΛ : IsClosed Λ) {V : (ℂ → ℂ) → ℂ} (hV : V ∈ zSpaceClosed Λ) :
    ∃ μ : ℂ → ℂ, (∃ k : ℝ, IsBeltramiCoeff μ univ k) ∧ (∀ φ ∈ aSpaceClosed Λ, V φ = beltramiPairing univ μ φ) ∧
      eLpNorm μ ⊤ volume = ENNReal.ofReal (dualNormOn (aSpaceClosed Λ) (fun φ => phiArea φ univ) V) ∧
      ∀ ν : ℂ → ℂ, (∃ k : ℝ, IsBeltramiCoeff ν univ k) → (∀ φ ∈ aSpaceClosed Λ, V φ = beltramiPairing univ ν φ) →
        ENNReal.ofReal (dualNormOn (aSpaceClosed Λ) (fun φ => phiArea φ univ) V) ≤ eLpNorm ν ⊤ volume := by
  -- Hahn–Banach on `L¹(ℂ)`: the representing `ν` has `‖ν‖∞ ≤ ‖V‖`, and every representative has `‖V‖ ≤ ‖·‖∞`
  have _hΛ := hΛ
  obtain ⟨h0, hadd, hsmul⟩ := gl3_zq_closed Λ
  obtain ⟨ν, hνm, hνb, hνrep⟩ := gl3_dual_repr MeasurableSet.univ (fun φ hφ => hφ.1.integrableOn) h0 hadd hsmul hV
  have hrep : ∀ φ ∈ aSpaceClosed Λ, V φ = beltramiPairing univ ν φ := hνrep
  refine ⟨ν, ⟨_, hνm, hνb⟩, hrep, le_antisymm ?_ ?_, fun ν' _ hν' => ?_⟩
  · rw [Measure.restrict_univ] at hνb hνm
    rw [eLpNorm_exponent_top hνm]
    exact eLpNormEssSup_le_of_ae_bound hνb
  · have h := gl3_dual_le (subset_univ univ) (ν := ν) hrep
    rwa [Measure.restrict_univ] at h
  · have h := gl3_dual_le (subset_univ univ) (ν := ν') hν'
    rwa [Measure.restrict_univ] at h

/-- **Formula (3.17)** (§3.4, l. 2466). `φ_z(w) = −(1/π) z(z − 1)/(w(w − 1)(w − z))`, the quadratic differential with
simple poles at `0, 1, z` (and `∞`). -/
def phiZ (z w : ℂ) : ℂ := -(1 / π : ℂ) * (z * (z - 1) / (w * (w - 1) * (w - z)))

/-- Helper for `lemma3_1` (Schwarz–Pick at the centre, for maps into `ℍ`): a holomorphic `Ψ : Δ → ℍ` has
`|Ψ′(0)| ≤ 2 Im Ψ(0)` (Schwarz's lemma for `(Ψ − Ψ(0))/(Ψ − conj Ψ(0))`). -/
theorem gl3_schwarz_H {Ψ : ℂ → ℂ} (hΨ : DifferentiableOn ℂ Ψ (ball 0 1))
    (hΨH : ∀ t ∈ ball (0 : ℂ) 1, 0 < (Ψ t).im) :
    ‖deriv Ψ 0‖ ≤ 2 * (Ψ 0).im := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hp0 : 0 < (Ψ 0).im := hΨH 0 h0
  have hne : ∀ t ∈ ball (0 : ℂ) 1, Ψ t - conj (Ψ 0) ≠ 0 := by
    intro t ht h
    have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith [hΨH t ht]
  have hfd : DifferentiableOn ℂ (fun t => (Ψ t - Ψ 0) / (Ψ t - conj (Ψ 0))) (ball 0 1) := fun t ht =>
    ((hΨ t ht).sub_const _).div ((hΨ t ht).sub_const _) (hne t ht)
  have hmaps : MapsTo (fun t => (Ψ t - Ψ 0) / (Ψ t - conj (Ψ 0))) (ball 0 1)
      (closedBall ((fun t => (Ψ t - Ψ 0) / (Ψ t - conj (Ψ 0))) 0) 1) := by
    intro t ht
    rw [mem_closedBall]
    beta_reduce
    rw [sub_self, zero_div, dist_zero_right, norm_div]
    exact div_le_one_of_le₀ (LiZhongQC.td_norm_sub_le_norm_sub_conj (hΨH t ht) hp0) (norm_nonneg _)
  have hS := Complex.norm_deriv_le_one_of_mapsTo_ball hfd hmaps one_pos
  have hΨd : DifferentiableAt ℂ Ψ 0 := (hΨ 0 h0).differentiableAt (isOpen_ball.mem_nhds h0)
  have hden : Ψ 0 - conj (Ψ 0) ≠ 0 := hne 0 h0
  have h1 := (hΨd.hasDerivAt.sub_const (Ψ 0)).div (hΨd.hasDerivAt.sub_const (conj (Ψ 0))) hden
  have h1' : HasDerivAt (fun t => (Ψ t - Ψ 0) / (Ψ t - conj (Ψ 0))) _ 0 := h1
  rw [h1'.deriv, sub_self, zero_mul, sub_zero, sq, mul_div_mul_right _ _ hden, norm_div, Complex.sub_conj,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos two_pos hp0),
    div_le_one (mul_pos two_pos hp0)] at hS
  exact hS

/-- Helper for `lemma3_1` (Landau): the Poincaré density of `ℂ ∖ {0, 1}` (the `sInf` of `1/|g′(0)|`) is positive.
Every admissible `g` lifts through the covering `φ : ℍ → ℂ ∖ {0, 1}` (`td_lift_holomorphic`) to `Ψ` with a fixed
`Ψ(0) = τ₀ ∈ φ⁻¹(w)`, so `|g′(0)| = |φ′(τ₀)||Ψ′(0)| ≤ 2 Im τ₀ |φ′(τ₀)|`. -/
theorem gl3_density_pos {w : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) :
    0 < poincareDensityGL {w : ℂ | w ≠ 0 ∧ w ≠ 1} w := by
  obtain ⟨τ₀, hτ₀⟩ := LiZhongQC.mcov_surj_modularPhi ⟨hw0, hw1⟩
  have hτ : 0 < (τ₀ : ℂ).im := τ₀.im_pos
  have hd0 := LiZhongQC.s15v_deriv_ne_zero hτ
  set L := 2 * (τ₀ : ℂ).im * ‖deriv LiZhongQC.modularPhi τ₀‖ with hL
  have hL0 : 0 < L := by
    have := norm_pos_iff.2 hd0
    positivity
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hbound : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g LiZhongQC.unitDisc →
      MapsTo g LiZhongQC.unitDisc {w : ℂ | w ≠ 0 ∧ w ≠ 1} → g 0 = w → ‖deriv g 0‖ ≤ L := by
    intro g hg hmaps hg0
    obtain ⟨Ψ, hΨd, hΨ0, hΨ⟩ := LiZhongQC.td_lift_holomorphic LiZhongQC.modularPhi_covering.2 hg
      (fun t ht => hmaps ht) (a₀ := τ₀) (by rw [hτ₀, hg0])
    have hSP := gl3_schwarz_H hΨd fun t ht => (hΨ t ht).1
    rw [hΨ0] at hSP
    have heq : g =ᶠ[𝓝 0] LiZhongQC.modularPhi ∘ Ψ := by
      filter_upwards [isOpen_ball.mem_nhds h0] with t ht
      exact ((hΨ t ht).2).symm
    have hΨd0 : DifferentiableAt ℂ Ψ 0 := (hΨd 0 h0).differentiableAt (isOpen_ball.mem_nhds h0)
    have hφd : DifferentiableAt ℂ LiZhongQC.modularPhi (Ψ 0) := by
      rw [hΨ0]
      exact (LiZhongQC.mphi_differentiableOn_modularPhi_upperHalf _ hτ).differentiableAt
        (LiZhongQC.isOpen_upperHalf.mem_nhds hτ)
    rw [heq.deriv_eq, deriv_comp _ hφd hΨd0, hΨ0, norm_mul, hL]
    calc ‖deriv LiZhongQC.modularPhi τ₀‖ * ‖deriv Ψ 0‖ ≤ ‖deriv LiZhongQC.modularPhi τ₀‖ * (2 * (τ₀ : ℂ).im) :=
          mul_le_mul_of_nonneg_left hSP (norm_nonneg _)
      _ = 2 * (τ₀ : ℂ).im * ‖deriv LiZhongQC.modularPhi τ₀‖ := by ring
  -- the admissible set is nonempty: `t ↦ w + ε t` with `ε = min |w| |w − 1| / 2`
  set ε : ℝ := min ‖w‖ ‖w - 1‖ / 2 with hε
  have hε0 : 0 < ε := by
    have := norm_pos_iff.2 hw0
    have := norm_pos_iff.2 (sub_ne_zero.2 hw1)
    positivity
  have hεw : ε < ‖w‖ := by have := min_le_left ‖w‖ ‖w - 1‖; have := norm_pos_iff.2 hw0; linarith
  have hεw1 : ε < ‖w - 1‖ := by
    have := min_le_right ‖w‖ ‖w - 1‖; have := norm_pos_iff.2 (sub_ne_zero.2 hw1); linarith
  have hgd : HasDerivAt (fun t : ℂ => w + (ε : ℂ) * t) ((ε : ℂ) * 1) 0 :=
    ((hasDerivAt_id (0 : ℂ)).const_mul (ε : ℂ)).const_add w
  have hne : {r : ℝ | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g LiZhongQC.unitDisc ∧
      MapsTo g LiZhongQC.unitDisc {w : ℂ | w ≠ 0 ∧ w ≠ 1} ∧ g 0 = w ∧ deriv g 0 ≠ 0 ∧
        r = 1 / ‖deriv g 0‖}.Nonempty := by
    refine ⟨_, fun t : ℂ => w + (ε : ℂ) * t, ?_, ?_, by simp, ?_, rfl⟩
    · exact ((differentiable_id.const_mul (ε : ℂ)).const_add w).differentiableOn
    · intro t ht
      simp only [mem_ofPred_eq]
      have ht' : ‖t‖ < 1 := mem_ball_zero_iff.1 ht
      have hεt : ‖(ε : ℂ) * t‖ < ε := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
        exact mul_lt_of_lt_one_right hε0 ht'
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have : w = -((ε : ℂ) * t) := by linear_combination h
        rw [this, norm_neg] at hεw
        linarith
      · have : w - 1 = -((ε : ℂ) * t) := by linear_combination h
        rw [this, norm_neg] at hεw1
        linarith
    · rw [hgd.deriv, mul_one]
      exact Complex.ofReal_ne_zero.2 hε0.ne'
  unfold poincareDensityGL
  refine lt_of_lt_of_le (one_div_pos.2 hL0) (le_csInf hne ?_)
  rintro r ⟨g, hg, hmaps, hg0, hd, rfl⟩
  exact one_div_le_one_div_of_le (norm_pos_iff.2 hd) (hbound g hg hmaps hg0)

/-- Helper for `para3_4_phiZ_norm` and `thm3_7_b/c`: `ofReal |w|⁻¹ ≤ |w|^{-1}` in `ℝ≥0∞` (equality off `0`). -/
theorem gl3_ofReal_inv_le (w : ℂ) : ENNReal.ofReal ‖w‖⁻¹ ≤ ‖w‖ₑ ^ (-1 : ℝ) := by
  by_cases hw : w = 0
  · simp [hw]
  refine le_of_eq ?_
  rw [ENNReal.rpow_neg_one, ← ofReal_norm, ENNReal.ofReal_inv_of_pos (norm_pos_iff.2 hw)]

/-- Helper for `para3_4_phiZ_norm` and `thm3_7_b/c`: `ofReal |w|⁻³ ≤ |w|^{-3}` in `ℝ≥0∞` (equality off `0`). -/
theorem gl3_ofReal_inv_pow_three_le (w : ℂ) : ENNReal.ofReal (‖w‖⁻¹ ^ 3) ≤ ‖w‖ₑ ^ (-3 : ℝ) := by
  by_cases hw : w = 0
  · simp [hw]
  refine le_of_eq ?_
  rw [ENNReal.ofReal_pow (inv_nonneg.2 (norm_nonneg _)), ENNReal.ofReal_inv_of_pos (norm_pos_iff.2 hw),
    ofReal_norm, ENNReal.rpow_neg, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
    ENNReal.inv_pow]

/-- Helper for `para3_4_phiZ_norm` and `thm3_7_b/c`: `1/(|ζ||ζ − 1|) ≤ 1/|ζ| + 1/|ζ − 1|` (as `|ζ| + |ζ − 1| ≥ 1`),
in `ℝ≥0∞`. -/
theorem gl3_ofReal_inv_mul_le (ζ : ℂ) :
    ENNReal.ofReal (‖ζ‖ * ‖ζ - 1‖)⁻¹ ≤ ‖ζ - 0‖ₑ ^ (-(1 : ℝ)) + ‖ζ - 1‖ₑ ^ (-(1 : ℝ)) := by
  by_cases h0 : ζ = 0
  · simp [h0]
  by_cases h1 : ζ - 1 = 0
  · rw [h1, norm_zero, mul_zero, inv_zero, ENNReal.ofReal_zero]
    exact zero_le
  have ha : 0 < ‖ζ‖ := norm_pos_iff.2 h0
  have hb : 0 < ‖ζ - 1‖ := norm_pos_iff.2 h1
  have h1' : 1 ≤ ‖ζ‖ + ‖ζ - 1‖ := by
    have := norm_sub_le ζ (ζ - 1)
    rw [sub_sub_cancel, norm_one] at this
    linarith
  have hsplit : (‖ζ‖ * ‖ζ - 1‖)⁻¹ ≤ ‖ζ‖⁻¹ + ‖ζ - 1‖⁻¹ := by
    rw [inv_add_inv ha.ne' hb.ne', inv_eq_one_div]
    exact div_le_div_of_nonneg_right h1' (by positivity)
  calc ENNReal.ofReal (‖ζ‖ * ‖ζ - 1‖)⁻¹ ≤ ENNReal.ofReal (‖ζ‖⁻¹ + ‖ζ - 1‖⁻¹) := ENNReal.ofReal_le_ofReal hsplit
    _ = ENNReal.ofReal ‖ζ - 0‖⁻¹ + ENNReal.ofReal ‖ζ - 1‖⁻¹ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), sub_zero]
    _ ≤ ‖ζ - 0‖ₑ ^ (-(1 : ℝ)) + ‖ζ - 1‖ₑ ^ (-(1 : ℝ)) := add_le_add (gl3_ofReal_inv_le _) (gl3_ofReal_inv_le _)

/-- Helper for `para3_4_phiZ_norm` and `thm3_7_b/c`: `∬_{|ζ| ≤ ρ} |ζ − c|⁻¹ < ∞` (LZ
`lintegral_closedBall_enorm_sub_rpow_neg_le`). -/
theorem gl3_closedBall_fin {ρ : ℝ} (hρ : 0 < ρ) (c : ℂ) :
    ∫⁻ ζ in closedBall (0 : ℂ) ρ, ‖ζ - c‖ₑ ^ (-(1 : ℝ)) < ⊤ :=
  (LiZhongQC.lintegral_closedBall_enorm_sub_rpow_neg_le one_pos hρ c).trans_lt
    (ENNReal.add_lt_top.2 ⟨(LiZhongQC.lintegral_ball_enorm_rpow_neg_ne_top zero_le_one (by norm_num) ρ).lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top⟩)

/-- Helper for `para3_4_phiZ_norm` and `thm3_7_c`: partial fractions
`w(w − 1)/(ζ(ζ − 1)(ζ − w)) = (w − 1)/ζ − w/(ζ − 1) + 1/(ζ − w)` bound the normalized Cauchy kernel by
`|w − 1|/|ζ| + |w|/|ζ − 1| + 1/|ζ − w|` (at the poles the left side is `0`). -/
theorem gl3_kernel_pf (w ζ : ℂ) :
    ‖w * (w - 1) / (ζ * (ζ - 1) * (ζ - w))‖ ≤ ‖w - 1‖ * ‖ζ‖⁻¹ + ‖w‖ * ‖ζ - 1‖⁻¹ + ‖ζ - w‖⁻¹ := by
  by_cases hD : ζ * (ζ - 1) * (ζ - w) = 0
  · rw [hD, div_zero, norm_zero]
    positivity
  have h0 : ζ ≠ 0 := fun h => hD (by rw [h]; ring)
  have h1 : ζ - 1 ≠ 0 := fun h => hD (by rw [h]; ring)
  have hw : ζ - w ≠ 0 := fun h => hD (by rw [h]; ring)
  have e : w * (w - 1) / (ζ * (ζ - 1) * (ζ - w)) = (w - 1) / ζ - w / (ζ - 1) + 1 / (ζ - w) := by
    field_simp
    ring
  rw [e]
  calc ‖(w - 1) / ζ - w / (ζ - 1) + 1 / (ζ - w)‖ ≤ ‖(w - 1) / ζ‖ + ‖w / (ζ - 1)‖ + ‖1 / (ζ - w)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ = ‖w - 1‖ * ‖ζ‖⁻¹ + ‖w‖ * ‖ζ - 1‖⁻¹ + ‖ζ - w‖⁻¹ := by
        simp only [norm_mul, norm_inv, div_eq_mul_inv, one_mul]

/-- Helper for `para3_4_phiZ_norm` and `thm3_7_c`: the normalized Cauchy kernel `w(w − 1)/(ζ(ζ − 1)(ζ − w))` is
integrable in `ζ` (near the poles by `gl3_kernel_pf`, for `|ζ| > 2|w| + 2` it is `≤ 4|w||w − 1|/|ζ|³`). -/
theorem gl3_kernel_lintegral_lt_top (w : ℂ) :
    ∫⁻ ζ, ENNReal.ofReal ‖w * (w - 1) / (ζ * (ζ - 1) * (ζ - w))‖ < ⊤ := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 2 * ‖w‖ + 2 := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  set f₁ : ℂ → ℝ≥0∞ := (closedBall (0 : ℂ) ρ).indicator (fun ζ => ENNReal.ofReal ‖w - 1‖ * ‖ζ - 0‖ₑ ^ (-(1 : ℝ)) +
    ENNReal.ofReal ‖w‖ * ‖ζ - 1‖ₑ ^ (-(1 : ℝ)) + ‖ζ - w‖ₑ ^ (-(1 : ℝ))) with hf₁
  set f₂ : ℂ → ℝ≥0∞ := {ζ : ℂ | ρ < ‖ζ‖}.indicator
    (fun ζ => ENNReal.ofReal (4 * (‖w‖ * ‖w - 1‖)) * ‖ζ‖ₑ ^ (-(3 : ℝ))) with hf₂
  have hm₂ : MeasurableSet {ζ : ℂ | ρ < ‖ζ‖} := measurableSet_lt measurable_const measurable_norm
  have hmeas₀ : Measurable fun ζ : ℂ => ENNReal.ofReal ‖w - 1‖ * ‖ζ - 0‖ₑ ^ (-(1 : ℝ)) +
      ENNReal.ofReal ‖w‖ * ‖ζ - 1‖ₑ ^ (-(1 : ℝ)) :=
    (measurable_const.mul ((measurable_id'.sub_const 0).enorm.pow_const _)).add
      (measurable_const.mul ((measurable_id'.sub_const 1).enorm.pow_const _))
  have hmeas₁ : Measurable f₁ :=
    (hmeas₀.add ((measurable_id'.sub_const w).enorm.pow_const _)).indicator measurableSet_closedBall
  have hpt : ∀ ζ, ENNReal.ofReal ‖w * (w - 1) / (ζ * (ζ - 1) * (ζ - w))‖ ≤ f₁ ζ + f₂ ζ := by
    intro ζ
    by_cases hζ : ζ ∈ closedBall (0 : ℂ) ρ
    · refine le_trans ?_ le_self_add
      rw [hf₁, indicator_of_mem hζ]
      refine (ENNReal.ofReal_le_ofReal (gl3_kernel_pf w ζ)).trans ?_
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _), sub_zero]
      gcongr
      · exact gl3_ofReal_inv_le _
      · exact gl3_ofReal_inv_le _
      · exact gl3_ofReal_inv_le _
    · refine le_trans ?_ le_add_self
      have hζρ : ρ < ‖ζ‖ := by simpa using hζ
      rw [hf₂, indicator_of_mem (show ζ ∈ {ζ : ℂ | ρ < ‖ζ‖} from hζρ)]
      have hζ0 : 0 < ‖ζ‖ := hρ0.trans hζρ
      have h1 : ‖ζ‖ / 2 ≤ ‖ζ - 1‖ := by
        have := norm_sub_norm_le ζ 1
        rw [norm_one] at this
        linarith [norm_nonneg w]
      have h2 : ‖ζ‖ / 2 ≤ ‖ζ - w‖ := by
        have := norm_sub_norm_le ζ w
        linarith
      have hb1 : 0 < ‖ζ - 1‖ := by linarith
      have hbw : 0 < ‖ζ - w‖ := by linarith
      have hle : ‖w * (w - 1) / (ζ * (ζ - 1) * (ζ - w))‖ ≤ 4 * (‖w‖ * ‖w - 1‖) * ‖ζ‖⁻¹ ^ 3 := by
        simp only [norm_div, norm_mul]
        rw [inv_pow, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
        have hD : ‖ζ‖ * (‖ζ‖ / 2) * (‖ζ‖ / 2) ≤ ‖ζ‖ * ‖ζ - 1‖ * ‖ζ - w‖ := by gcongr
        nlinarith [mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ 4 * (‖w‖ * ‖w - 1‖))]
      calc ENNReal.ofReal ‖w * (w - 1) / (ζ * (ζ - 1) * (ζ - w))‖
          ≤ ENNReal.ofReal (4 * (‖w‖ * ‖w - 1‖) * ‖ζ‖⁻¹ ^ 3) := ENNReal.ofReal_le_ofReal hle
        _ = ENNReal.ofReal (4 * (‖w‖ * ‖w - 1‖)) * ENNReal.ofReal (‖ζ‖⁻¹ ^ 3) := ENNReal.ofReal_mul (by positivity)
        _ ≤ ENNReal.ofReal (4 * (‖w‖ * ‖w - 1‖)) * ‖ζ‖ₑ ^ (-(3 : ℝ)) :=
            mul_le_mul_right (gl3_ofReal_inv_pow_three_le _) _
  refine (lintegral_mono hpt).trans_lt ?_
  rw [lintegral_add_left hmeas₁, hf₁, hf₂, lintegral_indicator measurableSet_closedBall, lintegral_indicator hm₂,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, LiZhongQC.lintegral_compl_ball_enorm_rpow_neg (by norm_num) hρ0,
    lintegral_add_left hmeas₀, lintegral_add_left (((measurable_id'.sub_const 0).enorm.pow_const _).const_mul _),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (gl3_closedBall_fin hρ0 0),
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (gl3_closedBall_fin hρ0 1)⟩, gl3_closedBall_fin hρ0 w⟩,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)⟩

/-- **Unlabelled** (§3.4, l. 2470). If `Λ` contains `0, 1, ∞` and `z`, then `φ_z ∈ A(Λ)`, and by Agard's formula its
norm is the reciprocal of the Poincaré density of `ℂ̄ ∖ {0, 1, ∞}` at `z`. -/
theorem para3_4_phiZ_norm {Λ : Set ExtPlane} (hΛ : IsClosed Λ) (h0 : ((0 : ℂ) : ExtPlane) ∈ Λ)
    (h1 : ((1 : ℂ) : ExtPlane) ∈ Λ) (hinf : (OnePoint.infty : ExtPlane) ∈ Λ) {z : ℂ} (hz : (z : ExtPlane) ∈ Λ)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    phiZ z ∈ aSpaceClosed Λ ∧
      phiArea (phiZ z) univ = ENNReal.ofReal (poincareDensityGL {w : ℂ | w ≠ 0 ∧ w ≠ 1} z)⁻¹ := by
  sorry

/-- **Theorem 7** (§3.4, l. 2511), (1). `V_μ(0) = V_μ(1) = 0`. -/
theorem thm3_7_a {μ : ℂ → ℂ} (hμ : ∃ k : ℝ, IsBeltramiCoeff μ univ k) :
    normalizedCauchyTOn univ μ 0 = 0 ∧ normalizedCauchyTOn univ μ 1 = 0 := by
  -- `hμ` is not needed: the factor `z(z − 1)` of `V_μ` vanishes at `0` and `1`
  have _ := hμ
  refine ⟨?_, ?_⟩
  · show -((0 : ℂ) * (0 - 1) / π : ℂ) * ∫ ζ in univ, μ ζ / (ζ * (ζ - 1) * (ζ - 0)) = 0
    simp
  · show -((1 : ℂ) * (1 - 1) / π : ℂ) * ∫ ζ in univ, μ ζ / (ζ * (ζ - 1) * (ζ - 1)) = 0
    simp

/-- Helper for `thm3_7_d`: Pompeiu's formula for `g(z) = z(z − 1) f(z)` (`∂̄g = z(z − 1) ∂̄f`, the factor being
holomorphic): `∬ z(z − 1) ∂̄f(z)/(z − ζ) = −π ζ(ζ − 1) f(ζ)` for a smooth compactly supported `f`. -/
theorem gl3_pompeiu_poly {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (ζ : ℂ) :
    ∫ z, z * (z - 1) * dzbar f z / (z - ζ) = -(π : ℂ) * (ζ * (ζ - 1) * f ζ) := by
  set g : ℂ → ℂ := fun z => z * (z - 1) * f z with hg
  have hpoly : ContDiff ℝ 1 (fun z : ℂ => z * (z - 1)) := by fun_prop
  have hg1 : ContDiff ℝ 1 g := hpoly.mul (hf.of_le (by simp))
  have hgc : HasCompactSupport g := hfc.mul_left
  have hdg : ∀ z, dzbar g z = z * (z - 1) * dzbar f z := by
    intro z
    have hu : DifferentiableAt ℝ (fun w : ℂ => w * (w - 1)) z := (hpoly.differentiable one_ne_zero) z
    have hv : DifferentiableAt ℝ f z := (hf.differentiable (by simp)) z
    have hu0 : dzbar (fun w : ℂ => w * (w - 1)) z = 0 :=
      (LiZhongQC.cauchyRiemann_iff.1 ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)))).2
    rw [hg, LiZhongQC.dzbar_mul hu hv, hu0, mul_zero, add_zero]
  have h := LiZhongQC.cauchyT_dzbar_eq hg1 hgc ζ
  unfold LiZhongQC.cauchyT at h
  simp only [hdg] at h
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  rw [hg] at h
  simp only at h
  rw [← h]
  field_simp

/-- Helper for `thm3_7_d`: for `h` bounded by `M` and vanishing off `B̄(0, R)`, the Cauchy-kernel integrals
`∬ |h(z)|/|z − ζ|` are bounded uniformly in `ζ` (LZ `lintegral_closedBall_enorm_sub_rpow_neg_le`). -/
theorem gl3_kernel_uniform {h : ℂ → ℂ} {M R : ℝ} (hR : 0 < R) (hb : ∀ z, ‖h z‖ ≤ M)
    (hs : ∀ z, R < ‖z‖ → h z = 0) (ζ : ℂ) :
    ∫⁻ z, ‖h z / (z - ζ)‖ₑ ≤ ENNReal.ofReal M *
      ((∫⁻ w in ball (0 : ℂ) R, ‖w‖ₑ ^ (-(1 : ℝ))) +
        ENNReal.ofReal (R ^ (-(1 : ℝ))) * volume (closedBall (0 : ℂ) R)) := by
  have hpt : ∀ z, ‖h z / (z - ζ)‖ₑ ≤ (closedBall (0 : ℂ) R).indicator
      (fun z => ENNReal.ofReal M * ‖z - ζ‖ₑ ^ (-(1 : ℝ))) z := by
    intro z
    by_cases hz : z ∈ closedBall (0 : ℂ) R
    · rw [indicator_of_mem hz, div_eq_mul_inv, enorm_mul, ENNReal.rpow_neg_one]
      have hinv : ‖(z - ζ)⁻¹‖ₑ ≤ ‖z - ζ‖ₑ⁻¹ := by
        by_cases hz0 : z - ζ = 0
        · rw [hz0, inv_zero, enorm_zero]
          exact zero_le
        · rw [← ofReal_norm, ← ofReal_norm, norm_inv, ENNReal.ofReal_inv_of_pos (norm_pos_iff.2 hz0)]
      refine mul_le_mul' ?_ hinv
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hb z)
    · rw [indicator_of_notMem hz, hs z (by simpa using hz), zero_div, enorm_zero]
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_indicator measurableSet_closedBall,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  gcongr
  exact LiZhongQC.lintegral_closedBall_enorm_sub_rpow_neg_le one_pos hR ζ

/-- Helper for `thm3_7_b`: for `|z| = r > 3`, `∬ dξdη/(|ζ||ζ − 1||ζ − z|) ≤ C log r / r` (regions `|ζ| ≤ 2`,
`|ζ − z| < r/2`, `|ζ| > 3r/2` and the annulus `2 < |ζ| < 2r`, the last one giving the logarithm). -/
theorem gl3_kernel_log_bound : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ z : ℂ, 3 < ‖z‖ →
    ∫⁻ ζ, ENNReal.ofReal ((‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖)⁻¹) ≤ ENNReal.ofReal (C₂ * Real.log ‖z‖ / ‖z‖) := by
  set A₁ : ℝ≥0∞ := ∫⁻ ζ in closedBall (0 : ℂ) 2, (‖ζ - 0‖ₑ ^ (-(1 : ℝ)) + ‖ζ - 1‖ₑ ^ (-(1 : ℝ))) with hA₁
  have hA₁fin : A₁ ≠ ⊤ := by
    rw [hA₁, lintegral_add_left ((measurable_id'.sub_const 0).enorm.pow_const _)]
    exact ENNReal.add_ne_top.2 ⟨(gl3_closedBall_fin two_pos 0).ne, (gl3_closedBall_fin two_pos 1).ne⟩
  refine ⟨3 * A₁.toReal + 20 * π + 8 * π, by positivity, fun z hz => ?_⟩
  set r := ‖z‖ with hr
  have hr0 : 0 < r := by linarith
  have hlog1 : 1 ≤ Real.log r := by
    rw [Real.le_log_iff_exp_le hr0]
    have := Real.exp_one_lt_d9
    linarith
  -- the four dominating terms
  set g₁ : ℂ → ℝ≥0∞ := (closedBall (0 : ℂ) 2).indicator
    (fun ζ => ENNReal.ofReal (3 / r) * (‖ζ - 0‖ₑ ^ (-(1 : ℝ)) + ‖ζ - 1‖ₑ ^ (-(1 : ℝ)))) with hg₁
  set g₂ : ℂ → ℝ≥0∞ := (ball z (r / 2)).indicator
    (fun ζ => ENNReal.ofReal (12 / r ^ 2) * ‖ζ - z‖ₑ ^ (-(1 : ℝ))) with hg₂
  set g₃ : ℂ → ℝ≥0∞ := {ζ : ℂ | 3 / 2 * r < ‖ζ‖}.indicator (fun ζ => ENNReal.ofReal 6 * ‖ζ‖ₑ ^ (-(3 : ℝ))) with hg₃
  set g₄ : ℂ → ℝ≥0∞ := (LiZhongQC.annulus 2 (2 * r)).indicator
    (fun ζ => ENNReal.ofReal (4 / r) * ENNReal.ofReal (1 / ‖ζ‖ ^ 2)) with hg₄
  have hm₃ : MeasurableSet {ζ : ℂ | 3 / 2 * r < ‖ζ‖} := measurableSet_lt measurable_const measurable_norm
  have hm₄ : MeasurableSet (LiZhongQC.annulus 2 (2 * r)) :=
    (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_lt measurable_norm measurable_const)
  have hmeas₁ : Measurable g₁ :=
    (measurable_const.mul (((measurable_id'.sub_const 0).enorm.pow_const _).add
      ((measurable_id'.sub_const 1).enorm.pow_const _))).indicator measurableSet_closedBall
  have hmeas₂ : Measurable g₂ :=
    (measurable_const.mul ((measurable_id'.sub_const z).enorm.pow_const _)).indicator measurableSet_ball
  have hmeas₃ : Measurable g₃ := (measurable_const.mul (measurable_enorm.pow_const _)).indicator hm₃
  -- pointwise domination
  have hpt : ∀ ζ, ENNReal.ofReal ((‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖)⁻¹) ≤ g₁ ζ + g₂ ζ + g₃ ζ + g₄ ζ := by
    intro ζ
    by_cases hdeg : ‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖ = 0
    · rw [hdeg, inv_zero, ENNReal.ofReal_zero]
      exact zero_le
    have hpos : 0 < ‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖ := lt_of_le_of_ne (by positivity) (Ne.symm hdeg)
    have hne : ‖ζ‖ ≠ 0 ∧ ‖ζ - 1‖ ≠ 0 ∧ ‖ζ - z‖ ≠ 0 := by
      refine ⟨fun h => hdeg ?_, fun h => hdeg ?_, fun h => hdeg ?_⟩ <;> rw [h] <;> ring
    have ha : 0 < ‖ζ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne.1)
    have hb : 0 < ‖ζ - 1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne.2.1)
    have hc : 0 < ‖ζ - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne.2.2)
    by_cases h2 : ζ ∈ ball z (r / 2)
    · -- near `z`: `|ζ| > r/2`, `|ζ − 1| > r/6`
      have hζz : ‖ζ - z‖ < r / 2 := by rwa [mem_ball, dist_eq_norm] at h2
      have hζ : r / 2 ≤ ‖ζ‖ := by
        have := norm_sub_norm_le z ζ
        rw [norm_sub_rev] at this
        linarith
      have hζ1 : r / 6 ≤ ‖ζ - 1‖ := by
        have := norm_sub_norm_le ζ 1
        rw [norm_one] at this
        linarith
      have hle : (‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖)⁻¹ ≤ 12 / r ^ 2 * ‖ζ - z‖⁻¹ := by
        rw [mul_inv]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
        calc r ^ 2 / 12 = r / 2 * (r / 6) := by ring
          _ ≤ ‖ζ‖ * ‖ζ - 1‖ := mul_le_mul hζ hζ1 (by positivity) (norm_nonneg _)
      have hg2 : ENNReal.ofReal ((‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖)⁻¹) ≤ g₂ ζ := by
        rw [hg₂, indicator_of_mem h2]
        calc ENNReal.ofReal ((‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖)⁻¹) ≤ ENNReal.ofReal (12 / r ^ 2 * ‖ζ - z‖⁻¹) :=
              ENNReal.ofReal_le_ofReal hle
          _ = ENNReal.ofReal (12 / r ^ 2) * ENNReal.ofReal ‖ζ - z‖⁻¹ := ENNReal.ofReal_mul (by positivity)
          _ ≤ ENNReal.ofReal (12 / r ^ 2) * ‖ζ - z‖ₑ ^ (-(1 : ℝ)) := by
              gcongr
              exact gl3_ofReal_inv_le _
      calc _ ≤ g₂ ζ := hg2
        _ ≤ g₁ ζ + g₂ ζ := le_add_self
        _ ≤ g₁ ζ + g₂ ζ + g₃ ζ := le_self_add
        _ ≤ g₁ ζ + g₂ ζ + g₃ ζ + g₄ ζ := le_self_add
    have hζz : r / 2 ≤ ‖ζ - z‖ := by
      rw [mem_ball, dist_eq_norm, not_lt] at h2
      exact h2
    by_cases h1 : ζ ∈ closedBall (0 : ℂ) 2
    · -- near the poles `0, 1`: `|ζ − z| ≥ r/3` and `1/(|ζ||ζ − 1|) ≤ 1/|ζ| + 1/|ζ − 1|`
      have hζ2 : ‖ζ‖ ≤ 2 := mem_closedBall_zero_iff.1 h1
      have hzζ : r / 3 ≤ ‖ζ - z‖ := by
        have := norm_sub_norm_le z ζ
        rw [norm_sub_rev] at this
        linarith
      have hle : (‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖)⁻¹ ≤ 3 / r * (‖ζ‖ * ‖ζ - 1‖)⁻¹ := by
        rw [mul_inv, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [inv_le_comm₀ hc (by positivity), inv_div]
        exact hzζ
      have hg1 : ENNReal.ofReal ((‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖)⁻¹) ≤ g₁ ζ := by
        rw [hg₁, indicator_of_mem h1]
        calc ENNReal.ofReal ((‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖)⁻¹) ≤ ENNReal.ofReal (3 / r * (‖ζ‖ * ‖ζ - 1‖)⁻¹) :=
              ENNReal.ofReal_le_ofReal hle
          _ = ENNReal.ofReal (3 / r) * ENNReal.ofReal (‖ζ‖ * ‖ζ - 1‖)⁻¹ := ENNReal.ofReal_mul (by positivity)
          _ ≤ ENNReal.ofReal (3 / r) * (‖ζ - 0‖ₑ ^ (-(1 : ℝ)) + ‖ζ - 1‖ₑ ^ (-(1 : ℝ))) :=
              mul_le_mul_right (gl3_ofReal_inv_mul_le ζ) _
      calc _ ≤ g₁ ζ := hg1
        _ ≤ g₁ ζ + g₂ ζ := le_self_add
        _ ≤ g₁ ζ + g₂ ζ + g₃ ζ := le_self_add
        _ ≤ g₁ ζ + g₂ ζ + g₃ ζ + g₄ ζ := le_self_add
    have hζ2 : 2 < ‖ζ‖ := by
      rw [mem_closedBall_zero_iff, not_le] at h1
      exact h1
    have hζ1 : ‖ζ‖ / 2 ≤ ‖ζ - 1‖ := by
      have := norm_sub_norm_le ζ 1
      rw [norm_one] at this
      linarith
    by_cases h3 : ζ ∈ {ζ : ℂ | 3 / 2 * r < ‖ζ‖}
    · -- far: `|ζ − z| ≥ |ζ|/3`, `|ζ − 1| ≥ |ζ|/2`
      have hζ3 : 3 / 2 * r < ‖ζ‖ := h3
      have hzζ : ‖ζ‖ / 3 ≤ ‖ζ - z‖ := by
        have := norm_sub_norm_le ζ z
        linarith
      have hle : (‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖)⁻¹ ≤ 6 * ‖ζ‖⁻¹ ^ 3 := by
        rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul, div_le_iff₀ hpos]
        have h4 : ‖ζ‖ * (‖ζ‖ / 2) * (‖ζ‖ / 3) ≤ ‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖ := by gcongr
        nlinarith
      have hg3 : ENNReal.ofReal ((‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖)⁻¹) ≤ g₃ ζ := by
        rw [hg₃, indicator_of_mem h3]
        calc ENNReal.ofReal ((‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖)⁻¹) ≤ ENNReal.ofReal (6 * ‖ζ‖⁻¹ ^ 3) :=
              ENNReal.ofReal_le_ofReal hle
          _ = ENNReal.ofReal 6 * ENNReal.ofReal (‖ζ‖⁻¹ ^ 3) := ENNReal.ofReal_mul (by norm_num)
          _ ≤ ENNReal.ofReal 6 * ‖ζ‖ₑ ^ (-(3 : ℝ)) := by
              gcongr
              exact gl3_ofReal_inv_pow_three_le _
      calc _ ≤ g₃ ζ := hg3
        _ ≤ g₁ ζ + g₂ ζ + g₃ ζ := le_add_self
        _ ≤ g₁ ζ + g₂ ζ + g₃ ζ + g₄ ζ := le_self_add
    · -- middle: `2 < |ζ| ≤ 3r/2`, `|ζ − z| ≥ r/2`
      have hζ3 : ‖ζ‖ ≤ 3 / 2 * r := not_lt.1 h3
      have h4 : ζ ∈ LiZhongQC.annulus 2 (2 * r) := ⟨hζ2, by linarith⟩
      have hle : (‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖)⁻¹ ≤ 4 / r * (1 / ‖ζ‖ ^ 2) := by
        rw [div_mul_div_comm, mul_one, inv_le_comm₀ hpos (by positivity), inv_div,
          div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
        have h5 : ‖ζ‖ * (‖ζ‖ / 2) * (r / 2) ≤ ‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖ := by gcongr
        nlinarith
      have hg4 : ENNReal.ofReal ((‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖)⁻¹) ≤ g₄ ζ := by
        rw [hg₄, indicator_of_mem h4, ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal hle
      calc _ ≤ g₄ ζ := hg4
        _ ≤ g₁ ζ + g₂ ζ + g₃ ζ + g₄ ζ := le_add_self
  -- the four integrals
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left ((hmeas₁.fun_add hmeas₂).fun_add hmeas₃), lintegral_add_left (hmeas₁.fun_add hmeas₂),
    lintegral_add_left hmeas₁, hg₁, hg₂, hg₃, hg₄, lintegral_indicator measurableSet_closedBall,
    lintegral_indicator measurableSet_ball, lintegral_indicator hm₃, lintegral_indicator hm₄,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    LiZhongQC.lintegral_ball_sub_enorm_rpow_neg (by norm_num) (by linarith),
    LiZhongQC.lintegral_compl_ball_enorm_rpow_neg (by norm_num) (by linarith),
    LiZhongQC.lintegral_annulus_inv_normSq (by norm_num) (by linarith)]
  calc ENNReal.ofReal (3 / r) * (∫⁻ ζ in closedBall (0 : ℂ) 2, (‖ζ - 0‖ₑ ^ (-(1 : ℝ)) + ‖ζ - 1‖ₑ ^ (-(1 : ℝ)))) +
        ENNReal.ofReal (12 / r ^ 2) * (ENNReal.ofReal (2 * π) * ENNReal.ofReal ((r / 2) ^ (2 - (1 : ℝ)) / (2 - 1))) +
        ENNReal.ofReal 6 * (ENNReal.ofReal (2 * π) * ENNReal.ofReal (-(3 / 2 * r) ^ (2 - (3 : ℝ)) / (2 - 3))) +
        ENNReal.ofReal (4 / r) * (ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (2 * r / 2)))
      ≤ ENNReal.ofReal (3 / r) * ENNReal.ofReal A₁.toReal +
        ENNReal.ofReal (12 / r ^ 2 * (2 * π * (r / 2))) +
        ENNReal.ofReal (6 * (2 * π * (2 / (3 * r)))) +
        ENNReal.ofReal (4 / r * (2 * π * Real.log r)) := by
          gcongr
          · exact (ENNReal.ofReal_toReal hA₁fin).ge
          · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            refine le_of_eq (congrArg ENNReal.ofReal ?_)
            norm_num
          · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
            refine le_of_eq (congrArg ENNReal.ofReal ?_)
            rw [show (2 : ℝ) - 3 = -1 by norm_num, Real.rpow_neg_one, neg_div_neg_eq, div_one]
            ring
          · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
              show 2 * r / 2 = r by ring]
    _ = ENNReal.ofReal (3 / r * A₁.toReal + 12 / r ^ 2 * (2 * π * (r / 2)) + 6 * (2 * π * (2 / (3 * r))) +
          4 / r * (2 * π * Real.log r)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((3 * A₁.toReal + 20 * π + 8 * π) * Real.log r / r) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hA : 0 ≤ A₁.toReal := ENNReal.toReal_nonneg
          rw [le_div_iff₀ hr0]
          have e1 : (3 / r * A₁.toReal + 12 / r ^ 2 * (2 * π * (r / 2)) + 6 * (2 * π * (2 / (3 * r))) +
              4 / r * (2 * π * Real.log r)) * r = 3 * A₁.toReal + 12 * π + 8 * π + 8 * π * Real.log r := by
            field_simp
            ring
          rw [e1]
          nlinarith [mul_nonneg hA (sub_nonneg.2 hlog1), mul_nonneg Real.pi_pos.le (sub_nonneg.2 hlog1)]

/-- Helper for `thm3_7_c`: `ζ ↦ w(w − 1) μ(ζ)/(ζ(ζ − 1)(ζ − w))` is integrable for a bounded measurable `μ`
(`gl3_kernel_lintegral_lt_top`). -/
theorem gl3_kernel_integrable {μ : ℂ → ℂ} {kb : ℝ} (hμm : AEStronglyMeasurable μ volume)
    (hμb : ∀ᵐ ζ ∂volume, ‖μ ζ‖ ≤ kb) (w : ℂ) :
    Integrable (fun ζ => w * (w - 1) * (μ ζ / (ζ * (ζ - 1) * (ζ - w)))) := by
  have hDinv : Measurable fun ζ : ℂ => (ζ * (ζ - 1) * (ζ - w))⁻¹ := by fun_prop
  have hK : Integrable (fun ζ : ℂ => w * (w - 1) / (ζ * (ζ - 1) * (ζ - w))) := by
    refine ⟨?_, (hasFiniteIntegral_iff_norm _).2 (gl3_kernel_lintegral_lt_top w)⟩
    simp only [div_eq_mul_inv]
    exact (measurable_const.mul hDinv).aestronglyMeasurable
  refine (hK.norm.const_mul kb).mono' ?_ ?_
  · simp only [div_eq_mul_inv]
    exact aestronglyMeasurable_const.mul (hμm.mul hDinv.aestronglyMeasurable)
  · filter_upwards [hμb] with ζ hζ
    rw [show w * (w - 1) * (μ ζ / (ζ * (ζ - 1) * (ζ - w))) = μ ζ * (w * (w - 1) / (ζ * (ζ - 1) * (ζ - w))) by
      ring, norm_mul]
    exact mul_le_mul_of_nonneg_right hζ (norm_nonneg _)

/-- Helper for `thm3_7_c`: for `|z|, |t| < R` and `0 < δ = |z − t| < 1/2`, the normalized Cauchy kernels satisfy
`∬ |K_z − K_t| ≤ B δ log(1/δ)`, `B` depending only on `R`. Here
`K_z − K_t = (z − t)(1/((ζ − z)(ζ − t)) − 1/(ζ(ζ − 1)))`; the discs `|ζ − z|, |ζ − t| < δ/2` contribute `2π` each,
`δ/4 < |ζ − z| < ρ + R + 1` (where `|ζ − t| ≥ |ζ − z|/3`) the logarithm, the poles `0, 1` a constant, and on
`|ζ| > ρ = 2R + 2` the bracket is `((z + t − 1)ζ − zt)/((ζ − z)(ζ − t)ζ(ζ − 1)) = O(|ζ|⁻³)`. -/
theorem gl3_kernel_diff_bound (R : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z t : ℂ, ‖z‖ < R → ‖t‖ < R → 0 < ‖z - t‖ →
    ‖z - t‖ < 1 / 2 → ∫⁻ ζ, ENNReal.ofReal ‖z * (z - 1) / (ζ * (ζ - 1) * (ζ - z)) -
      t * (t - 1) / (ζ * (ζ - 1) * (ζ - t))‖ ≤ ENNReal.ofReal (B * ‖z - t‖ * Real.log ‖z - t‖⁻¹) := by
  obtain ⟨R', hR'1, hRR'⟩ : ∃ R' : ℝ, 1 ≤ R' ∧ R ≤ R' := ⟨max R 1, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 2 * R' + 2 := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  set A₂ : ℝ≥0∞ := ∫⁻ ζ in closedBall (0 : ℂ) ρ, (‖ζ - 0‖ₑ ^ (-(1 : ℝ)) + ‖ζ - 1‖ₑ ^ (-(1 : ℝ))) with hA₂
  have hA₂fin : A₂ ≠ ⊤ := by
    rw [hA₂, lintegral_add_left ((measurable_id'.sub_const 0).enorm.pow_const _)]
    exact ENNReal.add_ne_top.2 ⟨(gl3_closedBall_fin hρ0 0).ne, (gl3_closedBall_fin hρ0 1).ne⟩
  have hlogρ : 0 ≤ Real.log (4 * (ρ + R' + 1)) := Real.log_nonneg (by linarith)
  set B₀ : ℝ := 4 * π + 6 * π * Real.log (4 * (ρ + R' + 1)) + A₂.toReal + 16 * π * (3 * R' + 1) / ρ with hB₀def
  have hB₀ : 0 ≤ B₀ := by
    rw [hB₀def]
    positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨B₀ / Real.log 2 + 6 * π, by positivity, fun z t hz ht hδ0 hδ => ?_⟩
  set δ := ‖z - t‖ with hδdef
  have hδne : δ ≠ 0 := hδ0.ne'
  have hzR : ‖z‖ < R' := hz.trans_le hRR'
  have htR : ‖t‖ < R' := ht.trans_le hRR'
  have h2δ : 2 ≤ δ⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hδ0]
    linarith [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  have hL : Real.log 2 ≤ Real.log δ⁻¹ := Real.log_le_log (by norm_num) h2δ
  have hδ2 : 0 < δ / 2 := by positivity
  -- the dominating functions
  set h₁ : ℂ → ℝ≥0∞ := (ball z (δ / 2)).indicator
    (fun ζ => ENNReal.ofReal (2 / δ) * ‖ζ - z‖ₑ ^ (-(1 : ℝ))) with hh₁
  set h₂ : ℂ → ℝ≥0∞ := (ball t (δ / 2)).indicator
    (fun ζ => ENNReal.ofReal (2 / δ) * ‖ζ - t‖ₑ ^ (-(1 : ℝ))) with hh₂
  set e₃ : ℂ → ℝ≥0∞ := (LiZhongQC.annulus (δ / 4) (ρ + R' + 1)).indicator
    (fun w => ENNReal.ofReal 3 * ENNReal.ofReal (1 / ‖w‖ ^ 2)) with he₃
  set h₄ : ℂ → ℝ≥0∞ := (closedBall (0 : ℂ) ρ).indicator
    (fun ζ => ‖ζ - 0‖ₑ ^ (-(1 : ℝ)) + ‖ζ - 1‖ₑ ^ (-(1 : ℝ))) with hh₄
  set h₅ : ℂ → ℝ≥0∞ := {ζ : ℂ | ρ < ‖ζ‖}.indicator
    (fun ζ => ENNReal.ofReal (8 * (3 * R' + 1)) * ‖ζ‖ₑ ^ (-(3 : ℝ))) with hh₅
  have hmA : MeasurableSet (LiZhongQC.annulus (δ / 4) (ρ + R' + 1)) :=
    (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_lt measurable_norm measurable_const)
  have hm₅ : MeasurableSet {ζ : ℂ | ρ < ‖ζ‖} := measurableSet_lt measurable_const measurable_norm
  have hm₁ : Measurable h₁ :=
    (measurable_const.mul ((measurable_id'.sub_const z).enorm.pow_const _)).indicator measurableSet_ball
  have hm₂ : Measurable h₂ :=
    (measurable_const.mul ((measurable_id'.sub_const t).enorm.pow_const _)).indicator measurableSet_ball
  have hme₃ : Measurable e₃ :=
    (measurable_const.mul (by fun_prop : Measurable fun w : ℂ => ENNReal.ofReal (1 / ‖w‖ ^ 2))).indicator hmA
  have hm₃ : Measurable fun ζ => e₃ (ζ - z) := hme₃.comp (measurable_id'.sub_const z)
  have hm₄ : Measurable h₄ :=
    (((measurable_id'.sub_const 0).enorm.pow_const _).add
      ((measurable_id'.sub_const 1).enorm.pow_const _)).indicator measurableSet_closedBall
  -- pointwise bound off the four poles
  have hpt : ∀ ζ : ℂ, ζ ≠ 0 → ζ ≠ 1 → ζ ≠ z → ζ ≠ t →
      ENNReal.ofReal ‖z * (z - 1) / (ζ * (ζ - 1) * (ζ - z)) - t * (t - 1) / (ζ * (ζ - 1) * (ζ - t))‖ ≤
        ENNReal.ofReal δ * (h₁ ζ + h₂ ζ + e₃ (ζ - z) + h₄ ζ + h₅ ζ) := by
    intro ζ h0 h1 hz' ht'
    have h1' : ζ - 1 ≠ 0 := sub_ne_zero.2 h1
    have hz'' : ζ - z ≠ 0 := sub_ne_zero.2 hz'
    have ht'' : ζ - t ≠ 0 := sub_ne_zero.2 ht'
    have ha : 0 < ‖ζ‖ := norm_pos_iff.2 h0
    have hb : 0 < ‖ζ - 1‖ := norm_pos_iff.2 h1'
    have hc : 0 < ‖ζ - z‖ := norm_pos_iff.2 hz''
    have hd : 0 < ‖ζ - t‖ := norm_pos_iff.2 ht''
    have ha' : ‖ζ‖ ≠ 0 := ha.ne'
    have hT1 : δ ≤ ‖ζ - z‖ + ‖ζ - t‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub z ζ t
      rw [norm_sub_rev z ζ] at this
      linarith
    have hT2 : ‖ζ - z‖ ≤ ‖ζ - t‖ + δ := by
      have := norm_sub_le_norm_sub_add_norm_sub ζ t z
      rw [norm_sub_rev t z] at this
      linarith
    by_cases hfar : ρ < ‖ζ‖
    · -- far: the bracket is `((z + t − 1)ζ − zt)/((ζ − z)(ζ − t)ζ(ζ − 1)) = O(|ζ|⁻³)`
      have e : z * (z - 1) / (ζ * (ζ - 1) * (ζ - z)) - t * (t - 1) / (ζ * (ζ - 1) * (ζ - t)) =
          (z - t) * ((z + t - 1) * ζ - z * t) / ((ζ - z) * (ζ - t) * (ζ * (ζ - 1))) := by
        field_simp
        ring
      have hζR : R' < ‖ζ‖ := by linarith
      have hnum : ‖(z + t - 1) * ζ - z * t‖ ≤ (3 * R' + 1) * ‖ζ‖ := by
        have hs : ‖z + t - 1‖ ≤ 2 * R' + 1 := by
          calc ‖z + t - 1‖ ≤ ‖z + t‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ ≤ ‖z‖ + ‖t‖ + 1 := by rw [norm_one]; exact add_le_add (norm_add_le _ _) le_rfl
            _ ≤ 2 * R' + 1 := by linarith
        have hp : ‖z‖ * ‖t‖ ≤ R' * ‖ζ‖ := mul_le_mul hzR.le (htR.trans hζR).le (norm_nonneg _) (by linarith)
        calc ‖(z + t - 1) * ζ - z * t‖ ≤ ‖z + t - 1‖ * ‖ζ‖ + ‖z‖ * ‖t‖ := by
              refine (norm_sub_le _ _).trans (le_of_eq ?_)
              rw [norm_mul, norm_mul]
          _ ≤ (2 * R' + 1) * ‖ζ‖ + R' * ‖ζ‖ := add_le_add (mul_le_mul_of_nonneg_right hs (norm_nonneg _)) hp
          _ = (3 * R' + 1) * ‖ζ‖ := by ring
      have hzz : ‖ζ‖ / 2 ≤ ‖ζ - z‖ := by
        have := norm_sub_norm_le ζ z
        linarith
      have htt : ‖ζ‖ / 2 ≤ ‖ζ - t‖ := by
        have := norm_sub_norm_le ζ t
        linarith
      have h11 : ‖ζ‖ / 2 ≤ ‖ζ - 1‖ := by
        have := norm_sub_norm_le ζ 1
        rw [norm_one] at this
        linarith
      have hden : ‖ζ‖ / 2 * (‖ζ‖ / 2) * (‖ζ‖ * (‖ζ‖ / 2)) ≤ ‖ζ - z‖ * ‖ζ - t‖ * (‖ζ‖ * ‖ζ - 1‖) := by
        gcongr
      have hle : ‖z * (z - 1) / (ζ * (ζ - 1) * (ζ - z)) - t * (t - 1) / (ζ * (ζ - 1) * (ζ - t))‖ ≤
          δ * (8 * (3 * R' + 1) * ‖ζ‖⁻¹ ^ 3) := by
        rw [e]
        simp only [norm_div, norm_mul]
        rw [← hδdef, mul_div_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hδ0.le
        rw [div_le_iff₀ (by positivity), inv_pow]
        calc ‖(z + t - 1) * ζ - z * t‖ ≤ (3 * R' + 1) * ‖ζ‖ := hnum
          _ = 8 * (3 * R' + 1) * (‖ζ‖ ^ 3)⁻¹ * (‖ζ‖ / 2 * (‖ζ‖ / 2) * (‖ζ‖ * (‖ζ‖ / 2))) := by
              field_simp
              ring
          _ ≤ 8 * (3 * R' + 1) * (‖ζ‖ ^ 3)⁻¹ * (‖ζ - z‖ * ‖ζ - t‖ * (‖ζ‖ * ‖ζ - 1‖)) := by
              gcongr
      calc ENNReal.ofReal ‖z * (z - 1) / (ζ * (ζ - 1) * (ζ - z)) - t * (t - 1) / (ζ * (ζ - 1) * (ζ - t))‖
          ≤ ENNReal.ofReal (δ * (8 * (3 * R' + 1) * ‖ζ‖⁻¹ ^ 3)) := ENNReal.ofReal_le_ofReal hle
        _ = ENNReal.ofReal δ * (ENNReal.ofReal (8 * (3 * R' + 1)) * ENNReal.ofReal (‖ζ‖⁻¹ ^ 3)) := by
            rw [ENNReal.ofReal_mul hδ0.le, ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal δ * h₅ ζ := by
            rw [hh₅, indicator_of_mem (show ζ ∈ {ζ : ℂ | ρ < ‖ζ‖} from hfar)]
            exact mul_le_mul_right (mul_le_mul_right (gl3_ofReal_inv_pow_three_le _) _) _
        _ ≤ ENNReal.ofReal δ * (h₁ ζ + h₂ ζ + e₃ (ζ - z) + h₄ ζ + h₅ ζ) := mul_le_mul_right le_add_self _
    · -- near: `|K_z − K_t| ≤ δ (1/(|ζ − z||ζ − t|) + 1/(|ζ||ζ − 1|))`
      have hζρ : ζ ∈ closedBall (0 : ℂ) ρ := mem_closedBall_zero_iff.2 (not_lt.1 hfar)
      have e : z * (z - 1) / (ζ * (ζ - 1) * (ζ - z)) - t * (t - 1) / (ζ * (ζ - 1) * (ζ - t)) =
          (z - t) * (1 / ((ζ - z) * (ζ - t)) - 1 / (ζ * (ζ - 1))) := by
        field_simp
        ring
      have hle : ‖z * (z - 1) / (ζ * (ζ - 1) * (ζ - z)) - t * (t - 1) / (ζ * (ζ - 1) * (ζ - t))‖ ≤
          δ * ((‖ζ - z‖ * ‖ζ - t‖)⁻¹ + (‖ζ‖ * ‖ζ - 1‖)⁻¹) := by
        rw [e, norm_mul, ← hδdef]
        refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (le_of_eq ?_)) hδ0.le
        rw [one_div, one_div, norm_inv, norm_inv, norm_mul, norm_mul]
      have hP : ENNReal.ofReal (‖ζ - z‖ * ‖ζ - t‖)⁻¹ ≤ h₁ ζ + h₂ ζ + e₃ (ζ - z) := by
        by_cases hb1 : ζ ∈ ball z (δ / 2)
        · have hζz : ‖ζ - z‖ < δ / 2 := by rwa [mem_ball, dist_eq_norm] at hb1
          have hζt : δ / 2 ≤ ‖ζ - t‖ := by linarith
          refine le_trans ?_ (le_trans le_self_add le_self_add)
          rw [hh₁, indicator_of_mem hb1]
          calc ENNReal.ofReal (‖ζ - z‖ * ‖ζ - t‖)⁻¹ ≤ ENNReal.ofReal (2 / δ * ‖ζ - z‖⁻¹) := by
                refine ENNReal.ofReal_le_ofReal ?_
                rw [mul_inv, mul_comm]
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                rw [inv_le_comm₀ hd (by positivity), inv_div]
                exact hζt
            _ = ENNReal.ofReal (2 / δ) * ENNReal.ofReal ‖ζ - z‖⁻¹ := ENNReal.ofReal_mul (by positivity)
            _ ≤ ENNReal.ofReal (2 / δ) * ‖ζ - z‖ₑ ^ (-(1 : ℝ)) := mul_le_mul_right (gl3_ofReal_inv_le _) _
        by_cases hb2 : ζ ∈ ball t (δ / 2)
        · have hζt : ‖ζ - t‖ < δ / 2 := by rwa [mem_ball, dist_eq_norm] at hb2
          have hζz : δ / 2 ≤ ‖ζ - z‖ := by linarith
          refine le_trans ?_ (le_trans le_add_self le_self_add)
          rw [hh₂, indicator_of_mem hb2]
          calc ENNReal.ofReal (‖ζ - z‖ * ‖ζ - t‖)⁻¹ ≤ ENNReal.ofReal (2 / δ * ‖ζ - t‖⁻¹) := by
                refine ENNReal.ofReal_le_ofReal ?_
                rw [mul_inv]
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                rw [inv_le_comm₀ hc (by positivity), inv_div]
                exact hζz
            _ = ENNReal.ofReal (2 / δ) * ENNReal.ofReal ‖ζ - t‖⁻¹ := ENNReal.ofReal_mul (by positivity)
            _ ≤ ENNReal.ofReal (2 / δ) * ‖ζ - t‖ₑ ^ (-(1 : ℝ)) := mul_le_mul_right (gl3_ofReal_inv_le _) _
        · have hζz : δ / 2 ≤ ‖ζ - z‖ := by
            rw [mem_ball, dist_eq_norm, not_lt] at hb1
            exact hb1
          have hζt : δ / 2 ≤ ‖ζ - t‖ := by
            rw [mem_ball, dist_eq_norm, not_lt] at hb2
            exact hb2
          have h3 : ‖ζ - z‖ ≤ 3 * ‖ζ - t‖ := by linarith
          have hA : ζ - z ∈ LiZhongQC.annulus (δ / 4) (ρ + R' + 1) := by
            refine ⟨by linarith, ?_⟩
            have := norm_sub_le ζ z
            have := mem_closedBall_zero_iff.1 hζρ
            linarith
          refine le_trans ?_ le_add_self
          rw [he₃, indicator_of_mem hA, ← ENNReal.ofReal_mul (by norm_num)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_one_div, inv_le_comm₀ (by positivity) (by positivity), inv_div, div_le_iff₀ (by norm_num)]
          nlinarith
      calc ENNReal.ofReal ‖z * (z - 1) / (ζ * (ζ - 1) * (ζ - z)) - t * (t - 1) / (ζ * (ζ - 1) * (ζ - t))‖
          ≤ ENNReal.ofReal (δ * ((‖ζ - z‖ * ‖ζ - t‖)⁻¹ + (‖ζ‖ * ‖ζ - 1‖)⁻¹)) := ENNReal.ofReal_le_ofReal hle
        _ = ENNReal.ofReal δ * (ENNReal.ofReal (‖ζ - z‖ * ‖ζ - t‖)⁻¹ + ENNReal.ofReal (‖ζ‖ * ‖ζ - 1‖)⁻¹) := by
            rw [ENNReal.ofReal_mul hδ0.le, ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ ENNReal.ofReal δ * (h₁ ζ + h₂ ζ + e₃ (ζ - z) + h₄ ζ) := by
            refine mul_le_mul_right (add_le_add hP ?_) _
            rw [hh₄, indicator_of_mem hζρ]
            exact gl3_ofReal_inv_mul_le ζ
        _ ≤ ENNReal.ofReal δ * (h₁ ζ + h₂ ζ + e₃ (ζ - z) + h₄ ζ + h₅ ζ) := mul_le_mul_right le_self_add _
  have hne : ∀ a : ℂ, ∀ᵐ ζ ∂(volume : Measure ℂ), ζ ≠ a := fun a => by
    rw [ae_iff]
    simp
  have hae : ∀ᵐ ζ ∂(volume : Measure ℂ),
      ENNReal.ofReal ‖z * (z - 1) / (ζ * (ζ - 1) * (ζ - z)) - t * (t - 1) / (ζ * (ζ - 1) * (ζ - t))‖ ≤
        ENNReal.ofReal δ * (h₁ ζ + h₂ ζ + e₃ (ζ - z) + h₄ ζ + h₅ ζ) := by
    filter_upwards [hne 0, hne 1, hne z, hne t] with ζ h0 h1 hz' ht'
    exact hpt ζ h0 h1 hz' ht'
  -- the integral of the dominating function
  have hlogsplit : Real.log ((ρ + R' + 1) / (δ / 4)) = Real.log (4 * (ρ + R' + 1)) + Real.log δ⁻¹ := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hI : ∫⁻ ζ, (h₁ ζ + h₂ ζ + e₃ (ζ - z) + h₄ ζ + h₅ ζ) ≤ ENNReal.ofReal (B₀ + 6 * π * Real.log δ⁻¹) := by
    rw [lintegral_add_left (((hm₁.fun_add hm₂).fun_add hm₃).fun_add hm₄),
      lintegral_add_left ((hm₁.fun_add hm₂).fun_add hm₃), lintegral_add_left (hm₁.fun_add hm₂),
      lintegral_add_left hm₁, lintegral_sub_right_eq_self e₃ z,
      hh₁, hh₂, he₃, hh₄, hh₅, lintegral_indicator measurableSet_ball, lintegral_indicator measurableSet_ball,
      lintegral_indicator hmA, lintegral_indicator measurableSet_closedBall, lintegral_indicator hm₅,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      LiZhongQC.lintegral_ball_sub_enorm_rpow_neg (by norm_num) hδ2,
      LiZhongQC.lintegral_ball_sub_enorm_rpow_neg (by norm_num) hδ2,
      LiZhongQC.lintegral_annulus_inv_normSq (by positivity) (by linarith),
      LiZhongQC.lintegral_compl_ball_enorm_rpow_neg (by norm_num) hρ0]
    have hlogA : 0 ≤ Real.log ((ρ + R' + 1) / (δ / 4)) := by
      rw [hlogsplit]
      have : 0 < Real.log δ⁻¹ := hlog2.trans_le hL
      positivity
    calc ENNReal.ofReal (2 / δ) * (ENNReal.ofReal (2 * π) * ENNReal.ofReal ((δ / 2) ^ (2 - (1 : ℝ)) / (2 - 1))) +
          ENNReal.ofReal (2 / δ) * (ENNReal.ofReal (2 * π) * ENNReal.ofReal ((δ / 2) ^ (2 - (1 : ℝ)) / (2 - 1))) +
          ENNReal.ofReal 3 * (ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log ((ρ + R' + 1) / (δ / 4)))) + A₂ +
          ENNReal.ofReal (8 * (3 * R' + 1)) *
            (ENNReal.ofReal (2 * π) * ENNReal.ofReal (-ρ ^ (2 - (3 : ℝ)) / (2 - 3)))
        ≤ ENNReal.ofReal (2 * π) + ENNReal.ofReal (2 * π) +
          ENNReal.ofReal (3 * (2 * π * Real.log ((ρ + R' + 1) / (δ / 4)))) + ENNReal.ofReal A₂.toReal +
          ENNReal.ofReal (8 * (3 * R' + 1) * (2 * π * ρ⁻¹)) := by
          gcongr
          · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            refine le_of_eq (congrArg ENNReal.ofReal ?_)
            norm_num
            field_simp
          · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            refine le_of_eq (congrArg ENNReal.ofReal ?_)
            norm_num
            field_simp
          · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
          · exact (ENNReal.ofReal_toReal hA₂fin).ge
          · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            refine le_of_eq (congrArg ENNReal.ofReal ?_)
            rw [show (2 : ℝ) - 3 = -1 by norm_num, Real.rpow_neg_one, neg_div_neg_eq, div_one]
      _ = ENNReal.ofReal (2 * π + 2 * π + 3 * (2 * π * Real.log ((ρ + R' + 1) / (δ / 4))) + A₂.toReal +
            8 * (3 * R' + 1) * (2 * π * ρ⁻¹)) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity)]
      _ = ENNReal.ofReal (B₀ + 6 * π * Real.log δ⁻¹) := by
          rw [hlogsplit, hB₀def]
          congr 1
          ring
  calc ∫⁻ ζ, ENNReal.ofReal ‖z * (z - 1) / (ζ * (ζ - 1) * (ζ - z)) - t * (t - 1) / (ζ * (ζ - 1) * (ζ - t))‖
      ≤ ∫⁻ ζ, ENNReal.ofReal δ * (h₁ ζ + h₂ ζ + e₃ (ζ - z) + h₄ ζ + h₅ ζ) := lintegral_mono_ae hae
    _ = ENNReal.ofReal δ * ∫⁻ ζ, (h₁ ζ + h₂ ζ + e₃ (ζ - z) + h₄ ζ + h₅ ζ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal δ * ENNReal.ofReal (B₀ + 6 * π * Real.log δ⁻¹) := mul_le_mul_right hI _
    _ = ENNReal.ofReal (δ * (B₀ + 6 * π * Real.log δ⁻¹)) := (ENNReal.ofReal_mul hδ0.le).symm
    _ ≤ ENNReal.ofReal ((B₀ / Real.log 2 + 6 * π) * δ * Real.log δ⁻¹) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hB : B₀ ≤ B₀ / Real.log 2 * Real.log δ⁻¹ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
          exact mul_le_mul_of_nonneg_left hL hB₀
        nlinarith [mul_le_mul_of_nonneg_left hB hδ0.le]

/-- **Theorem 7** (§3.4, l. 2511), (2). `|V_μ(z)| ≤ C |z| log |z|` for `|z| > 3`, `C` depending only on `‖μ‖∞`. -/
theorem thm3_7_b (k : ℝ) :
    ∃ C : ℝ, ∀ μ : ℂ → ℂ, IsBeltramiCoeff μ univ k → ∀ z : ℂ, 3 < ‖z‖ →
      ‖normalizedCauchyTOn univ μ z‖ ≤ C * ‖z‖ * Real.log ‖z‖ := by
  obtain ⟨C₂, hC₂, hJ⟩ := gl3_kernel_log_bound
  obtain ⟨kb, hkb0, hkbk⟩ : ∃ kb : ℝ, 0 ≤ kb ∧ k ≤ kb := ⟨max k 0, le_max_right _ _, le_max_left _ _⟩
  refine ⟨2 * kb * C₂ / π, fun μ hμ z hz => ?_⟩
  obtain ⟨-, hμb⟩ := hμ
  rw [Measure.restrict_univ] at hμb
  set r := ‖z‖ with hr
  have hr0 : 0 < r := by linarith
  have hlog : 0 < Real.log r := Real.log_pos (by linarith)
  -- `|∫ μ/(ζ(ζ − 1)(ζ − z))| ≤ kb ∫ 1/(|ζ||ζ − 1||ζ − z|) ≤ kb C₂ log r / r`
  have hint : ‖∫ ζ, μ ζ / (ζ * (ζ - 1) * (ζ - z))‖ ≤ kb * (C₂ * Real.log r / r) := by
    refine (norm_integral_le_lintegral_norm _).trans ?_
    have h1 : ∫⁻ ζ, ENNReal.ofReal ‖μ ζ / (ζ * (ζ - 1) * (ζ - z))‖ ≤
        ENNReal.ofReal kb * ∫⁻ ζ, ENNReal.ofReal ((‖ζ‖ * ‖ζ - 1‖ * ‖ζ - z‖)⁻¹) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [hμb] with ζ hζ
      rw [← ENNReal.ofReal_mul hkb0, norm_div, norm_mul, norm_mul, div_eq_mul_inv]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hζ.trans hkbk) (by positivity))
    have h2 := h1.trans (mul_le_mul_right (hJ z hz) _)
    rw [← ENNReal.ofReal_mul hkb0] at h2
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h2
  unfold normalizedCauchyTOn
  rw [Measure.restrict_univ, norm_mul, norm_neg, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, ← hr]
  have hz1 : ‖z - 1‖ ≤ 2 * r := by
    have := norm_sub_le z 1
    rw [norm_one] at this
    linarith
  calc r * ‖z - 1‖ / π * ‖∫ ζ, μ ζ / (ζ * (ζ - 1) * (ζ - z))‖
      ≤ r * (2 * r) / π * (kb * (C₂ * Real.log r / r)) := by
        gcongr
    _ = 2 * kb * C₂ / π * r * Real.log r := by
        field_simp

/-- **Theorem 7** (§3.4, l. 2511), (3). `|V_μ(z) − V_μ(t)| ≤ C |z − t| log |z − t|⁻¹` for `|z|, |t| < R`,
`|z − t| < 1/2`, `C` depending only on `R` and `‖μ‖∞`. -/
theorem thm3_7_c (k R : ℝ) :
    ∃ C : ℝ, ∀ μ : ℂ → ℂ, IsBeltramiCoeff μ univ k → ∀ z t : ℂ, ‖z‖ < R → ‖t‖ < R → ‖z - t‖ < 1 / 2 →
      ‖normalizedCauchyTOn univ μ z - normalizedCauchyTOn univ μ t‖ ≤ C * ‖z - t‖ * Real.log ‖z - t‖⁻¹ := by
  obtain ⟨B, hB, hK⟩ := gl3_kernel_diff_bound R
  obtain ⟨kb, hkb0, hkbk⟩ : ∃ kb : ℝ, 0 ≤ kb ∧ k ≤ kb := ⟨max k 0, le_max_right _ _, le_max_left _ _⟩
  refine ⟨kb * B / π, fun μ hμ z t hz ht hδ => ?_⟩
  obtain ⟨hμm, hμb⟩ := hμ
  rw [Measure.restrict_univ] at hμm hμb
  have hμb' : ∀ᵐ ζ ∂volume, ‖μ ζ‖ ≤ kb := hμb.mono fun ζ h => h.trans hkbk
  rcases eq_or_ne z t with rfl | hzt
  · simp
  have hδ0 : 0 < ‖z - t‖ := norm_pos_iff.2 (sub_ne_zero.2 hzt)
  have hL : 0 < Real.log ‖z - t‖⁻¹ := Real.log_pos (one_lt_inv_iff₀.2 ⟨hδ0, by linarith⟩)
  have hV : ∀ w, normalizedCauchyTOn univ μ w =
      -(1 / π : ℂ) * ∫ ζ, w * (w - 1) * (μ ζ / (ζ * (ζ - 1) * (ζ - w))) := by
    intro w
    unfold normalizedCauchyTOn
    rw [Measure.restrict_univ, integral_const_mul]
    ring
  rw [hV z, hV t, ← mul_sub, ← integral_sub (gl3_kernel_integrable hμm hμb' z) (gl3_kernel_integrable hμm hμb' t),
    norm_mul, norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  -- `|∫ μ (K_z − K_t)| ≤ kb ∫ |K_z − K_t| ≤ kb B δ log(1/δ)`
  have hint : ‖∫ ζ, (z * (z - 1) * (μ ζ / (ζ * (ζ - 1) * (ζ - z))) - t * (t - 1) * (μ ζ / (ζ * (ζ - 1) * (ζ - t))))‖ ≤
      kb * (B * ‖z - t‖ * Real.log ‖z - t‖⁻¹) := by
    refine (norm_integral_le_lintegral_norm _).trans ?_
    have h1 : ∫⁻ ζ, ENNReal.ofReal ‖z * (z - 1) * (μ ζ / (ζ * (ζ - 1) * (ζ - z))) -
        t * (t - 1) * (μ ζ / (ζ * (ζ - 1) * (ζ - t)))‖ ≤ ENNReal.ofReal kb * ∫⁻ ζ,
          ENNReal.ofReal ‖z * (z - 1) / (ζ * (ζ - 1) * (ζ - z)) - t * (t - 1) / (ζ * (ζ - 1) * (ζ - t))‖ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [hμb'] with ζ hζ
      rw [← ENNReal.ofReal_mul hkb0]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [show z * (z - 1) * (μ ζ / (ζ * (ζ - 1) * (ζ - z))) - t * (t - 1) * (μ ζ / (ζ * (ζ - 1) * (ζ - t))) =
        μ ζ * (z * (z - 1) / (ζ * (ζ - 1) * (ζ - z)) - t * (t - 1) / (ζ * (ζ - 1) * (ζ - t))) by ring, norm_mul]
      exact mul_le_mul_of_nonneg_right hζ (norm_nonneg _)
    have h2 := h1.trans (mul_le_mul_right (hK z t hz ht hδ0 hδ) _)
    rw [← ENNReal.ofReal_mul hkb0] at h2
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h2
  calc 1 / π * ‖∫ ζ, (z * (z - 1) * (μ ζ / (ζ * (ζ - 1) * (ζ - z))) - t * (t - 1) * (μ ζ / (ζ * (ζ - 1) * (ζ - t))))‖
      ≤ 1 / π * (kb * (B * ‖z - t‖ * Real.log ‖z - t‖⁻¹)) := by gcongr
    _ = kb * B / π * ‖z - t‖ * Real.log ‖z - t‖⁻¹ := by ring

/-- **Theorem 7** (§3.4, l. 2511), (4), in the form (3.23). `∂̄V_μ = μ` in the sense of distributions:
`∬ V ∂̄f = −∬ μ f` for every test function `f`. -/
theorem thm3_7_d {μ : ℂ → ℂ} (hμ : ∃ k : ℝ, IsBeltramiCoeff μ univ k) {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    ∫ z, normalizedCauchyTOn univ μ z * dzbar f z = -∫ z, μ z * f z := by
  classical
  obtain ⟨k, hμm, hμb⟩ := hμ
  rw [Measure.restrict_univ] at hμm hμb
  -- a bounded, strongly measurable version `ν` of `μ`
  set μm := hμm.mk μ with hμmdef
  have hμm_sm : StronglyMeasurable μm := hμm.stronglyMeasurable_mk
  have hμeq : μ =ᵐ[volume] μm := hμm.ae_eq_mk
  set kb := max k 0 with hkb
  set ν : ℂ → ℂ := fun ζ => if ‖μm ζ‖ ≤ kb then μm ζ else 0 with hνdef
  have hνm : StronglyMeasurable ν :=
    StronglyMeasurable.ite (measurableSet_le hμm_sm.measurable.norm measurable_const) hμm_sm
      stronglyMeasurable_const
  have hνb : ∀ ζ, ‖ν ζ‖ ≤ kb := by
    intro ζ
    simp only [hνdef]
    split_ifs with h
    · exact h
    · rw [norm_zero]
      exact le_max_right _ _
  have hμν : μ =ᵐ[volume] ν := by
    filter_upwards [hμeq, hμb] with ζ h1 h2
    have hc : ‖μm ζ‖ ≤ kb := by rw [← h1]; exact h2.trans (le_max_left _ _)
    simp only [hνdef, hc, ↓reduceIte]
    exact h1
  have hV : ∀ z, normalizedCauchyTOn univ μ z = normalizedCauchyTOn univ ν z := by
    intro z
    unfold normalizedCauchyTOn
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hμν] with ζ hζ
    rw [hζ]
  have hR : ∫ z, μ z * f z = ∫ z, ν z * f z := integral_congr_ae (hμν.mono fun ζ h => by simp only [h])
  simp only [hV]
  rw [hR]
  -- the support of `f` and the function `h = z(z − 1) ∂̄f`
  obtain ⟨R₀, hR₀⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set R := max R₀ 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hR0 : 0 < R := by linarith
  have hfz : ∀ z, R < ‖z‖ → z ∉ tsupport f := by
    intro z hz hmem
    have := mem_closedBall_zero_iff.1 (hR₀ hmem)
    have := le_max_left R₀ 1
    linarith
  have hdf0 : ∀ z, R < ‖z‖ → dzbar f z = 0 := by
    intro z hz
    have h := hfz z hz
    show (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2 = 0
    rw [LiZhongQC.sp_fderiv_eq_zero_of_notMem_tsupport h 1, LiZhongQC.sp_fderiv_eq_zero_of_notMem_tsupport h I]
    ring
  have hdfc : Continuous (dzbar f) := by
    have hc := hf.continuous_fderiv (by simp)
    show Continuous fun z => (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2
    exact ((hc.clm_apply continuous_const).add (continuous_const.mul (hc.clm_apply continuous_const))).div_const 2
  set h : ℂ → ℂ := fun z => z * (z - 1) * dzbar f z with hhdef
  have hhc : Continuous h := by fun_prop
  have hh0 : ∀ z, R < ‖z‖ → h z = 0 := fun z hz => by rw [hhdef]; simp only [hdf0 z hz, mul_zero]
  have hhcs : HasCompactSupport h := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) fun z hz => hh0 z ?_
    rw [mem_closedBall_zero_iff, not_le] at hz
    exact hz
  obtain ⟨M, hM⟩ := hhc.bounded_above_of_compact_support hhcs
  set M' := max M 0 with hM'
  have hM'b : ∀ z, ‖h z‖ ≤ M' := fun z => (hM z).trans (le_max_left _ _)
  -- the kernel on `ℂ × ℂ`
  set G : ℂ × ℂ → ℂ := fun p => h p.1 * (ν p.2 / (p.2 * (p.2 - 1) * (p.2 - p.1))) with hGdef
  have hGmeas : Measurable G :=
    (hhc.measurable.comp measurable_fst).mul ((hνm.measurable.comp measurable_snd).div
      ((measurable_snd.mul (measurable_snd.sub_const 1)).mul (measurable_snd.sub measurable_fst)))
  have hptG : ∀ z ζ, G (z, ζ) = -(ν ζ / (ζ * (ζ - 1))) * (h z / (z - ζ)) := by
    intro z ζ
    simp only [hGdef]
    rw [show z - ζ = -(ζ - z) by ring, div_neg, neg_mul_neg, div_mul_eq_div_div]
    ring
  -- the identity `∬ V(z) ∂̄f(z) = -(1/π) ∬∬ G`
  have hLHS : ∫ z, normalizedCauchyTOn univ ν z * dzbar f z = -(1 / π : ℂ) * ∫ z, ∫ ζ, G (z, ζ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show normalizedCauchyTOn univ ν z * dzbar f z = -(1 / π : ℂ) * ∫ ζ, G (z, ζ)
    unfold normalizedCauchyTOn
    rw [Measure.restrict_univ]
    simp only [hGdef, hhdef]
    rw [integral_const_mul]
    ring
  -- inner integrals in `z`: Pompeiu
  have hinner : ∀ ζ, ζ ≠ 0 → ζ ≠ 1 → ∫ z, G (z, ζ) = π * (ν ζ * f ζ) := by
    intro ζ h0 h1
    simp only [hptG]
    rw [integral_const_mul]
    have hP := gl3_pompeiu_poly hf hfc ζ
    simp only [hhdef]
    rw [hP]
    have h1' : ζ - 1 ≠ 0 := sub_ne_zero.2 h1
    field_simp
  -- integrability of `G` on `ℂ × ℂ`
  have hGint : Integrable G (volume.prod volume) := by
    rw [integrable_prod_iff' hGmeas.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun ζ => ?_, ?_⟩
    · have h1 := ((LiZhongQC.integrable_div_sub_of_hasCompactSupport hhc hhcs ζ).const_mul
        (-(ν ζ / (ζ * (ζ - 1)))))
      exact h1.congr (Eventually.of_forall fun z => (hptG z ζ).symm)
    · -- `∬ |G(z, ζ)| dz ≤` an integrable function of `ζ`
      set C₀ : ℝ≥0∞ := ENNReal.ofReal M' * ((∫⁻ w in ball (0 : ℂ) R, ‖w‖ₑ ^ (-(1 : ℝ))) +
        ENNReal.ofReal (R ^ (-(1 : ℝ))) * volume (closedBall (0 : ℂ) R)) with hC₀
      have hC₀fin : C₀ ≠ ⊤ := by
        refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨?_, ?_⟩)
        · exact LiZhongQC.lintegral_ball_enorm_rpow_neg_ne_top zero_le_one one_lt_two R
        · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
      set C₁ := C₀.toReal with hC₁
      have hΦ : ∀ ζ, ∫ z, ‖h z / (z - ζ)‖ ≤ C₁ := by
        intro ζ
        rw [integral_norm_eq_lintegral_enorm (f := fun z => h z / (z - ζ))
          ((hhc.measurable.div (measurable_id.sub_const ζ)).aestronglyMeasurable)]
        exact ENNReal.toReal_mono hC₀fin (gl3_kernel_uniform hR0 hM'b hh0 ζ)
      set vB := volume.real (closedBall (0 : ℂ) R) with hvB
      have hΦfar : ∀ ζ, 2 * R ≤ ‖ζ‖ → ∫ z, ‖h z / (z - ζ)‖ ≤ M' * (2 / ‖ζ‖) * vB := by
        intro ζ hζ
        have hζ0 : 0 < ‖ζ‖ := by linarith
        have hpt : ∀ z, ‖h z / (z - ζ)‖ ≤ (closedBall (0 : ℂ) R).indicator (fun _ => M' * (2 / ‖ζ‖)) z := by
          intro z
          by_cases hz : z ∈ closedBall (0 : ℂ) R
          · rw [indicator_of_mem hz, norm_div]
            have hzR : ‖z‖ ≤ R := mem_closedBall_zero_iff.1 hz
            have hd : ‖ζ‖ / 2 ≤ ‖z - ζ‖ := by
              have := norm_sub_norm_le ζ z
              rw [norm_sub_rev] at this
              linarith
            have hdpos : 0 < ‖z - ζ‖ := by linarith
            rw [div_le_iff₀ hdpos]
            calc ‖h z‖ ≤ M' := hM'b z
              _ = M' * (2 / ‖ζ‖) * (‖ζ‖ / 2) := by field_simp
              _ ≤ M' * (2 / ‖ζ‖) * ‖z - ζ‖ := by gcongr
          · rw [indicator_of_notMem hz, hh0 z (by simpa using hz), zero_div, norm_zero]
        refine (integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _)
          ((integrable_indicator_iff measurableSet_closedBall).2
            (integrableOn_const measure_closedBall_lt_top.ne)) (Eventually.of_forall hpt)).trans (le_of_eq ?_)
        rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, hvB]
        ring
      -- the dominating function
      set ρ := 2 * R with hρ
      set D : ℂ → ℝ := fun ζ => kb * C₁ * (ball (0 : ℂ) (ρ + 1)).indicator (fun ζ => ‖ζ‖⁻¹ + ‖ζ - 1‖⁻¹) ζ +
        kb * (M' * 2 * vB) * 2 * 8 * (1 + ‖ζ‖) ^ (-(3 : ℝ)) with hD
      have hDint : Integrable D := by
        refine Integrable.add (Integrable.const_mul ?_ _) (Integrable.const_mul ?_ _)
        · refine (integrable_indicator_iff measurableSet_ball).2 ?_
          have h1 := (LiZhongQC.integrableOn_cauchy_kernel_ball (by linarith : (0 : ℝ) < ρ + 1) 0).norm
          have h2 := (LiZhongQC.integrableOn_cauchy_kernel_ball (by linarith : (0 : ℝ) < ρ + 1) 1).norm
          refine IntegrableOn.congr_fun (h1.add h2) (fun ζ _ => ?_) measurableSet_ball
          simp only [Pi.add_apply, sub_zero, one_div, norm_inv]
        · exact integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
      refine Integrable.mono' hDint ((hGmeas.stronglyMeasurable.norm.integral_prod_left').aestronglyMeasurable)
        (Eventually.of_forall fun ζ => ?_)
      have hnorm : ∀ z, ‖G (z, ζ)‖ = ‖ν ζ / (ζ * (ζ - 1))‖ * ‖h z / (z - ζ)‖ := by
        intro z
        rw [hptG z ζ, norm_mul, norm_neg]
      simp only [hnorm]
      rw [integral_const_mul, Real.norm_of_nonneg (by positivity)]
      have hΦ0 : 0 ≤ ∫ z, ‖h z / (z - ζ)‖ := integral_nonneg fun z => norm_nonneg _
      have hC₁0 : 0 ≤ C₁ := ENNReal.toReal_nonneg
      have hvB0 : 0 ≤ vB := measureReal_nonneg
      have hkb0 : 0 ≤ kb := le_max_right _ _
      have hM'0 : 0 ≤ M' := le_max_right _ _
      have hD0 : 0 ≤ kb * C₁ * (ball (0 : ℂ) (ρ + 1)).indicator (fun ζ => ‖ζ‖⁻¹ + ‖ζ - 1‖⁻¹) ζ :=
        mul_nonneg (by positivity) (indicator_nonneg (fun ζ _ => by positivity) _)
      have hD1 : 0 ≤ kb * (M' * 2 * vB) * 2 * 8 * (1 + ‖ζ‖) ^ (-(3 : ℝ)) := by positivity
      have hDnn : 0 ≤ D ζ := by rw [hD]; exact add_nonneg hD0 hD1
      by_cases hζ0 : ζ = 0
      · have h00 : ‖ν ζ / (ζ * (ζ - 1))‖ = 0 := by rw [hζ0]; simp
        rw [h00, zero_mul]
        exact hDnn
      by_cases hζ1 : ζ = 1
      · have h00 : ‖ν ζ / (ζ * (ζ - 1))‖ = 0 := by rw [hζ1]; simp
        rw [h00, zero_mul]
        exact hDnn
      have ha : 0 < ‖ζ‖ := norm_pos_iff.2 hζ0
      have hb : 0 < ‖ζ - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hζ1)
      have hνζ : ‖ν ζ / (ζ * (ζ - 1))‖ ≤ kb * (‖ζ‖ * ‖ζ - 1‖)⁻¹ := by
        rw [norm_div, norm_mul, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (hνb ζ) (by positivity)
      by_cases hnear : ‖ζ‖ < ρ + 1
      · -- near: `1/(|ζ||ζ − 1|) ≤ 1/|ζ| + 1/|ζ − 1|` and the uniform bound
        have hmem : ζ ∈ ball (0 : ℂ) (ρ + 1) := mem_ball_zero_iff.2 hnear
        have hsplit : (‖ζ‖ * ‖ζ - 1‖)⁻¹ ≤ ‖ζ‖⁻¹ + ‖ζ - 1‖⁻¹ := by
          have h1 : 1 ≤ ‖ζ‖ + ‖ζ - 1‖ := by
            have := norm_sub_le ζ (ζ - 1)
            rw [sub_sub_cancel, norm_one] at this
            linarith
          rw [inv_le_iff_one_le_mul₀ (by positivity), add_mul, inv_mul_cancel_left₀ ha.ne',
            mul_comm ‖ζ‖ ‖ζ - 1‖, inv_mul_cancel_left₀ hb.ne']
          linarith
        calc ‖ν ζ / (ζ * (ζ - 1))‖ * ∫ z, ‖h z / (z - ζ)‖ ≤ kb * (‖ζ‖ * ‖ζ - 1‖)⁻¹ * C₁ :=
              mul_le_mul hνζ (hΦ ζ) hΦ0 (by positivity)
          _ ≤ kb * (‖ζ‖⁻¹ + ‖ζ - 1‖⁻¹) * C₁ := by gcongr
          _ = kb * C₁ * (ball (0 : ℂ) (ρ + 1)).indicator (fun ζ => ‖ζ‖⁻¹ + ‖ζ - 1‖⁻¹) ζ := by
              rw [indicator_of_mem hmem]
              ring
          _ ≤ D ζ := by rw [hD]; linarith
      · -- far: `|ζ − 1| ≥ |ζ|/2`, `∬ |h|/|z − ζ| ≤ 2M′ vol/|ζ|`, and `|ζ|⁻³ ≤ 8 (1 + |ζ|)⁻³`
        rw [not_lt] at hnear
        have hfar : 2 * R ≤ ‖ζ‖ := by linarith
        have hζ1' : ‖ζ‖ / 2 ≤ ‖ζ - 1‖ := by
          have := norm_sub_norm_le ζ 1
          rw [norm_one] at this
          linarith
        have h3 : ‖ζ‖⁻¹ ^ 3 ≤ 8 * (1 + ‖ζ‖) ^ (-(3 : ℝ)) := by
          have hpos : 0 < 1 + ‖ζ‖ := by positivity
          rw [Real.rpow_neg hpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow,
            ← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
          have h4 : (1 + ‖ζ‖) ≤ 2 * ‖ζ‖ := by linarith
          calc (1 + ‖ζ‖) ^ 3 ≤ (2 * ‖ζ‖) ^ 3 := pow_le_pow_left₀ hpos.le h4 3
            _ = 8 * ‖ζ‖ ^ 3 := by ring
        have hkerfar := hΦfar ζ hfar
        have hνfar : ‖ν ζ / (ζ * (ζ - 1))‖ ≤ kb * (2 * ‖ζ‖⁻¹ ^ 2) := by
          refine hνζ.trans (mul_le_mul_of_nonneg_left ?_ hkb0)
          rw [mul_inv, sq]
          have : ‖ζ - 1‖⁻¹ ≤ 2 * ‖ζ‖⁻¹ := by
            rw [inv_le_iff_one_le_mul₀ hb]
            have := mul_le_mul_of_nonneg_left hζ1' (by positivity : (0 : ℝ) ≤ 2 * ‖ζ‖⁻¹)
            rw [show 2 * ‖ζ‖⁻¹ * (‖ζ‖ / 2) = 1 by field_simp] at this
            linarith
          nlinarith [inv_pos.2 ha]
        calc ‖ν ζ / (ζ * (ζ - 1))‖ * ∫ z, ‖h z / (z - ζ)‖
            ≤ kb * (2 * ‖ζ‖⁻¹ ^ 2) * (M' * (2 / ‖ζ‖) * vB) := mul_le_mul hνfar hkerfar hΦ0 (by positivity)
          _ = kb * (M' * 2 * vB) * 2 * ‖ζ‖⁻¹ ^ 3 := by field_simp
          _ ≤ kb * (M' * 2 * vB) * 2 * (8 * (1 + ‖ζ‖) ^ (-(3 : ℝ))) := by gcongr
          _ ≤ D ζ := by rw [hD]; linarith
  -- Fubini and the inner Pompeiu integrals
  rw [hLHS, integral_integral_swap (f := fun z ζ => G (z, ζ)) hGint]
  have hae : ∀ᵐ ζ : ℂ, ζ ≠ 0 ∧ ζ ≠ 1 := by
    have h0 : ∀ᵐ ζ : ℂ, ζ ≠ 0 := by
      rw [ae_iff]
      simp
    have h1 : ∀ᵐ ζ : ℂ, ζ ≠ 1 := by
      rw [ae_iff]
      simp
    filter_upwards [h0, h1] with ζ a b
    exact ⟨a, b⟩
  rw [integral_congr_ae (hae.mono fun ζ hζ => hinner ζ hζ.1 hζ.2), integral_const_mul]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  field_simp

end GardinerLakic2000
