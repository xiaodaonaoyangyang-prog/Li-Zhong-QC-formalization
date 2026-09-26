import LiZhongQC.Ch01.S09_AnalyticProperties

/-!
# §10 拟共形映射的分析定义 — The analytic definition of quasiconformal mappings

* Theorem 10.1 (A.C.L. + dilatation inequality a.e. ⇔ `K`-q.c.)  — `thm10_1_isKQC_iff` (in S13)
* the A.C.L. condition cannot be dropped                        — `acl_not_removable`
* Definition 10.1 (complex characteristic and maximal dilatation of a q.c. map)
                                                                 — `maxDilatation`
* `L₂` generalized homeomorphic solutions of the Beltrami equation — `IsGenHomeoSolution`
* Theorem 10.2 (q.c. maps = generalized homeomorphic solutions)   — `thm10_2_*` ((⇐) and ⇔ in S13)

Theorem 10.1, Theorem 10.2 (⇐) and the ⇔ form are stated and proved at the END of
`Ch02/S13_Representation.lean` (moved there 2026-09-24, statements unchanged): their proof compares with the
Theorem 12.2 solution through the similarity principle of §13.2, which is what supplies the orientation
that the book's proof leaves implicit.  No file between S10 and S13 uses them.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace LiZhongQC

/-! ### The remark after Theorem 10.1 — helpers -/

/-- The ternary-digit map `b ↦ Σ 2 b_n / 3^(n+1)` from coin-toss sequences to the Cantor set. -/
def anN_T (b : ℕ → Bool) : ℝ := Real.ofDigits (fun i => cond (b i) (2 : Fin 3) 0)

/-- `anN_T` is continuous. -/
theorem anN_T_continuous : Continuous anN_T := by
  unfold anN_T
  exact Real.continuous_ofDigits.comp
    (continuous_pi fun i =>
      (continuous_of_discreteTopology (f := fun x : Bool => cond x (2 : Fin 3) 0)).comp
        (continuous_apply i))

/-- `anN_T` is injective (ternary expansions with digits `0, 2` are unique). -/
theorem anN_T_injective : Function.Injective anN_T := by
  intro a b h
  have hne : ∀ (c : ℕ → Bool) (n : ℕ), (fun i => cond (c i) (2 : Fin 3) 0) n ≠ 1 := by
    intro c n
    dsimp only
    cases c n <;> decide
  have h2 := ofDigits_zero_two_sequence_unique (hne a) (hne b) h
  funext n
  have hn := congrFun h2 n
  cases ha : a n <;> cases hb : b n <;> simp_all

/-- `anN_T` takes values in the Cantor set. -/
theorem anN_T_mem (b : ℕ → Bool) : anN_T b ∈ cantorSet :=
  ofDigits_bool_to_fin_three_mem_cantorSet b

/-- The fair coin-toss product measure has no atoms. -/
theorem anN_P_singleton (b : ℕ → Bool) :
    Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure) {b} = 0 := by
  rw [Measure.infinitePi_singleton]
  have h1 : ∀ i : ℕ, (PMF.uniformOfFintype Bool).toMeasure {b i} = 2⁻¹ := by
    intro i
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply]
    simp
  simp_rw [h1]
  rw [ENNReal.tprod_eq_iInf_prod (fun _ => by norm_num)]
  refine le_antisymm ?_ zero_le
  have ht : Tendsto (fun n : ℕ => (2⁻¹ : ℝ≥0∞) ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  refine ge_of_tendsto' ht (fun n => ?_)
  refine (iInf_le _ (Finset.range n)).trans ?_
  simp

/-- The Cantor measure: the image of the fair coin-toss measure under `anN_T`. -/
def anN_nu : Measure ℝ :=
  (Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)).map anN_T

/-- The Cantor measure is a probability measure. -/
theorem anN_nu_isProb : IsProbabilityMeasure anN_nu := by
  unfold anN_nu
  infer_instance

/-- Evaluation of the Cantor measure on a measurable set. -/
theorem anN_nu_apply {s : Set ℝ} (hs : MeasurableSet s) :
    anN_nu s = Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)
      (anN_T ⁻¹' s) :=
  Measure.map_apply anN_T_continuous.measurable hs

/-- The Cantor measure has no atoms. -/
theorem anN_nu_singleton (x : ℝ) : anN_nu {x} = 0 := by
  rw [anN_nu_apply (measurableSet_singleton x)]
  have hs : (anN_T ⁻¹' {x}).Subsingleton := fun a ha b hb => anN_T_injective (ha.trans hb.symm)
  rcases hs.eq_empty_or_singleton with h | ⟨b, h⟩
  · rw [h, measure_empty]
  · rw [h, anN_P_singleton]

/-- The Cantor measure is carried by the Cantor set. -/
theorem anN_nu_compl_cantorSet : anN_nu cantorSetᶜ = 0 := by
  rw [anN_nu_apply isClosed_cantorSet.measurableSet.compl]
  have : anN_T ⁻¹' cantorSetᶜ = ∅ := by
    ext b
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact anN_T_mem b
  rw [this, measure_empty]

/-- The Cantor function: the distribution function of the Cantor measure. -/
def anN_F (x : ℝ) : ℝ := ProbabilityTheory.cdf anN_nu x

/-- `anN_F x = ν(-∞, x]`. -/
theorem anN_F_eq (x : ℝ) : anN_F x = (anN_nu (Iic x)).toReal := by
  have := anN_nu_isProb
  unfold anN_F
  rw [ProbabilityTheory.cdf_eq_real]
  rfl

/-- The Cantor function is monotone. -/
theorem anN_F_monotone : Monotone anN_F := ProbabilityTheory.monotone_cdf anN_nu

/-- The Cantor function takes values in `[0, 1]`. -/
theorem anN_F_mem (x : ℝ) : 0 ≤ anN_F x ∧ anN_F x ≤ 1 :=
  ⟨ProbabilityTheory.cdf_nonneg anN_nu x, ProbabilityTheory.cdf_le_one anN_nu x⟩

/-- The Cantor function is continuous (the Cantor measure has no atoms). -/
theorem anN_F_continuous : Continuous anN_F := by
  have := anN_nu_isProb
  rw [continuous_iff_continuousAt]
  intro x
  have hm : (ProbabilityTheory.cdf anN_nu).measure {x} = 0 := by
    rw [ProbabilityTheory.measure_cdf]
    exact anN_nu_singleton x
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hm
  have hle := (ProbabilityTheory.monotone_cdf anN_nu).leftLim_le (le_refl x)
  have hl : Function.leftLim (ProbabilityTheory.cdf anN_nu) x = ProbabilityTheory.cdf anN_nu x := by
    linarith
  exact ((ProbabilityTheory.monotone_cdf anN_nu).continuousAt_iff_leftLim_eq_rightLim).2
    (by rw [hl, StieltjesFunction.rightLim_eq])

/-- `anN_F 0 = 0`. -/
theorem anN_F_zero : anN_F 0 = 0 := by
  have h0 : Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)
      (anN_T ⁻¹' {0}) = 0 := by
    rw [← anN_nu_apply (measurableSet_singleton 0)]
    exact anN_nu_singleton 0
  have hsub : anN_T ⁻¹' Iic 0 ⊆ anN_T ⁻¹' {0} := fun b hb =>
    le_antisymm hb (Real.ofDigits_nonneg _)
  rw [anN_F_eq, anN_nu_apply measurableSet_Iic, measure_mono_null hsub h0]
  simp

/-- `anN_F 1 = 1`. -/
theorem anN_F_one : anN_F 1 = 1 := by
  rw [anN_F_eq, anN_nu_apply measurableSet_Iic]
  have : anN_T ⁻¹' Iic 1 = univ := eq_univ_of_forall fun b => Real.ofDigits_le_one _
  rw [this, measure_univ]
  simp

/-- The Cantor function is constant on intervals avoiding the Cantor set. -/
theorem anN_F_eq_of_Ioc {x y : ℝ} (hxy : x ≤ y) (h : Ioc x y ⊆ cantorSetᶜ) :
    anN_F y = anN_F x := by
  rw [anN_F_eq, anN_F_eq]
  congr 1
  have h0 : anN_nu (Ioc x y) = 0 := measure_mono_null h anN_nu_compl_cantorSet
  rw [← Iic_union_Ioc_eq_Iic hxy]
  apply le_antisymm
  · calc anN_nu (Iic x ∪ Ioc x y) ≤ anN_nu (Iic x) + anN_nu (Ioc x y) := measure_union_le _ _
      _ = anN_nu (Iic x) := by rw [h0, add_zero]
  · exact measure_mono subset_union_left

/-- Off the Cantor set, the Cantor function is locally constant. -/
theorem anN_F_eventually_const {x : ℝ} (hx : x ∉ cantorSet) :
    ∀ᶠ y in 𝓝 x, anN_F y = anN_F x := by
  have ho : IsOpen cantorSetᶜ := isClosed_cantorSet.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 ho x hx
  filter_upwards [ball_mem_nhds x hε] with y hy
  rw [mem_ball, Real.dist_eq] at hy
  rcases le_total x y with hxy | hyx
  · refine anN_F_eq_of_Ioc hxy (fun t ht => hball ?_)
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, abs_lt.1 hy]
  · refine (anN_F_eq_of_Ioc hyx (fun t ht => hball ?_)).symm
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, abs_lt.1 hy]

/-- The `n`-th stage of the Cantor construction has measure at most `(2/3)^n`. -/
theorem anN_volume_preCantorSet (n : ℕ) :
    volume (preCantorSet n) ≤ ENNReal.ofReal ((2 / 3 : ℝ) ^ n) := by
  induction n with
  | zero => simp [Real.volume_Icc]
  | succ n ih =>
    rw [preCantorSet_succ]
    have e1 : (fun x : ℝ => x / 3) = AffineMap.homothety (0 : ℝ) (1 / 3 : ℝ) := by
      funext x
      simp [AffineMap.homothety_apply]
      ring
    have e2 : (fun x : ℝ => (2 + x) / 3) = AffineMap.homothety (1 : ℝ) (1 / 3 : ℝ) := by
      funext x
      simp [AffineMap.homothety_apply]
      ring
    have hv : ∀ c : ℝ, volume (AffineMap.homothety c (1 / 3 : ℝ) '' preCantorSet n) =
        ENNReal.ofReal (1 / 3) * volume (preCantorSet n) := by
      intro c
      rw [Measure.addHaar_image_homothety]
      simp [Module.finrank_self]
    calc volume ((fun x : ℝ => x / 3) '' preCantorSet n ∪
          (fun x : ℝ => (2 + x) / 3) '' preCantorSet n)
        ≤ volume ((fun x : ℝ => x / 3) '' preCantorSet n) +
          volume ((fun x : ℝ => (2 + x) / 3) '' preCantorSet n) := measure_union_le _ _
      _ = ENNReal.ofReal (1 / 3) * volume (preCantorSet n) +
          ENNReal.ofReal (1 / 3) * volume (preCantorSet n) := by rw [e1, e2, hv, hv]
      _ ≤ ENNReal.ofReal (1 / 3) * ENNReal.ofReal ((2 / 3 : ℝ) ^ n) +
          ENNReal.ofReal (1 / 3) * ENNReal.ofReal ((2 / 3 : ℝ) ^ n) := by gcongr
      _ = ENNReal.ofReal ((2 / 3 : ℝ) ^ (n + 1)) := by
        rw [← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- The Cantor set is Lebesgue-null. -/
theorem anN_volume_cantorSet : volume cantorSet = 0 := by
  refine le_antisymm ?_ zero_le
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal ((2 / 3 : ℝ) ^ n)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  exact ge_of_tendsto' ht fun n =>
    (measure_mono (iInter_subset _ n)).trans (anN_volume_preCantorSet n)

/-- A continuous monotone function, locally constant off a closed Lebesgue-null set, with
`F 0 = 0` and `F 1 = 1` (the Cantor function). -/
theorem anN_cantor_function : ∃ F : ℝ → ℝ, Continuous F ∧ Monotone F ∧ F 0 = 0 ∧ F 1 = 1 ∧
    (∀ x, 0 ≤ F x ∧ F x ≤ 1) ∧ ∃ C : Set ℝ, IsClosed C ∧ volume C = 0 ∧
      ∀ x ∉ C, ∀ᶠ y in 𝓝 x, F y = F x :=
  ⟨anN_F, anN_F_continuous, anN_F_monotone, anN_F_zero, anN_F_one, anN_F_mem, cantorSet,
    isClosed_cantorSet, anN_volume_cantorSet, fun _ hx => anN_F_eventually_const hx⟩

/-- For a continuous monotone bounded `F`, `z ↦ (Re z + F(Re z)) + i Im z` is a homeomorphism of
the plane onto itself. -/
theorem anN_homeo (F : ℝ → ℝ) (hFc : Continuous F) (hFm : Monotone F)
    (hFb : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    IsHomeomorphOnto (fun z : ℂ => (((z.re + F z.re : ℝ)) : ℂ) + (z.im : ℂ) * I) univ univ := by
  set f : ℂ → ℂ := fun z => (((z.re + F z.re : ℝ)) : ℂ) + (z.im : ℂ) * I with hf
  have hgc : Continuous (fun x : ℝ => x + F x) := continuous_id.add hFc
  have hgs : StrictMono (fun x : ℝ => x + F x) := strictMono_id.add_monotone hFm
  have hgsurj : Function.Surjective (fun x : ℝ => x + F x) := by
    refine hgc.surjective ?_ ?_
    · exact tendsto_atTop_mono (fun x => le_add_of_nonneg_right (hFb x).1) tendsto_id
    · exact tendsto_atBot_mono (fun x => add_le_add_right (hFb x).2 x)
        (tendsto_atBot_add_const_right _ 1 tendsto_id)
  have hfc : Continuous f := by
    rw [hf]
    fun_prop
  have hfi : Function.Injective f := by
    intro z w h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [hf] at hre him
    exact Complex.ext (hgs.injective hre) him
  have hfs : Function.Surjective f := by
    intro w
    obtain ⟨x, hx⟩ := hgsurj w.re
    refine ⟨(x : ℂ) + (w.im : ℂ) * I, ?_⟩
    apply Complex.ext <;> simp [hf, hx]
  have := qcl_f_isHomeomorphOnto_of_injOn isOpen_univ hfc.continuousOn hfi.injOn
  rwa [image_univ_of_surjective hfs] at this

/-- Where `F` is locally constant, `z ↦ (Re z + F(Re z)) + i Im z` has derivative the identity. -/
theorem anN_hasFDerivAt (F : ℝ → ℝ) {z : ℂ} (h : ∀ᶠ y in 𝓝 z.re, F y = F z.re) :
    HasFDerivAt (fun z : ℂ => (((z.re + F z.re : ℝ)) : ℂ) + (z.im : ℂ) * I)
      (ContinuousLinearMap.id ℝ ℂ) z := by
  have h1 : (fun w : ℂ => (((w.re + F w.re : ℝ)) : ℂ) + (w.im : ℂ) * I) =ᶠ[𝓝 z]
      fun w => w + (F z.re : ℂ) := by
    have : ∀ᶠ w in 𝓝 z, F w.re = F z.re :=
      Complex.continuous_re.continuousAt.tendsto.eventually h
    filter_upwards [this] with w hw
    apply Complex.ext <;> simp [hw]
  have h2 : HasFDerivAt (fun w : ℂ => w + (F z.re : ℂ)) (ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).add_const _
  exact h2.congr_of_eventuallyEq h1

/-- If `f` has derivative the identity at `z`, then `∂_z f = 1` and `∂_{z̄} f = 0` there. -/
theorem anN_dz_dzbar {f : ℂ → ℂ} {z : ℂ} (h : HasFDerivAt f (ContinuousLinearMap.id ℝ ℂ) z) :
    dz f z = 1 ∧ dzbar f z = 0 := by
  unfold dz dzbar
  rw [h.fderiv]
  simp only [ContinuousLinearMap.id_apply, Complex.I_mul_I]
  constructor <;> ring

/-- The preimage of a null set of reals under `Re` is a null set of the plane. -/
theorem anN_volume_re_preimage {C : Set ℝ} (hC : volume C = 0) :
    volume {z : ℂ | z.re ∈ C} = 0 := by
  have : {z : ℂ | z.re ∈ C} = Complex.measurableEquivRealProd ⁻¹' (C ×ˢ univ) := by
    ext z
    simp [Complex.measurableEquivRealProd]
  rw [this, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod, hC, zero_mul]

/-- §10.1: the A.C.L. condition in Theorem 10.1 cannot be replaced by mere differentiability
almost everywhere: there is a homeomorphism of the plane, differentiable a.e. and satisfying
the dilatation inequality (10.1) a.e. with `K = 1`, which is not quasiconformal.

Proved (2026-09-24): `f(x+iy) = x + F(x) + iy` with `F` the Cantor function (the distribution
function of the Cantor measure, the image of the fair-coin product measure under the ternary digit
map): `f` is differentiable with `f' = id` off the null set `{Re z ∈ Cantor set}`, but it is not A.C.L.
on horizontal lines (`F(1) - F(0) = 1` while `F' = 0` a.e.), so not quasiconformal (`thm9_1_isACL`). -/
theorem acl_not_removable :
    ∃ f : ℂ → ℂ, IsHomeomorphOnto f univ univ ∧ (∀ᵐ z, DifferentiableAt ℝ f z) ∧
      (∀ᵐ z, ‖dz f z‖ + ‖dzbar f z‖ ≤ 1 * (‖dz f z‖ - ‖dzbar f z‖)) ∧
      ∀ K : ℝ, ¬ IsKQC f univ K := by
  obtain ⟨F, hFc, hFm, hF0, hF1, hFb, C, -, hCv, hCloc⟩ := anN_cantor_function
  have hae : ∀ᵐ z : ℂ, z.re ∉ C :=
    measure_eq_zero_iff_ae_notMem.1 (anN_volume_re_preimage hCv)
  have hder : ∀ z : ℂ, z.re ∉ C → HasFDerivAt
      (fun z : ℂ => (((z.re + F z.re : ℝ)) : ℂ) + (z.im : ℂ) * I)
      (ContinuousLinearMap.id ℝ ℂ) z := fun z hz => anN_hasFDerivAt F (hCloc _ hz)
  refine ⟨fun z : ℂ => (((z.re + F z.re : ℝ)) : ℂ) + (z.im : ℂ) * I,
    anN_homeo F hFc hFm hFb, ?_, ?_, ?_⟩
  · filter_upwards [hae] with z hz using (hder z hz).differentiableAt
  · filter_upwards [hae] with z hz
    obtain ⟨h1, h2⟩ := anN_dz_dzbar (hder z hz)
    rw [h1, h2]
    simp
  · intro K hK
    have hacl := ((thm9_1_isACL hK).2 0 1 0 1 zero_lt_one zero_lt_one (subset_univ _)).2
    have hne : (ae (volume.restrict (Ioo (0 : ℝ) 1))).NeBot :=
      ae_neBot.2 (by simp [Measure.restrict_eq_zero])
    obtain ⟨y, hy⟩ := hacl.exists
    have hint := integral_deriv_eq_sub_of_absolutelyContinuous hy
    have hCae : ∀ᵐ x : ℝ, x ∉ C := measure_eq_zero_iff_ae_notMem.1 hCv
    have hderiv : ∀ x : ℝ, x ∉ C →
        deriv (fun x : ℝ => (fun z : ℂ => (((z.re + F z.re : ℝ)) : ℂ) + (z.im : ℂ) * I)
          ((x : ℂ) + (y : ℂ) * I)) x = 1 := by
      intro x hx
      have h1 : (fun t : ℝ => (fun z : ℂ => (((z.re + F z.re : ℝ)) : ℂ) + (z.im : ℂ) * I)
          ((t : ℂ) + (y : ℂ) * I)) =ᶠ[𝓝 x] fun t : ℝ => (t : ℂ) + ((F x : ℂ) + (y : ℂ) * I) := by
        filter_upwards [hCloc x hx] with t ht
        apply Complex.ext <;> simp [ht]
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) + ((F x : ℂ) + (y : ℂ) * I)) 1 x :=
        (hasDerivAt_id x).ofReal_comp.add_const _
      exact (h2.congr_of_eventuallyEq h1).deriv
    have hI : ∫ x in (0 : ℝ)..1, deriv (fun x : ℝ =>
        (fun z : ℂ => (((z.re + F z.re : ℝ)) : ℂ) + (z.im : ℂ) * I)
          ((x : ℂ) + (y : ℂ) * I)) x = 1 := by
      rw [intervalIntegral.integral_congr_ae (g := fun _ => (1 : ℂ))
        (by filter_upwards [hCae] with x hx _ using hderiv x hx)]
      simp
    rw [hI] at hint
    simp [hF0, hF1] at hint

/-- **Definition 10.1**: the maximal dilatation of a quasiconformal map,
`K[f] = ess sup_{z ∈ D} (|∂_z f| + |∂_{z̄} f|)/(|∂_z f| - |∂_{z̄} f|)`.  (The complex
characteristic `μ_f = ∂_{z̄} f / ∂_z f` is `complexDilatation f`, defined a.e.) -/
def maxDilatation (f : ℂ → ℂ) (D : Set ℂ) : ℝ≥0∞ :=
  essSup (fun z => ENNReal.ofReal ((‖dz f z‖ + ‖dzbar f z‖) / (‖dz f z‖ - ‖dzbar f z‖)))
    (volume.restrict D)

/-- §10.2: for a `K`-q.c. map, `K[f] ≤ K` and `|μ_f| ≤ (K-1)/(K+1)` a.e. -/
theorem isKQC_maxDilatation_le {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) :
    maxDilatation f D ≤ ENNReal.ofReal K ∧
      ∀ᵐ z ∂(volume.restrict D), ‖complexDilatation f z‖ ≤ (K - 1) / (K + 1) := by
  have hK1 : (1 : ℝ) ≤ K := hf.2.1
  have hae : ∀ᵐ z ∂(volume.restrict D), ‖dzbar f z‖ < ‖dz f z‖ ∧
      ‖dz f z‖ + ‖dzbar f z‖ ≤ K * (‖dz f z‖ - ‖dzbar f z‖) := by
    filter_upwards [thm9_4_dilatation_ae hf, thm9_6_cor2_jacobian_pos hf] with z h1 h2
    refine ⟨?_, h1⟩
    unfold jacobian at h2
    nlinarith [norm_nonneg (dz f z), norm_nonneg (dzbar f z)]
  refine ⟨essSup_le_of_ae_le _ ?_, ?_⟩
  · filter_upwards [hae] with z hz
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ (by linarith [hz.1] : (0 : ℝ) < ‖dz f z‖ - ‖dzbar f z‖)]
    linarith [hz.2]
  · filter_upwards [hae] with z hz
    have hp : 0 < ‖dz f z‖ := (norm_nonneg _).trans_lt hz.1
    rw [complexDilatation, norm_div, div_le_div_iff₀ hp (by linarith : (0 : ℝ) < K + 1)]
    linarith [hz.2]

/-- A measurable Beltrami coefficient on `D` with `|μ| ≤ k` a.e. -/
def IsBeltramiCoeff (μ : ℂ → ℂ) (D : Set ℂ) (k : ℝ) : Prop :=
  AEStronglyMeasurable μ (volume.restrict D) ∧ ∀ᵐ z ∂(volume.restrict D), ‖μ z‖ ≤ k

/-- `f` is an `L_p` generalized homeomorphic solution (广义同胚解) in `D` of the Beltrami equation
`∂_{z̄} w = μ(z) ∂_z w`: a homeomorphism of `D` onto `f(D)` with `L_p` generalized derivatives
satisfying the equation almost everywhere. -/
def IsGenHomeoSolution (f μ : ℂ → ℂ) (D : Set ℂ) (p : ℝ≥0∞) : Prop :=
  IsHomeomorphOnto f D (f '' D) ∧
    ∃ g h : ℂ → ℂ, HasGenPartials f g h D p ∧
      ∀ᵐ z ∂(volume.restrict D), genDzbar g h z = μ z * genDz g h z

/-- **Theorem 10.2** (⇒).  A `K`-q.c. map is an `L₂` generalized homeomorphic solution of the
Beltrami equation with `μ = μ_f`, `|μ| ≤ k = (K-1)/(K+1)`. -/
theorem thm10_2_genHomeoSolution_of_isKQC {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) :
    IsBeltramiCoeff (complexDilatation f) D ((K - 1) / (K + 1)) ∧
      IsGenHomeoSolution f (complexDilatation f) D 2 := by
  obtain ⟨-, hμ⟩ := isKQC_maxDilatation_le hf
  refine ⟨⟨((measurable_dzbar f).div (measurable_dz f)).aestronglyMeasurable, hμ⟩,
    hf.2.2.1, partialX f, partialY f, (thm9_5_L2_derivatives hf).1, ?_⟩
  filter_upwards [thm9_3_differentiable_ae hf, thm9_6_cor2_jacobian_pos hf] with z hz hJ
  have hp : dz f z ≠ 0 := by
    intro h
    rw [jacobian, h, norm_zero] at hJ
    nlinarith [norm_nonneg (dzbar f z)]
  have hx : partialX f z = dz f z + dzbar f z := by
    rw [partialX_eq_of_differentiableAt hz, fderiv_eq_dz_dzbar hz]
    simp
  have hy : partialY f z = I * (dz f z - dzbar f z) := by
    rw [partialY_eq_of_differentiableAt hz, fderiv_eq_dz_dzbar hz, Complex.conj_I]
    ring
  have hgz : genDz (partialX f) (partialY f) z = dz f z := by
    rw [genDz, hx, hy]
    linear_combination (-(dz f z - dzbar f z) / 2) * I_sq
  have hgzb : genDzbar (partialX f) (partialY f) z = dzbar f z := by
    rw [genDzbar, hx, hy]
    linear_combination ((dz f z - dzbar f z) / 2) * I_sq
  rw [hgz, hgzb, complexDilatation, div_mul_cancel₀ _ hp]

end LiZhongQC
