import LiZhongQC.Lemmas.Conformal

/-!
# §3 极值长度 — Extremal length

* locally rectifiable curves, `ρ`-length and `ρ`-area   — `LRCurve`, `LRCurve.rhoLength`,
                                                           `rhoArea`
* Definition 3.1 (extremal length `λ_D(Γ)`)            — `extremalLengthIn`, `extremalLength`
* independence of the domain `D`                        — `extremalLengthIn_eq`
* Theorem 3.1 (conformal invariance)                    — `thm3_1_conformal_invariance`
* the equivalent definitions (3.1), (3.3), (3.5)        — `eq3_1`, `eq3_3`, `eq3_5`
* Theorem 3.2 (comparison principle)                    — `thm3_2_comparison`
* Theorem 3.3 (composition principle)                   — `thm3_3_composition_i`,
                                                           `thm3_3_composition_ii`

## Curves

A locally rectifiable curve admits a reparametrization by arc length, which is
`1`-Lipschitz; after a further monotone change of parameter it is parametrized by a
locally Lipschitz map of the open interval `(0,1)`.  We therefore model a locally
rectifiable (open) curve as a map `ℝ → ℂ`, locally Lipschitz on `(0,1)`, and a closed
rectifiable curve as one which is Lipschitz on `[0,1]` with equal end values.  The
`ρ`-length is `∫_{(0,1)} ρ(γ(t)) |γ'(t)| dt`.  "`γ₁` contains `γ₂`" means that `γ₂` is a
monotone reparametrization of a sub-arc of `γ₁`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace LiZhongQC

/-- A locally rectifiable curve, parametrized by a map locally Lipschitz on `(0,1)`. -/
structure LRCurve where
  /-- The parametrization. -/
  toFun : ℝ → ℂ
  locallyLipschitzOn : LocallyLipschitzOn (Ioo 0 1) toFun

namespace LRCurve

/-- The point set (trace) of an open curve. -/
def trace (γ : LRCurve) : Set ℂ := γ.toFun '' Ioo 0 1

/-- The `ρ`-length `l_ρ(γ) = ∫_γ ρ |dz|`. -/
def rhoLength (ρ : ℂ → ℝ≥0∞) (γ : LRCurve) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) 1, ρ (γ.toFun t) * ‖deriv γ.toFun t‖ₑ

/-- The Euclidean length of `γ`. -/
def length (γ : LRCurve) : ℝ≥0∞ := γ.rhoLength 1

/-- `γ₁` contains `γ₂` (`γ₂ ⊂ γ₁`): `γ₂` is a monotone reparametrization of a sub-arc
of `γ₁`. -/
def Contains (γ₁ γ₂ : LRCurve) : Prop :=
  ∃ h : ℝ → ℝ, MonotoneOn h (Ioo 0 1) ∧ MapsTo h (Ioo 0 1) (Ioo 0 1) ∧
    LocallyLipschitzOn (Ioo 0 1) h ∧ EqOn γ₂.toFun (γ₁.toFun ∘ h) (Ioo 0 1)

/-- `γ` is a closed rectifiable curve. -/
def IsClosedCurve (γ : LRCurve) : Prop :=
  ∃ K : ℝ≥0, LipschitzOnWith K γ.toFun (Icc 0 1) ∧ γ.toFun 0 = γ.toFun 1

/-- The trace of a closed curve (including the initial point). -/
def closedTrace (γ : LRCurve) : Set ℂ := γ.toFun '' Icc 0 1

end LRCurve

/-- The `ρ`-area `m_ρ(D) = ∬_D ρ² dx dy`. -/
def rhoArea (ρ : ℂ → ℝ≥0∞) (D : Set ℂ) : ℝ≥0∞ := ∫⁻ z in D, ρ z ^ 2

/-- The set `P₀` of admissible densities on `D`: Borel measurable, `0 < m_ρ(D) < ∞`. -/
def densitiesP0 (D : Set ℂ) : Set (ℂ → ℝ≥0∞) :=
  {ρ | Measurable ρ ∧ 0 < rhoArea ρ D ∧ rhoArea ρ D < ⊤}

/-- **Definition 3.1** (极值长度).
`λ_D(Γ) = sup_{ρ ∈ P₀} inf_{γ ∈ Γ} l_ρ(γ)² / m_ρ(D)`. -/
def extremalLengthIn (D : Set ℂ) (Γ : Set LRCurve) : ℝ≥0∞ :=
  ⨆ ρ ∈ densitiesP0 D, (⨅ γ ∈ Γ, γ.rhoLength ρ ^ 2) / rhoArea ρ D

/-- The extremal length `λ(Γ)`, computed with `D = ℂ`
(it does not depend on `D`, see `extremalLengthIn_eq`). -/
def extremalLength (Γ : Set LRCurve) : ℝ≥0∞ := extremalLengthIn univ Γ

/-- The `ρ`-length only depends on the values of `ρ` on the trace. -/
theorem LRCurve.rhoLength_congr {ρ₁ ρ₂ : ℂ → ℝ≥0∞} {γ : LRCurve} (h : EqOn ρ₁ ρ₂ γ.trace) :
    γ.rhoLength ρ₁ = γ.rhoLength ρ₂ := by
  unfold LRCurve.rhoLength
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  rw [h (mem_image_of_mem _ ht)]

/-- `l_{cρ}(γ) = c l_ρ(γ)`. -/
theorem LRCurve.rhoLength_const_mul (γ : LRCurve) (ρ : ℂ → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    γ.rhoLength (fun z => c * ρ z) = c * γ.rhoLength ρ := by
  simp only [LRCurve.rhoLength, mul_assoc]
  exact lintegral_const_mul' c _ hc

/-- `m_{cρ}(D) = c² m_ρ(D)`. -/
theorem rhoArea_const_mul (ρ : ℂ → ℝ≥0∞) (D : Set ℂ) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    rhoArea (fun z => c * ρ z) D = c ^ 2 * rhoArea ρ D := by
  simp only [rhoArea, mul_pow]
  exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top hc)

/-- `inf_γ l_{cρ}(γ)² = c² inf_γ l_ρ(γ)²`. -/
theorem iInf_rhoLength_sq_const_mul (Γ : Set LRCurve) (ρ : ℂ → ℝ≥0∞) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : c ≠ ⊤) :
    ⨅ γ ∈ Γ, γ.rhoLength (fun z => c * ρ z) ^ 2 = c ^ 2 * ⨅ γ ∈ Γ, γ.rhoLength ρ ^ 2 := by
  simp only [LRCurve.rhoLength_const_mul _ _ hc, mul_pow,
    ENNReal.mul_iInf_of_ne (pow_ne_zero 2 hc0) (ENNReal.pow_ne_top hc)]

/-- Normalization of densities: for `0 < m, t < ∞` there is `0 < c < ∞` with `c² m = t`. -/
theorem exists_sq_mul_eq_of_ne {m t : ℝ≥0∞} (hm0 : m ≠ 0) (hm : m ≠ ⊤) (ht0 : t ≠ 0)
    (ht : t ≠ ⊤) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ c ^ 2 * m = t := by
  lift m to ℝ≥0 using hm
  lift t to ℝ≥0 using ht
  have hm0' : m ≠ 0 := by exact_mod_cast hm0
  have ht0' : t ≠ 0 := by exact_mod_cast ht0
  refine ⟨((NNReal.sqrt (t / m) : ℝ≥0) : ℝ≥0∞), ?_, ENNReal.coe_ne_top, ?_⟩
  · simp [hm0', ht0']
  · rw [← ENNReal.coe_pow, ← ENNReal.coe_mul, NNReal.sq_sqrt, div_mul_cancel₀ t hm0']

/-- Every Borel density of finite area bounds the extremal length from below — also when its area
vanishes: then `∞ ⋅ ρ + 1_E` (`E ⊆ D` open) shows `λ_D(Γ) = ∞`, unless all `ρ`-lengths vanish. -/
theorem le_extremalLengthIn {D : Set ℂ} (hD : IsOpen D) (hDne : D.Nonempty) (Γ : Set LRCurve)
    {ρ : ℂ → ℝ≥0∞} (hρm : Measurable ρ) (hρtop : rhoArea ρ D < ⊤) :
    (⨅ γ ∈ Γ, γ.rhoLength ρ ^ 2) / rhoArea ρ D ≤ extremalLengthIn D Γ := by
  unfold extremalLengthIn
  by_cases hD0 : rhoArea ρ D = 0
  swap
  · exact le_iSup₂_of_le ρ ⟨hρm, pos_iff_ne_zero.2 hD0, hρtop⟩ le_rfl
  by_cases hL0 : (⨅ γ ∈ Γ, γ.rhoLength ρ ^ 2) = 0
  · rw [hL0, ENNReal.zero_div]
    exact zero_le
  obtain ⟨z₀, hz₀⟩ := hDne
  set E := D ∩ ball z₀ 1 with hE
  have hEo : IsOpen E := hD.inter isOpen_ball
  have hEpos : 0 < volume E := hEo.measure_pos volume ⟨z₀, hz₀, mem_ball_self one_pos⟩
  have hEtop : volume E < ⊤ := (measure_mono inter_subset_right).trans_lt measure_ball_lt_top
  set ρ' : ℂ → ℝ≥0∞ := fun z => ⊤ * ρ z + E.indicator 1 z with hρ'
  have hρae : ∀ᵐ z ∂(volume.restrict D), ρ z = 0 := by
    unfold rhoArea at hD0
    have h2 := (lintegral_eq_zero_iff (hρm.pow_const 2)).1 hD0
    filter_upwards [h2] with z hz
    simpa using hz
  have hA' : rhoArea ρ' D = volume E := by
    have h : ∫⁻ z in D, ρ' z ^ 2 = ∫⁻ z in D, E.indicator 1 z := by
      refine lintegral_congr_ae ?_
      filter_upwards [hρae] with z hz
      simp only [hρ', hz, mul_zero, zero_add]
      by_cases hzE : z ∈ E <;> simp [hzE]
    rw [rhoArea, h, lintegral_indicator_one hEo.measurableSet,
      Measure.restrict_apply hEo.measurableSet, inter_eq_left.2 inter_subset_left]
  have hρ'm : Measurable ρ' :=
    (measurable_const.mul hρm).add (measurable_one.indicator hEo.measurableSet)
  have hmem : ρ' ∈ densitiesP0 D := by
    refine ⟨hρ'm, ?_, ?_⟩
    · rw [hA']; exact hEpos
    · rw [hA']; exact hEtop
  have hinf : ⨅ γ ∈ Γ, γ.rhoLength ρ' ^ 2 = ⊤ := by
    refine iInf₂_eq_top.2 fun γ hγ => ?_
    have hlen : γ.rhoLength ρ ≠ 0 := by
      intro h0
      exact hL0 (le_antisymm ((iInf₂_le γ hγ).trans (by rw [h0]; simp)) zero_le)
    have htop : ⊤ ≤ γ.rhoLength ρ' := by
      refine (ENNReal.top_mul hlen).symm.le.trans ?_
      unfold LRCurve.rhoLength
      refine (lintegral_const_mul_le _ _).trans (lintegral_mono fun t => ?_)
      simp only [hρ']
      rw [← mul_assoc]
      exact mul_le_mul_left le_self_add _
    rw [top_le_iff.1 htop]
    simp
  refine le_top.trans (le_iSup₂_of_le ρ' hmem (le_of_eq ?_))
  rw [hinf, hA', ENNReal.top_div_of_ne_top hEtop.ne]

/-- §3.1: `λ_D(Γ)` does not depend on the choice of the domain `D` containing all curves of
`Γ`; in particular `λ_{D₁}(Γ) = λ_{D₂}(Γ) = λ_{D₁ ∩ D₂}(Γ)`.
(Source note: `D` is assumed non-empty; for `D = ∅`, `Γ = ∅` the two sides are `0` and `∞`.) -/
theorem extremalLengthIn_eq {D : Set ℂ} (hD : IsOpen D) (hDne : D.Nonempty) {Γ : Set LRCurve}
    (hΓ : ∀ γ ∈ Γ, γ.trace ⊆ D) : extremalLengthIn D Γ = extremalLength Γ := by
  unfold extremalLength extremalLengthIn
  apply le_antisymm
  · -- a density on `D`, extended by zero, is a density on `ℂ` with the same lengths and area
    refine iSup₂_le fun ρ hρ => ?_
    obtain ⟨hρm, hρ0, hρtop⟩ := hρ
    have hA : rhoArea (D.indicator ρ) univ = rhoArea ρ D := by
      simp only [rhoArea, Measure.restrict_univ]
      rw [← lintegral_indicator hD.measurableSet]
      congr 1
      funext z
      by_cases hz : z ∈ D <;> simp [hz]
    have hL : ∀ γ ∈ Γ, γ.rhoLength (D.indicator ρ) = γ.rhoLength ρ := fun γ hγ =>
      LRCurve.rhoLength_congr fun z hz => indicator_of_mem (hΓ γ hγ hz) ρ
    have hmem : D.indicator ρ ∈ densitiesP0 univ := by
      refine ⟨hρm.indicator hD.measurableSet, ?_, ?_⟩
      · rw [hA]; exact hρ0
      · rw [hA]; exact hρtop
    refine le_iSup₂_of_le (D.indicator ρ) hmem (le_of_eq ?_)
    rw [hA]
    congr 1
    exact iInf_congr fun γ => iInf_congr fun hγ => by rw [hL γ hγ]
  · -- a density on `ℂ` has smaller area on `D`
    refine iSup₂_le fun ρ hρ => ?_
    obtain ⟨hρm, -, hρtop⟩ := hρ
    have hle : rhoArea ρ D ≤ rhoArea ρ univ := lintegral_mono_set (subset_univ D)
    exact (ENNReal.div_le_div_left hle _).trans
      (le_extremalLengthIn hD hDne Γ hρm (hle.trans_lt hρtop))

/-- The image family `Γ' = f(Γ)`. -/
def IsCurveImage (f : ℂ → ℂ) (Γ Γ' : Set LRCurve) : Prop :=
  (∀ γ ∈ Γ, ∃ γ' ∈ Γ', EqOn γ'.toFun (f ∘ γ.toFun) (Ioo 0 1)) ∧
    ∀ γ' ∈ Γ', ∃ γ ∈ Γ, EqOn γ'.toFun (f ∘ γ.toFun) (Ioo 0 1)

/-- An injective map carries the image family `f(Γ)` back to `Γ` by its inverse. -/
theorem IsCurveImage.inv {f : ℂ → ℂ} {D : Set ℂ} (hinj : InjOn f D) {Γ Γ' : Set LRCurve}
    (hΓ : ∀ γ ∈ Γ, γ.trace ⊆ D) (himg : IsCurveImage f Γ Γ') :
    IsCurveImage (Function.invFunOn f D) Γ' Γ := by
  constructor
  · intro γ' hγ'
    obtain ⟨γ, hγ, heq⟩ := himg.2 γ' hγ'
    refine ⟨γ, hγ, fun t ht => ?_⟩
    simp only [Function.comp_apply, heq ht]
    exact (hinj.leftInvOn_invFunOn (hΓ γ hγ (mem_image_of_mem _ ht))).symm
  · intro γ hγ
    obtain ⟨γ', hγ', heq⟩ := himg.1 γ hγ
    refine ⟨γ', hγ', fun t ht => ?_⟩
    simp only [Function.comp_apply, heq ht]
    exact (hinj.leftInvOn_invFunOn (hΓ γ hγ (mem_image_of_mem _ ht))).symm

/-- The pull-back density `(ρ' ∘ f) |f'|`, extended by zero outside `D`, is Borel. -/
theorem measurable_pullback_density {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hfc : ContinuousOn f D) {ρ' : ℂ → ℝ≥0∞} (hρ' : Measurable ρ') :
    Measurable (D.indicator fun z => ρ' (f z) * ‖deriv f z‖ₑ) := by
  classical
  have hpw : Measurable (D.piecewise f fun _ => 0) :=
    hfc.measurable_piecewise continuousOn_const hD.measurableSet
  have hm : Measurable
      (D.indicator fun z => ρ' (D.piecewise f (fun _ => 0) z) * ‖deriv f z‖ₑ) :=
    ((hρ'.comp hpw).mul (measurable_deriv f).enorm).indicator hD.measurableSet
  convert hm using 1
  funext z
  by_cases hz : z ∈ D <;> simp [hz]

/-- `l_{ρ'}(f ∘ γ) = l_ρ(γ)` for the pull-back density `ρ = (ρ' ∘ f) |f'|`. -/
theorem LRCurve.rhoLength_image_conformal {f : ℂ → ℂ} {D D' : Set ℂ} (hD : IsOpen D)
    (hf : IsConformalOnto f D D') {γ γ' : LRCurve} (hγ : γ.trace ⊆ D)
    (heq : EqOn γ'.toFun (f ∘ γ.toFun) (Ioo 0 1)) (ρ' : ℂ → ℝ≥0∞) :
    γ'.rhoLength ρ' = γ.rhoLength (D.indicator fun z => ρ' (f z) * ‖deriv f z‖ₑ) := by
  unfold LRCurve.rhoLength
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hev : ∀ᶠ s in 𝓝 t, s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhds ht.1 ht.2
  have hγt : ∀ᶠ s in 𝓝 t, γ.toFun s ∈ D := hev.mono fun s hs => hγ (mem_image_of_mem _ hs)
  have hderiv : deriv γ'.toFun t = deriv (f ∘ γ.toFun) t :=
    Filter.EventuallyEq.deriv_eq (hev.mono fun s hs => heq hs)
  rw [heq ht, hderiv, hf.deriv_comp hD hγt]
  simp only [indicator_of_mem (hγ (mem_image_of_mem _ ht)), Function.comp_apply, enorm_mul,
    mul_assoc]

/-- The pull-back density `(ρ' ∘ f) |f'|` has the same area as `ρ'`. -/
theorem rhoArea_pullback {D D' : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : IsConformalOnto f D D') (ρ' : ℂ → ℝ≥0∞) :
    rhoArea (D.indicator fun z => ρ' (f z) * ‖deriv f z‖ₑ) D = rhoArea ρ' D' := by
  simp only [rhoArea]
  rw [lintegral_image_conformal hD hf]
  refine setLIntegral_congr_fun hD.measurableSet fun z hz => ?_
  simp only [indicator_of_mem hz]
  ring

/-- The pull-back density `(ρ' ∘ f) |f'|` on `Γ` has the same infimum of squared lengths as `ρ'`
on `Γ' = f(Γ)`. -/
theorem iInf_rhoLength_sq_pullback {D D' : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : IsConformalOnto f D D') {Γ Γ' : Set LRCurve} (hΓ : ∀ γ ∈ Γ, γ.trace ⊆ D)
    (himg : IsCurveImage f Γ Γ') (ρ' : ℂ → ℝ≥0∞) :
    ⨅ γ' ∈ Γ', γ'.rhoLength ρ' ^ 2 =
      ⨅ γ ∈ Γ, γ.rhoLength (D.indicator fun z => ρ' (f z) * ‖deriv f z‖ₑ) ^ 2 := by
  apply le_antisymm
  · refine le_iInf₂ fun γ hγ => ?_
    obtain ⟨γ', hγ', heq⟩ := himg.1 γ hγ
    rw [← LRCurve.rhoLength_image_conformal hD hf (hΓ γ hγ) heq]
    exact iInf₂_le γ' hγ'
  · refine le_iInf₂ fun γ' hγ' => ?_
    obtain ⟨γ, hγ, heq⟩ := himg.2 γ' hγ'
    rw [LRCurve.rhoLength_image_conformal hD hf (hΓ γ hγ) heq]
    exact iInf₂_le γ hγ

/-- One half of **Theorem 3.1**: pulling back densities by a conformal map `f : D → D'`. -/
theorem extremalLengthIn_le_of_conformal {D D' : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : IsConformalOnto f D D') {Γ Γ' : Set LRCurve} (hΓ : ∀ γ ∈ Γ, γ.trace ⊆ D)
    (himg : IsCurveImage f Γ Γ') : extremalLengthIn D' Γ' ≤ extremalLengthIn D Γ := by
  refine iSup₂_le fun ρ' hρ' => ?_
  obtain ⟨hρ'm, hρ'0, hρ'top⟩ := hρ'
  have hA := rhoArea_pullback hD hf ρ'
  have hL := iInf_rhoLength_sq_pullback hD hf hΓ himg ρ'
  have hmem : (D.indicator fun z => ρ' (f z) * ‖deriv f z‖ₑ) ∈ densitiesP0 D := by
    refine ⟨measurable_pullback_density hD hf.1.continuousOn hρ'm, ?_, ?_⟩
    · rw [hA]
      exact hρ'0
    · rw [hA]
      exact hρ'top
  exact le_iSup₂_of_le _ hmem (le_of_eq (by rw [hL, hA]))

/-- **Theorem 3.1**: extremal length is a conformal invariant. -/
theorem thm3_1_conformal_invariance {D D' : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : IsConformalOnto f D D') {Γ Γ' : Set LRCurve} (hΓ : ∀ γ ∈ Γ, γ.trace ⊆ D)
    (himg : IsCurveImage f Γ Γ') : extremalLength Γ' = extremalLength Γ := by
  rcases Γ.eq_empty_or_nonempty with rfl | ⟨γ₀, hγ₀⟩
  · have hΓ' : Γ' = ∅ := eq_empty_iff_forall_notMem.2 fun γ' hγ' => by
      obtain ⟨γ, hγ, -⟩ := himg.2 γ' hγ'
      exact hγ
    rw [hΓ']
  have hD' : IsOpen D' := hf.isOpen hD
  have hDne : D.Nonempty :=
    ⟨γ₀.toFun (1 / 2), hΓ γ₀ hγ₀ (mem_image_of_mem _ ⟨by norm_num, by norm_num⟩)⟩
  have hD'ne : D'.Nonempty := by
    rw [← hf.2.2]
    exact hDne.image f
  have hΓ' : ∀ γ' ∈ Γ', γ'.trace ⊆ D' := by
    rintro γ' hγ' _ ⟨t, ht, rfl⟩
    obtain ⟨γ, hγ, heq⟩ := himg.2 γ' hγ'
    rw [heq ht, ← hf.2.2]
    exact mem_image_of_mem f (hΓ γ hγ (mem_image_of_mem _ ht))
  -- the inverse map carries `Γ'` back to `Γ`
  have himg' : IsCurveImage (Function.invFunOn f D) Γ' Γ := by
    constructor
    · intro γ' hγ'
      obtain ⟨γ, hγ, heq⟩ := himg.2 γ' hγ'
      refine ⟨γ, hγ, fun t ht => ?_⟩
      simp only [Function.comp_apply, heq ht]
      exact (hf.2.1.leftInvOn_invFunOn (hΓ γ hγ (mem_image_of_mem _ ht))).symm
    · intro γ hγ
      obtain ⟨γ', hγ', heq⟩ := himg.1 γ hγ
      refine ⟨γ', hγ', fun t ht => ?_⟩
      simp only [Function.comp_apply, heq ht]
      exact (hf.2.1.leftInvOn_invFunOn (hΓ γ hγ (mem_image_of_mem _ ht))).symm
  rw [← extremalLengthIn_eq hD' hD'ne hΓ', ← extremalLengthIn_eq hD hDne hΓ]
  exact le_antisymm (extremalLengthIn_le_of_conformal hD hf hΓ himg)
    (extremalLengthIn_le_of_conformal hD' (hf.symm hD) hΓ' himg')

/-- (3.1)–(3.2): `λ(Γ) = sup_{ρ ∈ P₁} inf_γ l_ρ(γ)²`, `P₁ = {ρ : 0 < m_ρ(D) ≤ 1}`. -/
theorem eq3_1 (Γ : Set LRCurve) :
    extremalLength Γ =
      ⨆ ρ ∈ {ρ : ℂ → ℝ≥0∞ | Measurable ρ ∧ 0 < rhoArea ρ univ ∧ rhoArea ρ univ ≤ 1},
        ⨅ γ ∈ Γ, γ.rhoLength ρ ^ 2 := by
  unfold extremalLength extremalLengthIn
  apply le_antisymm
  · -- normalize `ρ ∈ P₀` to unit area
    refine iSup₂_le fun ρ hρ => ?_
    obtain ⟨hρm, hρ0, hρtop⟩ := hρ
    obtain ⟨c, hc0, hct, hc⟩ :=
      exists_sq_mul_eq_of_ne hρ0.ne' hρtop.ne one_ne_zero ENNReal.one_ne_top
    have hmem : (fun z => c * ρ z) ∈
        {ρ : ℂ → ℝ≥0∞ | Measurable ρ ∧ 0 < rhoArea ρ univ ∧ rhoArea ρ univ ≤ 1} := by
      refine ⟨measurable_const.mul hρm, ?_, ?_⟩
      · rw [rhoArea_const_mul _ _ hct, hc]
        exact one_pos
      · exact le_of_eq (by rw [rhoArea_const_mul _ _ hct, hc])
    have hinv : (rhoArea ρ univ)⁻¹ = c ^ 2 := by
      calc (rhoArea ρ univ)⁻¹ = c ^ 2 * rhoArea ρ univ * (rhoArea ρ univ)⁻¹ := by
            rw [hc, one_mul]
        _ = c ^ 2 := by rw [mul_assoc, ENNReal.mul_inv_cancel hρ0.ne' hρtop.ne, mul_one]
    refine le_iSup₂_of_le (fun z => c * ρ z) hmem (le_of_eq ?_)
    rw [iInf_rhoLength_sq_const_mul Γ ρ hc0 hct, div_eq_mul_inv, hinv, mul_comm]
  · refine iSup₂_le fun ρ hρ => ?_
    obtain ⟨hρm, hρ0, hρ1⟩ := hρ
    refine le_iSup₂_of_le ρ ⟨hρm, hρ0, hρ1.trans_lt ENNReal.one_lt_top⟩ ?_
    calc (⨅ γ ∈ Γ, γ.rhoLength ρ ^ 2) = (⨅ γ ∈ Γ, γ.rhoLength ρ ^ 2) / 1 := (div_one _).symm
      _ ≤ _ := ENNReal.div_le_div_left hρ1 _

/-- (3.3)–(3.4): `λ(Γ) = (inf_{ρ ∈ P₂} m_ρ(D))⁻¹`,
`P₂ = {ρ ∈ P₀ : l_ρ(γ) ≥ 1 for all γ ∈ Γ}`. -/
theorem eq3_3 (Γ : Set LRCurve) :
    extremalLength Γ =
      (⨅ ρ ∈ {ρ ∈ densitiesP0 univ | ∀ γ ∈ Γ, 1 ≤ γ.rhoLength ρ}, rhoArea ρ univ)⁻¹ := by
  unfold extremalLength extremalLengthIn
  apply le_antisymm
  · refine iSup₂_le fun ρ hρ => ?_
    obtain ⟨hρm, hρ0, hρtop⟩ := hρ
    obtain ⟨L, hL⟩ : ∃ L, (⨅ γ ∈ Γ, γ.rhoLength ρ ^ 2) = L := ⟨_, rfl⟩
    rw [hL]
    rcases eq_or_ne L 0 with hL0 | hL0
    · rw [hL0, ENNReal.zero_div]
      exact zero_le
    have hlen : ∀ γ ∈ Γ, L ≤ γ.rhoLength ρ ^ 2 := fun γ hγ => by
      rw [← hL]
      exact iInf₂_le γ hγ
    rcases eq_or_ne L ⊤ with hLt | hLt
    · -- all lengths are infinite: the infimum of the areas is `0`
      suffices h : (⨅ ρ ∈ {ρ ∈ densitiesP0 univ | ∀ γ ∈ Γ, 1 ≤ γ.rhoLength ρ},
          rhoArea ρ univ) = 0 by
        rw [h, ENNReal.inv_zero]
        exact le_top
      refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
      obtain ⟨c, hc0, hct, hc⟩ := exists_sq_mul_eq_of_ne hρ0.ne' hρtop.ne
        (ENNReal.coe_ne_zero.2 hε.ne') ENNReal.coe_ne_top
      refine iInf₂_le_of_le (fun z => c * ρ z)
        ⟨⟨measurable_const.mul hρm, ?_, ?_⟩, fun γ hγ => ?_⟩ ?_
      · rw [rhoArea_const_mul _ _ hct, hc]
        exact ENNReal.coe_pos.2 hε
      · rw [rhoArea_const_mul _ _ hct, hc]
        exact ENNReal.coe_lt_top
      · have h1 : γ.rhoLength ρ = ⊤ := by
          have h := hlen γ hγ
          rw [hLt, top_le_iff, ENNReal.pow_eq_top_iff] at h
          exact h.1
        rw [LRCurve.rhoLength_const_mul _ _ hct, h1, ENNReal.mul_top hc0]
        exact le_top
      · exact le_of_eq (by rw [rhoArea_const_mul _ _ hct, hc, zero_add])
    · -- normalize `ρ` so that `inf_γ l_ρ(γ)² = 1`
      obtain ⟨c, hc0, hct, hc⟩ := exists_sq_mul_eq_of_ne hL0 hLt one_ne_zero ENNReal.one_ne_top
      have hmem : (fun z => c * ρ z) ∈ {ρ ∈ densitiesP0 univ | ∀ γ ∈ Γ, 1 ≤ γ.rhoLength ρ} := by
        refine ⟨⟨measurable_const.mul hρm, ?_, ?_⟩, fun γ hγ => ?_⟩
        · rw [rhoArea_const_mul _ _ hct]
          exact ENNReal.mul_pos (pow_ne_zero 2 hc0) hρ0.ne'
        · rw [rhoArea_const_mul _ _ hct]
          exact ENNReal.mul_lt_top (ENNReal.pow_lt_top hct.lt_top) hρtop
        · rw [LRCurve.rhoLength_const_mul _ _ hct, ← one_le_pow_iff two_ne_zero, mul_pow, ← hc]
          gcongr
          exact hlen γ hγ
      have hX : (⨅ ρ ∈ {ρ ∈ densitiesP0 univ | ∀ γ ∈ Γ, 1 ≤ γ.rhoLength ρ}, rhoArea ρ univ) ≤
          c ^ 2 * rhoArea ρ univ :=
        iInf₂_le_of_le _ hmem (rhoArea_const_mul _ _ hct).le
      have hc' : (c ^ 2)⁻¹ = L := by
        calc (c ^ 2)⁻¹ = c ^ 2 * L * (c ^ 2)⁻¹ := by rw [hc, one_mul]
          _ = L := by
            rw [mul_comm (c ^ 2) L, mul_assoc,
              ENNReal.mul_inv_cancel (pow_ne_zero 2 hc0) (ENNReal.pow_ne_top hct), mul_one]
      refine le_trans (le_of_eq ?_) (ENNReal.inv_le_inv.2 hX)
      rw [ENNReal.mul_inv (Or.inr hρtop.ne) (Or.inl (ENNReal.pow_ne_top hct)), hc',
        div_eq_mul_inv]
  · rw [ENNReal.inv_iInf]
    refine iSup_le fun ρ => ?_
    rw [ENNReal.inv_iInf]
    refine iSup_le fun hρ => ?_
    obtain ⟨⟨hρm, hρ0, hρtop⟩, hρ1⟩ := hρ
    refine le_iSup₂_of_le ρ ⟨hρm, hρ0, hρtop⟩ ?_
    have hL1 : 1 ≤ ⨅ γ ∈ Γ, γ.rhoLength ρ ^ 2 :=
      le_iInf₂ fun γ hγ => one_le_pow_of_one_le' (hρ1 γ hγ) 2
    calc (rhoArea ρ univ)⁻¹ = 1 / rhoArea ρ univ := (one_div _).symm
      _ ≤ _ := ENNReal.div_le_div_right hL1 _

/-- (3.5)–(3.6): `λ(Γ) = sup_{ρ ∈ P₃} m_ρ(D)`,
`P₃ = {ρ ∈ P₀ : inf_γ l_ρ(γ) = m_ρ(D)}` (for a non-empty family of finite extremal length). -/
theorem eq3_5 (Γ : Set LRCurve) (_hne : Γ.Nonempty) (hfin : extremalLength Γ < ⊤) :
    extremalLength Γ =
      ⨆ ρ ∈ {ρ ∈ densitiesP0 univ | (⨅ γ ∈ Γ, γ.rhoLength ρ) = rhoArea ρ univ},
        rhoArea ρ univ := by
  have hmono : Monotone fun x : ℝ≥0∞ => x ^ 2 := fun a b h => pow_le_pow_left' h 2
  have htop : (fun x : ℝ≥0∞ => x ^ 2) ⊤ = ⊤ := by simp
  have hsq : ∀ ρ : ℂ → ℝ≥0∞, (⨅ γ ∈ Γ, γ.rhoLength ρ) ^ 2 = ⨅ γ ∈ Γ, γ.rhoLength ρ ^ 2 := by
    intro ρ
    have h1 : ∀ g : LRCurve → ℝ≥0∞, (⨅ γ, g γ) ^ 2 = ⨅ γ, g γ ^ 2 := fun g =>
      hmono.map_iInf_of_continuousAt (ENNReal.continuous_pow 2).continuousAt htop
    have h2 : ∀ (γ : LRCurve) (g : γ ∈ Γ → ℝ≥0∞), (⨅ h, g h) ^ 2 = ⨅ h, g h ^ 2 := fun γ g =>
      hmono.map_iInf_of_continuousAt (ENNReal.continuous_pow 2).continuousAt htop
    rw [h1]
    exact iInf_congr fun γ => h2 γ _
  unfold extremalLength extremalLengthIn at hfin ⊢
  apply le_antisymm
  · refine iSup₂_le fun ρ hρ => ?_
    have hρ' := hρ
    obtain ⟨hρm, hρ0, hρtop⟩ := hρ
    have hle : (⨅ γ ∈ Γ, γ.rhoLength ρ ^ 2) / rhoArea ρ univ ≤
        ⨆ ρ ∈ densitiesP0 univ, (⨅ γ ∈ Γ, γ.rhoLength ρ ^ 2) / rhoArea ρ univ :=
      le_iSup₂_of_le ρ hρ' le_rfl
    rw [← hsq ρ] at hle ⊢
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, (⨅ γ ∈ Γ, γ.rhoLength ρ) = ℓ := ⟨_, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m, rhoArea ρ univ = m := ⟨_, rfl⟩
    rw [hℓ, hm] at hle ⊢
    rw [hm] at hρ0 hρtop
    rcases eq_or_ne ℓ 0 with hℓ0 | hℓ0
    · rw [hℓ0]
      simp
    rcases eq_or_ne ℓ ⊤ with hℓt | hℓt
    · -- `λ(Γ) = ∞` would contradict `hfin`
      exfalso
      rw [hℓt, ENNReal.pow_eq_top_iff.2 ⟨rfl, two_ne_zero⟩,
        ENNReal.top_div_of_ne_top hρtop.ne] at hle
      exact lt_irrefl _ (hle.trans_lt hfin)
    -- rescale `ρ` by `c = ℓ / m`, so that `inf_γ l_{cρ}(γ) = m_{cρ} = ℓ² / m`
    have hc0 : ℓ / m ≠ 0 := ENNReal.div_ne_zero.2 ⟨hℓ0, hρtop.ne⟩
    have hct : ℓ / m ≠ ⊤ := ENNReal.div_ne_top hℓt hρ0.ne'
    have hcm : ℓ / m * m = ℓ := ENNReal.div_mul_cancel hρ0.ne' hρtop.ne
    have harea : rhoArea (fun z => ℓ / m * ρ z) univ = ℓ / m * ℓ := by
      rw [rhoArea_const_mul _ _ hct, hm, sq, mul_assoc, hcm]
    have hlen : ⨅ γ ∈ Γ, γ.rhoLength (fun z => ℓ / m * ρ z) = ℓ / m * ℓ := by
      simp only [LRCurve.rhoLength_const_mul _ _ hct, ← ENNReal.mul_iInf_of_ne hc0 hct, hℓ]
    refine le_iSup₂_of_le (fun z => ℓ / m * ρ z)
      ⟨⟨measurable_const.mul hρm, ?_, ?_⟩, ?_⟩ (le_of_eq ?_)
    · rw [harea]
      exact pos_iff_ne_zero.2 (mul_ne_zero hc0 hℓ0)
    · rw [harea]
      exact (ENNReal.mul_ne_top hct hℓt).lt_top
    · rw [harea, hlen]
    · rw [harea, div_eq_mul_inv, div_eq_mul_inv, mul_right_comm, sq]
  · refine iSup₂_le fun ρ hρ => ?_
    obtain ⟨⟨hρm, hρ0, hρtop⟩, hρeq⟩ := hρ
    refine le_iSup₂_of_le ρ ⟨hρm, hρ0, hρtop⟩ (le_of_eq ?_)
    rw [← hsq ρ, hρeq, sq, mul_div_assoc, ENNReal.div_self hρ0.ne' hρtop.ne, mul_one]

section Containment

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Rademacher's theorem on `(0,1)`: a map locally Lipschitz on `(0,1)` is differentiable at
almost every point of `(0,1)`. -/
theorem LocallyLipschitzOn.ae_differentiableAt_Ioo {f : ℝ → V}
    (hf : LocallyLipschitzOn (Ioo 0 1) f) :
    ∀ᵐ x, x ∈ Ioo (0 : ℝ) 1 → DifferentiableAt ℝ f x := by
  have hn : ∀ n : ℕ, ∀ᵐ x, x ∈ Ioo (1 / (n + 1 : ℝ)) (1 - 1 / (n + 1)) →
      DifferentiableAt ℝ f x := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hsub : Icc (1 / (n + 1 : ℝ)) (1 - 1 / (n + 1)) ⊆ Ioo 0 1 :=
      Icc_subset_Ioo hpos (by linarith)
    obtain ⟨K, hK⟩ := (hf.mono hsub).exists_lipschitzOnWith_of_compact isCompact_Icc
    filter_upwards [(hK.mono Ioo_subset_Icc_self).ae_differentiableWithinAt_of_mem_real]
      with x hx hxI
    exact (hx hxI).differentiableAt (Ioo_mem_nhds hxI.1 hxI.2)
  filter_upwards [ae_all_iff.2 hn] with x hx hx01
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hx01.1 (sub_pos.2 hx01.2))
  refine hx n ⟨hn.trans_le (min_le_left _ _), ?_⟩
  have := hn.trans_le (min_le_right _ _)
  linarith

omit [FiniteDimensional ℝ V] in
/-- If `h` has derivative `0` at `t` and `g` is Lipschitz near `h t`, then `g ∘ h` has
derivative `0` at `t`. -/
theorem hasDerivAt_comp_zero_of_lipschitzOnWith {g : ℝ → V} {h : ℝ → ℝ} {t : ℝ} {K : ℝ≥0}
    {U : Set ℝ} (hU : U ∈ 𝓝 (h t)) (hg : LipschitzOnWith K g U) (hh : HasDerivAt h 0 t) :
    HasDerivAt (g ∘ h) 0 t := by
  have hev : ∀ᶠ s in 𝓝 t, h s ∈ U := hh.continuousAt.preimage_mem_nhds hU
  rw [hasDerivAt_iff_isLittleO] at hh ⊢
  simp only [smul_zero, sub_zero, Function.comp_apply] at hh ⊢
  refine Asymptotics.IsBigO.trans_isLittleO ?_ hh
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [hev] with s hs
  exact hg.norm_sub_le hs (mem_of_mem_nhds hU)

end Containment

/-- A function monotone on `(0,1)` is injective on the set of points of `(0,1)` where it has
non-zero derivative (it is constant between two points with the same value). -/
theorem MonotoneOn.injOn_deriv_ne_zero {h : ℝ → ℝ} (hh : MonotoneOn h (Ioo 0 1)) :
    InjOn h {t | t ∈ Ioo (0 : ℝ) 1 ∧ DifferentiableAt ℝ h t ∧ deriv h t ≠ 0} := by
  have key : ∀ t₁ t₂, t₁ < t₂ → t₁ ∈ Ioo (0 : ℝ) 1 → t₂ ∈ Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ h t₁ → h t₁ = h t₂ → deriv h t₁ = 0 := by
    intro t₁ t₂ hlt ht₁ ht₂ hd heq
    have hsub : Icc t₁ t₂ ⊆ Ioo 0 1 := Icc_subset_Ioo ht₁.1 ht₂.2
    have hconst : ∀ s ∈ Icc t₁ t₂, h s = h t₁ := fun s hs =>
      le_antisymm ((hh (hsub hs) ht₂ hs.2).trans heq.symm.le) (hh ht₁ (hsub hs) hs.1)
    have h0 : HasDerivWithinAt h 0 (Icc t₁ t₂) t₁ :=
      (hasDerivWithinAt_const t₁ (Icc t₁ t₂) (h t₁)).congr_of_eventuallyEq
        (eventually_nhdsWithin_of_forall hconst) rfl
    exact (uniqueDiffOn_Icc hlt t₁ ⟨le_rfl, hlt.le⟩).eq_deriv _
      hd.hasDerivAt.hasDerivWithinAt h0
  rintro t₁ ⟨ht₁, hd₁, hne₁⟩ t₂ ⟨ht₂, hd₂, hne₂⟩ heq
  rcases lt_trichotomy t₁ t₂ with hlt | heq' | hgt
  · exact absurd (key t₁ t₂ hlt ht₁ ht₂ hd₁ heq) hne₁
  · exact heq'
  · exact absurd (key t₂ t₁ hgt ht₂ ht₁ hd₂ heq.symm) hne₂

/-- If `γ₁` contains `γ₂` then `l_ρ(γ₂) ≤ l_ρ(γ₁)` (used without comment in the book).  Writing
`γ₂ = γ₁ ∘ h`, a.e. on `(0,1)` either `h' = 0` (and then `γ₂' = 0`) or `|γ₂'| = |γ₁' ∘ h| h'`; one
concludes by the change of variables `s = h(t)` on the set where `h' ≠ 0`, on which `h` is
injective. -/
theorem LRCurve.rhoLength_le_of_contains {γ₁ γ₂ : LRCurve} (h12 : γ₁.Contains γ₂)
    (ρ : ℂ → ℝ≥0∞) : γ₂.rhoLength ρ ≤ γ₁.rhoLength ρ := by
  classical
  obtain ⟨h, hmono, hmaps, hlip, heq⟩ := h12
  have hA := LocallyLipschitzOn.ae_differentiableAt_Ioo γ₁.locallyLipschitzOn
  have hB := LocallyLipschitzOn.ae_differentiableAt_Ioo hlip
  -- `F'` is `ρ(γ₁) |γ₁'|`, modified to be `∞` on the null set where `γ₁` is not differentiable
  set F : ℝ → ℝ≥0∞ := fun s => ρ (γ₁.toFun s) * ‖deriv γ₁.toFun s‖ₑ with hF
  set F' : ℝ → ℝ≥0∞ := fun s => if DifferentiableAt ℝ γ₁.toFun s then F s else ⊤ with hF'
  set S : Set ℝ := Ioo 0 1 ∩ {t | DifferentiableAt ℝ h t} ∩ deriv h ⁻¹' {0}ᶜ with hS
  have hSm : MeasurableSet S :=
    (measurableSet_Ioo.inter (measurableSet_of_differentiableAt ℝ h)).inter
      (measurable_deriv h (measurableSet_singleton 0).compl)
  have hSI : S ⊆ Ioo 0 1 := fun t ht => ht.1.1
  have hsubS : S ⊆ {t | t ∈ Ioo (0 : ℝ) 1 ∧ DifferentiableAt ℝ h t ∧ deriv h t ≠ 0} :=
    fun t ht => ⟨ht.1.1, ht.1.2, ht.2⟩
  have hinj : InjOn h S := (MonotoneOn.injOn_deriv_ne_zero hmono).mono hsubS
  have hderS : ∀ t ∈ S, HasDerivWithinAt h (deriv h t) S t := fun t ht =>
    (ht.1.2 : DifferentiableAt ℝ h t).hasDerivAt.hasDerivWithinAt
  have hbound : ∀ᵐ t, t ∈ Ioo (0 : ℝ) 1 → ρ (γ₂.toFun t) * ‖deriv γ₂.toFun t‖ₑ ≤
      S.indicator (fun t => ENNReal.ofReal |deriv h t| * F' (h t)) t := by
    filter_upwards [hB] with t hdt htI
    have hdh := hdt htI
    have hev : ∀ᶠ s in 𝓝 t, s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhds htI.1 htI.2
    have hderiv : deriv γ₂.toFun t = deriv (γ₁.toFun ∘ h) t :=
      Filter.EventuallyEq.deriv_eq (hev.mono fun s hs => heq hs)
    rw [heq htI, hderiv, Function.comp_apply]
    by_cases h0 : deriv h t = 0
    · -- `h'(t) = 0`: then `γ₂'(t) = 0`
      obtain ⟨K, U, hU, hKU⟩ := γ₁.locallyLipschitzOn (hmaps htI)
      rw [isOpen_Ioo.nhdsWithin_eq (hmaps htI)] at hU
      have hh0 : HasDerivAt h 0 t := by
        rw [← h0]
        exact hdh.hasDerivAt
      rw [(hasDerivAt_comp_zero_of_lipschitzOnWith hU hKU hh0).deriv, enorm_zero, mul_zero]
      exact zero_le
    · have htS : t ∈ S := ⟨⟨htI, hdh⟩, h0⟩
      rw [indicator_of_mem htS]
      by_cases hγd : DifferentiableAt ℝ γ₁.toFun (h t)
      · have h2 : HasDerivAt (γ₁.toFun ∘ h) (deriv h t • deriv γ₁.toFun (h t)) t :=
          hγd.hasDerivAt.scomp t hdh.hasDerivAt
        rw [h2.deriv, enorm_smul, Real.enorm_eq_ofReal_abs]
        simp only [hF', hF, if_pos hγd]
        exact le_of_eq (by ring)
      · simp only [hF', if_neg hγd]
        rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 (abs_pos.2 h0)).ne']
        exact le_top
  have hFF' : ∫⁻ s in Ioo 0 1, F' s = ∫⁻ s in Ioo 0 1, F s := by
    refine setLIntegral_congr_fun_ae measurableSet_Ioo ?_
    filter_upwards [hA] with s hs hsI
    simp only [hF', if_pos (hs hsI)]
  calc γ₂.rhoLength ρ = ∫⁻ t in Ioo 0 1, ρ (γ₂.toFun t) * ‖deriv γ₂.toFun t‖ₑ := rfl
    _ ≤ ∫⁻ t in Ioo 0 1, S.indicator (fun t => ENNReal.ofReal |deriv h t| * F' (h t)) t :=
        setLIntegral_mono_ae' measurableSet_Ioo hbound
    _ ≤ ∫⁻ t, S.indicator (fun t => ENNReal.ofReal |deriv h t| * F' (h t)) t :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ t in S, ENNReal.ofReal |deriv h t| * F' (h t) := lintegral_indicator hSm _
    _ = ∫⁻ s in h '' S, F' s :=
        (lintegral_image_eq_lintegral_abs_deriv_mul hSm hderS hinj F').symm
    _ ≤ ∫⁻ s in Ioo 0 1, F' s :=
        lintegral_mono_set (by rintro _ ⟨t, ht, rfl⟩; exact hmaps (hSI ht))
    _ = γ₁.rhoLength ρ := hFF'

/-- **Theorem 3.2** (比较原理, comparison principle).  If every curve of `Γ₁` contains a curve
of `Γ₂`, then `λ(Γ₁) ≥ λ(Γ₂)`. -/
theorem thm3_2_comparison {Γ₁ Γ₂ : Set LRCurve}
    (h : ∀ γ₁ ∈ Γ₁, ∃ γ₂ ∈ Γ₂, γ₁.Contains γ₂) : extremalLength Γ₂ ≤ extremalLength Γ₁ := by
  unfold extremalLength extremalLengthIn
  refine iSup₂_le fun ρ hρ =>
    le_iSup₂_of_le ρ hρ (ENNReal.div_le_div_right (le_iInf₂ fun γ₁ hγ₁ => ?_) _)
  obtain ⟨γ₂, hγ₂, hc⟩ := h γ₁ hγ₁
  exact (iInf₂_le γ₂ hγ₂).trans (pow_le_pow_left' (LRCurve.rhoLength_le_of_contains hc ρ) 2)

/-- Restricting a density does not increase its area. -/
theorem rhoArea_indicator_le (ρ : ℂ → ℝ≥0∞) (D E : Set ℂ) :
    rhoArea (D.indicator ρ) E ≤ rhoArea ρ E := by
  unfold rhoArea
  exact lintegral_mono fun z => by by_cases hz : z ∈ D <;> simp [hz]

/-- The area of a restricted density. -/
theorem rhoArea_indicator_univ (ρ : ℂ → ℝ≥0∞) {D : Set ℂ} (hD : MeasurableSet D) :
    rhoArea (D.indicator ρ) univ = ∫⁻ z in D, ρ z ^ 2 := by
  simp only [rhoArea, Measure.restrict_univ]
  rw [← lintegral_indicator hD]
  congr 1
  funext z
  by_cases hz : z ∈ D <;> simp [hz]

/-- `P₀(ℂ)` is non-empty. -/
theorem densitiesP0_univ_nonempty : (densitiesP0 univ).Nonempty := by
  have h : rhoArea ((ball (0 : ℂ) 1).indicator 1) univ = volume (ball (0 : ℂ) 1) := by
    rw [rhoArea, Measure.restrict_univ, ← lintegral_indicator_one measurableSet_ball]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ ball (0 : ℂ) 1 <;> simp [hz]
  refine ⟨(ball (0 : ℂ) 1).indicator 1, measurable_one.indicator measurableSet_ball, ?_, ?_⟩
  · rw [h]
    exact measure_ball_pos volume 0 one_pos
  · rw [h]
    exact measure_ball_lt_top

/-- `(inf_γ l_ρ(γ))² = inf_γ l_ρ(γ)²`. -/
theorem iInf_rhoLength_sq (Γ : Set LRCurve) (ρ : ℂ → ℝ≥0∞) :
    (⨅ γ ∈ Γ, γ.rhoLength ρ) ^ 2 = ⨅ γ ∈ Γ, γ.rhoLength ρ ^ 2 := by
  have hmono : Monotone fun x : ℝ≥0∞ => x ^ 2 := fun a b h => pow_le_pow_left' h 2
  have htop : (fun x : ℝ≥0∞ => x ^ 2) ⊤ = ⊤ := by simp
  have h1 : ∀ g : LRCurve → ℝ≥0∞, (⨅ γ, g γ) ^ 2 = ⨅ γ, g γ ^ 2 := fun g =>
    hmono.map_iInf_of_continuousAt (ENNReal.continuous_pow 2).continuousAt htop
  have h2 : ∀ (γ : LRCurve) (g : γ ∈ Γ → ℝ≥0∞), (⨅ h, g h) ^ 2 = ⨅ h, g h ^ 2 := fun γ g =>
    hmono.map_iInf_of_continuousAt (ENNReal.continuous_pow 2).continuousAt htop
  rw [h1]
  exact iInf_congr fun γ => h2 γ _

/-- **Theorem 3.3 (i)** (合成原理, composition principle).  Let the curves of `Γ₁`, `Γ₂` lie in
disjoint domains `D₁`, `D₂`.  If every `γ₁ ∈ Γ₁` and every `γ₂ ∈ Γ₂` contains a curve of `Γ`,
then `1/λ(Γ) ≥ 1/λ(Γ₁) + 1/λ(Γ₂)`. -/
theorem thm3_3_composition_i {D₁ D₂ : Set ℂ} (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    (hdisj : Disjoint D₁ D₂) {Γ Γ₁ Γ₂ : Set LRCurve} (hΓ₁ : ∀ γ ∈ Γ₁, γ.trace ⊆ D₁)
    (hΓ₂ : ∀ γ ∈ Γ₂, γ.trace ⊆ D₂) (h₁ : ∀ γ₁ ∈ Γ₁, ∃ γ ∈ Γ, γ₁.Contains γ)
    (h₂ : ∀ γ₂ ∈ Γ₂, ∃ γ ∈ Γ, γ₂.Contains γ) :
    (extremalLength Γ₁)⁻¹ + (extremalLength Γ₂)⁻¹ ≤ (extremalLength Γ)⁻¹ := by
  -- for `ρ ∈ P₂(Γ)`, the restriction `ρ|_{D'}` has `l ≥ 1` on `Γ'`, so `λ(Γ')⁻¹ ≤ ∬_{D'} ρ²`
  have key : ∀ {D' : Set ℂ} {Γ' : Set LRCurve}, IsOpen D' → (∀ γ ∈ Γ', γ.trace ⊆ D') →
      (∀ γ' ∈ Γ', ∃ γ ∈ Γ, γ'.Contains γ) →
      ∀ ρ ∈ {ρ ∈ densitiesP0 univ | ∀ γ ∈ Γ, 1 ≤ γ.rhoLength ρ},
        (extremalLength Γ')⁻¹ ≤ ∫⁻ z in D', ρ z ^ 2 := by
    intro D' Γ' hD' hΓ' hc ρ hρ
    obtain ⟨⟨hρm, -, hρtop⟩, hρ1⟩ := hρ
    have hA := rhoArea_indicator_univ ρ hD'.measurableSet
    have hfin : rhoArea (D'.indicator ρ) univ < ⊤ :=
      (rhoArea_indicator_le ρ D' univ).trans_lt hρtop
    have h1 : 1 ≤ ⨅ γ' ∈ Γ', γ'.rhoLength (D'.indicator ρ) ^ 2 := by
      refine le_iInf₂ fun γ' hγ' => ?_
      obtain ⟨γ, hγ, hcont⟩ := hc γ' hγ'
      rw [LRCurve.rhoLength_congr fun z hz => indicator_of_mem (hΓ' γ' hγ' hz) ρ]
      exact one_le_pow_of_one_le' ((hρ1 γ hγ).trans (LRCurve.rhoLength_le_of_contains hcont ρ)) 2
    have hle := le_extremalLengthIn isOpen_univ univ_nonempty Γ'
      (hρm.indicator hD'.measurableSet) hfin
    rw [← hA, ENNReal.inv_le_iff_inv_le]
    calc (rhoArea (D'.indicator ρ) univ)⁻¹ = 1 / rhoArea (D'.indicator ρ) univ := (one_div _).symm
      _ ≤ _ := ENNReal.div_le_div_right h1 _
      _ ≤ extremalLength Γ' := hle
  have hinv : (extremalLength Γ)⁻¹ =
      ⨅ ρ ∈ {ρ ∈ densitiesP0 univ | ∀ γ ∈ Γ, 1 ≤ γ.rhoLength ρ}, rhoArea ρ univ := by
    rw [eq3_3 Γ, inv_inv]
  rw [hinv]
  refine le_iInf₂ fun ρ hρ => ?_
  calc (extremalLength Γ₁)⁻¹ + (extremalLength Γ₂)⁻¹
      ≤ (∫⁻ z in D₁, ρ z ^ 2) + ∫⁻ z in D₂, ρ z ^ 2 :=
        add_le_add (key hD₁ hΓ₁ h₁ ρ hρ) (key hD₂ hΓ₂ h₂ ρ hρ)
    _ = ∫⁻ z in D₁ ∪ D₂, ρ z ^ 2 := (lintegral_union hD₂.measurableSet hdisj).symm
    _ ≤ rhoArea ρ univ := lintegral_mono_set (subset_univ _)

/-- The main case of **Theorem 3.3 (ii)**: for densities `ρᵢ` restricted to `Dᵢ` with
`0 < tᵢ = inf_{Γᵢ} l_{ρᵢ}² / m(ρᵢ|_{Dᵢ}) < ∞`, the density
`ρ = (L₁/m₁) ρ₁|_{D₁} + (L₂/m₂) ρ₂|_{D₂}` (`Lᵢ = inf_{Γᵢ} l_{ρᵢ}`) has
`l_ρ(γ) ≥ t₁ + t₂` on `Γ` and `m(ρ) = t₁ + t₂`. -/
theorem thm3_3_composition_ii_aux {D₁ D₂ : Set ℂ} (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    (hdisj : Disjoint D₁ D₂) {Γ Γ₁ Γ₂ : Set LRCurve} (hΓ₁ : ∀ γ ∈ Γ₁, γ.trace ⊆ D₁)
    (hΓ₂ : ∀ γ ∈ Γ₂, γ.trace ⊆ D₂)
    (h : ∀ γ ∈ Γ, (∃ γ₁ ∈ Γ₁, γ.Contains γ₁) ∧ ∃ γ₂ ∈ Γ₂, γ.Contains γ₂)
    {ρ₁ ρ₂ : ℂ → ℝ≥0∞} (hρ₁ : ρ₁ ∈ densitiesP0 univ) (hρ₂ : ρ₂ ∈ densitiesP0 univ)
    (h₁0 : (⨅ γ ∈ Γ₁, γ.rhoLength ρ₁ ^ 2) / rhoArea (D₁.indicator ρ₁) univ ≠ 0)
    (h₁t : (⨅ γ ∈ Γ₁, γ.rhoLength ρ₁ ^ 2) / rhoArea (D₁.indicator ρ₁) univ ≠ ⊤)
    (h₂0 : (⨅ γ ∈ Γ₂, γ.rhoLength ρ₂ ^ 2) / rhoArea (D₂.indicator ρ₂) univ ≠ 0)
    (h₂t : (⨅ γ ∈ Γ₂, γ.rhoLength ρ₂ ^ 2) / rhoArea (D₂.indicator ρ₂) univ ≠ ⊤) :
    (⨅ γ ∈ Γ₁, γ.rhoLength ρ₁ ^ 2) / rhoArea (D₁.indicator ρ₁) univ +
      (⨅ γ ∈ Γ₂, γ.rhoLength ρ₂ ^ 2) / rhoArea (D₂.indicator ρ₂) univ ≤ extremalLength Γ := by
  obtain ⟨L₁, hL₁⟩ : ∃ L, (⨅ γ ∈ Γ₁, γ.rhoLength ρ₁) = L := ⟨_, rfl⟩
  obtain ⟨L₂, hL₂⟩ : ∃ L, (⨅ γ ∈ Γ₂, γ.rhoLength ρ₂) = L := ⟨_, rfl⟩
  obtain ⟨m₁, hm₁⟩ : ∃ m, rhoArea (D₁.indicator ρ₁) univ = m := ⟨_, rfl⟩
  obtain ⟨m₂, hm₂⟩ : ∃ m, rhoArea (D₂.indicator ρ₂) univ = m := ⟨_, rfl⟩
  rw [← iInf_rhoLength_sq Γ₁ ρ₁, hL₁, hm₁] at h₁0 h₁t
  rw [← iInf_rhoLength_sq Γ₂ ρ₂, hL₂, hm₂] at h₂0 h₂t
  rw [← iInf_rhoLength_sq Γ₁ ρ₁, ← iInf_rhoLength_sq Γ₂ ρ₂, hL₁, hL₂, hm₁, hm₂]
  have hm₁t : m₁ ≠ ⊤ := by
    rw [← hm₁]
    exact ((rhoArea_indicator_le ρ₁ D₁ univ).trans_lt hρ₁.2.2).ne
  have hm₂t : m₂ ≠ ⊤ := by
    rw [← hm₂]
    exact ((rhoArea_indicator_le ρ₂ D₂ univ).trans_lt hρ₂.2.2).ne
  have hL₁0 : L₁ ≠ 0 := fun h0 => h₁0 (by simp [h0])
  have hL₂0 : L₂ ≠ 0 := fun h0 => h₂0 (by simp [h0])
  have hm₁0 : m₁ ≠ 0 := fun h0 => h₁t (by rw [h0]; exact ENNReal.div_zero (pow_ne_zero 2 hL₁0))
  have hm₂0 : m₂ ≠ 0 := fun h0 => h₂t (by rw [h0]; exact ENNReal.div_zero (pow_ne_zero 2 hL₂0))
  have hL₁t : L₁ ≠ ⊤ := fun ht => h₁t (by
    rw [ht, ENNReal.pow_eq_top_iff.2 ⟨rfl, two_ne_zero⟩, ENNReal.top_div_of_ne_top hm₁t])
  have hL₂t : L₂ ≠ ⊤ := fun ht => h₂t (by
    rw [ht, ENNReal.pow_eq_top_iff.2 ⟨rfl, two_ne_zero⟩, ENNReal.top_div_of_ne_top hm₂t])
  have ha₁t : L₁ / m₁ ≠ ⊤ := ENNReal.div_ne_top hL₁t hm₁0
  have ha₂t : L₂ / m₂ ≠ ⊤ := ENNReal.div_ne_top hL₂t hm₂0
  have hsq₁ : (L₁ / m₁) ^ 2 * m₁ = L₁ ^ 2 / m₁ := by
    rw [sq, mul_assoc, ENNReal.div_mul_cancel hm₁0 hm₁t, div_eq_mul_inv, div_eq_mul_inv,
      mul_right_comm, sq]
  have hsq₂ : (L₂ / m₂) ^ 2 * m₂ = L₂ ^ 2 / m₂ := by
    rw [sq, mul_assoc, ENNReal.div_mul_cancel hm₂0 hm₂t, div_eq_mul_inv, div_eq_mul_inv,
      mul_right_comm, sq]
  have hlin₁ : L₁ / m₁ * L₁ = L₁ ^ 2 / m₁ := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm, sq]
  have hlin₂ : L₂ / m₂ * L₂ = L₂ ^ 2 / m₂ := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm, sq]
  -- the combined density
  have hσarea : rhoArea (fun z => L₁ / m₁ * D₁.indicator ρ₁ z + L₂ / m₂ * D₂.indicator ρ₂ z)
      univ = L₁ ^ 2 / m₁ + L₂ ^ 2 / m₂ := by
    have hpt : ∀ z, (L₁ / m₁ * D₁.indicator ρ₁ z + L₂ / m₂ * D₂.indicator ρ₂ z) ^ 2 =
        (L₁ / m₁ * D₁.indicator ρ₁ z) ^ 2 + (L₂ / m₂ * D₂.indicator ρ₂ z) ^ 2 := by
      intro z
      by_cases hz : z ∈ D₁
      · have hz2 : z ∉ D₂ := Set.disjoint_left.1 hdisj hz
        simp [hz, hz2]
      · simp [hz]
    have hmeas₁ : Measurable fun z => (L₁ / m₁ * D₁.indicator ρ₁ z) ^ 2 :=
      (measurable_const.mul (hρ₁.1.indicator hD₁.measurableSet)).pow_const 2
    simp only [rhoArea, hpt]
    rw [lintegral_add_left hmeas₁]
    show rhoArea (fun z => L₁ / m₁ * D₁.indicator ρ₁ z) univ +
      rhoArea (fun z => L₂ / m₂ * D₂.indicator ρ₂ z) univ = _
    rw [rhoArea_const_mul _ _ ha₁t, rhoArea_const_mul _ _ ha₂t, hm₁, hm₂, hsq₁, hsq₂]
  have hσlen : ∀ γ ∈ Γ, L₁ ^ 2 / m₁ + L₂ ^ 2 / m₂ ≤
      γ.rhoLength (fun z => L₁ / m₁ * D₁.indicator ρ₁ z + L₂ / m₂ * D₂.indicator ρ₂ z) := by
    intro γ hγ
    obtain ⟨⟨γ₁, hγ₁, hc₁⟩, ⟨γ₂, hγ₂, hc₂⟩⟩ := h γ hγ
    have e₁ : L₁ ^ 2 / m₁ ≤ γ.rhoLength (fun z => L₁ / m₁ * D₁.indicator ρ₁ z) := by
      rw [LRCurve.rhoLength_const_mul _ _ ha₁t, ← hlin₁]
      gcongr
      calc L₁ ≤ γ₁.rhoLength ρ₁ := by
            rw [← hL₁]
            exact iInf₂_le γ₁ hγ₁
        _ = γ₁.rhoLength (D₁.indicator ρ₁) :=
            (LRCurve.rhoLength_congr fun z hz => indicator_of_mem (hΓ₁ γ₁ hγ₁ hz) ρ₁).symm
        _ ≤ γ.rhoLength (D₁.indicator ρ₁) := LRCurve.rhoLength_le_of_contains hc₁ _
    have e₂ : L₂ ^ 2 / m₂ ≤ γ.rhoLength (fun z => L₂ / m₂ * D₂.indicator ρ₂ z) := by
      rw [LRCurve.rhoLength_const_mul _ _ ha₂t, ← hlin₂]
      gcongr
      calc L₂ ≤ γ₂.rhoLength ρ₂ := by
            rw [← hL₂]
            exact iInf₂_le γ₂ hγ₂
        _ = γ₂.rhoLength (D₂.indicator ρ₂) :=
            (LRCurve.rhoLength_congr fun z hz => indicator_of_mem (hΓ₂ γ₂ hγ₂ hz) ρ₂).symm
        _ ≤ γ.rhoLength (D₂.indicator ρ₂) := LRCurve.rhoLength_le_of_contains hc₂ _
    refine (add_le_add e₁ e₂).trans ?_
    unfold LRCurve.rhoLength
    refine le_trans (le_lintegral_add _ _) (le_of_eq ?_)
    refine lintegral_congr fun t => ?_
    simp only [add_mul]
  have hT0 : L₁ ^ 2 / m₁ + L₂ ^ 2 / m₂ ≠ 0 := fun h0 => h₁0 (add_eq_zero.1 h0).1
  have hTt : L₁ ^ 2 / m₁ + L₂ ^ 2 / m₂ ≠ ⊤ := ENNReal.add_ne_top.2 ⟨h₁t, h₂t⟩
  have hσm : Measurable fun z => L₁ / m₁ * D₁.indicator ρ₁ z + L₂ / m₂ * D₂.indicator ρ₂ z :=
    (measurable_const.mul (hρ₁.1.indicator hD₁.measurableSet)).add
      (measurable_const.mul (hρ₂.1.indicator hD₂.measurableSet))
  have hle := le_extremalLengthIn isOpen_univ univ_nonempty Γ hσm
    (by rw [hσarea]; exact hTt.lt_top)
  refine le_trans ?_ hle
  rw [hσarea]
  calc L₁ ^ 2 / m₁ + L₂ ^ 2 / m₂
      = (L₁ ^ 2 / m₁ + L₂ ^ 2 / m₂) ^ 2 / (L₁ ^ 2 / m₁ + L₂ ^ 2 / m₂) := by
        rw [sq (L₁ ^ 2 / m₁ + L₂ ^ 2 / m₂), mul_div_assoc, ENNReal.div_self hT0 hTt, mul_one]
    _ ≤ _ := ENNReal.div_le_div_right
        (le_iInf₂ fun γ hγ => pow_le_pow_left' (hσlen γ hγ) 2) _

/-- **Theorem 3.3 (ii)** (composition principle).  Let the curves of `Γ₁`, `Γ₂` lie in disjoint
domains `D₁`, `D₂`.  If every `γ ∈ Γ` contains a curve of `Γ₁` and a curve of `Γ₂`, then
`λ(Γ) ≥ λ(Γ₁) + λ(Γ₂)`. -/
theorem thm3_3_composition_ii {D₁ D₂ : Set ℂ} (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    (hdisj : Disjoint D₁ D₂) {Γ Γ₁ Γ₂ : Set LRCurve} (hΓ₁ : ∀ γ ∈ Γ₁, γ.trace ⊆ D₁)
    (hΓ₂ : ∀ γ ∈ Γ₂, γ.trace ⊆ D₂)
    (h : ∀ γ ∈ Γ, (∃ γ₁ ∈ Γ₁, γ.Contains γ₁) ∧ ∃ γ₂ ∈ Γ₂, γ.Contains γ₂) :
    extremalLength Γ₁ + extremalLength Γ₂ ≤ extremalLength Γ := by
  -- a single density `ρ'`, restricted to `D'`, already gives `inf_{Γ'} l² / m ≤ λ(Γ)`
  have hsingle : ∀ {D' : Set ℂ} {Γ' : Set LRCurve}, IsOpen D' → (∀ γ ∈ Γ', γ.trace ⊆ D') →
      (∀ γ ∈ Γ, ∃ γ' ∈ Γ', γ.Contains γ') → ∀ ρ ∈ densitiesP0 univ,
        (⨅ γ ∈ Γ', γ.rhoLength ρ ^ 2) / rhoArea (D'.indicator ρ) univ ≤ extremalLength Γ := by
    intro D' Γ' hD' hΓ' hc ρ hρ
    refine le_trans (ENNReal.div_le_div_right ?_ _) (le_extremalLengthIn isOpen_univ
      univ_nonempty Γ (hρ.1.indicator hD'.measurableSet)
      ((rhoArea_indicator_le ρ D' univ).trans_lt hρ.2.2))
    refine le_iInf₂ fun γ hγ => ?_
    obtain ⟨γ', hγ', hcont⟩ := hc γ hγ
    calc (⨅ γ ∈ Γ', γ.rhoLength ρ ^ 2) ≤ γ'.rhoLength ρ ^ 2 := iInf₂_le γ' hγ'
      _ = γ'.rhoLength (D'.indicator ρ) ^ 2 := by
          rw [LRCurve.rhoLength_congr fun z hz => indicator_of_mem (hΓ' γ' hγ' hz) ρ]
      _ ≤ γ.rhoLength (D'.indicator ρ) ^ 2 :=
          pow_le_pow_left' (LRCurve.rhoLength_le_of_contains hcont _) 2
  show (⨆ ρ ∈ densitiesP0 univ, (⨅ γ ∈ Γ₁, γ.rhoLength ρ ^ 2) / rhoArea ρ univ) +
    (⨆ ρ ∈ densitiesP0 univ, (⨅ γ ∈ Γ₂, γ.rhoLength ρ ^ 2) / rhoArea ρ univ) ≤ _
  refine ENNReal.biSup_add_biSup_le' densitiesP0_univ_nonempty densitiesP0_univ_nonempty
    fun ρ₁ hρ₁ ρ₂ hρ₂ => ?_
  obtain ⟨t₁, ht₁⟩ : ∃ t, (⨅ γ ∈ Γ₁, γ.rhoLength ρ₁ ^ 2) / rhoArea (D₁.indicator ρ₁) univ = t :=
    ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t, (⨅ γ ∈ Γ₂, γ.rhoLength ρ₂ ^ 2) / rhoArea (D₂.indicator ρ₂) univ = t :=
    ⟨_, rfl⟩
  have hr₁ : (⨅ γ ∈ Γ₁, γ.rhoLength ρ₁ ^ 2) / rhoArea ρ₁ univ ≤ t₁ := by
    rw [← ht₁]
    exact ENNReal.div_le_div_left (rhoArea_indicator_le _ _ _) _
  have hr₂ : (⨅ γ ∈ Γ₂, γ.rhoLength ρ₂ ^ 2) / rhoArea ρ₂ univ ≤ t₂ := by
    rw [← ht₂]
    exact ENNReal.div_le_div_left (rhoArea_indicator_le _ _ _) _
  have hs₁ : t₁ ≤ extremalLength Γ := by
    rw [← ht₁]
    exact hsingle hD₁ hΓ₁ (fun γ hγ => (h γ hγ).1) ρ₁ hρ₁
  have hs₂ : t₂ ≤ extremalLength Γ := by
    rw [← ht₂]
    exact hsingle hD₂ hΓ₂ (fun γ hγ => (h γ hγ).2) ρ₂ hρ₂
  refine (add_le_add hr₁ hr₂).trans ?_
  rcases eq_or_ne t₁ ⊤ with h1t | h1t
  · exact le_top.trans (h1t ▸ hs₁)
  rcases eq_or_ne t₂ ⊤ with h2t | h2t
  · exact le_top.trans (h2t ▸ hs₂)
  rcases eq_or_ne t₁ 0 with h10 | h10
  · rw [h10, zero_add]
    exact hs₂
  rcases eq_or_ne t₂ 0 with h20 | h20
  · rw [h20, add_zero]
    exact hs₁
  rw [← ht₁, ← ht₂]
  exact thm3_3_composition_ii_aux hD₁ hD₂ hdisj hΓ₁ hΓ₂ h hρ₁ hρ₂ (by rw [ht₁]; exact h10)
    (by rw [ht₁]; exact h1t) (by rw [ht₂]; exact h20) (by rw [ht₂]; exact h2t)

end LiZhongQC
