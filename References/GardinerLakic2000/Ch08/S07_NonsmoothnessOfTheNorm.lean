import References.GardinerLakic2000.Ch08.S06_IsometryProperty

/-!
# Gardiner–Lakic 2000, Ch. 8 §8.7 Nonsmoothness of the norm

Source `teichmuller.txt`, lines 6803–6900 (Chapter 8, §8.7).

* Lemma 2 ((8.3), [Hub76], l. 6808) — `lemma8_2`
* Definition (a function of a real variable has a second derivative at `0`, l. 6823) — `HasSecondDerivAtZero`
* Proposition 1 (l. 6822; cited in Lemma 3) — `prop8_1`
* Lemma 3 (l. 6893; cited in Steps II of §8.8–§8.9 and l. 6998) — `lemma8_3`

Not items: (8.4), (8.5) and the computations l. 6826–6891 (proof). Modelling: surface level (C0.1); `ψ²/φ` is the
chart family `ψ_x² / φ_x` (a quadratic differential), and "`ψ²/φ ∈ L¹(R)`" is `quadDiffNorm (ψ²/φ) < ∞`;
`f(t) = ‖φ + tψ‖`, `g(t) = ‖φ + itψ‖` for real `t`. The book's `L¹(X)`, `L¹(Y)` in Lemma 3 are `L¹(R)`, `L¹(R₁)`
[misprint].
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (quadDiffNorm)

/-- **Lemma 2** ((8.3), §8.7, l. 6808). For all complex `z ≠ 1`, `|(1 − z)/|1 − z| − 1| ≤ 2|z|`. -/
theorem lemma8_2 {z : ℂ} (hz : z ≠ 1) : ‖(1 - z) / (‖1 - z‖ : ℂ) - 1‖ ≤ 2 * ‖z‖ := by
  set w := 1 - z with hwdef
  have hw : w ≠ 0 := sub_ne_zero.2 hz.symm
  have hr : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hw
  have hrc : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  -- step A: ‖w/‖w‖ − w‖ = |1 − ‖w‖|
  have hA : ‖w / (‖w‖ : ℂ) - w‖ = |1 - ‖w‖| := by
    have hcast : ((1 : ℂ) - (‖w‖ : ℂ)) = ((1 - ‖w‖ : ℝ) : ℂ) := by push_cast; ring
    have e : w / (‖w‖ : ℂ) - w = (w * ((1 : ℂ) - ‖w‖)) / ‖w‖ := by
      conv_rhs => rw [mul_sub, mul_one, sub_div]
      rw [mul_div_cancel_right₀ _ hrc]
    rw [e, norm_div, norm_mul, hcast, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg w)]
    exact mul_div_cancel_left₀ _ hr.ne'
  -- step B–D
  calc ‖(1 - z) / (‖1 - z‖ : ℂ) - 1‖ = ‖w / (‖w‖ : ℂ) - 1‖ := by rw [hwdef]
    _ ≤ ‖w / (‖w‖ : ℂ) - w‖ + ‖w - 1‖ := by
        rw [show w / (‖w‖ : ℂ) - 1 = (w / (‖w‖ : ℂ) - w) + (w - 1) from by ring]
        exact norm_add_le _ _
    _ = |1 - ‖w‖| + ‖w - 1‖ := by rw [hA]
    _ ≤ ‖w - 1‖ + ‖w - 1‖ := by
        have hle : |1 - ‖w‖| ≤ ‖w - 1‖ := by
          rw [abs_sub_comm (1 : ℝ) ‖w‖]
          have := abs_norm_sub_norm_le w 1
          rwa [norm_one] at this
        linarith [hle]
    _ = 2 * ‖z‖ := by
        rw [two_mul]
        have e : w - 1 = -z := by rw [hwdef]; ring
        rw [e, norm_neg]

/-- Helper (§8.7, l. 6823). `f : ℝ → ℝ` has a second derivative at `0`: it is differentiable near `0` and its
derivative is differentiable at `0`. -/
def HasSecondDerivAtZero (f : ℝ → ℝ) : Prop :=
  ∃ ε > (0 : ℝ), (∀ t ∈ Ioo (-ε) ε, DifferentiableAt ℝ f t) ∧ DifferentiableAt ℝ (deriv f) 0

/-- Helper for **Proposition 1** (§8.7). `A(R)` is closed under `φ ↦ φ + c ψ` (`gl31_add_mem` and the homogeneity
`gl31_quadDiffNorm_smul`). -/
theorem gl81_mem_lin {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R] [IsManifold 𝓘(ℂ) ω R]
    {φ ψ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R)
    (hψ : ψ ∈ integrableHolQDSet R) (c : ℂ) : φ + c • ψ ∈ integrableHolQDSet R := by
  have hs : c • ψ ∈ integrableHolQDSet R :=
    ⟨(LiZhongQC.holQuadDiffSubmodule R).smul_mem c hψ.1, by
      rw [gl31_quadDiffNorm_smul hψ c]
      exact ENNReal.mul_lt_top enorm_lt_top hψ.2⟩
  exact gl31_add_mem hφ hs

/-- Helper for **Lemma 3** (§8.7). A quadratic differential that vanishes identically has norm `0` as soon as `R` has a
chart partition (the surface integral is an infimum over chart partitions, `⊤` when there is none). -/
theorem gl81_quadDiffNorm_zero {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R] {q : R → ℂ → ℂ}
    (hq : ∀ x z, q x z = 0) (h : ∃ (x : ℕ → R) (P : ℕ → Set R), LiZhongQC.IsChartPartition R x P) :
    quadDiffNorm q = 0 := by
  obtain ⟨x, P, hP⟩ := h
  refine le_antisymm ?_ bot_le
  show (⨅ (x : ℕ → R) (P : ℕ → Set R) (_ : LiZhongQC.IsChartPartition R x P),
    ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, (fun (_ : R) (_ : ℂ) => (1 : ℝ≥0∞)) (x i) z *
      ENNReal.ofReal ‖q (x i) z‖) ≤ 0
  refine iInf_le_of_le x (iInf_le_of_le P (iInf_le_of_le hP ?_))
  refine le_of_eq (ENNReal.tsum_eq_zero.2 fun i => ?_)
  simp [hq]

/-- Helper for **Proposition 1** (§8.7). A nonzero holomorphic quadratic differential on a connected surface has a
null zero set in every chart (the set of points near which a chart function vanishes is open and closed; analytic
zeros are isolated, hence countable). -/
theorem gl81_zeros_null {R : Type u} [TopologicalSpace R] [T2Space R] [ChartedSpace ℂ R] [ConnectedSpace R]
    [IsManifold 𝓘(ℂ) ω R] {φ : R → ℂ → ℂ} (hφ : φ ∈ LiZhongQC.holQuadDiffSubmodule R) (hφ0 : φ ≠ 0) (y : R) :
    volume {z : ℂ | z ∈ (chartAt ℂ y).target ∧ φ y z = 0} = 0 := by
  classical
  set Z : Set ℂ := {z : ℂ | z ∈ (chartAt ℂ y).target ∧ φ y z = 0} with hZ
  have hiso : ∀ z ∈ Z, Zᶜ ∈ 𝓝[≠] z := by
    intro z hz
    have hfr := LiZhongQC.s26u_frequently_regular hφ hφ0 ((chartAt ℂ y).symm z)
    filter_upwards [LiZhongQC.s26u_eventually_ne_zero hφ y hz.1 hfr] with w hw hwZ
    exact hw hwZ.2
  haveI : DiscreteTopology Z := by
    rw [discreteTopology_subtype_iff]
    intro z hz
    exact inf_principal_eq_bot.2 (hiso z hz)
  have hcount : Z.Countable := countable_coe_iff.1 (TopologicalSpace.separableSpace_iff_countable.1 inferInstance)
  exact hcount.measure_zero volume

/-- Helper for **Proposition 1** (§8.7). The `L¹` cell model of `φ, ψ ∈ A(R)` (`gl31_model`, `gl31_cells_integral`):
a measurable `S ⊆ ℂ` and integrable `F = Eφ`, `G = Eψ` with `‖φ + cψ‖ = ∫_S |F + cG|` for all `c`, `F + cG ≠ 0` a.e.
whenever `φ + cψ ≠ 0` (`gl81_zeros_null` through the cells), and `ψ²/φ ∈ L¹(R)` iff `∫_S |G|²/|F| < ∞` (the model
partition is chosen with finite `Σᵢ ∬ |ψᵢ²/φᵢ|` when `quadDiffNorm (ψ²/φ) < ⊤`; `quadDiffNorm` is the infimum). -/
theorem gl81_model {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] {φ ψ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R) (hψ : ψ ∈ integrableHolQDSet R)
    (hφ0 : φ ≠ 0) :
    ∃ (S : Set ℂ) (F G : ℂ → ℂ), MeasurableSet S ∧ IntegrableOn F S ∧ IntegrableOn G S ∧
      (∀ c : ℂ, (quadDiffNorm (φ + c • ψ)).toReal = ∫ w in S, ‖F w + c * G w‖) ∧
      (∀ c : ℂ, φ + c • ψ ≠ 0 → ∀ᵐ w ∂(volume.restrict S), F w + c * G w ≠ 0) ∧
      (quadDiffNorm (fun x z => ψ x z ^ 2 / φ x z) < ⊤ ↔
        ∫⁻ w in S, ENNReal.ofReal (‖G w‖ ^ 2 / ‖F w‖) < ⊤) := by
  classical
  -- a chart partition, with `Σᵢ ∬ |ψᵢ²/φᵢ| < ⊤` when `ψ²/φ ∈ L¹` (the norm is an infimum over partitions)
  obtain ⟨x, P, hP, hsum⟩ : ∃ (x : ℕ → R) (P : ℕ → Set R), LiZhongQC.IsChartPartition R x P ∧
      (quadDiffNorm (fun x z => ψ x z ^ 2 / φ x z) < ⊤ →
        ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖ψ (x i) z ^ 2 / φ (x i) z‖ₑ < ⊤) := by
    by_cases hlt : quadDiffNorm (fun x z => ψ x z ^ 2 / φ x z) < ⊤
    · have h := hlt
      change (⨅ (x : ℕ → R) (P : ℕ → Set R) (_ : LiZhongQC.IsChartPartition R x P),
        ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, (fun (_ : R) (_ : ℂ) => (1 : ℝ≥0∞)) (x i) z *
          ENNReal.ofReal ‖(fun x z => ψ x z ^ 2 / φ x z) (x i) z‖) < ⊤ at h
      obtain ⟨x, hx⟩ := iInf_lt_iff.1 h
      obtain ⟨P, hP'⟩ := iInf_lt_iff.1 hx
      obtain ⟨hP, hs⟩ := iInf_lt_iff.1 hP'
      refine ⟨x, P, hP, fun _ => ?_⟩
      simpa only [one_mul, ofReal_norm] using hs
    · obtain ⟨x, P, hP⟩ := gl31_exists_partition_of_ne_top hφ.2.ne
      exact ⟨x, P, hP, fun h => absurd h hlt⟩
  obtain ⟨ι, piece, t, hpm, hpU, hpd, htd⟩ := gl31_cells hP
  have hQm : ∀ m, MeasurableSet ((fun w => w + t m) '' piece m) := fun m => by
    rw [image_add_right]
    exact measurable_add_const (-t m) (hpm m).1
  have hSm : MeasurableSet (⋃ m, (fun w => w + t m) '' piece m) := MeasurableSet.iUnion hQm
  have hval : ∀ (F : ℕ → ℂ → ℂ) m, ∀ w ∈ (fun w => w + t m) '' piece m,
      ∑' m', ((fun w => w + t m') '' piece m').indicator (F m') w = F m w := by
    intro F m w hw
    rw [tsum_eq_single m fun m' hm' => indicator_of_notMem (fun hw' => Set.disjoint_left.1 (htd hm') hw' hw) _,
      indicator_of_mem hw]
  have hval0 : ∀ (F : ℕ → ℂ → ℂ) w, w ∉ ⋃ m, (fun w => w + t m) '' piece m →
      ∑' m', ((fun w => w + t m') '' piece m').indicator (F m') w = 0 := fun F w hw =>
    (tsum_congr fun m => indicator_of_notMem (fun h => hw (mem_iUnion.2 ⟨m, h⟩)) _).trans tsum_zero
  obtain ⟨E, hEdef⟩ : ∃ E : (R → ℂ → ℂ) → ℂ → ℂ, E = fun χ w =>
      ∑' m, ((fun w => w + t m) '' piece m).indicator (fun w => χ (x (ι m)) (w - t m)) w := ⟨_, rfl⟩
  have hE : ∀ χ m, ∀ w ∈ (fun w => w + t m) '' piece m, E χ w = χ (x (ι m)) (w - t m) := by
    intro χ m w hw
    rw [hEdef]
    exact hval (fun m w => χ (x (ι m)) (w - t m)) m w hw
  have hE0 : ∀ χ w, w ∉ ⋃ m, (fun w => w + t m) '' piece m → E χ w = 0 := by
    intro χ w hw
    rw [hEdef]
    exact hval0 (fun m w => χ (x (ι m)) (w - t m)) w hw
  have hGt : ∀ i, chartAt ℂ (x i) '' P i ⊆ (chartAt ℂ (x i)).target := fun i =>
    image_subset_iff.2 fun y hy => (chartAt ℂ (x i)).map_source ((hP.1 i).1 hy)
  have hcont : ∀ χ ∈ LiZhongQC.holQuadDiffSubmodule R, ∀ i,
      AEStronglyMeasurable (χ (x i)) (volume.restrict (chartAt ℂ (x i) '' P i)) := fun χ hχ i =>
    ((hχ.2 (x i)).continuousOn.mono (hGt i)).aestronglyMeasurable (hP.1 i).2
  -- the `L¹` norm of the cell function is the norm of the quadratic differential
  have hnormE : ∀ χ ∈ LiZhongQC.holQuadDiffSubmodule R,
      AEStronglyMeasurable (E χ) (volume.restrict (⋃ m, (fun w => w + t m) '' piece m)) ∧
        ∫⁻ w in ⋃ m, (fun w => w + t m) '' piece m, ‖E χ w‖ₑ = quadDiffNorm χ := by
    intro χ hχ
    have hci := gl31_cells_integral hpm hpU hpd htd (fun i => χ (x i))
    have hEe : E χ = fun w => ∑' m, ((fun w => w + t m) '' piece m).indicator
        (fun w => χ (x (ι m)) (w - t m)) w := by rw [hEdef]
    have e := LiZhongQC.s26v_surfaceIntegral_eq_tsum hχ (fun _ => (1 : ℝ≥0∞)) hP
    simp only [one_mul, ofReal_norm] at e
    refine ⟨?_, ?_⟩
    · rw [hEe]
      exact (hci.2 (hcont χ hχ)).1
    · rw [hEe, hci.1]
      exact e.symm
  have hadd : ∀ c : ℂ, ∀ w, E (φ + c • ψ) w = E φ w + c * E ψ w := by
    intro c w
    by_cases hw : w ∈ ⋃ m, (fun w => w + t m) '' piece m
    · obtain ⟨m, hm⟩ := mem_iUnion.1 hw
      simp only [hE (φ + c • ψ) m w hm, hE φ m w hm, hE ψ m w hm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · simp only [hE0 (φ + c • ψ) w hw, hE0 φ w hw, hE0 ψ w hw, mul_zero, add_zero]
  refine ⟨⋃ m, (fun w => w + t m) '' piece m, E φ, E ψ, hSm, ?_, ?_, fun c => ?_, fun c hc => ?_, ?_⟩
  · refine ⟨(hnormE φ hφ.1).1, ?_⟩
    show ∫⁻ w, ‖E φ w‖ₑ ∂(volume.restrict (⋃ m, (fun w => w + t m) '' piece m)) < ⊤
    rw [(hnormE φ hφ.1).2]
    exact hφ.2
  · refine ⟨(hnormE ψ hψ.1).1, ?_⟩
    show ∫⁻ w, ‖E ψ w‖ₑ ∂(volume.restrict (⋃ m, (fun w => w + t m) '' piece m)) < ⊤
    rw [(hnormE ψ hψ.1).2]
    exact hψ.2
  · -- the norm of `φ + cψ`
    have hχ := gl81_mem_lin hφ hψ c
    obtain ⟨hm, hn⟩ := hnormE _ hχ.1
    rw [← hn, ← integral_norm_eq_lintegral_enorm hm]
    exact (integral_congr_ae (Eventually.of_forall fun w => by rw [hadd c w])).symm
  · -- `F + cG ≠ 0` a.e.
    have hχ : φ + c • ψ ∈ LiZhongQC.holQuadDiffSubmodule R := (gl81_mem_lin hφ hψ c).1
    have hz : ∀ i, volume {z : ℂ | z ∈ (chartAt ℂ (x i)).target ∧ (φ + c • ψ) (x i) z = 0} = 0 :=
      fun i => gl81_zeros_null hχ hc (x i)
    rw [ae_iff]
    simp only [not_not]
    rw [Measure.restrict_apply' hSm]
    refine measure_mono_null (t := ⋃ m, (fun z => z + t m) ''
      {z : ℂ | z ∈ (chartAt ℂ (x (ι m))).target ∧ (φ + c • ψ) (x (ι m)) z = 0}) ?_ ?_
    · rintro w ⟨hw0, hwS⟩
      obtain ⟨m, hm⟩ := mem_iUnion.1 hwS
      obtain ⟨z, hz', rfl⟩ := hm
      refine mem_iUnion.2 ⟨m, z, ⟨hGt (ι m) ((hpm m).2 hz'), ?_⟩, rfl⟩
      have h1 : E φ (z + t m) = φ (x (ι m)) z := by
        rw [hE φ m _ ⟨z, hz', rfl⟩, add_sub_cancel_right]
      have h2 : E ψ (z + t m) = ψ (x (ι m)) z := by
        rw [hE ψ m _ ⟨z, hz', rfl⟩, add_sub_cancel_right]
      have h3 : E φ (z + t m) + c * E ψ (z + t m) = 0 := hw0
      rw [h1, h2] at h3
      simpa using h3
    · refine measure_iUnion_null fun m => ?_
      rw [image_add_right]
      rw [measure_preimage_add_right]
      exact hz (ι m)
  · -- `ψ²/φ ∈ L¹` iff `∫_S |G|²/|F| < ∞`
    have hci := gl31_cells_integral hpm hpU hpd htd (fun i z => ψ (x i) z ^ 2 / φ (x i) z)
    have hass : ∀ w, ∑' m, ((fun w => w + t m) '' piece m).indicator
        (fun w => ψ (x (ι m)) (w - t m) ^ 2 / φ (x (ι m)) (w - t m)) w = E ψ w ^ 2 / E φ w := by
      intro w
      by_cases hw : w ∈ ⋃ m, (fun w => w + t m) '' piece m
      · obtain ⟨m, hm⟩ := mem_iUnion.1 hw
        rw [hval (fun m w => ψ (x (ι m)) (w - t m) ^ 2 / φ (x (ι m)) (w - t m)) m w hm, hE φ m w hm,
          hE ψ m w hm]
      · rw [hval0 (fun m w => ψ (x (ι m)) (w - t m) ^ 2 / φ (x (ι m)) (w - t m)) w hw, hE0 φ w hw,
          hE0 ψ w hw]
        simp
    have hint_eq : ∫⁻ w in ⋃ m, (fun w => w + t m) '' piece m, ENNReal.ofReal (‖E ψ w‖ ^ 2 / ‖E φ w‖) =
        ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖ψ (x i) z ^ 2 / φ (x i) z‖ₑ := by
      rw [← hci.1]
      refine lintegral_congr fun w => ?_
      rw [hass w, ← ofReal_norm, norm_div, norm_pow]
    have hqle : quadDiffNorm (fun x z => ψ x z ^ 2 / φ x z) ≤
        ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖ψ (x i) z ^ 2 / φ (x i) z‖ₑ := by
      show (⨅ (x : ℕ → R) (P : ℕ → Set R) (_ : LiZhongQC.IsChartPartition R x P),
        ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, (fun (_ : R) (_ : ℂ) => (1 : ℝ≥0∞)) (x i) z *
          ENNReal.ofReal ‖(fun x z => ψ x z ^ 2 / φ x z) (x i) z‖) ≤ _
      refine iInf_le_of_le x (iInf_le_of_le P (iInf_le_of_le hP ?_))
      simp only [one_mul, ofReal_norm]
      exact le_rfl
    rw [hint_eq]
    exact ⟨hsum, fun h => lt_of_le_of_lt hqle h⟩

/-- Helper for `gl81_planar_back` (§8.7). Differentiation under the integral sign for difference quotients: if
`|f t − f t₀| ≤ bound · |t − t₀|` with an integrable `bound`, and `t ↦ f t w` is differentiable at `t₀` for a.e. `w`
(only at `t₀`: the Lipschitz bound is not required at nearby parameters, unlike
`hasDerivAt_integral_of_dominated_loc_of_lip`), then `t ↦ ∫ f t` has the integral of the derivatives as derivative. -/
theorem gl81_hasDerivAt_dct {μ : Measure ℂ} {f : ℝ → ℂ → ℝ} {f' bound : ℂ → ℝ} {t₀ : ℝ}
    (hint : ∀ t, Integrable (f t) μ) (hb : Integrable bound μ)
    (hlip : ∀ t, ∀ᵐ w ∂μ, |f t w - f t₀ w| ≤ bound w * |t - t₀|)
    (hd : ∀ᵐ w ∂μ, HasDerivAt (fun t => f t w) (f' w) t₀) :
    HasDerivAt (fun t => ∫ w, f t w ∂μ) (∫ w, f' w ∂μ) t₀ := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hsl : ∀ t, slope (fun t => ∫ w, f t w ∂μ) t₀ t = ∫ w, (f t w - f t₀ w) / (t - t₀) ∂μ := by
    intro t
    rw [slope_def_field, integral_div, integral_sub (hint t) (hint t₀)]
  refine (tendsto_integral_filter_of_dominated_convergence bound (Eventually.of_forall fun t =>
    (((hint t).sub (hint t₀)).div_const _).aestronglyMeasurable) ?_ hb ?_).congr fun t => (hsl t).symm
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t - t₀ ≠ 0 := sub_ne_zero.2 ht
    filter_upwards [hlip t] with w hw
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, div_le_iff₀ (abs_pos.2 ht')]
    exact hw
  · filter_upwards [hd] with w hw
    have := hasDerivAt_iff_tendsto_slope.1 hw
    refine this.congr fun t => ?_
    rw [slope_def_field]
    rfl

/-- Helper for `gl81_planar_back` (§8.7). The derivative of `t ↦ |a + t b|` at a parameter where `a + t b ≠ 0`. -/
theorem gl81_pt_deriv {a b : ℂ} {t₀ : ℝ} (h : a + (t₀ : ℂ) * b ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖a + (t : ℂ) * b‖) ((b * conj (a + (t₀ : ℂ) * b)).re / ‖a + (t₀ : ℂ) * b‖) t₀ := by
  have hz : HasDerivAt (fun t : ℝ => a + (t : ℂ) * b) b t₀ := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := t₀)).mul_const b).const_add a
    simpa using this
  have hn := hz.norm_sq
  have hpos : 0 < ‖a + (t₀ : ℂ) * b‖ := norm_pos_iff.2 h
  have hs := hn.sqrt (pow_pos hpos 2).ne'
  have e : (fun t : ℝ => ‖a + (t : ℂ) * b‖) = fun t : ℝ => √(‖a + (t : ℂ) * b‖ ^ 2) :=
    funext fun t => (Real.sqrt_sq (norm_nonneg _)).symm
  rw [e]
  convert hs using 1
  rw [Real.sqrt_sq hpos.le, Complex.inner]
  field_simp

/-- Helper for `gl81_planar_back` (§8.7). `Re(b \bar z)/|z|` is bounded by `|b|`. -/
theorem gl81_pt_k_bound (b z : ℂ) : |(b * conj z).re / ‖z‖| ≤ ‖b‖ := by
  by_cases hz : z = 0
  · simp [hz]
  · have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    calc |(b * conj z).re| ≤ ‖b * conj z‖ := Complex.abs_re_le_norm _
      _ = ‖b‖ * ‖z‖ := by rw [norm_mul, Complex.norm_conj]

/-- Helper for `gl81_planar_back` (§8.7). The unit vector map is Lipschitz away from `0`:
`|u/|u| − v/|v|| ≤ 2|u − v|/|v|` (cf. `lemma8_2`). -/
theorem gl81_pt_unit_lip (u v : ℂ) (hv : v ≠ 0) :
    ‖u / (‖u‖ : ℂ) - v / (‖v‖ : ℂ)‖ ≤ 2 * ‖u - v‖ / ‖v‖ := by
  have hr : 0 < ‖v‖ := norm_pos_iff.2 hv
  by_cases hu : u = 0
  · subst hu
    simp only [zero_div, zero_sub, norm_neg, norm_zero, norm_div, Complex.norm_real, norm_norm]
    rw [div_self hr.ne', le_div_iff₀ hr]
    linarith
  · have hN : 0 < ‖u‖ := norm_pos_iff.2 hu
    have h1 : ‖u / (‖u‖ : ℂ) - u / (‖v‖ : ℂ)‖ ≤ ‖u - v‖ / ‖v‖ := by
      have hNc : (‖u‖ : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      have hrc : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have e : u / (‖u‖ : ℂ) - u / (‖v‖ : ℂ) = u * ((‖v‖ : ℂ) - (‖u‖ : ℂ)) / ((‖u‖ : ℂ) * (‖v‖ : ℂ)) := by
        field_simp
      rw [e, norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, norm_norm, norm_norm]
      have e2 : ‖(‖v‖ : ℂ) - (‖u‖ : ℂ)‖ = |‖v‖ - ‖u‖| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [e2]
      calc ‖u‖ * |‖v‖ - ‖u‖| / (‖u‖ * ‖v‖) = |‖v‖ - ‖u‖| / ‖v‖ := by field_simp
        _ ≤ ‖u - v‖ / ‖v‖ := by
          gcongr
          rw [abs_sub_comm]
          exact abs_norm_sub_norm_le u v
    have h2 : ‖u / (‖v‖ : ℂ) - v / (‖v‖ : ℂ)‖ = ‖u - v‖ / ‖v‖ := by
      rw [← sub_div, norm_div, Complex.norm_real, norm_norm]
    calc ‖u / (‖u‖ : ℂ) - v / (‖v‖ : ℂ)‖
        ≤ ‖u / (‖u‖ : ℂ) - u / (‖v‖ : ℂ)‖ + ‖u / (‖v‖ : ℂ) - v / (‖v‖ : ℂ)‖ := by
          rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
          exact dist_triangle _ _ _
      _ ≤ ‖u - v‖ / ‖v‖ + ‖u - v‖ / ‖v‖ := add_le_add h1 h2.le
      _ = 2 * ‖u - v‖ / ‖v‖ := by ring

/-- Helper for `gl81_planar_back` (§8.7). `Re(b \bar u)/|u| = Re(b \overline{u/|u|})`, also for `u = 0`. -/
theorem gl81_pt_k_eq (b u : ℂ) : (b * conj u).re / ‖u‖ = (b * conj (u / (‖u‖ : ℂ))).re := by
  rw [map_div₀, Complex.conj_ofReal, ← mul_div_assoc, Complex.div_ofReal_re]

/-- Helper for `gl81_planar_back` (§8.7). The Lipschitz bound `|k_t − k_0| ≤ 2|b|²|t|/|a|` for the normalised
derivative `k_t = Re(b \overline{(a + t b)})/|a + t b|` (valid also at the parameter where `a + t b = 0`). -/
theorem gl81_pt_lip {a b : ℂ} (ha : a ≠ 0) (t : ℝ) :
    |(b * conj (a + (t : ℂ) * b)).re / ‖a + (t : ℂ) * b‖ - (b * conj a).re / ‖a‖| ≤
      2 * ‖b‖ ^ 2 / ‖a‖ * |t| := by
  have hr : 0 < ‖a‖ := norm_pos_iff.2 ha
  rw [gl81_pt_k_eq, gl81_pt_k_eq, ← Complex.sub_re, ← mul_sub, ← map_sub]
  calc |(b * conj (((a + (t : ℂ) * b) / (‖a + (t : ℂ) * b‖ : ℂ)) - a / (‖a‖ : ℂ))).re|
      ≤ ‖b * conj (((a + (t : ℂ) * b) / (‖a + (t : ℂ) * b‖ : ℂ)) - a / (‖a‖ : ℂ))‖ := Complex.abs_re_le_norm _
    _ = ‖b‖ * ‖((a + (t : ℂ) * b) / (‖a + (t : ℂ) * b‖ : ℂ)) - a / (‖a‖ : ℂ)‖ := by
        rw [norm_mul, Complex.norm_conj]
    _ ≤ ‖b‖ * (2 * ‖(a + (t : ℂ) * b) - a‖ / ‖a‖) := by
        gcongr
        exact gl81_pt_unit_lip _ _ ha
    _ = 2 * ‖b‖ ^ 2 / ‖a‖ * |t| := by
        have : ‖(a + (t : ℂ) * b) - a‖ = |t| * ‖b‖ := by
          rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [this]
        ring

/-- Helper for `gl81_planar_fwd` (§8.7). The tangent line inequality `|a| + t Re(b \bar a)/|a| ≤ |a + t b|`. -/
theorem gl81_pt_tangent {a b : ℂ} (ha : a ≠ 0) (t : ℝ) :
    ‖a‖ + t * ((b * conj a).re / ‖a‖) ≤ ‖a + (t : ℂ) * b‖ := by
  have hr : 0 < ‖a‖ := norm_pos_iff.2 ha
  have h1 : ((a + (t : ℂ) * b) * conj a).re ≤ ‖a + (t : ℂ) * b‖ * ‖a‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 : ((a + (t : ℂ) * b) * conj a).re = ‖a‖ ^ 2 + t * (b * conj a).re := by
    rw [add_mul, Complex.add_re, Complex.mul_conj, mul_assoc, Complex.re_ofReal_mul]
    simp [Complex.normSq_eq_norm_sq]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [h2] at h1
  have e : ‖a‖ + t * ((b * conj a).re / ‖a‖) = (‖a‖ ^ 2 + t * (b * conj a).re) / ‖a‖ := by
    field_simp
  rw [e, div_le_iff₀ hr]
  exact h1

/-- Helper for `gl81_planar_back`, `gl81_planar_fwd` (§8.7). With `X = Re(b \bar a)`, `Y = Im(b \bar a)`:
`|b|² |a|² = X² + Y²` and `|a + t b|² = |a|² + 2 t X + t² |b|²`. -/
theorem gl81_pt_norm_sq (a b : ℂ) (t : ℝ) :
    (b * conj a).re ^ 2 + (b * conj a).im ^ 2 = ‖b‖ ^ 2 * ‖a‖ ^ 2 ∧
      ‖a + (t : ℂ) * b‖ ^ 2 = ‖a‖ ^ 2 + 2 * t * (b * conj a).re + t ^ 2 * ‖b‖ ^ 2 := by
  refine ⟨?_, ?_⟩
  · have h := Complex.sq_norm (b * conj a)
    rw [Complex.normSq_apply, norm_mul, Complex.norm_conj, mul_pow] at h
    nlinarith [h]
  · rw [Complex.sq_norm, Complex.normSq_add, ← Complex.sq_norm, ← Complex.sq_norm, map_mul, Complex.conj_ofReal,
      show a * ((t : ℂ) * conj b) = (t : ℂ) * (a * conj b) by ring, Complex.re_ofReal_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    have : (a * conj b).re = (b * conj a).re := by
      rw [show a * conj b = conj (b * conj a) by simp [mul_comm], Complex.conj_re]
    rw [this]
    ring

/-- Helper for `gl81_planar_fwd` (§8.7). The second-order quotient of `t ↦ |a + t b|` at `0`:
`(|a + t b| − |a| − t Re(b \bar a)/|a|)/t² → (Im b \bar a)²/(2|a|³)`. -/
theorem gl81_pt_quot {a b : ℂ} (ha : a ≠ 0) :
    Tendsto (fun t : ℝ => (‖a + (t : ℂ) * b‖ - ‖a‖ - t * ((b * conj a).re / ‖a‖)) / t ^ 2) (𝓝[≠] 0)
      (𝓝 ((b * conj a).im ^ 2 / (2 * ‖a‖ ^ 3))) := by
  have hr : 0 < ‖a‖ := norm_pos_iff.2 ha
  set X := (b * conj a).re with hX
  set Y := (b * conj a).im with hY
  set D : ℝ → ℝ := fun t => ‖a + (t : ℂ) * b‖ + ‖a‖ + t * (X / ‖a‖) with hD
  have hc : Continuous D := by
    simp only [hD]
    fun_prop
  have hD0 : Tendsto D (𝓝 0) (𝓝 (2 * ‖a‖)) := by
    have := hc.tendsto 0
    simpa [hD, two_mul] using this
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < D t := hD0.eventually (lt_mem_nhds (by positivity))
  have hlim : Tendsto (fun t => (Y ^ 2 / ‖a‖ ^ 2) / D t) (𝓝 0) (𝓝 ((Y ^ 2 / ‖a‖ ^ 2) / (2 * ‖a‖))) :=
    tendsto_const_nhds.div hD0 (by positivity)
  have hval : (Y ^ 2 / ‖a‖ ^ 2) / (2 * ‖a‖) = Y ^ 2 / (2 * ‖a‖ ^ 3) := by
    field_simp
  rw [← hval]
  refine (tendsto_nhdsWithin_of_tendsto_nhds hlim).congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hpos] with t ht ht'
  have ht0 : t ≠ 0 := ht
  obtain ⟨h1, h2⟩ := gl81_pt_norm_sq a b t
  have key : (‖a + (t : ℂ) * b‖ - ‖a‖ - t * (X / ‖a‖)) * D t = t ^ 2 * (Y ^ 2 / ‖a‖ ^ 2) := by
    simp only [hD]
    have e : (‖a + (t : ℂ) * b‖ - ‖a‖ - t * (X / ‖a‖)) * (‖a + (t : ℂ) * b‖ + ‖a‖ + t * (X / ‖a‖)) =
        ‖a + (t : ℂ) * b‖ ^ 2 - (‖a‖ + t * (X / ‖a‖)) ^ 2 := by ring
    rw [e, h2]
    field_simp
    nlinarith [h1]
  rw [div_eq_div_iff ht'.ne' (pow_ne_zero 2 ht0)]
  linear_combination key.symm

/-- Helper for `gl81_planar_back` (§8.7). The derivative at `0` of `k_t = Re(b \overline{(a + t b)})/|a + t b|`. -/
theorem gl81_pt_deriv2 {a b : ℂ} (ha : a ≠ 0) :
    HasDerivAt (fun t : ℝ => (b * conj (a + (t : ℂ) * b)).re / ‖a + (t : ℂ) * b‖)
      ((b * conj a).im ^ 2 / ‖a‖ ^ 3) 0 := by
  have hr : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hre : ∀ t : ℝ, (b * conj (a + (t : ℂ) * b)).re = (b * conj a).re + t * ‖b‖ ^ 2 := by
    intro t
    rw [map_add, map_mul, Complex.conj_ofReal, mul_add, Complex.add_re,
      show b * ((t : ℂ) * conj b) = (t : ℂ) * (b * conj b) by ring, Complex.re_ofReal_mul, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have e : (fun t : ℝ => (b * conj (a + (t : ℂ) * b)).re / ‖a + (t : ℂ) * b‖) =
      fun t : ℝ => ((b * conj a).re + t * ‖b‖ ^ 2) / ‖a + (t : ℂ) * b‖ := funext fun t => by rw [hre t]
  rw [e]
  have h0 : a + ((0 : ℝ) : ℂ) * b ≠ 0 := by simpa using ha
  have hn := gl81_pt_deriv h0
  have hnum : HasDerivAt (fun t : ℝ => (b * conj a).re + t * ‖b‖ ^ 2) (1 * ‖b‖ ^ 2) 0 :=
    ((hasDerivAt_id (0 : ℝ)).mul_const (‖b‖ ^ 2)).const_add _
  have hq := hnum.div hn (norm_ne_zero_iff.2 h0)
  convert hq using 1
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  obtain ⟨h1, -⟩ := gl81_pt_norm_sq a b 0
  field_simp
  nlinarith [h1]

/-- Helper for `gl81_planar_back`, `gl81_planar_fwd` (§8.7). Derivative of `t ↦ ∫_S |F + t G|` at a parameter where
`F + t G ≠ 0` a.e. (dominated convergence, Lipschitz bound `|G|`). -/
theorem gl81_hasDerivAt_f {S : Set ℂ} {F G : ℂ → ℂ} (hF : IntegrableOn F S) (hG : IntegrableOn G S) {t : ℝ}
    (ht : ∀ᵐ w ∂(volume.restrict S), F w + (t : ℂ) * G w ≠ 0) :
    HasDerivAt (fun s : ℝ => ∫ w in S, ‖F w + (s : ℂ) * G w‖)
      (∫ w in S, (G w * conj (F w + (t : ℂ) * G w)).re / ‖F w + (t : ℂ) * G w‖) t := by
  have hint : ∀ t : ℝ, Integrable (fun w => ‖F w + (t : ℂ) * G w‖) (volume.restrict S) := fun t =>
    (hF.add (hG.const_mul (t : ℂ))).norm
  refine gl81_hasDerivAt_dct (f := fun s w => ‖F w + (s : ℂ) * G w‖) (bound := fun w => ‖G w‖) hint hG.norm
    (fun s => Eventually.of_forall fun w => ?_) ?_
  · show |‖F w + (s : ℂ) * G w‖ - ‖F w + (t : ℂ) * G w‖| ≤ ‖G w‖ * |s - t|
    calc |‖F w + (s : ℂ) * G w‖ - ‖F w + (t : ℂ) * G w‖|
        ≤ ‖(F w + (s : ℂ) * G w) - (F w + (t : ℂ) * G w)‖ := abs_norm_sub_norm_le _ _
      _ = ‖G w‖ * |s - t| := by
        rw [show (F w + (s : ℂ) * G w) - (F w + (t : ℂ) * G w) = ((s - t : ℝ) : ℂ) * G w by
          push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  · filter_upwards [ht] with w hw
    exact gl81_pt_deriv hw

/-- Helper for **Proposition 1** (§8.7), (b) ⇒ (a) on the plane. If `F, G ∈ L¹(S)`, `F + tG ≠ 0` a.e. for small `t` and
`∫_S |G|²/|F| < ∞`, then `t ↦ ∫_S |F + tG|` has a second derivative at `0`: the first derivative is
`∫ Re(G \overline{(F + tG)}/|F + tG|)` (dominated convergence, bound `|G|`), and its difference quotient at `0`
converges
to `∫ (Im G F̄)²/|F|³` (dominated by `2|G|²/|F|` by `lemma8_2`). -/
theorem gl81_planar_back {S : Set ℂ} {F G : ℂ → ℂ} (hF : IntegrableOn F S) (hG : IntegrableOn G S) {ε : ℝ}
    (hε : 0 < ε) (hnz : ∀ t : ℝ, |t| < ε → ∀ᵐ w ∂(volume.restrict S), F w + (t : ℂ) * G w ≠ 0)
    (hfin : ∫⁻ w in S, ENNReal.ofReal (‖G w‖ ^ 2 / ‖F w‖) < ⊤) :
    HasSecondDerivAtZero (fun t : ℝ => ∫ w in S, ‖F w + (t : ℂ) * G w‖) := by
  classical
  have hFm : AEStronglyMeasurable F (volume.restrict S) := hF.aestronglyMeasurable
  have hGm : AEStronglyMeasurable G (volume.restrict S) := hG.aestronglyMeasurable
  have hF0 : ∀ᵐ w ∂(volume.restrict S), F w ≠ 0 := by
    filter_upwards [hnz 0 (by simpa using hε)] with w hw
    simpa using hw
  have hA : ∀ t : ℝ, |t| < ε → HasDerivAt (fun s : ℝ => ∫ w in S, ‖F w + (s : ℂ) * G w‖)
      (∫ w in S, (G w * conj (F w + (t : ℂ) * G w)).re / ‖F w + (t : ℂ) * G w‖) t :=
    fun t ht => gl81_hasDerivAt_f hF hG (hnz t ht)
  -- the derivative of the first derivative at `0`
  have hfinR : Integrable (fun w => 2 * (‖G w‖ ^ 2 / ‖F w‖)) (volume.restrict S) := by
    have hm : AEStronglyMeasurable (fun w => ‖G w‖ ^ 2 / ‖F w‖) (volume.restrict S) := by
      exact (((hGm.aemeasurable.norm).pow_const 2).div hFm.aemeasurable.norm).aestronglyMeasurable
    refine Integrable.const_mul ((lintegral_ofReal_ne_top_iff_integrable hm
      (Eventually.of_forall fun w => by positivity)).1 hfin.ne) 2
  have hk : ∀ s : ℝ, AEStronglyMeasurable (fun w => (G w * conj (F w + (s : ℂ) * G w)).re /
      ‖F w + (s : ℂ) * G w‖) (volume.restrict S) := by
    intro s
    have hu : AEMeasurable (fun w => F w + (s : ℂ) * G w) (volume.restrict S) :=
      hFm.aemeasurable.add (aemeasurable_const.mul hGm.aemeasurable)
    exact ((Complex.measurable_re.comp_aemeasurable (hGm.aemeasurable.mul
      (Complex.continuous_conj.measurable.comp_aemeasurable hu))).div hu.norm).aestronglyMeasurable
  have hkint : ∀ s : ℝ, Integrable (fun w => (G w * conj (F w + (s : ℂ) * G w)).re /
      ‖F w + (s : ℂ) * G w‖) (volume.restrict S) := fun s =>
    Integrable.mono' hG.norm (hk s) (Eventually.of_forall fun w => gl81_pt_k_bound _ _)
  have hC : HasDerivAt (fun s : ℝ => ∫ w in S, (G w * conj (F w + (s : ℂ) * G w)).re /
      ‖F w + (s : ℂ) * G w‖) (∫ w in S, (G w * conj (F w)).im ^ 2 / ‖F w‖ ^ 3) 0 := by
    refine gl81_hasDerivAt_dct (f := fun s w => (G w * conj (F w + (s : ℂ) * G w)).re /
      ‖F w + (s : ℂ) * G w‖) (bound := fun w => 2 * (‖G w‖ ^ 2 / ‖F w‖)) hkint hfinR
      (fun s => ?_) ?_
    · filter_upwards [hF0] with w hw
      have h := gl81_pt_lip hw s (b := G w)
      simp only [Complex.ofReal_zero, zero_mul, add_zero, sub_zero]
      calc _ ≤ 2 * ‖G w‖ ^ 2 / ‖F w‖ * |s| := h
        _ = _ := by ring
    · filter_upwards [hF0] with w hw
      exact gl81_pt_deriv2 hw
  unfold HasSecondDerivAtZero
  refine ⟨ε, hε, fun t ht => by exact (hA t (abs_lt.2 ⟨ht.1, ht.2⟩)).differentiableAt, ?_⟩
  have heq : (fun s : ℝ => ∫ w in S, (G w * conj (F w + (s : ℂ) * G w)).re / ‖F w + (s : ℂ) * G w‖) =ᶠ[𝓝 0]
      deriv (fun s : ℝ => ∫ w in S, ‖F w + (s : ℂ) * G w‖) := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.2 hε) hε] with t ht
    exact (hA t (abs_lt.2 ⟨ht.1, ht.2⟩)).deriv.symm
  exact hC.differentiableAt.congr_of_eventuallyEq heq.symm

/-- Helper for **Proposition 1** (§8.7), (a) ⇒ (b) on the plane. If `F, G ∈ L¹(S)`, `F ≠ 0` a.e. and
`t ↦ ∫_S |F + tG|` has a second derivative at `0`, then `∫_S (Im G F̄)²/|F|³ < ∞`. By convexity of `s ↦ |F + sG|` the
quotients `(|F + tG| − |F| − t Re(G F̄/|F|))/t²` are `≥ 0`, have integral `≤ C/2` for small `t > 0` (mean value theorem
for `f(s) − f(0) − s f′(0) − (C/2)s²`) and converge a.e. to `(Im G F̄)²/(2|F|³)`; Fatou. -/
theorem gl81_planar_fwd {S : Set ℂ} {F G : ℂ → ℂ} (hF : IntegrableOn F S) (hG : IntegrableOn G S)
    (hF0 : ∀ᵐ w ∂(volume.restrict S), F w ≠ 0)
    (hf : HasSecondDerivAtZero (fun t : ℝ => ∫ w in S, ‖F w + (t : ℂ) * G w‖)) :
    ∫⁻ w in S, ENNReal.ofReal ((G w * conj (F w)).im ^ 2 / ‖F w‖ ^ 3) < ⊤ := by
  classical
  have hFm : AEStronglyMeasurable F (volume.restrict S) := hF.aestronglyMeasurable
  have hGm : AEStronglyMeasurable G (volume.restrict S) := hG.aestronglyMeasurable
  set f : ℝ → ℝ := fun t => ∫ w in S, ‖F w + (t : ℂ) * G w‖ with hfdef
  set c : ℂ → ℝ := fun w => (G w * conj (F w)).re / ‖F w‖ with hcdef
  -- the first derivative at `0`
  have hnz0 : ∀ᵐ w ∂(volume.restrict S), F w + ((0 : ℝ) : ℂ) * G w ≠ 0 := by
    filter_upwards [hF0] with w hw
    simpa using hw
  have hd0 : HasDerivAt f (∫ w in S, c w) 0 := by
    have h := gl81_hasDerivAt_f hF hG hnz0
    have e : (fun w => (G w * conj (F w + ((0 : ℝ) : ℂ) * G w)).re / ‖F w + ((0 : ℝ) : ℂ) * G w‖) = c := by
      funext w
      simp [hcdef]
    rwa [e] at h
  have hf0 : f 0 = ∫ w in S, ‖F w‖ := by simp [hfdef]
  -- hypotheses on the second derivative
  obtain ⟨ε, hε, hdiff, hdd⟩ := hf
  obtain ⟨L, hL⟩ : ∃ L, HasDerivAt (deriv f) L 0 := ⟨_, hdd.hasDerivAt⟩
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), |deriv f s - deriv f 0| ≤ (|L| + 1) * |s| := by
    filter_upwards [hL.isLittleO.def zero_lt_one] with s hs
    simp only [Real.norm_eq_abs, sub_zero, smul_eq_mul, one_mul] at hs
    calc |deriv f s - deriv f 0| = |(deriv f s - deriv f 0 - s * L) + s * L| := by ring_nf
      _ ≤ |deriv f s - deriv f 0 - s * L| + |s * L| := abs_add_le _ _
      _ ≤ |s| + |s| * |L| := by rw [abs_mul]; exact add_le_add hs le_rfl
      _ = (|L| + 1) * |s| := by ring
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1 hev
  set C : ℝ := |L| + 1 with hCdef
  set δ' : ℝ := min ε δ / 2 with hδ'def
  have hδ'pos : 0 < δ' := by positivity
  have hδ'ε : δ' < ε := lt_of_lt_of_le (half_lt_self (lt_min hε hδ)) (min_le_left _ _)
  have hδ'δ : δ' < δ := lt_of_lt_of_le (half_lt_self (lt_min hε hδ)) (min_le_right _ _)
  -- the quadratic upper bound `f t − f 0 − t f′(0) ≤ (C/2) t²`
  have hup : ∀ t : ℝ, 0 ≤ t → t ≤ δ' → f t - f 0 - t * deriv f 0 ≤ C / 2 * t ^ 2 := by
    intro t ht0 htδ
    set h : ℝ → ℝ := fun s => f s - f 0 - s * deriv f 0 - C / 2 * s ^ 2 with hh
    have hhd : ∀ s ∈ Icc 0 δ', HasDerivAt h (deriv f s - deriv f 0 - C * s) s := by
      intro s hs
      have hsε : s ∈ Ioo (-ε) ε := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have h1 := (hdiff s hsε).hasDerivAt
      have h2 := ((h1.sub_const (f 0)).sub ((hasDerivAt_id s).mul_const (deriv f 0))).sub
        ((hasDerivAt_pow 2 s).const_mul (C / 2))
      exact h2.congr_deriv (by simp only [Nat.cast_ofNat]; ring)
    have hanti : AntitoneOn h (Icc 0 δ') := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 δ')
        (fun s hs => (hhd s hs).continuousAt.continuousWithinAt)
        (fun s hs => (hhd s (interior_subset hs)).differentiableAt.differentiableWithinAt) (fun s hs => ?_)
      rw [(hhd s (interior_subset hs)).deriv]
      rw [interior_Icc] at hs
      have hdist : dist s 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]
        linarith [hs.2]
      have := hδb hdist
      rw [abs_of_pos hs.1] at this
      linarith [le_abs_self (deriv f s - deriv f 0)]
    have := hanti ⟨le_rfl, hδ'pos.le⟩ ⟨ht0, htδ⟩ ht0
    simp only [hh, sub_self, zero_mul, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at this
    simp only [hfdef] at *
    linarith
  -- the second-order quotients
  set q : ℝ → ℂ → ℝ := fun t w => (‖F w + (t : ℂ) * G w‖ - ‖F w‖ - t * c w) / t ^ 2 with hqdef
  have hq_nonneg : ∀ t : ℝ, ∀ᵐ w ∂(volume.restrict S), 0 ≤ q t w := by
    intro t
    filter_upwards [hF0] with w hw
    have := gl81_pt_tangent hw t (b := G w)
    exact div_nonneg (by simp only [hcdef]; linarith) (sq_nonneg t)
  have hcm : AEStronglyMeasurable c (volume.restrict S) :=
    (((Complex.measurable_re.comp_aemeasurable (hGm.aemeasurable.mul
      (Complex.continuous_conj.measurable.comp_aemeasurable hFm.aemeasurable))).div
      hFm.aemeasurable.norm).aestronglyMeasurable)
  have hcint : Integrable c (volume.restrict S) :=
    Integrable.mono' hG.norm hcm (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs]
      exact gl81_pt_k_bound _ _)
  have hNint : ∀ t : ℝ, Integrable (fun w => ‖F w + (t : ℂ) * G w‖) (volume.restrict S) := fun t =>
    (hF.add (hG.const_mul (t : ℂ))).norm
  have hqint : ∀ t : ℝ, Integrable (q t) (volume.restrict S) := fun t =>
    (((hNint t).sub hF.norm).sub (hcint.const_mul t)).div_const _
  have hqval : ∀ t : ℝ, t ≠ 0 → ∫ w in S, q t w = (f t - f 0 - t * deriv f 0) / t ^ 2 := by
    intro t ht
    have hNF : Integrable (fun w => ‖F w + (t : ℂ) * G w‖ - ‖F w‖) (volume.restrict S) :=
      (hNint t).sub hF.norm
    have hct : Integrable (fun w => t * c w) (volume.restrict S) := hcint.const_mul t
    simp only [hqdef]
    rw [integral_div, integral_sub hNF hct, integral_sub (hNint t) hF.norm, integral_const_mul, hd0.deriv,
      hf0]
  have hqle : ∀ t : ℝ, 0 < t → t ≤ δ' → ∫ w in S, q t w ≤ C / 2 := by
    intro t ht htδ
    rw [hqval t ht.ne', div_le_iff₀ (pow_pos ht 2)]
    exact hup t ht.le htδ
  -- Fatou along `t_n = δ'/(n+1) → 0`
  set tt : ℕ → ℝ := fun n => δ' / ((n : ℝ) + 1) with htt
  have htt_pos : ∀ n, 0 < tt n := fun n => by simp only [htt]; positivity
  have htt_le : ∀ n, tt n ≤ δ' := fun n => by
    simp only [htt]
    exact div_le_self hδ'pos.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have htt_lim : Tendsto tt atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => (htt_pos n).ne'⟩
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ'
    simpa [htt, div_eq_mul_inv] using this
  have hqm : ∀ n, AEMeasurable (fun w => ENNReal.ofReal (q (tt n) w)) (volume.restrict S) := by
    intro n
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hqint _).aestronglyMeasurable.aemeasurable
  have hfat := lintegral_liminf_le' (u := atTop) hqm
  have hbound : ∀ n, ∫⁻ w in S, ENNReal.ofReal (q (tt n) w) ≤ ENNReal.ofReal (C / 2) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hqint _) (hq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hqle _ (htt_pos n) (htt_le n))
  have hliminf : ∀ᵐ w ∂(volume.restrict S), Filter.liminf (fun n => ENNReal.ofReal (q (tt n) w)) atTop =
      ENNReal.ofReal ((G w * conj (F w)).im ^ 2 / (2 * ‖F w‖ ^ 3)) := by
    filter_upwards [hF0] with w hw
    have := (gl81_pt_quot hw (b := G w)).comp htt_lim
    exact ((ENNReal.continuous_ofReal.tendsto _).comp this).liminf_eq
  have hhalf : ∫⁻ w in S, ENNReal.ofReal ((G w * conj (F w)).im ^ 2 / (2 * ‖F w‖ ^ 3)) ≤
      ENNReal.ofReal (C / 2) := by
    calc _ = ∫⁻ w in S, Filter.liminf (fun n => ENNReal.ofReal (q (tt n) w)) atTop :=
          (lintegral_congr_ae (hliminf.mono fun w hw => hw.symm))
      _ ≤ Filter.liminf (fun n => ∫⁻ w in S, ENNReal.ofReal (q (tt n) w)) atTop := hfat
      _ ≤ ENNReal.ofReal (C / 2) :=
          Filter.liminf_le_of_frequently_le' (Eventually.of_forall hbound).frequently
  have hdouble : ∀ w, ENNReal.ofReal ((G w * conj (F w)).im ^ 2 / ‖F w‖ ^ 3) =
      2 * ENNReal.ofReal ((G w * conj (F w)).im ^ 2 / (2 * ‖F w‖ ^ 3)) := by
    intro w
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rcases eq_or_ne (‖F w‖ ^ 3) 0 with h | h
    · simp [h]
    · field_simp
  calc ∫⁻ w in S, ENNReal.ofReal ((G w * conj (F w)).im ^ 2 / ‖F w‖ ^ 3)
      = 2 * ∫⁻ w in S, ENNReal.ofReal ((G w * conj (F w)).im ^ 2 / (2 * ‖F w‖ ^ 3)) := by
        rw [← lintegral_const_mul' _ _ (by norm_num)]
        exact lintegral_congr hdouble
    _ ≤ 2 * ENNReal.ofReal (C / 2) := by gcongr
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top

/-- Helper for **Proposition 1** (§8.7). `|G|²/|F| = ((Im G F̄)² + (Im (iG) F̄)²)/|F|³`, so the integral of the left
side is at most the sum of the two integrals on the right. -/
theorem gl81_sq_sum {S : Set ℂ} {F G : ℂ → ℂ} (hF : IntegrableOn F S) (hG : IntegrableOn G S) :
    ∫⁻ w in S, ENNReal.ofReal (‖G w‖ ^ 2 / ‖F w‖) ≤
      (∫⁻ w in S, ENNReal.ofReal ((G w * conj (F w)).im ^ 2 / ‖F w‖ ^ 3)) +
        ∫⁻ w in S, ENNReal.ofReal (((I * G w) * conj (F w)).im ^ 2 / ‖F w‖ ^ 3) := by
  have hFm : AEMeasurable F (volume.restrict S) := hF.aestronglyMeasurable.aemeasurable
  have hGm : AEMeasurable G (volume.restrict S) := hG.aestronglyMeasurable.aemeasurable
  have hpt : ∀ w, ENNReal.ofReal (‖G w‖ ^ 2 / ‖F w‖) =
      ENNReal.ofReal ((G w * conj (F w)).im ^ 2 / ‖F w‖ ^ 3) +
        ENNReal.ofReal (((I * G w) * conj (F w)).im ^ 2 / ‖F w‖ ^ 3) := by
    intro w
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    by_cases hw : F w = 0
    · simp [hw]
    · have hn : 0 < ‖F w‖ := norm_pos_iff.2 hw
      have him : ((I * G w) * conj (F w)).im = (G w * conj (F w)).re := by
        rw [mul_assoc]
        simp
      have hsq : (G w * conj (F w)).re ^ 2 + (G w * conj (F w)).im ^ 2 = ‖G w‖ ^ 2 * ‖F w‖ ^ 2 := by
        have h1 := Complex.sq_norm (G w * conj (F w))
        rw [Complex.normSq_apply, norm_mul, Complex.norm_conj, mul_pow] at h1
        nlinarith [h1]
      rw [him, ← add_div, add_comm, hsq]
      field_simp
  have hm : AEMeasurable (fun w => ENNReal.ofReal ((G w * conj (F w)).im ^ 2 / ‖F w‖ ^ 3))
      (volume.restrict S) := by
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    exact ((Complex.measurable_im.comp_aemeasurable (hGm.mul (Complex.continuous_conj.measurable.comp_aemeasurable
      hFm))).pow_const 2).div ((hFm.norm).pow_const 3)
  calc ∫⁻ w in S, ENNReal.ofReal (‖G w‖ ^ 2 / ‖F w‖)
      = ∫⁻ w in S, (ENNReal.ofReal ((G w * conj (F w)).im ^ 2 / ‖F w‖ ^ 3) +
        ENNReal.ofReal (((I * G w) * conj (F w)).im ^ 2 / ‖F w‖ ^ 3)) := lintegral_congr hpt
    _ = _ := lintegral_add_left' hm _
    _ ≤ _ := le_rfl

/-- Helper for **Proposition 1** (§8.7). If `φ ≠ 0` then `φ + cψ ≠ 0` for all small `c`. -/
theorem gl81_small_nonzero {R : Type u} {φ ψ : R → ℂ → ℂ} (hφ0 : φ ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : ℂ, ‖c‖ < ε → φ + c • ψ ≠ 0 := by
  by_cases h : ∃ c₀ : ℂ, φ + c₀ • ψ = 0
  · obtain ⟨c₀, hc₀⟩ := h
    have hc0 : c₀ ≠ 0 := by
      rintro rfl
      apply hφ0
      simpa using hc₀
    have hψ0 : ψ ≠ 0 := by
      rintro rfl
      apply hφ0
      simpa using hc₀
    refine ⟨‖c₀‖, norm_pos_iff.2 hc0, fun c hc hzero => ?_⟩
    have hφ : φ = -(c₀ • ψ) := eq_neg_of_add_eq_zero_left hc₀
    have h1 : (c - c₀) • ψ = 0 := by
      calc (c - c₀) • ψ = φ + c • ψ := by rw [hφ, sub_smul]; abel
        _ = 0 := hzero
    have h2 : c = c₀ := sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_right hψ0)
    rw [h2] at hc
    exact lt_irrefl _ hc
  · exact ⟨1, one_pos, fun c _ hzero => h ⟨c, hzero⟩⟩

/-- **Proposition 1** (§8.7, l. 6822). For `φ, ψ ∈ A(R)`, `φ ≠ 0`, the functions `f(t) = ‖φ + tψ‖` and
`g(t) = ‖φ + itψ‖` both have a second derivative at `t = 0` if and only if `ψ²/φ ∈ L¹(R)`. -/
theorem prop8_1 {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] {φ ψ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R) (hψ : ψ ∈ integrableHolQDSet R)
    (hφ0 : φ ≠ 0) :
    (HasSecondDerivAtZero (fun t : ℝ => (quadDiffNorm (φ + (t : ℂ) • ψ)).toReal) ∧
        HasSecondDerivAtZero (fun t : ℝ => (quadDiffNorm (φ + ((t : ℂ) * I) • ψ)).toReal)) ↔
      quadDiffNorm (fun x z => ψ x z ^ 2 / φ x z) < ⊤ := by
  obtain ⟨S, F, G, hSm, hF, hG, hnorm, hnz, hiff⟩ := gl81_model hφ hψ hφ0
  obtain ⟨ε, hε, hne⟩ := gl81_small_nonzero (ψ := ψ) hφ0
  -- the parameters `t` and `t i` give `F + tG` and `F + t (iG)`
  have hfeq : (fun t : ℝ => (quadDiffNorm (φ + (t : ℂ) • ψ)).toReal) =
      fun t : ℝ => ∫ w in S, ‖F w + (t : ℂ) * G w‖ := funext fun t => hnorm (t : ℂ)
  have hgeq : (fun t : ℝ => (quadDiffNorm (φ + ((t : ℂ) * I) • ψ)).toReal) =
      fun t : ℝ => ∫ w in S, ‖F w + (t : ℂ) * (I * G w)‖ := funext fun t => by
    rw [hnorm ((t : ℂ) * I)]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    show ‖F w + (t : ℂ) * I * G w‖ = ‖F w + (t : ℂ) * (I * G w)‖
    rw [mul_assoc]
  have hnz1 : ∀ t : ℝ, |t| < ε → ∀ᵐ w ∂(volume.restrict S), F w + (t : ℂ) * G w ≠ 0 := fun t ht =>
    hnz (t : ℂ) (hne (t : ℂ) (by rwa [Complex.norm_real, Real.norm_eq_abs]))
  have hnz2 : ∀ t : ℝ, |t| < ε → ∀ᵐ w ∂(volume.restrict S), F w + (t : ℂ) * (I * G w) ≠ 0 := fun t ht => by
    filter_upwards [hnz ((t : ℂ) * I) (hne ((t : ℂ) * I) (by
      rwa [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]))] with w hw
    rwa [mul_assoc] at hw
  have hF0 : ∀ᵐ w ∂(volume.restrict S), F w ≠ 0 := by
    filter_upwards [hnz 0 (by simpa using hφ0)] with w hw
    simpa using hw
  have hGI : IntegrableOn (fun w => I * G w) S := hG.const_mul I
  rw [hfeq, hgeq]
  constructor
  · rintro ⟨hf, hg⟩
    refine hiff.2 (lt_of_le_of_lt (gl81_sq_sum hF hG) (ENNReal.add_lt_top.2 ⟨gl81_planar_fwd hF hG hF0 hf,
      gl81_planar_fwd hF hGI hF0 hg⟩))
  · intro hlt
    have hfin := hiff.1 hlt
    refine ⟨gl81_planar_back hF hG hε hnz1 hfin, gl81_planar_back hF hGI hε hnz2 ?_⟩
    simpa [norm_mul] using hfin

/-- **Lemma 3** (§8.7, l. 6893). If `L` is a linear isometry of `A(R)` onto `A(R₁)`, then for `φ, ψ ∈ A(R)`,
`ψ²/φ ∈ L¹(R)` if and only if `L(ψ)²/L(φ) ∈ L¹(R₁)`. -/
theorem lemma8_3 {R R₁ : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] [TopologicalSpace R₁] [T2Space R₁] [ConnectedSpace R₁] [ChartedSpace ℂ R₁]
    [IsManifold 𝓘(ℂ) ω R₁] {L : (R → ℂ → ℂ) → (R₁ → ℂ → ℂ)}
    (hL : IsLinearIsometryOnto (integrableHolQDSet R) (integrableHolQDSet R₁) quadDiffNorm quadDiffNorm L)
    {φ ψ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R) (hψ : ψ ∈ integrableHolQDSet R) :
    quadDiffNorm (fun x z => ψ x z ^ 2 / φ x z) < ⊤ ↔ quadDiffNorm (fun x z => L ψ x z ^ 2 / L φ x z) < ⊤ := by
  have hL0 : L 0 = 0 := by
    have e := hL.2.2.2.2.1 0 φ hφ
    rwa [zero_smul, zero_smul] at e
  by_cases hφ0 : φ = 0
  · -- `φ = 0`: both quadratic differentials `ψ²/0` vanish identically, so both norms are `0`
    have hLφ : L φ = 0 := by rw [hφ0, hL0]
    have hRz : quadDiffNorm (fun x z => ψ x z ^ 2 / φ x z) = 0 :=
      gl81_quadDiffNorm_zero (fun x z => by subst hφ0; simp) (gl31_exists_partition_of_ne_top hφ.2.ne)
    have hR₁z : quadDiffNorm (fun x z => L ψ x z ^ 2 / L φ x z) = 0 :=
      gl81_quadDiffNorm_zero (fun x z => by rw [hLφ]; simp)
        (gl31_exists_partition_of_ne_top (hL.1 hφ).2.ne)
    rw [hRz, hR₁z]
  · have h0mem : (0 : R → ℂ → ℂ) ∈ integrableHolQDSet R :=
      ⟨(LiZhongQC.holQuadDiffSubmodule R).zero_mem, by
        rw [gl81_quadDiffNorm_zero (q := (0 : R → ℂ → ℂ)) (fun x z => rfl) (gl31_exists_partition_of_ne_top hφ.2.ne)]
        exact ENNReal.zero_lt_top⟩
    have hLφ0 : L φ ≠ 0 := fun h => hφ0 (hL.2.2.1 hφ h0mem (h.trans hL0.symm))
    have hfeq : ∀ c : ℂ, quadDiffNorm (L φ + c • L ψ) = quadDiffNorm (φ + c • ψ) := fun c => by
      have hcψ : c • ψ ∈ integrableHolQDSet R :=
        ⟨(LiZhongQC.holQuadDiffSubmodule R).smul_mem c hψ.1, by
          rw [gl31_quadDiffNorm_smul hψ c]
          exact ENNReal.mul_lt_top enorm_lt_top hψ.2⟩
      rw [← hL.2.2.2.2.1 c ψ hψ, ← hL.2.2.2.1 φ hφ (c • ψ) hcψ]
      exact hL.2.2.2.2.2 (φ + c • ψ) (gl81_mem_lin hφ hψ c)
    rw [← prop8_1 hφ hψ hφ0, ← prop8_1 (hL.1 hφ) (hL.1 hψ) hLφ0]
    have hf : (fun t : ℝ => (quadDiffNorm (L φ + (t : ℂ) • L ψ)).toReal) =
        fun t : ℝ => (quadDiffNorm (φ + (t : ℂ) • ψ)).toReal := funext fun t => by rw [hfeq (t : ℂ)]
    have hg : (fun t : ℝ => (quadDiffNorm (L φ + ((t : ℂ) * I) • L ψ)).toReal) =
        fun t : ℝ => (quadDiffNorm (φ + ((t : ℂ) * I) • ψ)).toReal := funext fun t => by
      rw [hfeq ((t : ℂ) * I)]
    rw [hf, hg]

end GardinerLakic2000
