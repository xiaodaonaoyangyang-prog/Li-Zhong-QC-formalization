import References.GardinerLakic2000.Ch08.S03_RotationalTransitivity

/-!
# Gardiner–Lakic 2000, Ch. 8 §8.4 Adjointness theorem

Source `teichmuller.txt`, lines 6723–6761 (Chapter 8, §8.4).

* Definition (a vanishing sequence in `Z`, l. 6732) — `IsVanishingSeqZ`
* Theorem 7 (l. 6734) — `thm8_7`
* Corollary 1 (l. 6746) — `cor8_7_1`
* Theorem 8 (the adjointness theorem, l. 6758; cited at l. 6677, 6765) — `thm8_8`

Modelling: surface level (C0.1): `Z = Z(R)` is A's `zSpace R` with batch B's dual norm `zNorm`; `Z₀` is A's
`zZeroSpace R`; an isometry of `Z` is a complex-linear norm-preserving bijection of `Z` (`IsLinearIsometryOnto`).
"`L` is the dual of `S`" is `L(V)(φ) = V(S(φ))`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (quadDiffNorm)

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

/-- **Definition** (§8.4, l. 6732). A vanishing sequence in `Z`: `‖wₙ‖ ≤ 1` and `wₙ(φ) → 0` for every `φ ∈ A`. -/
def IsVanishingSeqZ (w : ℕ → (R → ℂ → ℂ) → ℂ) : Prop :=
  (∀ n, w n ∈ zSpace R ∧ zNorm (w n) ≤ 1) ∧ ∀ φ ∈ integrableHolQDSet R, Tendsto (fun n => w n φ) atTop (𝓝 0)

/-- Helper for **Theorem 7** (§8.4). The `L¹` cell model of `A(R)` on a chart partition `(x, P)` with point evaluation
(`gl31_cells`, `gl31_cells_integral`): a measurable `S ⊆ ℂ` and `E` with `∫_S |E χ| = ‖χ‖` for holomorphic `χ`,
`E χ = 0` off `S`, and for every `w ∈ S` a chart point `φ_{xᵢ}(Pᵢ) ∋ z` (independent of `χ`) with `E χ w = χ_{xᵢ}(z)`.
In particular `E` is linear and locally uniform convergence in the charts gives pointwise convergence on `S`. -/
theorem gl84_cells_eval [IsManifold 𝓘(ℂ) ω R] {x : ℕ → R} {P : ℕ → Set R}
    (hP : LiZhongQC.IsChartPartition R x P) :
    ∃ (S : Set ℂ) (E : (R → ℂ → ℂ) → ℂ → ℂ), MeasurableSet S ∧
      (∀ χ ∈ LiZhongQC.holQuadDiffSubmodule R, AEStronglyMeasurable (E χ) (volume.restrict S) ∧
        ∫⁻ w in S, ‖E χ w‖ₑ = quadDiffNorm χ) ∧ (∀ χ w, w ∉ S → E χ w = 0) ∧
      ∀ w ∈ S, ∃ (i : ℕ) (z : ℂ), z ∈ chartAt ℂ (x i) '' P i ∧ ∀ χ, E χ w = χ (x i) z := by
  classical
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
  refine ⟨⋃ m, (fun w => w + t m) '' piece m, E, hSm, fun χ hχ => ?_, hE0, fun w hw => ?_⟩
  · have hci := gl31_cells_integral hpm hpU hpd htd (fun i => χ (x i))
    have hEe : E χ = fun w => ∑' m, ((fun w => w + t m) '' piece m).indicator
        (fun w => χ (x (ι m)) (w - t m)) w := by rw [hEdef]
    have e := LiZhongQC.s26v_surfaceIntegral_eq_tsum hχ (fun _ => (1 : ℝ≥0∞)) hP
    simp only [one_mul, ofReal_norm] at e
    refine ⟨?_, ?_⟩
    · rw [hEe]
      exact (hci.2 (hcont χ hχ)).1
    · rw [hEe, hci.1]
      exact e.symm
  · obtain ⟨m, hm⟩ := mem_iUnion.1 hw
    obtain ⟨z0, hz0, rfl⟩ := hm
    refine ⟨ι m, z0, (hpm m).2 hz0, fun χ => ?_⟩
    rw [hE χ m _ ⟨z0, hz0, rfl⟩, add_sub_cancel_right]

/-- Helper for **Theorem 7** (§8.4). Compactness of unit vectors of `A(R)`: a sequence of unit vectors has a subsequence
converging locally uniformly in every chart to some `ψ ∈ A(R)` (Montel, `gl31_montel`; the limit is holomorphic, obeys
the transformation law and has `‖ψ‖ ≤ 1` by Fatou), and `‖φₖ − ψ‖ → 1 − ‖ψ‖` (Brezis–Lieb in `L¹`: the functions
`|fₖ| − |fₖ − f|` tend pointwise to `|f|` and are dominated by `|f|`; the `L¹` cell model of `gl31_model`). -/
theorem gl84_limit [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {φ : ℕ → R → ℂ → ℂ}
    (hφ : ∀ n, φ n ∈ integrableHolQDSet R ∧ quadDiffNorm (φ n) = 1) :
    ∃ (σ : ℕ → ℕ) (ψ : R → ℂ → ℂ), StrictMono σ ∧ ψ ∈ integrableHolQDSet R ∧
      (∀ y : R, TendstoLocallyUniformlyOn (fun k => φ (σ k) y) (ψ y) atTop (chartAt ℂ y).target) ∧
      Tendsto (fun k => (quadDiffNorm (φ (σ k) - ψ)).toReal) atTop (𝓝 (1 - (quadDiffNorm ψ).toReal)) := by
  classical
  have hφA : ∀ n, φ n ∈ integrableHolQDSet R := fun n => (hφ n).1
  obtain ⟨σ, hσ, g, hg⟩ := gl31_montel (fun n => (hφA n).1) ENNReal.one_ne_top (fun n => ((hφ n).2).le)
  -- the limit differential
  set ψ : R → ℂ → ℂ := fun y z => (chartAt ℂ y).target.indicator (g y) z with hψ
  have hψt : ∀ y z, z ∈ (chartAt ℂ y).target → ψ y z = g y z := fun y z hz => indicator_of_mem hz _
  have hlim : ∀ y z, z ∈ (chartAt ℂ y).target → Tendsto (fun k => φ (σ k) y z) atTop (𝓝 (ψ y z)) := by
    intro y z hz
    rw [hψt y z hz]
    exact (hg y).tendsto_at hz
  have hψhol : ψ ∈ LiZhongQC.holQuadDiffSubmodule R := by
    refine ⟨⟨fun y z hz => indicator_of_notMem hz _, fun x y z hz hzs => ?_⟩, fun y => ?_⟩
    · have hτ : LiZhongQC.chartTransition x y z ∈ (chartAt ℂ x).target :=
        (chartAt ℂ x).map_source hzs
      have h1 := hlim y z hz
      have h2 : Tendsto (fun k => φ (σ k) y z) atTop
          (𝓝 (ψ x (LiZhongQC.chartTransition x y z) * deriv (LiZhongQC.chartTransition x y) z ^ (2 : ℤ) *
            conj (deriv (LiZhongQC.chartTransition x y) z) ^ (0 : ℤ))) := by
        have h3 := ((hlim x _ hτ).mul_const (deriv (LiZhongQC.chartTransition x y) z ^ (2 : ℤ))).mul_const
          (conj (deriv (LiZhongQC.chartTransition x y) z) ^ (0 : ℤ))
        refine h3.congr fun k => ?_
        exact ((hφA (σ k)).1.1.2 x y z hz hzs).symm
      exact tendsto_nhds_unique h1 h2
    · have h1 : DifferentiableOn ℂ (g y) (chartAt ℂ y).target :=
        (hg y).differentiableOn (Eventually.of_forall fun k => ((hφA (σ k)).1.2 y)) (chartAt ℂ y).open_target
      exact h1.congr fun z hz => hψt y z hz
  -- a chart partition and the cell model
  obtain ⟨x, P, hP⟩ := gl31_exists_partition_of_ne_top (hφA 0).2.ne
  obtain ⟨S, E, hSm, hnormE, hE0, heval⟩ := gl84_cells_eval hP
  have hEsub : ∀ k w, E (φ (σ k) - ψ) w = E (φ (σ k)) w - E ψ w := by
    intro k w
    by_cases hw : w ∈ S
    · obtain ⟨i, z, -, hz⟩ := heval w hw
      rw [hz, hz, hz]
      rfl
    · rw [hE0 _ w hw, hE0 _ w hw, hE0 _ w hw, sub_zero]
  have hGt : ∀ i, chartAt ℂ (x i) '' P i ⊆ (chartAt ℂ (x i)).target := fun i =>
    image_subset_iff.2 fun y hy => (chartAt ℂ (x i)).map_source ((hP.1 i).1 hy)
  have hconv : ∀ w ∈ S, Tendsto (fun k => E (φ (σ k)) w) atTop (𝓝 (E ψ w)) := by
    intro w hw
    obtain ⟨i, z, hz, hEw⟩ := heval w hw
    simp only [hEw]
    exact hlim (x i) z (hGt i hz)
  have hone : ∀ k, ∫⁻ w in S, ‖E (φ (σ k)) w‖ₑ = 1 := fun k => by
    rw [(hnormE _ (hφA (σ k)).1).2, (hφ (σ k)).2]
  -- `‖ψ‖ ≤ 1` by Fatou
  have hmeas : ∀ k, AEMeasurable (fun w => ‖E (φ (σ k)) w‖ₑ) (volume.restrict S) := fun k =>
    (hnormE _ (hφA (σ k)).1).1.enorm
  have hfat := lintegral_liminf_le' (u := atTop) hmeas
  have hpt : ∀ᵐ w ∂(volume.restrict S), Filter.liminf (fun k => ‖E (φ (σ k)) w‖ₑ) atTop = ‖E ψ w‖ₑ := by
    filter_upwards [ae_restrict_mem hSm] with w hw
    exact ((continuous_enorm.tendsto _).comp (hconv w hw)).liminf_eq
  have hψle : quadDiffNorm ψ ≤ 1 := by
    rw [← (hnormE ψ hψhol).2]
    calc ∫⁻ w in S, ‖E ψ w‖ₑ = ∫⁻ w in S, Filter.liminf (fun k => ‖E (φ (σ k)) w‖ₑ) atTop :=
          (lintegral_congr_ae (hpt.mono fun w hw => hw.symm))
      _ ≤ Filter.liminf (fun k => ∫⁻ w in S, ‖E (φ (σ k)) w‖ₑ) atTop := hfat
      _ = 1 := by simp [hone]
  have hψA : ψ ∈ integrableHolQDSet R := ⟨hψhol, lt_of_le_of_lt hψle ENNReal.one_lt_top⟩
  have hint : ∀ χ ∈ integrableHolQDSet R, Integrable (E χ) (volume.restrict S) := fun χ hχ =>
    ⟨(hnormE χ hχ.1).1, by
      show ∫⁻ w, ‖E χ w‖ₑ ∂(volume.restrict S) < ⊤
      rw [(hnormE χ hχ.1).2]
      exact hχ.2⟩
  have hsubA : ∀ k, φ (σ k) - ψ ∈ integrableHolQDSet R := fun k => by
    have hm := (LiZhongQC.holQuadDiffSubmodule R).sub_mem (hφA (σ k)).1 hψhol
    refine ⟨hm, ?_⟩
    rw [← (hnormE _ hm).2]
    calc ∫⁻ w in S, ‖E (φ (σ k) - ψ) w‖ₑ ≤ ∫⁻ w in S, (‖E (φ (σ k)) w‖ₑ + ‖E ψ w‖ₑ) :=
          lintegral_mono fun w => by rw [hEsub k w]; exact enorm_sub_le
      _ = (∫⁻ w in S, ‖E (φ (σ k)) w‖ₑ) + ∫⁻ w in S, ‖E ψ w‖ₑ := lintegral_add_left' (hmeas k) _
      _ < ⊤ := by
          rw [hone k, (hnormE ψ hψhol).2]
          exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hψA.2⟩
  refine ⟨σ, ψ, hσ, hψA, fun y => (hg y).congr_right fun z hz => (hψt y z hz).symm, ?_⟩
  -- Brezis–Lieb in `L¹`
  have hsubint : ∀ k, Integrable (fun w => E (φ (σ k)) w - E ψ w) (volume.restrict S) := fun k =>
    (hint _ (hφA (σ k))).sub (hint _ hψA)
  have hn1 : ∀ k, ∫ w in S, ‖E (φ (σ k)) w‖ = 1 := fun k => by
    rw [integral_norm_eq_lintegral_enorm (hint _ (hφA (σ k))).aestronglyMeasurable, hone k]
    simp
  have hnk : ∀ k, ∫ w in S, ‖E (φ (σ k)) w - E ψ w‖ = (quadDiffNorm (φ (σ k) - ψ)).toReal := fun k => by
    rw [integral_norm_eq_lintegral_enorm (hsubint k).aestronglyMeasurable,
      ← (hnormE _ (hsubA k).1).2]
    congr 2
    funext w
    rw [hEsub k w]
  have hnψ : ∫ w in S, ‖E ψ w‖ = (quadDiffNorm ψ).toReal := by
    rw [integral_norm_eq_lintegral_enorm (hint _ hψA).aestronglyMeasurable, ← (hnormE ψ hψhol).2]
  have hdct : Tendsto (fun k => ∫ w in S, (‖E (φ (σ k)) w‖ - ‖E (φ (σ k)) w - E ψ w‖)) atTop
      (𝓝 (∫ w in S, ‖E ψ w‖)) := by
    refine tendsto_integral_of_dominated_convergence (fun w => ‖E ψ w‖) (fun k => ?_) (hint _ hψA).norm
      (fun k => Eventually.of_forall fun w => ?_) ?_
    · exact ((hint _ (hφA (σ k))).norm.sub (hsubint k).norm).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      calc _ ≤ ‖E (φ (σ k)) w - (E (φ (σ k)) w - E ψ w)‖ := abs_norm_sub_norm_le _ _
        _ = ‖E ψ w‖ := by rw [sub_sub_cancel]
    · filter_upwards [ae_restrict_mem hSm] with w hw
      have h1 := hconv w hw
      have h2 : Tendsto (fun k => E (φ (σ k)) w - E ψ w) atTop (𝓝 0) := tendsto_sub_nhds_zero_iff.2 h1
      have h3 := ((continuous_norm.tendsto _).comp h1).sub ((continuous_norm.tendsto _).comp h2)
      simpa using h3
  have hrew : ∀ k, ∫ w in S, (‖E (φ (σ k)) w‖ - ‖E (φ (σ k)) w - E ψ w‖) =
      1 - (quadDiffNorm (φ (σ k) - ψ)).toReal := fun k => by
    rw [integral_sub (hint _ (hφA (σ k))).norm (hsubint k).norm, hn1 k, hnk k]
  simp only [hrew, hnψ] at hdct
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub hdct
  refine this.congr fun k => ?_
  ring

/-- Helper for **Theorem 7** (§8.4). A functional of `Z₀` tends to `0` along a norm-bounded sequence of `A(R)` that
converges to `0` locally uniformly: otherwise a subsequence is bounded away from `0` in norm, and its normalisation is a
degenerating sequence on which `|v|` stays away from `0`, contradicting `β(v) = 0`. -/
theorem gl84_beta_tail [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {v : (R → ℂ → ℂ) → ℂ}
    (hv : v ∈ zZeroSpace R) {χ : ℕ → R → ℂ → ℂ} (hχ : ∀ n, χ n ∈ integrableHolQDSet R) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hb : ∀ n, quadDiffNorm (χ n) ≤ C)
    (h0 : ∀ y : R, TendstoLocallyUniformlyOn (fun n => χ n y) 0 atTop (chartAt ℂ y).target) :
    Tendsto (fun n => v (χ n)) atTop (𝓝 0) := by
  classical
  obtain ⟨⟨hadd, hsmul, K, hK⟩, hβ⟩ := hv
  by_contra hnot
  rw [Metric.tendsto_nhds] at hnot
  push_neg at hnot
  obtain ⟨ε, hε, hfreq⟩ := hnot
  obtain ⟨σ, hσ, hσε⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hε' : ∀ k, ε ≤ ‖v (χ (σ k))‖ := fun k => by
    have := hσε k
    rwa [dist_zero_right] at this
  set r : ℕ → ℝ := fun k => (quadDiffNorm (χ (σ k))).toReal with hr
  have hKr : ∀ k, ε ≤ K * r k := fun k => (hε' k).trans (hK _ (hχ _))
  have hKpos : 0 < K := by
    by_contra hK0
    push_neg at hK0
    have := hKr 0
    have h0 : K * r 0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hK0 ENNReal.toReal_nonneg
    linarith
  have hrlow : ∀ k, ε / K ≤ r k := fun k => by
    rw [div_le_iff₀ hKpos]
    linarith [hKr k]
  have hrpos : ∀ k, 0 < r k := fun k => lt_of_lt_of_le (by positivity) (hrlow k)
  have hrup : ∀ k, r k ≤ C.toReal := fun k => ENNReal.toReal_mono hC (hb _)
  have hCpos : 0 < C.toReal := lt_of_lt_of_le (hrpos 0) (hrup 0)
  -- the normalisation
  set φ : ℕ → R → ℂ → ℂ := fun k => (((r k)⁻¹ : ℝ) : ℂ) • χ (σ k) with hφdef
  have hmem : ∀ k, φ k ∈ integrableHolQDSet R := fun k =>
    ⟨(LiZhongQC.holQuadDiffSubmodule R).smul_mem _ (hχ _).1, by
      rw [gl31_quadDiffNorm_smul (hχ _)]
      exact ENNReal.mul_lt_top enorm_lt_top (hχ _).2⟩
  have hnorm : ∀ k, quadDiffNorm (φ k) = 1 := fun k => by
    rw [gl31_quadDiffNorm_smul (hχ _), ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (hrpos k)), ← ENNReal.ofReal_toReal (ne_top_of_lt (hχ (σ k)).2)]
    rw [← ENNReal.ofReal_mul (inv_pos.2 (hrpos k)).le]
    show ENNReal.ofReal ((r k)⁻¹ * r k) = 1
    rw [inv_mul_cancel₀ (hrpos k).ne', ENNReal.ofReal_one]
  have hloc : ∀ y : R, TendstoLocallyUniformlyOn (fun k => φ k y) 0 atTop (chartAt ℂ y).target := by
    intro y
    have h1 := h0 y
    rw [Metric.tendstoLocallyUniformlyOn_iff] at h1 ⊢
    intro ε' hε' x hx
    obtain ⟨t, ht, hev⟩ := h1 (ε' * (ε / K)) (by positivity) x hx
    refine ⟨t, ht, ?_⟩
    filter_upwards [hσ.tendsto_atTop.eventually hev] with k hk z hz
    have h2 := hk z hz
    rw [dist_eq_norm, Pi.zero_apply, zero_sub, norm_neg] at h2 ⊢
    show ‖(((r k)⁻¹ : ℝ) : ℂ) * χ (σ k) y z‖ < ε'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hrpos k))]
    have hinv : (r k)⁻¹ ≤ K / ε := by
      rw [inv_le_comm₀ (hrpos k) (by positivity)]
      have := hrlow k
      rwa [inv_div] at *
    calc (r k)⁻¹ * ‖χ (σ k) y z‖ ≤ K / ε * ‖χ (σ k) y z‖ := by gcongr
      _ < K / ε * (ε' * (ε / K)) := by gcongr
      _ = ε' := by field_simp
  have hdeg : IsDegeneratingSeq φ := ⟨fun k => ⟨hmem k, hnorm k⟩, hloc⟩
  -- `|v (φ k)| ≥ ε / ‖C‖`
  have hvφ : ∀ k, ε / C.toReal ≤ ‖v (φ k)‖ := fun k => by
    have : v (φ k) = (((r k)⁻¹ : ℝ) : ℂ) * v (χ (σ k)) := hsmul _ _ (hχ _)
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hrpos k))]
    calc ε / C.toReal ≤ ε / r k := div_le_div_of_nonneg_left hε.le (hrpos k) (hrup k)
      _ = (r k)⁻¹ * ε := by rw [div_eq_inv_mul]
      _ ≤ (r k)⁻¹ * ‖v (χ (σ k))‖ := by gcongr; exact hε' k
  have hle : (ENNReal.ofReal (ε / C.toReal)) ≤ Filter.limsup (fun k => (‖v (φ k)‖₊ : ℝ≥0∞)) atTop := by
    refine le_trans ?_ (Filter.liminf_le_limsup)
    refine Filter.le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall fun k => ?_)
    calc ENNReal.ofReal (ε / C.toReal) ≤ ENNReal.ofReal ‖v (φ k)‖ := ENNReal.ofReal_le_ofReal (hvφ k)
      _ = (‖v (φ k)‖₊ : ℝ≥0∞) := ofReal_norm _
  have hβle : Filter.limsup (fun k => (‖v (φ k)‖₊ : ℝ≥0∞)) atTop ≤ betaSeminorm v :=
    le_iSup₂ (f := fun (φ : ℕ → R → ℂ → ℂ) (_ : IsDegeneratingSeq φ) =>
      Filter.limsup (fun n => (‖v (φ n)‖₊ : ℝ≥0∞)) atTop) φ hdeg
  rw [hβ] at hβle
  exact absurd (ENNReal.ofReal_pos.2 (by positivity)) (not_lt.2 (hle.trans hβle))

/-- Helper for **Theorem 7** (§8.4). `A(R)` is closed under `a ↦ a + c b` (`gl31_add_mem` and the homogeneity of the
norm); the same statement as `gl81_mem_lin` of the later file S07, which S04 cannot import. -/
theorem gl84_mem_lin [IsManifold 𝓘(ℂ) ω R] {a b : R → ℂ → ℂ} (ha : a ∈ integrableHolQDSet R)
    (hb : b ∈ integrableHolQDSet R) (c : ℂ) : a + c • b ∈ integrableHolQDSet R := by
  have hs : c • b ∈ integrableHolQDSet R :=
    ⟨(LiZhongQC.holQuadDiffSubmodule R).smul_mem c hb.1, by
      rw [gl31_quadDiffNorm_smul hb c]
      exact ENNReal.mul_lt_top enorm_lt_top hb.2⟩
  exact gl31_add_mem ha hs

/-- Helper for **Theorem 7** (§8.4). The sum of two elements of `Z` is in `Z`. -/
theorem gl84_zadd_mem {V W : (R → ℂ → ℂ) → ℂ} (hV : V ∈ zSpace R) (hW : W ∈ zSpace R) : V + W ∈ zSpace R := by
  obtain ⟨hVa, hVs, K, hK⟩ := hV
  obtain ⟨hWa, hWs, L, hL⟩ := hW
  refine ⟨fun a ha b hb => ?_, fun c a ha => ?_, K + L, fun a ha => ?_⟩
  · simp only [Pi.add_apply, hVa a ha b hb, hWa a ha b hb]
    ring
  · simp only [Pi.add_apply, hVs c a ha, hWs c a ha]
    ring
  · simp only [Pi.add_apply]
    calc ‖V a + W a‖ ≤ ‖V a‖ + ‖W a‖ := norm_add_le _ _
      _ ≤ K * (quadDiffNorm a).toReal + L * (quadDiffNorm a).toReal := add_le_add (hK a ha) (hL a ha)
      _ = (K + L) * (quadDiffNorm a).toReal := by ring

/-- Helper for **Theorem 7** (§8.4). Normalisation: a nonzero element of `A(R)` is a positive multiple of a unit
vector. -/
theorem gl84_normalize [IsManifold 𝓘(ℂ) ω R] {a : R → ℂ → ℂ} (ha : a ∈ integrableHolQDSet R)
    (h0 : quadDiffNorm a ≠ 0) :
    ∃ b ∈ integrableHolQDSet R, quadDiffNorm b = 1 ∧ a = (((quadDiffNorm a).toReal : ℝ) : ℂ) • b := by
  set r : ℝ := (quadDiffNorm a).toReal with hrdef
  have hr : 0 < r := ENNReal.toReal_pos h0 ha.2.ne
  refine ⟨((r⁻¹ : ℝ) : ℂ) • a, ⟨(LiZhongQC.holQuadDiffSubmodule R).smul_mem _ ha.1, ?_⟩, ?_, ?_⟩
  · rw [gl31_quadDiffNorm_smul ha]
    exact ENNReal.mul_lt_top enorm_lt_top ha.2
  · have he : ‖((r⁻¹ : ℝ) : ℂ)‖ₑ = ENNReal.ofReal r⁻¹ := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
    rw [gl31_quadDiffNorm_smul ha, he]
    calc ENNReal.ofReal r⁻¹ * quadDiffNorm a = ENNReal.ofReal r⁻¹ * ENNReal.ofReal r := by
          rw [hrdef, ENNReal.ofReal_toReal ha.2.ne]
      _ = 1 := by
          rw [← ENNReal.ofReal_mul (inv_pos.2 hr).le, inv_mul_cancel₀ hr.ne', ENNReal.ofReal_one]
  · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one, one_smul]

/-- Helper for **Theorem 7** (§8.4). A functional of `Z` is dominated by its dual norm: `|V a| ≤ ‖V‖ ‖a‖` on `A(R)`. -/
theorem gl84_dual_le [IsManifold 𝓘(ℂ) ω R] {V : (R → ℂ → ℂ) → ℂ} (hV : V ∈ zSpace R) {a : R → ℂ → ℂ}
    (ha : a ∈ integrableHolQDSet R) : ‖V a‖ ≤ zNorm V * (quadDiffNorm a).toReal := by
  obtain ⟨hadd, hsmul, K, hK⟩ := hV
  have hbdd : BddAbove (range fun b => ⨆ (_ : b ∈ integrableHolQDSet R ∧ quadDiffNorm b = 1), ‖V b‖) := by
    refine ⟨max K 0, ?_⟩
    rintro _ ⟨b, rfl⟩
    refine Real.iSup_le (fun hb => ?_) (le_max_right _ _)
    have e := hK b hb.1
    rw [hb.2, ENNReal.toReal_one, mul_one] at e
    exact e.trans (le_max_left _ _)
  by_cases h0 : quadDiffNorm a = 0
  · have e := hK a ha
    rw [h0, ENNReal.toReal_zero, mul_zero] at e
    rw [h0, ENNReal.toReal_zero, mul_zero]
    exact e
  · obtain ⟨b, hb, hb1, hab⟩ := gl84_normalize ha h0
    have hVb : ‖V b‖ ≤ zNorm V := by
      calc ‖V b‖ = ⨆ (_ : b ∈ integrableHolQDSet R ∧ quadDiffNorm b = 1), ‖V b‖ :=
            (ciSup_pos (f := fun _ => ‖V b‖) ⟨hb, hb1⟩).symm
        _ ≤ zNorm V := le_ciSup hbdd b
    have hr : 0 < (quadDiffNorm a).toReal := ENNReal.toReal_pos h0 ha.2.ne
    have : V a = (((quadDiffNorm a).toReal : ℝ) : ℂ) * V b := by
      conv_lhs => rw [hab]
      exact hsmul _ b hb
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, mul_comm]
    exact mul_le_mul_of_nonneg_right hVb hr.le

/-- Helper for **Theorem 7** (§8.4). The dual norm is approximated by unit vectors (when there are any). -/
theorem gl84_dual_approx {V : (R → ℂ → ℂ) → ℂ} (hV : V ∈ zSpace R)
    (hunit : ∃ a ∈ integrableHolQDSet R, quadDiffNorm a = 1) {η : ℝ} (hη : 0 < η) :
    ∃ a ∈ integrableHolQDSet R, quadDiffNorm a = 1 ∧ zNorm V - η < ‖V a‖ := by
  obtain ⟨hadd, hsmul, K, hK⟩ := hV
  have hbdd : BddAbove (range fun b => ⨆ (_ : b ∈ integrableHolQDSet R ∧ quadDiffNorm b = 1), ‖V b‖) := by
    refine ⟨max K 0, ?_⟩
    rintro _ ⟨b, rfl⟩
    refine Real.iSup_le (fun hb => ?_) (le_max_right _ _)
    have e := hK b hb.1
    rw [hb.2, ENNReal.toReal_one, mul_one] at e
    exact e.trans (le_max_left _ _)
  obtain ⟨a₀, ha₀, ha₀1⟩ := hunit
  have hlt : zNorm V - η < zNorm V := by linarith
  obtain ⟨b, hb⟩ := exists_lt_of_lt_ciSup hlt
  by_cases hbm : b ∈ integrableHolQDSet R ∧ quadDiffNorm b = 1
  · refine ⟨b, hbm.1, hbm.2, ?_⟩
    rwa [ciSup_pos hbm] at hb
  · have h0 : (⨆ (_ : b ∈ integrableHolQDSet R ∧ quadDiffNorm b = 1), ‖V b‖) = 0 := by
      rw [ciSup_neg hbm]
      exact Real.sSup_empty
    rw [h0] at hb
    exact ⟨a₀, ha₀, ha₀1, lt_of_lt_of_le hb (norm_nonneg _)⟩

/-- Helper for **Theorem 7** (§8.4), (⇒). For `v ∈ Z₀` and a vanishing sequence `wₙ` with `‖wₙ‖ ≤ ‖v‖`:
`‖v + wₙ‖ → ‖v‖`. (`liminf ≥ ‖v‖` by weak* lower semicontinuity; for `limsup`, choose unit `φₙ` with
`|(v + wₙ)(φₙ)| ≥ ‖v + wₙ‖ − 1/n`, a limit `ψ` by `gl84_limit`, and
`|(v + wₙ)(φₙ)| ≤ |v(ψ)| + |v(φₙ − ψ)| + ‖wₙ‖ ‖φₙ − ψ‖ → ≤ ‖v‖‖ψ‖ + ‖v‖(1 − ‖ψ‖)` by `gl84_beta_tail`.) -/
theorem gl84_forward [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {v : (R → ℂ → ℂ) → ℂ}
    (hv : v ∈ zZeroSpace R) {w : ℕ → (R → ℂ → ℂ) → ℂ} (hw : IsVanishingSeqZ w) (hle : ∀ n, zNorm (w n) ≤ zNorm v) :
    Tendsto (fun n => zNorm (v + w n)) atTop (𝓝 (zNorm v)) := by
  classical
  have hvZ : v ∈ zSpace R := hv.1
  have hβ : betaSeminorm v = 0 := hv.2
  have hwZ : ∀ n, w n ∈ zSpace R := fun n => (hw.1 n).1
  have hvwZ : ∀ n, v + w n ∈ zSpace R := fun n => gl84_zadd_mem hvZ (hwZ n)
  by_cases hunit : ∃ a ∈ integrableHolQDSet R, quadDiffNorm a = 1
  swap
  · have h0 : ∀ V : (R → ℂ → ℂ) → ℂ, zNorm V = 0 := fun V =>
      le_antisymm (Real.iSup_le (fun a => Real.iSup_le (fun ha => absurd ⟨a, ha.1, ha.2⟩ hunit) le_rfl) le_rfl)
        (Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _)
    simp only [h0]
    exact tendsto_const_nhds
  refine tendsto_order.2 ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩
  · -- `liminf ≥ ‖v‖`
    obtain ⟨a, ha, ha1, hva⟩ := gl84_dual_approx hvZ hunit (η := (zNorm v - a') / 2) (by linarith)
    have hconv : Tendsto (fun n => ‖v a + w n a‖) atTop (𝓝 ‖v a‖) :=
      by simpa using ((hw.2 a ha).const_add (v a)).norm
    filter_upwards [(tendsto_order.1 hconv).1 a' (by linarith)] with n hn
    have := gl84_dual_le (hvwZ n) ha
    rw [ha1, ENNReal.toReal_one, mul_one] at this
    exact lt_of_lt_of_le hn this
  · -- `limsup ≤ ‖v‖`
    by_contra hcon
    rw [not_eventually] at hcon
    have hfreq : ∃ᶠ n in atTop, a' ≤ zNorm (v + w n) := hcon.mono fun n hn => not_lt.1 hn
    obtain ⟨τ, hτ, hτa⟩ := Filter.extraction_of_frequently_atTop hfreq
    set ε : ℝ := a' - zNorm v with hεdef
    have hε : 0 < ε := by linarith
    choose a ha ha1 hlt using fun j => gl84_dual_approx (hvwZ (τ j)) hunit (η := ε / 3) (by positivity)
    obtain ⟨σ, ψ, hσ, hψ, hloc, hBL⟩ := gl84_limit (φ := a) fun j => ⟨ha j, ha1 j⟩
    set Nv : ℝ := zNorm v with hNv
    have hτσ : StrictMono (τ ∘ σ) := hτ.comp hσ
    -- the differences `d k = a (σ k) - ψ`
    have hdA : ∀ k, a (σ k) - ψ ∈ integrableHolQDSet R := fun k => by
      have := gl84_mem_lin (ha (σ k)) hψ (-1)
      rwa [neg_one_smul, ← sub_eq_add_neg] at this
    have hdq : ∀ k, quadDiffNorm (a (σ k) - ψ) = ENNReal.ofReal (quadDiffNorm (a (σ k) - ψ)).toReal :=
      fun k => (ENNReal.ofReal_toReal (hdA k).2.ne).symm
    obtain ⟨M, hM⟩ := hBL.bddAbove_range
    have hdloc : ∀ y : R, TendstoLocallyUniformlyOn (fun k => (a (σ k) - ψ) y) 0 atTop
        (chartAt ℂ y).target := by
      intro y
      have h1 := hloc y
      rw [Metric.tendstoLocallyUniformlyOn_iff] at h1 ⊢
      intro ε' hε' x hx
      obtain ⟨t, ht, hev⟩ := h1 ε' hε' x hx
      refine ⟨t, ht, ?_⟩
      filter_upwards [hev] with k hk z hz
      have h2 := hk z hz
      rw [dist_eq_norm] at h2 ⊢
      simpa [norm_sub_rev] using h2
    have hvd : Tendsto (fun k => v (a (σ k) - ψ)) atTop (𝓝 0) :=
      gl84_beta_tail hv hdA (C := ENNReal.ofReal (max M 0)) ENNReal.ofReal_ne_top
        (fun k => by
          rw [hdq k]
          exact ENNReal.ofReal_le_ofReal ((hM ⟨k, rfl⟩).trans (le_max_left _ _))) hdloc
    have huψ : Tendsto (fun k => w (τ (σ k)) ψ) atTop (𝓝 0) :=
      (hw.2 ψ hψ).comp hτσ.tendsto_atTop
    -- the bounding sequence
    have hT : Tendsto (fun k => ‖v ψ + w (τ (σ k)) ψ‖ + ‖v (a (σ k) - ψ)‖ +
        Nv * (quadDiffNorm (a (σ k) - ψ)).toReal) atTop
        (𝓝 (‖v ψ + 0‖ + ‖(0 : ℂ)‖ + Nv * (1 - (quadDiffNorm ψ).toReal))) :=
      (((tendsto_const_nhds.add huψ).norm).add hvd.norm).add (tendsto_const_nhds.mul hBL)
    have hL : ‖v ψ + 0‖ + ‖(0 : ℂ)‖ + Nv * (1 - (quadDiffNorm ψ).toReal) ≤ Nv := by
      have := gl84_dual_le hvZ hψ
      simp only [add_zero, norm_zero]
      nlinarith [this]
    obtain ⟨k, hk⟩ := ((tendsto_order.1 hT).2 (Nv + ε / 3) (by linarith)).exists
    -- `(v + wₖ)(aₖ) ≤ bounding term`
    have hs : ‖(v + w (τ (σ k))) (a (σ k))‖ ≤ ‖v ψ + w (τ (σ k)) ψ‖ + ‖v (a (σ k) - ψ)‖ +
        Nv * (quadDiffNorm (a (σ k) - ψ)).toReal := by
      have hdecomp : a (σ k) = ψ + (a (σ k) - ψ) := by abel
      have hvsplit : v (a (σ k)) = v ψ + v (a (σ k) - ψ) := by
        conv_lhs => rw [hdecomp]
        exact hvZ.1 ψ hψ _ (hdA k)
      have hwsplit : w (τ (σ k)) (a (σ k)) = w (τ (σ k)) ψ + w (τ (σ k)) (a (σ k) - ψ) := by
        conv_lhs => rw [hdecomp]
        exact (hwZ _).1 ψ hψ _ (hdA k)
      have hwd := gl84_dual_le (hwZ (τ (σ k))) (hdA k)
      have hle' : zNorm (w (τ (σ k))) * (quadDiffNorm (a (σ k) - ψ)).toReal ≤
          Nv * (quadDiffNorm (a (σ k) - ψ)).toReal :=
        mul_le_mul_of_nonneg_right (hle _) ENNReal.toReal_nonneg
      show ‖v (a (σ k)) + w (τ (σ k)) (a (σ k))‖ ≤ _
      rw [hvsplit, hwsplit]
      calc ‖v ψ + v (a (σ k) - ψ) + (w (τ (σ k)) ψ + w (τ (σ k)) (a (σ k) - ψ))‖
          = ‖(v ψ + w (τ (σ k)) ψ) + v (a (σ k) - ψ) + w (τ (σ k)) (a (σ k) - ψ)‖ := by ring_nf
        _ ≤ ‖v ψ + w (τ (σ k)) ψ‖ + ‖v (a (σ k) - ψ)‖ + ‖w (τ (σ k)) (a (σ k) - ψ)‖ := by
          refine (norm_add₃_le).trans ?_
          exact le_rfl
        _ ≤ _ := by gcongr; exact hwd.trans hle'
    have h1 := hlt (σ k)
    have h2 := hτa (σ k)
    linarith

/-- Helper for `gl84_phase_functional` (§8.4). The transformation law of the phase `\bar a/|a|` of a quadratic
coefficient `a t²`: `conj (a t²)/|a t²| = (conj a/|a|) t⁻¹ conj t`. -/
theorem gl84_phase_law (a t : ℂ) :
    conj (a * t ^ 2) / (‖a * t ^ 2‖ : ℂ) = conj a / (‖a‖ : ℂ) * t ^ (-1 : ℤ) * conj t ^ (1 : ℤ) := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases ht : t = 0
  · simp [ht]
  have hn : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 ha
  have hm : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 ht
  have hct : conj t ≠ 0 := by simpa using ht
  have h2 : (‖t‖ : ℂ) ^ 2 = t * conj t := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [norm_mul, norm_pow]
  push_cast
  rw [h2]
  simp only [zpow_neg, zpow_one, map_mul, map_pow]
  field_simp

/-- Helper for `gl84_phase_functional` (§8.4). On a chart partition `(x, P)`, for `χ ∈ A(R)` and a Beltrami
differential `μ`, the chart integrals `∬_{φ_{xᵢ}(Pᵢ)} χ_{xᵢ} μ_{xᵢ}` exist and are summable. -/
theorem gl84_pairing_summable [IsManifold 𝓘(ℂ) ω R] {μ : R → ℂ → ℂ} (hμ : μ ∈ beltramiSpace R)
    {x : ℕ → R} {P : ℕ → Set R} (hP : LiZhongQC.IsChartPartition R x P) {χ : R → ℂ → ℂ}
    (hχ : χ ∈ integrableHolQDSet R) :
    (∀ i, Integrable (fun z => χ (x i) z * μ (x i) z) (volume.restrict (chartAt ℂ (x i) '' P i))) ∧
      Summable (fun i => ∫ z in chartAt ℂ (x i) '' P i, χ (x i) z * μ (x i) z) := by
  classical
  obtain ⟨k, -, hbd⟩ := hμ
  have hGt : ∀ i, chartAt ℂ (x i) '' P i ⊆ (chartAt ℂ (x i)).target := fun i =>
    image_subset_iff.2 fun y hy => (chartAt ℂ (x i)).map_source ((hP.1 i).1 hy)
  have e := LiZhongQC.s26v_surfaceIntegral_eq_tsum hχ.1 (fun _ => (1 : ℝ≥0∞)) hP
  simp only [one_mul, ofReal_norm] at e
  have hqd : ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖χ (x i) z‖ₑ < ⊤ := by
    rw [← e]
    exact hχ.2
  have hχi : ∀ i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖χ (x i) z‖ₑ < ⊤ := fun i =>
    lt_of_le_of_lt (ENNReal.le_tsum (f := fun i => ∫⁻ z in chartAt ℂ (x i) '' P i, ‖χ (x i) z‖ₑ) i) hqd
  have hχm : ∀ i, AEStronglyMeasurable (χ (x i)) (volume.restrict (chartAt ℂ (x i) '' P i)) := fun i =>
    ((hχ.1.2 (x i)).continuousOn.mono (hGt i)).aestronglyMeasurable (hP.1 i).2
  have hχint : ∀ i, Integrable (χ (x i)) (volume.restrict (chartAt ℂ (x i) '' P i)) := fun i => ⟨hχm i, hχi i⟩
  have hint : ∀ i, Integrable (fun z => χ (x i) z * μ (x i) z) (volume.restrict (chartAt ℂ (x i) '' P i)) := by
    intro i
    refine Integrable.mono' ((hχint i).norm.const_mul k) ((hχm i).mul
      (((hbd (x i)).1).mono_measure (Measure.restrict_mono (hGt i) le_rfl))) ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (hGt i) (hbd (x i)).2] with z hz
    rw [norm_mul]
    calc ‖χ (x i) z‖ * ‖μ (x i) z‖ ≤ ‖χ (x i) z‖ * k := by gcongr
      _ = k * ‖χ (x i) z‖ := mul_comm _ _
  refine ⟨hint, ?_⟩
  have hs : Summable fun i => (∫⁻ z in chartAt ℂ (x i) '' P i, ‖χ (x i) z‖ₑ).toReal :=
    ENNReal.summable_toReal hqd.ne
  refine Summable.of_norm_bounded ((hs.mul_left k)) (fun i => ?_)
  calc ‖∫ z in chartAt ℂ (x i) '' P i, χ (x i) z * μ (x i) z‖
      ≤ ∫ z in chartAt ℂ (x i) '' P i, k * ‖χ (x i) z‖ := by
        refine norm_integral_le_of_norm_le ((hχint i).norm.const_mul k) ?_
        filter_upwards [ae_restrict_of_ae_restrict_of_subset (hGt i) (hbd (x i)).2] with z hz
        rw [norm_mul]
        calc ‖χ (x i) z‖ * ‖μ (x i) z‖ ≤ ‖χ (x i) z‖ * k := by gcongr
          _ = k * ‖χ (x i) z‖ := mul_comm _ _
    _ = k * (∫⁻ z in chartAt ℂ (x i) '' P i, ‖χ (x i) z‖ₑ).toReal := by
        rw [integral_const_mul, integral_norm_eq_lintegral_enorm (hχm i)]

/-- Helper for `gl84_phase_functional` (§8.4). A Beltrami differential gives a bounded functional on `A(R)`. -/
theorem gl84_pairing_linear [IsManifold 𝓘(ℂ) ω R] {μ : R → ℂ → ℂ} (hμ : μ ∈ beltramiSpace R) :
    IsBoundedFunctionalOn (integrableHolQDSet R) quadDiffNorm (fun χ => pairingRS χ μ) := by
  classical
  have key : ∀ χ ∈ integrableHolQDSet R,
      ∃ _ : (∃ (x : ℕ → R) (P : ℕ → Set R), LiZhongQC.IsChartPartition R x P), True :=
    fun χ hχ => ⟨gl31_exists_partition_of_ne_top hχ.2.ne, trivial⟩
  refine ⟨fun a ha b hb => ?_, fun c a ha => ?_, (beltramiNormRS μ).toReal, fun χ hχ => gl31_pairingRS_le hχ hμ⟩
  · obtain ⟨h, -⟩ := key a ha
    obtain ⟨hia, hsa⟩ := gl84_pairing_summable hμ h.choose_spec.choose_spec ha
    obtain ⟨hib, hsb⟩ := gl84_pairing_summable hμ h.choose_spec.choose_spec hb
    simp only [pairingRS, dite_eq_left h]
    rw [← hsa.tsum_add hsb]
    refine tsum_congr fun i => ?_
    simp only [Pi.add_apply, add_mul]
    exact integral_add (hia i) (hib i)
  · obtain ⟨h, -⟩ := key a ha
    simp only [pairingRS, dite_eq_left h]
    rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _

/-- Helper for `gl84_phase_functional` (§8.4). The phase Beltrami differential `μ = (\bar φ/|φ|) χ_{R∖K}` of a
holomorphic quadratic differential and a closed set `K`: `|μ| ≤ 1`, `μ = 0` over `K`, and `φ μ = |φ|` off `K`. -/
theorem gl84_phase_beltrami [IsManifold 𝓘(ℂ) ω R] {φ : R → ℂ → ℂ} (hφ : φ ∈ LiZhongQC.holQuadDiffSubmodule R)
    {K : Set R} (hK : IsClosed K) :
    ∃ μ ∈ beltramiSpace R, (∀ y z, ‖μ y z‖ ≤ 1) ∧ (∀ y z, (chartAt ℂ y).symm z ∈ K → μ y z = 0) ∧
      ∀ y z, φ y z * μ y z = Kᶜ.indicator (fun _ => ((‖φ y z‖ : ℝ) : ℂ)) ((chartAt ℂ y).symm z) := by
  classical
  have hunit : ∀ a : ℂ, ‖conj a / (‖a‖ : ℂ)‖ ≤ 1 := fun a => by
    by_cases ha : a = 0
    · simp [ha]
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 ha)]
  refine ⟨fun y z => if (chartAt ℂ y).symm z ∈ K then 0 else conj (φ y z) / (‖φ y z‖ : ℂ), ?_, ?_, ?_, ?_⟩
  · refine ⟨1, ?_, fun y => ⟨?_, ?_⟩⟩
    · intro x y
      have hset : MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source) :=
        ((chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x).open_source).measurableSet
      filter_upwards [ae_restrict_mem hset] with z hz
      have hT : (chartAt ℂ x).symm (LiZhongQC.chartTransition x y z) = (chartAt ℂ y).symm z :=
        (chartAt ℂ x).left_inv hz.2
      have law : φ y z = φ x (LiZhongQC.chartTransition x y z) * deriv (LiZhongQC.chartTransition x y) z ^ 2 := by
        have := hφ.1.2 x y z hz.1 hz.2
        simpa using this
      show (if (chartAt ℂ y).symm z ∈ K then 0 else conj (φ y z) / (‖φ y z‖ : ℂ)) =
        (if (chartAt ℂ x).symm (LiZhongQC.chartTransition x y z) ∈ K then 0 else
          conj (φ x (LiZhongQC.chartTransition x y z)) / (‖φ x (LiZhongQC.chartTransition x y z)‖ : ℂ)) *
        deriv (LiZhongQC.chartTransition x y) z ^ (-1 : ℤ) * conj (deriv (LiZhongQC.chartTransition x y) z) ^ (1 : ℤ)
      rw [hT]
      by_cases hKz : (chartAt ℂ y).symm z ∈ K
      · simp [hKz]
      · rw [if_neg hKz, if_neg hKz, law]
        exact gl84_phase_law _ _
    · have hφm : AEStronglyMeasurable (φ y) (volume.restrict (chartAt ℂ y).target) :=
        ((hφ.2 y).continuousOn).aestronglyMeasurable (chartAt ℂ y).open_target.measurableSet
      have hTK : MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' K) := by
        have h : (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' K =
            (chartAt ℂ y).target \ ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' Kᶜ) := by
          ext z
          simp only [mem_inter_iff, mem_diff, mem_preimage, mem_compl_iff]
          tauto
        rw [h]
        exact (chartAt ℂ y).open_target.measurableSet.diff
          ((chartAt ℂ y).isOpen_inter_preimage_symm hK.isOpen_compl).measurableSet
      have hu : AEMeasurable (fun z => conj (φ y z) / (‖φ y z‖ : ℂ)) (volume.restrict (chartAt ℂ y).target) :=
        (Complex.continuous_conj.measurable.comp_aemeasurable hφm.aemeasurable).div
          (Complex.measurable_ofReal.comp_aemeasurable hφm.aemeasurable.norm)
      refine (hu.indicator hTK.compl).aestronglyMeasurable.congr
        ((ae_restrict_iff' (chartAt ℂ y).open_target.measurableSet).2 (Eventually.of_forall fun z hz => ?_))
      by_cases hzK : (chartAt ℂ y).symm z ∈ K
      · have hzn : z ∉ ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' K)ᶜ := fun h => h ⟨hz, hzK⟩
        rw [indicator_of_notMem hzn]
        simp [hzK]
      · have hzn : z ∈ ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' K)ᶜ := fun h => hzK h.2
        rw [indicator_of_mem hzn]
        simp [hzK]
    · refine Eventually.of_forall fun z => ?_
      show ‖(if (chartAt ℂ y).symm z ∈ K then (0 : ℂ) else conj (φ y z) / (‖φ y z‖ : ℂ))‖ ≤ 1
      by_cases hzK : (chartAt ℂ y).symm z ∈ K
      · simp [hzK]
      · rw [if_neg hzK]
        exact hunit _
  · intro y z
    show ‖(if (chartAt ℂ y).symm z ∈ K then (0 : ℂ) else conj (φ y z) / (‖φ y z‖ : ℂ))‖ ≤ 1
    by_cases hzK : (chartAt ℂ y).symm z ∈ K
    · simp [hzK]
    · rw [if_neg hzK]
      exact hunit _
  · intro y z hz
    simp [hz]
  · intro y z
    by_cases hzK : (chartAt ℂ y).symm z ∈ K
    · simp [hzK]
    · have hn : (chartAt ℂ y).symm z ∈ Kᶜ := hzK
      beta_reduce
      rw [indicator_of_mem hn, if_neg hzK]
      by_cases ha : φ y z = 0
      · simp [ha]
      · have hn' : (‖φ y z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 ha
        rw [mul_div_assoc', Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        field_simp

/-- Helper for **Theorem 7** (§8.4), (⇐). The phase functional `w = [ (\overline{φ}/|φ|) χ_{R∖K} ]` of `φ ∈ A(R)` and a
compact `K`: a Beltrami functional (the chart family `\overline{φ_y}/|φ_y| · 𝟙_{R∖K}` obeys the transformation law
because `φ_y = φ_x(τ) τ′²`) with `‖w‖ ≤ 1`, `|w(χ)| ≤ ∬_{R∖K} |χ|` and `w(φ) = ∬_{R∖K} |φ|`. -/
theorem gl84_phase_functional [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {φ : R → ℂ → ℂ}
    (hφ : φ ∈ integrableHolQDSet R) {K : Set R} (hK : IsCompact K) :
    ∃ w ∈ zSpace R, zNorm w ≤ 1 ∧
      (∀ χ ∈ integrableHolQDSet R, ‖w χ‖ ≤ (LiZhongQC.surfaceIntegral χ
        (fun y z => Kᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z))).toReal) ∧
      w φ = (LiZhongQC.surfaceIntegral φ
        (fun y z => Kᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z))).toReal := by
  classical
  have hKc : IsClosed K := hK.isClosed
  obtain ⟨μ, hμ, hμ1, hμK, hφμ⟩ := gl84_phase_beltrami hφ.1 hKc
  set SI : (R → ℂ → ℂ) → ℝ≥0∞ := fun χ => LiZhongQC.surfaceIntegral χ
    (fun y z => Kᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z)) with hSI
  have hTKm : ∀ x : R, MeasurableSet ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' K) := by
    intro x
    have h : (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' K =
        (chartAt ℂ x).target \ ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Kᶜ) := by
      ext z
      simp only [mem_inter_iff, mem_diff, mem_preimage, mem_compl_iff]
      tauto
    rw [h]
    exact (chartAt ℂ x).open_target.measurableSet.diff
      ((chartAt ℂ x).isOpen_inter_preimage_symm hKc.isOpen_compl).measurableSet
  -- `‖μ‖∞ ≤ 1`
  have hμnorm : beltramiNormRS μ ≤ 1 := by
    obtain ⟨k0, -, hcoef⟩ := hμ
    refine iSup_le fun y => ?_
    rw [eLpNorm_exponent_top (hcoef y).1]
    refine (eLpNormEssSup_le_of_ae_bound (C := 1) (Eventually.of_forall fun z => hμ1 y z)).trans ?_
    simp
  -- `μ = 0` over `K`
  have hB : (⨆ x : R, eLpNorm (μ x) ⊤ (volume.restrict ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (Kᶜ)ᶜ))) = 0 := by
    refine le_antisymm (iSup_le fun x => ?_) bot_le
    have hmeas : MeasurableSet ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (Kᶜ)ᶜ) := by
      rw [compl_compl]
      exact hTKm x
    refine ((eLpNorm_congr_ae (g := 0) ((ae_restrict_iff' hmeas).2 (Eventually.of_forall fun z hz => ?_))).trans
      eLpNorm_zero).le
    exact hμK x z (by simpa using hz.2)
  have hpair_le : ∀ χ ∈ integrableHolQDSet R, ‖pairingRS χ μ‖ₑ ≤ SI χ := by
    intro χ hχ
    have h := gl31_pairingRS_split hχ hμ Kᶜ
    rw [hB, zero_mul, add_zero] at h
    exact h.trans ((mul_le_mul_left hμnorm _).trans (one_mul _).le)
  have hSIle : ∀ χ ∈ integrableHolQDSet R, SI χ ≤ quadDiffNorm χ := by
    intro χ hχ
    obtain ⟨x, P, hP⟩ := gl31_exists_partition_of_ne_top hχ.2.ne
    have e1 := LiZhongQC.s26v_surfaceIntegral_eq_tsum hχ.1 (Kᶜ.indicator (fun _ => (1 : ℝ≥0∞))) hP
    have e2 := LiZhongQC.s26v_surfaceIntegral_eq_tsum hχ.1 (fun _ => (1 : ℝ≥0∞)) hP
    calc SI χ = _ := e1
      _ ≤ _ := ENNReal.tsum_le_tsum fun i => lintegral_mono fun z => by
          by_cases hz : (chartAt ℂ (x i)).symm z ∈ Kᶜ
          · rw [indicator_of_mem hz]
          · rw [indicator_of_notMem hz, zero_mul]
            exact zero_le
      _ = quadDiffNorm χ := e2.symm
  refine ⟨fun χ => pairingRS χ μ, gl84_pairing_linear hμ, ?_, fun χ hχ => ?_, ?_⟩
  · refine Real.iSup_le (fun a => Real.iSup_le (fun ha => ?_) zero_le_one) zero_le_one
    calc ‖pairingRS a μ‖ = (‖pairingRS a μ‖ₑ).toReal := (toReal_enorm _).symm
      _ ≤ (quadDiffNorm a).toReal :=
          ENNReal.toReal_mono ha.1.2.ne ((hpair_le a ha.1).trans (hSIle a ha.1))
      _ = 1 := by rw [ha.2, ENNReal.toReal_one]
  · calc ‖pairingRS χ μ‖ = (‖pairingRS χ μ‖ₑ).toReal := (toReal_enorm _).symm
      _ ≤ (SI χ).toReal :=
          ENNReal.toReal_mono (ne_top_of_le_ne_top hχ.2.ne (hSIle χ hχ)) (hpair_le χ hχ)
  · -- `w φ = ∬_{R∖K} |φ|`
    have h := gl31_exists_partition_of_ne_top hφ.2.ne
    have hP := h.choose_spec.choose_spec
    have hGt : ∀ i, chartAt ℂ (h.choose i) '' h.choose_spec.choose i ⊆ (chartAt ℂ (h.choose i)).target := fun i =>
      image_subset_iff.2 fun y hy => (chartAt ℂ (h.choose i)).map_source ((hP.1 i).1 hy)
    have hS := LiZhongQC.s26v_surfaceIntegral_eq_tsum hφ.1 (Kᶜ.indicator (fun _ => (1 : ℝ≥0∞))) hP
    set F : ℕ → ℂ → ℝ≥0∞ := fun i z => Kᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ (h.choose i)).symm z) *
      ENNReal.ofReal ‖φ (h.choose i) z‖ with hF
    have hFm : ∀ i, AEMeasurable (F i) (volume.restrict (chartAt ℂ (h.choose i) '' h.choose_spec.choose i)) := by
      intro i
      have hφm : AEMeasurable (fun z => ENNReal.ofReal ‖φ (h.choose i) z‖)
          (volume.restrict (chartAt ℂ (h.choose i) '' h.choose_spec.choose i)) :=
        (((hφ.1.2 (h.choose i)).continuousOn.mono (hGt i)).aemeasurable (μ := volume) (hP.1 i).2).norm.ennreal_ofReal
      have hTc : MeasurableSet ((chartAt ℂ (h.choose i)).target ∩ (chartAt ℂ (h.choose i)).symm ⁻¹' Kᶜ) :=
        ((chartAt ℂ (h.choose i)).isOpen_inter_preimage_symm hKc.isOpen_compl).measurableSet
      refine (hφm.indicator hTc).congr ((ae_restrict_iff' (hP.1 i).2).2 (Eventually.of_forall fun z hz => ?_))
      beta_reduce
      simp only [hF]
      by_cases hzK : (chartAt ℂ (h.choose i)).symm z ∈ Kᶜ
      · rw [indicator_of_mem (show z ∈ (chartAt ℂ (h.choose i)).target ∩ (chartAt ℂ (h.choose i)).symm ⁻¹' Kᶜ from
          ⟨hGt i hz, hzK⟩), indicator_of_mem hzK, one_mul]
      · rw [indicator_of_notMem (show z ∉ (chartAt ℂ (h.choose i)).target ∩ (chartAt ℂ (h.choose i)).symm ⁻¹' Kᶜ from
          fun h' => hzK h'.2), indicator_of_notMem hzK, zero_mul]
    have hFlt : ∀ i, ∀ᵐ z ∂(volume.restrict (chartAt ℂ (h.choose i) '' h.choose_spec.choose i)), F i z < ⊤ := by
      intro i
      refine Eventually.of_forall fun z => ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top
      by_cases hzK : (chartAt ℂ (h.choose i)).symm z ∈ Kᶜ
      · rw [indicator_of_mem hzK]
        exact ENNReal.one_lt_top
      · rw [indicator_of_notMem hzK]
        exact ENNReal.zero_lt_top
    have hterm : ∀ i, ∫ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i, φ (h.choose i) z * μ (h.choose i) z =
        (((∫⁻ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i, F i z).toReal : ℝ) : ℂ) := by
      intro i
      rw [← integral_toReal (hFm i) (hFlt i), ← integral_complex_ofReal]
      refine setIntegral_congr_fun (hP.1 i).2 fun z hz => ?_
      show φ (h.choose i) z * μ (h.choose i) z = (((F i z).toReal : ℝ) : ℂ)
      rw [hφμ]
      by_cases hzK : (chartAt ℂ (h.choose i)).symm z ∈ Kᶜ
      · simp only [hF, indicator_of_mem hzK, one_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
      · simp only [hF, indicator_of_notMem hzK, zero_mul, ENNReal.toReal_zero, Complex.ofReal_zero]
    have hfin : ∀ i, ∫⁻ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i, F i z ≠ ⊤ := by
      intro i
      refine ne_top_of_le_ne_top (b := ∑' j, ∫⁻ z in chartAt ℂ (h.choose j) '' h.choose_spec.choose j,
        ENNReal.ofReal ‖φ (h.choose j) z‖) ?_ (le_trans (lintegral_mono fun z => ?_) (ENNReal.le_tsum
          (f := fun j => ∫⁻ z in chartAt ℂ (h.choose j) '' h.choose_spec.choose j,
            ENNReal.ofReal ‖φ (h.choose j) z‖) i))
      · have e2 := LiZhongQC.s26v_surfaceIntegral_eq_tsum hφ.1 (fun _ => (1 : ℝ≥0∞)) hP
        simp only [one_mul] at e2
        have h3 : ∑' j, ∫⁻ z in chartAt ℂ (h.choose j) '' h.choose_spec.choose j,
            ENNReal.ofReal ‖φ (h.choose j) z‖ = quadDiffNorm φ := e2.symm
        rw [h3]
        exact hφ.2.ne
      · by_cases hzK : (chartAt ℂ (h.choose i)).symm z ∈ Kᶜ
        · simp only [hF, indicator_of_mem hzK, one_mul]
          exact le_rfl
        · simp only [hF, indicator_of_notMem hzK, zero_mul]
          exact zero_le
    show pairingRS φ μ = _
    rw [gl31_pairingRS_eq φ μ h]
    simp only [hterm]
    rw [← Complex.ofReal_tsum, ← ENNReal.tsum_toReal_eq hfin]
    congr 2
    show _ = SI φ
    exact hS.symm

/-- Helper for `gl84_backward` (§8.4). The chart integrand `𝟙_{S'}(φ_{xᵢ}⁻¹ z) |χ_{xᵢ}(z)|` of a set `S'` with
measurable chart parts is a.e.-measurable on `φ_{xᵢ}(Pᵢ)`. -/
theorem gl84_ind_meas [IsManifold 𝓘(ℂ) ω R] {x : ℕ → R} {P : ℕ → Set R}
    (hP : LiZhongQC.IsChartPartition R x P) {χ : R → ℂ → ℂ} (hχ : χ ∈ LiZhongQC.holQuadDiffSubmodule R)
    {S' : Set R} (hS' : ∀ y : R, MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' S')) (i : ℕ) :
    AEMeasurable (fun z => S'.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ (x i)).symm z) *
      ENNReal.ofReal ‖χ (x i) z‖) (volume.restrict (chartAt ℂ (x i) '' P i)) := by
  classical
  have hGt : chartAt ℂ (x i) '' P i ⊆ (chartAt ℂ (x i)).target :=
    image_subset_iff.2 fun q hq => (chartAt ℂ (x i)).map_source ((hP.1 i).1 hq)
  have hφm : AEMeasurable (fun z => ENNReal.ofReal ‖χ (x i) z‖) (volume.restrict (chartAt ℂ (x i) '' P i)) :=
    (((hχ.2 (x i)).continuousOn.mono hGt).aemeasurable (μ := volume) (hP.1 i).2).norm.ennreal_ofReal
  refine (hφm.indicator (hS' (x i))).congr ((ae_restrict_iff' (hP.1 i).2).2 (Eventually.of_forall fun z hz => ?_))
  beta_reduce
  by_cases hzK : (chartAt ℂ (x i)).symm z ∈ S'
  · rw [indicator_of_mem (show z ∈ (chartAt ℂ (x i)).target ∩ (chartAt ℂ (x i)).symm ⁻¹' S' from ⟨hGt hz, hzK⟩),
      indicator_of_mem hzK, one_mul]
  · rw [indicator_of_notMem (show z ∉ (chartAt ℂ (x i)).target ∩ (chartAt ℂ (x i)).symm ⁻¹' S' from
      fun h' => hzK h'.2), indicator_of_notMem hzK, zero_mul]

/-- Helper for `gl84_backward` (§8.4). Splitting the norm along a closed set `K`: `∬_K |χ| + ∬_{R∖K} |χ| = ‖χ‖`. -/
theorem gl84_SI_add [IsManifold 𝓘(ℂ) ω R] {χ : R → ℂ → ℂ} (hχ : χ ∈ integrableHolQDSet R) {K : Set R}
    (hK : IsClosed K) :
    LiZhongQC.surfaceIntegral χ (fun y z => K.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z)) +
      LiZhongQC.surfaceIntegral χ (fun y z => Kᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z)) =
      quadDiffNorm χ := by
  classical
  obtain ⟨x, P, hP⟩ := gl31_exists_partition_of_ne_top hχ.2.ne
  have hTK : ∀ y : R, MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' K) := by
    intro y
    have h : (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' K =
        (chartAt ℂ y).target \ ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' Kᶜ) := by
      ext z
      simp only [mem_inter_iff, mem_diff, mem_preimage, mem_compl_iff]
      tauto
    rw [h]
    exact (chartAt ℂ y).open_target.measurableSet.diff
      ((chartAt ℂ y).isOpen_inter_preimage_symm hK.isOpen_compl).measurableSet
  have e1 := LiZhongQC.s26v_surfaceIntegral_eq_tsum hχ.1 (K.indicator (fun _ => (1 : ℝ≥0∞))) hP
  have e2 := LiZhongQC.s26v_surfaceIntegral_eq_tsum hχ.1 (Kᶜ.indicator (fun _ => (1 : ℝ≥0∞))) hP
  have e3 := LiZhongQC.s26v_surfaceIntegral_eq_tsum hχ.1 (fun _ => (1 : ℝ≥0∞)) hP
  rw [e1, e2, ← ENNReal.tsum_add]
  refine Eq.trans (tsum_congr fun i => ?_) e3.symm
  rw [← lintegral_add_left' (gl84_ind_meas hP hχ.1 hTK i)]
  refine lintegral_congr fun z => ?_
  rw [← add_mul]
  congr 1
  by_cases hzK : (chartAt ℂ (x i)).symm z ∈ K
  · rw [indicator_of_mem hzK, indicator_of_notMem (show (chartAt ℂ (x i)).symm z ∉ Kᶜ from fun h => h hzK), add_zero]
  · rw [indicator_of_notMem hzK, indicator_of_mem (show (chartAt ℂ (x i)).symm z ∈ Kᶜ from hzK), zero_add]

/-- Helper for `gl84_backward` (§8.4). If closed sets `Kⱼ` increase and exhaust `R`, then `∬_{R∖Kⱼ} |χ| → 0` for every
`χ ∈ A(R)` (dominated convergence in each chart integral, then in the series). -/
theorem gl84_tail_zero [IsManifold 𝓘(ℂ) ω R] {χ : R → ℂ → ℂ} (hχ : χ ∈ integrableHolQDSet R) {K : ℕ → Set R}
    (hKcl : ∀ j, IsClosed (K j)) (hKm : Monotone K) (hKc : ⋃ j, K j = univ) :
    Tendsto (fun j => (LiZhongQC.surfaceIntegral χ
      (fun y z => (K j)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z))).toReal) atTop (𝓝 0) := by
  classical
  obtain ⟨x, P, hP⟩ := gl31_exists_partition_of_ne_top hχ.2.ne
  set b : ℕ → ℝ≥0∞ := fun i => ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖χ (x i) z‖ with hb
  set a : ℕ → ℕ → ℝ≥0∞ := fun j i => ∫⁻ z in chartAt ℂ (x i) '' P i,
    (K j)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ (x i)).symm z) * ENNReal.ofReal ‖χ (x i) z‖ with ha
  have e3 := LiZhongQC.s26v_surfaceIntegral_eq_tsum hχ.1 (fun _ => (1 : ℝ≥0∞)) hP
  simp only [one_mul] at e3
  have hbsum : ∑' i, b i ≠ ⊤ := by
    have : ∑' i, b i = quadDiffNorm χ := e3.symm
    rw [this]
    exact hχ.2.ne
  have hbfin : ∀ i, b i ≠ ⊤ := fun i => ne_top_of_le_ne_top hbsum (ENNReal.le_tsum i)
  have hab : ∀ j i, a j i ≤ b i := fun j i => lintegral_mono fun z => by
    by_cases hz : (chartAt ℂ (x i)).symm z ∈ (K j)ᶜ
    · rw [indicator_of_mem hz, one_mul]
    · rw [indicator_of_notMem hz, zero_mul]
      exact zero_le
  have hSI : ∀ j, LiZhongQC.surfaceIntegral χ
      (fun y z => (K j)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z)) = ∑' i, a j i := fun j =>
    LiZhongQC.s26v_surfaceIntegral_eq_tsum hχ.1 ((K j)ᶜ.indicator (fun _ => (1 : ℝ≥0∞))) hP
  have hTc : ∀ j y, MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (K j)ᶜ) := fun j y =>
    ((chartAt ℂ y).isOpen_inter_preimage_symm (hKcl j).isOpen_compl).measurableSet
  have hai : ∀ i, Tendsto (fun j => a j i) atTop (𝓝 0) := by
    intro i
    have := tendsto_lintegral_of_dominated_convergence'
      (μ := volume.restrict (chartAt ℂ (x i) '' P i))
      (F := fun j z => (K j)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ (x i)).symm z) *
        ENNReal.ofReal ‖χ (x i) z‖) (f := fun _ => 0) (fun z => ENNReal.ofReal ‖χ (x i) z‖)
      (fun j => gl84_ind_meas hP hχ.1 (hTc j) i)
      (fun j => Eventually.of_forall fun z => by
        beta_reduce
        by_cases hz : (chartAt ℂ (x i)).symm z ∈ (K j)ᶜ
        · rw [indicator_of_mem hz, one_mul]
        · rw [indicator_of_notMem hz, zero_mul]
          exact zero_le)
      (hbfin i) ?_
    · simp only [lintegral_zero] at this
      exact this
    · refine Eventually.of_forall fun z => ?_
      obtain ⟨j₀, hj₀⟩ := mem_iUnion.1 (hKc ▸ mem_univ ((chartAt ℂ (x i)).symm z))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop j₀] with j hj
      rw [indicator_of_notMem (show (chartAt ℂ (x i)).symm z ∉ (K j)ᶜ from fun h => h (hKm hj hj₀)), zero_mul]
  have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := fun j i => (a j i).toReal)
    (g := fun _ => 0) (bound := fun i => (b i).toReal) (ENNReal.summable_toReal hbsum)
    (fun i => (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hai i))
    (Eventually.of_forall fun j i => by
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_mono (hbfin i) (hab j i))
  simp only [tsum_zero] at this
  refine this.congr fun j => ?_
  rw [hSI j, ENNReal.tsum_toReal_eq (fun i => ne_top_of_le_ne_top (hbfin i) (hab j i))]

/-- Helper for **Theorem 7** (§8.4), (⇐). If `v ∈ Z ∖ Z₀` with `‖v‖ ≤ 1`, there is a vanishing sequence `wₙ` with
`‖wₙ‖ ≤ ‖v‖` and `‖v + wₙ‖ ↛ ‖v‖`: `β(v) > 0` gives a degenerating sequence with `|v(φₙ)| ≥ ε₀` (rotate to make
`v(φₙ) ≥ ε₀`); exhaust `R` by compacts `Eₙ` (`R` is second countable, `gl31_secondCountable_of_partition`, and locally
compact) with `∬_{Eₙ} |φₙ| ≤ 1/n` (`gl31_degenerating_cpt`); `wₙ = ‖v‖ ·` the phase functional of `φₙ` and `Eₙ`
(`gl84_phase_functional`) satisfies `(v + wₙ)(φₙ) ≥ ε₀ + ‖v‖(1 − 1/n) > ‖v‖` for large `n`. -/
theorem gl84_backward [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {v : (R → ℂ → ℂ) → ℂ}
    (hv : v ∈ zSpace R) (hv1 : zNorm v ≤ 1) (hv0 : v ∉ zZeroSpace R) :
    ∃ w : ℕ → (R → ℂ → ℂ) → ℂ, IsVanishingSeqZ w ∧ (∀ n, zNorm (w n) ≤ zNorm v) ∧
      ¬ Tendsto (fun n => zNorm (v + w n)) atTop (𝓝 (zNorm v)) := by
  classical
  have hβ : 0 < betaSeminorm v := pos_iff_ne_zero.2 fun h0 => hv0 ⟨hv, h0⟩
  -- a degenerating sequence on which `|v|` stays away from `0`
  obtain ⟨φ, hφdeg, ε₀, hε₀, τ, hτ, hτε⟩ : ∃ (φ : ℕ → R → ℂ → ℂ) (_ : IsDegeneratingSeq φ) (ε₀ : ℝ), 0 < ε₀ ∧
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∀ j, ε₀ < ‖v (φ (τ j))‖ := by
    obtain ⟨φ, hφ⟩ := lt_iSup_iff.1 hβ
    obtain ⟨hφdeg, hlim⟩ := lt_iSup_iff.1 hφ
    obtain ⟨r, hr0, hr1, hrlt⟩ := ENNReal.lt_iff_exists_real_btwn.1 hlim
    obtain ⟨τ, hτ, hτε⟩ := Filter.extraction_of_frequently_atTop
      (Filter.frequently_lt_of_lt_limsup (by isBoundedDefault) hrlt)
    refine ⟨φ, hφdeg, r, ENNReal.ofReal_pos.1 hr1, τ, hτ, fun j => ?_⟩
    have h1 : ENNReal.ofReal r < ENNReal.ofReal ‖v (φ (τ j))‖ := by
      rw [ofReal_norm]
      exact hτε j
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr0).1 h1
  set φ' : ℕ → R → ℂ → ℂ := fun j => φ (τ j) with hφ'
  have hφ'unit : ∀ j, φ' j ∈ integrableHolQDSet R ∧ quadDiffNorm (φ' j) = 1 := fun j => hφdeg.1 (τ j)
  have hvsmul := hv.2.1
  -- rotate so that `v (ψ j) = |v (φ' j)|`
  have hvne : ∀ j, v (φ' j) ≠ 0 := fun j => norm_pos_iff.1 (lt_trans hε₀ (hτε j))
  set c : ℕ → ℂ := fun j => conj (v (φ' j)) / (‖v (φ' j)‖ : ℂ) with hc
  have hcn : ∀ j, ‖c j‖ = 1 := fun j => by
    simp only [hc]
    rw [norm_div, Complex.norm_conj, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 (hvne j))]
  have hψA : ∀ j, c j • φ' j ∈ integrableHolQDSet R := fun j =>
    ⟨(LiZhongQC.holQuadDiffSubmodule R).smul_mem _ (hφ'unit j).1.1, by
      rw [gl31_quadDiffNorm_smul (hφ'unit j).1]
      exact ENNReal.mul_lt_top enorm_lt_top (hφ'unit j).1.2⟩
  have hψ1 : ∀ j, quadDiffNorm (c j • φ' j) = 1 := fun j => by
    rw [gl31_quadDiffNorm_smul (hφ'unit j).1, (hφ'unit j).2, ← ofReal_norm, hcn, ENNReal.ofReal_one, one_mul]
  have hvψ : ∀ j, v (c j • φ' j) = ((‖v (φ' j)‖ : ℝ) : ℂ) := fun j => by
    rw [hvsmul _ _ (hφ'unit j).1]
    have hn : (‖v (φ' j)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 (hvne j)
    simp only [hc]
    rw [div_mul_eq_mul_div, Complex.conj_mul']
    push_cast
    field_simp
  have hψdeg : IsDegeneratingSeq (fun j => c j • φ' j) := ⟨fun j => ⟨hψA j, hψ1 j⟩, fun y => by
    have h1 := hφdeg.2 y
    rw [Metric.tendstoLocallyUniformlyOn_iff] at h1 ⊢
    intro ε' hε' x hx
    obtain ⟨t, ht, hev⟩ := h1 ε' hε' x hx
    refine ⟨t, ht, ?_⟩
    filter_upwards [hτ.tendsto_atTop.eventually hev] with j hj z hz
    have h2 := hj z hz
    simp only [dist_eq_norm, Pi.zero_apply, zero_sub, norm_neg] at h2 ⊢
    show ‖c j * φ (τ j) y z‖ < ε'
    rw [norm_mul, hcn, one_mul]
    exact h2⟩
  -- an exhaustion of `R` by compact sets
  obtain ⟨x₀, P₀, hP₀⟩ := gl31_exists_partition_of_ne_top (hψA 0).2.ne
  haveI : SecondCountableTopology R := gl31_secondCountable_of_partition hP₀
  haveI : LocallyCompactSpace R := ChartedSpace.locallyCompactSpace ℂ R
  let Kc : CompactExhaustion R := CompactExhaustion.choice R
  have hKcl : ∀ n, IsClosed (Kc n) := fun n => (Kc.isCompact n).isClosed
  have hKm : Monotone (fun n => Kc n) := fun m n h => Kc.subset h
  have hKu : ⋃ n, Kc n = univ := Kc.iUnion_eq
  have hsmall : ∀ j : ℕ, ∃ m : ℕ, LiZhongQC.surfaceIntegral (c m • φ' m)
      (fun y z => (Kc j).indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z)) <
        ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
    intro j
    have := gl31_degenerating_cpt hψdeg (Kc.isCompact j)
    exact ((tendsto_order.1 this).2 _ (ENNReal.ofReal_pos.2 (by positivity))).exists
  choose m hm using hsmall
  have hw : ∀ j, ∃ w ∈ zSpace R, zNorm w ≤ 1 ∧
      (∀ χ ∈ integrableHolQDSet R, ‖w χ‖ ≤ (LiZhongQC.surfaceIntegral χ
        (fun y z => (Kc j)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z))).toReal) ∧
      w (c (m j) • φ' (m j)) = (LiZhongQC.surfaceIntegral (c (m j) • φ' (m j))
        (fun y z => (Kc j)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z))).toReal :=
    fun j => gl84_phase_functional (hψA (m j)) (Kc.isCompact j)
  choose w hwZ hwn hwle hweq using hw
  set Nv : ℝ := zNorm v with hNv
  have hNv0 : 0 ≤ Nv := Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hWZ : ∀ j, (fun χ => ((Nv : ℝ) : ℂ) * w j χ) ∈ zSpace R := by
    intro j
    obtain ⟨hwa, hws, Kw, hKw⟩ := hwZ j
    refine ⟨fun a ha b hb => ?_, fun d a ha => ?_, Nv * Kw, fun a ha => ?_⟩
    · simp only [hwa a ha b hb]
      ring
    · simp only [hws d a ha]
      ring
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hNv0, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hKw a ha) hNv0
  have hWn : ∀ j, zNorm (fun χ => ((Nv : ℝ) : ℂ) * w j χ) ≤ Nv := by
    intro j
    refine Real.iSup_le (fun a => Real.iSup_le (fun ha => ?_) hNv0) hNv0
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hNv0]
    have := gl84_dual_le (hwZ j) ha.1
    rw [ha.2, ENNReal.toReal_one, mul_one] at this
    calc Nv * ‖w j a‖ ≤ Nv * 1 := mul_le_mul_of_nonneg_left (this.trans (hwn j)) hNv0
      _ = Nv := mul_one _
  refine ⟨fun j χ => ((Nv : ℝ) : ℂ) * w j χ, ⟨fun j => ⟨hWZ j, (hWn j).trans hv1⟩, fun χ hχ => ?_⟩, hWn, ?_⟩
  · -- vanishing
    have ht := (gl84_tail_zero hχ hKcl hKm hKu).const_mul Nv
    rw [mul_zero] at ht
    refine squeeze_zero_norm (fun j => ?_) ht
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hNv0]
    exact mul_le_mul_of_nonneg_left (hwle j χ hχ) hNv0
  · -- no convergence
    intro hconv
    have hevent : ∀ᶠ j : ℕ in atTop, zNorm (v + fun χ => ((Nv : ℝ) : ℂ) * w j χ) < Nv + ε₀ / 2 :=
      (tendsto_order.1 hconv).2 _ (by linarith)
    have hsmallN : ∀ᶠ j : ℕ in atTop, Nv * (1 / ((j : ℝ) + 1)) < ε₀ / 2 := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul Nv
      rw [mul_zero] at this
      exact (tendsto_order.1 this).2 _ (half_pos hε₀)
    obtain ⟨j, hj1, hj2⟩ := (hevent.and hsmallN).exists
    have hψj := hψA (m j)
    have hvW : (v + fun χ => ((Nv : ℝ) : ℂ) * w j χ) ∈ zSpace R := gl84_zadd_mem hv (hWZ j)
    have hupper := gl84_dual_le hvW hψj
    rw [hψ1 (m j), ENNReal.toReal_one, mul_one] at hupper
    have hadd := gl84_SI_add hψj (hKcl j)
    rw [hψ1 (m j)] at hadd
    have hfin1 : LiZhongQC.surfaceIntegral (c (m j) • φ' (m j))
        (fun y z => (Kc j).indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (le_self_add.trans_eq hadd)
    have hfin2 : LiZhongQC.surfaceIntegral (c (m j) • φ' (m j))
        (fun y z => (Kc j)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans_eq hadd)
    have hsum := congrArg ENNReal.toReal hadd
    rw [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_one] at hsum
    have hk := ENNReal.toReal_lt_of_lt_ofReal (hm j)
    set SIc := (LiZhongQC.surfaceIntegral (c (m j) • φ' (m j))
        (fun y z => (Kc j)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z))).toReal with hSIc
    have hSIc0 : 0 ≤ SIc := ENNReal.toReal_nonneg
    have hval : (v + fun χ => ((Nv : ℝ) : ℂ) * w j χ) (c (m j) • φ' (m j)) =
        ((‖v (φ' (m j))‖ + Nv * SIc : ℝ) : ℂ) := by
      show v (c (m j) • φ' (m j)) + ((Nv : ℝ) : ℂ) * w j (c (m j) • φ' (m j)) = _
      rw [hvψ, hweq j]
      push_cast
      ring
    rw [hval, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hupper
    have h1 := hτε (m j)
    have h2 : Nv * (1 - 1 / ((j : ℝ) + 1)) ≤ Nv * SIc :=
      mul_le_mul_of_nonneg_left (by linarith) hNv0
    nlinarith

/-- **Theorem 7** (§8.4, l. 6734). `v ∈ Z` with `‖v‖ ≤ 1` lies in `Z₀` if and only if `‖v + wₙ‖ → ‖v‖` for every
vanishing sequence `wₙ` with `‖wₙ‖ ≤ ‖v‖`.
[CORRECTION] The hypothesis `‖v‖ ≤ 1` is added. A vanishing sequence has `‖wₙ‖ ≤ 1`, so for `‖v‖ > 1` the right-hand
side cannot detect `v ∉ Z₀` (the book's proof starts "an element `v` of norm `1`"). Indeed for every `v ∈ Z` and
vanishing `wₙ`, `limsup ‖v + wₙ‖ ≤ max (‖v‖, β(v) + 1)`, and `v = 3u₀ + v₁` (`u₀ ∈ Z₀` of norm `1`,
`v₁ ∈ Z ∖ Z₀` of norm `≤ 1`) has `β(v) ≤ 1`, `‖v‖ ≥ 2` and `v ∉ Z₀` whenever `Z₀ ≠ Z`; the analogue in
`c₀ ⊂ ℓ∞` is `v = (5, 1, 1, …)`. -/
theorem thm8_7 [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {v : (R → ℂ → ℂ) → ℂ} (hv : v ∈ zSpace R)
    (hv1 : zNorm v ≤ 1) :
    v ∈ zZeroSpace R ↔ ∀ w : ℕ → (R → ℂ → ℂ) → ℂ, IsVanishingSeqZ w → (∀ n, zNorm (w n) ≤ zNorm v) →
      Tendsto (fun n => zNorm (v + w n)) atTop (𝓝 (zNorm v)) := by
  refine ⟨fun h w hw hle => gl84_forward h hw hle, fun h => ?_⟩
  by_contra hv0
  obtain ⟨w, hw, hle, hnot⟩ := gl84_backward hv hv1 hv0
  exact hnot (h w hw hle)

/-- **Corollary 1** (§8.4, l. 6746). Every complex-linear isometry `L` of `Z` preserves `Z₀`. -/
theorem cor8_7_1 [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {L : ((R → ℂ → ℂ) → ℂ) → (R → ℂ → ℂ) → ℂ}
    (hL : IsLinearIsometryOnto (zSpace R) (zSpace R) (fun V => ENNReal.ofReal (zNorm V))
      (fun V => ENNReal.ofReal (zNorm V)) L) :
    ∀ v ∈ zZeroSpace R, L v ∈ zZeroSpace R := by
  sorry

/-- **Theorem 8** (the adjointness theorem, §8.4, l. 6758). Any isometry `L` of `Z` is induced by an isometry `S` of
`A`: `L(V)(φ) = V(S(φ))`. -/
theorem thm8_8 [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {L : ((R → ℂ → ℂ) → ℂ) → (R → ℂ → ℂ) → ℂ}
    (hL : IsLinearIsometryOnto (zSpace R) (zSpace R) (fun V => ENNReal.ofReal (zNorm V))
      (fun V => ENNReal.ofReal (zNorm V)) L) :
    ∃ S : (R → ℂ → ℂ) → (R → ℂ → ℂ),
      IsLinearIsometryOnto (integrableHolQDSet R) (integrableHolQDSet R) quadDiffNorm quadDiffNorm S ∧
        ∀ V ∈ zSpace R, ∀ φ ∈ integrableHolQDSet R, L V φ = V (S φ) := by
  sorry

end GardinerLakic2000
