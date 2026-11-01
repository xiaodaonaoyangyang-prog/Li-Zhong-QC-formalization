import LiZhongQC.Lemmas.S22gbHoles

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

section GaussBonnetOrders

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S] [CompactSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- A single point has zero hyperbolic area. -/
theorem s22gb_singleton_null {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) (x : S) : s22gm_surfaceArea p F {x} = 0 := by
  obtain ⟨ε, hε, ψ, hball, hψ⟩ := s22gb_lift_ball hp x
  have hct : chartAt ℂ x x ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have hsing : MeasurableSet ({x} : Set S) := measurableSet_singleton x
  have h := s22gb_lintegral_transfer hp hF x (Metric.isOpen_ball (x := chartAt ℂ x x) (ε := ε))
    Metric.isOpen_ball.measurableSet hball (fun z hz => (hψ z hz).1) (fun z hz => (hψ z hz).2.1)
    (fun z hz => (hψ z hz).2.2.1)
    (fun z hz => (hψ z hz).2.2.2.self_of_nhds) (({x} : Set S).indicator 1)
    (measurable_one.indicator hsing) (fun y hy => by
      refine indicator_of_notMem (fun hyx => hy ?_) _
      rw [mem_singleton_iff] at hyx
      subst hyx
      exact ⟨chartAt ℂ y y, Metric.mem_ball_self hε, (chartAt ℂ y).left_inv (mem_chart_source ℂ y)⟩)
  rw [lintegral_indicator_one hsing] at h
  rw [h]
  have hae : ∀ᵐ z ∂(volume.restrict (Metric.ball (chartAt ℂ x x) ε)),
      z ≠ chartAt ℂ x x := by
    refine ae_restrict_of_ae ?_
    have : volume ({chartAt ℂ x x} : Set ℂ) = 0 := measure_singleton _
    exact (measure_eq_zero_iff_ae_notMem.1 this).mono fun z hz => by simpa using hz
  have hz0 : (fun z => (({x} : Set S).indicator 1 : S → ℝ≥0∞) ((chartAt ℂ x).symm z) *
      ENNReal.ofReal (s22gc_areaDensity ψ z)) =ᵐ[volume.restrict (Metric.ball (chartAt ℂ x x) ε)]
      fun _ => 0 := by
    filter_upwards [hae, ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz hzb
    have hzt := hball hzb
    have hne : (chartAt ℂ x).symm z ≠ x := by
      intro hh
      apply hz
      have h2 := (chartAt ℂ x).right_inv hzt
      rw [hh] at h2
      exact h2.symm
    simp [indicator_of_notMem (show (chartAt ℂ x).symm z ∉ ({x} : Set S) from hne)]
  rw [lintegral_congr_ae hz0]
  simp

/-- The boundary period of the gauge around a point of finite order tends to `-2π` times the order. -/
theorem s22gb_boundary_limit {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {q : S → ℂ → ℂ}
    {α : S → ℂ → ℂ → ℝ}
    (hα : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target →
      AnalyticAt ℂ (q x) z → q x z ≠ 0 →
      ∀ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z → deriv ψ z ≠ 0 → ψ z ∈ upperHalf →
        (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z] (fun w => (chartAt ℂ x).symm w) →
        α x =ᶠ[𝓝 z] s22cd_canonicalGauge ψ (q x))
    (x : S) (hm : MeromorphicAt (q x) (chartAt ℂ x x))
    (ho : meromorphicOrderAt (q x) (chartAt ℂ x x) ≠ ⊤) :
    Tendsto (fun r : ℝ => s22cd_rectBoundary (α x)
        (chartAt ℂ x x - (r : ℂ) * (1 + I)) (chartAt ℂ x x + (r : ℂ) * (1 + I)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-(2 * π * ((meromorphicOrderAt (q x) (chartAt ℂ x x)).untop₀ : ℝ)))) := by
  obtain ⟨ε, hε, ψ, hball, hψ⟩ := s22gb_lift_ball hp x
  have hψc := hψ (chartAt ℂ x x) (Metric.mem_ball_self hε)
  have hy : (ψ (chartAt ℂ x x)).im ≠ 0 := ne_of_gt (show 0 < (ψ (chartAt ℂ x x)).im from hψc.2.2.1)
  have hmeq : meromorphicOrderAt (q x) (chartAt ℂ x x) =
      (((meromorphicOrderAt (q x) (chartAt ℂ x x)).untop₀ : ℤ) : WithTop ℤ) :=
    (WithTop.coe_untop₀_of_ne_top ho).symm
  have hP1 := s22sl_canonicalGauge_boundary_limit hψc.1 hψc.2.1 hy hm hmeq
  have he : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), ∀ v, α x z v = s22cd_canonicalGauge ψ (q x) z v := by
    have hhon : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), AnalyticAt ℂ (q x) z ∧ q x z ≠ 0 := by
      filter_upwards [hm.eventually_analyticAt,
        (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hm).1 ho] with z h1 h2
      exact ⟨h1, h2⟩
    filter_upwards [hhon, nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hε)] with z hz hzb v
    have hg := hα x z (hball hzb) hz.1 hz.2 ψ (hψ z hzb).1 (hψ z hzb).2.1 (hψ z hzb).2.2.1
      (hψ z hzb).2.2.2
    exact congrFun hg.self_of_nhds v
  exact hP1.congr' (s22sl_boundary_eventuallyEq_of_punctured_germ he).symm

theorem s22gb_sq_mono {c : ℂ} {r r' : ℝ} (hr : 0 < r) (hrr : r ≤ r') :
    wv_rectK (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I)) ⊆
      wv_rectK (c - (r' : ℂ) * (1 + I)) (c + (r' : ℂ) * (1 + I)) := by
  intro z hz
  obtain ⟨a1, a2, a3, a4⟩ := s22gb_sq_corners (c := c) (δ := r)
  obtain ⟨b1, b2, b3, b4⟩ := s22gb_sq_corners (c := c) (δ := r')
  rw [s22gb_mem_rectK (by rw [a1, a2]; linarith) (by rw [a3, a4]; linarith), a1, a2, a3, a4] at hz
  rw [s22gb_mem_rectK (by rw [b1, b2]; linarith) (by rw [b3, b4]; linarith), b1, b2, b3, b4]
  exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, by linarith [hz.2.1], by linarith [hz.2.2]⟩

/-- (P3a) Exhaustion and limit: the total hyperbolic area is `2π` times the sum of the orders. -/
theorem s22gb_area_eq_orders {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {F : Set ℂ} (hFH : IsFundamentalDomainH Γ F)
    {q : S → ℂ → ℂ} (hq : IsDiffFamily 1 0 q)
    (hmer : ∀ x, MeromorphicAt (q x) (chartAt ℂ x x))
    (hord : ∀ x, meromorphicOrderAt (q x) (chartAt ℂ x x) ≠ ⊤)
    (Z : Finset S) (hZ : ∀ x, x ∉ Z → meromorphicOrderAt (q x) (chartAt ℂ x x) = 0) :
    s22gm_surfaceArea p F Set.univ =
      ENNReal.ofReal (2 * π * ∑ x ∈ Z, ((meromorphicOrderAt (q x) (chartAt ℂ x x)).untop₀ : ℝ)) := by
  classical
  obtain ⟨α, hα, hsm⟩ := s22gb_gauge_exists hp hq
  obtain ⟨r₀, hr₀, hB⟩ := s22gb_area_holes hp hFH hq hmer hord Z hZ α hα hsm
  set μ := s22gm_surfaceArea p F with hμ
  set L : ℝ := 2 * π * ∑ x ∈ Z, ((meromorphicOrderAt (q x) (chartAt ℂ x x)).untop₀ : ℝ) with hL
  set Aset : ℝ → Set S := fun r => Set.univ \ ⋃ x ∈ Z, (chartAt ℂ x).symm ''
    wv_rectK (chartAt ℂ x x - (r : ℂ) * (1 + I)) (chartAt ℂ x x + (r : ℂ) * (1 + I)) with hA
  -- the limit of the finite areas
  have hlim : Tendsto (fun r : ℝ => (μ (Aset r)).toReal) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    have hsum : Tendsto (fun r : ℝ => -∑ x ∈ Z, s22cd_rectBoundary (α x)
        (chartAt ℂ x x - (r : ℂ) * (1 + I)) (chartAt ℂ x x + (r : ℂ) * (1 + I)))
        (𝓝[>] (0 : ℝ)) (𝓝 (-∑ x ∈ Z, -(2 * π *
          ((meromorphicOrderAt (q x) (chartAt ℂ x x)).untop₀ : ℝ)))) :=
      (tendsto_finsetSum Z fun x _ => s22gb_boundary_limit hp hα x (hmer x) (hord x)).neg
    have hval : (-∑ x ∈ Z, -(2 * π * ((meromorphicOrderAt (q x) (chartAt ℂ x x)).untop₀ : ℝ))) = L := by
      rw [hL, Finset.sum_neg_distrib, neg_neg, Finset.mul_sum]
    rw [hval] at hsum
    refine hsum.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
    exact (hB r hr.1 hr.2).2.symm
  have hfin : ∀ r, 0 < r → r < r₀ → μ (Aset r) ≠ ⊤ := fun r h1 h2 => (hB r h1 h2).1
  -- the sequence of radii
  set rn : ℕ → ℝ := fun n => r₀ / ((n : ℝ) + 2) with hrn
  have hrn0 : ∀ n, 0 < rn n := fun n => by positivity
  have hrn1 : ∀ n, rn n < r₀ := fun n => by
    have : (1 : ℝ) < (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    exact (div_lt_self hr₀ this)
  have hrnanti : Antitone rn := by
    intro n m hnm
    have : (n : ℝ) + 2 ≤ (m : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hnm 2
    exact div_le_div_of_nonneg_left hr₀.le (by positivity) this
  have hrnlim : Tendsto rn atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall hrn0⟩
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hmono : Monotone (fun n => Aset (rn n)) := by
    intro n m hnm
    simp only [hA]
    refine diff_subset_diff_right ?_
    refine iUnion₂_mono fun x hx => ?_
    exact image_mono (s22gb_sq_mono (hrn0 m) (hrnanti hnm))
  -- exhaustion
  have hexh : (univ : Set S) \ ↑Z ⊆ ⋃ n, Aset (rn n) := by
    intro y hy
    have hyZ : y ∉ Z := fun h => hy.2 h
    have hev : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), ∀ x ∈ Z, y ∉ (chartAt ℂ x).symm ''
        wv_rectK (chartAt ℂ x x - (r : ℂ) * (1 + I)) (chartAt ℂ x x + (r : ℂ) * (1 + I)) := by
      rw [Filter.eventually_all_finset]
      intro x hx
      have hxy : (chartAt ℂ x).symm (chartAt ℂ x x) ≠ y := by
        rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
        exact fun h => hyZ (h ▸ hx)
      have hct : chartAt ℂ x x ∈ (chartAt ℂ x).target :=
        (chartAt ℂ x).map_source (mem_chart_source ℂ x)
      have h1 : ∀ᶠ w in 𝓝 (chartAt ℂ x x), (chartAt ℂ x).symm w ≠ y :=
        ((chartAt ℂ x).continuousAt_symm hct).eventually_ne hxy
      obtain ⟨ρ, hρ, hρb⟩ := Metric.eventually_nhds_iff_ball.1 h1
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ρ / 4 by positivity)] with r hr
      rintro ⟨w, hw, hwy⟩
      have hwb : w ∈ Metric.ball (chartAt ℂ x x) ρ :=
        s22gb_sq_subset_ball (δ := r) hr.1.le (by linarith [hr.2]) hw
      exact hρb w hwb hwy
    obtain ⟨n, hn⟩ := (hrnlim.eventually hev).exists
    refine mem_iUnion.2 ⟨n, mem_univ _, fun h => ?_⟩
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 h
    exact hn x hx hyx
  have hZnull : μ (↑Z : Set S) = 0 := by
    have : (↑Z : Set S) = ⋃ x ∈ (↑Z : Set S), {x} := (Set.biUnion_of_singleton _).symm
    rw [this, measure_biUnion_null_iff Z.countable_toSet]
    exact fun x _ => s22gb_singleton_null hp hFH x
  have hU : μ (⋃ n, Aset (rn n)) = μ univ := by
    refine le_antisymm (measure_mono (subset_univ _)) ?_
    calc μ univ ≤ μ ((⋃ n, Aset (rn n)) ∪ ↑Z) := measure_mono (fun y _ => by
          by_cases hy : y ∈ (↑Z : Set S)
          · exact Or.inr hy
          · exact Or.inl (hexh ⟨mem_univ _, hy⟩))
      _ ≤ μ (⋃ n, Aset (rn n)) + μ ↑Z := measure_union_le _ _
      _ = μ (⋃ n, Aset (rn n)) := by rw [hZnull, add_zero]
  have hT := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hU] at hT
  -- boundedness, finiteness and identification of the limit
  have hT2 : Tendsto (fun n => (μ (Aset (rn n))).toReal) atTop (𝓝 L) :=
    hlim.comp hrnlim
  have hfin' : ∀ n, μ (Aset (rn n)) ≠ ⊤ := fun n => hfin _ (hrn0 n) (hrn1 n)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ n, (μ (Aset (rn n))).toReal ≤ M :=
    ⟨_, fun n => le_ciSup hT2.bddAbove_range n⟩
  have hle : μ univ ≤ ENNReal.ofReal M := by
    refine le_of_tendsto' hT (fun n => ?_)
    rw [Function.comp_apply, ← ENNReal.ofReal_toReal (hfin' n)]
    exact ENNReal.ofReal_le_ofReal (hM n)
  have hμfin : μ univ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hT3 : Tendsto (fun n => (μ (Aset (rn n))).toReal) atTop (𝓝 (μ univ).toReal) :=
    (ENNReal.tendsto_toReal hμfin).comp hT
  have hL' : (μ univ).toReal = L := tendsto_nhds_unique hT3 hT2
  rw [← hL', ENNReal.ofReal_toReal hμfin]

end GaussBonnetOrders

end LiZhongQC
