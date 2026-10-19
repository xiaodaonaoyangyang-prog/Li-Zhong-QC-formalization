import LiZhongQC.Lemmas.SchottkyNonOrientableCover
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# End compactification of a double cover

Generic facts for `T = Y ⊕ ι`, the space `Y` with one point added at each of finitely many ends
given by charts `W i : Y ⇀ ℂ` onto punctured discs: the topology is described by an
`IsOpen` characterisation (`hT`), and we prove that the inclusion of `Y` is an open embedding, the
extended maps are continuous, `T` is Hausdorff, compact and connected, and, if the end charts are
analytic, `T` carries a Riemann surface structure extending that of `Y`.  The end charts are
analytic when the square of the chart is the composite of a chart of the base with a covering
(`s82bc_endchart_mem_maximalAtlas`, via the continuous square root lemma `s82bc_sqrt_analyticAt`).
-/

open Set Topology Filter
open scoped Manifold ContDiff

noncomputable section
namespace LiZhongQC
universe u

/-- A continuous square root of an analytic nonvanishing function is analytic. -/
theorem s82bc_sqrt_analyticAt {g w : ℂ → ℂ} {z₁ : ℂ} (hg : AnalyticAt ℂ g z₁) (hg0 : g z₁ ≠ 0)
    (hw : ContinuousAt w z₁) (hsq : ∀ᶠ z in 𝓝 z₁, w z ^ 2 = g z) : AnalyticAt ℂ w z₁ := by
  have hw1 : w z₁ ^ 2 = g z₁ := hsq.self_of_nhds
  have hw0 : w z₁ ≠ 0 := by
    intro h; apply hg0; rw [← hw1, h]; ring
  let σ : ℂ → ℂ := fun z => w z₁ * (g z / g z₁) ^ (((2 : ℕ) : ℂ)⁻¹)
  have hone : g z₁ / g z₁ = 1 := div_self hg0
  have hσa : AnalyticAt ℂ σ z₁ := by
    refine analyticAt_const.mul ?_
    refine AnalyticAt.cpow (hg.div analyticAt_const hg0) analyticAt_const ?_
    rw [hone]; exact Complex.one_mem_slitPlane
  have hσsq : ∀ z, σ z ^ 2 = g z := by
    intro z
    show (w z₁ * (g z / g z₁) ^ (((2 : ℕ) : ℂ)⁻¹)) ^ 2 = g z
    rw [mul_pow, Complex.cpow_nat_inv_pow _ (by norm_num), hw1, mul_div_cancel₀ _ hg0]
  have hσ1 : σ z₁ = w z₁ := by
    show w z₁ * (g z₁ / g z₁) ^ (((2 : ℕ) : ℂ)⁻¹) = w z₁
    rw [hone, Complex.one_cpow, mul_one]
  have hσc : ContinuousAt σ z₁ := hσa.continuousAt
  have h1 : ∀ᶠ z in 𝓝 z₁, ‖w z - σ z‖ < ‖w z₁‖ := by
    have hc : ContinuousAt (fun z => ‖w z - σ z‖) z₁ := (hw.sub hσc).norm
    refine hc.eventually_lt continuousAt_const ?_
    show ‖w z₁ - σ z₁‖ < ‖w z₁‖
    rw [hσ1, sub_self, norm_zero]
    exact norm_pos_iff.mpr hw0
  have h2 : ∀ᶠ z in 𝓝 z₁, ‖w z₁‖ / 2 < ‖σ z‖ := by
    refine continuousAt_const.eventually_lt hσc.norm ?_
    show ‖w z₁‖ / 2 < ‖σ z₁‖
    rw [hσ1]
    have := norm_pos_iff.mpr hw0
    linarith
  have hev : ∀ᶠ z in 𝓝 z₁, w z = σ z := by
    filter_upwards [hsq, h1, h2] with z hz hz1 hz2
    have hfac : (w z - σ z) * (w z + σ z) = 0 := by
      have : (w z - σ z) * (w z + σ z) = w z ^ 2 - σ z ^ 2 := by ring
      rw [this, hz, hσsq z, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have h3 : w z - σ z = -(2 * σ z) := by linear_combination h
      rw [h3, norm_neg, norm_mul] at hz1
      have : ‖(2 : ℂ)‖ = 2 := by simp
      rw [this] at hz1
      linarith
  exact hσa.congr (hev.mono fun z h => h.symm)

section EndCompactification

variable {Y X : Type*} [TopologicalSpace Y] {ι : Type*}
  (W : ι → OpenPartialHomeomorph Y ℂ)

/-- The tail of the `i`-th end: points of the end chart with `‖W i y‖ < s`. -/
theorem s82bc_tail_open (i : ι) (s : ℝ) :
    IsOpen {y : Y | y ∈ (W i).source ∧ ‖W i y‖ < s} := by
  have : {y : Y | y ∈ (W i).source ∧ ‖W i y‖ < s} = (W i).source ∩ (W i) ⁻¹' {v : ℂ | ‖v‖ < s} :=
    rfl
  rw [this]
  exact (W i).isOpen_inter_preimage (isOpen_lt continuous_norm continuous_const)

variable [τT : TopologicalSpace (Y ⊕ ι)]
  (hT : ∀ V : Set (Y ⊕ ι), IsOpen V ↔ (IsOpen (Sum.inl ⁻¹' V) ∧ ∀ i, Sum.inr i ∈ V →
    ∃ s > 0, ∀ y ∈ (W i).source, ‖W i y‖ < s → Sum.inl y ∈ V))

include hT in
theorem s82bc_inl_openEmbedding : Topology.IsOpenEmbedding (Sum.inl : Y → Y ⊕ ι) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ Sum.inl_injective ?_
  · exact continuous_def.mpr fun V hV => ((hT V).mp hV).1
  · intro V hV
    refine (hT _).mpr ⟨?_, ?_⟩
    · rwa [Sum.inl_injective.preimage_image]
    · rintro i ⟨y, _, h⟩
      exact absurd h (by simp)

include hT in
theorem s82bc_end_nhd_open (i : ι) (s : ℝ) (hs : 0 < s) :
    IsOpen (insert (Sum.inr i : Y ⊕ ι) (Sum.inl '' {y : Y | y ∈ (W i).source ∧ ‖W i y‖ < s})) := by
  refine (hT _).mpr ⟨?_, ?_⟩
  · have : (Sum.inl : Y → Y ⊕ ι) ⁻¹' insert (Sum.inr i)
        (Sum.inl '' {y : Y | y ∈ (W i).source ∧ ‖W i y‖ < s}) =
        {y : Y | y ∈ (W i).source ∧ ‖W i y‖ < s} := by
      ext y
      simp [Sum.inl_injective.eq_iff]
    rw [this]
    exact s82bc_tail_open W i s
  · intro j hj
    have hji : j = i := by
      rcases hj with h | ⟨y, _, h⟩
      · exact Sum.inr_injective h
      · exact absurd h (by simp)
    subst hji
    exact ⟨s, hs, fun y hy hys => Or.inr ⟨y, ⟨hy, hys⟩, rfl⟩⟩

include hT in
theorem s82bc_end_nhds_iff (i : ι) (A : Set (Y ⊕ ι)) :
    A ∈ 𝓝 (Sum.inr i : Y ⊕ ι) ↔ ∃ s > 0,
      insert (Sum.inr i : Y ⊕ ι) (Sum.inl '' {y : Y | y ∈ (W i).source ∧ ‖W i y‖ < s}) ⊆ A := by
  constructor
  · intro hA
    obtain ⟨V, hVA, hVo, hiV⟩ := mem_nhds_iff.mp hA
    obtain ⟨s, hs, hsV⟩ := ((hT V).mp hVo).2 i hiV
    refine ⟨s, hs, ?_⟩
    rintro _ (rfl | ⟨y, ⟨hy, hys⟩, rfl⟩)
    · exact hVA hiV
    · exact hVA (hsV y hy hys)
  · rintro ⟨s, hs, hsub⟩
    exact mem_nhds_iff.mpr ⟨_, hsub, s82bc_end_nhd_open W hT i s hs, Or.inl rfl⟩

include hT in
theorem s82bc_pr_continuous [TopologicalSpace X] (ψ : Y → X) (e : ι → X) (hψ : Continuous ψ)
    (hlim : ∀ i, ∀ A ∈ 𝓝 (e i), ∃ s > 0, ∀ y ∈ (W i).source, ‖W i y‖ < s → ψ y ∈ A) :
    Continuous (Sum.elim ψ e) := by
  refine continuous_def.mpr fun B hB => (hT _).mpr ⟨?_, ?_⟩
  · exact hB.preimage hψ
  · intro i hi
    have hBi : B ∈ 𝓝 (e i) := hB.mem_nhds hi
    obtain ⟨s, hs, hsy⟩ := hlim i B hBi
    exact ⟨s, hs, fun y hy hys => hsy y hy hys⟩

include hT in
theorem s82bc_t2 [TopologicalSpace X] [T2Space X] [T2Space Y] (ψ : Y → X) (e : ι → X)
    (hpr : Continuous (Sum.elim ψ e)) (he : Function.Injective e) (hne : ∀ y i, ψ y ≠ e i) :
    T2Space (Y ⊕ ι) := by
  have hopen := s82bc_inl_openEmbedding W hT
  refine ⟨fun a b hab => ?_⟩
  rcases a with y | i <;> rcases b with y' | j
  · obtain ⟨u, v, hu, hv, hyu, hyv, huv⟩ := t2_separation (fun h : y = y' => hab (by rw [h]))
    refine ⟨Sum.inl '' u, Sum.inl '' v, hopen.isOpenMap _ hu, hopen.isOpenMap _ hv,
      ⟨y, hyu, rfl⟩, ⟨y', hyv, rfl⟩, ?_⟩
    exact (Set.disjoint_image_iff hopen.injective).mpr huv
  · obtain ⟨u, v, hu, hv, hyu, hyv, huv⟩ := t2_separation (hne y j)
    exact ⟨_, _, hu.preimage hpr, hv.preimage hpr, hyu, hyv, huv.preimage _⟩
  · obtain ⟨u, v, hu, hv, hyu, hyv, huv⟩ := t2_separation (hne y' i).symm
    exact ⟨_, _, hu.preimage hpr, hv.preimage hpr, hyu, hyv, huv.preimage _⟩
  · have : e i ≠ e j := fun h => hab (by rw [he h])
    obtain ⟨u, v, hu, hv, hyu, hyv, huv⟩ := t2_separation this
    exact ⟨_, _, hu.preimage hpr, hv.preimage hpr, hyu, hyv, huv.preimage _⟩

include hT in
theorem s82bc_phi_continuousOn (i : ι) (R : ℝ) (hR : 0 < R)
    (hWt : (W i).target = {v : ℂ | 0 < ‖v‖ ∧ ‖v‖ < R}) :
    ContinuousOn (fun v : ℂ => if v = 0 then (Sum.inr i : Y ⊕ ι) else Sum.inl ((W i).symm v))
      (Metric.ball (0 : ℂ) R) := by
  classical
  have hinl := (s82bc_inl_openEmbedding W hT).continuous
  intro v hv
  have hvR : ‖v‖ < R := by simpa using hv
  by_cases h0 : v = 0
  · subst h0
    refine ContinuousAt.continuousWithinAt ?_
    intro A hA
    have hA' : A ∈ 𝓝 (Sum.inr i : Y ⊕ ι) := by simpa using hA
    have hφ0 : (if (0 : ℂ) = 0 then (Sum.inr i : Y ⊕ ι) else Sum.inl ((W i).symm 0)) = Sum.inr i :=
      by simp
    obtain ⟨s', hs', hsub⟩ := (s82bc_end_nhds_iff W hT i A).mp hA'
    rw [Filter.mem_map]
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) (lt_min hs' hR)) ?_
    intro v hvb
    rw [mem_preimage]
    by_cases hv0 : v = 0
    · rw [hv0]; simp only [if_true]; exact hsub (Or.inl rfl)
    · have hvn : ‖v‖ < min s' R := by simpa using hvb
      have hvt : v ∈ (W i).target := by
        rw [hWt]; exact ⟨norm_pos_iff.mpr hv0, lt_of_lt_of_le hvn (min_le_right _ _)⟩
      simp only [if_neg hv0]
      refine hsub (Or.inr ⟨(W i).symm v, ⟨(W i).map_target hvt, ?_⟩, rfl⟩)
      rw [(W i).right_inv hvt]
      exact lt_of_lt_of_le hvn (min_le_left _ _)
  · have hvt : v ∈ (W i).target := by
      rw [hWt]
      exact ⟨norm_pos_iff.mpr h0, hvR⟩
    refine ContinuousAt.continuousWithinAt ?_
    have hev : (fun v : ℂ => if v = 0 then (Sum.inr i : Y ⊕ ι) else Sum.inl ((W i).symm v))
        =ᶠ[𝓝 v] fun v => Sum.inl ((W i).symm v) := by
      filter_upwards [isOpen_ne.mem_nhds h0] with u hu
      simp [hu]
    refine ContinuousAt.congr ?_ hev.symm
    exact hinl.continuousAt.comp ((W i).continuousAt_symm hvt)

include hT in
theorem s82bc_end_compact (i : ι) (R s : ℝ) (hs0 : 0 < s) (hsR : s < R)
    (hWt : (W i).target = {v : ℂ | 0 < ‖v‖ ∧ ‖v‖ < R}) :
    IsCompact (insert (Sum.inr i : Y ⊕ ι)
      (Sum.inl '' {y : Y | y ∈ (W i).source ∧ ‖W i y‖ ≤ s})) := by
  classical
  let φ : ℂ → Y ⊕ ι := fun v => if v = 0 then Sum.inr i else Sum.inl ((W i).symm v)
  have hset : insert (Sum.inr i : Y ⊕ ι) (Sum.inl '' {y : Y | y ∈ (W i).source ∧ ‖W i y‖ ≤ s}) =
      φ '' Metric.closedBall (0 : ℂ) s := by
    ext t
    constructor
    · rintro (rfl | ⟨y, ⟨hy, hys⟩, rfl⟩)
      · exact ⟨0, by simpa using hs0.le, by simp [φ]⟩
      · have hv : W i y ∈ (W i).target := (W i).map_source hy
        rw [hWt] at hv
        refine ⟨W i y, by simpa using hys, ?_⟩
        simp only [φ]
        rw [if_neg (norm_pos_iff.mp hv.1), (W i).left_inv hy]
    · rintro ⟨v, hv, rfl⟩
      by_cases h0 : v = 0
      · left; simp [φ, h0]
      · right
        have hvt : v ∈ (W i).target := by
          rw [hWt]
          exact ⟨norm_pos_iff.mpr h0, lt_of_le_of_lt (by simpa using hv) hsR⟩
        refine ⟨(W i).symm v, ⟨(W i).map_target hvt, ?_⟩, by simp [φ, h0]⟩
        rw [(W i).right_inv hvt]; simpa using hv
  rw [hset]
  refine (isCompact_closedBall (0 : ℂ) s).image_of_continuousOn ?_
  exact (s82bc_phi_continuousOn W hT i R (lt_trans hs0 hsR) hWt).mono
    (fun v hv => by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (by simpa using hv) hsR)

end EndCompactification

section EndCharts

variable {Y : Type*} [TopologicalSpace Y] {ι : Type*}
  (W : ι → OpenPartialHomeomorph Y ℂ) (R : ι → ℝ)
  (hWt : ∀ i, (W i).target = {v : ℂ | 0 < ‖v‖ ∧ ‖v‖ < R i}) (hR : ∀ i, 0 < R i)
  [τT : TopologicalSpace (Y ⊕ ι)]
  (hT : ∀ V : Set (Y ⊕ ι), IsOpen V ↔ (IsOpen (Sum.inl ⁻¹' V) ∧ ∀ i, Sum.inr i ∈ V →
    ∃ s > 0, ∀ y ∈ (W i).source, ‖W i y‖ < s → Sum.inl y ∈ V))

include hT hWt hR in
/-- The extended end chart: the end chart `W i` together with the added point `inr i`. -/
theorem s82bc_endchart_exists :
    ∃ Wend : ι → OpenPartialHomeomorph (Y ⊕ ι) ℂ,
      (∀ i, (Wend i).source = insert (Sum.inr i) (Sum.inl '' (W i).source)) ∧
      (∀ i, (Wend i).target = Metric.ball (0 : ℂ) (R i)) ∧
      (∀ i y, Wend i (Sum.inl y) = W i y) ∧ (∀ i j, Wend i (Sum.inr j) = 0) ∧
      (∀ i v, v ∈ (W i).target → (Wend i).symm v = Sum.inl ((W i).symm v)) ∧
      (∀ i, (Wend i).symm 0 = Sum.inr i) := by
  classical
  have hinl := s82bc_inl_openEmbedding W hT
  have hball : ∀ i, Metric.ball (0 : ℂ) (R i) = insert 0 (W i).target := by
    intro i
    ext v
    rw [hWt i]
    simp only [Metric.mem_ball, dist_zero_right, mem_insert_iff, mem_setOf_eq]
    constructor
    · intro h
      by_cases hv : v = 0
      · exact Or.inl hv
      · exact Or.inr ⟨norm_pos_iff.mpr hv, h⟩
    · rintro (rfl | h)
      · simpa using hR i
      · exact h.2
  have hne0 : ∀ i y, y ∈ (W i).source → W i y ≠ 0 := by
    intro i y hy h
    have : W i y ∈ (W i).target := (W i).map_source hy
    rw [hWt i] at this
    exact (norm_pos_iff.mp this.1) h
  have hsrc_open : ∀ i, IsOpen (insert (Sum.inr i : Y ⊕ ι) (Sum.inl '' (W i).source)) := by
    intro i
    refine (hT _).mpr ⟨?_, ?_⟩
    · have : (Sum.inl : Y → Y ⊕ ι) ⁻¹' insert (Sum.inr i) (Sum.inl '' (W i).source) =
          (W i).source := by
        ext y; simp [Sum.inl_injective.eq_iff]
      rw [this]; exact (W i).open_source
    · intro j hj
      have hji : j = i := by
        rcases hj with h | ⟨y, _, h⟩
        · exact Sum.inr_injective h
        · exact absurd h (by simp)
      subst hji
      exact ⟨1, one_pos, fun y hy _ => Or.inr ⟨y, hy, rfl⟩⟩
  have hcont_f : ∀ i, ContinuousOn
      (fun t : Y ⊕ ι => Sum.elim (fun y => W i y) (fun _ => (0 : ℂ)) t)
      (insert (Sum.inr i : Y ⊕ ι) (Sum.inl '' (W i).source)) := by
    intro i
    refine continuousOn_of_forall_continuousAt ?_
    rintro t (rfl | ⟨y, hy, rfl⟩)
    · -- continuity at the added point
      rw [ContinuousAt, Filter.tendsto_def]
      intro B hB
      obtain ⟨ε, hε, hεB⟩ := Metric.mem_nhds_iff.mp (by simpa using hB)
      rw [s82bc_end_nhds_iff W hT]
      refine ⟨ε, hε, ?_⟩
      rintro _ (rfl | ⟨y, ⟨hy, hys⟩, rfl⟩)
      · exact mem_preimage.mpr (by simpa using hεB (Metric.mem_ball_self hε))
      · exact mem_preimage.mpr (hεB (by simpa using hys))
    · have hmap := hinl.map_nhds_eq y
      rw [ContinuousAt, ← hmap, Filter.tendsto_map'_iff]
      have : (fun t : Y ⊕ ι => Sum.elim (fun y => W i y) (fun _ => (0 : ℂ)) t) ∘ Sum.inl =
          fun y => W i y := rfl
      rw [Function.comp_def]
      show Filter.Tendsto (fun y => W i y) (𝓝 y) _
      exact ((W i).continuousAt hy).tendsto
  refine ⟨fun i =>
    { toFun := fun t => Sum.elim (fun y => W i y) (fun _ => (0 : ℂ)) t
      invFun := fun v => if v = 0 then Sum.inr i else Sum.inl ((W i).symm v)
      source := insert (Sum.inr i) (Sum.inl '' (W i).source)
      target := Metric.ball (0 : ℂ) (R i)
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := hsrc_open i
      open_target := Metric.isOpen_ball
      continuousOn_toFun := hcont_f i
      continuousOn_invFun := s82bc_phi_continuousOn W hT i (R i) (hR i) (hWt i) },
    fun i => rfl, fun i => rfl, fun i y => rfl, fun i j => rfl, ?_, ?_⟩
  · rintro t (rfl | ⟨y, hy, rfl⟩)
    · simpa using hR i
    · show W i y ∈ _
      rw [hball i]
      exact Or.inr ((W i).map_source hy)
  · intro v hv
    by_cases h0 : v = 0
    · simp [h0]
    · have : v ∈ (W i).target := by
        rw [hball i] at hv
        rcases hv with h | h
        · exact absurd h h0
        · exact h
      simp only [if_neg h0]
      exact Or.inr ⟨(W i).symm v, (W i).map_target this, rfl⟩
  · rintro t (rfl | ⟨y, hy, rfl⟩)
    · simp
    · show (if W i y = 0 then _ else _) = _
      simp only [Sum.elim_inl]
      rw [if_neg (hne0 i y hy), (W i).left_inv hy]
  · intro v hv
    by_cases h0 : v = 0
    · subst h0; simp
    · have : v ∈ (W i).target := by
        rw [hball i] at hv
        rcases hv with h | h
        · exact absurd h h0
        · exact h
      show Sum.elim (fun y => W i y) (fun _ => (0 : ℂ)) (if v = 0 then _ else _) = v
      simp only [if_neg h0]
      exact (W i).right_inv this
  · intro i v hv
    have : v ≠ 0 := by
      rw [hWt i] at hv; exact norm_pos_iff.mp hv.1
    show (if v = 0 then _ else _) = _
    rw [if_neg this]
  · intro i
    show (if (0 : ℂ) = 0 then _ else _) = _
    simp

end EndCharts

section TManifold

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] {ι : Type*}
  (W : ι → OpenPartialHomeomorph Y ℂ) (R : ι → ℝ)
  (hWt : ∀ i, (W i).target = {v : ℂ | 0 < ‖v‖ ∧ ‖v‖ < R i}) (hR : ∀ i, 0 < R i)
  (hWm : ∀ i, W i ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y)
  [τT : TopologicalSpace (Y ⊕ ι)]
  (hT : ∀ V : Set (Y ⊕ ι), IsOpen V ↔ (IsOpen (Sum.inl ⁻¹' V) ∧ ∀ i, Sum.inr i ∈ V →
    ∃ s > 0, ∀ y ∈ (W i).source, ‖W i y‖ < s → Sum.inl y ∈ V))

include hT hWt hR hWm in
/-- **The end compactification of a Riemann surface is a Riemann surface** when the end charts
`W i` are analytic charts. -/
theorem s82bc_T_manifold :
    ∃ (Wend : ι → OpenPartialHomeomorph (Y ⊕ ι) ℂ),
      (∀ i, (Wend i).source = insert (Sum.inr i) (Sum.inl '' (W i).source)) ∧
      (∀ i, (Wend i).target = Metric.ball (0 : ℂ) (R i)) ∧
      (∀ i y, Wend i (Sum.inl y) = W i y) ∧ (∀ i j, Wend i (Sum.inr j) = 0) ∧
      (∀ i v, v ∈ (W i).target → (Wend i).symm v = Sum.inl ((W i).symm v)) ∧
      (∀ i, (Wend i).symm 0 = Sum.inr i) ∧
      ∃ _ : ChartedSpace ℂ (Y ⊕ ι), IsManifold 𝓘(ℂ) ω (Y ⊕ ι) ∧
        (∀ y, chartAt ℂ (Sum.inl y : Y ⊕ ι) =
          (chartAt ℂ y).lift_openEmbedding (s82bc_inl_openEmbedding W hT)) ∧
        (∀ i, chartAt ℂ (Sum.inr i : Y ⊕ ι) = Wend i) := by
  classical
  obtain ⟨Wend, hsrc, htgt, happ_l, happ_r, hsymm, hsymm0⟩ := s82bc_endchart_exists W R hWt hR hT
  have hinl := s82bc_inl_openEmbedding W hT
  let cs : ChartedSpace ℂ (Y ⊕ ι) :=
    { atlas := {e | (∃ y : Y, e = (chartAt ℂ y).lift_openEmbedding hinl) ∨ ∃ i, e = Wend i}
      chartAt := fun t => Sum.elim (fun y => (chartAt ℂ y).lift_openEmbedding hinl)
        (fun i => Wend i) t
      mem_chart_source := by
        rintro (y | i)
        · exact ⟨y, mem_chart_source ℂ y, rfl⟩
        · show Sum.inr i ∈ (Wend i).source
          rw [hsrc]; exact Or.inl rfl
      chart_mem_atlas := by
        rintro (y | i)
        · exact Or.inl ⟨y, rfl⟩
        · exact Or.inr ⟨i, rfl⟩ }
  refine ⟨Wend, hsrc, htgt, happ_l, happ_r, hsymm, hsymm0, cs, ?_, fun y => rfl, fun i => rfl⟩
  have hbt : ∀ i v, v ∈ (W i).target ↔ v ∈ Metric.ball (0 : ℂ) (R i) ∧ v ≠ 0 := by
    intro i v
    rw [hWt i]
    simp only [mem_setOf_eq, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, norm_pos_iff.mp h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨norm_pos_iff.mpr h2, h1⟩
  let G := contDiffGroupoid ω 𝓘(ℂ)
  have hLL : ∀ (c c' : OpenPartialHomeomorph Y ℂ), c ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y →
      c' ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y →
      (c.lift_openEmbedding hinl).symm ≫ₕ (c'.lift_openEmbedding hinl) ∈ G := by
    intro c c' hc hc'
    rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
    exact IsManifold.compatible_of_mem_maximalAtlas hc hc'
  have hLE : ∀ (c : OpenPartialHomeomorph Y ℂ) (j : ι), c ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y →
      (c.lift_openEmbedding hinl).symm ≫ₕ Wend j ∈ G := by
    intro c j hc
    refine G.mem_of_eqOnSource (IsManifold.compatible_of_mem_maximalAtlas hc (hWm j)) ?_
    refine ⟨?_, ?_⟩
    · ext v
      simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        OpenPartialHomeomorph.lift_openEmbedding_target, mem_inter_iff, mem_preimage,
        OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply, hsrc]
      constructor
      · rintro ⟨h1, h2 | ⟨y, hy, hyv⟩⟩
        · exact absurd h2 (by simp)
        · exact ⟨h1, by rwa [← Sum.inl_injective hyv]⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, Or.inr ⟨_, h2, rfl⟩⟩
    · intro v hv
      simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
        OpenPartialHomeomorph.lift_openEmbedding_symm, happ_l]
  have hEL : ∀ (j : ι) (c' : OpenPartialHomeomorph Y ℂ), c' ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y →
      (Wend j).symm ≫ₕ (c'.lift_openEmbedding hinl) ∈ G := by
    intro j c' hc'
    refine G.mem_of_eqOnSource (IsManifold.compatible_of_mem_maximalAtlas (hWm j) hc') ?_
    refine ⟨?_, ?_⟩
    · ext v
      simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        OpenPartialHomeomorph.lift_openEmbedding_source, mem_inter_iff, mem_preimage, htgt]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h0 : v = 0
        · subst h0
          rw [hsymm0] at h2
          obtain ⟨y, _, hy⟩ := h2
          exact absurd hy (by simp)
        · have hv : v ∈ (W j).target := (hbt j v).mpr ⟨h1, h0⟩
          rw [hsymm j v hv] at h2
          obtain ⟨y, hy, hyv⟩ := h2
          exact ⟨hv, by rwa [← Sum.inl_injective hyv]⟩
      · rintro ⟨h1, h2⟩
        refine ⟨((hbt j v).mp h1).1, ?_⟩
        rw [hsymm j v h1]
        exact ⟨_, h2, rfl⟩
    · intro v hv
      simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        mem_inter_iff, mem_preimage, htgt] at hv
      have hv0 : v ≠ 0 := by
        rintro rfl
        rw [hsymm0] at hv
        obtain ⟨y, _, hy⟩ := hv.2
        exact absurd hy (by simp)
      have hvt : v ∈ (W j).target := (hbt j v).mpr ⟨hv.1, hv0⟩
      show (c'.lift_openEmbedding hinl) ((Wend j).symm v) = c' ((W j).symm v)
      rw [hsymm j v hvt]
      exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _
  have hEE : ∀ i j : ι, (Wend i).symm ≫ₕ Wend j ∈ G := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact G.mem_of_eqOnSource
        (ofSet_mem_contDiffGroupoid (I := 𝓘(ℂ)) (n := ω) (Wend i).open_target)
        (OpenPartialHomeomorph.symm_trans_self (Wend i))
    · refine G.mem_of_eqOnSource (IsManifold.compatible_of_mem_maximalAtlas (hWm i) (hWm j)) ?_
      refine ⟨?_, ?_⟩
      · ext v
        simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
          mem_inter_iff, mem_preimage, htgt, hsrc]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases h0 : v = 0
          · subst h0
            rw [hsymm0] at h2
            rcases h2 with h2 | ⟨y, _, hy⟩
            · exact absurd (Sum.inr_injective h2) hij
            · exact absurd hy (by simp)
          · have hv : v ∈ (W i).target := (hbt i v).mpr ⟨h1, h0⟩
            rw [hsymm i v hv] at h2
            rcases h2 with h2 | ⟨y, hy, hyv⟩
            · exact absurd h2 (by simp)
            · exact ⟨hv, by rwa [← Sum.inl_injective hyv]⟩
        · rintro ⟨h1, h2⟩
          refine ⟨((hbt i v).mp h1).1, ?_⟩
          rw [hsymm i v h1]
          exact Or.inr ⟨_, h2, rfl⟩
      · intro v hv
        simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
          mem_inter_iff, mem_preimage, htgt] at hv
        have hv0 : v ≠ 0 := by
          rintro rfl
          rw [hsymm0, hsrc j] at hv
          rcases hv.2 with h2 | ⟨y, _, hy⟩
          · exact hij (Sum.inr_injective h2)
          · exact absurd hy (by simp)
        have hvt : v ∈ (W i).target := (hbt i v).mpr ⟨hv.1, hv0⟩
        show Wend j ((Wend i).symm v) = W j ((W i).symm v)
        rw [hsymm i v hvt, happ_l]
  refine { compatible := ?_ }
  intro e e' he he'
  rcases he with ⟨y, rfl⟩ | ⟨i, rfl⟩ <;> rcases he' with ⟨y', rfl⟩ | ⟨j, rfl⟩
  · exact hLL _ _ (IsManifold.chart_mem_maximalAtlas y) (IsManifold.chart_mem_maximalAtlas y')
  · exact hLE _ j (IsManifold.chart_mem_maximalAtlas y)
  · exact hEL i _ (IsManifold.chart_mem_maximalAtlas y')
  · exact hEE i j

end TManifold

theorem s82bc_mem_groupoid_iff (f : OpenPartialHomeomorph ℂ ℂ) :
    f ∈ contDiffGroupoid ω 𝓘(ℂ) ↔ ContDiffOn ℂ ω f f.source ∧ ContDiffOn ℂ ω f.symm f.target := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, preimage_id, range_id, inter_univ]

section ChartCompat

variable {S Y : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **The end chart is an analytic chart.**  If `W0` is a homeomorphism from an open subset of the
cover `Y` to a punctured disc whose square is the chart `E` of the base composed with the covering
`q`, and `q` reads as the identity in the charts `chartAt`, then `W0` belongs to the maximal atlas
of `Y`. -/
theorem s82bc_endchart_mem_maximalAtlas
    (hatlas : ∀ e' ∈ atlas ℂ Y, ∃ y : Y, e' = chartAt ℂ y)
    (q : Y → S)
    (hchart : ∀ y y', y' ∈ (chartAt ℂ y).source → q y' ∈ (chartAt ℂ (q y)).source ∧
      chartAt ℂ (q y) (q y') = chartAt ℂ y y')
    (E : OpenPartialHomeomorph S ℂ) (hEm : E ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω S)
    (W0 : OpenPartialHomeomorph Y ℂ)
    (hsq : ∀ y ∈ W0.source, q y ∈ E.source ∧ W0 y ^ 2 = E (q y))
    (hne : ∀ y ∈ W0.source, W0 y ≠ 0) :
    W0 ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y := by
  intro e' he'
  obtain ⟨y0, rfl⟩ := hatlas e' he'
  set f0 := chartAt ℂ (q y0) with hf0
  have hf0m : f0 ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω S := IsManifold.chart_mem_maximalAtlas _
  have hΦ := (s82bc_mem_groupoid_iff _).mp
    (IsManifold.compatible_of_mem_maximalAtlas hEm hf0m)
  have hΨ := (s82bc_mem_groupoid_iff _).mp
    (IsManifold.compatible_of_mem_maximalAtlas hf0m hEm)
  have hT1 : W0.symm ≫ₕ chartAt ℂ y0 ∈ contDiffGroupoid ω 𝓘(ℂ) := by
    rw [s82bc_mem_groupoid_iff]
    constructor
    · -- the forward transition is `Φ ∘ (v ↦ v²)`
      have hΦc : ContDiffOn ℂ ω (E.symm ≫ₕ f0) (E.symm ≫ₕ f0).source := hΦ.1
      have hmaps : MapsTo (fun v : ℂ => v ^ 2) (W0.symm ≫ₕ chartAt ℂ y0).source
          (E.symm ≫ₕ f0).source := by
        intro v hv
        obtain ⟨hvt, hvs⟩ : v ∈ W0.target ∧ W0.symm v ∈ (chartAt ℂ y0).source := hv
        have hy : W0.symm v ∈ W0.source := W0.map_target hvt
        obtain ⟨hqE, hsq'⟩ := hsq _ hy
        rw [W0.right_inv hvt] at hsq'
        refine ⟨?_, ?_⟩
        · show v ^ 2 ∈ E.target
          rw [hsq']; exact E.map_source hqE
        · show E.symm (v ^ 2) ∈ f0.source
          rw [hsq', E.left_inv hqE]; exact (hchart y0 _ hvs).1
      refine (hΦc.comp (contDiff_id.pow 2).contDiffOn hmaps).congr ?_
      intro v hv
      obtain ⟨hvt, hvs⟩ : v ∈ W0.target ∧ W0.symm v ∈ (chartAt ℂ y0).source := hv
      have hy : W0.symm v ∈ W0.source := W0.map_target hvt
      obtain ⟨hqE, hsq'⟩ := hsq _ hy
      rw [W0.right_inv hvt] at hsq'
      show chartAt ℂ y0 (W0.symm v) = f0 (E.symm (v ^ 2))
      rw [hsq', E.left_inv hqE]
      exact ((hchart y0 _ hvs).2).symm
    · -- the inverse transition, by the square-root lemma
      intro u hu
      refine ContDiffAt.contDiffWithinAt ?_
      have hu2 := hu
      obtain ⟨hut, hus⟩ : u ∈ (chartAt ℂ y0).target ∧ (chartAt ℂ y0).symm u ∈ W0.source := hu2
      set y := (chartAt ℂ y0).symm u with hy
      have hys : y ∈ (chartAt ℂ y0).source := (chartAt ℂ y0).map_target hut
      have hyu : chartAt ℂ y0 y = u := (chartAt ℂ y0).right_inv hut
      obtain ⟨hqs, hqf⟩ := hchart y0 y hys
      obtain ⟨hqE, hsqy⟩ := hsq y hus
      have hqy : q y = f0.symm u := by
        rw [← hyu, ← hqf, f0.left_inv hqs]
      have hΨsrc : u ∈ (f0.symm ≫ₕ E).source := by
        refine ⟨?_, ?_⟩
        · show u ∈ f0.target
          rw [← hyu, ← hqf]; exact f0.map_source hqs
        · show f0.symm u ∈ E.source
          rw [← hqy]; exact hqE
      have hgA : AnalyticAt ℂ (fun u' => E (f0.symm u')) u :=
        ((hΨ.1.contDiffAt ((f0.symm ≫ₕ E).open_source.mem_nhds hΨsrc)).analyticAt)
      have hg0 : E (f0.symm u) ≠ 0 := by
        rw [← hqy, ← hsqy]
        exact pow_ne_zero 2 (hne y hus)
      have hwc : ContinuousAt (W0.symm ≫ₕ chartAt ℂ y0).symm u :=
        (W0.symm ≫ₕ chartAt ℂ y0).continuousAt_symm hu
      have hev : ∀ᶠ u' in 𝓝 u, ((W0.symm ≫ₕ chartAt ℂ y0).symm u') ^ 2 = E (f0.symm u') := by
        filter_upwards [(W0.symm ≫ₕ chartAt ℂ y0).open_target.mem_nhds hu] with u' hu'
        obtain ⟨hut', hus'⟩ : u' ∈ (chartAt ℂ y0).target ∧ (chartAt ℂ y0).symm u' ∈ W0.source := hu'
        have hys' : (chartAt ℂ y0).symm u' ∈ (chartAt ℂ y0).source :=
          (chartAt ℂ y0).map_target hut'
        have hyu' : chartAt ℂ y0 ((chartAt ℂ y0).symm u') = u' := (chartAt ℂ y0).right_inv hut'
        obtain ⟨hqs', hqf'⟩ := hchart y0 _ hys'
        obtain ⟨hqE', hsqy'⟩ := hsq _ hus'
        have hqy' : q ((chartAt ℂ y0).symm u') = f0.symm u' := by
          have h1 : f0 (q ((chartAt ℂ y0).symm u')) = u' := hqf'.trans hyu'
          rw [← h1, f0.left_inv hqs', h1]
        show (W0 ((chartAt ℂ y0).symm u')) ^ 2 = _
        rw [hsqy', hqy']
      exact (s82bc_sqrt_analyticAt hgA hg0 hwc hev).contDiffAt
  refine ⟨hT1, ?_⟩
  have := (contDiffGroupoid ω 𝓘(ℂ)).symm hT1
  rwa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm] at this

end ChartCompat

section MDiffTools

variable {A B : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) 1 A]
  [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) 1 B]

/-- A continuous map which, in the canonical charts, agrees near a point with a function
differentiable at that point is holomorphic there. -/
theorem s82bc_mdiffAt_of_charts (f : A → B) (a : A) (hf : ContinuousAt f a) (G : ℂ → ℂ)
    (hG : DifferentiableAt ℂ G (chartAt ℂ a a))
    (h : ∀ᶠ z in 𝓝 (chartAt ℂ a a), chartAt ℂ (f a) (f ((chartAt ℂ a).symm z)) = G z) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f a := by
  rw [mdifferentiableAt_iff_of_mem_source (mem_chart_source ℂ a) (mem_chart_source ℂ (f a))]
  refine ⟨hf, ?_⟩
  have e1 : ⇑(extChartAt 𝓘(ℂ) a) = chartAt ℂ a := by
    rw [extChartAt_coe]; rfl
  have e2 : ⇑(extChartAt 𝓘(ℂ) (f a)) = chartAt ℂ (f a) := by
    rw [extChartAt_coe]; rfl
  have e3 : ⇑(extChartAt 𝓘(ℂ) a).symm = (chartAt ℂ a).symm := by
    rw [extChartAt_coe_symm]; rfl
  rw [e1, e2, e3]
  refine DifferentiableAt.differentiableWithinAt ?_
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [h] with z hz
  exact hz

end MDiffTools

end LiZhongQC
