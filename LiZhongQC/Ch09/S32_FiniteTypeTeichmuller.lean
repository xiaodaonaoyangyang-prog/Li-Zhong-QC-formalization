import LiZhongQC.Ch09.S31_FiniteType
import LiZhongQC.Lemmas.LocalRoots

/-!
# §32 有限型曲面的 Teichmüller 定理 — Teichmüller's theorem for surfaces of finite type

* §32.1 surfaces of type `(g, n)`: Theorem 32.1 (uniqueness, (32.1)) via the two-sheeted covering
  branched at the punctures (the lifted differential `4ζ²φ(ζ²)dζ²` is holomorphic); Theorem 32.2
  (existence), (32.2)                 — `thm32_1_uniqueness_gn`, `thm32_2_existence_gn`
* §32.2 surfaces of type `(g, n, m)`, `m ≠ 0`, via the Schottky double: Theorem 32.3 (uniqueness),
  Theorem 32.4 (existence), (32.3)     — `thm32_3_uniqueness_gnm`, `thm32_4_existence_gnm`
* §32.3 the Teichmüller space `T_{g,n,m}` of marked surfaces of finite type: every point
  corresponds to `(k, ω)` with `ω ∈ Q̃(S₀)` normalized; `T_{g,n,m} ↔` unit ball of
  `ℝ^{6g-6+2n+3m}`; the Teichmüller distance; the modular group and `R_{g,n,m} = T/Mod`;
  `T_{g,n,m}` has no complex structure when its dimension is odd
                                       — `MarkedFiniteTypeRS`, `TeichSpaceFiniteType`,
                                         `teichSpaceFiniteType_ball`, `teichDistanceFT`

The symmetric lift (32.2) (`eq32_2_symmetric_lift`) is stated and proved in
`LiZhongQC.Lemmas.UniformizedTeichmuller` (moved there by leader decision, 2026-10-12): its proof is the
uniqueness half of Theorem 26.2 on the uniformized double cover, which this chapter cannot import.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- The pull-back `q ∘ ι` (in charts) of a quadratic differential on the closed surface `X` of a
finite type structure `F` to the interior `S`, read in the chart of `X` at the image point `ι(φ_x⁻¹ z)`,
and `0` off the chart target.

**Correction (2026-09-27).**  The pull-back was read in the fixed chart at `ι x` and evaluated `φ_x⁻¹` also
off the chart target, where both have junk values, which in a suitable atlas made every admissible
Teichmüller map impossible (refuted in Lean, s31t); it now uses the image-point chart and vanishes off the
target. -/
def pullbackQD {g n m : ℕ} (F : FiniteTypeStructure S g n m) (q : F.X.carrier → ℂ → ℂ) : S → ℂ → ℂ :=
  fun x => (chartAt ℂ x).target.indicator fun z =>
    q (F.ι ((chartAt ℂ x).symm z)) (chartAt ℂ (F.ι ((chartAt ℂ x).symm z)) (F.ι ((chartAt ℂ x).symm z))) *
      deriv (fun w => chartAt ℂ (F.ι ((chartAt ℂ x).symm z)) (F.ι ((chartAt ℂ x).symm w))) z ^ 2

/-- The pull-back is real linear. -/
def pullbackQDLinear {g n m : ℕ} (F : FiniteTypeStructure S g n m) :
    (F.X.carrier → ℂ → ℂ) →ₗ[ℝ] (S → ℂ → ℂ) where
  toFun := pullbackQD F
  map_add' q₁ q₂ := by
    funext x z
    simp only [pullbackQD, Pi.add_apply]
    by_cases hz : z ∈ (chartAt ℂ x).target
    · simp only [indicator_of_mem hz]
      ring
    · simp only [indicator_of_notMem hz, add_zero]
  map_smul' c q := by
    funext x z
    simp only [pullbackQD, Pi.smul_apply, Complex.real_smul, RingHom.id_apply]
    by_cases hz : z ∈ (chartAt ℂ x).target
    · simp only [indicator_of_mem hz]
      ring
    · simp only [indicator_of_notMem hz, mul_zero]

/-- §32.1: the admissible quadratic differentials of `S₀`, viewed on the interior `S₀` itself: the
pull-backs of the elements of `Q̃(S₀)`. -/
def admissibleQDInterior {g n m : ℕ} (F : FiniteTypeStructure S g n m) : Submodule ℝ (S → ℂ → ℂ) :=
  (admissibleQDSpace F).map (pullbackQDLinear F)

/-- The chart transfer `T = φ_x ∘ ι ∘ φ_y⁻¹` is holomorphic at `w` when `ι(φ_y⁻¹ w)` lies in the chart source at
`x`. -/
theorem s32p_T_differentiableAt [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    (x : F.X.carrier) (y : S) {w : ℂ} (hw : w ∈ (chartAt ℂ y).target)
    (hwx : F.ι ((chartAt ℂ y).symm w) ∈ (chartAt ℂ x).source) :
    DifferentiableAt ℂ (fun v => chartAt ℂ x (F.ι ((chartAt ℂ y).symm v))) w := by
  have h := ((s23_mdifferentiableAt_iff (f := F.ι) (y := x) ((chartAt ℂ y).map_target hw) hwx).1
    (F.holomorphic ((chartAt ℂ y).symm w))).2
  rwa [(chartAt ℂ y).right_inv hw] at h

/-- Local form of the pull-back: in any chart `x` of `X` at the image point, `(ι^* q)_y(w) = q_x(T w) T'(w)²`
with `T = φ_x ∘ ι ∘ φ_y⁻¹` (the transformation law of `q` and the chain rule). -/
theorem s32p_pullbackQD_local [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    {q : F.X.carrier → ℂ → ℂ} (hq : q ∈ admissibleQDSpace F) (y : S) (x : F.X.carrier) {w : ℂ}
    (hw : w ∈ (chartAt ℂ y).target) (hwx : F.ι ((chartAt ℂ y).symm w) ∈ (chartAt ℂ x).source) :
    pullbackQD F q y w = q x (chartAt ℂ x (F.ι ((chartAt ℂ y).symm w))) *
      deriv (fun v => chartAt ℂ x (F.ι ((chartAt ℂ y).symm v))) w ^ 2 := by
  have hlawq : IsDiffFamily 2 0 q := hq.1
  set s := F.ι ((chartAt ℂ y).symm w)
  show (chartAt ℂ y).target.indicator _ w = _
  rw [indicator_of_mem hw]
  show q s (chartAt ℂ s s) * deriv (fun v => chartAt ℂ s (F.ι ((chartAt ℂ y).symm v))) w ^ 2 = _
  have hst : chartAt ℂ s s ∈ (chartAt ℂ s).target := (chartAt ℂ s).map_source (mem_chart_source ℂ s)
  have hss : (chartAt ℂ s).symm (chartAt ℂ s s) = s := (chartAt ℂ s).left_inv (mem_chart_source ℂ s)
  have hlaw : q s (chartAt ℂ s s) = q x (chartTransition x s (chartAt ℂ s s)) *
      deriv (chartTransition x s) (chartAt ℂ s s) ^ 2 := by
    rw [hlawq.2 x s _ hst (by rw [hss]; exact hwx)]
    norm_num
  have hT : chartTransition x s (chartAt ℂ s s) = chartAt ℂ x s := by
    show chartAt ℂ x ((chartAt ℂ s).symm (chartAt ℂ s s)) = chartAt ℂ x s
    rw [hss]
  rw [hT] at hlaw
  have hTd : DifferentiableAt ℂ (chartTransition x s) (chartAt ℂ s s) :=
    s23_transition_differentiableAt x s hst (by rw [hss]; exact hwx)
  have hgd : DifferentiableAt ℂ (fun v => chartAt ℂ s (F.ι ((chartAt ℂ y).symm v))) w :=
    s32p_T_differentiableAt F s y hw (mem_chart_source ℂ s)
  have hcont : ContinuousAt (fun v => F.ι ((chartAt ℂ y).symm v)) w :=
    F.embedding.continuous.continuousAt.comp ((chartAt ℂ y).continuousAt_symm hw)
  have hev : (fun v => chartAt ℂ x (F.ι ((chartAt ℂ y).symm v))) =ᶠ[𝓝 w]
      chartTransition x s ∘ fun v => chartAt ℂ s (F.ι ((chartAt ℂ y).symm v)) := by
    filter_upwards [hcont.preimage_mem_nhds ((chartAt ℂ s).open_source.mem_nhds (mem_chart_source ℂ s))]
      with v hv
    show chartAt ℂ x (F.ι ((chartAt ℂ y).symm v)) =
      chartAt ℂ x ((chartAt ℂ s).symm (chartAt ℂ s (F.ι ((chartAt ℂ y).symm v))))
    rw [(chartAt ℂ s).left_inv hv]
  have hder : deriv (fun v => chartAt ℂ x (F.ι ((chartAt ℂ y).symm v))) w =
      deriv (chartTransition x s) (chartAt ℂ s s) *
        deriv (fun v => chartAt ℂ s (F.ι ((chartAt ℂ y).symm v))) w := by
    rw [hev.deriv_eq]
    exact (hTd.hasDerivAt.comp w hgd.hasDerivAt).deriv
  rw [hder, hlaw]
  ring

/-- The pull-back of an admissible differential is a holomorphic quadratic differential: `0` off the chart targets
by definition, the transformation law and holomorphy from the local form (with the chart at the image point). -/
theorem s32p_pullbackQD_isHolQuadDiff [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    {q : F.X.carrier → ℂ → ℂ} (hq : q ∈ admissibleQDSpace F) : IsHolQuadDiff (pullbackQD F q) := by
  have key : IsDiffFamily 2 0 (pullbackQD F q) ∧
      ∀ y : S, DifferentiableOn ℂ (pullbackQD F q y) (chartAt ℂ y).target := by
    refine ⟨⟨fun y w hw => indicator_of_notMem hw _, fun y y' w hw hwy => ?_⟩, fun y w hw => ?_⟩
    · rw [zpow_zero, mul_one, zpow_two]
      obtain ⟨hτt, -, hτeq⟩ := s23_transition_mem hw hwy
      have hsx : F.ι ((chartAt ℂ y).symm (chartTransition y y' w)) = F.ι ((chartAt ℂ y').symm w) := by
        rw [hτeq]
      have hsrc : F.ι ((chartAt ℂ y).symm (chartTransition y y' w)) ∈
          (chartAt ℂ (F.ι ((chartAt ℂ y').symm w))).source := by
        rw [hsx]
        exact mem_chart_source ℂ _
      rw [s32p_pullbackQD_local F hq y' (F.ι ((chartAt ℂ y').symm w)) hw (mem_chart_source ℂ _),
        s32p_pullbackQD_local F hq y (F.ι ((chartAt ℂ y').symm w)) hτt hsrc]
      have hτd := (s23_transition y y' hw hwy).1
      have hTd := s32p_T_differentiableAt F (F.ι ((chartAt ℂ y').symm w)) y hτt hsrc
      have hev : (fun v => chartAt ℂ (F.ι ((chartAt ℂ y').symm w)) (F.ι ((chartAt ℂ y').symm v))) =ᶠ[𝓝 w]
          (fun v => chartAt ℂ (F.ι ((chartAt ℂ y').symm w)) (F.ι ((chartAt ℂ y).symm v))) ∘
            chartTransition y y' := by
        filter_upwards [((chartAt ℂ y').isOpen_inter_preimage_symm (chartAt ℂ y).open_source).mem_nhds
          ⟨hw, hwy⟩] with v hv
        show chartAt ℂ (F.ι ((chartAt ℂ y').symm w)) (F.ι ((chartAt ℂ y').symm v)) =
          chartAt ℂ (F.ι ((chartAt ℂ y').symm w)) (F.ι ((chartAt ℂ y).symm (chartAt ℂ y ((chartAt ℂ y').symm v))))
        rw [(chartAt ℂ y).left_inv hv.2]
      have hder : deriv (fun v => chartAt ℂ (F.ι ((chartAt ℂ y').symm w)) (F.ι ((chartAt ℂ y').symm v))) w =
          deriv (fun v => chartAt ℂ (F.ι ((chartAt ℂ y').symm w)) (F.ι ((chartAt ℂ y).symm v)))
            (chartTransition y y' w) * deriv (chartTransition y y') w := by
        rw [hev.deriv_eq]
        exact (hTd.hasDerivAt.comp w hτd.hasDerivAt).deriv
      rw [hder, hsx]
      ring
    · set s := F.ι ((chartAt ℂ y).symm w)
      have hWo : IsOpen ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (F.ι ⁻¹' (chartAt ℂ s).source)) :=
        (chartAt ℂ y).isOpen_inter_preimage_symm
          (F.embedding.continuous.isOpen_preimage _ (chartAt ℂ s).open_source)
      have hwW : w ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (F.ι ⁻¹' (chartAt ℂ s).source) :=
        ⟨hw, mem_chart_source ℂ s⟩
      have hTd : DifferentiableOn ℂ (fun v => chartAt ℂ s (F.ι ((chartAt ℂ y).symm v)))
          ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (F.ι ⁻¹' (chartAt ℂ s).source)) :=
        fun v hv => (s32p_T_differentiableAt F s y hv.1 hv.2).differentiableWithinAt
      have hdd := hTd.deriv hWo
      -- `q s` is holomorphic near `φ_s(s)`: the open set `φ_s(U_s ∩ ι(S))` lies in the admissible set
      have hsι : (chartAt ℂ s).symm (chartAt ℂ s s) ∈ range F.ι := by
        rw [(chartAt ℂ s).left_inv (mem_chart_source ℂ s)]
        exact ⟨_, rfl⟩
      have hnhds : (chartAt ℂ s).target ∩ (chartAt ℂ s).symm ⁻¹' range F.ι ∈ 𝓝 (chartAt ℂ s s) :=
        ((chartAt ℂ s).isOpen_inter_preimage_symm F.embedding.isOpen_range).mem_nhds
          ⟨(chartAt ℂ s).map_source (mem_chart_source ℂ s), hsι⟩
      have h1 : DifferentiableAt ℂ (q s) (chartAt ℂ s (F.ι ((chartAt ℂ y).symm w))) :=
        ((hq.2.1 s) _ (mem_of_mem_nhds hnhds)).differentiableAt hnhds
      have hF : DifferentiableAt ℂ (fun v => q s (chartAt ℂ s (F.ι ((chartAt ℂ y).symm v))) *
          deriv (fun v => chartAt ℂ s (F.ι ((chartAt ℂ y).symm v))) v ^ 2) w :=
        (h1.comp w ((hTd w hwW).differentiableAt (hWo.mem_nhds hwW))).mul
          ((hdd.differentiableAt (hWo.mem_nhds hwW)).pow 2)
      have heq : pullbackQD F q y =ᶠ[𝓝 w] fun v => q s (chartAt ℂ s (F.ι ((chartAt ℂ y).symm v))) *
          deriv (fun v => chartAt ℂ s (F.ι ((chartAt ℂ y).symm v))) v ^ 2 :=
        Filter.eventuallyEq_of_mem (hWo.mem_nhds hwW) fun v hv => s32p_pullbackQD_local F hq y s hv.1 hv.2
      exact (hF.congr_of_eventuallyEq heq).differentiableWithinAt
  exact key

/-- A closed disc `IsClosedDiscIn` in a Hausdorff surface is closed: it is the image of the compact `closure J` under
the inverse chart. -/
theorem s32p_isClosed_disc {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X] {D : Set X}
    (hD : IsClosedDiscIn D) : IsClosed D := by
  obtain ⟨x, hDs, J, -, hJb, hJt, himg, -⟩ := hD
  have hDeq : D = (chartAt ℂ x).symm '' closure J := by
    ext y
    constructor
    · intro hy
      exact ⟨chartAt ℂ x y, himg ▸ mem_image_of_mem _ hy, (chartAt ℂ x).left_inv (hDs hy)⟩
    · rintro ⟨z, hz, rfl⟩
      rw [← himg] at hz
      obtain ⟨d, hd, rfl⟩ := hz
      rw [(chartAt ℂ x).left_inv (hDs hd)]
      exact hd
  rw [hDeq]
  exact (hJb.isCompact_closure.image_of_continuousOn ((chartAt ℂ x).continuousOn_symm.mono hJt)).isClosed

/-- An admissible differential whose pull-back vanishes is `0`: on `ι(S)` by the local form at the chart centres
(`T' ≠ 0`, `T = φ_{ι y} ∘ ι ∘ φ_y⁻¹` injective), at the punctures by the normalization `q_x(φ_x p) = 0`, inside the
holes because admissible differentials vanish there, and on the boundary curves by continuity from `ι(S)`. -/
theorem s32p_pullbackQD_eq_zero [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    {q : F.X.carrier → ℂ → ℂ} (hq : q ∈ admissibleQDSpace F) (h0 : pullbackQD F q = 0) : q = 0 := by
  have hlawq : IsDiffFamily 2 0 q := hq.1
  -- the value at the centre of the chart at a point of `ι(S)`
  have hcenter : ∀ y : S, q (F.ι y) (chartAt ℂ (F.ι y) (F.ι y)) = 0 := by
    intro y
    have hw : chartAt ℂ y y ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source (mem_chart_source ℂ y)
    have hsy : (chartAt ℂ y).symm (chartAt ℂ y y) = y := (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hval : pullbackQD F q y (chartAt ℂ y y) = 0 := by rw [h0]; rfl
    have hloc : pullbackQD F q y (chartAt ℂ y y) = q (F.ι y) (chartAt ℂ (F.ι y) (F.ι y)) *
        deriv (fun v => chartAt ℂ (F.ι y) (F.ι ((chartAt ℂ y).symm v))) (chartAt ℂ y y) ^ 2 := by
      show (chartAt ℂ y).target.indicator _ (chartAt ℂ y y) = _
      rw [indicator_of_mem hw]
      simp only [hsy]
    set W := (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (F.ι ⁻¹' (chartAt ℂ (F.ι y)).source)
    have hWo : IsOpen W := (chartAt ℂ y).isOpen_inter_preimage_symm
      (F.embedding.continuous.isOpen_preimage _ (chartAt ℂ (F.ι y)).open_source)
    have hwW : chartAt ℂ y y ∈ W := ⟨hw, by
      show F.ι ((chartAt ℂ y).symm (chartAt ℂ y y)) ∈ (chartAt ℂ (F.ι y)).source
      rw [hsy]
      exact mem_chart_source ℂ _⟩
    have hTd : DifferentiableOn ℂ (fun v => chartAt ℂ (F.ι y) (F.ι ((chartAt ℂ y).symm v))) W :=
      fun v hv => (s32p_T_differentiableAt F (F.ι y) y hv.1 hv.2).differentiableWithinAt
    have hinj : InjOn (fun v => chartAt ℂ (F.ι y) (F.ι ((chartAt ℂ y).symm v))) W := by
      intro v₁ hv₁ v₂ hv₂ h12
      have h1 := (chartAt ℂ (F.ι y)).injOn hv₁.2 hv₂.2 h12
      have h2 := F.embedding.injective h1
      rw [← (chartAt ℂ y).right_inv hv₁.1, ← (chartAt ℂ y).right_inv hv₂.1, h2]
    have hd := deriv_ne_zero_of_injOn hWo hTd hinj hwW
    rw [hloc] at hval
    exact (mul_eq_zero.1 hval).resolve_right (pow_ne_zero 2 hd)
  -- in any chart, at a point of `ι(S)`
  have hrange : ∀ (x : F.X.carrier) (z : ℂ), z ∈ (chartAt ℂ x).target →
      (chartAt ℂ x).symm z ∈ range F.ι → q x z = 0 := by
    rintro x z hz ⟨y, hy⟩
    have hsrc : (chartAt ℂ x).symm z ∈ (chartAt ℂ (F.ι y)).source := by
      rw [← hy]
      exact mem_chart_source ℂ _
    have hT : chartTransition (F.ι y) x z = chartAt ℂ (F.ι y) (F.ι y) := by
      show chartAt ℂ (F.ι y) ((chartAt ℂ x).symm z) = _
      rw [← hy]
    rw [hlawq.2 (F.ι y) x z hz hsrc, hT, hcenter y]
    simp
  funext x z
  show q x z = 0
  by_cases hz : z ∈ (chartAt ℂ x).target
  · set p := (chartAt ℂ x).symm z
    have hp : p ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
    have hpz : chartAt ℂ x p = z := (chartAt ℂ x).right_inv hz
    by_cases hι : p ∈ range F.ι
    · exact hrange x z hz hι
    by_cases hP : p ∈ (F.P : Finset F.X.carrier)
    · have h := (hq.2.2.1 x p hP hp).1
      rwa [hpz] at h
    -- `p` lies in a disc `D j`
    have hD : p ∈ ⋃ j, F.D j := by
      rw [F.range_ι] at hι
      simp only [mem_compl_iff, not_not, mem_union, Finset.mem_coe] at hι
      exact hι.resolve_left hP
    obtain ⟨j, hj⟩ := mem_iUnion.1 hD
    by_cases hint : p ∈ interior (F.D j)
    · exact hq.2.2.2.2.2 x j z hz hint
    -- `p` lies on the boundary curve of `D j`: continuity from `ι(S)`
    have hfr : p ∈ frontier (F.D j) := ⟨subset_closure hj, hint⟩
    have hC : IsClosed ((↑F.P : Set F.X.carrier) ∪ ⋃ i ∈ {i | i ≠ j}, F.D i) :=
      F.P.finite_toSet.isClosed.union
        ((Set.toFinite _).isClosed_biUnion fun i _ => s32p_isClosed_disc (F.disc i))
    have hpC : p ∉ (↑F.P : Set F.X.carrier) ∪ ⋃ i ∈ {i | i ≠ j}, F.D i := by
      rintro (h | h)
      · exact Set.disjoint_left.1 (F.disjoint_P j) hj h
      · obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.1 h
        exact Set.disjoint_left.1 (F.disjoint hi) hpi hj
    have hcl : p ∈ closure (range F.ι) := by
      rw [mem_closure_iff_nhds]
      intro t ht
      have ht' : t ∩ ((↑F.P : Set F.X.carrier) ∪ ⋃ i ∈ {i | i ≠ j}, F.D i)ᶜ ∈ 𝓝 p :=
        Filter.inter_mem ht (hC.isOpen_compl.mem_nhds hpC)
      have hfr' : p ∈ closure (F.D j)ᶜ := frontier_subset_closure (by rw [frontier_compl]; exact hfr)
      obtain ⟨y, ⟨hyt, hyC⟩, hyD⟩ := mem_closure_iff_nhds.1 hfr' _ ht'
      refine ⟨y, hyt, ?_⟩
      rw [F.range_ι]
      rintro (hyP | hyU)
      · exact hyC (Or.inl hyP)
      · obtain ⟨i, hi⟩ := mem_iUnion.1 hyU
        by_cases hij : i = j
        · exact hyD (hij ▸ hi)
        · exact hyC (Or.inr (mem_iUnion₂.2 ⟨i, hij, hi⟩))
    have hzA : z ∈ closure ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' range F.ι) := by
      have hp' : p ∈ closure ((chartAt ℂ x).source ∩ range F.ι) := by
        rw [mem_closure_iff_nhds] at hcl ⊢
        intro t ht
        obtain ⟨y, ⟨hyt, hys⟩, hyr⟩ :=
          hcl _ (Filter.inter_mem ht ((chartAt ℂ x).open_source.mem_nhds hp))
        exact ⟨y, hyt, hys, hyr⟩
      have himg := ((chartAt ℂ x).continuousAt hp).continuousWithinAt.mem_closure_image hp'
      rw [hpz] at himg
      refine closure_mono ?_ himg
      rintro _ ⟨y, ⟨hys, hyr⟩, rfl⟩
      refine ⟨(chartAt ℂ x).map_source hys, ?_⟩
      show (chartAt ℂ x).symm (chartAt ℂ x y) ∈ range F.ι
      rw [(chartAt ℂ x).left_inv hys]
      exact hyr
    have hcontq : ContinuousWithinAt (q x) ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' range F.ι) z :=
      ((hq.2.2.2.1 x j) z ⟨hz, Or.inr hfr⟩).mono
        (inter_subset_inter_right _ (preimage_mono subset_union_left))
    have hsub : q x '' ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' range F.ι) ⊆ {0} := by
      rintro _ ⟨w, ⟨hw, hwr⟩, rfl⟩
      exact hrange x w hw hwr
    have h0' := closure_mono hsub (hcontq.mem_closure_image hzA)
    rwa [closure_singleton, mem_singleton_iff] at h0'
  · exact hlawq.1 x z hz

/-- §32.1: the pull-back of an admissible differential is a holomorphic quadratic differential on the
interior, and `q ↦ q ∘ ι` is injective on `Q̃(S₀)`. -/
theorem admissibleQDInterior_holomorphic [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) :
    (∀ q ∈ admissibleQDInterior F, IsHolQuadDiff q) ∧
      InjOn (pullbackQDLinear F) (admissibleQDSpace F) := by
  refine ⟨fun q hq => ?_, fun q₁ hq₁ q₂ hq₂ h12 => ?_⟩
  · obtain ⟨q₀, hq₀, rfl⟩ := Submodule.mem_map.1 hq
    exact s32p_pullbackQD_isHolQuadDiff F hq₀
  · have hsub : q₁ - q₂ ∈ admissibleQDSpace F := (admissibleQDSpace F).sub_mem hq₁ hq₂
    have h0 : pullbackQD F (q₁ - q₂) = 0 := by
      have := map_sub (pullbackQDLinear F) q₁ q₂
      rw [h12, sub_self] at this
      exact this
    exact sub_eq_zero.1 (s32p_pullbackQD_eq_zero F hsub h0)

/-- §32.1: a Teichmüller map `f₀ : S₀ → S` between surfaces of finite type whose initial differential
is an admissible quadratic differential (its Beltrami differential is `k ω̄/|ω|`). -/
def IsAdmissibleTeichmullerMap {g n m : ℕ} (F : FiniteTypeStructure S₀ g n m) (f : S₀ ≃ₜ S)
    (q : S₀ → ℂ → ℂ) (q' : S → ℂ → ℂ) (k : ℝ) : Prop :=
  q ∈ admissibleQDInterior F ∧ IsTeichmullerMap f q q' k

/-! ## §32.1 Surfaces of type `(g, n)` -/

-- exists_branched_double_cover is stated and proved in LiZhongQC/Lemmas/SchottkyBranchedFinal.lean
-- (it needs the Hurwitz machinery downstream of this file).

/-- §32.1: the lift of an admissible differential to the branched double cover: if `ω = φ(z) dz²`
near a puncture (`z = 0`), then in the parameter `ζ = √z` of the point above it,
`ω̃ = 4ζ²φ(ζ²) dζ²`; a differential of order `n ≥ -1` at the puncture lifts to one of order
`2n + 2 ≥ 0`.  Hence the lift of an admissible differential is holomorphic.

Correction to the book's statement: the hypothesis `MeromorphicAt φ 0` is added.  It is implicit
in the book (`φ` is the coefficient of a meromorphic quadratic differential), and without it the
statement is false: Mathlib gives `meromorphicOrderAt` the junk value `0` at a point where the
function is not meromorphic, so a non-meromorphic `φ` satisfies the hypothesis with `N = 0`
while the left-hand side is `0`, not `2`. -/
theorem lift_admissibleQD_order {φ : ℂ → ℂ} {N : ℤ} (hφ0 : MeromorphicAt φ 0) (_hN : -1 ≤ N)
    (hφ : meromorphicOrderAt φ 0 = N) :
    meromorphicOrderAt (fun ζ => 4 * ζ ^ 2 * φ (ζ ^ 2)) 0 = 2 * N + 2 := by
  -- the squaring map `g : ζ ↦ ζ²` is analytic and vanishes to order `2` at `0`
  have hg : AnalyticAt ℂ (fun ζ : ℂ => ζ ^ 2) 0 := by fun_prop
  have hpow : (fun ζ : ℂ => ζ ^ 2) = (id : ℂ → ℂ) ^ 2 := by funext ζ; simp
  have hsq : analyticOrderAt (fun ζ : ℂ => ζ ^ 2) (0 : ℂ) = 2 := by
    rw [hpow, analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
    simp
  have hgo : analyticOrderAt (fun ζ : ℂ => ζ ^ 2 - (fun ζ : ℂ => ζ ^ 2) 0) (0 : ℂ) = 2 := by
    have hsub : (fun ζ : ℂ => ζ ^ 2 - (fun ζ : ℂ => ζ ^ 2) 0) = fun ζ : ℂ => ζ ^ 2 := by
      funext ζ; simp
    rw [hsub, hsq]
  -- hence `g` is not locally constant at `0`
  have hnc : ¬ EventuallyConst (fun ζ : ℂ => ζ ^ 2) (𝓝 (0 : ℂ)) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hgo]
    simp
  -- `φ` is meromorphic at `g 0 = 0`, and its order there is `N`
  have hφ0' : MeromorphicAt φ ((fun ζ : ℂ => ζ ^ 2) 0) := by simpa using hφ0
  have harg : meromorphicOrderAt φ ((fun ζ : ℂ => ζ ^ 2) 0) = (N : WithTop ℤ) := by
    simpa using hφ
  -- the order of `ζ ↦ φ(ζ²)` is `2N`
  have hcompm : MeromorphicAt (fun ζ : ℂ => φ (ζ ^ 2)) 0 :=
    MeromorphicAt.comp_analyticAt (f := φ) (g := fun ζ : ℂ => ζ ^ 2) (x := (0 : ℂ)) hφ0' hg
  have hco : meromorphicOrderAt (fun ζ : ℂ => φ (ζ ^ 2)) 0 = 2 * (N : WithTop ℤ) := by
    have h := MeromorphicAt.meromorphicOrderAt_comp (f := φ) (g := fun ζ : ℂ => ζ ^ 2)
      (x := (0 : ℂ)) hφ0' hg hnc
    rw [hgo, harg] at h
    show meromorphicOrderAt (φ ∘ fun ζ : ℂ => ζ ^ 2) 0 = 2 * (N : WithTop ℤ)
    rw [h]
    simp [mul_comm]
  -- the order of `ζ ↦ 4ζ²` is `2`
  have h4a : AnalyticAt ℂ (fun ζ : ℂ => 4 * ζ ^ 2) 0 := by fun_prop
  have h4o : analyticOrderAt (fun ζ : ℂ => 4 * ζ ^ 2) (0 : ℂ) = 2 := by
    rw [show (fun ζ : ℂ => 4 * ζ ^ 2) = (fun _ : ℂ => (4 : ℂ)) * fun ζ : ℂ => ζ ^ 2 from rfl,
      analyticOrderAt_mul analyticAt_const hg,
      (analyticAt_const (v := (4 : ℂ))).analyticOrderAt_eq_zero.mpr (by norm_num), zero_add, hsq]
  have h4 : meromorphicOrderAt (fun ζ : ℂ => 4 * ζ ^ 2) 0 = 2 := by
    rw [h4a.meromorphicOrderAt_eq, h4o]
    simp
  -- the order of a product is the sum of the orders
  rw [show (fun ζ : ℂ => 4 * ζ ^ 2 * φ (ζ ^ 2))
        = (fun ζ : ℂ => 4 * ζ ^ 2) * fun ζ : ℂ => φ (ζ ^ 2) from rfl,
    meromorphicOrderAt_mul h4a.meromorphicAt hcompm, h4, hco, add_comm]

variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

-- lift_teichmullerMap_double_cover is stated and proved in LiZhongQC/Lemmas/BranchedLiftBook.lean
-- (it needs the branched covers and the Teichmüller lifting machinery downstream of this file).

-- thm32_1_uniqueness_gn is stated and proved in LiZhongQC/Lemmas/Thm321.lean
-- (it needs the branched double covers downstream of this file).

/-- The lift formula of `lift_admissibleQD_order` without the side condition `-1 ≤ N`, which its
proof never uses: for `φ` meromorphic at `0` of order `N ∈ ℤ`, `4ζ²φ(ζ²)` has order `2N + 2`. -/
theorem meromorphicOrderAt_lift_sq {φ : ℂ → ℂ} {N : ℤ} (hφ0 : MeromorphicAt φ 0)
    (hφ : meromorphicOrderAt φ 0 = N) :
    meromorphicOrderAt (fun ζ => 4 * ζ ^ 2 * φ (ζ ^ 2)) 0 = 2 * N + 2 := by
  -- the squaring map `g : ζ ↦ ζ²` is analytic and vanishes to order `2` at `0`
  have hg : AnalyticAt ℂ (fun ζ : ℂ => ζ ^ 2) 0 := by fun_prop
  have hpow : (fun ζ : ℂ => ζ ^ 2) = (id : ℂ → ℂ) ^ 2 := by funext ζ; simp
  have hsq : analyticOrderAt (fun ζ : ℂ => ζ ^ 2) (0 : ℂ) = 2 := by
    rw [hpow, analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
    simp
  have hgo : analyticOrderAt (fun ζ : ℂ => ζ ^ 2 - (fun ζ : ℂ => ζ ^ 2) 0) (0 : ℂ) = 2 := by
    have hsub : (fun ζ : ℂ => ζ ^ 2 - (fun ζ : ℂ => ζ ^ 2) 0) = fun ζ : ℂ => ζ ^ 2 := by
      funext ζ; simp
    rw [hsub, hsq]
  -- hence `g` is not locally constant at `0`
  have hnc : ¬ EventuallyConst (fun ζ : ℂ => ζ ^ 2) (𝓝 (0 : ℂ)) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hgo]
    simp
  -- `φ` is meromorphic at `g 0 = 0`, and its order there is `N`
  have hφ0' : MeromorphicAt φ ((fun ζ : ℂ => ζ ^ 2) 0) := by simpa using hφ0
  have harg : meromorphicOrderAt φ ((fun ζ : ℂ => ζ ^ 2) 0) = (N : WithTop ℤ) := by
    simpa using hφ
  -- the order of `ζ ↦ φ(ζ²)` is `2N`
  have hcompm : MeromorphicAt (fun ζ : ℂ => φ (ζ ^ 2)) 0 :=
    MeromorphicAt.comp_analyticAt (f := φ) (g := fun ζ : ℂ => ζ ^ 2) (x := (0 : ℂ)) hφ0' hg
  have hco : meromorphicOrderAt (fun ζ : ℂ => φ (ζ ^ 2)) 0 = 2 * (N : WithTop ℤ) := by
    have h := MeromorphicAt.meromorphicOrderAt_comp (f := φ) (g := fun ζ : ℂ => ζ ^ 2)
      (x := (0 : ℂ)) hφ0' hg hnc
    rw [hgo, harg] at h
    show meromorphicOrderAt (φ ∘ fun ζ : ℂ => ζ ^ 2) 0 = 2 * (N : WithTop ℤ)
    rw [h]
    simp [mul_comm]
  -- the order of `ζ ↦ 4ζ²` is `2`
  have h4a : AnalyticAt ℂ (fun ζ : ℂ => 4 * ζ ^ 2) 0 := by fun_prop
  have h4o : analyticOrderAt (fun ζ : ℂ => 4 * ζ ^ 2) (0 : ℂ) = 2 := by
    rw [show (fun ζ : ℂ => 4 * ζ ^ 2) = (fun _ : ℂ => (4 : ℂ)) * fun ζ : ℂ => ζ ^ 2 from rfl,
      analyticOrderAt_mul analyticAt_const hg,
      (analyticAt_const (v := (4 : ℂ))).analyticOrderAt_eq_zero.mpr (by norm_num), zero_add, hsq]
  have h4 : meromorphicOrderAt (fun ζ : ℂ => 4 * ζ ^ 2) 0 = 2 := by
    rw [h4a.meromorphicOrderAt_eq, h4o]
    simp
  -- the order of a product is the sum of the orders
  rw [show (fun ζ : ℂ => 4 * ζ ^ 2 * φ (ζ ^ 2))
        = (fun ζ : ℂ => 4 * ζ ^ 2) * fun ζ : ℂ => φ (ζ ^ 2) from rfl,
    meromorphicOrderAt_mul h4a.meromorphicAt hcompm, h4, hco, add_comm]

/-- §32.1: the projection of the lifted differential: if `ω̃` is regular at the point above a
puncture, `ω` has a simple pole there; if `ω̃` has a zero there, `ω` is regular (a differential of
order `2(n+1)` above projects to one of order `n`). -/
theorem project_admissibleQD_order {φ : ℂ → ℂ} {N : ℤ} (hN : 0 ≤ N)
    (hφ : meromorphicOrderAt (fun ζ => 4 * ζ ^ 2 * φ (ζ ^ 2)) 0 = 2 * N + 2) : meromorphicOrderAt φ 0 = N := by
  -- `ψ = 4ζ²φ(ζ²)` is meromorphic at `0`, since its order is not the junk value `0`
  have hcast : ∀ k : ℤ, ((2 * k + 2 : ℤ) : WithTop ℤ) = 2 * (k : WithTop ℤ) + 2 := fun k => by
    norm_cast
  have hψ : MeromorphicAt (fun ζ => 4 * ζ ^ 2 * φ (ζ ^ 2)) 0 := by
    apply meromorphicAt_of_meromorphicOrderAt_ne_zero
    rw [hφ, ← hcast N]
    have h : (2 * N + 2 : ℤ) ≠ 0 := by omega
    exact fun h' => h (WithTop.coe_eq_coe.1 (h'.trans WithTop.coe_zero.symm))
  -- hence `φ` is meromorphic at `0`
  have hφ0 : MeromorphicAt φ 0 := by
    obtain ⟨m, hm⟩ := hψ
    refine ⟨m + 2, ?_⟩
    have hG : AnalyticAt ℂ (fun ζ => ζ ^ (2 * (m + 2)) * φ (ζ ^ 2)) 0 := by
      have h1 : AnalyticAt ℂ
          (fun ζ : ℂ => 1 / 4 * ζ ^ (m + 2) * ((ζ - 0) ^ m • (4 * ζ ^ 2 * φ (ζ ^ 2)))) 0 :=
        (analyticAt_const.mul (analyticAt_id.pow (m + 2))).mul hm
      refine h1.congr (Eventually.of_forall fun ζ => ?_)
      simp only [sub_zero, smul_eq_mul]
      ring
    have := analyticAt_of_analyticAt_pow_mul_comp_sq hG
    simpa using this
  -- the order of `φ` at `0`
  cases h : meromorphicOrderAt φ 0 using WithTop.recTopCoe with
  | top =>
    -- order `⊤`: `φ` vanishes near `0`, hence so does `ψ`, contradicting `ord ψ = 2N + 2`
    exfalso
    rw [meromorphicOrderAt_eq_top_iff] at h
    have hψtop : meromorphicOrderAt (fun ζ => 4 * ζ ^ 2 * φ (ζ ^ 2)) 0 = ⊤ := by
      rw [meromorphicOrderAt_eq_top_iff]
      have hsq : Tendsto (fun ζ : ℂ => ζ ^ 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have : Tendsto (fun ζ : ℂ => ζ ^ 2) (𝓝 0) (𝓝 ((0 : ℂ) ^ 2)) :=
            (continuous_pow 2).tendsto 0
          rw [zero_pow two_ne_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        · exact eventually_nhdsWithin_of_forall fun ζ hζ => pow_ne_zero 2 hζ
      exact (hsq.eventually h).mono fun ζ hζ => by simp [hζ]
    rw [hφ, ← hcast N] at hψtop
    exact WithTop.coe_ne_top hψtop
  | coe m =>
    have hlift := meromorphicOrderAt_lift_sq hφ0 h
    rw [hφ, ← hcast N, ← hcast m] at hlift
    have h2 : (2 * N + 2 : ℤ) = 2 * m + 2 := WithTop.coe_eq_coe.1 hlift
    have h3 : m = N := by omega
    rw [h3]

-- thm32_2_existence_gn is stated and proved in LiZhongQC/Lemmas/SchottkyDirectFinal.lean
-- (it needs the branched double covers and Theorem 32.1 downstream of this file).

/-! ## §32.2 Surfaces of type `(g, n, m)`, `m ≠ 0` -/

/-- §32.2: the symmetric extension of a map `f : S₀ → S` to the Schottky doubles:
`f^d ∘ ιd₀ = ιd₁ ∘ f` and `f^d ∘ J₀ = J₁ ∘ f^d`. -/
def IsSymmetricExtension {Xd₀ Xd₁ : ClosedRS.{u}} (J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier) (J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier)
    (ιd₀ : S₀ → Xd₀.carrier) (ιd₁ : S → Xd₁.carrier) (f : S₀ → S) (fd : Xd₀.carrier ≃ₜ Xd₁.carrier) : Prop :=
  (∀ x, fd (ιd₀ x) = ιd₁ (f x)) ∧ ∀ y, fd (J₀ y) = J₁ (fd y)

-- symmetric_extension_properties is stated and proved in LiZhongQC/Lemmas/S32wSymmExtProperties.lean
-- (it needs the Schottky double machinery downstream of this file).

-- thm32_3_uniqueness_gnm is stated and proved in LiZhongQC/Lemmas/S32wThm323.lean
-- (it needs Theorem 32.1 and the symmetric extension downstream of this file).

-- eq32_3_teichmuller_commutes_reflection is stated and proved in LiZhongQC/Lemmas/TeichmullerCommutesReflection.lean
-- (it needs Theorem 32.1 and the Schottky double machinery downstream of this file).

-- thm32_4_existence_gnm is stated and proved in LiZhongQC/Lemmas/S32wThm324.lean
-- (it needs Theorems 32.2, 32.3 and the symmetric extension downstream of this file).

/-! ## §32.3 The Teichmüller space of a surface of finite type -/

/-- A Riemann surface of finite type `(g, n, m)`, bundled. -/
structure FiniteTypeRS (g n m : ℕ) : Type (u + 1) where
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  [t2Space : T2Space carrier]
  [connectedSpace : ConnectedSpace carrier]
  [chartedSpace : ChartedSpace ℂ carrier]
  [isManifold : IsManifold 𝓘(ℂ) ω carrier]
  structure' : FiniteTypeStructure carrier g n m

attribute [instance] FiniteTypeRS.topologicalSpace FiniteTypeRS.t2Space FiniteTypeRS.connectedSpace
  FiniteTypeRS.chartedSpace FiniteTypeRS.isManifold

/-- **§32.3 (标记曲面).**  A surface `X` of type `(g, n, m)` marked by a quasiconformal
homeomorphism `f : S₀ → X`. -/
structure MarkedFiniteTypeRS (S₀ : Type u) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] (g n m : ℕ) where
  X : FiniteTypeRS.{u} g n m
  marking : S₀ ≃ₜ X.carrier
  qc : IsQCRS marking

/-- §32.3: `(S₁, f₁) ~ (S₂, f₂)` iff there is a conformal `φ : S₁ → S₂` homotopic to `f₂ ∘ f₁⁻¹`. -/
def MarkedFiniteTypeRS.Equiv {g n m : ℕ} (m₁ m₂ : MarkedFiniteTypeRS S₀ g n m) : Prop :=
  ∃ c : m₁.X.carrier ≃ₜ m₂.X.carrier, IsBiholomorphic c ∧
    ContinuousMap.Homotopic ((m₁.marking.trans c : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier))
      (m₂.marking : C(S₀, m₂.X.carrier))

/-- **§32.3**: the Teichmüller space `T(S₀) = T_{g,n,m}` of a surface of finite type. -/
def TeichSpaceFiniteType (S₀ : Type u) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] (g n m : ℕ) : Type (u + 1) :=
  Quot (MarkedFiniteTypeRS.Equiv (S₀ := S₀) (g := g) (n := n) (m := m))

-- markedFiniteType_teichmuller_data is stated and proved in LiZhongQC/Lemmas/FiniteTypeTeichSpace.lean
-- (it needs the existence and uniqueness theorems 32.1 and 32.4 downstream of this file).

-- teichSpaceFiniteType_ball is stated and proved in LiZhongQC/Lemmas/FiniteTypeTeichSpace.lean
-- (it needs the existence and uniqueness theorems 32.1 and 32.4 downstream of this file).

/-- §32.3: the Teichmüller distance `d_T(τ₁, τ₂) = ½ ln K[f₀]`, `f₀` the extremal map in the class of
`f₂ ∘ f₁⁻¹`.

Written as the `sInf` of a set of reals.  The nested form `⨅ m₁ m₂ g (_ : …), …` is identically `0` in `ℝ`:
for a triple outside the classes the innermost infimum is over an empty proposition, `sInf ∅ = 0`, and all values
are `≥ 0` (corrected 2026-09-25, as for `UniversalTeichmuller.dist`). -/
def teichDistanceFT {g n m : ℕ} (p q : TeichSpaceFiniteType S₀ g n m) : ℝ :=
  sInf {d | ∃ (m₁ : MarkedFiniteTypeRS S₀ g n m) (m₂ : MarkedFiniteTypeRS S₀ g n m) (h : m₁.X.carrier ≃ₜ m₂.X.carrier),
    Quot.mk _ m₁ = p ∧ Quot.mk _ m₂ = q ∧ IsQCRS h ∧
      ContinuousMap.Homotopic ((m₁.marking.trans h : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier))
        (m₂.marking : C(S₀, m₂.X.carrier)) ∧
    d = (1 / 2) * Real.log (maxDilatationRS h).toReal}

-- teichDistanceFT_complete_metric is stated and proved in LiZhongQC/Lemmas/FiniteTypeTeichMetric.lean
-- (it needs the Teichmüller data of §32.3 downstream of this file).

/-- §32.3: the modular group `Mod_{g,n,m}` (quasiconformal self-maps `σ` of `S₀` acting by
`[S, f] ↦ [S, f ∘ σ]`), and `R_{g,n,m} = T_{g,n,m}/Mod_{g,n,m}`: two marked surfaces have conformally
equivalent underlying surfaces iff they are related by a modular transformation. -/
theorem moduliFiniteType_eq_quotient {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (m₁ m₂ : MarkedFiniteTypeRS S₀ g n m) :
    RSConformallyEquivalent m₁.X.carrier m₂.X.carrier ↔
      ∃ (σ : S₀ ≃ₜ S₀) (hσ : IsQCRS (σ.trans m₂.marking)),
        MarkedFiniteTypeRS.Equiv ⟨m₂.X, σ.trans m₂.marking, hσ⟩ m₁ := by
  have _ := hex
  have _ := F₀
  have _ : T2Space S₀ := inferInstance
  have _ : ConnectedSpace S₀ := inferInstance
  constructor
  · rintro ⟨φ, hφ⟩
    obtain ⟨e, heb, _he⟩ := s28q_exists_homeomorph_of_isBiholomorphic hφ
    set σ : S₀ ≃ₜ S₀ := (m₁.marking.trans e).trans m₂.marking.symm
    have hσeq : σ.trans m₂.marking = m₁.marking.trans e := by
      ext x
      simp [σ]
    obtain ⟨K, hK⟩ := m₁.qc
    have he1 : IsKQCRS e 1 := (isKQCRS_one_iff e).2 heb
    have hσ : IsQCRS (σ.trans m₂.marking) := by
      rw [hσeq]
      exact ⟨_, (eq23_4 hK he1).1⟩
    refine ⟨σ, hσ, e.symm, IsBiholomorphic.homeomorph_symm heb, ?_⟩
    have hc : ((((σ.trans m₂.marking).trans e.symm : S₀ ≃ₜ m₁.X.carrier)) : C(S₀, m₁.X.carrier)) =
        (m₁.marking : C(S₀, m₁.X.carrier)) := by
      ext x
      simp [σ]
    exact hc ▸ ContinuousMap.Homotopic.refl _
  · rintro ⟨σ, hσ, c, hc, _hhom⟩
    have _ := hσ
    exact ⟨_, IsBiholomorphic.homeomorph_symm hc⟩

/-- §32.3 (remark): for `m ≠ 0` the dimension `6g - 6 + 2n + 3m` of `T_{g,n,m}` can be odd, so
`T_{g,n,m}` cannot be a complex manifold in general (e.g. type `(0, 0, 3)` has dimension `3`). -/
theorem teichSpaceFiniteType_odd_dimension : Odd (6 * 0 - 6 + 2 * 0 + 3 * 3 : ℤ) := by
  decide

end LiZhongQC
