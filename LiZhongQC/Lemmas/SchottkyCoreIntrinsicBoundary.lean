import LiZhongQC.Lemmas.SchottkyCoreC0Atlas
import LiZhongQC.Lemmas.SchottkyCoreBoundaryComponents
import LiZhongExternal.Classification.SchottkyClassification01
import LiZhongExternal.Classification.SchottkyClassification09

open Set Metric Topology Complex
open scoped Manifold ContDiff
noncomputable section
namespace LiZhongQC
universe u

/-- The explicit open embedding of the plane into the closed upper half-plane has image in the
open upper half-plane. -/
theorem s31ib_plane_openEmbedding_upper_pos :
    ∃ f : ℂ → {z : ℂ | 0 ≤ z.im}, Topology.IsOpenEmbedding f ∧ ∀ z, 0 < (f z).val.im := by
  let e : ℂ ≃ₜ {z : ℂ | 0 < z.im} := {
    toFun := fun z => ⟨⟨z.re, Real.exp z.im⟩, Real.exp_pos z.im⟩
    invFun := fun z => ⟨z.val.re, Real.log z.val.im⟩
    left_inv := by
      intro z
      apply Complex.ext
      · rfl
      · exact Real.log_exp z.im
    right_inv := by
      intro z
      apply Subtype.ext
      apply Complex.ext
      · rfl
      · exact Real.exp_log z.property
    continuous_toFun :=
      (Complex.equivRealProdCLM.symm.continuous.comp
        (continuous_re.prodMk (Real.continuous_exp.comp continuous_im))).subtype_mk _
    continuous_invFun :=
      Complex.equivRealProdCLM.symm.continuous.comp
        ((continuous_re.comp continuous_subtype_val).prodMk
          ((continuous_im.comp continuous_subtype_val).log
            (fun z => ne_of_gt z.property))) }
  have hle : ∀ z : {z : ℂ | 0 < z.im}, z.val ∈ {z : ℂ | 0 ≤ z.im} := fun z =>
    le_of_lt (show (0 : ℝ) < z.val.im from z.property)
  let k : {z : ℂ | 0 < z.im} → {z : ℂ | 0 ≤ z.im} :=
    fun z => ⟨z.val, hle z⟩
  have hpos : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im
  have hk : Topology.IsOpenEmbedding k :=
    Topology.IsOpenEmbedding.of_isEmbedding_isOpenMap
      (hpos.isOpenEmbedding_subtypeVal.isEmbedding.codRestrict _ hle)
      (hpos.isOpenEmbedding_subtypeVal.isOpenMap.subtype_mk hle)
  exact ⟨k ∘ e, hk.comp e.isOpenEmbedding, fun z => (e z).property⟩

/-- A local open embedding gives a chart whose value at the base point is the embedding's value. -/
theorem s31ib_chart_from_local_openEmbedding {X H : Type*}
    [TopologicalSpace X] [TopologicalSpace H] [Nonempty H]
    (U : Set X) (hU : IsOpen U) (p : X) (hp : p ∈ U)
    (f : U → H) (hf : Topology.IsOpenEmbedding f) :
    ∃ e : OpenPartialHomeomorph X H, p ∈ e.source ∧ e p = f ⟨p, hp⟩ := by
  letI : Nonempty U := ⟨⟨p, hp⟩⟩
  refine ⟨(hf.toOpenPartialHomeomorph f).lift_openEmbedding hU.isOpenEmbedding_subtypeVal,
    ?_, ?_⟩
  · change p ∈ ((hf.toOpenPartialHomeomorph f).lift_openEmbedding
      hU.isOpenEmbedding_subtypeVal).source
    rw [OpenPartialHomeomorph.lift_openEmbedding_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source]
    exact ⟨⟨p, hp⟩, mem_univ _, rfl⟩
  · exact (OpenPartialHomeomorph.lift_openEmbedding_apply (hf.toOpenPartialHomeomorph f)
      hU.isOpenEmbedding_subtypeVal (x := ⟨p, hp⟩)).trans
      (congr_fun (hf.toOpenPartialHomeomorph_apply f) _)

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
  {g n m : ℕ} (F : FiniteTypeStructure S g n m)

/-- Boundary points of the core get a half-space chart sending them to coordinate zero. -/
theorem s31ib_core_boundary_chart (p : s31dt_Core F) (hp : p ∈ s31dt_boundary F) :
    ∃ e : OpenPartialHomeomorph (s31dt_Core F) (EuclideanHalfSpace 2),
      p ∈ e.source ∧ (e p).val 0 = 0 := by
  have hpB : p ∈ s31dt_boundary F := hp
  obtain ⟨j, hpj⟩ := hp
  obtain ⟨x, J, N, f, e, hJ, hb, hN, hDN, hNs, hNP, hND,
      hf, hfi, hef, hei, heb, hfamily⟩ := s78ra_actual_boundary_chart_family F j
  obtain ⟨r, U, a, K, u, hr, hU, hpU, hrest⟩ := hfamily p hpj
  obtain ⟨-, -, -, -, -, -, hKb, -⟩ := hrest
  obtain ⟨L, hL⟩ := s31dt_upper_halfspace_homeomorph
  let k : U → EuclideanHalfSpace 2 :=
    fun y => L ⟨(K y).val, (K y).property.2⟩
  have hk : Topology.IsOpenEmbedding k :=
    L.isOpenEmbedding.comp ((s31dt_halfdisc_openEmbedding_upper r).comp K.isOpenEmbedding)
  obtain ⟨e', hs, hv⟩ := s31ib_chart_from_local_openEmbedding U hU p hpU k hk
  refine ⟨e', hs, ?_⟩
  rw [hv]
  exact (hL _).trans ((hKb ⟨p, hpU⟩).mp hpB)

/-- Non-boundary points of the core get a half-space chart sending them to positive coordinate. -/
theorem s31ib_core_interior_chart (p : s31dt_Core F) (hp : p ∉ s31dt_boundary F) :
    ∃ e : OpenPartialHomeomorph (s31dt_Core F) (EuclideanHalfSpace 2),
      p ∈ e.source ∧ 0 < (e p).val 0 := by
  let c := chartAt ℂ p.val
  let V : Set F.X.carrier := c.source ∩ (⋃ j, F.D j)ᶜ
  have hV : IsOpen V := c.open_source.inter
    (isClosed_iUnion_of_finite (fun j => (s31eg_disc_compact (F.disc j)).isClosed)).isOpen_compl
  have hpV : p.val ∈ V := by
    refine ⟨mem_chart_source ℂ p.val, ?_⟩
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    apply hp
    refine ⟨j, (mem_frontier_iff_notMem_interior hj).mpr ?_⟩
    intro hi
    exact p.property (mem_iUnion.mpr ⟨j, hi⟩)
  have hVC : V ⊆ s31dt_coreSet F := by
    intro x hx hi
    obtain ⟨j, hj⟩ := mem_iUnion.mp hi
    exact hx.2 (mem_iUnion.mpr ⟨j, interior_subset hj⟩)
  let U : Set (s31dt_Core F) := Subtype.val ⁻¹' V
  have hU : IsOpen U := hV.preimage continuous_subtype_val
  let E : U ≃ₜ V := {
    toFun := fun q => ⟨q.val.val, q.property⟩
    invFun := fun q => ⟨⟨q.val, hVC q.property⟩, q.property⟩
    left_inv := by intro q; rfl
    right_inv := by intro q; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hv : Topology.IsOpenEmbedding (fun q : U => q.val.val) :=
    hV.isOpenEmbedding_subtypeVal.comp E.isOpenEmbedding
  let k : U → c.source := fun q => ⟨q.val.val, q.property.1⟩
  have hk : Topology.IsOpenEmbedding k :=
    Topology.IsOpenEmbedding.of_isEmbedding_isOpenMap
      (hv.isEmbedding.codRestrict c.source (fun q => q.property.1))
      (hv.isOpenMap.subtype_mk (fun q => q.property.1))
  have hchart : Topology.IsOpenEmbedding (fun q : U => c q.val.val) :=
    c.isOpenEmbedding_restrict.comp hk
  obtain ⟨a, ha, hapos⟩ := s31ib_plane_openEmbedding_upper_pos
  obtain ⟨L, hL⟩ := s31dt_upper_halfspace_homeomorph
  obtain ⟨e', hs, hv'⟩ := s31ib_chart_from_local_openEmbedding U hU p hpV
    (fun q => L (a (c q.val.val))) (L.isOpenEmbedding.comp (ha.comp hchart))
  refine ⟨e', hs, ?_⟩
  rw [hv']
  show 0 < (L (a (c p.val))).val 0
  rw [hL]
  exact hapos _

/-- The core carries a `C⁰` half-space atlas whose intrinsic manifold boundary is exactly the
actual boundary `s31dt_boundary F`, with exactly `m` connected components (Brouwer's fixed-point principle for the plane is the instance
proved in `Moise.Brouwer`, imported through `SchottkyClassification09`). -/
theorem s31dt_core_intrinsic_boundary :
    ∃ c : ChartedSpace (EuclideanHalfSpace 2) (s31dt_Core F),
      letI := c
      IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 (s31dt_Core F) ∧
      (modelWithCornersEuclideanHalfSpace 2).boundary (s31dt_Core F) = s31dt_boundary F ∧
      Nonempty (ConnectedComponents
        ↥((modelWithCornersEuclideanHalfSpace 2).boundary (s31dt_Core F)) ≃ Fin m) ∧
      Nat.card (ConnectedComponents
        ↥((modelWithCornersEuclideanHalfSpace 2).boundary (s31dt_Core F))) = m := by
  classical
  have hlocal : ∀ p : s31dt_Core F,
      ∃ e : OpenPartialHomeomorph (s31dt_Core F) (EuclideanHalfSpace 2), p ∈ e.source ∧
        ((p ∈ s31dt_boundary F → (e p).val 0 = 0) ∧
          (p ∉ s31dt_boundary F → 0 < (e p).val 0)) := by
    intro p
    by_cases hp : p ∈ s31dt_boundary F
    · obtain ⟨e, h1, h2⟩ := s31ib_core_boundary_chart F p hp
      exact ⟨e, h1, fun _ => h2, fun h => absurd hp h⟩
    · obtain ⟨e, h1, h2⟩ := s31ib_core_interior_chart F p hp
      exact ⟨e, h1, fun h => absurd h hp, fun _ => h2⟩
  choose e hes hev using hlocal
  let c : ChartedSpace (EuclideanHalfSpace 2) (s31dt_Core F) := {
    atlas := range e
    chartAt := e
    mem_chart_source := hes
    chart_mem_atlas := fun p => mem_range_self p }
  refine ⟨c, ?_⟩
  letI := c
  have hman : IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 (s31dt_Core F) :=
    inferInstance
  have hbd : (modelWithCornersEuclideanHalfSpace 2).boundary (s31dt_Core F) =
      s31dt_boundary F := by
    ext x
    have hiff := LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isBoundaryPoint_iff_any_chart
      (modelWithCornersEuclideanHalfSpace 2) (x := x) (f := e x) (hes x)
    show (modelWithCornersEuclideanHalfSpace 2).IsBoundaryPoint x ↔ x ∈ s31dt_boundary F
    rw [hiff]
    show ((e x) x).val ∈ frontier (range (modelWithCornersEuclideanHalfSpace 2)) ↔ _
    rw [frontier_range_modelWithCornersEuclideanHalfSpace]
    show 0 = ((e x) x).val 0 ↔ _
    constructor
    · intro h
      by_contra hx
      have := (hev x).2 hx
      linarith
    · intro hx
      exact ((hev x).1 hx).symm
  obtain ⟨ee, -⟩ := s31dt_boundary_components_equiv F
  refine ⟨hman, hbd, ?_, ?_⟩
  · rw [hbd]
    exact ⟨ee⟩
  · rw [hbd]
    exact s31dt_boundary_component_card F

end LiZhongQC
