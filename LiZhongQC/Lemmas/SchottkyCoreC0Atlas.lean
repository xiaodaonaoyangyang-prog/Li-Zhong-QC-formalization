import LiZhongQC.Lemmas.SchottkyActualBoundaryCharts
import LiZhongQC.Lemmas.SchottkyDoubleConnected
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Set Metric Topology Complex
open scoped Manifold ContDiff
noncomputable section
namespace LiZhongQC
universe u

/-- The explicit real two-dimensional coordinate sends imaginary part to
coordinate zero, the coordinate constrained by EuclideanHalfSpace. -/
theorem s31dt_upper_halfspace_homeomorph :
    ∃ e : {z : ℂ | 0 ≤ z.im} ≃ₜ EuclideanHalfSpace 2,
      ∀ z, (e z).val 0 = z.val.im := by
  let L : ℂ ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    Complex.equivRealProdCLM.toHomeomorph.trans
      ((Homeomorph.prodComm ℝ ℝ).trans
        ((Homeomorph.finTwoArrow : (Fin 2 → ℝ) ≃ₜ ℝ × ℝ).symm.trans
          (EuclideanSpace.equiv (Fin 2) ℝ).symm.toHomeomorph))
  have hL : ∀ z, (L z) 0 = z.im := fun _ => rfl
  let e : {z : ℂ | 0 ≤ z.im} ≃ₜ EuclideanHalfSpace 2 :=
    L.subtype (fun z => show 0 ≤ z.im ↔ 0 ≤ (L z) 0 from by rw [hL])
  exact ⟨e, fun _ => rfl⟩

/-- An explicit open embedding of the whole complex plane into the closed
upper half-plane, with image its interior. Used only for interior C0 charts. -/
theorem s31dt_plane_openEmbedding_upper :
    ∃ f : ℂ → {z : ℂ | 0 ≤ z.im}, Topology.IsOpenEmbedding f := by
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
  exact ⟨k ∘ e, hk.comp e.isOpenEmbedding⟩

/-- A relative open half-disc embeds openly into the model half-plane. -/
theorem s31dt_halfdisc_openEmbedding_upper (r : ℝ) :
    Topology.IsOpenEmbedding
      (fun z : {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} =>
        (⟨z.val, z.property.2⟩ : {z : ℂ | 0 ≤ z.im})) := by
  let V : Set {z : ℂ | 0 ≤ z.im} := {z | ‖z.val‖ < r}
  have hV : IsOpen V :=
    isOpen_lt continuous_subtype_val.norm continuous_const
  let e : {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} ≃ₜ V := {
    toFun := fun z => ⟨⟨z.val, z.property.2⟩, z.property.1⟩
    invFun := fun z => ⟨z.val.val, ⟨z.property, z.val.property⟩⟩
    left_inv := by intro z; rfl
    right_inv := by intro z; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  exact hV.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding

/-- Turn a local open embedding into an actual chart without changing the
topology of its ambient space. The target is the actual open image. -/
theorem s31dt_chart_from_local_openEmbedding {X H : Type*}
    [TopologicalSpace X] [TopologicalSpace H] [Nonempty H]
    (U : Set X) (hU : IsOpen U) (p : X) (hp : p ∈ U)
    (f : U → H) (hf : Topology.IsOpenEmbedding f) :
    ∃ e : OpenPartialHomeomorph X H, p ∈ e.source := by
  letI : Nonempty U := ⟨⟨p, hp⟩⟩
  let e := (hf.toOpenPartialHomeomorph f).lift_openEmbedding hU.isOpenEmbedding_subtypeVal
  refine ⟨e, ?_⟩
  change p ∈ ((hf.toOpenPartialHomeomorph f).lift_openEmbedding
    hU.isOpenEmbedding_subtypeVal).source
  rw [OpenPartialHomeomorph.lift_openEmbedding_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source]
  exact ⟨⟨p, hp⟩, mem_univ _, rfl⟩

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
  {g n m : ℕ} (F : FiniteTypeStructure S g n m)

/-- Boundary points use the actual core half-disc K from the independently
constructed boundary-chart producer. The sewn double chart is not needed. -/
theorem s31dt_core_boundary_halfspace_chart (p : s31dt_Core F)
    (hp : p ∈ s31dt_boundary F) :
    ∃ e : OpenPartialHomeomorph (s31dt_Core F) (EuclideanHalfSpace 2), p ∈ e.source := by
  obtain ⟨j, hpj⟩ := hp
  obtain ⟨x, J, N, f, e, hJ, hb, hN, hDN, hNs, hNP, hND,
      hf, hfi, hef, hei, heb, hfamily⟩ := s78ra_actual_boundary_chart_family F j
  obtain ⟨r, U, a, K, u, hr, hU, hpU, hrest⟩ := hfamily p hpj
  obtain ⟨L, hL⟩ := s31dt_upper_halfspace_homeomorph
  let k : U → EuclideanHalfSpace 2 :=
    fun y => L ⟨(K y).val, (K y).property.2⟩
  have hk : Topology.IsOpenEmbedding k :=
    L.isOpenEmbedding.comp ((s31dt_halfdisc_openEmbedding_upper r).comp K.isOpenEmbedding)
  exact s31dt_chart_from_local_openEmbedding U hU p hpU k hk

/-- Away from the actual seam the core contains an open neighborhood in the
original closed surface, so its original chart gives an interior model chart. -/
theorem s31dt_core_interior_halfspace_chart (p : s31dt_Core F)
    (hp : p ∉ s31dt_boundary F) :
    ∃ e : OpenPartialHomeomorph (s31dt_Core F) (EuclideanHalfSpace 2), p ∈ e.source := by
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
  obtain ⟨a, ha⟩ := s31dt_plane_openEmbedding_upper
  obtain ⟨L, hL⟩ := s31dt_upper_halfspace_homeomorph
  exact s31dt_chart_from_local_openEmbedding U hU p hpV
    (fun q => L (a (c q.val.val))) (L.isOpenEmbedding.comp (ha.comp hchart))

/-- An actual C0 manifold-with-boundary structure on the existing core
subtype topology. There is no atlas or manifold input beyond F itself. -/
theorem s31dt_core_C0_manifold :
    ∃ c : ChartedSpace (EuclideanHalfSpace 2) (s31dt_Core F),
      letI := c
      IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 (s31dt_Core F) := by
  classical
  have hlocal : ∀ p : s31dt_Core F,
      ∃ e : OpenPartialHomeomorph (s31dt_Core F) (EuclideanHalfSpace 2), p ∈ e.source := by
    intro p
    by_cases hp : p ∈ s31dt_boundary F
    · exact s31dt_core_boundary_halfspace_chart F p hp
    · exact s31dt_core_interior_halfspace_chart F p hp
  choose e he using hlocal
  let c : ChartedSpace (EuclideanHalfSpace 2) (s31dt_Core F) := {
    atlas := range e
    chartAt := e
    mem_chart_source := he
    chart_mem_atlas := fun p => mem_range_self p }
  refine ⟨c, ?_⟩
  letI := c
  infer_instance

end LiZhongQC
