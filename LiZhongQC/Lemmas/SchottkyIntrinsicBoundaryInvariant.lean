import LiZhongQC.Lemmas.SchottkyCoreIntrinsicBoundary

open Set Metric Topology
open scoped Manifold ContDiff
noncomputable section
namespace LiZhongQC
universe u

/-- A chart into the Euclidean plane gives an open neighbourhood homeomorphic to the plane. -/
theorem s78nm_euclid_nbhd {S : Type*} [TopologicalSpace S]
    (e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2))) {x : S} (hx : x ∈ e.source) :
    ∃ U : Set S, IsOpen U ∧ x ∈ U ∧ Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 e.open_target (e x) (e.map_source hx)
  let b : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
    OpenPartialHomeomorph.univBall (e x) r
  have hbt : b.target = ball (e x) r := OpenPartialHomeomorph.univBall_target _ hr
  have hbs : b.source = univ := OpenPartialHomeomorph.univBall_source _ _
  let e2 := e.trans b.symm
  have hsrc : e2.source = e.source ∩ e ⁻¹' ball (e x) r := by
    show e.source ∩ e ⁻¹' b.symm.source = _
    rw [OpenPartialHomeomorph.symm_source, hbt]
  have htgt : e2.target = univ := by
    show b.symm.target ∩ b.symm.symm ⁻¹' e.target = univ
    rw [OpenPartialHomeomorph.symm_target, hbs, OpenPartialHomeomorph.symm_symm]
    ext z
    simp only [mem_inter_iff, mem_univ, mem_preimage, true_and]
    have hz : b z ∈ b.target := b.map_source (by rw [hbs]; exact mem_univ z)
    rw [hbt] at hz
    exact iff_true_intro (hball hz)
  have hxs : x ∈ e2.source := by
    rw [hsrc]
    exact ⟨hx, mem_ball_self hr⟩
  refine ⟨e2.source, e2.open_source, hxs, ⟨?_⟩⟩
  exact e2.toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr htgt).trans (Homeomorph.Set.univ _))

/-- If an open subset of the plane maps by a continuous injection into a manifold with boundary
(modelled on the half space), the image avoids the boundary. Equivalently: a boundary point has no
open neighbourhood homeomorphic to the plane. -/
theorem s78nm_boundary_not_euclid
    {S : Type*} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
    {x : S} (hx : (modelWithCornersEuclideanHalfSpace 2).IsBoundaryPoint x)
    {U : Set S} (_hU : IsOpen U) (hxU : x ∈ U) (h : ↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) : False := by
  let e0 := chartAt (EuclideanHalfSpace 2) x
  let f : EuclideanSpace ℝ (Fin 2) → S := fun z => (h.symm z).val
  have hfc : Continuous f := continuous_subtype_val.comp h.symm.continuous
  have hfi : Function.Injective f := Subtype.val_injective.comp h.symm.injective
  let D : Set (EuclideanSpace ℝ (Fin 2)) := f ⁻¹' e0.source
  have hD : IsOpen D := e0.open_source.preimage hfc
  let g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun z => (e0 (f z)).val
  have hgc : ContinuousOn g D := by
    have h1 : ContinuousOn (fun z => e0 (f z)) D :=
      e0.continuousOn.comp hfc.continuousOn (fun z hz => hz)
    exact continuous_subtype_val.comp_continuousOn h1
  have hgi : Set.InjOn g D := by
    intro a ha b hb hab
    have h1 : e0 (f a) = e0 (f b) := Subtype.ext hab
    exact hfi (e0.injOn ha hb h1)
  have hopen : IsOpen (g '' D) :=
    LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.invariance_of_domain_open_map
      g D hD hgc hgi
  have hsub : g '' D ⊆ range (modelWithCornersEuclideanHalfSpace 2) := by
    rintro _ ⟨z, -, rfl⟩
    exact ⟨e0 (f z), rfl⟩
  have hint : g '' D ⊆ interior (range (modelWithCornersEuclideanHalfSpace 2)) :=
    hopen.subset_interior_iff.2 hsub
  let z₀ : EuclideanSpace ℝ (Fin 2) := h ⟨x, hxU⟩
  have hfz : f z₀ = x := by
    show (h.symm (h ⟨x, hxU⟩)).val = x
    rw [Homeomorph.symm_apply_apply]
  have hz₀ : z₀ ∈ D := by
    show f z₀ ∈ e0.source
    rw [hfz]
    exact mem_chart_source _ x
  have hmem : g z₀ ∈ interior (range (modelWithCornersEuclideanHalfSpace 2)) :=
    hint ⟨z₀, hz₀, rfl⟩
  have hb : (modelWithCornersEuclideanHalfSpace 2) (e0 x) ∈
      frontier (range (modelWithCornersEuclideanHalfSpace 2)) := hx
  have hg : g z₀ = (modelWithCornersEuclideanHalfSpace 2) (e0 x) := by
    show (e0 (f z₀)).val = (e0 x).val
    rw [hfz]
  rw [hg] at hmem
  exact hb.2 hmem

/-- The manifold boundary of a surface with boundary is the set of points with no open
neighbourhood homeomorphic to the plane. -/
theorem s78nm_boundary_eq_intrinsic
    {S : Type*} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    (modelWithCornersEuclideanHalfSpace 2).boundary S =
      {x : S | ¬ ∃ U : Set S, IsOpen U ∧ x ∈ U ∧
        Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))} := by
  ext x
  constructor
  · intro hx
    rintro ⟨U, hU, hxU, ⟨h⟩⟩
    exact s78nm_boundary_not_euclid hx hU hxU h
  · intro hx
    by_contra hnb
    apply hx
    have hint : (modelWithCornersEuclideanHalfSpace 2).IsInteriorPoint x := by
      rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
      exact hnb
    let e0 := chartAt (EuclideanHalfSpace 2) x
    have hpos0 : (modelWithCornersEuclideanHalfSpace 2) (e0 x) ∈
        interior (range (modelWithCornersEuclideanHalfSpace 2)) :=
      (LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isInteriorPoint_iff_any_chart
        (modelWithCornersEuclideanHalfSpace 2) (mem_chart_source _ x)).1 hint
    rw [interior_range_modelWithCornersEuclideanHalfSpace] at hpos0
    have hpos : 0 < (e0 x).val 0 := hpos0
    let V : Set (EuclideanHalfSpace 2) := {y | 0 < y.val 0}
    have hcoord : Continuous (fun y : EuclideanSpace ℝ (Fin 2) => y 0) := by fun_prop
    have hV : IsOpen V := isOpen_lt continuous_const (hcoord.comp continuous_subtype_val)
    let f : V → EuclideanSpace ℝ (Fin 2) := fun v => v.val.val
    have hf : Topology.IsOpenEmbedding f := by
      refine ⟨Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal, ?_⟩
      have hr : range f = {w : EuclideanSpace ℝ (Fin 2) | 0 < w 0} := by
        ext w
        constructor
        · rintro ⟨v, rfl⟩
          exact v.property
        · intro hw
          exact ⟨⟨⟨w, le_of_lt hw⟩, hw⟩, rfl⟩
      show IsOpen (range f)
      rw [hr]
      exact isOpen_lt continuous_const hcoord
    letI : Nonempty V := ⟨⟨e0 x, hpos⟩⟩
    let j : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin 2)) :=
      (hf.toOpenPartialHomeomorph f).lift_openEmbedding hV.isOpenEmbedding_subtypeVal
    have hjs : e0 x ∈ j.source := by
      change e0 x ∈ ((hf.toOpenPartialHomeomorph f).lift_openEmbedding
        hV.isOpenEmbedding_subtypeVal).source
      rw [OpenPartialHomeomorph.lift_openEmbedding_source,
        Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source]
      exact ⟨⟨e0 x, hpos⟩, mem_univ _, rfl⟩
    exact s78nm_euclid_nbhd (e0.trans j) (x := x) ⟨mem_chart_source _ x, hjs⟩

/-- Homeomorphisms preserve the property "has an open neighbourhood homeomorphic to the plane". -/
theorem s78nm_euclid_nbhd_iff {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (φ : S ≃ₜ T) (x : S) :
    (∃ U : Set S, IsOpen U ∧ x ∈ U ∧ Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))) ↔
      (∃ U : Set T, IsOpen U ∧ φ x ∈ U ∧ Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))) := by
  constructor
  · rintro ⟨U, hU, hxU, ⟨h⟩⟩
    exact ⟨φ '' U, φ.isOpenMap U hU, mem_image_of_mem φ hxU, ⟨(φ.image U).symm.trans h⟩⟩
  · rintro ⟨U, hU, hxU, ⟨h⟩⟩
    refine ⟨φ ⁻¹' U, hU.preimage φ.continuous, hxU, ⟨?_⟩⟩
    have himg : φ '' (φ ⁻¹' U) = U := φ.image_preimage U
    exact ((φ.image (φ ⁻¹' U)).trans (Homeomorph.setCongr himg)).trans h

/-- The intrinsic boundaries of homeomorphic spaces have the same number of connected
components. -/
theorem s78nm_intrinsic_components_card {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (φ : S ≃ₜ T) :
    Nat.card (ConnectedComponents ↥{x : S | ¬ ∃ U : Set S, IsOpen U ∧ x ∈ U ∧
        Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))}) =
      Nat.card (ConnectedComponents ↥{y : T | ¬ ∃ U : Set T, IsOpen U ∧ y ∈ U ∧
        Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))}) := by
  let ψ : ↥{x : S | ¬ ∃ U : Set S, IsOpen U ∧ x ∈ U ∧
        Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))} ≃ₜ
      ↥{y : T | ¬ ∃ U : Set T, IsOpen U ∧ y ∈ U ∧
        Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))} :=
    φ.subtype (fun x => not_congr (s78nm_euclid_nbhd_iff φ x))
  refine Nat.card_congr
    { toFun := ψ.continuous.connectedComponentsMap
      invFun := ψ.symm.continuous.connectedComponentsMap
      left_inv := ?_
      right_inv := ?_ }
  · intro c
    obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [Continuous.connectedComponentsMap_mk, Continuous.connectedComponentsMap_mk]
    simp
  · intro c
    obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [Continuous.connectedComponentsMap_mk, Continuous.connectedComponentsMap_mk]
    simp

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
  {g n m : ℕ} (F : FiniteTypeStructure S g n m)

/-- The intrinsic boundary of the core has exactly `m` connected components. -/
theorem s78nm_core_intrinsic_components :
    Nat.card (ConnectedComponents ↥{x : s31dt_Core F | ¬ ∃ U : Set (s31dt_Core F),
        IsOpen U ∧ x ∈ U ∧ Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))}) = m := by
  obtain ⟨c, hman, hbd, -, hcard⟩ := s31dt_core_intrinsic_boundary F
  letI := c
  have hIB := s78nm_boundary_eq_intrinsic (S := s31dt_Core F)
  rw [← hIB]
  exact hcard

/-- If the core is homeomorphic to some space `T`, the intrinsic boundary of `T` has exactly `m`
connected components. -/
theorem s78nm_components_card_of_homeomorph
    {T : Type*} [TopologicalSpace T] (φ : s31dt_Core F ≃ₜ T) :
    Nat.card (ConnectedComponents ↥{y : T | ¬ ∃ U : Set T, IsOpen U ∧ y ∈ U ∧
        Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))}) = m :=
  (s78nm_intrinsic_components_card φ).symm.trans (s78nm_core_intrinsic_components F)

end LiZhongQC
