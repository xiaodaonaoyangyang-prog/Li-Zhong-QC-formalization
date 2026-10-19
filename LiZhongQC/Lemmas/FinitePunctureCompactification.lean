import LiZhongQC.Lemmas.FinitePunctureEnds
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- A complex chart rules out an isolated point on its underlying surface. -/
theorem s31cg_punctured_nhds_neBot {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] (x : X) : NeBot (𝓝[≠] x) := by
  refine ⟨fun hbot => ?_⟩
  have ho : IsOpen ({x} : Set X) := (isOpen_singleton_iff_punctured_nhds x).2 hbot
  have hi := (chartAt ℂ x).isOpen_image_of_subset_source ho
    (singleton_subset_iff.2 (mem_chart_source ℂ x))
  exact not_isOpen_singleton (chartAt ℂ x x) (by simpa only [image_singleton] using hi)

/-- Removing finitely many points from a complex-charted surface leaves a dense
set; this uses the actual chart, with no density assumption on the embedding. -/
theorem s31cg_denseRange {A X : Type*} [TopologicalSpace X] [T1Space X]
    [ChartedSpace ℂ X] (i : A → X) (hf : ((range i)ᶜ).Finite) : DenseRange i := by
  letI : ∀ x : X, NeBot (𝓝[≠] x) := s31cg_punctured_nhds_neBot
  exact s31fe_denseRange_of_finite_compl i hf

/-- At a point of a finite set, arbitrarily small chart discs avoid every other
point of that set. Their punctured parts are preconnected by the planar result
already proved in §26. -/
theorem s31cg_punctured_chart_basis {X : Type*} [TopologicalSpace X] [T1Space X]
    [ChartedSpace ℂ X] (P : Set X) (hP : P.Finite) {x : X} (hx : x ∈ P)
    (U : Set X) (hU : U ∈ 𝓝 x) :
    ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsPreconnected (V \ P) := by
  classical
  let e := chartAt ℂ x
  have hxs : x ∈ e.source := mem_chart_source ℂ x
  have hxt : e x ∈ e.target := e.map_source hxs
  let W : Set X := (U ∩ (P \ {x})ᶜ) ∩ e.source
  have hxavoid : x ∈ (P \ {x})ᶜ := by simp
  have hW : W ∈ 𝓝 x :=
    Filter.inter_mem
      (Filter.inter_mem hU ((hP.subset sdiff_subset).isClosed.isOpen_compl.mem_nhds hxavoid))
      (e.open_source.mem_nhds hxs)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (e.image_mem_nhds hxs hW)
  have hbt : ball (e x) r ⊆ e.target := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hball hz
    exact e.map_source hy.2
  let V : Set X := e.symm '' ball (e x) r
  have hVW : V ⊆ W := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨w, hw, heq⟩ := hball hz
    rw [← heq, e.left_inv hw.2]
    exact hw
  have hV : V ∈ 𝓝 x := by
    have hm := e.symm.image_mem_nhds hxt (ball_mem_nhds (e x) hr)
    simpa only [e.left_inv hxs] using hm
  have heq : V \ P = e.symm '' (ball (e x) r \ {e x}) := by
    ext y
    constructor
    · rintro ⟨hyV, hyP⟩
      obtain ⟨z, hz, rfl⟩ := hyV
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      intro hzx
      have hzxeq : z = e x := hzx
      exact hyP (by rw [hzxeq, e.left_inv hxs]; exact hx)
    · rintro ⟨z, hz, rfl⟩
      have hzV : e.symm z ∈ V := ⟨z, hz.1, rfl⟩
      refine ⟨hzV, ?_⟩
      intro hzP
      have hne : e.symm z ≠ x := by
        intro he
        apply hz.2
        change z = e x
        rw [← e.right_inv (hbt hz.1), he]
      exact (hVW hzV).1.2 ⟨hzP, hne⟩
  refine ⟨V, hV, fun y hy => (hVW hy).1.1, ?_⟩
  rw [heq]
  exact (s26d_b_isPreconnected_punctured (e x) r).image e.symm
    (e.continuousOn_symm.mono (fun z hz => hbt hz.1))

/-- An embedding whose complement is finite has connected neighborhood traces
at every missing point of a complex-charted surface. -/
theorem s31cg_connected_traces {A X : Type*} [TopologicalSpace A]
    [TopologicalSpace X] [T1Space X] [ChartedSpace ℂ X]
    (i : A → X) (hi : Topology.IsEmbedding i) (hf : ((range i)ᶜ).Finite) :
    ∀ x ∉ range i, ∀ U ∈ 𝓝 x,
      ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsPreconnected (i ⁻¹' V) := by
  intro x hx U hU
  obtain ⟨V, hV, hVU, hc⟩ := s31cg_punctured_chart_basis (range i)ᶜ hf hx U hU
  refine ⟨V, hV, hVU, hi.toIsInducing.isPreconnected_image.1 ?_⟩
  rw [image_preimage_eq_inter_range]
  simpa only [sdiff_compl] using hc

/-- Two finite-puncture compactifications of the same complex surface are
uniquely homeomorphic over that surface. All local end hypotheses are supplied
by complex charts. -/
theorem s31cg_compactification_unique {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] {g n g' n' : ℕ}
    (F : FiniteTypeStructure S g n 0) (F' : FiniteTypeStructure S g' n' 0) :
    ∃! H : F.X.carrier ≃ₜ F'.X.carrier, ∀ a, H (F.ι a) = F'.ι a := by
  have hr : (range F.ι)ᶜ = (↑F.P : Set F.X.carrier) := by rw [F.range_ι]; simp
  have hr' : (range F'.ι)ᶜ = (↑F'.P : Set F'.X.carrier) := by rw [F'.range_ι]; simp
  have hf : ((range F.ι)ᶜ).Finite := hr.symm ▸ F.P.finite_toSet
  have hf' : ((range F'.ι)ᶜ).Finite := hr'.symm ▸ F'.P.finite_toSet
  exact s31fe_extend_finite_missing F.ι F'.ι
    F.embedding.isEmbedding F'.embedding.isEmbedding
    (s31cg_denseRange F.ι hf) (s31cg_denseRange F'.ι hf') hf hf'
    (s31cg_connected_traces F.ι F.embedding.isEmbedding hf)
    (s31cg_connected_traces F'.ι F'.embedding.isEmbedding hf')

/-- In the no-hole case, genus and the arbitrary finite number of punctures
are intrinsic. No density, endpoint assignment, or extension is assumed. -/
theorem s31cg_no_holes_type_unique {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] {g n g' n' : ℕ}
    (F : FiniteTypeStructure S g n 0) (F' : FiniteTypeStructure S g' n' 0) :
    g = g' ∧ n = n' := by
  have hr : (range F.ι)ᶜ = (↑F.P : Set F.X.carrier) := by rw [F.range_ι]; simp
  have hr' : (range F'.ι)ᶜ = (↑F'.P : Set F'.X.carrier) := by rw [F'.range_ι]; simp
  have hf : ((range F.ι)ᶜ).Finite := hr.symm ▸ F.P.finite_toSet
  have hf' : ((range F'.ι)ᶜ).Finite := hr'.symm ▸ F'.P.finite_toSet
  exact s31fe_no_holes_unique_of_connected_traces F F'
    (s31cg_denseRange F.ι hf) (s31cg_denseRange F'.ι hf')
    (s31cg_connected_traces F.ι F.embedding.isEmbedding hf)
    (s31cg_connected_traces F'.ι F'.embedding.isEmbedding hf')

/-- The existential finite-type predicate has a unique type whenever both
presentations have no holes; puncture counts are unrestricted. -/
theorem s31cg_isFiniteType_no_holes_unique {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] {g n g' n' : ℕ}
    (h : IsFiniteType S g n 0) (h' : IsFiniteType S g' n' 0) :
    g = g' ∧ n = n' ∧ (0 : ℕ) = 0 := by
  obtain ⟨F⟩ := h
  obtain ⟨F'⟩ := h'
  have hu := s31cg_no_holes_type_unique F F'
  exact ⟨hu.1, hu.2, rfl⟩

end LiZhongQC

