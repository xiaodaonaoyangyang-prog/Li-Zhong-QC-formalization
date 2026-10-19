import LiZhongQC.Lemmas.SchottkyDoubleCarrier
import LiZhongQC.Lemmas.SchottkyActualBoundaryCharts
import LiZhongQC.Lemmas.SchottkyReflectionTransition
import LiZhongQC.Lemmas.HurwitzQuotientChart
import LiZhongQC.Lemmas.FiniteTypeChartInverse

/-!
# The complex atlas of the Schottky double (`s78ra_`, for `exists_schottkyDouble`)

On the actual double `s31dt_Double F` of a finite-type surface: interior charts on both sheets (punctures
included; the original chart on the original sheet and its conjugate on the mirror sheet), the actual seam
charts of `SchottkyActualBoundaryCharts`, analytic compatibility (open-sheet transitions and Schwarz reflection
across the seam), the installed complex manifold structure, holomorphy of the original embedding and the
anticonformal flip (`s78ra_double_complex_atlas`).  Drafts of GPT worker2 (Round78) are reused, reconciled and
completed here.
-/

open Complex Set Filter Topology
open scoped ComplexConjugate Manifold ContDiff

noncomputable section
namespace LiZhongQC

/-- A core point away from the seam lies outside every closed hole. -/
theorem s78ra_core_nonboundary_avoids_holes
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (p : s31dt_Core F)
    (hp : p ∉ s31dt_boundary F) : ∀ j : Fin m, p.val ∉ F.D j := by
  intro j hj
  apply hp
  refine ⟨j, ?_⟩
  refine ⟨subset_closure hj, ?_⟩
  intro hi
  exact p.property (mem_iUnion.2 ⟨j, hi⟩)

/-- Actual interior charts, including the filled punctures, on either
sheet of the shared double. The original chart is used on the original
sheet, and its complex conjugate on the mirror sheet. -/
theorem s78ra_actual_interior_chart
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (b : Bool) (p : s31dt_Core F)
    (hp : p ∉ s31dt_boundary F) :
    ∃ u : OpenPartialHomeomorph (s31dt_Double F) ℂ,
      u.source = s31dt_side F b '' {y : s31dt_Core F |
        y.val ∈ (chartAt ℂ p.val).source ∩ (⋃ j, F.D j)ᶜ} ∧
      s31dt_side F b p ∈ u.source ∧
      ∀ y : s31dt_Core F, y.val ∈ (chartAt ℂ p.val).source ∩ (⋃ j, F.D j)ᶜ →
        u (s31dt_side F b y) =
          if b then conj ((chartAt ℂ p.val) y.val) else (chartAt ℂ p.val) y.val := by
  let c := chartAt ℂ p.val
  let D : Set F.X.carrier := ⋃ j, F.D j
  have hDc : IsClosed D := isClosed_iUnion_of_finite
    (fun j => (s31eg_disc_compact (F.disc j)).isClosed)
  let V : Set F.X.carrier := c.source ∩ Dᶜ
  have hV : IsOpen V := c.open_source.inter hDc.isOpen_compl
  have hpV : p.val ∈ V := by
    refine ⟨mem_chart_source ℂ p.val, ?_⟩
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.1 h
    exact s78ra_core_nonboundary_avoids_holes F p hp j hj
  have havoid : ∀ y ∈ V, ∀ j : Fin m, y ∉ F.D j :=
    fun y hy j hj => hy.2 (mem_iUnion.2 ⟨j, hj⟩)
  have hcore : ∀ y ∈ V, y ∈ s31dt_coreSet F := by
    intro y hy h
    obtain ⟨j, hj⟩ := mem_iUnion.1 h
    exact havoid y hy j (interior_subset hj)
  let W : Set (s31dt_Core F) := {y | y.val ∈ V}
  have hW : IsOpen W := hV.preimage continuous_subtype_val
  have hWB : Disjoint W (s31dt_boundary F) := by
    apply Set.disjoint_left.2
    intro y hy hboundary
    obtain ⟨j, hj⟩ := hboundary
    exact havoid y.val hy j ((s31eg_disc_compact (F.disc j)).isClosed.closure_eq ▸ hj.1)
  let Ecore : ↥W ≃ₜ ↥V := {
    toFun := fun y => ⟨y.val.val, y.property⟩
    invFun := fun y => ⟨⟨y.val, hcore y.val y.property⟩, y.property⟩
    left_inv := by intro y; rfl
    right_inv := by intro y; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let Echart : ↥V ≃ₜ ↥(c '' V) :=
    c.toPartialHomeomorph.homeomorphOfImageSubsetSource inter_subset_left rfl
  let Eside : ↥W ≃ₜ ↥(s31dt_side F b '' W) :=
    (s31dt_side_isEmbedding F b).homeomorphImage W
  let E := Eside.symm.trans (Ecore.trans Echart)
  have hQ : IsOpen (s31dt_side F b '' W) := s31dt_open_side_image F b hW hWB
  have hT : IsOpen (c '' V) := c.isOpen_image_of_subset_source hV inter_subset_left
  obtain ⟨u₀, huS, _, hu⟩ := h84g_open_subspaces_chart (s31dt_side F b '' W) (c '' V)
    hQ hT ⟨s31dt_side F b p, ⟨p, hpV, rfl⟩⟩ ⟨c p.val, ⟨p.val, hpV, rfl⟩⟩ E
  have hcoord : ∀ y : s31dt_Core F, y.val ∈ V → u₀ (s31dt_side F b y) = c y.val := by
    intro y hy
    have h := hu (Eside ⟨y, hy⟩)
    change u₀ (s31dt_side F b y) =
      c (Ecore (Eside.symm (Eside ⟨y, hy⟩))).val at h
    rw [Eside.symm_apply_apply] at h
    exact h
  let τ : ℂ ≃ₜ ℂ := if b then Complex.conjCLE.toHomeomorph else Homeomorph.refl ℂ
  let u := u₀.transHomeomorph τ
  have huSource : u.source = s31dt_side F b '' W := huS
  refine ⟨u, huSource, ?_, ?_⟩
  · rw [huSource]
    exact ⟨p, hpV, rfl⟩
  · intro y hy
    change τ (u₀ (s31dt_side F b y)) = _
    rw [hcoord y hy]
    cases b <;> rfl



/-- The actual open surface with all closed holes removed embeds as the
two disjoint open sheets of the shared quotient. Punctures are retained. -/
theorem s78ra_actual_open_sheets
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (O : TopologicalSpace.Opens F.X.carrier)
    (hO : (O : Set F.X.carrier) = (⋃ j, F.D j)ᶜ) :
    ∃ i : Bool → O → s31dt_Double F,
      (∀ b, Topology.IsOpenEmbedding (i b)) ∧
      Disjoint (range (i false)) (range (i true)) ∧
      (∀ b y, s31dt_flip F (i b y) = i (!b) y) ∧
      (∀ b (y : O) (hy : y.val ∈ s31dt_coreSet F),
        i b y = s31dt_side F b ⟨y.val, hy⟩) ∧
      (∀ b y, (s31dt_project F (i b y)).val = y.val) := by
  have havoid : ∀ y : O, ∀ j, y.val ∉ F.D j := by
    intro y j hj
    have hy : y.val ∈ (⋃ k, F.D k)ᶜ := hO ▸ y.property
    exact hy (mem_iUnion.2 ⟨j, hj⟩)
  have hcore : ∀ y : O, y.val ∈ s31dt_coreSet F := by
    intro y hy
    obtain ⟨j, hj⟩ := mem_iUnion.1 hy
    exact havoid y j (interior_subset hj)
  let C : O → s31dt_Core F := fun y => ⟨y.val, hcore y⟩
  have hC : Topology.IsOpenEmbedding C := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact continuous_subtype_val.subtype_mk _
    · intro y z he
      exact Subtype.ext (congrArg (fun w : s31dt_Core F => w.val) he)
    · exact O.isOpen.isOpenMap_subtype_val.codRestrict hcore
  have hCB : ∀ y : O, C y ∉ s31dt_boundary F := by
    intro y hy
    obtain ⟨j, hj⟩ := hy
    exact havoid y j ((s31eg_disc_compact (F.disc j)).isClosed.closure_eq ▸ hj.1)
  let i : Bool → O → s31dt_Double F := fun b => s31dt_side F b ∘ C
  have hi : ∀ b, Topology.IsOpenEmbedding (i b) := by
    intro b
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact (s31dt_continuous_side F b).comp hC.continuous
    · exact (s31dt_side_injective F b).comp hC.injective
    · intro U hU
      change IsOpen ((s31dt_side F b ∘ C) '' U)
      rw [image_comp]
      apply s31dt_open_side_image F b (hC.isOpenMap U hU)
      apply Set.disjoint_left.2
      rintro p ⟨y, hy, he⟩ hpB
      exact hCB y (he.symm ▸ hpB)
  refine ⟨i, hi, ?_, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.2
    rintro q ⟨y, hy⟩ ⟨z, hz⟩
    have he : s31dt_side F false (C y) = s31dt_side F true (C z) := hy.trans hz.symm
    exact hCB y ((s31dt_opposite_eq_iff F (C y) (C z)).1 he).2
  · intro b y
    exact s31dt_flip_side F b (C y)
  · intro b y hy
    rfl
  · intro b y
    rfl



/-- On an open holomorphic sheet, transition differentiability follows
from holomorphic pullback coordinates and their actual injectivity. The
quotient itself need not have a complex atlas yet. -/
theorem s78ra_transition_on_holomorphic_sheet
    {X Q : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace Q]
    (i : X → Q) (hi : Topology.IsOpenEmbedding i)
    (u v : OpenPartialHomeomorph Q ℂ)
    (hu : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (u ∘ i) (i ⁻¹' u.source))
    (hv : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (v ∘ i) (i ⁻¹' v.source))
    {z : ℂ} (hz : z ∈ (u.symm.trans v).source)
    (hzi : u.symm z ∈ range i) :
    DifferentiableAt ℂ (v ∘ u.symm) z := by
  have hz' : z ∈ u.target ∧ u.symm z ∈ v.source := by
    have h := hz
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at h
    exact h
  obtain ⟨x, hx⟩ := hzi
  letI : Nonempty X := ⟨x⟩
  let U : Set X := i ⁻¹' u.source
  let V : Set X := i ⁻¹' v.source
  let φ : X → ℂ := u ∘ i
  let ψ : X → ℂ := v ∘ i
  have hU : IsOpen U := u.open_source.preimage hi.continuous
  have hV : IsOpen V := v.open_source.preimage hi.continuous
  have hxU : x ∈ U := by
    change i x ∈ u.source
    rw [hx]
    exact u.symm.mapsTo hz'.1
  have hxV : x ∈ V := by
    change i x ∈ v.source
    rw [hx]
    exact hz'.2
  have hφi : InjOn φ U := by
    intro y hy w hw he
    exact hi.injective (u.injOn hy hw he)
  have hxφ : φ x = z := by
    change u (i x) = z
    rw [hx, u.right_inv hz'.1]
  have hInv : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Function.invFunOn φ U) z :=
    s31eg_coordinate_inverse hU hφi hu ⟨x, hxU, hxφ⟩
  have hInvx : Function.invFunOn φ U z = x := by
    rw [← hxφ]
    exact hφi.leftInvOn_invFunOn hxU
  have hψ : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ (Function.invFunOn φ U z) := by
    rw [hInvx]
    exact (hv x hxV).mdifferentiableAt (hV.mem_nhds hxV)
  have hcomp := hψ.comp z hInv
  have hImage : IsOpen (φ '' U) := by
    change IsOpen ((u ∘ i) '' U)
    rw [image_comp]
    apply u.isOpen_image_of_subset_source (hi.isOpenMap U hU)
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  have heq : (v ∘ u.symm) =ᶠ[𝓝 z] (ψ ∘ Function.invFunOn φ U) := by
    filter_upwards [hImage.mem_nhds ⟨x, hxU, hxφ⟩] with w hw
    obtain ⟨y, hy, rfl⟩ := hw
    simp only [Function.comp_apply]
    rw [hφi.leftInvOn_invFunOn hy]
    change v (u.symm (u (i y))) = v (i y)
    rw [u.left_inv hy]
  exact mdifferentiableAt_iff_differentiableAt.1 (hcomp.congr_of_eventuallyEq heq)



/-- The analytic finite-exterior map of the closed-disc coordinate takes
its values in the open disc; boundary differentiability is not used. -/
theorem s78ra_exterior_formula_maps_disc {J : Set ℂ} (hb : Bornology.IsBounded J)
    (f : ℂ → ℂ) (e : ↥((toExt J)ᶜ) ≃ₜ Metric.closedBall (0 : ℂ) 1)
    (hef : ∀ z ∈ (closure J)ᶜ, ∀ hz : (z : ExtPlane) ∈ (toExt J)ᶜ,
      (e ⟨(z : ExtPlane), hz⟩).val = f z)
    (hei : ∀ z : ↥((toExt J)ᶜ),
      ‖(e z).val‖ < 1 ↔ z.val ∈ (closure (toExt J))ᶜ) :
    MapsTo f (closure J)ᶜ unitDisc := by
  intro z hz
  have hzC : (z : ExtPlane) ∈ (toExt J)ᶜ :=
    fun h => hz (subset_closure (coe_mem_toExt_iff.1 h))
  have hzE : (z : ExtPlane) ∈ (closure (toExt J))ᶜ := by
    rw [closure_toExt_of_isBounded' hb]
    exact fun h => hz (coe_mem_toExt_iff.1 h)
  have hn := (hei ⟨(z : ExtPlane), hzC⟩).2 hzE
  rw [hef z hz hzC] at hn
  exact mem_ball_zero_iff.2 hn

/-- The Cayley transform of the genuine exterior uniformizer is
holomorphic on the finite exterior. -/
theorem s78ra_cayley_of_disc_map_holomorphic
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) (hmap : MapsTo f D unitDisc)
    {a : ℂ} (ha : ‖a‖ = 1) :
    DifferentiableOn ℂ (fun z => I * (a - f z) / (a + f z)) D := by
  intro z hz
  have hn : ‖f z‖ < 1 := mem_ball_zero_iff.1 (hmap hz)
  have hc := s78ra_cayley_differentiableAt (s78ra_cayley_upper ha hn).1
  exact (hc.comp z (hf.differentiableAt (hD.mem_nhds hz))).differentiableWithinAt

/-- Holomorphic pullback of an actual boundary chart on either open sheet.
The formula is required only on the open exterior and is then used as an
eventual equality; no derivative at the physical boundary is inferred. -/
theorem s78ra_boundary_chart_sheet_pullback
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (O : TopologicalSpace.Opens F.X.carrier)
    (hO : (O : Set F.X.carrier) = (⋃ j, F.D j)ᶜ)
    (b : Bool) (i : O → s31dt_Double F) (hi : Continuous i)
    (hiFormula : ∀ (y : O) (hy : y.val ∈ s31dt_coreSet F),
      i y = s31dt_side F b ⟨y.val, hy⟩)
    (j : Fin m) (x : F.X.carrier) (J : Set ℂ)
    (hDs : F.D j ⊆ (chartAt ℂ x).source)
    (hDJ : (chartAt ℂ x) '' F.D j = closure J)
    (N : Set F.X.carrier) (hNs : N ⊆ (chartAt ℂ x).source)
    (U : Set (s31dt_Core F)) (hUN : U ⊆ {y | y.val ∈ N})
    {r : ℝ} (K : ↥U ≃ₜ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (u : OpenPartialHomeomorph (s31dt_Double F) ℂ)
    (huS : u.source = s31dt_project F ⁻¹' U)
    (huFormula : ∀ y : ↥U, u (s31dt_side F b y.val) =
      if b then conj (K y).val else (K y).val)
    (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G (closure J)ᶜ)
    (hKG : ∀ y : ↥U, y.val.val ∉ F.D j → (K y).val = G ((chartAt ℂ x) y.val.val)) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (fun y => if b then conj (u (i y)) else u (i y)) (i ⁻¹' u.source) := by
  let c := chartAt ℂ x
  have havoid : ∀ y : O, ∀ k, y.val ∉ F.D k := by
    intro y k hk
    have hy : y.val ∈ (⋃ k, F.D k)ᶜ := hO ▸ y.property
    exact hy (mem_iUnion.2 ⟨k, hk⟩)
  have hcore : ∀ y : O, y.val ∈ s31dt_coreSet F := by
    intro y hy
    obtain ⟨k, hk⟩ := mem_iUnion.1 hy
    exact havoid y k (interior_subset hk)
  have hmem : ∀ y ∈ i ⁻¹' u.source, (⟨y.val, hcore y⟩ : s31dt_Core F) ∈ U := by
    intro y hy
    change i y ∈ u.source at hy
    rw [hiFormula y (hcore y), huS] at hy
    exact hy
  have heq : ∀ y ∈ i ⁻¹' u.source,
      (if b then conj (u (i y)) else u (i y)) = G (c y.val) := by
    intro y hy
    rw [hiFormula y (hcore y), huFormula ⟨⟨y.val, hcore y⟩, hmem y hy⟩]
    rw [hKG ⟨⟨y.val, hcore y⟩, hmem y hy⟩ (havoid y j)]
    cases b <;> simp <;> rfl
  intro y hy
  have hyS : y.val ∈ c.source := hNs (hUN (hmem y hy))
  have hyJ : c y.val ∈ (closure J)ᶜ := by
    intro hc
    obtain ⟨z, hz, he⟩ := hDJ.symm ▸ hc
    have hzy : z = y.val := c.injOn (hDs hz) hyS he
    exact havoid y j (hzy ▸ hz)
  have hval : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : O → F.X.carrier) y :=
    (contMDiff_subtype_val (I := 𝓘(ℂ)) (U := O) (n := ω) y).mdifferentiableAt (by decide)
  have hc : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) c y.val :=
    mdifferentiableAt_atlas (chart_mem_atlas ℂ x) hyS
  have hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) G (c y.val) :=
    mdifferentiableAt_iff_differentiableAt.2
      (hG.differentiableAt (isClosed_closure.isOpen_compl.mem_nhds hyJ))
  have hcomp := hg.comp y (hc.comp y hval)
  apply (hcomp.congr_of_eventuallyEq ?_).mdifferentiableWithinAt
  filter_upwards [(u.open_source.preimage hi).mem_nhds hy] with z hz
  exact heq z hz



/-- The mirror version of the open-sheet transition theorem. Conjugating
both coordinates converts the two antiholomorphic pullbacks to holomorphic
ones, and conjugating the resulting transition twice preserves holomorphy. -/
theorem s78ra_transition_on_mirror_sheet
    {X Q : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace Q]
    (i : X → Q) (hi : Topology.IsOpenEmbedding i)
    (u v : OpenPartialHomeomorph Q ℂ)
    (hu : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (fun x => conj (u (i x))) (i ⁻¹' u.source))
    (hv : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (fun x => conj (v (i x))) (i ⁻¹' v.source))
    {z : ℂ} (hz : z ∈ (u.symm.trans v).source)
    (hzi : u.symm z ∈ range i) :
    DifferentiableAt ℂ (v ∘ u.symm) z := by
  let C : ℂ ≃ₜ ℂ := Complex.conjCLE.toHomeomorph
  let u' := u.transHomeomorph C
  let v' := v.transHomeomorph C
  have hz0 : z ∈ u.target ∧ u.symm z ∈ v.source := by
    have h := hz
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at h
    exact h
  have hz' : conj z ∈ (u'.symm.trans v').source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    change conj (conj z) ∈ u.target ∧ u.symm (conj (conj z)) ∈ v.source
    simpa only [conj_conj] using hz0
  have hi' : u'.symm (conj z) ∈ range i := by
    change u.symm (conj (conj z)) ∈ range i
    simpa only [conj_conj] using hzi
  have hd := s78ra_transition_on_holomorphic_sheet i hi u' v' hu hv hz' hi'
  have hc := hd.conj_conj
  change DifferentiableAt ℂ
    (fun w => conj (conj (v (u.symm (conj (conj w)))))) (conj (conj z)) at hc
  simp only [conj_conj] at hc
  exact hc

/-- All overlaps in a two-sheet reflection atlas are analytic. Every
chart has holomorphic original-side pullback and conjugate-holomorphic
mirror pullback. A chart either lies in one open sheet or is a genuine
reflection chart whose positive half lies in the original sheet. -/
theorem s78ra_reflection_atlas_compatible
    {X Q A : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace Q]
    (i₀ i₁ : X → Q) (hi₀ : Topology.IsOpenEmbedding i₀)
    (hi₁ : Topology.IsOpenEmbedding i₁) (J : Q → Q)
    (u : A → OpenPartialHomeomorph Q ℂ)
    (h₀ : ∀ a, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (u a ∘ i₀) (i₀ ⁻¹' (u a).source))
    (h₁ : ∀ a, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (fun x => conj (u a (i₁ x))) (i₁ ⁻¹' (u a).source))
    (hkind : ∀ a, (u a).source ⊆ range i₀ ∨ (u a).source ⊆ range i₁ ∨
      ((∀ q ∈ (u a).source, J q ∈ (u a).source ∧ u a (J q) = conj (u a q)) ∧
       (∀ z ∈ (u a).target, 0 < z.im → (u a).symm z ∈ range i₀))) :
    ∀ a b, AnalyticOnNhd ℂ (u b ∘ (u a).symm) ((u a).symm.trans (u b)).source := by
  intro a b
  have hOriginal : (∀ z ∈ ((u a).symm.trans (u b)).source,
      (u a).symm z ∈ range i₀) →
      AnalyticOnNhd ℂ (u b ∘ (u a).symm) ((u a).symm.trans (u b)).source := by
    intro h
    apply (analyticOnNhd_iff_differentiableOn ((u a).symm.trans (u b)).open_source).2
    intro z hz
    exact (s78ra_transition_on_holomorphic_sheet i₀ hi₀ (u a) (u b)
      (h₀ a) (h₀ b) hz (h z hz)).differentiableWithinAt
  have hMirror : (∀ z ∈ ((u a).symm.trans (u b)).source,
      (u a).symm z ∈ range i₁) →
      AnalyticOnNhd ℂ (u b ∘ (u a).symm) ((u a).symm.trans (u b)).source := by
    intro h
    apply (analyticOnNhd_iff_differentiableOn ((u a).symm.trans (u b)).open_source).2
    intro z hz
    exact (s78ra_transition_on_mirror_sheet i₁ hi₁ (u a) (u b)
      (h₁ a) (h₁ b) hz (h z hz)).differentiableWithinAt
  rcases hkind a with ha | ha | ha
  · exact hOriginal (fun z hz => ha ((u a).symm.mapsTo hz.1))
  · exact hMirror (fun z hz => ha ((u a).symm.mapsTo hz.1))
  · rcases hkind b with hb | hb | hb
    · exact hOriginal (fun z hz => hb hz.2)
    · exact hMirror (fun z hz => hb hz.2)
    · apply s78ra_boundary_charts_compatible J (u a) (u b) ha.1 hb.1
      intro z hz
      have hzO : z ∈ ((u a).symm.trans (u b)).source := hz.1
      exact (s78ra_transition_on_holomorphic_sheet i₀ hi₀ (u a) (u b)
        (h₀ a) (h₀ b) hzO (ha.2 z hzO.1 hz.2)).differentiableWithinAt

/-- Install the full complex atlas and prove the original-sheet inclusion
holomorphic. The geometric inputs describe actual local charts and their
sheet pullbacks; full analytic compatibility is proved above, not supplied
as an input. -/
theorem s78ra_install_reflection_atlas
    {X Q A : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace Q]
    (i₀ i₁ : X → Q) (hi₀ : Topology.IsOpenEmbedding i₀)
    (hi₁ : Topology.IsOpenEmbedding i₁) (J : Q → Q)
    (u : A → OpenPartialHomeomorph Q ℂ)
    (hcover : ∀ q : Q, ∃ a, q ∈ (u a).source)
    (h₀ : ∀ a, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (u a ∘ i₀) (i₀ ⁻¹' (u a).source))
    (h₁ : ∀ a, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (fun x => conj (u a (i₁ x))) (i₁ ⁻¹' (u a).source))
    (hkind : ∀ a, (u a).source ⊆ range i₀ ∨ (u a).source ⊆ range i₁ ∨
      ((∀ q ∈ (u a).source, J q ∈ (u a).source ∧ u a (J q) = conj (u a q)) ∧
       (∀ z ∈ (u a).target, 0 < z.im → (u a).symm z ∈ range i₀))) :
    ∃ c : ChartedSpace ℂ Q, letI := c
      IsManifold 𝓘(ℂ) ω Q ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) i₀ ∧
      ∀ a, u a ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Q := by
  classical
  let c : ChartedSpace ℂ Q := {
    atlas := range u
    chartAt := fun q => u (Classical.choose (hcover q))
    mem_chart_source := fun q => Classical.choose_spec (hcover q)
    chart_mem_atlas := fun q => ⟨Classical.choose (hcover q), rfl⟩ }
  letI := c
  have hM : IsManifold 𝓘(ℂ) ω Q := by
    apply isManifold_of_contDiffOn 𝓘(ℂ) ω Q
    intro e e' he he'
    change e ∈ range u at he
    change e' ∈ range u at he'
    obtain ⟨a, rfl⟩ := he
    obtain ⟨b, rfl⟩ := he'
    have hA := s78ra_reflection_atlas_compatible i₀ i₁ hi₀ hi₁ J u h₀ h₁ hkind a b
    have hC := hA.contDiffOn_of_completeSpace (n := ω)
    change ContDiffOn ℂ ω ((u a).symm.trans (u b))
      ((u a).symm.trans (u b)).source at hC
    simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, preimage_id, range_id, inter_univ] using hC
  letI : IsManifold 𝓘(ℂ) ω Q := hM
  have hAtlas : ∀ a, u a ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Q := by
    intro a
    exact IsManifold.subset_maximalAtlas ⟨a, rfl⟩
  have hHol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) i₀ := by
    intro x
    obtain ⟨a, ha⟩ := hcover (i₀ x)
    have hUx : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (u a ∘ i₀) x :=
      (h₀ a x ha).mdifferentiableAt
        (((u a).open_source.preimage hi₀.continuous).mem_nhds ha)
    have hInv : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (u a).symm (u a (i₀ x)) :=
      (contMDiffAt_symm_of_mem_maximalAtlas (hAtlas a) ((u a).mapsTo ha)).mdifferentiableAt
        (by decide)
    apply (hInv.comp x hUx).congr_of_eventuallyEq
    filter_upwards [((u a).open_source.preimage hi₀.continuous).mem_nhds ha] with y hy
    exact ((u a).left_inv hy).symm
  exact ⟨c, hM, hHol, hAtlas⟩

/-- An involution which interchanges paired maximal-atlas charts by
conjugation satisfies the original IsAnticonformalInvolution definition,
including at every point in the preferred-chart domains. -/
theorem s78ra_anticonformal_of_paired_atlas
    {Q A : Type*} [TopologicalSpace Q] [ChartedSpace ℂ Q]
    [IsManifold 𝓘(ℂ) ω Q]
    (J : Q ≃ₜ Q) (hJJ : ∀ q, J (J q) = q)
    (u : A → OpenPartialHomeomorph Q ℂ)
    (hcover : ∀ q : Q, ∃ a, q ∈ (u a).source)
    (hAtlas : ∀ a, u a ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Q)
    (hpair : ∀ a, ∃ b, ∀ q ∈ (u a).source,
      J q ∈ (u b).source ∧ u b (J q) = conj (u a q)) :
    IsAnticonformalInvolution J := by
  refine ⟨hJJ, ?_⟩
  intro p z hz
  let c := chartAt ℂ p
  let d := chartAt ℂ (J p)
  have hz' : z ∈ c.target ∧ J (c.symm z) ∈ d.source := hz
  let q := c.symm z
  obtain ⟨a, hqa⟩ := hcover q
  obtain ⟨b, hab⟩ := hpair a
  have hJqb : J q ∈ (u b).source := (hab q hqa).1
  have hconj : conj (u b (J q)) = u a q := by
    rw [(hab q hqa).2, conj_conj]
  have hc : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) c.symm z :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ p) hz'.1
  have hua : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (u a) q :=
    (contMDiffAt_of_mem_maximalAtlas (hAtlas a) hqa).mdifferentiableAt (by decide)
  have hT₁ : DifferentiableAt ℂ (u a ∘ c.symm) z :=
    mdifferentiableAt_iff_differentiableAt.1 (hua.comp z hc)
  have hub : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (u b).symm (u b (J q)) :=
    (contMDiffAt_symm_of_mem_maximalAtlas (hAtlas b) ((u b).mapsTo hJqb)).mdifferentiableAt
      (by decide)
  have hd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) d ((u b).symm (u b (J q))) := by
    rw [(u b).left_inv hJqb]
    exact mdifferentiableAt_atlas (chart_mem_atlas ℂ (J p)) hz'.2
  have hT₂ : DifferentiableAt ℂ (d ∘ (u b).symm) (u b (J q)) :=
    mdifferentiableAt_iff_differentiableAt.1 (hd.comp (u b (J q)) hub)
  have hG := hT₂.conj_conj
  rw [hconj] at hG
  have hComp := hG.comp z hT₁
  have heq : (fun w => conj (localMapExpr J p w)) =ᶠ[𝓝 z]
      ((conj ∘ (d ∘ (u b).symm) ∘ conj) ∘ (u a ∘ c.symm)) := by
    have hnear : ∀ᶠ w in 𝓝 z, c.symm w ∈ (u a).source :=
      hc.continuousAt ((u a).open_source.mem_nhds hqa)
    filter_upwards [hnear] with w hw
    change conj (d (J (c.symm w))) = conj (d ((u b).symm (conj (u a (c.symm w)))))
    rw [← (hab (c.symm w) hw).2, (u b).left_inv (hab (c.symm w) hw).1]
  exact (hComp.congr_of_eventuallyEq heq).differentiableWithinAt

/-- Global reflection-atlas consumer: complex manifold, holomorphic
original inclusion, and the exact original anticonformal-involution
predicate, all on the supplied unchanged topological space Q. -/
theorem s78ra_install_paired_reflection_atlas
    {X Q A : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace Q]
    (i₀ i₁ : X → Q) (hi₀ : Topology.IsOpenEmbedding i₀)
    (hi₁ : Topology.IsOpenEmbedding i₁)
    (J : Q ≃ₜ Q) (hJJ : ∀ q, J (J q) = q)
    (u : A → OpenPartialHomeomorph Q ℂ)
    (hcover : ∀ q : Q, ∃ a, q ∈ (u a).source)
    (h₀ : ∀ a, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (u a ∘ i₀) (i₀ ⁻¹' (u a).source))
    (h₁ : ∀ a, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (fun x => conj (u a (i₁ x))) (i₁ ⁻¹' (u a).source))
    (hkind : ∀ a, (u a).source ⊆ range i₀ ∨ (u a).source ⊆ range i₁ ∨
      ((∀ q ∈ (u a).source, J q ∈ (u a).source ∧ u a (J q) = conj (u a q)) ∧
       (∀ z ∈ (u a).target, 0 < z.im → (u a).symm z ∈ range i₀)))
    (hpair : ∀ a, ∃ b, ∀ q ∈ (u a).source,
      J q ∈ (u b).source ∧ u b (J q) = conj (u a q)) :
    ∃ c : ChartedSpace ℂ Q, letI := c
      IsManifold 𝓘(ℂ) ω Q ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) i₀ ∧
      IsAnticonformalInvolution J ∧
      ∀ a, u a ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Q := by
  obtain ⟨c, hM, hHol, hAtlas⟩ :=
    s78ra_install_reflection_atlas i₀ i₁ hi₀ hi₁ J u hcover h₀ h₁ hkind
  letI := c
  letI : IsManifold 𝓘(ℂ) ω Q := hM
  exact ⟨c, hM, hHol, s78ra_anticonformal_of_paired_atlas J hJJ u hcover hAtlas hpair, hAtlas⟩


/-- Every point of the double is a side point. -/
theorem s78ra_double_side_rep {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (q : s31dt_Double F) :
    ∃ (b : Bool) (y : s31dt_Core F), q = s31dt_side F b y := by
  obtain ⟨⟨b, y⟩, rfl⟩ := Quotient.exists_rep q
  exact ⟨b, y, rfl⟩

/-- A map into an open subset is holomorphic when it is holomorphic into the ambient surface (the charts of the
open subset are restrictions of the ambient charts). -/
theorem s78ra_mdifferentiable_opens_codRestrict {M M' : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [TopologicalSpace M'] [ChartedSpace ℂ M'] {f : M → M'} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (U : TopologicalSpace.Opens M') (hU : ∀ x, f x ∈ U) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x => (⟨f x, hU x⟩ : U)) := by
  intro x
  have h := hf x
  rw [mdifferentiableAt_iff] at h ⊢
  exact ⟨(hf.continuous.subtype_mk hU).continuousAt, h.2⟩

/-- The actual seam chart through a boundary point, with everything the atlas installer needs: flip
equivariance, the upper half on the original sheet, and holomorphic (resp. conjugate-holomorphic) pullbacks to
the original (resp. mirror) open sheet. -/
theorem s78ra_boundary_chart_good {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (O : TopologicalSpace.Opens F.X.carrier)
    (hO : (O : Set F.X.carrier) = (⋃ j, F.D j)ᶜ)
    (i : Bool → O → s31dt_Double F) (hi : ∀ b, Continuous (i b))
    (hiForm : ∀ b (y : O) (hy : y.val ∈ s31dt_coreSet F), i b y = s31dt_side F b ⟨y.val, hy⟩)
    (p : s31dt_Core F) (hp : p ∈ s31dt_boundary F) :
    ∃ u : OpenPartialHomeomorph (s31dt_Double F) ℂ,
      s31dt_side F false p ∈ u.source ∧
      (∀ q ∈ u.source, s31dt_flip F q ∈ u.source ∧ u (s31dt_flip F q) = conj (u q)) ∧
      (∀ z ∈ u.target, 0 < z.im → u.symm z ∈ range (i false)) ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (u ∘ i false) (i false ⁻¹' u.source) ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (fun x => conj (u (i true x))) (i true ⁻¹' u.source) := by
  obtain ⟨j, hj⟩ := hp
  obtain ⟨x, J, N, hJ, hb, hN, hDN, hNs, _hJt, hDJ, _hNP, _hND, hcore, hboundary,
      f, e, hf, _hfi, hef, hei, heb⟩ := s78ra_fixed_hole_uniformizer F j
  have hpD : p.val ∈ F.D j :=
    (s31eg_disc_compact (F.disc j)).isClosed.closure_eq ▸ frontier_subset_closure hj
  obtain ⟨r, U, a, hr, hU, hpU, hUN, ha, K, _hKp, hKb, hKformula⟩ :=
    s78ra_core_halfdisc_from_closed_coordinate F x J hJ hb N hN hNs hcore hboundary e heb p
      (hDN hpD) ⟨j, hj⟩
  obtain ⟨u, huS, huT, hside, hflip⟩ := s78ra_actual_quotient_halfdisc_chart F hr U hU K hKb
  set G : ℂ → ℂ := fun z => I * (a - f z) / (a + f z) with hGdef
  have hG : DifferentiableOn ℂ G (closure J)ᶜ :=
    s78ra_cayley_of_disc_map_holomorphic isClosed_closure.isOpen_compl hf
      (s78ra_exterior_formula_maps_disc hb f e hef hei) ha
  have hKG : ∀ y : ↥U, y.val.val ∉ F.D j → (K y).val = G ((chartAt ℂ x) y.val.val) := by
    intro y hy
    obtain ⟨hy', hK⟩ := hKformula y
    have hyS : y.val.val ∈ (chartAt ℂ x).source := hNs (hUN y.property)
    have hc : (chartAt ℂ x) y.val.val ∈ (closure J)ᶜ := by
      intro hcl
      rw [← hDJ] at hcl
      obtain ⟨z, hz, he⟩ := hcl
      have hzy : z = y.val.val := (chartAt ℂ x).injOn (hNs (hDN hz)) hyS he
      exact hy (hzy ▸ hz)
    rw [hK, hef _ hc hy']
  have hpull : ∀ b, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (fun y => if b then conj (u (i b y)) else u (i b y)) (i b ⁻¹' u.source) := fun b =>
    s78ra_boundary_chart_sheet_pullback F O hO b (i b) (hi b) (hiForm b) j x J (hDN.trans hNs) hDJ N hNs
      U hUN K u huS (hside b) G hG hKG
  refine ⟨u, ?_, hflip, ?_, ?_, ?_⟩
  · rw [huS]
    show s31dt_project F (s31dt_side F false p) ∈ U
    rw [s31dt_project_side]
    exact hpU
  · intro z hz hz0
    have hq : u.symm z ∈ u.source := u.map_target hz
    obtain ⟨b, y, hby⟩ := s78ra_double_side_rep F (u.symm z)
    have hyU : y ∈ U := by
      have := hq
      rw [huS, hby] at this
      change s31dt_project F (s31dt_side F b y) ∈ U at this
      rwa [s31dt_project_side] at this
    have hval : u (s31dt_side F b y) = z := by rw [← hby]; exact u.right_inv hz
    rw [hside b ⟨y, hyU⟩] at hval
    have hKim : 0 ≤ (K ⟨y, hyU⟩).val.im := (K ⟨y, hyU⟩).property.2
    cases b with
    | true =>
      exfalso
      simp only [if_true] at hval
      have : z.im = -(K ⟨y, hyU⟩).val.im := by rw [← hval, Complex.conj_im]
      linarith
    | false =>
      simp only [Bool.false_eq_true, if_false] at hval
      have hyB : y ∉ s31dt_boundary F := by
        intro hB
        have h0 := (hKb ⟨y, hyU⟩).1 hB
        rw [hval] at h0
        linarith
      have havoid := s78ra_core_nonboundary_avoids_holes F y hyB
      have hyO : y.val ∈ (O : Set F.X.carrier) := by
        rw [hO]
        intro hmem
        obtain ⟨k, hk⟩ := mem_iUnion.1 hmem
        exact havoid k hk
      refine ⟨⟨y.val, hyO⟩, ?_⟩
      rw [hiForm false ⟨y.val, hyO⟩ y.property, hby]
  · have h := hpull false
    simpa [Function.comp_def] using h
  · have h := hpull true
    simpa using h

/-- The pair of interior charts through a point off the seam: the original chart on the original sheet, its
conjugate on the mirror sheet, both with the same source in the core, exchanged by the flip. -/
theorem s78ra_interior_chart_pair {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (O : TopologicalSpace.Opens F.X.carrier)
    (hO : (O : Set F.X.carrier) = (⋃ j, F.D j)ᶜ)
    (i : Bool → O → s31dt_Double F) (hi : ∀ b, Continuous (i b))
    (hiForm : ∀ b (y : O) (hy : y.val ∈ s31dt_coreSet F), i b y = s31dt_side F b ⟨y.val, hy⟩)
    (hdisj : Disjoint (range (i false)) (range (i true)))
    (p : s31dt_Core F) (hp : p ∉ s31dt_boundary F) :
    ∃ u : Bool → OpenPartialHomeomorph (s31dt_Double F) ℂ, ∀ b,
      s31dt_side F b p ∈ (u b).source ∧ (u b).source ⊆ range (i b) ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (u b ∘ i false) (i false ⁻¹' (u b).source) ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (fun x => conj (u b (i true x))) (i true ⁻¹' (u b).source) ∧
      ∀ q ∈ (u b).source, s31dt_flip F q ∈ (u (!b)).source ∧
        u (!b) (s31dt_flip F q) = conj (u b q) := by
  have hex := fun b => s78ra_actual_interior_chart F b p hp
  choose u huS hpu hval using hex
  set c := chartAt ℂ p.val with hc
  set V : Set F.X.carrier := c.source ∩ (⋃ j, F.D j)ᶜ with hV
  have hVO : ∀ y ∈ V, y ∈ (O : Set F.X.carrier) := fun y hy => hO ▸ hy.2
  have hVcore : ∀ y ∈ V, y ∈ s31dt_coreSet F := by
    intro y hy h
    obtain ⟨j, hj⟩ := mem_iUnion.1 h
    exact hy.2 (mem_iUnion.2 ⟨j, interior_subset hj⟩)
  -- the source of `u b` lies in the sheet `i b`
  have hsrc : ∀ b, (u b).source ⊆ range (i b) := by
    intro b q hq
    rw [huS b] at hq
    obtain ⟨y, hy, rfl⟩ := hq
    refine ⟨⟨y.val, hVO _ hy⟩, ?_⟩
    rw [hiForm b _ y.property]
  -- the pullback of `u b` to its own sheet
  have hOcore : ∀ y : O, y.val ∈ s31dt_coreSet F := by
    intro y h
    have h1 : y.val ∈ (⋃ j, F.D j)ᶜ := hO ▸ y.property
    obtain ⟨j, hj⟩ := mem_iUnion.1 h
    exact h1 (mem_iUnion.2 ⟨j, interior_subset hj⟩)
  have hown : ∀ b, ∀ y : O, i b y ∈ (u b).source →
      y.val ∈ V ∧ (if b then conj (u b (i b y)) else u b (i b y)) = c y.val := by
    intro b y hy
    have hy' := hy
    rw [huS b, hiForm b y (hOcore y)] at hy'
    obtain ⟨y', hy'V, he⟩ := hy'
    have hyy : y' = ⟨y.val, hOcore y⟩ := s31dt_side_injective F b he
    have hyV : y.val ∈ V := by
      have := hy'V
      rw [hyy] at this
      exact this
    refine ⟨hyV, ?_⟩
    rw [hiForm b y (hOcore y), hval b ⟨y.val, hOcore y⟩ hyV]
    cases b <;> simp
  have hholo : ∀ b, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (fun y => if b then conj (u b (i b y)) else u b (i b y)) (i b ⁻¹' (u b).source) := by
    intro b y hy
    obtain ⟨hyV, _⟩ := hown b y hy
    have hval' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : O → F.X.carrier) y :=
      (contMDiff_subtype_val (I := 𝓘(ℂ)) (U := O) (n := ω) y).mdifferentiableAt (by decide)
    have hcx : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) c y.val :=
      mdifferentiableAt_atlas (chart_mem_atlas ℂ p.val) hyV.1
    have hopen : IsOpen (i b ⁻¹' (u b).source) := (u b).open_source.preimage (hi b)
    apply ((hcx.comp y hval').congr_of_eventuallyEq ?_).mdifferentiableWithinAt
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact (hown b z hz).2
  have hempty : ∀ b, i (!b) ⁻¹' (u b).source = ∅ := by
    intro b
    ext y
    simp only [mem_preimage, mem_empty_iff_false, iff_false]
    intro hy
    obtain ⟨y', hy'⟩ := hsrc b hy
    cases b
    · exact Set.disjoint_left.1 hdisj ⟨y', hy'⟩ ⟨y, rfl⟩
    · exact Set.disjoint_left.1 hdisj ⟨y, rfl⟩ ⟨y', hy'⟩
  refine ⟨u, fun b => ⟨hpu b, hsrc b, ?_, ?_, ?_⟩⟩
  · cases b
    · simpa [Function.comp_def] using hholo false
    · have := hempty true
      simp only [Bool.not_true] at this
      rw [this]
      exact mdifferentiableOn_empty
  · cases b
    · have := hempty false
      simp only [Bool.not_false] at this
      rw [this]
      exact mdifferentiableOn_empty
    · simpa using hholo true
  · intro q hq
    have hq' := hq
    rw [huS b] at hq'
    obtain ⟨y, hyV, rfl⟩ := hq'
    rw [s31dt_flip_side]
    refine ⟨?_, ?_⟩
    · rw [huS (!b)]
      exact ⟨y, hyV, rfl⟩
    · rw [hval (!b) y hyV, hval b y hyV]
      cases b <;> simp

/-- **The complex atlas of the Schottky double.**  The actual double `s31dt_Double F` carries a complex
manifold structure for which the original embedding is holomorphic and the flip is an anticonformal involution:
interior charts of `F.X` on both sheets (conjugated on the mirror sheet, punctures included) and the actual seam
charts, whose transitions are analytic by the open-sheet argument and Schwarz reflection across the seam. -/
theorem s78ra_double_complex_atlas {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) :
    ∃ c : ChartedSpace ℂ (s31dt_Double F), letI := c
      IsManifold 𝓘(ℂ) ω (s31dt_Double F) ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (s31dt_embed F false) ∧
      IsAnticonformalInvolution (s31dt_flipHomeomorph F) := by
  classical
  have hDc : IsClosed (⋃ j, F.D j) :=
    isClosed_iUnion_of_finite (fun j => (s31eg_disc_compact (F.disc j)).isClosed)
  let O : TopologicalSpace.Opens F.X.carrier := ⟨(⋃ j, F.D j)ᶜ, hDc.isOpen_compl⟩
  have hO : (O : Set F.X.carrier) = (⋃ j, F.D j)ᶜ := rfl
  obtain ⟨i, hi, hdisj, _hflipi, hform, _hproj⟩ := s78ra_actual_open_sheets F O hO
  have hB := fun (p : s31dt_Core F) (hp : p ∈ s31dt_boundary F) =>
    s78ra_boundary_chart_good F O hO i (fun b => (hi b).continuous) hform p hp
  have hI := fun (p : s31dt_Core F) (hp : p ∉ s31dt_boundary F) =>
    s78ra_interior_chart_pair F O hO i (fun b => (hi b).continuous) hform hdisj p hp
  choose uB huB using hB
  choose uI huI using hI
  let u : Bool × s31dt_Core F → OpenPartialHomeomorph (s31dt_Double F) ℂ := fun a =>
    if h : a.2 ∈ s31dt_boundary F then uB a.2 h else uI a.2 h a.1
  have hcover : ∀ q : s31dt_Double F, ∃ a, q ∈ (u a).source := by
    intro q
    obtain ⟨b, p, rfl⟩ := s78ra_double_side_rep F q
    refine ⟨(b, p), ?_⟩
    by_cases hp : p ∈ s31dt_boundary F
    · simp only [u, hp, dite_true]
      have heq : s31dt_side F b p = s31dt_side F false p := by
        rw [s31dt_side_eq_iff]
        exact ⟨rfl, Or.inr hp⟩
      rw [heq]
      exact (huB p hp).1
    · simp only [u, hp, dite_false]
      exact ((huI p hp) b).1
  have h₀ : ∀ a, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (u a ∘ i false) (i false ⁻¹' (u a).source) := by
    intro a
    by_cases hp : a.2 ∈ s31dt_boundary F
    · simp only [u, hp, dite_true]
      exact (huB a.2 hp).2.2.2.1
    · simp only [u, hp, dite_false]
      exact ((huI a.2 hp) a.1).2.2.1
  have h₁ : ∀ a, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (fun x => conj (u a (i true x))) (i true ⁻¹' (u a).source) := by
    intro a
    by_cases hp : a.2 ∈ s31dt_boundary F
    · simp only [u, hp, dite_true]
      exact (huB a.2 hp).2.2.2.2
    · simp only [u, hp, dite_false]
      exact ((huI a.2 hp) a.1).2.2.2.1
  have hkind : ∀ a, (u a).source ⊆ range (i false) ∨ (u a).source ⊆ range (i true) ∨
      ((∀ q ∈ (u a).source, s31dt_flipHomeomorph F q ∈ (u a).source ∧
          u a (s31dt_flipHomeomorph F q) = conj (u a q)) ∧
       (∀ z ∈ (u a).target, 0 < z.im → (u a).symm z ∈ range (i false))) := by
    intro a
    by_cases hp : a.2 ∈ s31dt_boundary F
    · simp only [u, hp, dite_true]
      exact Or.inr (Or.inr ⟨(huB a.2 hp).2.1, (huB a.2 hp).2.2.1⟩)
    · simp only [u, hp, dite_false]
      cases hb : a.1
      · exact Or.inl ((huI a.2 hp) false).2.1
      · exact Or.inr (Or.inl ((huI a.2 hp) true).2.1)
  have hpair : ∀ a, ∃ b, ∀ q ∈ (u a).source,
      s31dt_flipHomeomorph F q ∈ (u b).source ∧ u b (s31dt_flipHomeomorph F q) = conj (u a q) := by
    intro a
    by_cases hp : a.2 ∈ s31dt_boundary F
    · refine ⟨a, ?_⟩
      simp only [u, hp, dite_true]
      exact (huB a.2 hp).2.1
    · refine ⟨(!a.1, a.2), ?_⟩
      simp only [u, hp, dite_false]
      exact ((huI a.2 hp) a.1).2.2.2.2
  obtain ⟨c, hM, hHol, hAnti, _⟩ := s78ra_install_paired_reflection_atlas (i false) (i true) (hi false)
    (hi true) (s31dt_flipHomeomorph F) (fun q => s31dt_flip_involutive F q) u hcover h₀ h₁ hkind hpair
  letI := c
  refine ⟨c, hM, ?_, hAnti⟩
  -- the original embedding factors through the original open sheet
  have hmem : ∀ s : S, F.ι s ∈ O := by
    intro s hs
    obtain ⟨j, hj⟩ := mem_iUnion.1 hs
    exact s31dt_original_avoids_disc F s j hj
  have hk : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun s => (⟨F.ι s, hmem s⟩ : O)) :=
    s78ra_mdifferentiable_opens_codRestrict F.holomorphic O hmem
  have heq : s31dt_embed F false = i false ∘ (fun s => (⟨F.ι s, hmem s⟩ : O)) := by
    funext s
    simp only [Function.comp_apply]
    rw [hform false ⟨F.ι s, hmem s⟩ (s31dt_original_mem_core F s)]
    rfl
  rw [heq]
  exact hHol.comp hk

end LiZhongQC
