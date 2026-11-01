import LiZhongQC.Lemmas.SchottkyCollarConnectivity
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

open Set Metric Topology
noncomputable section
namespace LiZhongQC
universe u

/-- Actual boundary-circle maps through the same overlap and both thickened
halves. The basepoint is the already selected seam point, expressed in the
current disc coordinate; no new seam-point choice is made. -/
theorem s31dt_boundary_circle_maps
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    (v : Fin m → OpenPartialHomeomorph ℂ F.X.carrier) (R : Fin m → ℝ)
    (hR : ∀ j, 1 < R j)
    (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hD : ∀ j, v j '' closedBall (0 : ℂ) 1 = F.D j)
    (p : Fin m → s31dt_Core F) (hp : ∀ j, (p j).val ∈ frontier (F.D j))
    (j : Fin m) :
    let T := ↥(sphere (0 : ℂ) 1)
    let N : Fin m → Set (s31dt_Core F) := fun k =>
      Subtype.val ⁻¹' (v k '' ball (0 : ℂ) (R k))
    let W : Set (s31dt_Double F) := s31dt_project F ⁻¹' N j
    let U : Bool → Set (s31dt_Double F) := fun b =>
      range (s31dt_side F b) ∪ s31dt_project F ⁻¹' (⋃ k, N k)
    ∃ (c : C(T, s31dt_Core F)) (ζ : T) (w : C(T, W))
      (i : ∀ b, C(W, U b)) (r : ∀ b, C(U b, s31dt_Core F)),
      (∀ z, (c z).val = v j z.val) ∧
      (∀ z, c z ∈ s31dt_boundary F) ∧ c ζ = p j ∧
      ζ.val = (v j).symm (p j).val ∧
      (∀ z, (w z).val = s31dt_side F false (c z)) ∧
      (∀ z, (w z).val = s31dt_side F true (c z)) ∧
      (∀ b q, (i b q).val = q.val) ∧
      (∀ b q, r b q = s31dt_project F q.val) ∧
      (∀ b, ((r b).comp (i b)).comp w = c) := by
  let T := ↥(sphere (0 : ℂ) 1)
  let N : Fin m → Set (s31dt_Core F) := fun k =>
    Subtype.val ⁻¹' (v k '' ball (0 : ℂ) (R k))
  let W : Set (s31dt_Double F) := s31dt_project F ⁻¹' N j
  let U : Bool → Set (s31dt_Double F) := fun b =>
    range (s31dt_side F b) ∪ s31dt_project F ⁻¹' (⋃ k, N k)
  change ∃ (c : C(T, s31dt_Core F)) (ζ : T) (w : C(T, W))
    (i : ∀ b, C(W, U b)) (r : ∀ b, C(U b, s31dt_Core F)), _
  have hu : closedBall (0 : ℂ) 1 ⊆ (v j).source :=
    (closedBall_subset_closedBall (hR j).le).trans (hs j)
  have hsets := s31sd_disc_coordinate_sets (v j) hu (hD j)
  have hzs : ∀ z : T, z.val ∈ (v j).source :=
    fun z => hu (mem_closedBall_zero_iff.mpr (mem_sphere_zero_iff_norm.mp z.property).le)
  have hzfront : ∀ z : T, v j z.val ∈ frontier (F.D j) := by
    intro z
    apply (hsets.2.2 (hzs z)).mpr
    rw [frontier_closedBall (0 : ℂ) (by norm_num)]
    exact z.property
  let c : C(T, s31dt_Core F) := {
    toFun := fun z => ⟨v j z.val, s31dt_frontier_mem_core F (hzfront z)⟩
    continuous_toFun :=
      ((v j).continuousOn.comp_continuous continuous_subtype_val hzs).subtype_mk _ }
  have hcN : ∀ z, c z ∈ N j := by
    intro z
    refine ⟨z.val, ?_, rfl⟩
    apply mem_ball_zero_iff.mpr
    rw [mem_sphere_zero_iff_norm.mp z.property]
    exact hR j
  have hcB : ∀ z, c z ∈ s31dt_boundary F := fun z => ⟨j, hzfront z⟩
  have hpD : (p j).val ∈ F.D j := by
    have hcl := frontier_subset_closure (hp j)
    rwa [(s31eg_disc_compact (F.disc j)).isClosed.closure_eq] at hcl
  obtain ⟨z, hz, hzp⟩ := (hD j).symm ▸ hpD
  have hzfr : z ∈ frontier (closedBall (0 : ℂ) 1) :=
    (hsets.2.2 (hu hz)).mp (hzp.symm ▸ hp j)
  rw [frontier_closedBall (0 : ℂ) (by norm_num)] at hzfr
  let ζ : T := ⟨z, hzfr⟩
  have hζ : c ζ = p j := Subtype.ext hzp
  have hζcoord : ζ.val = (v j).symm (p j).val := by
    change z = (v j).symm (p j).val
    rw [← hzp, (v j).left_inv (hu hz)]
  let w : C(T, W) := {
    toFun := fun z => ⟨s31dt_side F false (c z), hcN z⟩
    continuous_toFun := ((s31dt_continuous_side F false).comp c.continuous).subtype_mk _ }
  let i : ∀ b, C(W, U b) := fun b => {
    toFun := fun q => ⟨q.val, Or.inr (mem_iUnion.mpr ⟨j, q.property⟩)⟩
    continuous_toFun := continuous_subtype_val.subtype_mk _ }
  let r : ∀ b, C(U b, s31dt_Core F) := fun b =>
    ⟨fun q => s31dt_project F q.val,
      (s31dt_continuous_project F).comp continuous_subtype_val⟩
  refine ⟨c, ζ, w, i, r, fun _ => rfl, hcB, hζ, hζcoord,
    fun _ => rfl, ?_, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  · intro z
    exact (s31dt_opposite_eq_iff F (c z) (c z)).mpr ⟨rfl, hcB z⟩
  · intro b
    ext z
    rfl

/-- Strictly commuting continuous triangles give the corresponding based
fundamental-group triangle, including the necessary target basepoint cast. -/
theorem s31dt_fundamental_triangle {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C)) (h : C(A, C)) (hgf : g.comp f = h) (a : A) :
    (FundamentalGroup.mapOfEq g (congrArg (fun k : C(A, C) => k a) hgf)).comp
      (FundamentalGroup.map f a) = FundamentalGroup.map h a := by
  subst h
  ext1 q
  rw [MonoidHom.comp_apply, FundamentalGroup.mapOfEq_apply]
  apply CategoryTheory.End.ext
  change (Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.map q.asHom f) g).cast _ _ =
    Path.Homotopic.Quotient.map q.asHom (g.comp f)
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]
  exact Path.Homotopic.Quotient.map_comp.symm

end LiZhongQC
