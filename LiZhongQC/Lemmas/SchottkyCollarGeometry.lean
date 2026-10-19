/- Mechanically assembled round78 proof; see BUNDLE_MAP.json. -/
import LiZhongQC.Lemmas.FiniteTypeUniqueness
import LiZhongQC.Lemmas.SchottkyDoubleCarrier
import LiZhongQC.Lemmas.SchottkyDoubleGeometry
import Mathlib.Topology.Connected.PathConnected

/- BEGIN SchottkyCollarSupports | SHA256 95ff28a68156e473071ef0111430b9e0eda3beab899ebebb4861c2758680a96a -/
section round78_collar_block_01

open Set Metric Topology

noncomputable section
namespace LiZhongQC

/-- Finitely many disjoint closed sets in a normal space admit pairwise
disjoint open neighborhoods. The neighborhoods are obtained by intersecting
the two sides of each pairwise separation. -/
theorem s31sd_disjoint_open_neighborhoods {X ι : Type*} [TopologicalSpace X]
    [NormalSpace X] [Finite ι] (D : ι → Set X)
    (hclosed : ∀ i, IsClosed (D i)) (hdisj : Pairwise fun i j => Disjoint (D i) (D j)) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i) ∧ D i ⊆ U i) ∧
      Pairwise fun i j => Disjoint (U i) (U j) := by
  classical
  have hsep : ∀ i j, ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ D i ⊆ U ∧ D j ⊆ V ∧ (i ≠ j → Disjoint U V) := by
    intro i j
    by_cases hij : i = j
    · exact ⟨univ, univ, isOpen_univ, isOpen_univ, subset_univ _, subset_univ _,
        fun h => (h hij).elim⟩
    · obtain ⟨U, V, hU, hV, hiU, hjV, hUV⟩ :=
        normal_separation (hclosed i) (hclosed j) (hdisj hij)
      exact ⟨U, V, hU, hV, hiU, hjV, fun _ => hUV⟩
  choose U V hU hV hDU hDV hUV using hsep
  let W : ι → Set X := fun i => ⋂ j, U i j ∩ V j i
  refine ⟨W, ?_, ?_⟩
  · intro i
    refine ⟨isOpen_iInter_of_finite (fun j => (hU i j).inter (hV j i)), ?_⟩
    intro x hx
    exact mem_iInter.2 (fun j => ⟨hDU i j hx, hDV j i hx⟩)
  · intro i j hij
    apply Set.disjoint_left.2
    intro x hxi hxj
    exact Set.disjoint_left.1 (hUV i j hij)
      ((mem_iInter.1 hxi j).1) ((mem_iInter.1 hxj i).2)

/-- Simultaneous actual disc coordinates with disjoint larger supports,
all avoiding the marked punctures. The radius is strictly greater than one,
so an exterior collar can be retained after removing each open hole. -/
theorem s31sd_disjoint_disc_coordinates {S : Type*} [TopologicalSpace S]
    [ChartedSpace ℂ S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) :
    ∃ (u : Fin m → OpenPartialHomeomorph ℂ F.X.carrier) (R : Fin m → ℝ),
      (∀ j, 1 < R j ∧ closedBall (0 : ℂ) (R j) ⊆ (u j).source ∧
        u j '' closedBall (0 : ℂ) 1 = F.D j ∧
        Disjoint (u j '' closedBall (0 : ℂ) (R j)) (↑F.P : Set F.X.carrier)) ∧
      Pairwise fun i j => Disjoint
        (u i '' closedBall (0 : ℂ) (R i)) (u j '' closedBall (0 : ℂ) (R j)) := by
  classical
  obtain ⟨U, hU, hUU⟩ := s31sd_disjoint_open_neighborhoods F.D
    (fun j => (s31eg_disc_compact (F.disc j)).isClosed) F.disjoint
  have hcoords : ∀ j, ∃ (u : OpenPartialHomeomorph ℂ F.X.carrier) (R : ℝ),
      1 < R ∧ closedBall (0 : ℂ) R ⊆ u.source ∧
      u '' closedBall (0 : ℂ) 1 = F.D j ∧
      u '' closedBall (0 : ℂ) R ⊆ U j ∩ (↑F.P : Set F.X.carrier)ᶜ := by
    intro j
    apply s31sh_surface_disc_coordinates_in (F.disc j)
      ((hU j).1.inter F.P.finite_toSet.isClosed.isOpen_compl)
    intro x hx
    exact ⟨(hU j).2 hx, fun hp => Set.disjoint_left.1 (F.disjoint_P j) hx hp⟩
  choose u R hR hsource hD hsupport using hcoords
  refine ⟨u, R, ?_, ?_⟩
  · intro j
    refine ⟨hR j, hsource j, hD j, Set.disjoint_left.2 ?_⟩
    intro x hx hp
    exact (hsupport j hx).2 hp
  · intro i j hij
    exact (hUU hij).mono (fun x hx => (hsupport i hx).1)
      (fun x hx => (hsupport j hx).1)

/-- Disc coordinates identify the actual interior and boundary as well as
the closed disc. This is the topological input for extracting the outer collar. -/
theorem s31sd_disc_coordinate_sets {X : Type*} [TopologicalSpace X]
    (u : OpenPartialHomeomorph ℂ X) {D : Set X}
    (hsource : closedBall (0 : ℂ) 1 ⊆ u.source)
    (hD : u '' closedBall (0 : ℂ) 1 = D) :
    u.IsImage (closedBall (0 : ℂ) 1) D ∧
      u.IsImage (interior (closedBall (0 : ℂ) 1)) (interior D) ∧
      u.IsImage (frontier (closedBall (0 : ℂ) 1)) (frontier D) := by
  have h : u.IsImage (closedBall (0 : ℂ) 1) D := by
    intro z hz
    constructor
    · intro hzD
      obtain ⟨w, hw, hwz⟩ := hD.symm ▸ hzD
      have hwz' : w = z := u.injOn (hsource hw) hz hwz
      exact hwz' ▸ hw
    · intro hzball
      exact hD ▸ mem_image_of_mem u hzball
  exact ⟨h, h.interior, h.frontier⟩

end LiZhongQC
end -- close original anonymous noncomputable section
end round78_collar_block_01
/- END SchottkyCollarSupports -/

/- BEGIN SchottkyCollarSelection | SHA256 40a2e856ac652214980d3a023e419bf6b75bc8ff650c6d5c122ca325e5794a34 -/
section round78_collar_block_02

open Set Metric Topology

noncomputable section
namespace LiZhongQC

universe u

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
  {g n m : ℕ} (F : FiniteTypeStructure S g n m)

/-- Choose one actual seam point on each actual deleted-disc boundary.
The points are pairwise distinct, including after inclusion in the core. -/
theorem s31sd_distinct_seam_points :
    ∃ p : Fin m → s31dt_Core F, Function.Injective p ∧
      ∀ j, (p j).val ∈ frontier (F.D j) := by
  classical
  have hex : ∀ j, ∃ x : F.X.carrier, x ∈ frontier (F.D j) := by
    intro j
    obtain ⟨v, hv, hvD⟩ := s31sh_surface_disc_coordinates (F.disc j)
    have hsets := s31sd_disc_coordinate_sets v hv hvD
    have hone : (1 : ℂ) ∈ closedBall (0 : ℂ) 1 :=
      mem_closedBall_zero_iff.2 (by simp)
    have hfront : (1 : ℂ) ∈ frontier (closedBall (0 : ℂ) 1) := by
      rw [frontier_closedBall (0 : ℂ) (by norm_num)]
      exact mem_sphere_zero_iff_norm.2 (by simp)
    exact ⟨v 1, (hsets.2.2 (hv hone)).2 hfront⟩
  choose x hx using hex
  have hxcore : ∀ j, x j ∈ s31dt_coreSet F := by
    intro j
    change x j ∈ (⋃ k, interior (F.D k))ᶜ
    rw [s31sd_half_partition F]
    exact Or.inr (mem_iUnion.2 ⟨j, hx j⟩)
  let p : Fin m → s31dt_Core F := fun j => ⟨x j, hxcore j⟩
  refine ⟨p, ?_, hx⟩
  intro i j hp
  by_contra hij
  have heq : x i = x j := congrArg Subtype.val hp
  have hiD : x i ∈ F.D i :=
    (s31eg_disc_compact (F.disc i)).isClosed.closure_eq ▸ frontier_subset_closure (hx i)
  have hjD : x j ∈ F.D j :=
    (s31eg_disc_compact (F.disc j)).isClosed.closure_eq ▸ frontier_subset_closure (hx j)
  exact Set.disjoint_left.1 (F.disjoint hij) hiD (heq.symm ▸ hjD)

/-- Shared collar-neighborhood formula for all workers. Its ingredients are
produced by `s31sd_disjoint_disc_coordinates`; path-connectedness and radial
deformation retractions are separate subsequent geometric steps. -/
theorem s31sd_collar_neighborhoods
    (v : Fin m → OpenPartialHomeomorph ℂ F.X.carrier) (R : Fin m → ℝ)
    (hR : ∀ j, 1 < R j)
    (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hD : ∀ j, v j '' closedBall (0 : ℂ) 1 = F.D j)
    (hdisj : Pairwise fun i j => Disjoint
      (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j))) :
    ∃ N : Fin m → Set (s31dt_Core F),
      (∀ j, N j = Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j))) ∧
      (∀ j, IsOpen (N j)) ∧
      (Pairwise fun i j => Disjoint (N i) (N j)) ∧
      s31dt_boundary F ⊆ ⋃ j, N j := by
  let N : Fin m → Set (s31dt_Core F) := fun j =>
    Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j))
  have hball : ∀ j, ball (0 : ℂ) (R j) ⊆ (v j).source :=
    fun j => ball_subset_closedBall.trans (hs j)
  refine ⟨N, fun _ => rfl, ?_, ?_, ?_⟩
  · intro j
    exact ((v j).isOpen_image_of_subset_source isOpen_ball (hball j)).preimage
      continuous_subtype_val
  · intro i j hij
    apply Set.disjoint_left.2
    intro x hxi hxj
    exact Set.disjoint_left.1 (hdisj hij)
      (image_mono ball_subset_closedBall hxi) (image_mono ball_subset_closedBall hxj)
  · intro x hx
    obtain ⟨j, hj⟩ := hx
    have hxD : x.val ∈ F.D j :=
      (s31eg_disc_compact (F.disc j)).isClosed.closure_eq ▸ frontier_subset_closure hj
    obtain ⟨z, hz, hzx⟩ := (hD j).symm ▸ hxD
    have hzball : z ∈ ball (0 : ℂ) (R j) := by
      apply mem_ball_zero_iff.2
      exact (mem_closedBall_zero_iff.1 hz).trans_lt (hR j)
    exact mem_iUnion.2 ⟨j, z, hzball, hzx⟩

end LiZhongQC
end -- close original anonymous noncomputable section
end round78_collar_block_02
/- END SchottkyCollarSelection -/

/- BEGIN SchottkySelectedRepresentatives | SHA256 d4c0a1bab53a3c5fb265b7144ab513061819fdabf582b5d7c4a06ae16a49f7cf -/
section round78_collar_block_03

open Set

namespace LiZhongQC

/-- Choosing a point in a nonempty selected set represents every path
component of a path-connected space. Written without the pending external
SVK definition; its conclusion unfolds exactly to `IsRepresentative A`. -/
theorem s31sd_representative_of_path_connected {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] {A : Set X} (hA : A.Nonempty) :
    ∀ x : X, ∃ a ∈ A, Joined a x := by
  obtain ⟨a, ha⟩ := hA
  intro x
  exact ⟨a, ha, PathConnectedSpace.joined a x⟩

/-- One chosen point in each path-connected member of a covering family
represents every path component of the union. Disjointness is unnecessary
for this representation property; it is needed later to identify components. -/
theorem s31sd_representative_of_components {X ι : Type*} [TopologicalSpace X]
    (W : ι → Set X) (hW : ∀ j, IsPathConnected (W j))
    (z : ι → X) (hz : ∀ j, z j ∈ W j) :
    ∀ x : ↥(⋃ j, W j), ∃ a : ↥(⋃ j, W j),
      a.val ∈ range z ∧ Joined a x := by
  intro x
  obtain ⟨j, hxj⟩ := mem_iUnion.1 x.property
  have hpath : JoinedIn (⋃ k, W k) (z j) x.val :=
    ((hW j).joinedIn (z j) (hz j) x.val hxj).mono (subset_iUnion W j)
  exact ⟨⟨z j, mem_iUnion.2 ⟨j, hz j⟩⟩, mem_range_self j, hpath.joined_subtype⟩

/-- Version with an explicit overlap set, matching selectedIn (range z) B
in the selected-object van Kampen statement without changing the ambient set. -/
theorem s31sd_representative_of_component_cover {X ι : Type*}
    [TopologicalSpace X] (B : Set X) (W : ι → Set X)
    (hcover : (⋃ j, W j) = B) (hW : ∀ j, IsPathConnected (W j))
    (z : ι → X) (hz : ∀ j, z j ∈ W j) :
    ∀ x : B, ∃ a : B, a.val ∈ range z ∧ Joined a x := by
  subst B
  exact s31sd_representative_of_components W hW z hz

end LiZhongQC
end round78_collar_block_03
/- END SchottkySelectedRepresentatives -/
