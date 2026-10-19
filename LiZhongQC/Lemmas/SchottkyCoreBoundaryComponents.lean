import LiZhongQC.Lemmas.SchottkyBoundaryCircleMaps
import Mathlib.Topology.Connected.Clopen

open Set Metric Topology
noncomputable section
namespace LiZhongQC
universe u

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
  {g n m : ℕ} (F : FiniteTypeStructure S g n m)

/-- The existing actual circle map parametrizes exactly one actual hole
boundary, homeomorphically. Its construction is reused, not replaced. -/
theorem s31dt_boundary_circle_homeomorph (j : Fin m) :
    Nonempty (↥(sphere (0 : ℂ) 1) ≃ₜ
      {x : s31dt_Core F | x.val ∈ frontier (F.D j)}) := by
  obtain ⟨v, R, hv, hd⟩ := s31sd_disjoint_disc_coordinates F
  obtain ⟨p, hpi, hp⟩ := s31sd_distinct_seam_points F
  have hR := fun k => (hv k).1
  have hs := fun k => (hv k).2.1
  have hD := fun k => (hv k).2.2.1
  obtain ⟨c, ζ, w, i, r, hc, hrest⟩ :=
    s31dt_boundary_circle_maps F v R hR hs hD p hp j
  have hu : closedBall (0 : ℂ) 1 ⊆ (v j).source :=
    (closedBall_subset_closedBall (hR j).le).trans (hs j)
  have hsets := s31sd_disc_coordinate_sets (v j) hu (hD j)
  have hsource : ∀ z : ↥(sphere (0 : ℂ) 1), z.val ∈ (v j).source :=
    fun z => hu (mem_closedBall_zero_iff.mpr (mem_sphere_zero_iff_norm.mp z.property).le)
  have hrange : range c = {x : s31dt_Core F | x.val ∈ frontier (F.D j)} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      change (c z).val ∈ frontier (F.D j)
      rw [hc]
      apply (hsets.2.2 (hsource z)).mpr
      rw [frontier_closedBall (0 : ℂ) (by norm_num)]
      exact z.property
    · intro hx
      have hxD : x.val ∈ F.D j := by
        have hcl := frontier_subset_closure hx
        rwa [(s31eg_disc_compact (F.disc j)).isClosed.closure_eq] at hcl
      obtain ⟨z, hz, hzx⟩ := (hD j).symm ▸ hxD
      have hzfr := (hsets.2.2 (hu hz)).mp (hzx.symm ▸ hx)
      rw [frontier_closedBall (0 : ℂ) (by norm_num)] at hzfr
      refine ⟨⟨z, hzfr⟩, Subtype.ext ?_⟩
      exact (hc ⟨z, hzfr⟩).trans hzx
  have hinj : Function.Injective c := by
    intro z z' he
    apply Subtype.ext
    apply (v j).injOn (hsource z) (hsource z')
    exact (hc z).symm.trans ((congrArg Subtype.val he).trans (hc z'))
  letI : CompactSpace ↥(sphere (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  exact ⟨(c.continuous.isClosedEmbedding hinj).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hrange)⟩

theorem s31dt_boundary_piece_pathConnected (j : Fin m) :
    IsPathConnected {x : s31dt_Core F | x.val ∈ frontier (F.D j)} := by
  obtain ⟨e⟩ := s31dt_boundary_circle_homeomorph F j
  letI : PathConnectedSpace ↥(sphere (0 : ℂ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (by simp [Complex.rank_real_complex]) 0 (by norm_num))
  letI := e.pathConnectedSpace
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

/-- Each actual hole boundary is a clopen connected piece of the entire
boundary subtype. The complement is the finite union of all other boundaries. -/
theorem s31dt_boundary_component_decomposition :
    let B : Fin m → Set ↥(s31dt_boundary F) :=
      fun j => {x | x.val.val ∈ frontier (F.D j)}
    (∀ j, IsClopen (B j)) ∧ (∀ j, IsConnected (B j)) ∧
      (Pairwise fun i j => Disjoint (B i) (B j)) ∧ (⋃ j, B j) = univ := by
  let B : Fin m → Set ↥(s31dt_boundary F) :=
    fun j => {x | x.val.val ∈ frontier (F.D j)}
  have hclosed : ∀ j, IsClosed (B j) := fun j =>
    isClosed_frontier.preimage (continuous_subtype_val.comp continuous_subtype_val)
  have hdisj : Pairwise fun i j => Disjoint (B i) (B j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    have hiD : x.val.val ∈ F.D i := by
      have hc := frontier_subset_closure hi
      rwa [(s31eg_disc_compact (F.disc i)).isClosed.closure_eq] at hc
    have hjD : x.val.val ∈ F.D j := by
      have hc := frontier_subset_closure hj
      rwa [(s31eg_disc_compact (F.disc j)).isClosed.closure_eq] at hc
    exact Set.disjoint_left.mp (F.disjoint hij) hiD hjD
  have hcover : (⋃ j, B j) = univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr x.property
  have hclopen : ∀ j, IsClopen (B j) := by
    intro j
    have he : (B j)ᶜ = ⋃ k : {k : Fin m // k ≠ j}, B k.val := by
      ext x
      constructor
      · intro hx
        obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
        have hkj : k ≠ j := fun h => hx (h ▸ hk)
        exact mem_iUnion.mpr ⟨⟨k, hkj⟩, hk⟩
      · intro hx hxj
        obtain ⟨k, hk⟩ := mem_iUnion.mp hx
        exact Set.disjoint_left.mp (hdisj k.property) hk hxj
    have hc : IsClosed ((B j)ᶜ) := by
      rw [he]
      exact isClosed_iUnion_of_finite (fun k => hclosed k.val)
    exact ⟨hclosed j, by simpa only [compl_compl] using hc.isOpen_compl⟩
  have hconn : ∀ j, IsConnected (B j) := by
    intro j
    have hp := (s31dt_boundary_piece_pathConnected F j).preimage_coe
      (show {x : s31dt_Core F | x.val ∈ frontier (F.D j)} ⊆ s31dt_boundary F from
        fun x hx => ⟨j, hx⟩)
    exact hp.isConnected
  exact ⟨hclopen, hconn, hdisj, hcover⟩

/-- The component equivalence remembers the actual hole label of every point. -/
theorem s31dt_boundary_components_equiv :
    ∃ e : ConnectedComponents ↥(s31dt_boundary F) ≃ Fin m,
      ∀ j (x : ↥(s31dt_boundary F)), x.val.val ∈ frontier (F.D j) →
        e (ConnectedComponents.mk x) = j := by
  obtain ⟨hclopen, hconn, hdisj, hcover⟩ := s31dt_boundary_component_decomposition F
  exact ⟨ConnectedComponents.equivOfIsClopenOfIsConnected hclopen hdisj hcover hconn,
    fun j x hx => ConnectedComponents.equivOfIsClopenOfIsConnected_mk
      hclopen hdisj hcover hconn x hx⟩

theorem s31dt_boundary_component_card : Nat.card (ConnectedComponents ↥(s31dt_boundary F)) = m := by
  obtain ⟨e, he⟩ := s31dt_boundary_components_equiv F
  simpa using Nat.card_congr e

end LiZhongQC
