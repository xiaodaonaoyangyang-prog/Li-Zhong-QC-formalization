import LiZhongQC.Lemmas.SchottkyDoubleCarrier
import LiZhongQC.Lemmas.SchottkyDoubleConnected
import LiZhongQC.Lemmas.SchottkyCollarGeometry
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Connected.LocallyPathConnected


open Set Metric Topology
noncomputable section
namespace LiZhongQC
universe u

/-- The planar half-annulus used by the shared collar coordinates. -/
theorem s31dt_half_annulus_pathConnected {R : ℝ} (hR : 1 < R) :
    IsPathConnected {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ < R} := by
  have hI : IsPathConnected (Ico (1 : ℝ) R) :=
    (convex_Ico (1 : ℝ) R).isPathConnected ⟨1, le_rfl, hR⟩
  have hC : IsPathConnected (sphere (0 : ℂ) 1) :=
    isPathConnected_sphere (by simp [Complex.rank_real_complex]) 0 (by norm_num)
  have him : (fun p : ℝ × ℂ => p.1 • p.2) ''
      (Ico (1 : ℝ) R ×ˢ sphere (0 : ℂ) 1) =
        {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ < R} := by
    ext z
    constructor
    · rintro ⟨⟨r, w⟩, ⟨hr, hw⟩, rfl⟩
      have hw' : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
      have hr0 : 0 ≤ r := le_trans (by norm_num) hr.1
      change 1 ≤ r ∧ r < R at hr
      simpa only [mem_setOf_eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0,
        hw', mul_one] using hr
    · intro hz
      have hn : ‖z‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hz.1)
      refine ⟨(‖z‖, ‖z‖⁻¹ • z), ⟨hz, ?_⟩, ?_⟩
      · apply mem_sphere_zero_iff_norm.mpr
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)),
          inv_mul_cancel₀ hn]
      · change ‖z‖ • (‖z‖⁻¹ • z) = z
        rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  rw [← him]
  exact (hI.prod hC).image (continuous_fst.smul continuous_snd)

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
  {g n m : ℕ} (F : FiniteTypeStructure S g n m)

/-- The literal N j from COLLAR_HANDOFF is the actual exterior half-annulus.
The coordinate and disjoint-support hypotheses are outputs of worker1's
actual simultaneous coordinate construction. -/
theorem s31dt_collar_half_image
    (v : Fin m → OpenPartialHomeomorph ℂ F.X.carrier) (R : Fin m → ℝ)
    (hR : ∀ j, 1 < R j)
    (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hD : ∀ j, v j '' closedBall (0 : ℂ) 1 = F.D j)
    (hdisj : Pairwise fun i j => Disjoint
      (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j)))
    (j : Fin m) :
    (Subtype.val : s31dt_Core F → F.X.carrier) ''
      (Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j))) =
        v j '' {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ < R j} := by
  have hu : ∀ k, closedBall (0 : ℂ) 1 ⊆ (v k).source :=
    fun k => (closedBall_subset_closedBall (hR k).le).trans (hs k)
  have hsets := s31sd_disc_coordinate_sets (v j) (hu j) (hD j)
  have hinter : interior (closedBall (0 : ℂ) 1) = ball (0 : ℂ) 1 :=
    interior_closedBall (0 : ℂ) (by norm_num)
  ext x
  constructor
  · rintro ⟨c, ⟨z, hz, hzc⟩, rfl⟩
    have hzs := hs j (ball_subset_closedBall hz)
    refine ⟨z, ⟨?_, mem_ball_zero_iff.mp hz⟩, hzc⟩
    by_contra hn
    have hzi : z ∈ interior (closedBall (0 : ℂ) 1) := by
      rw [hinter]
      exact mem_ball_zero_iff.mpr (lt_of_not_ge hn)
    have hvi : v j z ∈ interior (F.D j) := (hsets.2.1 hzs).mpr hzi
    exact c.property (mem_iUnion.mpr ⟨j, hzc ▸ hvi⟩)
  · rintro ⟨z, hz, rfl⟩
    have hzball : z ∈ ball (0 : ℂ) (R j) := mem_ball_zero_iff.mpr hz.2
    have hzclosed := ball_subset_closedBall hzball
    have hzs := hs j hzclosed
    have hcore : v j z ∈ s31dt_coreSet F := by
      intro hi
      obtain ⟨k, hk⟩ := mem_iUnion.mp hi
      by_cases hjk : j = k
      · subst k
        have hzi := (hsets.2.1 hzs).mp hk
        rw [hinter] at hzi
        exact (not_lt_of_ge hz.1) (mem_ball_zero_iff.mp hzi)
      · have hkD := interior_subset hk
        obtain ⟨w, hw, hwe⟩ := (hD k).symm ▸ hkD
        exact Set.disjoint_left.mp (hdisj hjk) ⟨z, hzclosed, rfl⟩
          ⟨w, closedBall_subset_closedBall (hR k).le hw, hwe⟩
    exact ⟨⟨v j z, hcore⟩, ⟨z, hzball, rfl⟩, rfl⟩

theorem s31dt_collar_half_pathConnected
    (v : Fin m → OpenPartialHomeomorph ℂ F.X.carrier) (R : Fin m → ℝ)
    (hR : ∀ j, 1 < R j)
    (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hD : ∀ j, v j '' closedBall (0 : ℂ) 1 = F.D j)
    (hdisj : Pairwise fun i j => Disjoint
      (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j)))
    (j : Fin m) : IsPathConnected
      ((Subtype.val : s31dt_Core F → F.X.carrier) ⁻¹' (v j '' ball (0 : ℂ) (R j))) := by
  apply Topology.IsInducing.subtypeVal.isPathConnected_iff.mpr
  rw [s31dt_collar_half_image F v R hR hs hD hdisj j]
  apply (s31dt_half_annulus_pathConnected (hR j)).image'
  apply (v j).continuousOn.mono
  intro z hz
  exact hs j (mem_closedBall_zero_iff.mpr hz.2.le)

/-- The inverse image of N under the projection is exactly its two sheet images. -/
theorem s31dt_project_preimage_eq (N : Set (s31dt_Core F)) :
    s31dt_project F ⁻¹' N = s31dt_side F false '' N ∪ s31dt_side F true '' N := by
  ext q
  refine Quotient.inductionOn q ?_
  intro x
  change x.2 ∈ N ↔ _
  constructor
  · intro hx
    rcases x with ⟨b, x⟩
    cases b
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (⟨y, hy, he⟩ | ⟨y, hy, he⟩)
    · have hey : y = x.2 := congrArg (s31dt_project F) he
      exact hey ▸ hy
    · have hey : y = x.2 := congrArg (s31dt_project F) he
      exact hey ▸ hy

theorem s31dt_doubled_neighborhood_pathConnected {N : Set (s31dt_Core F)}
    (hN : IsPathConnected N) (hNB : (N ∩ s31dt_boundary F).Nonempty) :
    IsPathConnected (s31dt_project F ⁻¹' N) := by
  rw [s31dt_project_preimage_eq]
  apply (hN.image (s31dt_continuous_side F false)).union
    (hN.image (s31dt_continuous_side F true))
  obtain ⟨x, hxN, hxB⟩ := hNB
  exact ⟨s31dt_side F false x, ⟨x, hxN, rfl⟩, x, hxN,
    ((s31dt_opposite_eq_iff F x x).mpr ⟨rfl, hxB⟩).symm⟩

/-- Apply the half-annulus proof to the literal W j, using the already selected
seam points rather than making another family of choices. -/
theorem s31dt_collar_double_pathConnected
    (v : Fin m → OpenPartialHomeomorph ℂ F.X.carrier) (R : Fin m → ℝ)
    (hR : ∀ j, 1 < R j)
    (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hD : ∀ j, v j '' closedBall (0 : ℂ) 1 = F.D j)
    (hdisj : Pairwise fun i j => Disjoint
      (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j)))
    (p : Fin m → s31dt_Core F) (hp : ∀ j, (p j).val ∈ frontier (F.D j))
    (j : Fin m) : IsPathConnected
      (s31dt_project F ⁻¹' (Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j)))) := by
  apply s31dt_doubled_neighborhood_pathConnected F
    (s31dt_collar_half_pathConnected F v R hR hs hD hdisj j)
  have hpD : (p j).val ∈ F.D j := by
    have hc := frontier_subset_closure (hp j)
    rwa [(s31eg_disc_compact (F.disc j)).isClosed.closure_eq] at hc
  obtain ⟨z, hz, hzp⟩ := (hD j).symm ▸ hpD
  refine ⟨p j, ⟨z, ?_, hzp⟩, j, hp j⟩
  exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt (hR j))

end LiZhongQC
end


open Set Topology
noncomputable section
namespace LiZhongQC

/-- In a disjoint open family of path-connected sets, each member is exactly
one path component of the union. This also excludes paths crossing collars. -/
theorem s31dt_overlap_pathComponent {X I : Type*} [TopologicalSpace X]
    (W : I → Set X) (hopen : ∀ j, IsOpen (W j))
    (hpath : ∀ j, IsPathConnected (W j))
    (hdisj : Pairwise fun i j => Disjoint (W i) (W j))
    (j : I) {x : X} (hx : x ∈ W j) : pathComponentIn (⋃ k, W k) x = W j := by
  let V : Set X := ⋃ k : {k : I // k ≠ j}, W k.val
  have hV : IsOpen V := isOpen_iUnion (fun k => hopen k.val)
  have hd : Disjoint (W j) V := by
    apply Set.disjoint_left.mpr
    intro y hyj hyV
    obtain ⟨k, hk⟩ := mem_iUnion.mp hyV
    exact Set.disjoint_left.mp (hdisj (Ne.symm k.property)) hyj hk
  have hcover : (⋃ k, W k) ⊆ W j ∪ V := by
    intro y hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    by_cases hkj : k = j
    · exact Or.inl (hkj ▸ hk)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k, hkj⟩, hk⟩)
  have hxall : x ∈ ⋃ k, W k := mem_iUnion.mpr ⟨j, hx⟩
  apply Subset.antisymm
  · have hc := (isPathConnected_pathComponentIn hxall).isConnected.isPreconnected
    rcases IsPreconnected.subset_or_subset (hopen j) hV hd
        (pathComponentIn_subset.trans hcover) hc with h | h
    · exact h
    · exact False.elim (Set.disjoint_left.mp hd hx (h (mem_pathComponentIn_self hxall)))
  · exact (hpath j).subset_pathComponentIn hx (subset_iUnion W j)

/-- The already selected point in each collar labels the path components
bijectively. No second choice of seam representatives is made here. -/
theorem s31dt_overlap_component_bijective {X I : Type*} [TopologicalSpace X]
    (W : I → Set X) (hopen : ∀ j, IsOpen (W j))
    (hpath : ∀ j, IsPathConnected (W j))
    (hdisj : Pairwise fun i j => Disjoint (W i) (W j))
    (z : I → X) (hz : ∀ j, z j ∈ W j) :
    Function.Bijective (fun j => ZerothHomotopy.mk
      (⟨z j, mem_iUnion.mpr ⟨j, hz j⟩⟩ : ↥(⋃ k, W k))) := by
  constructor
  · intro i j he
    have hj : Joined (⟨z i, mem_iUnion.mpr ⟨i, hz i⟩⟩ : ↥(⋃ k, W k))
        ⟨z j, mem_iUnion.mpr ⟨j, hz j⟩⟩ := Quotient.exact he
    have hji : z j ∈ pathComponentIn (⋃ k, W k) (z i) :=
      (joinedIn_iff_joined _ _).mpr hj
    rw [s31dt_overlap_pathComponent W hopen hpath hdisj i (hz i)] at hji
    by_contra hij
    exact Set.disjoint_left.mp (hdisj hij) hji (hz j)
  · intro q
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective q
    obtain ⟨j, hxj⟩ := mem_iUnion.mp x.property
    refine ⟨j, ?_⟩
    have hp : JoinedIn (⋃ k, W k) (z j) x.val :=
      ((hpath j).joinedIn _ (hz j) _ hxj).mono (subset_iUnion W j)
    exact ZerothHomotopy.sound hp.joined_subtype.somePath

theorem s31dt_overlap_component_card {X : Type*} [TopologicalSpace X] {m : ℕ}
    (W : Fin m → Set X) (hopen : ∀ j, IsOpen (W j))
    (hpath : ∀ j, IsPathConnected (W j))
    (hdisj : Pairwise fun i j => Disjoint (W i) (W j))
    (z : Fin m → X) (hz : ∀ j, z j ∈ W j) :
    Nat.card (ZerothHomotopy ↥(⋃ k, W k)) = m := by
  let e : Fin m ≃ ZerothHomotopy ↥(⋃ k, W k) :=
    Equiv.ofBijective _ (s31dt_overlap_component_bijective W hopen hpath hdisj z hz)
  simpa using Nat.card_congr e.symm

end LiZhongQC
end


open Set Metric Topology Filter
noncomputable section
namespace LiZhongQC
universe u

/-- A dense path-connected image reaches every point through a local
path-connected open neighborhood. Density alone is not used to assert this. -/
theorem s31dt_pathConnected_of_dense_local {A X : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [PathConnectedSpace A]
    (i : A → X) (hi : Continuous i) (hd : DenseRange i)
    (hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathConnected U) :
    PathConnectedSpace X := by
  have hreach : ∀ x : X, ∃ a : A, Joined x (i a) := by
    intro x
    obtain ⟨U, hU, hx, hUp⟩ := hlocal x
    obtain ⟨y, ⟨a, rfl⟩, hy⟩ := Dense.exists_mem_open hd hU ⟨x, hx⟩
    exact ⟨a, (hUp.joinedIn _ hx _ hy).joined⟩
  refine ⟨⟨i (Classical.choice inferInstance)⟩, ?_⟩
  intro x y
  obtain ⟨a, ha⟩ := hreach x
  obtain ⟨b, hb⟩ := hreach y
  exact (ha.trans ((PathConnectedSpace.joined a b).map hi)).trans hb.symm

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
  {g n m : ℕ} (F : FiniteTypeStructure S g n m)

theorem s31dt_core_pathConnected [ConnectedSpace S]
    (v : Fin m → OpenPartialHomeomorph ℂ F.X.carrier) (R : Fin m → ℝ)
    (hR : ∀ j, 1 < R j)
    (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hD : ∀ j, v j '' closedBall (0 : ℂ) 1 = F.D j)
    (hdisj : Pairwise fun i j => Disjoint
      (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j))) :
    PathConnectedSpace (s31dt_Core F) := by
  letI : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace ℂ S
  letI : PathConnectedSpace S := PathConnectedSpace.of_locallyPathConnectedSpace
  letI : LocallyPathConnectedSpace F.X.carrier :=
    ChartedSpace.locallyPathConnectedSpace ℂ F.X.carrier
  apply s31dt_pathConnected_of_dense_local (s31dt_originalCore F)
    (s31dt_originalCore_openEmbedding F).continuous (s31dt_originalCore_dense F)
  intro x
  by_cases hb : x ∈ s31dt_boundary F
  · obtain ⟨j, hj⟩ := hb
    let N : Set (s31dt_Core F) := Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j))
    have hN : IsOpen N :=
      ((v j).isOpen_image_of_subset_source isOpen_ball
        (ball_subset_closedBall.trans (hs j))).preimage continuous_subtype_val
    have hxD : x.val ∈ F.D j := by
      have hc := frontier_subset_closure hj
      rwa [(s31eg_disc_compact (F.disc j)).isClosed.closure_eq] at hc
    obtain ⟨z, hz, hzx⟩ := (hD j).symm ▸ hxD
    refine ⟨N, hN, ⟨z, ?_, hzx⟩,
      s31dt_collar_half_pathConnected F v R hR hs hD hdisj j⟩
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt (hR j))
  · let U : Set F.X.carrier := (⋃ j, F.D j)ᶜ
    have hU : IsOpen U :=
      (isClosed_iUnion_of_finite (fun j => (s31eg_disc_compact (F.disc j)).isClosed)).isOpen_compl
    have hxU : x.val ∈ U := by
      intro hd
      obtain ⟨j, hj⟩ := mem_iUnion.mp hd
      apply hb
      refine ⟨j, (mem_frontier_iff_notMem_interior hj).mpr ?_⟩
      intro hi
      exact x.property (mem_iUnion.mpr ⟨j, hi⟩)
    obtain ⟨V, ⟨hV, hxV, hVp⟩, hVU⟩ :=
      (isOpen_isPathConnected_basis x.val).mem_iff.mp (hU.mem_nhds hxU)
    have hVC : V ⊆ s31dt_coreSet F := by
      intro y hy hi
      obtain ⟨j, hj⟩ := mem_iUnion.mp hi
      exact hVU hy (mem_iUnion.mpr ⟨j, interior_subset hj⟩)
    exact ⟨Subtype.val ⁻¹' V, hV.preimage continuous_subtype_val, hxV,
      hVp.preimage_coe hVC⟩

/-- Thickened halves are path-connected by joining each collar to the
path-connected closed half at the already selected seam point. -/
theorem s31dt_thickened_half_pathConnected [PathConnectedSpace (s31dt_Core F)]
    (N : Fin m → Set (s31dt_Core F))
    (hW : ∀ j, IsPathConnected (s31dt_project F ⁻¹' N j))
    (p : Fin m → s31dt_Core F)
    (hpN : ∀ j, p j ∈ N j) (b : Bool) :
    IsPathConnected (range (s31dt_side F b) ∪ s31dt_project F ⁻¹' (⋃ j, N j)) := by
  let x₀ : s31dt_Core F := Classical.choice inferInstance
  have hhalf := isPathConnected_range (s31dt_continuous_side F b)
  refine ⟨s31dt_side F b x₀, Or.inl ⟨x₀, rfl⟩, ?_⟩
  intro q hq
  rcases hq with hq | hq
  · exact (hhalf.joinedIn _ ⟨x₀, rfl⟩ _ hq).mono subset_union_left
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hq
    have hpW : s31dt_side F b (p j) ∈ s31dt_project F ⁻¹' N j := hpN j
    have hfirst := (hhalf.joinedIn _ ⟨x₀, rfl⟩ _ ⟨p j, rfl⟩).mono
      (subset_union_left : range (s31dt_side F b) ⊆
        range (s31dt_side F b) ∪ s31dt_project F ⁻¹' (⋃ j, N j))
    have hsecond := ((hW j).joinedIn _ hpW _ hj).mono (show
        s31dt_project F ⁻¹' N j ⊆ range (s31dt_side F b) ∪
          s31dt_project F ⁻¹' (⋃ k, N k) from
      fun y hy => Or.inr (mem_iUnion.mpr ⟨j, hy⟩))
    exact hfirst.trans hsecond

end LiZhongQC
end


open Set Metric Topology
noncomputable section
namespace LiZhongQC
universe u

/-- Concrete shared-collar assembly. All coordinate and seam-point parameters
are exactly the data already produced by worker1. In particular no path or
component property is an input. The N and W expressions remain literal. -/
theorem s31dt_actual_collar_path_data
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [ConnectedSpace S]
    {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    (v : Fin m → OpenPartialHomeomorph ℂ F.X.carrier) (R : Fin m → ℝ)
    (hR : ∀ j, 1 < R j)
    (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hD : ∀ j, v j '' closedBall (0 : ℂ) 1 = F.D j)
    (hdisj : Pairwise fun i j => Disjoint
      (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j)))
    (p : Fin m → s31dt_Core F) (hp : ∀ j, (p j).val ∈ frontier (F.D j)) :
    let N : Fin m → Set (s31dt_Core F) := fun j =>
      Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j))
    let W : Fin m → Set (s31dt_Double F) := fun j => s31dt_project F ⁻¹' N j
    (∀ j, IsPathConnected (W j)) ∧
      PathConnectedSpace (s31dt_Core F) ∧
      (∀ b : Bool, IsPathConnected
        (range (s31dt_side F b) ∪ s31dt_project F ⁻¹' (⋃ j, N j))) ∧
      (∀ j, pathComponentIn (⋃ k, W k) (s31dt_side F false (p j)) = W j) ∧
      Nat.card (ZerothHomotopy ↥(⋃ j, W j)) = m := by
  dsimp only
  let N : Fin m → Set (s31dt_Core F) := fun j =>
    Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j))
  let W : Fin m → Set (s31dt_Double F) := fun j => s31dt_project F ⁻¹' N j
  have hNopen : ∀ j, IsOpen (N j) := fun j =>
    ((v j).isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans (hs j))).preimage continuous_subtype_val
  have hWopen : ∀ j, IsOpen (W j) :=
    fun j => (hNopen j).preimage (s31dt_continuous_project F)
  have hNdisj : Pairwise fun i j => Disjoint (N i) (N j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact Set.disjoint_left.mp (hdisj hij)
      (image_mono ball_subset_closedBall hxi) (image_mono ball_subset_closedBall hxj)
  have hWdisj : Pairwise fun i j => Disjoint (W i) (W j) :=
    fun i j hij => (hNdisj hij).preimage (s31dt_project F)
  have hpN : ∀ j, p j ∈ N j := by
    intro j
    have hpD : (p j).val ∈ F.D j := by
      have hc := frontier_subset_closure (hp j)
      rwa [(s31eg_disc_compact (F.disc j)).isClosed.closure_eq] at hc
    obtain ⟨z, hz, hzp⟩ := (hD j).symm ▸ hpD
    exact ⟨z, mem_ball_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp hz).trans_lt (hR j)), hzp⟩
  have hWpath : ∀ j, IsPathConnected (W j) :=
    s31dt_collar_double_pathConnected F v R hR hs hD hdisj p hp
  have hcore := s31dt_core_pathConnected F v R hR hs hD hdisj
  letI := hcore
  have hzW : ∀ j, s31dt_side F false (p j) ∈ W j := hpN
  refine ⟨hWpath, hcore, ?_, ?_, ?_⟩
  · exact s31dt_thickened_half_pathConnected F N hWpath p hpN
  · intro j
    exact s31dt_overlap_pathComponent W hWopen hWpath hWdisj j (hzW j)
  · exact s31dt_overlap_component_card W hWopen hWpath hWdisj
      (fun j => s31dt_side F false (p j)) hzW

end LiZhongQC
end
