import LiZhongQC.Lemmas.SchottkyCollarConnectivity
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.LocallyFinite


open Set Metric Topology unitInterval
noncomputable section
namespace LiZhongQC
universe u

/-- Radially contract the actual half-collar to its seam, fixing every seam
point. This is constructed inside the same N j; no collar homotopy is assumed. -/
theorem s31dt_collar_radial_homotopy
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    (v : Fin m → OpenPartialHomeomorph ℂ F.X.carrier) (R : Fin m → ℝ)
    (hR : ∀ j, 1 < R j)
    (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hD : ∀ j, v j '' closedBall (0 : ℂ) 1 = F.D j)
    (hdisj : Pairwise fun i j => Disjoint
      (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j)))
    (j : Fin m) :
    let N : Set (s31dt_Core F) := Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j))
    ∃ K : C(I × N, N),
      (∀ x, K (0, x) = x) ∧
      (∀ x, (K (1, x)).val ∈ s31dt_boundary F) ∧
      (∀ t x, x.val ∈ s31dt_boundary F → K (t, x) = x) := by
  let N : Set (s31dt_Core F) := Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j))
  change ∃ K : C(I × N, N), _
  have hu : ∀ k, closedBall (0 : ℂ) 1 ⊆ (v k).source :=
    fun k => (closedBall_subset_closedBall (hR k).le).trans (hs k)
  have hsets := s31sd_disc_coordinate_sets (v j) (hu j) (hD j)
  let z : N → ℂ := fun x => (v j).symm x.val.val
  have hzdata : ∀ x : N, 1 ≤ ‖z x‖ ∧ ‖z x‖ < R j ∧
      z x ∈ (v j).source ∧ v j (z x) = x.val.val := by
    intro x
    have him : x.val.val ∈ (Subtype.val : s31dt_Core F → F.X.carrier) '' N :=
      ⟨x.val, x.property, rfl⟩
    rw [s31dt_collar_half_image F v R hR hs hD hdisj j] at him
    obtain ⟨w, hw, hwe⟩ := him
    have hws : w ∈ (v j).source := hs j (mem_closedBall_zero_iff.mpr hw.2.le)
    have hz : z x = w := by
      change (v j).symm x.val.val = w
      rw [← hwe, (v j).left_inv hws]
    rw [hz]
    exact ⟨hw.1, hw.2, hws, hwe⟩
  have hzcont : Continuous z := by
    apply (v j).continuousOn_symm.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val)
    intro x
    change x.val.val ∈ (v j).target
    rw [← (hzdata x).2.2.2]
    exact (v j).map_source (hzdata x).2.2.1
  have hnorm : ∀ x : N, 0 < ‖z x‖ :=
    fun x => lt_of_lt_of_le zero_lt_one (hzdata x).1
  let a : I × N → ℝ := fun p => 1 + (1 - (p.1 : ℝ)) * (‖z p.2‖ - 1)
  have ha : ∀ p : I × N, 1 ≤ a p ∧ a p ≤ ‖z p.2‖ := by
    intro p
    have ht0 := p.1.property.1
    have ht1 := p.1.property.2
    have hn1 := (hzdata p.2).1
    have hnonneg := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hn1)
    have hupper := mul_nonneg ht0 (sub_nonneg.mpr hn1)
    dsimp [a]
    constructor <;> nlinarith
  have hacont : Continuous a := by
    exact continuous_const.add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        ((hzcont.comp continuous_snd).norm.sub continuous_const))
  let w : I × N → ℂ := fun p => (a p / ‖z p.2‖) • z p.2
  have hwnorm : ∀ p, ‖w p‖ = a p := by
    intro p
    have ha0 : 0 ≤ a p := le_trans zero_le_one (ha p).1
    change ‖(a p / ‖z p.2‖) • z p.2‖ = a p
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg ha0 (norm_nonneg _)), div_mul_cancel₀ _ (hnorm p.2).ne']
  have hwann : ∀ p, 1 ≤ ‖w p‖ ∧ ‖w p‖ < R j := by
    intro p
    rw [hwnorm]
    exact ⟨(ha p).1, (ha p).2.trans_lt (hzdata p.2).2.1⟩
  have hwcont : Continuous w :=
    (hacont.div ((hzcont.comp continuous_snd).norm)
      (fun p => (hnorm p.2).ne')).smul (hzcont.comp continuous_snd)
  have hvcont : Continuous (fun p => v j (w p)) :=
    (v j).continuousOn.comp_continuous hwcont
      (fun p => hs j (mem_closedBall_zero_iff.mpr (hwann p).2.le))
  have hwcore : ∀ p, v j (w p) ∈ s31dt_coreSet F := by
    intro p
    have him : v j (w p) ∈ v j '' {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ < R j} :=
      mem_image_of_mem _ (hwann p)
    rw [← s31dt_collar_half_image F v R hR hs hD hdisj j] at him
    obtain ⟨x, hx, he⟩ := him
    exact he ▸ x.property
  let K : C(I × N, N) := {
    toFun := fun p => ⟨⟨v j (w p), hwcore p⟩,
      ⟨w p, mem_ball_zero_iff.mpr (hwann p).2, rfl⟩⟩
    continuous_toFun := (hvcont.subtype_mk _).subtype_mk _ }
  have hnormB : ∀ x : N, x.val ∈ s31dt_boundary F → ‖z x‖ = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hx
    have hxD : x.val.val ∈ F.D k := by
      have hc := frontier_subset_closure hk
      rwa [(s31eg_disc_compact (F.disc k)).isClosed.closure_eq] at hc
    by_cases hjk : j = k
    · subst k
      have hzfr : z x ∈ frontier (closedBall (0 : ℂ) 1) :=
        (hsets.2.2 (hzdata x).2.2.1).mp ((hzdata x).2.2.2.symm ▸ hk)
      rw [frontier_closedBall (0 : ℂ) (by norm_num)] at hzfr
      exact mem_sphere_zero_iff_norm.mp hzfr
    · obtain ⟨y, hy, hye⟩ := (hD k).symm ▸ hxD
      exact False.elim (Set.disjoint_left.mp (hdisj hjk)
        ⟨z x, mem_closedBall_zero_iff.mpr (hzdata x).2.1.le, (hzdata x).2.2.2⟩
        ⟨y, closedBall_subset_closedBall (hR k).le hy, hye⟩)
  refine ⟨K, ?_, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    change v j ((a (0, x) / ‖z x‖) • z x) = x.val.val
    have ha0 : a (0, x) = ‖z x‖ := by simp [a]
    rw [ha0, div_self (hnorm x).ne', one_smul]
    exact (hzdata x).2.2.2
  · intro x
    refine ⟨j, ?_⟩
    change v j (w (1, x)) ∈ frontier (F.D j)
    apply (hsets.2.2 (hs j (mem_closedBall_zero_iff.mpr (hwann (1, x)).2.le))).mpr
    rw [frontier_closedBall (0 : ℂ) (by norm_num)]
    apply mem_sphere_zero_iff_norm.mpr
    rw [hwnorm]
    simp [a]
  · intro t x hx
    apply Subtype.ext
    apply Subtype.ext
    change v j ((a (t, x) / ‖z x‖) • z x) = x.val.val
    have hn := hnormB x hx
    have hat : a (t, x) = 1 := by simp [a, hn]
    rw [hat, hn, div_one, one_smul]
    exact (hzdata x).2.2.2

end LiZhongQC
end


open Set Topology unitInterval
noncomputable section
namespace LiZhongQC

/-- Glue the constructed local radial homotopies on the disjoint open
collars. This is ordinary open-cover gluing on their actual union. -/
theorem s31dt_union_radial_homotopy {X J : Type*} [TopologicalSpace X]
    (B : Set X) (N : J → Set X) (hN : ∀ j, IsOpen (N j))
    (hdisj : Pairwise fun i j => Disjoint (N i) (N j))
    (K : ∀ j, C(I × N j, N j))
    (hzero : ∀ j x, K j (0, x) = x)
    (hone : ∀ j x, (K j (1, x)).val ∈ B)
    (hfix : ∀ j t x, x.val ∈ B → K j (t, x) = x) :
    ∃ L : C(I × ↥(⋃ j, N j), ↥(⋃ j, N j)),
      (∀ x, L (0, x) = x) ∧
      (∀ x, (L (1, x)).val ∈ B) ∧
      (∀ t x, x.val ∈ B → L (t, x) = x) := by
  let A := ↥(⋃ j, N j)
  let G : J → Set (I × A) := fun j => {p | p.2.val ∈ N j}
  have hG : ∀ j, IsOpen (G j) := fun j =>
    (hN j).preimage (continuous_subtype_val.comp continuous_snd)
  let e : ∀ j, C(G j, I × N j) := fun j => {
    toFun := fun p => (p.val.1, ⟨p.val.2.val, p.property⟩)
    continuous_toFun :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        (((continuous_subtype_val : Continuous
          (Subtype.val : ↥(⋃ k, N k) → X)).comp
          (continuous_snd.comp continuous_subtype_val)).subtype_mk _) }
  let φ : ∀ j, C(G j, A) := fun j => {
    toFun := fun p => ⟨(K j (e j p)).val,
      mem_iUnion.mpr ⟨j, (K j (e j p)).property⟩⟩
    continuous_toFun :=
      (continuous_subtype_val.comp ((K j).continuous.comp (e j).continuous)).subtype_mk _ }
  have hφ : ∀ i j (p : I × A) (hi : p ∈ G i) (hj : p ∈ G j),
      φ i ⟨p, hi⟩ = φ j ⟨p, hj⟩ := by
    intro i j p hi hj
    by_cases hij : i = j
    · subst j
      rfl
    · exact False.elim (Set.disjoint_left.mp (hdisj hij) hi hj)
  have hGn : ∀ p : I × A, ∃ j, G j ∈ 𝓝 p := by
    intro p
    obtain ⟨j, hj⟩ := mem_iUnion.mp p.2.property
    exact ⟨j, (hG j).mem_nhds hj⟩
  let L : C(I × A, A) := ContinuousMap.liftCover G φ hφ hGn
  have hL : ∀ j t (x : A) (hx : x.val ∈ N j),
      (L (t, x)).val = (K j (t, ⟨x.val, hx⟩)).val := by
    intro j t x hx
    have he : L (t, x) = φ j ⟨(t, x), hx⟩ :=
      ContinuousMap.liftCover_coe (⟨(t, x), hx⟩ : G j)
    exact congrArg Subtype.val he
  refine ⟨L, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨j, hj⟩ := mem_iUnion.mp x.property
    apply Subtype.ext
    rw [hL j 0 x hj, hzero]
  · intro x
    obtain ⟨j, hj⟩ := mem_iUnion.mp x.property
    rw [hL j 1 x hj]
    exact hone j _
  · intro t x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp x.property
    apply Subtype.ext
    rw [hL j t x hj, hfix j t _ hx]

end LiZhongQC
end


open Set Topology unitInterval
noncomputable section
namespace LiZhongQC
universe u

/-- The two-stage crossing homotopy contracts on the opposite sheet, then
expands on the chosen sheet. The shared midpoint is justified by actual
boundary equivalence in the quotient. -/
theorem s31dt_collar_crossing
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    (N : Set (s31dt_Core F)) (b : Bool)
    (K : C(I × N, N))
    (hzero : ∀ x, K (0, x) = x)
    (hone : ∀ x, (K (1, x)).val ∈ s31dt_boundary F)
    (hfix : ∀ t x, x.val ∈ s31dt_boundary F → K (t, x) = x) :
    ∃ L : C(I × N, s31dt_Double F),
      (∀ x, L (0, x) = s31dt_side F (!b) x.val) ∧
      (∀ x, L (1, x) = s31dt_side F b x.val) ∧
      (∀ t x, x.val ∈ s31dt_boundary F → L (t, x) = s31dt_side F b x.val) ∧
      (∀ t x, L (t, x) ∈
        range (s31dt_side F b) ∪ s31dt_project F ⁻¹' N) := by
  let i₀ : C(N, s31dt_Double F) :=
    ⟨fun x => s31dt_side F (!b) x.val,
      (s31dt_continuous_side F (!b)).comp continuous_subtype_val⟩
  let i₁ : C(N, s31dt_Double F) :=
    ⟨fun x => s31dt_side F b x.val,
      (s31dt_continuous_side F b).comp continuous_subtype_val⟩
  let e : C(N, s31dt_Double F) :=
    ⟨fun x => s31dt_side F b (K (1, x)).val,
      (s31dt_continuous_side F b).comp (continuous_subtype_val.comp
        (K.continuous.comp (continuous_const.prodMk continuous_id)))⟩
  let A : ContinuousMap.Homotopy i₀ e := {
    toFun := fun p => s31dt_side F (!b) (K p).val
    continuous_toFun := (s31dt_continuous_side F (!b)).comp
      (continuous_subtype_val.comp K.continuous)
    map_zero_left := by intro x; change s31dt_side F (!b) (K (0, x)).val = _; rw [hzero]; rfl
    map_one_left := by
      intro x
      exact (s31dt_side_eq_iff F (!b) b _ _).mpr ⟨rfl, Or.inr (hone x)⟩ }
  let B : ContinuousMap.Homotopy i₁ e := {
    toFun := fun p => s31dt_side F b (K p).val
    continuous_toFun := (s31dt_continuous_side F b).comp
      (continuous_subtype_val.comp K.continuous)
    map_zero_left := by intro x; change s31dt_side F b (K (0, x)).val = _; rw [hzero]; rfl
    map_one_left := fun _ => rfl }
  let L := A.trans B.symm
  refine ⟨L.toContinuousMap, L.map_zero_left, L.map_one_left, ?_, ?_⟩
  · intro t x hx
    change (A.trans B.symm) (t, x) = _
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · change s31dt_side F (!b) (K (_, x)).val = _
      rw [hfix _ x hx]
      exact (s31dt_side_eq_iff F (!b) b x.val x.val).mpr ⟨rfl, Or.inr hx⟩
    · change s31dt_side F b (K (_, x)).val = _
      rw [hfix _ x hx]
  · intro t x
    change (A.trans B.symm) (t, x) ∈ _
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · apply Or.inr
      change (K (_, x)).val ∈ N
      exact (K (_, x)).property
    · exact Or.inl ⟨(K (_, x)).val, rfl⟩

end LiZhongQC
end


open Set Topology
noncomputable section
namespace LiZhongQC

/-- Finite closed-cover gluing, retaining the pointwise formulas needed by
the strong deformation. -/
theorem s31dt_closed_cover_gluing {X Y J : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Finite J]
    (A : J → Set X) (hA : ∀ j, IsClosed (A j)) (hcover : ⋃ j, A j = univ)
    (φ : ∀ j, C(A j, Y))
    (hφ : ∀ i j x (hi : x ∈ A i) (hj : x ∈ A j), φ i ⟨x, hi⟩ = φ j ⟨x, hj⟩) :
    ∃ f : C(X, Y), ∀ j x (hx : x ∈ A j), f x = φ j ⟨x, hx⟩ := by
  let f : X → Y := Set.liftCover A (fun j => φ j) hφ hcover
  have hf : Continuous f := by
    apply (locallyFinite_of_finite A).continuous hcover hA
    intro j
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (A j).domRestrict f = φ j := by
      funext x
      change Set.liftCover A (fun j => φ j) hφ hcover x.val = φ j x
      exact Set.liftCover_coe (S := A) (f := fun j => φ j)
        (hf := hφ) (hS := hcover) x
    rw [he]
    exact (φ j).continuous
  refine ⟨⟨f, hf⟩, ?_⟩
  intro j x hx
  change Set.liftCover A (fun j => φ j) hφ hcover x = φ j ⟨x, hx⟩
  exact Set.liftCover_of_mem (S := A) (f := fun j => φ j)
    (hf := hφ) (hS := hcover) hx

end LiZhongQC
end


open Set Topology unitInterval
noncomputable section
namespace LiZhongQC
universe u

/-- Extend an explicitly constructed collar crossing to the actual thickened
half, by the identity on its entire closed core. The two closed sheets glue
because the crossing fixes the seam. -/
theorem s31dt_half_strong_deformation_from_crossing
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    (N : Set (s31dt_Core F)) (hBN : s31dt_boundary F ⊆ N) (b : Bool)
    (L : C(I × N, s31dt_Double F))
    (hzero : ∀ x, L (0, x) = s31dt_side F (!b) x.val)
    (hone : ∀ x, L (1, x) = s31dt_side F b x.val)
    (hfix : ∀ t x, x.val ∈ s31dt_boundary F → L (t, x) = s31dt_side F b x.val)
    (hmem : ∀ t x, L (t, x) ∈ range (s31dt_side F b) ∪ s31dt_project F ⁻¹' N) :
    let U : Set (s31dt_Double F) := range (s31dt_side F b) ∪ s31dt_project F ⁻¹' N
    ∃ H : C(I × U, U),
      (∀ q, H (0, q) = q) ∧
      (∀ q, (H (1, q)).val = s31dt_side F b (s31dt_project F q.val)) ∧
      (∀ t q, q.val ∈ range (s31dt_side F b) → H (t, q) = q) := by
  let U : Set (s31dt_Double F) := range (s31dt_side F b) ∪ s31dt_project F ⁻¹' N
  change ∃ H : C(I × U, U), _
  have hrepr : ∀ i q, q ∈ range (s31dt_side F i) →
      s31dt_side F i (s31dt_project F q) = q := by
    intro i q hq
    obtain ⟨x, rfl⟩ := hq
    rfl
  have hseam : ∀ i q, s31dt_project F q ∈ s31dt_boundary F →
      s31dt_side F i (s31dt_project F q) = q := by
    intro i q
    refine Quotient.inductionOn q ?_
    intro x hx
    exact (s31dt_side_eq_iff F i x.1 x.2 x.2).mpr ⟨rfl, Or.inr hx⟩
  have hother : ∀ i, i ≠ b → ∀ q : U, q.val ∈ range (s31dt_side F i) →
      s31dt_project F q.val ∈ N := by
    intro i hib q hqi
    rcases q.property with hqb | hqN
    · apply hBN
      have he := (hrepr i q.val hqi).trans (hrepr b q.val hqb).symm
      exact ((s31dt_side_eq_iff F i b _ _).mp he).2.resolve_left hib
    · exact hqN
  let A : Bool → Set (I × U) := fun i => {p | p.2.val ∈ range (s31dt_side F i)}
  have hA : ∀ i, IsClosed (A i) := fun i =>
    (s31dt_side_closedEmbedding F i).isClosed_range.preimage
      (continuous_subtype_val.comp continuous_snd)
  have hcover : ⋃ i, A i = univ := by
    apply eq_univ_of_forall
    intro p
    have hc : p.2.val ∈ range (s31dt_side F false) ∪ range (s31dt_side F true) := by
      rw [s31dt_side_cover]
      exact mem_univ _
    rcases hc with h | h
    · exact mem_iUnion.mpr ⟨false, h⟩
    · exact mem_iUnion.mpr ⟨true, h⟩
  let φ : ∀ i, C(A i, s31dt_Double F) := fun i =>
    if hi : i = b then
      { toFun := fun p => p.val.2.val
        continuous_toFun := by fun_prop }
    else
      { toFun := fun p => L (p.val.1,
          ⟨s31dt_project F p.val.2.val, hother i hi p.val.2 p.property⟩)
        continuous_toFun := L.continuous.comp
          ((continuous_fst.comp continuous_subtype_val).prodMk
            (((s31dt_continuous_project F).comp (continuous_subtype_val.comp
              (continuous_snd.comp continuous_subtype_val))).subtype_mk _)) }
  have hφseam : ∀ i (p : I × U) (hp : p ∈ A i),
      s31dt_project F p.2.val ∈ s31dt_boundary F → φ i ⟨p, hp⟩ = p.2.val := by
    intro i p hp hB
    by_cases hi : i = b
    · simp only [φ, dif_pos hi, ContinuousMap.coe_mk]
    · simp only [φ, dif_neg hi, ContinuousMap.coe_mk]
      rw [hfix _ _ hB]
      exact hseam b p.2.val hB
  have hφ : ∀ i j (p : I × U) (hi : p ∈ A i) (hj : p ∈ A j),
      φ i ⟨p, hi⟩ = φ j ⟨p, hj⟩ := by
    intro i j p hi hj
    by_cases hij : i = j
    · subst j
      rfl
    · have he := (hrepr i p.2.val hi).trans (hrepr j p.2.val hj).symm
      have hB := ((s31dt_side_eq_iff F i j _ _).mp he).2.resolve_left hij
      exact (hφseam i p hi hB).trans (hφseam j p hj hB).symm
  obtain ⟨G, hG⟩ := s31dt_closed_cover_gluing A hA hcover φ hφ
  have hGmem : ∀ p, G p ∈ U := by
    intro p
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ p)
    rw [hG i p hi]
    by_cases hib : i = b
    · simpa only [φ, dif_pos hib, ContinuousMap.coe_mk] using p.2.property
    · simpa only [φ, dif_neg hib, ContinuousMap.coe_mk] using
        hmem p.1 ⟨s31dt_project F p.2.val, hother i hib p.2 hi⟩
  let H : C(I × U, U) := ⟨fun p => ⟨G p, hGmem p⟩, G.continuous.subtype_mk _⟩
  have hHfix : ∀ t q, q.val ∈ range (s31dt_side F b) → H (t, q) = q := by
    intro t q hq
    apply Subtype.ext
    change G (t, q) = q.val
    rw [hG b (t, q) hq]
    simp only [φ, dif_pos rfl, ContinuousMap.coe_mk]
  refine ⟨H, ?_, ?_, hHfix⟩
  · intro q
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ (0, q))
    apply Subtype.ext
    change G (0, q) = q.val
    rw [hG i (0, q) hi]
    by_cases hib : i = b
    · simp only [φ, dif_pos hib, ContinuousMap.coe_mk]
    · simp only [φ, dif_neg hib, ContinuousMap.coe_mk]
      rw [hzero]
      have hi' : i = !b := by
        cases i <;> cases b
        · exact False.elim (hib rfl)
        · rfl
        · rfl
        · exact False.elim (hib rfl)
      rw [← hi']
      exact hrepr i q.val hi
  · intro q
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ (1, q))
    change G (1, q) = _
    rw [hG i (1, q) hi]
    by_cases hib : i = b
    · simp only [φ, dif_pos hib, ContinuousMap.coe_mk]
      exact (hrepr b q.val (hib ▸ hi)).symm
    · simp only [φ, dif_neg hib, ContinuousMap.coe_mk]
      exact hone _

end LiZhongQC
end


open Set Metric Topology unitInterval
noncomputable section
namespace LiZhongQC
universe u

/-- Actual strong deformation retraction of either thickened half onto its
entire chosen core. The endpoints are the actual projection and side inclusion,
and every core point (hence every selected seam basepoint and boundary loop)
is fixed throughout. No deformation-retraction data is an input. -/
theorem s31dt_actual_half_strong_deformation
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    (v : Fin m → OpenPartialHomeomorph ℂ F.X.carrier) (R : Fin m → ℝ)
    (hR : ∀ j, 1 < R j)
    (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hD : ∀ j, v j '' closedBall (0 : ℂ) 1 = F.D j)
    (hdisj : Pairwise fun i j => Disjoint
      (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j)))
    (b : Bool) :
    let N : Fin m → Set (s31dt_Core F) := fun j =>
      Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j))
    let U : Set (s31dt_Double F) :=
      range (s31dt_side F b) ∪ s31dt_project F ⁻¹' (⋃ j, N j)
    ∃ (r : C(U, s31dt_Core F)) (e : C(s31dt_Core F, U))
      (H : ContinuousMap.Homotopy (ContinuousMap.id U) (e.comp r)),
      (∀ q, r q = s31dt_project F q.val) ∧
      (∀ x, (e x).val = s31dt_side F b x) ∧
      (∀ x, r (e x) = x) ∧
      (∀ t x, H (t, e x) = e x) ∧
      (∀ (γ : C(I, s31dt_Core F)) t s, H (t, e (γ s)) = e (γ s)) := by
  let N : Fin m → Set (s31dt_Core F) := fun j =>
    Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j))
  let U : Set (s31dt_Double F) :=
    range (s31dt_side F b) ∪ s31dt_project F ⁻¹' (⋃ j, N j)
  change ∃ (r : C(U, s31dt_Core F)) (e : C(s31dt_Core F, U))
    (H : ContinuousMap.Homotopy (ContinuousMap.id U) (e.comp r)), _
  have hNopen : ∀ j, IsOpen (N j) := fun j =>
    ((v j).isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans (hs j))).preimage continuous_subtype_val
  have hNdisj : Pairwise fun i j => Disjoint (N i) (N j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact Set.disjoint_left.mp (hdisj hij)
      (image_mono ball_subset_closedBall hxi) (image_mono ball_subset_closedBall hxj)
  have hBN : s31dt_boundary F ⊆ ⋃ j, N j := by
    intro x hx
    obtain ⟨j, hj⟩ := hx
    have hxD : x.val ∈ F.D j := by
      have hc := frontier_subset_closure hj
      rwa [(s31eg_disc_compact (F.disc j)).isClosed.closure_eq] at hc
    obtain ⟨z, hz, hzx⟩ := (hD j).symm ▸ hxD
    exact mem_iUnion.mpr ⟨j, z,
      mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt (hR j)), hzx⟩
  have hlocal : ∀ j, ∃ K : C(I × N j, N j),
      (∀ x, K (0, x) = x) ∧
      (∀ x, (K (1, x)).val ∈ s31dt_boundary F) ∧
      (∀ t x, x.val ∈ s31dt_boundary F → K (t, x) = x) :=
    s31dt_collar_radial_homotopy F v R hR hs hD hdisj
  choose K hKzero hKone hKfix using hlocal
  obtain ⟨Kall, hzero, hone, hfix⟩ := s31dt_union_radial_homotopy
    (s31dt_boundary F) N hNopen hNdisj K hKzero hKone hKfix
  obtain ⟨L, hLzero, hLone, hLfix, hLmem⟩ :=
    s31dt_collar_crossing F (⋃ j, N j) b Kall hzero hone hfix
  obtain ⟨G, hGzero, hGone, hGfix⟩ :=
    s31dt_half_strong_deformation_from_crossing F (⋃ j, N j) hBN b L
      hLzero hLone hLfix hLmem
  let r : C(U, s31dt_Core F) := ⟨fun q => s31dt_project F q.val,
    (s31dt_continuous_project F).comp continuous_subtype_val⟩
  let e : C(s31dt_Core F, U) := ⟨fun x => ⟨s31dt_side F b x, Or.inl ⟨x, rfl⟩⟩,
    (s31dt_continuous_side F b).subtype_mk _⟩
  let H : ContinuousMap.Homotopy (ContinuousMap.id U) (e.comp r) := {
    toContinuousMap := G
    map_zero_left := hGzero
    map_one_left := fun q => Subtype.ext (hGone q) }
  have hfixed : ∀ t x, H (t, e x) = e x :=
    fun t x => hGfix t (e x) ⟨x, rfl⟩
  exact ⟨r, e, H, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    hfixed, fun γ t s => hfixed t (γ s)⟩

end LiZhongQC
end
