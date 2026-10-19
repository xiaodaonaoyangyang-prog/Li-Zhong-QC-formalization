import LiZhongQC.Lemmas.FiniteTypeUniqueness

/-!
The concrete topological Schottky double. There is one carrier: the quotient of
two copies of the original closed surface with the open holes removed. Punctures
are retained in the core. Only actual hole-boundary points are identified.
-/

open Set Topology

noncomputable section
namespace LiZhongQC
universe u

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
  {g n m : ℕ} (F : FiniteTypeStructure S g n m)

/-- The compact surface with boundary, with its punctures filled back in. -/
def s31dt_coreSet : Set F.X.carrier := (⋃ j, interior (F.D j))ᶜ

/-- The core carries the subspace topology of the original closed surface. -/
abbrev s31dt_Core := ↥(s31dt_coreSet F)

/-- The actual union of the hole boundaries, regarded as a subset of the core. -/
def s31dt_boundary : Set (s31dt_Core F) :=
  {x | ∃ j, x.val ∈ frontier (F.D j)}

/-- Two points are identified exactly when their core coordinates agree and
they either lie on the same sheet or on an actual hole boundary. -/
def s31dt_rel (x y : Bool × s31dt_Core F) : Prop :=
  x.2 = y.2 ∧ (x.1 = y.1 ∨ x.2 ∈ s31dt_boundary F)

theorem s31dt_rel_refl (x : Bool × s31dt_Core F) : s31dt_rel F x x :=
  ⟨rfl, Or.inl rfl⟩

theorem s31dt_rel_symm {x y : Bool × s31dt_Core F}
    (h : s31dt_rel F x y) : s31dt_rel F y x := by
  refine ⟨h.1.symm, ?_⟩
  rcases h.2 with he | hb
  · exact Or.inl he.symm
  · exact Or.inr (h.1 ▸ hb)

theorem s31dt_rel_trans {x y z : Bool × s31dt_Core F}
    (hxy : s31dt_rel F x y) (hyz : s31dt_rel F y z) : s31dt_rel F x z := by
  refine ⟨hxy.1.trans hyz.1, ?_⟩
  rcases hxy.2 with he | hb
  · rcases hyz.2 with he' | hb'
    · exact Or.inl (he.trans he')
    · exact Or.inr (hxy.1.symm ▸ hb')
  · exact Or.inr hb

def s31dt_setoid : Setoid (Bool × s31dt_Core F) where
  r := s31dt_rel F
  iseqv := ⟨s31dt_rel_refl F, s31dt_rel_symm F, s31dt_rel_trans F⟩

/-- The unique shared carrier, with the usual quotient topology. -/
abbrev s31dt_Double := Quotient (s31dt_setoid F)

def s31dt_mk : Bool × s31dt_Core F → s31dt_Double F :=
  Quotient.mk (s31dt_setoid F)

/-- `false` is the original sheet and `true` is the mirror sheet. -/
def s31dt_side (b : Bool) (x : s31dt_Core F) : s31dt_Double F :=
  s31dt_mk F (b, x)

theorem s31dt_mk_eq_iff (x y : Bool × s31dt_Core F) :
    s31dt_mk F x = s31dt_mk F y ↔ s31dt_rel F x y :=
  ⟨Quotient.exact, fun h => @Quotient.sound _ (s31dt_setoid F) x y h⟩

theorem s31dt_side_eq_iff (b c : Bool) (x y : s31dt_Core F) :
    s31dt_side F b x = s31dt_side F c y ↔
      x = y ∧ (b = c ∨ x ∈ s31dt_boundary F) :=
  s31dt_mk_eq_iff F (b, x) (c, y)

theorem s31dt_side_injective (b : Bool) : Function.Injective (s31dt_side F b) := by
  intro x y h
  exact ((s31dt_side_eq_iff F b b x y).mp h).1

theorem s31dt_opposite_eq_iff (x y : s31dt_Core F) :
    s31dt_side F false x = s31dt_side F true y ↔
      x = y ∧ x ∈ s31dt_boundary F := by
  rw [s31dt_side_eq_iff]
  simp

theorem s31dt_continuous_mk : Continuous (s31dt_mk F) :=
  continuous_quotient_mk'

theorem s31dt_continuous_side (b : Bool) : Continuous (s31dt_side F b) :=
  (s31dt_continuous_mk F).comp (continuous_const.prodMk continuous_id)

/-- The map forgetting which sheet a point came from. -/
def s31dt_project : s31dt_Double F → s31dt_Core F :=
  Quotient.lift Prod.snd (fun _ _ h => h.1)

theorem s31dt_project_side (b : Bool) (x : s31dt_Core F) :
    s31dt_project F (s31dt_side F b x) = x := rfl

theorem s31dt_continuous_project : Continuous (s31dt_project F) :=
  continuous_snd.quotient_lift _

def s31dt_rawFlip (x : Bool × s31dt_Core F) : Bool × s31dt_Core F :=
  (!x.1, x.2)

theorem s31dt_rawFlip_rel {x y : Bool × s31dt_Core F}
    (h : s31dt_rel F x y) :
    s31dt_rel F (s31dt_rawFlip F x) (s31dt_rawFlip F y) := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with he | hb
  · exact Or.inl (congrArg Bool.not he)
  · exact Or.inr hb

def s31dt_flip : s31dt_Double F → s31dt_Double F :=
  Quotient.map' (s31dt_rawFlip F) (fun _ _ h => s31dt_rawFlip_rel F h)

theorem s31dt_flip_side (b : Bool) (x : s31dt_Core F) :
    s31dt_flip F (s31dt_side F b x) = s31dt_side F (!b) x := rfl

theorem s31dt_flip_involutive : Function.Involutive (s31dt_flip F) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  change s31dt_mk F (!(!x.1), x.2) = s31dt_mk F x
  simp

theorem s31dt_continuous_rawFlip : Continuous (s31dt_rawFlip F) :=
  ((continuous_of_discreteTopology : Continuous Bool.not).comp continuous_fst).prodMk
    continuous_snd

theorem s31dt_continuous_flip : Continuous (s31dt_flip F) :=
  (s31dt_continuous_rawFlip F).quotient_map' _

def s31dt_flipHomeomorph : s31dt_Double F ≃ₜ s31dt_Double F where
  toFun := s31dt_flip F
  invFun := s31dt_flip F
  left_inv := s31dt_flip_involutive F
  right_inv := s31dt_flip_involutive F
  continuous_toFun := s31dt_continuous_flip F
  continuous_invFun := s31dt_continuous_flip F

theorem s31dt_flip_fixed_side_iff (b : Bool) (x : s31dt_Core F) :
    s31dt_flip F (s31dt_side F b x) = s31dt_side F b x ↔
      x ∈ s31dt_boundary F := by
  rw [s31dt_flip_side, s31dt_side_eq_iff]
  cases b <;> simp

theorem s31dt_fixed_set : {q | s31dt_flip F q = q} =
    s31dt_side F false '' s31dt_boundary F := by
  ext q
  refine Quotient.inductionOn q ?_
  intro x
  rcases x with ⟨b, x⟩
  change (s31dt_flip F (s31dt_side F b x) = s31dt_side F b x) ↔ _
  constructor
  · intro h
    have hb := (s31dt_flip_fixed_side_iff F b x).mp h
    refine ⟨x, hb, ?_⟩
    exact (s31dt_side_eq_iff F false b x x).mpr ⟨rfl, Or.inr hb⟩
  · rintro ⟨y, hy, he⟩
    change s31dt_side F false y = s31dt_side F b x at he
    rw [← he]
    exact (s31dt_flip_fixed_side_iff F false y).mpr hy

theorem s31dt_side_cover : range (s31dt_side F false) ∪
    range (s31dt_side F true) = univ := by
  apply eq_univ_of_forall
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  rcases x with ⟨b, x⟩
  cases b
  · exact Or.inl ⟨x, rfl⟩
  · exact Or.inr ⟨x, rfl⟩

theorem s31dt_core_closed : IsClosed (s31dt_coreSet F) :=
  (isOpen_iUnion (fun j => isOpen_interior)).isClosed_compl

theorem s31dt_core_compact : CompactSpace (s31dt_Core F) :=
  isCompact_iff_compactSpace.mp (s31dt_core_closed F).isCompact

theorem s31dt_double_compact : CompactSpace (s31dt_Double F) := by
  letI := s31dt_core_compact F
  infer_instance

theorem s31dt_boundary_closed : IsClosed (s31dt_boundary F) := by
  have h : s31dt_boundary F =
      ⋃ j, (Subtype.val : s31dt_Core F → F.X.carrier) ⁻¹' frontier (F.D j) := by
    ext x
    simp only [s31dt_boundary, mem_setOf_eq, mem_iUnion, mem_preimage]
  rw [h]
  exact isClosed_iUnion_of_finite (fun j => isClosed_frontier.preimage continuous_subtype_val)

end LiZhongQC
end


open Set Topology
noncomputable section
namespace LiZhongQC
universe u

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
  {g n m : ℕ} (F : FiniteTypeStructure S g n m)

theorem s31dt_side_isEmbedding (b : Bool) : Topology.IsEmbedding (s31dt_side F b) :=
  Topology.IsEmbedding.of_leftInverse
    (show Function.LeftInverse (s31dt_project F) (s31dt_side F b) from
      s31dt_project_side F b)
    (s31dt_continuous_project F) (s31dt_continuous_side F b)

/-- An open subset of a sheet which avoids the seam remains open in the double. -/
theorem s31dt_open_side_image (b : Bool) {U : Set (s31dt_Core F)}
    (hU : IsOpen U) (hUB : Disjoint U (s31dt_boundary F)) :
    IsOpen (s31dt_side F b '' U) := by
  have heq : s31dt_mk F ⁻¹' (s31dt_side F b '' U) = {b} ×ˢ U := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      have hr := (s31dt_side_eq_iff F b x.1 y x.2).mp he
      have hb : b = x.1 := hr.2.resolve_right (fun h => Set.disjoint_left.mp hUB hy h)
      exact ⟨hb.symm, hr.1 ▸ hy⟩
    · rintro ⟨hb, hx⟩
      refine ⟨x.2, hx, ?_⟩
      exact (s31dt_side_eq_iff F b x.1 x.2 x.2).mpr ⟨rfl, Or.inl hb.symm⟩
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen (s31dt_mk F ⁻¹' (s31dt_side F b '' U))
  rw [heq]
  exact (isOpen_discrete ({b} : Set Bool)).prod hU

theorem s31dt_disjoint_opposite_images {U V : Set (s31dt_Core F)}
    (hUB : Disjoint U (s31dt_boundary F)) :
    Disjoint (s31dt_side F false '' U) (s31dt_side F true '' V) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨x, hx, hxe⟩ ⟨y, hy, hye⟩
  have hr := (s31dt_opposite_eq_iff F x y).mp (hxe.trans hye.symm)
  exact Set.disjoint_left.mp hUB hx hr.2

/-- Hausdorffness is proved on the actual quotient, rather than imposed on it. -/
theorem s31dt_double_t2 : T2Space (s31dt_Double F) := by
  constructor
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x y hne
  by_cases hxy : x.2 = y.2
  · have hxb : x.2 ∉ s31dt_boundary F := by
      intro hb
      exact hne ((s31dt_mk_eq_iff F x y).mpr ⟨hxy, Or.inr hb⟩)
    have hyb : y.2 ∉ s31dt_boundary F := hxy ▸ hxb
    have hbc : x.1 ≠ y.1 := by
      intro he
      exact hne ((s31dt_mk_eq_iff F x y).mpr ⟨hxy, Or.inl he⟩)
    let U := (s31dt_boundary F)ᶜ
    have hU : IsOpen U := (s31dt_boundary_closed F).isOpen_compl
    have hUB : Disjoint U (s31dt_boundary F) := disjoint_compl_left
    refine ⟨s31dt_side F x.1 '' U, s31dt_side F y.1 '' U,
      s31dt_open_side_image F x.1 hU hUB,
      s31dt_open_side_image F y.1 hU hUB, ⟨x.2, hxb, rfl⟩,
      ⟨y.2, hyb, rfl⟩, ?_⟩
    apply Set.disjoint_left.mpr
    rintro z ⟨a, ha, hae⟩ ⟨b, hb, hbe⟩
    have hr := (s31dt_side_eq_iff F x.1 y.1 a b).mp (hae.trans hbe.symm)
    exact hr.2.elim hbc ha
  · obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := t2_separation hxy
    refine ⟨s31dt_project F ⁻¹' U, s31dt_project F ⁻¹' V,
      hU.preimage (s31dt_continuous_project F),
      hV.preimage (s31dt_continuous_project F), hx, hy, ?_⟩
    exact hUV.preimage (s31dt_project F)

theorem s31dt_original_avoids_disc (s : S) (j : Fin m) : F.ι s ∉ F.D j := by
  have hr : F.ι s ∈ range F.ι := mem_range_self s
  rw [F.range_ι] at hr
  intro hj
  exact hr (Or.inr (mem_iUnion.mpr ⟨j, hj⟩))

theorem s31dt_original_mem_core (s : S) : F.ι s ∈ s31dt_coreSet F := by
  intro h
  obtain ⟨j, hj⟩ := mem_iUnion.mp h
  exact s31dt_original_avoids_disc F s j (interior_subset hj)

def s31dt_originalCore (s : S) : s31dt_Core F :=
  ⟨F.ι s, s31dt_original_mem_core F s⟩

theorem s31dt_originalCore_not_boundary (s : S) :
    s31dt_originalCore F s ∉ s31dt_boundary F := by
  rintro ⟨j, hj⟩
  apply s31dt_original_avoids_disc F s j
  have hc := frontier_subset_closure hj
  rwa [(s31eg_disc_compact (F.disc j)).isClosed.closure_eq] at hc

theorem s31dt_originalCore_openEmbedding :
    Topology.IsOpenEmbedding (s31dt_originalCore F) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact F.embedding.continuous.subtype_mk _
  · intro x y h
    exact F.embedding.injective (congrArg Subtype.val h)
  · exact F.embedding.isOpenMap.codRestrict (s31dt_original_mem_core F)

/-- The two actual embeddings of the punctured surface into the shared double. -/
def s31dt_embed (b : Bool) : S → s31dt_Double F :=
  s31dt_side F b ∘ s31dt_originalCore F

theorem s31dt_embed_openEmbedding (b : Bool) :
    Topology.IsOpenEmbedding (s31dt_embed F b) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (s31dt_continuous_side F b).comp
      (s31dt_originalCore_openEmbedding F).continuous
  · exact (s31dt_side_injective F b).comp
      (s31dt_originalCore_openEmbedding F).injective
  · intro U hU
    change IsOpen ((s31dt_side F b ∘ s31dt_originalCore F) '' U)
    rw [image_comp]
    apply s31dt_open_side_image F b ((s31dt_originalCore_openEmbedding F).isOpenMap U hU)
    apply Set.disjoint_left.mpr
    rintro x ⟨s, hs, he⟩ hb
    exact s31dt_originalCore_not_boundary F s (he.symm ▸ hb)

theorem s31dt_embed_disjoint :
    Disjoint (range (s31dt_embed F false)) (range (s31dt_embed F true)) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨s, hs⟩ ⟨t, ht⟩
  have hr := (s31dt_opposite_eq_iff F (s31dt_originalCore F s)
    (s31dt_originalCore F t)).mp (hs.trans ht.symm)
  exact s31dt_originalCore_not_boundary F s hr.2

theorem s31dt_flip_embed (b : Bool) (s : S) :
    s31dt_flip F (s31dt_embed F b s) = s31dt_embed F (!b) s := rfl

end LiZhongQC
end
