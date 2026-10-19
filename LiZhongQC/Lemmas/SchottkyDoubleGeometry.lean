/- Mechanically assembled round78 proof; see BUNDLE_MAP.json. -/
import LiZhongQC.Lemmas.FiniteTypeUniqueness
import LiZhongQC.Lemmas.SchottkyDoubleCarrier

/- BEGIN SchottkyHalfGeometry | SHA256 f10e3c6e71d3542f94fba9e8c1c4c0f30d1ff21af16618008f190829900bdf17 -/
section round78_block_01

open Set Filter Topology
open scoped Manifold ContDiff

noncomputable section
namespace LiZhongQC

universe u

/-- The original surface avoids every deleted closed disc. -/
theorem s31sd_range_avoids_discs {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    (s : S) (j : Fin m) : F.ι s ∉ F.D j := by
  have hs : F.ι s ∈ range F.ι := mem_range_self s
  rw [F.range_ι] at hs
  exact fun hj => hs (Or.inr (mem_iUnion.2 ⟨j, hj⟩))

/-- Filled punctures are disjoint from all deleted closed discs. -/
theorem s31sd_puncture_avoids_discs {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    {p : F.X.carrier} (hp : p ∈ F.P) (j : Fin m) : p ∉ F.D j := by
  intro hj
  exact Set.disjoint_left.1 (F.disjoint_P j) hj hp

/-- Filling the punctures and retaining each boundary produces a compact half. -/
theorem s31sd_half_compact {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) :
    IsCompact ((⋃ j, interior (F.D j))ᶜ) := by
  exact (isOpen_iUnion (fun j => isOpen_interior)).isClosed_compl.isCompact

/-- The compact half is exactly the original open surface, filled punctures,
and boundary circles. This uses the actual presentation, not extra cover data. -/
theorem s31sd_half_partition {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) :
    (⋃ j, interior (F.D j))ᶜ =
      range F.ι ∪ (↑F.P : Set F.X.carrier) ∪ ⋃ j, frontier (F.D j) := by
  classical
  have hclosed : ∀ j, IsClosed (F.D j) := fun j =>
    (s31eg_disc_compact (F.disc j)).isClosed
  ext x
  constructor
  · intro hx
    by_cases hP : x ∈ F.P
    · exact Or.inl (Or.inr hP)
    · by_cases hD : ∃ j, x ∈ F.D j
      · obtain ⟨j, hj⟩ := hD
        refine Or.inr (mem_iUnion.2 ⟨j, ?_⟩)
        rw [frontier, (hclosed j).closure_eq]
        exact ⟨hj, fun hi => hx (mem_iUnion.2 ⟨j, hi⟩)⟩
      · refine Or.inl (Or.inl ?_)
        rw [F.range_ι]
        intro h
        rcases h with h | h
        · exact hP h
        · exact hD (mem_iUnion.1 h)
  · intro hx hi
    obtain ⟨j, hj⟩ := mem_iUnion.1 hi
    rcases hx with (hx | hx) | hx
    · obtain ⟨s, rfl⟩ := hx
      exact s31sd_range_avoids_discs F s j (interior_subset hj)
    · exact s31sd_puncture_avoids_discs F hx j (interior_subset hj)
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hx
      have hkD : x ∈ F.D k := by
        exact (hclosed k).closure_eq ▸ frontier_subset_closure hk
      by_cases hkj : k = j
      · subst k
        exact hk.2 hj
      · exact Set.disjoint_left.1 (F.disjoint hkj) hkD (interior_subset hj)

/-- Filled punctures never lie on the gluing boundary. -/
theorem s31sd_punctures_disjoint_boundary {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) :
    Disjoint (↑F.P : Set F.X.carrier) (⋃ j, frontier (F.D j)) := by
  apply Set.disjoint_left.2
  intro p hp hboundary
  obtain ⟨j, hj⟩ := mem_iUnion.1 hboundary
  have hjD : p ∈ F.D j := by
    exact (s31eg_disc_compact (F.disc j)).isClosed.closure_eq ▸
      frontier_subset_closure hj
  exact s31sd_puncture_avoids_discs F hp j hjD

/-- Every filled puncture is approached by the original embedded surface. -/
theorem s31sd_puncture_mem_closure {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    {p : F.X.carrier} (hp : p ∈ F.P) : p ∈ closure (range F.ι) := by
  have hclosed : IsClosed (⋃ j, F.D j) :=
    isClosed_iUnion_of_finite (fun j => (s31eg_disc_compact (F.disc j)).isClosed)
  have hpD : p ∉ ⋃ j, F.D j := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.1 h
    exact s31sd_puncture_avoids_discs F hp j hj
  have htrace := s31fu_puncture_trace_neBot F.ι F.P hclosed F.range_ι hpD
  apply mem_closure_iff.2
  intro U hU hpU
  obtain ⟨s, hs⟩ := comap_neBot_iff.1 htrace U (hU.mem_nhds hpU)
  exact ⟨F.ι s, hs, mem_range_self s⟩

/-- Restricting the target of an open embedding to any containing subspace
preserves the open embedding. The containing subspace need not be open. -/
theorem s31sd_embedding_into_half {A X : Type*} [TopologicalSpace A]
    [TopologicalSpace X] (i : A → X) (hi : Topology.IsOpenEmbedding i)
    (C : Set X) (hC : ∀ a, i a ∈ C) :
    Topology.IsOpenEmbedding (fun a => (⟨i a, hC a⟩ : C)) := by
  let j : A → C := fun a => ⟨i a, hC a⟩
  have hj : Topology.IsEmbedding j :=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.1 hi.isEmbedding
  refine ⟨hj, ?_⟩
  have hr : range j = Subtype.val ⁻¹' range i := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact mem_range_self a
    · rintro ⟨a, ha⟩
      exact ⟨a, Subtype.ext ha⟩
  change IsOpen (range j)
  rw [hr]
  exact hi.isOpen_range.preimage continuous_subtype_val

end LiZhongQC
end -- close original anonymous noncomputable section
end round78_block_01
/- END SchottkyHalfGeometry -/

/- BEGIN SchottkyMarkedPoints | SHA256 01e6647151af49b5a3f18487164e8519edc37e805c0464149e3d233d9ea13987 -/
section round78_block_02

open Set

noncomputable section
namespace LiZhongQC

/-- The two reflected copies of a finite set give an actual invariant finite
set, with twice the cardinality and no fixed points. In applications `A` is
the subtype `F.P` and `a` is the positive quotient inclusion of that subtype. -/
theorem s31sd_marked_points {A Y : Type*} [Fintype A] [TopologicalSpace Y]
    (J : Y ≃ₜ Y) (hJ : ∀ y, J (J y) = y) (a : A → Y)
    (ha : Function.Injective a) (hsep : ∀ p q, a p ≠ J (a q)) :
    ∃ Pd : Finset Y,
      (↑Pd : Set Y) = range a ∪ range (J ∘ a) ∧
      Pd.card = 2 * Fintype.card A ∧
      J '' (↑Pd : Set Y) = ↑Pd ∧
      Disjoint (↑Pd : Set Y) {y | J y = y} := by
  classical
  let PPlus : Finset Y := Finset.univ.image a
  let PMinus : Finset Y := Finset.univ.image (J ∘ a)
  have hplus : (↑PPlus : Set Y) = range a := by
    ext y
    simp only [PPlus, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and,
      Set.mem_range]
  have hminus : (↑PMinus : Set Y) = range (J ∘ a) := by
    ext y
    simp only [PMinus, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and,
      Set.mem_range]
  have hdisj : Disjoint PPlus PMinus := by
    apply Finset.disjoint_left.2
    intro y hyPlus hyMinus
    have hyPlus' : y ∈ range a := hplus ▸ hyPlus
    have hyMinus' : y ∈ range (J ∘ a) := hminus ▸ hyMinus
    obtain ⟨p, hp⟩ := hyPlus'
    obtain ⟨q, hq⟩ := hyMinus'
    exact hsep p q (hp.trans hq.symm)
  have hcardPlus : PPlus.card = Fintype.card A := by
    exact (Finset.card_image_of_injective Finset.univ ha).trans Finset.card_univ
  have hcardMinus : PMinus.card = Fintype.card A := by
    exact (Finset.card_image_of_injective Finset.univ (J.injective.comp ha)).trans
      Finset.card_univ
  have hr : (↑(PPlus ∪ PMinus) : Set Y) = range a ∪ range (J ∘ a) := by
    rw [Finset.coe_union, hplus, hminus]
  refine ⟨PPlus ∪ PMinus, hr, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hcardPlus, hcardMinus]
    omega
  · rw [hr]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with hz | hz
      · obtain ⟨p, rfl⟩ := hz
        exact Or.inr ⟨p, rfl⟩
      · obtain ⟨p, rfl⟩ := hz
        exact Or.inl ⟨p, (hJ (a p)).symm⟩
    · intro hy
      rcases hy with hy | hy
      · obtain ⟨p, rfl⟩ := hy
        exact ⟨J (a p), Or.inr ⟨p, rfl⟩, hJ (a p)⟩
      · obtain ⟨p, rfl⟩ := hy
        exact ⟨a p, Or.inl ⟨p, rfl⟩, rfl⟩
  · rw [hr]
    apply Set.disjoint_left.2
    intro y hy hfix
    rcases hy with hy | hy
    · obtain ⟨p, rfl⟩ := hy
      exact hsep p p hfix.symm
    · obtain ⟨p, rfl⟩ := hy
      have heq : a p = J (a p) := (hJ (a p)).symm.trans hfix
      exact hsep p p heq

/-- Any set disjoint from both copies of the punctures is disjoint from the
constructed marked-point set. -/
theorem s31sd_marked_points_disjoint {A Y : Type*} [TopologicalSpace Y]
    (J : Y ≃ₜ Y) (a : A → Y) (Pd : Finset Y)
    (hPd : (↑Pd : Set Y) = range a ∪ range (J ∘ a)) (U : Set Y)
    (hplus : Disjoint U (range a)) (hminus : Disjoint U (range (J ∘ a))) :
    Disjoint U (↑Pd : Set Y) := by
  rw [hPd]
  exact disjoint_union_right.2 ⟨hplus, hminus⟩

end LiZhongQC
end -- close original anonymous noncomputable section
end round78_block_02
/- END SchottkyMarkedPoints -/

/- BEGIN SchottkyDoubleOpenCover | SHA256 008d07ea0d10e6ca8f8af78fa74e3cfe8e3559bc4b398a4ee4824b9892a64d50 -/
section round78_block_03

open Set Topology

noncomputable section
namespace LiZhongQC

universe u

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
  {g n m : ℕ} (F : FiniteTypeStructure S g n m)

/-- Thickening one closed half by the two-sheeted inverse image of any open
boundary neighborhood gives an open subset of the actual quotient double.
This does not need a Hausdorff instance or an analytic double atlas. -/
theorem s31sd_thickened_half_open (N : Set (s31dt_Core F)) (hN : IsOpen N)
    (hBN : s31dt_boundary F ⊆ N) (b : Bool) :
    IsOpen (range (s31dt_side F b) ∪ s31dt_project F ⁻¹' N) := by
  have hq : Topology.IsQuotientMap (s31dt_mk F) := isQuotientMap_quotient_mk'
  apply hq.1.isOpen_preimage.1
  have hpre : s31dt_mk F ⁻¹'
      (range (s31dt_side F b) ∪ s31dt_project F ⁻¹' N) =
      (Prod.fst ⁻¹' ({b} : Set Bool)) ∪ Prod.snd ⁻¹' N := by
    ext x
    change ((∃ y, s31dt_side F b y = s31dt_side F x.1 x.2) ∨ x.2 ∈ N) ↔
      (x.1 = b ∨ x.2 ∈ N)
    constructor
    · intro hx
      rcases hx with hx | hx
      · obtain ⟨y, hy⟩ := hx
        obtain ⟨hyx, hb⟩ := (s31dt_side_eq_iff F b x.1 y x.2).1 hy
        rcases hb with hb | hb
        · exact Or.inl hb.symm
        · exact Or.inr (hBN (hyx ▸ hb))
      · exact Or.inr hx
    · intro hx
      rcases hx with hx | hx
      · exact Or.inl ⟨x.2, (s31dt_side_eq_iff F b x.1 x.2 x.2).2
          ⟨rfl, Or.inl hx.symm⟩⟩
      · exact Or.inr hx
  rw [hpre]
  exact ((isOpen_discrete ({b} : Set Bool)).preimage continuous_fst).union
    (hN.preimage continuous_snd)

/-- The intersection of the two closed sheets projects to the actual seam. -/
theorem s31sd_sides_inter_subset_seam :
    range (s31dt_side F false) ∩ range (s31dt_side F true) ⊆
      s31dt_project F ⁻¹' s31dt_boundary F := by
  intro q hq
  obtain ⟨x, hx⟩ := hq.1
  obtain ⟨y, hy⟩ := hq.2
  have hxy := (s31dt_opposite_eq_iff F x y).1 (hx.trans hy.symm)
  rw [← hx]
  exact hxy.2

/-- An explicit two-set open cover of the double. Its intersection is exactly
the doubled boundary neighborhood, retaining all boundary components.

For a fundamental-group computation `N` must subsequently be chosen as a
disjoint union of actual collars. In general the intersection is disconnected;
this theorem does not assert the connected-intersection van Kampen hypotheses. -/
theorem s31sd_double_open_cover (N : Set (s31dt_Core F)) (hN : IsOpen N)
    (hBN : s31dt_boundary F ⊆ N) :
    ∃ U V : Set (s31dt_Double F),
      U = range (s31dt_side F false) ∪ s31dt_project F ⁻¹' N ∧
      V = range (s31dt_side F true) ∪ s31dt_project F ⁻¹' N ∧
      IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧
      U ∩ V = s31dt_project F ⁻¹' N := by
  let W := s31dt_project F ⁻¹' N
  let U := range (s31dt_side F false) ∪ W
  let V := range (s31dt_side F true) ∪ W
  refine ⟨U, V, rfl, rfl, s31sd_thickened_half_open F N hN hBN false,
    s31sd_thickened_half_open F N hN hBN true, ?_, ?_⟩
  · apply eq_univ_of_forall
    intro q
    have hq : q ∈ range (s31dt_side F false) ∪ range (s31dt_side F true) := by
      rw [s31dt_side_cover F]
      exact mem_univ q
    rcases hq with hq | hq
    · exact Or.inl (Or.inl hq)
    · exact Or.inr (Or.inl hq)
  · ext q
    constructor
    · intro hq
      rcases hq.1 with hl | hw
      · rcases hq.2 with hr | hw
        · exact hBN (s31sd_sides_inter_subset_seam F ⟨hl, hr⟩)
        · exact hw
      · exact hw
    · intro hw
      exact ⟨Or.inr hw, Or.inr hw⟩

end LiZhongQC
end -- close original anonymous noncomputable section
end round78_block_03
/- END SchottkyDoubleOpenCover -/

/- BEGIN SchottkyConcreteMarkedPoints | SHA256 8b505e5c728f336e3799cd5f6c51fd55f5813cf3f5f19eefbc05f3dc03e9b914 -/
section round78_block_04

open Set Topology

noncomputable section
namespace LiZhongQC

universe u

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
  {g n m : ℕ} (F : FiniteTypeStructure S g n m)

/-- The original embedding lands in the actual filled core. -/
theorem s31sd_surface_core_mem (s : S) : F.ι s ∈ s31dt_coreSet F := by
  intro hs
  obtain ⟨j, hj⟩ := mem_iUnion.1 hs
  exact s31sd_range_avoids_discs F s j (interior_subset hj)

/-- A marked puncture determines a point of the actual filled core. -/
theorem s31sd_puncture_core_mem (p : F.P) : p.val ∈ s31dt_coreSet F := by
  intro hp
  obtain ⟨j, hj⟩ := mem_iUnion.1 hp
  exact s31sd_puncture_avoids_discs F p.property j (interior_subset hj)

/-- Construct the two actual quotient copies of the punctures, with the exact
cardinality and invariance required by the original Schottky-double statement. -/
theorem s31sd_concrete_marked_points :
    ∃ Pd : Finset (s31dt_Double F),
      (↑Pd : Set (s31dt_Double F)) =
        s31dt_side F false '' {x : s31dt_Core F | x.val ∈ F.P} ∪
        s31dt_side F true '' {x : s31dt_Core F | x.val ∈ F.P} ∧
      Pd.card = 2 * n ∧
      s31dt_flipHomeomorph F '' (↑Pd : Set (s31dt_Double F)) = ↑Pd ∧
      Disjoint (↑Pd : Set (s31dt_Double F)) {q | s31dt_flip F q = q} := by
  classical
  let a : F.P → s31dt_Core F := fun p => ⟨p.val, s31sd_puncture_core_mem F p⟩
  let b : F.P → s31dt_Double F := s31dt_side F false ∘ a
  have ha : Function.Injective a := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun x : s31dt_Core F => x.val) hpq
  have hb : Function.Injective b := (s31dt_side_injective F false).comp ha
  have hsep : ∀ p q, b p ≠ s31dt_flipHomeomorph F (b q) := by
    intro p q heq
    change s31dt_side F false (a p) = s31dt_side F true (a q) at heq
    have hboundary := ((s31dt_opposite_eq_iff F (a p) (a q)).1 heq).2
    obtain ⟨j, hj⟩ := hboundary
    have hjD : p.val ∈ F.D j := by
      exact (s31eg_disc_compact (F.disc j)).isClosed.closure_eq ▸
        frontier_subset_closure hj
    exact s31sd_puncture_avoids_discs F p.property j hjD
  obtain ⟨Pd, hPd, hcard, hinv, hfix⟩ := s31sd_marked_points
    (s31dt_flipHomeomorph F) (s31dt_flip_involutive F) b hb hsep
  have hplus : range b =
      s31dt_side F false '' {x : s31dt_Core F | x.val ∈ F.P} := by
    ext q
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨a p, p.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x.val, hx⟩, ?_⟩
      apply congrArg (s31dt_side F false)
      exact Subtype.ext rfl
  have hminus : range (s31dt_flipHomeomorph F ∘ b) =
      s31dt_side F true '' {x : s31dt_Core F | x.val ∈ F.P} := by
    ext q
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨a p, p.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x.val, hx⟩, ?_⟩
      change s31dt_side F true (a ⟨x.val, hx⟩) = s31dt_side F true x
      apply congrArg (s31dt_side F true)
      exact Subtype.ext rfl
  refine ⟨Pd, hPd.trans (congrArg₂ (fun U V => U ∪ V) hplus hminus), ?_, hinv, hfix⟩
  rw [hcard, Fintype.card_coe, F.card_P]

/-- Coverage of the concrete double follows from the proved half partition.
The embedding is the actual positive quotient inclusion of the original map;
the supplied equation only allows the caller's chosen name for that function. -/
theorem s31sd_concrete_cover (i : S → s31dt_Double F)
    (hi : ∀ s, i s = s31dt_side F false
      ⟨F.ι s, s31sd_surface_core_mem F s⟩)
    (Pd : Finset (s31dt_Double F))
    (hPd : (↑Pd : Set (s31dt_Double F)) =
      s31dt_side F false '' {x : s31dt_Core F | x.val ∈ F.P} ∪
      s31dt_side F true '' {x : s31dt_Core F | x.val ∈ F.P}) :
    range i ∪ range (s31dt_flipHomeomorph F ∘ i) ∪
      {q | s31dt_flipHomeomorph F q = q} ∪ ↑Pd = univ := by
  apply eq_univ_of_forall
  intro q
  refine Quotient.inductionOn q ?_
  intro z
  rcases z with ⟨b, x⟩
  have hx : x.val ∈ range F.ι ∪ (↑F.P : Set F.X.carrier) ∪
      ⋃ j, frontier (F.D j) := by
    rw [← s31sd_half_partition F]
    exact x.property
  change s31dt_side F b x ∈ _
  rcases hx with (hx | hx) | hx
  · obtain ⟨s, hs⟩ := hx
    have hsx : (⟨F.ι s, s31sd_surface_core_mem F s⟩ : s31dt_Core F) = x :=
      Subtype.ext hs
    cases b
    · exact Or.inl (Or.inl (Or.inl ⟨s, (hi s).trans
        (congrArg (s31dt_side F false) hsx)⟩))
    · refine Or.inl (Or.inl (Or.inr ⟨s, ?_⟩))
      change s31dt_flip F (i s) = s31dt_side F true x
      rw [hi s, s31dt_flip_side]
      exact congrArg (s31dt_side F true) hsx
  · apply Or.inr
    rw [hPd]
    cases b
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  · apply Or.inl
    apply Or.inr
    exact (s31dt_flip_fixed_side_iff F b x).2 (mem_iUnion.1 hx)

end LiZhongQC
end -- close original anonymous noncomputable section
end round78_block_04
/- END SchottkyConcreteMarkedPoints -/
