import LiZhongQC.Lemmas.Conformal
import LiZhongQC.Lemmas.ConnectedComplement

/-!
# Theorem 2.1, the degenerate cases (i) and (ii)

Theorem 2.1 of the book (`thm2_1_canonical_form`, S02) says a doubly connected domain `B` is
conformally equivalent to `ℂ ∖ {0}`, to `{0 < |z| < 1}` or to an annulus.  This file proves the
cases in which a component of `ℂ̄ ∖ B` is a single point, following the book (§2.1):

* **Topology** (`exists_compl_eq_union_components`, `isClosed_connectedComponentIn_compl_toExt`,
  `fill_component`): `ℂ̄ ∖ B` is the union of the component of `∞` and one other component `E`, and
  `B ∪ E` is a domain whose complement in `ℂ̄` is the component of `∞` — so it is connected, and
  `hasHolomorphicSqrt_of_isConnected_compl` together with the Riemann mapping theorem applies.
* **Case (i)** (`canonical_form_of_two_points`): both components are points, `B = ℂ ∖ {p}`.
* **Case (ii)** (`canonical_form_of_one_point`): exactly one component is a point.  If it is a
  finite point `p`, map `B ∪ {p}` onto the disc with `p ↦ 0`
  (`conformallyEquivalent_diff_singleton_puncturedDisc`); if it is `∞`, first invert about a point
  of the other component (`inversion_compl_domain`).
* `canonical_form_of_degenerate_component` combines the two cases.

Case (iii), two nondegenerate components, still needs the construction of the annulus map and is
not treated here.
-/

open Complex Set Metric Filter Topology

noncomputable section

namespace LiZhongQC

/-! ### Basic facts -/

theorem coe_mem_toExt_iff {S : Set ℂ} {z : ℂ} : (z : ExtPlane) ∈ toExt S ↔ z ∈ S :=
  OnePoint.coe_injective.mem_set_image

theorem extInf_notMem_toExt (S : Set ℂ) : extInf ∉ toExt S := OnePoint.infty_notMem_image_coe

theorem extInf_mem_compl_toExt (S : Set ℂ) : extInf ∈ (toExt S)ᶜ := extInf_notMem_toExt S

theorem coe_mem_compl_toExt_iff {S : Set ℂ} {z : ℂ} : (z : ExtPlane) ∈ (toExt S)ᶜ ↔ z ∉ S := by
  rw [mem_compl_iff, coe_mem_toExt_iff]

theorem preimage_coe_toExt (S : Set ℂ) : ((↑) : ℂ → ExtPlane) ⁻¹' toExt S = S :=
  Set.preimage_image_eq S OnePoint.coe_injective

theorem toExt_union (S T : Set ℂ) : toExt (S ∪ T) = toExt S ∪ toExt T := Set.image_union _ _ _

theorem isOpen_toExt_iff {S : Set ℂ} : IsOpen (toExt S) ↔ IsOpen S := OnePoint.isOpen_image_coe

theorem isClosed_compl_toExt {S : Set ℂ} (hS : IsOpen S) : IsClosed (toExt S)ᶜ :=
  (isOpen_toExt_iff.mpr hS).isClosed_compl

/-- `ℂ̄ ∖ S` is `(ℂ ∖ S) ∪ {∞}`. -/
theorem compl_toExt (S : Set ℂ) : (toExt S)ᶜ = toExt Sᶜ ∪ {extInf} := by
  ext y
  induction y using OnePoint.rec with
  | infty => exact iff_of_true (extInf_mem_compl_toExt S) (Or.inr rfl)
  | coe z =>
    rw [coe_mem_compl_toExt_iff, mem_union, coe_mem_toExt_iff, mem_compl_iff, mem_singleton_iff]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · exact absurd h (OnePoint.coe_ne_infty z)

/-- Two connected components of a set are equal or disjoint. -/
theorem connectedComponentIn_eq_or_disjoint {α : Type*} [TopologicalSpace α] {F : Set α}
    (x y : α) :
    connectedComponentIn F x = connectedComponentIn F y ∨
      Disjoint (connectedComponentIn F x) (connectedComponentIn F y) := by
  by_cases h : Disjoint (connectedComponentIn F x) (connectedComponentIn F y)
  · exact Or.inr h
  · left
    rw [Set.not_disjoint_iff] at h
    obtain ⟨z, hzx, hzy⟩ := h
    rw [connectedComponentIn_eq hzx, connectedComponentIn_eq hzy]

/-- `∞` is a limit point of `ℂ ∖ A` in `ℂ̄` when `A` is bounded. -/
theorem extInf_mem_closure_toExt_compl_of_isBounded {A : Set ℂ} (hA : Bornology.IsBounded A) :
    extInf ∈ closure (toExt Aᶜ) := by
  rw [mem_closure_iff_nhds_basis OnePoint.hasBasis_nhds_infty]
  rintro s ⟨-, hs⟩
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hs.isBounded
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.1 hA
  set M : ℝ := |R| + |r| + 1 with hM
  have hMpos : 0 < M := by positivity
  have hnorm : ‖((M : ℝ) : ℂ)‖ = M := by rw [Complex.norm_real, Real.norm_of_nonneg hMpos.le]
  refine ⟨((M : ℂ) : ExtPlane), ⟨(M : ℂ), ?_, rfl⟩, Or.inl ⟨(M : ℂ), ?_, rfl⟩⟩
  · intro hmem
    have h := hr _ hmem
    rw [hnorm] at h
    linarith [le_abs_self r, abs_nonneg R]
  · intro hmem
    have h := hR _ hmem
    rw [hnorm] at h
    linarith [le_abs_self R, abs_nonneg r]

/-- For bounded `A` with connected complement, `ℂ̄ ∖ A` is connected. -/
theorem isPreconnected_compl_toExt {A : Set ℂ} (hA : Bornology.IsBounded A)
    (hAc : IsPreconnected Aᶜ) : IsPreconnected (toExt A)ᶜ := by
  rw [compl_toExt]
  have h1 : IsPreconnected (toExt Aᶜ) := hAc.image _ OnePoint.continuous_coe.continuousOn
  refine h1.subset_closure subset_union_left ?_
  exact union_subset subset_closure
    (singleton_subset_iff.2 (extInf_mem_closure_toExt_compl_of_isBounded hA))

/-! ### The complement of a doubly connected domain -/

/-- The complement `ℂ̄ ∖ B` of a doubly connected domain is the union of the component of `∞` and
one other component. -/
theorem exists_compl_eq_union_components {B : Set ℂ} (hB : IsDoublyConnected B) :
    ∃ x ∈ (toExt B)ᶜ,
      connectedComponentIn (toExt B)ᶜ x ≠ connectedComponentIn (toExt B)ᶜ extInf ∧
        (toExt B)ᶜ = connectedComponentIn (toExt B)ᶜ x ∪ connectedComponentIn (toExt B)ᶜ extInf := by
  have hinf : extInf ∈ (toExt B)ᶜ := extInf_mem_compl_toExt B
  obtain ⟨c₁, c₂, hne, huniv⟩ := Nat.card_eq_two_iff.mp hB.2.2
  have hmem : ∀ c : ConnectedComponents ↥(toExt B)ᶜ, c = c₁ ∨ c = c₂ := by
    intro c
    have h : c ∈ ({c₁, c₂} : Set (ConnectedComponents ↥(toExt B)ᶜ)) := by
      rw [huniv]; exact mem_univ c
    simpa only [mem_insert_iff, mem_singleton_iff] using h
  set pinf : ↥(toExt B)ᶜ := ⟨extInf, hinf⟩ with hpinf
  -- the class of some point differs from the class of `∞`
  obtain ⟨c, hc⟩ : ∃ c : ConnectedComponents ↥(toExt B)ᶜ, c ≠ ConnectedComponents.mk pinf := by
    rcases hmem (ConnectedComponents.mk pinf) with h | h
    · exact ⟨c₂, by rw [h]; exact hne.symm⟩
    · exact ⟨c₁, by rw [h]; exact hne⟩
  -- with only two classes, every class other than that of `∞` is `c`
  have key : ∀ d : ConnectedComponents ↥(toExt B)ᶜ, d ≠ ConnectedComponents.mk pinf → d = c := by
    intro d hd
    rcases hmem d with h1 | h1 <;> rcases hmem (ConnectedComponents.mk pinf) with h2 | h2 <;>
      rcases hmem c with h3 | h3
    all_goals first
      | exact absurd (h1.trans h2.symm) hd
      | exact absurd (h3.trans h2.symm) hc
      | exact h1.trans h3.symm
  obtain ⟨q, rfl⟩ := ConnectedComponents.surjective_coe c
  refine ⟨q.1, q.2, ?_, ?_⟩
  · intro heq
    apply hc
    rw [ConnectedComponents.coe_eq_coe]
    rw [connectedComponentIn_eq_image q.2, connectedComponentIn_eq_image hinf] at heq
    exact Set.image_injective.mpr Subtype.val_injective heq
  · apply Subset.antisymm
    · intro y hy
      by_cases hyc :
          ConnectedComponents.mk (⟨y, hy⟩ : ↥(toExt B)ᶜ) = ConnectedComponents.mk pinf
      · right
        rw [ConnectedComponents.coe_eq_coe, connectedComponent_eq_iff_mem] at hyc
        rw [connectedComponentIn_eq_image hinf]
        exact ⟨⟨y, hy⟩, hyc, rfl⟩
      · left
        have h := key _ hyc
        rw [ConnectedComponents.coe_eq_coe, connectedComponent_eq_iff_mem] at h
        rw [connectedComponentIn_eq_image q.2]
        exact ⟨⟨y, hy⟩, h, rfl⟩
    · exact union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)

/-- For an open `B ⊆ ℂ`, the components of `ℂ̄ ∖ B` are closed in `ℂ̄`. -/
theorem isClosed_connectedComponentIn_compl_toExt {B : Set ℂ} (hB : IsOpen B) (x : ExtPlane) :
    IsClosed (connectedComponentIn (toExt B)ᶜ x) := by
  by_cases hx : x ∈ (toExt B)ᶜ
  · rw [connectedComponentIn_eq_image hx]
    exact (isClosed_compl_toExt hB).isClosedEmbedding_subtypeVal.isClosedMap _
      isClosed_connectedComponent
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

/-- **Filling a component** (the step "`B ∪ C₂` is simply connected" of the book): if `E` is the
component of `ℂ̄ ∖ B` not containing `∞`, then `B ∪ E` is a domain in `ℂ` whose complement in `ℂ̄`
is the component of `∞`. -/
theorem fill_component {B : Set ℂ} (hB : IsDoublyConnected B) {x : ExtPlane}
    (hx : x ∈ (toExt B)ᶜ)
    (hne : connectedComponentIn (toExt B)ᶜ x ≠ connectedComponentIn (toExt B)ᶜ extInf) :
    IsOpen (B ∪ {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x}) ∧
      IsConnected (B ∪ {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x}) ∧
      (toExt (B ∪ {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x}))ᶜ =
        connectedComponentIn (toExt B)ᶜ extInf := by
  set A : Set ℂ := {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x} with hA
  have hinf : extInf ∈ (toExt B)ᶜ := extInf_mem_compl_toExt B
  have hBo : IsOpen B := hB.1
  have hBc : IsConnected B := hB.2.1
  -- the two components are disjoint, so `∞` is not in the component of `x`
  have hdisj : Disjoint (connectedComponentIn (toExt B)ᶜ x) (connectedComponentIn (toExt B)ᶜ extInf) :=
    (connectedComponentIn_eq_or_disjoint x extInf).resolve_left hne
  have hinfE : extInf ∉ connectedComponentIn (toExt B)ᶜ x :=
    fun h => Set.disjoint_left.mp hdisj h (mem_connectedComponentIn hinf)
  -- `ℂ̄ ∖ B` is the union of the two components
  have hcover : (toExt B)ᶜ =
      connectedComponentIn (toExt B)ᶜ x ∪ connectedComponentIn (toExt B)ᶜ extInf := by
    obtain ⟨x', hx', hne', hK'⟩ := exists_compl_eq_union_components hB
    have hxE' : x ∈ connectedComponentIn (toExt B)ᶜ x' := by
      have h : x ∈ connectedComponentIn (toExt B)ᶜ x' ∪ connectedComponentIn (toExt B)ᶜ extInf :=
        hK' ▸ hx
      rcases h with h | h
      · exact h
      · exact absurd (connectedComponentIn_eq h).symm hne
    rw [connectedComponentIn_eq hxE'] at hK'
    exact hK'
  -- the component of `x` is the image of `A`
  have hEA : toExt A = connectedComponentIn (toExt B)ᶜ x := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hz
    · intro y hy
      have hyinf : y ≠ extInf := fun h => hinfE (h ▸ hy)
      obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hyinf
      exact ⟨z, hy, rfl⟩
  -- (c) the complement of `toExt (B ∪ A)` is the component of `∞`
  have hcompl : (toExt (B ∪ A))ᶜ = connectedComponentIn (toExt B)ᶜ extInf := by
    rw [toExt_union, hEA, Set.compl_union]
    apply Subset.antisymm
    · rintro y ⟨hyK, hyE⟩
      have h : y ∈ connectedComponentIn (toExt B)ᶜ x ∪ connectedComponentIn (toExt B)ᶜ extInf :=
        hcover ▸ hyK
      exact h.resolve_left hyE
    · intro y hy
      exact ⟨connectedComponentIn_subset _ _ hy, fun hyE => Set.disjoint_left.mp hdisj hyE hy⟩
  -- (a) `B ∪ A` is open
  have hopen : IsOpen (B ∪ A) := by
    rw [← preimage_coe_toExt (B ∪ A)]
    refine OnePoint.continuous_coe.isOpen_preimage _ ?_
    rw [← compl_compl (toExt (B ∪ A)), hcompl]
    exact (isClosed_connectedComponentIn_compl_toExt hBo extInf).isOpen_compl
  -- `A` is nonempty, connected and compact
  have hEconn : IsConnected (connectedComponentIn (toExt B)ᶜ x) :=
    isConnected_connectedComponentIn_iff.mpr hx
  have hAne : A.Nonempty := by
    have hxinf : x ≠ extInf := fun h => hne (by rw [h])
    obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hxinf
    exact ⟨z, mem_connectedComponentIn hx⟩
  have hAconn : IsConnected A := by
    refine ⟨hAne, ?_⟩
    rw [← OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image]
    show IsPreconnected (toExt A)
    rw [hEA]
    exact hEconn.isPreconnected
  have hAcpt : IsCompact A := by
    rw [OnePoint.isOpenEmbedding_coe.isInducing.isCompact_iff]
    show IsCompact (toExt A)
    rw [hEA]
    exact (isClosed_connectedComponentIn_compl_toExt hBo x).isCompact
  have hAB : ∀ z ∈ A, z ∉ B := fun z hz hzB =>
    connectedComponentIn_subset _ _ hz ⟨z, hzB, rfl⟩
  -- (b) `B ∪ A` is connected: otherwise `A` would be a nonempty clopen subset of `ℂ`
  have hconn : IsConnected (B ∪ A) := by
    refine ⟨hBc.nonempty.mono subset_union_left, ?_⟩
    rw [isPreconnected_iff_subset_of_disjoint]
    intro u v hu hv hsuv hdis
    have hB' : B ⊆ u ∨ B ⊆ v :=
      (isPreconnected_iff_subset_of_disjoint.mp hBc.isPreconnected) u v hu hv
        (subset_union_left.trans hsuv)
        (Set.eq_empty_of_subset_empty
          (hdis ▸ Set.inter_subset_inter_left _ subset_union_left))
    have hA' : A ⊆ u ∨ A ⊆ v :=
      (isPreconnected_iff_subset_of_disjoint.mp hAconn.isPreconnected) u v hu hv
        (subset_union_right.trans hsuv)
        (Set.eq_empty_of_subset_empty
          (hdis ▸ Set.inter_subset_inter_left _ subset_union_right))
    have key : ∀ u v : Set ℂ, IsOpen v → (B ∪ A) ∩ (u ∩ v) = ∅ → B ⊆ u → A ⊆ v → False := by
      intro u v hv hdis hBu hAv
      have hAeq : A = (B ∪ A) ∩ v := by
        apply Subset.antisymm
        · exact fun z hz => ⟨Or.inr hz, hAv hz⟩
        · rintro z ⟨hz, hzv⟩
          rcases hz with hzB | hzA
          · exfalso
            have h : z ∈ (B ∪ A) ∩ (u ∩ v) := ⟨Or.inl hzB, hBu hzB, hzv⟩
            rw [hdis] at h
            exact h
          · exact hzA
      have hAopen : IsOpen A := by
        rw [hAeq]
        exact hopen.inter hv
      have hAuniv : A = univ := IsClopen.eq_univ ⟨hAcpt.isClosed, hAopen⟩ hAne
      obtain ⟨z, hzB⟩ := hBc.nonempty
      have hzA : z ∈ A := by
        rw [hAuniv]
        exact mem_univ z
      exact hAB z hzA hzB
    rcases hB' with hBu | hBv <;> rcases hA' with hAu | hAv
    · exact Or.inl (union_subset hBu hAu)
    · exact (key u v hv hdis hBu hAv).elim
    · exact (key v u hu (by rwa [inter_comm v u]) hBv hAu).elim
    · exact Or.inr (union_subset hBv hAv)
  exact ⟨hopen, hconn, hcompl⟩

/-- **Inversion**: for a compact connected `A ⊆ ℂ` with connected complement and two points
`a ≠ b`, the image of `ℂ ∖ A` under `z ↦ 1/(z - a)`, together with `0`, is a domain whose
complement in `ℂ̄` is connected and contains a finite point. -/
theorem inversion_compl_domain {A : Set ℂ} (hAc : IsCompact A) (hAconn : IsConnected A)
    (hAcompl : IsConnected Aᶜ) {a b : ℂ} (ha : a ∈ A) (hb : b ∈ A) (hab : b ≠ a) :
    IsOpen (insert 0 ((fun z => (z - a)⁻¹) '' Aᶜ)) ∧
      IsConnected (insert 0 ((fun z => (z - a)⁻¹) '' Aᶜ)) ∧
      IsConnected (toExt (insert 0 ((fun z => (z - a)⁻¹) '' Aᶜ)))ᶜ ∧
      (insert 0 ((fun z => (z - a)⁻¹) '' Aᶜ))ᶜ.Nonempty := by
  set U' : Set ℂ := insert 0 ((fun z => (z - a)⁻¹) '' Aᶜ) with hU'
  -- the inversion `z ↦ 1/(z - a)` as a homeomorphism of `ℂ̄`
  have hdet : (0 : ℂ) * (-a) - 1 * 1 ≠ 0 := by norm_num
  set M : ExtPlane ≃ₜ ExtPlane := mobiusHomeomorph 0 1 1 (-a) hdet with hM
  have hMinf : M extInf = ((0 : ℂ) : ExtPlane) := by
    show mobiusExt 0 1 1 (-a) extInf = ((0 : ℂ) : ExtPlane)
    rw [mobiusExt_infty_of_ne one_ne_zero, zero_div]
  have hMcoe : ∀ z : ℂ, z ≠ a → M (z : ExtPlane) = (((z - a)⁻¹ : ℂ) : ExtPlane) := by
    intro z hz
    have hden : (1 : ℂ) * z + -a ≠ 0 := by
      intro h0
      apply hz
      linear_combination h0
    show mobiusExt 0 1 1 (-a) (z : ExtPlane) = (((z - a)⁻¹ : ℂ) : ExtPlane)
    rw [mobiusExt_coe hden, mobiusFn, zero_mul, zero_add, one_mul, one_div, ← sub_eq_add_neg]
  -- `toExt U'` is the image of `ℂ̄ ∖ A` under `M`
  have hU'ext : toExt U' = M '' (toExt A)ᶜ := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases hw with rfl | ⟨z, hz, rfl⟩
      · exact ⟨extInf, extInf_mem_compl_toExt A, hMinf⟩
      · have hza : z ≠ a := fun h => hz (h ▸ ha)
        exact ⟨(z : ExtPlane), coe_mem_compl_toExt_iff.mpr hz, hMcoe z hza⟩
    · rintro ⟨p, hp, rfl⟩
      induction p using OnePoint.rec with
      | infty => exact ⟨0, mem_insert 0 _, hMinf.symm⟩
      | coe z =>
        have hz : z ∉ A := coe_mem_compl_toExt_iff.mp hp
        have hza : z ≠ a := fun h => hz (h ▸ ha)
        exact ⟨(z - a)⁻¹, mem_insert_of_mem _ ⟨z, hz, rfl⟩, (hMcoe z hza).symm⟩
  have hcompl : (toExt U')ᶜ = M '' toExt A := by
    rw [hU'ext, ← Set.image_compl_eq M.bijective, compl_compl]
  have hAext_cpt : IsCompact (toExt A) := hAc.image OnePoint.continuous_coe
  have hAext_conn : IsConnected (toExt A) := hAconn.image _ OnePoint.continuous_coe.continuousOn
  have hclosed : IsClosed (toExt U')ᶜ := by
    rw [hcompl]
    exact (hAext_cpt.image M.continuous).isClosed
  have hopen : IsOpen U' := isOpen_toExt_iff.mp (isClosed_compl_iff.mp hclosed)
  have hcconn : IsConnected (toExt U')ᶜ := by
    rw [hcompl]
    exact hAext_conn.image _ M.continuous.continuousOn
  have hconn : IsConnected U' := by
    refine ⟨⟨0, mem_insert 0 _⟩, ?_⟩
    rw [← OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image]
    show IsPreconnected (toExt U')
    rw [hU'ext]
    exact (isPreconnected_compl_toExt hAc.isBounded hAcompl.isPreconnected).image _
      M.continuous.continuousOn
  refine ⟨hopen, hconn, hcconn, ⟨(b - a)⁻¹, ?_⟩⟩
  intro hmem
  rcases hmem with h0 | ⟨z, hz, hzb⟩
  · exact hab (sub_eq_zero.mp (inv_eq_zero.mp h0))
  · apply hz
    have h : z - a = b - a := inv_inj.mp hzb
    rw [sub_left_inj] at h
    rw [h]
    exact hb

/-! ### The Riemann map with a puncture -/

/-- **Riemann mapping, punctured form**: a domain `U ≠ ℂ` whose complement in `ℂ̄` is connected,
with one point removed, is conformally equivalent to the punctured disc. -/
theorem conformallyEquivalent_diff_singleton_puncturedDisc {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsConnected U) (hc : IsConnected (toExt U)ᶜ) (hne : Uᶜ.Nonempty) {p : ℂ}
    (hp : p ∈ U) : ConformallyEquivalent (U \ {p}) puncturedDisc := by
  obtain ⟨f, hf, hfb⟩ := RMT.exists_riemannMap_of_hasHolomorphicSqrt hU hUc hne
    (hasHolomorphicSqrt_of_isConnected_compl hU hUc hc) hp
  refine ⟨f, hf.diff.mono diff_subset, hf.injOn.mono diff_subset, ?_⟩
  ext w
  simp only [puncturedDisc, annulus, mem_setOf_eq]
  constructor
  · rintro ⟨z, ⟨hzU, hzp⟩, rfl⟩
    have hz1 : ‖f z‖ < 1 := mem_ball_zero_iff.1 (hfb.mapsTo hzU)
    have hz0 : f z ≠ 0 := by
      intro h0
      apply hzp
      rw [mem_singleton_iff]
      exact hf.injOn hzU hp (h0.trans hf.center.symm)
    exact ⟨norm_pos_iff.2 hz0, hz1⟩
  · rintro ⟨hw0, hw1⟩
    obtain ⟨z, hzU, rfl⟩ := hfb.surjOn (mem_ball_zero_iff.2 hw1)
    refine ⟨z, ⟨hzU, ?_⟩, rfl⟩
    rw [mem_singleton_iff]
    rintro rfl
    rw [hf.center, norm_zero] at hw0
    exact lt_irrefl _ hw0

/-! ### Theorem 2.1, Stage A of case (iii) -/

/-- The component `A` of `ℂ̄ ∖ B` other than that of `∞`, read as a subset of `ℂ`
(`{z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x}`, the set `fill_component` unions
into `B`), is compact, connected, disjoint from `B`, and its image in `ℂ̄` is exactly the
component it comes from. -/
theorem isCompact_isConnected_component_ne_extInf {B : Set ℂ} (hB : IsDoublyConnected B)
    {x : ExtPlane} (hx : x ∈ (toExt B)ᶜ)
    (hne : connectedComponentIn (toExt B)ᶜ x ≠ connectedComponentIn (toExt B)ᶜ extInf) :
    IsCompact {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x} ∧
      IsConnected {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x} ∧
      toExt {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x} =
        connectedComponentIn (toExt B)ᶜ x ∧
      Disjoint B {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x} := by
  set A : Set ℂ := {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x} with hAdef
  have hinf : extInf ∈ (toExt B)ᶜ := extInf_mem_compl_toExt B
  have hBo : IsOpen B := hB.1
  have hdisj : Disjoint (connectedComponentIn (toExt B)ᶜ x) (connectedComponentIn (toExt B)ᶜ extInf) :=
    (connectedComponentIn_eq_or_disjoint x extInf).resolve_left hne
  have hinfE : extInf ∉ connectedComponentIn (toExt B)ᶜ x :=
    fun h => Set.disjoint_left.mp hdisj h (mem_connectedComponentIn hinf)
  have hEA : toExt A = connectedComponentIn (toExt B)ᶜ x := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩; exact hz
    · intro y hy
      have hyinf : y ≠ extInf := fun h => hinfE (h ▸ hy)
      obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hyinf
      exact ⟨z, hy, rfl⟩
  have hEconn : IsConnected (connectedComponentIn (toExt B)ᶜ x) :=
    isConnected_connectedComponentIn_iff.mpr hx
  have hAne : A.Nonempty := by
    have hxinf : x ≠ extInf := fun h => hne (by rw [h])
    obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hxinf
    exact ⟨z, mem_connectedComponentIn hx⟩
  have hAcpt : IsCompact A := by
    rw [OnePoint.isOpenEmbedding_coe.isInducing.isCompact_iff]
    show IsCompact (toExt A)
    rw [hEA]
    exact (isClosed_connectedComponentIn_compl_toExt hBo x).isCompact
  have hAconn : IsConnected A := by
    refine ⟨hAne, ?_⟩
    rw [← OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image]
    show IsPreconnected (toExt A)
    rw [hEA]
    exact hEconn.isPreconnected
  have hAB : Disjoint B A := by
    rw [Set.disjoint_left]
    intro z hzB hzA
    exact connectedComponentIn_subset _ _ hzA ⟨z, hzB, rfl⟩
  exact ⟨hAcpt, hAconn, hEA, hAB⟩

/-- **Theorem 2.1, Stage A** (LZ2 Steps 0 + 2): a doubly connected domain with no degenerate
complementary component is conformally equivalent to `unitDisc \ K` for some compact, connected,
non-degenerate `K ⊆ unitDisc`.

Since `B ⊆ ℂ`, `extInf ∉ toExt B` always, so `∞` sits canonically in exactly one of the two
components of `ℂ̄ ∖ B`; filling in the *other* component keeps the filled domain a subset of `ℂ`,
so the planar Riemann mapping theorem (`RMT.exists_riemannMap_of_hasHolomorphicSqrt` via
`hasHolomorphicSqrt_of_isConnected_compl`) applies with no Möbius normalization needed — unlike
LZ2's literal Step 0(0b), which states a spherical form of the Riemann mapping theorem (moving a
complement point to `∞`) because it is meant to apply to domains that may already contain `∞`. -/
theorem exists_conformallyEquivalent_diff_compact_of_isDoublyConnected {B : Set ℂ}
    (hB : IsDoublyConnected B)
    (hnd : ∀ x ∈ (toExt B)ᶜ, connectedComponentIn (toExt B)ᶜ x ≠ {x}) :
    ∃ K : Set ℂ, K ⊆ unitDisc ∧ IsCompact K ∧ IsConnected K ∧ K.Nontrivial ∧
      ConformallyEquivalent B (unitDisc \ K) := by
  obtain ⟨x, hx, hne, hcover⟩ := exists_compl_eq_union_components hB
  obtain ⟨hAcpt, hAconn, hEA, hAB⟩ := isCompact_isConnected_component_ne_extInf hB hx hne
  obtain ⟨hUopen, hUconn, hUcompl⟩ := fill_component hB hx hne
  set A : Set ℂ := {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x} with hAdef
  have hinf : extInf ∈ (toExt B)ᶜ := extInf_mem_compl_toExt B
  obtain ⟨p, hp⟩ := hB.2.1.nonempty
  have hpU : p ∈ B ∪ A := Or.inl hp
  have hEnontriv : connectedComponentIn (toExt B)ᶜ extInf ≠ {extInf} := hnd extInf hinf
  have hEne : ∃ y, y ∈ connectedComponentIn (toExt B)ᶜ extInf ∧ y ≠ extInf := by
    by_contra hcon
    push Not at hcon
    apply hEnontriv
    apply Subset.antisymm
    · intro y hy; rw [mem_singleton_iff]; exact hcon y hy
    · intro y hy
      rw [mem_singleton_iff] at hy
      rw [hy]; exact mem_connectedComponentIn hinf
  obtain ⟨y, hyE, hyinf⟩ := hEne
  obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hyinf
  have hzUc : z ∉ B ∪ A := by
    have hzmem : (z : ExtPlane) ∈ (toExt (B ∪ A))ᶜ := hUcompl ▸ hyE
    exact coe_mem_compl_toExt_iff.mp hzmem
  have hUne : (B ∪ A)ᶜ.Nonempty := ⟨z, hzUc⟩
  have hUc' : IsConnected (toExt (B ∪ A))ᶜ := hUcompl ▸ isConnected_connectedComponentIn_iff.mpr hinf
  obtain ⟨f, hf, hfb⟩ := RMT.exists_riemannMap_of_hasHolomorphicSqrt hUopen hUconn hUne
    (hasHolomorphicSqrt_of_isConnected_compl hUopen hUconn hUc') hpU
  set K : Set ℂ := f '' A with hKdef
  have hAsubU : A ⊆ B ∪ A := subset_union_right
  have hfcontA : ContinuousOn f A := hf.diff.continuousOn.mono hAsubU
  have hfinjA : InjOn f A := hf.injOn.mono hAsubU
  refine ⟨K, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hfb.mapsTo.mono hAsubU (le_refl _)).image_subset
  · exact hAcpt.image_of_continuousOn hfcontA
  · exact hAconn.image f hfcontA
  · have hAnontriv : A.Nontrivial := by
      by_contra hcon
      rw [Set.not_nontrivial_iff] at hcon
      obtain ⟨a, ha⟩ := hAconn.nonempty
      have hAeq : A = {a} := hcon.eq_singleton_of_mem ha
      have hcomp_eq : connectedComponentIn (toExt B)ᶜ x = {(a : ExtPlane)} := by
        rw [← hEA, hAeq]
        unfold toExt
        rw [Set.image_singleton]
      have hxeq : x = (a : ExtPlane) := by
        have hxmem : x ∈ connectedComponentIn (toExt B)ᶜ x := mem_connectedComponentIn hx
        rwa [hcomp_eq, mem_singleton_iff] at hxmem
      exact hnd x hx (by rw [hcomp_eq, hxeq])
    obtain ⟨a, ha, b, hb, hab⟩ := hAnontriv
    exact ⟨f a, mem_image_of_mem f ha, f b, mem_image_of_mem f hb,
      fun h => hab (hfinjA ha hb h)⟩
  · refine ⟨f, hf.diff.mono subset_union_left, hf.injOn.mono subset_union_left, ?_⟩
    have himg : f '' B = f '' (B ∪ A) \ f '' A := by
      ext w
      constructor
      · rintro ⟨z, hzB, rfl⟩
        refine ⟨mem_image_of_mem f (Or.inl hzB), ?_⟩
        rintro ⟨z', hz'A, hfz'⟩
        have heq : z = z' := hf.injOn (Or.inl hzB) (Or.inr hz'A) hfz'.symm
        exact Set.disjoint_left.mp hAB hzB (heq ▸ hz'A)
      · rintro ⟨⟨z, hzU, rfl⟩, hnA⟩
        rcases hzU with hzB | hzA
        · exact ⟨z, hzB, rfl⟩
        · exact absurd ⟨z, hzA, rfl⟩ hnA
    rw [himg, hfb.image_eq]
    rfl

/-! ### Cases (i) and (ii) of Theorem 2.1 -/

/-- **Theorem 2.1, case (i)**: if both components of `ℂ̄ ∖ B` are points, `B` is conformally
equivalent to `ℂ ∖ {0}`. -/
theorem canonical_form_of_two_points {B : Set ℂ} (hB : IsDoublyConnected B)
    (hpts : ∀ y ∈ (toExt B)ᶜ, connectedComponentIn (toExt B)ᶜ y = {y}) :
    ConformallyEquivalent B puncturedPlane := by
  obtain ⟨x, hx, hne, hcover⟩ := exists_compl_eq_union_components hB
  have hinf : extInf ∈ (toExt B)ᶜ := extInf_mem_compl_toExt B
  rw [hpts x hx, hpts extInf hinf] at hcover hne
  have hxinf : x ≠ extInf := fun h => hne (by rw [h])
  obtain ⟨p, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hxinf
  -- `B = ℂ ∖ {p}`
  have hBeq : B = {p}ᶜ := by
    ext z
    constructor
    · intro hz hzp
      rw [mem_singleton_iff] at hzp
      have h : (z : ExtPlane) ∈ (toExt B)ᶜ := by
        rw [hcover]
        exact Or.inl (by rw [hzp]; exact mem_singleton _)
      exact h ⟨z, hz, rfl⟩
    · intro hz
      by_contra hzB
      have h : (z : ExtPlane) ∈ (toExt B)ᶜ := fun h => hzB (coe_mem_toExt_iff.mp h)
      rw [hcover] at h
      rcases h with h | h
      · exact hz (OnePoint.coe_eq_coe.mp h)
      · exact OnePoint.coe_ne_infty z h
  unfold ConformallyEquivalent IsConformalOnto puncturedPlane
  refine ⟨fun z => z - p, (by fun_prop : Differentiable ℂ fun z : ℂ => z - p).differentiableOn,
    fun z₁ _ z₂ _ h => sub_left_inj.mp h, ?_⟩
  rw [hBeq]
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact fun h => hz (sub_eq_zero.mp h)
  · intro hw
    refine ⟨w + p, ?_, by ring⟩
    intro h
    rw [mem_singleton_iff] at h
    apply hw
    rw [mem_singleton_iff]
    linear_combination h

/-- **Theorem 2.1, case (ii)**: if one component of `ℂ̄ ∖ B` is a point and another is not, `B` is
conformally equivalent to `{0 < |z| < 1}`. -/
theorem canonical_form_of_one_point {B : Set ℂ} (hB : IsDoublyConnected B) {x y : ExtPlane}
    (hx : x ∈ (toExt B)ᶜ) (hxpt : connectedComponentIn (toExt B)ᶜ x = {x})
    (hy : y ∈ (toExt B)ᶜ) (hypt : connectedComponentIn (toExt B)ᶜ y ≠ {y}) :
    ConformallyEquivalent B puncturedDisc := by
  have hB' := hB
  obtain ⟨hBo, hBc, -⟩ := hB'
  have hinf : extInf ∈ (toExt B)ᶜ := OnePoint.infty_notMem_image_coe
  -- the two components of `ℂ̄ ∖ B`
  obtain ⟨x', hx', hx'ne, hunion⟩ := exists_compl_eq_union_components hB
  have hcomp : ∀ z ∈ (toExt B)ᶜ,
      connectedComponentIn (toExt B)ᶜ z = connectedComponentIn (toExt B)ᶜ x' ∨
        connectedComponentIn (toExt B)ᶜ z = connectedComponentIn (toExt B)ᶜ extInf := by
    intro z hz
    have hz' : z ∈ connectedComponentIn (toExt B)ᶜ x' ∪ connectedComponentIn (toExt B)ᶜ extInf :=
      hunion ▸ hz
    rcases hz' with h | h
    · exact Or.inl (connectedComponentIn_eq h).symm
    · exact Or.inr (connectedComponentIn_eq h).symm
  -- the component of `y` is not the component of `x`
  have hyx : connectedComponentIn (toExt B)ᶜ y ≠ connectedComponentIn (toExt B)ᶜ x := by
    intro h
    have hyx' : y ∈ connectedComponentIn (toExt B)ᶜ x := h ▸ mem_connectedComponentIn hy
    rw [hxpt, mem_singleton_iff] at hyx'
    subst hyx'
    exact hypt hxpt
  induction x using OnePoint.rec with
  | infty =>
    -- the point component is `∞`; `E`, the component of `y`, is the other one
    have hyinf : connectedComponentIn (toExt B)ᶜ y ≠ connectedComponentIn (toExt B)ᶜ extInf := hyx
    obtain ⟨E, hE⟩ : ∃ E : Set ExtPlane, E = connectedComponentIn (toExt B)ᶜ y := ⟨_, rfl⟩
    have hyE : y ∈ E := hE ▸ mem_connectedComponentIn hy
    have hEne : E ≠ {y} := hE ▸ hypt
    have hEinf : E ≠ connectedComponentIn (toExt B)ᶜ extInf := hE ▸ hyinf
    have hinfE : extInf ∉ E := fun h => hyinf (connectedComponentIn_eq (hE ▸ h))
    have hEx' : E = connectedComponentIn (toExt B)ᶜ x' := by
      rcases hcomp y hy with h | h
      · exact hE.trans h
      · exact absurd (hE.trans h) hEinf
    have hErange : E ⊆ range ((↑) : ℂ → ExtPlane) := by
      intro w hw
      rw [← OnePoint.compl_infty]
      exact fun h => hinfE ((mem_singleton_iff.1 h : w = extInf) ▸ hw)
    have hEclosed : IsClosed E := hE ▸ isClosed_connectedComponentIn_compl_toExt hBo y
    have hEconn : IsConnected E := hE ▸ isConnected_connectedComponentIn_iff.2 hy
    -- `A := coe⁻¹' E` is compact and connected, with `Aᶜ = B`
    have hAcpt : IsCompact (((↑) : ℂ → ExtPlane) ⁻¹' E) :=
      ((OnePoint.isClosed_iff_of_notMem hinfE).1 hEclosed).2
    have himg : ((↑) : ℂ → ExtPlane) '' (((↑) : ℂ → ExtPlane) ⁻¹' E) = E :=
      image_preimage_eq_of_subset hErange
    have hAconn : IsConnected (((↑) : ℂ → ExtPlane) ⁻¹' E) := by
      refine ⟨?_, ?_⟩
      · obtain ⟨q, hq⟩ := hErange hyE
        exact ⟨q, show (q : ExtPlane) ∈ E from hq ▸ hyE⟩
      · have hpre : IsPreconnected (((↑) : ℂ → ExtPlane) '' (((↑) : ℂ → ExtPlane) ⁻¹' E)) := by
          rw [himg]
          exact hEconn.isPreconnected
        exact (OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image).1 hpre
    have hAcompl : (((↑) : ℂ → ExtPlane) ⁻¹' E)ᶜ = B := by
      ext z
      constructor
      · intro hzA
        by_contra hzB
        have hzc : (z : ExtPlane) ∈ (toExt B)ᶜ := by
          rintro ⟨w, hwB, hw⟩
          rw [OnePoint.coe_eq_coe] at hw
          exact hzB (hw ▸ hwB)
        have hz' : (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x' ∪
            connectedComponentIn (toExt B)ᶜ extInf := hunion ▸ hzc
        rcases hz' with h | h
        · exact hzA (show (z : ExtPlane) ∈ E from hEx' ▸ h)
        · rw [hxpt, mem_singleton_iff] at h
          exact OnePoint.coe_ne_infty z h
      · intro hzB hzA
        have hzy : (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ y := hE ▸ hzA
        have hzc : (z : ExtPlane) ∈ (toExt B)ᶜ := connectedComponentIn_subset _ _ hzy
        exact hzc ⟨z, hzB, rfl⟩
    -- two distinct points of `A`
    obtain ⟨a, ha⟩ : ∃ a : ℂ, (a : ExtPlane) ∈ E := by
      obtain ⟨q, hq⟩ := hErange hyE
      exact ⟨q, hq ▸ hyE⟩
    obtain ⟨b, hb, hba⟩ : ∃ b : ℂ, (b : ExtPlane) ∈ E ∧ b ≠ a := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      apply hEne
      have hEa : E = {(a : ExtPlane)} := by
        refine Set.eq_singleton_iff_unique_mem.2 ⟨ha, fun w hw => ?_⟩
        obtain ⟨q, rfl⟩ := hErange hw
        rw [hcon q hw]
      have hya : y = (a : ExtPlane) := by
        have hyE' := hyE
        rw [hEa, mem_singleton_iff] at hyE'
        exact hyE'
      rw [hEa, hya]
    have haA : a ∈ ((↑) : ℂ → ExtPlane) ⁻¹' E := ha
    have hbA : b ∈ ((↑) : ℂ → ExtPlane) ⁻¹' E := hb
    have hBconn : IsConnected (((↑) : ℂ → ExtPlane) ⁻¹' E)ᶜ := hAcompl ▸ hBc
    -- inversion about `a`
    obtain ⟨hU'o, hU'c, hU'compl, hU'ne⟩ :=
      inversion_compl_domain hAcpt hAconn hBconn haA hbA hba
    have h0 : (0 : ℂ) ∈ insert 0 ((fun z => (z - a)⁻¹) '' (((↑) : ℂ → ExtPlane) ⁻¹' E)ᶜ) :=
      mem_insert _ _
    have h1 := conformallyEquivalent_diff_singleton_puncturedDisc hU'o hU'c hU'compl hU'ne h0
    have hnot0 : (0 : ℂ) ∉ (fun z => (z - a)⁻¹) '' (((↑) : ℂ → ExtPlane) ⁻¹' E)ᶜ := by
      rintro ⟨z, hz, hz0⟩
      have hza : z - a ≠ 0 := sub_ne_zero.2 fun h => hz (h ▸ haA)
      exact inv_ne_zero hza hz0
    have hdiff : insert 0 ((fun z => (z - a)⁻¹) '' (((↑) : ℂ → ExtPlane) ⁻¹' E)ᶜ) \ {0}
        = (fun z => (z - a)⁻¹) '' (((↑) : ℂ → ExtPlane) ⁻¹' E)ᶜ := by
      rw [insert_diff_of_mem _ (mem_singleton 0), diff_singleton_eq_self hnot0]
    rw [hdiff] at h1
    -- `z ↦ 1/(z - a)` is conformal from `B = Aᶜ` onto the image
    have h2 : ConformallyEquivalent B
        ((fun z => (z - a)⁻¹) '' (((↑) : ℂ → ExtPlane) ⁻¹' E)ᶜ) := by
      have hne' : ∀ z ∈ B, z - a ≠ 0 := fun z hz => sub_ne_zero.2 fun h =>
        (show z ∈ (((↑) : ℂ → ExtPlane) ⁻¹' E)ᶜ from hAcompl ▸ hz) (h ▸ haA)
      refine ⟨fun z => (z - a)⁻¹, ?_, ?_, ?_⟩
      · exact (differentiableOn_id.sub_const a).inv hne'
      · intro z hz w hw hzw
        have hzw' : (z - a)⁻¹ = (w - a)⁻¹ := hzw
        exact sub_left_injective (inv_injective hzw')
      · rw [hAcompl]
    exact h2.trans h1
  | coe p =>
    -- the point component is the finite point `p`; the other component is that of `∞`
    have hxinf : connectedComponentIn (toExt B)ᶜ (p : ExtPlane)
        ≠ connectedComponentIn (toExt B)ᶜ extInf := by
      intro h
      have hinf' : extInf ∈ connectedComponentIn (toExt B)ᶜ (p : ExtPlane) :=
        h ▸ mem_connectedComponentIn hinf
      rw [hxpt, mem_singleton_iff] at hinf'
      exact OnePoint.infty_ne_coe p hinf'
    have hyinf : connectedComponentIn (toExt B)ᶜ y = connectedComponentIn (toExt B)ᶜ extInf := by
      rcases hcomp y hy with h | h
      · rcases hcomp _ hx with h' | h'
        · exact absurd (h.trans h'.symm) hyx
        · exact absurd h' hxinf
      · exact h
    obtain ⟨hUo, hUc, hUcompl⟩ := fill_component hB hx hxinf
    have hset : {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ (p : ExtPlane)}
        = {p} := by
      ext z
      simp only [mem_setOf_eq, mem_singleton_iff, hxpt, OnePoint.coe_eq_coe]
    rw [hset] at hUo hUc hUcompl
    have hc : IsConnected (toExt (B ∪ {p}))ᶜ := by
      rw [hUcompl]
      exact isConnected_connectedComponentIn_iff.2 hinf
    -- `B ∪ {p} ≠ ℂ`: the component of `∞` is not `{∞}`
    have hne : (B ∪ {p})ᶜ.Nonempty := by
      have hne' : connectedComponentIn (toExt B)ᶜ extInf ≠ {extInf} := by
        intro h
        rw [← hyinf] at h
        have hy' : y ∈ ({extInf} : Set ExtPlane) := h ▸ mem_connectedComponentIn hy
        rw [mem_singleton_iff] at hy'
        subst hy'
        exact hypt h
      obtain ⟨w, hw, hwinf⟩ : ∃ w ∈ connectedComponentIn (toExt B)ᶜ extInf, w ≠ extInf := by
        by_contra hcon
        simp only [not_exists, not_and, not_not] at hcon
        exact hne' (Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponentIn hinf, hcon⟩)
      obtain ⟨q, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hwinf
      refine ⟨q, fun hq => ?_⟩
      rw [← hUcompl] at hw
      exact hw ⟨q, hq, rfl⟩
    have hpU : p ∈ B ∪ {p} := Or.inr rfl
    have h := conformallyEquivalent_diff_singleton_puncturedDisc hUo hUc hc hne hpU
    have hpB : p ∉ B := fun hpB => hx ⟨p, hpB, rfl⟩
    have hBeq : (B ∪ {p}) \ {p} = B := by
      rw [union_diff_right, diff_singleton_eq_self hpB]
    rw [hBeq] at h
    exact h

/-- **Theorem 2.1, cases (i) and (ii)**: if some component of `ℂ̄ ∖ B` is a single point, `B` is
conformally equivalent to `ℂ ∖ {0}` or to `{0 < |z| < 1}`. -/
theorem canonical_form_of_degenerate_component {B : Set ℂ} (hB : IsDoublyConnected B)
    {x : ExtPlane} (hx : x ∈ (toExt B)ᶜ) (hxpt : connectedComponentIn (toExt B)ᶜ x = {x}) :
    ConformallyEquivalent B puncturedPlane ∨ ConformallyEquivalent B puncturedDisc := by
  by_cases hall : ∀ y ∈ (toExt B)ᶜ, connectedComponentIn (toExt B)ᶜ y = {y}
  · exact Or.inl (canonical_form_of_two_points hB hall)
  · simp only [not_forall] at hall
    obtain ⟨y, hy, hypt⟩ := hall
    exact Or.inr (canonical_form_of_one_point hB hx hxpt hy hypt)

end LiZhongQC
