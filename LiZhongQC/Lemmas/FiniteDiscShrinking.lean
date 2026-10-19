import LiZhongQC.Lemmas.FinitePunctureCompactification

open Set Filter Topology

noncomputable section
namespace LiZhongQC

/-- A disc-complement shrinking that fixes a protected set restricts to its
complement. Injectivity proves that no additional point enters that set. -/
theorem s31fu_shrink_restrict {X : Type*} [TopologicalSpace X]
    {D A : Set X} {c : X} (hDA : Disjoint D A)
    (e : ↥(Dᶜ) ≃ₜ ({c}ᶜ : Set X))
    (hfix : ∀ x : ↥(Dᶜ), x.val ∈ A → (e x).val = x.val) :
    Nonempty (↥((A ∪ D)ᶜ) ≃ₜ ((A ∪ {c})ᶜ : Set X)) := by
  have hnotD : ∀ x ∈ A, x ∉ D := fun x hx hD => disjoint_left.1 hDA hD hx
  have hmem : ∀ x : ↥(Dᶜ), (e x).val ∈ A ↔ x.val ∈ A := by
    intro x
    constructor
    · intro hx
      let a : ↥(Dᶜ) := ⟨(e x).val, hnotD _ hx⟩
      have hea : e a = e x := Subtype.ext (hfix a hx)
      have hax : a = x := e.injective hea
      exact (congrArg Subtype.val hax) ▸ hx
    · intro hx
      rw [hfix x hx]
      exact hx
  let f : ↥((A ∪ D)ᶜ) → ((A ∪ {c})ᶜ : Set X) := fun x =>
    ⟨(e ⟨x.val, fun h => x.property (Or.inr h)⟩).val, by
      intro h
      rcases h with hA | hc'
      · exact x.property (Or.inl ((hmem _).1 hA))
      · exact (e ⟨x.val, fun h => x.property (Or.inr h)⟩).property hc'⟩
  let g : ((A ∪ {c})ᶜ : Set X) → ↥((A ∪ D)ᶜ) := fun y =>
    ⟨(e.symm ⟨y.val, fun h => y.property (Or.inr h)⟩).val, by
      intro h
      rcases h with hA | hD
      · apply y.property
        left
        have hm := (hmem (e.symm ⟨y.val, fun h => y.property (Or.inr h)⟩)).2 hA
        simpa only [e.apply_symm_apply] using hm
      · exact (e.symm ⟨y.val, fun h => y.property (Or.inr h)⟩).property hD⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (e.continuous.comp
      (continuous_subtype_val.subtype_mk _))
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (e.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _))
  refine ⟨{
    toFun := f
    invFun := g
    continuous_toFun := hf
    continuous_invFun := hg
    left_inv := ?_
    right_inv := ?_ }⟩
  · intro x
    apply Subtype.ext
    change (e.symm (e ⟨x.val, _⟩)).val = x.val
    rw [e.symm_apply_apply]
  · intro y
    apply Subtype.ext
    change (e (e.symm ⟨y.val, _⟩)).val = y.val
    rw [e.apply_symm_apply]

/-- Finite composition of local disc shrinkings. At each stage the support
avoids both the original punctures and every remaining disc. The conclusion
is a genuine homeomorphism of complements, with the omitted-point count. -/
theorem s31fu_shrink_finite {X I : Type*} [TopologicalSpace X] [T1Space X]
    (D : I → Set X) (s : Finset I)
    (hclosed : ∀ i ∈ s, IsClosed (D i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (D i) (D j))
    (hshrink : ∀ i ∈ s, ∀ A : Set X, IsClosed A → Disjoint (D i) A →
      ∃ c ∈ D i, ∃ e : ↥((D i)ᶜ) ≃ₜ ({c}ᶜ : Set X),
        ∀ x : ↥((D i)ᶜ), x.val ∈ A → (e x).val = x.val)
    (P : Finset X) (hP : ∀ i ∈ s, Disjoint (D i) (↑P : Set X)) :
    ∃ Q : Finset X, Q.card = P.card + s.card ∧
      Nonempty (↥(((↑P : Set X) ∪ ⋃ i ∈ s, D i)ᶜ) ≃ₜ ↥((↑Q : Set X)ᶜ)) := by
  classical
  revert hclosed hdisj hshrink P hP
  induction s using Finset.induction_on with
  | empty =>
      intro hclosed hdisj hshrink P hP
      refine ⟨P, by simp, ?_⟩
      exact ⟨Homeomorph.setCongr (by simp)⟩
  | @insert i s his ih =>
      intro hclosed hdisj hshrink P hP
      have hsc : ∀ j ∈ s, IsClosed (D j) :=
        fun j hj => hclosed j (Finset.mem_insert_of_mem hj)
      have hsd : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → Disjoint (D j) (D k) :=
        fun j hj k hk hne => hdisj j (Finset.mem_insert_of_mem hj)
          k (Finset.mem_insert_of_mem hk) hne
      have hss : ∀ j ∈ s, ∀ A : Set X, IsClosed A → Disjoint (D j) A →
          ∃ c ∈ D j, ∃ e : ↥((D j)ᶜ) ≃ₜ ({c}ᶜ : Set X),
            ∀ x : ↥((D j)ᶜ), x.val ∈ A → (e x).val = x.val :=
        fun j hj => hshrink j (Finset.mem_insert_of_mem hj)
      let A : Set X := (↑P : Set X) ∪ ⋃ j ∈ s, D j
      have hAc : IsClosed A := P.finite_toSet.isClosed.union
        (isClosed_biUnion_finset fun j hj => hsc j hj)
      have hiA : Disjoint (D i) A := by
        apply disjoint_left.2
        intro x hx hA
        rcases hA with hp | hs
        · exact disjoint_left.1 (hP i (Finset.mem_insert_self _ _)) hx hp
        · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hs
          have hij : i ≠ j := fun he => his (he.symm ▸ hj)
          exact disjoint_left.1 (hdisj i (Finset.mem_insert_self _ _)
            j (Finset.mem_insert_of_mem hj) hij) hx hxj
      obtain ⟨c, hc, e, he⟩ := hshrink i (Finset.mem_insert_self _ _) A hAc hiA
      have hcP : c ∉ P := fun hp =>
        disjoint_left.1 hiA hc (Or.inl hp)
      have hsP : ∀ j ∈ s, Disjoint (D j) (↑(insert c P) : Set X) := by
        intro j hj
        apply disjoint_left.2
        intro x hx hxp
        rcases Finset.mem_insert.1 hxp with hxc | hxp
        · subst x
          exact disjoint_left.1 hiA hc (Or.inr (mem_iUnion₂.2 ⟨j, hj, hx⟩))
        · exact disjoint_left.1 (hP j (Finset.mem_insert_of_mem hj)) hx hxp
      obtain ⟨Q, hQ, hEQ⟩ := ih hsc hsd hss (insert c P) hsP
      obtain ⟨E⟩ := s31fu_shrink_restrict hiA e he
      obtain ⟨H⟩ := hEQ
      have hleft : ((↑P : Set X) ∪ ⋃ j ∈ insert i s, D j)ᶜ = (A ∪ D i)ᶜ := by
        ext x
        simp only [A, Finset.mem_insert, iUnion_iUnion_eq_or_left]
        aesop
      have hright : (A ∪ {c})ᶜ = ((↑(insert c P) : Set X) ∪ ⋃ j ∈ s, D j)ᶜ := by
        ext x
        simp only [A, Finset.coe_insert, mem_compl_iff, mem_union,
          mem_singleton_iff, Set.mem_insert_iff]
        tauto
      refine ⟨Q, ?_, ⟨(Homeomorph.setCongr hleft).trans
        (E.trans ((Homeomorph.setCongr hright).trans H))⟩⟩
      rw [hQ, Finset.card_insert_of_notMem hcP, Finset.card_insert_of_notMem his]
      omega

end LiZhongQC

