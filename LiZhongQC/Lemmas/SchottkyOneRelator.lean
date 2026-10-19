import Mathlib.GroupTheory.PushoutI
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic

namespace LiZhongQC

/-- An amalgamated product of `G false` and a trivial group `G true` over `H` is the quotient of `G false`
by the normal closure of the image of `H`. -/
theorem s78dg_pushoutI_one_trivial {G : Bool → Type*} [∀ b, Group (G b)] {H : Type*} [Group H]
    (φ : ∀ b, H →* G b) [Subsingleton (G true)] :
    Nonempty (Monoid.PushoutI φ ≃*
      (G false ⧸ Subgroup.normalClosure ((φ false).range : Set (G false)))) := by
  let N : Subgroup (G false) := Subgroup.normalClosure ((φ false).range : Set (G false))
  have hN : ∀ h : H, φ false h ∈ N := fun h =>
    Subgroup.subset_normalClosure ⟨h, rfl⟩
  have hof : ∀ h : H, (Monoid.PushoutI.of false (φ false h) : Monoid.PushoutI φ) = 1 := by
    intro h
    rw [Monoid.PushoutI.of_apply_eq_base, ← Monoid.PushoutI.of_apply_eq_base (φ := φ) true,
      Subsingleton.elim (φ true h) 1, map_one]
  let f : ∀ b, G b →* (G false ⧸ N) := by
    intro b
    cases b
    · exact QuotientGroup.mk' N
    · exact 1
  let k : H →* (G false ⧸ N) := (QuotientGroup.mk' N).comp (φ false)
  have hf : ∀ b, (f b).comp (φ b) = k := by
    intro b
    cases b
    · rfl
    · ext h
      change (1 : G false ⧸ N) = QuotientGroup.mk (φ false h)
      exact ((QuotientGroup.eq_one_iff _).2 (hN h)).symm
  let T : Monoid.PushoutI φ →* (G false ⧸ N) := Monoid.PushoutI.lift f k hf
  have hker : N ≤ (Monoid.PushoutI.of false : G false →* Monoid.PushoutI φ).ker := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨h, rfl⟩
    exact hof h
  let S : (G false ⧸ N) →* Monoid.PushoutI φ :=
    QuotientGroup.lift N (Monoid.PushoutI.of false) (fun x hx => hker hx)
  have hTS : T.comp S = MonoidHom.id _ := by
    apply QuotientGroup.monoidHom_ext
    ext g
    simp [S, T, f]
  have hST : S.comp T = MonoidHom.id _ := by
    apply Monoid.PushoutI.hom_ext
    · intro b
      cases b
      · ext g
        simp [S, T, f]
      · ext g
        rw [Subsingleton.elim g 1]
        simp [S, T, f]
    · ext h
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
      rw [← Monoid.PushoutI.of_apply_eq_base (φ := φ) false]
      simp [hof h]
  exact ⟨MonoidHom.toMulEquiv T S hST hTS⟩

/-- Killing one more element of a presented group adds one relator. -/
theorem s78dg_quotient_presented {α : Type*} (R : Set (FreeGroup α)) (w : FreeGroup α)
    {G : Type*} [Group G] (e : G ≃* PresentedGroup R) :
    Nonempty (G ⧸ Subgroup.normalClosure ({e.symm (PresentedGroup.mk R w)} : Set G) ≃*
      PresentedGroup (insert w R)) := by
  let N : Subgroup G := Subgroup.normalClosure ({e.symm (PresentedGroup.mk R w)} : Set G)
  let x : G := e.symm (PresentedGroup.mk R w)
  -- the map into the quotient
  let f : α → G ⧸ N := fun a => QuotientGroup.mk (e.symm (PresentedGroup.of a))
  let c : FreeGroup α →* G ⧸ N :=
    ((QuotientGroup.mk' N).comp e.symm.toMonoidHom).comp (PresentedGroup.mk R)
  have hc : FreeGroup.lift f = c := by
    apply FreeGroup.ext_hom
    intro a
    simp [f, c, PresentedGroup.mk]
    rfl
  have hxN : (QuotientGroup.mk x : G ⧸ N) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure rfl)
  have hrel : ∀ r ∈ insert w R, FreeGroup.lift f r = 1 := by
    intro r hr
    rw [hc]
    rcases hr with rfl | hr
    · exact hxN
    · have : PresentedGroup.mk R r = 1 := PresentedGroup.one_of_mem hr
      change QuotientGroup.mk (e.symm (PresentedGroup.mk R r)) = 1
      rw [this, map_one]
      rfl
  let T : PresentedGroup (insert w R) →* G ⧸ N := PresentedGroup.toGroup hrel
  -- the map back
  let ψ0 : PresentedGroup R →* PresentedGroup (insert w R) :=
    PresentedGroup.toGroup (rels := R) (f := fun a => PresentedGroup.of a) (fun r hr => by
      have h1 : (PresentedGroup.mk (insert w R) r : PresentedGroup (insert w R)) = 1 :=
        PresentedGroup.one_of_mem (Set.mem_insert_of_mem w hr)
      have h2 : FreeGroup.lift (fun a => (PresentedGroup.of a : PresentedGroup (insert w R))) r =
          PresentedGroup.mk (insert w R) r := by
        have : FreeGroup.lift (fun a => (PresentedGroup.of a : PresentedGroup (insert w R))) =
            PresentedGroup.mk (insert w R) := by
          apply FreeGroup.ext_hom
          intro a
          simp [PresentedGroup.mk]
          rfl
        rw [this]
      rw [h2, h1])
  let ψ : G →* PresentedGroup (insert w R) := ψ0.comp e.toMonoidHom
  have hxψ : ψ x = 1 := by
    change ψ0 (e (e.symm (PresentedGroup.mk R w))) = 1
    rw [MulEquiv.apply_symm_apply]
    have : ψ0 (PresentedGroup.mk R w) =
        PresentedGroup.mk (insert w R) w := by
      have h3 : ψ0.comp (PresentedGroup.mk R) = PresentedGroup.mk (insert w R) := by
        apply FreeGroup.ext_hom
        intro a
        simp [ψ0, PresentedGroup.mk]
        rfl
      exact DFunLike.congr_fun h3 w
    rw [this]
    exact PresentedGroup.one_of_mem (Set.mem_insert w R)
  have hker : N ≤ ψ.ker := by
    refine Subgroup.normalClosure_le_normal ?_
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact hxψ
  let S : G ⧸ N →* PresentedGroup (insert w R) := QuotientGroup.lift N ψ (fun y hy => hker hy)
  have hψ0 : ψ0.comp (PresentedGroup.mk R) = PresentedGroup.mk (insert w R) := by
    apply FreeGroup.ext_hom
    intro a
    simp [ψ0, PresentedGroup.mk]
    rfl
  have hTmk : T.comp (PresentedGroup.mk (insert w R)) = FreeGroup.lift f := by
    apply FreeGroup.ext_hom
    intro a
    change T (PresentedGroup.of a) = FreeGroup.lift f (FreeGroup.of a)
    rw [FreeGroup.lift_apply_of]
    exact PresentedGroup.toGroup.of hrel
  have hTS : T.comp S = MonoidHom.id _ := by
    apply QuotientGroup.monoidHom_ext
    ext g
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (e g)
    have h1 : S (QuotientGroup.mk g) = ψ0 (e g) := rfl
    have h2 : ψ0 (e g) = PresentedGroup.mk (insert w R) u := by
      rw [← hu]
      exact DFunLike.congr_fun hψ0 u
    have h3 : T (PresentedGroup.mk (insert w R) u) = c u := by
      rw [← hc]
      exact DFunLike.congr_fun hTmk u
    have h4 : c u = QuotientGroup.mk g := by
      have hu' : PresentedGroup.mk R u = e g := hu
      change QuotientGroup.mk (e.symm (PresentedGroup.mk R u)) = _
      rw [hu', MulEquiv.symm_apply_apply]
    change T (S (QuotientGroup.mk g)) = QuotientGroup.mk g
    rw [h1, h2, h3, h4]
  have hST : S.comp T = MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro a
    change S (T (PresentedGroup.of a)) = PresentedGroup.of a
    have h1 : T (PresentedGroup.of a) = QuotientGroup.mk (e.symm (PresentedGroup.of a)) := by
      simp [T, f]
    rw [h1]
    change ψ0 (e (e.symm (PresentedGroup.of a))) = _
    rw [MulEquiv.apply_symm_apply]
    simp [ψ0]
  exact ⟨MonoidHom.toMulEquiv S T hTS hST⟩

end LiZhongQC
