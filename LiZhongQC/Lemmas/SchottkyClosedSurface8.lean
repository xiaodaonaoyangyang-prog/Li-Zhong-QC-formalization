import LiZhongExternal.DifferentialGeometry.SchottkyVanKampen
import LiZhongQC.Lemmas.SchottkyFreeProductSVK
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.PushoutI
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Tactic

universe u

namespace LiZhongQC

/-- Variant of `s78dg_pushoutI_trivial_base` recording the effect on the canonical injections. -/
theorem s78dg_pushoutI_trivial_base_gen {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
    {H : Type*} [Group H] [Subsingleton H] (φ : ∀ i, H →* G i) :
    ∃ e : Monoid.PushoutI φ ≃* Monoid.CoprodI G,
      ∀ (i : ι) (g : G i), e (Monoid.PushoutI.of i g) = Monoid.CoprodI.of g := by
  let hf : ∀ i, (Monoid.CoprodI.of : G i →* Monoid.CoprodI G).comp (φ i) =
      (1 : H →* Monoid.CoprodI G) := by
    intro i
    ext h
    rw [Subsingleton.elim h 1]
    simp
  let T : Monoid.PushoutI φ →* Monoid.CoprodI G :=
    Monoid.PushoutI.lift (fun i => Monoid.CoprodI.of) 1 hf
  let S : Monoid.CoprodI G →* Monoid.PushoutI φ := Monoid.PushoutI.ofCoprodI
  have hST : S.comp T = MonoidHom.id _ := by
    apply Monoid.PushoutI.hom_ext
    · intro i
      ext g
      simp [S, T]
    · ext h
      rw [Subsingleton.elim h 1]
      simp
  have hTS : T.comp S = MonoidHom.id _ := by
    apply Monoid.CoprodI.ext_hom
    intro i
    ext g
    simp [S, T]
  refine ⟨MonoidHom.toMulEquiv T S hST hTS, fun i g => ?_⟩
  simp [T]

/-- A free product of free groups is free; the canonical injections are read off from the given
isomorphisms. -/
theorem s78dg_coprodI_free_gen {G : Bool → Type*} [∀ b, Group (G b)] {ι : Bool → Type}
    (e : ∀ b, G b ≃* FreeGroup (ι b)) :
    ∃ E : Monoid.CoprodI G ≃* FreeGroup (Σ b, ι b),
      ∀ (b : Bool) (g : G b), E (Monoid.CoprodI.of g) =
        FreeGroup.lift (fun x : ι b => FreeGroup.of (⟨b, x⟩ : Σ b, ι b)) (e b g) := by
  let B : ∀ b : Bool, FreeGroupBasis (ι b) (G b) := fun b => FreeGroupBasis.ofRepr (e b)
  refine ⟨(Monoid.CoprodI.FreeGroupBasis.coprodI B).repr, fun b g => ?_⟩
  change (Monoid.CoprodI.lift fun i : Bool => (B i).lift fun x : ι i =>
    FreeGroup.of (⟨i, x⟩ : Σ b, ι b)) (Monoid.CoprodI.of g) = _
  rw [Monoid.CoprodI.lift_of]
  rfl

open DifferentialGeometry.Topology.VanKampen in
/-- **Wedge step with generator tracking.**  Under the hypotheses of `s78dg_wedge_free_step`, the
isomorphism `π₁(X) ≃* FreeGroup (α ⊕ β)` can be chosen compatibly with the given isomorphisms of the
pieces with free groups: the images of `π₁(U)` and `π₁(V)` are read through `inl`, `inr`. -/
theorem s78dg_wedge_free_step_gen {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))]
    [SimplyConnectedSpace (↑(U ∩ V))] {α β : Type}
    (eU : fundamentalGroupFactor U V x₀ hx₀ false ≃* FreeGroup α)
    (eV : fundamentalGroupFactor U V x₀ hx₀ true ≃* FreeGroup β) :
    ∃ e : FundamentalGroup X x₀ ≃* FreeGroup (α ⊕ β),
      (∀ u, e ((fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom u) = FreeGroup.map Sum.inl (eU u)) ∧
      (∀ v, e ((fundamentalGroupRightToAmbient V x₀ hx₀.2).hom v) = FreeGroup.map Sum.inr (eV v)) := by
  let eS := fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x₀ hx₀
  obtain ⟨e2, he2⟩ := s78dg_pushoutI_trivial_base_gen (fundamentalGroupAmalgamation U V x₀ hx₀)
  let ι : Bool → Type := fun b => cond b β α
  let e' : ∀ b : Bool, fundamentalGroupFactor U V x₀ hx₀ b ≃* FreeGroup (ι b) := by
    intro b
    cases b
    · exact eU
    · exact eV
  obtain ⟨E, hE⟩ := s78dg_coprodI_free_gen e'
  let σ : (Σ b : Bool, ι b) ≃ α ⊕ β := (Equiv.sumEquivSigmaBool α β).symm
  refine ⟨eS.symm.trans (e2.trans (E.trans (FreeGroup.freeGroupCongr σ))), ?_, ?_⟩
  · intro u
    have h1 : eS (Monoid.PushoutI.of false u) = (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom u := by
      have := fundamentalGroupEquivAmalgamatedProduct_comp_left U V hU hV hcover x₀ hx₀
      exact DFunLike.congr_fun this u
    have h2 : eS.symm ((fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom u) =
        Monoid.PushoutI.of false u := eS.symm_apply_eq.2 h1.symm
    simp only [MulEquiv.trans_apply]
    rw [h2, he2, hE]
    have h3 : e' false u = eU u := rfl
    rw [h3]
    have key : ∀ w : FreeGroup α, FreeGroup.freeGroupCongr σ
        (FreeGroup.lift (fun x : ι false => FreeGroup.of (⟨false, x⟩ : Σ b, ι b)) w) =
        FreeGroup.map Sum.inl w := by
      intro w
      have := DFunLike.congr_fun (FreeGroup.ext_hom (f := (FreeGroup.map σ).comp
        (FreeGroup.lift (fun x : ι false => FreeGroup.of (⟨false, x⟩ : Σ b, ι b))))
        (g := FreeGroup.map (Sum.inl : α → α ⊕ β)) (fun x => by
          simp [σ, ι]; rfl)) w
      exact this
    exact key (eU u)
  · intro v
    have h1 : eS (Monoid.PushoutI.of true v) = (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom v := by
      have := fundamentalGroupEquivAmalgamatedProduct_comp_right U V hU hV hcover x₀ hx₀
      exact DFunLike.congr_fun this v
    have h2 : eS.symm ((fundamentalGroupRightToAmbient V x₀ hx₀.2).hom v) =
        Monoid.PushoutI.of true v := eS.symm_apply_eq.2 h1.symm
    simp only [MulEquiv.trans_apply]
    rw [h2, he2, hE]
    have h3 : e' true v = eV v := rfl
    rw [h3]
    have key : ∀ w : FreeGroup β, FreeGroup.freeGroupCongr σ
        (FreeGroup.lift (fun x : ι true => FreeGroup.of (⟨true, x⟩ : Σ b, ι b)) w) =
        FreeGroup.map Sum.inr w := by
      intro w
      have := DFunLike.congr_fun (FreeGroup.ext_hom (f := (FreeGroup.map σ).comp
        (FreeGroup.lift (fun x : ι true => FreeGroup.of (⟨true, x⟩ : Σ b, ι b))))
        (g := FreeGroup.map (Sum.inr : β → α ⊕ β)) (fun x => by
          simp [σ, ι]; rfl)) w
      exact this
    exact key (eV v)

end LiZhongQC
