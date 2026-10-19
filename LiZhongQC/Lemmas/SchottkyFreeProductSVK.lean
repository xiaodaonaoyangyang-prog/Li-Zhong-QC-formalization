import LiZhongExternal.DifferentialGeometry.SchottkyVanKampen
import Mathlib.GroupTheory.PushoutI
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

universe u

namespace LiZhongQC

/-- An amalgamated product over a subsingleton base group is the free product. -/
theorem s78dg_pushoutI_trivial_base {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
    {H : Type*} [Group H] [Subsingleton H] (φ : ∀ i, H →* G i) :
    Nonempty (Monoid.PushoutI φ ≃* Monoid.CoprodI G) := by
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
  exact ⟨MonoidHom.toMulEquiv T S hST hTS⟩

/-- **Van Kampen over a simply connected overlap**: the fundamental group of a space covered by two
open sets with path-connected pieces and simply connected path-connected overlap is the free product
of the fundamental groups of the pieces. -/
theorem s78dg_svk_free_product {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    Nonempty (FundamentalGroup X x₀ ≃*
      Monoid.CoprodI (DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactor U V x₀ hx₀)) := by
  obtain ⟨e⟩ := s78dg_pushoutI_trivial_base
    (DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamation U V x₀ hx₀)
  exact ⟨(DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivAmalgamatedProduct
    U V hU hV hcover x₀ hx₀).symm.trans e⟩

/-- **Wedge step.**  Under the hypotheses of `s78dg_svk_free_product`, if the fundamental groups of the two
pieces are free on `α` and `β`, then that of the union is free on `α ⊕ β`. -/
theorem s78dg_wedge_free_step {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))]
    [SimplyConnectedSpace (↑(U ∩ V))] {α β : Type}
    (eU : DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactor U V x₀ hx₀ false ≃*
      FreeGroup α)
    (eV : DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactor U V x₀ hx₀ true ≃*
      FreeGroup β) :
    Nonempty (FundamentalGroup X x₀ ≃* FreeGroup (α ⊕ β)) := by
  obtain ⟨e⟩ := s78dg_svk_free_product U V hU hV hcover x₀ hx₀
  let ι : Bool → Type := fun b => cond b β α
  let B : ∀ b : Bool, FreeGroupBasis (ι b)
      (DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactor U V x₀ hx₀ b) := by
    intro b
    cases b
    · exact FreeGroupBasis.ofRepr eU
    · exact FreeGroupBasis.ofRepr eV
  let σ : (Σ b : Bool, ι b) ≃ α ⊕ β :=
    (Equiv.sumEquivSigmaBool α β).symm
  exact ⟨e.trans ((Monoid.CoprodI.FreeGroupBasis.coprodI B).repr.trans (FreeGroup.freeGroupCongr σ))⟩

end LiZhongQC
