import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.Homotopy.Path

open unitInterval

namespace LiZhongQC

/-- **π₁ invariance under strong deformation retraction.**  If `r : X → A` is a retraction of `i : A → X`
and the identity of `X` is homotopic to `i ∘ r` by a homotopy that fixes the image of `i` pointwise, then
`i` induces a bijection on fundamental groups. -/
theorem s78dg_pi1_deformation_bijective {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (r : C(X, A)) (hri : ∀ y, r (i y) = y)
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) (i.comp r))
    (hH : ∀ (y : A) (s : I), H (s, i y) = i y) (a : A) :
    Function.Bijective (FundamentalGroup.map i a) := by
  constructor
  · intro x y hxy
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    induction x using Quotient.inductionOn with
    | h δ₁ =>
    induction y using Quotient.inductionOn with
    | h δ₂ =>
    have h1 : (δ₁.map i.continuous).Homotopic (δ₂.map i.continuous) := by
      rw [← Path.Homotopic.Quotient.eq]
      exact congrArg CategoryTheory.End.asHom hxy
    have h2 := (h1.map r).pathCast (hri a).symm (hri a).symm
    have e1 : (((δ₁.map i.continuous).map r.continuous).cast (hri a).symm (hri a).symm) = δ₁ := by
      ext t
      simp [hri]
    have e2 : (((δ₂.map i.continuous).map r.continuous).cast (hri a).symm (hri a).symm) = δ₂ := by
      ext t
      simp [hri]
    rw [e1, e2] at h2
    exact congrArg CategoryTheory.End.of (Path.Homotopic.Quotient.eq.mpr h2)
  · intro g
    obtain ⟨g⟩ := g
    induction g using Quotient.inductionOn with
    | h γ =>
    let δ : Path a a := (γ.map r.continuous).cast (hri a).symm (hri a).symm
    refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ), ?_⟩
    apply CategoryTheory.End.ext
    change Path.Homotopic.Quotient.mk (δ.map i.continuous) = Path.Homotopic.Quotient.mk γ
    rw [Path.Homotopic.Quotient.eq]
    have hγ0 : ∀ s : I, H (s, γ 0) = γ 0 := by
      intro s
      have := hH a s
      rw [γ.source]; exact this
    have hγ1 : ∀ s : I, H (s, γ 1) = γ 1 := by
      intro s
      have := hH a s
      rw [γ.target]; exact this
    let F : Path.Homotopy γ (δ.map i.continuous) :=
      { toFun := fun p => H (p.1, γ p.2)
        continuous_toFun := H.continuous.comp (continuous_fst.prodMk (γ.continuous.comp continuous_snd))
        map_zero_left := fun t => by simp
        map_one_left := fun t => by simp [δ]
        prop' := fun s t ht => by
          rcases ht with rfl | rfl
          · simpa using hγ0 s
          · simpa using hγ1 s }
    exact Path.Homotopic.symm (⟨F⟩ : Path.Homotopic γ (δ.map i.continuous))

/-- The group isomorphism induced by a strong deformation retraction. -/
theorem s78dg_pi1_deformation_equiv {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (r : C(X, A)) (hri : ∀ y, r (i y) = y)
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) (i.comp r))
    (hH : ∀ (y : A) (s : I), H (s, i y) = i y) (a : A) :
    Nonempty (FundamentalGroup A a ≃* FundamentalGroup X (i a)) :=
  ⟨MulEquiv.ofBijective (FundamentalGroup.map i a) (s78dg_pi1_deformation_bijective i r hri H hH a)⟩

end LiZhongQC
