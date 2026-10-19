import LiZhongExternal.Classification.SchottkyClassification01
import Mathlib

/-!
# Boundary rank, B2 (ii)(A): points of the open disc are Euclidean in a boundary gluing

In any quotient of the closed unit disc by a relation that only relates boundary points, the image of the
open disc is an open set homeomorphic to the plane.
-/

open Complex Set Topology LeanEval.Topology.ClassificationOfSurfaces

namespace LiZhongQC

/-- A chain of relations starting or ending at an interior point is trivial when only boundary points are
related. -/
theorem s78rb_eqvGen_interior (R : ClosedUnitDisc → ClosedUnitDisc → Prop)
    (hR : ∀ x y, R x y → ‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1) {a b : ClosedUnitDisc}
    (h : Relation.EqvGen R a b) : ‖(a : ℂ)‖ < 1 ∨ ‖(b : ℂ)‖ < 1 → a = b := by
  induction h with
  | rel x y hxy =>
      intro hxy'
      obtain ⟨hx, hy⟩ := hR x y hxy
      rcases hxy' with h' | h' <;> linarith
  | refl x => intro _; rfl
  | symm x y _ ih =>
      intro h'
      exact (ih h'.symm).symm
  | trans x y z _ _ ih1 ih2 =>
      intro h'
      rcases h' with h' | h'
      · have hxy := ih1 (Or.inl h')
        subst hxy
        exact ih2 (Or.inl h')
      · have hyz := ih2 (Or.inr h')
        subst hyz
        exact ih1 (Or.inr h')

/-- (A) Points of the open disc are Euclidean in any quotient of the closed disc by a relation that
only relates boundary points. -/
theorem s78rb_euclid_disc_interior (R : ClosedUnitDisc → ClosedUnitDisc → Prop)
    (hR : ∀ x y, R x y → ‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1)
    (z : ClosedUnitDisc) (hz : ‖(z : ℂ)‖ < 1) :
    ∃ U : Set (Quot R), IsOpen U ∧ Quot.mk R z ∈ U ∧
      Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
  let D : Set ClosedUnitDisc := {w | ‖(w : ℂ)‖ < 1}
  have hD : IsOpen D := isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  let e : D → Quot R := fun w => Quot.mk R w.1
  have hsat : ∀ (w : ClosedUnitDisc) (v : D), Quot.mk R w = Quot.mk R v.1 → w = v.1 := fun w v h =>
    s78rb_eqvGen_interior R hR (Quot.eqvGen_exact h) (Or.inr v.2)
  have hcont : Continuous e := continuous_quot_mk.comp continuous_subtype_val
  have hinj : Function.Injective e := fun v w h => Subtype.ext (hsat v.1 w h)
  have hopen : IsOpenMap e := by
    intro V hV
    rw [← isQuotientMap_quot_mk.isOpen_preimage]
    have : Quot.mk R ⁻¹' (e '' V) = Subtype.val '' V := by
      ext w
      constructor
      · rintro ⟨v, hv, hvw⟩
        exact ⟨v, hv, (hsat w v hvw.symm).symm⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v, hv, rfl⟩
    rw [this]
    exact hD.isOpenMap_subtype_val V hV
  have hemb : IsOpenEmbedding e := .of_continuous_injective_isOpenMap hcont hinj hopen
  refine ⟨range e, hemb.isOpen_range, ⟨⟨z, hz⟩, rfl⟩, ?_⟩
  -- `D ≃ₜ ball 0 1 ≃ₜ ℂ ≃ₜ ℝ²`
  let hball : D ≃ₜ Metric.ball (0 : ℂ) 1 :=
    { toFun := fun w => ⟨w.1.1, mem_ball_zero_iff.mpr w.2⟩
      invFun := fun b => ⟨⟨b.1, Metric.ball_subset_closedBall b.2⟩,
        show ‖(b.1 : ℂ)‖ < 1 from mem_ball_zero_iff.mp b.2⟩
      left_inv := fun w => rfl
      right_inv := fun b => rfl
      continuous_toFun :=
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      continuous_invFun :=
        ((continuous_subtype_val.subtype_mk _).subtype_mk _) }
  exact ⟨hemb.isEmbedding.toHomeomorph.symm.trans
    (hball.trans (Homeomorph.unitBall.symm.trans
      Complex.orthonormalBasisOneI.repr.toHomeomorph))⟩

end LiZhongQC
