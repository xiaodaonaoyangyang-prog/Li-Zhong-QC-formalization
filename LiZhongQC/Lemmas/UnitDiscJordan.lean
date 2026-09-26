import Mathlib
import LiZhongQC.Basic

open Complex Set Metric Filter Topology

namespace LiZhongQC

/-- `toExt` of a bounded open set has frontier `toExt` of the (plain) frontier: same argument as
the project's `frontier_toExt_of_isBounded` (Lemmas/Quadrilateral.lean), reproved here from
Mathlib alone since this leaf may only import `Basic`. -/
private theorem toExt_frontier_of_isBounded {A : Set ℂ} (hA : Bornology.IsBounded A)
    (hAo : IsOpen A) : frontier (toExt A) = toExt (frontier A) := by
  have hclosure : closure (toExt A) = toExt (closure A) := by
    unfold toExt
    refine subset_antisymm (closure_minimal (image_mono subset_closure) ?_)
      (image_closure_subset_closure_image OnePoint.continuous_coe)
    exact OnePoint.isClosed_image_coe.2 ⟨isClosed_closure, hA.isCompact_closure⟩
  have hopen' : IsOpen (toExt A) := OnePoint.isOpen_image_coe.2 hAo
  rw [hopen'.frontier_eq, hclosure, hAo.frontier_eq]
  unfold toExt
  exact (image_diff OnePoint.coe_injective _ _).symm

theorem frontier_toExt_unitDisc : frontier (toExt unitDisc) = toExt (Metric.sphere (0 : ℂ) 1) := by
  unfold unitDisc
  rw [toExt_frontier_of_isBounded isBounded_ball isOpen_ball, frontier_ball (0 : ℂ) one_ne_zero]

theorem isJordanCurve_toExt_unitCircle : IsJordanCurve (toExt (Metric.sphere (0 : ℂ) 1)) := by
  refine ⟨fun θ => ((θ : ℂ) : ExtPlane), ?_, ?_, ?_⟩
  · exact OnePoint.continuous_coe.comp continuous_subtype_val
  · exact fun a b hab => Circle.coe_injective (OnePoint.coe_injective hab)
  · unfold toExt
    ext w
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨θ, rfl⟩
      exact ⟨(θ : ℂ), mem_sphere_zero_iff_norm.2 (Circle.norm_coe θ), rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩

theorem isJordanDomain_unitDisc : IsJordanDomain unitDisc := by
  refine ⟨isOpen_ball, isConnected_ball one_pos, ?_⟩
  rw [frontier_toExt_unitDisc]
  exact isJordanCurve_toExt_unitCircle

end LiZhongQC
