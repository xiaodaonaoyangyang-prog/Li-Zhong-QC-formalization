import LiZhongQC.Lemmas.SchottkyIntrinsicBoundaryInvariant
import LiZhongExternal.Classification.SchottkyClassification01

open LeanEval.Topology.ClassificationOfSurfaces Set Topology

universe u

namespace LiZhongQC

/-- Every point of the 2-sphere has an open neighbourhood homeomorphic to the plane
(stereographic projection from the antipode). -/
theorem s78rb_sphere_plane_nbhd (x : SphereRepresentative) :
    ∃ U : Set SphereRepresentative, IsOpen U ∧ x ∈ U ∧
      Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hne : x ≠ -x := by
    intro h
    have h3 : ((x : SphereRepresentative) : EuclideanSpace ℝ (Fin 3)) =
        ((-x : SphereRepresentative) : EuclideanSpace ℝ (Fin 3)) := congrArg Subtype.val h
    have h4 : (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
      have h5 : (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
        have : -(x : EuclideanSpace ℝ (Fin 3)) = (x : EuclideanSpace ℝ (Fin 3)) := h3.symm
        rw [two_smul]
        nth_rewrite 1 [← this]
        simp
      exact (smul_eq_zero.1 h5).resolve_left (by norm_num)
    have := x.2
    rw [h4] at this
    simp at this
  let w : SphereRepresentative := -x
  refine ⟨({w}ᶜ : Set SphereRepresentative), isOpen_compl_singleton, hne, ⟨?_⟩⟩
  exact ((Homeomorph.setCongr (stereographic'_source (n := 2) w).symm).trans
    (((stereographic' 2 w).toHomeomorphSourceTarget).trans
      (Homeomorph.setCongr (stereographic'_target (n := 2) w)))).trans
    (Homeomorph.Set.univ _)

/-- **The core of a Schottky pair is not a sphere.**  With `m ≠ 0` holes the core has `m ≥ 1`
intrinsic boundary components, while every point of a sphere has a plane neighbourhood. -/
theorem s78rb_core_not_sphere {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [ConnectedSpace S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) (hm : m ≠ 0)
    (φ : s31dt_Core F ≃ₜ SphereRepresentative) : False := by
  have hcard := s78nm_components_card_of_homeomorph F φ
  have hpos : 0 < Nat.card (ConnectedComponents ↥{y : SphereRepresentative | ¬ ∃ U : Set SphereRepresentative,
      IsOpen U ∧ y ∈ U ∧ Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))}) := by
    rw [hcard]; exact Nat.pos_of_ne_zero hm
  obtain ⟨c⟩ := (Nat.card_pos_iff.1 hpos).1
  obtain ⟨y, -⟩ := ConnectedComponents.surjective_coe c
  exact y.2 (s78rb_sphere_plane_nbhd y.1)

end LiZhongQC
