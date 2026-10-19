import LiZhongQC.Lemmas.QDReflectionAfterHalves
open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- Zero transport forces a zero coefficient family: at every point the transport value is the centre value
times the square of a nonzero coordinate derivative, and the tensor law reaches all chart values. -/
theorem s31qi_transport_zero
    (Xd : ClosedRS.{u}) (Pd : Finset Xd.carrier) {gd nd : ℕ}
    (Fd : FiniteTypeStructure (puncturedOpens Pd) gd nd 0)
    (E : Xd.carrier ≃ₜ Fd.X.carrier) (hE : IsBiholomorphic (E : Xd.carrier → Fd.X.carrier))
    {Q : Xd.carrier → ℂ → ℂ} (hQ : IsDiffFamily 2 0 Q)
    (h0 : s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q = 0) :
    ∀ x z, z ∈ (chartAt ℂ x).target → Q x z = 0 := by
  classical
  intro x z hz
  have hs0 : (chartAt ℂ x).symm z ∈ (chartAt ℂ ((chartAt ℂ x).symm z)).source :=
    mem_chart_source ℂ _
  have hcenter : Q ((chartAt ℂ x).symm z)
      (chartAt ℂ ((chartAt ℂ x).symm z) ((chartAt ℂ x).symm z)) = 0 := by
    set p : Xd.carrier := (chartAt ℂ x).symm z with hp
    let y : Fd.X.carrier := E p
    let w : ℂ := chartAt ℂ y y
    have hw : w ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source (mem_chart_source ℂ y)
    have hleft : (chartAt ℂ y).symm w = y := (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hH : E.symm y = p := E.symm_apply_apply p
    have hder := s31qr_coordinate_deriv_ne_zero (U := (univ : Set Fd.X.carrier)) isOpen_univ
      (H := (E.symm : Fd.X.carrier → Xd.carrier))
      (fun u _ => hE.homeomorph_symm.1 u) E.symm.injective.injOn y p hw (mem_univ _)
      (by rw [hleft, hH]; exact mem_chart_source ℂ p)
    have hval := congrFun (congrFun h0 y) w
    have hguard : w ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm w ∈ (univ : Set Fd.X.carrier) :=
      ⟨hw, mem_univ _⟩
    simp only [s31qr_transportOn, hguard, and_self, if_true, Pi.zero_apply, hleft, hH] at hval
    exact (mul_eq_zero.1 hval).resolve_right (pow_ne_zero 2 hder)
  have hT : chartTransition ((chartAt ℂ x).symm z) x z =
      chartAt ℂ ((chartAt ℂ x).symm z) ((chartAt ℂ x).symm z) := rfl
  rw [hQ.2 ((chartAt ℂ x).symm z) x z hz hs0, hT, hcenter]
  simp

end LiZhongQC
