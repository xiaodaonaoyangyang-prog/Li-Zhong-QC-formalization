import LiZhongQC.Lemmas.QDReflectionAfterHalves
import LiZhongQC.Lemmas.QDReflectionPuncturePoles
import LiZhongQC.Lemmas.QDTransportZero
import LiZhongQC.Lemmas.QDSeamFill
import LiZhongQC.Lemmas.QDBoundaryExtension
import LiZhongQC.Lemmas.QDDecompRestrictionIdentity
open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- (S6b) Restriction: an admissible differential of `Fd` fixed by the conjugate transport along
`E ∘ J ∘ E⁻¹` is the transported seam-filled extension of some `q ∈ Q̃(S₀)` (its restriction to `S`,
extended to the boundary curves by the boundary jet (S6a) and to the punctures). -/
theorem s31qd_restriction {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {gd nd : ℕ} (Fd : FiniteTypeStructure (puncturedOpens Pd) gd nd 0)
    (E : Xd.carrier ≃ₜ Fd.X.carrier) (hE : IsBiholomorphic (E : Xd.carrier → Fd.X.carrier))
    (hEι : ∀ a : puncturedOpens Pd, E a.val = Fd.ι a)
    (hP : ∀ p : Xd.carrier, p ∈ Pd ↔ E p ∈ Fd.P)
    (T0 : admissibleQDSpace F →ₗ[ℝ] (Xd.carrier → ℂ → ℂ))
    (hT0 : ∀ q : admissibleQDSpace F,
      IsDiffFamily 2 0 (T0 q) ∧
      (∀ a : Xd.carrier, DifferentiableOn ℂ (T0 q a)
        ((chartAt ℂ a).target ∩ (chartAt ℂ a).symm ⁻¹' (↑Pd : Set Xd.carrier)ᶜ)) ∧
      (∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range ιd →
        T0 q x z = s31qr_positiveData F hd (q : F.X.carrier → ℂ → ℂ) x z) ∧
      (∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range (J ∘ ιd) →
        T0 q x z = s31qr_mirrorData F hd (q : F.X.carrier → ℂ → ℂ) x z) ∧
      (∀ a : Xd.carrier, ∀ p ∈ Pd, p ∈ (chartAt ℂ a).source → T0 q a (chartAt ℂ a p) = 0))
    {Q : Fd.X.carrier → ℂ → ℂ} (hQ : IsAdmissibleQD Fd Q)
    (hfix : s31qr_transportOn univ (fun y : Fd.X.carrier => E (J (E.symm y)))
      Complex.conjCLE.toLinearMap Q = Q) :
    ∃ q : admissibleQDSpace F, s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) (T0 q) = Q := by
  haveI : Nonempty S := inferInstance
  exact s31qd_restriction_from_extension F hm hd Fd E hE hP T0 hT0 hQ hfix
    (s31qd_boundary_extension F hm hd Fd E hE hP hQ hfix)

end LiZhongQC
