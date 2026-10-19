import LiZhongQC.Lemmas.QDReflectionAfterHalves
import LiZhongQC.Lemmas.QDReflectionPuncturePoles
import LiZhongQC.Lemmas.QDTransportZero
import LiZhongQC.Lemmas.QDSeamFill
open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}

/-- §31.2: for `m ≠ 0` every admissible differential `q ∈ Q̃(S₀)` extends symmetrically (by
reflection through `J`) to an admissible differential `q^d` on the double `S^d` (a meromorphic
quadratic differential with at most `2n` simple poles); `q ↦ q^d` is injective and real linear. -/
theorem admissibleQD_symmetric_extension [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    (Fd : FiniteTypeStructure (puncturedOpens Pd) (2 * g + m - 1) (2 * n) 0) :
    ∃ ext : admissibleQDSpace F →ₗ[ℝ] admissibleQDSpace Fd, Function.Injective ext := by
  classical
  obtain ⟨T, hT⟩ := s31qi_seam_fill F hm hd
  obtain ⟨E, hE, hEι, hEP⟩ := s31qr_fd_compactification Xd Pd Fd
  have hadm : ∀ q : admissibleQDSpace F,
      IsAdmissibleQD Fd (s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) (T q)) := by
    intro q
    obtain ⟨h1, h2, h3, h4, h5⟩ := hT q
    refine s31qr_fd_transport_admissible Xd Pd Fd E hE hEP h1 h2 ?_
    intro a p hp hs
    exact ⟨h5 a p hp hs, s31qi_puncture_poles F hm hd q (T q) h3 h4 a p hp hs⟩
  let tr : (Xd.carrier → ℂ → ℂ) →ₗ[ℝ] (Fd.X.carrier → ℂ → ℂ) :=
    { toFun := s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
      map_add' := fun q r => s31qr_transport_add _ _ _ q r
      map_smul' := fun c q => s31qr_transport_real_smul _ _ _ c q }
  let ext : admissibleQDSpace F →ₗ[ℝ] admissibleQDSpace Fd :=
    { toFun := fun q => ⟨tr (T q), hadm q⟩
      map_add' := fun q r => by
        apply Subtype.ext
        change tr (T (q + r)) = tr (T q) + tr (T r)
        rw [map_add, map_add]
      map_smul' := fun c q => by
        apply Subtype.ext
        change tr (T (c • q)) = c • tr (T q)
        rw [map_smul, map_smul] }
  refine ⟨ext, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro q hq0
  have h0 : tr (T q) = 0 := congrArg Subtype.val hq0
  obtain ⟨h1, h2, h3, h4, h5⟩ := hT q
  have hzero := s31qi_transport_zero Xd Pd Fd E hE h1 h0
  apply Subtype.ext
  haveI : Nonempty S := inferInstance
  refine s31qr_positive_restriction_recover F hd q.2 ?_
  intro x z hz hp
  rw [← h3 x z hz hp]
  exact hzero x z hz

end LiZhongQC
