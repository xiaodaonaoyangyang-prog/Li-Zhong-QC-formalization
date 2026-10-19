import LiZhongQC.Ch07.S25_QuadraticDifferentials
import LiZhongQC.Lemmas.GeodesicExtraction
open Set
open scoped ENNReal Manifold ContDiff

namespace LiZhongQC

universe u
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- Every path class on a compact surface with a nonzero holomorphic quadratic
differential contains a finite-length geodesic. This supplies the existence half
of the uniqueness corollary without any uniqueness hypothesis. -/
theorem s25u_geodesic_exists [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] [CompactSpace S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {a b : S} (α : Path a b) :
    ∃ γ : Path a b, γ.Homotopic α ∧ IsPhiGeodesicRS q γ ∧ phiLengthPath q γ < ⊤ := by
  obtain ⟨β, hβα, hβfin⟩ := s25s_finite_rep hq hne α
  obtain ⟨γ, hγα, hmin⟩ := thm25_4_shortest_exists hq hne α
  have hγfin : phiLengthPath q γ < ⊤ := (hmin β hβα).trans_lt hβfin
  refine ⟨γ, hγα, ?_, hγfin⟩
  apply shortest_isPhiGeodesicRS hq hne _ hγfin
  intro γ' hγ'
  exact hmin γ' (hγ'.trans hγα)

end LiZhongQC

