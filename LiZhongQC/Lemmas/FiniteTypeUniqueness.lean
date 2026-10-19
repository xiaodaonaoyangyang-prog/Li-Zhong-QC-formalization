import LiZhongQC.Lemmas.FiniteTypeUniquenessProof

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- §31.1: the type `(g, n, m)` of a surface of finite type is well defined; the puncture
neighbourhoods are punctured discs and the hole neighbourhoods are annuli. -/
theorem finiteType_type_unique {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n m g' n' m' : ℕ} (h : IsFiniteType S g n m)
    (h' : IsFiniteType S g' n' m') : g = g' ∧ n = n' ∧ m = m' := by
  obtain ⟨F⟩ := h
  obtain ⟨F'⟩ := h'
  exact s31fu_type_unique_of_local_geometry F F'
    (fun j => (s31eg_disc_compact (F.disc j)).isClosed)
    (fun j => (s31eg_disc_compact (F'.disc j)).isClosed)
    (fun j A hA hDA => s31sh_surface_disc_shrink_away (F.disc j) hA hDA)
    (fun j A hA hDA => s31sh_surface_disc_shrink_away (F'.disc j) hA hDA)
    (fun p hp => s31eg_puncture_endpoint F F' hp)
    (fun p hp => s31eg_puncture_endpoint F' F hp)

end LiZhongQC
