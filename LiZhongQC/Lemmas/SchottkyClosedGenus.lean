import LiZhongExternal.Classification.SchottkyClassification28
import LiZhongQC.Lemmas.SchottkyGenusBridge4
import LiZhongQC.Lemmas.SchottkyNonOrientable

/-!
# Every closed Riemann surface has a genus

`s78fa_closed_surface_has_genus` is `closed_surface_has_genus` (§22.1, S22) with the book statement:
a compact connected Hausdorff Riemann surface has a genus.

* The complex charts give a `C⁰` structure over the half-space (`s78dg_halfspace_chartedSpace`), so
  the topological classification `classification_of_surfaces` applies.
* `s78dg_has_genus_of_cls` turns the classification into a genus, once the non-orientable normal
  forms `N_p` are excluded; `s78no_not_homeo_nonOrientable` excludes all of them (`p ≥ 1`).
-/

open LeanEval.Topology.ClassificationOfSurfaces Set Topology
open scoped Manifold ContDiff

noncomputable section
namespace LiZhongQC

universe u

/-- **§22.1: every closed Riemann surface has a genus** (the statement of `closed_surface_has_genus`). -/
theorem s78fa_closed_surface_has_genus {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    [CompactSpace S] : ∃ g : ℕ, HasGenus S g := by
  obtain ⟨cs⟩ := s78dg_halfspace_chartedSpace S
  have hcls :=
    letI := cs
    classification_of_surfaces S
  refine s78dg_has_genus_of_cls ?_ ?_ ?_
  · rcases hcls with h0 | ⟨p, n, ⟨hpn, h1⟩ | ⟨hp, h2⟩⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨p, n, hpn, h1⟩)
    · exact Or.inr (Or.inr ⟨p, n, hp, h2⟩)
  · intro p hp _
    exact s78no_not_homeo_nonOrientable S p (by omega)
  · exact s78no_not_homeo_nonOrientable S 1 le_rfl

section BookStatement

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- §22.1: every closed Riemann surface has a genus; it is unique by `closed_surface_genus_unique`.

**Statement change (2026-10-13, user decision).**  The statement was `∃! g : ℕ, HasGenus S g`.  It is
split into existence (this theorem) and uniqueness (`closed_surface_genus_unique`, proved).  For `g > 1`,
existence needs the topological classification of closed surfaces, i.e. a presentation of a cocompact
torsion-free Fuchsian group as `surfaceGroup g`, which is not formalized. -/
theorem closed_surface_has_genus [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    [CompactSpace S] : ∃ g : ℕ, HasGenus S g := by
  exact s78fa_closed_surface_has_genus

end BookStatement

end LiZhongQC
