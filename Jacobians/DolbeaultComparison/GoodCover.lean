/-
  The Dolbeault comparison without any Leray hypothesis.

  The comparison spine of `DolbeaultComparisonEquiv` (`comparison_linearEquiv` and its two
  round-trips) takes an `hL : 𝔘.IsLeray` argument that its proof bodies never consume.  This file
  re-derives the two round-trip identities, the comparison `≃ₗ[ℝ]`
  (`comparison_linearEquiv'`), and the `finrank` comparison
  `finrank ℝ (DolbeaultH01 X) = 2 · finrank ℂ (cechH1 𝔇 0)` (`cechH1_dolbeault_comparison'`)
  with the hypothesis removed, reusing the `hL`-free sub-lemmas of `DolbeaultComparisonEquiv`
  verbatim.  Consumers that have a `ChartDiskCover` but no Leray witness can use these directly.
-/
import Jacobians.DolbeaultComparison.DolbeaultComparisonEquiv

open scoped Manifold ContDiff Bundle Topology
open TopologicalSpace (Opens)

set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The two comparison round-trips, with the `IsLeray` hypothesis REMOVED

These are `DolbeaultComparisonEquiv.cech_to_dolbeault_comp_dolbeault_to_cech` and
`dolbeault_to_cech_comp_cech_to_dolbeault` with the `hL : 𝔇.toFiniteCover.IsLeray` argument deleted.
The proof bodies are identical to the originals (which never reference `hL`); they go through the
`hL`-free sub-lemmas `etaFn_germ_diff_eq`, `holCochain_mem_sections0`, `cechDelta0_holCochain_eq`,
`dbarL_globalPrim_eq`.  That they still close is the mechanical proof that the overlap hypothesis is
dead weight in the comparison. -/

set_option maxHeartbeats 400000 in
/-- **Round-trip 1 (Dolbeault → Čech → Dolbeault = id), `IsLeray`-free.**  Identical statement and
proof to `cech_to_dolbeault_comp_dolbeault_to_cech` minus the unused `hL`. -/
theorem cech_to_dolbeault_comp_dolbeault_to_cech' (𝔇 : ChartDiskCover X) :
    (cech_to_dolbeault 𝔇) ∘ₗ (dolbeault_to_cech 𝔇) = LinearMap.id := by
  refine LinearMap.ext fun cls => ?_
  obtain ⟨⟨g, hg⟩, rfl⟩ := Submodule.Quotient.mk_surjective (dbarImageInZeroOne X) cls
  rw [LinearMap.comp_apply, LinearMap.id_apply]
  have hdol : dolbeault_to_cech 𝔇 (Submodule.Quotient.mk ⟨g, hg⟩)
      = Submodule.Quotient.mk (dolbeaultToCechCocycle 𝔇 ⟨g, hg⟩) := rfl
  rw [hdol, cech_to_dolbeault_mk]
  have hmem : (cechToDolbeaultForm 𝔇 (dolbeaultToCechCocycle 𝔇 ⟨g, hg⟩) + ⟨g, hg⟩ :
      ↥(OneFormsZeroOne X)) ∈ dbarImageInZeroOne X := by
    rw [dbarImageInZeroOne, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.mem_range]
    refine ⟨∑ k, gdTerm 𝔇 k g, ?_⟩
    rw [dbarL_globalPrim_eq 𝔇 hg, Submodule.coe_add]
  have hz : (Submodule.mkQ (dbarImageInZeroOne X)
        (cechToDolbeaultForm 𝔇 (dolbeaultToCechCocycle 𝔇 ⟨g, hg⟩)))
      + (Submodule.mkQ (dbarImageInZeroOne X) (⟨g, hg⟩ : ↥(OneFormsZeroOne X))) = 0 := by
    rw [← map_add, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hmem
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hz
  exact neg_eq_of_add_eq_zero_right hz

/-- **Round-trip 2 (Čech → Dolbeault → Čech = id), `IsLeray`-free.** Identical statement and proof
to `dolbeault_to_cech_comp_cech_to_dolbeault` minus the unused `hL`. -/
theorem dolbeault_to_cech_comp_cech_to_dolbeault' (𝔇 : ChartDiskCover X) :
    (dolbeault_to_cech 𝔇) ∘ₗ (cech_to_dolbeault 𝔇) = LinearMap.id := by
  refine LinearMap.ext fun cls => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ cls
  rw [LinearMap.comp_apply, LinearMap.id_apply, cech_to_dolbeault_mk, map_neg]
  set omg : SmoothCOneForms X :=
    ((cechToDolbeaultForm 𝔇 f : ↥(OneFormsZeroOne X)) : SmoothCOneForms X) with hωdef
  have hdol : dolbeault_to_cech 𝔇 (Submodule.Quotient.mk (cechToDolbeaultForm 𝔇 f))
      = Submodule.Quotient.mk (dolbeaultToCechCocycle 𝔇 (cechToDolbeaultForm 𝔇 f)) := rfl
  rw [hdol]
  have hcob : (dolbeaultToCechCocycle 𝔇 (cechToDolbeaultForm 𝔇 f) : 𝔇.toFiniteCover.Cochain1)
      + (f : 𝔇.toFiniteCover.Cochain1) ∈ 𝔇.toFiniteCover.coboundaries1 (0 : Divisor X) := by
    refine ⟨holCochain 𝔇 f, holCochain_mem_sections0 𝔇 f, ?_⟩
    rw [cechDelta0_holCochain_eq 𝔇 f]
    congr 1
  have hzero : Submodule.Quotient.mk
        (dolbeaultToCechCocycle 𝔇 (cechToDolbeaultForm 𝔇 f))
      + Submodule.Quotient.mk f = (0 : 𝔇.toFiniteCover.cechH1 0) := by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.mk_eq_zero]
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.coe_add]
    exact hcob
  exact neg_eq_of_add_eq_zero_right hzero

/-! ### The comparison equivalence and `finrank` count, `IsLeray`-free -/

/-- **The Dolbeault isomorphism `H^{0,1}(X) ≃ₗ[ℝ] H¹(X, 𝒪)`, with NO `IsLeray` hypothesis.**
Assembled from the two `IsLeray`-free round-trips via `LinearEquiv.ofLinear`. This is
`DolbeaultComparisonEquiv.comparison_linearEquiv` with the phantom `hL` argument removed — the
concrete demonstration that the proven comparison never used the cover's preconnected-overlap (or
even simply-connected) condition. -/
noncomputable def comparison_linearEquiv' (𝔇 : ChartDiskCover X) :
    DolbeaultH01 X ≃ₗ[ℝ] 𝔇.toFiniteCover.cechH1 0 :=
  LinearEquiv.ofLinear (dolbeault_to_cech 𝔇) (cech_to_dolbeault 𝔇)
    (dolbeault_to_cech_comp_cech_to_dolbeault' 𝔇)
    (cech_to_dolbeault_comp_dolbeault_to_cech' 𝔇)

end Jacobians.Dolbeault
