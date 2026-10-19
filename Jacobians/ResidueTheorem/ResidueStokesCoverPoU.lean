/-
  The chart-cover partition of unity for the genus-uniform residue theorem.

  A clash-free re-derivation of the genuine-cover PoU of `ChartCoverDbarGlue.lean` (that file
  transitively imports `CechFinitenessBallSolve`, which cannot coexist with the
  `PairFormResidueTheorem` import chain — duplicate `rhoC` declarations).  Built directly on
  `CechModelGeometry` + `DiskAcyclicCore`'s `exists_smoothPartitionOfUnity_core`:

  * `coverPoU` — a smooth PoU over `𝓘(ℝ, ℂ)`, subordinate to the genuine Montel chart cover
    `(chartOpen (coverCenter j))_j`, summing to `1` on ALL of `X`;
  * `sum_coverPoU_eq_one`, `coverPoU_tsupport_subset`, `contMDiff_coverPoU`;
  * the complexified components `coverRhoC` with their sum/vanishing/continuity facts.

  Everything here is complete and depends on no unproved lemma.
-/
import Jacobians.Finiteness.CechModelGeometry
import Jacobians.Dbar.DiskAcyclicCore

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Jacobians.Montel Filter

namespace Jacobians.Dolbeault.StokesResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]

/-- The genuine chart cover covers `X` (inner shrinkings already cover, and
`innerShrunkChart ⊆ chartOpen`). -/
theorem iUnion_chartOpen_coverCenter_eq' {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ChartedSpace ℂ X] :
    (⋃ j : Fin ((chartCover : Finset X).card), chartOpen (X := X) (coverCenter j))
      = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← iUnion_innerShrunkChart_coverCenter_eq (X := X)]
  exact Set.iUnion_mono fun j => innerShrunkChart_subset_chartOpen (coverCenter j)

/-- A smooth PoU subordinate to the genuine chart cover, summing to `1` on all of `X`. -/
theorem exists_coverPoU :
    ∃ ρ : SmoothPartitionOfUnity (Fin ((chartCover : Finset X).card)) 𝓘(ℝ, ℂ) X Set.univ,
      ρ.IsSubordinate (fun j => chartOpen (X := X) (coverCenter j)) := by
  apply exists_smoothPartitionOfUnity_core
    (fun j => ⟨chartOpen (X := X) (coverCenter j), chartOpen_isOpen (coverCenter j)⟩)
    isClosed_univ
  rw [Set.univ_subset_iff]
  exact iUnion_chartOpen_coverCenter_eq'

/-- The chosen chart-cover PoU. -/
noncomputable def coverPoU :
    SmoothPartitionOfUnity (Fin ((chartCover : Finset X).card)) 𝓘(ℝ, ℂ) X Set.univ :=
  (exists_coverPoU (X := X)).choose

theorem coverPoU_subordinate :
    (coverPoU (X := X)).IsSubordinate (fun j => chartOpen (X := X) (coverCenter j)) :=
  (exists_coverPoU (X := X)).choose_spec

/-- `tsupport ρ_j ⊆ chartOpen (coverCenter j)`. -/
theorem coverPoU_tsupport_subset (j : Fin ((chartCover : Finset X).card)) :
    tsupport (coverPoU (X := X) j) ⊆ chartOpen (X := X) (coverCenter j) :=
  coverPoU_subordinate j

/-- `∑ j, ρ_j x = 1` at EVERY `x : X`. -/
theorem sum_coverPoU_eq_one (x : X) : ∑ j, (coverPoU (X := X)) j x = 1 :=
  smoothPartitionOfUnity_sum_eq_one_of_mem (coverPoU (X := X)) (Set.mem_univ x)

theorem contMDiff_coverPoU (j : Fin ((chartCover : Finset X).card)) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (coverPoU (X := X) j) :=
  (coverPoU (X := X) j).contMDiff

/-- The complexified PoU component `ρC_j : X → ℂ`. -/
noncomputable def coverRhoC (j : Fin ((chartCover : Finset X).card)) : X → ℂ :=
  fun x => ((coverPoU (X := X) j x : ℝ) : ℂ)

theorem continuous_coverRhoC (j : Fin ((chartCover : Finset X).card)) :
    Continuous (coverRhoC (X := X) j) :=
  Complex.continuous_ofReal.comp (contMDiff_coverPoU (X := X) j).continuous

theorem sum_coverRhoC_eq_one (x : X) : ∑ j, coverRhoC (X := X) j x = 1 := by
  have h := sum_coverPoU_eq_one (X := X) x
  show (∑ j, ((coverPoU (X := X) j x : ℝ) : ℂ)) = 1
  rw [← Complex.ofReal_sum]
  exact_mod_cast h

theorem coverRhoC_eq_zero_of_notMem (j : Fin ((chartCover : Finset X).card)) {x : X}
    (hx : x ∉ tsupport (coverPoU (X := X) j)) : coverRhoC (X := X) j x = 0 := by
  rw [coverRhoC, image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero]

/-- Off `tsupport ρ_j`, the (real) PoU component is locally `≡ 0` (the cst-germ form consumed by
the ledger kill conditions). -/
theorem coverPoU_eventually_zero_of_notMem (j : Fin ((chartCover : Finset X).card)) {x : X}
    (hx : x ∉ tsupport (coverPoU (X := X) j)) :
    ∀ᶠ x' in 𝓝 x, (coverPoU (X := X) j) x' = 0 := by
  filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hx] with x' hx'
  exact image_eq_zero_of_notMem_tsupport hx'

/-- `tsupport ρ_j` is compact (`X` is compact). -/
theorem isCompact_tsupport_coverPoU (j : Fin ((chartCover : Finset X).card)) :
    IsCompact (tsupport (coverPoU (X := X) j)) :=
  (isClosed_tsupport _).isCompact

end Jacobians.Dolbeault.StokesResidue
