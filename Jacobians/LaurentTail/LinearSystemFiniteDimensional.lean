/-
  `L(D)` is finite-dimensional — the cohomology bridge, packaged as an instance.

  The Laurent-tail route (Miranda Ch. VI) needs `dim L(D) < ∞` for its dimension bookkeeping
  (Lemma 2.3).  This follows from the Čech tower: `finiteDimensional_globalSections`
  (`H⁰(𝔘, 𝒪_D)` finite, Forster §16) transported along
  `globalSectionsEquivQuot : L(D)/germZero ≃ₗ H⁰(𝔘, 𝒪_D)` (`CechH0`), for the canonical
  chart-disk cover (`exists_realizableLerayCover`).  No new analysis — this file only registers
  the `FiniteDimensional ℂ (lSysModule D)` instance on the junk-free quotient whose `finrank`
  *is* `lDim D`.
-/
import Jacobians.CanonicalForms.CanonicalFormIso
import Jacobians.Finiteness.SkyscraperProductWitness
open scoped Manifold ContDiff Topology
open Module

namespace Jacobians.LaurentTail

open Jacobians Jacobians.Dolbeault

/-- `lDim D` is by definition the `finrank` of the junk-free linear-system module. -/
theorem lDim_eq_finrank_lSysModule {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : Divisor X) :
    lDim (X := X) D = finrank ℂ (lSysModule (X := X) D) := rfl

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **`L(D)/germZero` is finite-dimensional** (Forster §16 / Miranda Ch. VI Prop. 2.5, by the
Čech route: `h⁰(𝔘, 𝒪_D) < ∞` + the `H⁰ ≅ L(D)/germZero` bridge). -/
instance finiteDimensional_lSysModule (D : Divisor X) :
    FiniteDimensional ℂ (lSysModule (X := X) D) := by
  obtain ⟨𝔘, _, _⟩ := exists_realizableLerayCover (X := X)
  haveI := finiteDimensional_globalSections 𝔘 D
  exact (𝔘.globalSectionsEquivQuot D).symm.finiteDimensional

end Jacobians.LaurentTail
