/-
  Dolbeault ladder — manifold instantiation of the Čech finiteness node (Forster 14.9), TOP LAYER.

  The sup-norm Čech model TYPES and the abstract finiteness spine (`DiskOverlapData`,
  `Coboundaries`, `supH1`, `finiteDimensional_supH1`, `leray_surjective`,
  `exists_cechModel_of_subsingleton`) now live in `CechModelBase.lean`; this file is the thin top
  layer that wires the general-divisor model term `CechFinitenessDtwist.exists_cechModel_general`
  into `exists_cechModel`, and assembles the finiteness node `finiteDimensional_cechH1_wired`.

  The split (model types into `CechModelBase`, this file importing `CechFinitenessDtwist`) BREAKS
  what would otherwise be an import cycle: the model types are consumed by `CechModelArtificial` /
  `CechModelGeometry` (now repointed to `CechModelBase`), which feed `exists_cechModel_general`.

  Main results:
    * `exists_cechModel` — every finite cover `𝔘` and divisor `D` admits a chart-disk Leray model
      whose sup-norm `H¹` is `ℂ`-linearly isomorphic to the genuine germ-class `𝔘.cechH1 D`. Proven
      by `exists_cechModel_general` (the general-divisor skyscraper reduction of
      `CechFinitenessDtwist` onto the artificial finite-dimensional Montel model).
    * `cechH1_linearEquiv_supH1` — the correctly-scoped comparison consumer.
    * `finiteDimensional_cechH1_wired` — the finiteness node
      (`DolbeaultLadder.finiteDimensional_cechH1`).
-/
import Jacobians.Finiteness.CechFinitenessDtwist
open Jacobians.Dolbeault.CechFiniteness ContinuousLinearMap
open BoundedContinuousFunction
open scoped Manifold ContDiff Topology

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Existence of the chart-disk Leray model -/

/-- **The chart-disk Leray model exists and computes `cechH1`.**
Every finite cover `𝔘` and divisor `D` admits a chart-disk Leray model — a `DiskOverlapData`
(per-overlap chart-images as disks in `ℂ`, each with a relatively-compact shrinking) and a
`Coboundaries` bundle (the sup-norm `δ⁰/δ¹`, the restriction commuting square, AND the `leray`
disk-acyclicity witness) — whose sup-norm `H¹` is `ℂ`-linearly isomorphic to the genuine germ-class
`𝔘.cechH1 D`.

The comparison is bundled into the conclusion (rather than a free-`c` standalone) precisely because
`supH1` depends only on the model and `cechH1 D` only on `(𝔘, D)`: the isomorphism holds only for
the model *built from* `(𝔘, D)`.

proven by `CechFinitenessDtwist.exists_cechModel_general`: the general-divisor finiteness
`finiteDimensional_cechH1_general` (the Forster §16 skyscraper reduction climbing the `D = 0`
finiteness one point at a time) makes `𝔘.cechH1 D` finite-dimensional, and the artificial
finite-dimensional Montel model `exists_cechModel_of_finiteDimensional` then supplies a
`DiskOverlapData` + `Coboundaries` whose `supH1` is `ℂ`-linearly isomorphic to it. This is exactly
the statement of `DolbeaultLadder.finiteDimensional_cechH1`'s model-existence input. -/
theorem exists_cechModel (𝔘 : FiniteCover X) (D : Divisor X) :
    ∃ (d : DiskOverlapData) (c : Coboundaries d), Nonempty (𝔘.cechH1 D ≃ₗ[ℂ] c.supH1) :=
  exists_cechModel_general 𝔘 D

/-! ### The comparison to the germ-class `cechH1`

SOUNDNESS NOTE.  The comparison is bundled into `exists_cechModel`'s conclusion (above) rather than
stated as a standalone equivalence `(𝔘 D d c) → 𝔘.cechH1 D ≃ₗ c.supH1`.  The latter is FALSE for a
free `c`: `supH1` depends only on the model `c` while `cechH1 D` depends only on `(𝔘, D)`, so for an
unrelated acyclic model (e.g. one chart-disk with `supH1 = 0`) against a high-genus `(𝔘, D)` the two
sides have different dimensions.  The equivalence holds only for the model that is *built from*
`(𝔘, D)` — hence the existential `∃ d c, …` tying `c` to `(𝔘, D)`.  `cechH1_linearEquiv_supH1` below
is the corresponding correctly-scoped *consumer* (it extracts the bundled equivalence), kept as a
named, inspectable entry point. -/

/-! ### Discharging `finiteDimensional_cechH1` -/

/-- **The finiteness node, assembled.** `H¹(𝔘, 𝒪_D)` is finite-dimensional: take the chart-disk
Leray model with its comparison (`exists_cechModel`); its sup-norm `H¹` is
finite-dimensional by `finiteDimensional_supH1` (`ρ` compact via the Montel atom +
the Leray surjectivity `leray_surjective`); and the bundled comparison `cechH1 ≃ₗ supH1`
transports finiteness back to the germ-class `cechH1`. This discharges the exact statement of
`DolbeaultLadder.finiteDimensional_cechH1`. -/
theorem finiteDimensional_cechH1_wired (𝔘 : FiniteCover X) (D : Divisor X) :
    FiniteDimensional ℂ (𝔘.cechH1 D) := by
  obtain ⟨d, c, ⟨e⟩⟩ := exists_cechModel 𝔘 D
  haveI : FiniteDimensional ℂ c.supH1 := c.finiteDimensional_supH1 (leray_surjective d c)
  exact e.symm.finiteDimensional

end Jacobians.Dolbeault
