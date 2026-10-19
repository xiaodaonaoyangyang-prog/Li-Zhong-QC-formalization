/-
  The **closed-core** partition-of-unity primitives for the disk-acyclicity.

  A `SharedChartCover` is a finite *family* of opens living in one chart (not a cover of compact
  `X` — a single chart cannot cover a compact connected surface).  The disk-acyclicity globalizes
  a cocycle with a smooth partition of unity `ρ` subordinate to the family `(Uᵢ)`.  A subordinate
  PoU *cannot* sum to `1` on the open `⋃ Uᵢ`: that would force `⋃ Uᵢ` clopen, hence `= X` on
  connected `X`.

  Instead, sum to `1` only on a **closed core** `C ⊆ ⋃ Uᵢ`.  Mathlib's
  `SmoothPartitionOfUnity.exists_isSubordinate` takes a *closed* `s ⊆ ⋃ Uᵢ`; with `s := C` it
  gives a subordinate PoU summing to `1` on `C` — no clopen issue.  Since every pairwise overlap
  of a `SharedChartCover` lies in `interior C`, the cocycle germ-splitting (consumed only at
  overlap points) happens exactly where `∑ ρ = 1` on a neighbourhood.

  The lemmas are stated abstractly over a finite family `U : ι → Opens X` and a closed
  `C ⊆ ⋃ Uᵢ`, so they are independent of the `SharedChartCover` packaging and reusable for any
  closed-core globalization.
-/
import Jacobians.Surface.RealManifold
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ## The closed-core subordinate partition of unity

A compact `T2` `ℂ`-manifold is a `σ`-compact finite-dimensional real manifold (over `𝓘(ℝ, ℂ)`), so
Mathlib's manifold PoU applies. We expose the closed-core existence and the sum-on-`C` value form.
-/

/-- **Closed-core subordinate PoU exists.**  For a finite family of opens `U : ι → Opens X` and a
CLOSED set `C ⊆ ⋃ i, Uᵢ`, there is a smooth partition of unity over `𝓘(ℝ, ℂ)`, subordinate to `(Uᵢ)`
(`tsupport ρᵢ ⊆ Uᵢ`), summing to `1` on `C`. This is the sound replacement for the (vacuous on a
single-chart family) `univ`-subordinate PoU: the closed set `C` is the sum-to-one locus, avoiding
the clopen obstruction. Direct application of `SmoothPartitionOfUnity.exists_isSubordinate` with
`s := C`. -/
theorem exists_smoothPartitionOfUnity_core [T2Space X] [SigmaCompactSpace X] [IsManifold 𝓘(ℂ) ω X]
    {ι : Type} [Fintype ι] (U : ι → Opens X)
    {C : Set X} (hCclosed : IsClosed C) (hCsub : C ⊆ ⋃ i, (U i : Set X)) :
    ∃ ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) X C,
      ρ.IsSubordinate (fun i => (U i : Set X)) :=
  SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) hCclosed
    (fun i => (U i : Set X)) (fun i => (U i).isOpen) hCsub

/-- **Sum-to-one on the core**, value form: a PoU over the closed set `C` sums to `1` at every
point of `C`.  (Repackages Mathlib's `SmoothPartitionOfUnity.sum_eq_one` with the
`finsum = Finset.sum` collapse for the `Fintype` index.) -/
theorem smoothPartitionOfUnity_sum_eq_one_of_mem {ι : Type} [Fintype ι] {C : Set X}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) X C) {x : X} (hx : x ∈ C) :
    ∑ i, ρ i x = 1 := by
  rw [← finsum_eq_sum_of_fintype]; exact ρ.sum_eq_one hx

end Jacobians.Dolbeault
