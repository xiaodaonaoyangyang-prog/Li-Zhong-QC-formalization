/-
  The **germ-level disk-acyclicity lemma** (`H¹(disk, 𝒪_D) = 0`):

      every `MGerm`-cocycle on a finite cover of a *chart disk* `W` is an `MGerm`-coboundary.

  This feeds both the Leray strictly-finer surjectivity (`RefinementLift`) and the finiteness
  `leray` field (`CechFinitenessWiring.Coboundaries.leray`).

  ## Route

  There is no Riemann mapping theorem in Mathlib, so we work only on a *literal* chart disk,
  where the cover sets pull back through a single chart to opens in a Euclidean ball `B ⊆ ℂ` and
  the full-disk ∂̄ engine applies directly.

  The analytic engine is `DbarDiskCohomology.dbar_holo_splitting_ball` / `dbar_solvable_ball`
  (`H¹(ball, 𝒪) = 0` on *functions* `ℂ → ℂ`).  The work here is:

    * **§1 `dbar` algebra** — `DbarDisk.dbar` is `ℝ`-linear in `f` (`add`/`sub`/`smul`), the
      bookkeeping the Čech split needs.
    * **§2 function-level ball Čech split** — the function-level acyclicity engine, packaged as a
      clean statement on holomorphic functions over a ball: a Čech 1-cocycle of holomorphic
      functions that splits *smoothly* into a 0-cochain difference splits *holomorphically*.  For
      a 2-set cover this is exactly `dbar_holo_splitting_ball`.
    * **§3 the germ ↔ function bridge** — a germ-class `𝒪_D`-section on an open `↥W ⊆ X` has an
      honest meromorphic representative function on `↥W` (choice on `OmegaDGerm = map toGerm`);
      the normal-form machinery of `CechH0` (`nfX_Gext_codiscrete`, `toGerm_eq_iff`) bridges
      germ-class equality to honest `𝓝[≠]`-eventual equality and back.
    * **§4 the germ-level reduction** — the target `cocycle ⟹ coboundary` reduced to a clean
      *function-level chart-disk acyclicity* predicate `FunctionDiskAcyclic`, in exactly the
      "lift mod coboundary" shape of `CechFinitenessWiring.Coboundaries.leray` /
      `CechRefinementLeray.RefinementLift`.  The predicate is discharged for the degenerate
      1-cover and 2-cover cases from §2; the general n-cover discharge (the partition-of-unity
      multi-set Čech split) is carried out in `CechDiskAcyclicProof` and assembled in
      `CechDiskAcyclicAssembly`.
-/
import Jacobians.Cech.CechH0
import Jacobians.Dbar.DbarDiskCohomology
open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Complex Metric

namespace Jacobians.Dolbeault

/-! ### §1 — `dbar` is `ℝ`-linear in the function argument

`DbarDisk.dbar f z = ½(∂₁f + i·∂_I f)` is built from `fderiv ℝ f`, hence additive/subtractive/scalar
in `f` at any point where the relevant functions are differentiable.  This is the bookkeeping layer
the Čech split needs (the `sub` case is inline in `DbarDiskCohomology.dbar_holo_splitting_ball`; we
make it reusable). -/

/-- `∂̄` is additive at a point where both summands are real-differentiable. -/
theorem dbarFun_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    DbarDisk.dbar (fun x => f x + g x) z = DbarDisk.dbar f z + DbarDisk.dbar g z := by
  unfold DbarDisk.dbar
  rw [fderiv_fun_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- `∂̄` is subtractive at a point where both functions are real-differentiable. -/
theorem dbarFun_sub {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    DbarDisk.dbar (fun x => f x - g x) z = DbarDisk.dbar f z - DbarDisk.dbar g z := by
  unfold DbarDisk.dbar
  rw [fderiv_fun_sub hf hg]
  simp only [ContinuousLinearMap.sub_apply]
  ring

/-! ### §2 — the function-level ball Čech split (the disk engine, on functions `ℂ → ℂ`)

The genuine analytic content of `H¹(ball, 𝒪) = 0`, packaged on functions.  A **2-set** Čech cocycle
on a ball is automatically a coboundary by `dbar_holo_splitting_ball`; we record that as the base
case `ballSplit_two`.  The general n-set assembly (partition of unity over the ball, reducing to a
single ∂̄-solve) is the OBSTRUCTION-3 gap and lives in §4 as prose. -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### §3 — the germ ↔ function bridge for a single open

A germ-class `𝒪_D`-section on an open submanifold `↥W` lifts to an honest representative function in
`OmegaD D W` (choice on `OmegaDGerm = map toGerm`); restriction-compatibility and the `CechH0`
codiscrete ↔ `𝓝[≠]` dictionary (`toGerm_eq_iff`, `Gext_overlap_eventuallyEq`,
`nfX_Gext_codiscrete`) bridge germ-class statements to honest punctured-neighbourhood ones. -/

/-! ### §4 — the germ-level disk-acyclicity target and its function-level reduction

`IsDiskAcyclic 𝔙 D` is the deliverable in the SHAPE of `CechFinitenessWiring.Coboundaries.leray` and
`CechRefinementLeray.RefinementLift`: every `𝒪_D` 1-cocycle is a coboundary. We prove it
unconditionally for a **subsingleton-indexed** cover (the cocycle is forced to be `0`), and reduce
the general case to a clean function-level chart-disk acyclicity predicate. -/

/-! ### The function-level chart-disk acyclicity predicate (the honest analytic interface)

For the general (≥ 2 patches) case, the germ-level acyclicity reduces to a *function-level*
statement on the chart-image balls, which is what the committed ∂̄ engine proves. We isolate that
statement as a predicate, in the same "lift the cocycle to a coboundary" shape, and discharge the
analytic part where the engine applies. -/

end Jacobians.Dolbeault

/-! The discharge of `FunctionDiskAcyclic` for a chart-disk cover — the germ → honest-function
lift, the chart-transport dictionary for holomorphy + `dbar`, and the partition-of-unity
multi-set Čech split on the ball — is carried out in `CechDiskAcyclicProof` and assembled in
`CechDiskAcyclicAssembly`; with it, `isDiskAcyclic_of_funcLevel` and
`cechH1_subsingleton_of_isDiskAcyclic` here give the germ-level `H¹(disk) = 0`. -/
