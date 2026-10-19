import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Shared layer: Riemann surfaces

The convention for Riemann surfaces in `References` (DESIGN §2, shared layer; registry `refs_lean\FOUNDATIONS.md`;
leader rulings Forster1981 A0.1 and GardinerLakic2000 Part A item 4). A Riemann surface is a type `X` with the Mathlib
bundle

`[TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]`,

as in the project (`LiZhongQC/Ch06/S22_RiemannSurfaces.lean`): a connected Hausdorff space with an atlas of charts to
`ℂ` whose transition maps are complex analytic. Holomorphic maps between surfaces are `MDifferentiable 𝓘(ℂ) 𝓘(ℂ)`;
a chart of the maximal atlas is a member of `(contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X`. No second countability is
assumed. In statements the bundle is written as instance binders; `IsRiemannSurface` is the same condition as a
proposition, for conclusions of the form "there is a Riemann surface `Y` …", where instance binders cannot be used.
The project has no such predicate (it bundles closed surfaces as `LiZhongQC.ClosedRS` and surfaces of finite type as
`LiZhongQC.FiniteTypeRS`).

* Shared notion (Riemann surface, as a proposition on a charted space) — `IsRiemannSurface`
-/

open scoped Manifold ContDiff

namespace References

/-- A charted space `X` over `ℂ` is a Riemann surface (shared notion): it is Hausdorff and connected, and its atlas is
complex analytic (`IsManifold 𝓘(ℂ) ω X`). The binder form of the same condition is the standard bundle
`[T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]`. -/
def IsRiemannSurface (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  T2Space X ∧ ConnectedSpace X ∧ IsManifold 𝓘(ℂ) ω X

end References
