import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-!
# Shared layer: hyperbolic convexity in `ℍ`

The one notion of this file, `HypConvex`, was moved out of `Common/HyperbolicSurface.lean` (definition and docstring
unchanged) so that modules that must not depend on the heavy hyperbolic-surface layer (for example `Katok1992.Ch03`,
which the Gardiner–Lakic Chapter 10 items point to) can use it.

* Shared notion (hyperbolic convexity of a subset of `ℍ`) — `HypConvex`
-/

noncomputable section

namespace References

/-- **Hyperbolic convexity** of `C ⊆ ℍ`: with two points, `C` contains the geodesic segment joining them. In `ℍ`
the segment from `z` to `w` is exactly the set of `u` with `d(z, u) + d(u, w) = d(z, w)`. -/
def HypConvex (C : Set UpperHalfPlane) : Prop :=
  ∀ z ∈ C, ∀ w ∈ C, ∀ u : UpperHalfPlane, dist z u + dist u w = dist z w → u ∈ C

end References
