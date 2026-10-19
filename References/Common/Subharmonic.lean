import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Data.EReal.Operations

/-!
# Shared layer: subharmonic and superharmonic functions of the plane

Subharmonic and superharmonic functions on open subsets of the plane `ℂ`, with values in the extended real line
`EReal` (DESIGN §2, shared layer; registry `refs_lean\FOUNDATIONS.md`). Mathlib and the project have no such notion.
Garnett–Marshall 2005 uses both notions without defining them (Ch. III: the logarithmic potential is superharmonic,
Lemma III.2.1; subharmonic functions in §III.8); later works need the same notions (capacity in Pommerenke 1992, the
Perron method in Forster and in Farkas–Kra).

The definition is the classical one by harmonic majorants on discs: `u` is subharmonic on the open set `U` if
`u < +∞` on `U`, `u` is upper semicontinuous on `U`, and for every closed disc `D̄ ⊆ U` and every function `h`
continuous on `D̄` and harmonic on the open disc `D` with `u ≤ h` on `∂D`, also `u ≤ h` on `D`. On an open set this
is equivalent to the local sub-mean-value inequality, which is not used here because it needs circle averages of
`EReal`-valued functions. The value `−∞` is allowed, and `u ≡ −∞` is admitted (as in Ransford, *Potential Theory in
the Complex Plane*, 1995); works that exclude it add the condition in their statements. The set `U` is open, a
conjunct of the definition: on a set that is not open the majorant condition can be vacuous (for `U = {p}` every `u`
with `u(p) < +∞` would qualify). Harmonic functions are Mathlib's `InnerProductSpace.HarmonicOnNhd` (real-valued
here).

* Shared notion (subharmonic function on an open subset of `ℂ`, `EReal`-valued, by harmonic majorants on closed
  discs) — `IsSubharmonicOn`
* Shared notion (superharmonic function: `−u` is subharmonic) — `IsSuperharmonicOn`
-/

open Set Metric

namespace References

/-- A subharmonic function on an open set `U ⊆ ℂ` (shared notion): `U` is open, and `u : ℂ → [−∞, +∞]` has `u < +∞`
on `U`, is upper semicontinuous on `U`, and has the harmonic-majorant property on every closed disc contained in `U`:
if the closed disc `D̄ = B̄(c, r)`, `r > 0`, lies in `U`, and `h` is continuous on `D̄`, harmonic on `D = B(c, r)` and
`u ≤ h` on `∂D`, then `u ≤ h` on `D`. The function `u ≡ −∞` is admitted (as in Ransford); works that exclude it add
the condition in their statements. Only the values of `u` on `U` matter. -/
def IsSubharmonicOn (u : ℂ → EReal) (U : Set ℂ) : Prop :=
  IsOpen U ∧ (∀ z ∈ U, u z < ⊤) ∧ UpperSemicontinuousOn u U ∧
    ∀ (c : ℂ) (r : ℝ), 0 < r → closedBall c r ⊆ U → ∀ h : ℂ → ℝ, ContinuousOn h (closedBall c r) →
      InnerProductSpace.HarmonicOnNhd h (ball c r) → (∀ ζ ∈ sphere c r, u ζ ≤ (h ζ : EReal)) →
        ∀ z ∈ ball c r, u z ≤ (h z : EReal)

/-- A superharmonic function on an open set `U ⊆ ℂ` (shared notion): `−u` is subharmonic on `U` (`IsSubharmonicOn`,
which includes that `U` is open); so `u > −∞` on `U`, `u` is lower semicontinuous on `U`, and `u ≥ h` on every open
disc `D` with `D̄ ⊆ U` for every `h` continuous on `D̄`, harmonic on `D` and `≤ u` on `∂D`. The function `u ≡ +∞` is
admitted. -/
def IsSuperharmonicOn (u : ℂ → EReal) (U : Set ℂ) : Prop :=
  IsSubharmonicOn (-u) U

end References
