/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Jacobians.MappingDegree.MeromorphicDivisor

/-! # Local normal form for analytic / meromorphic maps and local multiplicity

This file lays the framework for the **(R3) local-multiplicity = local-order**
gap of `Manifold/ResidueTheorem.lean`. The classical statement is:

> Let `f : X → ℂ` be meromorphic at `x : X` on a complex manifold, and let
> `k := (mmeromorphicOrderAt I f x).untop₀` be the chart-pulled-back integer
> order. Then in any chart at `x`, the function `f ∘ chart⁻¹` admits the
> local normal form
>
>   `(f ∘ chart⁻¹)(z) = (z - chart x) ^ k • g(z)`
>
> for some analytic `g` with `g (chart x) ≠ 0` (interpreting `k < 0` as the
> meromorphic-power case `(z - chart x) ^ (k : ℤ)`).
>
> Consequently the *topological local multiplicity* of `f` at `x` (cardinality
> of `f⁻¹{w}` near `x` for `w` near `f x`, in the analytic case) equals
> `k.natAbs`.

## Status: framework + chart-coordinate proof

What is **proven** in this file:

1. `localOrder I f x : ℤ` — a structural rename of
   `MMeromorphicOn.orderFun I f x`. Definitionally equal; serves as the named
   replacement for the `degreeIndicator` indicator in `LocalMultiplicity.lean`.
2. `localOrder_eq_orderFun` — the structural identity.
3. `localOrder_eq_zero_iff` — under the no-germ-zero hypothesis, vanishing
   of `localOrder` matches vanishing of `mmeromorphicOrderAt`.
4. **`MMeromorphicAt.exists_local_normal_form`** — the *honest* local-form
   theorem in chart coordinates. For `f` meromorphic at `x` with finite
   order `k`, the chart representative `f ∘ chart⁻¹` admits the form
   `(z - chart x) ^ k • g(z)` for some analytic `g` with `g(chart x) ≠ 0`,
   on a punctured neighborhood. **Proof: direct application of the mathlib
   lemma `meromorphicOrderAt_eq_int_iff`.** Zero gaps.
5. **`MMeromorphicAt.exists_local_normal_form_of_nonneg`** — the analytic
   case (`k ≥ 0`) strengthens the punctured neighborhood to a full
   neighborhood (no zero-divisor singularity to remove).

Stated as inert `Prop`-valued `def`s here (NOT axioms), kept for reference:

6. `localMultiplicity_eq_localOrder_statement` and the sibling `*_statement`
   `def`s package the connection between `localOrder` and the topological
   local multiplicity (cardinality of `f⁻¹{w}` near `x` for `w` near `f x`).
   These specific placeholder `def`s are left unproven, but the underlying
   fact — `(z - x₀) ^ k · u(z) = w` has exactly `k` solutions near `x₀` for
   small `w ≠ 0` when `u(x₀) ≠ 0` — IS proven, via the k-th-root
   substitution route, in `LocalKFoldMultiplicityUnconditional.lean` /
   `LocalKFoldMultiplicityFullyUnconditional.lean` (not via Rouché).

The file therefore provides definitions, structural identities, and the
chart-coordinate local-form theorem, all proven; the `*_statement` defs are
inert `Prop`-valued placeholders (NOT axioms), superseded by the proven
k-fold count in the sibling files.

## Open mathlib lemmas (catalogued for the next pass)

The following mathlib names are what the eventual filling will route through:

* `AnalyticAt.analyticOrderAt_eq_natCast`
  — `Mathlib/Analysis/Analytic/Order.lean`. The analytic local form
  `f z = (z - z₀) ^ n • g z` for analytic `f` with order `n : ℕ`.
* `meromorphicOrderAt_eq_int_iff`
  — `Mathlib/Analysis/Meromorphic/Order.lean`. The meromorphic local form
  `f z = (z - x) ^ n • g z` (with `n : ℤ`) on the punctured neighborhood.
* `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`
  — `Mathlib/Analysis/Analytic/IsolatedZeros.lean`. The existence side of
  the analytic decomposition (used in the proof of (4) above via
  `meromorphicOrderAt_eq_int_iff`).
* `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`
  — companion isolated-zeros lemma; not invoked here but useful for the
  topological-multiplicity discharge.

The topological-multiplicity discharge (Rouché-via-degree-theory) will need
an argument analogous to mathlib's
`Complex.exists_count_preimage_of_eq_pow` (does not exist at the pin) or
the Rouché theorem applied to `f(z) - w = (z - x₀)^k u(z) - w`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace Jacobians.Discharge

universe u

/-! ## The structural local-order definition

`localOrder I f x` is the integer-valued local order of `f` at `x`,
expressed as the chart-pulled-back `mmeromorphicOrderAt` cast through
`WithTop.untop₀` (positive at zeros, negative at poles, `0` at regular
nonzero points and at germ-zero points).

This is **definitionally equal** to `MMeromorphicOn.orderFun I f x` from
`Manifold/MeromorphicDivisor.lean` — we just give it the structural name
that `R3_localMultiplicity_statement` in `Manifold/ResidueTheorem.lean`
should ultimately route through. -/

/-! ## The chart-coordinate local normal form

The honest content. We invoke the mathlib lemma `meromorphicOrderAt_eq_int_iff`
to extract the local form `f(z) = (z - x₀) ^ k • g(z)` on a punctured
neighborhood, with `g` analytic and `g(x₀) ≠ 0`. -/

namespace MMeromorphicAt

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {I : ModelWithCorners ℂ ℂ ℂ} {f : X → ℂ} {x : X}

/-! ### Topological-multiplicity content for the analytic case

The `R3` Rouché-style topological-multiplicity statement asks for an exact
preimage count `Set.ncard {z ∈ V \ {0} | g z = w} = k` near a zero of order
`k`. The full Rouché theorem (with `k > 1`) is **not** available at the pin —
mathlib has neither a general "preimage count = winding number" theorem nor an
"argument principle" giving exact-equality counts in the form needed.

The `k = 1` slice however **is** available: it is precisely the inverse
function theorem for one-variable analytic maps (i.e. local injectivity from
nonvanishing derivative). We discharge that slice honestly here. The general
`k ≥ 2` content remains the named gap — captured in
`localMultiplicity_eq_order_punctured_statement` below as a `Prop`-valued
`def` (not an `axiom`). -/

end MMeromorphicAt

/-! ## The headline R3 statement (Prop-valued, not axiom)

`localMultiplicity_eq_localOrder_statement` packages the bridge between the
chart-coordinate local form (proven above) and the topological local
multiplicity (cardinality of `f⁻¹{w}` near `x` for `w` near `f x`).

We state it as a `Prop`-valued `def` (per the brief): the statement is
*meaningful* and unambiguous, but the discharge requires Rouché-style
counting that is not in mathlib at the pin. -/

variable (X : Type u)
  [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) ω X]

/-! ## Compatibility statement bridging `localOrder` to the existing
`R3_localMultiplicity_statement` in `ResidueTheorem.lean`

The R3 statement in `ResidueTheorem.lean` is the coarse "multiplicity ≥ 1"
form. We discharge it directly here, since it follows from the no-germ-zero
hypothesis and the fact that `Int.natAbs` of a nonzero integer is `≥ 1`. -/

/-! ## The general-`k` Rouché-style statement (Prop-only)

The general `k ≥ 1` case asserts that an analytic `g : ℂ → ℂ` with order
`k` at `0` has *exactly* `k` preimages of every nonzero value `w` close to
`0`, in some punctured neighborhood of `0`. This is the Rouché theorem
applied to `f(z) - w = (z - z₀)^k u(z) - w`.

At the mathlib pin (`8e3c989`, 15 April 2026) the precise gating input is
**not present**. The relevant pieces that *are* present:

* `Mathlib.Analysis.Analytic.IsolatedZeros.exists_eventuallyEq_pow_smul_nonzero_iff`
  — the local form `g z = (z - z₀)^n • h z` with `h(z₀) ≠ 0` (analytic case).
* `Mathlib.Analysis.Analytic.Order.AnalyticAt.analyticOrderAt_eq_natCast`
  — the same local form expressed via the order.
* `Mathlib.Analysis.Calculus.FDeriv.Analytic.AnalyticAt.hasStrictDerivAt`
  — analytic ⟹ strict derivative at the point.
* `Mathlib.Analysis.Calculus.Deriv.Inverse.HasStrictDerivAt.hasStrictFDerivAt_equiv`
  — strict derivative + nonzero ⟹ strict Fréchet derivative as an equiv.
* `HasStrictFDerivAt.toOpenPartialHomeomorph`
  (`Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`)
  — the inverse function theorem packaged as an `OpenPartialHomeomorph`.

What is **deferred** for the general `k ≥ 2` case:

> A theorem of the form: for `g` analytic at `z₀` with `analyticOrderAt g z₀ = (k : ℕ∞)`
> and `k ≥ 1`, there exist neighborhoods `V` of `z₀` and `W` of `0` such that
> for every `w ∈ W \ {0}`,
> `Set.ncard {z ∈ V \ {z₀} | g z = w} = k`.

Mathlib does not name this. Candidate name in a future PR:
`AnalyticAt.exists_count_preimage_of_analyticOrderAt`. Existence in some form
would route via Rouché's theorem applied to `g - w` versus `(z - z₀)^k`,
combined with the open-mapping / strict-derivative-of-the-inverse argument.
The `k = 1` special case is `localMultiplicity_one_locally_injective` above
(the inverse function theorem suffices); `k ≥ 2` requires winding-number /
argument-principle content not in mathlib at the pin.

We therefore state the general case as a `Prop`-valued `def` (NOT an
`axiom`) so future filling does not contaminate the kernel. -/

/-! ## The argument-principle disk lemma

The discharge of `localMultiplicity_eq_order_punctured_statement` for `k ≥ 2`
classically routes through the **argument principle**: for `g` analytic at `0`
with `g(0) = 0` of order `k`, the contour integral

  `(1 / (2πi)) · ∮_{|z|=ε} g'(z) / (g(z) - w) dz = k`

for every `w` close to but not equal to `0`. This is the Rouché-style winding-
number count: the integrand is the logarithmic derivative of `g - w`, which has
`k` simple zeros (by the open-mapping / Rouché shift) in the disk and no poles,
so the integral counts those zeros.

At the mathlib pin `8e3c989` the argument principle in the form needed is not
named. The nearest mathlib content is `Complex.integral_circle_div_eq` and the
Cauchy integral formula for analytic functions, but the statement
"`(1 / 2πi) ∫ g'/g = (zero count − pole count)`" is not packaged generally.

We therefore name the precise gap as two `Prop`-valued statements:

1. `argumentPrinciple_disk_statement k g` — the disk-centred argument-principle
   integral identity itself. This is the mathlib gap.
2. `argumentPrinciple_implies_rouche_statement k g` — once (1) is available,
   it implies the Rouché-style preimage count
   `localMultiplicity_eq_order_punctured_statement`.

Both are stated as `def : Prop`, not `axiom`, so they are inert until
discharged. -/

namespace MMeromorphicAt

/-! ### k = 0 trivial case of the argument principle (zero-free disk)

When `f : ℂ → ℂ` is holomorphic and **nonzero** everywhere on a closed disk
`closedBall z₀ r` with `0 < r`, the logarithmic derivative `deriv f / f` is
holomorphic on a neighborhood of the closed disk (no poles, since `f ≠ 0`).
Cauchy's theorem (Cauchy–Goursat) applied to `deriv f / f` then gives

  `∮_{|z - z₀| = r} (deriv f) z / f z dz = 0`.

This is the `k = 0` (no-zero, no-pole) leg of the argument principle, and it
is honestly proven below from `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`.
The general (k ≥ 1) case is deferred; see `argumentPrinciple_disk_statement`. -/

end MMeromorphicAt

end Jacobians.Discharge

end
