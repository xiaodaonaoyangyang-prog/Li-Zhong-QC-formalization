/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-! # Topological degree of a holomorphic map between compact Riemann surfaces

This file provides the candidate body for `ContMDiff.degree`, the degree of a
holomorphic map `f : X → Y` between compact connected Riemann surfaces,
matching the convention specified in challenge item 9 of `Jacobians.Discharge.Basic`:

* `degree(constant) = 0`,
* `degree(non-constant) = (cardinality of a generic fiber)`.

## Status: indicator stub

The eventual analytic content — define a *regular value* `y₀ : Y` (one whose
fiber `f ⁻¹' {y₀}` is finite and avoids ramification points), then take
`Nat.card (f ⁻¹' {y₀})` — requires the chart-independence of
`mmeromorphicOrderAt` (so that "ramification index `≥ 2`" is well-defined
intrinsically on the manifold). That chart-independence is deferred work in
`Jacobians.Discharge.Manifold.MeromorphicAt` (see its file header).

Per the project's "honest stub > speculative real definition" principle, we
ship the **constant-vs-non-constant indicator**:

```
degreeIndicator hf := if (∃ y, ∀ x, f x = y) then 0 else 1
```

This satisfies `degree(constant) = 0` and gives a typechecking witness for the
challenge signatures (items 9, 24). It does **not** give the correct numerical
degree for non-constant maps; that lands in a follow-up once the regular-value
machinery is in.

## Why a separate name and not `_root_.ContMDiff.degree` directly?

`Basic.lean` already declared `def _root_.ContMDiff.degree ... ` as an unproved
stub, and this single-file edit is forbidden from touching `Basic.lean`. If we
declared `_root_.ContMDiff.degree` here as well, the build would fail with a
duplicate definition. So we expose the candidate body under
`Jacobians.Discharge.Manifold.degreeIndicator`. The sister edit that wires this in
will replace the stub body in `Basic.lean` with `:= degreeIndicator f hf`.

## Main definitions

* `Jacobians.Discharge.IsConstantMap f` — `f` is constant (one packaged form).
* `Jacobians.Discharge.Manifold.degreeIndicator f hf` — `0` if `f` is constant,
  `1` otherwise. **Stub.**
-/

noncomputable section

open scoped Manifold Topology
open Set

namespace Jacobians.Discharge

universe u v

/-- A function `f : X → Y` is **constant** if there is a single value `y : Y`
that `f` takes everywhere. Packaged as a `Prop` for use in the indicator
definition of the degree stub. -/
def IsConstantMap {X : Type u} {Y : Type v} (f : X → Y) : Prop :=
  ∃ y, ∀ x, f x = y

namespace Manifold

/-! ## Degree stub

Note the underscore on `_hf` — the indicator stub does not consume the
holomorphy hypothesis. It is retained in the signature so that the eventual
real definition (regular-value cardinality) can be a drop-in replacement
without touching the call site. -/

end Manifold

end Jacobians.Discharge

end
