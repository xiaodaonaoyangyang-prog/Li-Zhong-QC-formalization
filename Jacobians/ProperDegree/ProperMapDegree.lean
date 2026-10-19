/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.MappingDegree.RoucheBridge
import Jacobians.ProjectiveLine
import Jacobians.ProperDegree.DegDivResidue
import Mathlib.Analysis.CStarAlgebra.Classes
/-!
# The proper-map degree: `zerosCount f = polesCount f` (conservation of number)

For a compact connected Riemann surface `X` and a meromorphic function
`f : X → ℂ`, the number of zeros equals the number of poles, each counted with
multiplicity:

> `zerosCount f = polesCount f`.

This is the **argument-principle equality** (Forster Cor. 4.24–4.25; Miranda
§II.4 "conservation of number"), the keystone of the residue theorem
`deg (div f) = 0` and hence of Riemann–Roch.

## The route: proper-map degree via local-constancy of the fibre multiplicity

The map `F = f.toRiemannSphere : X → ℂℙ¹` is **proper** (`isProperMap_toRiemannSphere`)
and holomorphic.  For each `w ∈ ℂℙ¹` define the **fibre multiplicity**

> `N(w) = ∑_{x ∈ F⁻¹(w)} (local degree of F at x)`     (= # preimages with multiplicity),

the local degree being `ord_x(f − w)` at a finite value `w` and `−ord_x(f)` at
`w = ∞`.  The classical argument principle says

> `N(w) = (1/2πi) ∮_{∂D} F'/(F − w)`     is **integer-valued and continuous in `w`**,

hence **locally constant**; as `ℂℙ¹` is connected, `N` is *globally constant*,
equal to the degree `d`.  The two special fibres then read off the counts:

> `N(0)  = ∑_{x : F x = 0} ord_x f      = zerosCount f`,
> `N(∞)  = ∑_{x : F x = ∞} (−ord_x f)   = polesCount f`,

so `zerosCount f = d = polesCount f`.  Crucially the multiplicity count *eats
ramification automatically*: at a zero/pole of order `k > 1` the local degree is
`k`, matching the order — exactly what `zerosCount`/`polesCount` already sum.

This file proves the globalization step (connectedness of `ℂℙ¹`) and bundles the
argument-principle output as `ProperMapDegreeData`.  The construction of the
locally-constant witness — finite disk cover, per-disk argument principle, and
multiplicity merging at the finitely many branch values — is carried out in
`ProperMapDegreeSheets`.

## References

* Forster, *Lectures on Riemann Surfaces*, §4 (the degree), Cor. 4.24–4.25.
* Miranda, *Algebraic Curves and Riemann Surfaces*, §II.4 ("conservation of
  number"; the degree of a holomorphic map).
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Finset

namespace Jacobians.ProperMapDegree

open Jacobians


/-! ### The globalization: locally constant on a connected sphere ⇒ the equality

The single analytic gate of the route is that the fibre-multiplicity function `N`
on `ℂℙ¹` is **locally constant** (the argument principle: `N(w)` is an integer-
valued contour integral, continuous in `w`).  Given that, the equality
`zerosCount f = polesCount f` is *purely topological*: `ℂℙ¹` is connected
(`RiemannSphere` has `ConnectedSpace`, hence `PreconnectedSpace`), so a locally
constant function takes the same value at every pair of points — in particular at
`0` and `∞`, which are `zerosCount f` and `polesCount f`.

We isolate this as a standalone lemma taking the three honest hypotheses (local
constancy + the two boundary identities) directly, before bundling them as a
structure. -/

/-- **Globalization of the argument principle (the connectedness step).**

If `N : ℂℙ¹ → ℤ` is locally constant with `N(0) = zerosCount f` and
`N(∞) = polesCount f`, then `zerosCount f = polesCount f`. -/
theorem zerosCount_eq_polesCount_of_isLocallyConstant {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (f : MeromorphicFunction X)
    (N : RiemannSphere → ℤ) (hN : IsLocallyConstant N)
    (hzero : N ((0 : ℂ) : RiemannSphere) = zerosCount f)
    (hinfty : N OnePoint.infty = polesCount f) :
    zerosCount f = polesCount f := by
  have hconst : N ((0 : ℂ) : RiemannSphere) = N OnePoint.infty :=
    hN.apply_eq_of_preconnectedSpace _ _
  rw [hzero, hinfty] at hconst
  exact hconst

/-! ### The argument-principle data bundle

We package the output of the conservation-of-number assembly — the locally
constant fibre-multiplicity function with its two boundary readings — as a
structure.  Each field is a *true* statement; the structure is satisfiable
(with `N ≡ 0` when `f.div = 0`), so it is an honest hypothesis, not a
disguised `False`. -/

/-- **Conservation-of-number data for `f`** through `F = toRiemannSphere`.

Bundles the output of the global argument-principle assembly:

* `N : ℂℙ¹ → ℤ` — the fibre multiplicity `N(w) = ∑_{x ∈ F⁻¹ w} (local degree)`;
* `locallyConstant` — the argument principle: `N` is locally constant (its value
  is the integer-valued contour integral `(1/2πi) ∮ F'/(F − w)`, continuous in
  `w`);
* `zero_eq` — the zero-fibre reading `N(0) = zerosCount f` (the finite-value
  local degree at a zero is the order, summed over the zeros);
* `infty_eq` — the pole-fibre reading `N(∞) = polesCount f` (the local degree at
  a pole is `−ord`, summed over the poles). -/
structure ProperMapDegreeData {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (f : MeromorphicFunction X) where
  /-- The fibre-multiplicity function on `ℂℙ¹`. -/
  N : RiemannSphere → ℤ
  /-- The argument principle: `N` is locally constant. -/
  locallyConstant : IsLocallyConstant N
  /-- The zero-fibre reading: `N(0)` is the number of zeros (with multiplicity). -/
  zero_eq : N ((0 : ℂ) : RiemannSphere) = zerosCount f
  /-- The pole-fibre reading: `N(∞)` is the number of poles (with multiplicity). -/
  infty_eq : N OnePoint.infty = polesCount f

/-- **`zerosCount = polesCount` via the conservation-of-number data.**  Given a
`ProperMapDegreeData f` (the output of the argument-principle assembly), the
number of zeros equals the number of poles. -/
theorem zerosCount_eq_polesCount_of_properMapDegreeData {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (f : MeromorphicFunction X)
    (D : ProperMapDegreeData f) :
    zerosCount f = polesCount f :=
  zerosCount_eq_polesCount_of_isLocallyConstant f D.N D.locallyConstant D.zero_eq D.infty_eq

/-- The proper-map-degree existential (`∃ d, zerosCount = d ∧ polesCount = d`),
derived from a `ProperMapDegreeData` via the nonnegativity reduction
`exists_properMapDegree_of_zerosCount_eq_polesCount`.  This is the exact shape the
parent's `exists_properMapDegree` needs. -/
theorem exists_properMapDegree_of_properMapDegreeData {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (f : MeromorphicFunction X)
    (D : ProperMapDegreeData f) :
    ∃ d : ℕ, zerosCount f = (d : ℤ) ∧ polesCount f = (d : ℤ) :=
  exists_properMapDegree_of_zerosCount_eq_polesCount f
    (zerosCount_eq_polesCount_of_properMapDegreeData f D)

end Jacobians.ProperMapDegree
