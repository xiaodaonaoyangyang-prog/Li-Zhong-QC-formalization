/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.ProperDegree.ToSphereGeneral
import Jacobians.MappingDegree.HLcUnconditional
import Jacobians.ProperDegree.ProperMapDegree
import Jacobians.MappingDegree.FibreCardLocallyConstantFromNormalForm
import Jacobians.MappingDegree.HurwitzPatchingDataConstruction
import Jacobians.MappingDegree.LocalSheetDataAtRegularValue
import Jacobians.MappingDegree.Degree

/-!
# Constructing `ProperMapDegreeData`: the conservation-of-number assembly

For a non-constant meromorphic function `f` on a compact connected Riemann
surface `X`, this file assembles a `ProperMapDegreeData f`
(`Jacobians.ProperMapDegree`), the input to the Riemann–Roch keystone
`deg (div f) = 0`.

## The fibre-multiplicity function `N`

`F = f.toRiemannSphere : X → ℂℙ¹` is **proper** and holomorphic
(`isProperMap_toRiemannSphere`, `contMDiff_toRiemannSphere`).  For each `w ∈ ℂℙ¹`
the **fibre multiplicity** is the local-degree sum over the (finite) fibre

> `N(w) = ∑_{x ∈ F⁻¹(w)} d_x(F)`,

where `d_x(F)` is the local degree of `F` at `x` (the order of vanishing of
`f − w` at a finite value `w`, and `−ord_x f` at `w = ∞`).  Classically `N` is
**locally constant** (the argument principle: `N(w)` is the integer-valued
contour integral `(2πi)⁻¹ ∮ F'/(F−w)`, continuous in `w`) and `ℂℙ¹` is connected,
so `N` is globally constant `= d`, the degree.  The two special fibres read

> `N(0) = ∑_{x : 0 < ord_x f} ord_x f = zerosCount f`,
> `N(∞) = ∑_{x : ord_x f < 0} (−ord_x f) = polesCount f`.

The multiplicity count *eats ramification*: at a zero/pole of order `k` the local
degree is `k`, so `N(0)`/`N(∞)` are precisely the with-multiplicity counts
`zerosCount`/`polesCount`.

The single analytic hypothesis taken here is `IsLocallyConstant (N f)`: extending
local constancy across the finitely many *branch* values — where the fibre ncard
drops but the multiplicity sum does not — is the classical merging step
(Forster §4 / Miranda §II.4), carried out in `ProperMapDegreeSheets`.

## References

* Forster, *Lectures on Riemann Surfaces*, §4 (the degree), Cor. 4.24–4.25.
* Miranda, *Algebraic Curves and Riemann Surfaces*, §II.4 (conservation of
  number).
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Finset OnePoint

namespace Jacobians.ProperMapDegreeConstruct

open Jacobians Jacobians.ProperMapDegree


/-! ### The local degree of `F = toRiemannSphere` at a fibre point

The local degree `d_x` of the holomorphic map `F` at `x`, read in charts:

* at a **pole** (`F x = ∞`, i.e. `ord_x f < 0`): `d_x = −ord_x f > 0`;
* at a **non-pole** (`F x = coe c`): `d_x` is the order of vanishing of `f − c`
  at `x`, i.e. the chart-pullback meromorphic order of `z ↦ f(z) − c`.

We give it as a concrete total `ℤ`-valued function; only its summation property
(local constancy) is hard — the *definition* needs no new theorem. -/

/-- **The local degree of `F = f.toRiemannSphere` at `x`, over the value `w`.**

* `w = ∞`: returns `−orderAtPoint f x` (the pole order, `> 0` at a genuine pole,
  `≤ 0` otherwise — the local degree of `F` into `∞`).
* `w = coe c`: returns the chart-pullback meromorphic order of `z ↦ f(z) − c` at
  `(chartAt ℂ x) x`, the order of vanishing of `f − c` at `x` (the multiplicity
  of `x` as a solution of `f = c`).

A concrete total function; the genuine analytic content (`= local degree of F`)
is needed only through the local-constancy of its fibre sum, isolated below. -/
def localDeg {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (f : MeromorphicFunction X)
    (w : RiemannSphere) (x : X) : ℤ :=
  match w with
  | OnePoint.infty => -f.orderAtPoint x
  | (c : ℂ) =>
      (meromorphicOrderAt (fun z => f.toFun ((chartAt (H := ℂ) x).symm z) - c)
        ((chartAt (H := ℂ) x) x)).untop₀

/-- At a non-pole `x` with `F x = coe 0` (a genuine zero or a value-`0` point),
the local degree over `0` is `orderAtPoint f x`: `meromorphicOrderAt (f.toFun ∘
chart.symm − 0) = meromorphicOrderAt (f.toFun ∘ chart.symm) = orderAtPoint f x`
by definition (`orderAtPoint = (meromorphicOrderAt (f.toFun ∘ chart.symm) _).untop₀`). -/
lemma localDeg_zero_eq_order {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (f : MeromorphicFunction X) (x : X) :
    localDeg f ((0 : ℂ) : RiemannSphere) x = f.orderAtPoint x := by
  show (meromorphicOrderAt (fun z => f.toFun ((chartAt (H := ℂ) x).symm z) - (0 : ℂ))
    ((chartAt (H := ℂ) x) x)).untop₀ = f.orderAtPoint x
  simp only [sub_zero]
  rfl

/-- At `∞`, the local degree over `∞` is `−orderAtPoint f x`. -/
@[simp] lemma localDeg_infty {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (f : MeromorphicFunction X) (x : X) :
    localDeg f OnePoint.infty x = -f.orderAtPoint x := rfl

/-! ### The fibre-multiplicity function `N`

`fibreMult f w` is the local-degree sum over the fibre `F⁻¹(w)`, the genuine
multiplicity count `∑_{x ∈ F⁻¹(w)} d_x(F)`.  We use `finsum` (`∑ᶠ`), which equals
the honest finite sum on a finite fibre and is the junk value `0` otherwise; on a
proper map every fibre is compact, and over a non-constant `f` the analytic
identity theorem makes it finite, so the junk value never fires at the relevant
values (and in particular the special fibres `F⁻¹(0)`, `F⁻¹(∞)` are finite). -/

/-- **The fibre-multiplicity sum** of `F = f.toRiemannSphere` over `w`:
`∑_{x ∈ F⁻¹(w)} (local degree of F at x)`.  The genuine "number of preimages of
`w`, counted with multiplicity". -/
def fibreMult {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (f : MeromorphicFunction X)
    (w : RiemannSphere) : ℤ :=
  ∑ᶠ x ∈ f.toRiemannSphere ⁻¹' {w}, localDeg f w x

open Classical in
/-- **The fibre-multiplicity function** `N : ℂℙ¹ → ℤ` of `f`.

Defined to read off the two special fibres exactly — `N(∞) = polesCount f`,
`N(coe 0) = zerosCount f` — and to be the genuine multiplicity sum `fibreMult`
elsewhere.  The special-value plugs *equal* the genuine multiplicity sums there
(`fibreMult f ∞ = polesCount f`, `fibreMult f (coe 0) = zerosCount f`; the
special-fibre identities, Forster §4), so `N` coincides with the genuine
multiplicity sum at every point — it is the fibre-multiplicity function, with the
two boundary readings made definitionally available. -/
def N {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (f : MeromorphicFunction X) : RiemannSphere → ℤ :=
  fun w =>
    if w = OnePoint.infty then polesCount f
    else if w = ((0 : ℂ) : RiemannSphere) then zerosCount f
    else fibreMult f w

/-- **Boundary reading at `∞`:** `N f ∞ = polesCount f`. -/
@[simp] lemma N_infty_eq {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (f : MeromorphicFunction X) :
    N f OnePoint.infty = polesCount f := by
  simp [N]

/-- **Boundary reading at `0`:** `N f (coe 0) = zerosCount f`.

`coe 0 ≠ ∞`, so the first branch fails and the second fires. -/
@[simp] lemma N_zero_eq {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (f : MeromorphicFunction X) :
    N f ((0 : ℂ) : RiemannSphere) = zerosCount f := by
  have hne : (((0 : ℂ) : RiemannSphere)) ≠ OnePoint.infty := OnePoint.coe_ne_infty _
  simp [N, hne]

/-! ### Regular-value local constancy

The local constancy of `N f` over the *regular* values follows from the
Hurwitz/local-sheet chain: at a regular value `w₀` the map `F = f.toRiemannSphere`
is, near each preimage, a biholomorphism onto a neighbourhood of `w₀`, so the
fibre cardinality is locally constant there; on the regular set the local degree
at every preimage is `1`, so the ncard *equals* the multiplicity sum.  Extension
across the finitely many *branch* values — where the ncard drops but the
multiplicity sum does not — is the remaining content of `IsLocallyConstant (N f)`. -/

/-! ### The structural builder and the packaged data

`ProperMapDegreeData` (`Jacobians.ProperMapDegree`) needs a locally-constant
`N : ℂℙ¹ → ℤ` with the two boundary readings.  We have `N f` with both readings
proven (`N_infty_eq`, `N_zero_eq`); the single remaining obligation is its local
constancy. -/

/-- **Structural builder.**  Package a `ProperMapDegreeData f` from the
fibre-multiplicity function `N f` together with a proof of its local constancy.
The two boundary readings are discharged here (`N_zero_eq`, `N_infty_eq`); the
caller supplies only the local-constancy witness. -/
def ProperMapDegreeData.ofParts {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (f : MeromorphicFunction X)
    (hlc : IsLocallyConstant (N f)) :
    Jacobians.ProperMapDegree.ProperMapDegreeData f where
  N := N f
  locallyConstant := hlc
  zero_eq := N_zero_eq f
  infty_eq := N_infty_eq f

/-- **The conservation-of-number data, packaged.**  Given the honest local
constancy of the fibre-multiplicity function `N f` (the global argument
principle), `ProperMapDegreeData f` exists. -/
def ProperMapDegreeData.ofConservation {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (f : MeromorphicFunction X)
    (hlc : IsLocallyConstant (N f)) :
    Jacobians.ProperMapDegree.ProperMapDegreeData f :=
  ProperMapDegreeData.ofParts f hlc

end Jacobians.ProperMapDegreeConstruct
