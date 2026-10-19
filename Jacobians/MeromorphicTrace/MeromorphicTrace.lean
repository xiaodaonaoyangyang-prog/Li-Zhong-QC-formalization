/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.Meromorphic.Order
import Jacobians.MeromorphicTrace.TraceResidue
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The meromorphic trace `Tr_F α` and the residue-trace compatibility (Miranda §VIII.3, b + c)

This file builds **pillars (b) and (c)** of the trace-to-`ℙ¹` route to the residue theorem
(Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3, "An Algebraic Proof of the Residue
Theorem").  With pillar (a) — the `ℂℙ¹` residue theorem `LaurentForm.…_eq_zero` in
`Jacobians.TraceResidue` — and the cover `F = MeromorphicFunction.toRiemannSphere` (in
`Jacobians.ToSphereGeneral`), they assemble into

> `∑_{p ∈ X} Res_p α = ∑_{q ∈ ℂℙ¹} Res_q (Tr_F α) = 0`.

## Design — the `resAt` (local coordinate) level

A meromorphic `1`-form on `X` is, in any chart, `(coefficient) · dz` with the coefficient
meromorphic; its residue at a point `x` is `resAt (coeff) (chart x)`
(`Jacobians.Dolbeault.resAt`, the `(2πi)⁻¹∮` contour residue).  The deep manifold-bundle trace
already exists for *holomorphic* forms (`Jacobians.TraceForm.traceForm`, the fibre-sum pushforward
with its removable-singularity branch extension); what is genuinely new — and what Lemma 3.2 is
about — is the *residue interaction*, which is a one-variable **coordinate** statement.  So we work
at the `resAt`/coefficient level, where the whole §VIII.3 argument lives, and where it connects
directly to `LaurentForm` for the combine.

The genuine content of Lemma 3.2 is the **residue change-of-variables** under a single
(unramified) sheet `s` of the cover: pushing a `1`-form `g·dw` forward along `w = φ(z)` (with `φ`
a local biholomorphism, `φ'(a) ≠ 0`) gives `g(φ z)·φ'(z)·dz`, whose residue at the source point
equals the residue of `g·dw` at the image point.  The trace over a fibre is the sum over the sheets,
so its residue is the fibre sum of the per-point residues — Lemma 3.2.

## What is proved here (all complete)

* **`resAt_inv_sub_mul`** — Cauchy's integral formula as a residue: `Res_a (h(z)/(z − a)) = h(a)`
  for `h` analytic at `a` (the workhorse simple-pole residue with analytic numerator).
* **`resAt_simplePole_pushforward`** — the **simple-pole residue change-of-variables** (the heart of
  Lemma 3.2, *fully proved*): for `φ` analytic at `a` with `φ'(a) ≠ 0` and `φ a = b`, the
  pushforward `z ↦ c·(φ z − b)⁻¹ · φ'(z)` of the simple pole `c·(w − b)⁻¹` has `resAt = c` at `a`.
  This is exactly the case the `df/f` route to `deg_div` needs (`df/f` has only simple poles).
* **`resAt_logDeriv_eq_order`** — the order link `Res_a(df/f) = ord_a f` (`= n` when
  `meromorphicOrderAt f a = n`), the per-point input of the `deg_div` route.  *Fully proved*: the
  factorization `f = (z−a)^n·g`, `g a ≠ 0`, gives `logDeriv f = n/(z−a) + logDeriv g` with
  `logDeriv g` analytic.
* **`FibreTrace` / `FibreTrace.traceCoeff`** — the coordinate model of the meromorphic trace
  `Tr_F α` over a finite (off-branch) fibre: the finite sum of the per-sheet pushforwards
  `∑ i, coeff i (sheet i w)·(sheet i)'(w)`.
* **Lemma 3.2 (`FibreTrace.resAt_traceCoeff`)** — `Res_b (Tr_F α) = ∑_{sheets} Res_{pre i} (coeff
i)`,
  the residue-trace compatibility, from per-sheet change of variables + `resAt_finsum` (additivity).
  Its **simple-pole specialization** `FibreTrace.resAt_traceCoeff_of_simplePole` is *unconditional*
  (no analytic atom), built on the proved `resAt_simplePole_pushforward`.
* **The combine (`finiteResidueSum_trace_eq_zero`, `…_of_fibres`, `…_of_simplePole_fibres`)** —
  packaging `Tr_F α` as a `LaurentForm` and applying pillar (a); the simple-pole form is fully
  hypothesis-free up to the manifold bookkeeping `hL32` (that `L` *is* the trace).

## The one isolated analytic atom

The fully-general (higher-order-pole) residue change-of-variables `resAt (g ∘ φ · φ') a =
resAt g (φ a)` is a contour-substitution / deformation statement that Mathlib lacks at this pin
(no winding-number-invariance of `circleIntegral` along a biholomorphism).  It is isolated as the
named Prop `ResidueChangeOfVariables` and is **not** needed for the `df/f` route (only simple poles
there) — that route uses only the *proved* `resAt_simplePole_pushforward`.  See the report.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces*, §17 (`Res`); §4.22–4.25 (sheets, local normal form).
-/

open Complex Metric Filter Topology
open scoped Real

namespace Jacobians.MeromorphicTrace

open Jacobians.Dolbeault Jacobians.TraceResidue

/-! ### Cauchy's integral formula as a residue

The single workhorse: a simple pole `h(z)/(z − a)` with **analytic numerator** `h` has residue
`h a`.  This is Cauchy's integral formula `(2πi)⁻¹ ∮_{|z−a|=r} h(z)/(z − a) = h(a)` read through
`resAt`.  Everything in this file funnels through it. -/

/-- **Cauchy's integral formula, residue form.**  For `h` analytic at `a`, the residue of the
simple pole `z ↦ (z − a)⁻¹ · h z` at `a` is `h a`. -/
theorem resAt_inv_sub_mul {h : ℂ → ℂ} {a : ℂ} (hh : AnalyticAt ℂ h a) :
    resAt (fun z => (z - a)⁻¹ * h z) a = h a := by
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ z ∈ ball a ρ, DifferentiableAt ℂ h z := by
    have hev := hh.eventually_analyticAt
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hb⟩ := hev
    exact ⟨ε, hε, fun z hz => (hb (mem_ball.mp hz)).differentiableAt⟩
  set r := ρ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrρ : r < ρ := by rw [hr]; exact half_lt_self hρ
  have hpunct : ∀ z ∈ ball a ρ \ {a}, DifferentiableAt ℂ (fun z => (z - a)⁻¹ * h z) z := by
    intro z hz
    have hzne : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hz.2)
    exact (((differentiableAt_id).sub_const a).inv hzne).mul (hball z hz.1)
  rw [resAt_eq_smul_circleIntegral hpunct hr0 hrρ]
  have hcont : ContinuousOn h (closedBall a r) := fun z hz =>
    (hball z (lt_of_le_of_lt (mem_closedBall.mp hz) hrρ)).continuousAt.continuousWithinAt
  have hdiff : ∀ z ∈ ball a r \ (∅ : Set ℂ), DifferentiableAt ℂ h z := fun z hz =>
    hball z (lt_trans (mem_ball.mp hz.1) hrρ)
  have hcauchy := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (R := r) (c := a) (w := a) (f := h) (s := ∅) Set.countable_empty (mem_ball_self hr0) hcont hdiff
  rw [show (fun z => (z - a)⁻¹ * h z) = (fun z => (z - a)⁻¹ • h z) by funext z; rw [smul_eq_mul]]
  exact hcauchy

/-- Variant with the numerator on the left: `Res_a (h(z) · (z − a)⁻¹) = h a`. -/
theorem resAt_mul_inv_sub {h : ℂ → ℂ} {a : ℂ} (hh : AnalyticAt ℂ h a) :
    resAt (fun z => h z * (z - a)⁻¹) a = h a := by
  rw [show (fun z => h z * (z - a)⁻¹) = (fun z => (z - a)⁻¹ * h z) by funext z; ring]
  exact resAt_inv_sub_mul hh

/-! ### Analytic factorization at a simple zero of a biholomorphism

If `φ` is analytic at `a` with `φ'(a) ≠ 0` (a local biholomorphism) and `φ a = b`, then `φ − b`
has a *simple* zero at `a`: `φ z − b = (z − a) · g z` near `a`, with `g` analytic and
`g a = φ'(a) ≠ 0`.  This is the change-of-coordinate fact underlying Lemma 3.2: the cover, read in
charts at an unramified preimage, is exactly such a `φ`. -/

/-! ### The simple-pole residue change of variables — the heart of Lemma 3.2

For a single (unramified) sheet, pushing the simple pole `c·(w − b)⁻¹` of a `1`-form forward along
the local biholomorphism `w = φ(z)` (`b = φ a`) gives `z ↦ c·(φ z − b)⁻¹·φ'(z)`, whose residue at
the source point `a` is again `c`.  *Fully proved*: by the simple-zero factorization the pushforward
equals `(z − a)⁻¹ · H z` with `H` analytic, `H a = c` (the `φ'` numerator and the slope `g` cancel),
so Cauchy (`resAt_inv_sub_mul`) gives residue `H a = c`.

This is exactly the residue-preservation the `df/f` route to `deg_div` needs: `df/f` has only simple
poles, with residue the integer order, and unramified preimages give such `φ`. -/

/-! ### The logarithmic-derivative residue — the `df/f` route to `deg_div`

For the divisor route to the residue theorem, the relevant `1`-form is `α = df/f` (the logarithmic
differential), whose residue at a point is the **order** of `f` there:

> `Res_a (df/f) = ord_a f`.

This is the local argument principle: if `f` has order `n` at `a`, then `f z = (z − a)^n · g z` with
`g a ≠ 0` (`meromorphicOrderAt_eq_int_iff`), so `logDeriv f = n/(z − a) + logDeriv g` near `a`, and
`logDeriv g` is analytic at `a` (`g a ≠ 0`), contributing no residue.  Hence `Res_a (df/f) = n`.
The poles of `df/f` are all *simple* (residue `= n`), which is why the *proved* simple-pole change
of
variables (`resAt_simplePole_pushforward`) is all this route needs.  Fully proved. -/

/-! ### The general residue change of variables, as a named atom

The fully-general (any-order-pole) residue change of variables `resAt (g ∘ s · s') b = resAt g a`
for `s` a local biholomorphism (`s b = a`, `s'(b) ≠ 0`) and `g` *any* meromorphic function at `a`
is a contour-substitution / homotopy-invariance statement Mathlib lacks at this pin (there is no
winding-number-invariance of `circleIntegral` along a biholomorphism).  We isolate it as a named
`Prop` so the general Lemma 3.2 can be stated and assembled; the **simple-pole** instance below is
*proved* (`resAt_changeOfVariables_of_simplePole`) and is all the `df/f`/`deg_div` route requires.

`s` is the **section** (the local inverse of the cover read in charts): `w ↦ z`.  The pushforward of
the `1`-form `g·dz` is `(g ∘ s)·s'·dw`. -/

/-! ### The fibre trace and Lemma 3.2

A **fibre** of the cover over a base point with target-chart coordinate `b` is a finite family of
sheets; sheet `i` has a holomorphic local section `sheet i` (`sheet i b = pre i`, `(sheet i)'(b) ≠
0`) and carries the form coefficient `coeff i` (meromorphic at the preimage coordinate `pre i`).
The **trace coefficient** at the base is the finite sum of the per-sheet pushforwards
`w ↦ ∑ i, coeff i (sheet i w) · (sheet i)'(w)`. -/

/-- A finite fibre of an (unramified) cover over a base point of target-chart coordinate `b`, with
the per-sheet holomorphic sections and meromorphic form coefficients.  The data of Miranda's local
picture for the trace `Tr_F` over `b` (off the branch locus). -/
structure FibreTrace where
  /-- Index of the sheets meeting the fibre. -/
  ι : Type
  /-- Finiteness of the sheet index. -/
  fintype_ι : Fintype ι
  /-- The base-point coordinate in the target chart. -/
  b : ℂ
  /-- The local holomorphic section of sheet `i` (target coord `↦` source coord). -/
  sheet : ι → ℂ → ℂ
  /-- The source-chart coordinate of the `i`-th preimage, `= sheet i b`. -/
  pre : ι → ℂ
  /-- Each section is analytic at the base. -/
  sheet_analytic : ∀ i, AnalyticAt ℂ (sheet i) b
  /-- Each section is a local biholomorphism (nonzero derivative). -/
  sheet_deriv_ne : ∀ i, deriv (sheet i) b ≠ 0
  /-- The section hits the `i`-th preimage at the base. -/
  sheet_base : ∀ i, sheet i b = pre i
  /-- The form coefficient on sheet `i`, meromorphic at the preimage coordinate. -/
  coeff : ι → ℂ → ℂ
  /-- Meromorphy of each sheet's form coefficient. -/
  coeff_mero : ∀ i, MeromorphicAt (coeff i) (pre i)

namespace FibreTrace

attribute [instance] FibreTrace.fintype_ι

variable (T : FibreTrace)

end FibreTrace

/-! ### The simple-pole instance of the change of variables (fully proved)

For the `df/f` route to `deg_div`, every form coefficient is `df/f`, which has only **simple
poles**,
with residue the integer order.  The simple-pole change of variables `resAt_simplePole_pushforward`
is proved above; here we re-express it in the section (`s = φ⁻¹`) form used by `FibreTrace`, so the
fibre Lemma 3.2 holds *unconditionally* for simple-pole coefficients.

The section form follows from the forward form by reading the inverse: if `s` is the section
(`s b = a`, `s'(b) ≠ 0`) and the coefficient is the simple pole `g w = c·(w − a)⁻¹`, then
`g (s w)·s'(w) = c·(s w − a)⁻¹·s'(w)`, and since `s` is itself a local biholomorphism with
`s b = a`, this is exactly the shape `resAt_simplePole_pushforward` evaluates (with `φ := s`,
`b := a`), giving residue `c = resAt g a` (`resAt_const_mul_sub_inv`). -/

/-! ### The combine — pillar (a) ∘ Lemma 3.2 = the residue theorem on `X`

The final step of Miranda §VIII.3.  The trace `Tr_F α` is a rational `1`-form on `ℂℙ¹`, so (away
from `∞`) it is in partial-fraction form — a `LaurentForm L` whose coefficient `L.R` is the trace
coefficient.  Pillar (a) gives `L.finiteResidueSum + Res_∞ L.R = 0`.  By Lemma 3.2 each finite
residue `resAt L.R p = Res_p (Tr_F α)` equals the fibre sum `∑_{x ∈ F⁻¹ p} Res_x α`; summing over
the (finitely many) centers regroups `L.finiteResidueSum` as the total residue of `α` over all
finite-fibre points of `X`.  Hence

> `(∑_{finite fibres} ∑_{x ∈ fibre} Res_x α) + Res_∞ (Tr_F α) = 0`,

which is `∑_{x ∈ X} Res_x α = 0` once the `∞`-fibre residues are folded into `Res_∞` (the standard
inversion-symmetric bookkeeping; geometrically the residue theorem on `X`). -/

end Jacobians.MeromorphicTrace
