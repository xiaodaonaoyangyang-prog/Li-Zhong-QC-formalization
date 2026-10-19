import References.GarnettMarshall2005.Ch02.S01_SchwarzAlternatingMethod

/-!
# Garnett–Marshall, Chapter II §2: Green's functions and Poisson kernels

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. II §2 (pp. 41–50;
`full.md` P1:1918–2263).

Conventions as in §1: `Ω` is a domain of `ℂ*`, boundaries and closures are taken in `ℂ*`, and `z, w` range over
`ℂ*` (Green's function `g(z, ∞)` has its pole at `∞`). Green's function `g(z, w)` is built from the solutions
`u_f = dirichletSolution` of Theorem 1.1 exactly as in the book, so its values are meaningful for `z ∈ Ω \ {w}`; at
`z = w` and off `Ω` they are junk, and every statement excludes them (the book's (2.3) "`g(ζ, w) = 0` on `∂Ω`" is
the limit along `Ω`). Analytic arcs lie in the finite plane, so a boundary made of analytic Jordan curves is a subset
of `ℂ`, written `References.finitePart (frontier Ω)`, and its points are `ζ : ℂ`. Arc length `ds` on `∂Ω` is the
one-dimensional Hausdorff measure `μH[1]` of `ℂ` restricted to `∂Ω` (`arcLengthOn Ω`). The unit outer normal and
the normal derivative `∂u/∂n` at a boundary point are defined here (`IsOuterUnitNormal`, `HasOuterNormalDeriv`); a
statement that asserts a normal derivative uses the predicate `HasOuterNormalDeriv`, and the value
`outerNormalDeriv` (junk `0` where the derivative does not exist) is read only under hypotheses that give it.

* Definition ((2.1), Green's function `g(z, w)` with pole `w`: for bounded `Ω`, P1:1920–1924, and for unbounded `Ω`
  through a point `a ∉ Ω̄`, P1:1946–1952, §2) — `greenFunction`
* Formula (2.2) (§2) — `eq2_2_2`
* Formula (2.3) (§2, with the continuity of `g(·, w)` on `Ω̄ \ {w}`) — `eq2_2_3`
* Formula (2.4) (§2) — `eq2_2_4`
* Formula (2.5) (§2; for `w = ∞` as in P1:1952) — `eq2_2_5`
* Unlabelled (§2, P1:1944, 1952): properties (2.3), (2.4) and (2.5) determine `g(z, w)` uniquely —
  `greenFunction_unique`
* Unlabelled (§2, P1:1952): for unbounded `Ω` the definition does not depend on the choice of `a ∉ Ω̄` —
  `greenFunction_indep`
* Formula (2.6) (§2; conformal invariance) — `eq2_2_6`
* Formula (2.7) (§2; Green's function of the disc) — `eq2_2_7`
* Theorem 2.1 (§2) — `thm2_2_1`
* Definition (analytic arc; analytic Jordan curve, §2, P1:1978) — `IsAnalyticArcParam`, `IsAnalyticArcGM`,
  `IsAnalyticJordanCurve` (B-cand. LehtoVirtanen1973.IsAnalyticOpenArc, every closed subarc is analytic: one map on
  a neighbourhood of the whole arc is GM's stronger local form, and the converse needs a gluing lemma;
  LehtoVirtanen1973.IsAnalyticCurve, the image of a circle under one conformal map, equivalent to GM's analytic Jordan
  curve only by a local-to-global lemma; Pommerenke1992's analytic curve is the LV notion)
* Lemma 2.2 (§2) — `lemma2_2_2`
* Theorem 2.3 (§2; the symmetry (2.8)) — `thm2_2_3`
* Definition (the unit outer normal `n` at a point of `∂Ω` and the normal derivative `∂u/∂n`, §2, P1:2003, 2040,
  2086) — `IsOuterUnitNormal`, `HasOuterNormalDeriv`, `outerNormalDeriv`
* Lemma 2.4 (§2; (2.10)) — `lemma2_2_4_i`, `lemma2_2_4_ii`
* Definition (arc length `ds` on `∂Ω`, §2) — exists: `MeasureTheory.Measure.hausdorffMeasure` (the one-dimensional
  Hausdorff measure of the plane, restricted to the boundary; written arcLengthOn in the statements)
* Theorem 2.5 (§2; (2.11), (2.12)) — `thm2_2_5_i`, `thm2_2_5_ii`
* Definition (the Poisson kernel `P_z(ζ) = −(1/2π) ∂g(ζ, z)/∂n_ζ` for `Ω`, §2, P1:2092–2098) — `poissonKernelFC`
* Corollary 2.6 (§2; (2.14), (2.15)) — `cor2_2_6`
* Definition (the cone `Γ_α(ζ)` in `Ω`, §2, P1:2178–2182) — `coneIn`
* Theorem 2.7 (§2; (2.16)–(2.19)) — `thm2_2_7_i`, `thm2_2_7_ii`
* Definition (the arc-length maximal function `M_s f`, §2, P1:2244–2248) — `arcMaximal`
* Formula (2.20) (§2; [CORRECTION] stated in the additive form `C (M_s f(ζ) + ∫_{∂Ω∖J} |f| ds)`, `J` the boundary
  component of `ζ`) — `eq2_2_20`
* Unlabelled (§2, P1:2254; restated at P1:2942, "harmonic measure is conformally invariant"): harmonic measure is
  transplanted by a conformal map that extends to a homeomorphism of the closures — `harmonicMeasureFC_conformal`

Helpers (not book notions): `logDistExt` and `greenLogTerm` (the logarithmic terms of (2.1) and of P1:1946–1952, with
their limit values at `∞`), `IsAnalyticArcParam` (the parametrization of an analytic arc), `IsOuterUnitNormal` (the
unit outer normal, used by the normal derivative), `outerNormalDeriv` (the value of `∂u/∂n`, read under hypotheses
that give it) and `arcLengthOn` (`ds` on `∂Ω`).

Not stated (inventory U−): the remark that Exercise 5 defines Green's function for non-Jordan finitely connected domains
(P1:1989; an exercise); `φ(z) → ∂Ω'` as `z → ∂Ω` for a conformal map `φ` (P1:1954, used only to derive (2.6)); the
isometry between bounded harmonic functions and `L^∞(∂Ω, ds)` (P1:2208, a restatement of Theorem 2.7); `M_s` is
weak-type 1-1 (P1:2250, a remark with the proof left out); Green's theorem (P1:1997–2003, inside a proof). (2.9) and
(2.13) are steps of the proofs of Theorem 2.3 and Theorem 2.5; Questions 1 and 2 (P1:2256–2262) are answered by
Corollaries 4.6 and 4.7.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References ComplexConjugate

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt unitDisc IsJordanCurve)
open References (IsDomainExt IsJordanDomainExt finitePart)
open LehtoVirtanen1973 (IsConformalMap)
open InnerProductSpace (HarmonicAt)

/-- `log |z − w|` for points `z, w` of `ℂ*` (helper): the logarithm of the distance of two finite points. Junk: `0`
when `z` or `w` is `∞` (the bounded case of (2.1) never evaluates it there), and `log 0 = 0` at `z = w`. -/
def logDistExt (z w : ExtPlane) : ℝ :=
  OnePoint.elim z 0 fun x => OnePoint.elim w 0 fun y => Real.log ‖x - y‖

/-- The logarithmic term of Green's function of an unbounded domain (helper, P1:1946–1952): for a finite point `a`,
`log |(z − a)/(z − w)|` if `w` is finite and `log |z − a|` if `w = ∞`, for finite `z`; at `z = ∞` (and `w` finite)
the value is the limit `0`. Junk: `0` at `z = w = ∞`, and `log 0 = 0` at `z = w` finite. -/
def greenLogTerm (a : ℂ) (z w : ExtPlane) : ℝ :=
  OnePoint.elim z 0 fun x => OnePoint.elim w (Real.log ‖x - a‖) fun y => Real.log ‖(x - a) / (x - y)‖

open scoped Classical in
/-- **Definition** ((2.1), Green's function with pole `w`, Ch. II §2, P1:1920–1924 and P1:1946–1952). Let `Ω` be a
finitely connected Jordan domain and `w ∈ Ω`. If `Ω` is bounded, let `h(z, w)` be the solution to the Dirichlet
problem for the boundary value `f(ζ) = log |ζ − w| ∈ C(∂Ω)`, and `g(z, w) = log (1/|z − w|) + h(z, w)` (2.1). When
`Ω` is unbounded, fix `a ∉ Ω̄`; for `w ≠ ∞` let `h(z, w)` solve the Dirichlet problem for
`f(ζ) = log |(ζ − w)/(ζ − a)|` and `g(z, w) = log |(z − a)/(z − w)| + h(z, w)`; for `w = ∞` use
`f(ζ) = log |1/(ζ − a)|` and `g(z, ∞) = log |z − a| + h(z, ∞)`.
Modelling: "`Ω` bounded" is `∞ ∉ Ω̄` (in `ℂ*`); the solution of the Dirichlet problem is `dirichletSolution`
(Theorem 1.1; the data are continuous on `∂Ω`, with the value `0` of `log |(ζ − w)/(ζ − a)|` at `ζ = ∞`); for
unbounded `Ω` the value is taken over all finite `a ∉ Ω̄` (the registered "value over all maps" pattern), a single
point by `greenFunction_indep`. Junk: the values at `z = w` and for `z ∉ Ω` (there `u_f` is junk); never used there. -/
def greenFunction (Ω : Set ExtPlane) (z w : ExtPlane) : ℝ :=
  if LiZhongQC.extInf ∈ closure Ω then
    sSup {r : ℝ | ∃ a : ℂ, (a : ExtPlane) ∉ closure Ω ∧
      r = greenLogTerm a z w + dirichletSolution Ω (fun ζ => -greenLogTerm a ζ w) z}
  else -logDistExt z w + dirichletSolution Ω (fun ζ => logDistExt ζ w) z

/-- **Formula (2.2)** (Ch. II §2, P1:1926–1929; for unbounded `Ω`, P1:1952; cited at P1:3404). `g(z, w) > 0` on `Ω`.
Modelling: for `z ∈ Ω`, `z ≠ w` (at the pole the book's `g` is `+∞`; the Lean value there is junk). -/
theorem eq2_2_2 {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) {w : ExtPlane} (hw : w ∈ Ω) :
    ∀ z ∈ Ω, z ≠ w → 0 < greenFunction Ω z w := by
  sorry

/-- **Formula (2.3)** (Ch. II §2, P1:1926, 1933; for unbounded `Ω`, P1:1952; cited at P1:1960, 3550). `g(z, w)` is
continuous in `z ∈ Ω̄ \ {w}`, and `g(ζ, w) = 0` on `∂Ω`.
Modelling: the function equal to `g(·, w)` on `Ω \ {w}` and to `0` on `∂Ω` is continuous on `Ω̄ \ {w}`: on
`Ω \ {w}` this is part of (2.4), and at the boundary it is the limit `g(z, w) → 0` as `Ω ∋ z → ζ ∈ ∂Ω`. -/
theorem eq2_2_3 {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) {w : ExtPlane} (hw : w ∈ Ω) :
    ∀ ζ ∈ frontier Ω, Tendsto (fun z => greenFunction Ω z w) (𝓝[Ω] ζ) (𝓝 0) := by
  sorry

/-- **Formula (2.4)** (Ch. II §2, P1:1937; for unbounded `Ω`, P1:1952; cited at P1:1960, 3404, 3550).
`z ↦ g(z, w)` is harmonic on `Ω \ {w}`.
Modelling: harmonic in the charts of `ℂ*` (at `z = ∞ ∈ Ω` through `g(1/ζ, w)`). -/
theorem eq2_2_4 {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) {w : ExtPlane} (hw : w ∈ Ω) :
    HarmonicOnExt (fun z => greenFunction Ω z w) (Ω \ {w}) := by
  sorry

/-- **Formula (2.5)** (Ch. II §2, P1:1941; for unbounded `Ω` and `w = ∞`, P1:1952; cited at P1:1960, 3404, 3550).
`z ↦ g(z, w) − log (1/|w − z|)` is harmonic at `w`.
Modelling: in the chart of `ℂ*` at `w` (`z = w + ζ` for finite `w`, `z = 1/ζ` for `w = ∞`) the function
`ζ ↦ g(z, w) + log |ζ|` agrees near `0`, off `0`, with a function harmonic at `0` (a removable singularity; the
value at the pole itself is junk). For finite `w` this is the book's statement, since `log (1/|w − z|) = −log |ζ|`; for
`w = ∞` it reads "`g(z, ∞) − log |z|` is harmonic at `∞`" [interpretation: the book says only that (2.2)–(2.5) still
hold; this is the form used in III.1, P1:3296 and (III.1.6), P1:3389: `g(z, ∞) = log |z| + γ(E) + o(1)`]. -/
theorem eq2_2_5 {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) {w : ExtPlane} (hw : w ∈ Ω) :
    ∃ H : ℂ → ℝ, HarmonicAt H 0 ∧
      ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), H ζ = greenFunction Ω (LehtoVirtanen1973.extChartInv w ζ) w + Real.log ‖ζ‖ := by
  sorry

/-- **Unlabelled** (Ch. II §2, P1:1944 and P1:1952; cited at P1:1960 "because Green's functions are characterized by
(2.3), (2.4), and (2.5)", P1:2128 "By uniqueness", P1:3550 "those conditions determine Green's function"). By the
maximum principle, properties (2.3), (2.4) and (2.5) determine `g(z, w)` uniquely: a function `G` with `G → 0` at
`∂Ω`, harmonic on `Ω \ {w}` and with the logarithmic singularity (2.5) at `w` equals `g(·, w)` on `Ω \ {w}`.
Modelling: (2.3) as the boundary limit and (2.5) in the chart at `w`, as in `eq2_2_3` and `eq2_2_5`. -/
theorem greenFunction_unique {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) {w : ExtPlane} (hw : w ∈ Ω)
    {G : ExtPlane → ℝ} (h3 : ∀ ζ ∈ frontier Ω, Tendsto G (𝓝[Ω] ζ) (𝓝 0)) (h4 : HarmonicOnExt G (Ω \ {w}))
    (h5 : ∃ H : ℂ → ℝ, HarmonicAt H 0 ∧
      ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), H ζ = G (LehtoVirtanen1973.extChartInv w ζ) + Real.log ‖ζ‖) :
    EqOn G (fun z => greenFunction Ω z w) (Ω \ {w}) := by
  sorry

/-- **Unlabelled** (Ch. II §2, P1:1952; the definition of `greenFunction` for unbounded `Ω` rests on it). When `Ω` is
unbounded, the definitions of `g(z, w)` through a point `a ∉ Ω̄` are independent of the choice of `a`.
Modelling: for two finite points `a, b ∉ Ω̄` the two expressions agree at every `z ∈ Ω \ {w}`; `z ≠ w` is needed
(junk): at `z = w` both expressions take junk values, which differ by `log |(w − b)/(w − a)|`. -/
theorem greenFunction_indep {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) (hinf : LiZhongQC.extInf ∈ closure Ω)
    {a b : ℂ} (ha : (a : ExtPlane) ∉ closure Ω) (hb : (b : ExtPlane) ∉ closure Ω) {w : ExtPlane} (hw : w ∈ Ω) :
    ∀ z ∈ Ω, z ≠ w →
      greenLogTerm a z w + dirichletSolution Ω (fun ζ => -greenLogTerm a ζ w) z =
        greenLogTerm b z w + dirichletSolution Ω (fun ζ => -greenLogTerm b ζ w) z := by
  sorry

/-- **Formula (2.6)** (Ch. II §2, P1:1954–1960; cited at P1:1976). Suppose `φ` is a conformal mapping from one
finitely connected Jordan domain `Ω` onto another finitely connected Jordan domain `Ω'`. Then
`g_{Ω'}(φ(z), φ(w)) = g_Ω(z, w)`.
Modelling: `φ` is a conformal map of `ℂ*`-domains (`LehtoVirtanen1973.IsConformalMap`) with `φ(Ω) = Ω'`; `z ≠ w` is
added (junk): at `z = w` both sides are junk values. -/
theorem eq2_2_6 {Ω Ω' : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) (hΩ' : IsFCJordanDomain Ω')
    {φ : ExtPlane → ExtPlane} (hφ : IsConformalMap φ Ω) (hφΩ : φ '' Ω = Ω') {z w : ExtPlane} (hz : z ∈ Ω)
    (hw : w ∈ Ω) (hzw : z ≠ w) :
    greenFunction Ω' (φ z) (φ w) = greenFunction Ω z w := by
  sorry

/-- Helper (Ch. II §2). Harmonicity at a point is invariant under translations. -/
theorem gm22_harmonicAt_translate {u : ℂ → ℝ} {c x : ℂ} (h : HarmonicAt u (c + x)) :
    HarmonicAt (fun y => u (c + y)) x := by
  obtain ⟨h1, h2⟩ := h
  have hc : ContDiffAt ℝ 2 (fun y : ℂ => c + y) x := contDiffAt_const.add contDiffAt_id
  refine ⟨h1.comp x hc, ?_⟩
  have hlap : ∀ y, Laplacian.laplacian (fun y => u (c + y)) y = Laplacian.laplacian u (c + y) := fun y => by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
      InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_comp_add_left]
  have hcont : Tendsto (fun y : ℂ => c + y) (𝓝 x) (𝓝 (c + x)) :=
    (continuous_const.add continuous_id).tendsto x
  filter_upwards [hcont.eventually h2] with y hy
  rw [hlap]
  exact hy

/-- Helper (Ch. II §2). Harmonicity in the chart of `ℂ*` at a finite point is harmonicity of the restriction to `ℂ`. -/
theorem gm22_harmonicAt_of_chart {v : ExtPlane → ℝ} {x : ℂ}
    (h : HarmonicAt (v ∘ LehtoVirtanen1973.extChartInv (x : ExtPlane)) 0) :
    HarmonicAt (fun y : ℂ => v (y : ExtPlane)) x := by
  have h' : HarmonicAt (fun ζ : ℂ => v ((x + ζ : ℂ) : ExtPlane)) 0 := h
  have h'' := gm22_harmonicAt_translate (c := -x) (x := x) (u := fun ζ : ℂ => v ((x + ζ : ℂ) : ExtPlane))
    (by simpa using h')
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 h''
  exact Filter.Eventually.of_forall fun y => by simp

/-- Helper (Ch. II §2, (2.7)). The Dirichlet solution on the unit disc for the data `ζ ↦ log |ζ − w|` is
`z ↦ log |1 − z w̄|` (bounded and harmonic in the disc, equal to the data on the circle because `|1 − ζ w̄| = |ζ − w|`
for `|ζ| = 1`; unique by the maximum principle). -/
theorem gm22_dirichletSolution_disc {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    dirichletSolution (toExt unitDisc) (fun ζ => logDistExt ζ (w : ExtPlane)) (z : ExtPlane) =
      Real.log ‖1 - z * conj w‖ := by
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc] using hz
  have hw1 : ‖w‖ < 1 := by simpa [unitDisc] using hw
  have hcw : ‖conj w‖ = ‖w‖ := by simp
  have hne : ∀ x : ℂ, ‖x‖ ≤ 1 → 1 - x * conj w ≠ 0 := fun x hx h => by
    have : x * conj w = 1 := by linear_combination -h
    have h2 : ‖x‖ * ‖w‖ = 1 := by
      have := congrArg norm this
      simpa [hcw] using this
    nlinarith [norm_nonneg x, norm_nonneg w]
  have hfrontier : frontier (toExt unitDisc) = toExt (Metric.sphere (0 : ℂ) 1) := by
    have := LiZhongQC.frontier_toExt_of_isBounded (Metric.isBounded_ball (x := (0 : ℂ)) (r := 1)) isOpen_ball
    simpa [unitDisc, frontier_ball _ (one_ne_zero)] using this
  set f : ExtPlane → ℝ := fun ζ => logDistExt ζ (w : ExtPlane) with hf
  set u0 : ExtPlane → ℝ := fun p => OnePoint.elim p 0 (fun x => Real.log ‖1 - x * conj w‖) with hu0
  have hu0c : ∀ x : ℂ, u0 (x : ExtPlane) = Real.log ‖1 - x * conj w‖ := fun x => rfl
  have hfc : ∀ x : ℂ, f (x : ExtPlane) = Real.log ‖x - w‖ := fun x => rfl
  have hbd : Bornology.IsBounded unitDisc := Metric.isBounded_ball
  have hmem : ∀ p ∈ toExt unitDisc, ∃ x : ℂ, ‖x‖ < 1 ∧ p = (x : ExtPlane) := by
    rintro p ⟨x, hx, rfl⟩
    exact ⟨x, by simpa [unitDisc] using hx, rfl⟩
  -- the circle values
  have hcirc : ∀ x : ℂ, ‖x‖ = 1 → ‖1 - x * conj w‖ = ‖x - w‖ := fun x hx => by
    have hxx : x * conj x = 1 := by
      rw [Complex.mul_conj', hx]; simp
    calc ‖1 - x * conj w‖ = ‖x * conj x - x * conj w‖ := by rw [hxx]
      _ = ‖x * (conj x - conj w)‖ := by rw [mul_sub]
      _ = ‖x - w‖ := by rw [norm_mul, hx, one_mul, ← map_sub, Complex.norm_conj]
  -- u0 is a bounded solution
  have hsol : IsBoundedDirichletSolution (toExt unitDisc) f u0 := by
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨|Real.log (1 - ‖w‖)| + |Real.log 2|, fun p hp => ?_⟩
      obtain ⟨x, hx, rfl⟩ := hmem p hp
      rw [hu0c]
      have hpos : 0 < ‖1 - x * conj w‖ := norm_pos_iff.2 (hne x hx.le)
      have hlo : 1 - ‖w‖ ≤ ‖1 - x * conj w‖ := by
        have := norm_sub_norm_le (1 : ℂ) (x * conj w)
        rw [norm_mul, hcw] at this
        simp at this
        nlinarith [norm_nonneg w, norm_nonneg x]
      have hhi : ‖1 - x * conj w‖ ≤ 2 := by
        calc ‖1 - x * conj w‖ ≤ ‖(1 : ℂ)‖ + ‖x * conj w‖ := norm_sub_le _ _
          _ ≤ 2 := by
            rw [norm_mul, hcw]; simp
            nlinarith [norm_nonneg w, norm_nonneg x]
      have h1 := Real.log_le_log (by linarith) hlo
      have h2 := Real.log_le_log hpos hhi
      rw [abs_le]
      constructor <;> linarith [neg_abs_le (Real.log (1 - ‖w‖)), le_abs_self (Real.log 2),
        le_abs_self (Real.log (1 - ‖w‖)), abs_nonneg (Real.log 2), abs_nonneg (Real.log (1 - ‖w‖)),
        neg_abs_le (Real.log 2)]
    · intro p hp
      obtain ⟨x, hx, rfl⟩ := hmem p hp
      have hch : (u0 ∘ LehtoVirtanen1973.extChartInv (x : ExtPlane)) =
          fun ζ : ℂ => Real.log ‖1 - (x + ζ) * conj w‖ := by
        funext ζ
        rfl
      rw [hch]
      refine AnalyticAt.harmonicAt_log_norm (by fun_prop) ?_
      simpa using hne x hx.le
    · intro ζ hζ _
      rw [hfrontier] at hζ
      obtain ⟨x, hx, rfl⟩ := hζ
      have hx1 : ‖x‖ = 1 := by simpa using hx
      have hca : ContinuousAt u0 (x : ExtPlane) := by
        refine OnePoint.continuousAt_coe.2 ?_
        have : (u0 ∘ ((↑) : ℂ → ExtPlane)) = fun y : ℂ => Real.log ‖1 - y * conj w‖ := rfl
        rw [this]
        exact ContinuousAt.log (by fun_prop) (norm_ne_zero_iff.2 (hne x hx1.le))
      have hfu : f (x : ExtPlane) = u0 (x : ExtPlane) := by
        rw [hfc, hu0c, hcirc x hx1]
      rw [hfu]
      exact hca.tendsto.mono_left nhdsWithin_le_nhds
  -- uniqueness
  have huniq : ∀ v : ExtPlane → ℝ, IsBoundedDirichletSolution (toExt unitDisc) f v → v (z : ExtPlane) = u0 (z : ExtPlane) := by
    intro v hv
    obtain ⟨-, hvh, hvb⟩ := hv
    obtain ⟨-, hu0h, -⟩ := hsol
    have hfcw : ∀ ζ ∈ frontier (toExt unitDisc), ContinuousWithinAt f (frontier (toExt unitDisc)) ζ := by
      intro ζ hζ
      rw [hfrontier] at hζ
      obtain ⟨x, hx, rfl⟩ := hζ
      have hx1 : ‖x‖ = 1 := by simpa using hx
      refine ContinuousAt.continuousWithinAt ?_
      refine OnePoint.continuousAt_coe.2 ?_
      have : (f ∘ ((↑) : ℂ → ExtPlane)) = fun y : ℂ => Real.log ‖y - w‖ := rfl
      rw [this]
      refine ContinuousAt.log (by fun_prop) (norm_ne_zero_iff.2 (sub_ne_zero.2 ?_))
      rintro rfl
      linarith
    set h : ℂ → ℝ := fun y => v (y : ExtPlane) - u0 (y : ExtPlane) with hh
    have hharm : InnerProductSpace.HarmonicOnNhd h unitDisc := by
      intro y hy
      have hy' : (y : ExtPlane) ∈ toExt unitDisc := ⟨y, hy, rfl⟩
      exact (gm22_harmonicAt_of_chart (hvh _ hy')).sub (gm22_harmonicAt_of_chart (hu0h _ hy'))
    have hb0 : ∀ ζ ∈ frontier unitDisc, Tendsto h (𝓝[unitDisc] ζ) (𝓝 0) := by
      intro ζ hζ
      have hζ' : ζ ∈ Metric.sphere (0 : ℂ) 1 := by
        simpa [unitDisc, frontier_ball _ (one_ne_zero)] using hζ
      have hx1 : ‖ζ‖ = 1 := by simpa using hζ'
      have hfr : (ζ : ExtPlane) ∈ frontier (toExt unitDisc) := by
        rw [hfrontier]; exact ⟨ζ, hζ', rfl⟩
      have hca : ContinuousAt u0 (ζ : ExtPlane) := by
        refine OnePoint.continuousAt_coe.2 ?_
        have : (u0 ∘ ((↑) : ℂ → ExtPlane)) = fun y : ℂ => Real.log ‖1 - y * conj w‖ := rfl
        rw [this]
        exact ContinuousAt.log (by fun_prop) (norm_ne_zero_iff.2 (hne ζ hx1.le))
      have hfu : f (ζ : ExtPlane) = u0 (ζ : ExtPlane) := by
        rw [hfc, hu0c, hcirc ζ hx1]
      have hvt := hvb _ hfr (hfcw _ hfr)
      rw [hfu] at hvt
      have hcoe : Tendsto (fun y : ℂ => (y : ExtPlane)) (𝓝[unitDisc] ζ) (𝓝[toExt unitDisc] (ζ : ExtPlane)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · exact (OnePoint.continuous_coe.tendsto ζ).mono_left nhdsWithin_le_nhds
        · exact eventually_nhdsWithin_of_forall fun y hy => ⟨y, hy, rfl⟩
      have h1 := hvt.comp hcoe
      have h2 : Tendsto (fun y : ℂ => u0 (y : ExtPlane)) (𝓝[unitDisc] ζ) (𝓝 (u0 (ζ : ExtPlane))) :=
        (hca.tendsto.comp (OnePoint.continuous_coe.tendsto ζ)).mono_left nhdsWithin_le_nhds
      have := h1.sub h2
      simpa [hh] using this
    have hz0 := LiZhongQC.eqOn_zero_of_harmonicOnNhd_of_tendsto_frontier (U := unitDisc) isOpen_ball hbd
      (isPreconnected_ball) hharm hb0 z hz
    simp only [hh] at hz0
    linarith
  have hset : {r : ℝ | ∃ u : ExtPlane → ℝ, IsBoundedDirichletSolution (toExt unitDisc) f u ∧ u (z : ExtPlane) = r} =
      {u0 (z : ExtPlane)} := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact huniq v hv
    · intro hr
      rw [Set.mem_singleton_iff] at hr
      exact ⟨u0, hsol, hr.symm⟩
  unfold dirichletSolution
  rw [hset, csSup_singleton]
  exact hu0c z

/-- **Formula (2.7)** (Ch. II §2, P1:1962–1966; cited at P1:1976). If `Ω` is the unit disc `𝔻`, then
`g(z, w) = log |(1 − z w̄)/(z − w)|`.
Modelling: for `z, w ∈ 𝔻` with `z ≠ w` (junk): at `z = w` the right side is `log 0 = 0` in Lean and the left side
is a junk value. -/
theorem eq2_2_7 {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    greenFunction (toExt unitDisc) z w = Real.log ‖(1 - z * conj w) / (z - w)‖ := by
  have hinf : LiZhongQC.extInf ∉ closure (toExt unitDisc) := by
    have hb : Bornology.IsBounded unitDisc := Metric.isBounded_ball
    rw [LiZhongQC.closure_toExt_of_isBounded hb]
    rintro ⟨x, -, hx⟩
    exact OnePoint.coe_ne_infty x hx
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc] using hz
  have hw1 : ‖w‖ < 1 := by simpa [unitDisc] using hw
  have h1 : (1 : ℂ) - z * conj w ≠ 0 := by
    intro h
    have : z * conj w = 1 := by linear_combination -h
    have h2 : ‖z‖ * ‖w‖ = 1 := by
      have := congrArg norm this
      simpa using this
    nlinarith [norm_nonneg z, norm_nonneg w]
  have h2 : z - w ≠ 0 := sub_ne_zero.2 hzw
  unfold greenFunction
  simp only [hinf, ↓reduceIte]
  rw [gm22_dirichletSolution_disc hz hw]
  have hld : logDistExt (z : ExtPlane) (w : ExtPlane) = Real.log ‖z - w‖ := rfl
  rw [hld, norm_div, Real.log_div (norm_ne_zero_iff.2 h1) (norm_ne_zero_iff.2 h2)]
  ring

/-- **Theorem 2.1** (Ch. II §2). Let `Ω` be a simply connected domain bounded by a Jordan curve, let `w ∈ Ω` and let
`ψ : Ω → 𝔻` be a conformal map with `ψ(w) = 0`. Then `g(z, w) = −log |ψ(z)|`.
Modelling: `Ω` is a Jordan domain of `ℂ*` and `ψ` a conformal map of `ℂ*`-domains onto `𝔻`; the identity is for
`z ∈ Ω \ {w}` (junk: at `z = w` the right side is `−log 0 = 0` in Lean), with `ψ(z) ∈ 𝔻` written as a point of `ℂ`. -/
theorem thm2_2_1 {Ω : Set ExtPlane} (hΩ : IsJordanDomainExt Ω) {w : ExtPlane} (hw : w ∈ Ω)
    {ψ : ExtPlane → ExtPlane} (hψ : IsConformalMap ψ Ω) (hψΩ : ψ '' Ω = toExt unitDisc)
    (hψw : ψ w = ((0 : ℂ) : ExtPlane)) :
    ∀ z ∈ Ω, z ≠ w → ∀ x : ℂ, ψ z = x → greenFunction Ω z w = -Real.log ‖x‖ := by
  sorry

/-- A parametrization of an analytic arc (Ch. II §2, P1:1978; helper): `ψ` is one-to-one and analytic on a
neighbourhood in `ℂ` of the open interval `(−1, 1)`. -/
def IsAnalyticArcParam (ψ : ℂ → ℂ) : Prop :=
  ∃ U : Set ℂ, IsOpen U ∧ (∀ t : ℝ, t ∈ Ioo (-1) 1 → (t : ℂ) ∈ U) ∧ InjOn ψ U ∧ AnalyticOnNhd ℂ ψ U

/-- **Definition** (analytic arc, Ch. II §2, P1:1978). An analytic arc is the image `ψ((−1, 1))` of the open
interval `(−1, 1)` under a map `ψ` one-to-one and analytic on a neighbourhood in `ℂ` of `(−1, 1)` to `ℂ`.
Modelling: a subset of the finite plane. `LehtoVirtanen1973.IsAnalyticOpenArc` asks only that every closed subarc be
analytic (a conformal map of a neighbourhood of each closed subarc), a weaker form that equals this one only through a
gluing lemma; no comparison theorem is stated. -/
def IsAnalyticArcGM (γ : Set ℂ) : Prop :=
  ∃ ψ : ℂ → ℂ, IsAnalyticArcParam ψ ∧ γ = (fun t : ℝ => ψ t) '' Ioo (-1) 1

/-- **Definition** (analytic Jordan curve, Ch. II §2, P1:1978). An analytic Jordan curve is a Jordan curve that is a
finite union of (open) analytic arcs.
Modelling: a Jordan curve of `ℂ*` (so that it can be a boundary component of a domain of `ℂ*`) that is the union of
finitely many analytic arcs of `ℂ`; in particular it lies in `ℂ`. `LehtoVirtanen1973.IsAnalyticCurve` (the image of
a circle under one conformal map of a neighbourhood) describes the same curves only through a local-to-global lemma
(the book's Exercise II.10(a), an exercise, not an item). -/
def IsAnalyticJordanCurve (Γ : Set ExtPlane) : Prop :=
  IsJordanCurve Γ ∧ ∃ (n : ℕ) (γ : Fin n → Set ℂ), (∀ j, IsAnalyticArcGM (γ j)) ∧ Γ = ⋃ j, toExt (γ j)

/-- **Lemma 2.2** (Ch. II §2; cited at P1:1989, 1997, 2254, 2930 and in App. B, P3:2607). Let `Ω` be a finitely
connected Jordan domain. Then there exists a finitely connected Jordan domain `Ω*` such that `∂Ω*` consists of
finitely many pairwise disjoint analytic Jordan curves and there exists a conformal map from `Ω` onto `Ω*` which
extends to be a homeomorphism from `Ω̄` to `Ω̄*`.
Modelling: the extension `Φ` is continuous and one-to-one on the compact set `Ω̄ ⊆ ℂ*` with image `Ω̄*`, which makes
it a homeomorphism of `Ω̄` onto `Ω̄*` (compact to Hausdorff). -/
theorem lemma2_2_2 {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) :
    ∃ (Ωs : Set ExtPlane) (φ Φ : ExtPlane → ExtPlane), IsFCJordanDomain Ωs ∧
      IsDisjointUnionOf IsAnalyticJordanCurve (frontier Ωs) ∧ IsConformalMap φ Ω ∧ φ '' Ω = Ωs ∧
      EqOn Φ φ Ω ∧ ContinuousOn Φ (closure Ω) ∧ InjOn Φ (closure Ω) ∧ Φ '' closure Ω = closure Ωs := by
  sorry

/-- **Theorem 2.3** (Ch. II §2; the symmetry (2.8), cited at P1:2029, 3392, 3556). Let `Ω` be a finitely connected
Jordan domain and let `z₁, z₂ ∈ Ω`. Then (2.8) `g(z₁, z₂) = g(z₂, z₁)`.
Modelling: no hypothesis `z₁ ≠ z₂` is needed: for `z₁ = z₂` both sides are the same value. `z₁` or `z₂` may be `∞`
(III.1 uses `g(∞, z) = g(z, ∞)`, P1:3556). -/
theorem thm2_2_3 {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) {z₁ z₂ : ExtPlane} (h₁ : z₁ ∈ Ω) (h₂ : z₂ ∈ Ω) :
    greenFunction Ω z₁ z₂ = greenFunction Ω z₂ z₁ := by
  sorry

/-- **Definition** (the unit outer normal, Ch. II §2, P1:2003 "the unit normal vector pointing out from the domain",
P1:2086 "the unit outer normal at `ζ ∈ ∂Ω`"; helper). `ν` is the unit outer normal of `Ω` at the finite point `ζ`:
`|ν| = 1`, and near `ζ` the domain looks like the half-plane `{x : Re((x − ζ) ν̄) < 0}`: for every `δ > 0` there is
`r > 0` such that the points `x` with `|x − ζ| < r` and `Re((x − ζ) ν̄) < −δ |x − ζ|` lie in `Ω`, and those with
`Re((x − ζ) ν̄) > δ |x − ζ|` lie outside `Ω̄`.
Modelling: the book uses the normal of a smooth boundary without defining it; this form needs no parametrization,
determines `ν` uniquely when it holds, and holds at every point of an analytic or `C¹` boundary curve. -/
def IsOuterUnitNormal (Ω : Set ExtPlane) (ζ ν : ℂ) : Prop :=
  ‖ν‖ = 1 ∧ ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ ∀ x : ℂ, ‖x - ζ‖ < r →
    (((x - ζ) * conj ν).re < -(δ * ‖x - ζ‖) → (x : ExtPlane) ∈ Ω) ∧
      (δ * ‖x - ζ‖ < ((x - ζ) * conj ν).re → (x : ExtPlane) ∉ closure Ω)

/-- **Definition** (the normal derivative `∂u/∂n(ζ)`, Ch. II §2, (2.10), (2.11), P1:2040, 2083). `u` has outer normal
derivative `L` at the boundary point `ζ`: `Ω` has a unit outer normal `ν` at `ζ`, `u(ζ − εν)` has a limit `b` as
`ε ↓ 0`, and `(b − u(ζ − εν))/ε → L`; that is, `∂u/∂n(ζ) = L` for the boundary value `u(ζ) = b`.
Modelling: only values of `u` inside `Ω` are read (the points `ζ − εν`, `ε > 0` small, lie in `Ω`), so the predicate
applies to functions such as Green's function that are defined only on `Ω`; for a function extending `C¹` across `ζ`
it is the derivative of the extension in the direction `ν`. -/
def HasOuterNormalDeriv (Ω : Set ExtPlane) (u : ExtPlane → ℝ) (ζ : ℂ) (L : ℝ) : Prop :=
  ∃ ν : ℂ, IsOuterUnitNormal Ω ζ ν ∧ ∃ b : ℝ,
    Tendsto (fun ε : ℝ => u ((ζ - ε * ν : ℂ) : ExtPlane)) (𝓝[>] 0) (𝓝 b) ∧
      Tendsto (fun ε : ℝ => (b - u ((ζ - ε * ν : ℂ) : ExtPlane)) / ε) (𝓝[>] 0) (𝓝 L)

/-- The value of the outer normal derivative `∂u/∂n(ζ)` (helper, Ch. II §2, used in (2.12) and in the Poisson kernel):
the `L` with `HasOuterNormalDeriv Ω u ζ L`, taken as the supremum of the set of such `L`, which has at most one
element (`ν` and the limits are unique). Junk: `0` where there is no outer normal or no normal derivative; every
statement that reads it assumes an analytic or `C^{1+α}` boundary, where the normal derivative of Green's function
exists. -/
def outerNormalDeriv (Ω : Set ExtPlane) (u : ExtPlane → ℝ) (ζ : ℂ) : ℝ :=
  sSup {L : ℝ | HasOuterNormalDeriv Ω u ζ L}

/-- **Lemma 2.4** (Ch. II §2), first part (cited at P1:1997, 2100, 2226, and in IV, P1:6205). Suppose `Ω` is a
finitely connected Jordan domain and suppose `γ ⊆ ∂Ω` is an analytic arc. Let `u(z)` be a harmonic function in `Ω`.
If `lim_{z→ζ} u(z) = 0` for all `ζ ∈ γ`, then there is an open set `W ⊇ γ ∪ Ω` such that `u` extends to be harmonic
on `W`.
Modelling: `u` is real-valued on `ℂ*` and harmonic in the charts of `ℂ*`; the extension `U` is harmonic on `W` and
equal to `u` on `Ω`. -/
theorem lemma2_2_4_i {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) {γ : Set ℂ} (hγ : IsAnalyticArcGM γ)
    (hγΩ : toExt γ ⊆ frontier Ω) {u : ExtPlane → ℝ} (hu : HarmonicOnExt u Ω)
    (hlim : ∀ ζ ∈ γ, Tendsto u (𝓝[Ω] (ζ : ExtPlane)) (𝓝 0)) :
    ∃ W : Set ExtPlane, IsOpen W ∧ toExt γ ∪ Ω ⊆ W ∧ ∃ U : ExtPlane → ℝ, HarmonicOnExt U W ∧ EqOn U u Ω := by
  sorry

/-- **Lemma 2.4** (Ch. II §2), second part. In the situation of the first part, if also `u(z) > 0` in `Ω`, then (2.10)
`∂u/∂n(ζ) < 0` for all `ζ ∈ γ`.
Modelling: the normal derivative exists and is negative: `HasOuterNormalDeriv Ω u ζ L` with `L < 0` (the boundary
value is `0`, so `L = lim_{ε↓0} −u(ζ − εν)/ε`). -/
theorem lemma2_2_4_ii {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) {γ : Set ℂ} (hγ : IsAnalyticArcGM γ)
    (hγΩ : toExt γ ⊆ frontier Ω) {u : ExtPlane → ℝ} (hu : HarmonicOnExt u Ω)
    (hlim : ∀ ζ ∈ γ, Tendsto u (𝓝[Ω] (ζ : ExtPlane)) (𝓝 0)) (hpos : ∀ z ∈ Ω, 0 < u z) :
    ∀ ζ ∈ γ, ∃ L : ℝ, L < 0 ∧ HasOuterNormalDeriv Ω u ζ L := by
  sorry

/-- Arc length `ds` on `∂Ω` (helper, Ch. II §2 from (2.12) on): the one-dimensional Hausdorff measure of `ℂ` (arc
length on rectifiable curves) restricted to the finite part of `∂Ω`. -/
def arcLengthOn (Ω : Set ExtPlane) : Measure ℂ :=
  (μH[1] : Measure ℂ).restrict (finitePart (frontier Ω))

/-- **Theorem 2.5** (Ch. II §2), first part ((2.11), cited at P1:2100, 2174). Assume `∂Ω` consists of finitely many
pairwise disjoint analytic Jordan curves, and let `z ∈ Ω`. Then Green's function `g(ζ, z)` extends to be harmonic
(and hence real analytic) on a neighbourhood of `∂Ω`, and (2.11) `−∂g(ζ, z)/∂n_ζ > 0` on `∂Ω`, where `n_ζ` is the
unit outer normal at `ζ ∈ ∂Ω`.
Modelling: `Ω` is a domain of `ℂ*` (then a finitely connected Jordan domain); the harmonic extension `U` of
`g(·, z)` lives on an open `V ⊇ ∂Ω` and equals `g(·, z)` on `V ∩ Ω`; (2.11) says that the normal derivative exists at
every `ζ ∈ ∂Ω ⊆ ℂ` and is negative. -/
theorem thm2_2_5_i {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω)
    (hΓ : IsDisjointUnionOf IsAnalyticJordanCurve (frontier Ω)) {z : ExtPlane} (hz : z ∈ Ω) :
    (∃ V : Set ExtPlane, IsOpen V ∧ frontier Ω ⊆ V ∧
      ∃ U : ExtPlane → ℝ, HarmonicOnExt U V ∧ EqOn U (fun ζ => greenFunction Ω ζ z) (V ∩ Ω)) ∧
      ∀ ζ : ℂ, (ζ : ExtPlane) ∈ frontier Ω →
        ∃ L : ℝ, L < 0 ∧ HasOuterNormalDeriv Ω (fun w => greenFunction Ω w z) ζ L := by
  sorry

/-- **Theorem 2.5** (Ch. II §2), second part ((2.12), cited at P1:2092–2152, 2218, 2226, and in App. H, P3:4875).
Assume `∂Ω` consists of finitely many pairwise disjoint analytic Jordan curves, and let `z ∈ Ω`. If `u ∈ C(Ω̄)` is
harmonic on `Ω`, then (2.12) `u(z) = ∫_{∂Ω} (−∂g(ζ, z)/∂n_ζ) u(ζ) ds(ζ)/2π`.
Modelling: `ds` is `arcLengthOn Ω`; the normal derivative is read through `outerNormalDeriv`, which exists at every
boundary point under the hypotheses (first part). -/
theorem thm2_2_5_ii {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω)
    (hΓ : IsDisjointUnionOf IsAnalyticJordanCurve (frontier Ω)) {z : ExtPlane} (hz : z ∈ Ω)
    {u : ExtPlane → ℝ} (hu : ContinuousOn u (closure Ω)) (hh : HarmonicOnExt u Ω) :
    u z = ∫ ζ, -outerNormalDeriv Ω (fun w => greenFunction Ω w z) ζ * u ζ / (2 * π) ∂(arcLengthOn Ω) := by
  sorry

/-- **Definition** (the Poisson kernel for `Ω`, Ch. II §2, P1:2092–2098). Because of (2.12),
`P_z(ζ) = −(1/2π) ∂g(ζ, z)/∂n_ζ` is called the Poisson kernel for `Ω`.
Modelling: `z ∈ ℂ*`, `ζ ∈ ℂ` a boundary point. Junk: `0` where the normal derivative does not exist (not an analytic
or `C^{1+α}` boundary point); never used there. -/
def poissonKernelFC (Ω : Set ExtPlane) (z : ExtPlane) (ζ : ℂ) : ℝ :=
  -(1 / (2 * π)) * outerNormalDeriv Ω (fun w => greenFunction Ω w z) ζ

/-- **Corollary 2.6** (Ch. II §2; cited at P1:2176, 2260, 2942). If `∂Ω` consists of finitely many pairwise disjoint
analytic Jordan curves and if `z ∈ Ω`, then (2.14) `dω(z, ζ) = −(∂g(z, ζ)/∂n_ζ) ds(ζ)/2π`. In other words, harmonic
measure for `z ∈ Ω` is absolutely continuous to arc length on `∂Ω`, the density
`dω/ds = −(1/2π) ∂g(z, ζ)/∂n_ζ = P_z(ζ)` is real analytic on `∂Ω`, and (2.15) `c₁ < dω/ds < c₂` for positive
constants `c₁` and `c₂`.
Modelling: (2.14) as the equality of `ω(z, ·)` with the image in `ℂ*` of `ds` with density
`−(1/2π) ∂g(z, ζ)/∂n_ζ` (the derivative in the pole variable, as printed; it equals the Poisson kernel, which
differentiates `g(ζ, z)`, by the symmetry (2.8)); "real analytic on `∂Ω`" is real analyticity along every analytic
arc of `∂Ω`, in its parameter `t ∈ (−1, 1)`; `c₁, c₂` depend on `Ω` and `z`. -/
theorem cor2_2_6 {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω)
    (hΓ : IsDisjointUnionOf IsAnalyticJordanCurve (frontier Ω)) {z : ExtPlane} (hz : z ∈ Ω) :
    harmonicMeasureFC Ω z = ((arcLengthOn Ω).withDensity fun ζ =>
        ENNReal.ofReal (-(1 / (2 * π)) * outerNormalDeriv Ω (fun w => greenFunction Ω z w) ζ)).map
        ((↑) : ℂ → ExtPlane) ∧
      (∀ ζ : ℂ, (ζ : ExtPlane) ∈ frontier Ω →
        -(1 / (2 * π)) * outerNormalDeriv Ω (fun w => greenFunction Ω z w) ζ = poissonKernelFC Ω z ζ) ∧
      (∀ ψ : ℂ → ℂ, IsAnalyticArcParam ψ → (∀ t : ℝ, t ∈ Ioo (-1) 1 → ((ψ t : ℂ) : ExtPlane) ∈ frontier Ω) →
        AnalyticOnNhd ℝ (fun t : ℝ => poissonKernelFC Ω z (ψ t)) (Ioo (-1) 1)) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ ζ : ℂ, (ζ : ExtPlane) ∈ frontier Ω →
        c₁ < poissonKernelFC Ω z ζ ∧ poissonKernelFC Ω z ζ < c₂ := by
  sorry

/-- **Definition** (the cone `Γ_α(ζ)` in `Ω`, Ch. II §2, Theorem 2.7, P1:2178–2182). For `ζ ∈ ∂Ω` and `α > 1`,
`Γ_α(ζ) = {z ∈ Ω : |z − ζ| < α dist(z, ∂Ω)}`.
Modelling: a set of finite points (the boundary is analytic, hence in `ℂ`); `dist(z, ∂Ω)` is the distance to the
finite part of `∂Ω`. -/
def coneIn (Ω : Set ExtPlane) (α : ℝ) (ζ : ℂ) : Set ℂ :=
  {z : ℂ | (z : ExtPlane) ∈ Ω ∧ ‖z - ζ‖ < α * infDist z (finitePart (frontier Ω))}

/-- **Theorem 2.7** (Ch. II §2), first part ((2.16), (2.17), (2.18); cited at P1:1912, 2250). Assume `∂Ω` consists of
finitely many pairwise disjoint analytic Jordan curves, and for `ζ ∈ ∂Ω` and `α > 1` let `Γ_α(ζ)` be the cone. If
`u(z)` is a bounded harmonic function on `Ω`, then for `ds`-almost all `ζ ∈ ∂Ω` the limit (2.16)
`lim_{Γ_α(ζ)∋z→ζ} u(z) = f(ζ)` exists, (2.17) `u(z) = ∫_{∂Ω} P_z(ζ) f(ζ) ds(ζ)`, and (2.18) `sup_Ω |u(z)| = ‖f‖_{L^∞}`.
Modelling: [OCR] the statement's "H u(z)" (P1:2184) is read "If u(z)"; `f` does not depend on `α` (the cones
increase with `α`), so it is chosen before `α`; `f ∈ L^∞(∂Ω, ds)`; `u` is real-valued. -/
theorem thm2_2_7_i {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω)
    (hΓ : IsDisjointUnionOf IsAnalyticJordanCurve (frontier Ω)) {u : ExtPlane → ℝ} (hu : HarmonicOnExt u Ω)
    (hub : ∃ M : ℝ, ∀ z ∈ Ω, |u z| ≤ M) :
    ∃ f : ℂ → ℝ, MemLp f ⊤ (arcLengthOn Ω) ∧
      (∀ α : ℝ, 1 < α → ∀ᵐ ζ ∂(arcLengthOn Ω), Tendsto (fun x : ℂ => u x) (𝓝[coneIn Ω α ζ] ζ) (𝓝 (f ζ))) ∧
      (∀ z ∈ Ω, u z = ∫ ζ, poissonKernelFC Ω z ζ * f ζ ∂(arcLengthOn Ω)) ∧
      ⨆ z ∈ Ω, ‖u z‖ₑ = eLpNorm f ⊤ (arcLengthOn Ω) := by
  sorry

/-- **Theorem 2.7** (Ch. II §2), second part ((2.16)–(2.19)). Conversely, if `f` is a bounded Borel function on
`∂Ω`, then (2.17) defines a bounded harmonic function `u(z)` on `Ω` such that (2.18) holds and (2.16) holds `ds`-almost
everywhere. Moreover, if `f` is continuous at `ζ₀ ∈ ∂Ω`, then (2.19) `lim_{z→ζ₀} u(z) = f(ζ₀)`.
Modelling: `u` is any function equal to the integral (2.17) on `Ω`; "continuous at `ζ₀`" is continuity of `f` as a
function on `∂Ω`; the limit (2.19) is along `Ω`. -/
theorem thm2_2_7_ii {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω)
    (hΓ : IsDisjointUnionOf IsAnalyticJordanCurve (frontier Ω)) {f : ℂ → ℝ} (hf : Measurable f)
    (hfb : ∃ M : ℝ, ∀ ζ ∈ finitePart (frontier Ω), |f ζ| ≤ M) {u : ExtPlane → ℝ}
    (hu : ∀ z ∈ Ω, u z = ∫ ζ, poissonKernelFC Ω z ζ * f ζ ∂(arcLengthOn Ω)) :
    HarmonicOnExt u Ω ∧ (∃ M : ℝ, ∀ z ∈ Ω, |u z| ≤ M) ∧ ⨆ z ∈ Ω, ‖u z‖ₑ = eLpNorm f ⊤ (arcLengthOn Ω) ∧
      (∀ α : ℝ, 1 < α → ∀ᵐ ζ ∂(arcLengthOn Ω), Tendsto (fun x : ℂ => u x) (𝓝[coneIn Ω α ζ] ζ) (𝓝 (f ζ))) ∧
      ∀ ζ₀ ∈ finitePart (frontier Ω), ContinuousWithinAt f (finitePart (frontier Ω)) ζ₀ →
        Tendsto u (𝓝[Ω] (ζ₀ : ExtPlane)) (𝓝 (f ζ₀)) := by
  sorry

/-- **Definition** (the maximal function `M_s f`, Ch. II §2, P1:2244–2248). `M_s f(ζ)` is the supremum of the
averages of `|f|` over arcs `γ ⊆ ∂Ω` with `ζ ∈ γ`: `M_s f(ζ) = sup_{γ∋ζ} (1/ℓ(γ)) ∫_γ |f| ds`, with values in
`[0, ∞]`.
Modelling: the arcs are Jordan arcs (`LehtoVirtanen1973.IsJordanArc`) contained in the finite part of `∂Ω`, and
`ℓ(γ)` is their length `μH[1] γ`. -/
def arcMaximal (Ω : Set ExtPlane) (f : ℂ → ℝ) (ζ : ℂ) : ℝ≥0∞ :=
  ⨆ (γ : Set ℂ) (_ : γ ⊆ finitePart (frontier Ω) ∧ LehtoVirtanen1973.IsJordanArc (toExt γ) ∧ ζ ∈ γ),
    (μH[1] γ)⁻¹ * ∫⁻ x in γ, ‖f x‖ₑ ∂μH[1]

/-- **Formula (2.20)** (Ch. II §2, P1:2238–2248; cited at P1:2252 and in Exercise 9). Using the real analyticity of
`g(w, z)`, one can refine the proof of Lemma I.2.2 and show that (2.20) `sup_{Γ_α(ζ)} |u(z)| ≤ C(α, Ω) M_s f(ζ)`, where
`u` is the Poisson integral (2.17).
Modelling: `∂Ω` consists of analytic Jordan curves (the setting of Theorem 2.7); `f ∈ L¹(∂Ω, ds)`, as for Lemma
I.2.2 which (2.20) refines (the Poisson integral (2.17) is defined for such `f`); `C` depends on `α` and `Ω` only; the
inequality is in `[0, ∞]`.
[CORRECTION] As printed, (2.20) is false when `∂Ω` has more than one component: the arcs `γ ∋ ζ` lie in the
component `J` of `∂Ω` that contains `ζ`, so for `f ≥ 0` vanishing on `J` and not a.e. zero we get `M_s f(ζ) = 0`
while `u > 0` on `Ω`. It is stated in the additive form
`sup_{Γ_α(ζ)} |u(z)| ≤ C(α, Ω) (M_s f(ζ) + ∫_{∂Ω∖J} |f| ds)`, which holds for every `f ∈ L¹(ds)` and is the printed
statement when `∂Ω` is connected (the integral is then over the empty set). Argument: write `f = f₁ + f₂` with
`f₁ = f` on `J` and `f₂ = f` off `J`. Every arc `γ ∋ ζ` of `∂Ω` lies in `J`, so `M_s f₁(ζ) = M_s f(ζ)`, and the
refined Lemma I.2.2 argument (the arcs `γ ∋ ζ` exhaust `J`) bounds the Poisson integral of `f₁` on `Γ_α(ζ)` by
`C M_s f(ζ)`. A point `z ∈ Γ_α(ζ)` has `dist(z, ∂Ω) > |z − ζ|/α`, hence `dist(z, ∂Ω∖J) ≥ δ/(1 + α)`, `δ` the least
distance between two boundary curves; by the real analyticity of `g` up to `∂Ω` (Theorem 2.5) the kernel `P_z(ξ)`
is bounded for such `z` and `ξ ∈ ∂Ω∖J`, and the Poisson integral of `f₂` is at most `C ∫_{∂Ω∖J} |f| ds` there. -/
theorem eq2_2_20 {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω)
    (hΓ : IsDisjointUnionOf IsAnalyticJordanCurve (frontier Ω)) {α : ℝ} (hα : 1 < α) :
    ∃ C : ℝ, ∀ f : ℂ → ℝ, Integrable f (arcLengthOn Ω) → ∀ u : ExtPlane → ℝ,
      (∀ z ∈ Ω, u z = ∫ ζ, poissonKernelFC Ω z ζ * f ζ ∂(arcLengthOn Ω)) →
      ∀ ζ ∈ finitePart (frontier Ω),
        ⨆ x ∈ coneIn Ω α ζ, ‖u x‖ₑ ≤ ENNReal.ofReal C * (arcMaximal Ω f ζ +
          ∫⁻ ξ in (connectedComponentIn (finitePart (frontier Ω)) ζ)ᶜ, ‖f ξ‖ₑ ∂(arcLengthOn Ω)) := by
  sorry

/-- **Unlabelled** (Ch. II §2, P1:2254; used at P1:2942, "since harmonic measure is conformally invariant"). Let `Ω`
be a finitely connected Jordan domain and `φ` a conformal map of `Ω` onto a finitely connected Jordan domain `Ω'`
that is a homeomorphism of `Ω̄` onto `Ω̄'`. Then harmonic measure can be transplanted by `φ`:
`ω(z, E, Ω) = ω(φ(z), φ(E), Ω')` ("an alternate but equivalent definition of harmonic measure for `Ω`").
Modelling: the book states this for the map of Lemma 2.2 onto a domain with analytic boundary, and uses it for any
such map at P1:2942; `φ` is a conformal map of `ℂ*`-domains with continuous one-to-one extension `Φ` of `Ω̄` onto
`Ω̄'`; `E` is a Borel subset of `∂Ω` and `φ(E)` is `Φ(E)`. -/
theorem harmonicMeasureFC_conformal {Ω Ω' : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) (hΩ' : IsFCJordanDomain Ω')
    {φ Φ : ExtPlane → ExtPlane} (hφ : IsConformalMap φ Ω) (hφΩ : φ '' Ω = Ω') (hΦφ : EqOn Φ φ Ω)
    (hΦ : ContinuousOn Φ (closure Ω)) (hΦi : InjOn Φ (closure Ω)) (hΦΩ : Φ '' closure Ω = closure Ω')
    {z : ExtPlane} (hz : z ∈ Ω) {E : Set ExtPlane} (hE : MeasurableSet E) (hEΩ : E ⊆ frontier Ω) :
    harmonicMeasureFC Ω' (φ z) (Φ '' E) = harmonicMeasureFC Ω z E := by
  sorry

end GarnettMarshall2005
