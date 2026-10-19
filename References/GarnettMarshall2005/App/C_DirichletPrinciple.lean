import References.GarnettMarshall2005.Ch03.S01_CapacityGreenFunctions
import References.GarnettMarshall2005.Ch04.S04_ExtremalMetricsExtremalDistance

/-!
# Garnett–Marshall, Appendix C: The Dirichlet principle

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Appendix C (pp. 447–456;
`full.md` P3:2776–3184; no Notes, no exercises).

Conventions (leader rulings Fa1, Fa3). Domains are bounded plane sets `Ω : Set ℂ`: the disc `𝔻 = LiZhongQC.unitDisc`
(Lemmas C.1, C.2) and bounded finitely connected Jordan domains, `IsFCJordanDomain (toExt Ω) ∧ Bornology.IsBounded Ω`
(Theorem C.3, Corollary C.4). Every finitely connected Jordan domain of `ℂ*` is the image of a bounded one under a
Möbius map, and the Dirichlet integral is a conformal invariant (`dirichletIntegralGM_comp_conformal`), so the
boundedness loses nothing; it keeps the Dirichlet integral a plane integral. Boundaries and closures are taken in `ℂ`.
Functions are real and planar, `ℂ → ℝ`; where a predicate of Chapters I–II on `ℂ*` is applied, a function `v` is
lifted by `fun w => w.elim 0 v` (Mathlib's `OnePoint.elim`), whose value at `∞` is never read. `∂𝔻` is
`Metric.sphere 0 1`, an open arc of `∂𝔻` is `openArc a b` with `a < b ≤ a + 2π` (Ch. I §1), and "a (nonempty) finite
union of open arcs on `∂Ω`" is Ch. IV §4's helper `IsFiniteUnionOf` (at least one member) of open Jordan arcs
(`LehtoVirtanen1973.IsOpenJordanArc`) contained in `∂Ω`. The Dirichlet integral `D(u) = D_Ω(u)` is
`dirichletIntegralGM Ω u ∈ [0, ∞]` (the value `∞` is part of the discourse: the counterexample to (C.2) and every
hypothesis "`D(v) < ∞`"), and `D(u, v)` is `dirichletInner Ω u v`, read only when `D(u), D(v) < ∞`.
"`lim_{z→ζ} v(z) = f(ζ)`" is `Tendsto v (𝓝[Ω] ζ) (𝓝 (f ζ))`; `limsup ≤ 0` and `liminf ≥ 1` are written in `ε`-form
(Part A §2); `∂u/∂n` and `∂u/∂r` are Ch. II §2's `HasOuterNormalDeriv` (outer unit normal; on `∂𝔻` it is the radial
derivative); "harmonic", `Δu = 0`, is Mathlib's `InnerProductSpace.HarmonicOnNhd`. Each statement writes its class
(`𝒟_f`, `𝒞_f`, (C.12)) as a set named by a hypothesis `h𝒟 : 𝒟 = {v | …}`. "The extremal problem has a unique
solution `u`" and "`u` is the unique element of minimal Dirichlet norm" are stated as two claims: `u` lies in the
class and minimizes `D` over it, and every minimizer in the class equals `u` on the domain (not as an equivalence).

* Definition (piecewise continuous function on `∂𝔻`: continuous except on a finite set `E`, with finite left and
  right limits at each point of `E`, App. C, P3:2778) — exists: `GarnettMarshall2005.IsPiecewiseContinuousOn`
  (Ch. II §1's notion at the domain toExt unitDisc, whose boundary is the unit circle, applied to the lift of a
  plane function; its extra conjunct "f is bounded on the boundary" holds automatically: f is continuous off the
  finite set E of the compact circle and has finite one-sided limits at the points of E; the one-sided limits are
  taken along a loop parametrization, i.e. along the circle)
* Definition (piecewise smooth function on a domain `Ω`: continuous on `Ω` and continuously differentiable on
  `Ω \ J` for a finite union `J` of closed or open analytic arcs in `Ω`; closed analytic arcs, App. C, P3:2778) —
  `IsPiecewiseSmooth`, `IsClosedAnalyticArcGM`
* Definition (the Dirichlet integral, or squared Dirichlet norm, `D(u) = D_Ω(u) = ∬_Ω |∇u|² dx dy`, App. C,
  P3:2778–2782) — `dirichletIntegralGM`
* Unlabelled (App. C, P3:2784–2790): if `u = Re F` with `F` analytic on `Ω`, then `D(u) = ∬_Ω |F′|² dx dy` =
  `Area F(Ω)`, values counted with multiplicity — `dirichletIntegralGM_re_eq_area`
* Definition (the Dirichlet inner product `D(u, v) = ∬_Ω ∇u · ∇v dx dy` for `D(u), D(v) < ∞`, App. C,
  P3:2790–2794) — `dirichletInner`
* Formula (C.1) (App. C, P3:2802–2806) — `eqC_1`
* Definition (the class `𝒟_f` of piecewise smooth functions on `Ω` with `lim_{z→ζ} v(z) = f(ζ)` on `∂Ω`, App. C,
  P3:2808–2810) — omitted: each statement writes its own class inline (Lemma C.1, Lemma C.2, Theorem C.3 and
  Corollary C.4 each define a different class)
* Formula (C.2), the Dirichlet principle (named assertion, App. C, P3:2812–2818) — omitted: the assertion that the
  extremal problem (C.2) over the class of piecewise smooth functions with boundary values f has a unique solution,
  and that it solves the Dirichlet problem, is false, and the book refutes it at once (the counterexample below
  (C.4)); its correct forms are Lemma C.1, Theorem C.3 and Corollary C.4 (the citations of the Dirichlet principle,
  II Notes P1:2950, III Exercise 21(d) P1:5750, point to the appendix as a whole)
* Formula (C.4) (App. C, P3:2818–2834; with the Fourier series (C.3)) — `eqC_4`
* Lemma C.1 (App. C) — `lemmaC_1`
* Unlabelled (App. C, P3:2908–2914; formula (C.6) of the proof of Lemma C.1): `D(v) = D(u) + D(v − u)` for `v ∈ 𝒟_f`
  with `D(v) < ∞` — `eqC_6`
* Unlabelled (App. C, P3:2916): the Dirichlet integral is a conformal invariant — `dirichletIntegralGM_comp_conformal`
* Unlabelled (App. C, P3:2916): Lemma C.1 also holds with any simply connected Jordan domain in place of `𝔻` —
  `lemmaC_1_jordan`
* Lemma C.2 (App. C; (C.7)) — `lemmaC_2`
* Definition (free boundary: the set `∂𝔻 \ Ī` of Lemma C.2, App. C, P3:2932) — omitted: a term used by no statement
  (leader ruling B6)
* Theorem C.3 (App. C; (C.8), (C.9)) — `thmC_3_a`, `thmC_3_b`
* Corollary C.4 (App. C; (C.12)–(C.15)) — `corC_4_a`, `corC_4_b`

Helpers (not book notions): `IsClosedAnalyticArcGM` (a compact subarc of an analytic arc) and `IsArcOfClass` (a
closed arc of class `C^{k+α}`, the arc version of Ch. II §4's `IsCurveOfClass`, for "`C^{1+α}` arcs" in Theorem C.3).

Not stated (inventory U−, remarks, examples and proof steps): the Cauchy–Schwarz inequality
`D(u, v) ≤ √D(u) √D(v)` (P3:2796–2800; not cited later, the Cauchy–Schwarz inequalities of the proofs of Theorem C.3
and Lemma G.2 concern other integrals); the Fourier series (C.3) as a notation (its coefficients are written inline in
`eqC_4` with Mathlib's `fourierCoeffOn`) and the Poisson series `u(re^{iθ}) = Σ a_n r^{|n|} e^{inθ}` (P3:2818–2828,
used only through the partial sums `u_N` in the proof of Lemma C.1); the example
`f(e^{iθ}) = Σ_{k≥1} k^{−2} cos(2^k θ) ∈ C(∂𝔻)` with `D(u) = π Σ 2^k/k⁴ = ∞` (P3:2836–2846); "this example is the
only thing wrong with Dirichlet principle … (C.2) holds whenever `𝒟_f ∩ {v : D(v) < ∞} ≠ ∅`" (P3:2848–2852, it
announces Lemma C.1 and Theorem C.3); the proof of Lemma C.1 (`u_N`, (C.5), P3:2870–2906, and the step from (C.6) to
uniqueness); the proof of Lemma C.2 (the map to `𝔻⁺`, the reflected data `g`, Figure C.1, `γ_ε`, `W_ε`, `z*`, `V_δ`,
`D_{𝔻⁺}(v) = ½ lim D_𝔻(V_δ)`, P3:2934–2983); the proof of Theorem C.3 (minimizing sequences, (C.10), the independence
of `(α, β)` from the sequence, the mean value estimate for harmonic functions, (C.11), `W = Ω ∩ B(ζ, δ)`, Figure C.2,
P3:3019–3127; it applies (C.6) on the Jordan domain `W`, a proof-internal use: no Jordan form of (C.6) is stated,
leader ruling Fa11); the two proofs of Corollary C.4 (the truncation `h ∘ v`; "`u` is a harmonic measure on a
Riemann surface double of `Ω`"; `|∇u| = O(|z − ζ|^{−1/2})` at the endpoints; `D_Ω(v − u, u) = ∫_{E∪F} (v − u) ∂u/∂n
ds`; "a third proof will be given in Appendix H", P3:3157–3183). (C.5), (C.10) and (C.11) are proof steps. In the
second proof of Corollary C.4 (P3:3177) "`0 ≤ u(z) ≤ 1` by Exercise H.5(a)" is a misdirected reference [misprint?]:
Exercise H.5 (P3:4919) has no part (a) and concerns Theorem H.9; `0 ≤ u ≤ 1` is the maximum principle. In the proof of
Theorem C.3, "Lemma (C.2)" (P3:3127) is Lemma C.2 [OCR].
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt unitDisc IsConformalOnto)
open InnerProductSpace (HarmonicOnNhd)

/-- A closed analytic arc (helper, App. C, P3:2778, "closed or open analytic arcs"): the image `ψ([a, b])` of a
compact interval `[a, b] ⊂ (−1, 1)` under a parametrization `ψ` of an analytic arc (Ch. II §2's
`IsAnalyticArcParam`: one-to-one and analytic on a neighbourhood of `(−1, 1)`).
Modelling: a compact subarc of an (open) analytic arc of Ch. II §2; every arc `ψ([a, b])` with `ψ` one-to-one and
analytic on a neighbourhood of `[a, b]` is of this form after an affine change of parameter. -/
def IsClosedAnalyticArcGM (γ : Set ℂ) : Prop :=
  ∃ ψ : ℂ → ℂ, IsAnalyticArcParam ψ ∧ ∃ a b : ℝ, -1 < a ∧ a < b ∧ b < 1 ∧ γ = (fun t : ℝ => ψ t) '' Icc a b

/-- **Definition** (piecewise smooth, App. C, P3:2778; used in every statement of App. C, and for "piecewise `C¹`" in
App. H, P3:4621). A real valued function `u(z)` is piecewise smooth on a domain `Ω` if `u(z)` is continuous on `Ω`
and continuously differentiable on `Ω \ J`, where `J = J(u)` is a finite union of (closed or open) analytic arcs in
`Ω`.
Modelling: open analytic arcs are Ch. II §2's `IsAnalyticArcGM` (P1:1978), closed ones `IsClosedAnalyticArcGM`; the
arcs are indexed by `Fin k`, and `k = 0` (`J = ∅`) is allowed; "in `Ω`" is `γ_i ⊆ Ω`; "continuously differentiable
on `Ω \ J`" is `ContDiffOn ℝ 1 u (Ω \ J)`. `J` has area zero, so the Dirichlet integral does not see it. -/
def IsPiecewiseSmooth (Ω : Set ℂ) (u : ℂ → ℝ) : Prop :=
  ContinuousOn u Ω ∧ ∃ (k : ℕ) (γ : Fin k → Set ℂ),
    (∀ i, (IsAnalyticArcGM (γ i) ∨ IsClosedAnalyticArcGM (γ i)) ∧ γ i ⊆ Ω) ∧ ContDiffOn ℝ 1 u (Ω \ ⋃ i, γ i)

/-- **Definition** (the Dirichlet integral, App. C, P3:2778–2782; used throughout App. C, in App. G, P3:4394, 4446,
and in App. H, P3:4603, 4752, 4780). The Dirichlet integral of `u`, or the squared Dirichlet norm of `u`, is
`D(u) = D_Ω(u) = ∬_Ω |∇u|² dx dy = ∬_{Ω∖J} |∇u|² dx dy`.
Modelling (leader ruling Fa3): a lower Lebesgue integral with values in `[0, ∞]`, since `D(u) = ∞` is part of the
discourse (the counterexample to (C.2), every hypothesis "`D(v) < ∞`"); `|∇u(z)|` is `‖fderiv ℝ u z‖`, the operator
norm of the real derivative, a functional on the Euclidean plane `ℂ`, which is `(u_x² + u_y²)^{1/2}`. The derivative's
junk value `0` at points where `u` is not differentiable is read, for the piecewise smooth `u` of every statement, only
on the null set `J(u)` and at the finitely many endpoints of its open arcs, which is the book's second expression.
B-cand. `LiZhongQC.dirichletIntegral` (a real-valued Bochner integral, whose junk value `0` is taken exactly where
`D(u) = ∞`) is not used; LV's `O_AD` writes the same lower integral inline. -/
def dirichletIntegralGM (Ω : Set ℂ) (u : ℂ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Ω, ‖fderiv ℝ u z‖ₑ ^ 2

/-- **Unlabelled** (App. C, P3:2784–2790; used in App. H, in the proof of Theorem H.1, P3:4752, "The Dirichlet integral
`D(ω)` is the sum of the areas of the rectangles", and in Example H.5, P3:4780). If `u = Re F` and `F` is analytic on
`Ω`, then `D(u) = ∬_Ω |F′|² dx dy = Area F(Ω)`, where each value `F(z)` is counted according to its multiplicity.
Modelling: `Ω` is any open set (the book's domain; connectedness plays no role); "`Area F(Ω)` counted with
multiplicity" is the integral over `ℂ` of the counting function `w ↦ #{z ∈ Ω : F(z) = w}` (in `ℕ∞`, an infinite
multiplicity counting `∞`); both equalities are in `[0, ∞]`. -/
theorem dirichletIntegralGM_re_eq_area {Ω : Set ℂ} (hΩ : IsOpen Ω) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F Ω) :
    dirichletIntegralGM Ω (fun z => (F z).re) = ∫⁻ z in Ω, ‖deriv F z‖ₑ ^ 2 ∧
      ∫⁻ z in Ω, ‖deriv F z‖ₑ ^ 2 = ∫⁻ w, ((({z ∈ Ω | F z = w}).encard : ℕ∞) : ℝ≥0∞) := by
  sorry

/-- **Definition** (the Dirichlet inner product, App. C, P3:2790–2794; used in (C.1) and in the proofs of Lemma C.1
and Corollary C.4). If `D(u) < ∞` and `D(v) < ∞`, the Dirichlet inner product is
`D(u, v) = ∬_Ω ∇u · ∇v dx dy = ∬_Ω (u_x v_x + u_y v_y) dx dy`.
Modelling (leader ruling Fa3): a real Bochner integral, with `u_x = fderiv ℝ u z 1` and `u_y = fderiv ℝ u z I`; the
integrand is integrable when `D(u), D(v) < ∞` (pointwise Cauchy–Schwarz). Junk: `0` when the integrand is not
integrable; never read there, since every statement assumes `D(u), D(v) < ∞`. -/
def dirichletInner (Ω : Set ℂ) (u v : ℂ → ℝ) : ℝ :=
  ∫ z in Ω, (fderiv ℝ u z 1 * fderiv ℝ v z 1 + fderiv ℝ u z I * fderiv ℝ v z I)

/-- **Formula (C.1)** (App. C, P3:2802–2806; cited in the proofs of Lemma C.1, P3:2894, Theorem C.3, P3:3027, and
Corollary C.4, P3:3180). If `D(u) < ∞` and `D(v) < ∞`, then (C.1) `D(u ± v) = D(u) + D(v) ± 2 D(u, v)`.
Modelling: `u` and `v` are piecewise smooth on the open set `Ω` (the book defines `D` for piecewise smooth functions;
it makes `∇(u ± v) = ∇u ± ∇v` hold off a null set); the setting in which `D(u, v)` is defined, `D(u), D(v) < ∞`, is
assumed. The conclusion states `D(u ± v) < ∞` (implicit in the book's finite right side) and the two identities for
the real numbers `D(u ± v)`; both signs are one displayed formula, so one declaration. (C.1) was checked against the
equation image. -/
theorem eqC_1 {Ω : Set ℂ} (hΩ : IsOpen Ω) {u v : ℂ → ℝ} (hu : IsPiecewiseSmooth Ω u) (hv : IsPiecewiseSmooth Ω v)
    (hDu : dirichletIntegralGM Ω u < ⊤) (hDv : dirichletIntegralGM Ω v < ⊤) :
    dirichletIntegralGM Ω (u + v) < ⊤ ∧ dirichletIntegralGM Ω (u - v) < ⊤ ∧
      (dirichletIntegralGM Ω (u + v)).toReal =
        (dirichletIntegralGM Ω u).toReal + (dirichletIntegralGM Ω v).toReal + 2 * dirichletInner Ω u v ∧
      (dirichletIntegralGM Ω (u - v)).toReal =
        (dirichletIntegralGM Ω u).toReal + (dirichletIntegralGM Ω v).toReal - 2 * dirichletInner Ω u v := by
  sorry

/-- **Formula (C.4)** (App. C, P3:2818–2834; cited in the proof of Lemma C.1, P3:2870, 2908, "(C.4) implies that
`D(u − u_N) → 0`"). If `f ∈ C(∂𝔻)` has Fourier series (C.3) `f(e^{iθ}) ~ Σ_{−∞}^{+∞} a_n e^{inθ}`, then its Poisson
integral `u` satisfies (C.4) `D(u) = 2π Σ_{−∞}^{+∞} |n| |a_n|²`.
Modelling: `f` is real (the Dirichlet integral is defined for real functions) and continuous on the circle; `u` is
Ch. I §1's `poissonIntegral`; `a_n = (1/2π) ∫₀^{2π} f(e^{iθ}) e^{−inθ} dθ` is Mathlib's `fourierCoeffOn` on `[0, 2π]`;
the series is summed in `[0, ∞]`, since both sides may be `∞`, as in the book's example. (C.3) and (C.4) were checked
against the equation images. -/
theorem eqC_4 {f : ℂ → ℝ} (hf : ContinuousOn f (sphere 0 1)) :
    dirichletIntegralGM unitDisc (poissonIntegral f) =
      ENNReal.ofReal (2 * π) * ∑' n : ℤ,
        ENNReal.ofReal (|(n : ℝ)| * ‖fourierCoeffOn Real.two_pi_pos (fun θ => (f (circleMap 0 1 θ) : ℂ)) n‖ ^ 2) := by
  sorry

/-- **Lemma C.1** (App. C; cited at P3:2916, in the proof of Lemma C.2, P3:2940, 2946, 2983, and on the Jordan domain
`W` in the proof of Theorem C.3, P3:3089). Let `f` be piecewise continuous on `∂𝔻` and let `u` be the Poisson integral
of `f`. Let `E ⊂ ∂𝔻` be the finite set of discontinuities of `f`, and set `𝒟_f = {v : v bounded and piecewise smooth
on 𝔻, lim_{z→ζ} v(z) = f(ζ) for all ζ ∈ ∂𝔻 \ E}`. If `𝒟_f ∩ {v : D(v) < ∞} ≠ ∅`, then `D(u) < ∞`, and `u` is the unique
element of `𝒟_f` of minimal Dirichlet norm. That is, `D(u) = inf {D(v) : v ∈ 𝒟_f}`, and if `v ∈ 𝒟_f` satisfies
`D(v) = D(u)`, then `v = u`.
Modelling: `f` is a real function on `ℂ` read on the circle, piecewise continuous in the sense of Ch. II §1 at the
domain `𝔻` (the `exists` bullet); `E` is the set of points of `∂𝔻` at which `f`, as a function on `∂𝔻`, is not
continuous; "bounded on `𝔻`" is a bound on `𝔻`; "the unique element of `𝒟_f` of minimal Dirichlet norm" includes
`u ∈ 𝒟_f`, which is stated, and is stated as two claims (the infimum, and every `v ∈ 𝒟_f` with `D(v) = D(u)` equals
`u` on `𝔻`). The hypothesis is printed "I f 𝒟_f ∩ …" inside a formula (P3:2862), read "If" [OCR]. -/
theorem lemmaC_1 {f : ℂ → ℝ} (hf : IsPiecewiseContinuousOn (toExt unitDisc) fun w => w.elim 0 f) {E : Set ℂ}
    (hE : E = {ζ ∈ sphere (0 : ℂ) 1 | ¬ ContinuousWithinAt f (sphere 0 1) ζ}) {𝒟 : Set (ℂ → ℝ)}
    (h𝒟 : 𝒟 = {v | (∃ C : ℝ, ∀ z ∈ unitDisc, |v z| ≤ C) ∧ IsPiecewiseSmooth unitDisc v ∧
      ∀ ζ ∈ sphere (0 : ℂ) 1 \ E, Tendsto v (𝓝[unitDisc] ζ) (𝓝 (f ζ))})
    {u : ℂ → ℝ} (hu : u = poissonIntegral f) (hfin : ∃ v ∈ 𝒟, dirichletIntegralGM unitDisc v < ⊤) :
    u ∈ 𝒟 ∧ dirichletIntegralGM unitDisc u < ⊤ ∧
      dirichletIntegralGM unitDisc u = ⨅ v ∈ 𝒟, dirichletIntegralGM unitDisc v ∧
      ∀ v ∈ 𝒟, dirichletIntegralGM unitDisc v = dirichletIntegralGM unitDisc u → EqOn v u unitDisc := by
  sorry

/-- **Unlabelled** (App. C, P3:2908–2914; formula (C.6) of the proof of Lemma C.1, cited in the proof of Theorem C.3,
P3:3089, "and in fact by (C.6)"). In the setting of Lemma C.1, (C.6) `D(v) = D(u) + D(v − u)` whenever `v ∈ 𝒟_f` and
`D(v) < ∞`.
Modelling: the data of `lemmaC_1`; the identity is in `[0, ∞]` (both sides are finite). The printed disc form is
stated; the proof of Theorem C.3 applies it on a Jordan domain `W` inside a proof, which is not a reason for a Jordan
form (leader ruling Fa11). (C.6) was checked against the equation image. -/
theorem eqC_6 {f : ℂ → ℝ} (hf : IsPiecewiseContinuousOn (toExt unitDisc) fun w => w.elim 0 f) {E : Set ℂ}
    (hE : E = {ζ ∈ sphere (0 : ℂ) 1 | ¬ ContinuousWithinAt f (sphere 0 1) ζ}) {𝒟 : Set (ℂ → ℝ)}
    (h𝒟 : 𝒟 = {v | (∃ C : ℝ, ∀ z ∈ unitDisc, |v z| ≤ C) ∧ IsPiecewiseSmooth unitDisc v ∧
      ∀ ζ ∈ sphere (0 : ℂ) 1 \ E, Tendsto v (𝓝[unitDisc] ζ) (𝓝 (f ζ))})
    {u : ℂ → ℝ} (hu : u = poissonIntegral f) {v : ℂ → ℝ} (hv : v ∈ 𝒟)
    (hDv : dirichletIntegralGM unitDisc v < ⊤) :
    dirichletIntegralGM unitDisc v = dirichletIntegralGM unitDisc u + dirichletIntegralGM unitDisc (v - u) := by
  sorry

/-- **Unlabelled** (App. C, P3:2916, "the Dirichlet integral is a conformal invariant"; used as a result in the proofs
of Lemma C.2, P3:2934, "Because Dirichlet integrals are conformally invariant", Theorem C.3, P3:3019, Corollary C.4,
P3:3157, "By conformal invariance", and in App. H, P3:4752). If `φ` maps `Ω` conformally onto `Ω'` and `v` is
piecewise smooth on `Ω'`, then `D_Ω(v ∘ φ) = D_{Ω'}(v)`.
Modelling: plane conformal maps are the project's `LiZhongQC.IsConformalOnto` (holomorphic and one-to-one on `Ω`,
with image `Ω'`); `Ω` is open (the book's domain). The identity also holds without piecewise smoothness, because the
junk value of the derivative is transported consistently by a biholomorphism; the book's setting is kept. B-cand.
`LiZhongQC.dmq_dirichletIntegral_eq` concerns the project's real-valued integral and differentiable functions: a
different integral. -/
theorem dirichletIntegralGM_comp_conformal {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ Ω Ω') {v : ℂ → ℝ} (hv : IsPiecewiseSmooth Ω' v) :
    dirichletIntegralGM Ω (v ∘ φ) = dirichletIntegralGM Ω' v := by
  sorry

/-- **Unlabelled** (App. C, P3:2916; cited in the proof of Theorem C.3, P3:3089, "By Lemma C.1, `D_W(v_n) ≤
D_W(u_n)`", on the Jordan domain `W = Ω ∩ B(ζ, δ)`). Because the Dirichlet integral is a conformal invariant, Lemma C.1
also holds with any simply connected Jordan domain `Ω` in place of `𝔻`: for `f` piecewise continuous on `∂Ω` with
finite set `E` of discontinuities, the solution `u = u_f` of the Dirichlet problem for `f` (the Poisson integral of
`f` transplanted to `Ω`) is the unique element of minimal Dirichlet norm of the class `𝒟_f` of bounded piecewise smooth
functions `v` on `Ω` with `lim_{z→ζ} v(z) = f(ζ)` for all `ζ ∈ ∂Ω \ E`, provided `𝒟_f ∩ {v : D(v) < ∞} ≠ ∅`.
Modelling: `Ω` is a bounded plane Jordan domain (`LiZhongQC.IsJordanDomain`, bounded: leader ruling Fa1; the use at
P3:3089 is bounded, and on an unbounded domain the plane function `f` would miss the boundary point `∞`); `f` is a
real function on `ℂ` read on `∂Ω`, piecewise continuous in the sense of Ch. II §1; "the Poisson integral of `f`" is
Ch. II §1's `dirichletSolution` (the bounded harmonic `u_f` of Theorem II.1.1, which is the transplanted Poisson
integral); the conclusion is that of `lemmaC_1` with `Ω` for `𝔻`. -/
theorem lemmaC_1_jordan {Ω : Set ℂ} (hΩ : LiZhongQC.IsJordanDomain Ω) (hΩb : Bornology.IsBounded Ω) {f : ℂ → ℝ}
    (hf : IsPiecewiseContinuousOn (toExt Ω) fun w => w.elim 0 f) {E : Set ℂ}
    (hE : E = {ζ ∈ frontier Ω | ¬ ContinuousWithinAt f (frontier Ω) ζ}) {𝒟 : Set (ℂ → ℝ)}
    (h𝒟 : 𝒟 = {v | (∃ C : ℝ, ∀ z ∈ Ω, |v z| ≤ C) ∧ IsPiecewiseSmooth Ω v ∧
      ∀ ζ ∈ frontier Ω \ E, Tendsto v (𝓝[Ω] ζ) (𝓝 (f ζ))})
    {u : ℂ → ℝ} (hu : u = fun z : ℂ => dirichletSolution (toExt Ω) (fun w => w.elim 0 f) z)
    (hfin : ∃ v ∈ 𝒟, dirichletIntegralGM Ω v < ⊤) :
    u ∈ 𝒟 ∧ dirichletIntegralGM Ω u < ⊤ ∧ dirichletIntegralGM Ω u = ⨅ v ∈ 𝒟, dirichletIntegralGM Ω v ∧
      ∀ v ∈ 𝒟, dirichletIntegralGM Ω v = dirichletIntegralGM Ω u → EqOn v u Ω := by
  sorry

/-- **Lemma C.2** (App. C; cited in the proof of Theorem C.3, P3:3127, printed "Lemma (C.2)" [OCR]). Let `I` be an open
arc on `∂𝔻`, and let `f` be a bounded continuous function on `I`. Set `𝒞_f = {v : v is piecewise smooth on 𝔻 and
lim_{z→ζ} v(z) = f(ζ) for all ζ ∈ I}`. If `𝒞_f ∩ {v : D(v) < ∞} ≠ ∅`, then `𝒞_f` contains a unique element `u(z)` of
minimal Dirichlet norm and `u(z)` solves the mixed boundary value problem (C.7): `Δu = 0` on `𝔻`, `u = f` on `I`,
`∂u/∂r = 0` on `∂𝔻 \ Ī`.
Modelling: `I = openArc a b` with `a < b ≤ a + 2π` (Ch. I §1); `f` is a real function on `ℂ` read on `I`; "`u = f` on
`I`" is the membership `u ∈ 𝒞_f` (limits at the points of `I`); `∂u/∂r` is the outer normal derivative on `∂𝔻`
(`HasOuterNormalDeriv`, the radial derivative); the minimality and the uniqueness are two claims (every minimizer in
`𝒞_f` equals `u` on `𝔻`). (C.7) prints "`Δu = 0`, on `Ω`" (checked against the equation image): `Ω` is undefined in
the lemma, which is set on `𝔻`, so it is read "on `𝔻`" [misprint] (root Corrections list). The "If" before the
hypothesis is lost in the OCR [OCR]. -/
theorem lemmaC_2 {a b : ℝ} (hab : a < b) (hb : b ≤ a + 2 * π) {f : ℂ → ℝ} (hfc : ContinuousOn f (openArc a b))
    (hfb : ∃ C : ℝ, ∀ ζ ∈ openArc a b, |f ζ| ≤ C) {𝒞 : Set (ℂ → ℝ)}
    (h𝒞 : 𝒞 = {v | IsPiecewiseSmooth unitDisc v ∧ ∀ ζ ∈ openArc a b, Tendsto v (𝓝[unitDisc] ζ) (𝓝 (f ζ))})
    (hfin : ∃ v ∈ 𝒞, dirichletIntegralGM unitDisc v < ⊤) :
    ∃ u ∈ 𝒞, (∀ v ∈ 𝒞, dirichletIntegralGM unitDisc u ≤ dirichletIntegralGM unitDisc v) ∧
      (∀ w ∈ 𝒞, (∀ v ∈ 𝒞, dirichletIntegralGM unitDisc w ≤ dirichletIntegralGM unitDisc v) → EqOn w u unitDisc) ∧
      HarmonicOnNhd u unitDisc ∧
      ∀ ζ ∈ sphere (0 : ℂ) 1 \ closure (openArc a b),
        HasOuterNormalDeriv (toExt unitDisc) (fun w => w.elim 0 u) ζ 0 := by
  sorry

/-- A closed arc of class `C^{k+α}` (helper, App. C, Theorem C.3, P3:3013, "`∂Ω \ E` consists of `C^{1+α}` arcs"; the
arc version of Ch. II §4's `IsCurveOfClass`, P1:2820–2826): `A` is a Jordan arc `γ([0, ℓ])` of length `ℓ > 0` in its
arc length parametrization `γ` (the length of `γ` on `[s₁, s₂]` is `s₂ − s₁`), and `γ` is in `C^{k+α}` on `[0, ℓ]`
(one-sided derivatives at the ends).
Modelling: `α` has no upper bound here, as in `MemCkAlphaOn` (the theorem says only `α > 0`). -/
def IsArcOfClass (k : ℕ) (α : ℝ) (A : Set ℂ) : Prop :=
  ∃ (ℓ : ℝ) (γ : ℝ → ℂ), 0 < ℓ ∧ InjOn γ (Icc 0 ℓ) ∧ γ '' Icc 0 ℓ = A ∧
    (∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ ℓ → eVariationOn γ (Icc s₁ s₂) = ENNReal.ofReal (s₂ - s₁)) ∧
    MemCkAlphaOn k α γ (Icc 0 ℓ)

/-- **Theorem C.3** (App. C; cited in the first proof of Corollary C.4, P3:3157, 3159), the extremal problem. Let `Ω`
be a finitely connected Jordan domain, let `E` be a nonempty finite union of open arcs on `∂Ω` and let `f ∈ C(Ē)`.
Set `𝒞_f = {v : v is piecewise smooth on Ω, lim_{z→ζ} v(z) = f(ζ) for all ζ ∈ E}` and assume
`𝒞_f ∩ {v : D(v) < ∞} ≠ ∅`. Then the extremal problem (C.8) `D(u) = inf {D(v) : v ∈ 𝒞_f}` has unique solution `u`, and
`u` satisfies `Δu = 0` on `Ω` and `u = f` on `Ē`.
Modelling: `Ω` is a bounded plane finitely connected Jordan domain (leader ruling Fa1); `E` is `IsFiniteUnionOf` of
open Jordan arcs contained in `∂Ω` (at least one, so `E` is nonempty); `f` is a real function on `ℂ` read on `Ē`; the
unique solution is stated as two claims (a minimizer `u ∈ 𝒞_f`, and every minimizer in `𝒞_f` equals `u` on `Ω`);
"`u = f` on `Ē`" is read with limits at every point of `Ē`, the endpoints of the arcs of `E` included [reading]. (C.8)
was checked against the equation image. -/
theorem thmC_3_a {Ω : Set ℂ} (hΩ : IsFCJordanDomain (toExt Ω)) (hΩb : Bornology.IsBounded Ω) {E : Set ℂ}
    (hE : IsFiniteUnionOf (fun s => LehtoVirtanen1973.IsOpenJordanArc (toExt s) ∧ s ⊆ frontier Ω) E) {f : ℂ → ℝ}
    (hf : ContinuousOn f (closure E)) {𝒞 : Set (ℂ → ℝ)}
    (h𝒞 : 𝒞 = {v | IsPiecewiseSmooth Ω v ∧ ∀ ζ ∈ E, Tendsto v (𝓝[Ω] ζ) (𝓝 (f ζ))})
    (hfin : ∃ v ∈ 𝒞, dirichletIntegralGM Ω v < ⊤) :
    ∃ u ∈ 𝒞, (∀ v ∈ 𝒞, dirichletIntegralGM Ω u ≤ dirichletIntegralGM Ω v) ∧
      (∀ w ∈ 𝒞, (∀ v ∈ 𝒞, dirichletIntegralGM Ω w ≤ dirichletIntegralGM Ω v) → EqOn w u Ω) ∧
      HarmonicOnNhd u Ω ∧ ∀ ζ ∈ closure E, Tendsto u (𝓝[Ω] ζ) (𝓝 (f ζ)) := by
  sorry

/-- **Theorem C.3** (App. C), the free boundary condition (C.9). In the situation of `thmC_3_a`: moreover, if for some
`α > 0`, `∂Ω \ E` consists of `C^{1+α}` arcs, then (C.9) `∂u/∂n = 0` on `∂Ω \ Ē`.
Modelling: stated for every minimizer `u ∈ 𝒞_f` (by `thmC_3_a` there is exactly one, up to its values off `Ω`); the
hypothesis `𝒞_f ∩ {v : D(v) < ∞} ≠ ∅` is kept (without it every element of `𝒞_f` would be a minimizer, all with
`D = ∞`). "`∂Ω \ E` consists of `C^{1+α}` arcs" is read component by component [reading], at the points of `∂Ω \ Ē` (a
common endpoint of two arcs of `E` is a one-point component of `∂Ω \ E`, which is no arc; it lies in `Ē`, where
(C.9) asserts nothing): each connected component of
`∂Ω \ E` is a closed arc of class `C^{1+α}` (`IsArcOfClass 1 α`) or, when a boundary curve does not meet `E`, a whole
Jordan curve of class `C^{1+α}` (`IsCurveOfClass 1 α`; the book's proof treats the arcs, and the condition (C.9) is
local). The reading "`∂Ω \ E` is a union of finitely many `C^{1+α}` arcs" would make the statement false: for the unit
square `Ω = (0, 1)²`, `E` its open bottom side and `f = 0`, `∂Ω \ E` is the union of the other three closed sides, the
minimizer is `u = 0`, and at the corners `i` and `1 + i` of `∂Ω \ Ē` there is no outer normal, so `∂u/∂n = 0` fails
there. `∂u/∂n` is `HasOuterNormalDeriv`. (C.9) was checked against the equation image. -/
theorem thmC_3_b {Ω : Set ℂ} (hΩ : IsFCJordanDomain (toExt Ω)) (hΩb : Bornology.IsBounded Ω) {E : Set ℂ}
    (hE : IsFiniteUnionOf (fun s => LehtoVirtanen1973.IsOpenJordanArc (toExt s) ∧ s ⊆ frontier Ω) E) {f : ℂ → ℝ}
    (hf : ContinuousOn f (closure E)) {𝒞 : Set (ℂ → ℝ)}
    (h𝒞 : 𝒞 = {v | IsPiecewiseSmooth Ω v ∧ ∀ ζ ∈ E, Tendsto v (𝓝[Ω] ζ) (𝓝 (f ζ))})
    (hfin : ∃ v ∈ 𝒞, dirichletIntegralGM Ω v < ⊤) {α : ℝ} (hα : 0 < α)
    (hfree : ∀ ζ ∈ frontier Ω \ closure E, IsArcOfClass 1 α (connectedComponentIn (frontier Ω \ E) ζ) ∨
      IsCurveOfClass 1 α (connectedComponentIn (frontier Ω \ E) ζ))
    {u : ℂ → ℝ} (hu : u ∈ 𝒞) (hmin : ∀ v ∈ 𝒞, dirichletIntegralGM Ω u ≤ dirichletIntegralGM Ω v) :
    ∀ ζ ∈ frontier Ω \ closure E, HasOuterNormalDeriv (toExt Ω) (fun w => w.elim 0 u) ζ 0 := by
  sorry

/-- **Corollary C.4** (App. C; cited in App. H, P3:4612, "Theorem H.1 also implies Corollary C.4 of Appendix C"), the
extremal problem. Let `Ω` be a finitely connected Jordan domain, and let `E` and `F` be finite unions of open arcs on
`∂Ω` such that `Ē ∩ F̄ = ∅`. Then the extremal problem (C.12) `inf {D_Ω(v) : v piecewise smooth on Ω,
limsup_{z→ζ∈E} v(z) ≤ 0, liminf_{z→ζ∈F} v(z) ≥ 1}` has a unique solution, which satisfies (C.13) `Δu(z) = 0` on `Ω`
and (C.14) `u = 0` on `E` and `u = 1` on `F`.
Modelling: `Ω` is a bounded plane finitely connected Jordan domain (leader ruling Fa1); `E` and `F` are as `E` in
Theorem C.3, so both are nonempty [reading]: with `E = ∅` every constant `c ≥ 1` lies in the class (C.12) with
`D = 0`, and the solution is not unique (root Corrections list); `limsup ≤ 0` and `liminf ≥ 1` are in `ε`-form; the
unique solution is stated as two claims; (C.14) is read as limits at the points of `E` and of `F`. (C.12)–(C.14) were
checked against the equation images. The second proof in the book cites "Exercise H.5(a)" for `0 ≤ u ≤ 1`, a
misdirected reference [misprint?] (Exercise H.5 has no part (a) and concerns Theorem H.9; the bound is the maximum
principle). -/
theorem corC_4_a {Ω : Set ℂ} (hΩ : IsFCJordanDomain (toExt Ω)) (hΩb : Bornology.IsBounded Ω) {E F : Set ℂ}
    (hE : IsFiniteUnionOf (fun s => LehtoVirtanen1973.IsOpenJordanArc (toExt s) ∧ s ⊆ frontier Ω) E)
    (hF : IsFiniteUnionOf (fun s => LehtoVirtanen1973.IsOpenJordanArc (toExt s) ∧ s ⊆ frontier Ω) F)
    (hEF : Disjoint (closure E) (closure F)) {𝒞 : Set (ℂ → ℝ)}
    (h𝒞 : 𝒞 = {v | IsPiecewiseSmooth Ω v ∧ (∀ ζ ∈ E, ∀ ε > 0, ∀ᶠ z in 𝓝[Ω] ζ, v z ≤ ε) ∧
      ∀ ζ ∈ F, ∀ ε > 0, ∀ᶠ z in 𝓝[Ω] ζ, 1 - ε ≤ v z}) :
    ∃ u ∈ 𝒞, (∀ v ∈ 𝒞, dirichletIntegralGM Ω u ≤ dirichletIntegralGM Ω v) ∧
      (∀ w ∈ 𝒞, (∀ v ∈ 𝒞, dirichletIntegralGM Ω w ≤ dirichletIntegralGM Ω v) → EqOn w u Ω) ∧
      HarmonicOnNhd u Ω ∧ (∀ ζ ∈ E, Tendsto u (𝓝[Ω] ζ) (𝓝 0)) ∧ ∀ ζ ∈ F, Tendsto u (𝓝[Ω] ζ) (𝓝 1) := by
  sorry

/-- **Corollary C.4** (App. C), the free boundary condition (C.15). In the situation of `corC_4_a`: if `∂Ω` consists
of `C^{1+α}` curves, then (C.15) `∂u/∂n = 0` on `∂Ω \ (E ∪ F)‾`.
Modelling: "`∂Ω` consists of `C^{1+α}` curves" is Ch. III §1's `IsSmoothFCDomain` of the domain `Ω ⊆ ℂ*`; stated for
every minimizer `u` of the class (C.12) (by `corC_4_a` there is exactly one, up to its values off `Ω`; the class
always contains functions with `D < ∞`, e.g. a smooth function equal to `0` near `Ē` and to `1` near `F̄`, so the
minimum is finite); `∂u/∂n` is `HasOuterNormalDeriv`. (C.15) was checked against the equation image. -/
theorem corC_4_b {Ω : Set ℂ} (hΩ : IsFCJordanDomain (toExt Ω)) (hΩb : Bornology.IsBounded Ω) {E F : Set ℂ}
    (hE : IsFiniteUnionOf (fun s => LehtoVirtanen1973.IsOpenJordanArc (toExt s) ∧ s ⊆ frontier Ω) E)
    (hF : IsFiniteUnionOf (fun s => LehtoVirtanen1973.IsOpenJordanArc (toExt s) ∧ s ⊆ frontier Ω) F)
    (hEF : Disjoint (closure E) (closure F)) {𝒞 : Set (ℂ → ℝ)}
    (h𝒞 : 𝒞 = {v | IsPiecewiseSmooth Ω v ∧ (∀ ζ ∈ E, ∀ ε > 0, ∀ᶠ z in 𝓝[Ω] ζ, v z ≤ ε) ∧
      ∀ ζ ∈ F, ∀ ε > 0, ∀ᶠ z in 𝓝[Ω] ζ, 1 - ε ≤ v z})
    (hsm : IsSmoothFCDomain (toExt Ω)) {u : ℂ → ℝ} (hu : u ∈ 𝒞)
    (hmin : ∀ v ∈ 𝒞, dirichletIntegralGM Ω u ≤ dirichletIntegralGM Ω v) :
    ∀ ζ ∈ frontier Ω \ closure (E ∪ F), HasOuterNormalDeriv (toExt Ω) (fun w => w.elim 0 u) ζ 0 := by
  sorry

end GarnettMarshall2005
