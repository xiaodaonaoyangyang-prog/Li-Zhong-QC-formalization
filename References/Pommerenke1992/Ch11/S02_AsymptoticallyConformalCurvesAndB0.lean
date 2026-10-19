import References.Pommerenke1992.Ch11.S01_Overview

/-!
# Pommerenke 1992, Ch. 11 §11.2 Asymptotically Conformal Curves and `B₀`

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 11 *Local Boundary Behaviour*, §11.2; source
`full.md` of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3…` (P2), lines 2740–2954.

* Definition (asymptotically conformal curve, (11.2.1), "is called"; used in Theorem 11.1 (i), (11.2.5), Theorem
  11.2, at P2 l. 2871, 3011 and in Exercises 11.2.1–11.2.2; forward reference at P1 l. 7375) —
  `IsAsymptoticallyConformalCurve`
* Unlabelled (§11.2, P2 l. 2748: "It follows from (5.4.1) that every asymptotically conformal curve is a
  quasicircle"; used in the proof of Theorem 11.1 (i) ⇒ (ii), P2 l. 2804) —
  `isQuasicircle_of_isAsymptoticallyConformalCurve`
* Theorem 11.1 (Pom78; (iv), (v): BePo78, compare AgGe65; cited at P2 l. 2863, 3011, 3013; its method at P2 l. 3027
  and 2463) — `thm11_1`
* Definition (`B₀`, recalled at P2 l. 2857: "Let again `B₀` be the space of all Bloch functions `g` with
  `(1 - |z|²)g'(z) → 0` as `|z| → 1`") — exists: `Pommerenke1992.IsLittleBloch` (Ch. 4, (4.2.22): the Bloch
  functions g with (1 - |z|²)|g'(z)| → 0 as |z| → 1-, the same condition)
* Formula (11.2.5) (cited "(5)" at P2 l. 2875; used at P2 l. 2871) — `eq11_2_5`
* Theorem 11.2 (Makarov, Mak89d; cited at P2 l. 2875) — `thm11_2`
* Formula (11.2.7) (Mak89d; cited "(7)" at P2 l. 2883; forward reference at P2 l. 263) — `eq11_2_7`

Not items (DESIGN §3): "note that the quotient is constant on ellipses with foci `a` and `b`", "Every smooth curve is
asymptotically conformal but corners are not allowed" and the references to analytic characterizations (Pom78) and
quantitative estimates (PoWa82, RoWa84, Bec87) (P2 l. 2748–2750; remarks, not cited; P1 l. 7375 only asserts that
asymptotically smooth curves are asymptotically conformal, itself U− there); "If `z ∈ 𝔻` and `a > 1` then
`{ζ ∈ 𝔻̄ : |z - ζ| ≤ a(1 - |z|)}` contains a proper arc of `𝕋`" (P2 l. 2764; a remark, not cited); the proof of
Theorem 11.1 (P2 l. 2774–2855; its displays (1)–(4) are partly lost under the library slip of p. 247, see §11.1; the
integration in (ii) ⇒ (iii) is reused only as a method, P2 l. 3027 and 2463); the Example (11.2.6), `log f'(z) =
Σ b_k z^{2^k}` with `|b_k| < 1/3`, `b_k → 0` (an example; its claims are cited only in the remark at P2 l. 3011); "It
is furthermore best possible" (P2 l. 2881; not cited); the transference principle (CaCuPo88) and its relation to
(10.4.12) (quoted, not cited); inner functions ("`g(𝔻) ⊆ 𝔻` and `|g(ζ)| = 1` for almost all `ζ ∈ 𝕋`", used only in
the quoted result that follows and in Exercise 11.2.4) and the theorem `dim {ζ ∈ 𝕋 : g(ζ) = w} = 1` for inner
`g ∈ B₀` (Roh89, compare Hun88; quoted, not cited); (11.2.8) (a restatement of (7.2.1), Part C's `blochIntegral`),
"Zygmund-smooth" (defined inline and used only in the quoted results), "as in Theorem 7.2, `h` is Zygmund-smooth if and
only if `g ∈ B₀`" (Zyg45), Makarov's differentiability theorems (Mak89d, Mak89e) and the nowhere differentiable
complex Zygmund-smooth function (P2 l. 2897–2917; quoted, not cited); (11.2.9), (11.2.10), (11.2.11) (Jon89; Bla84,
Bea91; "compare Corollary 8.11 and (8.6.22)") and Roh91 (P2 l. 2919–2939; quoted, not cited); Exercises 11.2.1–11.2.4.

**Conventions.** As in §11.1. A Jordan curve `J ⊆ ℂ` is `IsJordanCurve (toExt J)`; for `a ≠ b` in `J` the two arcs
of `J` between `a` and `b` are the closures of the two components of `J ∖ {a, b}`, as in the project's bounded
turning and in `IsQuasicircle` (§5.1). The inner domain is `innerDomain J` (Ch. 1), and `f(ζ)` for `ζ ∈ 𝕋` is the
continuous extension `F` of `f` to `𝔻̄`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane toExt unitDisc IsConformalOnto IsJordanCurve)

/-- **Definition (11.2.1)** (§11.2, "is called"; P2 l. 2742–2748; used in Theorem 11.1 (i), (11.2.5), Theorem 11.2
and at P2 l. 2871, 3011). The Jordan curve `J ⊆ ℂ` is asymptotically conformal if
`max_{w ∈ J(a, b)} (|a - w| + |w - b|)/|a - b| → 1` as `a, b ∈ J`, `|a - b| → 0`, where `J(a, b)` is the smaller arc
of `J` between `a` and `b`.
[misprint?] The crop prints `|a, b| → 0`; read `|a - b| → 0`, as in the §11.1 display (P2 l. 2694) and in Exercise
11.2.2 (P2 l. 2948), which restates (1) with `|a - b| → 0`.
Modelling: `J ⊆ ℂ` with `IsJordanCurve (toExt J)`; for `a ≠ b` the condition is asked for one of the two arcs of `J`
between `a` and `b` (the ∃-arc form of the project's bounded turning, `LiZhongQC.IsBoundedTurning`, and of
`IsQuasicircle`, §5.1). This is the book's smaller-arc form: an arc on which the quotient is `≤ 1 + ε` lies in the
closed ellipse with foci `a`, `b` and major axis `(1 + ε)|a - b|`, so its diameter is `≤ (1 + ε)|a - b|`, while the
two arcs together have diameter `≥ diam J`; for `|a - b| < diam J/(2(1 + ε))` it is therefore the arc of smaller
diameter, and `δ` may be shrunk. The maximum over the closed arc equals the supremum over the open one (the quotient is
`1` at `a` and `b`), and since the quotient is always `≥ 1`, "`→ 1`" is "eventually `≤ 1 + ε`".
The name differs from `AstalaGehring1990.IsAsymptoticallyConformal` (the leader's ruling QD5): that is a different
notion, a quasiarc `g([0, ∞])` with `g` quasiconformal in `ℂ̄` and `K`-quasiconformal near `[0, ∞]` for every
`K > 1`; the two agree on Jordan curves of `ℂ` only by a theorem. -/
def IsAsymptoticallyConformalCurve (J : Set ℂ) : Prop :=
  IsJordanCurve (toExt J) ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ a ∈ J, ∀ b ∈ J, a ≠ b → ‖a - b‖ < δ →
    ∃ p ∈ J \ {a, b}, ∀ w ∈ connectedComponentIn (J \ {a, b}) p, ‖a - w‖ + ‖w - b‖ ≤ (1 + ε) * ‖a - b‖

/-- **Unlabelled claim** (§11.2, P2 l. 2748; used in the proof of Theorem 11.1 (i) ⇒ (ii), P2 l. 2804: "Now `f(𝔻)` is
a quasidisk and thus a John domain"). It follows from (5.4.1) that every asymptotically conformal curve is a
quasicircle.
Modelling: `IsQuasicircle` is the bounded-turning definition (5.4.1) of §5.1. -/
theorem isQuasicircle_of_isAsymptoticallyConformalCurve {J : Set ℂ} (hJ : IsAsymptoticallyConformalCurve J) :
    IsQuasicircle J := by
  sorry

/-- **Theorem 11.1** (§11.2; Pom78; (iv), (v): BePo78, compare AgGe65; P2 l. 2752–2772; cited at P2 l. 2863, 3011 and
3013). Let `f` map `𝔻` conformally onto the inner domain of the Jordan curve `J`. Then the following conditions are
equivalent:
(i) `J` is asymptotically conformal;
(ii) `(1 - |z|²) f''(z)/f'(z) → 0` as `|z| → 1-`;
(iii) `(f(z) - f(ζ))/((z - ζ) f'(z)) → 1` as `|z| → 1-`, `ζ ∈ 𝔻̄`, `|z - ζ|/(1 - |z|) ≤ a` (`a > 0`);
(iv) `(1 - |z|²)² S_f(z) → 0` as `|z| → 1-`;
(v) `f` has a quasiconformal extension to `ℂ` such that `(∂f/∂z̄)/(∂f/∂z) → 0` as `|z| → 1+`.
[CORRECTION] In (iii) the case `ζ = z` is excluded. It satisfies `ζ ∈ 𝔻̄` and `|z - ζ|/(1 - |z|) = 0 ≤ a`, and there
the quotient is `0/0`; with Lean's `x/0 = 0` its value is `0`, so the literal (iii) fails for every `f`, for instance
for `f = id`, `J = 𝕋`, where (i) holds. "`(a > 0)`" (crop ✓) is read "for every `a > 0`", the limit being uniform in
`ζ`: the proof of (ii) ⇒ (iii) takes `a` arbitrary (with `b = (a + 2)²`), and the proof of (iii) ⇒ (i) uses `a = 2`
(`|ζ_j - z| = 2(1 - |z|)`).
Modelling: `f(ζ)` for `ζ ∈ 𝔻̄` is the continuous extension `F` (on `𝔻` it is `f`). The quotients are genuine:
`f' ≠ 0` in `𝔻`, and in (iii) `z ≠ ζ`. `S_f` is `LiZhongQC.schwarzian`. In (v) the extension `h` (`h = f` on `𝔻`) is a
`κ`-quasiconformal map of `ℂ` onto `ℂ` with the data of `IsKappaQC` (§5.1), whose Beltrami coefficient `μ` is exposed:
`μ = h_z̄/h_z` almost everywhere (`h_z ≠ 0` a.e. for a quasiconformal map), both being defined only almost everywhere,
so the limit "as `|z| → 1+`" is the essential one (§11.1). -/
theorem thm11_1 {J : Set ℂ} (hJ : IsJordanCurve (toExt J)) {f F : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (innerDomain J)) (hFc : ContinuousOn F (closedBall 0 1))
    (hFf : EqOn F f unitDisc) :
    List.TFAE [IsAsymptoticallyConformalCurve J,
      ∀ ε > (0 : ℝ), ∃ r < (1 : ℝ), ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 →
        (1 - ‖z‖ ^ 2) * ‖deriv (deriv f) z / deriv f z‖ < ε,
      ∀ a > (0 : ℝ), ∀ ε > (0 : ℝ), ∃ r < (1 : ℝ), ∀ z ζ : ℂ, r < ‖z‖ → ‖z‖ < 1 → ‖ζ‖ ≤ 1 → ζ ≠ z →
        ‖z - ζ‖ / (1 - ‖z‖) ≤ a → ‖(f z - F ζ) / ((z - ζ) * deriv f z) - 1‖ < ε,
      ∀ ε > (0 : ℝ), ∃ r < (1 : ℝ), ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 →
        (1 - ‖z‖ ^ 2) ^ 2 * ‖LiZhongQC.schwarzian f z‖ < ε,
      ∃ h : ℂ → ℂ, EqOn h f unitDisc ∧ ∃ κ : ℝ, 0 ≤ κ ∧ κ < 1 ∧ h '' univ = univ ∧
        ∃ μ : ℂ → ℂ, LiZhongQC.IsBeltramiCoeff μ univ κ ∧ LiZhongQC.IsGenHomeoSolution h μ univ 2 ∧
          ∀ ε > (0 : ℝ), ∃ r > (1 : ℝ), ∀ᵐ z : ℂ, 1 < ‖z‖ → ‖z‖ < r → ‖μ z‖ < ε] := by
  sorry

/-- **Formula (11.2.5)** (§11.2; P2 l. 2857–2863; cited "(5)" at P2 l. 2875 and used at P2 l. 2871). Let `f` map `𝔻`
conformally onto the inner domain of the Jordan curve `J`. Then `J` is asymptotically conformal if and only if
`log f' ∈ B₀` ("by Theorem 11.1").
Modelling: `log f'` is any branch `L` (§11.1); `B₀` is `IsLittleBloch` (Ch. 4, (4.2.22)), whose condition
`(1 - |z|²)|L'(z)| → 0` is condition (ii) of Theorem 11.1, since `L' = f''/f'`. Stated as a U+ item: a numbered display
outside a proof, cited by number (the `eq6_6_5` precedent). -/
theorem eq11_2_5 {J : Set ℂ} (hJ : IsJordanCurve (toExt J)) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (innerDomain J)) {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L unitDisc)
    (hLf : ∀ z ∈ unitDisc, exp (L z) = deriv f z) :
    IsAsymptoticallyConformalCurve J ↔ IsLittleBloch L := by
  sorry

/-- **Theorem 11.2** (§11.2; Makarov, Mak89d; P2 l. 2873; cited at P2 l. 2875). Let `f` map `𝔻` conformally onto the
inner domain of an asymptotically conformal curve. Then `f` is conformal on a set of Hausdorff dimension one.
Modelling: the set `{ζ ∈ 𝕋 : f is conformal at ζ}` (`IsConformalAtBoundary`, §4.3) has Hausdorff dimension `1`
(`dimH`); this is "conformal on a set of dimension one", since subsets of `𝕋` have dimension at most `1` and `dimH` is
monotone. -/
theorem thm11_2 {J : Set ℂ} (hJ : IsAsymptoticallyConformalCurve J) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (innerDomain J)) :
    dimH {ζ ∈ sphere (0 : ℂ) 1 | IsConformalAtBoundary f ζ} = 1 := by
  sorry

/-- **Formula (11.2.7)** (§11.2; Mak89d; P2 l. 2875–2881; cited "(7)" at P2 l. 2883; forward reference at P2 l. 263).
For `g ∈ B₀`, `dim {ζ ∈ 𝕋 : g has a finite angular limit at ζ} = 1`.
Modelling: stated as a U+ item: a numbered display stated as a result outside a proof ("This result of Makarov is, by
(5), equivalent to the assertion that (7) … for `g ∈ B₀`"), in its general form for `g ∈ B₀`, which `thm11_2` alone
does not give formally. `dim` is `dimH`; the finite angular limit is `HasAngularLimit` (§1.2) with a value in `ℂ`. -/
theorem eq11_2_7 {g : ℂ → ℂ} (hg : IsLittleBloch g) :
    dimH {ζ ∈ sphere (0 : ℂ) 1 | ∃ w : ℂ, HasAngularLimit (fun z => (g z : ExtPlane)) ζ w} = 1 := by
  sorry

end Pommerenke1992
