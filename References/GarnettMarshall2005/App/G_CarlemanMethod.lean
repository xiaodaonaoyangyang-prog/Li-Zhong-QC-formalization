import References.GarnettMarshall2005.Ch03.S05_WienerSolution

/-!
# Garnett–Marshall, Appendix G: Carleman's method

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Appendix G (pp. 480–484;
`full.md` P3:4374–4563: the main text to P3:4558, the Notes at P3:4560–4562).

Conventions. `Ω ⊂ ℂ` is a plane domain (open and connected). For real `x`, `Ω_x = Ω ∩ {Re z = x}` is written
inline as `Ω ∩ {z | z.re = x}`, `|Ω_x|` is its length `μH[1] (Ω ∩ {z | z.re = x})` (leader ruling C2: length is
one-dimensional Hausdorff measure), `E_b = ∂Ω ∩ {Re z ≥ b}` is the plane set `{ζ ∈ frontier Ω | b ≤ ζ.re}` (`∞`
has no real part; when `Ω` is unbounded, `∞ ∈ ∂Ω` in `ℂ*` is a polar point and carries no harmonic measure), and
`ℓ(x)`, the length of the longest interval in `Ω_x`, is `longestIntervalLength Ω x`, in `[0, ∞]`. `B(z₀, r₀)` is
`Metric.ball z₀ r₀` with `r₀ > 0`, and `x₀ = Re z₀`. In Theorem G.1, (G.9) and (G.10) `ω(z₀, E_b, Ω)` is Wiener's
harmonic measure `harmonicMeasureWiener (toExt Ω) z₀` of Ch. III §5 at `toExt E_b` (leader ruling Fa10: `Ω` is an
arbitrary plane domain), compared in `[0, ∞]`; `Cap(ℂ* \ Ω) > 0` holds automatically under `|Ω_x| ≤ M < ∞` (every
vertical line meets `ℂ \ Ω` in a set of infinite length) and is not added. In Lemma G.2, stated in the context of
the proof of Theorem G.1 (leader ruling C10), `ω` is the finitely connected stage `harmonicMeasureFC` of Ch. II §1,
since that proof reduces to a bounded finitely connected Jordan domain with analytic boundary curves (leader rulings
D1, B5, Fa10). The right sides of (G.1), (G.9) and (G.10) are written in `[0, ∞]`: `∫_{x₀}^t dx/ℓ(x)` is the lower
integral `∫⁻ x in Ioo x₀ t, (ℓ x)⁻¹` (`0⁻¹ = ∞`; a lower integral needs no measurability), `exp{…}` is `EReal.exp`
(`exp(+∞) = ∞`, `exp(−∞) = 0`) of a real multiple of that integral, and `(…)^{−1/2}` is the `ℝ≥0∞` power, so the
values `ℓ(x) = 0` and `∫ dx/ℓ = ∞` never reach a junk value.

* Definition (`ℓ(x)`, the length of the longest interval in `Ω_x = Ω ∩ {Re z = x}`, App. G, P3:4378) —
  `longestIntervalLength`
* Theorem G.1 (Carleman, App. G; (G.1)) — `thmG_1`
* Formula (G.2), Wirtinger's inequality (named, quoted without proof, App. G, P3:4386–4392) — `eqG_2`
* Lemma G.2 (Carleman's differential inequality, App. G, in the proof of Theorem G.1; (G.3)) — `lemmaG_2`
* Formula (G.9) (App. G, P3:4534–4546) — `eqG_9`
* Formula (G.10) (App. G, P3:4546–4556) — `eqG_10`

Readings (leader ruling Fa12): (G.9) is stated for `0 < ε ≤ b − x₀` [reading]; (G.10) carries `0 < b` [reading]
(see its docstring). The displayed step before (G.10) needs `x₀ ≤ (1 − δ)b`, but (G.10) itself holds without it
(a proof-step note in its docstring, not a correction).

Not stated (inventory U−, remarks and proof steps): the introduction (P3:4376: removing finitely many horizontal slits
from a rectangle leaves the right side of (IV.6.3) unchanged but lowers `ω(z₀, E)`; "This defect in Theorem IV.6.1
is circumvented in Carleman's [1933] version of the theorem"); the remarks that `ℓ(x)` is measurable because it is
lower semicontinuous and that the main improvement of (G.1) over (IV.6.3) is the replacement of `θ(x)` by the smaller
`ℓ(x)` (P3:4384; the lower integrals need no measurability); the remarks that (G.2) is proved by examining the
Fourier series of `g` and that Lemma III.3.2 is very similar (P3:4392); the reductions at the start of the proof of
Theorem G.1 (`Ω` bounded, `∂Ω` finitely many analytic Jordan curves, `inf {Re z : z ∈ Ω} = 0`, P3:4394–4400: the
context of Lemma G.2, made explicit there); the rest of the proof of Theorem G.1 (the formula for `A′`, Green's
theorem (G.4), the Cauchy–Schwarz step, `φ(x) = ∫_{Ω_x} ω² dy`, Harnack's inequality and (G.5), `φ′ = 2A`, `μ(x)`,
`ψ(x)`, (G.6), (G.7), (G.8) and the square root, P3:4408–4532; (G.8) prints `9φ(z₀)/r₀` for `9φ(x₀)/r₀`
[misprint], checked against the equation image); the comparison display before (G.9) (P3:4534–4538) and the display
`∫_{x₀}^b exp{−2π∫_t^b dx/ℓ(x)} dt ≥ δ(1 − e^{−b})` before (G.10) (P3:4546–4550), the derivations of (G.9) and
(G.10) (both checked against the equation images); the remark that for `ℓ(x) = θ(x)` inequality (G.9) is weaker
than (IV.6.3) (P3:4546); the remark "Of course, either (G.9) or (G.10) is enough to give Theorem V.1.1" (P3:4558,
recorded with Theorem V.1.1). The Notes (P3:4560–4562: Tsuji [1959] proved (G.9) in polar coordinates; Carleman
[1933], Haliste [1965]) are not items. Citations into this appendix from other chapters: Ch. IV, P1:6478 ("sharper
versions of (6.3) are available. See Appendix G", `thmG_1`); the Notes of Ch. IV (P1:6500) and Ch. V (P2:419,
"Carleman's proof is in Appendix G"); Ch. III, Exercise 15 (P1:5523) and App. H, Exercise H.2 (P3:4913), both
exercises, which cite Theorem G.1, (G.1) and the comments after its proof (`thmG_1`, `eqG_9`, `eqG_10`).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt)

/-- **Definition** (`ℓ(x)`, the length of the longest interval in `Ω_x = Ω ∩ {Re z = x}`, App. G, P3:4378, printed
"let (x) denote the length ofthe longest interval" [OCR: `ℓ` lost]; used in Theorem G.1, Lemma G.2, (G.9), (G.10)
and in App. H, Exercise H.2). Let `ℓ(x)` denote the length of the longest interval in `Ω_x`.
Modelling: for an open `Ω`, `Ω_x` is an open subset of the vertical line `Re z = x`, and its intervals are its
connected components (`connectedComponentIn`); the length is `μH[1]` (leader ruling C2), which on a segment is its
euclidean length. The value is the supremum, in `[0, ∞]`, of the lengths of the components; it is attained when
`|Ω_x| < ∞` (only finitely many components are longer than any `ε > 0`). For `Ω_x = ∅` the supremum is empty and
the value is `0`, which is used as such: every statement reads `ℓ` through `(ℓ x)⁻¹` in `[0, ∞]` (`0⁻¹ = ∞`), and
for a connected `Ω` with `Ω_x = ∅` all of `Ω` lies on one side of the line `Re z = x`. -/
def longestIntervalLength (Ω : Set ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ z ∈ Ω ∩ {w : ℂ | w.re = x}, μH[1] (connectedComponentIn (Ω ∩ {w : ℂ | w.re = x}) z)

/-- **Theorem G.1** (Carleman; App. G, P3:4378–4382; cited at P3:4384, 4394, 4514 and 4532–4558, in Ch. IV, P1:6478,
"sharper versions of (6.3) are available. See Appendix G", in Ch. III, Exercise 15, P1:5523, and in App. H,
Exercise H.2, P3:4913). Let `Ω ⊂ ℂ` be a domain, let `Ω_x = Ω ∩ {Re z = x}` and let `E_b = ∂Ω ∩ {Re z ≥ b}`.
Suppose `|Ω_x| ≤ M < ∞`, and let `ℓ(x)` denote the length of the longest interval in `Ω_x`. Assume
`z₀ = x₀ + iy₀` and `B(z₀, r₀) ⊂ Ω`. Then for `b > x₀`,
(G.1) `ω(z₀, E_b, Ω) ≤ ((2πr₀/(9M²)) ∫_{x₀}^b exp{2π ∫_{x₀}^t dx/ℓ(x)} dt)^{−1/2}`.
Modelling (leader ruling Fa10): `Ω` open and connected; `|Ω_x| ≤ M` for every real `x`, with `M` real (then
`M < ∞`); the printed hypothesis "`z₀ = x₀ + iy₀ ∈ B(z₀, r₀) ⊂ Ω`" is read "`z₀ = x₀ + iy₀` and `B(z₀, r₀) ⊂ Ω`"
with `r₀ > 0` [reading]; `x₀ = Re z₀`; `ω` is Wiener's harmonic measure of the plane domain `Ω` at the plane set
`E_b`; the integrals, `exp` and the power `−1/2` are taken in `[0, ∞]` as in the file's conventions. No junk is read:
the ball gives `|Ω_{x₀}| ≥ 2r₀`, so `M ≥ 2r₀ > 0`, and since `exp ≥ 1` the bracket is at least
`(2πr₀/(9M²))(b − x₀) > 0`; if the bracket is `∞` the bound reads `ω = 0` (for instance when `ℓ = 0` on a set of
positive length in `(x₀, b)`: then `Ω` lies to the left of a line `Re z = x` with `x < b`, and `E_b = ∅`). (G.1) was
checked against the equation image. -/
theorem thmG_1 {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) {M : ℝ}
    (hM : ∀ x : ℝ, μH[1] (Ω ∩ {z : ℂ | z.re = x}) ≤ ENNReal.ofReal M) {z₀ : ℂ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hball : ball z₀ r₀ ⊆ Ω) {b : ℝ} (hb : z₀.re < b) :
    harmonicMeasureWiener (toExt Ω) (z₀ : ExtPlane) (toExt {ζ ∈ frontier Ω | b ≤ ζ.re}) ≤
      (ENNReal.ofReal (2 * π * r₀ / (9 * M ^ 2)) *
          ∫⁻ t in Ioo z₀.re b,
            EReal.exp (2 * π * ((∫⁻ x in Ioo z₀.re t, (longestIntervalLength Ω x)⁻¹ : ℝ≥0∞) : EReal))) ^
        (-(1 / 2 : ℝ)) := by
  sorry

/-- **Formula (G.2)**, Wirtinger's inequality (App. G, P3:4386–4392, named and quoted without proof, "proved by
examining the Fourier series of `g`"; used in the proof of Lemma G.2, P3:4414). If `g` and `g′` are real valued
continuous functions on the interval `(a, b)` and if `g(a) = g(b) = 0`, then
(G.2) `∫_a^b (g′)² dx ≥ (π/(b − a))² ∫_a^b g² dx`.
Modelling: `a < b` (meaning: `(a, b)` is an interval; it also keeps `π/(b − a)` off the junk value `π/0 = 0`); `g′`
is the derivative of `g` on `(a, b)` (`HasDerivAt`), continuous there; "`g(a) = g(b) = 0`" is read with `g`
continuous on `[a, b]` [reading]: with `g` continuous only on `(a, b)` and the endpoint values prescribed separately,
`g ≡ 1` on `(a, b)` with `g(a) = g(b) = 0` would be a counterexample (`g′ = 0`). The integrals are lower integrals in
`[0, ∞]`: `∫_a^b (g′)² dx` may be infinite (then the inequality is trivial), and `∫_a^b g² dx` is finite. No
candidate: Mathlib and the project have no Wirtinger or Poincaré inequality on an interval (the project's
"Wirtinger" names concern Wirtinger derivatives). (G.2) was checked against the equation image. -/
theorem eqG_2 {a b : ℝ} (hab : a < b) {g g' : ℝ → ℝ} (hg : ContinuousOn g (Icc a b))
    (hg' : ContinuousOn g' (Ioo a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (ha : g a = 0) (hb : g b = 0) :
    ENNReal.ofReal ((π / (b - a)) ^ 2) * ∫⁻ x in Ioo a b, ENNReal.ofReal (g x ^ 2) ≤
      ∫⁻ x in Ioo a b, ENNReal.ofReal (g' x ^ 2) := by
  sorry

/-- **Lemma G.2** (Carleman's differential inequality; App. G, P3:4394–4406, inside the proof of Theorem G.1; cited
as (G.3) at P3:4470, 4488). [The context of the proof, P3:4394–4400:] suppose that `Ω` is bounded, that `∂Ω`
consists of finitely many analytic Jordan curves, and that `inf {Re z : z ∈ Ω} = 0`; write
`ω(z) = ω(z, E_b, Ω)` and define `A(t) = ∫_0^t ∫_{Ω_x} |∇ω|² dy dx`; by the smoothness assumptions on `∂Ω`, the
function `A(t)` is continuously differentiable. Then for `x ∈ (0, b)`, (G.3) `A′(x) ≥ (2π/ℓ(x)) A(x)`.
Modelling (leader rulings C10, Fa10): a labelled lemma inside a proof, stated in the proof's context made explicit:
`Ω` a bounded plane domain with `toExt Ω` a finitely connected Jordan domain whose boundary is the disjoint union of
finitely many analytic Jordan curves (Ch. II §2), and `inf Re = 0`; `b > 0` (in the proof `b > x₀ = Re z₀ > 0`);
`ω` is the harmonic measure `harmonicMeasureFC` of Ch. II §1 (the explicit finitely connected Jordan setting of the
proof), its value on `toExt E_b` as a real number (the measure is finite); `|∇ω|²` is `‖fderiv ℝ ω z‖²` (the operator
norm of the real derivative, a linear form on the euclidean `ℂ`), read only at points of the open set `Ω`, where
`ω` is harmonic; `A(t)` is the area integral of `|∇ω|²` over `Ω ∩ {Re z < t}` (Fubini, since `Ω ⊆ {Re z > 0}`); it
is finite for `t < b`, because `ω` is smooth up to `∂Ω` away from the points with `Re z = b` (the ends of `E_b`),
and its values for `t ≥ b` are not read (the conclusion concerns the open interval `(0, b)`). The proof's claim that
`A` is continuously differentiable is part of the conclusion (`ContDiffOn` on `(0, b)`), so `deriv A x` is a genuine
derivative. (G.3) is multiplied by `ℓ(x)`: `2π A(x) ≤ ℓ(x) A′(x)`, which avoids `2π/0`; `ℓ(x) < ∞` since `Ω` is
bounded, and `ℓ(x) = 0` only when `Ω_x = ∅`, where `Ω` lies to the left of the line (connectedness and
`inf Re = 0`), `E_b = ∅`, `ω ≡ 0` and both sides vanish. (G.3) was checked against the equation image. -/
theorem lemmaG_2 {Ω : Set ℂ} (hΩ : IsFCJordanDomain (toExt Ω)) (hΩb : Bornology.IsBounded Ω)
    (han : IsDisjointUnionOf IsAnalyticJordanCurve (frontier (toExt Ω))) (hinf : sInf (Complex.re '' Ω) = 0)
    {b : ℝ} (hb : 0 < b) {ω : ℂ → ℝ}
    (hω : ∀ z : ℂ, ω z = (harmonicMeasureFC (toExt Ω) (z : ExtPlane) (toExt {ζ ∈ frontier Ω | b ≤ ζ.re})).toReal)
    {A : ℝ → ℝ} (hA : ∀ t : ℝ, A t = ∫ z in Ω ∩ {z : ℂ | z.re < t}, ‖fderiv ℝ ω z‖ ^ 2) :
    ContDiffOn ℝ 1 A (Ioo 0 b) ∧
      ∀ x ∈ Ioo 0 b, 2 * π * A x ≤ (longestIntervalLength Ω x).toReal * deriv A x := by
  sorry

/-- **Formula (G.9)** (App. G, P3:4534–4546, stated after the proof of Theorem G.1; cited at P3:4546, 4558 and in the
Notes, P3:4562, "Tsuji [1959] proved (G.9) in polar coordinates"). To compare (G.1) and (IV.6.3), note that
`∫_{x₀}^b exp{2π ∫_{x₀}^t dx/ℓ(x)} dt ≥ ε exp{2π ∫_{x₀}^{b−ε} dx/ℓ(x)}`, so that
(G.9) `ω(z₀, E_b) ≤ (9M²/(2πr₀ε))^{1/2} exp{−π ∫_{x₀}^{b−ε} dx/ℓ(x)}`.
Modelling: the setting and the hypotheses of Theorem G.1 (`ω(z₀, E_b)` is `ω(z₀, E_b, Ω)`, Wiener's), and
`0 < ε ≤ b − x₀` [reading] (root Corrections list): the derivation integrates over `(b − ε, b) ⊆ (x₀, b)`; for
`ε > b − x₀` it does not apply, and the integral over the empty interval `(x₀, b − ε)` would read `0`, turning the
bound into `(9M²/(2πr₀ε))^{1/2}`, which tends to `0` as `ε → ∞`. The square root is that of a positive real number
(`M > 0` as in Theorem G.1); `exp{−π ∫}` is `EReal.exp` of `−π` times the lower integral, which is `0` when the
integral is `∞` (no junk). (G.9) and the display before it were checked against the equation images. -/
theorem eqG_9 {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) {M : ℝ}
    (hM : ∀ x : ℝ, μH[1] (Ω ∩ {z : ℂ | z.re = x}) ≤ ENNReal.ofReal M) {z₀ : ℂ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hball : ball z₀ r₀ ⊆ Ω) {b : ℝ} (hb : z₀.re < b) {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ b - z₀.re) :
    harmonicMeasureWiener (toExt Ω) (z₀ : ExtPlane) (toExt {ζ ∈ frontier Ω | b ≤ ζ.re}) ≤
      ENNReal.ofReal (Real.sqrt (9 * M ^ 2 / (2 * π * r₀ * ε))) *
        EReal.exp (-((π : EReal) * ((∫⁻ x in Ioo z₀.re (b - ε), (longestIntervalLength Ω x)⁻¹ : ℝ≥0∞) : EReal))) := by
  sorry

/-- **Formula (G.10)** (App. G, P3:4546–4556, stated after the proof of Theorem G.1; cited at P3:4558, "either (G.9) or
(G.10) is enough to give Theorem V.1.1"). If `ℓ(x) ≥ 2πδ > 0` for all `x > (1 − δ)b > 0`, then
`∫_{x₀}^b exp{−2π ∫_t^b dx/ℓ(x)} dt ≥ δ(1 − e^{−b})`, and thus (G.10)
`ω(z₀, E_b) ≤ (9M²/(2πr₀δ(1 − e^{−b})))^{1/2} exp(−π ∫_{x₀}^b dx/ℓ(x))`.
Modelling: the setting and the hypotheses of Theorem G.1; `δ > 0`, `(1 − δ)b > 0` and `ℓ(x) ≥ 2πδ` for every
`x > (1 − δ)b`, as printed; one added hypothesis, `0 < b` [reading]: with `δ > 0` and `(1 − δ)b > 0` it is equivalent to
`δ < 1`; the printed hypotheses also admit `b < 0 < (1 − δ)b` (with `δ > 1`), where `1 − e^{−b} < 0`, the printed right
side is the square root of a negative number (Lean's `Real.sqrt` would read the junk value `0`), and the interval
`((1 − δ)b, b)` of the derivation is reversed. Proof-step note (leader ruling Fa12(5)): the displayed step
`∫_{x₀}^b exp{−2π ∫_t^b dx/ℓ} dt ≥ δ(1 − e^{−b})` (checked against the equation image) needs `x₀ ≤ (1 − δ)b` (strip
`0 < Im z < 1`, `δ = 1/2π`, `b = 1`, `x₀ = 0.95`: `0.0429 < 0.1006`), but (G.10) holds without it (there the right side
is `≈ 4.56 ≥ 1`; in general, if the right side is `< 1` then `e^{−(b−x₀)/δ} < 1/18`, the integral exceeds `(17/18)δ`,
and Harnack along the whole vertical diameter of the ball improves the proof's constant `9` to `1/(6 − 8 log 2) ≈ 2.2`),
so no hypothesis on `x₀` is added. `exp(−π ∫)` is as in (G.9) (no junk). (G.10) was checked against the equation image.
-/
theorem eqG_10 {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) {M : ℝ}
    (hM : ∀ x : ℝ, μH[1] (Ω ∩ {z : ℂ | z.re = x}) ≤ ENNReal.ofReal M) {z₀ : ℂ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hball : ball z₀ r₀ ⊆ Ω) {b : ℝ} (hb : z₀.re < b) {δ : ℝ} (hδ : 0 < δ) (hδb : 0 < (1 - δ) * b)
    (hℓ : ∀ x : ℝ, (1 - δ) * b < x → ENNReal.ofReal (2 * π * δ) ≤ longestIntervalLength Ω x)
    (hb0 : 0 < b) :
    harmonicMeasureWiener (toExt Ω) (z₀ : ExtPlane) (toExt {ζ ∈ frontier Ω | b ≤ ζ.re}) ≤
      ENNReal.ofReal (Real.sqrt (9 * M ^ 2 / (2 * π * r₀ * δ * (1 - Real.exp (-b))))) *
        EReal.exp (-((π : EReal) * ((∫⁻ x in Ioo z₀.re b, (longestIntervalLength Ω x)⁻¹ : ℝ≥0∞) : EReal))) := by
  sorry

end GarnettMarshall2005
