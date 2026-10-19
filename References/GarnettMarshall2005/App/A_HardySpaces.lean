import References.GarnettMarshall2005.Ch01.S02_FatouMaximalFunctions

/-!
# Garnett–Marshall, Appendix A: Hardy spaces

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Appendix A (pp. 435–440;
`full.md` P3:2257–2534).

Conventions as in Ch. I §1–§2, whose notions this appendix uses (`poissonIntegral`, `arcMeasure`, the cones
`LiZhongQC.stolzAngle`, `HasNontangentialLimit`, `ntMaximal`, `hlMaximal`): `𝔻` is `LiZhongQC.unitDisc`, `∂𝔻` is
`Metric.sphere 0 1`, a function "on `∂𝔻`" is a function on `ℂ` read on the circle, `dθ` is `arcMeasure` (total mass
`2π`), `‖f‖_p` is `eLpNorm f p arcMeasure`, and "almost everywhere `dθ`" is `arcMeasure`-almost everywhere. The
Hardy norm is the book's (A.1), with respect to `dθ` and without a factor `1/2π`, like `‖f‖_p`. The book writes
`f(e^{iθ})` both for the analytic function on the circle and for its nontangential boundary function; here the
boundary function is a separate function `fstar` with `∀ᵐ ζ ∂arcMeasure, HasNontangentialLimit f ζ (fstar ζ)` (it
is determined almost everywhere). The book uses the disc Poisson kernel `P_z(θ)` in this appendix both with the
factor `1/2π` of I.1 (P1:419; so at P3:2270) and without it (P3:2294, P3:2330, where `dθ/2π` follows): the factor
is written explicitly around Mathlib's `poissonKernel`, and each docstring says which form it follows.

Two labels are misprinted [misprint] (text-layer spans of the source, not OCR output): the theorem printed
"Theorem A.4" (P3:2275) is Theorem A.1 (every internal reference, P3:2289–2377, and VI.1, P2:753, say Theorem
A.1), and the corollary printed "Corollary A.5" (P3:2307) is Corollary A.2 (cited so in VI.1, P2:771 and
P2:801).

* Definition ((A.1), the Hardy space `Hᵖ` for `0 < p < ∞` and its norm `‖f‖_{Hᵖ}`; the space `H^∞` of bounded
  analytic functions with `‖f‖_∞ = sup_𝔻 |f|`; App. A, P3:2259–2265) — `MemHardy`, `hardyNorm`
* Unlabelled (App. A, P3:2267–2273): `‖f_r‖_p` is an increasing function of `r` whenever `0 < p ≤ ∞` —
  `lpNorm_dilate_mono`
* Theorem A.1 (App. A; printed as Theorem A.4 [misprint]): part (a) with (A.2), part (b) with (A.3) — `thmA_1_a`,
  `thmA_1_b`
* Unlabelled (App. A, P3:2291–2301): the Poisson representation `f(z) = ∫ P_z(θ) f(e^{iθ}) dθ/2π` and
  `‖f‖^p_{Hᵖ} = ‖f‖^p_{Lᵖ(∂𝔻)}` for `f ∈ Hᵖ`, `1 ≤ p < ∞` — `thmA_1_poisson`
* Unlabelled (App. A, P3:2303): Theorem A.1 also holds for `f ∈ Hᵖ`, `0 < p < 1` (proof left to Exercise A.1;
  used, uncited, in X.1, P2:7253, and App. M, P3:6151, for `0 < p < ∞`) — `thmA_1_a_of_lt_one`,
  `thmA_1_b_of_lt_one`
* Corollary A.2 (App. A; printed as Corollary A.5 [misprint]) — `corA_2`
* Theorem A.3 (the Hardy–Littlewood maximal theorem for `Hᵖ` functions, App. A): (A.4) — `thmA_3` (corrected,
  false as printed: with p-th roots the constant cannot be uniform in p as p tends to 0; the p-th-power form, with
  one constant for all p, is stated)
* Formula (A.5) (App. A, P3:2350) — omitted: a step of the proof of Theorem A.1(a) (the Poisson integral of the
  singular part of the weak-star limit has nontangential limit 0 almost everywhere)
* Formula (A.6) (App. A, P3:2395–2398, stated in the proof of Theorem A.1(b)) — `eqA_6`
* Unlabelled (App. A; the Poisson form of (A.6) at any `z ∈ 𝔻`, cited in VII.2, P2:2295, "by Theorem A.1") —
  `eqA_6_poisson`
* Formula (A.7) (App. A, P3:2406) — omitted: a step of the proof of Theorem A.3 (Lemma I.2.2 applied to the boundary
  function)
* Formula (A.8), the Hardy–Littlewood maximal theorem (named, App. A, P3:2409–2415) — `hardy_littlewood_maximal`
* Formulas (A.9)–(A.11) and the distribution function `m(λ)` of `Mf` (App. A, P3:2419–2480) — omitted: steps of the
  proof of Theorem A.3 and a notion used only there (the Symbol Index lists m(λ) on p. 438, this page)

Not stated (inventory U−, proof steps and remarks): the subharmonicity estimate
`|f_r(z)|^p ≤ ∫₀^{2π} P_{(r/s)z}(θ) |f_s(e^{iθ})|^p dθ` (P3:2270, the book's reason for `lpNorm_dilate_mono`);
`f(z) = lim_{r→1} f(rz)` (P3:2294, continuity); the remark that the case `p > 1` of Theorem A.1(a) follows from
Exercise I.11 (P3:2289); the attributions (P3:2305); the bounds on the constants inside the proof of Theorem A.3
(`A_α ≤ 2√6(1 + 2α)` for `p ≥ 2`, P3:2461; the Marcinkiewicz constants `2(3p/(p − 1))^{1/p}` for `1 < p < 2`,
P3:2463). Exercises A.1–A.4 are not items (Exercise A.4 is cited by VIII, P2:5403).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (unitDisc)

/-- **Definition** (the norm of the Hardy space `Hᵖ`, (A.1), App. A, P3:2259–2265). For `0 < p < ∞` and `f`
analytic on `𝔻`, `‖f‖_{Hᵖ} = (sup_{0<r<1} ∫₀^{2π} |f(re^{iθ})|^p dθ)^{1/p}`, so that `‖f‖^p_{Hᵖ}` is the
supremum in (A.1); for `p = ∞` it is the norm `‖f‖_∞ = sup_{z∈𝔻} |f(z)|` of `H^∞`. Values in `[0, ∞]`.
Modelling: the book's normalization, with respect to `dθ` and without the factor `1/2π`, like `‖f‖_p` (the
inequality (A.4) and the identity `‖f‖_{Hᵖ} = ‖f‖_{Lᵖ(∂𝔻)}` compare the two norms); `re^{iθ}` is `circleMap 0 r θ`;
only the values of `f` on `𝔻` enter. Junk: for `p = 0`, outside the book's range `0 < p ≤ ∞`, the value is `1`;
never used there. -/
def hardyNorm (p : ℝ≥0∞) (f : ℂ → ℂ) : ℝ≥0∞ :=
  if p = ∞ then ⨆ z ∈ unitDisc, ‖f z‖ₑ
  else (⨆ r ∈ Ioo (0 : ℝ) 1, ∫⁻ θ in Ioc 0 (2 * π), ‖f (circleMap 0 r θ)‖ₑ ^ p.toReal) ^ (1 / p.toReal)

/-- **Definition** (the Hardy space `Hᵖ`, `0 < p ≤ ∞`, (A.1), App. A, P3:2259–2265). For `0 < p < ∞`, an analytic
function `f` on `𝔻` is in `Hᵖ` if `sup_{0<r<1} ∫ |f(re^{iθ})|^p dθ = ‖f‖^p_{Hᵖ} < ∞`; `H^∞` is the space of bounded
analytic functions on `𝔻`. In both cases: `f` is analytic on `𝔻` and `hardyNorm p f < ∞`.
Modelling: "analytic on `𝔻`" is `DifferentiableOn ℂ f unitDisc` (`𝔻` is open); only the values of `f` on `𝔻`
enter. Junk: for `p = 0`, outside the book's range, every analytic function; every statement assumes `0 < p`. -/
def MemHardy (p : ℝ≥0∞) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f unitDisc ∧ hardyNorm p f < ∞

/-- **Unlabelled** (App. A, P3:2267–2273; cited at P3:2297, "since `‖f_r‖_p` is increasing in `r`", and used in
VIII.4, P2:4415, "the means `∫ |φ′(re^{iθ})|^{2−p} dθ` are increasing in `r`"). Let `f` be analytic on `𝔻` and
write `f_r(z) = f(rz)`. Then `‖f_r‖_p` is an increasing function of `r ∈ (0, 1)` whenever `0 < p ≤ ∞`.
Modelling: `‖f_r‖_p` is the norm of `f_r` in `Lᵖ(∂𝔻)`, `eLpNorm f_r p arcMeasure`, as the claim is used at P3:2297
(for `p < ∞` it is `(∫₀^{2π} |f(re^{iθ})|^p dθ)^{1/p}`); for `p = ∞` it is `max_{|z|=r} |f(z)|`, which is the
book's `‖f_r‖_∞ = sup_𝔻 |f_r|` by the maximum principle. `f` is any analytic function on `𝔻` (the book's argument
uses only the subharmonicity of `|f|^p`, and VIII.4 applies the claim to a power of `φ′`, not to an `Hᵖ` function);
`r` is real. -/
theorem lpNorm_dilate_mono {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) {p : ℝ≥0∞} (hp : 0 < p) :
    MonotoneOn (fun r : ℝ => eLpNorm (fun ζ => f ((r : ℂ) * ζ)) p arcMeasure) (Ioo 0 1) := by
  sorry

/-- **Theorem A.1** (App. A; printed "Theorem A.4" [misprint]), part (a), due to F. and M. Riesz. Assume `1 ≤ p < ∞`
and let `f ∈ Hᵖ`. Then the function `f(z)` has a nontangential limit `f(e^{iθ})` almost everywhere `dθ` and (A.2)
`lim_{r→1} ∫₀^{2π} |f(re^{iθ}) − f(e^{iθ})|^p dθ = 0` (cited in VI.1, P2:753, with `p = 1` and `f = φ′`).
Modelling: the boundary function is `fstar`; `r → 1` from below; the integral is a lower Lebesgue integral with
values in `[0, ∞]`, which needs no integrability hypothesis and respects almost-everywhere equality. (A.2) was
checked against the equation image. -/
theorem thmA_1_a {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ℂ → ℂ} (hf : MemHardy p f) :
    ∃ fstar : ℂ → ℂ, (∀ᵐ ζ ∂arcMeasure, HasNontangentialLimit f ζ (fstar ζ)) ∧
      Tendsto (fun r : ℝ => ∫⁻ θ in Ioc 0 (2 * π), ‖f (circleMap 0 r θ) - fstar (circleMap 0 1 θ)‖ₑ ^ p.toReal)
        (𝓝[<] 1) (𝓝 0) := by
  sorry

/-- **Theorem A.1** (App. A; printed "Theorem A.4" [misprint]), part (b), due to F. Riesz. Assume `1 ≤ p < ∞`, let
`f ∈ Hᵖ`, and let `f(e^{iθ})` be its nontangential boundary function (part (a)). If `f ≢ 0`, then (A.3)
`∫ log |f(e^{iθ})| dθ > −∞`.
Modelling: `f ≢ 0` is `f z ≠ 0` for some `z ∈ 𝔻`; `fstar` is any function that is almost everywhere the
nontangential limit of `f`. The integral in (A.3) takes values in `[−∞, ∞)` (its positive part is finite, since
`log⁺ x ≤ x^p/p` and `f(e^{iθ}) ∈ Lᵖ`), and (A.3) says that it is finite: `f(e^{iθ}) ≠ 0` almost everywhere and
`log |f(e^{iθ})|` is integrable. Both are stated, so that neither `Real.log 0 = 0` nor the value `0` of the integral
of a non-integrable function enters. [OCR] The lead-in of (b) is garbled ("H f f ≠ 0", P3:2283); read "If `f ≢ 0`",
as in Corollary A.2. (A.3) was checked against the equation image. -/
theorem thmA_1_b {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ℂ → ℂ} (hf : MemHardy p f) {fstar : ℂ → ℂ}
    (hfstar : ∀ᵐ ζ ∂arcMeasure, HasNontangentialLimit f ζ (fstar ζ)) (hf0 : ∃ z ∈ unitDisc, f z ≠ 0) :
    (∀ᵐ ζ ∂arcMeasure, fstar ζ ≠ 0) ∧ Integrable (fun ζ => Real.log ‖fstar ζ‖) arcMeasure := by
  sorry

/-- **Unlabelled** (App. A, P3:2303, "Theorem A.1 is also true for `f ∈ Hᵖ` for all `p < 1`. See Exercise A.1";
used, uncited, in X.1, P2:7253, and App. M, P3:6151, where `Hᵖ` of a domain is taken for `0 < p < ∞`), part (a).
Assume `0 < p < 1` and let `f ∈ Hᵖ`. Then the function `f(z)` has a nontangential limit `f(e^{iθ})` almost
everywhere `dθ` and (A.2) `lim_{r→1} ∫₀^{2π} |f(re^{iθ}) − f(e^{iθ})|^p dθ = 0`.
Modelling: as in `thmA_1_a` (the boundary function is `fstar`; the lower Lebesgue integral in `[0, ∞]`); the book
leaves the proof to Exercise A.1. -/
theorem thmA_1_a_of_lt_one {p : ℝ≥0∞} (hp₀ : 0 < p) (hp₁ : p < 1) {f : ℂ → ℂ} (hf : MemHardy p f) :
    ∃ fstar : ℂ → ℂ, (∀ᵐ ζ ∂arcMeasure, HasNontangentialLimit f ζ (fstar ζ)) ∧
      Tendsto (fun r : ℝ => ∫⁻ θ in Ioc 0 (2 * π), ‖f (circleMap 0 r θ) - fstar (circleMap 0 1 θ)‖ₑ ^ p.toReal)
        (𝓝[<] 1) (𝓝 0) := by
  sorry

/-- **Unlabelled** (App. A, P3:2303; used, uncited, in X.1, P2:7253, and App. M, P3:6151), part (b). Assume
`0 < p < 1`, let `f ∈ Hᵖ`, and let `f(e^{iθ})` be its nontangential boundary function. If `f ≢ 0`, then (A.3)
`∫ log |f(e^{iθ})| dθ > −∞`.
Modelling: as in `thmA_1_b`: `f ≢ 0` is `f z ≠ 0` for some `z ∈ 𝔻`, and (A.3) is stated as `f(e^{iθ}) ≠ 0` almost
everywhere together with the integrability of `log |f(e^{iθ})|` (the positive part is finite, since
`log⁺ x ≤ x^p/p` and `f(e^{iθ}) ∈ Lᵖ`), so that no junk value enters. -/
theorem thmA_1_b_of_lt_one {p : ℝ≥0∞} (hp₀ : 0 < p) (hp₁ : p < 1) {f : ℂ → ℂ} (hf : MemHardy p f)
    {fstar : ℂ → ℂ} (hfstar : ∀ᵐ ζ ∂arcMeasure, HasNontangentialLimit f ζ (fstar ζ))
    (hf0 : ∃ z ∈ unitDisc, f z ≠ 0) :
    (∀ᵐ ζ ∂arcMeasure, fstar ζ ≠ 0) ∧ Integrable (fun ζ => Real.log ‖fstar ζ‖) arcMeasure := by
  sorry

/-- **Unlabelled** (App. A, P3:2291–2301; used in App. M, P3:6162, "the Poisson formula holds for `F`", with
`p = 1`). Assume `1 ≤ p < ∞`, let `f ∈ Hᵖ`, and let `f(e^{iθ})` be its nontangential boundary function. From part
(a) of Theorem A.1, `f(z) = lim_{r→1} f(rz) = ∫ P_z(θ) f(e^{iθ}) dθ/2π`, and since `‖f_r‖_p` is increasing in `r`,
`‖f‖^p_{Hᵖ} = ‖f‖^p_{Lᵖ(∂𝔻)}` for all `f ∈ Hᵖ`.
Modelling: in this display `P_z(θ)` is the kernel without the factor `1/2π` (the display carries `dθ/2π`), i.e.
Mathlib's `poissonKernel 0 z (e^{iθ})`, so the right side is the Poisson integral `poissonIntegral fstar z` of I.1;
`‖f‖_{Lᵖ(∂𝔻)}` is `eLpNorm fstar p arcMeasure`. `fstar ∈ Lᵖ(∂𝔻)` is stated with the two identities (the book's
proof obtains the boundary function as a weak limit in `Lᵖ`), so that the Poisson integral is that of an integrable
function. The first equality `f(z) = lim_{r→1} f(rz)` is continuity and is not stated. Both displays were checked
against the equation images. -/
theorem thmA_1_poisson {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ℂ → ℂ} (hf : MemHardy p f) {fstar : ℂ → ℂ}
    (hfstar : ∀ᵐ ζ ∂arcMeasure, HasNontangentialLimit f ζ (fstar ζ)) :
    MemLp fstar p arcMeasure ∧ (∀ z ∈ unitDisc, f z = poissonIntegral fstar z) ∧
      hardyNorm p f ^ p.toReal = eLpNorm fstar p arcMeasure ^ p.toReal := by
  sorry

/-- **Corollary A.2** (App. A; printed "Corollary A.5" [misprint]; cited in VI.1, P2:771 and P2:801). If `f ∈ H¹` and
`f ≢ 0`, then `|f(e^{iθ})| > 0` almost everywhere.
Modelling: `f(e^{iθ})` is the nontangential boundary function `fstar` of Theorem A.1(a); `f ≢ 0` is `f z ≠ 0` for
some `z ∈ 𝔻`. -/
theorem corA_2 {f : ℂ → ℂ} (hf : MemHardy 1 f) (hf0 : ∃ z ∈ unitDisc, f z ≠ 0) {fstar : ℂ → ℂ}
    (hfstar : ∀ᵐ ζ ∂arcMeasure, HasNontangentialLimit f ζ (fstar ζ)) :
    ∀ᵐ ζ ∂arcMeasure, 0 < ‖fstar ζ‖ := by
  sorry

/-- **Theorem A.3** (App. A; "called Hardy–Littlewood maximal theorem for `Hᵖ` functions", P3:2309), corrected. Let
`α > 1` be fixed, let `0 < p ≤ ∞`, and let `f ∈ Hᵖ`. Then the nontangential maximal function
`f*_α(ζ) = sup_{Γ_α(ζ)} |f(z)|` satisfies (A.4) `‖f*_α‖_p ≤ A_α ‖f‖_{Hᵖ}`, where the constant `A_α` depends only on
`α`. Stated in the p-th-power form `∫ (f*_α)^p dθ ≤ A_α ‖f‖^p_{Hᵖ}` for `0 < p < ∞` (and `‖f*_α‖_∞ ≤ A_α ‖f‖_{H^∞}`),
with one constant `A_α` for all `p`.
[CORRECTION] As printed (p-th roots, `A_α` independent of `p ∈ (0, ∞]`), the theorem is false: for `f(z) = e^{Nz}`
every cone `Γ_α(ζ)` contains the disc `|z| < ρ`, `ρ = (α − 1)/(α + 1)`, so `f*_α ≥ e^{Nρ}` on `∂𝔻`, while
`‖f‖^p_{Hᵖ} = 2π I₀(pN) ≤ 2π e^{p²N²/4}`; the factors `(2π)^{1/p}` cancel, and with `p = 2ρ/N` the quotient
`‖f*_α‖_p / ‖f‖_{Hᵖ}` is at least `e^{Nρ/2}`: the best constant is at least `e^{ρ²/p}`, unbounded as `p → 0`. The
book's proof (Case II, P3:2465–2495, printed for `0 < p ≤ 2`, whose argument works verbatim for every `p`; its
display `‖f*_α‖_p ≤ ‖g*_α‖_2^{2/p}` checked against the equation image) gives `∫ (f*_α)^p dθ ≤ A_2² ‖f‖^p_{Hᵖ}`,
i.e. the constant `A_2^{2/p}` in (A.4); "the same bound on
`A_α` as for the case `p = 2`" (P3:2495) holds for the p-th-power form, which is stated (it holds with
`A_α = 24(1 + 2α)²`). The only use of the theorem in the book (the proof of Theorem A.1(a)) needs only
`f*_α ∈ Lᵖ`. Checked independently (work/THM_A3_CHECK.md).
Modelling: `‖f*_α‖_p` is `eLpNorm (ntMaximal α f) p arcMeasure`, with respect to `dθ`, and `‖f‖_{Hᵖ}` is
`hardyNorm p f`, the book's un-normalized (A.1); for `p = ∞` both are suprema. The constant is in `ℝ≥0` (so finite).
(A.4) was checked against the equation image (no `p` on `A_α`). -/
theorem thmA_3 {α : ℝ} (hα : 1 < α) :
    ∃ A : ℝ≥0,
      (∀ p : ℝ≥0∞, 0 < p → p ≠ ∞ → ∀ f : ℂ → ℂ, MemHardy p f →
        eLpNorm (ntMaximal α f) p arcMeasure ^ p.toReal ≤ (A : ℝ≥0∞) * hardyNorm p f ^ p.toReal) ∧
      ∀ f : ℂ → ℂ, MemHardy ∞ f →
        eLpNorm (ntMaximal α f) ∞ arcMeasure ≤ (A : ℝ≥0∞) * hardyNorm ∞ f := by
  sorry

/-- **Formula (A.6)** (App. A, P3:2395–2398, "the important inequality", stated in the proof of Theorem A.1(b);
VII.2 cites its Poisson form `log |φ′(z)| ≤ ∫ P_z(e^{iθ}) log |φ′(e^{iθ})| dθ/2π` for `φ′ ∈ H¹` "by Theorem A.1",
P2:2295, and VII.4 uses (A.6) itself for `φ′` and `(φ′)^{−q}` in `H¹`, P2:2783–2791). Assume `1 ≤ p < ∞`, let
`f ∈ Hᵖ` with nontangential boundary function `f(e^{iθ})`, and suppose `f(0) ≠ 0`.
Then `log |f(0)| ≤ ∫ log |f(e^{iθ})| dθ/2π`.
Modelling: the right side is an integral with values in `[−∞, ∞)`; with the finite left side, the inequality says
that `f(e^{iθ}) ≠ 0` almost everywhere, that `log |f(e^{iθ})|` is integrable, and the inequality of real numbers.
All three are stated, so that neither `Real.log 0 = 0` nor the value `0` of the integral of a non-integrable
function enters (the first two are also (A.3), which (A.6) "implies", P3:2401). `∫ … dθ/2π` is `(2π)⁻¹` times the
integral against `arcMeasure`. (A.6) was checked against the equation image. -/
theorem eqA_6 {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ℂ → ℂ} (hf : MemHardy p f) (hf0 : f 0 ≠ 0)
    {fstar : ℂ → ℂ} (hfstar : ∀ᵐ ζ ∂arcMeasure, HasNontangentialLimit f ζ (fstar ζ)) :
    (∀ᵐ ζ ∂arcMeasure, fstar ζ ≠ 0) ∧ Integrable (fun ζ => Real.log ‖fstar ζ‖) arcMeasure ∧
      Real.log ‖f 0‖ ≤ (2 * π)⁻¹ * ∫ ζ, Real.log ‖fstar ζ‖ ∂arcMeasure := by
  sorry

/-- **Unlabelled** (App. A; the Poisson form of (A.6), cited in VII.2, P2:2295, for `φ′ ∈ H¹`, "by Theorem A.1").
Assume `1 ≤ p < ∞`, let `f ∈ Hᵖ` with nontangential boundary function `f(e^{iθ})`, `z ∈ 𝔻` and `f(z) ≠ 0`. Then
`log |f(z)| ≤ ∫ P_z(e^{iθ}) log |f(e^{iθ})| dθ/2π`.
Modelling: as in `eqA_6` (the a.e. non-vanishing and the integrability of `log |f(e^{iθ})|` are stated, so that no
junk value enters); the right side is the Poisson integral `poissonIntegral` of Ch. I §1 (the book's `dθ/2π`
normalization). At `z = 0` it is (A.6). -/
theorem eqA_6_poisson {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ℂ → ℂ} (hf : MemHardy p f) {z : ℂ}
    (hz : z ∈ unitDisc) (hfz : f z ≠ 0) {fstar : ℂ → ℂ}
    (hfstar : ∀ᵐ ζ ∂arcMeasure, HasNontangentialLimit f ζ (fstar ζ)) :
    (∀ᵐ ζ ∂arcMeasure, fstar ζ ≠ 0) ∧ Integrable (fun ζ => Real.log ‖fstar ζ‖) arcMeasure ∧
      Real.log ‖f z‖ ≤ poissonIntegral (fun ζ => Real.log ‖fstar ζ‖) z := by
  sorry

/-- **Formula (A.8)**, the Hardy–Littlewood maximal theorem (App. A, P3:2409–2415, proved P3:2419–2461; named at
P3:2415; cited in VIII.1, P2:3627, "apply the Hardy–Littlewood maximal theorem"). `‖Mf‖_p ≤ C_p ‖f‖_p` for
`1 < p ≤ ∞`; the constants `C_p` depend on `p`, but `C_p ≤ 2√6` for `p ≥ 2`.
Modelling: first conjunct `∀ p, ∃ C_p, ∀ f ∈ Lᵖ(∂𝔻)`; second conjunct the bound `2√6` for every `p ≥ 2`, `p = ∞`
included. `Mf` is `hlMaximal f` of I.2 and `‖·‖_p` is `eLpNorm · p arcMeasure`, with respect to `dθ`; `f` is
complex-valued. (A.8) was checked against the equation image; `2√6` is the value `2(3p/(p − 1))^{1/p}` of the
proof's constant at `p = 2` (P3:2458–2461). -/
theorem hardy_littlewood_maximal :
    (∀ p : ℝ≥0∞, 1 < p → ∃ C : ℝ≥0, ∀ f : ℂ → ℂ, MemLp f p arcMeasure →
      eLpNorm (hlMaximal f) p arcMeasure ≤ (C : ℝ≥0∞) * eLpNorm f p arcMeasure) ∧
    ∀ p : ℝ≥0∞, 2 ≤ p → ∀ f : ℂ → ℂ, MemLp f p arcMeasure →
      eLpNorm (hlMaximal f) p arcMeasure ≤ ENNReal.ofReal (2 * Real.sqrt 6) * eLpNorm f p arcMeasure := by
  sorry

end GarnettMarshall2005
