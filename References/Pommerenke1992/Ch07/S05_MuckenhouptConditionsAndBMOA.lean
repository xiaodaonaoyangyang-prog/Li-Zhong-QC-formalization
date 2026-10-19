import References.Pommerenke1992.Ch07.S04_LavrentievDomains

/-!
# Pommerenke 1992, Ch. 7 §7.5 The Muckenhoupt Conditions and BMOA

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 7 *Smirnov and Lavrentiev Domains*, §7.5;
source `full.md` of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 7199–7404.

* Definition (the Coifman–Fefferman condition `(A∞)`, by its form (i); CoFe74, ReRy75 p. 52; used in Theorem 7.11 (3),
  (7.5.12) and the proofs of Theorem 7.11, Corollary 7.12, Proposition 7.13) — `SatisfiesAInfty`
* Theorem 7.11 (Lav36, JeKe82b; (7.5.1)–(7.5.3); cited in the proofs of Corollary 7.12 and Proposition 7.13) —
  `thm7_11`
* Definition (the Muckenhoupt condition `(A_p)`, (7.5.4), `1 < p < ∞`) — `SatisfiesAp`
* Definition (the condition `(B_q)`, (7.5.5), `q > 1`) — `SatisfiesBq`
* Unlabelled (§7.5, l. 7201–7221 and l. 7275–7279: "one of the following three equivalent conditions" (i)–(iii), and
  (iv), (v) "are equivalent to (i), (ii) and (iii)"; CoFe74, ReRy75 pp. 50, 52; cited in the proof of Corollary 7.12,
  "because (v) is equivalent to (i)", "(iv)") — `aInfty_tfae`
* Corollary 7.12 ((7.5.8), (7.5.9), printed "(8)" [OCR]; cited in Exercise 7.5.2) — `cor7_12`
* Helson–Szegö theorem (named; Gar81, pp. 149, 255; the book's form (7.5.10) for Smirnov domains) — `helson_szego`
* Definition (the space `BMO(𝕋)`, (7.5.11); used in (7.5.12) and for BMOA) — `MemBMOT`
* Formula (7.5.12) (CoFe74; Gar81, pp. 235, 258; cited in the proof of Proposition 7.13, "see (12)", "from (12)") —
  `eq7_5_12`
* Definition (the conjugate function `g*` of a real `g`, l. 7315, used in (7.5.12); not defined in the book) —
  exists: `GarnettMarshall2005.boundaryConjugate` (GM Ch. II §3, (3.1): the nontangential boundary values of the
  harmonic conjugate, vanishing at 0, of the Poisson integral of g; defined for g integrable on the circle, and junk
  only on a null set, which BMO does not see)
* Definition (the space BMOA, l. 7317; used in Proposition 7.13) — `MemBMOA`
* Proposition 7.13 — `prop7_13`

Not items (DESIGN §3): "(i) is a reversed geometric-arithmetic mean inequality, while (ii) is a strong form of
condition (iv') for John domains" (a remark); the remarks after Theorem 7.11 ("every Lavrentiev domain satisfies (1)
and (2)", which is part of `thm7_11`; "it is not possible to delete either condition", with the example (7.3.6);
"Ahlfors-regular John domain if and only if (2) and (3)", Pom82, FiLe86; quoted or example remarks, not cited);
(7.5.6) (Muc72) and (7.5.7) (Geh73, "a result of Gehring") (quoted, not cited by number; the proof of Corollary 7.12
uses (iv) and (v) of `aInfty_tfae`); "`δ` cannot be chosen independent of `f`" (Zin85) and the same for `q` (JoZi82)
(quoted); "`log f' ∈ BMOA` if `f(𝔻)` is Ahlfors-regular" (Zin84; immediate from Theorem 7.6 and Proposition 7.13,
not cited); the norm (7.5.14) and "BMOA is a Banach space" (Bae80), (7.5.15), (7.5.16) `BMOA ⊆ B`, VMOA (7.5.17)
(Sar75) with `VMOA ⊆ B₀`, the duality (7.5.18) (Fef71), (7.5.19) and asymptotically smooth curves (Pom78) (not cited
by any item); the literature remark (Zin84, Sem88, Zin89, AsZi91, BiJo92). The OCR prints the conditions of Theorem
7.11 as "(1)–(3)"; they are the displays (7.5.1)–(7.5.3).

**Conventions.** As in §7.1. A weight is a function `φ : ℂ → ℝ≥0∞` read on `𝕋` through the parameter; an arc
`I ⊆ 𝕋` is the parameter interval `Icc t₁ t₂`, `t₁ < t₂ ≤ t₁ + 2π`, with `Λ(I) = t₂ - t₁`, and a measurable `E ⊆ I`
is a measurable set of parameters in `Icc t₁ t₂` with `Λ(E) = volume E` (the book's measurable sets differ from
measurable sets of parameters by null sets, which no quantity here sees). The means of weights are `ℝ≥0∞`-averages of
lower integrals, and `ℝ≥0∞`-powers give the book's `0^{-a} = ∞`, `∞^{-a} = 0` in (7.5.4) and (7.5.9). The book's
weights are tacitly nondegenerate: `(A∞)` asks `0 < φ < ∞` almost everywhere and `log φ` integrable on every arc, so
that the geometric mean `exp((1/Λ(I)) ∫_I log φ)` is a genuine real number (for such weights this is the book's (i)
read with `exp(-∞) = 0`); the equivalences (i)–(v) are stated for measurable weights with `0 < φ < ∞` almost
everywhere and `∫_𝕋 φ < ∞`, which makes the ratios of (ii), (iii) genuine (Q7.4). `|f'|` on `𝕋` is `‖φ ζ‖ₑ` for a
boundary function `φ` of `f'`. BMO(𝕋) consists of complex functions (BMOA boundary values are complex); the averages
there are Bochner averages of functions that are integrable by hypothesis.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto)

/-- **Definition** (§7.5, l. 7201–7207; CoFe74, ReRy75 p. 52). The weight `φ ≥ 0` on `𝕋` satisfies the
Coifman–Fefferman `(A∞)` condition, by its form (i): for all arcs `I ⊆ 𝕋`,
`(1/Λ(I)) ∫_I φ(ζ) |dζ| ≤ M₁ exp((1/Λ(I)) ∫_I log φ(ζ) |dζ|)`.
Modelling: `0 < φ < ∞` almost everywhere on `𝕋` and `log φ` integrable on every arc (the nondegeneracy of the book's
weights, see the file header; the measurability of `φ` follows). These two conjuncts exclude exactly the weights that
the book's (i), read with extended-real conventions, would admit although its equivalence with (iv) fails: `φ = 0`
almost everywhere (where (i) reads `0 ≤ M₁ · 0`), and weights with `∫_I log φ = +∞` on every arc (right side `∞`;
for instance `exp(Σₙ 4⁻ⁿ/|t - rₙ|)` for an enumeration `(rₙ)` of the rationals, finite almost everywhere). The left
side is an `ℝ≥0∞`-average, the right side is a real number (the Bochner average of the integrable `log φ`); `M₁`
depends on `φ`. -/
def SatisfiesAInfty (φ : ℂ → ℝ≥0∞) : Prop :=
  (∀ᵐ t : ℝ, 0 < φ (exp (t * I)) ∧ φ (exp (t * I)) < ⊤) ∧
    (∀ t₁ t₂ : ℝ, IntervalIntegrable (fun t : ℝ => Real.log (φ (exp (t * I))).toReal) volume t₁ t₂) ∧
    ∃ M₁ : ℝ, ∀ t₁ t₂ : ℝ, t₁ < t₂ → t₂ ≤ t₁ + 2 * π →
      ⨍⁻ t in Icc t₁ t₂, φ (exp (t * I)) ∂volume ≤
        ENNReal.ofReal (M₁ * Real.exp (⨍ t in Icc t₁ t₂, Real.log (φ (exp (t * I))).toReal ∂volume))

/-- **Theorem 7.11** (§7.5; Lav36, JeKe82b; cited in the proofs of Corollary 7.12 and Proposition 7.13). Let `f` map
`𝔻` conformally onto `G`. Then `G` is a Lavrentiev domain if and only if (7.5.1) `G` is linearly connected, (7.5.2)
`G` is a Smirnov domain, (7.5.3) `|f'|` satisfies the `(A∞)` condition.
Modelling: "`G` is a Smirnov domain" is read for the given `f`, `Λ(∂G) < ∞` with the Smirnov condition (7.3.3) for
`f` (the book's definition; see §7.3): in "if" this is the book's hypothesis, and "only if", holding for every `f`,
gives `IsSmirnovDomain G`. `|f'|` on `𝕋` is `‖φ‖ₑ` for a boundary function `φ` of `f'`. -/
theorem thm7_11 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) :
    IsLavrentievDomain G ↔ IsLinearlyConnected G ∧ (μH[1] (frontier G) < ⊤ ∧ HasSmirnovCondition f) ∧
      ∃ φ : ℂ → ℂ, IsAngularBoundaryFun (deriv f) φ ∧ SatisfiesAInfty (fun ζ => ‖φ ζ‖ₑ) := by
  sorry

/-- **Definition (7.5.4)** (§7.5). For `1 < p < ∞`, the weight `φ ≥ 0` satisfies the Muckenhoupt `(A_p)` condition:
`(1/Λ(I)) ∫_I φ |dζ| ≤ M₄ ((1/Λ(I)) ∫_I φ^{-1/(p-1)} |dζ|)^{-(p-1)}` for all arcs `I ⊆ 𝕋`.
Modelling: literal, with `ℝ≥0∞`-averages and `ℝ≥0∞`-powers (`0^{-a} = ∞`, `∞^{-a} = 0`, as in the book); `M₄`
depends on `φ` and `p`. There is no measurability conjunct (here and in `SatisfiesBq`): the book's weights are
measurable, and every use supplies an almost everywhere measurable weight. -/
def SatisfiesAp (φ : ℂ → ℝ≥0∞) (p : ℝ) : Prop :=
  1 < p ∧ ∃ M₄ : ℝ, ∀ t₁ t₂ : ℝ, t₁ < t₂ → t₂ ≤ t₁ + 2 * π →
    ⨍⁻ t in Icc t₁ t₂, φ (exp (t * I)) ∂volume ≤
      ENNReal.ofReal M₄ * (⨍⁻ t in Icc t₁ t₂, φ (exp (t * I)) ^ (-(1 / (p - 1))) ∂volume) ^ (-(p - 1))

/-- **Definition (7.5.5)** (§7.5). For `q > 1`, the weight `φ ≥ 0` satisfies the `(B_q)` condition:
`((1/Λ(I)) ∫_I φ(ζ)^q |dζ|)^{1/q} ≤ (M₅/Λ(I)) ∫_I φ(ζ) |dζ|` for all arcs `I ⊆ 𝕋`.
Modelling: literal, with `ℝ≥0∞`-averages and `ℝ≥0∞`-powers; `M₅` depends on `φ` and `q`. -/
def SatisfiesBq (φ : ℂ → ℝ≥0∞) (q : ℝ) : Prop :=
  1 < q ∧ ∃ M₅ : ℝ, ∀ t₁ t₂ : ℝ, t₁ < t₂ → t₂ ≤ t₁ + 2 * π →
    (⨍⁻ t in Icc t₁ t₂, φ (exp (t * I)) ^ q ∂volume) ^ (1 / q) ≤
      ENNReal.ofReal M₅ * ⨍⁻ t in Icc t₁ t₂, φ (exp (t * I)) ∂volume

/-- **Unlabelled claim** (§7.5, l. 7201–7221 and l. 7275–7279; CoFe74, ReRy75 pp. 50, 52; cited in the proof of
Corollary 7.12). For a weight `φ` the following conditions are equivalent:
(i) the `(A∞)` condition;
(ii) there exists `α > 0` such that `∫_E φ |dζ| / ∫_I φ |dζ| ≤ M₂ Λ(E)^α/Λ(I)^α` for all arcs `I ⊆ 𝕋` and measurable
sets `E ⊆ I`;
(iii) there exists `β > 0` such that, for arcs `I ⊆ 𝕋` and measurable `E ⊆ I`,
`∫_E φ |dζ| / ∫_I φ |dζ| < β ⇒ Λ(E)/Λ(I) < 1/2`;
(iv) `φ` satisfies `(A_p)` for some `p < ∞`;
(v) `φ` satisfies `(B_q)` for some `q > 1`.
Modelling: for measurable weights with `0 < φ < ∞` almost everywhere and `∫_𝕋 φ |dζ| < ∞` (the book's weights,
Q7.4), so that `0 < ∫_I φ < ∞` for every arc and the quotients are genuine. The hypotheses are needed: `φ ≡ 0`
satisfies (iv) and (v) literally but not (i), and a weight that is finite almost everywhere but integrable on no arc
satisfies `(B_q)` as `∞ ≤ ∞` but not (i). `E` is a measurable set of parameters in
the parameter interval of `I`; the quotients are `ℝ≥0∞`-quotients; `M₂` depends on `φ`. -/
theorem aInfty_tfae {φ : ℂ → ℝ≥0∞} (hφm : AEMeasurable (fun t : ℝ => φ (exp (t * I))))
    (hφ : ∀ᵐ t : ℝ, 0 < φ (exp (t * I)) ∧ φ (exp (t * I)) < ⊤)
    (hint : ∫⁻ t in Icc 0 (2 * π), φ (exp (t * I)) < ⊤) :
    List.TFAE [SatisfiesAInfty φ,
      ∃ α : ℝ, 0 < α ∧ ∃ M₂ : ℝ, ∀ t₁ t₂ : ℝ, t₁ < t₂ → t₂ ≤ t₁ + 2 * π → ∀ E ⊆ Icc t₁ t₂, MeasurableSet E →
        (∫⁻ t in E, φ (exp (t * I))) / (∫⁻ t in Icc t₁ t₂, φ (exp (t * I))) ≤
          ENNReal.ofReal M₂ * (volume E / ENNReal.ofReal (t₂ - t₁)) ^ α,
      ∃ β : ℝ, 0 < β ∧ ∀ t₁ t₂ : ℝ, t₁ < t₂ → t₂ ≤ t₁ + 2 * π → ∀ E ⊆ Icc t₁ t₂, MeasurableSet E →
        (∫⁻ t in E, φ (exp (t * I))) / (∫⁻ t in Icc t₁ t₂, φ (exp (t * I))) < ENNReal.ofReal β →
          volume E / ENNReal.ofReal (t₂ - t₁) < 2⁻¹,
      ∃ p : ℝ, SatisfiesAp φ p,
      ∃ q : ℝ, SatisfiesBq φ q] := by
  sorry

/-- **Corollary 7.12** (§7.5; (7.5.8), (7.5.9), printed "(8)" [OCR]; cited in Exercise 7.5.2). If `f` maps `𝔻`
conformally onto a Lavrentiev domain then there are `δ > 0` and `q > 1` such that
(7.5.8) `(1/Λ(I(z))) ∫_{I(z)} |f'(ζ)|^q |dζ| ≤ M₆ |f'(z)|^q` for `z ∈ 𝔻`, and
(7.5.9) `(1/Λ(I(z))) ∫_{I(z)} |dζ|/|f'(ζ)|^δ ≤ M₇/|f'(z)|^δ` for `z ∈ 𝔻`.
Modelling: both are the condition (7.3.10), `HasArcMeanBound`, with the exponents `q` and `-δ` (`ℝ≥0∞`-powers);
`δ`, `q`, `M₆`, `M₇` depend on `f` (`∀ f, ∃ δ q`). -/
theorem cor7_12 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) (hG : IsLavrentievDomain G) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q : ℝ, 1 < q ∧ HasArcMeanBound f q ∧ HasArcMeanBound f (-δ) := by
  sorry

/-- **Helson–Szegö theorem** (§7.5, l. 7299–7303; named; Gar81, pp. 149, 255; the book's form (7.5.10)). For Smirnov
domains, `|f'|` satisfies the `(A₂)` condition if and only if
`f' = e^{g+h}` with `sup_{z∈𝔻} |Re g(z)| < ∞`, `sup_{z∈𝔻} |Im h(z)| < π/2`.
Modelling: `f` maps `𝔻` conformally onto `G`, and "Smirnov domain" is read for the given `f` (`Λ(∂G) < ∞` and the
Smirnov condition for `f`, see §7.3); `g`, `h` are analytic in `𝔻`; `sup |Im h| < π/2` is a bound `c < π/2`. -/
theorem helson_szego {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) (hΛ : μH[1] (frontier G) < ⊤)
    (hS : HasSmirnovCondition f) :
    (∃ φ : ℂ → ℂ, IsAngularBoundaryFun (deriv f) φ ∧ SatisfiesAp (fun ζ => ‖φ ζ‖ₑ) 2) ↔
      ∃ g h : ℂ → ℂ, DifferentiableOn ℂ g unitDisc ∧ DifferentiableOn ℂ h unitDisc ∧
        (∀ z ∈ unitDisc, deriv f z = exp (g z + h z)) ∧ (∃ C : ℝ, ∀ z ∈ unitDisc, |(g z).re| ≤ C) ∧
        ∃ c : ℝ, c < π / 2 ∧ ∀ z ∈ unitDisc, |(h z).im| ≤ c := by
  sorry

/-- **Definition (7.5.11)** (§7.5; used in (7.5.12) and for BMOA). `BMO(𝕋)` is the space of all integrable
functions `g` on `𝕋` such that `sup_I (1/Λ(I)) ∫_I |g(ζ) - a_I| |dζ| < ∞`, `a_I = (1/Λ(I)) ∫_I g(ζ) |dζ|`, where the
supremum is taken over all arcs `I ⊆ 𝕋`.
Modelling: `g : ℂ → ℂ` read on `𝕋`, integrable over a period (hence over every arc); the supremum is finite when there
is a common bound `C`; the averages are Bochner averages of integrable functions. -/
def MemBMOT (g : ℂ → ℂ) : Prop :=
  IntervalIntegrable (fun t : ℝ => g (exp (t * I))) volume 0 (2 * π) ∧
    ∃ C : ℝ, ∀ t₁ t₂ : ℝ, t₁ < t₂ → t₂ ≤ t₁ + 2 * π →
      ⨍ t in Icc t₁ t₂, ‖g (exp (t * I)) - ⨍ s in Icc t₁ t₂, g (exp (s * I)) ∂volume‖ ∂volume ≤ C

/-- **Formula (7.5.12)** (§7.5; CoFe74; Gar81, pp. 235, 258; cited in the proof of Proposition 7.13). For real-valued
`g`: `g ∈ BMO(𝕋) ⇔ g* ∈ BMO(𝕋) ⇔ e^{qg}` satisfies `(A∞)` for some `q > 0`, where `g*` is the conjugate function
of `g`.
Modelling: `g` is integrable on `𝕋` (so that `g*` is defined); `g*` is `GarnettMarshall2005.boundaryConjugate g`; the
real functions are viewed in the complex `BMO(𝕋)`. -/
theorem eq7_5_12 {g : ℂ → ℝ} (hg : Integrable g GarnettMarshall2005.arcMeasure) :
    List.TFAE [MemBMOT (fun ζ => (g ζ : ℂ)),
      MemBMOT (fun ζ => (GarnettMarshall2005.boundaryConjugate g ζ : ℂ)),
      ∃ q : ℝ, 0 < q ∧ SatisfiesAInfty (fun ζ => ENNReal.ofReal (Real.exp (q * g ζ)))] := by
  sorry

/-- **Definition** (§7.5, l. 7317; used in Proposition 7.13). `g ∈ BMOA`: `g ∈ H¹` and the boundary values of `g` on
`𝕋` belong to `BMO(𝕋)`.
Modelling: `H¹` is `GarnettMarshall2005.MemHardy 1`; the boundary values are a boundary function `φ` of `g` (angular
limits almost everywhere, `IsAngularBoundaryFun`; `MemBMOT` does not see the choice). -/
def MemBMOA (g : ℂ → ℂ) : Prop :=
  GarnettMarshall2005.MemHardy 1 g ∧ ∃ φ : ℂ → ℂ, IsAngularBoundaryFun g φ ∧ MemBMOT φ

/-- **Proposition 7.13** (§7.5). Let `f` map `𝔻` conformally into `ℂ` and let `f' ∈ Hᵖ` for some `p > 0`. Then
`log f' ∈ BMOA` if and only if there exists `q > 0` such that
`(1/Λ(I(z))) ∫_{I(z)} |f'(ζ)|^q |dζ| ≤ M₈ |f'(z)|^q` for `z ∈ 𝔻`.
Modelling: `Hᵖ` is `GarnettMarshall2005.MemHardy (ENNReal.ofReal p)`; `log f'` is a holomorphic branch `L` (BMOA
membership does not depend on the branch); (7.5.13) is `HasArcMeanBound f q`, with `M₈` depending on `f` and `q`. -/
theorem prop7_13 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hp : ∃ p : ℝ, 0 < p ∧ GarnettMarshall2005.MemHardy (ENNReal.ofReal p) (deriv f)) {L : ℂ → ℂ}
    (hL : DifferentiableOn ℂ L unitDisc) (hLf : ∀ z ∈ unitDisc, exp (L z) = deriv f z) :
    MemBMOA L ↔ ∃ q : ℝ, 0 < q ∧ HasArcMeanBound f q := by
  sorry

end Pommerenke1992
