import References.Pommerenke1992.Ch06.S02_LinearMeasureAndMeasurability
import References.LehtoVirtanen1973.Ch03.S02_AbsoluteContinuity
import References.GarnettMarshall2005.App.A_HardySpaces

/-!
# Pommerenke 1992, Ch. 6 §6.3 Rectifiable Curves

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §6.3; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 5740–5971.

* Theorem 6.8 (Rie16, Pri19; the Riesz–Privalov theorem; (6.3.3) cited at l. 6028, 6230; "Section 6.3" at l. 6594)
  — `thm6_8_a`, `thm6_8_b`, `thm6_8_c`, `thm6_8_d`
* Definition (the Hardy space `H¹`, (6.3.5); used in Theorems 6.8, 6.10, 6.12 and Ch. 7) — exists:
  `GarnettMarshall2005.MemHardy` (with p = 1: g analytic in the unit disc with the supremum over 0 < r < 1 of the
  integral of the modulus of g on the circle of radius r finite, the same normalization without the factor 1/2π;
  every use in Ch. 6–8 is membership, leader ruling QC3)
* Unlabelled claim and formula (6.3.6) (Dur70; cited "(6)" twice in the proof of Theorem 6.8, used at l. 6770) —
  `eq6_3_6`
* Proposition 6.9 — `prop6_9`
* Formula (6.3.10) (Pom75; cited "(6.3.10)" at l. 6770) — `eq6_3_10`
* Theorem 6.10 (Ale89; the proof is omitted in the book) — `thm6_10`
* Proposition 6.11 (Lav36) — `prop6_11`
* Formula (6.3.14), the inequality between the geometric and the arithmetic mean (HaLiPo67; stated in the proof of
  Proposition 6.11 and cited "(6.3.14)" as a result at l. 6898) — `eq6_3_14`
* Theorem 6.12 (War30) — `thm6_12`

Not items (DESIGN §3): the recall of Theorem 2.6 and "`Λ` is the length for rectifiable curves by Proposition 6.2"
(l. 5742); (6.3.7), (6.3.8) and the formula `f(e^{it}) - f(1) = i ∫₀^t e^{iτ} f'(e^{iτ}) dτ` (steps of the proof of
Theorem 6.8); (6.3.12) `Λ(∂G) ≤ ∫_𝕋 |f'| ≤ 2Λ(∂G)` (a consequence of Theorem 6.10, not cited); the recall of Theorem
2.11 after Theorem 6.12 (l. 5926); (6.3.18)–(6.3.20) (steps of the proof of Theorem 6.12); Exercises 6.3.1–6.3.4.

**Standing assumption** (l. 5742): `J ⊆ ℂ` is a Jordan curve (`IsJordanCurve (toExt J)`), `G` its inner domain
(`innerDomain J`, Ch. 1), `f` maps `𝔻` conformally onto `G`, and `F` is the continuous (injective) extension of `f`
to `𝔻̄` (Theorem 2.6), a hypothesis `ContinuousOn F 𝔻̄`, `F = f` on `𝔻`; `f(A)` is `F(A)` for `A ⊆ 𝕋`.

**Conventions.** As in §6.2. `f'(ζ)` for `ζ ∈ 𝕋` is the angular limit of `f'` (it exists almost everywhere for
`f' ∈ H¹` by (6.3.6)); a boundary function `φ` of an analytic `g` is a function with `g(z) → φ(ζ)` in every Stolz
angle at `ζ = e^{it}` for almost all `t`. Integrals `∫_A … |dζ|` over `A ⊆ 𝕋` are integrals over the parameters
`t ∈ [0, 2π)` with `e^{it} ∈ A`. "Rectifiable Jordan curve" is `LehtoVirtanen1973.IsRectifiableJordanCurve` (a
Jordan curve of finite linear measure, the length by Proposition 6.2); "Jordan curve of finite length `L`" is
`Λ(J) = L`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto IsJordanCurve)
open LehtoVirtanen1973 (IsRectifiableJordanCurve)

/-- **Theorem 6.8** (§6.3; Rie16, Pri19), (6.3.1). Let `f` map `𝔻` conformally onto the inner domain of the Jordan
curve `J`. Then `Λ(J) < ∞ ⇔ f' ∈ H¹`. -/
theorem thm6_8_a {J : Set ℂ} (hJ : IsJordanCurve (toExt J)) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (innerDomain J)) :
    μH[1] J < ⊤ ↔ GarnettMarshall2005.MemHardy 1 (deriv f) := by
  sorry

/-- **Theorem 6.8** (§6.3), (6.3.2). If `Λ(J) < ∞` and if `A ⊆ 𝕋` is measurable, then
`Λ(f(A)) = ∫_A |f'(ζ)| |dζ|` and `f(A)` is linearly measurable.
Modelling: `f'(ζ)` is a boundary function `φ` of `f'` (its angular limits, which exist almost everywhere; any two such
functions agree almost everywhere); `f(A) = F(A)`; the integral is the lower Lebesgue integral in `[0, ∞]`. -/
theorem thm6_8_b {J : Set ℂ} (hJ : IsJordanCurve (toExt J)) {f F : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (innerDomain J)) (hFc : ContinuousOn F (closedBall 0 1))
    (hFf : EqOn F f unitDisc) (hΛ : μH[1] J < ⊤) :
    ∃ φ : ℂ → ℂ,
      (∀ᵐ t : ℝ, HasAngularLimit (fun z => ((deriv f z : ℂ) : ExtPlane)) (exp (t * I)) (φ (exp (t * I)))) ∧
      ∀ A ⊆ sphere (0 : ℂ) 1, IsLinearlyMeasurable A →
        μH[1] (F '' A) = ∫⁻ t in {t : ℝ | t ∈ Ico 0 (2 * π) ∧ exp (t * I) ∈ A}, ‖φ (exp (t * I))‖ₑ ∧
          IsLinearlyMeasurable (F '' A) := by
  sorry

/-- **Theorem 6.8** (§6.3; (6.3.3) cited at l. 6028, 6230), (6.3.3). If `Λ(J) < ∞`, then `Λ(E) = 0 ⇔ Λ(f(E)) = 0`
for `E ⊆ 𝕋`.
Modelling: `E` is any subset of `𝕋` (outer measures); `f(E) = F(E)`. -/
theorem thm6_8_c {J : Set ℂ} (hJ : IsJordanCurve (toExt J)) {f F : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (innerDomain J)) (hFc : ContinuousOn F (closedBall 0 1))
    (hFf : EqOn F f unitDisc) (hΛ : μH[1] J < ⊤) {E : Set ℂ} (hE : E ⊆ sphere (0 : ℂ) 1) :
    circleMeasure E = 0 ↔ μH[1] (F '' E) = 0 := by
  sorry

/-- **Theorem 6.8** (§6.3), (6.3.4). If `Λ(J) < ∞`, then
`lim_{z → ζ, z ∈ 𝔻̄} (f(z) - f(ζ))/(z - ζ) ≠ 0, ∞` exists `= f'(ζ)` for almost all `ζ ∈ 𝕋`.
Modelling: `f` on `𝔻̄` is `F`; the limit is taken over `z ∈ 𝔻̄ ∖ {ζ}`, and "`= f'(ζ)`" says that it is the angular
limit of `f'` at `ζ` (the boundary function of (6.3.2)). -/
theorem thm6_8_d {J : Set ℂ} (hJ : IsJordanCurve (toExt J)) {f F : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (innerDomain J)) (hFc : ContinuousOn F (closedBall 0 1))
    (hFf : EqOn F f unitDisc) (hΛ : μH[1] J < ⊤) :
    ∀ᵐ t : ℝ, ∃ a : ℂ, a ≠ 0 ∧
      Tendsto (fun z => (F z - F (exp (t * I))) / (z - exp (t * I)))
        (𝓝[closedBall 0 1 \ {exp (t * I)}] (exp (t * I))) (𝓝 a) ∧
      HasAngularLimit (fun z => ((deriv f z : ℂ) : ExtPlane)) (exp (t * I)) a := by
  sorry

/-- **Unlabelled claim and formula (6.3.6)** (§6.3, l. 5776; Dur70; cited "(6)" twice in the proof of Theorem 6.8 and
used at l. 6770). If `g ∈ H¹`, then `g(ζ)` exists and is `≠ 0` for almost all `ζ ∈ 𝕋` and is integrable,
furthermore `∫_𝕋 |g(rζ) - g(ζ)| |dζ| → 0` and `∫_𝕋 |g(rζ)| |dζ| → ∫_𝕋 |g(ζ)| |dζ|` as `r → 1`.
Modelling: `g(ζ)` is the angular limit, given by a boundary function `φ`; [CORRECTION] "`≠ 0` for almost all `ζ`" is
stated for `g ≢ 0` (the book applies it to `g = f' ≠ 0`; for `g = 0` it is false), written `∃ z ∈ 𝔻, g(z) ≠ 0`
(leader ruling, Q6.8(b)); the integrals are over `t ∈ [0, 2π]`, `ζ = e^{it}`, of integrable functions. -/
theorem eq6_3_6 {g : ℂ → ℂ} (hg : GarnettMarshall2005.MemHardy 1 g) :
    ∃ φ : ℂ → ℂ, (∀ᵐ t : ℝ, HasAngularLimit (fun z => (g z : ExtPlane)) (exp (t * I)) (φ (exp (t * I)))) ∧
      IntervalIntegrable (fun t : ℝ => φ (exp (t * I))) volume 0 (2 * π) ∧
      ((∃ z ∈ unitDisc, g z ≠ 0) → ∀ᵐ t : ℝ, φ (exp (t * I)) ≠ 0) ∧
      Tendsto (fun r : ℝ => ∫ t in (0 : ℝ)..2 * π, ‖g (r * exp (t * I)) - φ (exp (t * I))‖) (𝓝[<] 1) (𝓝 0) ∧
      Tendsto (fun r : ℝ => ∫ t in (0 : ℝ)..2 * π, ‖g (r * exp (t * I))‖) (𝓝[<] 1)
        (𝓝 (∫ t in (0 : ℝ)..2 * π, ‖φ (exp (t * I))‖)) := by
  sorry

/-- **Proposition 6.9** (§6.3). Let `f` be analytic and bounded in `𝔻`. If `ζ ∈ 𝕋` and if (6.3.9)
`(f(z) - ω)/(z - ζ) → a ∈ ℂ` as `z → ζ` restricted to `z ∈ 𝕋`, then (6.3.9) holds for `z ∈ 𝔻`.
Modelling (leader ruling, Q6.8(c)): `ω ∈ ℂ` is a constant; `f(z)` for `z ∈ 𝕋` is the boundary value, the angular
limit of `f` at `z` (it exists almost everywhere by Fatou's theorem); the hypothesis is the limit over the points
`z ∈ 𝕋 ∖ {ζ}` where the boundary value exists (this does not depend on a choice of boundary function), and the
conclusion is the limit as `z → ζ`, `z ∈ 𝔻`. For bounded `f` the angular and the radial limits coincide (Lindelöf),
so this agrees with the radial convention of Ch. 6. The OCR prints the display without its tag. -/
theorem prop6_9 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hb : ∃ M : ℝ, ∀ z ∈ unitDisc, ‖f z‖ ≤ M)
    {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) {ω a : ℂ}
    (h9 : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ z ∈ sphere (0 : ℂ) 1, z ≠ ζ → ‖z - ζ‖ < δ → ∀ w : ℂ,
      HasAngularLimit (fun u => (f u : ExtPlane)) z w → ‖(w - ω) / (z - ζ) - a‖ < ε) :
    Tendsto (fun z => (f z - ω) / (z - ζ)) (𝓝[unitDisc] ζ) (𝓝 a) := by
  sorry

/-- **Formula (6.3.10)** (§6.3, l. 5856; Pom75; cited "(6.3.10)" at l. 6770). The assumption of Theorem 6.8 that
`G = f(𝔻)` is a Jordan domain can be relaxed: if `f` maps `𝔻` conformally onto `G ⊆ ℂ`, then
`Λ(∂G) < ∞ ⇔ f' ∈ H¹`.
Modelling: `∂G` is the boundary in `ℂ`; for bounded `G` it is the book's `∂G`, and for unbounded `G` both sides are
false (`∂G` meets every large circle, so `Λ(∂G) = ∞`, and `f' ∈ H¹` would make `f` bounded). -/
theorem eq6_3_10 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) :
    μH[1] (frontier G) < ⊤ ↔ GarnettMarshall2005.MemHardy 1 (deriv f) := by
  sorry

/-- **Theorem 6.10** (§6.3; Ale89; the book omits the proof). Let `B` be a continuum in `ℂ` with `Λ(B) < ∞` and let
`G_k` be the components of `Ĉ ∖ B`. If `f_k` maps `𝔻` conformally onto `G_k`, then `f_k' ∈ H¹` ("with modifications
for the unbounded component") and (6.3.11) `2Λ(B) = Σ_k ∫_𝕋 |f_k'(z)| |dz|`.
Modelling (leader ruling, Q6.8(d)):
- The bounded components are the bounded components `U` of `ℂ ∖ B`, with conformal maps `fk U` of `𝔻` onto `U`.
- "With modifications for the unbounded component": the unbounded component `G_∞ ∋ ∞` is mapped from
  `𝔻* = {|z| > 1} ∪ {∞}` by `f_∞` with `f_∞(∞) = ∞`, given by its finite part `g`, analytic and injective in
  `{|z| > 1}` with `g(z) → ∞` as `z → ∞`, onto the unbounded component of `ℂ ∖ B`; the `H¹` condition is
  `sup_{r > 1} ∫_𝕋 |g'(rζ)| |dζ| < ∞`, and its term in (6.3.11) is the outer boundary integral
  `lim_{r → 1+} ∫_𝕋 |g'(rζ)| |dζ|`.
- The boundary integral `∫_𝕋 |f_k'(z)| |dz|` is written as `lim_{r → 1-} ∫_𝕋 |f_k'(rz)| |dz|`, a supremum (the
  integral means of `|f_k'|` increase with `r`), which is the integral of the boundary function by (6.3.6) once
  `f_k' ∈ H¹` (`eq6_3_6`); likewise the outer means decrease in `r > 1`. The sum runs over the bounded components (at
  most countably many), in `[0, ∞]`; `B` is a continuum of `Ĉ` contained in `ℂ` (`IsContinuum`, Ch. 1).
- Redundancies, kept for readability: `hginf` follows from the other hypotheses on `g` (the pole at `∞` is
  automatic), and the first two conjuncts follow from the third, given `Λ(B) < ∞`. -/
theorem thm6_10 {B : Set ℂ} (hB : IsContinuum (toExt B)) (hΛ : μH[1] B < ⊤) {fk : Set ℂ → ℂ → ℂ}
    (hfk : ∀ U ∈ {U : Set ℂ | ∃ x ∉ B, U = connectedComponentIn Bᶜ x ∧ Bornology.IsBounded U},
      IsConformalOnto (fk U) unitDisc U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g {z | 1 < ‖z‖}) (hgi : InjOn g {z | 1 < ‖z‖})
    (hgG : ∃ x ∉ B, ¬ Bornology.IsBounded (connectedComponentIn Bᶜ x) ∧
      g '' {z | 1 < ‖z‖} = connectedComponentIn Bᶜ x)
    (hginf : Tendsto g (cocompact ℂ) (cocompact ℂ)) :
    (∀ U ∈ {U : Set ℂ | ∃ x ∉ B, U = connectedComponentIn Bᶜ x ∧ Bornology.IsBounded U},
      GarnettMarshall2005.MemHardy 1 (deriv (fk U))) ∧
    (⨆ r ∈ Ioi (1 : ℝ), ∫⁻ t in Ioc 0 (2 * π), ‖deriv g (r * exp (t * I))‖ₑ) < ⊤ ∧
    2 * μH[1] B =
      (∑' U : {U : Set ℂ // ∃ x ∉ B, U = connectedComponentIn Bᶜ x ∧ Bornology.IsBounded U},
        ⨆ r ∈ Ioo (0 : ℝ) 1, ∫⁻ t in Ioc 0 (2 * π), ‖deriv (fk U.1) (r * exp (t * I))‖ₑ) +
      ⨆ r ∈ Ioi (1 : ℝ), ∫⁻ t in Ioc 0 (2 * π), ‖deriv g (r * exp (t * I))‖ₑ := by
  sorry

/-- **Proposition 6.11** (§6.3; Lav36). Let `f` map `𝔻` conformally onto the inner domain of a Jordan curve of finite
length `L`. If `E ⊆ 𝕋` is measurable, then (6.3.13)
`Λ(f(E)) ≥ L exp(-(2π/Λ(E)) log(L/(π|f'(0)|)))`.
Modelling: the length is `Λ(J) = L` (Proposition 6.2); `f(E) = F(E)`; the hypothesis `0 < Λ(E)` only guards
against Lean's convention `2π/0 = 0`, which would turn the case `Λ(E) = 0` into the false `L ≤ Λ(f(E))`; in the book's
reading `2π/0 = ∞` that case is trivially true (`L exp(-∞) = 0`, the logarithm being positive since
`L = ∫|f'| ≥ 2π|f'(0)|`), so this is no correction of the book. The estimate "sharpens the implication
`Λ(E) > 0 ⇒ Λ(f(E)) > 0`" (l. 5878). -/
theorem prop6_11 {J : Set ℂ} (hJ : IsJordanCurve (toExt J)) {L : ℝ} (hL : μH[1] J = ENNReal.ofReal L)
    {f F : ℂ → ℂ} (hf : IsConformalOnto f unitDisc (innerDomain J)) (hFc : ContinuousOn F (closedBall 0 1))
    (hFf : EqOn F f unitDisc) {E : Set ℂ} (hET : E ⊆ sphere (0 : ℂ) 1) (hE : IsLinearlyMeasurable E)
    (hEpos : 0 < circleMeasure E) :
    ENNReal.ofReal (L * Real.exp (-(2 * π / (circleMeasure E).toReal) * Real.log (L / (π * ‖deriv f 0‖)))) ≤
      μH[1] (F '' E) := by
  sorry

/-- **Formula (6.3.14)** (§6.3, stated in the proof of Proposition 6.11, HaLiPo67; cited "(6.3.14)" as a result at
l. 6898, in the proof of Proposition 7.5). The inequality between the geometric and the arithmetic mean:
`exp((1/Λ(A)) ∫_A log φ(t) dt) ≤ (1/Λ(A)) ∫_A φ(t) dt`.
Modelling: stated for a finite non-zero measure `μ` in place of `dt` on `A` (`μ = volume.restrict A`,
`0 < Λ(A) < ∞`), because l. 6898 applies it to the probability measure `p(z, ζ)|dζ|` on `𝕋`; `φ > 0` almost
everywhere with `φ` and `log φ` integrable (outside this case the book's inequality holds with `log 0 = -∞` or an
infinite right-hand side, which the real integrals cannot express). -/
theorem eq6_3_14 {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] (hμ : μ ≠ 0) {φ : α → ℝ}
    (hpos : ∀ᵐ x ∂μ, 0 < φ x) (hφ : Integrable φ μ) (hlog : Integrable (fun x => Real.log (φ x)) μ) :
    Real.exp ((μ univ).toReal⁻¹ * ∫ x, Real.log (φ x) ∂μ) ≤ (μ univ).toReal⁻¹ * ∫ x, φ x ∂μ := by
  sorry

/-- **Theorem 6.12** (§6.3; War30). Let `f_n` (`n = 1, 2, …`) and `f` map `𝔻` conformally onto the inner domains of
the rectifiable Jordan curves `J_n` and `J`. If (6.3.15) `f_n → f` as `n → ∞` locally uniformly in `𝔻` and (6.3.16)
`Λ(J_n) → Λ(J)` as `n → ∞`, then (6.3.17) `∫_𝕋 |f_n'(z) - f'(z)| |dz| → 0` as `n → ∞`.
Modelling: `f_n'(z)`, `f'(z)` on `𝕋` are boundary functions `φ_n`, `φ` of `f_n'`, `f'` (angular limits almost
everywhere; the integral does not depend on the choice); the integral is the lower Lebesgue integral in `[0, ∞]`; the
OCR splits the tags "(15)" and (16). -/
theorem thm6_12 {Js : ℕ → Set ℂ} {J : Set ℂ} (hJs : ∀ n, IsRectifiableJordanCurve (Js n))
    (hJ : IsRectifiableJordanCurve J) {fs : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hfs : ∀ n, IsConformalOnto (fs n) unitDisc (innerDomain (Js n)))
    (hf : IsConformalOnto f unitDisc (innerDomain J)) (h15 : TendstoLocallyUniformlyOn fs f atTop unitDisc)
    (h16 : Tendsto (fun n => μH[1] (Js n)) atTop (𝓝 (μH[1] J))) {φs : ℕ → ℂ → ℂ} {φ : ℂ → ℂ}
    (hφs : ∀ n, ∀ᵐ t : ℝ,
      HasAngularLimit (fun z => ((deriv (fs n) z : ℂ) : ExtPlane)) (exp (t * I)) (φs n (exp (t * I))))
    (hφ : ∀ᵐ t : ℝ, HasAngularLimit (fun z => ((deriv f z : ℂ) : ExtPlane)) (exp (t * I)) (φ (exp (t * I)))) :
    Tendsto (fun n => ∫⁻ t in Ioc 0 (2 * π), ‖φs n (exp (t * I)) - φ (exp (t * I))‖ₑ) atTop (𝓝 0) := by
  sorry

end Pommerenke1992
