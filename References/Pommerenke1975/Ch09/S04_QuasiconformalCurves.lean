import References.Pommerenke1975.Ch03.S01_GrunskyInequality
import LiZhongQC.Ch04.S18_BoundedTurning

/-!
# Pommerenke 1975, Ch. 9 §9.4 Quasiconformal curves

Ch. Pommerenke, *Univalent Functions*, 1975, Chapter 9 §9.4; source `full.md` of
`[Christian-Pommerenke;-Gerd-Jensen]-Univalent-func(z-lib.org)(1)(2).pdf-740e7909…` (P2), lines 3178–3560 (the OCR repeats
the heading "9.4" at l. 3292 as a page header). Only the part of the chapter that is related to Teichmüller theory is
formalized (BRIEF_W2: quasiconformal curves, extensions, the classes `Σ(κ)`); the rest of Ch. 9 is out of scope.

* Definition (quasiconformal curve, the arc condition (9.4.1), P2 l. 3180–3182) — exists: `LiZhongQC.IsBoundedTurning`
* Lemma 9.8 (cross-ratio characterization of quasiconformal curves, P2 l. 3192–3194) — `IsCyclicOrder`, `lem9_8`
* Definition (the class `Σ(κ)`, (9.4.4), P2 l. 3212–3218) — `IsClassSigmaKappa`
* Unlabelled (P2 l. 3218, `Σ(1) = Σ` by the Grunsky inequality (3.1.22)) — `para9_4_sigma_one`
* Example 9.2 (P2 l. 3220) — `ex9_2_a`, `ex9_2_b`
* Lemma 9.9, part (a) (P2 l. 3224–3230, (9.4.5)) — `lem9_9_a`
* Lemma 9.9, part (b) (P2 l. 3232, (9.4.6)) — `lem9_9_b`
* Lemma 9.10 (P2 l. 3240–3246, (9.4.7)) — `lem9_10_a`, `lem9_10_b`
* Theorem 9.12 (P2 l. 3258–3296) — `thm9_12`
* Definition (`κ`-quasiconformal extension of `g ∈ Σ`, (9.4.14), P2 l. 3308–3312) — `HasKappaQCExtension`
* Theorem 9.13 (Schiffer, Springer, Kühnau; P2 l. 3316) — `thm9_13`
* Corollary 9.6 (Ahlfors, Becker; P2 l. 3414) — `cor9_6`
* Theorem 9.14 (quasiconformal curves, Ahlfors, Kühnau; P2 l. 3438) — `thm9_14`

Not items: the Dirichlet-principle inequality (9.4.15) (a step of the proof of Theorem 9.13), the Remark after Theorem 9.13
(equality case (9.4.23), not cited), the Beurling–Ahlfors extension (9.4.26)–(9.4.27) (quoted, with the reference to Lehto–Virtanen
and Reich–Strebel), the comparison with absolute continuity on lines (a remark; the statement of Theorem 9.13 is for the
class `HasKappaQCExtension` only), Problems 9.4.1–9.4.2 (Problem 1 is `g ∈ Σ(κ) ⇔ ‖B‖ ≤ κ`).

**Conventions.** `Δ = {|z| > 1}`, `D = {|z| < 1}`. The class `Σ` is `Pommerenke1992.IsClassSigma`; the Grunsky coefficients
`b_kl` and the branch of the logarithm are `grunskyCoeff`, `grunskyLog` (`Ch03/S01`). Curves in `ℂ` are put into the
extended plane by `LiZhongQC.toExt`. The arc condition (9.4.1) with constant `K` is `LiZhongQC.IsBoundedTurning (toExt J) K`:
the same inequality `min [diam J', diam J''] ≤ K |w' − w''|` for a Jordan curve `J` (an arc through `∞` has infinite
diameter), with `K ≥ 1` (forced by the inequality for two close points). The book's "closed curve satisfying (1)" is automatically a Jordan
curve ("It follows from (1) that `J` is a Jordan curve"), so the statements below assume a Jordan curve. The relation to
`LiZhongQC.IsQuasicircle` (image of the circle under a quasiconformal map of the plane) is part of Theorem 9.14.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1975

open Pommerenke1992 (IsClassSigma sigmaCoeff)
open LiZhongQC (toExt IsBoundedTurning IsJordanCurve)

/-- **Cyclic order** (§9.4, helper for Lemma 9.8). `w₁, w₂, w₃, w₄` are cyclically ordered points of the Jordan curve `J`:
four distinct points of `J` with `w₂` and `w₄` in different components of `J ∖ {w₁, w₃}`. -/
def IsCyclicOrder (J : Set ℂ) (w₁ w₂ w₃ w₄ : ℂ) : Prop :=
  w₁ ∈ J ∧ w₂ ∈ J ∧ w₃ ∈ J ∧ w₄ ∈ J ∧ w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₁ ≠ w₄ ∧ w₂ ≠ w₃ ∧ w₂ ≠ w₄ ∧ w₃ ≠ w₄ ∧
    connectedComponentIn (J \ {w₁, w₃}) w₂ ≠ connectedComponentIn (J \ {w₁, w₃}) w₄

/-- **Lemma 9.8** (§9.4, P2 l. 3192). The Jordan curve `J ⊂ ℂ` is quasiconformal (arc condition (9.4.1) for some constant
`K`) if and only if, for some positive constant `γ`,
`|(w₁ − w₃)/(w₂ − w₃)| · |(w₂ − w₄)/(w₁ − w₄)| ≥ γ > 0` for all cyclically ordered points `w₁, …, w₄` of `J`.
Modelling: `toExt J` never contains `∞`, so `IsJordanCurve (toExt J)` restricts `J` to bounded Jordan curves in `ℂ` (the book's
lemma is Möbius invariant and also covers curves through `∞`). The restriction is needed for `IsCyclicOrder`, which tests the two
components of `J ∖ {w₁, w₃}` and would be wrong for an unbounded `J` (three components for a line). -/
theorem lem9_8 {J : Set ℂ} (hJ : IsJordanCurve (toExt J)) :
    (∃ K : ℝ, IsBoundedTurning (toExt J) K) ↔
      ∃ γ : ℝ, 0 < γ ∧ ∀ w₁ w₂ w₃ w₄ : ℂ, IsCyclicOrder J w₁ w₂ w₃ w₄ →
        γ ≤ ‖w₁ - w₃‖ / ‖w₂ - w₃‖ * (‖w₂ - w₄‖ / ‖w₁ - w₄‖) := by
  sorry

/-- **Definition** (the class `Σ(κ)`, §9.4, (9.4.4), P2 l. 3212). Let `0 ≤ κ ≤ 1`. `Σ(κ)` is the class of `g ∈ Σ` whose Grunsky
coefficients satisfy `|Σ_k Σ_l b_kl λ_k λ_l| ≤ κ Σ_k |λ_k|²/k` for all complex `λ_k` with `Σ |λ_k|²/k < ∞`.
Modelling: as in the Grunsky inequality `thm3_2_b`, the double series is summed by rectangular partial sums `Σ_{k ≤ m} Σ_{l ≤ n}`
(`m, n → ∞`): it converges to a limit `L` and `‖L‖ ≤ κ Σ_k |λ_k|²/k`; indices start at `1`. -/
def IsClassSigmaKappa (κ : ℝ) (g : ℂ → ℂ) : Prop :=
  IsClassSigma g ∧ 0 ≤ κ ∧ κ ≤ 1 ∧
    ∀ lam : ℕ → ℂ, Summable (fun k : ℕ => ‖lam (k + 1)‖ ^ 2 / ((k + 1 : ℕ) : ℝ)) →
      ∃ L : ℂ, Tendsto (fun p : ℕ × ℕ => ∑ k ∈ Finset.Icc 1 p.1, ∑ l ∈ Finset.Icc 1 p.2,
          grunskyCoeff g k l * lam k * lam l) atTop (𝓝 L) ∧
        ‖L‖ ≤ κ * ∑' k : ℕ, ‖lam (k + 1)‖ ^ 2 / ((k + 1 : ℕ) : ℝ)

/-- **Unlabelled** (§9.4, P2 l. 3218). The Grunsky inequality (3.1.22) shows `Σ(1) = Σ`. -/
theorem para9_4_sigma_one (g : ℂ → ℂ) : IsClassSigmaKappa 1 g ↔ IsClassSigma g := by
  sorry

/-- **Example 9.2, part (a)** (§9.4, P2 l. 3220). Let `0 < ρ < 1` and let `g(z) = z + …` be univalent in `|z| > ρ`, i.e.
`ρ⁻¹ g(ρ z) ∈ Σ`. Then `g ∈ Σ(ρ²)`. -/
theorem ex9_2_a {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hg : IsClassSigma (fun z => (ρ : ℂ)⁻¹ * g (ρ * z))) :
    IsClassSigmaKappa (ρ ^ 2) g := by
  sorry

/-- **Example 9.2, part (b)** (§9.4, P2 l. 3220). The relation of part (a) is sharp: `z + ρ² z⁻¹ ∈ Σ(κ)` implies `κ ≥ ρ²`
(`0 < ρ < 1`). -/
theorem ex9_2_b {ρ κ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (h : IsClassSigmaKappa κ (fun z => z + (ρ : ℂ) ^ 2 * z⁻¹)) :
    ρ ^ 2 ≤ κ := by
  sorry

/-- **Lemma 9.9, part (a)** (§9.4, P2 l. 3224, the sharper Golusin inequality (9.4.5)). Let `0 ≤ κ ≤ 1` and `g ∈ Σ`. Then
`g ∈ Σ(κ)` if and only if
`|Σ_μ Σ_ν γ_μ γ_ν log((g(z_μ) − g(z_ν))/(z_μ − z_ν))| ≤ κ Σ_μ Σ_ν γ_μ conj γ_ν log (1/(1 − (z_μ conj z_ν)⁻¹))`
for all `n`, `z_ν ∈ Δ`, `γ_ν ∈ ℂ`. Modelling: the logarithm on the left is `grunskyLog` (the branch of (3.1.8); at
`μ = ν` it is `log g'(z)`); the right side is a non-negative real number, the principal logarithm of `1/(1 − w)`, `|w| < 1`. -/
theorem lem9_9_a {g : ℂ → ℂ} (hg : IsClassSigma g) {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1) :
    IsClassSigmaKappa κ g ↔
      ∀ (n : ℕ) (z γ : Fin n → ℂ), (∀ ν, 1 < ‖z ν‖) →
        ‖∑ μ, ∑ ν, γ μ * γ ν * grunskyLog g (z μ) (z ν)‖ ≤
          κ * (∑ μ, ∑ ν, γ μ * conj (γ ν) * Complex.log (1 / (1 - (z μ * conj (z ν))⁻¹))).re := by
  sorry

/-- **Lemma 9.9, part (b)** (§9.4, P2 l. 3232, (9.4.6)). Choosing `n = 1` in part (a): if `g ∈ Σ(κ)` then
`(1 − |z|⁻²)^κ ≤ |g'(z)| ≤ (1 − |z|⁻²)^(−κ)` for `|z| > 1`. -/
theorem lem9_9_b {g : ℂ → ℂ} {κ : ℝ} (h : IsClassSigmaKappa κ g) {z : ℂ} (hz : 1 < ‖z‖) :
    (1 - ‖z‖⁻¹ ^ 2) ^ κ ≤ ‖deriv g z‖ ∧ ‖deriv g z‖ ≤ (1 - ‖z‖⁻¹ ^ 2) ^ (-κ) := by
  sorry

/-- **Lemma 9.10, part (a)** (§9.4, P2 l. 3240, (9.4.7)). Let `φ(z) = a + b z⁻¹ + …` be a Moebius transformation of `Δ` onto `Δ`.
If `g ∈ Σ(κ)`, then `h(z) = b g'(a)/(g(φ(z)) − g(a)) = z + …` also belongs to `Σ(κ)`.
Modelling: `φ(z) = (Az + B)/(Cz + D)`, `AD − BC ≠ 0`, is a Moebius automorphism of `Δ ∪ {∞}` with `φ(∞) = a` finite: `C ≠ 0`,
`a = A/C`, the pole `−D/C` lies in `Δ` (it is `φ⁻¹(∞)`), and `φ` maps `Δ ∖ {−D/C}` bijectively onto `Δ ∖ {a}`;
`b = lim z (φ(z) − a) = (BC − AD)/C²`. The function `h` (which vanishes at the pole of `φ`) is any function of `Σ(κ)`
given by the formula off the pole.
[CORRECTION, Pom1975-fix1] The earlier hypotheses `φ '' Δ = Δ` (read as a map `ℂ → ℂ`) and `φ → a` finite were jointly
unsatisfiable, and the formula read `g` at Lean's value `φ(−D/C) = 0 ∉ Δ` (AUDIT5_W2 W1). -/
theorem lem9_10_a {g : ℂ → ℂ} {κ : ℝ} (hg : IsClassSigmaKappa κ g) {A B C D : ℂ} (hdet : A * D - B * C ≠ 0)
    (hC : C ≠ 0) (hpole : 1 < ‖D / C‖)
    (hΔ : Set.BijOn (fun z => (A * z + B) / (C * z + D)) ({z : ℂ | 1 < ‖z‖} \ {-D / C})
      ({z : ℂ | 1 < ‖z‖} \ {A / C})) :
    ∃ h : ℂ → ℂ, IsClassSigmaKappa κ h ∧ ∀ z : ℂ, 1 < ‖z‖ → z ≠ -D / C →
      h z = (B * C - A * D) / C ^ 2 * deriv g (A / C) / (g ((A * z + B) / (C * z + D)) - g (A / C)) := by
  sorry

/-- **Lemma 9.10, part (b)** (§9.4, P2 l. 3246). If `g ∈ Σ(κ)` and `|c| ≥ 1`, then `c⁻¹ g(c z) ∈ Σ(κ)`. -/
theorem lem9_10_b {g : ℂ → ℂ} {κ : ℝ} (hg : IsClassSigmaKappa κ g) {c : ℂ} (hc : 1 ≤ ‖c‖) :
    IsClassSigmaKappa κ (fun z => c⁻¹ * g (c * z)) := by
  sorry

/-- **Theorem 9.12** (§9.4, P2 l. 3258). Let `0 ≤ κ < 1` and `g ∈ Σ(κ)`. Then `g` has a homeomorphic extension to `Δ̄` and maps
`∂Δ` onto a quasiconformal curve.
Modelling: the extension `G` is continuous and injective on `{|z| ≥ 1}`, equal to `g` on `Δ`, and `G(∂Δ)` satisfies the arc
condition (9.4.1) for some `K`. -/
theorem thm9_12 {g : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1) (hg : IsClassSigmaKappa κ g) :
    ∃ G : ℂ → ℂ, ContinuousOn G {z : ℂ | 1 ≤ ‖z‖} ∧ InjOn G {z : ℂ | 1 ≤ ‖z‖} ∧
      (∀ z : ℂ, 1 < ‖z‖ → G z = g z) ∧ ∃ K : ℝ, IsBoundedTurning (toExt (G '' sphere (0 : ℂ) 1)) K := by
  sorry

/-- **Definition** (`κ`-quasiconformal extension, §9.4, (9.4.14), P2 l. 3308–3312). Let `0 ≤ κ < 1`. The function `g ∈ Σ` has a
`κ`-quasiconformal extension to `ℂ` if it has a homeomorphic extension `G` to `ℂ` (a homeomorphism of the plane that agrees with
`g` on `Δ`) that is continuously differentiable (in the real sense) in `D` and satisfies `|∂G/∂z̄| ≤ κ |∂G/∂z|` in `D`
(differentiability on `|z| = 1` is not assumed). Modelling: `∂/∂z = ½(∂/∂x − i ∂/∂y)`, `∂/∂z̄ = ½(∂/∂x + i ∂/∂y)` computed
from the real Fréchet derivative. -/
def HasKappaQCExtension (κ : ℝ) (g : ℂ → ℂ) : Prop :=
  IsClassSigma g ∧ 0 ≤ κ ∧ κ < 1 ∧
    ∃ G : ℂ ≃ₜ ℂ, (∀ z : ℂ, 1 < ‖z‖ → G z = g z) ∧ ContDiffOn ℝ 1 G (ball (0 : ℂ) 1) ∧
      ∀ z ∈ ball (0 : ℂ) 1,
        ‖(fderiv ℝ G z 1 + Complex.I * fderiv ℝ G z Complex.I) / 2‖ ≤
          κ * ‖(fderiv ℝ G z 1 - Complex.I * fderiv ℝ G z Complex.I) / 2‖

/-- **Theorem 9.13** (§9.4, Schiffer, Springer, Kühnau; P2 l. 3316). If `g ∈ Σ` has a `κ`-quasiconformal extension
(`0 ≤ κ < 1`) to `ℂ`, then `g ∈ Σ(κ)`. -/
theorem thm9_13 {g : ℂ → ℂ} {κ : ℝ} (h : HasKappaQCExtension κ g) : IsClassSigmaKappa κ g := by
  sorry

/-- **Corollary 9.6** (§9.4, Ahlfors 1974, Becker 1973; P2 l. 3414). If `g(z) = z + b₁ z⁻¹ + …` is analytic in `Δ` (with the
expansion at `∞`) and `(|z|² − 1) |z g''(z)/g'(z)| ≤ κ < 1` for `z ∈ Δ`, then `g ∈ Σ(κ)`.
Modelling: `g` analytic in `Δ` with `g(z) − z → b₀` at `∞` and `g' ≠ 0` (so that the quotient is defined); univalence is a
conclusion (`g ∈ Σ(κ)` contains `g ∈ Σ`, as in Becker's theorem, Theorem 6.8). -/
theorem cor9_6 {g : ℂ → ℂ} {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ < 1) (hd : DifferentiableOn ℂ g {z : ℂ | 1 < ‖z‖})
    (hb : ∃ b₀ : ℂ, Tendsto (fun z => g z - z - b₀) (cocompact ℂ) (𝓝 0))
    (hg' : ∀ z : ℂ, 1 < ‖z‖ → deriv g z ≠ 0)
    (h : ∀ z : ℂ, 1 < ‖z‖ → (‖z‖ ^ 2 - 1) * ‖z * deriv (deriv g) z / deriv g z‖ ≤ κ) :
    IsClassSigmaKappa κ g := by
  sorry

/-- **Theorem 9.14** (§9.4, characterization of quasiconformal curves; Ahlfors 1963, Kühnau 1971). Let `g ∈ Σ`. The following
are equivalent: (i) `g(Δ)` is bounded by a quasiconformal curve (the arc condition (9.4.1) for some `K`); (ii) `g` has a
quasiconformal extension to `ℂ` (a `κ`-quasiconformal extension for some `κ < 1`); (iii) `g ∈ Σ(κ)` for some `κ < 1`.
Modelling: for (i), the boundary of `g(Δ)` in `ℂ`. -/
theorem thm9_14 {g : ℂ → ℂ} (hg : IsClassSigma g) :
    List.TFAE [∃ K : ℝ, IsBoundedTurning (toExt (frontier (g '' {z : ℂ | 1 < ‖z‖}))) K,
      ∃ κ : ℝ, HasKappaQCExtension κ g, ∃ κ : ℝ, κ < 1 ∧ IsClassSigmaKappa κ g] := by
  sorry

end Pommerenke1975
