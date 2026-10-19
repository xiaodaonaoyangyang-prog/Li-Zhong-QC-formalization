import References.Pommerenke1992.Ch01.S03_KoebeDistortionTheorem

/-!
# Pommerenke 1975, Ch. 3 §3.1 The Grunsky inequality

Ch. Pommerenke, *Univalent Functions*, 1975, Chapter 3 *The Grunsky Inequality* (introduction and §3.1); source
`full.md` of `[Christian-Pommerenke;-Gerd-Jensen]-Univalent-func(z-lib.org)(1)(2).pdf-a3a4b68f…` (P1),
lines 1936–2283 (the OCR repeats the heading "3.1" at l. 2152 as a page header).

* Definition (the exterior set `E = ℂ ∖ g(Δ)`, §1.1; used throughout) — `sigmaE`
* Definition (the Faber polynomials, recursion (3.1.5), l. 1983–1999; used throughout) — `faberPoly`
* Formula (3.1.2) (cited at P1 l. 3363, 3592, 3640) — `eq3_1_2`
* Formula (3.1.3) (cited at P1 l. 5560) — `eq3_1_3`
* Formula (3.1.4) (cited at P1 l. 8022, 8362, 8458) — `eq3_1_4`
* Formula (3.1.7) (cited at P1 l. 2530, 8180) — `eq3_1_7`
* Definition (the Grunsky coefficients `b_kl`, (3.1.8), l. 2014–2021; used throughout) — `grunskyCoeff`
* Definition (the logarithm of the difference quotient, branch fixed by (3.1.8); used in §9.4) — `grunskyLog`
* Formula (3.1.8) (cited at P1 l. 2303, 3127, 8438 and P2 l. 3218) — `eq3_1_8`
* Formula (3.1.9) (cited at P1 l. 2102) — `eq3_1_9`
* Formula (3.1.11) (cited at P1 l. 2102, 2530, 3296, 3620, 5532, 8472) — `eq3_1_11`
* Formula (3.1.12) (cited at P1 l. 3749) — `eq3_1_12`
* Formula (3.1.13) (cited at P1 l. 2507, 2580) — `eq3_1_13`
* Theorem 3.1 (cited at P1 l. 2081, 2226, 3598, 3612) — `thm3_1`
* Formula (3.1.15) (cited at P1 l. 2527) — `eq3_1_15`
* Formula (3.1.16) (cited at P1 l. 2525) — `eq3_1_16`
* Unlabelled (§3.1, l. 2105 and 2129: the proof steps (3.1.18) and (3.1.20) of Theorem 3.1; cited as results at
  P2 l. 3342) — `eq3_1_20`
* Theorem 3.2, (3.1.21) (cited at P1 l. 3181) — `thm3_2_a`
* Theorem 3.2, (3.1.22) (the Grunsky inequality; cited at P1 l. 2309, 2430, 3727, 8416 and P2 l. 3218) — `thm3_2_b`
* Definition (the Grunsky operator `B`, (3.1.26), l. 2198–2203; used in §9.4) — `grunskyOperator`
* Corollary 3.1 (the Grunsky operator is unitary if and only if area `E = 0`) — `cor3_1`
* Definition (the Grunsky matrix of order `m`, (3.1.31), l. 2236–2241) — `grunskyMatrix`
* Corollary 3.2 — `cor3_2`

Not items (DESIGN §3): the introductory claim (*) at l. 1940 (the double series is analytic if and only if
`g ∈ Σ`) and the Grunsky inequality (*) of l. 1947 (it is (3.1.22)); (3.1.5) itself (the definition `faberPoly`);
(3.1.6) (the leading terms of `Φ_n`) and (3.1.10) (a step towards (3.1.11)); the independence of the `b_kl` of `b₀`
(l. 2045); Example 3.1 (not cited; its content is `b_kk = a^k/k`); the converse remark of l. 2090 ((3.1.14) implies
univalence; not cited); (3.1.17) (the polynomial `h`, part of `eq3_1_20`); (3.1.19) (Corollary 1.1 applied, a step);
(3.1.23)–(3.1.25) and the discussion of equality in the finite case (steps; not cited); the adjoint (3.1.27) and
(3.1.28) with the remark that the two inequalities (28) are equivalent (not cited as results); the definition of a
unitary bounded operator and (3.1.29) (the book's own reformulation, used as the statement of `cor3_1`);
Problems 3.1.1–3.1.7.

Book errors (inside the proof, recorded only): in (3.1.23), first line, the inner sum should start at `l = q`, not
`l = p`. The reference "Corollary 1.5 (Section 1.5)" at l. 2108 is the analytic Green's formula for `H(r)`
(Corollary 1.1, `cor1_1`).

**Conventions.**
- `Σ` is `Pommerenke1992.IsClassSigma`, `b_n = Pommerenke1992.sigmaCoeff g n`, `E = sigmaE g` (defined in this file; the Ch. 1 file of the same name is not delivered, see the INVENTORY), `Δ = {|z| > 1}`,
  and the area is `volume`. The book states the formal identities (3.1.2)–(3.1.13) for any `g` analytic near `∞`
  and univalent in some `|z| > R`; they are stated here for `g ∈ Σ`, the case used everywhere later (decision D2).
- Indices of Grunsky coefficients, of the `λ_k` and of the sequences `z_k` start at `1`. Infinite sums over
  `k = 1, 2, …` are written over `k : ℕ` with the shift `k + 1`; finite ones use `Finset.Icc 1 m`.
- `z^{-n}` is written `z⁻¹ ^ n`. The Faber polynomial `Φ_n(w)` of `g` is
  `Polynomial.eval w (faberPoly (sigmaCoeff g) n)`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1975

open LiZhongQC (unitDisc knHyp)
open Pommerenke1992 (IsClassSigma sigmaCoeff sCoeff)

/-- **Definition** (`E(g)`, §1.1, l. 234–239; used throughout). For `g ∈ Σ`, `E = E(g) = ℂ ∖ g(Δ)` is the complement of the
image domain. Modelling: `g(Δ)` is the image of `{|z| > 1}` (the point `∞ ↦ ∞` is not in `ℂ`). -/
def sigmaE (g : ℂ → ℂ) : Set ℂ :=
  (g '' {z : ℂ | 1 < ‖z‖})ᶜ

/-- **Definition** (the Faber polynomials, §3.1, recursion (3.1.5), l. 1983–1999). For
`g(z) = z + Σ_{n ≥ 0} b_n z⁻ⁿ`, the `n`-th Faber polynomial `Φ_n(w)` is given by `Φ₀ = 1`, `Φ₁(w) = w - b₀` and
(3.1.5) `Φ_{n+1}(w) = (w - b₀)Φ_n(w) - Σ_{ν=1}^{n-1} b_{n-ν}Φ_ν(w) - (n + 1)b_n` (`n = 1, 2, …`).
Modelling: defined from the coefficient sequence `b` (applied to `b = sigmaCoeff g`); the book defines `Φ_n` by the
expansion (3.1.2) and derives (3.1.5); here (3.1.5) is the definition (decision D1) and (3.1.2) a theorem. In the
clause for `n + 2`, `ν : Fin n` stands for the index `ν + 1 ∈ {1, …, n}`. -/
def faberPoly (b : ℕ → ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | 1 => Polynomial.X - Polynomial.C (b 0)
  | n + 2 => (Polynomial.X - Polynomial.C (b 0)) * faberPoly b (n + 1) -
      ∑ ν : Fin n, Polynomial.C (b (n - ν.1)) * faberPoly b (ν.1 + 1) -
      Polynomial.C (((n + 2 : ℕ) : ℂ) * b (n + 1))
decreasing_by all_goals omega

/-- **Formula (3.1.2)** (§3.1, l. 1965; cited at P1 l. 3363, 3592, 3640). For `g ∈ Σ` and fixed `w ∈ ℂ`,
`log ((g(ζ) - w)/ζ) = -Σ_{n ≥ 1} Φ_n(w)ζ⁻ⁿ/n` for large `|ζ|`.
Modelling: the logarithm is the branch vanishing at `∞`; the statement is written branch-free: the series converges
for large `|ζ|` and its exponential is `(g(ζ) - w)/ζ` (a convergent series `Σ c_n ζ⁻ⁿ` tends to `0` at `∞`, which
fixes the branch). -/
theorem eq3_1_2 {g : ℂ → ℂ} (hg : IsClassSigma g) (w : ℂ) :
    ∃ R : ℝ, ∀ ζ : ℂ, R < ‖ζ‖ →
      Summable (fun n : ℕ =>
        Polynomial.eval w (faberPoly (sigmaCoeff g) (n + 1)) * ζ⁻¹ ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) ∧
      (g ζ - w) / ζ = exp (-∑' n : ℕ,
        Polynomial.eval w (faberPoly (sigmaCoeff g) (n + 1)) * ζ⁻¹ ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) := by
  sorry

/-- **Formula (3.1.3)** (§3.1, l. 1971; cited at P1 l. 5560). For `g ∈ Σ` and fixed `w ∈ ℂ`,
`g'(ζ)/(g(ζ) - w) = Σ_{n ≥ 0} Φ_n(w) ζ^{-(n+1)}` for large `|ζ|`. -/
theorem eq3_1_3 {g : ℂ → ℂ} (hg : IsClassSigma g) (w : ℂ) :
    ∃ R : ℝ, ∀ ζ : ℂ, R < ‖ζ‖ →
      HasSum (fun n : ℕ => Polynomial.eval w (faberPoly (sigmaCoeff g) n) * ζ⁻¹ ^ (n + 1))
        (deriv g ζ / (g ζ - w)) := by
  sorry

/-- **Formula (3.1.4)** (§3.1, l. 1977; cited at P1 l. 8022, 8362, 8458). For `g ∈ Σ` and fixed `w ∈ ℂ`,
`1/(g(ζ) - w) = Σ_{n ≥ 1} Φ_n'(w) ζ⁻ⁿ/n` for large `|ζ|`. -/
theorem eq3_1_4 {g : ℂ → ℂ} (hg : IsClassSigma g) (w : ℂ) :
    ∃ R : ℝ, ∀ ζ : ℂ, R < ‖ζ‖ →
      HasSum (fun n : ℕ => Polynomial.eval w (Polynomial.derivative (faberPoly (sigmaCoeff g) (n + 1))) *
          ζ⁻¹ ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
        (1 / (g ζ - w)) := by
  sorry

/-- **Formula (3.1.7)** (§3.1, l. 2001–2011; cited at P1 l. 2530, 8180). `Φ₀(w) = 1`, `Φ₁(w) = w - b₀`,
`Φ₂(w) = (w - b₀)² - 2b₁`, `Φ₃(w) = (w - b₀)³ - 3b₁(w - b₀) - 3b₂`,
`Φ₄(w) = (w - b₀)⁴ - 4b₁(w - b₀)² - 4b₂(w - b₀) + (2b₁² - 4b₃)`.
Modelling: identities of polynomials, for every coefficient sequence `b`. -/
theorem eq3_1_7 (b : ℕ → ℂ) :
    faberPoly b 0 = 1 ∧ faberPoly b 1 = Polynomial.X - Polynomial.C (b 0) ∧
      faberPoly b 2 = (Polynomial.X - Polynomial.C (b 0)) ^ 2 - Polynomial.C (2 * b 1) ∧
      faberPoly b 3 = (Polynomial.X - Polynomial.C (b 0)) ^ 3 -
        Polynomial.C (3 * b 1) * (Polynomial.X - Polynomial.C (b 0)) - Polynomial.C (3 * b 2) ∧
      faberPoly b 4 = (Polynomial.X - Polynomial.C (b 0)) ^ 4 -
        Polynomial.C (4 * b 1) * (Polynomial.X - Polynomial.C (b 0)) ^ 2 -
        Polynomial.C (4 * b 2) * (Polynomial.X - Polynomial.C (b 0)) + Polynomial.C (2 * b 1 ^ 2 - 4 * b 3) := by
  sorry

/-- **Definition** (the Grunsky coefficients, §3.1, (3.1.8), l. 2014–2021; used throughout). The Grunsky coefficients
`b_kl` (`k, l = 1, 2, …`) of `g ∈ Σ` are the coefficients of
`log ((g(z) - g(ζ))/(z - ζ)) = -Σ_k Σ_l b_kl z^{-k} ζ^{-l}`.
Modelling: computed, as the book's (3.1.11) `Φ_k(g(z)) = z^k + k Σ_l b_kl z^{-l}` shows, as `1/k` times the
coefficient of `z^{-l}` in the Laurent expansion of `Φ_k(g(z))` in `|z| > 1`:
`b_kl = k⁻¹ (2πi)⁻¹ ∮_{|z| = 2} Φ_k(g(z)) z^{l-1} dz` (in the pattern of `Pommerenke1992.sigmaCoeff`; decision D1).
The values for `k = 0` or `l = 0` are not used; (3.1.8) is the theorem `eq3_1_8`. -/
def grunskyCoeff (g : ℂ → ℂ) (k l : ℕ) : ℂ :=
  (k : ℂ)⁻¹ * ((2 * π * I)⁻¹ *
    circleIntegral (fun z => Polynomial.eval (g z) (faberPoly (sigmaCoeff g) k) * z ^ ((l : ℤ) - 1)) 0 2)

/-- **Definition** (the logarithm of the difference quotient, §3.1, (3.1.8); used in §9.4). For `g ∈ Σ` and `|z|, |ζ| > 1`,
`grunskyLog g z ζ = -Σ_{k ≥ 1} Σ_{l ≥ 1} b_kl z^{-k} ζ^{-l}`, the branch of `log ((g(z) - g(ζ))/(z - ζ))` fixed by (3.1.8)
(`log g'(z)` for `z = ζ`). Modelling: `tsum` over `ℕ × ℕ` (absolutely convergent by `eq3_1_8`). -/
def grunskyLog (g : ℂ → ℂ) (z ζ : ℂ) : ℂ :=
  -∑' p : ℕ × ℕ, grunskyCoeff g (p.1 + 1) (p.2 + 1) * z⁻¹ ^ (p.1 + 1) * ζ⁻¹ ^ (p.2 + 1)

/-- **Formula (3.1.8)** (§3.1, l. 2017; cited at P1 l. 2303, 3127, 8438 and P2 l. 3218). For `g ∈ Σ`,
`log ((g(z) - g(ζ))/(z - ζ)) = -Σ_{k ≥ 1} Σ_{l ≥ 1} b_kl z^{-k} ζ^{-l}` for `|z| > 1`, `|ζ| > 1`.
Modelling: the double series converges absolutely (summable over `ℕ × ℕ`), and its negative is a logarithm of the
difference quotient: `exp(-Σ Σ b_kl z^{-k} ζ^{-l}) = (g(z) - g(ζ))/(z - ζ)`, read as `g'(z)` for `z = ζ`
(`dslope`). This determines the branch (the one of `Pommerenke1975.grunskyLog`, §3.2). -/
theorem eq3_1_8 {g : ℂ → ℂ} (hg : IsClassSigma g) {z ζ : ℂ} (hz : 1 < ‖z‖) (hζ : 1 < ‖ζ‖) :
    Summable (fun p : ℕ × ℕ => grunskyCoeff g (p.1 + 1) (p.2 + 1) * z⁻¹ ^ (p.1 + 1) * ζ⁻¹ ^ (p.2 + 1)) ∧
      exp (-∑' p : ℕ × ℕ, grunskyCoeff g (p.1 + 1) (p.2 + 1) * z⁻¹ ^ (p.1 + 1) * ζ⁻¹ ^ (p.2 + 1)) =
        dslope g ζ z := by
  sorry

/-- **Formula (3.1.9)** (§3.1, l. 2023; cited at P1 l. 2102). For `g ∈ Σ`, `b_kl = b_lk` (`k, l = 1, 2, …`). -/
theorem eq3_1_9 {g : ℂ → ℂ} (hg : IsClassSigma g) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    grunskyCoeff g k l = grunskyCoeff g l k := by
  sorry

/-- **Formula (3.1.11)** (§3.1, l. 2035; cited at P1 l. 2102, 2530, 3296, 3620, 5532, 8472). For `g ∈ Σ` and
`k = 1, 2, …`, `Φ_k(g(z)) = z^k + k Σ_{l ≥ 1} b_kl z^{-l}` (`|z| > 1`). -/
theorem eq3_1_11 {g : ℂ → ℂ} (hg : IsClassSigma g) {k : ℕ} (hk : 1 ≤ k) {z : ℂ} (hz : 1 < ‖z‖) :
    HasSum (fun l : ℕ => (k : ℂ) * grunskyCoeff g k (l + 1) * z⁻¹ ^ (l + 1))
      (Polynomial.eval (g z) (faberPoly (sigmaCoeff g) k) - z ^ k) := by
  sorry

/-- **Formula (3.1.12)** (§3.1, l. 2041; cited at P1 l. 3749). For `g ∈ Σ`, `b_k1 = b_1k = b_k`
(`k = 1, 2, …`). -/
theorem eq3_1_12 {g : ℂ → ℂ} (hg : IsClassSigma g) {k : ℕ} (hk : 1 ≤ k) :
    grunskyCoeff g k 1 = sigmaCoeff g k ∧ grunskyCoeff g 1 k = sigmaCoeff g k := by
  sorry

/-- **Formula (3.1.13)** (§3.1, l. 2047–2055; cited at P1 l. 2507, 2580). For `g ∈ Σ`:
`b₂₂ = b₃ + ½b₁²`, `b₂₃ = b₄ + b₁b₂`, `b₂₄ = b₅ + b₁b₃ + ½b₂²`, `b₃₃ = b₅ + b₁b₃ + b₂² + ⅓b₁³`,
`b₃₄ = b₆ + b₁b₄ + 2b₂b₃ + b₁²b₂`, `b₄₄ = b₇ + b₁b₅ + 2b₂b₄ + 2b₁b₂² + b₁²b₃ + (3/2)b₃² + ¼b₁⁴`.
Modelling: `b` is the coefficient sequence `sigmaCoeff g`. -/
theorem eq3_1_13 {g : ℂ → ℂ} (hg : IsClassSigma g) {b : ℕ → ℂ} (hb : b = sigmaCoeff g) :
    grunskyCoeff g 2 2 = b 3 + b 1 ^ 2 / 2 ∧ grunskyCoeff g 2 3 = b 4 + b 1 * b 2 ∧
      grunskyCoeff g 2 4 = b 5 + b 1 * b 3 + b 2 ^ 2 / 2 ∧
      grunskyCoeff g 3 3 = b 5 + b 1 * b 3 + b 2 ^ 2 + b 1 ^ 3 / 3 ∧
      grunskyCoeff g 3 4 = b 6 + b 1 * b 4 + 2 * b 2 * b 3 + b 1 ^ 2 * b 2 ∧
      grunskyCoeff g 4 4 = b 7 + b 1 * b 5 + 2 * b 2 * b 4 + 2 * b 1 * b 2 ^ 2 + b 1 ^ 2 * b 3 +
        3 / 2 * b 3 ^ 2 + b 1 ^ 4 / 4 := by
  sorry

/-- **Theorem 3.1** (§3.1, l. 2074; Schiffer, Milin, Jenkins, Pommerenke; cited at P1 l. 2081, 2226, 3598, 3612). Let
`g ∈ Σ` and let `λ₁, …, λ_m` (`m = 1, 2, …`) be complex numbers not all zero. Then
(3.1.14) `Σ_{k ≥ 1} k |Σ_{l=1}^m b_kl λ_l|² ≤ Σ_{k=1}^m |λ_k|²/k`, and equality holds if and only if `area E = 0`.
Modelling: the conclusion includes the convergence of the left-hand series. -/
theorem thm3_1 {g : ℂ → ℂ} (hg : IsClassSigma g) {m : ℕ} (hm : 1 ≤ m) {lam : ℕ → ℂ}
    (hlam : ∃ l ∈ Finset.Icc 1 m, lam l ≠ 0) :
    Summable (fun k : ℕ =>
        ((k + 1 : ℕ) : ℝ) * ‖∑ l ∈ Finset.Icc 1 m, grunskyCoeff g (k + 1) l * lam l‖ ^ 2) ∧
      ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * ‖∑ l ∈ Finset.Icc 1 m, grunskyCoeff g (k + 1) l * lam l‖ ^ 2 ≤
        ∑ k ∈ Finset.Icc 1 m, ‖lam k‖ ^ 2 / (k : ℝ) ∧
      (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * ‖∑ l ∈ Finset.Icc 1 m, grunskyCoeff g (k + 1) l * lam l‖ ^ 2 =
          ∑ k ∈ Finset.Icc 1 m, ‖lam k‖ ^ 2 / (k : ℝ) ↔ volume (sigmaE g) = 0) := by
  sorry

/-- **Formula (3.1.15)** (§3.1, l. 2085; cited at P1 l. 2527). For `g ∈ Σ`, `Σ_{k ≥ 1} k |b_km|² ≤ 1/m`
(`m = 1, 2, …`).
Modelling: the conclusion includes the convergence of the series. -/
theorem eq3_1_15 {g : ℂ → ℂ} (hg : IsClassSigma g) {m : ℕ} (hm : 1 ≤ m) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ‖grunskyCoeff g (k + 1) m‖ ^ 2) ∧
      ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * ‖grunskyCoeff g (k + 1) m‖ ^ 2 ≤ 1 / (m : ℝ) := by
  sorry

/-- **Formula (3.1.16)** (§3.1, l. 2091; cited at P1 l. 2525). For `g ∈ Σ`, `|b_kl| ≤ 1/√(kl) ≤ 1`
(`k, l = 1, 2, …`). -/
theorem eq3_1_16 {g : ℂ → ℂ} (hg : IsClassSigma g) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ‖grunskyCoeff g k l‖ ≤ 1 / Real.sqrt ((k : ℝ) * l) ∧ 1 / Real.sqrt ((k : ℝ) * l) ≤ 1 := by
  sorry

/-- **Unlabelled claim** (§3.1, (3.1.18) at l. 2105 and (3.1.20) at l. 2129, steps of the proof of Theorem 3.1;
cited as results at P2 l. 3342). Let `g ∈ Σ`, `λ₁, …, λ_m ∈ ℂ`, and (3.1.17) `h(w) = Σ_{k=1}^m (λ_k/k) Φ_k(w)`.
Then (3.1.18) `h(g(z)) = Σ_{k=1}^m (λ_k/k) z^k + Σ_{k ≥ 1} d_k z^{-k}` (`|z| > 1`) with
`d_k = Σ_{l=1}^m b_kl λ_l`, and (3.1.20) `π⁻¹ ∬_E |h'(w)|² dΩ = Σ_{k=1}^m |λ_k|²/k - Σ_{k ≥ 1} k |d_k|²`.
Modelling: the area integral is the Lebesgue integral over the compact set `E = sigmaE g`; the conclusion includes
the convergence of `Σ k |d_k|²`. The book's hypothesis `h ≢ 0` is not needed here. -/
theorem eq3_1_20 {g : ℂ → ℂ} (hg : IsClassSigma g) (m : ℕ) (lam : ℕ → ℂ) {h : Polynomial ℂ}
    (hh : h = ∑ k ∈ Finset.Icc 1 m, Polynomial.C (lam k / k) * faberPoly (sigmaCoeff g) k) {d : ℕ → ℂ}
    (hd : ∀ k, d k = ∑ l ∈ Finset.Icc 1 m, grunskyCoeff g k l * lam l) :
    (∀ z : ℂ, 1 < ‖z‖ → HasSum (fun k : ℕ => d (k + 1) * z⁻¹ ^ (k + 1))
        (Polynomial.eval (g z) h - ∑ k ∈ Finset.Icc 1 m, lam k / k * z ^ k)) ∧
      Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ‖d (k + 1)‖ ^ 2) ∧
      π⁻¹ * ∫ w in sigmaE g, ‖Polynomial.eval w (Polynomial.derivative h)‖ ^ 2 =
        ∑ k ∈ Finset.Icc 1 m, ‖lam k‖ ^ 2 / (k : ℝ) - ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * ‖d (k + 1)‖ ^ 2 := by
  sorry

/-- **Theorem 3.2** (§3.1, l. 2136; cited at P1 l. 3181), inequality (3.1.21). If `g ∈ Σ` and `λ_k ∈ ℂ`
(`k = 1, 2, …`), then `Σ_{k ≥ 1} k |Σ_{l ≥ 1} b_kl λ_l|² ≤ Σ_{k ≥ 1} |λ_k|²/k`, provided that the last series
converges.
Modelling: the OCR places the tags (21) and (22) one display off; (21) is this inequality, as the proof and the
citations show. The conclusion includes the absolute convergence of the inner series (shown in the proof) and the
convergence of the outer one. -/
theorem thm3_2_a {g : ℂ → ℂ} (hg : IsClassSigma g) {lam : ℕ → ℂ}
    (hlam : Summable (fun k : ℕ => ‖lam (k + 1)‖ ^ 2 / ((k + 1 : ℕ) : ℝ))) :
    (∀ k : ℕ, 1 ≤ k → Summable (fun l : ℕ => ‖grunskyCoeff g k (l + 1) * lam (l + 1)‖)) ∧
      Summable (fun k : ℕ =>
        ((k + 1 : ℕ) : ℝ) * ‖∑' l : ℕ, grunskyCoeff g (k + 1) (l + 1) * lam (l + 1)‖ ^ 2) ∧
      ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * ‖∑' l : ℕ, grunskyCoeff g (k + 1) (l + 1) * lam (l + 1)‖ ^ 2 ≤
        ∑' k : ℕ, ‖lam (k + 1)‖ ^ 2 / ((k + 1 : ℕ) : ℝ) := by
  sorry

/-- **Theorem 3.2** (§3.1, l. 2136–2146; the Grunsky inequality, Grunsky 1939; cited at P1 l. 2309, 2430, 3727, 8416
and P2 l. 3218), inequality (3.1.22). If `g ∈ Σ` and `λ_k ∈ ℂ` (`k = 1, 2, …`), then
`|Σ_{k ≥ 1} Σ_{l ≥ 1} b_kl λ_k λ_l| ≤ Σ_{k ≥ 1} |λ_k|²/k`, provided that the last series converges.
Modelling: the book proves convergence, not absolute convergence, of the double series (l. 2152–2156), in the sense
of rectangular partial sums `Σ_{k ≤ m} Σ_{l ≤ n}`, `m, n → ∞` (decision D8): the partial sums tend to a limit `L`
along `atTop` on `ℕ × ℕ`, and `|L|` is bounded as stated. -/
theorem thm3_2_b {g : ℂ → ℂ} (hg : IsClassSigma g) {lam : ℕ → ℂ}
    (hlam : Summable (fun k : ℕ => ‖lam (k + 1)‖ ^ 2 / ((k + 1 : ℕ) : ℝ))) :
    ∃ L : ℂ, Tendsto (fun p : ℕ × ℕ => ∑ k ∈ Finset.Icc 1 p.1, ∑ l ∈ Finset.Icc 1 p.2,
        grunskyCoeff g k l * lam k * lam l) atTop (𝓝 L) ∧
      ‖L‖ ≤ ∑' k : ℕ, ‖lam (k + 1)‖ ^ 2 / ((k + 1 : ℕ) : ℝ) := by
  sorry

/-- **Definition** (the Grunsky operator, §3.1, (3.1.26), l. 2198–2203; used in §9.4). The Grunsky operator of `g`
is `B : (z_k) ↦ (Σ_{l ≥ 1} √(kl) b_kl z_l)_k` on the Hilbert space of square-summable sequences `(z_k)_{k ≥ 1}`.
Modelling: a pointwise map on all sequences `ℕ → ℂ`, indexed from `1` (the entry `0` is not used: the factor
`√(kl)` makes its contributions `0`); the series is a `tsum`, whose junk value `0` for a divergent series does not
occur on square-summable sequences for `g ∈ Σ` by (3.1.21). No statement of this chapter uses the operator: "`B` is
unitary" is stated through the book's equivalent (3.1.29) in `cor3_1` (decision D4). -/
def grunskyOperator (g : ℂ → ℂ) (z : ℕ → ℂ) : ℕ → ℂ :=
  fun k => ∑' l : ℕ, (Real.sqrt ((k : ℝ) * l) : ℂ) * grunskyCoeff g k l * z l

/-- **Corollary 3.1** (§3.1, l. 2226; Milin, Pommerenke, Pederson). For `g ∈ Σ`, the Grunsky operator is unitary if
and only if `area E = 0`.
Modelling: by (3.1.26) and (3.1.27) the operator is unitary if and only if (3.1.29)
`Σ_{k ≥ 1} k b_kj conj(b_kl) = 0` for `j ≠ l` and `= 1/l` for `j = l` (l. 2219, the book's own reformulation); this
condition is stated for all `j, l ≥ 1`, with the convergence of the series (decision D4). -/
theorem cor3_1 {g : ℂ → ℂ} (hg : IsClassSigma g) :
    (∀ j l : ℕ, 1 ≤ j → 1 ≤ l →
        HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℂ) * grunskyCoeff g (k + 1) j * conj (grunskyCoeff g (k + 1) l))
          (if j = l then 1 / (l : ℂ) else 0)) ↔
      volume (sigmaE g) = 0 := by
  sorry

/-- **Definition** (the Grunsky matrix, §3.1, (3.1.31), l. 2236–2241). The Grunsky matrix of order `m` of `g` is
`𝔅 = (√(kl) b_kl)_{k, l = 1, …, m}`.
Modelling: rows and columns indexed by `Fin m`, the entry `(k, l)` standing for the indices `k + 1`, `l + 1`. -/
def grunskyMatrix (g : ℂ → ℂ) (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun k l =>
    (Real.sqrt (((k.1 + 1 : ℕ) : ℝ) * ((l.1 + 1 : ℕ) : ℝ)) : ℂ) * grunskyCoeff g (k.1 + 1) (l.1 + 1)

/-- **Corollary 3.2** (§3.1, l. 2244). If `g ∈ Σ`, then the Grunsky matrix of order `m` (`m = 1, 2, …`) can be
written as (3.1.32) `𝔅 = 𝔘ᵀ diag(d₁, …, d_m) 𝔘` with `𝔘` unitary and `|d_k| ≤ 1` (`k = 1, …, m`). -/
theorem cor3_2 {g : ℂ → ℂ} (hg : IsClassSigma g) (m : ℕ) :
    ∃ U ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ d : Fin m → ℂ, (∀ k, ‖d k‖ ≤ 1) ∧
      grunskyMatrix g m = U.transpose * Matrix.diagonal d * U := by
  sorry

end Pommerenke1975
