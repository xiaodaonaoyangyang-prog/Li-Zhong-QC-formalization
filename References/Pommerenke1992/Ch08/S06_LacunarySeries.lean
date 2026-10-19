import References.Pommerenke1992.Ch08.S05_GrowthOfBlochFunctions

/-!
# Pommerenke 1992, Ch. 8 §8.6 Lacunary Series

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 8 *Integral Means*, §8.6; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3…` (P2), lines 87–390.

* Definition (Hadamard gaps, (8.6.1), "We say"; cited at P2 l. 133, 255) — `IsHadamardGapSeries`, `HasHadamardGaps`
* Proposition 8.12 (cited at P2 l. 2871) — `prop8_12_a`, `prop8_12_b`
* Proposition 8.13 ((8.6.3); cited at P2 l. 239, 327 and in Exercise 8.6.3) — `prop8_13`
* Definition (the constant `B_q`, (8.6.4), in Proposition 8.14; used at P2 l. 183, 191, 205, 247, 363) —
  `lacunaryConstB`
* Proposition 8.14 ((8.6.5); cited at P2 l. 185, 349, 2871; its proof is cited at P2 l. 363) — `prop8_14`
* Unlabelled (§8.6, P2 l. 169: the table "Upper bound for `B_q`" of Proposition 8.14; the row `q = 2` is used at
  P2 l. 349 and 2871, the row `q = 15` at P2 l. 247 and 363) — `prop8_14_table`
* Definition (the map (8.6.6); used in Proposition 8.15, at P2 l. 2020 and in Exercise 8.6.1) — `lacunaryMap`
* Definition (the modified Bessel functions `I_n`, (8.6.7); used in Proposition 8.15 and at P2 l. 239, 247–253) —
  `modBesselI`
* Formula (8.6.8) (quoted from MaObSo66; cited at P2 l. 233) — `eq8_6_8`
* Proposition 8.15 (Roh89; (8.6.9); cited at P2 l. 253) — `prop8_15`
* Formula (8.6.11) (HaLi26, Binm69, quoted; cited at P2 l. 355) — `eq8_6_11`
* Formula (8.6.12) (Zyg68, quoted; cited at P2 l. 2871) — `eq8_6_12`
* Definition (`b(r)`, (8.6.18); used in (8.6.21), (8.6.22) and at P2 l. 363) — `lacunarySpread`
* Formula (8.6.22) (the law of the iterated logarithm for lacunary series, Wei59, quoted; cited at P2 l. 369 and 2939,
  by name at P2 l. 2020) — `eq8_6_22`

Not items (DESIGN §3): (8.6.2) (immediate from (8.6.1); used in the proofs of Propositions 8.12 and 8.13); the remark
that lacunary series are useful for constructing pathological conformal maps (GnHPo86); "(6) maps `𝔻` conformally
onto a quasidisk if `|b| < 1/B_q`" (P2 l. 185–191; U−, immediate from Proposition 8.14 with `b₀ = 0`, `b_k = b`);
(8.6.10) and the proof of Theorem 8.6 (proofs); "every function in `B₀` has finite radial limits on a set of Hausdorff
dimension 1" (P2 l. 263; a forward reference to (11.2.7)); "(12) implies `g ∈ Hᵖ` for every `p < ∞`", (8.6.13) and
"(12) implies `g ∈ VMOA`" (Zyg68, HaSa90; quoted, not cited); (8.6.14) (Sid27), (8.6.15) (GnPo83; printed with `f'`
where the series is `g` [misprint?]), Murai's theorem (Mur81; it is Exercise 8.6.5), the open problem on
`g(𝔻) ≠ ℂ` under weaker gap assumptions and the theta-function identity (8.6.16) (quoted or examples, not cited as
results: the later "(14)" names the condition `Σ|b_k| < ∞`, not Sidon's theorem); (8.6.17) (Mur83) and the remark on
the Privalov uniqueness theorem (P2 l. 299–305; quoted, not cited); the probabilistic material of P2 l. 307–333: the
weakly dependent random variables (Kah85), the Brownian approximation (8.6.19), (8.6.20) (PhSt75; the time scale
`2b(r_t)² = t` [misprint?]; `Var Re g(r_t ζ) = b(r_t)²/2` asks for `b(r_t)² = 2t`) and the central limit theorem
(8.6.21) (Zyg68; false as printed for every `x ≤ 0`, where the left side tends to `0`; the version for `|g|` has the
limit `Λ(E)(1 - e^{-x²})` for `x ≥ 0`, and the printed right side is the central limit theorem for `Re g` at the
scale `b(r)/√2` [misprint?]), all quoted and not cited, with no probability library; part "3.", the proofs of
Proposition 4.12 (with (8.6.23)) and of the second part of Theorem 8.10; Exercises 8.6.1–8.6.7.

**Conventions.** As in §8.1–§8.5. "`g` is given by (8.6.1)" is `IsHadamardGapSeries g q b n`: the data `q > 1`,
`b : ℕ → ℂ` (`b 0 = b₀`) and `n : ℕ → ℕ` (`n k = n_k` for `k ≥ 1`; `n 0` is unused) are exposed, since
Proposition 8.13 needs `r_j = 1 - 1/n_j` and (8.6.22) needs `b(r)`, and the statements hold for every representation.
The representation of `g` is unique except at indices with `b_k = 0`, which change neither `sup |b_k|`, nor `b_k → 0`,
nor `Σ |b_k|²`, nor `b(r)`. The standing assumption of part 2 (P2 l. 255, "we assume throughout that `g` is given by
(1)") is made explicit in (8.6.11), (8.6.12) and (8.6.22). `B_q` is named `lacunaryConstB`, apart from the unrelated
"(B_q) condition" of Chapter 7.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane unitDisc IsConformalOnto)

/-- The data of a Hadamard gap series (helper for (8.6.1)): `g(z) = b₀ + Σ_{k≥1} b_k z^{n_k}` for `z ∈ 𝔻`, with
`n_{k+1}/n_k ≥ q` (`k = 1, 2, …`) and a real `q > 1`.
Modelling: `b 0 = b₀`, and `n k = n_k` for `k ≥ 1` (`n 0` is unused); `n_1 ≥ 1`, so that the exponents are positive,
the ratios are defined and the exponents are strictly increasing; the series converges on `𝔻` (`HasSum`), so its
radius of convergence is `≥ 1` and `g` is analytic in `𝔻`. -/
def IsHadamardGapSeries (g : ℂ → ℂ) (q : ℝ) (b : ℕ → ℂ) (n : ℕ → ℕ) : Prop :=
  1 < q ∧ 1 ≤ n 1 ∧ (∀ k : ℕ, 1 ≤ k → q * (n k : ℝ) ≤ (n (k + 1) : ℝ)) ∧
    ∀ z ∈ unitDisc, HasSum (fun k : ℕ => b (k + 1) * z ^ n (k + 1)) (g z - b 0)

/-- **Definition (8.6.1)** (§8.6, "We say"; P2 l. 89–95; cited at P2 l. 133, 255). The function `g` has Hadamard gaps
if (8.6.1) `g(z) = b₀ + Σ_{k≥1} b_k z^{n_k}`, `n_{k+1}/n_k ≥ q` (`k = 1, 2, …`) for some real `q > 1`. -/
def HasHadamardGaps (g : ℂ → ℂ) : Prop :=
  ∃ (q : ℝ) (b : ℕ → ℂ) (n : ℕ → ℕ), IsHadamardGapSeries g q b n

/-- **Proposition 8.12** (§8.6; P2 l. 97–105; cited at P2 l. 2871), first part. If `g` has Hadamard gaps, then
`g ∈ B ⟺ sup |b_k| < ∞`.
Modelling: for every representation (8.6.1) of `g`; `sup |b_k| < ∞` is the boundedness of `(|b_k|)` (the term `b₀`
does not matter). -/
theorem prop8_12_a {g : ℂ → ℂ} {q : ℝ} {b : ℕ → ℂ} {n : ℕ → ℕ} (hg : IsHadamardGapSeries g q b n) :
    IsBloch g ↔ BddAbove (range fun k => ‖b k‖) := by
  sorry

/-- **Proposition 8.12** (§8.6), second part. If `g` has Hadamard gaps, then `g ∈ B₀ ⟺ b_k → 0` as `k → ∞`.
Modelling: for every representation (8.6.1) of `g`; `B₀` is `IsLittleBloch` ((4.2.22)). -/
theorem prop8_12_b {g : ℂ → ℂ} {q : ℝ} {b : ℕ → ℂ} {n : ℕ → ℕ} (hg : IsHadamardGapSeries g q b n) :
    IsLittleBloch g ↔ Tendsto b atTop (𝓝 0) := by
  sorry

/-- **Proposition 8.13** (§8.6; P2 l. 133–139; cited at P2 l. 239, 327 and in Exercise 8.6.3). Let the lacunary
series `g` be given by (8.6.1). If `r_j = 1 - 1/n_j` for `j = 1, 2, …`, then (8.6.3)
`|b₀ + Σ_{k=1}^{j} b_k ζ^{n_k} - g(rζ)| ≤ K(q) sup |b_k|` (`ζ ∈ 𝕋`) for `r_j ≤ r ≤ r_{j+1}`, where `K(q)` depends
only on `q > 1`.
Modelling: `∀ q > 1, ∃ K, ∀ g b n j r ζ`. The supremum is over `k ≥ 1` (`b₀` cancels, and the proof normalizes
`|b_k| ≤ 1`); it is replaced by any bound `M` of the `|b_k|`, `k ≥ 1`, which is equivalent for `K ≥ 0` and makes the
boundedness of `(b_k)` explicit. -/
theorem prop8_13 {q : ℝ} (hq : 1 < q) :
    ∃ K : ℝ, ∀ (g : ℂ → ℂ) (b : ℕ → ℂ) (n : ℕ → ℕ), IsHadamardGapSeries g q b n →
      ∀ M : ℝ, (∀ k : ℕ, 1 ≤ k → ‖b k‖ ≤ M) →
      ∀ j : ℕ, 1 ≤ j → ∀ r : ℝ, 1 - 1 / (n j : ℝ) ≤ r → r ≤ 1 - 1 / (n (j + 1) : ℝ) →
        ∀ ζ ∈ sphere (0 : ℂ) 1, ‖b 0 + ∑ k ∈ Finset.Icc 1 j, b k * ζ ^ n k - g (r * ζ)‖ ≤ K * M := by
  sorry

/-- **Definition (8.6.4)** (§8.6, in Proposition 8.14; P2 l. 155–161; used at P2 l. 183, 191, 205, 247, 363). For
`q = 2, 3, …`, `B_q = max_{0≤x≤1} 2 Σ_{n=-∞}^{∞} q^{n+x} exp(-q^{n+x})`.
Modelling: the supremum over `x ∈ [0, 1]`. For `q ≥ 2` the series over `n ∈ ℤ` converges, and its sum is continuous
and `1`-periodic in `x` (P2 l. 171), so the supremum is the book's maximum. For `q = 0, 1` the value is junk; every
statement assumes `q ≥ 2`. -/
def lacunaryConstB (q : ℕ) : ℝ :=
  sSup ((fun x : ℝ => 2 * ∑' m : ℤ, (q : ℝ) ^ ((m : ℝ) + x) * Real.exp (-((q : ℝ) ^ ((m : ℝ) + x)))) '' Icc 0 1)

/-- **Proposition 8.14** (§8.6; P2 l. 155–167; cited at P2 l. 185, 349, 2871; its proof is cited at P2 l. 363). Let
`q = 2, 3, …` and `B_q` be defined by (8.6.4). If (8.6.5) `log f'(z) = Σ_{k≥0} b_k z^{q^k}` with
`sup_k |b_k| < 1/B_q`, then `f` maps `𝔻` conformally onto a quasidisk.
Modelling: `f` is analytic in `𝔻`, and `log f'` is a function `L` with `exp ∘ L = f'` on `𝔻` given by the series for
`z ∈ 𝔻`; `sup_k |b_k| < 1/B_q` is a bound `|b_k| ≤ M < 1/B_q` for all `k`; "onto a quasidisk" is the form of
`cor5_23`. -/
theorem prop8_14 {q : ℕ} (hq : 2 ≤ q) {f L : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hLf : ∀ z ∈ unitDisc, exp (L z) = deriv f z) {b : ℕ → ℂ}
    (hLb : ∀ z ∈ unitDisc, HasSum (fun k : ℕ => b k * z ^ (q ^ k)) (L z)) {M : ℝ} (hM : ∀ k : ℕ, ‖b k‖ ≤ M)
    (hMB : M < 1 / lacunaryConstB q) :
    IsConformalOnto f unitDisc (f '' unitDisc) ∧ IsQuasidisk (f '' unitDisc) := by
  sorry

/-- **Unlabelled claim** (§8.6, P2 l. 169: the table "Upper bound for `B_q`" of Proposition 8.14, obtained (P2 l. 183)
"by splitting `[0, 1]` into 128 subintervals"; the row `q = 2` is used at P2 l. 349 and 2871, the row `q = 15` at
P2 l. 247 and 363). `B_2 ≤ 2.8913`, `B_3 ≤ 1.8291`, `B_4 ≤ 1.4614`, `B_5 ≤ 1.2754`, `B_6 ≤ 1.1642`,
`B_7 ≤ 1.0907`, `B_8 ≤ 1.0386`, `B_9 ≤ 0.9998`, `B_10 ≤ 0.9699`, `B_11 ≤ 0.9460`, `B_12 ≤ 0.9266`,
`B_13 ≤ 0.9104`, `B_14 ≤ 0.8968`, `B_15 ≤ 0.8851`, `B_20 ≤ 0.8455`, `B_30 ≤ 0.8074`, `B_40 ≤ 0.7890`,
`B_50 ≤ 0.7782`, `B_80 ≤ 0.7621`, and the row `q = ∞`: `0.7358`.
Modelling: the 19 finite rows as `≤` (each checked numerically as an upper bound, e.g. `B_2 = 2.8854…`,
`B_15 = 0.8819…`, `B_80 = 0.7612…`). The row `∞` is not a value of (8.6.4), which is defined for `q = 2, 3, …`; it is
the limit `2/e = 0.73576…` of `B_q` as `q → ∞` (`B_q` decreases to it: `B_1000 = 0.7378…`), rounded up, and is stated
as `limsup_{q→∞} B_q ≤ 0.7358` (an `EReal` `limsup`). -/
theorem prop8_14_table :
    lacunaryConstB 2 ≤ 2.8913 ∧ lacunaryConstB 3 ≤ 1.8291 ∧ lacunaryConstB 4 ≤ 1.4614 ∧
      lacunaryConstB 5 ≤ 1.2754 ∧ lacunaryConstB 6 ≤ 1.1642 ∧ lacunaryConstB 7 ≤ 1.0907 ∧
      lacunaryConstB 8 ≤ 1.0386 ∧ lacunaryConstB 9 ≤ 0.9998 ∧ lacunaryConstB 10 ≤ 0.9699 ∧
      lacunaryConstB 11 ≤ 0.9460 ∧ lacunaryConstB 12 ≤ 0.9266 ∧ lacunaryConstB 13 ≤ 0.9104 ∧
      lacunaryConstB 14 ≤ 0.8968 ∧ lacunaryConstB 15 ≤ 0.8851 ∧ lacunaryConstB 20 ≤ 0.8455 ∧
      lacunaryConstB 30 ≤ 0.8074 ∧ lacunaryConstB 40 ≤ 0.7890 ∧ lacunaryConstB 50 ≤ 0.7782 ∧
      lacunaryConstB 80 ≤ 0.7621 ∧
      limsup (fun q : ℕ => (lacunaryConstB q : EReal)) atTop ≤ ((0.7358 : ℝ) : EReal) := by
  sorry

/-- **Definition (8.6.6)** (§8.6; P2 l. 185–189; used in Proposition 8.15, at P2 l. 2020 and in Exercise 8.6.1). For
`q = 2, 3, …` and `b ∈ ℂ`, `f(z) = ∫₀^z exp(b Σ_{k≥1} ζ^{q^k}) dζ = z + …`.
Modelling: the integral along the segment `[0, z]`, `f(z) = z ∫₀¹ exp(b Σ_{k≥1} (tz)^{q^k}) dt`, used for `z ∈ 𝔻`,
where the series converges locally uniformly; for `q = 0, 1` the value is junk, and no statement uses it. -/
def lacunaryMap (q : ℕ) (b : ℂ) (z : ℂ) : ℂ :=
  z * ∫ t in (0 : ℝ)..1, exp (b * ∑' k : ℕ, ((t : ℂ) * z) ^ (q ^ (k + 1)))

/-- **Definition (8.6.7)** (§8.6; MaObSo66, pp. 66, 70; P2 l. 191–197; used in Proposition 8.15 and at P2 l. 239,
247–253). The modified Bessel functions `I_n(x) = (x/2)ⁿ Σ_{ν≥0} x^{2ν}/(2^{2ν} ν! (ν + n)!)`, `n = 0, 1, …`.
Modelling: for real `x` (the series converges for every `x`); Mathlib has only the Bessel functions of the first kind,
and no comparison theorem is stated. -/
def modBesselI (n : ℕ) (x : ℝ) : ℝ :=
  (x / 2) ^ n * ∑' ν : ℕ, x ^ (2 * ν) / (2 ^ (2 * ν) * (ν.factorial : ℝ) * ((ν + n).factorial : ℝ))

/-- **Formula (8.6.8)** (§8.6; quoted from MaObSo66; P2 l. 197–201; cited at P2 l. 233, in the proof of
Proposition 8.15). The modified Bessel functions appear in the Fourier series
`exp(x cos ϑ) = I₀(x) + 2 Σ_{n≥1} I_n(x) cos nϑ`.
Modelling: `x, ϑ ∈ ℝ`; the series converges (`HasSum`, no `tsum` junk) to `exp(x cos ϑ) - I₀(x)`. -/
theorem eq8_6_8 (x ϑ : ℝ) :
    HasSum (fun n : ℕ => 2 * modBesselI (n + 1) x * Real.cos (((n : ℝ) + 1) * ϑ))
      (Real.exp (x * Real.cos ϑ) - modBesselI 0 x) := by
  sorry

/-- **Proposition 8.15** (§8.6; Roh89; P2 l. 203–211; cited at P2 l. 253, in the proof of Theorem 8.6). Let `f` be the
conformal map defined by (8.6.6) with `q` odd and `0 < b < 1/B_q`. If `p ∈ ℝ`, then (8.6.9)
`∫_𝕋 |f'(rζ)|^p |dζ| ≥ c (1 - r)^{-a}` (`0 < r < 1`), where `c > 0` and `a = log I₀(bp)/log q`.
Modelling: `q ∈ {3, 5, 7, …}` (odd, among `q = 2, 3, …`); `b` is real; `c` depends on `q`, `b` and `p` (`∃ c > 0`
after `p`); `∫_𝕋 … |dζ| = 2π · circleAverage`. `I₀(bp) ≥ 1` and `log q > 0`, so `a ≥ 0` is a genuine real number,
and `f' = exp(b Σ z^{q^k})` has no zeros, so `|f'|^p` sees no junk. -/
theorem prop8_15 {q : ℕ} (hq : 2 ≤ q) (hodd : Odd q) {b : ℝ} (hb0 : 0 < b) (hbB : b < 1 / lacunaryConstB q)
    (p : ℝ) :
    ∃ c > (0 : ℝ), ∀ r : ℝ, 0 < r → r < 1 →
      c * (1 - r) ^ (-(Real.log (modBesselI 0 (b * p)) / Real.log q)) ≤
        2 * π * Real.circleAverage (fun z => ‖deriv (lacunaryMap q b) z‖ ^ p) 0 r := by
  sorry

/-- **Formula (8.6.11)** (§8.6; HaLi26, Binm69, quoted; P2 l. 255–263; cited at P2 l. 355, in the proof of
Proposition 4.12). Let `g` be given by (8.6.1). If `g` has a finite asymptotic value (see (4.2.14)) at some point of
`𝕋`, then (8.6.11) `b_k → 0` as `k → ∞`, and thus `g ∈ B₀`.
Modelling: `HasAsymptoticValue` (§4.2) with a finite value `w ∈ ℂ` (it includes `ζ ∈ 𝕋`); the conclusion "and thus
`g ∈ B₀`" (by Proposition 8.12) is included. -/
theorem eq8_6_11 {g : ℂ → ℂ} {q : ℝ} {b : ℕ → ℂ} {n : ℕ → ℕ} (hg : IsHadamardGapSeries g q b n)
    (hav : ∃ ζ w : ℂ, HasAsymptoticValue g ζ (w : ExtPlane)) :
    Tendsto b atTop (𝓝 0) ∧ IsLittleBloch g := by
  sorry

/-- **Formula (8.6.12)** (§8.6; Zyg68, I, p. 203, quoted; P2 l. 265–269; cited at P2 l. 2871, "compare (8.6.12)"). Let
`g` be given by (8.6.1). If `g` has finite radial limits on a set of positive measure, then (8.6.12)
`Σ_k |b_k|² < ∞`.
Modelling: a set `A ⊆ 𝕋` with `Λ(A) > 0` (`circleMeasure`, an outer measure, so `A` need not be measurable) at each
point of which the radial limit (`HasRadialLimit`, §2.5) exists and is finite. -/
theorem eq8_6_12 {g : ℂ → ℂ} {q : ℝ} {b : ℕ → ℂ} {n : ℕ → ℕ} (hg : IsHadamardGapSeries g q b n) {A : Set ℂ}
    (hAT : A ⊆ sphere 0 1) (hA : 0 < circleMeasure A)
    (hlim : ∀ ζ ∈ A, ∃ w : ℂ, HasRadialLimit (fun z => (g z : ExtPlane)) ζ w) :
    Summable (fun k : ℕ => ‖b k‖ ^ 2) := by
  sorry

/-- **Definition (8.6.18)** (§8.6; P2 l. 309–315; used in (8.6.21), (8.6.22) and at P2 l. 363). For `g` given by
(8.6.1) with bounded `(b_k)`: `b(r)² = Σ_{k≥1} |b_k|² r^{2n_k}`, `0 ≤ r < 1`.
Modelling: `b(r)` is the nonnegative square root, built from the representation data `b`, `n` of
`IsHadamardGapSeries`; the series is summable for bounded `(b_k)` and `0 ≤ r < 1` (the `n_k` are distinct), and the
value is junk (the `tsum` of a non-summable family) only outside that range, which no statement uses. -/
def lacunarySpread (b : ℕ → ℂ) (n : ℕ → ℕ) (r : ℝ) : ℝ :=
  Real.sqrt (∑' k : ℕ, ‖b (k + 1)‖ ^ 2 * r ^ (2 * n (k + 1)))

/-- **Formula (8.6.22)** (§8.6; the law of the iterated logarithm, Wei59, p. 469, quoted; P2 l. 335–339; cited at
P2 l. 369 and 2939, by name at P2 l. 2020). Let `g` be given by (8.6.1) with `b₀ = 0` and `(b_k)` bounded, and let
(8.6.18) `b(r) → ∞` as `r → 1-`. Then `limsup_{r→1} |g(rζ)|/(b(r) √(log log b(r))) = 1` for almost all `ζ ∈ 𝕋`.
Modelling: the standing assumptions of P2 l. 255, 309 and 329 are explicit hypotheses; `ζ = e^{it}` for almost every
`t ∈ ℝ`; the `limsup` over `r → 1-` is taken in `EReal` (the denominator is positive for `r` near `1`, as
`b(r) → ∞`). -/
theorem eq8_6_22 {g : ℂ → ℂ} {q : ℝ} {b : ℕ → ℂ} {n : ℕ → ℕ} (hg : IsHadamardGapSeries g q b n) (hb0 : b 0 = 0)
    (hbdd : BddAbove (range fun k => ‖b k‖)) (hspread : Tendsto (lacunarySpread b n) (𝓝[<] 1) atTop) :
    ∀ᵐ t : ℝ, limsup (fun r : ℝ => ((‖g (r * exp (t * I))‖ /
      (lacunarySpread b n r * Real.sqrt (Real.log (Real.log (lacunarySpread b n r)))) : ℝ) : EReal)) (𝓝[<] 1) = 1 := by
  sorry

end Pommerenke1992
