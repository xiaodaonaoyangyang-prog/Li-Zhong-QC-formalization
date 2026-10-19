import References.Pommerenke1992.Ch08.S01_Overview

/-!
# Pommerenke 1992, Ch. 8 §8.2 Univalent Functions

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 8 *Integral Means*, §8.2; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…` (P1), lines 7461–7584.

* Hardy's identity ((8.2.2), named; cited at P1 l. 7495, 7820, 8078 and in Exercise 8.2.1; hypotheses corrected) —
  `hardy_identity`
* Definition (the maximum modulus `M(r)`, (8.2.3), in Proposition 8.1; used at P1 l. 7950 and in Exercise 8.2.3) —
  `maxModulus`
* Proposition 8.1 ((8.2.4), (8.2.5); cited at P1 l. 7537, 7655, 7962, 7964) — `prop8_1_a`, `prop8_1_b`
* Theorem 8.2 (Prawitz, Pra27; (8.2.6), (8.2.7); cited at P1 l. 710, 7962) — `thm8_2_a`, `thm8_2_b`
* Formula (8.2.8) (cited at P1 l. 7655, 7675) — `eq8_2_8_a`, `eq8_2_8_b`
* Formula (8.2.10) (quoted from MaObSo66; cited at P1 l. 7629 and, as "(8.2.9)", at P1 l. 7689; the second case
  corrected) — `eq8_2_10_a`, `eq8_2_10_b`

Not items (DESIGN §3): (8.2.1) (the calculation behind Hardy's identity, not cited); the remark that the integral
means are maximized in `S` by the Koebe function (Bae74, P1 l. 7543; quoted, not cited); (8.2.9), the Legendre-function
formula `(1/2π)∫₀^{2π} |1 - re^{it}|^{-q} dt = (1 - r²)^{-q/2} P_{-q/2}((1 + r²)/(1 - r²))` (MaObSo66, P1 l. 7545–7549):
omitted (U−), since its one citation (P1 l. 7689, in the proof of Theorem 8.4) uses the asymptotics (8.2.10), and
Mathlib has no Legendre functions; the sharpness remark on the maps `(1 - z)^{-α}` (P1 l. 7561; not cited);
Exercises 8.2.1–8.2.4 (Exercise 8.2.1 is cited in the proof of Theorem 8.5, P1 l. 7826).

**Conventions.** As in §8.1 (`Ch08/S01_Overview`). The integral means `∫₀^{2π} |g(re^{it})|^p dt` are
`2 * π * Real.circleAverage (fun z => ‖g z‖ ^ p) 0 r`; the book's `(1/2π) ∫₀^{2π}` of (8.2.10) is
`Real.circleAverage` itself. "`f(z) = O((1 - |z|)^{-α})` as `|z| → 1`" is `Asymptotics.IsBigO` along
`comap (fun z => ‖z‖) (𝓝[<] 1)` (the points `z ∈ 𝔻` with `|z| → 1`); `r → 1` is `𝓝[<] 1`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (unitDisc)

/-- **Hardy's identity** (§8.2, (8.2.2), named; P1 l. 7463–7473; cited at P1 l. 7495, 7820, 8078). Let `g` be analytic
in `𝔻` and `p ∈ ℝ`. Then
`d/dr (r d/dr ∫₀^{2π} |g(re^{it})|^p dt) = p² r ∫₀^{2π} |g(re^{it})|^{p-2} |g'(re^{it})|² dt`.
[CORRECTION] The book states the identity for every analytic `g` and every real `p`. At a radius `r` where `g` has a
zero `z₀` and `p ≤ 1` the right-hand side diverges (near a simple zero the integrand is `≍ |z - z₀|^{p-2}`, which is
not integrable along the circle), so a hypothesis is needed: the identity is stated for `0 < r < 1` when `g` has no
zeros on `|z| = r`, or when `p` is an even integer `≥ 2` (then `|g|^p = (g ḡ)^{p/2}` is real-analytic). This is a
simple sufficient condition that covers the three uses, not the exact range of validity (the identity also holds, for
instance, for `p > 1` with zeros on the circle, which no use needs; the degenerate radius `r = 0` is left out): `g = f`
univalent with `f(0) = 0` on the circles `|z| = s > 0` (Proposition 8.1), `g = f'` (zero-free, Theorem 8.5), and
`g ∈ B` with `p = 2n + 2` (Theorem 8.9).
Modelling: the mean `∫₀^{2π} |g(se^{it})|^p dt` is `2π · circleAverage (|g|^p) 0 s`. The conclusion says that the
mean has a derivative `D(s)` in `s` for `s` near `r`, and that `s ↦ s D(s)` has the stated derivative at `r`
(`HasDerivAt`, so that no junk value of `deriv` is used). -/
theorem hardy_identity {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) {p r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hgp : (∀ z ∈ sphere (0 : ℂ) r, g z ≠ 0) ∨ ∃ m : ℕ, 1 ≤ m ∧ p = 2 * m) :
    ∃ D : ℝ → ℝ,
      (∀ᶠ ρ : ℝ in 𝓝 r,
        HasDerivAt (fun s : ℝ => 2 * π * Real.circleAverage (fun z => ‖g z‖ ^ p) 0 s) (D ρ) ρ) ∧
      HasDerivAt (fun s : ℝ => s * D s)
        (p ^ 2 * r * (2 * π * Real.circleAverage (fun z => ‖g z‖ ^ (p - 2) * ‖deriv g z‖ ^ 2) 0 r)) r := by
  sorry

/-- **Definition (8.2.3)** (§8.2, in Proposition 8.1; P1 l. 7477; used at P1 l. 7950 and in Exercise 8.2.3). The
maximum modulus `M(r) = max_{|z| = r} |f(z)|` for `0 ≤ r < 1`.
Modelling: the supremum of `|f|` over the circle `|z| = r`; for `f` continuous in `𝔻` and `0 ≤ r < 1` it is a maximum
(by compactness), with `M(0) = |f(0)|`. Outside this range the value is junk, and no statement uses it there. -/
def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' sphere 0 r)

/-- **Proposition 8.1** (§8.2; P1 l. 7475–7493; cited at P1 l. 7537, 7655, 7962, 7964), first part. Let `f` map `𝔻`
conformally into `ℂ` and let `M(r) = max_{|z|=r} |f(z)|` (8.2.3). If `f(0) = 0` and `p > 0`, then (8.2.4)
`∫₀^{2π} |f(re^{it})|^p dt ≤ 2πp ∫₀^r M(ρ)^p ρ^{-1} dρ`.
Modelling: `0 ≤ r < 1`; the constant `2πp` belongs to the book's normalization `∫₀^{2π} dt` (no `1/2π`), which is
written `2π · circleAverage`. The integrand `M(ρ)^p ρ^{-1}` is continuous on `(0, r]` and `O(ρ^{p-1})` as `ρ → 0`
(Theorem 1.3), hence integrable. -/
theorem prop8_1_a {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) (hf0 : f 0 = 0)
    {p : ℝ} (hp : 0 < p) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    2 * π * Real.circleAverage (fun z => ‖f z‖ ^ p) 0 r ≤
      2 * π * p * ∫ ρ in (0 : ℝ)..r, maxModulus f ρ ^ p * ρ⁻¹ := by
  sorry

/-- **Proposition 8.1** (§8.2), second part. Let `f` map `𝔻` conformally into `ℂ` with `f(0) = 0`, and let `p > 0`.
Then, for `1/2 ≤ r < 1`, (8.2.5)
`∫₀^{2π} |f(re^{it})|^{p-2} |f'(re^{it})|² dt ≤ K(p) M(r)^p/(1 - r) ≤ K(p) |f'(0)|^p/(1 - r)^{2p+1}`,
where `K(p)` depends only on `p`.
Modelling: `∀ p > 0, ∃ K, ∀ f r`. The only zero of `f` is `0`, so the power `|f|^{p-2}` sees no zero on `|z| = r`. -/
theorem prop8_1_b {p : ℝ} (hp : 0 < p) :
    ∃ K : ℝ, ∀ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc → InjOn f unitDisc → f 0 = 0 →
      ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
        2 * π * Real.circleAverage (fun z => ‖f z‖ ^ (p - 2) * ‖deriv f z‖ ^ 2) 0 r ≤
            K * maxModulus f r ^ p / (1 - r) ∧
          K * maxModulus f r ^ p / (1 - r) ≤ K * ‖deriv f 0‖ ^ p / (1 - r) ^ (2 * p + 1) := by
  sorry

/-- **Theorem 8.2** (§8.2; Prawitz, Pra27; P1 l. 7523–7535; cited at P1 l. 710 and 7962), first part. Let `f` map `𝔻`
conformally into `ℂ` and suppose that (8.2.6) `f(z) = O((1 - |z|)^{-α})` as `|z| → 1`, where `0 ≤ α ≤ 2`. If
`p > 1/α`, then (8.2.7) `∫₀^{2π} |f(re^{it})|^p dt = O(1/(1 - r)^{αp-1})` as `r → 1`.
Modelling: "`p > 1/α`" is written `αp > 1`, so that `α = 0` (where the condition is void) needs no division; the
growth condition is taken along `|z| → 1` in `𝔻`, the conclusion along `r → 1-`. -/
theorem thm8_2_a {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {α : ℝ} (hα0 : 0 ≤ α)
    (hα2 : α ≤ 2) (hgr : Asymptotics.IsBigO (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) f (fun z => (1 - ‖z‖) ^ (-α)))
    {p : ℝ} (hp : 1 < α * p) :
    Asymptotics.IsBigO (𝓝[<] 1) (fun r : ℝ => 2 * π * Real.circleAverage (fun z => ‖f z‖ ^ p) 0 r)
      (fun r : ℝ => 1 / (1 - r) ^ (α * p - 1)) := by
  sorry

/-- **Theorem 8.2** (§8.2; Prawitz), second part. Under the hypotheses of `thm8_2_a` ((8.2.6), `0 ≤ α ≤ 2`): if
`0 < p < 1/α`, then `f` belongs to the Hardy space `Hᵖ`.
Modelling: "`p < 1/α`" is written `αp < 1` (every `p > 0` when `α = 0`); `Hᵖ` membership is
`GarnettMarshall2005.MemHardy (ENNReal.ofReal p) f` (GM's (A.1), without `1/2π`, which does not affect
membership). -/
theorem thm8_2_b {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {α : ℝ} (hα0 : 0 ≤ α)
    (hα2 : α ≤ 2) (hgr : Asymptotics.IsBigO (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) f (fun z => (1 - ‖z‖) ^ (-α)))
    {p : ℝ} (hp0 : 0 < p) (hp : α * p < 1) :
    GarnettMarshall2005.MemHardy (ENNReal.ofReal p) f := by
  sorry

/-- **Formula (8.2.8)** (§8.2; P1 l. 7537–7543; cited at P1 l. 7655, 7675), first part. Since (8.2.6) with `α = 2`
holds for all conformal maps, every conformal map `f` of `𝔻` into `ℂ` satisfies
`∫₀^{2π} |f(re^{it})|^p dt = O(1/(1 - r)^{2p-1})` as `r → 1` for `p > 1/2` (compare Theorem 1.7). -/
theorem eq8_2_8_a {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {p : ℝ}
    (hp : 1 / 2 < p) :
    Asymptotics.IsBigO (𝓝[<] 1) (fun r : ℝ => 2 * π * Real.circleAverage (fun z => ‖f z‖ ^ p) 0 r)
      (fun r : ℝ => 1 / (1 - r) ^ (2 * p - 1)) := by
  sorry

/-- **Formula (8.2.8)** (§8.2), second part. Every conformal map `f` of `𝔻` into `ℂ` belongs to `Hᵖ` for `p < 1/2`.
Modelling: `0 < p < 1/2` (the Hardy spaces have `p > 0`); `Hᵖ` as in `thm8_2_b`. -/
theorem eq8_2_8_b {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {p : ℝ}
    (hp0 : 0 < p) (hp : p < 1 / 2) :
    GarnettMarshall2005.MemHardy (ENNReal.ofReal p) f := by
  sorry

/-- **Formula (8.2.10)** (§8.2; quoted from MaObSo66, p. 157, formula 10; P1 l. 7551–7559; cited at P1 l. 7629 and,
as "(8.2.9)", at P1 l. 7689), first case. As `r → 1 - 0`,
`(1/2π) ∫₀^{2π} |1 - re^{it}|^{-q} dt ∼ 2^{-q} π^{-1/2} Γ((1 - q)/2) Γ(1 - q/2)^{-1}` if `0 ≤ q < 1`.
Modelling: the book's `(1/2π) ∫₀^{2π} dt` is literally `circleAverage`; "`∼` a positive constant" is convergence to
that constant. -/
theorem eq8_2_10_a {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun r : ℝ => Real.circleAverage (fun z => ‖1 - z‖ ^ (-q)) 0 r) (𝓝[<] 1)
      (𝓝 ((2 : ℝ) ^ (-q) * π ^ (-(1 / 2 : ℝ)) * Real.Gamma ((1 - q) / 2) * (Real.Gamma (1 - q / 2))⁻¹)) := by
  sorry

/-- **Formula (8.2.10)** (§8.2; MaObSo66), second case, corrected. As `r → 1 - 0`,
`(1/2π) ∫₀^{2π} |1 - re^{it}|^{-q} dt ∼ 2^{-1} π^{-1/2} Γ((q - 1)/2) Γ(q/2)^{-1} (1 - r)^{-q+1}` if `q > 1`.
[CORRECTION] The book (and its equation crop) prints `Γ(q/2)` where `Γ(q/2)^{-1}` is right. Derivation: from
`(1 - z)^{-q/2} = Σ_n ((q/2)_n/n!) zⁿ` and Parseval, `(1/2π) ∫₀^{2π} |1 - re^{it}|^{-q} dt = ₂F₁(q/2, q/2; 1; r²)`,
and for `q > 1` (`c - a - b = 1 - q < 0`) Gauss's asymptotics give
`₂F₁(q/2, q/2; 1; r²) ∼ Γ(q - 1) Γ(q/2)^{-2} (1 - r²)^{1-q} ∼ 2^{1-q} Γ(q - 1) Γ(q/2)^{-2} (1 - r)^{1-q}`; the
duplication formula `Γ(q - 1) = 2^{q-2} π^{-1/2} Γ((q - 1)/2) Γ(q/2)` turns this into
`2^{-1} π^{-1/2} Γ((q - 1)/2) Γ(q/2)^{-1} (1 - r)^{1-q}`. The two forms agree at `q = 2` (both constants are `1/2`);
at `q = 3` the true constant is `1/π ≈ 0.318` against the printed `0.25` (numerically, the mean times `(1 - r)²` is
`0.3185` at `r = 0.999`). The uses (P1 l. 7629, 7689) compare exponents only, which the constant does not affect.
Modelling: `Asymptotics.IsEquivalent` along `r → 1-`. -/
theorem eq8_2_10_b {q : ℝ} (hq : 1 < q) :
    Asymptotics.IsEquivalent (𝓝[<] 1) (fun r : ℝ => Real.circleAverage (fun z => ‖1 - z‖ ^ (-q)) 0 r)
      (fun r : ℝ => 2⁻¹ * π ^ (-(1 / 2 : ℝ)) * Real.Gamma ((q - 1) / 2) * (Real.Gamma (q / 2))⁻¹ *
        (1 - r) ^ (-q + 1)) := by
  sorry

end Pommerenke1992
