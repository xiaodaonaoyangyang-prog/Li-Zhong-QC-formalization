import References.GarnettMarshall2005.Ch03.S06_RegularPoints

/-!
# Garnett–Marshall, Chapter III §7: Wiener series

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. III §7 (pp. 97–102;
`full.md` P1:4431–4615).

Conventions as in §5–§6. The notation `γ(E) = log(1/Cap(E))` recalled at P1:4439–4442 is Robin's constant of a set,
`robinConstant` (defined with (4.8) in §4), with values in `[−∞, +∞]`: `γ(E) = +∞` exactly for polar `E`. The book's
quotients `n/γ(·)` and `1/γ(·)` are taken in `[0, ∞]` through `EReal.toENNReal`; the book's convention `1/γ = 0` for a
polar set is then `x/∞ = 0` (leader rulings B1, B8). The rings `A_n(ζ)` are `wienerRing ζ n`; `A_n \ Ω` and
`A_n ∩ ∂Ω` are the plane sets `wienerRing ζ n \ finitePart Ω` and `wienerRing ζ n ∩ finitePart (frontier Ω)`. The
circular projection `E* = {|z| : z ∈ E}` is a subset of `ℝ`, and its length is Lebesgue measure on `ℝ`.

* Definition (the rings `A_n = A_n(ζ)`, §7, P1:4433–4437) — `wienerRing`
* Theorem 7.1 (Wiener, §7; (7.1), (7.2), (7.3); [CORRECTION]: the series are stated from `n = 2`) — `thm3_7_1`
* Corollary 7.3 (Beurling, §7; its hypothesis is printed with a second label (7.9)) — `cor3_7_3`
* Corollary 7.4 (§7; (7.11), (7.12)) — `cor3_7_4_a`, `cor3_7_4_b`
* Lemma 7.5 (§7) — `lemma3_7_5`

Not stated: Example 7.2 (every point of the Cantor set `K` of Example 4.7 is a regular point of `ℂ* \ K`,
P1:4537–4556; an example not cited as a result: Corollary 7.4 and Corollary D.3 of Appendix D reprove it, P1:4556).
(7.4)–(7.8) and the (7.9) of the proof of Theorem 7.1 are steps of that proof; the displays after Corollary 7.4 are
steps of its proof.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt extInf)
open References (IsDomainExt finitePart)

/-- **Definition** (the rings `A_n(ζ)`, Ch. III §7, P1:4433–4437). `A_n = A_n(ζ) = {z : 2^{−n} ≤ |z − ζ| ≤ 2^{−n+1}}`.
Modelling: `ζ ∈ ℂ` and `n ∈ ℕ`; closed rings of the plane. -/
def wienerRing (ζ : ℂ) (n : ℕ) : Set ℂ :=
  {z | (2 : ℝ) ^ (-(n : ℤ)) ≤ ‖z - ζ‖ ∧ ‖z - ζ‖ ≤ (2 : ℝ) ^ (-(n : ℤ) + 1)}

/-- **Theorem 7.1** (Wiener; Ch. III §7; cited at P1:4537, 4551, 4566, 4594, in the Notes, P1:5072–5084, and in
Exercise 9, P1:5274). Let `Ω` be a domain in `ℂ*` and let `ζ ∈ ∂Ω`. Then the following are equivalent: (7.1) `ζ` is a
regular point; (7.2) `∑_{n=1}^∞ n/γ(A_n \ Ω) = ∞`; (7.3) `∑_{n=1}^∞ n/γ(A_n ∩ ∂Ω) = ∞`.
[CORRECTION] (leader ruling B12(2)): as printed, with the series starting at `n = 1` (the equation images of (7.2)
and (7.3) show the lower index `n = 1`), the theorem is false. Counterexample: `Ω = 𝔻 \ {0}`, `ζ = 0`, for which
`Cap(ℂ* \ Ω) > 0`. Then `A_1 \ Ω = A_1 ∩ ∂Ω = ∂𝔻`, of capacity `1`, so `γ(A_1 \ Ω) = γ(∂𝔻) = 0` and the `n = 1` term
of both series is `1/0 = ∞`: the printed criterion declares `0` a regular point, but `0` is an irregular point of
`𝔻 \ {0}` (P1:4219–4231: every bounded harmonic function on `𝔻 \ {0}` extends to be harmonic at `0`). The series are
stated from `n = 2`. Then every term is finite: `A_n ⊂ B̄(ζ, 2^{1−n})`, so `Cap(A_n \ Ω) ≤ 2^{1−n} < 1` and
`γ(A_n \ Ω) ≥ (n − 1) log 2 > 0` (the same for `A_n ∩ ∂Ω`); and regularity is local (Theorem 6.1): the book's proof
itself begins by assuming `Ω ⊂ B(ζ, 1/2)`, and the divergence of a series does not depend on finitely many finite
terms.
Modelling: `Ω` a domain of `ℂ*` with `Cap(ℂ* \ Ω) > 0` (the standing assumption of §6, under which regular points are
defined, P1:4207); `ζ` a finite point (the rings are euclidean); the sums are in `[0, ∞]`, the term of index `n ≥ 2`
written at `n + 2`, with `γ = robinConstant` (4.8) through `EReal.toENNReal`; a polar piece has `γ = +∞` and gives the
term `0`, the book's convention `1/γ = 0`. -/
theorem thm3_7_1 {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) (hcap : 0 < capacity (finitePart Ωᶜ)) {ζ : ℂ}
    (hζ : (ζ : ExtPlane) ∈ frontier Ω) :
    List.TFAE [IsRegularPoint Ω ζ,
      ∑' n : ℕ, ((n + 2 : ℕ) : ℝ≥0∞) / (robinConstant (wienerRing ζ (n + 2) \ finitePart Ω)).toENNReal = ⊤,
      ∑' n : ℕ, ((n + 2 : ℕ) : ℝ≥0∞) /
        (robinConstant (wienerRing ζ (n + 2) ∩ finitePart (frontier Ω))).toENNReal = ⊤] := by
  sorry

/-- **Corollary 7.3** (Beurling; Ch. III §7; cited in the Notes, P1:5084, "Corollary 7.3 is from Beurling's thesis").
Let `E` be a compact set. Assume `0 ∈ E` and set `E* = {|z| : z ∈ E}`. If (7.9) `∫_{E*} dr/r = ∞`, then `0` is a
regular point for `Ω = ℂ* \ E`.
Modelling: `E*` is a subset of `[0, ∞) ⊆ ℝ` and the integral is the lower Lebesgue integral of `1/r` over it, in
`[0, ∞]` (the value `1/0 = ∞` at the single point `r = 0` is on a null set); `ℂ* \ E` need not be connected, and
regular points are defined for domains: the conclusion is that `0` is a regular point of every component of `ℂ* \ E`
that has `0` on its boundary. The standing assumption `Cap(ℂ* \ Ω) > 0` of §6 follows from (7.9) (it forces
`|E*| > 0`, and then `Cap(E) ≥ |E*|/4 > 0` by (4.12)) and is not added. The label "(7.9)" of the hypothesis is printed a
second time (the first (7.9) is in the proof of Theorem 7.1, and there is no (7.10)); the proof of the corollary cites
"(7.9)" for its hypothesis: a numbering slip of the book, recorded in the root's Corrections list. The formula was
checked against the equation image. -/
theorem cor3_7_3 {E : Set ℂ} (hE : IsCompact E) (h0 : (0 : ℂ) ∈ E)
    (h79 : ∫⁻ r in (fun z : ℂ => ‖z‖) '' E, (ENNReal.ofReal r)⁻¹ = ⊤) :
    ∀ z ∈ (toExt E)ᶜ, ((0 : ℂ) : ExtPlane) ∈ frontier (connectedComponentIn (toExt E)ᶜ z) →
      IsRegularPoint (connectedComponentIn (toExt E)ᶜ z) ((0 : ℂ) : ExtPlane) := by
  sorry

/-- **Corollary 7.4** (Ch. III §7; cited at P1:4556), first case. Assume `ζ ∈ E = ∂Ω`. If
(7.11) `limsup_{r→0} Cap(E ∩ B(ζ, r))/r > 0`, then `ζ` is a regular point of `∂Ω`.
Modelling: `Ω` a domain of `ℂ*`; `ζ` a finite point of `E = ∂Ω` (the discs are euclidean); `E ∩ B(ζ, r)` is the plane
set `finitePart (frontier Ω) ∩ ball ζ r`; the quotient and the `limsup` along `r → 0⁺` are in `[0, ∞]` (a complete
lattice: no junk value; `r > 0` there). The standing assumption `Cap(ℂ* \ Ω) > 0` of §6 follows from (7.11) and is
not added. The two conditions (7.11), (7.12) give two statements (the proof shows that (7.11) implies (7.12)). The
formula was checked against the equation image. -/
theorem cor3_7_4_a {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) {ζ : ℂ} (hζ : (ζ : ExtPlane) ∈ frontier Ω)
    (h711 : 0 < limsup (fun r : ℝ => capacity (finitePart (frontier Ω) ∩ ball ζ r) / ENNReal.ofReal r) (𝓝[>] 0)) :
    IsRegularPoint Ω ζ := by
  sorry

/-- **Corollary 7.4** (Ch. III §7), second case. Assume `ζ ∈ E = ∂Ω`. If
(7.12) `limsup_{r→0} log(1/r)/γ(E ∩ B(ζ, r)) > 0`, then `ζ` is a regular point of `∂Ω`.
Modelling: as in the first case; `γ = robinConstant` (4.8), and the quotient is taken in `[0, ∞]`: for `0 < r < 1`,
`Cap(E ∩ B(ζ, r)) ≤ r < 1`, so `γ(E ∩ B(ζ, r)) ≥ log(1/r) > 0` and no quotient by `0` occurs; a polar
`E ∩ B(ζ, r)` has `γ = +∞` and gives `0`, the book's convention. The standing assumption `Cap(ℂ* \ Ω) > 0` follows from
(7.12) and is not added. The formula was checked against the equation image. -/
theorem cor3_7_4_b {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) {ζ : ℂ} (hζ : (ζ : ExtPlane) ∈ frontier Ω)
    (h712 : 0 < limsup (fun r : ℝ => ENNReal.ofReal (Real.log (1 / r)) /
      (robinConstant (finitePart (frontier Ω) ∩ ball ζ r)).toENNReal) (𝓝[>] 0)) :
    IsRegularPoint Ω ζ := by
  sorry

/-- **Lemma 7.5** (Ch. III §7; cited at P1:4588 in the proof of Corollary 7.4, and in Exercise 9, P1:5244). Suppose
`E₁, …, E_n` are disjoint Borel subsets of `B(0, 1/2)`. Then `1/γ(⋃ E_k) ≤ ∑_{k=1}^n 1/γ(E_k)`.
Modelling: the sets are indexed by `Fin n`; `γ = robinConstant` (4.8), and the reciprocals are taken in `[0, ∞]`
(`EReal.toENNReal`, then `⁻¹`): on subsets of `B(0, 1/2)`, `Cap ≤ 1/2`, so `γ ≥ log 2 > 0` and no reciprocal of `0`
occurs; a polar set has `γ = +∞` and reciprocal `0`, the book's convention. The formula was checked against the
equation image. -/
theorem lemma3_7_5 {n : ℕ} {E : Fin n → Set ℂ} (hEm : ∀ k, MeasurableSet (E k))
    (hEd : Pairwise fun i j => Disjoint (E i) (E j)) (hEB : ∀ k, E k ⊆ ball 0 (1 / 2)) :
    ((robinConstant (⋃ k, E k)).toENNReal)⁻¹ ≤ ∑ k, ((robinConstant (E k)).toENNReal)⁻¹ := by
  sorry

end GarnettMarshall2005
