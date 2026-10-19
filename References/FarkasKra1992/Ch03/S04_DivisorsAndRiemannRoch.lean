import References.Forster1981.Ch02.S17_TheSerreDualityTheorem

/-!
# Farkas–Kra, Chapter III §4: Divisors and the Riemann–Roch theorem

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. III §4 (`full.md` FK1:3062–3587).

Conventions: `M` is a compact Riemann surface of genus `g` (`LiZhongQC.HasGenus M g`, which includes compactness; the
relation to `Forster1981.genus`, the dimension of `H¹(𝒪)`, is not stated); the binders are the project's Riemann-surface
binders, without second countability. **Divisors** are Forster's `Function.locallyFinsupp M ℤ`, written *additively*: FK's
multiplicative divisor `𝔄 = ∏ P^{α(P)}` is the function `P ↦ α(P)`, the product is the sum, `𝔄⁻¹` is `-A`, `𝔄 ≥ 𝔅` is
`DivLE B A` (pointwise). A function `f` is a multiple of `𝔄` if `(f) ≥ 𝔄`, i.e. `ord_P f ≥ α(P)` for all `P`. **Dimensions
are junk-free:** FK's `L(𝔄) = {f ∈ 𝒦(M) : (f) ≥ 𝔄}` is the space of sections `H⁰(M, 𝒪_{-A})` of Forster's sheaf
(`Forster1981.modOD`: meromorphic functions modulo functions vanishing on punctured neighbourhoods), `r(𝔄) = dimL A`;
`Ω(𝔄) = {ω abelian : (ω) ≥ 𝔄}` is `H⁰(M, Ω_{-A})` (`Forster1981.modOmegaD`) and `i(𝔄) = dimOmega A` (Forster's
`specialityIndex` is `dim H¹(𝒪_D)`, a different object, equal to this by Serre duality). `LFun A` is the set of *functions*
(values at poles are irrelevant) used where a statement is about functions.

* Definition III.4.1 (divisors, degree, principal, canonical divisors; equivalence) — exists: `Forster1981.divDeg`,
  `Forster1981.IsDivisorOf`, `Forster1981.IsPrincipalDivisor`, `Forster1981.AreEquivalentDivisors`,
  `Forster1981.IsCanonicalDivisor`
* Definition III.4.2 (integral divisors, order, multiple of a divisor) — `DivLE`, `IsIntegralDiv`, `LFun`
* Definition III.4.3 (`L(𝔄)`, `r(𝔄)`) — `dimL`
* Proposition III.4.3 — `prop3_4_3`
* Proposition III.4.4 — `prop3_4_4`
* Proposition III.4.5 — `prop3_4_5`
* Definition III.4.6 (`Ω(𝔄)`, `i(𝔄)`) — `dimOmega`
* Theorem III.4.6 — `thm3_4_6`
* Proposition III.4.7 — `prop3_4_7`
* Theorem III.4.8 (Riemann–Roch for integral divisors) — `RRHolds`, `thm3_4_8`
* Corollary III.4.9 (1) (genus 0) — exists: `Forster1981.cor16_13`
* Corollary III.4.9 (2) (`deg Z = 2g - 2`) — exists: `LiZhongQC.deg_canonical`
* Corollary III.4.9 (3) — `cor3_4_9_c`
* Proposition III.4.10 — `prop3_4_10`
* Corollary III.4.10 — `cor3_4_10`
* Theorem III.4.11 (Riemann–Roch for every divisor) — `thm3_4_11`
* Paragraph III.4.12 (analytic proof of Riemann–Hurwitz) — omitted: proof of Theorem I.2.7
* Definition III.4.13 (complete linear system `|D|`) — `linearSystem`
* Proposition III.4.13 — `prop3_4_13`
-/

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

namespace FarkasKra1992

open Forster1981 (H0 modOD modOmegaD divDeg IsPrincipalDivisor AreEquivalentDivisors IsCanonicalDivisor)

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- **Order of divisors** (Ch. III §4.2): FK's `𝔄 ≥ 𝔅` is `DivLE B A`, i.e. `A(P) ≥ B(P)` for all `P`. -/
def DivLE (B A : Function.locallyFinsupp M ℤ) : Prop := ∀ x, B x ≤ A x

/-- **Integral divisor** (Ch. III §4.2): `𝔄 ≥ 1`, i.e. `A(P) ≥ 0` for all `P`. -/
def IsIntegralDiv (A : Function.locallyFinsupp M ℤ) : Prop := ∀ x, 0 ≤ A x

/-- **`L(𝔄)` as a set of functions** (Ch. III §4.2–4.3): the meromorphic `f` which are multiples of `𝔄`,
`ord_P f ≥ α(P)` for all `P` (the values of `f` at its poles are irrelevant: functions are only determined up to
this; `dimL` uses the quotient). -/
def LFun (A : Function.locallyFinsupp M ℤ) : Set (M → ℂ) :=
  {f | LiZhongQC.IsMeromorphicRS f ∧ ∀ x, ((A x : ℤ) : WithTop ℤ) ≤ LiZhongQC.ordRS f x}

/-- **`r(𝔄) = dim L(𝔄)`** (Ch. III §4.3), the dimension of the space of sections `H⁰(M, 𝒪_{-A})` of Forster's sheaf of
meromorphic functions `f` with `(f) ≥ A` (modulo functions vanishing on punctured neighbourhoods). -/
def dimL (A : Function.locallyFinsupp M ℤ) : ℕ := Module.finrank ℂ (H0 (modOD M (-A)))

/-- **`i(𝔄) = dim Ω(𝔄)`**, the index of specialty (Ch. III §4.6): the dimension of the space of abelian differentials `ω`
with `(ω) ≥ 𝔄`, i.e. of `H⁰(M, Ω_{-A})`. -/
def dimOmega (A : Function.locallyFinsupp M ℤ) : ℕ := Module.finrank ℂ (H0 (modOmegaD M (-A)))

/-- **Proposition III.4.3** (Ch. III §4.3). `𝔅 ≥ 𝔄 ⇒ L(𝔅) ⊂ L(𝔄)`. -/
theorem prop3_4_3 {A B : Function.locallyFinsupp M ℤ} (h : DivLE A B) : LFun B ⊆ LFun A := by
  sorry

/-- **Proposition III.4.4** (Ch. III §4.4). On a compact surface `L(1) = ℂ` and `r(1) = 1`: a function of `L(1)` is a
constant (off a discrete set), and `dimL 0 = 1`. -/
theorem prop3_4_4 [CompactSpace M] :
    (∀ f ∈ LFun (0 : Function.locallyFinsupp M ℤ), ∃ c : ℂ, ∀ᶠ x in Filter.codiscrete M, f x = c) ∧
      dimL (0 : Function.locallyFinsupp M ℤ) = 1 := by
  sorry

/-- **Proposition III.4.5** (Ch. III §4.5). If `deg 𝔄 > 0` then `r(𝔄) = 0`. -/
theorem prop3_4_5 [CompactSpace M] {A : Function.locallyFinsupp M ℤ} (h : 0 < divDeg A) :
    (∀ f ∈ LFun A, ∀ᶠ x in Filter.codiscrete M, f x = 0) ∧ dimL A = 0 := by
  sorry

/-- **Theorem III.4.6** (Ch. III §4.6). For `𝔄 ∈ Div(M)`, `r(𝔄)` and `i(𝔄)` depend only on the divisor class of `𝔄`;
and if `ω ≠ 0` is an abelian differential with divisor `K`, then `i(𝔄) = r(𝔄 (ω)⁻¹)`, i.e. `dimOmega A = dimL (A - K)`. -/
theorem thm3_4_6 [CompactSpace M] :
    (∀ A B : Function.locallyFinsupp M ℤ, AreEquivalentDivisors A B → dimL A = dimL B ∧ dimOmega A = dimOmega B) ∧
      ∀ (A K : Function.locallyFinsupp M ℤ) (w : Forster1981.Form1 M), Forster1981.IsDivisorOfForm w K →
        dimOmega A = dimL (A - K) := by
  sorry

/-- **Proposition III.4.7** (Ch. III §4.7). `Ω(1) = ℋ¹(M)`, the space of holomorphic abelian differentials, and
`i(1) = g`. -/
theorem prop3_4_7 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) :
    dimOmega (0 : Function.locallyFinsupp M ℤ) = g := by
  sorry

/-- The conclusion of the Riemann–Roch theorem for the divisor `A` (Ch. III §4.8, (4.8.1)): the spaces are finite
dimensional and `r(𝔄⁻¹) = deg 𝔄 - g + 1 + i(𝔄)`, i.e. `dimL (-A) = deg A - g + 1 + dimOmega A`. -/
def RRHolds (g : ℕ) (A : Function.locallyFinsupp M ℤ) : Prop :=
  FiniteDimensional ℂ (H0 (modOD M A)) ∧ FiniteDimensional ℂ (H0 (modOmegaD M (-A))) ∧
    (dimL (-A) : ℤ) = divDeg A - g + 1 + dimOmega A

/-- **Theorem III.4.8 (Riemann–Roch)** (Ch. III §4.8). Let `M` be a compact Riemann surface of genus `g` and `𝔄` an integral
divisor. Then `r(𝔄⁻¹) = deg 𝔄 - g + 1 + i(𝔄)` (4.8.1). Modelling: FK's form, with `i(𝔄) = dim Ω(𝔄)`; near misses
`LiZhongQC.thm22_4_riemann_roch` (with `ℓ(K - α)` a function space) and `Forster1981.thm16_9` (sheaf cohomology). -/
theorem thm3_4_8 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) {A : Function.locallyFinsupp M ℤ}
    (hA : IsIntegralDiv A) : RRHolds g A := by
  sorry

/-- **Corollary III.4.9 (3)** (Ch. III §4.9). The Riemann–Roch theorem holds for `𝔄` provided that (a) `𝔄` is equivalent to
an integral divisor, or (b) `Z/𝔄` is equivalent to an integral divisor for some canonical divisor `Z`. -/
theorem cor3_4_9_c [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) {A : Function.locallyFinsupp M ℤ}
    (h : (∃ B, IsIntegralDiv B ∧ AreEquivalentDivisors A B) ∨
      ∃ Z B, IsCanonicalDivisor Z ∧ IsIntegralDiv B ∧ AreEquivalentDivisors (Z - A) B) : RRHolds g A := by
  sorry

/-- **Proposition III.4.10** (Ch. III §4.10). If `r(𝔄⁻¹) > 0`, then `𝔄` is equivalent to an integral divisor. -/
theorem prop3_4_10 [CompactSpace M] {A : Function.locallyFinsupp M ℤ} (h : 0 < dimL (-A)) :
    ∃ B, IsIntegralDiv B ∧ AreEquivalentDivisors A B := by
  sorry

/-- **Corollary to Proposition III.4.10** (Ch. III §4.10). If `i(𝔄) > 0`, then `Z/𝔄` is equivalent to an integral divisor
(for a canonical divisor `Z`). -/
theorem cor3_4_10 [CompactSpace M] {A : Function.locallyFinsupp M ℤ} (h : 0 < dimOmega A) :
    ∃ Z B, IsCanonicalDivisor Z ∧ IsIntegralDiv B ∧ AreEquivalentDivisors (Z - A) B := by
  sorry

/-- **Theorem III.4.11 (Riemann–Roch for every divisor)** (Ch. III §4.11). The Riemann–Roch theorem holds for every
divisor `𝔄` on a compact surface: `r(𝔄⁻¹) = deg 𝔄 - g + 1 + i(𝔄)`. -/
theorem thm3_4_11 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (A : Function.locallyFinsupp M ℤ) : RRHolds g A := by
  sorry

/-- **The complete linear system `|D|`** (Ch. III §4.13): the integral divisors equivalent to `D`. -/
def linearSystem (D : Function.locallyFinsupp M ℤ) : Set (Function.locallyFinsupp M ℤ) :=
  {D₁ | IsIntegralDiv D₁ ∧ AreEquivalentDivisors D₁ D}

/-- **Proposition III.4.13** (Ch. III §4.13). For every divisor `D`, the points of `|D|` are in one-to-one correspondence
with the points of the projective space of the vector space `L(1/D)` (= `H⁰(M, 𝒪_D)`). [weaker: the canonical form of the
correspondence, `D₁ = D (f)`, is not stated] -/
theorem prop3_4_13 [CompactSpace M] (D : Function.locallyFinsupp M ℤ) :
    Nonempty (↥(linearSystem D) ≃ Projectivization ℂ (H0 (modOD M D))) := by
  sorry

end FarkasKra1992
