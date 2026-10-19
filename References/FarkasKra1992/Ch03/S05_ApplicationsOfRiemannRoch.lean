import References.FarkasKra1992.Ch03.S04_DivisorsAndRiemannRoch
import References.Forster1981.Ch02.S18_FunctionsAndDifferentialFormsWithPrescribedPrincipalParts

/-!
# Farkas–Kra, Chapter III §5: Applications of the Riemann–Roch theorem (gaps, weights, classical Weierstrass points)

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. III §5 (`full.md` FK1:3588–4084).

Conventions: as in `Ch03/S04_DivisorsAndRiemannRoch` (divisors additive, `dimL`, `dimOmega`, `LFun`, genus by
`LiZhongQC.HasGenus`). This file contains the part of III.5 that does not involve `q`-differentials for `q ≠ 1`: the gap
theorems and the classical (`q = 1`) Weierstrass points. A point is a **Weierstrass point** (FK III.5.9, `q = 1`) iff
the Wronskian of a basis of the holomorphic abelian differentials vanishes at it: `Forster1981.IsWeierstrassPoint` (for a basis
`w` given by `Forster1981.IsBasisOfHol`; independence of the basis is not stated), its weight is
`Forster1981.weierstrassWeight` (FK's weight of III.5.8 with respect to `ℋ¹(M)`, equal by the Proposition of III.5.8).
Pole orders: `f` has a pole of order `n` at `P` iff `ord_P f = -n`. The general `q`-differential items (III.5.1 (5.1.5),
III.5.2, the `q`-Weierstrass points III.5.9–III.5.10) are in the sibling file `Ch03/S05b_HolomorphicQDifferentials`; the
holomorphic de Rham cohomology (III.5.12–5.13) is not formalized.

* Paragraph III.5.1 (consequences of Riemann–Roch (5.1.1)–(5.1.4), (5.1.2a)) — `para3_5_1_a`
* Paragraph III.5.1 ((5.1.5) `L(Z^{-q}) ≅ ℋ^q(M)`) — para3_5_1_b in the sibling file `Ch03/S05b_HolomorphicQDifferentials`
* Proposition III.5.2 (dimension table of `ℋ^q(M)`) — prop3_5_2 in `Ch03/S05b_HolomorphicQDifferentials`
* Definition (gaps and non-gaps at `P`, III.5.3) — `IsGap`
* Theorem III.5.3 (Weierstrass gap theorem) — `thm3_5_3`
* Theorem III.5.4 (Noether gap theorem) — `noetherDiv`, `thm3_5_4`
* Proposition III.5.5 — `nonGap`, `prop3_5_5`
* Proposition III.5.6 — `prop3_5_6`
* Proposition III.5.7 — `prop3_5_7`
* Corollary to Proposition III.5.7 — `cor3_5_7`
* Paragraph III.5.8 (gaps and zeros of abelian differentials of the first kind; the Fact) — `para3_5_8_gaps`
* Definition (weight `τ(z)` with respect to a space `A` of holomorphic functions, III.5.8) — `weightWRT`
* Proposition III.5.8 (`ord_z Φ = τ(z)` for the Wronskian) — `prop3_5_8`
* Remark of III.5.8 (`Φ ≡ 0` iff the functions are dependent) — `para3_5_8`
* Corollary 1 to Proposition III.5.8 — `cor3_5_8_a`
* Corollary 2 to Proposition III.5.8 — `cor3_5_8_b`
* Definition (`q`-Weierstrass point, III.5.9) — exists: `FarkasKra1992.IsQWeierstrass`
* Proposition III.5.9 (`q = 1`: the classical Weierstrass points) — `weierstrassSet`, `prop3_5_9_one`
* Proposition III.5.10 (`q = 1`: `Σ τ(P) = (g - 1) g (g + 1)`) — exists: `Forster1981.thm18_8`
* Proposition III.5.10 and Corollary (general `q`) — prop3_5_10, cor3_5_10 in `Ch03/S05b_HolomorphicQDifferentials`
* Theorem III.5.11 (the weight of a point is at most `g(g - 1)/2`) — `thm3_5_11`
* Corollary to Theorem III.5.11 (`2g + 2 ≤ W ≤ g³ - g`) — `cor3_5_11`
* Paragraph III.5.12 (holomorphic de Rham cohomology `H¹_hol(M')`, Theorem) — deferred: the exterior derivative on holomorphic
  functions of an open surface is not a map of Forster's sheaves of forms
* Proposition III.5.13 and Corollary — deferred: as III.5.12
-/

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

namespace FarkasKra1992

open Forster1981 (H0 modOD modOmegaD divDeg divSingle)

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- **Paragraph III.5.1** (consequences of the Riemann–Roch theorem, (5.1.2a)–(5.1.4)). On a compact Riemann surface of
genus `g`: `i(D) = 0` if `deg D > 2g - 2`; if `deg D = 0` then `r(D) ≤ 1`, and `r(D) = 1` iff `D` is principal. -/
theorem para3_5_1_a [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (D : Function.locallyFinsupp M ℤ) :
    (2 * (g : ℤ) - 2 < divDeg D → dimOmega D = 0) ∧
      (divDeg D = 0 → dimL D ≤ 1 ∧ (dimL D = 1 ↔ Forster1981.IsPrincipalDivisor D)) := by
  sorry

/-! ## Gaps -/

/-- **Gaps at `P`** (Ch. III §5.3): the positive integer `n` is a gap at `P` if there is no meromorphic function on `M`,
holomorphic on `M ∖ {P}`, with a pole of order `n` at `P` (`ord_P f = -n`). -/
def IsGap (P : M) (n : ℕ) : Prop :=
  ¬∃ f : M → ℂ, LiZhongQC.IsMeromorphicRS f ∧ (∀ x, x ≠ P → 0 ≤ LiZhongQC.ordRS f x) ∧
    LiZhongQC.ordRS f P = (((-(n : ℤ)) : ℤ) : WithTop ℤ)

/-- **Theorem III.5.3 (Weierstrass gap theorem)** (Ch. III §5.3). Let `M` have positive genus `g` and `P ∈ M`. There are
precisely `g` integers `1 = n₁ < n₂ < ⋯ < n_g < 2g` such that no such function exists: the set of gaps at `P` has exactly
`g` elements, contains `1`, and all gaps are `< 2g`. -/
theorem thm3_5_3 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (hpos : 0 < g) (P : M) :
    {n : ℕ | 0 < n ∧ IsGap P n}.ncard = g ∧ IsGap P 1 ∧ ∀ n, 0 < n → IsGap P n → n < 2 * g := by
  sorry

/-- **The divisors `D_0 = 1`, `D_{j+1} = D_j P_{j+1}`** of III.5.4 for a sequence of points `P_1, P_2, …`
(`P i` is the point `P_{i+1}`). -/
def noetherDiv (P : ℕ → M) (j : ℕ) : Function.locallyFinsupp M ℤ := ∑ i ∈ Finset.range j, divSingle (P i) 1

/-- **Theorem III.5.4 (Noether gap theorem)** (Ch. III §5.4). For a sequence of points `P_1, P_2, …` of `M` (genus `g > 0`),
the answer to Question "j" (is there a meromorphic `f` with `(f) ≥ D_j⁻¹` and `(f) ≱ D_{j-1}⁻¹`?) is "no" for precisely `g`
integers `j`, namely `1 = n₁ < n₂ < ⋯ < n_g < 2g`. -/
theorem thm3_5_4 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (hpos : 0 < g) (P : ℕ → M) :
    {j : ℕ | 0 < j ∧ ¬∃ f ∈ LFun (-(noetherDiv P j)), f ∉ LFun (-(noetherDiv P (j - 1)))}.ncard = g ∧
      (¬∃ f ∈ LFun (-(noetherDiv P 1)), f ∉ LFun (-(noetherDiv P 0))) ∧
      ∀ j, 0 < j → (¬∃ f ∈ LFun (-(noetherDiv P j)), f ∉ LFun (-(noetherDiv P (j - 1)))) → j < 2 * g := by
  sorry

/-- **The `j`-th non-gap `α_j` at `P`** (Ch. III §5.5), `j ≥ 1`: the `j`-th smallest positive non-gap
(`α₁ < α₂ < ⋯`; the first `g` are `≤ 2g`, `α_g = 2g`). -/
def nonGap (P : M) (j : ℕ) : ℕ := Nat.nth (fun n => 0 < n ∧ ¬IsGap P n) (j - 1)

/-- **Proposition III.5.5** (Ch. III §5.5). For `0 < j < g`: `α_j + α_{g-j} ≥ 2g`. -/
theorem prop3_5_5 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (hpos : 0 < g) (P : M) {j : ℕ} (h0 : 0 < j)
    (hj : j < g) : 2 * g ≤ nonGap P j + nonGap P (g - j) := by
  sorry

/-- **Proposition III.5.6** (Ch. III §5.6). If `α₁ = 2`, then `α_j = 2j` and `α_j + α_{g-j} = 2g` for `0 < j < g`. -/
theorem prop3_5_6 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (hpos : 0 < g) (P : M)
    (h : nonGap P 1 = 2) {j : ℕ} (h0 : 0 < j) (hj : j < g) :
    nonGap P j = 2 * j ∧ nonGap P j + nonGap P (g - j) = 2 * g := by
  sorry

/-- **Proposition III.5.7** (Ch. III §5.7). If `α₁ > 2`, then for some `j` with `0 < j < g`, `α_j + α_{g-j} > 2g`. -/
theorem prop3_5_7 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (hpos : 0 < g) (P : M)
    (h : 2 < nonGap P 1) : ∃ j, 0 < j ∧ j < g ∧ 2 * g < nonGap P j + nonGap P (g - j) := by
  sorry

/-- **Corollary to Proposition III.5.7** (Ch. III §5.7). `Σ_{j=1}^{g-1} α_j ≥ g(g - 1)`, with equality if and only if
`α₁ = 2`. -/
theorem cor3_5_7 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (hpos : 0 < g) (P : M) :
    g * (g - 1) ≤ ∑ j ∈ Finset.Ico 1 g, nonGap P j ∧ (∑ j ∈ Finset.Ico 1 g, nonGap P j = g * (g - 1) ↔ nonGap P 1 = 2) := by
  sorry

/-- **Paragraph III.5.8** (gaps and zeros of abelian differentials of the first kind; the Fact). The integer `j ≥ 1` is a gap
at `P` iff `r(P^{-j}) - r(P^{-j+1}) = 0` iff `i(P^{j-1}) - i(P^j) = 1` (i.e. there is an abelian differential of the first
kind with a zero of order exactly `j - 1` at `P`); and for `g > 0` some abelian differential of the first kind does not
vanish at `P`: `i(P) + 1 = i(1) = g`. -/
theorem para3_5_8_gaps [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (hpos : 0 < g) (P : M) {j : ℕ} (hj : 0 < j) :
    (IsGap P j ↔ dimL (-(divSingle P (j : ℤ))) = dimL (-(divSingle P ((j : ℤ) - 1)))) ∧
      (IsGap P j ↔ dimOmega (divSingle P ((j : ℤ) - 1)) = dimOmega (divSingle P (j : ℤ)) + 1) ∧
        dimOmega (divSingle P 1) + 1 = g := by
  sorry

/-! ## Weights and Wronskians -/

/-- **Weight `τ(z)` of `z` with respect to a finite-dimensional space `A` of functions holomorphic near `z`** (Ch. III §5.8,
(5.8.2)): `τ(z) = Σ_{j=1}^{n} (μ_j - j + 1)`, where `μ_1 < ⋯ < μ_n` are the distinct orders `ord_z φ` of the non-zero
elements `φ` of `A` (the orders of a basis adapted to `z`). -/
def weightWRT (A : Submodule ℂ (ℂ → ℂ)) (z : ℂ) : ℕ :=
  ∑ j ∈ Finset.range (Module.finrank ℂ A),
    (Nat.nth (fun m => ∃ φ ∈ A, φ ≠ 0 ∧ analyticOrderAt φ z = (m : ℕ∞)) j - j)

/-- **Proposition III.5.8** (Ch. III §5.8). Let `A` be an `n`-dimensional space of holomorphic functions on a domain `D ⊂ ℂ` and
`φ_1, …, φ_n` any basis of `A`. Then the Wronskian `Φ = det[φ_k^{(m)}]` satisfies `ord_z Φ = τ(z)` for `z ∈ D`.
[CORRECTION, FK-fix2] `A` is a space of functions on `D`: `hAD` (an element vanishing on `D` is zero), so that `finrank A` and
the linear independence of the basis are not counted by values off `D` (AUDIT5_FK F1: `A = span {1 on Dᶜ, 0 on D}` has a
Wronskian of order `⊤` and weight `0`). -/
theorem prop3_5_8 {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {A : Submodule ℂ (ℂ → ℂ)}
    (hA : ∀ φ ∈ A, DifferentiableOn ℂ φ D) (hAD : ∀ φ ∈ A, (∀ w ∈ D, φ w = 0) → φ = 0) {n : ℕ} (hn : Module.finrank ℂ A = n) (φ : Fin n → ℂ → ℂ)
    (hφ : ∀ k, φ k ∈ A) (hli : LinearIndependent ℂ (fun k => (⟨φ k, hφ k⟩ : A))) {z : ℂ} (hz : z ∈ D) :
    analyticOrderAt (Forster1981.wronskian φ) z = (weightWRT A z : ℕ∞) := by
  sorry

/-- **Remark after Proposition III.5.8** (Ch. III §5.8). For holomorphic functions `φ_1, …, φ_n` on a domain `D`, the Wronskian
vanishes identically on `D` if and only if the functions are linearly dependent on `D`. -/
theorem para3_5_8 {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {n : ℕ} (φ : Fin n → ℂ → ℂ)
    (hφ : ∀ k, DifferentiableOn ℂ (φ k) D) :
    (∀ z ∈ D, Forster1981.wronskian φ z = 0) ↔ ∃ c : Fin n → ℂ, c ≠ 0 ∧ ∀ z ∈ D, ∑ k, c k * φ k z = 0 := by
  sorry

/-- **Corollary 1 to Proposition III.5.8** (Ch. III §5.8). The set of `z ∈ D` of positive weight with respect to a
finite-dimensional space `A` of holomorphic functions on a domain `D` is discrete (every point of `D` has a punctured
neighbourhood of weight `0`). -/
theorem cor3_5_8_a {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {A : Submodule ℂ (ℂ → ℂ)}
    (hA : ∀ φ ∈ A, DifferentiableOn ℂ φ D) [FiniteDimensional ℂ A] (hne : 0 < Module.finrank ℂ A) :
    ∀ z ∈ D, ∀ᶠ w in 𝓝[≠] z, weightWRT A w = 0 := by
  sorry

/-- **Corollary 2 to Proposition III.5.8** (Ch. III §5.8). Under the hypotheses of Corollary 1, for an open dense set of
`z ∈ D` the basis adapted to `z` has `ord_z φ_j = j - 1`, i.e. the points of weight `0` form an open dense subset of `D`. -/
theorem cor3_5_8_b {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {A : Submodule ℂ (ℂ → ℂ)}
    (hA : ∀ φ ∈ A, DifferentiableOn ℂ φ D) [FiniteDimensional ℂ A] (hne : 0 < Module.finrank ℂ A) :
    IsOpen {z ∈ D | weightWRT A z = 0} ∧ D ⊆ closure {z ∈ D | weightWRT A z = 0} := by
  sorry

/-! ## Classical Weierstrass points -/

/-- **The set of classical Weierstrass points `W(M)`** (Ch. III §5.9, `q = 1`; Ch. V §1.2): the points `p` at which the Wronskian
of a basis of the holomorphic abelian differentials vanishes (`Forster1981.IsWeierstrassPoint`). -/
def weierstrassSet (M : Type) [TopologicalSpace M] [ChartedSpace ℂ M] (g : ℕ) : Set M :=
  {p | ∃ w : Fin g → Forster1981.Form1 M, Forster1981.IsBasisOfHol w ∧ Forster1981.IsWeierstrassPoint w p}

/-- **Proposition III.5.9, `q = 1`** (Ch. III §5.9). A point `P` of a compact surface of genus `g ≥ 2` is a (classical)
Weierstrass point if and only if `i(P^g) > 0`, iff `r(P^{-g}) ≥ 2` (at least one of the integers `2, …, g` is not a gap). -/
theorem prop3_5_9_one [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (h2 : 2 ≤ g) (P : M) :
    P ∈ weierstrassSet M g ↔ 0 < dimOmega (divSingle P (g : ℤ)) ∧ 2 ≤ dimL (-(divSingle P (g : ℤ))) := by
  sorry

/-- **Theorem III.5.11** (Ch. III §5.11). For `g ≥ 2`, the weight of a point with respect to the holomorphic abelian
differentials is `≤ g(g - 1)/2`; this bound is attained only at a point where the non-gap sequence begins with `2`. -/
theorem thm3_5_11 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (h2 : 2 ≤ g) {w : Fin g → Forster1981.Form1 M}
    (hw : Forster1981.IsBasisOfHol w) (P : M) :
    2 * Forster1981.weierstrassWeight w P ≤ g * (g - 1) ∧
      (2 * Forster1981.weierstrassWeight w P = g * (g - 1) → nonGap P 1 = 2) := by
  sorry

/-- **Corollary to Theorem III.5.11** (Ch. III §5.11). The number `W` of Weierstrass points of a compact surface of genus
`g ≥ 2` satisfies `2g + 2 ≤ W ≤ g³ - g`. -/
theorem cor3_5_11 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (h2 : 2 ≤ g) :
    2 * g + 2 ≤ (weierstrassSet M g).ncard ∧ (weierstrassSet M g).ncard ≤ g ^ 3 - g := by
  sorry

end FarkasKra1992
