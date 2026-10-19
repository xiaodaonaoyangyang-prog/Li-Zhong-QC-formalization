import References.Katok1992.Ch04.S02_CocompactGroups
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Katok 1992, Ch. 5 §5.5 The modular group and its subgroups

S. Katok, *Fuchsian Groups* (1992), Chapter 5, §5.5; source `full.md` of `Fuchsian groups (Katok, Svetlana)
…-3766f6b7…`, lines 2839–3069. Of Chapter 5 only §5.5 is formalized: it is the part that feeds Teichmüller theory
(finite-area quotients with cusps, the area and the number of cusps of the congruence subgroups). §5.1–§5.4
(quaternion algebras, arithmetic Fuchsian groups, compactness for division algebras) and §5.6 (examples of arithmetic
groups) are out of scope.

* Definition (the reduction ψ_n; l. 2845) — exists: `Matrix.SpecialLinearGroup.map` (Mathlib)
* Definition (the principal congruence subgroup Γ(n) as a subgroup of PSL(2, ℝ); l. 2856) — `principalCongruence`
  (Mathlib's CongruenceSubgroup.Gamma is the subgroup of SL(2, ℤ); a near miss)
* Theorem 5.5.1 (`ψ_n : SL(2, ℤ) → SL(2, ℤ_n)` is surjective; l. 2858) — `thm5_5_1`
* Corollary 5.5.2 (the quotients `SL(2, ℤ)/K(n)`, `Γ/Γ(n)`; `|PSL(2, ℤ_n)| = ½|SL(2, ℤ_n)|`; l. 2871) — omitted: folded
  into Theorem 5.5.4 (the order of `SL(2, ℤ_n)` is the content of (5.5.2))
* Lemma 5.5.3 (`|SL(2, ℤ_p)| = p³(1 − 1/p²)`; l. 2965) — omitted: proof step of Theorem 5.5.4
* Theorem 5.5.4 (the index `|Γ : Γ(n)|`; l. 2975) — `thm5_5_4`
* Corollary 5.5.5 (the area of a fundamental region of `Γ(n)`; l. 2985) — `cor5_5_5`
* The groups `Γ_n` and their index and area (l. 2991–3002) — omitted: unlabelled computation (the same method)
* Lemma 5.5.6 (`Γ` acts transitively on `ℚ̂`; l. 3005) — omitted: proof step of Theorem 5.5.12
* Lemma 5.5.7 (each `r ∈ ℚ̂` has a maximal parabolic subgroup `Γ_r` stabilizing it; l. 3009) — omitted: proof step of Theorem 5.5.12
* Lemma 5.5.8 (`|B : A ∩ B| ≤ |G : A|` for subgroups `A`, `B`; l. 3015) — omitted: proof step of Theorem 5.5.12
* Corollary 5.5.9 (`Λ ∩ Γ_r` is a maximal parabolic subgroup of `Λ`, and all arise so; l. 3019) — omitted: proof step of
  Theorem 5.5.12
* Lemma 5.5.10 (classes of maximal parabolic subgroups of `Λ` ↔ `Λ`-orbits on `ℚ̂`; l. 3023) — omitted: proof step of
  Theorem 5.5.12
* Corollary 5.5.11 (`1 ≤ s ≤ N`; l. 3033) — omitted: proof step of Theorem 5.5.12 (its content is part of `thm5_5_12`)
* Theorem 5.5.12 (a subgroup of finite index in `Γ` has `s ≤ N` cusps, is non-compact of finite area; l. 3037) —
  `thm5_5_12` (the maximal parabolic subgroups and their classes are IsMaxParabolic and maxParabolicClasses of Ch. 4 §4.2)
* Example F (`Γ(2)`; l. 3039) — omitted: example (its numbers follow from Theorems 5.5.4 and 5.5.12)

**Conventions.** `Γ = PSL(2, ℤ)` is `Katok1992.modularGroup`. `Γ(n)` is the image of Mathlib's
`CongruenceSubgroup.Gamma n` (the kernel of `SL(2, ℤ) → SL(2, ℤ/n)`) in `PSL(2, ℝ)`; its index in `Γ` is the book's
`|Γ : Γ(n)|` (for `n > 2` the matrix `−1` is not in the kernel, and `Γ(n)` is the image of the kernel). The area is the
hyperbolic `volume` of `ℍ`. A *maximal parabolic subgroup* of `Λ` is a maximal subgroup of `Λ`, different from `{Id}`,
all of whose non-identity elements are parabolic (such a subgroup is cyclic, the stabilizer of a parabolic fixed point);
the *parabolic class number* `s` of `Λ` is the number of its `Λ`-conjugacy classes.

**Corrections.** Corollary 5.5.5 [CORRECTION]: as printed it holds for *every* fundamental region `F`, which is false
without a condition on the boundary (a fundamental region in the sense of §3.1 may have a boundary of positive area, and
then `μ(F)` exceeds the covolume); the statement adds `μ(∂F) = 0`, the hypothesis of Theorem 3.1.1.

**Near miss.** None in the project: Mathlib has `CongruenceSubgroup.Gamma` and `IsCongruenceSubgroup.finiteIndex` but
neither the surjectivity of the reduction nor the index of `Γ(N)`.
-/

open Set MeasureTheory
open scoped UpperHalfPlane MatrixGroups Real Topology

noncomputable section

namespace Katok1992

/-- **Theorem 5.5.1** (§5.5; l. 2858). For `n > 1` the reduction `ψ_n : SL(2, ℤ) → SL(2, ℤ_n)` modulo `n` is a surjective
homomorphism. -/
theorem thm5_5_1 {n : ℕ} (hn : 1 < n) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n)) : SL(2, ℤ) →* SL(2, ZMod n)) := by
  sorry

/-- **The principal congruence subgroup `Γ(n)`** (§5.5; l. 2845–2856) as a subgroup of `PSL(2, ℝ)`: the image of the
kernel `CongruenceSubgroup.Gamma n` of the reduction modulo `n`, i.e. the transformations `(az + b)/(cz + d)` with
`a ≡ d ≡ ±1`, `b ≡ c ≡ 0 (mod n)`. -/
def principalCongruence (n : ℕ) : Subgroup PSL(2, ℝ) :=
  (CongruenceSubgroup.Gamma n).map
    ((QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)))

/-- **Theorem 5.5.4** (§5.5; l. 2975). The index of `Γ(n)` in the modular group `Γ`: `|Γ : Γ(n)| = 6` for `n = 2` and
`|Γ : Γ(n)| = (n³/2) ∏_{p | n} (1 − 1/p²)` for `n > 2`, `p` running over the distinct primes dividing `n`. -/
theorem thm5_5_4 {n : ℕ} :
    (n = 2 → (principalCongruence n).relIndex modularGroup = 6) ∧
      (2 < n → (((principalCongruence n).relIndex modularGroup : ℕ) : ℚ) =
        (n : ℚ) ^ 3 / 2 * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ 2)) := by
  sorry

/-- **Corollary 5.5.5** (§5.5; l. 2985). Let `F` be a fundamental region for `Γ(n)` whose boundary has zero hyperbolic area
(see the correction in the module docstring). Then `μ(F) = (π n³/6) ∏_{p | n} (1 − 1/p²)` for `n > 2`, and `μ(F) = 2π`
for `n = 2`. -/
theorem cor5_5_5 {n : ℕ} {F : Set ℍ} (hF : IsFundamentalRegion (principalCongruence n) F) (hb : volume (frontier F) = 0) :
    (n = 2 → volume F = ENNReal.ofReal (2 * π)) ∧
      (2 < n → volume F = ENNReal.ofReal (π * (n : ℝ) ^ 3 / 6 * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2))) := by
  sorry

/-- **Theorem 5.5.12** (§5.5; l. 3037). Let `Λ ≤ Γ` be a subgroup of the modular group of finite index `N`. Then `Λ` has a
finite number `s` of conjugacy classes of maximal parabolic subgroups, `1 ≤ s ≤ N`, and `Λ\ℍ` is not compact but is of
finite hyperbolic area (every fundamental region with boundary of zero area has finite area), having `s` cusps. -/
theorem thm5_5_12 {Λ : Subgroup PSL(2, ℝ)} (hΛ : Λ ≤ modularGroup) {N : ℕ} (hN : Λ.relIndex modularGroup = N)
    (hN0 : N ≠ 0) :
    ∃ s : ℕ, Nat.card (maxParabolicClasses Λ) = s ∧ 1 ≤ s ∧ s ≤ N ∧
      ¬ CompactSpace (MulAction.orbitRel.Quotient Λ ℍ) ∧
        ∀ F : Set ℍ, IsFundamentalRegion Λ F → volume (frontier F) = 0 → volume F < ⊤ := by
  sorry

end Katok1992
