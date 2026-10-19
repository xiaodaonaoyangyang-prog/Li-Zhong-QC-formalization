import References.Pommerenke1992.Ch11.S03_VisserOstrowskiQuotient

/-!
# Pommerenke 1992, Ch. 11 §11.4 Module and Conformality

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 11 *Local Boundary Behaviour*, §11.4; source
`full.md` of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3…` (P2), lines 3206–3489.

* Definition (system of circular crosscuts, (11.4.1); used throughout §11.4–§11.5, restated at P2 l. 3492–3496) —
  `IsCircularCrosscutSystem`
* Definition (the crosscuts `Q(ρ) = f⁻¹(T(ρ))`, (11.4.2); used in (11.4.3), Theorem 11.13, (11.5.2) and in proofs;
  helper) — `crosscutPreimage`
* Definition (the family `Γ(ρ₁, ρ₂)` of all crosscuts of `G` that separate `T(ρ₁)` and `T(ρ₂)`, P2 l. 3222,
  Fig. 11.5; used in Proposition 11.8, (11.4.5), Theorem 11.9, the proof of Theorem 11.10, Propositions 11.12, 11.15
  and Theorems 11.13, 11.14) — `separatingCrosscuts`
* Proposition 11.8 (RoWa76, JenOi77; cited in the proofs of Theorem 11.9, P2 l. 3319, and Theorem 11.14,
  P2 l. 3575) — `prop11_8`
* Definition (the module of a curve family, recalled at P2 l. 3236: "The module of a curve family was introduced in
  Section 9.2") — exists: `LehtoVirtanen1973.arcFamilyModule` (the leader's ruling QD2: Pommerenke's (9.2.1),
  (9.2.2), the infimum of the area integral of the square of an admissible non-negative Borel function, with no
  normalizing factor, which the constants of Theorems 11.9 and 11.13 depend on; the families are sets of point sets of
  the extended plane, here crosscuts)
* Formula (11.4.5) ("It follows from Proposition 9.3"; its content is cited as (11.5.4) in the proof of Theorem 11.14,
  P2 l. 3569, and used in the proof of Theorem 11.10, P2 l. 3392) — `eq11_4_5`
* Unlabelled (§11.4, P2 l. 3264–3268: (11.4.8), from part (a) of the proof of Proposition 11.8, in the form (11.4.12);
  reused as a result in the proofs of Theorem 11.9, P2 l. 3319, and Theorem 11.14, P2 l. 3575) — `prop11_8_asymp`
* Definition (conformal at `ζ ∈ 𝕋`, recalled at P2 l. 3295: "In Section 4.3 we defined `f` to be conformal at `ζ` if
  `f` has a finite nonzero angular derivative") — exists: `Pommerenke1992.IsConformalAtBoundary` (the same
  definition)
* Theorem 11.9 (RoWa76, JenOi77; cited in the proof of Theorem 11.10, P2 l. 3396, 3430) — `thm11_9`
* Definition (`δ_n`, (11.4.14), Fig. 11.7; used in Theorem 11.10 and in the proof of Corollary 11.11) —
  `openingDefect`
* Theorem 11.10 (cited in the proof of Corollary 11.11, P2 l. 3454, 3462) — `thm11_10`
* Corollary 11.11 (War32; the Warschawski condition, named at P2 l. 2719, a local version of Theorem 3.5) —
  `cor11_11_a`, `cor11_11_b`

Not items (DESIGN §3): "Then, by Theorem 2.15, `Q(ρ)` … are crosscuts of `𝔻` that separate `0` from `ζ` if `ρ₀` is
small enough" (P2 l. 3216–3222; a recall of Theorem 2.15, (2.4.11), that no statement needs); "In particular we have
`T(ρ) ∈ Γ(ρ₁, ρ₂)` for `ρ₁ < ρ < ρ₂`" (P2 l. 3222; immediate from condition (iii) of the null-chain
`T(ρ₂), T(ρ), T(ρ₁), …`; used in the proof of Proposition 11.12); "We saw in Theorem 11.7 that (3) is a consequence of
the Visser-Ostrowski condition" (P2 l. 3236; a remark restating Theorem 11.7, which the proof of Theorem 11.9 cites
itself); "approximately additive" (P2 l. 3242; a name for (11.4.4), which is part of `prop11_8`); the proof of
Proposition 11.8, with the map (11.4.6) `s = π⁻¹ log((ζ + z)/(ζ - z)) + i/2` onto the strip `{0 < Im s < 1}` (reused
as an explicit construction at P2 l. 3317, 3319, 3553), (11.4.7), (11.4.9) and Propositions 9.4, 9.5, (9.2.5), (9.2.7);
"No strictly geometric characterization of conformality is known" (P2 l. 3295; a remark); the proof of Theorem 11.9
((11.4.12) is `prop11_8_asymp`; (11.4.13); Propositions 4.10, 4.11, 9.1, 9.2, (9.2.5); "it can be shown (RoWa76 or
JenOi77) that `f` is isogonal"); the remark of P2 l. 3333 on geometric characterizations of conformality (Fer44,
LeF55, Hali65, Eke71, RoWa77), which sets the standing assumption `G ⊆ 𝔻`, `ω ∈ 𝕋` of Theorem 11.10 and Corollary
11.11; the proof of Theorem 11.10 with (11.4.15)–(11.4.17) (the second line of the display at P2 l. 3393 is lost in
the OCR and is in the crop) and "(ii) ⇒ (iii): RoWa77, p. 9"; "We deduce a simple sufficient condition (War32; see
e.g. War67 and RoWa77 for generalizations) which is a local version of Theorem 3.5; compare also Theorem 4.14"
(P2 l. 3432; a remark); the proof of Corollary 11.11; Exercises 11.4.1–11.4.2.

**Conventions.** As in §11.1. Standing assumption of §11.4 (P2 l. 3208): `f` maps `𝔻` conformally onto `G ⊆ ℂ` and
has the angular limit `ω = f(ζ) ≠ ∞` at the given `ζ ∈ 𝕋` (`hf`, `hω`), and `T` is a system of circular crosscuts
(11.4.1) with bound `ρ₀` (`hT`); from P2 l. 3333 on (Theorem 11.10, Corollary 11.11) also `G ⊆ 𝔻` and `ω ∈ 𝕋`. `T` is
a function `ℝ → Set ℂ` used only on `(0, ρ₀]`, and `Γ(ρ₁, ρ₂)` only for `0 < ρ₁ < ρ₂ ≤ ρ₀`; so every statement with
`ρ_j → 0` bounds the radii by `ρ₀` as well. `mod Γ(ρ₁, ρ₂)` is
`LehtoVirtanen1973.arcFamilyModule (separatingCrosscuts G T ρ₁ ρ₂)` in `ℝ≥0∞`; it is finite and positive (the
region of `𝔻` between `Q(ρ₁)` and `Q(ρ₂)`, whose closures are disjoint, is a quadrilateral), and where the book forms
a difference with it, its finiteness is stated with it.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane toExt unitDisc IsConformalOnto)
open LehtoVirtanen1973 (SeparatesIn arcFamilyModule)

/-- **Definition (11.4.1)** (§11.4; P2 l. 3210–3216; used throughout §11.4–§11.5, restated at P2 l. 3492–3496). A
system of circular crosscuts `T(ρ)` of `G = f(𝔻)` with (11.4.1) `T(ρ) ⊆ ∂D(ω, ρ)` (`0 < ρ ≤ ρ₀`) that forms a
null-chain defining the prime end corresponding to `ζ`; more precisely, if `ρ_n ↘ 0` then `(T(ρ_n))` is a null-chain
(Section 2.4).
Modelling: `T : ℝ → Set ℂ`, used only on `(0, ρ₀]`; crosscuts and null-chains are those of Ch. 2 on `toExt G`;
"`ρ_n ↘ 0`" is a strictly decreasing sequence in `(0, ρ₀]` tending to `0` (equal radii would repeat a crosscut,
against condition (ii) of a null-chain). "Defining the prime end corresponding to `ζ`" is the last clause: the
preimages `f⁻¹(T(ρ))` shrink to `ζ` as `ρ → 0`; by Theorem 2.15 ((2.4.11)) a null-chain of `G` represents the prime
end `f̂(ζ')` if and only if its preimages converge to `ζ'`. (The alternative through `IsPrimeEndCorrespondence` of
§2.4 is heavier, and its meaning rests on Theorem 2.15.) The book's "if `ρ₀` is small enough" is absorbed: the system
is given. The definition is satisfiable: `f = id`, `ζ = ω = 1`, `T(ρ) = 𝔻 ∩ ∂D(1, ρ)`, `0 < ρ₀ < 2`. -/
def IsCircularCrosscutSystem (f : ℂ → ℂ) (ζ ω : ℂ) (ρ₀ : ℝ) (T : ℝ → Set ℂ) : Prop :=
  0 < ρ₀ ∧ (∀ ρ ∈ Ioc 0 ρ₀, T ρ ⊆ sphere ω ρ ∧ IsCrosscut (toExt (f '' unitDisc)) (toExt (T ρ))) ∧
    (∀ ρs : ℕ → ℝ, StrictAnti ρs → (∀ n, ρs n ∈ Ioc 0 ρ₀) → Tendsto ρs atTop (𝓝 0) →
      IsNullChain (toExt (f '' unitDisc)) (fun n => toExt (T (ρs n)))) ∧
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ ρ ∈ Ioc 0 ρ₀, ρ < δ → ∀ z ∈ unitDisc, f z ∈ T ρ → ‖z - ζ‖ < ε

/-- The crosscuts `Q(ρ) = f⁻¹(T(ρ))` of (11.4.2) (§11.4, P2 l. 3216–3222; used in (11.4.3), Theorem 11.13, (11.5.2) and
in proofs; helper), `0 < ρ ≤ ρ₀`.
Modelling: the preimage in `𝔻`. By Theorem 2.15 these are crosscuts of `𝔻` that separate `0` from `ζ` if `ρ₀` is small
enough (not needed by the statements). -/
def crosscutPreimage (f : ℂ → ℂ) (T : ℝ → Set ℂ) (ρ : ℝ) : Set ℂ :=
  {z | z ∈ unitDisc ∧ f z ∈ T ρ}

/-- **Definition** (§11.4, P2 l. 3222, Fig. 11.5; used in Proposition 11.8, (11.4.5), Theorem 11.9, the proof of
Theorem 11.10, Propositions 11.12, 11.15 and Theorems 11.13, 11.14). For `0 < ρ₁ < ρ₂ ≤ ρ₀`, `Γ(ρ₁, ρ₂)` denotes the
family of all crosscuts `C` of `G` that separate `T(ρ₁)` and `T(ρ₂)`.
Modelling: a family of point sets of `Ĉ` (`Set (Set ExtPlane)`), the type of `LehtoVirtanen1973.arcFamilyModule`
(§11.1); crosscuts are `IsCrosscut (toExt G)` (Ch. 2), and "separate" is `LehtoVirtanen1973.SeparatesIn (toExt G)`
(`T(ρ₁)` and `T(ρ₂)` lie in different components of `G ∖ C`). The caption of Fig. 11.1 speaks of "curves in the
shaded domain"; the formal definition is this one of §11.4. -/
def separatingCrosscuts (G : Set ℂ) (T : ℝ → Set ℂ) (ρ₁ ρ₂ : ℝ) : Set (Set ExtPlane) :=
  {C | IsCrosscut (toExt G) C ∧ SeparatesIn (toExt G) C (toExt (T ρ₁)) (toExt (T ρ₂))}

/-- **Proposition 11.8** (§11.4; RoWa76, JenOi77; P2 l. 3224–3232; cited in the proofs of Theorem 11.9, P2 l. 3319, and
Theorem 11.14, P2 l. 3575). The condition (11.4.3) `sup_{z ∈ Q(ρ)} |z - ζ| / inf_{z ∈ Q(ρ)} |z - ζ| → 1` as `ρ → 0`
holds if and only if, for every `ε > 0`, there exists `δ > 0` such that (11.4.4)
`mod Γ(ρ₁, ρ₃) < mod Γ(ρ₁, ρ₂) + mod Γ(ρ₂, ρ₃) + ε` for `ρ₁ < ρ₂ < ρ₃ < δ`.
Modelling: under the standing assumption of §11.4. The quotient in (11.4.3) is `≥ 1` and `Q(ρ)` is nonempty, so
(11.4.3) is: for every `ε > 0` there is `δ > 0` with `|z - ζ| ≤ (1 + ε)|z' - ζ|` for all `z, z' ∈ Q(ρ)`, `0 < ρ < δ`
(no quotient of a supremum by an infimum is formed). In (11.4.4) `0 < ρ₁` and `ρ₃ ≤ ρ₀` (where `Γ` is defined) are
explicit; the modules are `ℝ≥0∞`-valued and finite, and `ε` enters as `ENNReal.ofReal ε`. -/
theorem prop11_8 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) {ρ₀ : ℝ} {T : ℝ → Set ℂ}
    (hT : IsCircularCrosscutSystem f ζ ω ρ₀ T) :
    (∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ ρ ∈ Ioc 0 ρ₀, ρ < δ →
      ∀ z ∈ crosscutPreimage f T ρ, ∀ z' ∈ crosscutPreimage f T ρ, ‖z - ζ‖ ≤ (1 + ε) * ‖z' - ζ‖) ↔
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ ρ₁ ρ₂ ρ₃ : ℝ, 0 < ρ₁ → ρ₁ < ρ₂ → ρ₂ < ρ₃ → ρ₃ < δ → ρ₃ ≤ ρ₀ →
      arcFamilyModule (separatingCrosscuts G T ρ₁ ρ₃) <
        arcFamilyModule (separatingCrosscuts G T ρ₁ ρ₂) + arcFamilyModule (separatingCrosscuts G T ρ₂ ρ₃) +
          ENNReal.ofReal ε := by
  sorry

/-- **Formula (11.4.5)** (§11.4; P2 l. 3236–3242, "It follows from Proposition 9.3"; its content is cited as (11.5.4) in
the proof of Theorem 11.14, P2 l. 3569, and used in the proof of Theorem 11.10, P2 l. 3392). Under the standing
assumption of §11.4, `mod Γ(ρ₁, ρ₃) ≥ mod Γ(ρ₁, ρ₂) + mod Γ(ρ₂, ρ₃)` holds for all `ρ₁ < ρ₂ < ρ₃ ≤ ρ₀`.
Modelling: `0 < ρ₁` is implicit (the families are defined for `0 < ρ₁ < ρ₂ ≤ ρ₀`). Stated as a U+ item: a numbered
display stated outside a proof, whose restatement (11.5.4) is cited by number. -/
theorem eq11_4_5 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) {ρ₀ : ℝ} {T : ℝ → Set ℂ}
    (hT : IsCircularCrosscutSystem f ζ ω ρ₀ T) {ρ₁ ρ₂ ρ₃ : ℝ} (h₁ : 0 < ρ₁) (h₁₂ : ρ₁ < ρ₂) (h₂₃ : ρ₂ < ρ₃)
    (h₃ : ρ₃ ≤ ρ₀) :
    arcFamilyModule (separatingCrosscuts G T ρ₁ ρ₂) + arcFamilyModule (separatingCrosscuts G T ρ₂ ρ₃) ≤
      arcFamilyModule (separatingCrosscuts G T ρ₁ ρ₃) := by
  sorry

/-- **Unlabelled claim** (§11.4, P2 l. 3264–3268 and 3319–3325: (11.4.8) in the form (11.4.12), from part (a) of the
proof of Proposition 11.8; reused as a result in the proofs of Theorem 11.9, P2 l. 3319, "As in part (a) of the proof
of Proposition 11.8 we deduce that (8) holds which, by (6), can be rewritten (12)", and of Theorem 11.14, P2 l. 3575,
"As in part (a) of its proof we deduce that …"). If (11.4.3) holds, then
`mod Γ(ρ₁, ρ₂) = π⁻¹ log |(z₂ - ζ)/(z₁ - ζ)| + o(1)` as `ρ₁ < ρ₂ → 0`, where `z_j ∈ Q(ρ_j)`.
Modelling: under the standing assumption of §11.4, with (11.4.3) in the form of `prop11_8`. The `o(1)`: for every
`ε > 0` there is `δ > 0` such that for `0 < ρ₁ < ρ₂ < δ` (`ρ₂ ≤ ρ₀`) and all `z₁ ∈ Q(ρ₁)`, `z₂ ∈ Q(ρ₂)` the module is
finite and differs from `π⁻¹ log(|z₂ - ζ|/|z₁ - ζ|)` by less than `ε` (the finiteness is part of the claim, which forms
the difference; `z_j ≠ ζ` since `z_j ∈ 𝔻`). The form (11.4.12) is the one both reuses need; the book's (11.4.8),
`mod Γ(ρ₁, ρ₂) = Re(s₁ - s₂) + o(1)` with `s` of (11.4.6), differs from it by
`π⁻¹ log |(ζ + z₁)/(ζ + z₂)| → 0`. -/
theorem prop11_8_asymp {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) {ρ₀ : ℝ} {T : ℝ → Set ℂ}
    (hT : IsCircularCrosscutSystem f ζ ω ρ₀ T)
    (h3 : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ ρ ∈ Ioc 0 ρ₀, ρ < δ →
      ∀ z ∈ crosscutPreimage f T ρ, ∀ z' ∈ crosscutPreimage f T ρ, ‖z - ζ‖ ≤ (1 + ε) * ‖z' - ζ‖) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ ρ₁ ρ₂ : ℝ, 0 < ρ₁ → ρ₁ < ρ₂ → ρ₂ < δ → ρ₂ ≤ ρ₀ →
      ∀ z₁ ∈ crosscutPreimage f T ρ₁, ∀ z₂ ∈ crosscutPreimage f T ρ₂,
        arcFamilyModule (separatingCrosscuts G T ρ₁ ρ₂) ≠ ⊤ ∧
          |(arcFamilyModule (separatingCrosscuts G T ρ₁ ρ₂)).toReal -
            π⁻¹ * Real.log (‖z₂ - ζ‖ / ‖z₁ - ζ‖)| < ε := by
  sorry

/-- **Theorem 11.9** (§11.4; RoWa76, JenOi77; P2 l. 3297–3309; cited in the proof of Theorem 11.10, P2 l. 3396, 3430).
The function `f` is conformal at `ζ ∈ 𝕋` if and only if (11.4.10) `mod Γ(ρ₁, ρ₂) - π⁻¹ log(ρ₂/ρ₁) → 0` as
`0 < ρ₁ < ρ₂ → 0` and if furthermore there is `α` such that (11.4.11)
`{w : |arg[w - ω] - α| < π/2 - ε, |w - ω| < δ} ⊆ G` for every `ε > 0` and some `δ = δ(ε) > 0`.
[CORRECTION] In (11.4.11) the point `w = ω` is excluded (crop ✓: the book's set is as printed). `arg[w - ω]` is
undefined at `w = ω`, and with `arg 0 = 0` (Mathlib's `Complex.arg`) the set would contain `ω ∉ G`, so (11.4.11)
would never hold and the theorem would be false: `f = id`, `ζ = ω = 1` (`G = 𝔻`) is conformal at `1`. This is a
modelling point, not an error of the book.
Modelling: under the standing assumption of §11.4, for every system `T` of circular crosscuts. (11.4.10): for every
`ε > 0` there is `δ > 0` such that for `0 < ρ₁ < ρ₂ < δ` (`ρ₂ ≤ ρ₀`) the module is finite and differs from
`π⁻¹ log(ρ₂/ρ₁)` by less than `ε` (the book forms the difference). (11.4.11): `α` is an angle, determined modulo
`2π`, and `|arg[w - ω] - α| < π/2 - ε` (the angle between `w - ω` and the direction `e^{iα}`) is written
`|arg(e^{-iα}(w - ω))| < π/2 - ε`, which does not depend on the representative of `α` or on the branch cut of
`Complex.arg`; the literal `|Complex.arg (w - ω) - α|` would, for `α = 2π`, describe the empty set (the values of
`Complex.arg` lie in `(-π, π]`), and (11.4.11) would become trivial. -/
theorem thm11_9 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) {ρ₀ : ℝ} {T : ℝ → Set ℂ}
    (hT : IsCircularCrosscutSystem f ζ ω ρ₀ T) :
    IsConformalAtBoundary f ζ ↔
      (∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ ρ₁ ρ₂ : ℝ, 0 < ρ₁ → ρ₁ < ρ₂ → ρ₂ < δ → ρ₂ ≤ ρ₀ →
        arcFamilyModule (separatingCrosscuts G T ρ₁ ρ₂) ≠ ⊤ ∧
          |(arcFamilyModule (separatingCrosscuts G T ρ₁ ρ₂)).toReal - π⁻¹ * Real.log (ρ₂ / ρ₁)| < ε) ∧
      ∃ α : ℝ, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
        {w : ℂ | w ≠ ω ∧ |arg (exp (-(α * I)) * (w - ω))| < π / 2 - ε ∧ ‖w - ω‖ < δ} ⊆ G := by
  sorry

/-- **Definition (11.4.14)** (§11.4; P2 l. 3335–3339, Fig. 11.7; used in Theorem 11.10 and in the proof of Corollary
11.11). For a sequence `ρ_n ↘ 0`, `δ_n` is the smallest number such that
`{w ∈ 𝔻 : ρ_{n+1} < |w - ω| ≤ ρ_n, |arg(1 - ω̄w)| < π/2 - δ_n} ⊆ G = f(𝔻)`.
`openingDefect G ω a b` is this number for `ρ_{n+1} = a`, `ρ_n = b`, so `δ_n = openingDefect G ω ρ_{n+1} ρ_n`.
[CORRECTION] The book defines "`δ_n > 0` as the smallest number"; read `δ_n ≥ 0`. When `G` contains the whole piece
`{w ∈ 𝔻 : ρ_{n+1} < |w - ω| ≤ ρ_n}` (for instance `f = id`, `G = 𝔻`), every `δ ≥ 0` has the property (on `𝔻`,
`|arg(1 - ω̄w)| < π/2` always holds, so negative `δ` give the same region as `δ = 0`), and there is no smallest
positive one; the smallest non-negative one is `0`. The crop shows `ρ_{n+1}` with a speck that the OCR reads as
`ρ'_{n+1}`; the proof's (15) and (16) have `ρ_{n+1}`, `σ_{n+1}`.
Modelling: the infimum of the set of `δ ≥ 0` with the property. The set contains `π/2` (the region is then empty) and
is bounded below by `0`, so `sInf` is a genuine infimum in `[0, π/2]`; it is attained, since the region for `δ` is the
union of the regions for `δ' > δ`, so "smallest" is right. On `𝔻`, `1 - ω̄w ≠ 0` for `ω ∈ 𝕋`. -/
def openingDefect (G : Set ℂ) (ω : ℂ) (a b : ℝ) : ℝ :=
  sInf {δ : ℝ | 0 ≤ δ ∧
    {w : ℂ | w ∈ unitDisc ∧ a < ‖w - ω‖ ∧ ‖w - ω‖ ≤ b ∧ |arg (1 - conj ω * w)| < π / 2 - δ} ⊆ G}

/-- **Theorem 11.10** (§11.4; P2 l. 3341–3353; cited in the proof of Corollary 11.11, P2 l. 3454, 3462). If `G ⊆ 𝔻` and
`ω ∈ 𝕋` then the following three conditions are equivalent:
(i) `f` is conformal at `ζ`;
(ii) `Σ_n δ_n (ρ_n - ρ_{n+1})/ρ_n < ∞` for all `(ρ_n)` with `Σ_n ((ρ_n - ρ_{n+1})/ρ_n)² < ∞`;
(iii) there exists a sequence `(ρ_n)` such that `Σ_n δ_n (ρ_n - ρ_{n+1})/ρ_n < ∞`, `Σ_n δ_n² < ∞`.
Modelling: under the standing assumption of §11.4 (no system `T` is needed) with `G ⊆ 𝔻`, `ω ∈ 𝕋`. The sequences are
the `ρ_n ↘ 0` of (11.4.14): positive, antitone, tending to `0` (a repeated radius gives `δ_n = 0` and a zero term);
`δ_n = openingDefect G ω ρ_{n+1} ρ_n`. The series have non-negative terms, and "`< ∞`" is `Summable`.
[CORRECTION] (1) In (iii) the side condition `Σ ((ρ_n − ρ_{n+1})/ρ_n)² < ∞` of (ii) is added: for sparse sequences
(iii) ⇒ (i) fails (`G₀` of (11.4.18) with `δ(ρ) = 1/log(1/ρ)` and `ρ_{n+1} = ρ_n²` satisfies (iii), but `f` is not
conformal; the book's proof needs `Σ δ_n log(ρ_n/ρ_{n+1}) < ∞`). (2) `ζ` is tied to the prime end reached along the
radius towards `ω` (hypothesis `hζ`): otherwise `G = 𝔻 ∖ S` with a spiralling slit `S` creating a second,
cusp-shaped prime end over `1` is a counterexample (leader audit of batch 6). -/
theorem thm11_10 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) (hGD : G ⊆ unitDisc) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) (hω1 : ω ∈ sphere (0 : ℂ) 1)
    (hζ : ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ z ∈ unitDisc, ∀ ρ ∈ Ioo 0 η, f z = (1 - ρ) * ω → ‖z - ζ‖ < ε) :
    List.TFAE [IsConformalAtBoundary f ζ,
      ∀ ρ : ℕ → ℝ, (∀ n, 0 < ρ n) → Antitone ρ → Tendsto ρ atTop (𝓝 0) →
        Summable (fun n => ((ρ n - ρ (n + 1)) / ρ n) ^ 2) →
        Summable (fun n => openingDefect G ω (ρ (n + 1)) (ρ n) * (ρ n - ρ (n + 1)) / ρ n),
      ∃ ρ : ℕ → ℝ, (∀ n, 0 < ρ n) ∧ Antitone ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
        Summable (fun n => ((ρ n - ρ (n + 1)) / ρ n) ^ 2) ∧
        Summable (fun n => openingDefect G ω (ρ (n + 1)) (ρ n) * (ρ n - ρ (n + 1)) / ρ n) ∧
        Summable (fun n => openingDefect G ω (ρ (n + 1)) (ρ n) ^ 2)] := by
  sorry

/-- **Corollary 11.11** (§11.4; War32; the Warschawski condition, named at P2 l. 2719; P2 l. 3434–3446), first part.
Let `f` map `𝔻` conformally into `𝔻` and let `ζ ∈ 𝕋`, `ω = f(ζ) ∈ 𝕋`. We define (11.4.18)
`G₀ = {(1 - ρe^{iϑ})ω : 0 < ρ < ρ₀, |ϑ| < π/2 - δ(ρ)}`, where `δ(ρ)` (`0 < ρ < ρ₀`) is a continuous increasing
function. If `f(𝔻) ⊇ G₀` and if (11.4.19) `∫₀^{ρ₀} δ(ρ)ρ⁻¹ dρ < ∞`, then `f` is conformal at `ζ`.
Modelling: `f(ζ)` is the angular limit; "increasing" is `MonotoneOn` (non-decreasing, the book's convention) on
`(0, ρ₀)`; `0 < ρ₀`. `G₀ ⊆ f(𝔻) ⊆ 𝔻` forces `δ(ρ) > 0`, since `|1 - ρe^{iϑ}|² = 1 - 2ρ cos ϑ + ρ² > 1` when
`cos ϑ < ρ/2`, so (11.4.19) is the integrability of the positive continuous function `δ(ρ)/ρ` on `(0, ρ₀)`. The
hypothesis is equivalent to integrability near `0` (apply it with a smaller `ρ₀`). The
§11.1 form of the Warschawski condition ("if and only if", domains (11.1.3)) is a preview of this corollary.
[CORRECTION] `ζ` is tied to the prime end reached along the radius towards `ω` (hypothesis `hζ`), as in
`thm11_10`: a spiralling slit creating a second prime end over `ω` is otherwise a counterexample. -/
theorem cor11_11_a {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hD : MapsTo f unitDisc unitDisc) {ζ ω : ℂ} (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω)
    (hω1 : ω ∈ sphere (0 : ℂ) 1)
    (hζ : ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ z ∈ unitDisc, ∀ ρ ∈ Ioo 0 η, f z = (1 - ρ) * ω → ‖z - ζ‖ < ε)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {δ : ℝ → ℝ} (hδc : ContinuousOn δ (Ioo 0 ρ₀))
    (hδm : MonotoneOn δ (Ioo 0 ρ₀))
    (hG₀ : {w : ℂ | ∃ ρ ∈ Ioo 0 ρ₀, ∃ ϑ : ℝ, |ϑ| < π / 2 - δ ρ ∧ w = (1 - ρ * exp (ϑ * I)) * ω} ⊆ f '' unitDisc)
    (h19 : IntegrableOn (fun ρ => δ ρ / ρ) (Ioo 0 ρ₀)) :
    IsConformalAtBoundary f ζ := by
  sorry

/-- **Corollary 11.11** (§11.4), second part. Conversely, under the hypotheses of the first part on `f`, `ζ`, `ω` and
`δ`, if `f(𝔻) = G₀` and if `f` is conformal at `ζ` then (11.4.19) `∫₀^{ρ₀} δ(ρ)ρ⁻¹ dρ < ∞` holds.
[CORRECTION] The conclusion is read as convergence of (11.4.19) at `0`: `∫₀^{ρ₁} δ(ρ)ρ⁻¹ dρ < ∞` for some
`0 < ρ₁ ≤ ρ₀`, which is what the proof shows. Literally (11.4.19) can fail when `δ` blows up at `ρ₀`: for `ρ₀ = 1`,
`ω = 1`, `δ(ρ) = ρ/(1 - ρ)`, `G₀` is a Jordan domain (the slices are empty once `δ ≥ π/2`), its Riemann map is
conformal at the point over `1` by the first part applied with `ρ₀ = 1/2`, but `∫₀¹ dρ/(1 - ρ) = ∞`. The page
image of (11.4.19) (`images\402da4a9…df433.jpg`, P2 l. 3443) prints `∫₀^{ρ₀} δ(ρ)ρ⁻¹ dρ < ∞`, so this is the print,
not the OCR; the book's proof of the converse (P2 l. 3448ff.) only bounds `∫₀^{1/m} δ(ρ)ρ⁻¹ dρ` for a suitable `m`.
Modelling: as `cor11_11_a`; `f(𝔻) = G₀ ⊆ 𝔻` again forces `δ > 0`. -/
theorem cor11_11_b {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hD : MapsTo f unitDisc unitDisc) {ζ ω : ℂ} (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω)
    (hω1 : ω ∈ sphere (0 : ℂ) 1) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {δ : ℝ → ℝ} (hδc : ContinuousOn δ (Ioo 0 ρ₀))
    (hδm : MonotoneOn δ (Ioo 0 ρ₀))
    (hG₀ : f '' unitDisc = {w : ℂ | ∃ ρ ∈ Ioo 0 ρ₀, ∃ ϑ : ℝ, |ϑ| < π / 2 - δ ρ ∧ w = (1 - ρ * exp (ϑ * I)) * ω})
    (hc : IsConformalAtBoundary f ζ) :
    ∃ ρ₁ ∈ Ioc 0 ρ₀, IntegrableOn (fun ρ => δ ρ / ρ) (Ioo 0 ρ₁) := by
  sorry

end Pommerenke1992
