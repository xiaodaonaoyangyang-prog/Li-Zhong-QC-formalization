import References.Pommerenke1992.Ch11.S04_ModuleAndConformality

/-!
# Pommerenke 1992, Ch. 11 §11.5 The Ahlfors Integral

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 11 *Local Boundary Behaviour*, §11.5; source
`full.md` of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3…` (P2), lines 3490–3705.

* Definition (`λ(ρ) = Λ(T(ρ))`, (11.5.1); used in Proposition 11.12, Theorems 11.13, 11.14, (11.5.7), (11.5.8) and
  the proof of Theorem 11.16) — `crosscutLength`
* Definition (the set `A = ⋃_{0<ρ<ρ₀} Q(ρ) = f⁻¹(B)` of (11.5.2); used in Theorem 11.14 and the proof of Theorem
  11.16; helper) — `crosscutPreimageUnion`
* Proposition 11.12 ((11.5.3) cited in the proofs of Theorems 11.13 and 11.14, P2 l. 3553, 3563, 3569; complemented
  by Proposition 11.15, P2 l. 3591) — `prop11_12_a`, `prop11_12_b`
* Formula (11.5.4) (in the proof of Proposition 11.12; cited in the proof of Theorem 11.14, P2 l. 3569) — exists:
  `Pommerenke1992.eq11_4_5` (the same inequality for the radii ρ₁′ < ρ₁ < ρ₂: the integrals of 1/λ over the adjacent
  intervals add up and are finite, so cancelling them turns (11.5.4) into (11.4.5); the additivity of the lower
  integral over adjacent intervals needs no measurability of the integrand)
* Theorem 11.13 (the Ahlfors distortion theorem, Ahl30, Tei38; the second inequality cited in the proof of Theorem
  11.14, P2 l. 3589) — `thm11_13`
* Theorem 11.14 (Eke67; proof RoWa76; cited in the proof of Theorem 11.16, P2 l. 3659, and in Exercises 11.5.1,
  11.5.2) — `thm11_14`
* Unlabelled (§11.5, P2 l. 3589, end of the proof of Theorem 11.14: "we have shown moreover that the limit is positive
  if and only if `a` is finite"; cited in the proof of Theorem 11.16, P2 l. 3659, and in Exercise 11.5.1) —
  `thm11_14_pos`
* Definition (the domains (11.5.9) = (11.1.3), Fig. 11.1, and their circular crosscuts; used in Proposition 11.15,
  Theorem 11.16 and Exercises 11.5.3–11.5.4; helpers) — `polarSectorDomain`, `polarSectorArc`
* Proposition 11.15 (War42, RoWa76; cited in the proof of Theorem 11.16, P2 l. 3659) — `prop11_15`
* Theorem 11.16 (War42; imaginary part: War42, RoWa76; previewed as (11.1.4); cited at P2 l. 3663, 3665) —
  `thm11_16`

Not items (DESIGN §3): the restatements of (11.4.1), (11.4.2) and of `Γ(ρ₁, ρ₂)` (P2 l. 3492–3498, 3510–3513,
Fig. 11.8); "so that `0 < λ(ρ) ≤ 2πρ`" (P2 l. 3504; immediate); the proof of Proposition 11.12 (the Schwarz inequality,
Proposition 9.3; the set `B` of (11.5.2) is used only there); the proof of Theorem 11.13 ((11.4.6), reflection,
`e^{πs}`, Teichmüller's estimate (9.2.19); Ahl73, p. 77); the proof of Theorem 11.14 with (11.5.7) (the limit
`0 ≤ a ≤ +∞` of `mod Γ(ρ₁, ρ₂) - ∫_{ρ₁}^{ρ₂} λ(ρ)⁻¹ dρ` as `ρ₁ → 0`, which exists by Proposition 11.12; it enters
`thm11_14_pos` through its finiteness), (11.5.8) and the case `a = +∞`; "In particular it follows that the limit `a` in
(7) is finite" (P2 l. 3611; immediate from (11.5.11), (11.5.10) and `λ(ρ) = ρ(ϑ₊ - ϑ₋)`; the proof of Theorem 11.16
cites Proposition 11.15 itself) and the references Ahl30, LeF55, JenOi71, RoWa79a, RoWa79b, RoWa83; the proof of
Proposition 11.15 with (11.5.12)–(11.5.15) and (9.2.2); the proof of Theorem 11.16 with (11.5.17) ("in the present
situation we have `λ(ρ) = ρ(ϑ₊(ρ) - ϑ₋(ρ))`, and `A` is identical with `𝔻` near `ζ`"; it prints "Proposition 11.14"
for Theorem 11.14 [misprint?]) and the reference to War42, RoWa76 for the imaginary part; "It is clear that Theorem
11.16 also holds if `G` has the form (9) only in a neighbourhood of `ω`" (P2 l. 3663; not cited); the outward
pointing cusp (11.5.18), (11.5.19) (P2 l. 3665–3675; derived from Theorem 11.16 and never cited; P1 l. 2448, "will be
considered in Chapter 11", is a forward reference); Exercises 11.5.1–11.5.4.

**Conventions.** As in §11.1 and §11.4. Standing assumption of §11.5 (P2 l. 3492): as in §11.4 (`f` onto `G ⊆ ℂ`, the
finite angular limit `ω` at `ζ`, a system `T` of circular crosscuts with bound `ρ₀`, `Q(ρ) = f⁻¹(T(ρ))`).
*The Ahlfors integral.* There is no definition of it: the book writes it in two normalizations, `∫ dρ/λ(ρ)`
(Proposition 11.12, (11.5.7), (11.5.8)) and `∫ π/λ(ρ) dρ` (Theorems 11.13, 11.14, (11.1.4), (11.5.16)), and the stated
constants depend on the factor, so each integral is written as printed. The integrals of `1/λ` and `π/λ` are lower
Lebesgue integrals `∫⁻ ρ in Ioo ρ₁ ρ₂, …` in `ℝ≥0∞` over the parameter interval (`1/0 = ∞` is never seen: `λ > 0`
for a crosscut). No measurability of `ρ ↦ λ(ρ)` is assumed (inventory Q11.3): it is not known for an arbitrary
system `T`, the lower integral needs none, and it is the Lebesgue integral whenever `λ` is measurable (for the arcs of
(11.5.9), `λ(ρ) = ρ(ϑ₊(ρ) - ϑ₋(ρ))` is continuous). The integrals of explicit functions of `ϑ_±` in Proposition 11.15
are lower integrals of the `ENNReal.ofReal` of non-negative integrands, and the integral in Theorem 11.16 is the
interval integral of a continuous function on a compact subinterval of `(0, c)`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane toExt unitDisc IsConformalOnto)
open LehtoVirtanen1973 (arcFamilyModule)

/-- **Definition (11.5.1)** (§11.5; P2 l. 3498–3504; used in Proposition 11.12, Theorems 11.13, 11.14, (11.5.7),
(11.5.8) and the proof of Theorem 11.16). `λ(ρ) = Λ(T(ρ))` (`0 < ρ ≤ ρ₀`), "so that `0 < λ(ρ) ≤ 2πρ`".
Modelling: `Λ` is `μH[1]` (§11.1), with values in `ℝ≥0∞`; for an arc of a circle it is the arc length
(Proposition 6.2). `T` is used only on `(0, ρ₀]`. -/
def crosscutLength (T : ℝ → Set ℂ) (ρ : ℝ) : ℝ≥0∞ :=
  μH[1] (T ρ)

/-- The set `A` of (11.5.2) (§11.5, P2 l. 3506–3508; used in Theorem 11.14 and the proof of Theorem 11.16; helper):
`A = ⋃_{0<ρ<ρ₀} Q(ρ) = f⁻¹(B)` with `B = ⋃_{0<ρ<ρ₀} T(ρ)`.
Modelling: the points of `𝔻` that `f` maps into some `T(ρ)`, `0 < ρ < ρ₀`; `B` is used only in the proof of
Proposition 11.12. -/
def crosscutPreimageUnion (f : ℂ → ℂ) (T : ℝ → Set ℂ) (ρ₀ : ℝ) : Set ℂ :=
  {z | z ∈ unitDisc ∧ ∃ ρ ∈ Ioo 0 ρ₀, f z ∈ T ρ}

/-- **Proposition 11.12** (§11.5; P2 l. 3515–3521; (11.5.3) cited in the proofs of Theorems 11.13 and 11.14, P2 l. 3553,
3563, 3569; complemented by Proposition 11.15, P2 l. 3591), first part. If `0 < ρ₁ < ρ₂ ≤ ρ₀` then (11.5.3)
`mod Γ(ρ₁, ρ₂) - ∫_{ρ₁}^{ρ₂} dρ/λ(ρ) ≥ 0`.
Modelling: under the standing assumption of §11.5; additively (§11.1), `∫_{ρ₁}^{ρ₂} dρ/λ(ρ) ≤ mod Γ(ρ₁, ρ₂)` in
`ℝ≥0∞`, with the lower integral (file header). -/
theorem prop11_12_a {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) {ρ₀ : ℝ} {T : ℝ → Set ℂ}
    (hT : IsCircularCrosscutSystem f ζ ω ρ₀ T) {ρ₁ ρ₂ : ℝ} (h₁ : 0 < ρ₁) (h₁₂ : ρ₁ < ρ₂) (h₂ : ρ₂ ≤ ρ₀) :
    ∫⁻ ρ in Ioo ρ₁ ρ₂, (crosscutLength T ρ)⁻¹ ≤ arcFamilyModule (separatingCrosscuts G T ρ₁ ρ₂) := by
  sorry

/-- **Proposition 11.12** (§11.5), second part. The difference `mod Γ(ρ₁, ρ₂) - ∫_{ρ₁}^{ρ₂} dρ/λ(ρ)` is decreasing in
`ρ₁`.
Modelling: for `0 < ρ₁' < ρ₁ < ρ₂ ≤ ρ₀` the claim is `mod Γ(ρ₁', ρ₂) - ∫_{ρ₁'}^{ρ₂} ≥ mod Γ(ρ₁, ρ₂) - ∫_{ρ₁}^{ρ₂}`.
Since `∫_{ρ₁'}^{ρ₂} = ∫_{ρ₁'}^{ρ₁} + ∫_{ρ₁}^{ρ₂}` and `∫_{ρ₁}^{ρ₂}` is finite (by the first part, the module being
finite), this is the additive form `mod Γ(ρ₁, ρ₂) + ∫_{ρ₁'}^{ρ₁} dρ/λ(ρ) ≤ mod Γ(ρ₁', ρ₂)` stated here. -/
theorem prop11_12_b {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) {ρ₀ : ℝ} {T : ℝ → Set ℂ}
    (hT : IsCircularCrosscutSystem f ζ ω ρ₀ T) {ρ₁' ρ₁ ρ₂ : ℝ} (h₁' : 0 < ρ₁') (h₁'₁ : ρ₁' < ρ₁) (h₁₂ : ρ₁ < ρ₂)
    (h₂ : ρ₂ ≤ ρ₀) :
    arcFamilyModule (separatingCrosscuts G T ρ₁ ρ₂) + ∫⁻ ρ in Ioo ρ₁' ρ₁, (crosscutLength T ρ)⁻¹ ≤
      arcFamilyModule (separatingCrosscuts G T ρ₁' ρ₂) := by
  sorry

/-- **Theorem 11.13** (§11.5; the Ahlfors distortion theorem, Ahl30, Tei38; P2 l. 3543–3551; the second inequality is
cited in the proof of Theorem 11.14, P2 l. 3589). If `0 < ρ₁ < ρ₂ ≤ ρ₀` and `z₁ ∈ Q(ρ₁)`, `z₂ ∈ Q(ρ₂)` then (11.5.5)
`exp(∫_{ρ₁}^{ρ₂} π/λ(ρ) dρ) ≤ exp[π mod Γ(ρ₁, ρ₂)]
  < 32 inf |(z₂ - ζ)/(z₂ + ζ)| / sup |(z₁ - ζ)/(z₁ + ζ)|`;
if the last quotient is `< 1` it is replaced by `1`.
Modelling: under the standing assumption of §11.5. The infimum is over `z₂ ∈ Q(ρ₂)` and the supremum over
`z₁ ∈ Q(ρ₁)`, taken in `ℝ≥0∞` together with their quotient `q`, so that no junk value enters (`z + ζ ≠ 0` on `𝔻`;
`Q(ρ₁)` is nonempty and misses `ζ`, so the supremum is positive; `q` is finite). "Replaced by `1`" is `max 1 q`. The
first inequality is `∫⁻ π/λ ≤ π mod Γ(ρ₁, ρ₂)` (`exp` is increasing); the second asserts that the module is finite
and `exp[π mod Γ(ρ₁, ρ₂)] < 32 max(1, q)`. -/
theorem thm11_13 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) {ρ₀ : ℝ} {T : ℝ → Set ℂ}
    (hT : IsCircularCrosscutSystem f ζ ω ρ₀ T) {ρ₁ ρ₂ : ℝ} (h₁ : 0 < ρ₁) (h₁₂ : ρ₁ < ρ₂) (h₂ : ρ₂ ≤ ρ₀) :
    ∫⁻ ρ in Ioo ρ₁ ρ₂, ENNReal.ofReal π * (crosscutLength T ρ)⁻¹ ≤
        ENNReal.ofReal π * arcFamilyModule (separatingCrosscuts G T ρ₁ ρ₂) ∧
      arcFamilyModule (separatingCrosscuts G T ρ₁ ρ₂) ≠ ⊤ ∧
      ENNReal.ofReal (Real.exp (π * (arcFamilyModule (separatingCrosscuts G T ρ₁ ρ₂)).toReal)) <
        32 * max 1 ((⨅ z ∈ crosscutPreimage f T ρ₂, ‖(z - ζ) / (z + ζ)‖ₑ) /
          ⨆ z ∈ crosscutPreimage f T ρ₁, ‖(z - ζ) / (z + ζ)‖ₑ) := by
  sorry

/-- **Theorem 11.14** (§11.5; Eke67; proof RoWa76; P2 l. 3555–3561; cited in the proof of Theorem 11.16, P2 l. 3659, and
in Exercises 11.5.1, 11.5.2). If `A` is given by (11.5.2) then (11.5.6)
`lim_{z → ζ, z ∈ A} |z - ζ| exp(∫_{|f(z) - ω|}^{ρ₀} π/λ(ρ) dρ) ≠ ∞` exists.
Modelling: under the standing assumption of §11.5. For `z ∈ A`, `|f(z) - ω| ∈ (0, ρ₀)` is the `ρ` with `f(z) ∈ T(ρ)`,
and the integral is finite (it is at most `π mod Γ(|f(z) - ω|, ρ₀)` by Proposition 11.12); this finiteness is stated
first, so `.toReal` sees no junk. "`≠ ∞` exists" is the existence of a real limit `L` along `z → ζ`, `z ∈ A` (`ζ` lies
in the closure of `A`, the `Q(ρ)` shrinking to `ζ`). -/
theorem thm11_14 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) {ρ₀ : ℝ} {T : ℝ → Set ℂ}
    (hT : IsCircularCrosscutSystem f ζ ω ρ₀ T) :
    (∀ z ∈ crosscutPreimageUnion f T ρ₀,
      ∫⁻ ρ in Ioo ‖f z - ω‖ ρ₀, ENNReal.ofReal π * (crosscutLength T ρ)⁻¹ ≠ ⊤) ∧
    ∃ L : ℝ, Tendsto (fun z => ‖z - ζ‖ *
        Real.exp (∫⁻ ρ in Ioo ‖f z - ω‖ ρ₀, ENNReal.ofReal π * (crosscutLength T ρ)⁻¹).toReal)
      (𝓝[crosscutPreimageUnion f T ρ₀] ζ) (𝓝 L) := by
  sorry

/-- **Unlabelled claim** (§11.5, P2 l. 3589, end of the proof of Theorem 11.14; cited in the proof of Theorem 11.16,
P2 l. 3659, "the limit in (6) is positive as we remarked in the proof of Proposition [Theorem] 11.14", and in Exercise
11.5.1). "We have shown moreover that the limit is positive if and only if `a` is finite", where (11.5.7)
`mod Γ(ρ₁, ρ₂) - ∫_{ρ₁}^{ρ₂} λ(ρ)⁻¹ dρ → a` as `ρ₁ → 0`, `0 ≤ a ≤ +∞`.
Modelling: under the standing assumption of §11.5; `L` is the limit (11.5.6) of `thm11_14` (the hypothesis `hL`
identifies it; the filter is nontrivial, so the limit is unique). `a` is taken with `ρ₂ = ρ₀`, as in the proof's case
`a = +∞` (P2 l. 3583–3589). By Proposition 11.12 the difference `mod Γ(ρ₁, ρ₀) - ∫_{ρ₁}^{ρ₀} λ⁻¹` is `≥ 0` and
decreasing in `ρ₁`, so `a` is its supremum, and `a < ∞` is its boundedness, written additively (§11.1):
`mod Γ(ρ₁, ρ₀) ≤ ∫_{ρ₁}^{ρ₀} λ⁻¹ + M` for `0 < ρ₁ < ρ₀`. The integrals in `hL` are finite on `A` (`thm11_14`). -/
theorem thm11_14_pos {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) {ρ₀ : ℝ} {T : ℝ → Set ℂ}
    (hT : IsCircularCrosscutSystem f ζ ω ρ₀ T) {L : ℝ}
    (hL : Tendsto (fun z => ‖z - ζ‖ *
        Real.exp (∫⁻ ρ in Ioo ‖f z - ω‖ ρ₀, ENNReal.ofReal π * (crosscutLength T ρ)⁻¹).toReal)
      (𝓝[crosscutPreimageUnion f T ρ₀] ζ) (𝓝 L)) :
    0 < L ↔ ∃ M : ℝ, ∀ ρ₁ ∈ Ioo 0 ρ₀,
      arcFamilyModule (separatingCrosscuts G T ρ₁ ρ₀) ≤
        (∫⁻ ρ in Ioo ρ₁ ρ₀, (crosscutLength T ρ)⁻¹) + ENNReal.ofReal M := by
  sorry

/-- The domains (11.5.9) (= (11.1.3), Fig. 11.1) (§11.5, P2 l. 3593–3597; used in Proposition 11.15, Theorem 11.16 and
Exercises 11.5.3–11.5.4; helper): `G = {ω + ρe^{iϑ} : 0 < ρ < c, ϑ₋(ρ) < ϑ < ϑ₊(ρ)}`.
Modelling: `ϑm`, `ϑp` stand for `ϑ₋`, `ϑ₊`; the statements add `ϑ₋ < ϑ₊` on `(0, c)`. `ϑ₊ - ϑ₋ ≤ 2π` need not be
assumed: it is forced once `f` maps `𝔻` conformally onto `G`, since `ω ∉ G` (`ρ > 0`), and a whole circle about `ω`
in the simply connected `G` would put the disc it bounds, and so `ω`, into `G`. -/
def polarSectorDomain (ω : ℂ) (c : ℝ) (ϑm ϑp : ℝ → ℝ) : Set ℂ :=
  {w | ∃ ρ ∈ Ioo 0 c, ∃ ϑ ∈ Ioo (ϑm ρ) (ϑp ρ), w = ω + ρ * exp (ϑ * I)}

/-- The circular crosscuts of the domains (11.5.9) (§11.5, P2 l. 3593–3597 and Fig. 11.1; helper):
`T(ρ) = {ω + ρe^{iϑ} : ϑ₋(ρ) < ϑ < ϑ₊(ρ)}`. In Proposition 11.15 and Theorem 11.16 the system `T` of §11.4 is formed
by these arcs ("in the present situation we have `λ(ρ) = ρ(ϑ₊(ρ) - ϑ₋(ρ))`", P2 l. 3659). -/
def polarSectorArc (ω : ℂ) (ϑm ϑp : ℝ → ℝ) (ρ : ℝ) : Set ℂ :=
  {w | ∃ ϑ ∈ Ioo (ϑm ρ) (ϑp ρ), w = ω + ρ * exp (ϑ * I)}

/-- **Proposition 11.15** (§11.5; War42, RoWa76, "to complement (3) by an upper estimate"; P2 l. 3591–3611; cited in the
proof of Theorem 11.16, P2 l. 3659). Let (see Fig. 11.1) (11.5.9)
`G = {ω + ρe^{iϑ} : 0 < ρ < c, ϑ₋(ρ) < ϑ < ϑ₊(ρ)}`, where the functions `ϑ_±` are locally absolutely continuous and
satisfy (11.5.10) `∫₀^c (ϑ₊'(ρ)² + ϑ₋'(ρ)²)/(ϑ₊(ρ) - ϑ₋(ρ)) ρ dρ < ∞`. Then, for `ρ₁ < ρ₂ < ρ₀`, (11.5.11)
`mod Γ(ρ₁, ρ₂) ≤ ∫_{ρ₁}^{ρ₂} 1/(ϑ₊ - ϑ₋) dρ/ρ + ½ ∫_{ρ₁}^{ρ₂} (ϑ₊'² + ϑ₋'²)/(ϑ₊ - ϑ₋) ρ dρ`.
Modelling: under the standing assumption of §11.5, with `G` of the form (11.5.9) and the system `T` formed by the arcs
`polarSectorArc` (Fig. 11.1; the proof of Theorem 11.16, P2 l. 3659); this hypothesis holds automatically for every
`ρ₀ < c` (the arcs are the only crosscuts `G ∩ ∂D(ω, ρ)`, and `ζ` is forced by its angular limit `ω`); it supplies
`ρ₀`. "Locally absolutely continuous" is Mathlib's
`AbsolutelyContinuousOnInterval` on every `[a, b] ⊆ (0, c)`; `ϑ₋ < ϑ₊` on `(0, c)` is explicit (the integrands divide
by `ϑ₊ - ϑ₋`). `ϑ_±'` is `deriv`, the derivative almost everywhere (an absolutely continuous function is
differentiable almost everywhere; the value `0` of `deriv` at the other points is invisible to the integrals). The
integrands are non-negative, and the integrals are lower integrals of their `ENNReal.ofReal`; `0 < ρ₁` is implicit. -/
theorem prop11_15 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) {c : ℝ} {ϑm ϑp : ℝ → ℝ}
    (hG : G = polarSectorDomain ω c ϑm ϑp) (hlt : ∀ ρ ∈ Ioo 0 c, ϑm ρ < ϑp ρ)
    (hACm : ∀ a b : ℝ, 0 < a → a ≤ b → b < c → AbsolutelyContinuousOnInterval ϑm a b)
    (hACp : ∀ a b : ℝ, 0 < a → a ≤ b → b < c → AbsolutelyContinuousOnInterval ϑp a b)
    (h10 : ∫⁻ ρ in Ioo 0 c, ENNReal.ofReal ((deriv ϑp ρ ^ 2 + deriv ϑm ρ ^ 2) / (ϑp ρ - ϑm ρ) * ρ) < ⊤)
    {ρ₀ : ℝ} (hT : IsCircularCrosscutSystem f ζ ω ρ₀ (polarSectorArc ω ϑm ϑp)) {ρ₁ ρ₂ : ℝ} (h₁ : 0 < ρ₁)
    (h₁₂ : ρ₁ < ρ₂) (h₂ : ρ₂ < ρ₀) :
    arcFamilyModule (separatingCrosscuts G (polarSectorArc ω ϑm ϑp) ρ₁ ρ₂) ≤
      (∫⁻ ρ in Ioo ρ₁ ρ₂, ENNReal.ofReal (1 / (ϑp ρ - ϑm ρ) / ρ)) +
        ENNReal.ofReal (1 / 2) *
          ∫⁻ ρ in Ioo ρ₁ ρ₂, ENNReal.ofReal ((deriv ϑp ρ ^ 2 + deriv ϑm ρ ^ 2) / (ϑp ρ - ϑm ρ) * ρ) := by
  sorry

/-- **Theorem 11.16** (§11.5; War42; the imaginary part: War42, RoWa76; P2 l. 3643–3651; previewed as (11.1.4); cited at
P2 l. 3663, 3665). Let `G` be defined by (11.5.9) with locally absolutely continuous `ϑ_±` and let (11.5.10) be
satisfied. Then, with `f(z) = ω + ρe^{iϑ}`, (11.5.16)
`log(z - ζ) = -∫_ρ^c π/(ϑ₊(t) - ϑ₋(t)) dt/t + iπ(ϑ - ϑ₋(ρ))/(ϑ₊(ρ) - ϑ₋(ρ)) + b + o(1)`
as `z → ζ`, `z ∈ 𝔻`, where `-∞ < Re b < +∞` and `Im b = arg ζ + π/2`.
[CORRECTION] The upper limit `c` of the integral is replaced by a fixed `c₀ ∈ (0, c)` (crop ✓: the book prints `c`).
Nothing in (11.5.10) prevents `ϑ₊ - ϑ₋ → 0` as `ρ → c`, and then `∫_ρ^c` diverges for every `ρ`: for
`ϑ_±(ρ) = ±(c - ρ)²/2` with `0 < c < 1` the integrand of (11.5.10) is `2ρ`, so (11.5.10) holds, while
`∫_ρ^c π dt/(t(c - t)²) = ∞`. The upper limit only shifts `Re b`: when `∫^c` converges, the two forms are equivalent
(`Re b` changes by the finite `∫_{c₀}^c`), which is the book's case.
Modelling: under the hypotheses of `prop11_15` (the standing assumption of §11.5, `T` formed by the arcs of (11.5.9)).
`ζ = e^{iθ₀}`, and `arg ζ` is `θ₀`. `log(z - ζ)` is the branch `log|z - ζ| + i(θ₀ + π + arg((z - ζ)/(-ζ)))`, continuous
on `𝔻` (there `Re((z - ζ)/(-ζ)) = 1 - Re(z ζ̄) > 0`) with imaginary part in `(θ₀ + π/2, θ₀ + 3π/2)`; the statement is
invariant under `θ₀ ↦ θ₀ + 2π`, which shifts both `log(z - ζ)` and `Im b` by `2π`. `ρ = |f(z) - ω|`, and `ϑ = ϑ(z)` is
the polar angle of `f(z) - ω` in `(ϑ₋(ρ), ϑ₊(ρ))`; it exists since `f(z) ∈ G` and is unique since `ϑ₊ - ϑ₋ ≤ 2π` (see
`polarSectorDomain`), and it is any function `Θ` with this property (`b` does not depend on it). For `z` near `ζ`,
`ρ < c₀`, and the integral is the interval integral of a continuous positive function on `[ρ, c₀] ⊆ (0, c)`.
"`-∞ < Re b < +∞`" is `b ∈ ℂ`. The book proves only the real part and refers to War42 or RoWa76 for the imaginary
part; both are stated. -/
theorem thm11_16 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) {c : ℝ} {ϑm ϑp : ℝ → ℝ}
    (hG : G = polarSectorDomain ω c ϑm ϑp) (hlt : ∀ ρ ∈ Ioo 0 c, ϑm ρ < ϑp ρ)
    (hACm : ∀ a b : ℝ, 0 < a → a ≤ b → b < c → AbsolutelyContinuousOnInterval ϑm a b)
    (hACp : ∀ a b : ℝ, 0 < a → a ≤ b → b < c → AbsolutelyContinuousOnInterval ϑp a b)
    (h10 : ∫⁻ ρ in Ioo 0 c, ENNReal.ofReal ((deriv ϑp ρ ^ 2 + deriv ϑm ρ ^ 2) / (ϑp ρ - ϑm ρ) * ρ) < ⊤)
    {ρ₀ : ℝ} (hT : IsCircularCrosscutSystem f ζ ω ρ₀ (polarSectorArc ω ϑm ϑp)) {θ₀ : ℝ}
    (hθ₀ : ζ = exp (θ₀ * I)) :
    ∀ c₀ ∈ Ioo 0 c, ∃ b : ℂ, b.im = θ₀ + π / 2 ∧ ∀ Θ : ℂ → ℝ,
      (∀ z ∈ unitDisc, Θ z ∈ Ioo (ϑm ‖f z - ω‖) (ϑp ‖f z - ω‖) ∧ f z = ω + ‖f z - ω‖ * exp (Θ z * I)) →
      Tendsto (fun z => ((Real.log ‖z - ζ‖ : ℝ) : ℂ) + ((θ₀ + π + arg ((z - ζ) / (-ζ)) : ℝ) : ℂ) * I -
          ((-(∫ t in ‖f z - ω‖..c₀, π / (ϑp t - ϑm t) / t) : ℝ) +
            ((π * (Θ z - ϑm ‖f z - ω‖) / (ϑp ‖f z - ω‖ - ϑm ‖f z - ω‖) : ℝ) : ℂ) * I + b))
        (𝓝[unitDisc] ζ) (𝓝 0) := by
  sorry

end Pommerenke1992
