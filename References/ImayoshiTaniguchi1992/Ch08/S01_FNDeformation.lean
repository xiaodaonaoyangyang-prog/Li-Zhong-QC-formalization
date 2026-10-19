import References.ImayoshiTaniguchi1992.Ch07.S03_WeilPetersson
import References.Lehto1987.Ch05.S07_ExtremalMappingsOfRiemannSurfaces

/-!
# Imayoshi–Taniguchi, Chapter 8 §8.1: Fenchel–Nielsen deformations

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 8 §8.1 (`full.md` IT2:1396–1607,
folder `An Introduction to Teichmuller Spaces … 0ac64ea2`).

Conventions (Ch. 8, IT2:1406): `Γ` is a Fuchsian model of a closed Riemann surface of genus `g ≥ 2` (`IsFuchsian`,
`IsCocompact`), `C` a simple closed geodesic covered by `γ₀ ∈ Γ`, normalized by a real Möbius map `A` so that
`A γ₀ A⁻¹ (z) = λ z`, `λ > 1` (`IsNormalizedBy`); the statements of §8.1 take `A = 1`. The collar of `C` is the sector
`{|arg z - π/2| < θ₀}` (`sector`), `θ₀ ∈ (0, π/2)` such that its images under the elements of `Γ` outside `⟨γ₀⟩` are disjoint
from it (`IsCollarAngle`). Sums over `⟨γ₀⟩\Γ` run over the right cosets of `(Subgroup.closure {γ₀, −1}).subgroupOf Γ = ⟨γ₀, −1⟩ ∩ Γ` in `Γ` (for `−1 ∉ Γ` it is `zpowers γ₀`). **IT correction/reading:** the book's cosets of `⟨γ₀⟩` in `PSL(2, ℝ)`; with `−1 ∈ Γ` the cosets of `zpowers γ₀` alone would count
every Möbius coset twice, as the summands depend only on the Möbius map of the representative (`Quotient.out` of a coset
is a representative; the summands are independent of it by the `γ₀`-invariance of the coefficient). `w^t` is
`LiZhongQC.normalizedSolution μ_t` (dilatation `μ_t` on `H`, `0` on `H*`). Chart-wise FN data (IT-D5): functions on
coefficients `ℂ → ℂ` with their values on `LiZhongQC.BeltramiGamma Γ`: the geodesic length (`IsLengthFn`), the oriented
displacement `τ` between the feet (`IsTwistFn`; IT's twist is `References.footDisp`, here `τ_j = ℓ_j θ_j/2π`), and their
differentials `dFn` along the real path `t ↦ [w^{tμ}]`. The sign of the twist is IT's (opposite to Wolpert's); statements about the
sign of `τ` are stated up to this convention (`[weaker]`).

* Definition (FN deformation, qc form: `W_C`, `w^t`, `τ_t`, `μ_t`, §8.1, IT2:1406) — `sector`, `IsCollarAngle`, `argBook`,
  `tauT`, `fnBeltrami`
* Definition (deformed elements, length and twist functions; differentials) — `IsDeformedElem`, `IsLengthFn`, `IsTwistFn`, `dFn`
* Unlabelled (`μ_t ∈ B(H, Γ)₁` and it represents the FN deformation, IT2:1443) — `para8_1_a`
* Definition (`ν` (8.1), tangent vector `φ_C`, IT2:1464) — `nu0`, `fnTangentBeltrami`, `wDot`
* Unlabelled ((8.2) and `‖μ_t/t - ν‖_∞ → 0`, IT2:1486) — `eq8_2`
* Lemma 8.1 (IT2:1506) — `logBook`, `FgammaFn`, `lemma8_1`
* Theorem 8.2 (`φ_C = (i/2π) Σ (γ'/γ)²`, IT2:1556) — `thm8_2`
* Definition (Petersson series `Θ_C`, IT2:1580) — `peterssonSeries`
* Unlabelled (`Θ_C ∈ A₂(H, Γ)`, IT2:1590) — `para8_1_b`
* Corollary to Theorem 8.2 (IT2:1594) — `thm8_2_cor`
-/

open Complex Set Metric Filter Topology MeasureTheory Asymptotics
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (upperHalf lowerHalf fMuSym normalizedSolution dz dzbar IsFuchsian IsCocompact BeltramiGamma
  IsFundamentalDomainH IsHyperbolic translationLength)
open References (footDisp fixedPtsH)

/-! ## The qc form of the Fenchel–Nielsen deformation -/

/-- `A` conjugates `γ₀` to the dilation `z ↦ λ z`, `λ > 1` (0 and ∞ are its repelling and attracting fixed points):
`A γ₀ A⁻¹` is diagonal with `(A γ₀ A⁻¹)₀₀² > 1`. -/
def IsNormalizedBy (A γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Prop :=
  (A * γ₀ * A⁻¹) 0 1 = 0 ∧ (A * γ₀ * A⁻¹) 1 0 = 0 ∧ 1 < (A * γ₀ * A⁻¹) 0 0 ^ 2

/-- The collar sector `{z : |arg z - π/2| < θ₀}` (`W̃_C`, Ch. 8 §8.1). -/
def sector (θ₀ : ℝ) : Set ℂ := {z | |Complex.arg z - Real.pi / 2| < θ₀}

/-- `θ₀` is a collar angle for `γ₀` (normalized by `A`): `0 < θ₀ < π/2` and the sector is disjoint from its images under all
elements of `Γ` which are not powers of `γ₀` (up to sign), in `A`-coordinates. -/
def IsCollarAngle (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (γ₀ A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (θ₀ : ℝ) : Prop :=
  0 < θ₀ ∧ θ₀ < Real.pi / 2 ∧ ∀ γ ∈ Γ, (∀ k : ℤ, γ ≠ γ₀ ^ k ∧ γ ≠ -(γ₀ ^ k)) →
    Disjoint (sector θ₀) ((mobH (A * γ * A⁻¹)) '' sector θ₀)

/-- The argument in the book's convention, `[-π, π)`. -/
def argBook (z : ℂ) : ℝ := if Complex.arg z = Real.pi then -Real.pi else Complex.arg z

/-- The logarithm with the argument in `[-π, π)`: `log |z| + i arg z`. -/
def logBook (z : ℂ) : ℂ := (Real.log ‖z‖ : ℂ) + (argBook z : ℂ) * Complex.I

/-- **`τ_t`** (Ch. 8 §8.1, IT2:1443): `τ_t(z) = (iε/(2 - iε)) χ_I(arg z) z/\bar z` on the sector, with `ε = -t/(2θ₀)`. -/
def tauT (θ₀ t : ℝ) (z : ℂ) : ℂ :=
  if |Complex.arg z - Real.pi / 2| < θ₀ then
    (Complex.I * (-t / (2 * θ₀) : ℝ) / (2 - Complex.I * (-t / (2 * θ₀) : ℝ))) * (z / conj z)
  else 0

/-- **`μ_t = Σ_{γ ∈ ⟨γ₀⟩\\Γ} (τ_t ∘ Aγ) \overline{(Aγ)'}/(Aγ)'`** (Ch. 8 §8.1): the Beltrami coefficient of the Fenchel–Nielsen
deformation of `R` along `C` with twist `t`, normalized by `A`; extended to the plane by `0` off `ℍ`. -/
def fnBeltrami (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (γ₀ : Γ) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (θ₀ t : ℝ) (z : ℂ) : ℂ :=
  if 0 < z.im then
    ∑' c : Quotient (QuotientGroup.rightRel ((Subgroup.closure {(γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ), -1}).subgroupOf Γ)),
      tauT θ₀ t (mobH (A * (c.out : Γ)) z) *
        (conj (deriv (mobH (A * (c.out : Γ))) z) / deriv (mobH (A * (c.out : Γ))) z)
  else 0

/-! ## Length and twist functions on coefficients, and their differentials -/

/-- `A` represents `w^ν γ (w^ν)⁻¹`: the Möbius map with `A ∘ w^ν = w^ν ∘ γ` on `ℍ` (`A ∈ Γ^ν`). -/
def IsDeformedElem (ν : ℂ → ℂ) (γ A : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Prop :=
  ∀ z ∈ upperHalf, mobH A (fMuSym ν z) = fMuSym ν (mobH γ z)

/-- **Geodesic length function** `ℓ_C` on coefficients (Ch. 8 §8.2, IT2:1610): `f(μ)` is the translation length of the
element `w^μ γ (w^μ)⁻¹` of `Γ^μ`, i.e. the hyperbolic length of the closed geodesic of `C` on `H/Γ^μ`, for every
`μ ∈ M(Γ)`. -/
def IsLengthFn (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (f : (ℂ → ℂ) → ℝ) : Prop :=
  ∀ m : BeltramiGamma Γ, ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, IsDeformedElem m.1.1 γ A ∧
    f m.1.1 = translationLength A

/-- **Twist function** `τ_C` on coefficients (Ch. 3 §3.2.3, Ch. 8): `f(μ) = References.footDisp` of the deformed elements
`G^μ, A^μ, B^μ`, the oriented displacement along the axis of `G^μ` between the feet of the common perpendiculars from the
axes of `A^μ`, `B^μ` (a real number; `θ = 2π τ/ℓ`). -/
def IsTwistFn (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (G a b : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (f : (ℂ → ℂ) → ℝ) : Prop :=
  ∀ m : BeltramiGamma Γ, ∃ AG Aa Ab : Matrix.SpecialLinearGroup (Fin 2) ℝ, IsDeformedElem m.1.1 G AG ∧
    IsDeformedElem m.1.1 a Aa ∧ IsDeformedElem m.1.1 b Ab ∧ f m.1.1 = footDisp AG Aa Ab

/-- **Differential** of a function `f` on coefficients at the base point in the direction `μ` (Ch. 8 §8.2):
`(df)(μ) = d/dt f(tμ)|_{t=0}`, `t` real (the derivative along the path `t ↦ [w^{tμ}]`). -/
def dFn (f : (ℂ → ℂ) → ℝ) (μ : ℂ → ℂ) : ℝ := deriv (fun t : ℝ => f (fun z => (t : ℂ) * μ z)) 0

/-- **The elements of an FN datum**: `G` hyperbolic and `a, b` hyperbolic without a common fixed point with `G` (so that
`footDisp` has no junk value; preserved by the deformations). -/
def IsFNElements (G a b : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Prop :=
  IsHyperbolic G ∧ IsHyperbolic a ∧ IsHyperbolic b ∧ Disjoint (fixedPtsH G) (fixedPtsH a) ∧ Disjoint (fixedPtsH G) (fixedPtsH b)

/-- **Unlabelled claim** (Ch. 8 §8.1, IT2:1443). `μ_t ∈ B(H, Γ)₁` for small `t` (it is a `Γ`-compatible Beltrami coefficient of
norm `< 1`), and `t ↦ [w^{μ_t}]` represents the Fenchel–Nielsen deformation of `R` along `C` with twist `t`: the length
`ℓ_C` is unchanged and the twist `τ` changes by `t` [weaker: up to the sign convention of IT, `τ(μ_t) = τ(0) ± t`]. -/
theorem para8_1_a {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hco : IsCocompact Γ) {γ₀ : Γ}
    {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : IsNormalizedBy A γ₀) {θ₀ : ℝ} (hθ : IsCollarAngle Γ γ₀ A θ₀)
    {a b : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hab : IsFNElements γ₀ a b) {ℓ τ : (ℂ → ℂ) → ℝ}
    (hℓ : IsLengthFn Γ γ₀ ℓ) (hτ : IsTwistFn Γ γ₀ a b τ) :
    ∃ δ > (0 : ℝ), ∀ t : ℝ, |t| < δ → (∃ m : BeltramiGamma Γ, m.1.1 = fnBeltrami Γ γ₀ A θ₀ t) ∧
      ℓ (fnBeltrami Γ γ₀ A θ₀ t) = ℓ (fnBeltrami Γ γ₀ A θ₀ 0) ∧
      (τ (fnBeltrami Γ γ₀ A θ₀ t) = τ (fnBeltrami Γ γ₀ A θ₀ 0) + t ∨
        τ (fnBeltrami Γ γ₀ A θ₀ t) = τ (fnBeltrami Γ γ₀ A θ₀ 0) - t) := by
  sorry

/-! ## The tangent vector `ν` and the variation `ẇ` -/

/-- **`ν₀`** (8.1): `ν₀(z) = -(i/(4θ₀)) χ_I(arg z) z/\bar z`, `I = (π/2 - θ₀, π/2 + θ₀)`. -/
def nu0 (θ₀ : ℝ) (z : ℂ) : ℂ :=
  if |Complex.arg z - Real.pi / 2| < θ₀ then -(Complex.I / ((4 * θ₀ : ℝ) : ℂ)) * (z / conj z) else 0

/-- **`ν = ν₀ + Σ_{γ ∈ ⟨γ₀⟩\\Γ, γ ∉ ⟨γ₀⟩} (ν₀ ∘ Aγ) \overline{(Aγ)'}/(Aγ)'`** (8.1), the tangent vector of the deformation
`∂/∂τ_C` at the base point (the sum over all cosets, the trivial one being `ν₀`); extended by `0` off `ℍ`. -/
def fnTangentBeltrami (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (γ₀ : Γ)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (θ₀ : ℝ) (z : ℂ) : ℂ :=
  if 0 < z.im then
    ∑' c : Quotient (QuotientGroup.rightRel ((Subgroup.closure {(γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ), -1}).subgroupOf Γ)),
      nu0 θ₀ (mobH (A * (c.out : Γ)) z) *
        (conj (deriv (mobH (A * (c.out : Γ))) z) / deriv (mobH (A * (c.out : Γ))) z)
  else 0

/-- **`ẇ(z) = -(1/π) ∬_H ν(ζ) z(z-1)/(ζ(ζ-1)(ζ-z)) dξ dη`** (8.2), the derivative of `w^{tν}` at `t = 0` (`z ∈ ℂ`). -/
def wDot (ν : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(1 / (Real.pi : ℂ)) * ∫ ζ in upperHalf, ν ζ * (z * (z - 1)) / (ζ * (ζ - 1) * (ζ - z))

/-- **Unlabelled claim** ((8.2), Ch. 8 §8.1, IT2:1486). `‖μ_t/t - ν‖_∞ → 0` as `t → 0`, and `ẇ = ∂w_t/∂t |_{t=0}` is given by
(8.2): `(d/dt) w^{μ_t}(z) |_{t=0} = ẇ(z)` for every `z ∈ ℂ`. -/
theorem eq8_2 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hco : IsCocompact Γ) {γ₀ : Γ}
    (hA : IsNormalizedBy 1 γ₀) {θ₀ : ℝ} (hθ : IsCollarAngle Γ γ₀ 1 θ₀) :
    Tendsto (fun t : ℝ => eLpNorm (fun z => fnBeltrami Γ γ₀ 1 θ₀ t z / (t : ℂ) - fnTangentBeltrami Γ γ₀ 1 θ₀ z) ⊤ volume)
        (𝓝[≠] 0) (𝓝 0) ∧
      ∀ z : ℂ, HasDerivAt (fun t : ℝ => normalizedSolution (fnBeltrami Γ γ₀ 1 θ₀ t) z)
        (wDot (fnTangentBeltrami Γ γ₀ 1 θ₀) z) 0 := by
  sorry

/-- **`F_γ`** of Lemma 8.1: `F_γ(z) = -(γ(z)/γ'(z)) {∫₀^{arg γ(z)} χ_I(s)/(2θ₀) ds + (i/2π) log γ(z)} + (i/2π) P(z)` for the
Möbius map `γ` and a polynomial `P`. -/
def FgammaFn (θ₀ : ℝ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (P : Polynomial ℂ) (z : ℂ) : ℂ :=
  -(mobH γ z / deriv (mobH γ) z) *
      ((∫ s in (0 : ℝ)..argBook (mobH γ z), (if |s - Real.pi / 2| < θ₀ then 1 / (2 * θ₀) else 0) : ℝ) +
        (Complex.I / (2 * (Real.pi : ℂ))) * logBook (mobH γ z)) +
    (Complex.I / (2 * (Real.pi : ℂ))) * P.eval z

/-- **Lemma 8.1** (Ch. 8 §8.1). For `z ∈ ℂ` (with `arg z ∈ [-π, π)`),
`ẇ(z) = -z{∫₀^{arg z} χ_I(s)/(2θ₀) ds + (i/2π) log z} + Σ_{γ ∈ ⟨γ₀⟩\\Γ, γ ∉ ⟨γ₀⟩} F_γ(z)`, where `P_γ` is the unique polynomial of
degree `≤ 2` with `F_γ(0) = F_γ(1) = 0` and `F_γ(z) = o(|z|²)` at `∞`; the series converges locally uniformly on `ℂ`. -/
theorem lemma8_1 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hco : IsCocompact Γ) {γ₀ : Γ}
    (hA : IsNormalizedBy 1 γ₀) {θ₀ : ℝ} (hθ : IsCollarAngle Γ γ₀ 1 θ₀) :
    ∃ P : Quotient (QuotientGroup.rightRel ((Subgroup.closure {(γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ), -1}).subgroupOf Γ)) → Polynomial ℂ,
      (∀ c, c ≠ Quotient.mk _ 1 → (P c).natDegree ≤ 2 ∧ FgammaFn θ₀ (c.out : Γ) (P c) 0 = 0 ∧
        FgammaFn θ₀ (c.out : Γ) (P c) 1 = 0 ∧
        (fun z => FgammaFn θ₀ (c.out : Γ) (P c) z) =o[Bornology.cobounded ℂ] fun z => z ^ 2) ∧
      HasSumLocallyUniformlyOn (fun (c : {c : Quotient (QuotientGroup.rightRel ((Subgroup.closure {(γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ), -1}).subgroupOf Γ)) // c ≠ Quotient.mk _ 1})
          (z : ℂ) => FgammaFn θ₀ (c.1.out : Γ) (P c.1) z)
        (fun z => wDot (fnTangentBeltrami Γ γ₀ 1 θ₀) z +
          z * ((∫ s in (0 : ℝ)..argBook z, (if |s - Real.pi / 2| < θ₀ then 1 / (2 * θ₀) else 0) : ℝ) +
            (Complex.I / (2 * (Real.pi : ℂ))) * logBook z)) univ := by
  sorry

/-- **Theorem 8.2** (Ch. 8 §8.1). The tangent vector `φ_C = d³ẇ/dz³ ∈ A₂(H*, Γ)` at the base point is
`φ_C = (i/2π) Σ_{γ ∈ ⟨γ₀⟩\\Γ} (γ'/γ)²`, the series converging locally uniformly on `H*`. -/
theorem thm8_2 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hco : IsCocompact Γ) {γ₀ : Γ}
    (hA : IsNormalizedBy 1 γ₀) {θ₀ : ℝ} (hθ : IsCollarAngle Γ γ₀ 1 θ₀) :
    HasSumLocallyUniformlyOn (fun (c : Quotient (QuotientGroup.rightRel ((Subgroup.closure {(γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ), -1}).subgroupOf Γ))) (z : ℂ) =>
        (Complex.I / (2 * (Real.pi : ℂ))) * (deriv (mobH (c.out : Γ)) z / mobH (c.out : Γ) z) ^ 2)
      (fun z => iteratedDeriv 3 (wDot (fnTangentBeltrami Γ γ₀ 1 θ₀)) z) lowerHalf := by
  sorry

/-! ## The Petersson series `Θ_C` -/

/-- **`Θ_C`** (Ch. 8 §8.1, IT2:1580): for `γ₀ ∈ Γ` covering `C` with (finite, real) fixed points `a ≠ b`,
`ω_{γ₀}(z) = (a - b)²/((z - a)²(z - b)²)` and `Θ_C = Σ_{γ ∈ ⟨γ₀⟩\\Γ} (ω_{γ₀} ∘ γ)(γ')²`. -/
def peterssonSeries (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (γ₀ : Γ) (a b : ℝ) (z : ℂ) : ℂ :=
  ∑' c : Quotient (QuotientGroup.rightRel ((Subgroup.closure {(γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ), -1}).subgroupOf Γ)),
    ((a - b : ℝ) : ℂ) ^ 2 / ((mobH (c.out : Γ) z - a) ^ 2 * (mobH (c.out : Γ) z - b) ^ 2) *
      deriv (mobH (c.out : Γ)) z ^ 2

/-- **Unlabelled claim** (Ch. 8 §8.1, IT2:1590). The series `Θ_C` converges locally uniformly on `H` and belongs to `A₂(H, Γ)`
[weaker: the independence of the choice of `γ₀` covering `C` is not stated].
**Correction** (IT-fix2, audit AUDIT3_IT finding 5): `γ₀` is hyperbolic (`hh`). Without it `γ₀ = ±1` fixes every real `a ≠ b`, the
cosets are all of `Γ/±1` and the series diverges (`∬_H |ω_{a,b}| = ∞`). -/
theorem para8_1_b {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hco : IsCocompact Γ) {γ₀ : Γ}
    (hh : IsHyperbolic γ₀) {a b : ℝ} (hab : a ≠ b) (ha : mobH γ₀ a = a) (hb : mobH γ₀ b = b) :
    HasSumLocallyUniformlyOn (fun (c : Quotient (QuotientGroup.rightRel ((Subgroup.closure {(γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ), -1}).subgroupOf Γ))) (z : ℂ) =>
        ((a - b : ℝ) : ℂ) ^ 2 / ((mobH (c.out : Γ) z - a) ^ 2 * (mobH (c.out : Γ) z - b) ^ 2) *
          deriv (mobH (c.out : Γ)) z ^ 2) (peterssonSeries Γ γ₀ a b) upperHalf ∧
      peterssonSeries Γ γ₀ a b ∈ A2 Γ := by
  sorry

/-- **Corollary to Theorem 8.2** (Ch. 8 §8.1). `ν ≡ -(i/π) λ_H^{-2} \overline{Θ_C} mod N(Γ)`; equivalently
`H[ν] = -(i/π) λ_H^{-2} \overline{Θ_C}` and `φ[ν] = (i/π) Θ_C` on `H` (`phiOf` is the holomorphic `φ[ν] = β₂(λ_H² ν̄)`; with the
earlier conjugate reading of `phiOf` the second and third assertions were false, IT-fix2). -/
theorem thm8_2_cor {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hco : IsCocompact Γ) {γ₀ : Γ}
    (hA : IsNormalizedBy 1 γ₀) {θ₀ : ℝ} (hθ : IsCollarAngle Γ γ₀ 1 θ₀) {a b : ℝ} (hab : a ≠ b) (ha : mobH γ₀ a = a)
    (hb : mobH γ₀ b = b) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hFc : IsCompact (closure F)) :
    (fun z => fnTangentBeltrami Γ γ₀ 1 θ₀ z + (Complex.I / (Real.pi : ℂ)) * harmBeltrami (peterssonSeries Γ γ₀ a b) z) ∈
        Lehto1987.infinitesimallyTrivial Γ F ∧
      (∀ z ∈ upperHalf, harmProj (fnTangentBeltrami Γ γ₀ 1 θ₀) z =
        -(Complex.I / (Real.pi : ℂ)) * harmBeltrami (peterssonSeries Γ γ₀ a b) z) ∧
      ∀ z ∈ upperHalf, phiOf (fnTangentBeltrami Γ γ₀ 1 θ₀) z = (Complex.I / (Real.pi : ℂ)) * peterssonSeries Γ γ₀ a b z := by
  sorry

end ImayoshiTaniguchi1992
