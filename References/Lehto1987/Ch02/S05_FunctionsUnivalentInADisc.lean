import References.Lehto1987.Ch02.S04_UnivalenceAndQuasiconformalExtensibilityOfMeromorphicFunctions

/-!
# Lehto, Chapter II §5: Functions univalent in a disc

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. II §5 (`full.md`
P1:3248–3557).

Conventions (see §1, §3, §4 and the root file). "`f` meromorphic in a disc with `‖S_f‖ < 2`" (or `≤ 2`) presupposes
that `f` is locally injective (root Corrections, reading (4)): `IsLocUnivMeroExt f A`, resp. `LiZhongQC.IsLocUnivMero`
in the unit disc. Discs are `IsDiscExt` (§1.6); `D` is the unit disc, `H` the upper half-plane. Extensions to the plane
are `IsQCExtensionOf` (§3), homeomorphic extensions are LV's `IsHomeoOn F univ univ`. The parallel strip is
`{|Im z| < π/2}` (every parallel strip is its image under a similarity, a Möbius transformation).

* Theorem 5.1 (§5.1, Ahlfors–Weill) — `thm2_5_1`, `thm2_5_1_sharp`, `thm2_5_1_disc`, `thm2_5_1_half`
* Unlabelled (§5.1, P1:3286–3288): a simply connected domain with `δ(A) < 2` is a quasidisc — `para2_5_1_a`
* Unlabelled (§5.1, P1:3298, Bers, quoted): extensions with complex dilatation `φ̄/η²` for quasidiscs —
  `para2_5_1_b`
* Unlabelled (§5.1, P1:3302–3304): Bers's mapping `μ ↦ S_{f|A}` is invertible near the origin — omitted: quoted, not
  cited
* §5.2 (real-analytic solutions of the boundary value problem) — omitted: the proof of Theorem I.5.3
  (`thm1_5_3`); formula (5.3) is a step of it
* Theorem 5.2 (§5.3, Nehari) — `thm2_5_2`, `thm2_5_2_sharp`
* Unlabelled (§5.4, P1:3366–3368): Theorem 5.2 in the strip `{|Im z| < π/2}` — omitted: a reformulation, not cited
* Formula (5.4) (§5.4) — `eq2_5_4`
* Formula (5.5)–(5.6) (§5.4) — `eq2_5_5`
* Lemma 5.1 (§5.5) — `lemma2_5_1`
* Unlabelled (§5.5, P1:3430): a function satisfying the conditions of Lemma 5.1 extends continuously to the closed
  disc — `para2_5_5`
* Theorem 5.3 (§5.6, Gehring–Pommerenke) — `thm2_5_3`
* Formula (5.8), (5.9) (§5.6) — omitted: steps of the proof of Theorem 5.3
* Theorem 5.4 (§5.7, Gehring–Pommerenke) — `thm2_5_4`
* Unlabelled (§5.7, P1:3533–3549): the classification by `(1 − |z|²)² |S_f| ≤ 2`, `< 2`, `sup < 2` — omitted: a
  summary of Theorems 5.2, 5.4 and 5.1
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace Lehto1987

open LiZhongQC (ExtPlane extInf toExt unitDisc upperHalf schwarzian meroToExt IsLocUnivMero IsMobius)
open References (finitePart IsJordanDomainExt IsQuasidiskExt)
open LehtoVirtanen1973 (complexDilatationLV IsHomeoOn)
open Gehring1978 (hypDensity hypNorm IsHypSimplyConnectedExt IsConformalExt imageExt)

/-! ## §5.1 Quasiconformal extension to the complement of a disc -/

/-- **Theorem 5.1** (Ch. II §5.1, Ahlfors–Weill). Let `f` be meromorphic in a disc `D`. If `‖S_f‖_D < 2`, then `f`
is univalent and can be extended to a quasiconformal mapping of the plane. -/
theorem thm2_5_1 {A : Set ExtPlane} (hA : IsDiscExt A) {f : ℂ → ℂ} (hf : IsLocUnivMeroExt f A)
    (hS : hypNorm (schwarzian f) A < 2) :
    IsConformalExt f A ∧ ∃ F : ExtPlane → ExtPlane, IsQCExtensionOf F f A := by
  sorry

/-- **Theorem 5.1** (Ch. II §5.1), sharpness. The constant `2` is best possible: `log z` is univalent in the upper
half-plane `H` with `‖S_{log}‖_H = 2`, and it has no homeomorphic extension to the plane (the image of `H` is a
parallel strip, not a Jordan domain).
Modelling: the principal branch of the logarithm. -/
theorem thm2_5_1_sharp :
    IsConformalExt Complex.log (toExt upperHalf) ∧ hypNorm (schwarzian Complex.log) (toExt upperHalf) = 2 ∧
      ¬ ∃ F : ExtPlane → ExtPlane, IsHomeoOn F univ univ ∧
        ∀ z ∈ upperHalf, F z = ((Complex.log z : ℂ) : ExtPlane) := by
  sorry

/-- **Theorem 5.1** (Ch. II §5.1), the unit disc. If `D` is the unit disc, there is an extension with complex
dilatation `μ(1/z̄) = −½ (z/z̄)² (1 − |z|²)² S_f(z)` (5.1) for `z` in `D`.
Modelling: the identity holds for almost every `z ∈ D` (the map `z ↦ 1/z̄` carries null sets to null sets). -/
theorem thm2_5_1_disc {f : ℂ → ℂ} (hf : IsLocUnivMeroExt f (toExt unitDisc))
    (hS : hypNorm (schwarzian f) (toExt unitDisc) < 2) :
    ∃ F : ExtPlane → ExtPlane, IsQCExtensionOf F f (toExt unitDisc) ∧
      ∀ᵐ z : ℂ ∂(volume.restrict unitDisc), complexDilatationLV F ((conj z)⁻¹ : ℂ) =
        -(1 / 2) * (z / conj z) ^ 2 * ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) ^ 2 * schwarzian f z := by
  sorry

/-- **Theorem 5.1** (Ch. II §5.1), the half-plane. If `D` is the upper half-plane, an extension exists with
`μ(z̄) = −2 y² S_f(z)` (5.2) for `z = x + iy` in `D`.
Modelling: almost every `z ∈ H`, as in `thm2_5_1_disc`. -/
theorem thm2_5_1_half {f : ℂ → ℂ} (hf : IsLocUnivMeroExt f (toExt upperHalf))
    (hS : hypNorm (schwarzian f) (toExt upperHalf) < 2) :
    ∃ F : ExtPlane → ExtPlane, IsQCExtensionOf F f (toExt upperHalf) ∧
      ∀ᵐ z : ℂ ∂(volume.restrict upperHalf), complexDilatationLV F (conj z : ℂ) =
        -2 * ((z.im ^ 2 : ℝ) : ℂ) * schwarzian f z := by
  sorry

/-- **Unlabelled** (Ch. II §5.1, P1:3286–3288; announced in §2.1). Let `A` be a simply connected domain with more
than one boundary point. If the distance `δ(A)` from a disc is `< 2`, then `A` is a quasidisc. -/
theorem para2_5_1_a {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) (hδ : discDistance A < 2) :
    IsQuasidiskExt A := by
  sorry

/-- **Unlabelled** (Ch. II §5.1, P1:3298, Bers, quoted). A function `f` which is meromorphic in a quasidisc `A` and has
a sufficiently small `‖S_f‖` is univalent and has a quasiconformal extension with a complex dilatation `φ̄/η²` in the
complement `A*` of the closure of `A`, where `φ` is a holomorphic function and `η` the Poincaré density of `A*`.
Modelling: "sufficiently small" is `‖S_f‖_A < ε` for some `ε > 0` depending on `A`; `φ` is holomorphic at the finite
points of `A*`, and the identity holds a.e. there. -/
theorem para2_5_1_b {A : Set ExtPlane} (hA : IsQuasidiskExt A) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f : ℂ → ℂ, IsLocUnivMeroExt f A → hypNorm (schwarzian f) A < ENNReal.ofReal ε →
      IsConformalExt f A ∧ ∃ F : ExtPlane → ExtPlane, IsQCExtensionOf F f A ∧ ∃ φ : ℂ → ℂ,
        DifferentiableOn ℂ φ (finitePart (closure A)ᶜ) ∧
        ∀ᵐ z : ℂ ∂(volume.restrict (finitePart (closure A)ᶜ)),
          complexDilatationLV F z = conj (φ z) / ((hypDensity (closure A)ᶜ z : ℝ) : ℂ) ^ 2 := by
  sorry

/-! ## §5.3 Criterion for univalence -/

/-- **Theorem 5.2** (Ch. II §5.3, Nehari). Let `f` be meromorphic in a disc. If `‖S_f‖ ≤ 2`, then `f` is univalent. -/
theorem thm2_5_2 {A : Set ExtPlane} (hA : IsDiscExt A) {f : ℂ → ℂ} (hf : IsLocUnivMeroExt f A)
    (hS : hypNorm (schwarzian f) A ≤ 2) : IsConformalExt f A := by
  sorry

/-- **Theorem 5.2** (Ch. II §5.3, Hille), sharpness. The bound `2` is best possible: for `ε > 0`, the function
`f(z) = z^{iε}` in the upper half-plane has `‖S_f‖ = 2(1 + ε²)` and is not univalent (it takes the same value at `i`
and `i e^{2π/ε}`).
Modelling: `z^{iε} = exp(iε log z)` (principal branch). [OCR] The exponent is printed `ε`; `S_f(z) = (1 + ε²)(2z²)⁻¹`
and the equal values at `i`, `i e^{2π/ε}` hold for the exponent `iε`. -/
theorem thm2_5_2_sharp {ε : ℝ} (hε : 0 < ε) :
    IsLocUnivMeroExt (fun z => z ^ ((ε : ℂ) * I)) (toExt upperHalf) ∧
      hypNorm (schwarzian fun z => z ^ ((ε : ℂ) * I)) (toExt upperHalf) = ENNReal.ofReal (2 * (1 + ε ^ 2)) ∧
      ¬ InjOn (fun z => z ^ ((ε : ℂ) * I)) upperHalf := by
  sorry

/-! ## §5.4 Parallel strips -/

/-- **Formula (5.4)** (Ch. II §5.4). Let `f` be meromorphic in the unit disc `D`, `h(z) = tanh(z/2)` the conformal
mapping of the strip `A = {|Im z| < π/2}` onto `D`, and `g = f ∘ h`. If `x` is a point of the real axis and
`w = h(x)`, then `4 |S_g(x) + ½| = (1 − |w|²)² |S_f(w)|`.
Modelling: `f` is locally injective meromorphic in `D` (so that `S_f` is defined). -/
theorem eq2_5_4 {f : ℂ → ℂ} (hf : IsLocUnivMero f unitDisc) (x : ℝ) :
    4 * ‖schwarzian (fun z => f (Complex.tanh (z / 2))) x + 1 / 2‖ =
      (1 - ‖Complex.tanh ((x : ℂ) / 2)‖ ^ 2) ^ 2 * ‖schwarzian f (Complex.tanh ((x : ℂ) / 2))‖ := by
  sorry

/-- **Formula (5.5)–(5.6)** (Ch. II §5.4). If `g` is holomorphic in the strip `A = {|Im z| < π/2}`, then on the real
axis the function `v(x) = |g′(x)|^{−1/2}` satisfies `v″ = φ v` (5.5) with
`φ = −½ Re S_g + (½ Im (g″/g′))²` (5.6).
Modelling: `g` is locally injective (`g′ ≠ 0`) in the strip, so that `v` and `S_g` are defined; `v″` is the second
derivative of the real function `v`. -/
theorem eq2_5_5 {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g {z : ℂ | |z.im| < Real.pi / 2})
    (hg' : ∀ z : ℂ, |z.im| < Real.pi / 2 → deriv g z ≠ 0) (x : ℝ) :
    deriv (deriv fun t : ℝ => ‖deriv g t‖ ^ (-(1 / 2 : ℝ))) x =
      (-(1 / 2) * (schwarzian g x).re + ((1 / 2) * (deriv (deriv g) x / deriv g x).im) ^ 2) *
        ‖deriv g x‖ ^ (-(1 / 2 : ℝ)) := by
  sorry

/-! ## §5.5 Continuous extension -/

/-- **Lemma 5.1** (Ch. II §5.5). Let `f` be a function meromorphic in the unit disc `D` satisfying `f″(0) = 0`,
`‖S_f‖_D ≤ 2`, and `(1 − |w|²)² |S_f(w)| ≤ 1` in a neighbourhood `|w| ≤ a < 1` of the origin. Then `f` is holomorphic
in `D` and `|f′(w)| ≤ M |f′(0)| / (1 − |w|²) · (log((1 + |w|)/(1 − |w|)))^{−2}` (5.7), where `M` is a constant
depending only on `a`.
Modelling: `∀ a ∈ (0, 1), ∃ M`; `f` is locally injective meromorphic in `D` and holomorphic at `0`; (5.7) is
multiplied by the square of the logarithm (at `w = 0` the book's right-hand side is infinite). -/
theorem lemma2_5_1 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ M : ℝ, ∀ f : ℂ → ℂ, IsLocUnivMero f unitDisc → AnalyticAt ℂ f 0 → deriv (deriv f) 0 = 0 →
      hypNorm (schwarzian f) (toExt unitDisc) ≤ 2 →
      (∀ w : ℂ, ‖w‖ ≤ a → (1 - ‖w‖ ^ 2) ^ 2 * ‖schwarzian f w‖ ≤ 1) →
      DifferentiableOn ℂ f unitDisc ∧ ∀ w ∈ unitDisc,
        ‖deriv f w‖ * Real.log ((1 + ‖w‖) / (1 - ‖w‖)) ^ 2 ≤ M * ‖deriv f 0‖ / (1 - ‖w‖ ^ 2) := by
  sorry

/-- **Unlabelled** (Ch. II §5.5, P1:3430). A function `f` satisfying the conditions of Lemma 5.1 has a continuous
extension to the boundary of `D`.
Modelling: the extension is a function continuous on the closed unit disc and equal to `f` in `D` (`f` is holomorphic
there by Lemma 5.1). -/
theorem para2_5_5 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {f : ℂ → ℂ} (hf : IsLocUnivMero f unitDisc)
    (h0 : AnalyticAt ℂ f 0) (h2 : deriv (deriv f) 0 = 0) (hS : hypNorm (schwarzian f) (toExt unitDisc) ≤ 2)
    (hSa : ∀ w : ℂ, ‖w‖ ≤ a → (1 - ‖w‖ ^ 2) ^ 2 * ‖schwarzian f w‖ ≤ 1) :
    ∃ F : ℂ → ℂ, ContinuousOn F (Metric.closedBall 0 1) ∧ EqOn F f unitDisc := by
  sorry

/-! ## §5.6 Image of discs -/

/-- **Theorem 5.3** (Ch. II §5.6, Gehring–Pommerenke). Let `f` be meromorphic in a disc `D` and `‖S_f‖ ≤ 2`. Then
`f(D)` is either a Jordan domain or the image of a parallel strip under a Möbius transformation. -/
theorem thm2_5_3 {A : Set ExtPlane} (hA : IsDiscExt A) {f : ℂ → ℂ} (hf : IsLocUnivMeroExt f A)
    (hS : hypNorm (schwarzian f) A ≤ 2) :
    IsJordanDomainExt (imageExt f A) ∨
      ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ imageExt f A = M '' toExt {z : ℂ | |z.im| < Real.pi / 2} := by
  sorry

/-! ## §5.7 Homeomorphic extension -/

/-- **Theorem 5.4** (Ch. II §5.7, Gehring–Pommerenke). Let `f` be meromorphic and satisfy
`|S_f(z)| < 2/(1 − |z|²)²` in the unit disc. Then `f` is univalent and has a homeomorphic extension to the plane.
Modelling: `f` is locally injective meromorphic in `D`; the extension is a homeomorphism of `ℂ̄` equal to `f` (read
in `ℂ̄`) in `D`. -/
theorem thm2_5_4 {f : ℂ → ℂ} (hf : IsLocUnivMero f unitDisc)
    (hS : ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzian f z‖ < 2) :
    IsConformalExt f (toExt unitDisc) ∧
      ∃ F : ExtPlane → ExtPlane, IsHomeoOn F univ univ ∧ ∀ z ∈ unitDisc, F z = meroToExt f z := by
  sorry

end Lehto1987
