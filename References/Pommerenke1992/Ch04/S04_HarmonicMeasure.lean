import References.Pommerenke1992.Ch04.S03_AngularDerivative

/-!
# Pommerenke 1992, Ch. 4 §4.4 Harmonic Measure

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §4.4; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 3544–3654.

* Definition (harmonic measure `ω(z, A)` of `A ⊆ 𝕋` at `z ∈ 𝔻`, (4.4.1); cited at l. 4193 and P2 l. 1501; the arc
  length `Λ(A)` of `A ⊆ 𝕋`) — `harmonicMeasure`, `circleMeasure`
* Formula (4.4.4) (cited in §4.4 and at l. 3695) — `eq4_4_4`
* Formula (4.4.5) (cited for (4.4.8)) — `eq4_4_5`
* Proposition 4.15 — `prop4_15`
* Löwner's lemma ((4.4.8); named; cited by name at l. 6244 and P2 l. 2421) — `lowner_lemma`
* Definition (the harmonic measure `ω(z, A, G)` relative to `G`, (4.4.9)) — `harmonicMeasureIn`
* Unlabelled (§4.4, l. 3615: the definition (4.4.9) does not depend on the choice of the map `f`) —
  `harmonicMeasureIn_eq`
* Corollary 4.16 (Carleman's principle of domain extension) — `cor4_16`

Not items (DESIGN §3): "`ω(·, A)` is harmonic with `0 ≤ ω ≤ 1`" (clear); (4.4.2) (quoted from Duren, not cited);
(4.4.3) (a derivation step for (4.4.4)); the interpretation of `2πω(z, A)` as the total angle (l. 3576); "`f⁻¹(A)` is a
Borel set on `𝕋`" (l. 3609, immediate); the remarks after Corollary 4.16 on the maximum principle and on multiply
connected domains.

**Conventions.** As in §4.2–§4.3. Sets `A ⊆ 𝕋` are measured through the parameter `t ∈ [0, 2π)`, `ζ = e^{it}`; the arc
length `Λ(A)` is the Lebesgue measure of `{t ∈ [0, 2π) : e^{it} ∈ A}`. A conformal self-map of `𝔻` (`τ ∈ Möb(𝔻)`) is
`c (z - a)/(1 - ā z)` with `|c| = 1`, `|a| < 1`, which is also defined on `𝕋`. For `ω(z, A, G)`, `G ⊆ ℂ` is a simply
connected domain with locally connected boundary (`IsBoundarySetting`), and `A ⊆ ∂G` (boundary in `Ĉ`) is a Borel set.
"Measurable" is Borel measurable (`MeasurableSet` on `ℂ`); the book's Lebesgue-measurable sets of `𝕋` differ from Borel
sets by null sets, which `ω(z, ·)` and `Λ` do not see, so the statements for them follow by inner and outer
regularity.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto IsJordanDomain)

/-- The arc length `Λ(A)` of a set `A ⊆ 𝕋` (§4.4, (4.4.5)): the Lebesgue measure of `{t ∈ [0, 2π) : e^{it} ∈ A}`. -/
def circleMeasure (A : Set ℂ) : ℝ≥0∞ :=
  volume {t : ℝ | t ∈ Ico 0 (2 * π) ∧ exp (t * I) ∈ A}

/-- **Definition (4.4.1)** (§4.4; cited at l. 4193 and P2 l. 1501). The harmonic measure of the measurable set
`A ⊆ 𝕋` at `z ∈ 𝔻`: `ω(z, A) = (1/2π) ∫_A (1 - |z|²)/|ζ - z|² |dζ|`, the Poisson integral of the characteristic
function of `A`.
Modelling: the integral over the parameters `t ∈ [0, 2π)` with `e^{it} ∈ A`; only measurable `A` are used. -/
def harmonicMeasure (z : ℂ) (A : Set ℂ) : ℝ :=
  1 / (2 * π) * ∫ t in {t : ℝ | t ∈ Ico 0 (2 * π) ∧ exp (t * I) ∈ A}, (1 - ‖z‖ ^ 2) / ‖exp (t * I) - z‖ ^ 2

/-- **Formula (4.4.4)** (§4.4; cited in §4.4 and at l. 3695). `ω(τ(z), τ(A)) = ω(z, A)` for `τ ∈ Möb(𝔻)`.
Modelling: `MeasurableSet` is Borel measurability (see the file header). -/
theorem eq4_4_4 {c a : ℂ} (hc : ‖c‖ = 1) (ha : ‖a‖ < 1) {A : Set ℂ} (hA : MeasurableSet A)
    (hAT : A ⊆ sphere 0 1) {z : ℂ} (hz : z ∈ unitDisc) :
    harmonicMeasure (c * (z - a) / (1 - conj a * z)) ((fun ζ => c * (ζ - a) / (1 - conj a * ζ)) '' A) =
      harmonicMeasure z A := by
  sorry

/-- **Formula (4.4.5)** (§4.4; cited for (4.4.8)). `ω(0, A) = (1/2π) ∫_A |dζ| = Λ(A)/2π`. -/
theorem eq4_4_5 {A : Set ℂ} (hA : MeasurableSet A) (hAT : A ⊆ sphere 0 1) :
    harmonicMeasure 0 A = (circleMeasure A).toReal / (2 * π) := by
  sorry

/-- **Proposition 4.15** (§4.4). Let `φ` be analytic in `𝔻` and let `A, B ⊆ 𝕋` be measurable. If the angular limit
`φ(ζ)` exists for all `ζ ∈ A` and if (4.4.6) `φ(𝔻) ⊆ 𝔻`, `φ(A) ⊆ B ⊆ 𝕋`, then (4.4.7) `ω(φ(z), B) ≥ ω(z, A)` for
`z ∈ 𝔻`.
Modelling: `φ(A) ⊆ B` says that the angular limit at each `ζ ∈ A` lies in `B`; `MeasurableSet` is Borel
measurability (see the file header). -/
theorem prop4_15 {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {A B : Set ℂ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAT : A ⊆ sphere 0 1) (hBT : B ⊆ sphere 0 1) (hφD : MapsTo φ unitDisc unitDisc)
    (hφA : ∀ ζ ∈ A, ∃ w ∈ B, HasAngularLimit (fun z => (φ z : ExtPlane)) ζ w) :
    ∀ z ∈ unitDisc, harmonicMeasure z A ≤ harmonicMeasure (φ z) B := by
  sorry

/-- **Löwner's lemma** (§4.4, (4.4.8); named in §4.1; cited by name at l. 6244 and P2 l. 2421). If `φ(0) = 0` and
(4.4.6) is satisfied, then `Λ(B) ≥ Λ(A)`.
Modelling: as in Proposition 4.15; `MeasurableSet` is Borel measurability (see the file header). -/
theorem lowner_lemma {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) (hφ0 : φ 0 = 0) {A B : Set ℂ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAT : A ⊆ sphere 0 1) (hBT : B ⊆ sphere 0 1)
    (hφD : MapsTo φ unitDisc unitDisc) (hφA : ∀ ζ ∈ A, ∃ w ∈ B, HasAngularLimit (fun z => (φ z : ExtPlane)) ζ w) :
    circleMeasure A ≤ circleMeasure B := by
  sorry

/-- **Definition (4.4.9)** (§4.4). Let `G` be a simply connected domain with locally connected boundary, `f` a
conformal map of `𝔻` onto `G` (continuous in `𝔻̄`, Theorem 2.1) and `A` a Borel set of `∂G`. The harmonic measure of
`A` at `z ∈ G` relative to `G` is `ω(z, A, G) = ω(f⁻¹(z), f⁻¹(A), 𝔻)`.
Modelling: `f⁻¹(A) = {ζ ∈ 𝕋 : F(ζ) ∈ A}` for the extension `F`; the value does not depend on `f`
(`harmonicMeasureIn_eq`), so it is written as the supremum of the set of the values for all `f`, a single point (the
pattern of `Gehring1978.hypDensity`): a single point for `z ∈ G` and Borel `A ⊆ ∂G` (`harmonicMeasureIn_eq`); `0`
when `G` has no such map or `z ∉ G`; non-Borel `A` are outside the domain of discourse. The notion is
for `G ⊆ ℂ`, the standing assumption of Chapter 4 (l. 2964). The harmonic measures `ω`, `ω*` of §6.6 (the inner and
the outer domain `G* ∋ ∞` of a Jordan curve, for arbitrary sets) are modelled literally by (6.6.1), as
`boundaryHarmonicMeasure` (Ch. 6 §6.6). -/
def harmonicMeasureIn (G : Set ℂ) (A : Set ExtPlane) (z : ℂ) : ℝ :=
  sSup {r : ℝ | ∃ (f : ℂ → ℂ) (F : ℂ → ExtPlane), IsBoundarySetting f G F ∧
    ∃ w ∈ unitDisc, f w = z ∧ r = harmonicMeasure w {ζ ∈ sphere (0 : ℂ) 1 | F ζ ∈ A}}

/-- **Unlabelled claim** (§4.4, l. 3615; the definition (4.4.9) rests on it). By (4.4.4), `ω(z, A, G)` does not
depend on the choice of the function `f` mapping `𝔻` onto `G`: `ω(f(w), A, G) = ω(w, f⁻¹(A), 𝔻)` for every such
`f`. -/
theorem harmonicMeasureIn_eq {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F)
    {A : Set ExtPlane} (hA : MeasurableSet[borel ExtPlane] A) (hAG : A ⊆ frontier (toExt G)) {w : ℂ}
    (hw : w ∈ unitDisc) :
    harmonicMeasureIn G A (f w) = harmonicMeasure w {ζ ∈ sphere (0 : ℂ) 1 | F ζ ∈ A} := by
  sorry

/-- **Corollary 4.16** (§4.4; Carleman's principle of domain extension). Let `G₁, G₂` be Jordan domains. If
(4.4.10) `G₁ ⊆ G₂`, `A ⊆ ∂G₁ ∩ ∂G₂`, where `A` is a Borel set, then (4.4.11) `ω(z, A, G₁) ≤ ω(z, A, G₂)` for
`z ∈ G₁`. -/
theorem cor4_16 {G₁ G₂ : Set ℂ} (h₁ : IsJordanDomain G₁) (h₂ : IsJordanDomain G₂) (hG : G₁ ⊆ G₂)
    {A : Set ExtPlane} (hA : MeasurableSet[borel ExtPlane] A)
    (hAG : A ⊆ frontier (toExt G₁) ∩ frontier (toExt G₂)) :
    ∀ z ∈ G₁, harmonicMeasureIn G₁ A z ≤ harmonicMeasureIn G₂ A z := by
  sorry

end Pommerenke1992
