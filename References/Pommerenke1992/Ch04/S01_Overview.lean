import References.Pommerenke1992.Ch04.S03_AngularDerivative
import LiZhongQC.Ch05.S20_SchwarzDomains

/-!
# Pommerenke 1992, Ch. 4 §4.1 An Overview

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 4 *Distortion*, §4.1; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 2962–3013.

* Definition (normal function, (4.1.1); cited at l. 3056) — `IsNormalFunction`
* Lehto–Virtanen Theorem (named, §4.1) — `lehto_virtanen_theorem`
* Julia–Wolff Lemma (named, §4.1 form) — `julia_wolff_lemma`
* Löwner's Lemma (named, §4.1; a preview of (4.4.8), stated in §4.4, with B a Borel hull of φ(A), cf. l. 3599) —
  exists: `Pommerenke1992.lowner_lemma`
* Gehring–Hayman Theorem (named, §4.1, l. 3006; stated in §4.5 in this form, next to Theorem 4.20) — exists:
  `Pommerenke1992.gehring_hayman_curve`

**Import order (the exception of Ch. 2 §2.1, approved by the leader 2026-09-28).** The overview states the named
results for normal functions and the Julia–Wolff lemma with the notions of §4.2–§4.3 (asymptotic values, angular
derivatives), so this file imports the file of §4.3; no other file imports it.

Not items (DESIGN §3), all previews of later labelled items: the Bloch seminorm (the definition (4.2.1)); (4.1.2), the
angular derivative (the definition (4.3.1)); (4.1.3) (Corollary 4.18); the description of the harmonic measure
(l. 2996, the definition (4.4.1)); the maximum principle for normal functions (LeVi57, l. 2972, quoted).

**Conventions.** A meromorphic function `g` in `𝔻` takes its values in `Ĉ` through the project's
`LiZhongQC.meroToExt` (the value `∞` at the poles); the spherical derivative is `sphericalDeriv` (§1.2).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc meroToExt)

/-- **Definition (4.1.1)** (§4.1; cited at l. 3056). A normal function: a meromorphic function `g` in `𝔻` with
`sup_{|z| < 1} (1 - |z|²) g#(z) < ∞`. -/
def IsNormalFunction (g : ℂ → ℂ) : Prop :=
  MeromorphicOn g unitDisc ∧ ∃ M : ℝ, ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) * sphericalDeriv g z ≤ M

/-- **Lehto–Virtanen Theorem** (§4.1, named). For normal functions, every asymptotic value is an angular limit: if
`g(z) → a` as `z → ζ ∈ 𝕋` along some curve, then `g(z) → a` as `z → ζ` in every Stolz angle. In particular, radial
and angular limits are the same.
Modelling: the curves are the curves in `𝔻` ending at `ζ` (`IsCurveEndingAt`); the values of `g` are in `Ĉ`
(`meroToExt`). -/
theorem lehto_virtanen_theorem {g : ℂ → ℂ} (hg : IsNormalFunction g) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1)
    (a : ExtPlane) :
    ((∃ Γ : Set ℂ, IsCurveEndingAt Γ ζ ∧ Tendsto (meroToExt g) (𝓝[Γ] ζ) (𝓝 a)) →
      HasAngularLimit (meroToExt g) ζ a) ∧
    (HasRadialLimit (meroToExt g) ζ a ↔ HasAngularLimit (meroToExt g) ζ a) := by
  sorry

/-- **Julia–Wolff Lemma** (§4.1, named; the general form is Proposition 4.13). Let `φ` be analytic in `𝔻`,
`φ(0) = 0`, `φ(𝔻) ⊆ 𝔻`. If `ζ ∈ 𝕋` and `φ(ζ) ∈ 𝕋`, then `φ'(ζ)` exists and satisfies `1 ≤ |φ'(ζ)| ≤ ∞`.
Modelling: `φ(ζ)` is the angular limit; `φ'(ζ)` is the angular derivative (4.3.1), finite with `1 ≤ |φ'(ζ)|` or
`∞`. -/
theorem julia_wolff_lemma {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) (hφ0 : φ 0 = 0)
    (hφD : MapsTo φ unitDisc unitDisc) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) {φζ : ℂ}
    (hlim : HasAngularLimit (fun z => (φ z : ExtPlane)) ζ φζ) (hφζ : φζ ∈ sphere (0 : ℂ) 1) :
    (∃ a : ℂ, HasAngularDerivative φ ζ a ∧ 1 ≤ ‖a‖) ∨ HasAngularDerivative φ ζ extInf := by
  sorry

end Pommerenke1992
