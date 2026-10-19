import References.GarnettMarshall2005.Ch06.S04_ConePointsMcMillan
import References.GarnettMarshall2005.App.D_HausdorffMeasure

/-!
# Garnett–Marshall, Chapter VI §5: Compression and expansion

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. VI §5 (pp. 212–216;
`full.md` of the second part, P2:1110–1293).

Conventions of the section, as modelled here (Chapter VI conventions, leader ruling C6). `Ω ⊆ ℂ` is a plane domain,
"simply connected" is `Gehring1978.IsHypSimplyConnectedExt (toExt Ω)`, `φ : 𝔻 → Ω` a conformal map is
`LiZhongQC.IsConformalOnto φ unitDisc Ω`, `φ⁻¹(V)` for `V ⊆ ∂Ω` is `bdryPreimage φ V` and `A` the set of accessible
points (§3). "Harmonic measure for a simply connected domain" is Wiener's harmonic measure `harmonicMeasureWiener`
(Ch. III §5), pulled back to `ℂ` by `.comap (↑)` where it is compared with a measure on `ℂ` (the point `∞` carries no
harmonic measure); the statement (5.1), set by the book for a rectifiable Jordan curve, uses the Jordan-domain harmonic
measure `harmonicMeasureJordan` (leader rulings D1, B5, C6). `Λ₁` is `μH[1]` (leader ruling C2); `Λ_α` (`α ≠ 1`) and
`Λ_h` are App. D's disc-radius Hausdorff measures `hausdorffMeasureGM (fun r => r ^ α)`, `hausdorffMeasureGM h`, and a
"measure function" is `IsMeasureFunction` (App. D; leader ruling C3: App. D is compiled before this file). `ω ≪ Λ` and
`ω ⊥ Λ` are Mathlib's `Measure.AbsolutelyContinuous` and `Measure.MutuallySingular`. `|E|` and "almost every
`ζ ∈ E`" refer to `arcMeasure`.

* Unlabelled (§5, P2:1112, 1122–1134): "`φ` compresses" and "`φ` expands"; the examples of Lavrentiev (`ω` not
  absolutely continuous to `Λ₁`), McMillan–Piranian (`ω ⊥ Λ₁`) and Kaufman–Wu — omitted: informal notions and quoted
  literature without labels
* Definition (measure function; the Hausdorff measures `Λ_α`, `Λ_h`, used in §5 and defined in App. D, P2:1110–1152)
  — exists: `GarnettMarshall2005.IsMeasureFunction` `GarnettMarshall2005.hausdorffMeasureGM` (App. D, compiled before
  this file, leader ruling C3; Λ_α is the measure of the function r to the power α)
* Formula (5.1) (Lavrentiev's estimate, §5, P2:1114–1120; cited in Chapter VII, P2:2717) — `eq6_5_1`
* Unlabelled (§5, P2:1136): Beurling's `ω ≪ Λ_{1/2}` (Corollary III.9.3) and Carleson's `ω ≪ Λ_β` — omitted: a
  remark on quoted results; the OCR prints the index of Beurling's measure as 1/λ, read 1/2 [OCR]
* Theorem 5.1 (Makarov, §5) — `thm6_5_1`
* Unlabelled (§5, P2:1144): Øksendal's theorem (Exercise III.12) and conjecture — omitted: quoted results and a
  conjecture
* Theorem 5.2 (Makarov, §5) — `thm6_5_2`
* Unlabelled (§5, P2:1154–1156): "in particular `ω ⊥ Λ_α` if `α > 1`", "harmonic measure has dimension 1", the
  Jones–Wolff theorem, "Theorem 5.1 will be proved in Chapter VIII" — omitted: immediate from Theorem 5.2, remarks and
  forward references
* Definition (nontangentially dense a.e. on `E`, §5, P2:1158–1162) — `IsNTDenseAE`
* Lemma 5.3 (§5; (5.2)) — `lemma6_5_3`
* Unlabelled (§5, P2:1209–1292): the proof of Theorem 5.2, the arcs `I(z)`, (5.3)–(5.7) and the covering lemma of
  Vitali (Exercise I.9) — omitted: steps of a proof; `I(z)` is reused only inside proofs (P2:1351, Chapter VIII,
  P2:3851)

Near misses in Pommerenke1992 Ch. 6 (not pointers): Theorem 6.25 (`thm6_25`, Makarov's compression theorem in the
form `𝕋 = Sect(f) ∪ A₀ ∪ A₁`, `Λ(f(A₀)) = 0`, `Λ(A₁) = 0`) and Corollary 6.26 (`cor6_26`); they are the
circle-side forms, not Theorems 5.1, 5.2 (which are about harmonic measure against `Λ_α` and `Λ_h`, Pommerenke's
Chapter 10, not installed).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt unitDisc stolzAngle IsConformalOnto)
open References (IsJordanDomainExt)
open Gehring1978 (IsHypSimplyConnectedExt)

/-- **Formula (5.1)** (Lavrentiev's estimate, Ch. VI §5, P2:1114–1120; proved in Exercise VI.2; cited as
"Lavrentiev's estimate (VI.5.1)" in Chapter VII, P2:2717, and as "Lavrentiev's theorem, Exercise VI.2" in Chapter
X, P3:1542). There is a constant `C` such that, when `∂Ω` is a rectifiable Jordan curve, `E ⊂ ∂Ω` and
`dist(z₀, ∂Ω) ≥ 1`, `ω(E) ≤ C log Λ₁(∂Ω)/(1 + |log Λ₁(E)|)`.
Modelling: the setting of the surrounding sentence ("If `∂Ω` is a rectifiable Jordan curve", P2:1114) and of Exercise
VI.2: `Ω` a bounded plane Jordan domain (`References.IsJordanDomainExt (toExt Ω)`, bounded because a rectifiable
Jordan curve is planar, leader ruling C12(c)), rectifiable as `jordanCurveLength (toExt (frontier Ω)) < ⊤` (§1);
`ω(E) = ω(z₀, E, Ω)` is `harmonicMeasureJordan` (module docstring), read as a real number since a quotient follows;
`C` is absolute (`∃ C, ∀ Ω z₀ E`), crop checked; `E` is any subset of `∂Ω` (outer measures; both measures are Borel
regular, so the Borel case gives the general one). The case `Λ₁(E) = 0` is the book's `1/(1 + ∞) = 0`, stated
separately as `ω(E) = 0`, so that no `log 0` junk value is read; for `Λ₁(E) > 0` the value `Λ₁(E) ≤ Λ₁(∂Ω) < ∞` is
finite. `Λ₁(∂Ω) ≥ 2π` (the curve surrounds the disc `B(z₀, 1)`), so `log Λ₁(∂Ω) > 0`. The constant does not depend
on the normalization of `Λ₁` (leader ruling C2). -/
theorem eq6_5_1 : ∃ C : ℝ, ∀ (Ω : Set ℂ) (z₀ : ℂ), IsJordanDomainExt (toExt Ω) → Bornology.IsBounded Ω →
    jordanCurveLength (toExt (frontier Ω)) < ⊤ → z₀ ∈ Ω → 1 ≤ infDist z₀ (frontier Ω) → ∀ E ⊆ frontier Ω,
      (μH[1] E = 0 → harmonicMeasureJordan (toExt Ω) (z₀ : ExtPlane) (toExt E) = 0) ∧
      (0 < μH[1] E → (harmonicMeasureJordan (toExt Ω) (z₀ : ExtPlane) (toExt E)).toReal *
          (1 + |Real.log (μH[1] E).toReal|) ≤ C * Real.log (μH[1] (frontier Ω)).toReal) := by
  sorry

/-- **Theorem 5.1** (Makarov, Ch. VI §5; cited at P2:1154, 1156, in Chapter VIII, P2:3723, "Theorem 2.2 contains
Theorem VI.5.1", and P2:5209, 5371). Let `ω` be harmonic measure for a simply connected domain `Ω` and let
`0 < α < 1`. Then `ω ≪ Λ_α`.
Modelling: `ω = ω(z, ·, Ω)` for any `z ∈ Ω` (Wiener's harmonic measure, pulled back to `ℂ`; module docstring);
`Λ_α` is App. D's `hausdorffMeasureGM (fun r => r ^ α)` (leader ruling C3; `μH[α]` has the same null sets). -/
theorem thm6_5_1 {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) {z : ℂ} (hz : z ∈ Ω) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    (harmonicMeasureWiener (toExt Ω) (z : ExtPlane)).comap ((↑) : ℂ → ExtPlane) ≪
      hausdorffMeasureGM (fun r => r ^ α) := by
  sorry

/-- **Theorem 5.2** (Makarov, Ch. VI §5; cited at P2:1296, 1334, "We follow the proof of Theorem 5.2", in Chapter
VIII, P2:3681, "by Theorem VI.5.2", P2:3839, and in Chapter IX, P2:7067). Let `ω` be harmonic measure for a simply
connected domain `Ω` and let `h(t)` be a measure function such that `lim_{t→0} h(t)/t = 0`. Then `ω` is singular to
`Λ_h`, `ω ⊥ Λ_h`.
Modelling: `ω` as in `thm6_5_1`; the measure function is `IsMeasureFunction h` and `Λ_h` is `hausdorffMeasureGM h`
(App. D); `t → 0` is `t → 0⁺` (`h` is read on `[0, ∞)`). -/
theorem thm6_5_2 {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) {z : ℂ} (hz : z ∈ Ω) {h : ℝ → ℝ}
    (hh : IsMeasureFunction h) (hh0 : Tendsto (fun t => h t / t) (𝓝[>] 0) (𝓝 0)) :
    (harmonicMeasureWiener (toExt Ω) (z : ExtPlane)).comap ((↑) : ℂ → ExtPlane) ⟂ₘ hausdorffMeasureGM h := by
  sorry

/-- **Definition** (nontangentially dense a.e., Ch. VI §5, P2:1158–1162; used in Lemma 5.3, in the proofs of Theorems
5.2 and 6.1, in Chapter VIII, P2:3851, and in Chapter IX, P2:7051). Let `E ⊂ ∂𝔻` and let `S = {z_k}` be a sequence
in `𝔻`. We say `S` is nontangentially dense a.e. on `E` if there is `α > 1` such that for almost every `ζ ∈ E`,
`ζ ∈ closure (S ∩ Γ_α(ζ))`.
Modelling: `S` is the set of the terms of the sequence (only the set enters); `Γ_α(ζ)` is `LiZhongQC.stolzAngle ζ α`;
"almost every `ζ ∈ E`" is for `arcMeasure`. -/
def IsNTDenseAE (S E : Set ℂ) : Prop :=
  ∃ α : ℝ, 1 < α ∧ ∀ᵐ ζ ∂arcMeasure, ζ ∈ E → ζ ∈ closure (S ∩ stolzAngle ζ α)

/-- **Lemma 5.3** (Ch. VI §5; cited in the proofs of Theorems 5.2 and 6.1, P2:1292, 1380, and in Chapter VIII,
P2:3893). Assume `{z_k}` is nontangentially dense a.e. on `E ⊂ ∂𝔻` and let `φ` be the conformal map from `𝔻` onto a
simply connected domain `Ω`. Set `w_k = φ(z_k)`, `r_k = dist(w_k, ∂Ω)`, `B_k = B(w_k, 2r_k)`, and
`V = ∂Ω ∩ (⋃ B_k) ∩ A`, where `A` is the set of accessible boundary points. Then (5.2) `|E ∖ φ⁻¹(V)| = 0`.
Modelling: `z : ℕ → ℂ` with values in `𝔻`; `∂Ω` is the frontier in `ℂ` and `dist(w_k, ∂Ω)` is `infDist`; `A` is
`accessiblePoints Ω` and `φ⁻¹(V)` is `bdryPreimage φ V` (§3); `Ω` is simply connected because it is the conformal
image of `𝔻`; `|·|` is the (outer) `arcMeasure`. -/
theorem lemma6_5_3 {z : ℕ → ℂ} (hz : ∀ k, z k ∈ unitDisc) {E : Set ℂ} (hE : E ⊆ sphere (0 : ℂ) 1)
    (hdense : IsNTDenseAE (range z) E) {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ unitDisc Ω) :
    arcMeasure (E \ bdryPreimage φ (frontier Ω ∩ (⋃ k, ball (φ (z k)) (2 * infDist (φ (z k)) (frontier Ω))) ∩
      accessiblePoints Ω)) = 0 := by
  sorry

end GarnettMarshall2005
