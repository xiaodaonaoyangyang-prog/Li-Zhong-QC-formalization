import References.Pommerenke1992.Ch09.S03_CapacityAndGreensFunction

/-!
# Pommerenke 1992, Ch. 9 §9.4 Pfluger's Theorem

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 9 *Curve Families and Capacity*, §9.4; source
`full.md` of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3…` (P2), lines 1163–1374.

* Proposition 9.15 ((9.4.1), (9.4.2); cited at P2 l. 1248, 1282 in the proof of Theorem 9.17; index "starlike function
  210") — `prop9_15_a`, `prop9_15_b`
* Formula (9.4.3) (inside the proof of Proposition 9.15; U+, cited "(3) and Theorem 9.7" at P2 l. 1254, 1284 in the
  proof of Theorem 9.17) — `eq9_4_3`
* Proposition 9.16 (a starlike function related to the "Evans function"; (9.4.4); cited at P2 l. 1282; index "Evans
  function 211", "Fσ-set 211") — `prop9_16`
* Formula (9.4.7) (U+; cited "(7)" at P2 l. 1352 and "(9.4.7)" at P2 l. 1525, 1624) — `eq9_4_7`
* Definition (the family `Γ_E(r)`, P2 l. 1233; index "Γ_E(r) 212"; used in the proofs of Corollary 9.18 and Theorems
  9.19, 9.21, 9.24) — `pflugerFamily`
* Theorem 9.17 (Pfluger's theorem, Pfl55; (9.4.8), (9.4.9); cited at P2 l. 423 ((9.1.5)), 1340, 1435, 1493, 1606 and
  "(9.4.8)" at P2 l. 1618; index "Pfluger's theorem 196, 212") — `thm9_17_a`, `thm9_17_b`
* Corollary 9.18 (BiCaGaJo89, Roh91; (9.4.12), (9.4.13); cited at P1 l. 6528 in the proof of Theorem 6.30,
  "Corollary 9.18 (to be proved later)") — `cor9_18`

Not items (DESIGN §3): "There is a close connection to the starlike functions studied in Section 3.6" (P2 l. 1165, a
remark); the proof of Proposition 9.15 apart from (9.4.3) ("the same holds for `h`", the use of (3.6.7), "`h(ζ)`
exists for `ζ ∈ 𝕋`", the `Λ`-computation, P2 l. 1187–1193); (9.4.5), (9.4.6) and the proof of Proposition 9.16;
Fig. 9.5, (9.4.10), (9.4.11) and the proof of Theorem 9.17 (with (2.5.6), Theorem 1.3 and Exercise 9.3.4 cited inside
it; the lower estimate is proved there for arbitrary `E ⊆ 𝕋`, P2 l. 1274); (9.4.14), Fig. 9.6 and the proof of
Corollary 9.18; the remark "`R²` can often be replaced by `R^{2+δ}`" (Roh91, P2 l. 1354); Exercises 9.4.1–9.4.4 (the
"Evans function" of Exercise 9.4.2, the generalized Privalov theorem of Exercise 9.4.3).

**Conventions.** As in §9.1–§9.3. Sets `E ⊆ 𝕋` are subsets of `sphere 0 1`; "Borel" is `MeasurableSet`; `Λ(E)` is the
arc length `circleMeasure E` (Ch. 4); compact sets have the compact capacity `GarnettMarshall2005.capacityCompact`,
arbitrary (Borel) sets the inner capacity `GarnettMarshall2005.capacity`. `h(ζ)` for `ζ ∈ 𝕋` is the angular limit
(`HasAngularLimit`). The function `h` of (9.4.1) enters through a hypothesis `h z = …` for `z ∈ 𝔻` (its values off
`𝔻` are never used). The quantity `exp(−π/mod Γ_E(r))` is written `EReal.exp (−(π/mod Γ_E(r)))` with the quotient in
`[0, ∞]`: it is `0` when `mod Γ_E(r) = 0` (`π/0 = ∞`, `exp(−∞) = 0`), the book's value, and no `Real.exp` of a junk
quotient occurs (`mod Γ_E(r) < ∞` always).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto IsJordanCurve)
open LehtoVirtanen1973 (arcFamilyModule)
open GarnettMarshall2005 (capacityCompact capacity)

/-- **Proposition 9.15** (§9.4; P2 l. 1167–1179; cited at P2 l. 1248, 1282), first part. Let `E ⊆ 𝕋` be compact and
`cap E > 0`. Then the equilibrium measure `μ` is uniquely determined.
Modelling: any two equilibrium measures of `E` (`IsEquilibriumMeasure`, Pommerenke's definition through (9.3.18),
(9.3.19)) are equal. -/
theorem prop9_15_a {E : Set ℂ} (hE : IsCompact E) (hET : E ⊆ sphere 0 1) (hcap : 0 < capacityCompact E)
    {μ ν : Measure ℂ} (hμ : IsEquilibriumMeasure E μ) (hν : IsEquilibriumMeasure E ν) : μ = ν := by
  sorry

/-- **Proposition 9.15** (§9.4; (9.4.1), (9.4.2); P2 l. 1167–1179; cited at P2 l. 1248, 1282), second part. Let
`E ⊆ 𝕋` be compact and `cap E > 0`. The function (9.4.1)
`h(z) = z (cap E)² exp[−2 ∫_E log(1 − ζ̄z) dμ(ζ)]` (`z ∈ 𝔻`) maps `𝔻` conformally onto a starlike domain (9.4.2)
`h(𝔻) = {s e^{iϑ} : 0 ≤ s < R(ϑ), 0 ≤ ϑ ≤ 2π} ⊆ 𝔻`, where `R(ϑ) = 1` for almost all `ϑ` and `|h(ζ)| = 1` for nearly
all `ζ ∈ E`.
Modelling: `μ` is the equilibrium measure of `E`; `log` is the principal branch (`Re(1 − ζ̄z) > 0` for `ζ ∈ 𝕋`,
`z ∈ 𝔻`, and the integrand is bounded on `E`, which carries `μ`); `cap E` is finite (`≤ 1`), so its real value is
used. "Conformally onto a starlike domain" is `IsStarlikeFunction h` (§3.6, which includes `h(0) = 0`); (9.4.2) with
`R(ϑ) = 1` for almost all `ϑ` says `h(𝔻) ⊆ 𝔻` and that for almost all `ϑ` the whole radius `{s e^{iϑ} : 0 ≤ s < 1}`
lies in `h(𝔻)`; `h(ζ)` is the angular limit, and "nearly all" is `NearlyEverywhereOn`. -/
theorem prop9_15_b {E : Set ℂ} (hE : IsCompact E) (hET : E ⊆ sphere 0 1) (hcap : 0 < capacityCompact E)
    {μ : Measure ℂ} (hμ : IsEquilibriumMeasure E μ) {h : ℂ → ℂ}
    (hh : ∀ z ∈ unitDisc, h z = z * ((capacityCompact E).toReal : ℂ) ^ 2 *
      exp (-2 * ∫ ζ, log (1 - conj ζ * z) ∂μ)) :
    IsStarlikeFunction h ∧ h '' unitDisc ⊆ unitDisc ∧
      (∀ᵐ ϑ : ℝ, ∀ s ∈ Ico (0 : ℝ) 1, (s : ℂ) * exp (ϑ * I) ∈ h '' unitDisc) ∧
      NearlyEverywhereOn E (fun ζ => ∃ w : ℂ, HasAngularLimit (fun z => (h z : ExtPlane)) ζ w ∧ ‖w‖ = 1) := by
  sorry

/-- **Formula (9.4.3)** (§9.4, inside the proof of Proposition 9.15; P2 l. 1183–1185; U+, cited "(3) and Theorem 9.7"
at P2 l. 1254, 1284 in the proof of Theorem 9.17). For the function `h` of (9.4.1),
`|h(z)| = |z| exp[−2g(z)] < 1` for `z ∈ 𝔻`, where `g` is the Green's function (9.3.17).
Modelling: as in `prop9_15_b`; `g = greenFnInf E μ`, which is finite on `𝔻` (the points of `𝔻` are off `E ⊆ 𝕋`), so
its real value is used. -/
theorem eq9_4_3 {E : Set ℂ} (hE : IsCompact E) (hET : E ⊆ sphere 0 1) (hcap : 0 < capacityCompact E)
    {μ : Measure ℂ} (hμ : IsEquilibriumMeasure E μ) {h : ℂ → ℂ}
    (hh : ∀ z ∈ unitDisc, h z = z * ((capacityCompact E).toReal : ℂ) ^ 2 *
      exp (-2 * ∫ ζ, log (1 - conj ζ * z) ∂μ)) :
    ∀ z ∈ unitDisc, ‖h z‖ = ‖z‖ * Real.exp (-2 * (greenFnInf E μ z).toReal) ∧ ‖h z‖ < 1 := by
  sorry

/-- **Proposition 9.16** (§9.4; (9.4.4); P2 l. 1195–1201; cited at P2 l. 1282 in the proof of Theorem 9.17; index
"Evans function 211"). If `E ⊆ 𝕋` is an `F_σ`-set of zero capacity then there is a starlike function
`h(z) = z + …` (`z ∈ 𝔻`) such that (9.4.4) `|h(z)| → ∞` as `z → ζ`, `z ∈ 𝔻`, for each `ζ ∈ E`.
Modelling: `F_σ` is `IsFSigma` (§6.2); "zero capacity" is the inner capacity `0`; `h(z) = z + …` is
`IsStarlikeFunction h` with `h'(0) = 1` (`h(0) = 0` is part of `IsStarlikeFunction`). -/
theorem prop9_16 {E : Set ℂ} (hET : E ⊆ sphere 0 1) (hF : IsFSigma E) (hcap : capacity E = 0) :
    ∃ h : ℂ → ℂ, IsStarlikeFunction h ∧ deriv h 0 = 1 ∧
      ∀ ζ ∈ E, Tendsto (fun z => ‖h z‖) (𝓝[unitDisc] ζ) atTop := by
  sorry

/-- **Formula (9.4.7)** (§9.4; P2 l. 1225–1229: "It follows from (9.3.33) and (9.3.36)"; U+, cited "(7)" at P2
l. 1352 and "(9.4.7)" at P2 l. 1525, 1624). For any Borel set `E` on `𝕋`,
`Λ(E)/2π ≤ sin(Λ(E)/4) ≤ cap E`.
Modelling: `Λ(E)` is `circleMeasure E` (finite, `≤ 2π`, so its real value is used); `cap E` is the inner capacity. -/
theorem eq9_4_7 {E : Set ℂ} (hEB : MeasurableSet E) (hET : E ⊆ sphere 0 1) :
    (circleMeasure E).toReal / (2 * π) ≤ Real.sin ((circleMeasure E).toReal / 4) ∧
      ENNReal.ofReal (Real.sin ((circleMeasure E).toReal / 4)) ≤ capacity E := by
  sorry

/-- **Definition** (§9.4, P2 l. 1233; index "Γ_E(r) 212"; used in the proofs of Corollary 9.18 and Theorems 9.19, 9.21,
9.24). For `E ⊆ 𝕋` and `0 < r < 1`, `Γ_E(r)` is the family of all curves in `{r < |z| < 1}` that connect `E` with
`{|z| = r}`.
Modelling: the connecting curves are `joiningArcFamily` (closed Jordan arcs from a point of `{|z| = r}` to a point of
`E`, all other points in the annulus; see §9.2). -/
def pflugerFamily (E : Set ℂ) (r : ℝ) : Set (Set ExtPlane) :=
  joiningArcFamily (toExt (LiZhongQC.annulus r 1)) (toExt (sphere 0 r)) (toExt E)

/-- **Theorem 9.17** (§9.4; Pfluger's theorem, Pfl55; (9.4.8); P2 l. 1231–1239; cited at P2 l. 1340, 1435, 1493, 1606
and "(9.4.8)" at P2 l. 1618), first part. Let `E` be a Borel set on `𝕋` and let `Γ_E(r)` (`0 < r < 1`) denote the
family of all curves in `{r < |z| < 1}` that connect `E` with `{|z| = r}`. Then (9.4.8)
`(√r/(1 + r)) cap E ≤ exp(−π/mod Γ_E(r)) ≤ (√r/(1 − r)) cap E` for `0 < r ≤ 1/3`.
Modelling: `cap E` is the inner capacity; `exp(−π/mod Γ_E(r))` is written as in the file header (`0` when the module
is `0`); the inequalities are taken in `[0, ∞]`. -/
theorem thm9_17_a {E : Set ℂ} (hEB : MeasurableSet E) (hET : E ⊆ sphere 0 1) {r : ℝ} (hr0 : 0 < r)
    (hr : r ≤ 1 / 3) :
    ENNReal.ofReal (Real.sqrt r / (1 + r)) * capacity E ≤
        EReal.exp (-((ENNReal.ofReal π / arcFamilyModule (pflugerFamily E r) : ℝ≥0∞) : EReal)) ∧
      EReal.exp (-((ENNReal.ofReal π / arcFamilyModule (pflugerFamily E r) : ℝ≥0∞) : EReal)) ≤
        ENNReal.ofReal (Real.sqrt r / (1 - r)) * capacity E := by
  sorry

/-- **Theorem 9.17** (§9.4; (9.4.9); P2 l. 1239–1243; cited at P2 l. 423 as Pfluger's theorem (9.1.5)), second part.
For a Borel set `E` on `𝕋`, (9.4.9) `cap E = lim_{r → 0} r^{−1/2} exp(−π/mod Γ_E(r))`.
[misprint?] The crop of (9.4.9) prints `mod Γ_r(r)`; it is read `mod Γ_E(r)`, as in (9.1.5) (P2 l. 426) and (9.4.8),
of which (9.4.9) is the consequence ("and thus").
Modelling: `r → 0` is `r → 0+`; the limit is taken in `[0, ∞]`. -/
theorem thm9_17_b {E : Set ℂ} (hEB : MeasurableSet E) (hET : E ⊆ sphere 0 1) :
    Tendsto (fun r : ℝ => ENNReal.ofReal (1 / Real.sqrt r) *
        EReal.exp (-((ENNReal.ofReal π / arcFamilyModule (pflugerFamily E r) : ℝ≥0∞) : EReal)))
      (𝓝[>] 0) (𝓝 (capacity E)) := by
  sorry

/-- **Corollary 9.18** (§9.4; BiCaGaJo89, Roh91; (9.4.12), (9.4.13); P2 l. 1318–1332; cited at P1 l. 6528 in the proof
of Theorem 6.30). Let `f₁` and `f₂` map `𝔻` onto the inner and outer domain of the Jordan curve `J ⊆ ℂ` and let
(9.4.12) `A_j = f_j⁻¹(J ∩ D(a, R))` (`a ∈ J`, `R > 0`) for `j = 1, 2`. Then (9.4.13)
`Λ(A₁) Λ(A₂) ≤ 4π² cap A₁ cap A₂ ≤ M R²` for `R < R₀`, where the constants `M` and `R₀` depend only on `f₁` and `f₂`.
Modelling (Q9.12): `f₁` maps `𝔻` conformally onto the inner domain `innerDomain J`; `f₂` is a conformal map of `ℂ̂`
(`LehtoVirtanen1973.IsConformalMap`) of `𝔻` onto the outer domain `outerDomain J` (§6.6), which contains `∞`.
`f_j⁻¹(B)` is the set of `ζ ∈ 𝕋` whose radial limit lies in `B` (`radialPreimage`, (6.2.16); for these maps the
radial limits exist everywhere and give the homeomorphic boundary extensions of Theorem 2.6), a relatively open subset
of `𝕋`. `Λ` is the arc length `circleMeasure`, `cap` the inner capacity; `D(a, R)` is the open disc. The constants:
`∀ J f₁ f₂, ∃ M R₀`, with `R₀ > 0`. -/
theorem cor9_18 {J : Set ℂ} (hJ : IsJordanCurve (toExt J)) {f₁ : ℂ → ℂ}
    (hf₁ : IsConformalOnto f₁ unitDisc (innerDomain J)) {f₂ : ExtPlane → ExtPlane}
    (hf₂ : LehtoVirtanen1973.IsConformalMap f₂ (toExt unitDisc)) (hf₂D : f₂ '' toExt unitDisc = outerDomain J) :
    ∃ M R₀ : ℝ, 0 < R₀ ∧ ∀ a ∈ J, ∀ R : ℝ, 0 < R → R < R₀ → ∀ A₁ A₂ : Set ℂ,
      A₁ = radialPreimage (fun z => (f₁ z : ExtPlane)) (toExt (J ∩ ball a R)) →
      A₂ = radialPreimage (fun z => f₂ (z : ExtPlane)) (toExt (J ∩ ball a R)) →
      circleMeasure A₁ * circleMeasure A₂ ≤ ENNReal.ofReal (4 * π ^ 2) * capacity A₁ * capacity A₂ ∧
        ENNReal.ofReal (4 * π ^ 2) * capacity A₁ * capacity A₂ ≤ ENNReal.ofReal (M * R ^ 2) := by
  sorry

end Pommerenke1992
