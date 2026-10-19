import References.Pommerenke1992.Ch09.S04_PflugersTheorem

/-!
# Pommerenke 1992, Ch. 9 §9.5 Applications to Conformal Mapping

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 9 *Curve Families and Capacity*, §9.5; source
`full.md` of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3…` (P2), lines 1375–1664.

* Theorem 9.19 ("We first generalize Theorem 1.7"; (9.5.1)–(9.5.3), the OCR prints a lone "(1)" and tags the first
  display "(2)" [OCR]; cited at P2 l. 1471, 1998, 2461 and forward at P1 l. 1175, 6088) — `thm9_19_a`, `thm9_19_b`
* Corollary 9.20 ("more precise than Corollary 4.18"; (9.5.8)–(9.5.10); forward at P1 l. 3707 and P2 l. 441
  ((9.1.7)); index "d_f(z) 216") — `cor9_20`
* Theorem 9.21 (Pom75, p. 348; compare Kom42, Jen56; an analogue of Löwner's lemma; (9.5.12); cited "(12)" at P2
  l. 1525, 1536 and at P2 l. 1576, 2277, and P2 l. 441 ((9.1.8)); index "Löwner's lemma 217") — `thm9_21`
* Corollary 9.22 ((9.5.13) and the refinement for arcs; cited at P2 l. 1511, 1536; index "harmonic measure 218") —
  `cor9_22_a`, `cor9_22_b`
* Theorem 9.23 (Schi46, Pom68; (9.5.16); cited at P2 l. 2301 in Exercise 10.3.4) — `thm9_23`
* Theorem 9.24 ((9.5.19), (9.5.20); cited at P2 l. 2176 in the proof of Proposition 10.10; index "crowding 220") —
  `thm9_24`

Not items (DESIGN §3): "By applying a suitable Möbius transformation we deduce (Beu40) at once that every conformal
map of `𝔻` into `Ĉ` has angular limits nearly everywhere" (P2 l. 1397; U−, "at once", not cited: P2 l. 1998, 2461
cite Theorem 9.19 for maps into `ℂ`); (9.5.4)–(9.5.6) and the proof of Theorem 9.19 (the Koebe distortion theorem,
Exercise 1.3.3, Theorem 4.20, Corollary 2.17); (9.5.7) "`cap{ζ ∈ 𝕋 : ∫₀¹ |f'(rζ)| dr = ∞} = 0`" and "`f(ζ) ≠ ∞`
exists outside this Borel set" (P2 l. 1437–1443; U−, the end of the proof of Theorem 9.19, = (9.1.6), not cited);
(9.5.11) and the proof of Corollary 9.20; the recalls of the harmonic measure `ω(z, A)` of (4.4.1) and of the
non-euclidean distance `λ(z, z')` of (1.2.8) (P2 l. 1501; `harmonicMeasure`, `hypDistD`); (9.5.14) and the
Carleman–Milloux problem (P2 l. 1511–1517; U−, derived from (9.5.13), not cited); the proof of Corollary 9.22, Fig.
9.7 and the sharpness example (9.5.15) (P2 l. 1536–1554, an example not cited as a result; "cap `B` = sin β" reads
`cap f(A)` [misprint?]); the recall of the class `Σ` (P2 l. 1556, `IsClassSigma`); (9.5.17) (Duf45, "In particular it
easily follows"; U−, not cited); the proof of Theorem 9.23 (the special case of a continuum; "see Pom75, p. 344 or
Mak87, p. 50 for the general case"); (9.5.18) (Küh71, quoted and not cited; the Part C (8.6.14) precedent); the
remarks on boundary sets that are difficult to reach, "crowding" and numerical conformal mapping (P2 l. 1602–1604,
compare Corollary 6.26); the proof of Theorem 9.24 and Fig. 9.8; Exercises 9.5.1–9.5.6.

**Conventions.** As in §9.1–§9.4. `f(ζ)` for `ζ ∈ 𝕋` is the angular limit (`HasAngularLimit`; for conformal maps it
equals the radial limit, Corollary 2.17), and `f(E)` for `E ⊆ 𝕋` is the set of these limits, the finite part of
`radialImage` (§6.2). For `g ∈ Σ` the angular limit from outside at `ζ ∈ 𝕋` is the angular limit of `z ↦ g(1/z)` at
`ζ̄ = 1/ζ` (the Part C ruling Q6.9). `Λ` is `circleMeasure` on `𝕋` and `μH[1]` in the plane; `cap` is the inner
capacity `GarnettMarshall2005.capacity`; area is `volume`. "Absolute constant" is `∃ K, ∀ f …`. Integrals of `|f'|`
are lower integrals in `[0, ∞]`: `∫₀¹ |f'(rζ)| dr` over `r ∈ [0, 1)`, and `∫_S |f'(s)| |ds|` against the linear
measure `μH[1]` on the non-euclidean segment `S` (a Jordan arc, on which `|ds|` is the linear measure). The
exponential `exp(−πb²/area H)` is `EReal.exp` of `−(πb²/area H)` with the quotient in `[0, ∞]`, so that `area H = ∞`
gives `exp(0) = 1` and no junk quotient occurs.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto)
open References (finitePart)
open GarnettMarshall2005 (capacity)

/-- **Theorem 9.19** (§9.5; P2 l. 1377–1379; cited at P2 l. 1471, 1998, 2461 and forward at P1 l. 1175, 6088), first
part. Let `f` map `𝔻` conformally into `ℂ`. Then the angular limit `f(ζ)` exists and is finite for nearly all
`ζ ∈ 𝕋`.
Modelling: "nearly all" is `NearlyEverywhereOn` (the exceptional set has inner capacity `0`). -/
theorem thm9_19_a {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) :
    NearlyEverywhereOn (sphere 0 1) (fun ζ => ∃ w : ℂ, HasAngularLimit (fun z => (f z : ExtPlane)) ζ w) := by
  sorry

/-- **Theorem 9.19** (§9.5; (9.5.1)–(9.5.3); P2 l. 1379–1395), second part. Let `f` map `𝔻` conformally into `ℂ`. If
`R ≥ 1` then (9.5.1) `|f(ζ) − f(0)| ≤ |f'(0)| R` and (9.5.2) `∫₀¹ |f'(rζ)| dr ≤ K₁ |f'(0)| R log(6R)` for
`ζ ∈ 𝕋 ∖ E`, with an absolute constant `K₁`, where the exceptional set `E` satisfies (9.5.3)
`Λ(E)/(2π) ≤ cap E ≤ 1/√R`.
[OCR] The display tags are shifted: a lone "(1)" precedes the first display, which carries "(2)", and the integral
display is untagged; the proof (P2 l. 1437) gets "(2)" from Theorem 4.20, so (9.5.1) is the bound for `|f(ζ) − f(0)|`
and (9.5.2) the integral bound.
Modelling (Q9.6(f)): `K₁` is absolute (`∃ K₁, ∀ f R`); `E` is the exact exceptional set, the `ζ ∈ 𝕋` at which the
finite angular limit `f(ζ)` does not exist or (9.5.1) or (9.5.2) fails. It is a Borel set: the set of `ζ` with a finite
angular limit is Borel by the Cauchy criterion, which by continuity of `f` need only be tested over rational Stolz
angles, rational tolerances and rational points, and `ζ ↦ ∫₀¹ |f'(rζ)| dr` is lower semicontinuous (the integral of a
lower semicontinuous function of `(r, ζ)`); the bound `‖w − f(0)‖ ≤ |f'(0)| R` is a closed condition on the limit `w`. So that `Λ(E)/(2π) ≤ cap E` is meaningful
under the inner capacity (compare (9.4.7), which needs Borel sets); the book's exceptional set of the proof, (9.5.5),
contains it. The integral is a lower integral in `[0, ∞]`. -/
theorem thm9_19_b : ∃ K₁ : ℝ, ∀ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc → InjOn f unitDisc → ∀ R : ℝ, 1 ≤ R →
    ∀ E : Set ℂ, E = {ζ ∈ sphere (0 : ℂ) 1 | ¬ ((∃ w : ℂ, HasAngularLimit (fun z => (f z : ExtPlane)) ζ w ∧
        ‖w - f 0‖ ≤ ‖deriv f 0‖ * R) ∧
      ∫⁻ r in Ico (0 : ℝ) 1, ‖deriv f (r * ζ)‖ₑ ≤ ENNReal.ofReal (K₁ * ‖deriv f 0‖ * R * Real.log (6 * R)))} →
      circleMeasure E / ENNReal.ofReal (2 * π) ≤ capacity E ∧ capacity E ≤ ENNReal.ofReal (1 / Real.sqrt R) := by
  sorry

/-- **Corollary 9.20** (§9.5; (9.5.8)–(9.5.10); P2 l. 1445–1463; forward at P1 l. 3707; the case `a = π` is (9.1.7)).
Let `f` map `𝔻` conformally onto `G ⊆ ℂ` and let `ζ ∈ 𝕋`, `0 ≤ r < 1`, `a > 0` and `R ≥ 1`. Then (9.5.8)
`|f(z) − f(rζ)| ≤ 4R d_f(rζ)` for `z ∈ I ∖ E`, where `I = {e^{it} : |t − arg ζ| ≤ a(1 − r)}` and (9.5.9)
`cap E ≤ (1 + a²)(1 − r)/√R`, and if `S` is the non-euclidean segment from `rζ` to `z` then (9.5.10)
`∫_S |f'(s)| |ds| ≤ K₂ d_f(rζ) R log(6R)` for `z ∈ I ∖ E`.
Modelling (Q9.6(g)): `K₂` is absolute (`∃ K₂, ∀ f G ζ r a R`); `E` is some subset of `I` (the proof's `φ(E*) ∩ I`);
`f(z)` is the finite angular limit at `z ∈ I ∖ E`; `I` is `arcT (arg ζ − a(1 − r)) (arg ζ + a(1 − r))` (all of `𝕋`
when `a(1 − r) ≥ π`); `d_f` is `distToBoundary`; the integral over `S` is taken over its points in `𝔻` (the end point
`z ∈ 𝕋` has linear measure `0`). -/
theorem cor9_20 : ∃ K₂ : ℝ, ∀ (f : ℂ → ℂ) (G : Set ℂ), IsConformalOnto f unitDisc G →
    ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r a R : ℝ, 0 ≤ r → r < 1 → 0 < a → 1 ≤ R →
      ∃ E ⊆ arcT (arg ζ - a * (1 - r)) (arg ζ + a * (1 - r)),
        capacity E ≤ ENNReal.ofReal ((1 + a ^ 2) * (1 - r) / Real.sqrt R) ∧
        ∀ z ∈ arcT (arg ζ - a * (1 - r)) (arg ζ + a * (1 - r)) \ E,
          ∃ w : ℂ, HasAngularLimit (fun s => (f s : ExtPlane)) z w ∧
            ‖w - f (r * ζ)‖ ≤ 4 * R * distToBoundary f (r * ζ) ∧
            ∫⁻ s in nonEuclideanSegment (r * ζ) z ∩ unitDisc, ‖deriv f s‖ₑ ∂(μH[1] : Measure ℂ) ≤
              ENNReal.ofReal (K₂ * distToBoundary f (r * ζ) * R * Real.log (6 * R)) := by
  sorry

/-- **Theorem 9.21** (§9.5; Pom75, p. 348; (9.5.12); P2 l. 1479–1485; cited "(12)" at P2 l. 1525, 1536 and at P2
l. 1576, 2277). Let `f` map `𝔻` conformally into `𝔻` with `f(0) = 0`. If `E` is a Borel set on `𝕋` such that the
angular limit exists and `f(ζ) ∈ 𝕋` for `ζ ∈ E` then (9.5.12) `cap f(E) ≥ cap E/√|f'(0)| ≥ cap E`.
Modelling: `f(E)` is the finite part of `radialImage` (the angular limits, which are the radial limits); capacities are
inner capacities in `[0, ∞]`; `f'(0) ≠ 0` for a conformal map, so `1/√|f'(0)|` is a genuine real number. -/
theorem thm9_21 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hmaps : MapsTo f unitDisc unitDisc) (hf0 : f 0 = 0) {E : Set ℂ} (hEB : MeasurableSet E)
    (hET : E ⊆ sphere 0 1)
    (hlim : ∀ ζ ∈ E, ∃ w ∈ sphere (0 : ℂ) 1, HasAngularLimit (fun z => (f z : ExtPlane)) ζ w) :
    ENNReal.ofReal (1 / Real.sqrt ‖deriv f 0‖) * capacity E ≤
        capacity (finitePart (radialImage (fun z => (f z : ExtPlane)) E)) ∧
      capacity E ≤ ENNReal.ofReal (1 / Real.sqrt ‖deriv f 0‖) * capacity E := by
  sorry

/-- **Corollary 9.22** (§9.5; (9.5.13); P2 l. 1503–1507; cited at P2 l. 1511, 1536), first part. Let `f` map `𝔻`
conformally into `𝔻 ∖ {w}`. If `A` is a Borel set in `𝕋` and `f(A) ⊆ 𝕋` then, for `z ∈ 𝔻`, (9.5.13)
`sin[πω(z, A)/2] ≤ (1 − exp[−4λ(f(z), w)])^{1/2}`.
Modelling: `w ∈ 𝔻` (the non-euclidean distance `λ = hypDistD` of (1.2.8) is taken between points of `𝔻`); "`f(A) ⊆ 𝕋`"
includes the existence of the angular limits on `A`; `ω(z, A)` is `harmonicMeasure z A` ((4.4.1)). -/
theorem cor9_22_a {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {w : ℂ}
    (hw : w ∈ unitDisc) (hmaps : MapsTo f unitDisc (unitDisc \ {w})) {A : Set ℂ} (hAB : MeasurableSet A)
    (hAT : A ⊆ sphere 0 1)
    (hlim : ∀ ζ ∈ A, ∃ v ∈ sphere (0 : ℂ) 1, HasAngularLimit (fun z => (f z : ExtPlane)) ζ v) :
    ∀ z ∈ unitDisc, Real.sin (π * harmonicMeasure z A / 2) ≤ Real.sqrt (1 - Real.exp (-4 * hypDistD (f z) w)) := by
  sorry

/-- **Corollary 9.22** (§9.5; P2 l. 1509), second part. If moreover `f(A)` is an arc of `𝕋` then there is an
additional factor `sin[πω(f(z), f(A))/2]` on the right-hand side of (9.5.13):
`sin[πω(z, A)/2] ≤ (1 − exp[−4λ(f(z), w)])^{1/2} sin[πω(f(z), f(A))/2]`.
Modelling: as in `cor9_22_a`; "`f(A)` is an arc" is `{e^{it} : t₁ < t < t₂} ⊆ f(A) ⊆ {e^{it} : t₁ ≤ t ≤ t₂}` with
`t₁ < t₂ ≤ t₁ + 2π` (open, half-open and closed arcs; the harmonic measure does not see the end points), `f(A)` being
the finite part of `radialImage`; the remark that the factor is `< 1` (for a proper arc) is not part of the
statement. The OCR's "there there is" reads "then there is". -/
theorem cor9_22_b {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {w : ℂ}
    (hw : w ∈ unitDisc) (hmaps : MapsTo f unitDisc (unitDisc \ {w})) {A : Set ℂ} (hAB : MeasurableSet A)
    (hAT : A ⊆ sphere 0 1)
    (hlim : ∀ ζ ∈ A, ∃ v ∈ sphere (0 : ℂ) 1, HasAngularLimit (fun z => (f z : ExtPlane)) ζ v) {t₁ t₂ : ℝ}
    (ht : t₁ < t₂) (ht2 : t₂ ≤ t₁ + 2 * π)
    (harc₁ : (fun t : ℝ => exp (t * I)) '' Ioo t₁ t₂ ⊆ finitePart (radialImage (fun z => (f z : ExtPlane)) A))
    (harc₂ : finitePart (radialImage (fun z => (f z : ExtPlane)) A) ⊆ arcT t₁ t₂) :
    ∀ z ∈ unitDisc, Real.sin (π * harmonicMeasure z A / 2) ≤
      Real.sqrt (1 - Real.exp (-4 * hypDistD (f z) w)) *
        Real.sin (π * harmonicMeasure (f z) (finitePart (radialImage (fun z => (f z : ExtPlane)) A)) / 2) := by
  sorry

/-- **Theorem 9.23** (§9.5; Schi46, Pom68; (9.5.16); P2 l. 1558–1562; cited at P2 l. 2301 in Exercise 10.3.4). If
`g ∈ Σ` and `A ⊆ 𝕋` is a Borel set such that `g(ζ)` exists for `ζ ∈ A` then (9.5.16) `cap g(A) ≥ (cap A)²`.
Modelling: `g ∈ Σ` is `IsClassSigma g` (`g(ζ) = ζ + b₀ + b₁ζ⁻¹ + …` univalent for `|ζ| > 1`); `g(ζ)` for `ζ ∈ 𝕋` is the
angular limit from outside, transported by `ζ ↦ 1/ζ` (the angular limit of `z ↦ g(1/z)` at `ζ̄`), and it is finite
(`g` is bounded near `𝕋`); `g(A)` is the set of these limits; capacities are inner capacities. -/
theorem thm9_23 {g : ℂ → ℂ} (hg : IsClassSigma g) {A : Set ℂ} (hAB : MeasurableSet A) (hAT : A ⊆ sphere 0 1)
    (hlim : ∀ ζ ∈ A, ∃ w : ℂ, HasAngularLimit (fun z => (g (z⁻¹) : ExtPlane)) (conj ζ) w) :
    capacity A ^ 2 ≤ capacity {w : ℂ | ∃ ζ ∈ A, HasAngularLimit (fun z => (g (z⁻¹) : ExtPlane)) (conj ζ) w} := by
  sorry

/-- **Theorem 9.24** (§9.5; (9.5.19), (9.5.20); P2 l. 1590–1600; cited at P2 l. 2176 in the proof of Proposition
10.10). Let `f` map `𝔻` conformally onto `G ⊆ ℂ` and let `E ⊆ 𝕋`. If `0 < α ≤ 1` and if `H` is an open subset of `G`
such that (9.5.19) `dist(f(0), H) ≥ α|f'(0)|`, `Λ(f(C) ∩ H) ≥ b ≥ 0` for every curve `C ⊆ 𝔻` from `0` to `E`, then
(9.5.20) `Λ(E) ≤ 2π cap E < (15/√α) exp(−πb²/area H)`.
[CORRECTION] (leader ruling) The first inequality `Λ(E) ≤ 2π cap E` needs `E` Borel: it comes from (9.4.7), which is
stated for Borel sets, and it fails for a Bernstein set `E ⊆ 𝕋` (every compact subset is countable, so the inner
capacity is `0`, while the outer measure is `2π`), which satisfies the hypotheses with `f = id`, `α = 1/2`,
`H = D(0.8, 0.1)` and `b = 0`. It is stated for Borel `E`; the second inequality holds for every `E` (its proof, through
the lower estimate of Pfluger's theorem, which is proved for arbitrary `E ⊆ 𝕋`, P2 l. 1274, allows it).
[OCR] (9.5.19) prints `A(f(C) ∩ H)`: the glyph `Λ` read as `A` (crop checked).
Modelling: the curves `C` are half-open curves (`HalfOpenCurve`, (1.1.11)) with `C(α) = 0`, lying in `𝔻` and ending at
a point of `E`; `Λ(f(C) ∩ H)` is `μH[1]` of the image point set; `dist(f(0), H)` is `infDist` (for `H = ∅` Mathlib's
value `0` makes the hypothesis fail, which loses nothing: then `b = 0` works for the book as well, and `H ≠ ∅` has
positive area); `Λ(E)` is `circleMeasure E`, `cap E` the inner capacity, `area H` is `volume H` in `[0, ∞]`. -/
theorem thm9_24 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {E : Set ℂ} (hET : E ⊆ sphere 0 1)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {H : Set ℂ} (hHo : IsOpen H) (hHG : H ⊆ G)
    (hdist : α * ‖deriv f 0‖ ≤ infDist (f 0) H) {b : ℝ} (hb : 0 ≤ b)
    (hC : ∀ C : HalfOpenCurve, C.toFun C.α = 0 → C.toFun '' Ico C.α C.β ⊆ unitDisc →
      (∃ ζ ∈ E, C.EndsAt (ζ : ExtPlane)) → ENNReal.ofReal b ≤ μH[1] (f '' (C.toFun '' Ico C.α C.β) ∩ H)) :
    (MeasurableSet E → circleMeasure E ≤ ENNReal.ofReal (2 * π) * capacity E) ∧
      ENNReal.ofReal (2 * π) * capacity E <
        ENNReal.ofReal (15 / Real.sqrt α) * EReal.exp (-((ENNReal.ofReal (π * b ^ 2) / volume H : ℝ≥0∞) : EReal)) := by
  sorry

end Pommerenke1992
