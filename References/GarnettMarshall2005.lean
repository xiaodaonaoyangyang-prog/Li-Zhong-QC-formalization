import References.GarnettMarshall2005.Ch01.S01_HalfPlaneAndDisc
import References.GarnettMarshall2005.Ch01.S02_FatouMaximalFunctions
import References.GarnettMarshall2005.Ch01.S03_CaratheodoryTheorem
import References.GarnettMarshall2005.Ch01.S04_DistortionHyperbolicMetric
import References.GarnettMarshall2005.Ch01.S05_HaymanWuTheorem
import References.GarnettMarshall2005.Ch02.S01_SchwarzAlternatingMethod
import References.GarnettMarshall2005.Ch02.S02_GreenFunctionsPoissonKernels
import References.GarnettMarshall2005.Ch02.S03_ConjugateFunctions
import References.GarnettMarshall2005.Ch02.S04_BoundarySmoothness
import References.GarnettMarshall2005.Ch03.S01_CapacityGreenFunctions
import References.GarnettMarshall2005.Ch03.S02_LogarithmicPotential
import References.GarnettMarshall2005.Ch03.S03_EnergyIntegral
import References.GarnettMarshall2005.Ch03.S04_EquilibriumDistribution
import References.GarnettMarshall2005.Ch03.S05_WienerSolution
import References.GarnettMarshall2005.Ch03.S06_RegularPoints
import References.GarnettMarshall2005.Ch03.S07_WienerSeries
import References.GarnettMarshall2005.Ch03.S08_PolarSetsHarmonicMeasureZero
import References.GarnettMarshall2005.Ch03.S09_EstimatesHarmonicMeasure
import References.GarnettMarshall2005.Ch04.S01_DefinitionsExamples
import References.GarnettMarshall2005.Ch04.S02_UniquenessExtremalMetrics
import References.GarnettMarshall2005.Ch04.S03_FourRules
import References.GarnettMarshall2005.Ch04.S04_ExtremalMetricsExtremalDistance
import References.GarnettMarshall2005.Ch04.S05_ExtremalDistanceHarmonicMeasure
import References.GarnettMarshall2005.Ch04.S06_ThetaIntegralEstimate
import References.GarnettMarshall2005.Ch05.S01_AsymptoticValuesEntireFunctions
import References.GarnettMarshall2005.Ch05.S02_LowerBounds
import References.GarnettMarshall2005.Ch05.S03_ReducedExtremalDistance
import References.GarnettMarshall2005.Ch05.S04_TeichmullerModulsatz
import References.GarnettMarshall2005.Ch05.S05_BoundaryConformality
import References.GarnettMarshall2005.Ch05.S06_ConditionsMoreGeometric
import References.GarnettMarshall2005.Ch06.S01_FMRieszTheorem
import References.GarnettMarshall2005.Ch06.S02_PrivalovPlessner
import References.GarnettMarshall2005.Ch06.S03_AccessiblePoints
import References.GarnettMarshall2005.Ch06.S04_ConePointsMcMillan
import References.GarnettMarshall2005.Ch06.S05_CompressionExpansion
import References.GarnettMarshall2005.Ch06.S06_PommerenkeExtension
import References.GarnettMarshall2005.App.A_HardySpaces
import References.GarnettMarshall2005.App.B_MixedBoundaryValueProblems
import References.GarnettMarshall2005.App.C_DirichletPrinciple
import References.GarnettMarshall2005.App.D_HausdorffMeasure
import References.GarnettMarshall2005.App.F_MartingalesBrownianMotionKakutani
import References.GarnettMarshall2005.App.G_CarlemanMethod
import References.GarnettMarshall2005.App.H_ExtremalDistanceFCJordan
import References.GarnettMarshall2005.App.I_McMillanTwistPoint

/-!
# Garnett–Marshall, *Harmonic Measure* (2005)

J. B. Garnett, D. E. Marshall, *Harmonic Measure*, New Mathematical Monographs 2, Cambridge University Press,
Cambridge 2005. Statement-level formalization: genuine definitions, every result of the book stated with a `sorry`
proof; results already in the project or in Mathlib are passed with an `exists:` pointer in the file's item index.

## Sources

The OCR'd text (MinerU) in `D:\lean\lizhong_thm21_archive\refs\`:
- `harmonic measure.pdf-e1247c10-…\full.md` (P1) — front matter, Ch. I – V §5 (book pp. 1–182);
- `harmonic measure.pdf-ea943014-…\full.md` (P2) — V §5 – X §4 (pp. 183–382);
- `harmonic measure.pdf-708022b4-…\full.md` (P3) — X §4 – XI, Appendices A–M, bibliography, indexes (pp. 383–571).

## Coverage

The whole book is present (constant page offsets, no gaps; p. 554 is blank); both seams (inside V §5 and X §4) are
seamless. MinerU dropped the two footnotes of the book (pp. 229 and 376); they are recovered from `layout.json`.
Delivered so far: Chapters I–VI and Appendices A–D, F–I (with the shared files `References.Common.ExtPlaneBorel` and
`References.Common.Subharmonic`).

## Standing conventions and their modelling

- The book's `ℂ*` is the extended plane `LiZhongQC.ExtPlane` (`OnePoint ℂ`); domains are open connected subsets
  (`References.IsDomainExt`), Jordan domains are `References.IsJordanDomainExt`, `∂Ω` is the boundary in `ℂ*`. Items
  whose content is planar take `Ω : Set ℂ` with the `ℂ*`-boundary `frontier (toExt Ω)` where `∞` matters.
- Conformal maps of `ℂ*`-domains are `LehtoVirtanen1973.IsConformalMap`; planar conformal maps are
  `LiZhongQC.IsConformalOnto`.
- Harmonic measure `ω(z, ·, Ω)` is a measure at every stage the book introduces it (the half-plane and the disc via
  the Poisson kernel, Jordan domains via the conformal map, finitely connected Jordan domains in II.1); the number
  `ω(z, E, Ω)` is `(μ E).toReal`. Borel sets of `ℂ*` come from the scoped instance of `References.Common.ExtPlaneBorel`
  (`open scoped References`).
- `|E|` on `∂𝔻` is arc length (total mass `2π`) and `‖f‖_p` is taken with respect to `dθ`, as in the book; the disc
  Poisson kernel is Mathlib's `poissonKernel` with the book's factor `1/(2π)` written explicitly.
- Cones are `LiZhongQC.stolzAngle`; a nontangential limit is a limit through every cone `Γ_α`, `α > 1`.
- Constants are quantified as in the book (`∃ C, ∀ …`, `∀ α, ∃ A_α, ∀ …`); `limsup ≤ 0` is written in `ε`-form.
- Exercises ("Exercises and Further Results"), Notes, examples, figures and conjectures are not items; a notion that
  a statement needs and that the book defines only in an exercise is defined at its first use.
- Unlabelled results stated in the text and cited later are included (bullets "Unlabelled (§n, P1:line)"); unlabelled
  facts used only inside proofs, remarks, examples and proof steps are not items.

## Corrections

Repairs of the source (misprints, OCR damage, statements false as printed), each marked in the declaration's
docstring:
- I.2, Lemma 2.4 (P1:687): the lead-in is garbled in the OCR ("weak-type I·I: I f f ∈ L¹"); read "weak-type 1-1:
  if f ∈ L¹" [OCR] (`lemma1_2_4`; the inequality (2.8) was checked against the equation image).
- I.4, Whitney squares (P1:1110–1118): condition (iii) reads "dim" for diam [OCR]; `<` or `≤` there is
  unverifiable (inline formula) and both keep every result true (`IsWhitneyFamily`).
- II.2, (2.20) (P1:2238–2248): false as printed when `∂Ω` has two or more components (the arcs `γ ∋ ζ` stay in the
  component `J` of `ζ`); stated in the additive form `C (M_s f(ζ) + ∫_{∂Ω∖J} |f| ds)`, true for every `f ∈ L¹(ds)`
  and the printed statement when `∂Ω` is connected [CORRECTION] (`eq2_2_20`).
- II.2, Theorem 2.7 (P1:2184): "H u(z)" is "If u(z)" [OCR] (`thm2_2_7_i`, `thm2_2_7_ii`).
- App. A: "Theorem A.4", "Corollary A.5" (P3:2275, 2307; text-layer spans of the source, not OCR output) are
  Theorem A.1 and Corollary A.2 [misprint]; the lead-in of A.1(b) "H f f ≠ 0" is "If f ≢ 0" [OCR] (`thmA_1_a`,
  `thmA_1_b`, `corA_2`).
- App. A, Theorem A.3 (P3:2311–2322): false as printed (`‖f*_α‖_p ≤ A_α ‖f‖_{Hᵖ}` with `A_α` independent of
  `p ∈ (0, ∞]`; `f(z) = e^{Nz}` forces a constant `≥ e^{ρ²/p}`, `ρ = (α − 1)/(α + 1)`); stated in the p-th-power
  form `∫ (f*_α)^p dθ ≤ A_α ‖f‖^p_{Hᵖ}`, which the book's proof gives [CORRECTION] (`thmA_3`).
- III: "`a ∋ Ω̄`" (P1:3284) is `a ∉ Ω̄` (`robinConstantFC`), and the lead-ins "H …" at P1:3496, 3598, 3778 and
  4716 are "If …" (`lemma3_2_1`, `thm3_3_1_a`, `lemma3_4_2_a`, `cor3_8_4_a`) [OCR or misprint; inline, no crop];
  the statement of Example 1.2 is garbled ("I^r E ⊂ ∂𝔻, t h e n", P1:3444) [OCR] (`example3_1_2`).
- III.7, Theorem 7.1 (P1:4445–4456): false as printed, with the series (7.2), (7.3) from `n = 1` (crops): for
  `Ω = 𝔻 ∖ {0}`, `ζ = 0`, `γ(A₁ ∖ Ω) = γ(A₁ ∩ ∂Ω) = γ(∂𝔻) = 0`, so the `n = 1` term is `1/0 = ∞` at the irregular
  point `0`; stated with the series from `n = 2`, which is the book's criterion whenever the printed first term is
  finite [CORRECTION] (`thm3_7_1`).
- III.7: the label (7.9) is printed twice (P1:4526 in the proof of Theorem 7.1, P1:4561 for the hypothesis of
  Corollary 7.3; there is no (7.10)); the proof of Corollary 7.3 cites the second [numbering slip] (`cor3_7_3`); the
  labels lie outside the equation crops, so the duplicate rests on the OCR text and the citations at P1:4535, 4566.
- III.8, Corollary 8.4 (P1:4716): "every bounded harmonic function on Ω ∩ E" is read `Ω ∖ E` [OCR?] (inline
  formula, OCR confidence 0.70, no crop) (`cor3_8_4_b`).
- IV.1, conformal invariance (P1:5870): "λ_{𝒪(Ω)}" is `λ_{φ(Ω)}` [OCR]; the quadrilateral normalization
  (P1:5929–5935): "i, 0, , and ℓ + i" is `i, 0, ℓ, ℓ + i` [OCR] (`extremalLengthGM_conformal`,
  `quadrilateral_extremalDist`).
- IV.2, Theorem 2.1 (P1:5988): the equality clause (b) and its "in particular" (c) are false as printed when the
  common ratio `L²/A` (resp. `λ`) is `0` or `∞` (for (b), and for `λ = ∞` in (c): one segment `γ₀` as the family,
  `ρ_j = χ_{D_j}` or `∞·χ_{γ₀} + χ_{D_j}` for disjoint discs `D_j`; for `λ = 0` in (c): the family of all
  rectifiable arcs, for which every metric is extremal); stated with `0 < L²/A < ∞` and `0 < λ < ∞` [CORRECTION]
  (`thm4_2_1_b`, `thm4_2_1_c`).
- IV.3 (P1:6032): `d_Ω(E, F) = d_{Ω∖(E∪F)}(E, F)` for closed `E, F ⊆ Ω̄` is false as printed (`Ω = 𝔻`, `E = 𝔻̄`,
  `F = ∅`: `∞` against `0`; overlapping `E ⊂ F`: `0` against `∞`); stated for disjoint non-empty `E`, `F`
  [CORRECTION] (`extremalDistGM_diff`).
- IV.3, the parallel rule (P1:6092): "we obtain (2.3)" is (3.3) [misprint] (a text-layer span; `parallel_rule`);
  (3.5) of the symmetry rule (P1:6116–6128): as printed the hypothesis `Ω₁ ⊃ Ω ∪ T(Ω)` is too weak (the argument
  needs `Ω₁ ∩ ℍ = Ω`), recorded only, not stated; the rule (3.4) is `symmetry_rule`.
- IV.6, Theorem 6.1: "separating z from F" is "separating `z₀` from `F`" [OCR or misprint?] (a text-layer span;
  the reading is forced) (`thm4_6_1`).
- V.3, Corollary 3.6 (P1:7153): "`R > 0`" and "independent of ψ and R" are `λ` [misprint] (the display shows
  `Cλ^{−1/2}`; `cor5_3_6`).
- V.4, Corollary 4.3 (P1:7330): false as printed; (4.11) cannot hold with `C` independent of `R ∈ (1, e]` (for a
  curve `σ` within the angle `ε`, the radial segments outside it give an excess `≤ ε log R/(2π(2π − ε)) → 0`; the
  proof hides `C = 2π²/(log R)²`, P1:7386), and for `ε₀ ≥ 1` both bounds tend to `+∞`; stated for `ε₀ < 1` and, in
  (4.11), for `R₀ ≤ R ≤ e` with `C = C(ε₀, R₀)` [CORRECTION] (`cor5_4_3`); the uses in Ch. VIII (P2:4233, 4537)
  also need angles `1 ≤ sup|arg| < π`, which no corrected formula of the book states.
- V.6 (P2:156): "`Ω̃_M` is the largest domain … whose boundary consists of two `M`-Lipschitz graphs" fails for
  `Ω̃ = ℂ` and whenever `Ω̃` contains a half-plane; stated under (6.3), the setting of Theorem 6.1 where it is used
  [CORRECTION] (`lipschitzSubregion_isLargest`).
- App. C, Lemma C.2 (C.7): "Δu = 0 on Ω" in a lemma set on `𝔻` is `𝔻` [misprint] (crop); Corollary C.4 needs `E`
  and `F` non-empty [reading] (for `E = ∅` every constant `≥ 1` minimizes) (`lemmaC_2`, `corC_4_a`, `corC_4_b`).
- App. D (P3:3205): "we change the definition (M.2)" is (D.2) [misprint] (a text-layer span; App. M's (M.2) is
  unrelated); Exercise D.2(b)'s hint (P3:3649) "Corollary A.2 implies Cap(K) > 0" is Corollary D.2 [misprint]
  (a text-layer span) (`hausdorffMeasureGM`, `corD_2`).
- `Λ₁` [book inconsistency]: App. D (P3:3219) says `Λ₁(E)` is half the arc length of `E` on a rectifiable curve
  (discs charged by radius), while Chapters VI–X, App. I and App. K use `Λ₁` as arc length; `Λ₁` is `μH[1]` there
  (leader ruling C2), `hausdorffMeasureGM` only for App. D's `Λ_h`, `Λ_α`.
- App. F, Theorem F.5: "Lemma F.3" is Lemma F.2 [misprint] (the only weak limit) (`thmF_5`).
- App. G, (G.9) is stated for `0 < ε ≤ b − x₀` [reading] (`eqG_9`); the displayed step before (G.10) needs
  `x₀ ≤ (1 − δ)b`, but (G.10) holds without it (a proof-step note in `eqG_10`).
- VI.6, (6.6) and the proof of Theorem 6.3 (P2:1432): "`J_j` separates `z_j` from `w`" makes (6.6) false (a thin
  wedge at `w` plus a boundary piece near `w` not cut off by the arcs gives a left side `≳ r^{1/3}` against a right
  side `≈ r²`); the proof's Theorem IV.6.2 needs separation from `Γ ∩ B(w, r)`, which is stated in (6.6) [CORRECTION]
  (`IsAdmissibleCircleArcs` with `A = Γ ∩ B(w, r)`, `eq6_6_6`); Corollary 6.4 keeps the book's separation from `w`
  (`A = {w}`, `cor6_6_4`), which Chapter X derives.
- VI.3, Theorem 3.2: "Clearly, A is a Borel set" (P2:931) is kept as printed but stated separately
  (`thm6_3_2_a_borel`); (3.2) does not use it.
- App. H, H.1: harmonic measure on the double is read through App. B's charts with even reflection [reading]
  (`IsDoubleHarmonicMeasure`); cusps are excluded in Lemma H.3 [reading].
- Back-references: App. J's "Theorem II.3.3" is Theorem II.3.4 at P3:5336 (`thm2_3_4`, `thm2_3_4_bounds`) and the
  `Z*`-scale claim after it at P3:5342 (`zygmund_subset_lipschitzClass`, `lipschitzClassNorm_le_zygmundNorm`)
  [misprint]; X §5 (P3:382) "the Koebe estimate (I.2.11)" is (I.4.13) [misprint] (an `exists` pointer of Ch. I §4);
  App. K (P3:5898) "Theorem V.4.2" is Theorem VI.4.2 [misprint].
Further readings of later chapters are added with their batches.

Hypotheses added for meaning or truth (each with a `Modelling:` line): in Ch. I: `λ > 0` in (2.3) and Lemma 2.4 ((2.8)):
a positive level, for `λ < 0` the left side is `2π` and the right side negative, and `λ = 0` divides by zero;
`d > 0` in (4.5), `Ω₁ ≠ ℂ` in Corollary 4.4 and `z ≠ 0` in (4.18) (junk or meaning, each explained); in Ch. II:
`z ≠ w` in (2.2), (2.6), (2.7), Theorem 2.1 and the independence of `g` (junk at the pole), and "Ω bounded" as the
standing assumption of II.4 (`IsJordanDiscMap`; `C^{k+α}(Ω̄)` and `D^n u` need finite values); in Ch. III:
`Cap > 0` and `z ≠ w` wherever `greenFunctionLim` is read (its junk), `z ≠ w` in `greenFunction_mono`, `E` compact
in Example 1.2 (in Example 1.1 `Cap > 0` follows from the hypotheses), `E` compact in Theorem 4.5 (the standing
assumption of §4), finite measures with compact support in Corollary 4.3(b) (the junk `⊥` of `energy`), the §6
standing assumption `Cap(ℂ* ∖ Ω) > 0` in Corollary 6.2(b) and Theorem 7.1, `Cap(ℂ* ∖ Ω) > 0` in Corollary 9.3
(equivalent there to `∂Ω` having two points), `E` closed in §9 and compact in Hall's lemma (Exercise 20); in Ch. IV:
"`θ` measurable" in Theorem 6.1 (stated in (6.2) and Theorem 6.2; the book's integral needs it), `λ(z₀, E) < ∞`
repeated in Theorem 5.2(b), proved in 5.2(a), so that `λ` is read as a real number, and disjoint non-empty `E`, `F`
in the `Ω ∖ (E ∪ F)` rule (a correction); in Ch. V: `θ > 0` in (2.2), Theorem 2.1 and Corollary 2.2 and `δ > 0` in
Theorem 2.1 (a width and a non-empty square), the absolute continuity and `θ > 0` of Theorem 2.1 carried to `(a, ∞)`
in Corollary 2.2, (6.3) in the P2:156 claim and `ε₀ < 1`, `R₀ ≤ R` in Corollary 4.3 (corrections).; in the appendices:
`E`, `F` non-empty in Corollary C.4, `0 < ε ≤ b − x₀` in (G.9), `0 < b` in (G.10), `g` continuous on `[a, b]` in
(G.2), `r₀ > 0` in Theorem G.1, `0 ≤ h 0` and non-decreasing `h` in `IsMeasureFunction`, and `α ≥ 0` in (D.5) and
the `dimH` pointer (readings, each stated in its docstring); in Ch. VI:
boundedness of the Jordan domain in Theorems 1.1–1.3 (`jordanCurveLength`), `MeasurableSet E` in Theorem 3.2(b),
(c); in App. H: `ε < 1` in H.1(c), `∞ ∉ Ω` in H.4 (planar `criticalOrder`; Möbius note).

## Counts

| Chapter | new definitions | new statements | `exists` pointers | omitted | deferred |
|---|---|---|---|---|---|
| I Jordan domains (§1–§5) | 14 (+5 helpers) | 33 | 31 | 32 | 0 |
| II Finitely connected domains (§1–§4) | 30 (+10 helpers) | 49 | 3 | 20 | 0 |
| III Potential theory (§1–§9) | 24 (+8 helpers) | 75 | 5 | 36 | 0 |
| IV Extremal distance (§1–§6) | 9 (+8 helpers) | 33 | 7 | 22 | 0 |
| V Applications and reverse inequalities (§1–§6) | 16 (+8 helpers) | 36 | 4 | 35 | 0 |
| VI Simply connected domains, part one (§1–§6) | 18 (incl. helpers) | 37 | 10 | 28 | 0 |
| App. A Hardy spaces | 2 | 11 | 0 | 4 | 0 |
| App. B Mixed boundary value problems | 2 (+1 helper) | 6 | 0 | 10 | 0 |
| App. C The Dirichlet principle | 3 (+2 helpers) | 12 | 1 | 11 | 0 |
| App. D Hausdorff measure | 4 (+2 helpers) | 10 | 3 | 17 | 0 |
| App. F Martingales, Brownian motion, Kakutani | 4 | 11 | 9 | 12 | 0 |
| App. G Carleman's method | 1 | 5 | 0 | 8 | 0 |
| App. H Extremal distance in finitely connected Jordan domains | 5 (+4 helpers) | 12 | 1 | 23 | 0 |
| App. I McMillan's twist point theorem | 0 | 2 | 2 | 9 | 0 |

The shared file `References.Common.ExtPlaneBorel` (two scoped instances) was delivered with batch 1, and
`References.Common.Subharmonic` (`IsSubharmonicOn`, `IsSuperharmonicOn`, leader ruling B7) with batch 3. The `exists`
column counts the distinct names after `exists:` in the item bullets (as the gate does).
-/
