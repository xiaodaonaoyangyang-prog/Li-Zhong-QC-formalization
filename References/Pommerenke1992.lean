import References.Pommerenke1992.Ch01.S01_SetsAndCurves
import References.Pommerenke1992.Ch01.S02_ConformalMaps
import References.Pommerenke1992.Ch01.S03_KoebeDistortionTheorem
import References.Pommerenke1992.Ch01.S04_SequencesOfConformalMaps
import References.Pommerenke1992.Ch01.S05_SomeUnivalenceCriteria
import References.Pommerenke1992.Ch02.S01_Overview
import References.Pommerenke1992.Ch02.S02_LocalConnection
import References.Pommerenke1992.Ch02.S03_CutPointsAndJordanDomains
import References.Pommerenke1992.Ch02.S04_CrosscutsAndPrimeEnds
import References.Pommerenke1992.Ch02.S05_LimitsAndClusterSets
import References.Pommerenke1992.Ch02.S06_CountabilityTheorems
import References.Pommerenke1992.Ch03.S01_Introduction
import References.Pommerenke1992.Ch03.S02_SmoothJordanCurves
import References.Pommerenke1992.Ch03.S03_ContinuityOfTheDerivatives
import References.Pommerenke1992.Ch03.S04_TangentsAndCorners
import References.Pommerenke1992.Ch03.S05_RegulatedDomains
import References.Pommerenke1992.Ch03.S06_StarlikeAndCloseToConvexDomains
import References.Pommerenke1992.Ch04.S01_Overview
import References.Pommerenke1992.Ch04.S02_BlochFunctions
import References.Pommerenke1992.Ch04.S03_AngularDerivative
import References.Pommerenke1992.Ch04.S04_HarmonicMeasure
import References.Pommerenke1992.Ch04.S05_LengthDistortion
import References.Pommerenke1992.Ch04.S06_HyperbolicMetric
import References.Pommerenke1992.Ch05.S01_Overview
import References.Pommerenke1992.Ch05.S02_JohnDomains
import References.Pommerenke1992.Ch05.S03_LinearlyConnectedDomains
import References.Pommerenke1992.Ch05.S04_QuasidisksAndQuasisymmetricFunctions
import References.Pommerenke1992.Ch05.S05_QuasiconformalExtension
import References.Pommerenke1992.Ch05.S06_AnalyticFamiliesOfInjections
import References.Pommerenke1992.Ch06.S01_Overview
import References.Pommerenke1992.Ch06.S02_LinearMeasureAndMeasurability
import References.Pommerenke1992.Ch06.S03_RectifiableCurves
import References.Pommerenke1992.Ch06.S04_PlessnersTheoremAndTwisting
import References.Pommerenke1992.Ch06.S05_SectorialAccessibility
import References.Pommerenke1992.Ch06.S06_JordanCurvesAndHarmonicMeasure
import References.Pommerenke1992.Ch07.S01_Overview
import References.Pommerenke1992.Ch07.S02_IntegralsOfBlochFunctions
import References.Pommerenke1992.Ch07.S03_SmirnovDomainsAndAhlforsRegularity
import References.Pommerenke1992.Ch07.S04_LavrentievDomains
import References.Pommerenke1992.Ch07.S05_MuckenhouptConditionsAndBMOA
import References.Pommerenke1992.Ch08.S01_Overview
import References.Pommerenke1992.Ch08.S02_UnivalentFunctions
import References.Pommerenke1992.Ch08.S03_DerivativesOfUnivalentFunctions
import References.Pommerenke1992.Ch08.S04_CoefficientProblems
import References.Pommerenke1992.Ch08.S05_GrowthOfBlochFunctions
import References.Pommerenke1992.Ch08.S06_LacunarySeries
import References.Pommerenke1992.Ch09.S01_Overview
import References.Pommerenke1992.Ch09.S02_ModuleOfACurveFamily
import References.Pommerenke1992.Ch09.S03_CapacityAndGreensFunction
import References.Pommerenke1992.Ch09.S04_PflugersTheorem
import References.Pommerenke1992.Ch09.S05_ApplicationsToConformalMapping
import References.Pommerenke1992.Ch10.S01_Overview
import References.Pommerenke1992.Ch10.S02_HausdorffMeasures
import References.Pommerenke1992.Ch10.S03_LowerBoundsForCompression
import References.Pommerenke1992.Ch10.S04_ZygmundMeasuresAndTheAngularDerivative
import References.Pommerenke1992.Ch10.S05_SizeOfTheBoundary
import References.Pommerenke1992.Ch11.S01_Overview
import References.Pommerenke1992.Ch11.S02_AsymptoticallyConformalCurvesAndB0
import References.Pommerenke1992.Ch11.S03_VisserOstrowskiQuotient
import References.Pommerenke1992.Ch11.S04_ModuleAndConformality
import References.Pommerenke1992.Ch11.S05_AhlforsIntegral

/-!
# Pommerenke, *Boundary Behaviour of Conformal Maps* (1992)

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Grundlehren der mathematischen Wissenschaften 299,
Springer-Verlag, Berlin–Heidelberg 1992. Statement-level formalization: genuine definitions, every result of the book
stated with a `sorry` proof; results already in the project, in Mathlib or in the References are passed with an
`exists:` pointer in the file's item index.

## Sources

The OCR'd text (MinerU) in `D:\lean\lizhong_thm21_archive\refs\`:
- `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f-…\full.md` (P1, 8119 lines) — front
  matter, Ch. 1 – Ch. 8 §8.5;
- `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3-…\full.md` (P2, 5732 lines) — Ch. 8
  §8.5 – Ch. 11, references, index.

Line numbers `l.` in the files refer to P1 unless marked "P2" (§8.5–§8.6 and Chapters 9–11, whose files use P2
throughout).

## Coverage

Delivered so far: Chapter 1 *Some Basic Facts* (§1.1–§1.5), Chapter 2 *Continuity and Prime Ends* (§2.1–§2.6),
Chapter 3 *Smoothness and Corners* (§3.1–§3.6), Chapter 4 *Distortion* (§4.1–§4.6), Chapter 5 *Quasidisks*
(§5.1–§5.6), Chapter 6 *Linear Measure* (§6.1–§6.6), Chapter 7 *Smirnov and Lavrentiev Domains* (§7.1–§7.5),
Chapter 8 *Integral Means* (§8.1–§8.6), Chapter 9 *Curve Families and Capacity* (§9.1–§9.5), Chapter 10 *Hausdorff
Measure* (§10.1–§10.5) and Chapter 11 *Local Boundary Behaviour* (§11.1–§11.5): the whole book, one file per section.
The OCR lost the headings of Chapters 1, 2 and 6–11 (not their text); the titles are those of the table of contents.
A library due-date slip was scanned over the left column of p. 247 (P2 l. 2774–2802, inside the proof of Theorem 11.1
(i) ⇒ (ii)); no statement is affected. Exercises are not items.

**Import order.** The files follow the numbering, with three exceptions of the same kind: `Ch02/S01_Overview`
states the three named theorems of §2.1 (Continuity, Carathéodory, Prime End Theorem) with the notions of §2.2–§2.5,
so it imports the files of §2.3 and §2.5; `Ch04/S01_Overview` states the Lehto–Virtanen theorem and the Julia–Wolff
lemma with the notions of §4.2–§4.3, so it imports the file of §4.3; `Ch06/S01_Overview` states the
Kolmogoroff–Verčenko theorem and points to the named theorems of §6.3–§6.5, so it imports the file of §6.6;
`Ch09/S01_Overview` points to Pfluger's theorem (§9.4) and imports the file of §9.4; `Ch10/S01_Overview` states the
Anderson–Pitt theorem and points to the Makarov dimension theorem (§10.3), so it imports the file of §10.3. No file
imports these five overviews. The overviews `Ch05/S01_Overview`, `Ch07/S01_Overview`, `Ch08/S01_Overview` and
`Ch11/S01_Overview` import no later file and are imported by the next file of their chapter; the last three hold only
a module docstring (the overviews of Chapters 7, 8 and 11 state no item of their own). Hence the import graph stays
acyclic.

## Standing conventions and their modelling

- **Spaces.** The Riemann sphere `Ĉ` is `LiZhongQC.ExtPlane`. §2.2–§2.3 work with bounded domains of `ℂ`, §2.1 and
  §2.4–§2.6 with (simply connected) domains of `Ĉ`; each statement carries the standing assumption of its section.
- **Conformal maps.** "`f` maps `𝔻` conformally into `ℂ`" is `DifferentiableOn ℂ f 𝔻 ∧ InjOn f 𝔻`; "onto a bounded
  `G ⊆ ℂ`" is the project's `LiZhongQC.IsConformalOnto f unitDisc G`; "onto `G ⊆ Ĉ`" is
  `LehtoVirtanen1973.IsConformalMap f (toExt 𝔻)` with `f '' toExt 𝔻 = G`.
- **Metrics.** The book's spherical metric is the chordal `d#` (`chordalDist`, `chordalDiam`), which is not a constant
  multiple of Lehto–Virtanen's `sphericalDist`. The non-euclidean metric is `λ` (`hypDistD`, curvature `-4`), half the
  project's disc distance; the constants of Corollary 1.5 depend on this normalization.
- **Curves.** A curve is a parametrized object (`Curve`, `HalfOpenCurve`); lengths are `eVariationOn`. An open Jordan
  arc is continuous and injective, not necessarily an embedding (`IsOpenJordanArcP`). A crosscut (`IsCrosscut`) is an
  open Jordan arc whose two ends converge to its end points on `∂G`. The curve classes of Chapter 3 (smooth,
  Dini-smooth, `C^n`, `C^{n,α}`, `C^∞`) are given by `2π`-periodic parametrizations (`IsPeriodicParam`).
- **Local connection** is Pommerenke's ε–δ definition by continua (`IsLocConn`, and `IsLocConnSph` with `d#`); it
  differs from topological local connectedness for the non-compact sets of Theorem 2.1 (iv).
- **Prime ends** are sets of null-chains (the equivalence classes of `NullChainEquiv`), not a quotient type; the
  correspondence of Theorem 2.15 is the helper predicate `IsPrimeEndCorrespondence`, used by §2.5–§2.6 and §3.6.
- **Cluster sets** are defined by sequences, for `f : ℂ → Ĉ` on `𝔻`, as in (2.5.2).
- **Angles** (Chapter 3). Limits of `arg` are limits of directions `w/|w|`; where the value of an angle matters (the
  opening of a corner, the jumps of a forward tangent, the argument of a starlike function), it is read through a
  continuous branch of the argument. `(z - e^{iϑ})^α` is the branch (3.4.2) (`logAt`, `powAt`). The forward tangent
  `β` of a regulated domain is the book's lift: (3.5.4) fixes its values only modulo `2π` (`IsRegulatedForMod`), and
  `IsRegulatedFor` adds the normalization by the jumps (3.5.5), (3.5.6) and `β(t) = β(t+)`. The Stieltjes
  integrals are Riemann–Stieltjes integrals (`HasRSIntegral`). The Poisson kernel is Mathlib's `poissonKernel` with the
  factor `1/(2π)` written in the statements.
- **Distortion** (Chapter 4). The Bloch seminorm is `ℝ≥0∞`-valued (`blochSeminorm`). Arcs of `𝕋` are closed parameter
  arcs `arcT t₁ t₂`; the harmonic measure `ω(z, A)` of `A ⊆ 𝕋` is (4.4.1) with the arc length `Λ(A)` of the parameter
  set; "measurable" is Borel measurable. Notions defined through a conformal map `f` of `𝔻` onto `G` and independent of
  `f` (`ω(z, A, G)`, `λ_G`) are the supremum of the one-point set of their values (the pattern of
  `Gehring1978.hypDensity`), with the independence as an unlabelled item. The constants `K₁, K₂, …` of §4.5 are
  absolute (`∃ K, ∀ f`). The hyperbolic density is `Gehring1978.hypDensity`; the quasihyperbolic metric is the
  project's `metricDist` for the density `1/dist(w, ∂G)`.
- **Quasidisks** (Chapter 5). A quasicircle (5.4.1) is the project's bounded turning (`LiZhongQC.IsBoundedTurning`,
  reused under the book's name), and (a) ⟺ (d) of the Quasicircle Theorem is, in its Möbius-normalized form, the
  project's proved `LiZhongQC.thm18_1`. Quasidisks and quasisymmetric maps are the book's own definitions (Ahlfors'
  (5.1.1) and Väisälä's (5.4.4); the leader's decision Q4); the equivalence of the two quasisymmetry definitions is
  an unlabelled item. `κ`-quasiconformal maps of `ℂ` onto `ℂ` are the book's analytic
  definition (5.1.2), (5.1.3) on the project's `LiZhongQC.IsGenHomeoSolution` and `LiZhongQC.IsBeltramiCoeff` (Q3);
  quasiconformal maps of `Ĉ` onto `Ĉ` not fixing `∞` (Theorems 5.16, 5.17) are
  `LehtoVirtanen1973.IsQuasiconformalMap F univ`. Theorem 5.2 is a cycle of implications with uniform constants (Q6).
  The Douady–Earle extension picks the zero of `F_φ(z, ·)` by `Classical.epsilon`; its meaning rests on Lemma 5.20,
  and every statement using it assumes a sense-preserving homeomorphism of `𝕋` (Q8). The extensions of Theorems 5.16
  and 5.17 are operators `E` with the Möbius naturality as a property of `E`.
- **Linear measure** (Chapter 6). The linear measure `Λ` of plane sets is Mathlib's `μH[1]` ((6.2.7), no normalizing
  factor); on `𝕋` it is the arc length `circleMeasure` of Chapter 4, the two being identified by the unlabelled item
  `linearMeasure_eq_lebesgue`. "Measurable" is linear measurability (`IsLinearlyMeasurable`, Carathéodory
  measurability for `μH[1]`; Proposition 6.7(b) is false for Borel measurability). The book's `f(A)` and `f⁻¹(B)` are
  the sets of radial limits (`radialImage`, `radialPreimage`); "σ-finite linear measure" is
  `SigmaFinite ((μH[1] : Measure ℂ).restrict E)`, as in Lehto–Virtanen; a rectifiable Jordan curve is
  `LehtoVirtanen1973.IsRectifiableJordanCurve`; `H¹` is `GarnettMarshall2005.MemHardy 1`.
  `Sect(f)` is the literal definition of §6.5 (`sect`). The harmonic measures `ω`, `ω*` of §6.6 are the literal
  (6.6.1) (`boundaryHarmonicMeasure`) in the Jordan setting `IsJordanSetting` (the maps of `𝔻` onto the inner and
  of `𝔻*` onto the outer domain, with their extensions); meromorphic functions are read through their germs
  (`meroToExt`), so that junk values at poles do not count.
- **Smirnov and Lavrentiev domains** (Chapter 7). The boundary values `f'(ζ)` are the angular limits, carried by a
  boundary function (`IsAngularBoundaryFun`) that is determined almost everywhere. Means over arcs are `ℝ≥0∞`-averages
  over the parameter interval, with `ℝ≥0∞`-powers for the book's conventions `0^{-a} = ∞`, `∞^{-a} = 0`; the arc
  `I(z)` is `arcI` (Chapter 5). The Poisson and Herglotz kernels are Mathlib's `poissonKernel` and
  `herglotzRieszKernel`; singular measures are mutually singular with `GarnettMarshall2005.arcMeasure`; `Hᵖ` is
  `GarnettMarshall2005.MemHardy (ENNReal.ofReal p)` and `g*` is `GarnettMarshall2005.boundaryConjugate`. The `(A∞)`
  condition carries the nondegeneracy of the book's weights (`0 < φ < ∞` almost everywhere, `log φ` integrable on
  arcs), without which the equivalences (i)–(v) fail. The standing assumption of §7.3, `Λ(∂G) < ∞` (l. 6770), is an
  explicit hypothesis of every §7.3 statement, Theorem 7.6 included (the upper half-plane, an Ahlfors-regular domain
  with `Λ(∂G) = ∞`, shows that it cannot be dropped there).
- **Integral means** (Chapter 8). `∫₀^{2π} |g(re^{it})|^p dt` is `2 * π * Real.circleAverage (fun z => ‖g z‖ ^ p) 0 r`,
  and the book's `(1/2π)∫` is the circle average itself; the constants that depend on this normalization are stated as
  printed. `β_f(p)` (`integralMeansSpectrum`) and every other `limsup` are taken in `EReal`. The class `S` is
  `LiZhongQC.knHyp`; "`K(p)` depending only on `p`" is `∀ p, ∃ K, ∀ f`, and "for small `|p|`" is `∃ δ > 0`. A series
  with Hadamard gaps exposes its data (`IsHadamardGapSeries g q b n`), and every statement is invariant under the
  choice of the data.
- **Curve families and capacity** (Chapter 9). The module of a curve family is
  `LehtoVirtanen1973.arcFamilyModule` (the same normalization); curve families are families of point sets (Jordan
  arcs and curves) in `Ĉ`. Capacity is Garnett–Marshall's (`GarnettMarshall2005.capacityCompact` for compact sets,
  `GarnettMarshall2005.capacity`, the inner capacity, for arbitrary sets); Pommerenke's definition by the transfinite
  diameter (9.3.7) is the stated Fekete–Szegő equality `eq9_3_7`, and his Fekete quantities (`feketeDelta`,
  `IsFeketeSystem`, `feketePoly`, `feketeGamma`) are defined literally. The outer domain is
  `GarnettMarshall2005.unboundedComponentExt`; the Green function with pole at `∞` and the equilibrium measure are
  Pommerenke's (`greenFnInf`, `IsEquilibriumMeasure`), through GM's logarithmic potential.
- **Hausdorff measure** (Chapter 10). `Λ_α` is Mathlib's `μH[α]`; `Λ_φ` is `hausdorffMeasureGauge φ`
  (`Measure.mkMetric` of the gauge), the content `Λ′_φ` is `hausdorffContent φ`; the dimension is `dimH`; `N(ε, E)`
  is Mathlib's covering number at radius `ε/2` and the Minkowski dimension is `minkowskiDim`. Statements about the
  gauges (10.3.1), (10.4.1) hold for every gauge equal to them near `0`.
- **Local boundary behaviour** (Chapter 11). Asymptotically conformal curves are `IsAsymptoticallyConformalCurve`
  (not `AstalaGehring1990.IsAsymptoticallyConformal`, a notion for quasiconformal maps); circular crosscut systems,
  their separating families and the Ahlfors integrals are written with `μH[1]` of the crosscuts and lower integrals.
- Numbered formulas and unlabelled claims stated outside proofs and cited later are items (bullets "Formula (x.y.z)",
  "Unlabelled (§n, l. …)"); facts used only inside proofs, remarks, examples and quoted results not cited are listed as
  "Not items" in each file.

## Corrections

Each marked in the declaration's docstring:
- Proposition 2.13 [CORRECTION]: the hypothesis `J ∩ ∂G ≠ ∅` is added. As printed (`G ∩ J ≠ ∅` only) the statement
  is false for a Jordan curve `J ⊆ G`; the proof and the uses of the proposition have `J` meeting `∂G`.
- Crosscuts: the book's `C̄ = C ∪ {a, b}` is read with `a, b` the limits of the two ends of the arc (`IsCrosscut`).
  Read literally for an injective arc that is not an embedding, it admits a "figure 6", for which Proposition 2.12
  fails.
- Kellogg–Warschawski theorem (§3.1) and its restatement at l. 2141 (`thm3_6_cinfty`) [CORRECTION]: the converse
  needs `f' ≠ 0` on `𝔻̄` as well; `f(z) = z - z²/2` has continuous derivatives of all orders but a cusp at `f(1)`.
- Theorem 3.11, the case `α = 1` [CORRECTION]: the sign of `b₂` in (3.4.22) is corrected to
  `b₂ = -e^{-iβ} b₁² (κ^+ - κ^-)/(2π)` (checked on `f(z) = z + ic(z - 1)² log(z - 1)` and against (3.4.14), (3.4.21)).
- Formula (6.3.6) [CORRECTION]: "`g(ζ) ≠ 0` for almost all `ζ`" is stated for `g ≢ 0`.
- Lemma 6.19 [misprint]: `d_f(ζ)` is read `d_f(z)`; Theorem 6.30 [misprint]: `w*(B*)` is read `ω*(B*)` (both
  confirmed by the page images).
- Proposition 7.3 [CORRECTION]: `μ ≠ 0` is added (the zero measure is a Zygmund measure and gives `Re g = 0`).
- Formula (7.4.3) [CORRECTION]: stated for `f' ∈ H¹`; it is false for some conformal maps onto quasidisks.
- Hardy's identity (8.2.2) [CORRECTION]: stated when `g` has no zeros on the circle or `p` is an even integer `≥ 2`
  (at a zero on the circle and `p ≤ 1` the right-hand side diverges).
- Formula (8.2.10), the case `q > 1` [CORRECTION]: the constant is `2^{-1}π^{-1/2}Γ((q-1)/2)Γ(q/2)^{-1}` (the book
  prints `Γ(q/2)`).
- Proposition 9.6, (9.3.13) [CORRECTION]: the second equality needs `E` infinite (`E = {0, 1}`, `n ≥ 3`).
- Theorem 9.12 [CORRECTION]: `cap E < ∞` (the strict "`< cap E + ε`" fails at `cap E = ∞`, e.g. `E = ℝ`).
- Theorem 9.24 [CORRECTION]: the inequality `Λ(E) ≤ 2π cap E` needs `E` Borel (a Bernstein set in `𝕋`).
- (11.2.1) [misprint?] `|a, b| → 0` is read `|a - b| → 0`; Theorem 11.1 (iii) [CORRECTION] excludes `ζ = z` and
  reads "(a > 0)" as "for every `a > 0`"; (11.4.11) [CORRECTION] excludes `w = ω`; (11.4.14) [CORRECTION] `δ_n ≥ 0`;
  Theorem 11.16 [CORRECTION] with a fixed `c₀ < c`.
- Corollary 11.11, second part [CORRECTION]: (11.4.19) is concluded near `0` only (it can diverge at `ρ₀`).
- Theorem 11.10 [CORRECTION]: (iii) carries the side condition `Σ ((ρ_n − ρ_{n+1})/ρ_n)² < ∞` of (ii) (it fails for
  sparse `ρ_n`); Theorem 11.10 and Corollary 11.11, first part [CORRECTION]: `ζ` is the prime end reached along the
  radius towards `ω` (a spiralling slit gives a second prime end over `ω`).
- OCR: Corollary 2.19, "as `ρ → 1-`" read as `r → 1-`; (3.3.1) "`δ ≤ 0`" read as `δ ≥ 0`; (3.4.1)
  "`0 ≤ α ≤ 2π`" read as `0 ≤ α ≤ 2`.

## Counts

Items of the book; helper definitions in parentheses; U+ = unlabelled claims kept as items.

| Chapter | new definitions | new statements | `exists` items | not items (listed per file) | deferred |
|---|---|---|---|---|---|
| 1 Some Basic Facts (§1.1–§1.5) | 27 | 31 (2 U+) | 20 | 25 | 0 |
| 2 Continuity and Prime Ends (§2.1–§2.6) | 25 (+2) | 36 (7 U+) | 5 | 27 | 0 |
| 3 Smoothness and Corners (§3.1–§3.6) | 25 (+7) | 50 (8 U+) | 5 | 23 | 0 |
| 4 Distortion (§4.1–§4.6) | 17 (+5) | 45 (3 U+) | 3 | 31 | 0 |
| 5 Quasidisks (§5.1–§5.6) | 17 (+4) | 43 (7 U+) | 2 | 34 | 0 |
| 6 Linear Measure (§6.1–§6.6) | 13 (+5) | 48 (11 U+) | 18 | 42 | 0 |
| 7 Smirnov and Lavrentiev Domains (§7.1–§7.5) | 14 (+3) | 24 (9 U+) | 4 | 24 | 0 |
| 8 Integral Means (§8.1–§8.6) | 7 (+2) | 40 (16 U+) | 6 | 42 | 0 |
| 9 Curve Families and Capacity (§9.1–§9.5) | 8 (+4) | 49 (15 U+) | 11 | 53 | 0 |
| 10 Hausdorff Measure (§10.1–§10.5) | 5 (+2) | 30 (5 U+) | 11 | 54 | 0 |
| 11 Local Boundary Behaviour (§11.1–§11.5) | 8 (+5) | 24 (6 U+) | 5 | 52 | 0 |
| total | 166 (+39) | 420 (89 U+) | 90 | 407 | 0 |
-/
