import References.FarkasKra1992.Ch01.S01_DefinitionsAndExamples
import References.FarkasKra1992.Ch01.S02_TopologyOfRiemannSurfaces
import References.FarkasKra1992.Ch01.S03_DifferentialForms
import References.FarkasKra1992.Ch01.S04_IntegrationFormulae
import References.FarkasKra1992.Ch02.S01_HilbertSpaceReview
import References.FarkasKra1992.Ch02.S02_WeylsLemma
import References.FarkasKra1992.Ch02.S03_SquareIntegrableForms
import References.FarkasKra1992.Ch02.S04_HarmonicDifferentials
import References.FarkasKra1992.Ch02.S05_MeromorphicFunctionsAndDifferentials
import References.FarkasKra1992.Ch03.S01_IntersectionTheory
import References.FarkasKra1992.Ch03.S02_HarmonicAndAnalyticDifferentials
import References.FarkasKra1992.Ch03.S03_BilinearRelations
import References.FarkasKra1992.Ch03.S04_DivisorsAndRiemannRoch
import References.FarkasKra1992.Ch03.S05_ApplicationsOfRiemannRoch
import References.FarkasKra1992.Ch03.S05b_HolomorphicQDifferentials
import References.FarkasKra1992.Ch04.S01_HarmonicFunctions
import References.FarkasKra1992.Ch04.S02_SubharmonicFunctions
import References.FarkasKra1992.Ch04.S03_Classification
import References.FarkasKra1992.Ch04.S04_SimplyConnected
import References.FarkasKra1992.Ch04.S05_Uniformization
import References.FarkasKra1992.Ch04.S06_ExceptionalSurfaces
import References.FarkasKra1992.Ch04.S07_TwoProblemsOnModuli
import References.FarkasKra1992.Ch04.S08_RiemannianMetrics
import References.FarkasKra1992.Ch04.S09_DiscontinuousGroups
import References.FarkasKra1992.Ch04.S10_RiemannRochAlternateApproach
import References.FarkasKra1992.Ch04.S10b_QCanonicalDivisors
import References.FarkasKra1992.Ch04.S11_AlgebraicFunctionFields
import References.FarkasKra1992.Ch04.S11b_ValuationsAndMorphisms
import References.FarkasKra1992.Ch05.S01_HurwitzTheorem
import References.FarkasKra1992.Ch05.S01b_WeierstrassPointsAndAutomorphisms
import References.FarkasKra1992.Ch05.S02_RepresentationsOnDifferentials
import References.FarkasKra1992.Ch05.S03_RepresentationOnHomology
import References.FarkasKra1992.Ch05.S04_ExceptionalSurfaces

/-!
# Farkas–Kra, *Riemann Surfaces* (2nd ed., 1992)

H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd edition, Graduate Texts in Mathematics 71, Springer, New York 1992.
Statement-level formalization of the in-scope chapters: genuine definitions, every result stated with a `sorry` proof;
results already in Mathlib, the project or the References are passed with an `exists:` pointer in the file's item index.

## Sources

The OCR'd text (MinerU) `full.md` of `Riemann Surfaces -- Farkas, Hershel M.;Kra, Irwi…` (FK1, Ch. 0 – IV.3.10) and
`…Kra, Irwin` (FK2, IV.3.10 – VII). Line numbers `FK1:n`, `FK2:n` in the files are sed/grep numbering.

## Coverage

Delivered so far (batches B1–B5, B4b, B6a, B7a, B7b): Chapter I §1 *Definitions and examples*, §2 *Topology of Riemann surfaces*, §3 *Differential forms*,
§4 *Integration formulae* (without the boundary-integral items), Chapter II §1 *Hilbert space theory*, §2 *Weyl's lemma*,
§3 *Square integrable forms*, §4 *Harmonic differentials*, §5 *Meromorphic functions and differentials*, Chapter IV §1 *More on harmonic functions*, §2 *Subharmonic functions and Perron's
method*, §3 *A classification of Riemann surfaces*, §4 *The uniformization theorem for simply connected surfaces*, §5 *Uniformization of arbitrary Riemann surfaces*, §6 *The exceptional Riemann
surfaces*, §7 *Two problems on moduli*, §8 *Riemannian metrics*, §9 *Discontinuous groups and branched coverings*,
§11 *Algebraic function fields in one variable* (IV.11.6–IV.11.13), and Chapter V §1 *Hurwitz's theorem* (without the items
that need Weierstrass points), §2 *Representations of the automorphism group on spaces of differentials*, §3 *Representation of Aut M on H₁(M)*, §4 *The exceptional Riemann surfaces*. One file per section, in book order. Later batches: the rest of IV.11. Out of scope: III.6–III.12, VI, VII except
VII.2 (itself omitted: it needs the theta function and the Jacobian).

**Batch B5 (Lane A).** Chapter III §1 *Intersection theory on compact surfaces*, §2 *Harmonic and analytic differentials on compact
surfaces*, §3 *Bilinear relations* (III.3.1–III.3.4; III.3.5–III.3.8, the normalized differentials of the third kind and the
reciprocity laws, are omitted for scope: they are used only by III.6–III.8). One file per section, in book order.

**Batch B6a (Lane D).** Chapter III §4 *Divisors and the Riemann–Roch theorem*, §5 *Applications of the Riemann–Roch theorem* (the
`q = 1` and gap parts; the general-`q` items are in batch B6b), Chapter IV §10 *Riemann–Roch, an alternate approach*
(IV.10.2–10.3; IV.10.1 is in batch B6b), §11.14–11.17 *Valuations and morphisms of compact surfaces* (`Ch04/S11b`), and Chapter V §1.2,
§1.7 *Weierstrass points and automorphisms* (`Ch05/S01b`, a sibling of the Hurwitz file). Dimensions `r(A)`, `i(A)` are
those of Forster's sheaf quotients `H0 (modOD M (-A))`, `H0 (modOmegaD M (-A))`.

**Batch B6b (Lane D).** The general-`q` items of Chapter III §5 (`Ch03/S05b`: §5.1 (5.1.5) `L(Z^{-q}) ≅ ℋ^q(M)`, §5.2 the dimension table of
`ℋ^q(M)`, §5.9–§5.10 `q`-Weierstrass points and their total weight) and Proposition IV.10.1 (`Ch04/S10b`: the degree of a `q`-canonical
divisor). The holomorphic `q`-differentials `IsHolQDiff`, `holQDiffSpan`, `dimHolQ` are those of `Ch02/S05` (holomorphic on every chart
target). III.5.12–III.5.13 (holomorphic de Rham cohomology) stay deferred.

## Standing conventions and their modelling

- **Riemann surfaces** are Mathlib charted spaces over `ℂ` with the binders `[TopologicalSpace M] [T2Space M]`
  `[ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]` (the shared `References.IsRiemannSurface` in existential
  positions). The book's countable basis is not assumed (FK prove it in IV.3.18 Corollary 3). `ℂ̂` is
  `References.RiemannSphere` (scoped charts, `open scoped References`); the model surfaces `Δ`, `Δ*`, `ℂ*` are the open
  subsets `Forster1981.unitDiscOpen`, `Forster1981.punctUnitDisc`, `Forster1981.punctPlane` of `ℂ`, and `U`, `ℂ` are the
  open subsets `upperHalfPlaneOpens`, `finitePlaneOpens` of `ℂ̂`.
- **Groups of Möbius transformations** are subgroups `G` of `SL(2, ℂ)` acting through `LiZhongQC.mobiusSL`; `−I` acts
  trivially, so FK's `G ⊂ PSL(2, ℂ)` is `G` modulo `±I` (orders and isomorphisms are taken through
  `toPSL : SL(2, ℂ) →* SL(2, ℂ)/center`). `Ω(G)`, `Λ(G)`, "Kleinian" and "elementary" are those of `Lehto1987`
  (`discontinuitySet G = (limitSet G)ᶜ`, `IsKleinian`, `IsElementary`); this agrees with FK's pointwise definition of
  `Ω(G)` (finite isotropy and an invariant neighbourhood with disjoint translates) for every subgroup of `SL(2, ℂ)`:
  if `z ∈ Ω_FK` and `z = lim γ_n q` with distinct `γ_n`, then `γ_m γ_n⁻¹` lies in the finite isotropy group for large `n, m`,
  a contradiction; conversely a point outside the limit set has finite isotropy (an infinite one would give
  `z = lim γ_n z`), and the convergence property of `SL(2, ℂ)` (`LiZhongQC.k22_convergence`) rules out points with no
  good neighbourhood. Möbius types are `Lehto1987`'s normal forms; the trace characterization is `para4_6_2_*`.
- **Quotients `D/G`.** The orbit space of a `G`-invariant domain is described by an orbit projection `π : D → N` onto a
  Riemann surface `N` (`IsOrbitProjection`, `IsRelProjection`): holomorphic, open, onto, fibres the orbits. This
  determines the Riemann surface `D/G`, whose structure FK obtain from III.7.7 (out of scope).
- **Surfaces of finite type, punctures, signature, characteristic** (IV.9.1): `LiZhongQC.IsFiniteType S g n 0`,
  `IsPuncture`, `HasSignature`, `signatureChar` (`1/∞ = 0`, `ν` in `ℕ∞`).
- **Genus and `Aut M`** (Ch. V): `LiZhongQC.HasGenus`, `Aut M` as biholomorphic homeomorphisms of `M`; the genus of a
  quotient is `IsQuotientGenus`; meromorphic functions of degree `n` are `Forster1981.IsHolomorphicCovering f n`.
- **Harmonic and subharmonic functions** on Riemann surfaces are the shared `References.IsHarmonicRS`, `IsSubharmonicRS`,
  `IsSuperharmonicRS`, `IsPerronFamily`, `IsGreenFunction` (`Common/RiemannSurfaceHarmonic`); FK's definition of
  subharmonicity by the maximum principle is Proposition IV.2.1. Surfaces are elliptic / parabolic / hyperbolic
  (`IsElliptic`, `IsParabolicSurface`, `IsHyperbolicSurface`).
- **Homology.** The first homology `H₁(M)` is the abelianization of `π₁(M)` (leader ruling, 2026-10-09); simplicial
  homology and triangulations are deferred (W-TOP).
- **Chapter III (compact surfaces).** Cycles are classes `a ∈ H₁(M) = Abelianization(π₁(M, x₀))`, written multiplicatively; the
  period `∫_a α` of a closed smooth form is `IsPeriodOf α a v` (the relation `Forster1981.period` of any representing loop).
  The form `η_a` of a cycle is characterized by (1.1.1), `∫_c α = −∬_M α ∧ η_c` (`IsAssociatedForm`), and the intersection
  number `a · b = ∬_M η_a ∧ η_b` is the relation `IsIntersectionNumber`. A canonical homology basis is a `ℤ`-basis
  `{a_j, b_j}` of `H₁` with `a_j · b_k = δ_{jk}`, `a_j · a_k = 0 = b_j · b_k` (`IsCanonicalHomologyBasis`; matrix
  `symplecticJ = [[0, I], [−I, 0]]`). The genus is the topological genus `LiZhongQC.HasGenus` (near miss
  `Forster1981.genus = dim H¹(M, 𝒪)`). Harmonic differentials are complex valued (`dim_ℂ H = 2g`); the inner product is
  `HasL2Inner`, `(ω₁, ω₂) = ∬ ω₁ ∧ *ω̄₂`; holomorphic differentials are `Forster1981.IsAbelianDiff1` and the three kinds are
  `Forster1981.IsAbelianDiff1/2/3`. Orientation: `∬ f dx ∧ dy = ∬ f dx dy` and `*dz = −i dz`; with these the matrix
  statements below hold with `J = [[0, I], [−I, 0]]` (checked on the torus `ℂ/(ℤ + τℤ)`, where `(dz, dz) = 2 Im τ`).

## Corrections and readings

- IV.9.2 (iv) [reading]: the side-pairing element `g` is not the identity (with `g = 1` the printed condition is
  vacuous).
- IV.9.10 Corollary 1 [reading]: punctures correspond to the `G`-orbits of parabolic fixed points (conjugacy classes of
  parabolic *subgroups*), not to conjugacy classes of parabolic elements (all powers of a generator are parabolic).
- IV.9.11 Corollary [reading]: `D` is an invariant component of `Ω(G)` (for `G = 1`, `D = ℂ` the characteristic is `−1`
  because of the puncture at `∞`, so the printed trichotomy needs this).
- IV.9.12 [CORRECTION]: the characteristic statement is for compact `M` with finitely many points (for non-compact `M`
  the punctures of `M` are not in the data), and the excluded cases for `M = ℂ̂` must include one point with
  `ν = ∞` (then `M' = ℂ`, `M̃ = ℂ`, `χ = −1`).
- IV.3.3 Theorem and Corollaries, IV.3.4, IV.3.5 [reading]: `δD ≠ ∅` (resp. `K ≠ ∅`) is added; for `D = M` two constants are bounded
  solutions, and for `K = ∅` the proof of IV.3.4 takes a minimum over `∅`.
- V.1.11 [misprint]: "genus `g ≤ 2`" is read `g ≥ 2`.

## Counts

| Chapter | new definitions (book notions; helpers in parentheses) | new statements | `exists` bullets |
|---|---|---|---|
| I §1 Definitions and examples | 0 (+0) | 1 | 7 |
| I §2 Topology of Riemann surfaces | 1 (+0) | 6 | 5 |
| I §3 Differential forms | 5 (+1) | 8 | 6 |
| I §4 Integration formulae | 3 (+1) | 1 | 0 |
| II §1 Hilbert space theory (review) | 0 (+0) | 0 | 3 |
| II §2 Weyl's lemma | 0 (+0) | 1 | 1 |
| II §3 Square integrable forms | 6 (+2) | 15 | 0 |
| II §4 Harmonic differentials | 0 (+1) | 5 | 0 |
| II §5 Meromorphic functions and differentials | 5 (+1) | 3 | 4 |
| IV §1 More on harmonic functions | 1 (+0) | 8 | 0 |
| IV §2 Subharmonic functions and Perron's method | 5 (+0) | 11 | 2 |
| IV §3 A classification of Riemann surfaces | 4 (+4) | 19 | 2 |
| IV §4 Uniformization of simply connected surfaces | 1 (+0) | 10 | 0 |
| IV §5 Uniformization of arbitrary Riemann surfaces | 6 (+7) | 12 | 3 |
| IV §6 The exceptional Riemann surfaces | 1 (+2) | 21 | 1 |
| IV §7 Two problems on moduli | 0 (+1) | 3 | 1 |
| IV §8 Riemannian metrics | 2 (+0) | 5 | 3 |
| IV §9 Discontinuous groups and branched coverings | 8 (+5) | 22 | 1 |
| IV §11 Algebraic function fields (IV.11.6–11.13) | 2 (+2) | 5 | 1 |
| V §1 Hurwitz's theorem | 2 (+1) | 20 | 2 |
| V §2 Representations on spaces of differentials | 4 (+5) | 23 | 1 |
| V §3 Representation of Aut M on H₁(M) | 2 (+2) | 12 | 0 |
| V §4 The exceptional Riemann surfaces | 1 (+0) | 4 | 1 |
| III §1 Intersection theory on compact surfaces | 3 (+1) | 6 | 0 |
| III §2 Harmonic and analytic differentials on compact surfaces | 1 (+2) | 11 | 0 |
| III §3 Bilinear relations (III.3.1–III.3.4) | 0 (+0) | 7 | 1 |
| III §4 Divisors and the Riemann–Roch theorem | 7 (+0) | 11 | 3 |
| III §5 Applications of the Riemann–Roch theorem | 5 (+0) | 15 | 2 |
| IV §10 Riemann–Roch, an alternate approach | 0 (+0) | 1 | 1 |
| IV §11.14–11.17 Valuations and morphisms | 3 (+0) | 6 | 0 |
| V §1.2, §1.7 Weierstrass points and automorphisms | 0 (+0) | 3 | 0 |
| III §5 (general `q`: `q`-Weierstrass points) | 1 (+0) | 6 | 2 |
| IV §10.1 `q`-canonical divisors | 1 (+0) | 1 | 0 |
-/
