import References.Nag1988.Ch02.S01_TeichmullerSpaceAndReducedSpace
import References.Nag1988.Ch02.S03_AllowableBijectionsAndModularGroup
import References.Nag1988.Ch02.S04_OrbitSpace
import References.Nag1988.Ch02.S05_FrickeCoordinatesFiniteType
import References.Nag1988.Ch02.S07_DiscontinuityOfModularGroup
import References.Nag1988.Ch02.S08_IntermediateModuliSpaces
import References.Nag1988.Ch03.S02_ComplexStructuresOnTargetSpaces
import References.Nag1988.Ch03.S03_BersEmbeddingOfArbitraryTG
import References.Nag1988.Ch03.S05_ProofOfSubmersivityOfBersProjection
import References.Nag1988.Ch03.S06_RecapitulationAndRationale
import References.Nag1988.Ch04.S01_PeriodMap
import References.Nag1988.Ch04.S02_QuasiconformalDeformations
import References.Nag1988.Ch04.S03_SchifferVariation
import References.Nag1988.Ch04.S04_SchwarzianAndDeformations
import References.Nag1988.Ch04.S05_BersBoundary
import References.Nag1988.Ch04.S06_ComplexAnalyticParameters
import References.Nag1988.Ch05.S01_BersFiberSpace
import References.Nag1988.Ch05.S02_UniversalFamily
import References.Nag1988.Ch05.S03_BersIsomorphism
import References.Nag1988.Ch05.S04_UniversalProperty

/-!
# Nag, *The Complex Analytic Theory of Teichmüller Spaces* (1988)

S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Canadian Mathematical Society Series of Monographs and
Advanced Texts, Wiley, New York 1988. Statement-level formalization: genuine definitions, every result stated with a `sorry`
proof; results already in Mathlib, the project or the References are passed with an `exists:` pointer in the file's item
index.

## Sources

The Mathpix text `full.md` of `The Complex Analytic Theory of Teichmuller Spaces … c10f6cd1` (cited `N2:<line>`), Chapter 5
§5.1–§5.4 (`N2:4356–6023`). The other two OCR folders (`10dae1e9`, `2f58d419`) and the other sections of Chapter 5 are not
formalized in this delivery; for them see the section-level concordance in `refs_lean/Nag1988/INVENTORY.md` §9.

**Batch N1a (W2, Lane A).** Chapter 2 *The Moduli Spaces for Riemann Surfaces*, new items only (`Ch02/`, one file per section that
has new items; the other items are passed with `exists:` pointers in the file docstrings): §2.1 reduced and Riemann moduli
spaces, the quotient pseudometric (Lemma 2.1.6), §2.3.10 isometries between Teichmüller spaces, §2.4 `T(X)` as an orbit space,
§2.5.5–§2.5.7 Fricke coordinates for finite type, §2.7.1 discreteness of the quasiconformal mapping class group, §2.8.1 orbit
spaces of free properly discontinuous actions. Later batches: Chapter 3 (N1b), Chapter 4 (N2, N3). The Chapter 2 sources are
the folder `10dae1e9` (`N1:<line>`); Chapters 3–4 are in `10dae1e9` (to §3.2) and `c10f6cd1`.

**Batch N2 (W2, Lane B).** Chapter 4 *Teichmüller spaces and the period map*, §4.1–§4.3 (`Ch04/`, source `c10f6cd1`, `N2:<line>`):
§4.1 the period map and the Torelli theorem (Torelli 4.1.2, the real-analytic Beltrami representatives 4.1.4, the period map
of `T(g, 0)` and its derivative 4.1.5, Rauch's formula 4.1.6; 4.1.3 and the Riemann bilinear relations are `exists:` pointers
to `FarkasKra1992`), §4.2 quasiconformal deformations `Def(G)` (Lemma 4.2.1, Proposition 4.2.2, Theorem 4.2.3 on the `6g − 6`
real coordinates, the formula of 4.2.4), §4.3 Schiffer variation (Theorem 4.3.2 A and C, the claim of 4.3.4, Proposition
4.3.5, Theorem 4.3.6).

## Coverage

Delivered (batch D1): Chapter 5 §5.1 *The Bers fiber space* (`Ch05/S01`), §5.2 *The universal family* (`Ch05/S02`),
§5.3.1–§5.3.4 *Puncture-forgetting fiber spaces, Bers' isomorphism theorem, principal bundles* (`Ch05/S03`), §5.4.1–§5.4.5
*Marked families and the universal property* (`Ch05/S04`). Deferred (listed one per line in the item indices):
§5.3.5–§5.3.10 and §5.4.6–§5.4.8 (they need the `C^∞`/Hölder topology on diffeomorphism groups, projective structures, or the
Earle–Fowler theory), the items resting on normal complex spaces (2.12, Corollary 5.2.5, the universal curves over moduli
spaces), on complex submanifolds of `ℙ² × ℂ*` (Examples 5.4.4, Fact 5.4.3), on the type of a group with torsion
(Earle–Kra), and on the identification `T(G) ≅ T(g,n)` (Proposition 5.2.4 (c)), Corollary 5.3.2 (c). Gottschling's theorem
(quoted inside a proof) is omitted.

**Batch N3 (W2, worker 下属3).** Chapter 4 §4.4–§4.6, new items only (the other items are passed with `exists:` pointers or omitted with a reason in the
file docstrings): the deformations of a Fuchsian group and their Schwarzians, the description of `T(G)`, Theorem S and Theorem K, holomorphy in
`φ` of the solutions of `2y'' + φy = 0` (`Ch04/S04`); the Bers boundary: boundary groups are Kleinian, cusps, totally degenerate groups, the
category theorem, the extension of modular elements as isometries (`Ch04/S05`); once-punctured torus coordinates, Lamé's equation for
`T_β(1, 1)` through Mathlib's Weierstrass `℘`, and the coordinates of `T(0, 5) ≅ T(1, 2)` (`Ch04/S06`). Sections 4.4.4–4.4.6 (projective structures)
are omitted; the clauses on topological dimension (Theorem 4.5.3, Proposition A) and the identifications with the fundamental projection (Theorem 4.6.3) and
with the canonical isometry `T(1, 2) → T(0, 5)` (Corollary 4.6.7) are not stated (named in the file docstrings).

**Batch N1b (W2, Lane A).** Chapter 3 *The Complex Structure of Teichmüller Spaces*, new items only (`Ch03/`): §3.2 complex structures on
target spaces (Lemma 3.2.1, Theorem 3.2.2 on submersions, the complex structure of the Fricke image, Bers local coordinates), §3.3
Proposition 3.3.2 (Bers and Fricke structures coincide), §3.5 the operators `ℒ_C` and Bers' main theorem, §3.6.3 finite dimension of `T(G)`.
The other items of Chapter 3 are passed with `exists:` pointers in the file docstrings (§3.1, §3.3.1, §3.3.3–3.3.6, §3.4, §3.7, §3.8);
§3.9 (Earle's embedding of the reduced space, Proposition 3.9.3) is not formalized: it needs the universal covering of the region of
discontinuity of a Fuchsian group of the second kind and a real-analytic Banach structure on `B^#(G)`, neither of which is modelled.
Chapter 3 sources: folders `10dae1e9` (to §3.2) and `c10f6cd1` (`N2:<line>`).

Batch N2 (Chapter 4 §4.1–§4.3): delivered as above. Deferred (one per line in the item indices): Theorem 4.3.2 B (prescribed
disk boundaries), Theorem 4.3.3 (reduced Teichmüller space, doubles), the formula (3.12) of 4.3.5, the complex diagonal of
4.2.4, 4.2.5. Omitted: Noether's theorem (4.1.8), Proposition 4.1.10 (no type-level complex structure on `T(g, 0)`),
exercises, examples and remarks. Genus `1` is not modelled for the period map.

## Standing conventions and their modelling

- **Models** (N-D1, N-D2): `G` is a Fuchsian group `Γ ≤ SL(2, ℝ)` acting on `ℍ = U`; `M(G)` is `LiZhongQC.BeltramiGamma Γ`,
  `w^μ` is `LiZhongQC.normalizedSolution μ` (dilatation `μ` on `ℍ`, `0` on `𝕃`), and `T(G)` is identified with the Bers image
  `LiZhongQC.bersImage Γ ⊆ B(G)` (`GardinerLakic2000.cuspFormsL Γ`); `F(G)` is `LiZhongQC.BersFiberSpace Γ` and
  `V(G) = F(G)/G` is `LiZhongQC.BersQuotient Γ`. `T(g,n)` for a torsion-free group of type `(g, n)` is `T(G)` with
  `Nag1988.IsOfType Γ g n`; the punctured-marking Teichmüller space of §5.4 is `Nag1988.PointedTeichSpace`.
- **Holomorphy and topology** (N-D1): no `ChartedSpace`/`NormedSpace` instance is put on `T(G)`, `F(G)`, `V(G)`. Openness,
  continuity, derivative, holomorphy and biholomorphy are the Banach-style predicates `IsBOpen`, `IsBContOn`, `HasBDerivAt`,
  `IsBHolOn`, `IsBBiholOn` for norms given as functions into `ℝ≥0∞` (the cusp norm `GardinerLakic2000.cuspNorm`; as in
  `Lehto1987.IsHolomorphicFn`); topologies where needed are `generateFrom` the open sets so defined. Complex structures on
  quotients are given chart-wise (`IsQuotientManifoldOfDim`).
- **Anti-action** (N-D3): `mod(G)` acts on `F(G)` as printed, `(ω₁ ∘ ω₂)^* = ω₂^* ∘ ω₁^*` (`thm5_1_2_b`), `ω^*` being the
  relation `modStarFiber` (a relation, since no inverse functions are used). `N_qc(G)` is `GardinerLakic2000.qcNormalizer`,
  `Mod(G)` is `GardinerLakic2000.mcgGamma`, and `mod(G)` is the new `modExtended`.
- **Holomorphic families and markings** (N-D4, N-D5): a holomorphic family of closed genus-`g` Riemann surfaces is
  `LiZhongQC.IsHolomorphicFamily` with the fibers given as data; a marking is a fiberwise homotopy class of homeomorphisms
  `X_n ≃ₜ (fiber minus the sections)`, locally constant over trivializing neighbourhoods (replacing the book's reduction of
  the structure group to `Diff₀(X, n)`; equivalent for surfaces by Baer–Epstein).
- **Punctures** (§5.3.1): `X = ℍ/Γ`, `X' = X − {pts} = ℍ/Γ'`; the inclusion lifts to `ι : ℍ → ℍ` (`IsPunctureCovering`) and
  `M(X') = M(X)` is the pull-back `μ' = ι^*μ`.
- **Chapter 2 model** (group version). The surface `X = ℍ/Γ` is represented by the Fuchsian group `Γ ≤ SL(2, ℝ)`: `M(X)` is
  `LiZhongQC.BeltramiGamma Γ`, `T(X)` is `LiZhongQC.TeichGamma Γ`, `w^μ` is `LiZhongQC.fMuSym μ`, the Teichmüller distance
  is `LiZhongQC.teichDistanceGamma`; the reduced space `T^#(X)` is `ReducedTeichGamma` (`E_μ = E_ν`) and the Riemann space
  `R(X)` is `RiemannSpaceGamma` (conjugate groups `E_μ(Γ)`); `Q(X)`, `Q₀(X)`, `Q₀^#(X)` are the lifts `qcNormalizer`,
  `qcNormalizer0`, `qcNormalizerSharp`; `Mod` acts through `GardinerLakic2000.IsRhoGamma`. No topology or manifold instance is put
  on `T(X)`: real analyticity is read through the Bers embedding (Fricke coordinates).
- **Chapter 3 model.** A complex structure on a region `Ω` of a finite-dimensional real vector space (the Fricke image) is a set of
  charts `OpenPartialHomeomorph` onto open subsets of `ℂ^d` with holomorphic transitions (`IsComplexAtlasOn`); "unique" means that the
  union of two such atlases is again an atlas. A complex Banach manifold `X` is a Mathlib `ChartedSpace B X` with `IsManifold 𝓘(ℂ, B) ω X`;
  the unit ball `L^∞(U, Γ)₁` is `beltramiSet Γ` with the norm `essNorm` and the Banach-style predicates of Chapter 5. Nag's Poincaré
  metric has curvature `−4` (`λ_U = 1/(2 Im z)`): `GardinerLakic2000.poincareDensityGL`, half of `LiZhongQC.poincareDensity`.
- **Chapter 4 model** (batch N2). Homology of `S` is `Abelianization (FundamentalGroup S x₀)`, transported to a marked surface
  by the marking (`mapCycle`); period matrices use `Farkas–Kra`'s `IsPeriodOf`, `IsCanonicalHomologyBasis`; the period map
  `π : T(g, 0) → 𝔖_g` is the relation `IsPeriodMatrixOfClass` on Bers-image classes (`periodMatrix` chooses a representative),
  and "holomorphic on `T(g, 0)`" is `IsBHolOn` for the cusp norm through the Bers embedding. `Def(G)` is the quotient
  `DefSpace Γ` of pairs `(μ₁, μ₂)` of `BeltramiGamma Γ` (second factor recorded by reflection), reusing `Hubbard2006.qfSol`.
  Schiffer variation is modelled by lifted parametrized discs (`ParamDisk`) with `Γ`-invariant Schiffer forms
  (`IsSchifferForm`). Normalization: Nag's `∬ φ∧ψ` uses `dz∧dz̄ = −2i dx dy`, the project's pairings use `dx dy`.

## Corrections and readings

- Lemma 2.1.6 [CORRECTION]: the quotient pseudometric of a complete metric space through an arbitrary surjection need not be
  complete (counterexample in the docstring of `lemma2_1_6`); the book's proof uses that each point is as close to a fibre as its
  own fibre is, which holds for orbit maps of isometry groups (the pull-back by `Q₀` is isometric for `τ̂`), and the statement carries
  this hypothesis.
- Proposition 5.1.6 (ii): the order `n` of the bounded partial derivatives is not legible in the OCR; read as every order
  with one common radius `R₀` (Ahlfors–Weill gives all orders at once). [OCR?]
- Theorem 5.2.1 (a): "acts properly discontinuously and effectively" is read as: finitely many group elements meet a small
  neighbourhood, and only `±I` acts trivially.
- Corollary 5.4.3: the book's `C^∞` triviality is stated topologically (homeomorphisms).
- Theorem 4.4.1 [CORRECTION, Nag-fix2]: the compatibility of `w` with `G` is stated on `ℂ̂` (`mobiusSL g`); the plane form
  evaluated the junk value of `mobAct` at the real pole of `g`. Split submersions (`IsHolFiberSpace`) and the derivative of `F̃`
  (`IsFrickeHolAtlas`) are asked on the tangent directions only (the earlier clauses were satisfiable by any extension off them).

## Counts

| Chapter | new definitions (incl. helpers) | new statements | `exists` bullets |
|---|---|---|---|
| 2 Moduli spaces (§2.1, §2.3.10, §2.4, §2.5.5–§2.5.7, §2.7.1, §2.8.1) | 20 | 16 | 11 |
| 3 Complex structure (§3.2, §3.3.2, §3.5, §3.6.3) | 7 | 10 | 10 |
| 4 §4.1 Period map, Torelli, Rauch | 12 | 6 | 2 |
| 4 §4.2 Quasiconformal deformations | 4 | 6 | 0 |
| 4 §4.3 Schiffer variation | 11 | 8 | 0 |
| 4 §4.4 Schwarzian derivatives, deformations, Theorem S | 7 | 10 | 0 |
| 4 §4.5 The Bers boundary | 7 | 9 | 0 |
| 4 §4.6 Complex analytic parameters for `T(1, 1)`, `T(1, 2)` | 0 | 9 | 0 |
| 5 §5.1 The Bers fiber space | 16 | 11 | 6 |
| 5 §5.2 The universal family | 14 | 11 | 5 |
| 5 §5.3.1–§5.3.4 Bers' isomorphism theorem | 7 | 6 | 0 |
| 5 §5.4.1–§5.4.5 Marked families, universal property | 11 | 5 | 1 |
-/
