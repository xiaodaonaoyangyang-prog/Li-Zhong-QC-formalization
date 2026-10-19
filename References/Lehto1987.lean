import References.Lehto1987.Ch01.S01_ConformalInvariants
import References.Lehto1987.Ch01.S02_GeometricDefinitionOfQuasiconformalMappings
import References.Lehto1987.Ch01.S03_AnalyticDefinitionOfQuasiconformalMappings
import References.Lehto1987.Ch01.S04_BeltramiDifferentialEquation
import References.Lehto1987.Ch01.S05_TheBoundaryValueProblem
import References.Lehto1987.Ch01.S06_Quasidiscs
import References.Lehto1987.Ch02.S01_SchwarzianDerivative
import References.Lehto1987.Ch02.S02_DistanceBetweenSimplyConnectedDomains
import References.Lehto1987.Ch02.S03_ConformalMappingsWithQuasiconformalExtensions
import References.Lehto1987.Ch02.S04_UnivalenceAndQuasiconformalExtensibilityOfMeromorphicFunctions
import References.Lehto1987.Ch02.S05_FunctionsUnivalentInADisc
import References.Lehto1987.Ch03.S01_ModelsOfTheUniversalTeichmullerSpace
import References.Lehto1987.Ch03.S02_MetricOfTheUniversalTeichmullerSpace
import References.Lehto1987.Ch03.S03_SpaceOfQuasisymmetricFunctions
import References.Lehto1987.Ch03.S04_SpaceOfSchwarzianDerivatives
import References.Lehto1987.Ch03.S05_InnerRadiusOfUnivalence
import References.Lehto1987.Ch04.S01_ManifoldsAndTheirStructures
import References.Lehto1987.Ch04.S02_TopologyOfCoveringSurfaces
import References.Lehto1987.Ch04.S03_UniformizationOfRiemannSurfaces
import References.Lehto1987.Ch04.S04_GroupsOfMobiusTransformations
import References.Lehto1987.Ch04.S05_CompactRiemannSurfaces
import References.Lehto1987.Ch04.S06_TrajectoriesOfQuadraticDifferentials
import References.Lehto1987.Ch04.S07_GeodesicsOfQuadraticDifferentials
import References.Lehto1987.Ch05.S01_QuasiconformalMappingsOfRiemannSurfaces
import References.Lehto1987.Ch05.S02_DefinitionsOfTeichmullerSpace
import References.Lehto1987.Ch05.S03_TeichmullerSpaceAndLiftedMappings
import References.Lehto1987.Ch05.S04_TeichmullerSpaceAndSchwarzianDerivatives
import References.Lehto1987.Ch05.S05_ComplexStructuresOnTeichmullerSpaces
import References.Lehto1987.Ch05.S06_TeichmullerSpaceOfATorus
import References.Lehto1987.Ch05.S07_ExtremalMappingsOfRiemannSurfaces
import References.Lehto1987.Ch05.S08_UniquenessOfExtremalMappingsOfCompactSurfaces
import References.Lehto1987.Ch05.S09_TeichmullerSpacesOfCompactSurfaces

/-!
# Lehto, *Univalent Functions and Teichmüller Spaces* (1987)

O. Lehto, *Univalent Functions and Teichmüller Spaces*, Graduate Texts in Mathematics 109, Springer, New York 1987.
Statement-level formalization: genuine definitions, every result of the book stated with a `sorry` proof; results
already in Mathlib, the project or the References are passed with an `exists:` pointer in the file's item index.

## Sources

The OCR'd text (MinerU), `full.md` of
`Univalent Functions and Teichmüller Spaces (Olli Lehto (auth.)) (Z-Library).pdf-74996424-…` (P1, 6358 lines:
front matter, Ch. I – V §3.4) and `…pdf-994159c2-…` (P2, 2581 lines: V §3.5 – end). Line numbers `P1:n` in the files
refer to the first (sed/grep numbering).

## Coverage

The whole book: Chapter I *Quasiconformal Mappings* (§1–§6), Chapter II *Univalent Functions* (§1–§5), Chapter III
*Universal Teichmüller Space* (§1–§5), Chapter IV *Riemann Surfaces* (§1–§7) and Chapter V *Teichmüller Spaces*
(§1–§9), one file per section, in book order. The book has no exercises. The text layer of Ch. V §3.4 has a gap at
the seam of the two PDF parts (P1:6358 / P2:4); the surviving claim is kept (`para5_3_4`).
The displays (I.4.6)–(I.4.8) are lost in the text layer; (4.7) was read from its page image, (4.6) and (4.8) are the
operators of LV III.7 and the project.

## Standing conventions and their modelling

- **The plane.** Lehto's plane is the Riemann sphere `ℂ̄ = LiZhongQC.ExtPlane`; domains, Jordan curves and Jordan
  domains are those of `ℂ̄` (`References.IsDomainExt`, `LiZhongQC.IsJordanCurve`, `References.IsJordanDomainExt`).
- **Quasiconformal mappings** (Ch. I summarizes Lehto–Virtanen): LV's notions on `ℂ̄`
  (`LehtoVirtanen1973.IsKQuasiconformal`, `IsQuasiconformalMap`, `maxDilatationK`, `IsConformalMap`,
  `complexDilatationLV`, quadrilaterals and ring domains); every `K` is `≥ 1`. A "`K`-quasiconformal mapping of the
  plane" is `IsKQuasiconformal f univ K`. `‖μ‖∞` is `eLpNorm μ ⊤ volume`, read literally (a.e.), so LV's pointwise
  statements are near misses (Theorems I.4.1, I.4.4).
- **Quasicircles** are the project's `LiZhongQC.IsQuasicircle`, `IsKQuasicircle`; quasidiscs `References.IsQuasidiskExt`
  and the new `IsKQuasidiscExt`.
- **Meromorphic functions** are `f : ℂ → ℂ` read in `ℂ̄` by `LiZhongQC.meroToExt`; locally injective meromorphic
  functions are `LiZhongQC.IsLocUnivMero` in plane sets and `IsLocUnivMeroExt` in domains of `ℂ̄`; univalent
  (conformal) ones are `Gehring1978.IsConformalExt`.
- **Schwarzian derivatives and norms.** `S_f` is `LiZhongQC.schwarzian`; the Poincaré density `η_A = |f′|/(1 − |f|²)`
  and the norm `‖φ‖_A = sup |φ| η_A⁻²` are Gehring's `Gehring1978.hypDensity`, `Gehring1978.hypNorm` (curvature
  `−4`); every constant of Ch. II (6, 2, 12, …) is for this normalization, so statements with other norms are near
  misses.
- **The universal Teichmüller space** (Ch. III) is the project's model throughout (Li Zhong §21, §33): `B` is
  `LiZhongQC.BeltramiH`, `f^μ` is `LiZhongQC.fMuSym`, `f_μ` is `LiZhongQC.normalizedSolution`, `T` is
  `LiZhongQC.UniversalTeichmuller` with origin `LiZhongQC.UniversalTeichmuller.origin`. In the project `f_μ` is
  conformal in the lower half-plane `H′`, so the half-planes of Lehto's §4–§5 (where the roles are exchanged) are
  mirrored: `Q` is `LiZhongQC.bersSpaceL`, `T(1)` the range of `LiZhongQC.bersMapU`, `U`
  `LiZhongQC.schwarzianUnivalentSet`. The Teichmüller distance `τ` is `teichDist`, half of the project's
  `LiZhongQC.UniversalTeichmuller.dist`; the norm of `Q` is Lehto's (`Gehring1978.hypNorm`, 4 times
  `LiZhongQC.bersNormL`). `T` has no topology instance, so "continuous", "homeomorphism", "complete" are stated in
  `ε–δ` form for `τ`.
- **Riemann surfaces** (Ch. IV): a surface is a second countable connected Hausdorff `ChartedSpace ℂ`; a Riemann
  surface adds `IsManifold 𝓘(ℂ) ω` (the shared `References.IsRiemannSurface`, with second countability). Lehto's
  covering notions are his own (smooth = local homeomorphism; unlimited = paths lift; branched covering surfaces), and
  the covering group is Mathlib's `deck`. Conformal structures are explicit `ChartedSpace ℂ` arguments, compared
  through their holomorphic functions. Differentials are the project's local-coefficient families
  (`LiZhongQC.IsDiffFamily`). Möbius groups are subgroups of `SL(2, ℂ)` acting by `LiZhongQC.mobiusSL`, and
  Fuchsian groups (fixed point free, on the disc) are taken on `ℍ` (`LiZhongQC.IsFuchsian`, `LiZhongQC.ActsFreely`).
  The `φ`-metric of a quadratic differential is the project's (`LiZhongQC.phiLengthPathInv`, `LiZhongQC.phiDistRS`).
- **Teichmüller spaces** (Ch. V): for surfaces covered by the disc, `T_S` is Gardiner–Lakic's
  `GardinerLakic2000.TeichSpace` (Beltrami coefficients modulo Teichmüller equivalence, through a uniformization by
  `ℍ`) with `GardinerLakic2000.teichDist`; the lifted model of §3–§7 is the project's `LiZhongQC.TeichGamma` with
  `LiZhongQC.teichDistanceGamma`, mirrored as in Ch. III §4 (the Schwarzians on `𝕃`); tori have the general
  `TeichmullerSpace`. Compact surfaces of genus `p > 1` use the project's §26–§29 (Teichmüller maps
  `LiZhongQC.IsTeichmullerMap`). Spaces of functions with a norm given as a function carry no normed instance;
  holomorphy there is written out (`IsHolomorphicFn`). Where several conformal structures of one surface are compared
  (Ch. V §1–§2) they are atlases `Set (OpenPartialHomeomorph S ℂ)` (`IsConformalAtlas`): a local `ChartedSpace`
  variable would act as an instance and override the ambient structure.
- **Quantified constants** ("`c(K)` depending only on `K`") are `∀ K, ∃ c, ∀ …`; families of normalized solutions
  (Theorem II.3.1, Corollary II.3.1, Theorem I.4.6) are stated relationally, for every family with the stated
  normalization.

## Corrections

- (II.1.16) [misprint]: equality `|b₁| = 1` holds iff `f(z) = z + b₀ + e^{iθ}/z`; the book drops `b₀`, which (1.14)
  allows (the pointer `Pommerenke1992.area_theorem` has the `b₀`).
- II §3.6 [misprint]: "`aₙ = 2k/(n + 1)` for the extremal (3.16) in Theorem 3.4" reads `bₙ` and (3.10) in Theorem
  3.5 (a remark; no statement depends on it).
- Proof slips (notes only): in the proof of Lemma I.2.1, `M(f(B)) ≤ 2π²/η²` should be `π²/(2η²)` by (1.9); the proof of
  Theorem I.4.3 uses Hölder's inequality for `Tφᵢ`, which needs the bounded support of `φᵢ` (true).
- Reading: "`f` meromorphic with `‖S_f‖ ≤ 2`" (Theorems II.4.1, II.5.1–II.5.4, Schwarzian domains) presupposes that `f`
  is locally injective (otherwise `S_f` has poles and the norm is infinite); modelled with `IsLocUnivMero(Ext)`.
- Theorem II.5.2, sharpness [OCR]: the exponent of `z^{iε}` is printed `ε`.
- Proof slip (note only): in the proof of Lemma III.5.2, `‖S_f‖_{A_k} = 4k − k²` should be `4k − 2k²` (P1:4644).
- Lemma V.5.1 (i) [false as printed]: Gâteaux holomorphy alone does not imply holomorphy in infinite dimension (a
  discontinuous linear functional satisfies (i)); stated with the continuity of `f`, as in Bourbaki.
- Theorem V.6.6 [misprint]: "an isometry of `T_S` onto `T_S`" reads `T_{S′}`.
- Formula (V.2.4) [misprint]: "a geodesic from 0 to `p_t`" reads "from 0 to `p`".
- Theorem V.4.1 [OCR gap]: the statement is lost in the text layer (only "(4.4)" survives); reconstructed as
  `T(G) = Q(G) ∩ T(1)` from its proof and uses.
- Lemma V.7.1 [OCR]: the bound printed `42t²` is `12t²`.
- Lemma V.6.3, equality case (reading): "equality iff `f` is affine" is for `K` the maximal dilatation of `f`, as in
  the proof; for a larger `K` the affine `f` gives a strict inequality.

## Counts

| Chapter | new definitions (helpers) | new statements | `exists` bullets | omitted bullets |
|---|---|---|---|---|
| I Quasiconformal Mappings (§1–§6) | 9 (+4) | 72 | 71 | 21 |
| II Univalent Functions (§1–§5) | 13 (+5) | 72 | 13 | 29 |
| III Universal Teichmüller Space (§1–§5) | 26 (+2) | 52 | 18 | 30 |
| IV Riemann Surfaces (§1–§7) | 54 (+8) | 75 | 38 | 48 |
| V Teichmüller Spaces (§1–§9) | 35 (+5) | 105 | 51 | 65 |
| total | 137 (+24) | 376 | 191 | 193 |
-/
