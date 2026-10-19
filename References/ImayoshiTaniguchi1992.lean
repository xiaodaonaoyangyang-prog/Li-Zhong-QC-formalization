import References.ImayoshiTaniguchi1992.Ch01.S02_TeichmullerSpaceOfGenusOne
import References.ImayoshiTaniguchi1992.Ch01.S03_TeichmullerSpaceOfGenusG
import References.ImayoshiTaniguchi1992.Ch01.S04_QuasiconformalDescription
import References.ImayoshiTaniguchi1992.Ch02.S04_FuchsianGroups
import References.ImayoshiTaniguchi1992.Ch02.S05_FrickeSpace
import References.ImayoshiTaniguchi1992.Ch03.S01_HyperbolicGeometry
import References.ImayoshiTaniguchi1992.Ch03.S02_FenchelNielsen
import References.ImayoshiTaniguchi1992.Ch03.S03_FrickeKlein
import References.ImayoshiTaniguchi1992.Ch03.S04_ThurstonCompactification
import References.ImayoshiTaniguchi1992.Ch04.S01_QuasiconformalMappings
import References.ImayoshiTaniguchi1992.Ch04.S02_BeltramiEquation
import References.ImayoshiTaniguchi1992.Ch04.S03_DependenceOnCoefficients
import References.ImayoshiTaniguchi1992.Ch05.S01_AnalyticConstruction
import References.ImayoshiTaniguchi1992.Ch05.S02_TeichmullerMappings
import References.ImayoshiTaniguchi1992.Ch05.S03_UniquenessProof
import References.ImayoshiTaniguchi1992.Ch06.S01_BersEmbedding
import References.ImayoshiTaniguchi1992.Ch06.S02_InvarianceOfComplexStructure
import References.ImayoshiTaniguchi1992.Ch06.S03_ModuliSets
import References.ImayoshiTaniguchi1992.Ch06.S04_Royden
import References.ImayoshiTaniguchi1992.Ch06.S05_ModularClassification
import References.ImayoshiTaniguchi1992.Ch07.S03_WeilPetersson
import References.ImayoshiTaniguchi1992.Ch08.S01_FNDeformation
import References.ImayoshiTaniguchi1992.Ch08.S02_WolpertFormula

/-!
# Imayoshi–Taniguchi, *An Introduction to Teichmüller Spaces* (1992)

Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer-Verlag, Tokyo 1992. Statement-level
formalization of the new-topic slice (Chapter 3, §6.4–§6.5, §7.3, Chapter 8): genuine definitions, every result stated with a
`sorry` proof; results already in Mathlib, the project or the References are passed with an `exists:` pointer in the file's
item index. The other chapters are covered by the section-level concordance in `refs_lean/ImayoshiTaniguchi1992/INVENTORY.md` §9
and get no statements here, except for the items promoted in W2 (below).

**W2 batch I2 (worker 下属3).** The genuinely new items of Chapter 2 §2.4–§2.5 and Chapter 4 (all other numbered results of these chapters
are `exists:` pointers in the item indices): Lemmas 2.16, 2.18, 2.20, Proposition 2.19 and Lemma 2.24 (`Ch02/S04`, `S05`: Fuchsian groups
and the canonical generators), Proposition 4.18 (`Ch04/S01`), Corollary 1 to Theorem 4.24 (`Ch04/S02`), Lemmas 4.34, 4.35, Theorem 4.37 and its
corollary (`Ch04/S03`). The canonical `μ`-quasiconformal map `f^μ` is `LiZhongQC.normalizedSolution`.

## Sources

The Mathpix text `full.md` of `An Introduction to Teichmuller Spaces … ef13744b` (cited `IT1:<line>`, Chapters 1–7.1) and
`… 0ac64ea2` (cited `IT2:<line>`, §7.2 – Appendix).

## Coverage

Delivered so far: Chapter 3 *Fenchel–Nielsen and Fricke–Klein coordinates, Thurston's compactification* (batch D2: §3.1 `Ch03/S01`, §3.2 `S02`, §3.3 `S03`, §3.4 `S04`) and (batch D4) Chapter 6 §6.4 *Royden's theorems* (`Ch06/S04`) and §6.5 *Classification of Teichmüller modular
transformations* (`Ch06/S05`). The pseudo-Anosov items (§6.5.4 and Theorem 6.35) are deferred (pseudo-Anosov diffeomorphisms
are not defined in the book). The Weil–Petersson metric (batch D3: Chapter 7 §7.3 `Ch07/S03`, with the notions of §7.1–§7.2 it needs) and Chapter 8 §8.1–§8.3
(`Ch08/S01` Fenchel–Nielsen deformations, `Ch08/S02` Gardiner's and Wolpert's formulas) complete the slice; Lemma 8.7, the mirror map
and Lemma 8.8, and the genus-1 Weil–Petersson metric, are deferred or omitted (item indices).

**W2 batch I3 (Lane D).** The genuinely new items of Chapter 6 §6.1–§6.3 (all other results of these sections are `exists:` pointers
in the item indices): the local right inverse of Bers' embedding and the real-analytic representatives (`Ch06/S02`: Theorem 6.8,
Corollary to Theorem 6.9), the derivative of the Bers map at a general point (Theorem 6.11), and Lemma 6.15 (`Ch06/S03`). Theorem 6.19
(the moduli space as a normal complex analytic space) is deferred. `Ch06/S01` is an item index only.

**W2 batch I1a (Lane D).** Chapter 5 (item indices for all results; every result is an `exists:` pointer except two new statements):
Lemma 5.8 (continuity of the Fricke coordinates on `T(R)`, `Ch05/S02`) and Proposition 5.19 (existence and uniqueness of the terminal
quadratic differential of a Teichmüller map, `Ch05/S03`, with the definition of a formal Teichmüller mapping). Lemma 5.1 is the
closed case `LiZhongQC.thm27_1`; its non-compact case is deferred (marked surfaces are closed in `LiZhongQC.MarkedRS`).

**W2 batch I1b (Lane D).** Chapter 1 §1.2–§1.5: the markings of tori and surfaces of genus `g` by canonical systems of generators of
the fundamental group (`Ch01/S02`: `IsCanonicalSystem`, `MarkedEquiv`, Theorem 1.3; `Ch01/S03`: Theorem 1.4), and the quasiconformal
description of `T(R)` (`Ch01/S04`: Proposition 1.5, Theorem 1.6). Diffeomorphisms of IT are quasiconformal homeomorphisms here. The
Corollary to Theorem 1.6 and Theorems 1.7, 1.8 (Riemannian metrics) are deferred in the item index of `Ch01/S04` (they need a smooth and
Riemannian layer that is not installed).

## Standing conventions and their modelling

- **Teichmüller spaces**: `T(Γ)` is `LiZhongQC.TeichGamma Γ`, `T(R_*)` is `LiZhongQC.TeichSpace S₀`; modular transformations are
  `LiZhongQC.ModTransform` acting by `LiZhongQC.ModAction`. (IT-D1.)
- **Distance** (IT-D3): IT's Teichmüller distance `d = log K` is twice `LiZhongQC.teichDistance` (`½ log K`); the factor is explicit
  wherever it matters (`IsStraightLineTeich`).
- **Kobayashi metric** (IT-D4): `GardinerLakic2000.kobayashiPseudo`; Royden's theorem 6.21 is `Lehto1987.thm5_9_4`.
- **Geodesics**: simple closed geodesics of `ℍ/Γ` are simple closed Poincaré geodesics (`GardinerLakic2000.IsClosedPoincareGeodesic`)
  with their length `LiZhongQC.poincareLengthLoop`.

- **Fricke coordinates and twists (Chapter 3, IT-D1, IT-D2)**: IT's own `frickeCoordinatesIT`/`frickeSpaceIT` (entries `(a, c, d)` of the
  normalized generators with `c > 0`, on `FC g`); lengths are `References.markedLength`; the twisting angle is `2π τ/ℓ` with
  `τ = References.footDisp` of three based loops (`IsAdjacentPantsDatum`: lifts `G, A, B` generating the stabilizers of the two adjacent lifted pants); `θ_j` is a relation mod `2π`.
- **Pants** (`IsPantsOf`): a relatively compact open subset of `ℍ/Γ` homeomorphic to `pantsModel` whose frontier consists of three
  disjoint simple closed geodesics (`References.IsSimpleClosedGeodesicOf`); Theorems 3.4, 3.5 are stated with the shared
  `References.IsTrouserCoreWithLengths`.
- **Thurston's compactification**: `MF`, `PMF` are IT's closure definitions in `(ℝ̄⁺)^S` (`SimpleClass`).

## Counts

| Chapter | new definitions (incl. helpers) | new statements | `exists` bullets |
|---|---|---|---|
| 1 §1.2 Tori and Teichmüller space of genus one | 2 | 1 | 2 |
| 1 §1.3 Teichmüller space of genus g | 0 | 2 | 1 |
| 1 §1.4–§1.5 Quasiconformal description | 0 | 2 | 1 |
| 2 §2.1–§2.4 Fuchsian groups | 3 | 4 | 15 |
| 2 §2.5 Fricke space | 0 | 1 | 2 |
| 4 §4.1 Quasiconformal mappings | 0 | 2 | 18 |
| 4 §4.2 The Beltrami equation | 1 | 2 | 12 |
| 4 §4.3 Dependence on Beltrami coefficients | 0 | 4 | 3 |
| 3 §3.1 Hyperbolic geometry | 6 | 11 | 7 |
| 3 §3.2 Fenchel–Nielsen coordinates | 16 | 9 | 1 |
| 3 §3.3 Fricke–Klein embedding | 3 | 3 | 1 |
| 3 §3.4 Thurston's compactification | 14 | 9 | 3 |
| 5 §5.1 Analytic construction (item index) | 0 | 0 | 7 |
| 5 §5.2 Teichmüller mappings and theorems | 0 | 1 | 13 |
| 5 §5.3 Proof of the uniqueness theorem | 1 | 1 | 5 |
| 6 §6.1 Bers' embedding (item index) | 0 | 0 | 6 |
| 6 §6.2 Invariance of the complex structure | 2 | 4 | 3 |
| 6 §6.3 Moduli sets | 0 | 1 | 5 |
| 6 §6.4 Royden's theorems | 2 | 4 | 3 |
| 6 §6.5 Classification of modular transformations | 23 | 14 | 1 |
| 7 §7.3 Weil–Petersson metric | 26 | 10 | 1 |
| 8 §8.1 Fenchel–Nielsen deformations | 17 | 6 | 0 |
| 8 §8.2–§8.3 Gardiner's and Wolpert's formulas | 3 | 6 | 2 |
-/
