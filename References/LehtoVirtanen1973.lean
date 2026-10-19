import References.LehtoVirtanen1973.Ch01.S01_TopologicalProperties
import References.LehtoVirtanen1973.Ch01.S02_ConformalMappings
import References.LehtoVirtanen1973.Ch01.S03_DefinitionQC
import References.LehtoVirtanen1973.Ch01.S04_ModuleExtremalLength
import References.LehtoVirtanen1973.Ch01.S05_TwoBasicProperties
import References.LehtoVirtanen1973.Ch01.S06_ModuleRingDomain
import References.LehtoVirtanen1973.Ch01.S07_RingCharacterization
import References.LehtoVirtanen1973.Ch01.S08_ExtensionTheorems
import References.LehtoVirtanen1973.Ch01.S09_LocalCharacterization
import References.LehtoVirtanen1973.Ch02.S01_ExtremalRingDomains
import References.LehtoVirtanen1973.Ch02.S02_GrotzschModule
import References.LehtoVirtanen1973.Ch02.S03_DistortionDisc
import References.LehtoVirtanen1973.Ch02.S04_OrderOfContinuity
import References.LehtoVirtanen1973.Ch02.S05_ConvergenceTheorems
import References.LehtoVirtanen1973.Ch02.S06_BoundaryValues
import References.LehtoVirtanen1973.Ch02.S07_QuasisymmetricFunctions
import References.LehtoVirtanen1973.Ch02.S08_QCContinuation
import References.LehtoVirtanen1973.Ch02.S09_CircularDilatation
import References.LehtoVirtanen1973.Ch03.S01_MeasureIntegral
import References.LehtoVirtanen1973.Ch03.S02_AbsoluteContinuity
import References.LehtoVirtanen1973.Ch03.S03_Differentiability
import References.LehtoVirtanen1973.Ch03.S04_ModuleArcFamilies
import References.LehtoVirtanen1973.Ch03.S05_Approximation
import References.LehtoVirtanen1973.Ch03.S06_LpDerivatives
import References.LehtoVirtanen1973.Ch03.S07_HilbertTransformation
import References.LehtoVirtanen1973.Ch04.S01_AnalyticProperties
import References.LehtoVirtanen1973.Ch04.S02_AnalyticDefinition
import References.LehtoVirtanen1973.Ch04.S03_VariantsGeometricDefinition
import References.LehtoVirtanen1973.Ch04.S04_CircularDilatation
import References.LehtoVirtanen1973.Ch04.S05_ComplexDilatation
import References.LehtoVirtanen1973.Ch05.S01_ExistenceTheorem
import References.LehtoVirtanen1973.Ch05.S02_LocalDilatationMeasures
import References.LehtoVirtanen1973.Ch05.S03_RemovablePointSets
import References.LehtoVirtanen1973.Ch05.S04_ApproximationOfQuasiconformalMapping
import References.LehtoVirtanen1973.Ch05.S05_ApplicationOfHilbertTransformation
import References.LehtoVirtanen1973.Ch05.S06_ConformalityAtAPoint
import References.LehtoVirtanen1973.Ch05.S07_RegularityOfMappingWithPrescribedDilatation
import References.LehtoVirtanen1973.Ch06.S00_Introduction
import References.LehtoVirtanen1973.Ch06.S01_GeometricCharacterization
import References.LehtoVirtanen1973.Ch06.S02_AnalyticCharacterization

/-!
# Lehto–Virtanen, *Quasiconformal Mappings in the Plane* (1973)

O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, second edition, Die Grundlehren der mathematischen
Wissenschaften 126, Springer-Verlag, Berlin–Heidelberg–New York 1973 (translated from *Quasikonforme Abbildungen*,
1965). Statement-level formalization: genuine definitions, every result of the book stated with a `sorry` proof;
results already in the project or in Mathlib are passed with an `exists:` pointer in the file's item index.

## Sources

The OCR'd text (MinerU) in `D:\lean\lizhong_thm21_archive\refs\`:
- `Olli Lehto - Quasiconformal mappings in the plane -Springer (1973)\full.md` — front matter, Ch. I – Ch. V §1.4
  (book pp. 1–194);
- `Olli Lehto - Quasiconformal mappings in the plane -Springer (1973).pdf-e\full.md` — Ch. V §1.4 – Ch. VI, index
  (pp. 195–258).

## Coverage

The whole book is present (printed page numbers continuous, pp. 1–258); the two parts join seamlessly between pp. 194
and 195. MinerU dropped the footnotes from `full.md`; they were recovered from `layout.json` (all but footnote 39).
Delivered: Chapters I–VI (the whole book).

## Standing conventions and their modelling

- The *plane* is the extended plane `ℂ̄ = LiZhongQC.ExtPlane` (`OnePoint ℂ`); the *finite plane* is `ℂ` (I.1.1).
  Domains are open connected subsets of `ℂ̄` (`References.IsDomainExt`); maps are functions
  `ExtPlane → ExtPlane`, only their values on the relevant set matter. `IsKQuasiconformal w univ K` is a `K`-q.c.
  self-map of `ℂ̄`.
- The spherical metric `k` (`sphericalDist`) is used for uniform convergence and for distances and diameters in `ℂ̄`.
- The empty set counts as connected (footnote 3): "connected" is `IsPreconnected` where a set may be empty.
- Quasiconformal mappings are sense-preserving homeomorphisms between domains of `ℂ̄` whose maximal dilatation
  `K(G)`, defined with the conformal modules of quadrilaterals `Q̄ ⊂ G` (quadrilaterals may contain `∞`), is finite
  (`IsKQuasiconformal`, `IsQuasiconformalMap`). Orientation is LV's topological one (a positively oriented boundary
  parametrization winds `+1` after a Möbius normalization).
- Conformality, differentiability and Jacobians at `∞` and at poles are read in the charts `z ↦ z - p`, `z ↦ 1/z`
  (`localRep`); from I.9 on "differentiable" refers to finite points and finite values (`finiteMap`).
- Extremal-length classes: Chapter I models the "deliberately indefinite" classes of I.4 and I.6 by Borel densities
  and the project's locally rectifiable curves (`LiZhongQC.LRCurve`, `LiZhongQC.rhoLength`, `LiZhongQC.rhoArea`,
  `LiZhongQC.densitiesP0`), the precision announced in footnotes 7–8; Chapter III §4 formalizes LV's own module of
  families of point-set arcs and curves (`arcFamilyModule`).
- Values: `K(G)`, `F(z)`, the module `M(B)` of a ring domain and the module `M(𝒞)` of a family of arcs or curves
  (III.4) are `ℝ≥0∞`-valued; the module `M(Q)` of a quadrilateral is real. Inequalities between moduli are
  multiplied out.
- Unlabelled results stated in the text and cited later are included (bullets "Unlabelled (§n.m, P1:line)");
  unlabelled facts used only inside proofs, remarks, examples and proof steps are not items.

## Corrections

Repairs of the source (misprints, OCR damage, statements false as printed), each marked in the declaration's
docstring:
- I.1.9, free boundary arc, condition 1° (P1:291): printed "`C ∩ (Fr G - C)` is empty", which is vacuous; the
  overline was lost in the OCR. Stated as `C ∩ closure (Fr G \ C) = ∅` (`IsFreeBoundaryArc`).
- I.6.7, convergence of ring domains from inside (P1:955): `(-B₁)ᵢ` printed for `(-B)ᵢ` [OCR]
  (`RingConvergesFromInside`).
- Cross-references in Ch. II [OCR]: P1:2900 "Lemma I.4.4" is Lemma I.1.4; P1:2934 "I.4.9" is I.1.9.
- II.1.4, formula (1.6) (P1:1637): the denominator is printed `√2 (|z₁| + |z₂|)`; stated as `√(2(|z₁| + |z₂|))`, the
  form of (1.8) and of its use at P1:2069 [OCR] (`thm2_1_2`).
- II.3, formula (3.6): `γ` printed for `r` [OCR] (`eq2_3_6`).
- II.4.2 1° and II.5.1 2°: false as printed if the two points `z₁`, `z₂` may coincide (`wₙ(z) = nz`, `a = ∞`,
  `z₁ = z₂ = 0`); stated with `z₁ ≠ z₂` ("two points") (`thm2_4_2_i`, `thm2_5_1_ii`).
- II.7.1, Remark (P1:2706): the constant `k^{2n}` as OCR'd, probably a flattened `k^{2^n}`, the constant the book's
  doubling argument gives; with `k^{2n}` the Remark is false for `n ≥ 6` [OCR?] (`kQuasisymmetric_of_local_and_large`).
- III.1.2, Lemma 1.2: false as printed (equality of `dim (A × B)` and `dim A + dim B`); stated as the true inequality
  and the equality for a segment factor, the case used in IV.2.2 (`lemma3_1_2`, `lemma3_1_2_interval`).
- III.2.11, formula (2.11) (P1:3702): `dg′` printed for `dg` [misprint] (`eq3_2_11`).
- III.6.5, the example (6.17) (P1:4603): OCR'd as `g(z) = 1/z` (inline OCR, unverifiable against the print) for
  `g(z) = z̄` [OCR?] (`eq3_6_17`).
- Cross-reference in Ch. V [OCR or misprint]: P2:221 "Lemma III.4.3" is Lemma III.1.3 (`lemma3_1_3`,
  `gross_finite_sections`).
- IV.5.2, formula (5.6) (P1:5730): the OCR reads `arg w_z(z)` in the exponent of the denominator; the book prints
  `arg w_{\bar z}(z)` [OCR] (`eq4_5_6_i`, `eq4_5_6_ii`, stated as printed).
- IV.5.5, weak convergence (5.12) and Lemma 5.1 (P1:5835–5845): with LV's presupposition that every `fₙ` is locally
  integrable in `G`, Lemma 5.1 is false (conformal `wₙ` of the disc with `∞ ∈ wₙ(G)` can converge to the identity);
  `fₙ` is required to be integrable on each test rectangle for all large `n` (`ConvergesWeaklyOnRectangles`).
- Ch. V–VI [OCR]: the Beltrami equation `w_{\bar z} = κ w_z` is OCR'd as `w_z = κ w_z` (P2:1, 5, 465, 1586, 1740);
  `κ` is OCR'd as `x` at P2:1586, 1767, and `w̃_z` stands for `w̃_{\bar z}` at P2:465, 595. The print is right (page
  image of (2.1) of Ch. VI). Also V.4.3 (P2:423) `|z|` for `|κ(z)|`; V.5.4 (P2:635–637) `φ(K)` for `p(K)`
  (`limitExponent_mul_bounds`) and (7.1) (P2:1343) `τ` for `r` (`thm5_7_1`), both checked on the page images; VI.1
  (P2:1600, 1670, 1687) `<` for `⊂`.
- Cross-references and slips in the running text of Ch. V–VI [OCR or misprint] (no page-image check): P2:23
  "Lemma I.9.4" is Lemma I.9.1; P2:217 "Lemma IV.4.1" is Lemma IV.1.1; P2:1312 "Lemmas 1 and 2" are Lemmas 6.1, 6.2
  (`thm5_6_1_uniform`); V.7.2 (P2:1424) "`z₀ ∉ F`" for `z₀ ∈ F` (`DilIntegralConvergesUniformly`); P2:1622
  "Theorem 1.4" is Theorem VI.1.1.

Hypotheses added for meaning or truth (each with a `Modelling:` line): Lemma I.1.4 (`Gᶜ` nonempty), Theorem I.8.3
(`w` sense-preserving, since `K(·)` is defined only for such maps), Radó's theorem (finite normalization point); in
Ch. II: Teichmüller's module theorem (`z₁ ≠ 0`), Theorem 1.2 and Mori (i) (`z₁ ≠ z₂`), Mori (ii) (`z₁ ≠ 1`),
Theorem 5.1, last sentence (the two omitted values distinct, `a ≠ b`), Theorem 6.1 (ii) (`z₄ ∈ Fr G`), Theorem 8.3
(`n ≥ 1`: simply connected domains, as applied in 8.5), the family statements of §4–§5 (`G` a domain, explicitly),
(9.1) (finite domains, as in the proof); read off the context: (3.8) (`K > 1`, the standing assumption of the
derivation), (3.10) (`0 < r`, `0 < R`: nonempty discs), (7.8) and (7.10) (`x ≠ y`; for `x = y` both sides vanish);
in Ch. III: Lemma 1.2 (nonempty factors), and the chapter's standing assumptions made explicit in each statement
(`G` a domain of the finite plane, `1 ≤ p < ∞`, sense-preserving in §3.3–§3.5; Theorem 6.1 and Lemma 6.4 carry
none, as printed); in Ch. IV: `1 ≤ K` (LV's standing `K ≥ 1`; without it the hypotheses are unsatisfiable or, in Theorem
5.1 (ii), the statement is false) in the remark of §1.1 (also sense-preserving), the analytic definition, Theorems
3.3, 3.4, 4.2 and 5.1 (ii); in Ch. V: `1 ≤ K` in §3 (removability is vacuous for `K < 1`) and in (6.11), `G − E′` a
domain (`hGE'`) in the monotonicity of removability with respect to `𝒲₃` (`isRemovableW3_mono`: the class of `E′` is
defined only then), `StrictMono` of the subsequence in Theorem 4.1, `1 < p` in Lemma 5.1 (`‖S‖_p` is used only for
`p > 1`), `1 < K` in (5.10) (`(K + 1)/(K − 1)`), `w` finite in Theorem 5.3, `1 ≤ p` in Theorem 5.1 (i), the disc
`ball z₀ r ⊆ D` in (7.1) (the domain where `κ` is defined); in Ch. VI: `1 ≤ K` in Theorem 2.2 and its corollary
(false for `K < −1`).

Conclusions strengthened (documented in the docstring, and true): in Ch. VI, the claim of the Introduction (P2:1584)
that a quasiconformal function is locally homeomorphic up to isolated points also asserts sense-preservation off
them (`qcFunction_localHomeo`; there `f` is locally a conformal mapping composed with the sense-preserving `w`, and
Theorem 1.1, which the Introduction announces, assumes it).

## Counts

| Chapter | new definitions | new statements | `exists` pointers | omitted | deferred |
|---|---|---|---|---|---|
| I Geometric definition (§1–§9) | 74 (+14 helpers) | 93 | 20 | 26 | 0 |
| II Distortion theorems (§1–§9) | 25 | 97 | 13 | 48 | 0 |
| III Real analysis (§1–§7) | 41 (+8 helpers) | 90 | 75 | 34 | 0 |
| IV Analytic characterization (§1–§5) | 9 | 36 | 1 | 28 | 0 |
| V Prescribed complex dilatation (§1–§7) | 8 | 59 | 15 | 53 | 0 |
| VI Quasiconformal functions (Introduction, §1–§2) | 10 | 16 | 2 | 13 | 0 |

The `exists` column counts the distinct names after `exists:` in the item bullets (as the gate does; in Chapter V
`uniqueness_theorem` is pointed to twice). For Chapters V and VI the omitted column counts the items of the `omitted:`
bullets and of the "Not stated" paragraphs of the module docstrings (bibliographic footnotes and recollections of stated
items not counted).
-/
