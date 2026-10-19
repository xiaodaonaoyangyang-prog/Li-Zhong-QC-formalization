import References.GarnettMarshall2005.Ch06.S03_AccessiblePoints
import References.Pommerenke1992.Ch06.S06_JordanCurvesAndHarmonicMeasure

/-!
# Garnett–Marshall, Chapter VI §4: Cone points and McMillan's theorem

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. VI §4 (pp. 207–212;
`full.md` of the second part, P2:939–1109).

Conventions of the section, as modelled here (Chapter VI conventions of §1–§3, leader ruling C6). `Ω ⊆ ℂ` is a plane
domain; "simply connected domain" is `Gehring1978.IsHypSimplyConnectedExt (toExt Ω)`; `φ : 𝔻 → Ω` is a conformal map,
`LiZhongQC.IsConformalOnto φ unitDisc Ω`; the boundary function `φ(ζ)` is the nontangential limit
(`HasNontangentialLimit`, Ch. I §2), and `φ(S)` for `S ⊆ ∂𝔻` is `bdryImage φ S` (§3). "`φ` has a non-zero angular
derivative at `ζ ∈ ∂𝔻`" is Definition V.5.3 for `Ω = 𝔻` with the inner normal `−ζ` (`θ = arg(−ζ)`):
`HasAngularDerivGM φ unitDisc ζ (arg (-ζ)) w L` with `L ≠ 0` (inventory C4; for the disc the truncated cones
`Γ^ε_β(ζ, arg(−ζ))` are Pommerenke's Stolz angles near `ζ`, so this is `Pommerenke1992.IsConformalAtBoundary`). `|E|`
and "almost every `ζ ∈ ∂𝔻`" refer to `arcMeasure`. `Λ₁` is linear measure `μH[1]` (leader ruling C2), and "σ-finite
`Λ₁` measure" is `SigmaFinite (μH[1].restrict K)`. Harmonic measure (leader rulings D1, B5, C6): Wiener's harmonic
measure `harmonicMeasureWiener` for a general simply connected domain (Theorem 4.2), and the Jordan-domain harmonic
measure `harmonicMeasureJordan` for the two complementary domains of a Jordan curve (the claim on `Tn(Γ)`); `ω(E)`
without a point is stated for every `z ∈ Ω` (the null sets do not depend on `z`); a comparison with `Λ₁` pulls the
measure back to `ℂ` by `.comap (↑)` (the point `∞` carries no harmonic measure).

One notion, one definition (leader ruling QC7 of the Pommerenke calibration and Fb5): the cone points, the twist
points and McMillan's twist point theorem are Pommerenke's, installed in `Pommerenke1992` Ch. 6, and are named here by
`exists:` pointers. So the set `K = K(Ω)` is `Pommerenke1992.triangleVertexSet (toExt Ω) (frontier Ω)` in the
statements.

* Unlabelled (§4, P2:941): the recall "a non-zero angular derivative makes `φ` conformal at `ζ`", the pointwise
  examples and the forward reference to Theorem 6.1 — omitted: a recall of the Chapter V claim
  (isConformalAtGM_of_hasAngularDerivGM, Ch. V §5), examples of Exercises VI.8 and V.7, a forward reference
* Definition (the sets `G` and `B`, (4.1), §4, P2:943–957) — `angDerivSet`, `zeroLiminfSet`
* Theorem 4.1 (§4) — `thm6_4_1`
* Definition (cone point; the set `K = K(Ω)` of cone points, §4, P2:967, 975–977) — exists:
  `Pommerenke1992.triangleVertexSet` (with the domain toExt Ω and the set frontier Ω: the points of the boundary that
  are the vertex of an open triangle contained in Ω; an open triangle with vertex w contains an open isosceles
  triangle with apex w, namely the one on the bisector of the angle at w with a small height, and an isosceles
  triangle is a triangle, so the book's isosceles triangles give the same set)
* Unlabelled (§4, P2:967–973): every cone point is accessible; the pointwise implication chain and the failure of its
  converses — omitted: immediate, a recall of the Chapter V claims, and examples; the first line of the chain is
  duplicated across the page break in the OCR [OCR]
* Unlabelled (§4, P2:979): `φ(G) ⊂ K` — `bdryImage_angDerivSet_subset_conePoints`
* Theorem 4.2 (McMillan, §4; (4.2)) — `thm6_4_2_a`, `thm6_4_2_b`, `thm6_4_2_c`
* Unlabelled (§4, proof of Theorem 4.2, P2:993; cited in Chapter X, P2:8079, 8125): `K` is a countable union of
  compact sets, each lying on the graph of a Lipschitz function over a line — `conePoints_subset_lipschitzGraphs`
* Definition (twist point, §4, P2:1067) — exists: `Pommerenke1992.IsTwistingAt` (Pommerenke's twisting at ζ, (6.4.9):
  the angular limit w = φ(ζ) exists and a continuous branch of arg(φ(z) − w) on the disc is unbounded above and
  below along every curve in the disc ending at ζ; this is the book's condition, since the angular limit of a
  function at ζ is its nontangential limit, the two families of cones being comparable near ζ, a curve with endpoint
  ζ is a half-open curve in the disc tending to ζ, and a continuous branch is bounded on every compact part of the
  curve, so unbounded on the curve means unbounded near ζ; the twist property is attached to ζ, as in App. I, P3:4929)
* McMillan twist point theorem (named, §4, P2:1067; proved in App. I as Theorem I.1) — exists:
  `Pommerenke1992.thm6_18` (Theorem 6.18: for f analytic and injective in the disc, at almost every t either f is
  conformal at e^{it}, which is the book's non-zero angular derivative, see the module docstring, or f is twisting at
  e^{it}; the book's "at almost every ζ of the circle minus G the map twists" is the same alternative; almost every t
  of the line is almost every ζ for arcMeasure, by periodicity; the hypotheses are weaker than the book's conformal
  map onto Ω)
* Unlabelled (§4, P2:1067): the radial image is a rectifiable arc along which the argument is unbounded, and the
  forward claim that Example 4.3 gives `|∂𝔻 \ G| = 2π` — omitted: a consequence stated in passing, not cited; the
  forward claim is example6_4_3_d
* Unlabelled (§4, P2:1069–1075; (4.4)): if the twisting holds at one `ζ₀ ∈ φ⁻¹(w)` on one curve, it holds at every
  `ζ ∈ φ⁻¹(w)` and on every curve — omitted: not cited (App. I re-derives it, P3:4929)
* Definition (tangent points `Tn(Γ)` of a Jordan curve, §4, P2:1075–1079) — `tangentPoints` (B-cand.
  Pommerenke1992.tangentPointSet, defined through the boundary map of a conformal map onto the inner domain and
  Pommerenke's corners of opening π; equal only through Theorem II.4.2-type arguments)
* Unlabelled (§4, P2:1081–1085; cited in the proof of Theorem 6.3, P2:1424, and in Chapter VII, P2:3264): `ω₁`,
  `ω₂` and `Λ₁` are in the same measure class on `Tn(Γ)` — `tangentPoints_measureClass`
* Unlabelled (§4, P2:1087–1099): Bishop's examples with `ω₁(Twi(Γ)) = 1`, `ω₂(Tn(Γ) ∪ Twi(Γ)) = 0` — omitted:
  examples (Exercise 10)
* Definition (Hausdorff dimension `dim E`, P2:1108; defined in App. D) — exists: `dimH` (leader ruling D6: the disc
  covers of App. D and the covers by sets of small diameter give comparable measures of each dimension, hence the
  same null sets and the same dimension)
* Example 4.3 (the von Koch snowflake, §4; cited in Chapter VII, P2:2272, and used in VII, VIII) —
  `kochSnowflakeDomain`, `example6_4_3_a`, `example6_4_3_b`, `example6_4_3_c`, `example6_4_3_d`

Helpers (not book notions): `kochSides` (the directed sides of the polygon `Γ_n`) and `kochPolygonDomain` (the
Jordan domain `Ω_n` bounded by `Γ_n`).

Near misses in Pommerenke1992 Ch. 6 (not pointers): Corollary 6.16 (`cor6_16`, the radial form of Theorem 4.1's
dichotomy), Proposition 6.22 (`prop6_22`, conformal points are in `Sect(f)`, the analogue of `φ(G) ⊂ K`), (6.5.3) and
Theorem 6.24 (`eq6_5_3`, `thm6_24`, the McMillan sector theorem, stated for `Sect(f)` and its image, with harmonic
measure read on the circle), and (6.6.4), (6.6.5) (`eq6_6_4`, `eq6_6_5`, the measure classes on `S`, `S*`, `T` with
Pommerenke's boundary harmonic measure).

Not stated (inventory U−, besides the omitted bullets): the uncited claims of Example 4.3 (P2:1108): `dim Γ =
log 4/log 3` and `0 < Λ_{log 4/log 3}(Γ) < ∞` (App. D, Exercise 11), "for any `ε > 0`, `Ω` contains a truncated cone
with vertex `φ(ζ)` and aperture `π − ε`" (a step), the consequences "linear measure `0`" and "harmonic measure `0`"
of the inner tangents (immediate from (b), Theorem 4.2 and `dim E < 1`), and "the three measures `Λ₁`, `ω₁`, `ω₂` are
pairwise mutually singular on `Γ`" (from §6, not cited); the construction of the proof of Theorem 4.2 (the lines
`L_n`, the sets `K_n`, `U`, `V`, `W`, (4.3)); "the von Koch snowflake is a quasicircle" (Chapter VII).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane extInf toExt unitDisc stolzAngle IsConformalOnto IsJordanCurve)
open References (IsJordanDomainExt finitePart)
open Gehring1978 (IsHypSimplyConnectedExt)
open Pommerenke1992 (triangleVertexSet)

/-- **Definition** (the set `G`, (4.1), Ch. VI §4, P2:943–947; "we permanently write"; used in §4–§6, in Chapter X §9,
P3:1226, and in App. I, P3:4925). For a conformal map `φ` of `𝔻`,
`G = {ζ ∈ ∂𝔻 : φ has non-zero angular derivative at ζ}`.
Modelling: the angular derivative is Definition V.5.3 on `𝔻` with the inner normal `−ζ` (`θ = arg(−ζ)`), with a
nontangential limit `φ(ζ) = w` and a finite derivative `L ≠ 0` (module docstring). Only the values of `φ` on `𝔻`
near `ζ` are read. -/
def angDerivSet (φ : ℂ → ℂ) : Set ℂ :=
  {ζ ∈ sphere (0 : ℂ) 1 | ∃ w L : ℂ, L ≠ 0 ∧ HasAngularDerivGM φ unitDisc ζ (arg (-ζ)) w L}

/-- **Definition** (the set `B`, (4.1), Ch. VI §4, P2:949–957; recalled in §6, P2:1300–1306). For a conformal map `φ`
of `𝔻`, `B = {ζ ∈ ∂𝔻 : φ has a nontangential limit at ζ, and liminf_{Γ_α(ζ) ∋ z → ζ} |φ′(z)| = 0 for all α > 1}`.
Modelling: the nontangential limit is finite (`HasNontangentialLimit`, Ch. I §2); the lower limit is taken in
`[0, ∞]` along the filter `𝓝[Γ_α(ζ)] ζ` (`Γ_α(ζ) = LiZhongQC.stolzAngle ζ α`), so no junk value is read; `φ′` is
`deriv φ`, read only on `𝔻`. -/
def zeroLiminfSet (φ : ℂ → ℂ) : Set ℂ :=
  {ζ ∈ sphere (0 : ℂ) 1 | (∃ w : ℂ, HasNontangentialLimit φ ζ w) ∧
    ∀ α : ℝ, 1 < α → liminf (fun z => ‖deriv φ z‖ₑ) (𝓝[stolzAngle ζ α] ζ) = 0}

/-- **Theorem 4.1** (Ch. VI §4; cited in the proof of Theorem 6.1, P2:1392, and in App. I, P3:4941). Let `φ` be a
univalent function on `𝔻`. Then `G ∩ B = ∅` and `|G ∪ B| = 2π`.
Modelling: "univalent on `𝔻`" is analytic and injective on `𝔻`; `|G ∪ B|` is the (outer) `arcMeasure`. -/
theorem thm6_4_1 {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) (hinj : InjOn φ unitDisc) :
    Disjoint (angDerivSet φ) (zeroLiminfSet φ) ∧
      arcMeasure (angDerivSet φ ∪ zeroLiminfSet φ) = ENNReal.ofReal (2 * π) := by
  sorry

/-- **Unlabelled** (Ch. VI §4, P2:979, "Then it is clear that `φ(G) ⊂ K`"; recalled before Theorem 6.1, P2:1314, used
in its proof, P2:1392, and in App. I, P3:4929). For a conformal map `φ` of `𝔻` onto `Ω`, `φ(G) ⊂ K`: the boundary
value at a point where `φ` has a non-zero angular derivative is a cone point of `Ω`.
Modelling: `φ(G)` is `bdryImage φ (angDerivSet φ)` (§3); `K` is `Pommerenke1992.triangleVertexSet (toExt Ω)
(frontier Ω)` (module docstring). -/
theorem bdryImage_angDerivSet_subset_conePoints {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ unitDisc Ω) :
    bdryImage φ (angDerivSet φ) ⊆ triangleVertexSet (toExt Ω) (frontier Ω) := by
  sorry

/-- **Theorem 4.2** (McMillan, Ch. VI §4), first part (cited at P2:1067, 1081, 1108, 1392, 1424, 1478, 1508, in
Chapter X, P3:676, and in App. K, P3:5898, printed "Theorem V.4.2" [misprint]). Let `Ω` be a bounded simply connected
domain. Then the set `K` of cone points is a Borel set, with σ-finite `Λ₁` measure.
Modelling: `K` as in the module docstring; Borel is `MeasurableSet` in `ℂ`; σ-finite `Λ₁` measure is
`SigmaFinite (μH[1].restrict K)` (the union of countably many sets of finite linear measure, as in Pommerenke §6.2). -/
theorem thm6_4_2_a {Ω : Set ℂ} (hΩb : Bornology.IsBounded Ω) (hΩ : IsHypSimplyConnectedExt (toExt Ω)) :
    MeasurableSet (triangleVertexSet (toExt Ω) (frontier Ω)) ∧
      SigmaFinite ((μH[1] : Measure ℂ).restrict (triangleVertexSet (toExt Ω) (frontier Ω))) := by
  sorry

/-- **Theorem 4.2** (McMillan, Ch. VI §4), second part, (4.2). Let `Ω` be a bounded simply connected domain. When
`E ⊂ K`, `ω(E) = 0 ⟺ Λ₁(E) = 0`.
Modelling: `ω(E) = ω(z, E, Ω)` is Wiener's harmonic measure (Ch. III §5) of `E ⊆ ∂Ω ⊆ ℂ*`, for every `z ∈ Ω` (module
docstring); `E` is any subset of `K` (outer measures on both sides; `K` is Borel by the first part, and both measures
are Borel regular, so the statement for Borel `E` gives it for all `E`). -/
theorem thm6_4_2_b {Ω : Set ℂ} (hΩb : Bornology.IsBounded Ω) (hΩ : IsHypSimplyConnectedExt (toExt Ω)) {z : ℂ}
    (hz : z ∈ Ω) {E : Set ℂ} (hE : E ⊆ triangleVertexSet (toExt Ω) (frontier Ω)) :
    harmonicMeasureWiener (toExt Ω) (z : ExtPlane) (toExt E) = 0 ↔ μH[1] E = 0 := by
  sorry

/-- **Theorem 4.2** (McMillan, Ch. VI §4), third part. Let `Ω` be a bounded simply connected domain. Moreover, at
almost every `w ∈ K`, `∂Ω` has an inner tangent.
Modelling: "almost every" is for `Λ₁` (the proof: `∂Ω` has an inner tangent at `Λ₁`-almost every point of the Lipschitz
curves `Γ_{n,j}`), equivalently for `ω` by the second part; the inner tangent is Definition V.5.1 with some inner
normal `e^{iθ}`. -/
theorem thm6_4_2_c {Ω : Set ℂ} (hΩb : Bornology.IsBounded Ω) (hΩ : IsHypSimplyConnectedExt (toExt Ω)) :
    ∀ᵐ w ∂((μH[1] : Measure ℂ).restrict (triangleVertexSet (toExt Ω) (frontier Ω))),
      ∃ θ : ℝ, HasInnerTangent Ω w θ := by
  sorry

/-- **Unlabelled** (Ch. VI §4, proof of Theorem 4.2, P2:993; cited as a result in Chapter X, P2:8079, "In Chapter VI
we proved that `Tn(Γ) = ⋃ K_n` where, after an affine transformation, `K_n = {y = f(x) = g(x)}`, `f` and `g`
Lipschitz", and P2:8125, "the construction in Chapter VI"). Let `Ω` be a bounded simply connected domain. Then
`K = ⋃_n K_n` with `K_n` compact, and each `K_n` lies on the graph, over a line `L_n`, of a Lipschitz function:
after a rotation `L_n` is horizontal and `K_n` lies on the graph of a Lipschitz function defined on `L_n`.
Modelling: the line `L_n` is `{c_n + u_n x : x ∈ ℝ}` with `|u_n| = 1`, and the graph of `g_n : ℝ → ℝ` over it is
`{c_n + u_n (x + i g_n(x))}`; the book's `K_n` (vertices of triangles with base on `L_n`) meet both sides of `L_n`,
and the graphs are the `Γ_{n,j} ∖ L_n`, so the pieces here are the book's `K_n` split by side (each part is compact,
at distance `≥ 1/n` from `L_n`), reindexed by `ℕ`; "borderline" U+ (a step of a proof, cited as a result, inventory
§C8). -/
theorem conePoints_subset_lipschitzGraphs {Ω : Set ℂ} (hΩb : Bornology.IsBounded Ω)
    (hΩ : IsHypSimplyConnectedExt (toExt Ω)) :
    ∃ (Kn : ℕ → Set ℂ) (c u : ℕ → ℂ) (g : ℕ → ℝ → ℝ),
      triangleVertexSet (toExt Ω) (frontier Ω) = ⋃ n, Kn n ∧
        ∀ n, IsCompact (Kn n) ∧ ‖u n‖ = 1 ∧ (∃ L : ℝ≥0, LipschitzWith L (g n)) ∧
          Kn n ⊆ {w : ℂ | ∃ x : ℝ, w = c n + u n * ((x : ℂ) + (g n x : ℂ) * I)} := by
  sorry

/-- **Definition** (tangent points, Ch. VI §4, P2:1075–1079; used in the proof of Theorem 6.3, in (6.6), Corollary 6.4,
and in Chapter X §2, P2:8079, 8155). For a Jordan curve `Γ` of `ℂ*`,
`Tn(Γ) = {w ∈ Γ : Γ has a tangent at w}`.
Modelling: `Γ : Set ℂ*`; the tangent at a finite point `w` is `HasTangentAtPoint Γ w` (§1: (II.4.1), (II.4.2) for a
loop parametrization of `Γ`); the point `∞` (on a curve through `∞`) is excluded, a point of linear measure `0`.
Near miss: `Pommerenke1992.tangentPointSet`, defined through the boundary map of a conformal map onto the inner
domain. -/
def tangentPoints (Γ : Set ExtPlane) : Set ℂ :=
  {w : ℂ | (w : ExtPlane) ∈ Γ ∧ HasTangentAtPoint Γ w}

/-- **Unlabelled** (Ch. VI §4, P2:1081–1085; cited in the proof of Theorem 6.3, P2:1424, "On `Tn(Γ)`,
`ω_j ≪ Λ₁ ≪ ω_j` by Theorem 4.2", and in Chapter VII, P2:3264). Let `Γ` be a Jordan curve, `Ω₁` and `Ω₂` the two
components of `ℂ* ∖ Γ`, `p_j ∈ Ω_j` and `ω_j = ω(p_j, ·, Ω_j)`. If `w ∈ Tn(Γ)` then, by Theorem II.4.2, `φ_j` is
conformal at `φ_j⁻¹(w)`; consequently, by Theorem 4.2, the three measures `ω₁`, `ω₂` and `Λ₁` are in the same
measure class on `Tn = Tn(Γ)`: `χ_Tn ω₁ ≪ χ_Tn Λ₁ ≪ χ_Tn ω₂ ≪ χ_Tn ω₁`.
Modelling: the two components are two disjoint Jordan domains `Ω₁`, `Ω₂` of `ℂ*` with boundary `Γ` (each is then a
component of `ℂ* ∖ Γ`); `p_j` may be `∞`; `ω_j` is the Jordan-domain harmonic measure `harmonicMeasureJordan Ω_j p_j`
(module docstring), pulled back to `ℂ` by `.comap (↑)` for the comparison with `Λ₁ = μH[1]`; `χ_Tn μ` is
`μ.restrict (tangentPoints Γ)`. Theorem II.4.2 is stated for bounded Jordan domains; for a component containing `∞`
the claim reduces to it by a Möbius map `w ↦ 1/(w − a)`, `a ∉ Ω̄_j` (leader ruling F4; see
`isConformalAtGM_of_hasTangent`, Ch. V §5), which keeps tangents at finite points. -/
theorem tangentPoints_measureClass {Γ : Set ExtPlane} (hΓ : IsJordanCurve Γ) {Ω₁ Ω₂ : Set ExtPlane}
    (hΩ₁ : IsJordanDomainExt Ω₁ ∧ frontier Ω₁ = Γ) (hΩ₂ : IsJordanDomainExt Ω₂ ∧ frontier Ω₂ = Γ)
    (h12 : Disjoint Ω₁ Ω₂) {p₁ p₂ : ExtPlane} (hp₁ : p₁ ∈ Ω₁) (hp₂ : p₂ ∈ Ω₂) :
    ((harmonicMeasureJordan Ω₁ p₁).comap ((↑) : ℂ → ExtPlane)).restrict (tangentPoints Γ) ≪
        (μH[1] : Measure ℂ).restrict (tangentPoints Γ) ∧
      (μH[1] : Measure ℂ).restrict (tangentPoints Γ) ≪
        ((harmonicMeasureJordan Ω₂ p₂).comap ((↑) : ℂ → ExtPlane)).restrict (tangentPoints Γ) ∧
      ((harmonicMeasureJordan Ω₂ p₂).comap ((↑) : ℂ → ExtPlane)).restrict (tangentPoints Γ) ≪
        ((harmonicMeasureJordan Ω₁ p₁).comap ((↑) : ℂ → ExtPlane)).restrict (tangentPoints Γ) := by
  sorry

/-- The directed sides of the polygon `Γ_n` of Example 4.3 (helper, Ch. VI §4, P2:1101–1105). `Γ₀` is the triangle
with vertices `0`, `1`, `1/2 + i√3/2`, traversed counterclockwise, so that `Ω₀` lies to the left of each side. A side
`(a, b)` of `Γ_n` with `d = (b − a)/3` is replaced in `Γ_{n+1}` by the four sides `(a, a + d)`, `(a + d, p)`,
`(p, a + 2d)`, `(a + 2d, b)`, where `p = a + d + d(1/2 − i√3/2)` is the third vertex of the equilateral triangle
`T_{n,j}` on the middle third `I_{n,j} = [a + d, a + 2d]` that lies to the right of the side, away from `Ω_n`. So
`Γ_n` consists of `3·4ⁿ` segments of length `3⁻ⁿ`, and the orientation is kept. -/
def kochSides : ℕ → List (ℂ × ℂ)
  | 0 => [(0, 1), (1, 1 / 2 + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I), (1 / 2 + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I, 0)]
  | n + 1 => (kochSides n).flatMap fun s =>
      [(s.1, s.1 + (s.2 - s.1) / 3),
        (s.1 + (s.2 - s.1) / 3, s.1 + (s.2 - s.1) / 3 + (s.2 - s.1) / 3 * (1 / 2 - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I)),
        (s.1 + (s.2 - s.1) / 3 + (s.2 - s.1) / 3 * (1 / 2 - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I),
          s.1 + 2 * ((s.2 - s.1) / 3)),
        (s.1 + 2 * ((s.2 - s.1) / 3), s.2)]

/-- The Jordan domain `Ω_n` bounded by `Γ_n` in Example 4.3 (helper, Ch. VI §4, P2:1101–1105). `Ω₀` is the open
triangle with vertices `0`, `1`, `1/2 + i√3/2`; `Ω_{n+1}` is `Ω_n` together with, for each side `(a, b)` of `Γ_n`
(`kochSides n`), the open equilateral triangle `T_{n,j}` erected outside on its middle third and the open middle
third `I_{n,j}` itself (the side of `T_{n,j}` removed from the boundary). Since `T_{n,j} ∩ Ω_n = ∅` (the book's
condition), this is the domain bounded by `Γ_{n+1}`, and `Ω_{n+1} ⊃ Ω_n`. -/
def kochPolygonDomain : ℕ → Set ℂ
  | 0 => interior (convexHull ℝ {0, 1, 1 / 2 + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I})
  | n + 1 => kochPolygonDomain n ∪ ⋃ s ∈ kochSides n,
      (interior (convexHull ℝ {s.1 + (s.2 - s.1) / 3,
          s.1 + (s.2 - s.1) / 3 + (s.2 - s.1) / 3 * (1 / 2 - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I),
          s.1 + 2 * ((s.2 - s.1) / 3)}) ∪
        openSegment ℝ (s.1 + (s.2 - s.1) / 3) (s.1 + 2 * ((s.2 - s.1) / 3)))

/-- **Definition** (the von Koch snowflake domain, Example 4.3, Ch. VI §4, P2:1101–1105; used as an object in Chapter
VII, P2:2092, 2272, and Chapter VIII, P2:3595, 3751). `Ω = ⋃_n Ω_n`, the union of the increasing sequence of Jordan
domains `Ω_n` bounded by the polygons `Γ_n`; its boundary `Γ = ∂Ω` is the von Koch snowflake.
Modelling: `Ω_n` is `kochPolygonDomain n`. Near miss: the project's `LiZhongQC.koch_IsArc` (a generalized Koch arc by
a functional equation; not this construction, and no closed curve). -/
def kochSnowflakeDomain : Set ℂ :=
  ⋃ n, kochPolygonDomain n

/-- **Example 4.3** (the von Koch snowflake, Ch. VI §4), claim (a) (P2:1105). `Ω = ⋃ Ω_n` is a Jordan domain and
`∂Ω = Γ = lim Γ_n`, where the limit is taken in the Hausdorff metric.
Modelling: `Γ_n = ∂Ω_n` and `∂Ω` are frontiers in `ℂ` (all sets are bounded); the Hausdorff metric is
`Metric.hausdorffDist` (finite here: the sets are nonempty and bounded). -/
theorem example6_4_3_a :
    IsJordanDomainExt (toExt kochSnowflakeDomain) ∧
      Tendsto (fun n => hausdorffDist (frontier (kochPolygonDomain n)) (frontier kochSnowflakeDomain)) atTop
        (𝓝 0) := by
  sorry

/-- **Example 4.3** (the von Koch snowflake, Ch. VI §4), claim (b) (P2:1108; cited in Chapter VII, P2:2272, "The domain
bounded by the snowflake has an inner tangent only on a set … where dim … "). If `Ω` has an inner tangent at a point
of `Γ`, then the point lies in `E = ⋃_n (Γ ∩ Γ_n)`, and `E` is the union of a sequence of linear images of the Cantor
set with `dim E = log 2/log 3`.
Modelling: the book's "at `φ(ζ)`" (`φ` the conformal map of `𝔻` onto `Ω`) is any point of `Γ`, since `φ` extends to a
homeomorphism of the closures; the inner tangent is Definition V.5.1 with some inner normal; `dim` is `dimH` (leader
ruling D6); the description of `E` as a union of linear images of the Cantor set is the reason given, not a separate
claim. -/
theorem example6_4_3_b :
    {w : ℂ | ∃ θ : ℝ, HasInnerTangent kochSnowflakeDomain w θ} ⊆
        ⋃ n, frontier kochSnowflakeDomain ∩ frontier (kochPolygonDomain n) ∧
      dimH (⋃ n, frontier kochSnowflakeDomain ∩ frontier (kochPolygonDomain n)) =
        ENNReal.ofReal (Real.log 2 / Real.log 3) := by
  sorry

/-- **Example 4.3** (the von Koch snowflake, Ch. VI §4), claim (c) (P2:1108; cited in Chapter VII, P2:2272). The
exterior domain `Ω̃ = ℂ* ∖ Ω̄` has inner tangents only on a countable subset of `Γ`.
Modelling: the inner tangent is a notion at finite points of the plane set `ℂ ∖ Ω̄`, the finite part of `Ω̃`. -/
theorem example6_4_3_c :
    {w : ℂ | ∃ θ : ℝ, HasInnerTangent (closure kochSnowflakeDomain)ᶜ w θ}.Countable := by
  sorry

/-- **Example 4.3** (the von Koch snowflake, Ch. VI §4), claim (d) (P2:1108; the forward claim of P2:1067, "Example 4.3
below will show that we can have `|∂𝔻 ∖ G| = 2π`"). The conformal maps `φ` and `φ̃` of `𝔻` onto `Ω` and `Ω̃`
respectively have (non-zero) angular derivatives only on a set of measure `0`.
Modelling: the book derives the claim from (b), (c) and Theorem 4.2 through `φ(G) ⊂ K` and the inner tangents, so
"angular derivative" is the non-zero one of `G = angDerivSet` (the form cited at P2:1067). The exterior map `φ̃` has
a pole at the point of `𝔻` sent to `∞`: it is a conformal map `Φ` of `𝔻` onto `Ω̃ ⊆ ℂ*`
(`LehtoVirtanen1973.IsConformalMap`), and `φ̃ : ℂ → ℂ` agrees with `Φ` at every point of `𝔻` with a finite image;
`angDerivSet` reads `φ̃` only near `∂𝔻`, away from the pole. -/
theorem example6_4_3_d :
    (∀ φ : ℂ → ℂ, IsConformalOnto φ unitDisc kochSnowflakeDomain → arcMeasure (angDerivSet φ) = 0) ∧
      ∀ (Φ : ExtPlane → ExtPlane) (φ : ℂ → ℂ), LehtoVirtanen1973.IsConformalMap Φ (toExt unitDisc) →
        Φ '' toExt unitDisc = (closure (toExt kochSnowflakeDomain))ᶜ →
        (∀ z ∈ unitDisc, Φ (z : ExtPlane) ≠ extInf → Φ (z : ExtPlane) = (φ z : ExtPlane)) →
        arcMeasure (angDerivSet φ) = 0 := by
  sorry

end GarnettMarshall2005
