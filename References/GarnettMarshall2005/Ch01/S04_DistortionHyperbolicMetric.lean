import References.GarnettMarshall2005.Ch01.S03_CaratheodoryTheorem
import References.Pommerenke1992.Ch01.S02_ConformalMaps
import References.Pommerenke1992.Ch01.S03_KoebeDistortionTheorem
import References.Pommerenke1992.Ch04.S06_HyperbolicMetric

/-!
# Garnett–Marshall, Chapter I §4: Distortion and the hyperbolic metric

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. I §4 (pp. 16–23;
`full.md` P1:854–1179).

Conventions as in §1–§3. The results of this section are planar: domains are open connected subsets of `ℂ`, a
conformal mapping of `U` onto `V` is `LiZhongQC.IsConformalOnto φ U V`, and a simply connected domain `Ω ⊆ ℂ` is
`LehtoVirtanen1973.IsSimplyConnectedDomain (toExt Ω)` (a domain whose complement in `ℂ*` is connected).
`dist(w, ∂Ω)` is `Metric.infDist w (frontier Ω)` with the boundary taken in `ℂ`: the point `∞` of the `ℂ*`-boundary
of an unbounded domain is at infinite distance and does not change the infimum. The distance of two sets is the
helper `setDist`. A univalent function in `𝔻` is analytic and one-to-one on `𝔻` (`DifferentiableOn ℂ ψ unitDisc`,
`InjOn ψ unitDisc`); the normalization (4.6) is `ψ 0 = 0`, `deriv ψ 0 = 1`, and its coefficient
`a₂ = ψ''(0)/2` is `Pommerenke1992.sCoeff ψ 2`. The hyperbolic distance `ρ = ρ_𝔻` of (4.1) (density
`1/(1 − |z|²)`, curvature `−4`) is `Pommerenke1992.hypDistD`; `ρ_Ω` and `Q_Ω` are `Pommerenke1992.hypDistG` and
`Pommerenke1992.quasihypDist`. These real-valued distances are junk (`0`) off the domain of discourse, so every
statement takes its points in `𝔻` or in `Ω`. The parameter `λ` of the Koebe functions is written `lam`.

* Definition ((4.1), the hyperbolic distance `ρ(z₁, z₂) = ρ_𝔻(z₁, z₂)` on `𝔻`, §4) — exists:
  `Pommerenke1992.hypDistD` (the infimum over rectifiable curves in the unit disc from z₁ to z₂ of the integral of
  |dz|/(1 − |z|²), the book's normalization; arcs and rectifiable curves give the same infimum, since a curve can
  be shortened to an arc and a non-rectifiable arc has infinite hyperbolic length; the book's term hyperbolic
  metric, P1:882, is the infinitesimal form |dz|/(1 − |z|²) of this distance, the integrand of the infimum)
* Definition (the set `𝓜` of conformal self-maps `T(z) = λ(z − a)/(1 − āz)`, `a ∈ 𝔻`, `|λ| = 1`, of `𝔻`, §4) —
  exists: `LiZhongQC.IsConformalOnto` `LiZhongQC.exists_rotation_blaschke_of_isConformalOnto_unitDisc`
  `LiZhongQC.isConformalOnto_blaschke` `LiZhongQC.isConformalOnto_rot` (the book defines 𝓜 as the conformal self-maps
  of the disc, the maps T with IsConformalOnto T of the unit disc onto itself; the second declaration proves that each
  of them is c(z − a)/(1 − ā z) with |c| = 1, |a| < 1, and the last two that these maps are conformal self-maps)
* Formula (4.2) (§4) — exists: `Pommerenke1992.eq1_2_7` (ρ(T(z₁), T(z₂)) = ρ(z₁, z₂) for every conformal self-map T
  of the unit disc and z₁, z₂ in the disc: the same statement)
* Formula (4.3) (§4) — exists: `Pommerenke1992.eq1_2_8` (the same formula for z₁, z₂ in the unit disc, with
  |(z₂ − z₁)/(1 − z̄₁z₂)| written |z₁ − z₂|/|1 − z̄₁z₂|: the norm of a quotient and |z₂ − z₁| = |z₁ − z₂|)
* Definition (the hyperbolically shortest curve, or geodesic, from `z₁` to `z₂` in `𝔻`, §4, P1:906) —
  `IsHypGeodesicDisc`
* Unlabelled (§4, P1:906): the geodesic from `z₁` to `z₂` is a segment of a diameter of `𝔻` or an arc of a circle
  in `𝔻` orthogonal to `∂𝔻` — `hypGeodesic_disc`
* Formula (4.4) (§4): the hyperbolic ball `B = {z : ρ(z, a) < d}` is the euclidean disc
  `{z : |(z − a)/(1 − āz)| < t}`, `t = tanh d`, of euclidean radius `r(a, d)` — `eq1_4_4`
* Formula (4.5) (§4): the euclidean distance `dist(B, ∂𝔻)` — `eq1_4_5`
* Definition (univalent function in `𝔻`, and the normalization (4.6) `ψ(z) = z + a₂z² + ⋯`, §4) — exists:
  `LiZhongQC.knHyp` `Pommerenke1992.sCoeff` (a univalent function, analytic and one-to-one on the unit disc, with
  ψ(0) = 0 and ψ′(0) = 1, which is (4.6), is knHyp; the coefficient a₂ is sCoeff ψ 2 = ψ″(0)/2; the statements write
  the four conditions out, as the book does)
* Definition ((4.7), the Koebe functions `ψ_λ(z) = z/(1 − λz)²`, `|λ| = 1`, §4) — `koebeFunction`
* Theorem 4.1 (Koebe one-quarter theorem, §4), (4.8) `|a₂| ≤ 2` — exists: `Pommerenke1992.eq1_3_11`,
  `LiZhongQC.koebe_bieberbach` (the latter is exactly |ψ″(0)| ≤ 4, i.e. |a₂| ≤ 2; the former at n = 2: for
  ψ analytic and one-to-one on the unit disc with ψ(0) = 0 and ψ′(0) = 1, the bound |a₂| ≤ 2 with a₂ = sCoeff ψ 2;
  the declaration states |a_n| ≤ n for every n ≥ 2 under the same hypotheses, a stronger conclusion)
* Theorem 4.1 (Koebe one-quarter theorem, §4), (4.9) `dist(0, ∂ψ(𝔻)) ≥ 1/4` — exists: `Pommerenke1992.cor1_4` (at
  z = 0: for ψ analytic and one-to-one on the unit disc, (1/4)|ψ′(0)| ≤ dist(ψ(0), ∂ψ(𝔻)); with ψ(0) = 0 and
  ψ′(0) = 1 this is (4.9); the declaration needs no normalization)
* Theorem 4.1 (Koebe one-quarter theorem, §4), the equality clause — `thm1_4_1_eq`
* Lemma 4.2 (area theorem, §4) — `lemma1_4_2`
* Theorem 4.3 (Koebe's estimate, §4), (4.13) — exists: `Pommerenke1992.cor1_4` (for φ analytic and one-to-one on
  the unit disc and z in the disc, (1/4)|φ′(z)|(1 − |z|²) ≤ dist(φ(z), ∂φ(𝔻)) ≤ |φ′(z)|(1 − |z|²); with
  Ω = φ(𝔻) this is (4.13); the hypotheses are weaker, as simple connectivity of Ω is not assumed; the boundary is
  taken in the plane, and the point ∞ of the boundary in the extended plane does not change the distance)
* Corollary 4.4 (§4), (4.14) — `cor1_4_4`
* Definition (the hyperbolic distance `ρ_Ω` of a simply connected domain `Ω ≠ ℂ`, §4, P1:1081–1087) — exists:
  `Pommerenke1992.hypDistG` (ρ_Ω(φ(z₁), φ(z₂)) = ρ_𝔻(z₁, z₂) for a conformal map φ of the unit disc onto Ω, written
  as the value over all such maps and preimages: the same definition and normalization)
* Unlabelled (§4, P1:1087): by (4.2), `ρ_Ω(w₁, w₂)` does not depend on the choice of the conformal map `φ` — exists:
  `Pommerenke1992.hypDistG_eq` (ρ_Ω(φ(z₁), φ(z₂)) = ρ_𝔻(z₁, z₂) for every conformal map φ of the unit disc onto Ω
  and all z₁, z₂ in the disc: the same statement)
* Definition (the quasihyperbolic distance `Q_Ω(w₁, w₂)`, §4, P1:1087–1091) — exists: `Pommerenke1992.quasihypDist`
  (the infimum over rectifiable curves in Ω from w₁ to w₂ of the integral of |dw|/dist(w, ∂Ω): the same
  definition; arcs and rectifiable curves give the same infimum)
* Formula (4.15) (§4) — exists: `Pommerenke1992.eq4_6_6` (ρ_Ω(w₁, w₂) ≤ Q_Ω(w₁, w₂) ≤ 4ρ_Ω(w₁, w₂) for w₁, w₂ in
  Ω, where Ω is the image of a conformal map of the unit disc: by the Riemann mapping theorem these are exactly the
  book's simply connected domains Ω ≠ ℂ, on which ρ_Ω is defined; the same inequalities)
* Definition (Whitney squares of a proper open subset `Ω` of `ℂ`, conditions (i)–(iii), §4, P1:1110–1118) —
  `IsWhitneyFamily`
* Unlabelled (§4, P1:1110–1116): every proper open subset of `ℂ` has Whitney squares — `exists_whitneyFamily`
* Unlabelled (§4, P1:1120): Whitney squares are almost conformally invariant: the constant `M` for `φ(T_k)` and
  `φ⁻¹(S_k)`, and `M(d)` for hyperbolic balls of radius `d` — `whitney_conformal_i`, `whitney_conformal_ii`
* Theorem 4.5 (§4), (4.16), the growth theorem — exists: `Pommerenke1992.thm1_3` (for ψ analytic and one-to-one on
  the unit disc and z in the disc, its first two inequalities have the factors |ψ′(0)| and ψ(z) − ψ(0); with
  ψ(0) = 0 and ψ′(0) = 1 they are (4.16); the declaration needs no normalization)
* Theorem 4.5 (§4), (4.17), the distortion theorem — exists: `Pommerenke1992.thm1_3` (its last two inequalities,
  which with ψ′(0) = 1 are (4.17))
* Theorem 4.5 (§4), (4.18) — `thm1_4_5_c`
* Formula (4.20) (§4, in the proof of Theorem 4.5, P1:1157; cited as a result in App. L, P3:6042) — exists:
  `LiZhongQC.kb_koebe_transform_ineq` (for f analytic and one-to-one on the unit disc, with no normalization, and z
  in the disc: |(1 − |z|²) f″(z)/f′(z) − 2 z̄| ≤ 4; for z = r e^{iθ}, multiplying the expression inside the modulus
  by the unimodular e^{iθ}, using e^{iθ} z̄ = |z|, and dividing by 1 − |z|² > 0 gives (4.20); these are the only
  differences)

Helper (not a book notion): `setDist` (the euclidean distance `dist(A, B)` of two plane sets, used in (4.5) and in
condition (iii) of the Whitney squares).

Not stated (inventory U−, immediate or used only in proofs): the identity `|T'(z)|/(1 − |T(z)|²) = 1/(1 − |z|²)` for
`T ∈ 𝓜` (P1:870–872, the step to (4.2); it is `Pommerenke1992.eq1_2_3`); the radius `[0, w]` is the shortest arc
from `0` and `ρ(0, w) = ½ log((1 + |w|)/(1 − |w|))` (P1:891–898, the case `z₁ = 0` of (4.3)); the identity
`|(z₂ − z₁)/(1 − z̄₁z₂)| = tanh ρ(z₁, z₂)` and the notation `t = t(d) = tanh d` (P1:908–918, algebra from (4.3));
the remark that for fixed `d` the distance to `∂𝔻` and the diameter of a hyperbolic ball are comparable to
`dist(a, ∂𝔻)`, and that its euclidean centre is not `a` (P1:938); the power series of `ψ_λ` and the slit image
`ψ_λ(𝔻)` (P1:955–961, not cited; `LiZhongQC.koebeFn_image` is the case `λ = 1`); (4.10), a step of the proof of
Theorem 4.1; the infinitesimal form of (4.13) used for (4.15) (P1:1093–1097; it is `Pommerenke1992.eq4_6_5`) and the
remark after (4.15) that the geometry of hyperbolic balls near `∂𝔻` persists approximately in every simply connected
domain (P1:1108); the construction of Whitney squares and the universal constants `c₁ < c₂` such that every Whitney
square of `𝔻` contains a hyperbolic ball of radius `c₁` and lies in one of radius `c₂` (P1:1118, not cited);
(4.19) and (4.21), steps of the proof of Theorem 4.5, and the remark that equality anywhere in (4.16)–(4.18) or
(4.21) forces a Koebe function (P1:1178, not cited); the citation "by the proof of the area theorem" in V
(P1:7270) is a citation of a method, not of a result.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (toExt unitDisc IsConformalOnto IsPathIn LRCurve)
open LehtoVirtanen1973 (IsSimplyConnectedDomain)
open Pommerenke1992 (hypDistD nonEuclideanSegment sCoeff hypDistG)

/-- **Definition** (the hyperbolic geodesic of `𝔻`, Ch. I §4, P1:906). A hyperbolically shortest curve, or geodesic,
from `z₁` to `z₂`: a curve `γ` in `𝔻` from `z₁` to `z₂` whose hyperbolic length `∫_γ |dz|/(1 − |z|²)` equals the
hyperbolic distance `ρ(z₁, z₂)` of (4.1), the infimum of these lengths.
Modelling: curves are the project's rectifiable curves (`LiZhongQC.LRCurve`, Lipschitz on `[0, 1]` by
`LiZhongQC.IsPathIn`), and the hyperbolic length is `LRCurve.rhoLength` for the density `1/(1 − |z|²)`, as in
`Pommerenke1992.hypDistD`. -/
def IsHypGeodesicDisc (γ : LRCurve) (z₁ z₂ : ℂ) : Prop :=
  IsPathIn unitDisc z₁ z₂ γ ∧
    γ.rhoLength (fun z => ENNReal.ofReal (1 / (1 - ‖z‖ ^ 2))) = ENNReal.ofReal (hypDistD z₁ z₂)

/-- **Unlabelled** (Ch. I §4, P1:906; the geodesics of `𝔻` recur in Ch. VII–X). For `z₁, z₂ ∈ 𝔻`, the hyperbolically
shortest curve, or the geodesic, from `z₁` to `z₂` is a segment of a diameter of `𝔻` or an arc of a circle in `𝔻`
orthogonal to `∂𝔻`.
Modelling: "the" shortest curve is read as: a geodesic exists, and the point set of every geodesic is the arc from
`z₁` to `z₂` of the line or circle through `z₁` and `z₂` orthogonal to `∂𝔻`, which is
`Pommerenke1992.nonEuclideanSegment z₁ z₂` (the image of the radius `[0, T(z₂)]`, `T(z) = (z − z₁)/(1 − z̄₁z)`,
under `T⁻¹`: a segment of a diameter when `0`, `z₁`, `z₂` are collinear, else an arc of a circle orthogonal to
`∂𝔻`). -/
theorem hypGeodesic_disc {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitDisc) (h₂ : z₂ ∈ unitDisc) :
    (∃ γ : LRCurve, IsHypGeodesicDisc γ z₁ z₂) ∧
      ∀ γ : LRCurve, IsHypGeodesicDisc γ z₁ z₂ → γ.closedTrace = nonEuclideanSegment z₁ z₂ := by
  sorry

/-- **Formula (4.4)** (Ch. I §4, P1:920–932; cited at P1:1108). For `a ∈ 𝔻`, the hyperbolic ball (so named at
P1:920)
`B = {z : ρ(z, a) < d}` is the euclidean disc `{z : |(z − a)/(1 − āz)| < t}`, `t = t(d) = tanh d`, and `B` has
euclidean radius (4.4) `r(a, d) = t(1 − |a|²)/(1 − t²|a|²)`.
Modelling: the points of both sets are taken in `𝔻`: off `𝔻` the value of `hypDistD` is junk (`0`), and at
`z = 1/ā` the quotient divides by zero; for the other `|z| ≥ 1` the quotient has modulus `≥ 1 > t`, so the book's
disc lies in `𝔻` anyway. "Euclidean disc of radius `r(a, d)`" is `B = ball c (r(a, d))` for some centre `c` (the
book remarks that `c ≠ a` for `a ≠ 0`). No sign condition on `d` is needed (for `d ≤ 0` both sides are empty). The
radius was checked against the equation image. -/
theorem eq1_4_4 {a : ℂ} (ha : a ∈ unitDisc) (d : ℝ) :
    {z ∈ unitDisc | hypDistD z a < d} = {z ∈ unitDisc | ‖(z - a) / (1 - conj a * z)‖ < Real.tanh d} ∧
      ∃ c : ℂ, {z ∈ unitDisc | hypDistD z a < d} =
        ball c (Real.tanh d * (1 - ‖a‖ ^ 2) / (1 - Real.tanh d ^ 2 * ‖a‖ ^ 2)) := by
  sorry

/-- The euclidean distance `dist(A, B) = inf {|a − b| : a ∈ A, b ∈ B}` of two plane sets (helper, not a book
notion). Junk: `0` when `A` or `B` is empty; never used there. -/
def setDist (A B : Set ℂ) : ℝ :=
  ⨅ a : A, infDist (a : ℂ) B

/-- **Formula (4.5)** (Ch. I §4, P1:934; cited at P1:1108). For `a ∈ 𝔻` and `d > 0`, the hyperbolic ball
`B = {z : ρ(z, a) < d}` has euclidean distance to `∂𝔻`
(4.5) `dist(B, ∂𝔻) = ((1 − t)/(1 + |a|t))(1 − |a|)`, `t = tanh d`.
Modelling: `d > 0` is added (junk): for `d ≤ 0` the ball is empty and has no distance to `∂𝔻` (the helper `setDist`
is `0` there); the book's hyperbolic balls have positive radius. The points of `B` are taken in `𝔻`, as in
`eq1_4_4`. The constants were checked against the equation image. -/
theorem eq1_4_5 {a : ℂ} (ha : a ∈ unitDisc) {d : ℝ} (hd : 0 < d) :
    setDist {z ∈ unitDisc | hypDistD z a < d} (sphere 0 1) =
      (1 - Real.tanh d) / (1 + ‖a‖ * Real.tanh d) * (1 - ‖a‖) := by
  sorry

/-- **Definition** (the Koebe functions, (4.7), Ch. I §4, P1:949–953). `ψ_λ(z) = z/(1 − λz)²` with `|λ| = 1`. The
parameter `λ` is written `lam`, and `|λ| = 1` is imposed where the Koebe functions are used. Junk: the value `0` at
the pole `z = 1/λ` (division by zero), which lies on `∂𝔻` when `|λ| = 1`; never used there. The project's
`LiZhongQC.koebeFn` is `ψ_1`. -/
def koebeFunction (lam z : ℂ) : ℂ :=
  z / (1 - lam * z) ^ 2

/-- **Theorem 4.1** (Koebe one-quarter theorem, Ch. I §4), the equality clause. Assume `ψ(z)` is a univalent function
on `𝔻` of the form (4.6) `ψ(z) = z + a₂z² + ⋯`. Equality holds in (4.8) `|a₂| ≤ 2` or in (4.9)
`dist(0, ∂ψ(𝔻)) ≥ 1/4` if and only if `ψ` is a Koebe function (4.7).
Modelling: the clause is read for each inequality: `|a₂| = 2` if and only if `ψ = ψ_λ` on `𝔻` for some `|λ| = 1`,
and `dist(0, ∂ψ(𝔻)) = 1/4` if and only if the same holds (the proof shows "equality in either implies a Koebe
function", P1:1017). `a₂ = ψ''(0)/2` is `Pommerenke1992.sCoeff ψ 2`; `∂ψ(𝔻)` is the boundary in `ℂ`, nonempty
since `ψ(𝔻) ≠ ℂ`. The inequalities (4.8) and (4.9) themselves are `Pommerenke1992.eq1_3_11` and
`Pommerenke1992.cor1_4`. -/
theorem thm1_4_1_eq {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ unitDisc) (hinj : InjOn ψ unitDisc) (h0 : ψ 0 = 0)
    (h1 : deriv ψ 0 = 1) :
    (‖sCoeff ψ 2‖ = 2 ↔ ∃ lam : ℂ, ‖lam‖ = 1 ∧ EqOn ψ (koebeFunction lam) unitDisc) ∧
      (infDist 0 (frontier (ψ '' unitDisc)) = 1 / 4 ↔
        ∃ lam : ℂ, ‖lam‖ = 1 ∧ EqOn ψ (koebeFunction lam) unitDisc) := by
  sorry

/-- **Lemma 4.2** (area theorem, Ch. I §4; cited in Ch. V, P1:7270, and Ch. X, P2:8567). If the univalent function
`F(z)` satisfies (4.11) `F(z) = 1/z + Σ_{n=1}^∞ b_n zⁿ`, then (4.12) `Σ_{n=1}^∞ n|b_n|² ≤ 1`.
Modelling: `F` is the `ℂ*`-valued function on `𝔻` with the pole `F(0) = ∞`. It is written as a function `ℂ → ℂ`
on `𝔻 \ {0}`, where the expansion (4.11) converges (so `F − 1/z` extends analytically to `𝔻`), and its univalence
in `𝔻` is injectivity on `𝔻 \ {0}` (the pole is the only preimage of `∞`). The coefficients are `b : ℕ → ℂ` with
`b 0 = 0`, as (4.11) has no constant term (the form with a constant term `b₀`, applied in Ch. X, P2:8567, is the
lemma for `F − b₀`). The series (4.12) is summed in `[0, ∞]`, where it always has a value
(its `n = 0` term is `0`). The inequality was checked against the equation image. `Pommerenke1992.area_theorem` is
the same inequality for the class `Σ` on `|ζ| > 1` (after `ζ = 1/z`), with contour-integral coefficients. -/
theorem lemma1_4_2 {F : ℂ → ℂ} {b : ℕ → ℂ} (hb0 : b 0 = 0)
    (hF : ∀ z ∈ unitDisc, z ≠ 0 → HasSum (fun n : ℕ => b n * z ^ n) (F z - z⁻¹))
    (hinj : InjOn F (unitDisc \ {0})) :
    ∑' n : ℕ, (n : ℝ≥0∞) * ‖b n‖ₑ ^ 2 ≤ 1 := by
  sorry

/-- **Corollary 4.4** (Ch. I §4; (4.14), cited only in Exercises of Ch. VII, P2:3357 and P2:3391). Let `ψ` be a
conformal mapping from a simply connected domain `Ω₁` onto a simply connected domain `Ω₂`, and let `ψ(z₀) = w₀`. Then
(4.14) `|ψ'(z₀)|/4 ≤ dist(w₀, ∂Ω₂)/dist(z₀, ∂Ω₁) ≤ 4|ψ'(z₀)|`.
Modelling: `Ω₁ ≠ ℂ` is added (meaning): the simply connected domains of this section have nontrivial boundary (they
carry the hyperbolic metric, P1:1081); for `Ω₁ = ℂ` (and then `Ω₂ = ℂ`) both distances are infinite and the ratio
is undefined, while in Lean the distance to the empty boundary is `0`. With `Ω₁ ≠ ℂ` the denominator is positive,
so the ratio is the book's. The domains are planar, `z₀ ∈ Ω₁`, and the boundaries are taken in `ℂ`. The constants
were checked against the equation image. App. I (P3:4975) calls its displayed inequality
`|(φ(w) − φ(z))/((1 − |z|²) φ′(z))| ≤ |τ|/(1 − |τ|²)`, `τ = (w − z)/(1 − z̄w)`, "the conformally invariant form of
inequality (4.14) of Chapter I"; it is the invariant form of the growth theorem (4.16), printed with the square on
the modulus only (false for the Koebe function, whose bound has `(1 − |τ|)²`) [misprint?]; recorded for App. I. -/
theorem cor1_4_4 {Ω₁ Ω₂ : Set ℂ} (hΩ₁ : IsSimplyConnectedDomain (toExt Ω₁))
    (hΩ₂ : IsSimplyConnectedDomain (toExt Ω₂)) (hne : Ω₁ ≠ univ) {ψ : ℂ → ℂ} (hψ : IsConformalOnto ψ Ω₁ Ω₂)
    {z₀ w₀ : ℂ} (hz₀ : z₀ ∈ Ω₁) (hw₀ : ψ z₀ = w₀) :
    ‖deriv ψ z₀‖ / 4 ≤ infDist w₀ (frontier Ω₂) / infDist z₀ (frontier Ω₁) ∧
      infDist w₀ (frontier Ω₂) / infDist z₀ (frontier Ω₁) ≤ 4 * ‖deriv ψ z₀‖ := by
  sorry

/-- **Definition** (Whitney squares, Ch. I §4, P1:1110–1118). For a proper open subset `Ω` of `ℂ`: a family of closed
squares `S_j` having pairwise disjoint interiors and sides parallel to the axes, such that (i) `S_j` has sidelength
`ℓ(S_j) = 2^{−n_j}`, (ii) `Ω = ⋃ S_j`, and (iii) `diam(S_j) ≤ dist(S_j, ∂Ω) < 4 diam(S_j)`. The squares `S_j` are
called Whitney squares.
Modelling: the family is a set `S` of subsets of `ℂ` (a family of squares with disjoint interiors is countable, so
this is the book's sequence `{S_j}`); `n_j ∈ ℤ`, since the squares of an unbounded `Ω` have unbounded size; the
squares need not be dyadic (Ch. X says "we may assume each `Q_j` is a dyadic square", P3:1550); `∂Ω` is the boundary
in `ℂ` and `dist(S_j, ∂Ω)` is `setDist`. [OCR] (iii) reads "dim" in the source; it is the diameter (leader check of
P1:1110–1118); whether (iii) has `<` or `≤` cannot be checked (inline formula, no image), and both readings keep
every stated result true. -/
def IsWhitneyFamily (Ω : Set ℂ) (S : Set (Set ℂ)) : Prop :=
  (∀ Q ∈ S, ∃ (n : ℤ) (x y : ℝ),
    Q = {z : ℂ | x ≤ z.re ∧ z.re ≤ x + 2 ^ (-n) ∧ y ≤ z.im ∧ z.im ≤ y + 2 ^ (-n)}) ∧
  S.PairwiseDisjoint interior ∧ Ω = ⋃₀ S ∧
  ∀ Q ∈ S, diam Q ≤ setDist Q (frontier Ω) ∧ setDist Q (frontier Ω) < 4 * diam Q

/-- **Unlabelled** (Ch. I §4, P1:1110–1116; the Whitney squares are used in Ch. X). Let `Ω` be any proper open
subset of `ℂ`. Then there exist closed squares `{S_j}` having pairwise disjoint interiors and sides parallel to the
axes such that (i)–(iii) hold: `Ω` has a family of Whitney squares. -/
theorem exists_whitneyFamily {Ω : Set ℂ} (hΩ : IsOpen Ω) (hne : Ω ≠ univ) :
    ∃ S : Set (Set ℂ), IsWhitneyFamily Ω S := by
  sorry

/-- **Unlabelled** (Ch. I §4, P1:1120, first part). Whitney squares are almost conformally invariant: assume `Ω` is
simply connected, let `φ : 𝔻 → Ω` be a conformal mapping, let `{S_j}` be the Whitney squares for `Ω` and let
`{T_k}` be the Whitney squares for `𝔻`. Then there is a constant `M`, not depending on the map `φ`, such that for
each `k`, `φ(T_k)` is contained in at most `M` squares `S_j`, and `φ⁻¹(S_k)` is contained in at most `M` squares
`T_j`.
Modelling: `∃ M, ∀ Ω φ`: `M` does not depend on `φ`, hence not on `Ω = φ(𝔻)`, and it is taken uniform over the
choice of the two Whitney families (the book speaks of "the" Whitney squares). "Contained in at most `M` squares" is
"contained in the union of at most `M` squares of the family"; `φ⁻¹(S_k)` is the preimage in `𝔻`. -/
theorem whitney_conformal_i :
    ∃ M : ℕ, ∀ (Ω : Set ℂ) (φ : ℂ → ℂ), IsSimplyConnectedDomain (toExt Ω) → IsConformalOnto φ unitDisc Ω →
      ∀ S T : Set (Set ℂ), IsWhitneyFamily Ω S → IsWhitneyFamily unitDisc T →
        (∀ Tk ∈ T, ∃ F ⊆ S, F.Finite ∧ F.ncard ≤ M ∧ φ '' Tk ⊆ ⋃₀ F) ∧
          ∀ Sk ∈ S, ∃ F ⊆ T, F.Finite ∧ F.ncard ≤ M ∧ unitDisc ∩ φ ⁻¹' Sk ⊆ ⋃₀ F := by
  sorry

/-- **Unlabelled** (Ch. I §4, P1:1120, second part). In particular, for each `d > 0`, there is `M(d)` such that every
hyperbolic ball `{z : ρ_Ω(z, a) < d}` in `Ω` is covered by `M(d)` Whitney squares.
Modelling: `∀ d > 0, ∃ M, ∀ Ω φ`: `M(d)` depends only on `d` (it comes from the constant `M` of the first part);
`Ω` is simply connected with a conformal map `φ` of `𝔻` onto `Ω`, as in the first part; `ρ_Ω` is
`Pommerenke1992.hypDistG Ω`, and the ball, centred at `a ∈ Ω`, is taken in `Ω` (off `Ω` the value is junk).
"Covered by `M(d)` Whitney squares" is "contained in the union of at most `M(d)` squares of the family". -/
theorem whitney_conformal_ii {d : ℝ} (hd : 0 < d) :
    ∃ M : ℕ, ∀ (Ω : Set ℂ) (φ : ℂ → ℂ), IsSimplyConnectedDomain (toExt Ω) → IsConformalOnto φ unitDisc Ω →
      ∀ S : Set (Set ℂ), IsWhitneyFamily Ω S → ∀ a ∈ Ω,
        ∃ F ⊆ S, F.Finite ∧ F.ncard ≤ M ∧ {z ∈ Ω | hypDistG Ω z a < d} ⊆ ⋃₀ F := by
  sorry

/-- **Theorem 4.5** (Ch. I §4), (4.18). Let `ψ(z)` be a univalent function satisfying `ψ(0) = 0` and `ψ'(0) = 1`.
Then (4.18) `(1 − |z|)/(|z|(1 + |z|)) ≤ |ψ'(z)|/|ψ(z)| ≤ (1 + |z|)/(|z|(1 − |z|))`.
Modelling: `z ∈ 𝔻`, and `z ≠ 0` is added (junk): the three members involve `1/|z|` and `1/|ψ(z)|` with `ψ(0) = 0`,
so they are undefined at `z = 0`, where Lean's division by zero would make all three `0`; for `z ≠ 0`, `ψ(z) ≠ 0`
by injectivity, so no junk value occurs. The inequalities (4.16) and (4.17) of the theorem are
`Pommerenke1992.thm1_3`. The constants were checked against the equation image. -/
theorem thm1_4_5_c {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ unitDisc) (hinj : InjOn ψ unitDisc) (h0 : ψ 0 = 0)
    (h1 : deriv ψ 0 = 1) {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    (1 - ‖z‖) / (‖z‖ * (1 + ‖z‖)) ≤ ‖deriv ψ z‖ / ‖ψ z‖ ∧
      ‖deriv ψ z‖ / ‖ψ z‖ ≤ (1 + ‖z‖) / (‖z‖ * (1 - ‖z‖)) := by
  sorry

end GarnettMarshall2005
