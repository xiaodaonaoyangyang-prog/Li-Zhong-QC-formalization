import References.Lehto1987.Ch01.S05_TheBoundaryValueProblem
import References.Common.Quasidisk
import LiZhongQC.Ch05.S20_SchwarzDomains

/-!
# Lehto, Chapter I §6: Quasidiscs

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. I §6 (`full.md`
P1:1436–1835).

Conventions (see §1–§5): a (`K`-)quasicircle is the image of a circle under a (`K`-)quasiconformal mapping of the
plane, the project's `LiZhongQC.IsQuasicircle`, `LiZhongQC.IsKQuasicircle` (the image of the unit circle under a
`K`-quasiconformal map of `ℂ` followed by a Möbius map; its `K` is the project's `IsKQC` constant, the geometric one of
§2); a quasidisc is a Jordan domain of `ℂ̄` bounded by a quasicircle, the shared `References.IsQuasidiskExt`. "`C`
bounds `A₁` and `A₂`" is LV's `JordanCurveBounds C A₁ A₂`. The reflection `j(z) = z̄` of `ℂ̄` is
`OnePoint.map (starRingEnd ℂ)`. In §6.3–§6.5 the domains are subsets of the finite plane (P1:1542, 1654): a domain
`A ⊆ ℂ` is simply connected with more than one boundary point when `toExt A` is Gehring's
`IsHypSimplyConnectedExt`; `d(z, ∂A)` is `Metric.infDist z (frontier A)`, and the euclidean length `l(α)` of an arc is
its linear (Hausdorff `1`-) measure `μH[1]`. Linear local connectivity is the project's
`LiZhongQC.IsKLocallyConnected` and the arc condition the project's `LiZhongQC.IsBoundedTurning`. Constants
`c(K), c₁(K), …` depending only on `K` are `∀ K, ∃ c`.

* Definition (quasicircle, `K`-quasicircle, quasidisc, §6.1) — exists: `LiZhongQC.IsQuasicircle`,
  `LiZhongQC.IsKQuasicircle`, `References.IsQuasidiskExt`
* Definition (`K`-quasidisc, §6.1) — `IsKQuasidiscExt`
* Unlabelled (§6.1, P1:1444): a quasiconformal mapping of `A` agrees on a compact `F ⊂ A` with a quasiconformal
  mapping of the plane — exists: `LehtoVirtanen1973.thm2_8_1` (with a bound on the maximal dilatation depending only
  on K, A and F)
* Unlabelled (§6.1, P1:1444): quasiconformal mappings of `A` map circles in `A` onto quasicircles — `para1_6_1_b`
* Unlabelled (§6.1, P1:1446): a quasicircle has zero area — `para1_6_1_c`
* Unlabelled (§6.1, P1:1446, Gehring–Väisälä): the Hausdorff dimension of a quasicircle is less than `2`, and every
  value `λ ∈ [1, 2)` occurs — `para1_6_1_d`
* Unlabelled (§6.1, P1:1446): quasicircles all of whose subarcs are non-rectifiable exist — omitted: quoted
  examples, not cited
* Lemma 6.1 (§6.1) — `lemma1_6_1`
* Definition (`K`-quasiconformal reflection, §6.2) — `IsKQCReflection`
* Theorem 6.1 (§6.2) — `thm1_6_1`
* Unlabelled (§6.2, P1:1468): a curve with a `K`-quasiconformal reflection is a `K`-quasicircle; a `K`-quasicircle
  admits a `K²`-quasiconformal reflection — `para1_6_2`
* Lemma 6.2 (§6.2) — `lemma1_6_2_i`, `lemma1_6_2_ii`, `lemma1_6_2_iii`
* Lemma 6.3 (§6.2) — `lemma1_6_3`
* Formula (6.2) (§6.2) — `eq1_6_2`
* Formula (6.3) (§6.2) — `eq1_6_3`
* Lemma 6.4 (§6.2) — `lemma1_6_4`
* Definition (uniform domain, (6.5), (6.6), §6.3) — `IsUniformDomainWith`, `IsUniformDomain`
* Lemma 6.5 (§6.3) — `lemma1_6_5`
* Formula (6.7) (§6.3) — omitted: a step of the proof of Lemma 6.5 (Koebe's theorem at iy)
* Theorem 6.2 (§6.3) — `thm1_6_2`
* Theorem 6.3 (§6.3) — `thm1_6_3`
* Definition (linearly locally connected set, §6.4) — exists: `LiZhongQC.IsKLocallyConnected` (the conditions 1°,
  2° with a constant c ≥ 1, the points being joined by paths in the sets, which in these sets of the plane is the
  same as being joined by arcs; the book's c is at least 1 as well, since 1° with r small forces it)
* Unlabelled (§6.4, P1:1660): a linearly locally connected simply connected domain with more than one boundary point
  is a Jordan domain — `para1_6_4`
* Theorem 6.4 (§6.4) — `thm1_6_4`
* Definition (arc condition, §6.5) — exists: `LiZhongQC.IsBoundedTurning` (a Jordan curve for which one of the two
  arcs between any two finite points has diameter at most k times their distance; the arc through ∞ has infinite
  diameter, so this is the arc of smaller diameter of the book)
* Theorem 6.5 (§6.5) — `thm1_6_5`
* Definition (conjugate quadrilaterals, §6.6) — exists: `LehtoVirtanen1973.AreConjugateQuads`
* Lemma 6.6 (§6.6) — `lemma1_6_6`
* Lemma 6.7 (§6.6) — `lemma1_6_7`
* Theorem 6.6 (§6.7) — `thm1_6_6`
* Formula (6.9), (6.10) (§6.7) — omitted: steps of the proof of Theorem 6.6
* Theorem 6.7 (§6.7) — `thm1_6_7`
* Unlabelled (§6.7, P1:1828): for simply connected domains of the plane with more than one boundary point, the
  quasidiscs are exactly the domains with the hyperbolic segment property of Theorem 6.2, the uniform domains, the
  linearly locally connected domains and the Jordan domains whose boundary satisfies the arc condition —
  `para1_6_7`

Helpers (not book notions): `conjExt` (`z ↦ z̄` on `ℂ̄`) and `HasHypSegmentProperty` (the property of Theorem 6.2,
used again in `para1_6_7`).

Not stated (inventory U−): the special case "a homeomorphism `K`-quasiconformal off a straight line is
`K`-quasiconformal" (P1:1450, the reflection remark of §2.4); the half-plane and disc constants `a = b = π/2`
(P1:1606); the strip and parabola examples (P1:1656, 1698); the remark on the LLC constant `2 max(a, b) + 1`
(P1:1692) and the constant `c²` of Theorem 6.5 (P1:1716); the remark that `C` is a `c(k)`-quasicircle (P1:1802); the
direct proof of the converse of Theorem 6.6 (P1:1806); `c(K) = λ(K)` in (6.11) and the converse of Theorem 6.7
(P1:1824–1826); the remarks on domains containing `∞` (P1:1830).
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Lehto1987

open LiZhongQC (ExtPlane extInf toExt upperHalf lambdaInv IsQuasicircle IsKQuasicircle IsKLocallyConnected
  IsBoundedTurning IsJordanCurve)
open References (IsDomainExt IsJordanDomainExt finitePart IsQuasidiskExt)
open LehtoVirtanen1973 (IsKQuasiconformal IsQuasiconformalMap IsConformalMap IsHomeoOn Quadrilateral finiteMap
  finiteValue JordanCurveBounds AreConjugateQuads)
open Gehring1978 (hypDensity IsHypSimplyConnectedExt)

/-! ## §6.1 Quasicircles -/

/-- **Definition** (`K`-quasidisc, Ch. I §6.1): a domain bounded by a `K`-quasicircle, i.e. a Jordan domain of `ℂ̄`
whose boundary is a `K`-quasicircle. -/
def IsKQuasidiscExt (A : Set ExtPlane) (K : ℝ) : Prop := IsJordanDomainExt A ∧ IsKQuasicircle (frontier A) K

/-- The reflection `j(z) = z̄` of `ℂ̄` (`∞ ↦ ∞`). -/
def conjExt : ExtPlane → ExtPlane := OnePoint.map (starRingEnd ℂ)

/-- **Unlabelled** (Ch. I §6.1, P1:1444). A quasiconformal mapping `f` of a domain `A` maps circles in `A` onto
quasicircles.
Modelling: circles are the euclidean circles `|z − c| = r`, `r > 0`, contained in `A`. -/
theorem para1_6_1_b {f : ExtPlane → ExtPlane} {A : Set ExtPlane} (hf : IsQuasiconformalMap f A) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hcA : toExt (Metric.sphere c r) ⊆ A) : IsQuasicircle (f '' toExt (Metric.sphere c r)) := by
  sorry

/-- **Unlabelled** (Ch. I §6.1, P1:1446). A quasicircle has zero area. -/
theorem para1_6_1_c {C : Set ExtPlane} (hC : IsQuasicircle C) : volume (finitePart C) = 0 := by
  sorry

/-- **Unlabelled** (Ch. I §6.1, P1:1446, quoted from Gehring–Väisälä). The Hausdorff dimension of a quasicircle is
always less than `2`, and it can take any value `λ`, `1 ≤ λ < 2`.
Modelling: the Hausdorff dimension of the finite part of the curve (the point `∞` does not change it). -/
theorem para1_6_1_d :
    (∀ C : Set ExtPlane, IsQuasicircle C → dimH (finitePart C) < 2) ∧
      ∀ l : ℝ, 1 ≤ l → l < 2 → ∃ C : Set ExtPlane, IsQuasicircle C ∧ dimH (finitePart C) = ENNReal.ofReal l := by
  sorry

/-- **Lemma 6.1** (Ch. I §6.1). Let `C` be a quasicircle and `f` a homeomorphism of the plane which is
`K`-quasiconformal in the complement of `C`. Then `f` is a `K`-quasiconformal mapping of the plane.
Modelling: the complement of `C` consists of the two domains `A₁`, `A₂` bounded by `C`, and `f` is
`K`-quasiconformal in each of them. -/
theorem lemma1_6_1 {C A₁ A₂ : Set ExtPlane} (hC : IsQuasicircle C) (hB : JordanCurveBounds C A₁ A₂)
    {f : ExtPlane → ExtPlane} {K : ℝ} (hf : IsHomeoOn f univ univ) (h₁ : IsKQuasiconformal f A₁ K)
    (h₂ : IsKQuasiconformal f A₂ K) : IsKQuasiconformal f univ K := by
  sorry

/-! ## §6.2 Quasiconformal reflections -/

/-- **Definition** (`K`-quasiconformal reflection, Ch. I §6.2). Let `C` be a Jordan curve bounding the domains `A₁`
and `A₂`. A sense-reversing `K`-quasiconformal involution `φ` of the plane which maps `A₁` onto `A₂` is a
`K`-quasiconformal reflection in `C` if `φ` keeps every point of `C` fixed.
Modelling: `φ` is sense-reversing `K`-quasiconformal when `z̄ ∘ φ` is a `K`-quasiconformal mapping of the plane (as
LV's anti-quasiconformal mappings). -/
def IsKQCReflection (C A₁ A₂ : Set ExtPlane) (K : ℝ) (φ : ExtPlane → ExtPlane) : Prop :=
  JordanCurveBounds C A₁ A₂ ∧ IsKQuasiconformal (conjExt ∘ φ) univ K ∧ (∀ z, φ (φ z) = z) ∧ φ '' A₁ = A₂ ∧
    ∀ z ∈ C, φ z = z

/-- **Theorem 6.1** (Ch. I §6.2). A Jordan curve admits a quasiconformal reflection if and only if it is a
quasicircle. -/
theorem thm1_6_1 {C A₁ A₂ : Set ExtPlane} (hB : JordanCurveBounds C A₁ A₂) :
    (∃ (K : ℝ) (φ : ExtPlane → ExtPlane), IsKQCReflection C A₁ A₂ K φ) ↔ IsQuasicircle C := by
  sorry

/-- **Unlabelled** (Ch. I §6.2, P1:1468). If `C` admits a `K`-quasiconformal reflection, then `C` is a
`K`-quasicircle; a `K`-quasicircle always admits a `K²`-quasiconformal reflection. -/
theorem para1_6_2 {C A₁ A₂ : Set ExtPlane} (hB : JordanCurveBounds C A₁ A₂) (K : ℝ) :
    ((∃ φ : ExtPlane → ExtPlane, IsKQCReflection C A₁ A₂ K φ) → IsKQuasicircle C K) ∧
      (IsKQuasicircle C K → ∃ φ : ExtPlane → ExtPlane, IsKQCReflection C A₁ A₂ (K ^ 2) φ) := by
  sorry

/-- **Lemma 6.2, 1°** (Ch. I §6.2). Let `A` be a `K`-quasidisc. Every quasiconformal reflection in `∂A` is of the form
`f ∘ j ∘ f⁻¹`, where `f` is a quasiconformal mapping of the plane which maps the upper half-plane `H` conformally onto
`A`, and `j` denotes the reflection `z ↦ z̄`.
Modelling: the reflection is taken with respect to `A` and the complementary domain `(Ā)ᶜ`, with any constant `K′`;
`φ = f ∘ j ∘ f⁻¹` is written `φ ∘ f = f ∘ j` (`f` is a bijection of `ℂ̄`). -/
theorem lemma1_6_2_i {A : Set ExtPlane} {K : ℝ} (hA : IsKQuasidiscExt A K) {K' : ℝ} {φ : ExtPlane → ExtPlane}
    (hφ : IsKQCReflection (frontier A) A (closure A)ᶜ K' φ) :
    ∃ f : ExtPlane → ExtPlane, IsQuasiconformalMap f univ ∧ f '' toExt upperHalf = A ∧
      IsConformalMap f (toExt upperHalf) ∧ ∀ z, φ (f z) = f (conjExt z) := by
  sorry

/-- **Lemma 6.2, 2°** (Ch. I §6.2). A `K`-quasidisc `A` is the image of `H` under a `K²`-quasiconformal mapping `f` of
the plane which is conformal in `H`. -/
theorem lemma1_6_2_ii {A : Set ExtPlane} {K : ℝ} (hA : IsKQuasidiscExt A K) :
    ∃ f : ExtPlane → ExtPlane, IsKQuasiconformal f univ (K ^ 2) ∧ f '' toExt upperHalf = A ∧
      IsConformalMap f (toExt upperHalf) := by
  sorry

/-- **Lemma 6.2, 3°** (Ch. I §6.2). If `A` is a `K`-quasidisc, every conformal mapping `f : H → A` has a
`K²`-quasiconformal extension to the plane. -/
theorem lemma1_6_2_iii {A : Set ExtPlane} {K : ℝ} (hA : IsKQuasidiscExt A K) {f : ExtPlane → ExtPlane}
    (hf : IsConformalMap f (toExt upperHalf)) (hfA : f '' toExt upperHalf = A) :
    ∃ F : ExtPlane → ExtPlane, IsKQuasiconformal F univ (K ^ 2) ∧ EqOn F f (toExt upperHalf) := by
  sorry

/-- **Lemma 6.3** (Ch. I §6.2). Let `φ` be a `K`-quasiconformal reflection in a Jordan curve `C` which passes through
`∞` (bounding `A₁` and `A₂`). Then `|φ(z) − z| ≤ c₁(K)/η₂(φ(z))` (6.1) for `z ∈ A₁`, where `η₂` is the Poincaré
density of `A₂`.
Modelling: `∀ K, ∃ c₁`; the points `z ∈ A₁` are finite and so is `φ(z)` (`φ` fixes `∞ ∈ C`). -/
theorem lemma1_6_3 (K : ℝ) :
    ∃ c : ℝ, ∀ (C A₁ A₂ : Set ExtPlane) (φ : ExtPlane → ExtPlane), IsKQCReflection C A₁ A₂ K φ → extInf ∈ C →
      ∀ z : ℂ, (z : ExtPlane) ∈ A₁ → ‖finiteValue (φ z) - z‖ ≤ c / hypDensity A₂ (finiteValue (φ z)) := by
  sorry

/-- **Formula (6.2)** (Ch. I §6.2). In the situation of Lemma 6.3, for `z ∈ A₁` and `z₀ ∈ C`,
`|z − z₀|/c(K) ≤ |φ(z) − z₀| ≤ c(K) |z − z₀|`.
Modelling: `∀ K, ∃ c > 0`; `z` and `z₀` are finite. -/
theorem eq1_6_2 (K : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (C A₁ A₂ : Set ExtPlane) (φ : ExtPlane → ExtPlane), IsKQCReflection C A₁ A₂ K φ →
      extInf ∈ C → ∀ z : ℂ, (z : ExtPlane) ∈ A₁ → ∀ z₀ : ℂ, (z₀ : ExtPlane) ∈ C →
        ‖z - z₀‖ / c ≤ ‖finiteValue (φ z) - z₀‖ ∧ ‖finiteValue (φ z) - z₀‖ ≤ c * ‖z - z₀‖ := by
  sorry

/-- **Formula (6.3)** (Ch. I §6.2). In the situation of Lemma 6.3, `d(z, C)/λ(K) ≤ d(φ(z), C) ≤ λ(K) d(z, C)` for
`z ∈ A₁` (the book derives (6.3) with the constant of (6.2) and remarks that it can be taken to be `λ(K)`, by §2.5).
Modelling: `d(·, C)` is the distance to the finite points of `C`. -/
theorem eq1_6_3 {K : ℝ} {C A₁ A₂ : Set ExtPlane} {φ : ExtPlane → ExtPlane} (hφ : IsKQCReflection C A₁ A₂ K φ)
    (hC : extInf ∈ C) {z : ℂ} (hz : (z : ExtPlane) ∈ A₁) :
    Metric.infDist z (finitePart C) / lambdaInv K ≤ Metric.infDist (finiteValue (φ z)) (finitePart C) ∧
      Metric.infDist (finiteValue (φ z)) (finitePart C) ≤ lambdaInv K * Metric.infDist z (finitePart C) := by
  sorry

/-- **Lemma 6.4** (Ch. I §6.2, Ahlfors). Let `C` be a `K`-quasicircle bounding the domains `A₁` and `A₂` and passing
through `∞`. Then there exists a `c₂(K)`-quasiconformal reflection `φ` in `C`, continuously differentiable in `A₁` and
`A₂`, such that `|dφ(z)| ≤ c₃(K) |dz|` (6.4) at every point `z ∈ A₁`.
Modelling: `∀ K, ∃ c₂ c₃`; differentiability at the finite points (`A₁`, `A₂` do not contain `∞ ∈ C`); (6.4) bounds
the norm of the real derivative. -/
theorem lemma1_6_4 (K : ℝ) :
    ∃ c₂ c₃ : ℝ, ∀ C A₁ A₂ : Set ExtPlane, IsKQuasicircle C K → extInf ∈ C → JordanCurveBounds C A₁ A₂ →
      ∃ φ : ExtPlane → ExtPlane, IsKQCReflection C A₁ A₂ c₂ φ ∧
        ContDiffOn ℝ 1 (finiteMap φ) (finitePart A₁ ∪ finitePart A₂) ∧
        ∀ z ∈ finitePart A₁, ‖fderiv ℝ (finiteMap φ) z‖ ≤ c₃ := by
  sorry

/-! ## §6.3 Uniform domains -/

/-- **Definition** (uniform domain with constants `a`, `b`, Ch. I §6.3). Each pair of points `z₁, z₂ ∈ A` can be
joined by an arc `α` in `A` with 1° `l(α) ≤ a |z₁ − z₂|` (6.5) and 2° `min(l(α₁), l(α₂)) ≤ b d(z, ∂A)` (6.6) for every
`z ∈ α`, where `α₁` and `α₂` are the components of `α \ {z}`.
Modelling: `A` is a set of the finite plane; distinct points are joined (a Jordan arc has two distinct endpoints);
the arc is `γ([0, 1])` for an embedding `γ` of `[0, 1]`, the components of `α \ {z}` for `z = γ(s)` are measured by
the subarcs `γ([0, s])`, `γ([s, 1])` (one point more does not change their linear measure). -/
def IsUniformDomainWith (A : Set ℂ) (a b : ℝ) : Prop :=
  ∀ z₁ ∈ A, ∀ z₂ ∈ A, z₁ ≠ z₂ → ∃ γ : ℝ → ℂ, IsEmbedding ((Icc (0 : ℝ) 1).domRestrict γ) ∧ γ 0 = z₁ ∧ γ 1 = z₂ ∧
    γ '' Icc 0 1 ⊆ A ∧ μH[1] (γ '' Icc 0 1) ≤ ENNReal.ofReal (a * ‖z₁ - z₂‖) ∧
    ∀ s ∈ Icc (0 : ℝ) 1, min (μH[1] (γ '' Icc 0 s)) (μH[1] (γ '' Icc s 1)) ≤
      ENNReal.ofReal (b * Metric.infDist (γ s) (frontier A))

/-- **Definition** (uniform domain, Ch. I §6.3): there are constants `a` and `b` with (6.5) and (6.6). -/
def IsUniformDomain (A : Set ℂ) : Prop := ∃ a b : ℝ, IsUniformDomainWith A a b

/-- **Lemma 6.5** (Ch. I §6.3). Let `A` be a `K`-quasidisc with `∞ ∈ ∂A`, and `f : H → A` a conformal mapping
satisfying `f(∞) = ∞`. Then `∫₀^y |f′(it)| dt ≤ c₁(K) d(f(iy), ∂A)` for `0 < y < ∞`.
Modelling: `∀ K, ∃ c₁`; `f(∞) = ∞` is the limit of `f` at the boundary point `∞` of `H`; the integral of the
nonnegative integrand is taken in `[0, ∞]` (so its finiteness is part of the claim); `d(·, ∂A)` is the distance to
the finite boundary points. [OCR] The upper limit is printed `γ` for `y`. -/
theorem lemma1_6_5 (K : ℝ) :
    ∃ c : ℝ, ∀ (A : Set ExtPlane) (f : ExtPlane → ExtPlane), IsKQuasidiscExt A K → extInf ∈ frontier A →
      IsConformalMap f (toExt upperHalf) → f '' toExt upperHalf = A →
      Tendsto f (𝓝[toExt upperHalf] extInf) (𝓝 extInf) → ∀ y : ℝ, 0 < y →
        ∫⁻ t in Ioo (0 : ℝ) y, ENNReal.ofReal ‖deriv (finiteMap f) ((t : ℂ) * I)‖ ≤
          ENNReal.ofReal (c * Metric.infDist (finiteMap f ((y : ℂ) * I)) (finitePart (frontier A))) := by
  sorry

/-- The property of the hyperbolic segments of Theorem 6.2: every hyperbolic segment `α` of the plane domain `A`, from
`z₁` to `z₂`, satisfies (6.5) and (6.6) with the constants `a` and `b` (the components of `α \ {z}` being
those containing `z₁` and `z₂`; for `z = zᵢ` one of them is empty). -/
def HasHypSegmentProperty (A : Set ℂ) (a b : ℝ) : Prop :=
  ∀ z₁ ∈ A, ∀ z₂ ∈ A, ∀ S : Set ℂ, Pommerenke1992.IsHypGeodesicSegment A S z₁ z₂ →
    μH[1] S ≤ ENNReal.ofReal (a * ‖z₁ - z₂‖) ∧
      ∀ z ∈ S, min (μH[1] (connectedComponentIn (S \ {z}) z₁)) (μH[1] (connectedComponentIn (S \ {z}) z₂)) ≤
        ENNReal.ofReal (b * Metric.infDist z (frontier A))

/-- **Theorem 6.2** (Ch. I §6.3, Gehring–Osgood). Let `A` be a `K`-quasidisc and `α` a hyperbolic segment in `A` joining
the points `z₁` and `z₂`. Then `α` satisfies the conditions (6.5) and (6.6) with constants `a` and `b` which depend
only on `K`.
Modelling: `A` is a domain of the finite plane (the theorem is false if `∞ ∈ A`, P1:1830); `∀ K, ∃ a b`. -/
theorem thm1_6_2 (K : ℝ) :
    ∃ a b : ℝ, ∀ A : Set ℂ, IsKQuasidiscExt (toExt A) K → HasHypSegmentProperty A a b := by
  sorry

/-- **Theorem 6.3** (Ch. I §6.3). A quasidisc is a uniform domain.
Modelling: a quasidisc of the finite plane. -/
theorem thm1_6_3 {A : Set ℂ} (hA : IsQuasidiskExt (toExt A)) : IsUniformDomain A := by
  sorry

/-! ## §6.4 Linear local connectivity -/

/-- **Unlabelled** (Ch. I §6.4, P1:1660). If a simply connected domain `A` with more than one boundary point is
linearly locally connected, then `A` is a Jordan domain.
Modelling: `A` is a domain of the finite plane (the standing convention of §6.3–§6.5). -/
theorem para1_6_4 {A : Set ℂ} (hA : IsHypSimplyConnectedExt (toExt A)) (hlc : ∃ c : ℝ, IsKLocallyConnected A c) :
    IsJordanDomainExt (toExt A) := by
  sorry

/-- **Theorem 6.4** (Ch. I §6.4). A uniform domain `A` is linearly locally connected.
Modelling: `A` is a simply connected proper subdomain of the finite plane, the standing assumption of §6.3 (a
simply connected domain of `ℂ̄` with more than one boundary point, not containing `∞`). -/
theorem thm1_6_4 {A : Set ℂ} (hA : IsHypSimplyConnectedExt (toExt A)) (hu : IsUniformDomain A) :
    ∃ c : ℝ, IsKLocallyConnected A c := by
  sorry

/-! ## §6.5 Arc condition -/

/-- **Theorem 6.5** (Ch. I §6.5, Gehring). Let `A` be a simply connected domain whose boundary contains more than one
point. If `A` is linearly locally connected, then `∂A` is a Jordan curve which satisfies the arc condition.
Modelling: `A` is a domain of the finite plane, as in §6.4 (the book remarks, P1:1830, that the theorem holds in
`ℂ̄` as well; that remark is not stated). -/
theorem thm1_6_5 {A : Set ℂ} (hA : IsHypSimplyConnectedExt (toExt A)) {c : ℝ} (hlc : IsKLocallyConnected A c) :
    ∃ k : ℝ, IsBoundedTurning (frontier (toExt A)) k := by
  sorry

/-! ## §6.6 Conjugate quadrilaterals -/

/-- **Lemma 6.6** (Ch. I §6.6). Let `C` be a Jordan curve such that for all conjugate quadrilaterals `A₁`, `A₂` with
`M(A₁) = 1` we have `M(A₂) ≤ K`. Then `C` is a `c(K)`-quasicircle, where `c(K)` depends only on `K`.
Modelling: `∀ K, ∃ c`; `C` bounds `A₁` and `A₂`, and the first quadrilateral of each conjugate pair is formed from
`A₁`, as in the book (and LV II.8.5). -/
theorem lemma1_6_6 (K : ℝ) :
    ∃ c : ℝ, ∀ C A₁ A₂ : Set ExtPlane, JordanCurveBounds C A₁ A₂ →
      (∀ Q₁ Q₂ : Quadrilateral, Q₁.dom = A₁ → AreConjugateQuads C Q₁ Q₂ → Q₁.module = 1 → Q₂.module ≤ K) →
        IsKQuasicircle C c := by
  sorry

/-- **Lemma 6.7** (Ch. I §6.6). Let `Q(z₁, z₂, z₃, z₄)` be a quadrilateral with module `1`, and let `s₁` and `s₂`
denote the euclidean distances in `Q` between the sides `(z₁, z₂), (z₃, z₄)` and `(z₂, z₃), (z₄, z₁)`, respectively.
Then `s₁/s₂ > 10⁻³`.
Modelling: `s₁`, `s₂` are LV's `aDist`, `bDist` (positive and finite for every quadrilateral); the quotient
inequality is multiplied out in `[0, ∞]`. -/
theorem lemma1_6_7 (Q : Quadrilateral) (hQ : Q.module = 1) : ENNReal.ofReal (1 / 1000) * Q.bDist < Q.aDist := by
  sorry

/-! ## §6.7 Characterizations of quasidiscs -/

/-- **Theorem 6.6** (Ch. I §6.7, Ahlfors). A Jordan domain whose boundary satisfies the arc condition is a
quasidisc. -/
theorem thm1_6_6 {A : Set ExtPlane} (hA : IsJordanDomainExt A) {k : ℝ} (hk : IsBoundedTurning (frontier A) k) :
    IsQuasidiskExt A := by
  sorry

/-- **Theorem 6.7** (Ch. I §6.7). Let `C` be a `K`-quasicircle passing through `∞`, and `z₁, z₂, z₃` finite points of
`C` such that `z₂` lies between `z₁` and `z₃`. Then `|z₁ − z₂| + |z₂ − z₃| ≤ c(K) |z₁ − z₃|` (6.11).
Modelling: `∀ K, ∃ c`; "`z₂` lies between `z₁` and `z₃`" (on the arc `C \ {∞}`): `z₂` differs from `z₁`, `z₃`, and
`z₁`, `z₃` lie in different components of `C \ {z₂, ∞}`. -/
theorem thm1_6_7 (K : ℝ) :
    ∃ c : ℝ, ∀ C : Set ExtPlane, IsKQuasicircle C K → extInf ∈ C → ∀ z₁ z₂ z₃ : ℂ,
      (z₁ : ExtPlane) ∈ C → (z₂ : ExtPlane) ∈ C → (z₃ : ExtPlane) ∈ C → z₁ ≠ z₂ → z₂ ≠ z₃ →
      connectedComponentIn (C \ {(z₂ : ExtPlane), extInf}) z₁ ≠
        connectedComponentIn (C \ {(z₂ : ExtPlane), extInf}) z₃ →
      ‖z₁ - z₂‖ + ‖z₂ - z₃‖ ≤ c * ‖z₁ - z₃‖ := by
  sorry

/-- **Unlabelled** (Ch. I §6.7, P1:1828). For a simply connected domain `A` of the plane with more than one boundary
point the following are equivalent: `A` is a quasidisc; the hyperbolic segments of `A` have the property of
Theorem 6.2 for some constants; `A` is uniform; `A` is linearly locally connected; `A` is a Jordan domain whose
boundary satisfies the arc condition.
Modelling: `A` is a domain of the finite plane (uniform domains and Theorem 6.2 are for `∞ ∉ A`, P1:1830). -/
theorem para1_6_7 {A : Set ℂ} (hA : IsHypSimplyConnectedExt (toExt A)) :
    List.TFAE [IsQuasidiskExt (toExt A), ∃ a b : ℝ, HasHypSegmentProperty A a b, IsUniformDomain A,
      ∃ c : ℝ, IsKLocallyConnected A c,
      IsJordanDomainExt (toExt A) ∧ ∃ k : ℝ, IsBoundedTurning (frontier (toExt A)) k] := by
  sorry

end Lehto1987
