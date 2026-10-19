import References.GarnettMarshall2005.Ch02.S04_BoundarySmoothness
import References.LehtoVirtanen1973.Ch01.S06_ModuleRingDomain
import References.LehtoVirtanen1973.Ch03.S02_AbsoluteContinuity
import LiZhongQC.Ch01.S03_ExtremalLength

/-!
# Garnett–Marshall, Chapter IV §1: Definitions and examples

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. IV §1 (pp. 129–133;
`full.md` P1:5828–5983).

Conventions of Chapter IV, as modelled here. Chapter IV is planar (leader ruling B9): domains, open sets, the sets
`E`, `F` and the curves are subsets of `ℂ`. A Jordan domain `Ω` of `ℂ*` (Ch. I §3) and sets `E ⊆ ∂Ω ⊆ ℂ*` enter
through their finite parts (`References.finitePart`). Arcs through or ending at `∞` are not countable unions of
rectifiable arcs of `ℂ`; a family of such arcs has extremal length `∞` (metrics of finite area such as
`1/(|z| log |z|)` near `∞` give them infinite length), so leaving them out does not change an extremal length. This
fact is used, not stated.

A curve (a member of a path family) is a point set, a countable union of rectifiable arcs in `Ω`
(`LehtoVirtanen1973.IsRectifiableArc`: a Jordan arc of `ℂ` of finite linear measure). Its `ρ`-length `∫_γ ρ |dz|`
is the integral of `ρ` over the point set `γ` against the linear measure `μH[1]`, as in LV III.4. So overlapping
pieces and self-intersections of a curve count once: multiplicity is not counted. No path family of the book
(joining arcs, separating finite unions of arcs and closed curves, crosscuts) depends on multiplicity.

A metric is an element of `LiZhongQC.densitiesP0 Ω`: a Borel function `ρ : ℂ → [0, ∞]` with `0 < ∬_Ω ρ² < ∞`, the
book's definition verbatim (the value `∞` is allowed, P1:6122); only its values on `Ω` enter. The area is
`LiZhongQC.rhoArea ρ Ω`. Lengths, areas and extremal lengths are `ℝ≥0∞`-valued; the infimum over the empty family
is `∞`, and the module `λ_Ω(Γ)⁻¹` is the inverse in `[0, ∞]` (`1/0 = ∞`, `1/∞ = 0`, the book's meanings).

Reading of "join" (for `d_Ω(E, F)`): a connected arc in `Ω` joining `E` and `F` is an open Jordan arc
`f((0, 1)) ⊆ Ω` with `f` continuous and one-to-one on `[0, 1]`, `f(0) ∈ E` and `f(1) ∈ F` (the closed arc
`f([0, 1])` need not lie in `Ω`, since `E, F ⊆ Ω̄`); it must also be a curve of a path family.

Reading of "separate" (for `d*_Ω(E, F)`, P1:5894): a separating curve is a curve which is a finite union of Jordan
arcs and closed curves in `Ω` such that no component of `Ω \ γ` has points of both `E` and `F` in its closure
(`IsSeparatingIn`); this is how "`E` and `F` lie in the boundaries of distinct components of `Ω \ γ`" is read. The
stricter literal reading ("`E` lies in the boundary of one component and `F` in the boundary of another") is not
used: it fails for the broken vertical segments of a slit rectangle whose slits end on a vertical side, which the
book counts as separating curves ("need not be connected", P1:6157) and needs for `d* = 1/d` in Theorem 4.1.

"The extremal metrics are the constant multiples of `ρ₀`" is stated as two claims: every `c ρ₀` with a positive real
constant `c` is an extremal metric, and every extremal metric agrees with some `c ρ₀` almost everywhere on `Ω`. It is
not an equivalence: `ρ`-lengths see area-null sets, so a metric equal to `c ρ₀` a.e. that vanishes on one extremal
curve has `L(Γ, ρ) = 0` and is not extremal.

* Definition (rectifiable arc, the building block of path families, §1) — exists:
  `LehtoVirtanen1973.IsRectifiableArc` (a Jordan arc of the plane of finite linear measure; any kind of parameter
  interval)
* Definition (path family in a domain; curve, §1, P1:5838) — `IsPathFamily`, `IsPathCurve`
* Definition (metric on `Ω`, §1, P1:5852) — exists: `LiZhongQC.densitiesP0` (Borel functions from ℂ to [0, ∞]
  with positive finite area over the set; the book's definition, infinite values included)
* Definition (area `A(Ω, ρ)`, §1, P1:5854) — exists: `LiZhongQC.rhoArea` (the integral of the square of ρ over the
  set)
* Definition (`ρ`-length `L(Γ, ρ)`; extremal length `λ_Ω(Γ)`, (1.3), §1, P1:5858–5868) — `pathRhoLength`,
  `extremalLengthGM` (B-cand. LehtoVirtanen1973.arcFamilyModule and LehtoVirtanen1973.arcFamilyExtremalLength, the
  module of families of arcs and curves of the extended plane, an infimum of areas of admissible functions;
  LiZhongQC.extremalLengthIn, the same supremum formula for parametrized locally rectifiable curves: different member
  classes)
* Unlabelled (§1, P1:5870): conformal invariance, `λ_{φ(Ω)}(φ(Γ)) = λ_Ω(Γ)` — `extremalLengthGM_conformal`
* Definition (extremal metric, §1, P1:5872) — `IsExtremalMetricGM`
* Definition (modulus or module `λ_Ω(Γ)⁻¹` of a path family, §1, P1:5886) — omitted: written as the inverse of the
  extremal length in [0, ∞] wherever it occurs
* Definition (extremal distance `d_Ω(E, F)` and conjugate extremal distance `d*_Ω(E, F)`, §1, P1:5888–5894) —
  `extremalDistGM`, `conjExtremalDistGM` (with the families `joiningFamily`, `separatingFamily` and the separation
  predicate `IsSeparatingIn`)
* Example 1.1 (the rectangle; (1.4), §1) — `eq4_1_4`, `example4_1_1_b`, `example4_1_1_c`
* Definition (Jordan domain with four boundary points in counterclockwise order, §1, P1:5929) — exists:
  `LehtoVirtanen1973.Quadrilateral` (a Jordan domain of the extended plane with four positively ordered boundary
  points)
* Unlabelled (§1, P1:5929): a unique `ℓ > 0` and a conformal map of the Jordan domain onto `(0, ℓ) × (0, 1)` with
  `ζ₁, ζ₂, ζ₃, ζ₄ ↦ i, 0, ℓ, ℓ + i` — exists: `LehtoVirtanen1973.exists_canonicalMap_normalized` (existence, for the
  quadrilateral with the vertices relabelled cyclically as (ζ₂, ζ₃, ζ₄, ζ₁): the canonical map onto the rectangle
  with corners 0, M, M + i, i, so ℓ = M(Q)), `LehtoVirtanen1973.module_eq_of_isCanonicalMap` (uniqueness of ℓ: every
  canonical rectangle has side ratio M(Q)); the book's counterclockwise order is the positive orientation of LV
* Unlabelled (§1, P1:5929–5935): `ℓ = d_Ω(E, F)`, and the extremal metrics are the constant multiples of `|φ'|` —
  `quadrilateral_extremalDist`
* Formula (1.7) (§1) — `eq4_1_7`
* Example 1.2 (the annulus, §1) — `example4_1_2_a`, `example4_1_2_b`, `example4_1_2_c`
* Definition (ring domain, §1, P1:5978) — exists: `LehtoVirtanen1973.IsRingDomain` (a doubly connected domain of
  the extended plane; the book's plane domains may contain ∞)
* Definition (module `mod(Ω)` of a ring domain, §1, P1:5978–5981) — `ringModGM` (with the family `ringSepFamily`;
  the book's normalization (1/2π) log(R/r), not LehtoVirtanen1973.ringModule or LiZhongQC.dcModulus, which are
  log(R/r): stated constants depend on the factor)
* Unlabelled (§1, P1:5978): `mod(Ω) = (1/2π) log(R/r)` for a conformal map `ψ` of `Ω` onto `{r < |z| < R}`, with
  extremal metric `|ψ'|/|ψ|` — `ringModGM_annulus`

Helpers (not book notions): `joiningFamily` (the arcs joining `E` and `F` in `Ω`), `IsSeparatingIn` (separation in
`Ω`, the reading above), `separatingFamily` (the curves separating `E` from `F`), `ringSepFamily` (the curves in a
ring domain separating its two boundary components).

Not stated (inventory U−): the chapter introduction (P1:5830); the euclidean length (1.1) of a path family and the
conformally invariant quantity (1.2), with the pointer to Exercise III.22 (P1:5838–5850, motivation, not used
later); the remarks that (1.3) is the square of (1.2) when there is an extremal metric `|φ'|` and that every metric
gives a lower bound for `λ_Ω(Γ)` (P1:5872, 5935); the normalizations `A(Ω, ρ) = 1` and `L(Γ, ρ) = 1` (P1:5874–5884,
homogeneity of (1.3)); the existence and uniqueness sketches for the rectangle `(0, ℓ) × (0, 1)` (P1:5929); the
remark that (1.7) holds in very general circumstances (P1:5944, Theorem 4.1 and Theorem H.1); every ring domain is
conformally equivalent to an annulus (P1:5978, Exercise II.7, an exercise). (1.5), (1.6), (1.8) and (1.9) are steps
of the proofs of the examples.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt densitiesP0 rhoArea IsConformalOnto annulus)
open LehtoVirtanen1973 (IsRectifiableArc IsJordanArc IsConformalMap Quadrilateral IsCanonicalMap IsRingDomain
  derivDensity logDerivDensity)
open References (finitePart)

/-- **Definition** (curve, Ch. IV §1, P1:5838). An element `γ` of a path family in `Ω` is called a curve even though
`γ` may not be connected and may have many self-intersections: it is a countable union of rectifiable arcs in `Ω`.
Modelling: a point set `γ = ⋃ₙ sₙ` with every `sₙ` a rectifiable Jordan arc of `ℂ` (`IsRectifiableArc`) contained
in `Ω`; finite unions are the case of repeated arcs. -/
def IsPathCurve (Ω γ : Set ℂ) : Prop :=
  ∃ s : ℕ → Set ℂ, (∀ n, IsRectifiableArc (s n) ∧ s n ⊆ Ω) ∧ γ = ⋃ n, s n

/-- **Definition** (path family, Ch. IV §1, P1:5838). A path family in a domain `Ω` is a non-empty set `Γ` of
countable unions of rectifiable arcs in `Ω`. -/
def IsPathFamily (Ω : Set ℂ) (Γ : Set (Set ℂ)) : Prop :=
  Γ.Nonempty ∧ ∀ γ ∈ Γ, IsPathCurve Ω γ

/-- **Definition** (`ρ`-length, Ch. IV §1, P1:5858–5862). `L(Γ, ρ) = inf_{γ ∈ Γ} ∫_γ ρ |dz|`.
Modelling: `∫_γ ρ |dz|` is the (lower) integral of `ρ` over the point set `γ` with respect to the linear measure
`μH[1]` (arc length on rectifiable arcs); multiplicity is not counted (module docstring). The infimum over the empty
family is `∞`. -/
def pathRhoLength (Γ : Set (Set ℂ)) (ρ : ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ γ ∈ Γ, ∫⁻ z in γ, ρ z ∂μH[1]

/-- **Definition** (extremal length, (1.3), Ch. IV §1, P1:5864–5868). `λ_Ω(Γ) = sup_ρ L(Γ, ρ)²/A(Ω, ρ)`, the
supremum over all metrics `ρ` on `Ω`.
Modelling: metrics are `LiZhongQC.densitiesP0 Ω` and the area is `LiZhongQC.rhoArea ρ Ω`; the quotient is taken in
`[0, ∞]`, where `A(Ω, ρ) ∈ (0, ∞)` makes it junk-free (`L = ∞` gives the value `∞`). Near misses (not pointers):
`LehtoVirtanen1973.arcFamilyExtremalLength`, the inverse of `LehtoVirtanen1973.arcFamilyModule` (LV III.4: an
infimum of areas of admissible functions, for families of Jordan arcs and curves of `ℂ̄`; a disconnected member is
ignored there), and `LiZhongQC.extremalLengthIn` (the same supremum formula over `LiZhongQC.densitiesP0`, for
parametrized locally rectifiable curves, counted with multiplicity). -/
def extremalLengthGM (Ω : Set ℂ) (Γ : Set (Set ℂ)) : ℝ≥0∞ :=
  ⨆ ρ ∈ densitiesP0 Ω, pathRhoLength Γ ρ ^ 2 / rhoArea ρ Ω

/-! ### GM4-A helpers (-d9), moved here from Ch04/S02 for the import order (GM4-B I-1) -/

/-- Helper (unfolding, `rfl`): the area `A(D, ρ) = ∬_D ρ²`. -/
theorem gm4a_rhoArea_eq (ρ : ℂ → ℝ≥0∞) (D : Set ℂ) : rhoArea ρ D = ∫⁻ z in D, ρ z ^ 2 := rfl

/-- Helper (unfolding, `rfl`): membership in `P₀(D)`. -/
theorem gm4a_mem_densitiesP0 {ρ : ℂ → ℝ≥0∞} {D : Set ℂ} :
    ρ ∈ densitiesP0 D ↔ Measurable ρ ∧ 0 < rhoArea ρ D ∧ rhoArea ρ D < ⊤ := Iff.rfl

/-- Helper (unfolding, `rfl`): the `ρ`-length of a family. -/
theorem gm4a_pathRhoLength_eq (Γ : Set (Set ℂ)) (ρ : ℂ → ℝ≥0∞) :
    pathRhoLength Γ ρ = ⨅ γ ∈ Γ, ∫⁻ z in γ, ρ z ∂μH[1] := rfl

/-- Helper (unfolding, `rfl`): the extremal length as a supremum over `P₀(Ω)`. -/
theorem gm4a_extremalLengthGM_eq (Ω : Set ℂ) (Γ : Set (Set ℂ)) :
    extremalLengthGM Ω Γ = ⨆ ρ ∈ densitiesP0 Ω, pathRhoLength Γ ρ ^ 2 / rhoArea ρ Ω := rfl

/-- Helper: every metric gives a lower bound for the extremal length. -/
theorem gm4a_ratio_le {Ω : Set ℂ} {Γ : Set (Set ℂ)} {ρ : ℂ → ℝ≥0∞} (hρ : ρ ∈ densitiesP0 Ω) :
    pathRhoLength Γ ρ ^ 2 / rhoArea ρ Ω ≤ extremalLengthGM Ω Γ := by
  rw [gm4a_extremalLengthGM_eq]
  exact le_iSup₂_of_le ρ hρ le_rfl

/-- Helper: if every curve of `Γ'` contains a curve of `Γ`, then `L(Γ, ρ) ≤ L(Γ', ρ)`. -/
theorem gm4a_pathRhoLength_le_of_contains {Γ Γ' : Set (Set ℂ)} (ρ : ℂ → ℝ≥0∞)
    (h : ∀ γ' ∈ Γ', ∃ γ ∈ Γ, γ ⊆ γ') : pathRhoLength Γ ρ ≤ pathRhoLength Γ' ρ := by
  rw [gm4a_pathRhoLength_eq, gm4a_pathRhoLength_eq]
  refine le_iInf₂ fun γ' hγ' => ?_
  obtain ⟨γ, hγ, hsub⟩ := h γ' hγ'
  exact (iInf₂_le γ hγ).trans (lintegral_mono_set hsub)

/-- Helper: `L(Γ, ρ) ≤ L(Γ, ρ')` when `ρ ≤ ρ'` on every curve of `Γ` (measurable metrics). -/
theorem gm4a_pathRhoLength_mono {Γ : Set (Set ℂ)} {ρ ρ' : ℂ → ℝ≥0∞} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (h : ∀ γ ∈ Γ, ∀ z ∈ γ, ρ z ≤ ρ' z) : pathRhoLength Γ ρ ≤ pathRhoLength Γ ρ' := by
  rw [gm4a_pathRhoLength_eq, gm4a_pathRhoLength_eq]
  refine iInf₂_mono fun γ hγ => lintegral_mono_ae (ae_iff.2 ?_)
  have hset : {z | ¬ρ z ≤ ρ' z} ∩ γ = ∅ := eq_empty_iff_forall_notMem.2 fun z hz => hz.1 (h γ hγ z hz.2)
  rw [Measure.restrict_apply (show MeasurableSet {a | ¬ρ a ≤ ρ' a} from (measurableSet_le hρ hρ').compl), hset,
    measure_empty]

/-- Helper: `L(Γ, ρ₁) + L(Γ, ρ₂) ≤ L(Γ, ρ₁ + ρ₂)`. -/
theorem gm4a_pathRhoLength_add_le {Γ : Set (Set ℂ)} {ρ₁ : ℂ → ℝ≥0∞} (hρ₁ : Measurable ρ₁) (ρ₂ : ℂ → ℝ≥0∞) :
    pathRhoLength Γ ρ₁ + pathRhoLength Γ ρ₂ ≤ pathRhoLength Γ (fun z => ρ₁ z + ρ₂ z) := by
  rw [gm4a_pathRhoLength_eq, gm4a_pathRhoLength_eq, gm4a_pathRhoLength_eq]
  refine le_iInf₂ fun γ hγ => ?_
  rw [lintegral_add_left hρ₁]
  exact add_le_add (iInf₂_le γ hγ) (iInf₂_le γ hγ)

/-- Helper: `c L(Γ, ρ) ≤ L(Γ, cρ)`. -/
theorem gm4a_const_mul_pathRhoLength_le {Γ : Set (Set ℂ)} {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) (c : ℝ≥0∞) :
    c * pathRhoLength Γ ρ ≤ pathRhoLength Γ (fun z => c * ρ z) := by
  rw [gm4a_pathRhoLength_eq, gm4a_pathRhoLength_eq]
  refine le_iInf₂ fun γ hγ => ?_
  rw [lintegral_const_mul c hρ]
  gcongr
  exact iInf₂_le γ hγ

/-- Helper (Minkowski's inequality in `L²(D)`): `A(D, ρ₁ + ρ₂)^{1/2} ≤ A(D, ρ₁)^{1/2} + A(D, ρ₂)^{1/2}`. -/
theorem gm4a_rhoArea_add_rpow_le {D : Set ℂ} {ρ₁ ρ₂ : ℂ → ℝ≥0∞} (hρ₁ : Measurable ρ₁) (hρ₂ : Measurable ρ₂) :
    rhoArea (fun z => ρ₁ z + ρ₂ z) D ^ (1 / 2 : ℝ) ≤ rhoArea ρ₁ D ^ (1 / 2 : ℝ) + rhoArea ρ₂ D ^ (1 / 2 : ℝ) := by
  rw [gm4a_rhoArea_eq, gm4a_rhoArea_eq, gm4a_rhoArea_eq]
  have h := ENNReal.lintegral_Lp_add_le (μ := volume.restrict D) hρ₁.aemeasurable hρ₂.aemeasurable one_le_two
  simp only [Pi.add_apply, ENNReal.rpow_two] at h
  exact h

/-- Helper (the parallelogram identity in `[0, ∞]`, with the absolute difference `(a − b) + (b − a)`). -/
theorem gm4a_parallelogram (a b : ℝ≥0∞) : (a + b) ^ 2 + ((a - b) + (b - a)) ^ 2 = 2 * a ^ 2 + 2 * b ^ 2 := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp [ENNReal.top_pow two_ne_zero]
  rcases le_total a b with hab | hab
  · obtain ⟨c, rfl⟩ := exists_add_of_le hab
    rw [tsub_eq_zero_of_le hab, ENNReal.add_sub_cancel_left ha, zero_add]
    ring
  · obtain ⟨c, rfl⟩ := exists_add_of_le hab
    rw [tsub_eq_zero_of_le hab, ENNReal.add_sub_cancel_left (ne_top_of_le_ne_top ha hab), add_zero]
    ring

/-- Helper (the equality case of the parallelogram law): if `∬_D (f + g)² = 2∬_D f² + 2∬_D g² < ∞`, then
`f = g` almost everywhere on `D`. -/
theorem gm4a_ae_eq_of_rhoArea_add {D : Set ℂ} {f g : ℂ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfin : rhoArea f D + rhoArea g D < ⊤)
    (heq : rhoArea (fun z => f z + g z) D = 2 * rhoArea f D + 2 * rhoArea g D) :
    f =ᵐ[volume.restrict D] g := by
  rw [gm4a_rhoArea_eq, gm4a_rhoArea_eq] at hfin
  rw [gm4a_rhoArea_eq, gm4a_rhoArea_eq, gm4a_rhoArea_eq] at heq
  have hd : Measurable fun z => (f z - g z) + (g z - f z) := (hf.sub hg).add (hg.sub hf)
  have hint : (∫⁻ z in D, (f z + g z) ^ 2) + (∫⁻ z in D, ((f z - g z) + (g z - f z)) ^ 2) =
      2 * (∫⁻ z in D, f z ^ 2) + 2 * ∫⁻ z in D, g z ^ 2 := by
    have m1 : Measurable fun z => (f z + g z) ^ 2 := by fun_prop
    have m2 : Measurable fun z => 2 * f z ^ 2 := by fun_prop
    rw [← lintegral_add_left m1, ← lintegral_const_mul 2 (by fun_prop : Measurable fun z => f z ^ 2),
      ← lintegral_const_mul 2 (by fun_prop : Measurable fun z => g z ^ 2), ← lintegral_add_left m2]
    exact lintegral_congr fun z => gm4a_parallelogram (f z) (g z)
  rw [← heq] at hint
  have hfin2 : (∫⁻ z in D, (f z + g z) ^ 2) ≠ ⊤ := by
    rw [heq]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.add_lt_top.1 hfin).1.ne,
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.add_lt_top.1 hfin).2.ne⟩
  have hd0 : ∫⁻ z in D, ((f z - g z) + (g z - f z)) ^ 2 = 0 :=
    (ENNReal.add_right_inj hfin2).1 (hint.trans (add_zero _).symm)
  have hae := (lintegral_eq_zero_iff (hd.pow_const 2)).1 hd0
  filter_upwards [hae] with z hz
  simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero, add_eq_zero, tsub_eq_zero_iff_le] at hz
  exact le_antisymm hz.1 hz.2

/-- Helper (arithmetic): `(½ A^{−1/2})² = ¼ A⁻¹` in `[0, ∞]`. -/
theorem gm4a_coeff_sq (A : ℝ≥0∞) :
    (2⁻¹ * A ^ (-(1 / 2 : ℝ))) ^ 2 = 4⁻¹ * A⁻¹ := by
  have h1 : (A ^ (-(1 / 2 : ℝ))) ^ 2 = A⁻¹ := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
    exact ENNReal.rpow_neg_one A
  rw [mul_pow, h1, ← ENNReal.inv_pow]
  norm_num

/-- Helper (arithmetic): `(¼)^{1/2} = ½` in `[0, ∞]`. -/
theorem gm4a_quarter_rpow : (4⁻¹ : ℝ≥0∞) ^ (1 / 2 : ℝ) = 2⁻¹ := by
  rw [show (4⁻¹ : ℝ≥0∞) = 2⁻¹ ^ (2 : ℝ) by rw [ENNReal.rpow_two, ← ENNReal.inv_pow]; norm_num,
    ← ENNReal.rpow_mul]
  norm_num

/-- Helper: the normalizing constant `c = ½ A(Ω, ρ)^{−1/2}` of a metric is finite and positive, `A(Ω, cρ) = ¼`, and
`(c L(Γ, ρ))² = ¼ L(Γ, ρ)²/A(Ω, ρ)`. -/
theorem gm4a_coeff {Ω : Set ℂ} (Γ : Set (Set ℂ)) {ρ : ℂ → ℝ≥0∞} (hρ : ρ ∈ densitiesP0 Ω) {c : ℝ≥0∞}
    (hc : c = 2⁻¹ * rhoArea ρ Ω ^ (-(1 / 2 : ℝ))) :
    c ≠ 0 ∧ c ≠ ⊤ ∧ rhoArea (fun z => c * ρ z) Ω = 4⁻¹ ∧
      (c * pathRhoLength Γ ρ) ^ 2 = 4⁻¹ * (pathRhoLength Γ ρ ^ 2 / rhoArea ρ Ω) := by
  obtain ⟨-, h0, htop⟩ := gm4a_mem_densitiesP0.1 hρ
  have hcsq : c ^ 2 = 4⁻¹ * (rhoArea ρ Ω)⁻¹ := by rw [hc]; exact gm4a_coeff_sq _
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) (ENNReal.rpow_pos h0 htop.ne).ne'
  have hctop : c ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_pow two_ne_zero] at hcsq
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (by norm_num)) (ENNReal.inv_ne_top.2 h0.ne') hcsq.symm
  refine ⟨hc0, hctop, ?_, ?_⟩
  · rw [LiZhongQC.rhoArea_const_mul ρ Ω hctop, hcsq, mul_assoc, ENNReal.inv_mul_cancel h0.ne' htop.ne, mul_one]
  · rw [mul_pow, hcsq, ENNReal.div_eq_inv_mul]
    ring

/-- Helper ((2.1)–(2.2)): with `ρ₃ = c₁ρ₁ + c₂ρ₂`, `L(Γ, ρ₃)² ≥ L²(Γ, ρ₁)/A(Ω, ρ₁)` and `¼ ≤ A(Ω, ρ₃) ≤ 1`. -/
theorem gm4a_rho3_bounds {Ω : Set ℂ} {Γ : Set (Set ℂ)} {ρ₁ ρ₂ : ℂ → ℝ≥0∞} (hρ₁ : ρ₁ ∈ densitiesP0 Ω)
    (hρ₂ : ρ₂ ∈ densitiesP0 Ω)
    (h₁₂ : pathRhoLength Γ ρ₁ ^ 2 / rhoArea ρ₁ Ω = pathRhoLength Γ ρ₂ ^ 2 / rhoArea ρ₂ Ω) {c₁ c₂ : ℝ≥0∞}
    (hc₁ : c₁ = 2⁻¹ * rhoArea ρ₁ Ω ^ (-(1 / 2 : ℝ))) (hc₂ : c₂ = 2⁻¹ * rhoArea ρ₂ Ω ^ (-(1 / 2 : ℝ))) :
    pathRhoLength Γ ρ₁ ^ 2 / rhoArea ρ₁ Ω ≤ pathRhoLength Γ (fun z => c₁ * ρ₁ z + c₂ * ρ₂ z) ^ 2 ∧
      rhoArea (fun z => c₁ * ρ₁ z + c₂ * ρ₂ z) Ω ≤ 1 ∧ 4⁻¹ ≤ rhoArea (fun z => c₁ * ρ₁ z + c₂ * ρ₂ z) Ω := by
  have hm₁ := (gm4a_mem_densitiesP0.1 hρ₁).1
  have hm₂ := (gm4a_mem_densitiesP0.1 hρ₂).1
  obtain ⟨-, -, hA₁, hL₁⟩ := gm4a_coeff Γ hρ₁ hc₁
  obtain ⟨-, -, hA₂, hL₂⟩ := gm4a_coeff Γ hρ₂ hc₂
  have hLsum : c₁ * pathRhoLength Γ ρ₁ + c₂ * pathRhoLength Γ ρ₂ ≤
      pathRhoLength Γ (fun z => c₁ * ρ₁ z + c₂ * ρ₂ z) :=
    (add_le_add (gm4a_const_mul_pathRhoLength_le hm₁ c₁) (gm4a_const_mul_pathRhoLength_le hm₂ c₂)).trans
      (gm4a_pathRhoLength_add_le (hm₁.const_mul c₁) _)
  have hx : c₁ * pathRhoLength Γ ρ₁ = c₂ * pathRhoLength Γ ρ₂ := by
    have h2 : (c₁ * pathRhoLength Γ ρ₁) ^ 2 = (c₂ * pathRhoLength Γ ρ₂) ^ 2 := by rw [hL₁, hL₂, h₁₂]
    exact le_antisymm ((ENNReal.pow_le_pow_left_iff two_ne_zero).1 h2.le)
      ((ENNReal.pow_le_pow_left_iff two_ne_zero).1 h2.ge)
  refine ⟨?_, ?_, ?_⟩
  · calc pathRhoLength Γ ρ₁ ^ 2 / rhoArea ρ₁ Ω = 4 * (c₁ * pathRhoLength Γ ρ₁) ^ 2 := by
          rw [hL₁, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ = (c₁ * pathRhoLength Γ ρ₁ + c₂ * pathRhoLength Γ ρ₂) ^ 2 := by rw [← hx]; ring
      _ ≤ pathRhoLength Γ (fun z => c₁ * ρ₁ z + c₂ * ρ₂ z) ^ 2 := by gcongr
  · have hM := gm4a_rhoArea_add_rpow_le (D := Ω) (hm₁.const_mul c₁) (hm₂.const_mul c₂)
    rw [hA₁, hA₂, gm4a_quarter_rpow, ENNReal.inv_two_add_inv_two,
      ← ENNReal.one_rpow (1 / 2 : ℝ)] at hM
    exact (ENNReal.rpow_le_rpow_iff (by norm_num)).1 hM
  · rw [← hA₁, gm4a_rhoArea_eq, gm4a_rhoArea_eq]
    exact lintegral_mono fun z => by gcongr; exact le_self_add

/-- Helper (arithmetic in `[0, ∞]`): `a ≤ b` and `c ≤ 1` give `a ≤ b / c`. -/
theorem gm4a_le_div_of_le_one {a b c : ℝ≥0∞} (hab : a ≤ b) (hc : c ≤ 1) : a ≤ b / c := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rcases eq_or_ne b 0 with rfl | hb0
    · simpa using hab
    · rw [ENNReal.div_zero hb0]; exact le_top
  · rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl (ne_top_of_le_ne_top ENNReal.one_ne_top hc))]
    calc a * c ≤ a * 1 := by gcongr
      _ = a := mul_one a
      _ ≤ b := hab

/-- Helper (arithmetic in `[0, ∞]`): if `0 < r < ∞`, `r ≤ L`, `¼ ≤ A ≤ 1` and `L/A = r`, then `A = 1`. -/
theorem gm4a_eq_one_of_div_eq {r L A : ℝ≥0∞} (hr₀ : 0 < r) (hr : r < ⊤) (hL : r ≤ L) (hA : A ≤ 1) (hA₀ : 4⁻¹ ≤ A)
    (heq : L / A = r) : A = 1 := by
  have hA0 : A ≠ 0 := (lt_of_lt_of_le (ENNReal.inv_pos.2 (by norm_num)) hA₀).ne'
  have hAtop : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hA
  have hLA : L = r * A := by rw [← heq, ENNReal.div_mul_cancel hA0 hAtop]
  refine le_antisymm hA ?_
  have h : r * 1 ≤ r * A := by rw [mul_one, ← hLA]; exact hL
  exact (ENNReal.mul_le_mul_iff_right hr₀.ne' hr.ne).1 h

/-- Helper: cancelling a finite positive constant in an a.e. equality. -/
theorem gm4a_ae_eq_of_const_mul {D : Set ℂ} {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ⊤) {f g : ℂ → ℝ≥0∞}
    (h : (fun z => c * f z) =ᵐ[volume.restrict D] fun z => c * g z) : f =ᵐ[volume.restrict D] g := by
  filter_upwards [h] with z hz
  exact (ENNReal.mul_right_inj hc₀ hc).1 hz

/-- Helper: `ρ₃ = c₁ρ₁ + c₂ρ₂` is a metric when `¼ ≤ A(Ω, ρ₃) ≤ 1`. -/
theorem gm4a_rho3_mem {Ω : Set ℂ} {ρ₁ ρ₂ : ℂ → ℝ≥0∞} (hρ₁ : Measurable ρ₁) (hρ₂ : Measurable ρ₂) (c₁ c₂ : ℝ≥0∞)
    (hA : rhoArea (fun z => c₁ * ρ₁ z + c₂ * ρ₂ z) Ω ≤ 1)
    (hA₀ : 4⁻¹ ≤ rhoArea (fun z => c₁ * ρ₁ z + c₂ * ρ₂ z) Ω) :
    (fun z => c₁ * ρ₁ z + c₂ * ρ₂ z) ∈ densitiesP0 Ω := by
  refine gm4a_mem_densitiesP0.2 ⟨(hρ₁.const_mul c₁).add (hρ₂.const_mul c₂), ?_, hA.trans_lt ENNReal.one_lt_top⟩
  exact lt_of_lt_of_le (ENNReal.inv_pos.2 (by norm_num)) hA₀

/-- Helper (arithmetic): `¼ + ¼ < ∞`. -/
theorem gm4a_quarter_add_lt_top : (4⁻¹ : ℝ≥0∞) + 4⁻¹ < ⊤ := by
  exact ENNReal.add_lt_top.2 ⟨ENNReal.inv_lt_top.2 (by norm_num), ENNReal.inv_lt_top.2 (by norm_num)⟩

/-- Helper (arithmetic): `1 = 2 · ¼ + 2 · ¼` in `[0, ∞]`. -/
theorem gm4a_one_eq_quarters : (1 : ℝ≥0∞) = 2 * 4⁻¹ + 2 * 4⁻¹ := by
  rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 by norm_num, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

/-! ### GM4-B helpers (-e8): linear measure under conformal maps (W-AREA1), lines, circles, projections -/

/-- Helper (a countable local-to-global argument): if `m` is countably subadditive on subsets of `S`, `ν` is
countably additive on disjoint Borel subsets of `S`, and every point of the Borel set `S` has an open neighbourhood
`U` with `m T ≤ ν T` for the Borel `T ⊆ U ∩ S`, then `m S ≤ ν S` (Lindelöf + `disjointed`). -/
theorem gm4b_le_of_local {S : Set ℂ} (hS : MeasurableSet S) {m ν : Set ℂ → ℝ≥0∞} (hm0 : m ∅ = 0)
    (hm : ∀ T : ℕ → Set ℂ, (∀ k, T k ⊆ S) → m (⋃ k, T k) ≤ ∑' k, m (T k))
    (hν : ∀ T : ℕ → Set ℂ, (∀ k, MeasurableSet (T k) ∧ T k ⊆ S) → Pairwise (Function.onFun Disjoint T) →
      ν (⋃ k, T k) = ∑' k, ν (T k))
    (hloc : ∀ z ∈ S, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ ∀ T, MeasurableSet T → T ⊆ U ∩ S → m T ≤ ν T) :
    m S ≤ ν S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [hm0]
    exact zero_le
  choose! U hUo hzU hUle using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun z : S => U z) fun z => hUo z z.2
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    have : z ∈ ⋃ i : S, U i := mem_iUnion.2 ⟨⟨z, hz⟩, hzU z hz⟩
    rw [← hTU] at this
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.1 this
    exact ⟨i, hi⟩
  obtain ⟨e, he⟩ := hTc.exists_eq_range hTne
  set V : ℕ → Set ℂ := fun k => U (e k) ∩ S with hV
  have hcov : S = ⋃ k, V k := by
    apply Subset.antisymm
    · intro z hz
      have : z ∈ ⋃ i : S, U i := mem_iUnion.2 ⟨⟨z, hz⟩, hzU z hz⟩
      rw [← hTU] at this
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 this
      rw [he] at hi
      obtain ⟨k, rfl⟩ := hi
      exact mem_iUnion.2 ⟨k, hzi, hz⟩
    · exact iUnion_subset fun k => inter_subset_right
  set P := disjointed V with hP
  have hPV : ∀ k, P k ⊆ V k := disjointed_subset V
  have hPm : ∀ k, MeasurableSet (P k) :=
    MeasurableSet.disjointed fun k => ((hUo _ (e k).2).measurableSet).inter hS
  have hPS : ∀ k, P k ⊆ S := fun k => (hPV k).trans inter_subset_right
  have hPU : S = ⋃ k, P k := by rw [hP, iUnion_disjointed, ← hcov]
  calc m S = m (⋃ k, P k) := by rw [← hPU]
    _ ≤ ∑' k, m (P k) := hm P hPS
    _ ≤ ∑' k, ν (P k) := ENNReal.tsum_le_tsum fun k => hUle _ (e k).2 _ (hPm k) fun z hz =>
        ⟨(hPV k hz).1, hPS k hz⟩
    _ = ν (⋃ k, P k) := (hν P (fun k => ⟨hPm k, hPS k⟩) (disjoint_disjointed V)).symm
    _ = ν S := by rw [← hPU]

/-- Helper: near a point of `Ω`, the derivative of a conformal map stays within the factor `1 ± δ` of its value. -/
theorem gm4b_deriv_near {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ} (hφ : IsConformalOnto φ Ω Ω') {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∀ w ∈ ball z₀ r,
      (1 - δ) * ‖deriv φ z₀‖ ≤ ‖deriv φ w‖ ∧ ‖deriv φ w‖ ≤ (1 + δ) * ‖deriv φ z₀‖ := by
  have hc : 0 < ‖deriv φ z₀‖ := norm_pos_iff.2 (LiZhongQC.deriv_ne_zero_of_injOn hΩ hφ.1 hφ.2.1 hz₀)
  have hcont : ContinuousAt (deriv φ) z₀ :=
    ((hφ.1.analyticOnNhd hΩ).deriv z₀ hz₀).continuousAt
  obtain ⟨r₁, hr₁, hr₁Ω⟩ := Metric.isOpen_iff.1 hΩ z₀ hz₀
  obtain ⟨r₂, hr₂, hr₂c⟩ := Metric.continuousAt_iff.1 hcont (δ * ‖deriv φ z₀‖) (mul_pos hδ hc)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, (ball_subset_ball (min_le_left _ _)).trans hr₁Ω, fun w hw => ?_⟩
  have hd : ‖deriv φ w - deriv φ z₀‖ < δ * ‖deriv φ z₀‖ :=
    by simpa [dist_eq_norm] using hr₂c (lt_of_lt_of_le (mem_ball.1 hw) (min_le_right _ _))
  have h1 := norm_sub_norm_le (deriv φ w) (deriv φ z₀)
  have h2 := norm_sub_norm_le (deriv φ z₀) (deriv φ w)
  rw [norm_sub_rev] at h2
  constructor <;> nlinarith

/-- Helper: on a ball where `‖φ'‖ ≤ K`, `μH[1](φ(T)) ≤ K μH[1](T)` for `T` in the ball. -/
theorem gm4b_hausdorff_image_le_of_ball {φ : ℂ → ℂ} {z₀ : ℂ} {r K : ℝ} (hK : 0 ≤ K)
    (hd : ∀ w ∈ ball z₀ r, DifferentiableAt ℂ φ w) (hb : ∀ w ∈ ball z₀ r, ‖deriv φ w‖ ≤ K) {T : Set ℂ}
    (hT : T ⊆ ball z₀ r) : μH[1] (φ '' T) ≤ ENNReal.ofReal K * μH[1] T := by
  have hlip : LipschitzOnWith (Real.toNNReal K) φ (ball z₀ r) :=
    (convex_ball z₀ r).lipschitzOnWith_of_nnnorm_deriv_le hd fun w hw => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hK]
      exact hb w hw
  have h := (hlip.mono hT).hausdorffMeasure_image_le zero_le_one
  simpa [ENNReal.rpow_one, ENNReal.ofReal] using h

/-- Helper: `X ≤ Y` in `[0, ∞]` when `X ≤ t Y` for every real `t > 1`. -/
theorem gm4b_le_of_forall_one_lt {X Y : ℝ≥0∞} (h : ∀ t : ℝ, 1 < t → X ≤ ENNReal.ofReal t * Y) : X ≤ Y := by
  have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal t * Y) (𝓝[>] 1) (𝓝 (ENNReal.ofReal 1 * Y)) :=
    ENNReal.Tendsto.mul_const ((ENNReal.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds)
      (Or.inl (by simp))
  rw [ENNReal.ofReal_one, one_mul] at hlim
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t ht => h t ht)

/-- Helper (W-AREA1, upper half): for a conformal map `φ` of an open set and a Borel set `S` inside it,
`μH[1](φ(S)) ≤ ∫_S |φ'| dμH[1]` (local Lipschitz bounds on small convex pieces). -/
theorem gm4b_hausdorff_image_le {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ} (hφ : IsConformalOnto φ Ω Ω')
    {S : Set ℂ} (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) :
    μH[1] (φ '' S) ≤ ∫⁻ z in S, ‖deriv φ z‖ₑ ∂μH[1] := by
  have hd : ∀ w ∈ Ω, DifferentiableAt ℂ φ w := fun w hw => hφ.1.differentiableAt (hΩ.mem_nhds hw)
  refine gm4b_le_of_forall_one_lt fun t ht => ?_
  set δ : ℝ := (t - 1) / (t + 1) with hδ
  have hδ0 : 0 < δ := div_pos (by linarith) (by linarith)
  have hδ1 : δ < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hδt : 1 + δ = t * (1 - δ) := by rw [hδ]; field_simp; ring
  refine gm4b_le_of_local (m := fun T => μH[1] (φ '' T))
    (ν := fun T => ENNReal.ofReal t * ∫⁻ z in T, ‖deriv φ z‖ₑ ∂μH[1]) hS (by simp) ?_ ?_ ?_
  · intro T _
    rw [image_iUnion]
    exact measure_iUnion_le _
  · intro T hT hdisj
    rw [lintegral_iUnion (fun k => (hT k).1) hdisj, ENNReal.tsum_mul_left]
  · intro z hz
    obtain ⟨r, hr, hrΩ, hb⟩ := gm4b_deriv_near hΩ hφ (hSΩ hz) hδ0
    refine ⟨ball z r, isOpen_ball, mem_ball_self hr, fun T hTm hT => ?_⟩
    have hTb : T ⊆ ball z r := hT.trans inter_subset_left
    calc μH[1] (φ '' T) ≤ ENNReal.ofReal ((1 + δ) * ‖deriv φ z‖) * μH[1] T :=
          gm4b_hausdorff_image_le_of_ball (by positivity) (fun w hw => hd w (hrΩ hw))
            (fun w hw => (hb w hw).2) hTb
      _ = ENNReal.ofReal t * (ENNReal.ofReal ((1 - δ) * ‖deriv φ z‖) * μH[1] T) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith), hδt, mul_assoc]
      _ ≤ ENNReal.ofReal t * ∫⁻ w in T, ‖deriv φ w‖ₑ ∂μH[1] := by
          gcongr
          rw [← setLIntegral_const]
          refine setLIntegral_mono' hTm fun w hw => ?_
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hb w (hTb hw)).1

/-- Helper (W-AREA1, lower half): `∫_S |φ'| dμH[1] ≤ μH[1](φ(S))` (the same bounds for the local inverse). -/
theorem gm4b_lintegral_le_hausdorff_image {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ Ω Ω') {S : Set ℂ} (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) :
    ∫⁻ z in S, ‖deriv φ z‖ₑ ∂μH[1] ≤ μH[1] (φ '' S) := by
  have hΩ' : IsOpen Ω' := hφ.isOpen hΩ
  have hψ := hφ.symm hΩ
  set ψ := Function.invFunOn φ Ω with hψdef
  have hleft : ∀ z ∈ Ω, ψ (φ z) = z := fun z hz => hφ.2.1.leftInvOn_invFunOn hz
  have hφc : ContinuousOn φ Ω := hφ.1.continuousOn
  have hd : ∀ w ∈ Ω, DifferentiableAt ℂ φ w := fun w hw => hφ.1.differentiableAt (hΩ.mem_nhds hw)
  have hdψ : ∀ w ∈ Ω', DifferentiableAt ℂ ψ w := fun w hw => hψ.1.differentiableAt (hΩ'.mem_nhds hw)
  have hφΩ : ∀ z ∈ Ω, φ z ∈ Ω' := fun z hz => hφ.2.2 ▸ mem_image_of_mem φ hz
  have hinv : ∀ z ∈ Ω, ‖deriv ψ (φ z)‖ * ‖deriv φ z‖ = 1 := by
    intro z hz
    have h1 : HasDerivAt (ψ ∘ φ) (deriv ψ (φ z) * deriv φ z) z :=
      (hdψ _ (hφΩ z hz)).hasDerivAt.comp z (hd z hz).hasDerivAt
    have h2 : (id : ℂ → ℂ) =ᶠ[𝓝 z] ψ ∘ φ := by
      filter_upwards [hΩ.mem_nhds hz] with w hw
      exact (hleft w hw).symm
    have h3 := (h1.congr_of_eventuallyEq h2).unique (hasDerivAt_id z)
    rw [← norm_mul, h3, norm_one]
  refine gm4b_le_of_forall_one_lt fun t ht => ?_
  set δ : ℝ := min ((t - 1) / 3) 1 with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδ3 : δ ≤ (t - 1) / 3 := min_le_left _ _
  have hδt : (1 + δ) * (1 + δ) ≤ t := by nlinarith
  refine gm4b_le_of_local (m := fun T => ∫⁻ z in T, ‖deriv φ z‖ₑ ∂μH[1])
    (ν := fun T => ENNReal.ofReal t * μH[1] (φ '' T)) hS (by simp) ?_ ?_ ?_
  · intro T _
    exact lintegral_iUnion_le T _
  · intro T hT hdisj
    rw [image_iUnion, measure_iUnion, ENNReal.tsum_mul_left]
    · intro i j hij
      exact disjoint_image_image fun a ha b hb hab => (hdisj hij).ne_of_mem ha hb
        (hφ.2.1 ((hT i).2.trans hSΩ ha) ((hT j).2.trans hSΩ hb) hab)
    · exact fun k => (hT k).1.image_of_continuousOn_injOn (hφc.mono ((hT k).2.trans hSΩ))
        (hφ.2.1.mono ((hT k).2.trans hSΩ))
  · intro z hz
    have hzΩ := hSΩ hz
    have hc : 0 < ‖deriv φ z‖ := norm_pos_iff.2 (LiZhongQC.deriv_ne_zero_of_injOn hΩ hφ.1 hφ.2.1 hzΩ)
    obtain ⟨r, hr, hrΩ, hb⟩ := gm4b_deriv_near hΩ hφ hzΩ hδ0
    obtain ⟨r', hr', hr'Ω, hb'⟩ := gm4b_deriv_near hΩ' hψ (hφΩ z hzΩ) hδ0
    refine ⟨ball z r ∩ (Ω ∩ φ ⁻¹' ball (φ z) r'), isOpen_ball.inter (hφc.isOpen_inter_preimage hΩ isOpen_ball),
      ⟨mem_ball_self hr, hzΩ, mem_ball_self hr'⟩, fun T hTm hT => ?_⟩
    have hTb : T ⊆ ball z r := fun w hw => (hT hw).1.1
    have hTΩ : T ⊆ Ω := fun w hw => (hT hw).1.2.1
    have hφT : φ '' T ⊆ ball (φ z) r' := by
      rintro _ ⟨w, hw, rfl⟩
      exact (hT hw).1.2.2
    have hψφT : ψ '' (φ '' T) = T := by
      rw [image_image]
      exact (image_congr fun w hw => hleft w (hTΩ hw)).trans (image_id T)
    have hψb : ∀ w ∈ ball (φ z) r', ‖deriv ψ w‖ ≤ (1 + δ) * ‖deriv φ z‖⁻¹ := by
      intro w hw
      have h := (hb' w hw).2
      have h2 : ‖deriv ψ (φ z)‖ = ‖deriv φ z‖⁻¹ := by
        exact eq_inv_of_mul_eq_one_left (hinv z hzΩ)
      rwa [h2] at h
    have hμT : μH[1] T ≤ ENNReal.ofReal ((1 + δ) * ‖deriv φ z‖⁻¹) * μH[1] (φ '' T) := by
      calc μH[1] T = μH[1] (ψ '' (φ '' T)) := by rw [hψφT]
        _ ≤ _ := gm4b_hausdorff_image_le_of_ball (by positivity) (fun w hw => hdψ w (hr'Ω hw)) hψb hφT
    calc ∫⁻ w in T, ‖deriv φ w‖ₑ ∂μH[1] ≤ ∫⁻ _ in T, ENNReal.ofReal ((1 + δ) * ‖deriv φ z‖) ∂μH[1] := by
          refine setLIntegral_mono' hTm fun w hw => ?_
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hb w (hTb hw)).2
      _ = ENNReal.ofReal ((1 + δ) * ‖deriv φ z‖) * μH[1] T := by rw [setLIntegral_const, mul_comm]
      _ ≤ ENNReal.ofReal ((1 + δ) * ‖deriv φ z‖) *
            (ENNReal.ofReal ((1 + δ) * ‖deriv φ z‖⁻¹) * μH[1] (φ '' T)) := by gcongr
      _ = ENNReal.ofReal ((1 + δ) * (1 + δ)) * μH[1] (φ '' T) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          field_simp
      _ ≤ ENNReal.ofReal t * μH[1] (φ '' T) := by gcongr

/-- Helper (W-AREA1): linear measure transforms with `|φ'|` under a conformal map,
`∫_{φ(S)} ρ dμH[1] = ∫_S (ρ ∘ φ) |φ'| dμH[1]` for `S` Borel inside the open set and `ρ` Borel. -/
theorem gm4b_lintegral_image_conformal {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ Ω Ω') {S : Set ℂ} (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) : ∫⁻ w in φ '' S, ρ w ∂μH[1] = ∫⁻ z in S, ρ (φ z) * ‖deriv φ z‖ₑ ∂μH[1] := by
  classical
  set g : ℂ → ℂ := Ω.piecewise φ (fun _ => 0) with hg
  have hgm : Measurable g := hφ.1.continuousOn.measurable_piecewise continuousOn_const hΩ.measurableSet
  have hgS : ∀ z ∈ S, g z = φ z := fun z hz => piecewise_eq_of_mem _ _ _ (hSΩ hz)
  have hdm : Measurable fun z => ‖deriv φ z‖ₑ := (measurable_deriv φ).enorm
  have hmeas : μH[1].restrict (φ '' S) =
      Measure.map g ((μH[1].restrict S).withDensity fun z => ‖deriv φ z‖ₑ) := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.map_apply hgm hA, withDensity_apply _ (hgm hA),
      Measure.restrict_restrict (hgm hA)]
    have hTm : MeasurableSet (g ⁻¹' A ∩ S) := (hgm hA).inter hS
    have hTΩ : g ⁻¹' A ∩ S ⊆ Ω := inter_subset_right.trans hSΩ
    have hpre : φ '' (g ⁻¹' A ∩ S) = A ∩ φ '' S := by
      ext w
      constructor
      · rintro ⟨z, ⟨hzA, hzS⟩, rfl⟩
        exact ⟨by rw [← hgS z hzS]; exact hzA, z, hzS, rfl⟩
      · rintro ⟨hwA, z, hzS, rfl⟩
        exact ⟨z, ⟨by show g z ∈ A; rw [hgS z hzS]; exact hwA, hzS⟩, rfl⟩
    rw [← hpre]
    exact le_antisymm (gm4b_hausdorff_image_le hΩ hφ hTm hTΩ) (gm4b_lintegral_le_hausdorff_image hΩ hφ hTm hTΩ)
  rw [hmeas, lintegral_map hρ hgm, show (fun a => ρ (g a)) = ρ ∘ g from rfl,
    lintegral_withDensity_eq_lintegral_mul _ hdm (hρ.comp hgm)]
  refine setLIntegral_congr_fun hS fun z hz => ?_
  simp only [Pi.mul_apply, Function.comp_apply, hgS z hz]
  ring

/-- Helper: a plane set whose image in `ℂ̄` is the embedded image of an interval is a Borel set (Lusin–Souslin for
the continuous injective parametrization read back in `ℂ`). -/
theorem gm4b_measurableSet_of_jordanOver {I : Set ℝ} (hI : I.OrdConnected) {g : ℝ → LiZhongQC.ExtPlane}
    (hg : IsEmbedding (I.domRestrict g)) {C : Set ℂ} (hgI : g '' I = LiZhongQC.toExt C) : MeasurableSet C := by
  classical
  have hmem : ∀ t ∈ I, ∃ z : ℂ, (z : LiZhongQC.ExtPlane) = g t := by
    intro t ht
    have h : g t ∈ LiZhongQC.toExt C := hgI ▸ mem_image_of_mem g ht
    obtain ⟨z, -, hz⟩ := h
    exact ⟨z, hz⟩
  set k : ℝ → ℂ := fun t => OnePoint.elim (g t) 0 id with hkdef
  have hk : ∀ t ∈ I, (k t : LiZhongQC.ExtPlane) = g t := fun t ht => by
    obtain ⟨z, hz⟩ := hmem t ht
    rw [hkdef]
    simp only
    rw [← hz]
    rfl
  have hcont : ContinuousOn k I := by
    rw [OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff]
    exact (continuousOn_iff_continuous_domRestrict.2 hg.continuous).congr fun t ht => hk t ht
  have hinj : InjOn k I := fun a ha b hb hab => by
    have h : I.domRestrict g ⟨a, ha⟩ = I.domRestrict g ⟨b, hb⟩ := by
      show g a = g b
      rw [← hk a ha, ← hk b hb, hab]
    exact congrArg Subtype.val (hg.injective h)
  have hC : C = k '' I := by
    ext z
    constructor
    · intro hz
      have h : (z : LiZhongQC.ExtPlane) ∈ g '' I := hgI ▸ ⟨z, hz, rfl⟩
      obtain ⟨t, ht, hzt⟩ := h
      exact ⟨t, ht, OnePoint.coe_injective (by rw [hk t ht, hzt])⟩
    · rintro ⟨t, ht, rfl⟩
      have h : g t ∈ LiZhongQC.toExt C := hgI ▸ mem_image_of_mem g ht
      obtain ⟨z, hz, hzt⟩ := h
      rw [show k t = z from OnePoint.coe_injective (by rw [hk t ht, hzt])]
      exact hz
  rw [hC]
  exact hI.measurableSet.image_of_continuousOn_injOn hcont hinj

/-- Helper: a curve of a path family (a countable union of Jordan arcs) is a Borel set. -/
theorem gm4b_isPathCurve_measurableSet {Ω γ : Set ℂ} (hγ : IsPathCurve Ω γ) : MeasurableSet γ := by
  obtain ⟨s, hs, rfl⟩ := hγ
  refine MeasurableSet.iUnion fun n => ?_
  obtain ⟨⟨I, hI, -, g, hg, hgI⟩, -⟩ := id (hs n).1
  exact gm4b_measurableSet_of_jordanOver hI hg hgI

/-- Helper: linear measure on a line, `∫_{c + u·A} ρ dμH[1] = ∫_A ρ(c + t u) dt` for `|u| = 1`. -/
theorem gm4b_lintegral_line {c u : ℂ} (hu : ‖u‖ = 1) {A : Set ℝ} (hA : MeasurableSet A) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) : ∫⁻ z in (fun t : ℝ => c + t * u) '' A, ρ z ∂μH[1] = ∫⁻ t in A, ρ (c + t * u) := by
  have _ := hA
  have _ := hρ
  set e : ℝ → ℂ := fun t => c + t * u with he
  have hiso : Isometry e := by
    refine Isometry.of_dist_eq fun x y => ?_
    simp only [he, dist_eq_norm]
    rw [show c + x * u - (c + y * u) = ((x - y : ℝ) : ℂ) * u by push_cast; ring, norm_mul, hu, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
  have hme : MeasurableEmbedding e := hiso.isClosedEmbedding.measurableEmbedding
  have hmap : Measure.map e (volume : Measure ℝ) = μH[1].restrict (range e) := by
    rw [← hiso.map_hausdorffMeasure (Or.inl zero_le_one), hausdorffMeasure_real]
  have hsub : e '' A ⊆ range e := image_subset_range e A
  calc ∫⁻ z in e '' A, ρ z ∂μH[1] = ∫⁻ z in e '' A, ρ z ∂(μH[1].restrict (range e)) := by
        rw [Measure.restrict_restrict_of_subset hsub]
    _ = ∫⁻ z in e '' A, ρ z ∂(Measure.map e volume) := by rw [hmap]
    _ = ∫⁻ t in A, ρ (e t) := by
        rw [hme.restrict_map, hme.lintegral_map, hme.injective.preimage_image]

/-- Helper: `z ↦ s e^{iz}` is a conformal map of the strip `0 < Re z < 2π`. -/
theorem gm4b_expStrip_conformal {s : ℝ} (hs : 0 < s) :
    LiZhongQC.IsConformalOnto (fun z : ℂ => (s : ℂ) * exp (z * I)) {z : ℂ | 0 < z.re ∧ z.re < 2 * π}
      ((fun z : ℂ => (s : ℂ) * exp (z * I)) '' {z : ℂ | 0 < z.re ∧ z.re < 2 * π}) := by
  refine ⟨fun z _ => by fun_prop, fun a ha b hb hab => ?_, rfl⟩
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have h : exp (a * I) = exp (b * I) := mul_left_cancel₀ hs0 hab
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have hre : a.re - b.re = 2 * π * n := by
    have := congrArg Complex.im hn
    simp at this
    linarith
  have hn0 : n = 0 := by
    have h1 : |(2 * π * n : ℝ)| < 2 * π := by
      rw [← hre, abs_lt]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at h1
    have h2 : |(n : ℝ)| < 1 := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [Real.pi_pos]
    exact_mod_cast abs_lt.1 h2 |>.elim (fun h3 h4 => by
      have : (-1 : ℤ) < n ∧ n < 1 := ⟨by exact_mod_cast h3, by exact_mod_cast h4⟩
      omega)
  rw [hn0] at hn
  simp only [Int.cast_zero, zero_mul, add_zero] at hn
  exact mul_right_cancel₀ I_ne_zero hn

/-- Helper: linear measure on a circle, `∫_{|z| = s} ρ dμH[1] = ∫_0^{2π} ρ(s e^{iθ}) s dθ`. -/
theorem gm4b_lintegral_sphere {s : ℝ} (hs : 0 < s) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    ∫⁻ z in sphere (0 : ℂ) s, ρ z ∂μH[1] =
      ∫⁻ θ in Ioo (0 : ℝ) (2 * π), ρ (s * exp (θ * I)) * ENNReal.ofReal s := by
  set φ : ℂ → ℂ := fun z => (s : ℂ) * exp (z * I) with hφdef
  set Ω : Set ℂ := {z : ℂ | 0 < z.re ∧ z.re < 2 * π} with hΩdef
  have hΩ : IsOpen Ω := (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hφ := gm4b_expStrip_conformal hs
  set S : Set ℂ := (fun t : ℝ => (0 : ℂ) + t * 1) '' Ioo 0 (2 * π) with hSdef
  have hSm : MeasurableSet S := by
    have hiso : Isometry (fun t : ℝ => (0 : ℂ) + t * 1) := by
      refine Isometry.of_dist_eq fun x y => ?_
      simp [dist_eq_norm, ← ofReal_sub]
    exact hiso.isClosedEmbedding.measurableEmbedding.measurableSet_image.2 measurableSet_Ioo
  have hSΩ : S ⊆ Ω := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hΩdef]
    simpa using ht
  have hderiv : ∀ t : ℝ, ‖deriv φ ((0 : ℂ) + t * 1)‖ₑ = ENNReal.ofReal s := by
    intro t
    have h : HasDerivAt φ ((s : ℂ) * (exp (((0 : ℂ) + t * 1) * I) * I)) ((0 : ℂ) + t * 1) := by
      have := ((hasDerivAt_id ((0 : ℂ) + t * 1)).mul_const I).cexp.const_mul (s : ℂ)
      simpa [hφdef] using this
    rw [h.deriv, ← ofReal_norm]
    congr 1
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le, norm_I, mul_one]
    rw [show ((0 : ℂ) + t * 1) * I = ((t : ℂ)) * I by ring, norm_exp_ofReal_mul_I, mul_one]
  -- the image of the segment is the circle minus the point `s`
  have hsub : φ '' S ⊆ sphere 0 s := by
    rintro _ ⟨_, ⟨t, -, rfl⟩, rfl⟩
    simp only [hφdef, mem_sphere_zero_iff_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
    rw [show ((0 : ℂ) + t * 1) * I = ((t : ℂ)) * I by ring, norm_exp_ofReal_mul_I, mul_one]
  have hsup : sphere (0 : ℂ) s ⊆ φ '' S ∪ {(s : ℂ)} := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    by_cases hzs : z = s
    · exact Or.inr hzs
    left
    have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; exact hs.ne' hz.symm
    have harg0 : arg z ≠ 0 := by
      intro h
      apply hzs
      have := norm_mul_exp_arg_mul_I z
      rw [h, hz] at this
      simpa using this.symm
    set θ : ℝ := if 0 < arg z then arg z else arg z + 2 * π with hθ
    have hθI : Ioo 0 (2 * π) θ := by
      have h1 := neg_pi_lt_arg z
      have h2 := arg_le_pi z
      rw [hθ]
      split_ifs with h
      · exact ⟨h, by linarith [Real.pi_pos]⟩
      · rw [not_lt] at h
        exact ⟨by linarith [lt_of_le_of_ne h harg0], by linarith [lt_of_le_of_ne h harg0]⟩
    refine ⟨(0 : ℂ) + θ * 1, ⟨θ, hθI, rfl⟩, ?_⟩
    have hexp : exp (((θ : ℝ) : ℂ) * I) = exp ((arg z : ℂ) * I) := by
      rw [hθ]
      split_ifs
      · rfl
      · push_cast
        rw [add_mul, exp_add, show (2 * (π : ℂ)) * I = 2 * π * I by ring, exp_two_pi_mul_I, mul_one]
    simp only [hφdef]
    rw [show ((0 : ℂ) + θ * 1) * I = ((θ : ℂ)) * I by ring, hexp, ← hz]
    exact norm_mul_exp_arg_mul_I z
  have hae : (sphere (0 : ℂ) s : Set ℂ) =ᵐ[μH[1]] φ '' S := by
    have hnull : μH[1] ({(s : ℂ)} : Set ℂ) = 0 := by
      have : NullSingletonClass (μH[1] : Measure ℂ) :=
        MeasureTheory.Measure.nullSingletonClass_hausdorff ℂ one_pos
      exact measure_singleton _
    refine (ae_eq_set).2 ⟨?_, ?_⟩
    · exact measure_mono_null (fun z hz => by
        rcases hsup hz.1 with h | h
        · exact absurd h hz.2
        · exact h) hnull
    · rw [sdiff_eq_empty.2 hsub, measure_empty]
  rw [setLIntegral_congr hae, gm4b_lintegral_image_conformal hΩ hφ hSm hSΩ hρ,
    gm4b_lintegral_line (c := 0) (u := 1) norm_one measurableSet_Ioo]
  · refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
    rw [hderiv t]
    congr 2
    simp only [zero_add, mul_one]
  · exact hρ.comp (by fun_prop) |>.mul ((measurable_deriv φ).enorm)

/-- Helper: a branch `ψ` of a logarithm on an open set (`|ψ'(z)| = 1/|z|`) followed by a 1-Lipschitz real map `p`
satisfies `μH[1]((p ∘ ψ)(S)) ≤ ∫_S |z|⁻¹ dμH[1]` (W-AREA1, upper half). -/
theorem gm4b_hausdorff_branch_le {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω) {ψ : ℂ → ℂ} (hψ : LiZhongQC.IsConformalOnto ψ Ω Ω')
    (hd : ∀ z ∈ Ω, ‖deriv ψ z‖ = ‖z‖⁻¹) {p : ℂ → ℝ} (hp : LipschitzWith 1 p) {S : Set ℂ} (hS : MeasurableSet S)
    (hSΩ : S ⊆ Ω) : μH[1] ((fun z => p (ψ z)) '' S) ≤ ∫⁻ z in S, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] := by
  have h1 : μH[1] (p '' (ψ '' S)) ≤ μH[1] (ψ '' S) := by
    have h := hp.hausdorffMeasure_image_le zero_le_one (ψ '' S)
    simpa using h
  calc μH[1] ((fun z => p (ψ z)) '' S) = μH[1] (p '' (ψ '' S)) := by rw [image_image]
    _ ≤ μH[1] (ψ '' S) := h1
    _ ≤ ∫⁻ z in S, ‖deriv ψ z‖ₑ ∂μH[1] := gm4b_hausdorff_image_le hΩ hψ hS hSΩ
    _ = ∫⁻ z in S, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] := by
        refine setLIntegral_congr_fun hS fun z hz => ?_
        rw [← ofReal_norm, hd z (hSΩ hz)]

/-- Helper: `log` is a conformal map of the slit plane, with `|log'(z)| = 1/|z|`. -/
theorem gm4b_log_conformal :
    LiZhongQC.IsConformalOnto Complex.log slitPlane (Complex.log '' slitPlane) ∧
      ∀ z ∈ slitPlane, ‖deriv Complex.log z‖ = ‖z‖⁻¹ := by
  refine ⟨⟨fun z hz => (differentiableAt_log hz).differentiableWithinAt, fun a ha b hb hab => ?_, rfl⟩,
    fun z hz => ?_⟩
  · rw [← exp_log (slitPlane_ne_zero ha), ← exp_log (slitPlane_ne_zero hb), hab]
  · rw [(hasDerivAt_log hz).deriv, norm_inv]

/-- Helper: `z ↦ log(−z)` is a conformal map of the plane slit along the positive axis, with derivative of modulus
`1/|z|`. -/
theorem gm4b_logNeg_conformal :
    LiZhongQC.IsConformalOnto (fun z => Complex.log (-z)) (Neg.neg ⁻¹' slitPlane)
        ((fun z => Complex.log (-z)) '' (Neg.neg ⁻¹' slitPlane)) ∧
      ∀ z ∈ Neg.neg ⁻¹' slitPlane, ‖deriv (fun z => Complex.log (-z)) z‖ = ‖z‖⁻¹ := by
  refine ⟨⟨fun z hz => ((differentiableAt_log hz).comp z differentiableAt_id.neg).differentiableWithinAt,
    fun a ha b hb hab => ?_, rfl⟩, fun z hz => ?_⟩
  · have h : -a = -b := by
      rw [← exp_log (slitPlane_ne_zero ha), ← exp_log (slitPlane_ne_zero hb)]
      exact congrArg exp hab
    exact neg_injective h
  · have h := (hasDerivAt_log hz).comp z (hasDerivAt_neg z)
    rw [show (fun z => Complex.log (-z)) = Complex.log ∘ Neg.neg from rfl, h.deriv, norm_mul, norm_inv, norm_neg,
      norm_neg, norm_one, mul_one]

/-- Helper (weighted radial projection): `μH[1](log|S|) ≤ ∫_S |z|⁻¹ dμH[1]` for a Borel set `S` not containing `0`. -/
theorem gm4b_hausdorff_logNorm_le {S : Set ℂ} (hS : MeasurableSet S) (h0 : (0 : ℂ) ∉ S) :
    μH[1] ((fun z : ℂ => Real.log ‖z‖) '' S) ≤ ∫⁻ z in S, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] := by
  have hre : LipschitzWith 1 Complex.re := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simpa [dist_eq_norm, Real.dist_eq] using abs_re_le_norm (a - b)
  obtain ⟨hlog, hdlog⟩ := gm4b_log_conformal
  obtain ⟨hneg, hdneg⟩ := gm4b_logNeg_conformal
  set S₁ := S ∩ slitPlane
  set S₂ := S \ slitPlane
  have hS₁ : MeasurableSet S₁ := hS.inter isOpen_slitPlane.measurableSet
  have hS₂ : MeasurableSet S₂ := hS.diff isOpen_slitPlane.measurableSet
  have hS₂neg : S₂ ⊆ Neg.neg ⁻¹' slitPlane := by
    intro z hz
    have hz0 : z ≠ 0 := fun h => h0 (h ▸ hz.1)
    have h := hz.2
    simp only [mem_slitPlane_iff, not_or, not_lt, not_not] at h
    show -z ∈ slitPlane
    rw [mem_slitPlane_iff]
    left
    have hre : z.re ≠ 0 := fun hre => hz0 (Complex.ext hre h.2)
    simp only [neg_re]
    exact neg_pos.2 (lt_of_le_of_ne h.1 hre)
  have himg : (fun z : ℂ => Real.log ‖z‖) '' S ⊆
      (fun z => Complex.re (Complex.log z)) '' S₁ ∪ (fun z => Complex.re (Complex.log (-z))) '' S₂ := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases hzs : z ∈ slitPlane
    · exact Or.inl ⟨z, ⟨hz, hzs⟩, by simp [log_re]⟩
    · exact Or.inr ⟨z, ⟨hz, hzs⟩, by simp [log_re]⟩
  calc μH[1] ((fun z : ℂ => Real.log ‖z‖) '' S)
      ≤ μH[1] ((fun z => Complex.re (Complex.log z)) '' S₁) +
          μH[1] ((fun z => Complex.re (Complex.log (-z))) '' S₂) :=
        (measure_mono himg).trans (measure_union_le _ _)
    _ ≤ ∫⁻ z in S₁, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] + ∫⁻ z in S₂, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] := by
        gcongr
        · exact gm4b_hausdorff_branch_le isOpen_slitPlane hlog hdlog hre hS₁ inter_subset_right
        · exact gm4b_hausdorff_branch_le (isOpen_slitPlane.preimage continuous_neg) hneg hdneg hre hS₂ hS₂neg
    _ = ∫⁻ z in S, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] := by
        rw [← lintegral_union hS₂ (disjoint_sdiff_inter.symm.mono_left subset_rfl |>.mono_right subset_rfl)]
        rw [inter_union_sdiff]

/-- Helper (weighted angular projection): `μH[1](arg S) ≤ ∫_S |z|⁻¹ dμH[1]` for a Borel `S` in the slit plane. -/
theorem gm4b_hausdorff_arg_le {S : Set ℂ} (hS : MeasurableSet S) (hslit : S ⊆ slitPlane) :
    μH[1] (arg '' S) ≤ ∫⁻ z in S, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] := by
  have him : LipschitzWith 1 Complex.im := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simpa [dist_eq_norm, Real.dist_eq] using abs_im_le_norm (a - b)
  obtain ⟨hlog, hdlog⟩ := gm4b_log_conformal
  have h := gm4b_hausdorff_branch_le isOpen_slitPlane hlog hdlog him hS hslit
  have heq : (fun z => Complex.im (Complex.log z)) '' S = arg '' S := image_congr fun z _ => log_im z
  rwa [heq] at h

/-- Helper (conformal invariance, one inequality): for Borel curves inside the open set `Ω`,
`λ_{φ(Ω)}(φ(Γ)) ≤ λ_Ω(Γ)` (pull back the metrics: `ρ = 1_Ω (ρ' ∘ φ)|φ'|`, same area by
`LiZhongQC.rhoArea_pullback`, same lengths by `gm4b_lintegral_image_conformal`). -/
theorem gm4b_extremalLength_image_le {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ Ω Ω') {Γ : Set (Set ℂ)} (hΓ : ∀ γ ∈ Γ, MeasurableSet γ ∧ γ ⊆ Ω) :
    extremalLengthGM Ω' (image φ '' Γ) ≤ extremalLengthGM Ω Γ := by
  have hΩ' := hφ.isOpen hΩ
  rw [gm4a_extremalLengthGM_eq Ω', gm4a_extremalLengthGM_eq Ω]
  refine iSup₂_le fun ρ' hρ' => ?_
  obtain ⟨hm', h0', ht'⟩ := gm4a_mem_densitiesP0.1 hρ'
  set ρ : ℂ → ℝ≥0∞ := Ω.indicator fun z => ρ' (φ z) * ‖deriv φ z‖ₑ with hρdef
  have hm : Measurable ρ := LiZhongQC.measurable_pullback_density hΩ hφ.1.continuousOn hm'
  have hA : rhoArea ρ Ω = rhoArea ρ' Ω' := LiZhongQC.rhoArea_pullback hΩ hφ ρ'
  have hmem : ρ ∈ densitiesP0 Ω := gm4a_mem_densitiesP0.2 ⟨hm, hA ▸ h0', hA ▸ ht'⟩
  have hL : pathRhoLength (image φ '' Γ) ρ' = pathRhoLength Γ ρ := by
    rw [gm4a_pathRhoLength_eq, gm4a_pathRhoLength_eq, iInf_image]
    refine iInf_congr fun γ => iInf_congr fun hγ => ?_
    rw [gm4b_lintegral_image_conformal hΩ hφ (hΓ γ hγ).1 (hΓ γ hγ).2 hm']
    refine setLIntegral_congr_fun (hΓ γ hγ).1 fun z hz => ?_
    rw [hρdef, indicator_of_mem ((hΓ γ hγ).2 hz)]
  calc pathRhoLength (image φ '' Γ) ρ' ^ 2 / rhoArea ρ' Ω' = pathRhoLength Γ ρ ^ 2 / rhoArea ρ Ω := by
        rw [hL, hA]
    _ ≤ ⨆ ρ ∈ densitiesP0 Ω, pathRhoLength Γ ρ ^ 2 / rhoArea ρ Ω := le_iSup₂_of_le ρ hmem le_rfl

/-- Helper (conformal invariance, the other inequality): `λ_Ω(Γ) ≤ λ_{φ(Ω)}(φ(Γ))`, by
`gm4b_extremalLength_image_le` for the inverse map, which carries `φ(Γ)` back onto `Γ`. -/
theorem gm4b_extremalLength_le_image {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ Ω Ω') {Γ : Set (Set ℂ)} (hΓ : ∀ γ ∈ Γ, MeasurableSet γ ∧ γ ⊆ Ω) :
    extremalLengthGM Ω Γ ≤ extremalLengthGM Ω' (image φ '' Γ) := by
  have hΩ' := hφ.isOpen hΩ
  have hψ := hφ.symm hΩ
  have hφc : ContinuousOn φ Ω := hφ.1.continuousOn
  have hΓ' : ∀ γ' ∈ image φ '' Γ, MeasurableSet γ' ∧ γ' ⊆ Ω' := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact ⟨(hΓ γ hγ).1.image_of_continuousOn_injOn (hφc.mono (hΓ γ hγ).2) (hφ.2.1.mono (hΓ γ hγ).2),
      hφ.2.2 ▸ image_mono (hΓ γ hγ).2⟩
  have h := gm4b_extremalLength_image_le hΩ' hψ hΓ'
  have hback : image (Function.invFunOn φ Ω) '' (image φ '' Γ) = Γ := by
    rw [image_image]
    refine (image_congr fun γ hγ => ?_).trans (image_id Γ)
    rw [image_image]
    exact (image_congr fun z hz => hφ.2.1.leftInvOn_invFunOn ((hΓ γ hγ).2 hz)).trans (image_id γ)
  rwa [hback] at h

/-- **Unlabelled** (Ch. IV §1, P1:5870; cited as "conformal invariance" at P1:5929, 6162, 6189, 6347, 6382 and in
Chapter V, P1:6991, 7739, 7842, 7856). A conformal mapping `φ` transforms the metric `ρ` on `Ω` into the metric
`ρ(φ⁻¹(z)) |(φ⁻¹)'(z)|` on `φ(Ω)`. Therefore `λ_{φ(Ω)}(φ(Γ)) = λ_Ω(Γ)`, and the extremal length (1.3) is
conformally invariant.
Modelling: `φ` is a conformal map of the plane domain `Ω` onto `Ω'` (`LiZhongQC.IsConformalOnto`); `φ(Γ)` is the
family of the images `φ(γ)`, `γ ∈ Γ` [OCR: "λ_{𝒪(Ω)}" is `λ_{φ(Ω)}`]. -/
theorem extremalLengthGM_conformal {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω ∧ IsConnected Ω) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ Ω Ω') {Γ : Set (Set ℂ)} (hΓ : IsPathFamily Ω Γ) :
    extremalLengthGM Ω' (image φ '' Γ) = extremalLengthGM Ω Γ := by
  obtain ⟨-, hΓc⟩ := hΓ
  have hΓm : ∀ γ ∈ Γ, MeasurableSet γ ∧ γ ⊆ Ω := fun γ hγ => by
    refine ⟨gm4b_isPathCurve_measurableSet (hΓc γ hγ), ?_⟩
    obtain ⟨s, hs, rfl⟩ := hΓc γ hγ
    exact iUnion_subset fun n => (hs n).2
  exact le_antisymm (gm4b_extremalLength_image_le hΩ.1 hφ hΓm) (gm4b_extremalLength_le_image hΩ.1 hφ hΓm)

/-- **Definition** (extremal metric, Ch. IV §1, P1:5872). An extremal metric for `Γ` is a metric `ρ` which attains
the supremum (1.3). -/
def IsExtremalMetricGM (Ω : Set ℂ) (Γ : Set (Set ℂ)) (ρ : ℂ → ℝ≥0∞) : Prop :=
  ρ ∈ densitiesP0 Ω ∧ pathRhoLength Γ ρ ^ 2 / rhoArea ρ Ω = extremalLengthGM Ω Γ

/-- The family of connected arcs in `Ω` that join `E` and `F` (helper for `d_Ω(E, F)`, Ch. IV §1, P1:5894): all
the open Jordan arcs `f((0, 1)) ⊆ Ω`, `f` continuous and one-to-one on `[0, 1]`, with `f(0) ∈ E` and `f(1) ∈ F`,
which are curves of a path family in `Ω`. -/
def joiningFamily (Ω E F : Set ℂ) : Set (Set ℂ) :=
  {γ | IsPathCurve Ω γ ∧ ∃ f : ℝ → ℂ, ContinuousOn f (Icc 0 1) ∧ InjOn f (Icc 0 1) ∧ f 0 ∈ E ∧ f 1 ∈ F ∧
    γ = f '' Ioo 0 1}

/-- `S` separates `A` from `B` in `Ω` (helper; the reading of "separate" in §1 and §6): no component of `Ω \ S` has
points of both `A` and `B` in its closure. -/
def IsSeparatingIn (Ω S A B : Set ℂ) : Prop :=
  ∀ x ∈ Ω \ S, ¬ ((closure (connectedComponentIn (Ω \ S) x) ∩ A).Nonempty ∧
    (closure (connectedComponentIn (Ω \ S) x) ∩ B).Nonempty)

/-- The family `Γ*` of curves that separate `E` from `F` in `Ω` (helper for `d*_Ω(E, F)`, Ch. IV §1, P1:5894): any
finite union, not necessarily connected, of arcs and closed curves in `Ω` such that `E` and `F` lie in the boundaries
of distinct components of `Ω \ γ`.
Modelling: the union is a curve of a path family in `Ω`; an arc is a Jordan arc of the plane (any kind of parameter
interval), a closed curve is the image of a closed path `g : [0, 1] → ℂ`, `g(0) = g(1)`; the separation condition is
`IsSeparatingIn Ω γ E F` (module docstring). -/
def separatingFamily (Ω E F : Set ℂ) : Set (Set ℂ) :=
  {γ | IsPathCurve Ω γ ∧
    (∃ s : Set (Set ℂ), s.Finite ∧ γ = ⋃₀ s ∧ ∀ c ∈ s, IsJordanArc (toExt c) ∨
      ∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ g 0 = g 1 ∧ c = g '' Icc 0 1) ∧
    IsSeparatingIn Ω γ E F}

/-- **Definition** (extremal distance, Ch. IV §1, P1:5888–5894). For `E ⊆ Ω̄` and `F ⊆ Ω̄`, the extremal distance
from `E` to `F` is `d_Ω(E, F) = λ_Ω(Γ)`, where `Γ` is the family of connected arcs in `Ω` that join `E` and `F`.
Modelling: `Γ = joiningFamily Ω E F` (the reading of "join" in the module docstring); defined for all sets, used
for `E, F ⊆ Ω̄`. -/
def extremalDistGM (Ω E F : Set ℂ) : ℝ≥0∞ :=
  extremalLengthGM Ω (joiningFamily Ω E F)

/-- **Definition** (conjugate extremal distance, Ch. IV §1, P1:5894). `d*_Ω(E, F)` is the extremal length of the
family `Γ*` of curves that separate `E` from `F`. -/
def conjExtremalDistGM (Ω E F : Set ℂ) : ℝ≥0∞ :=
  extremalLengthGM Ω (separatingFamily Ω E F)

/-! ### GM4-B helpers (-e8): uniqueness of extremal metrics, the rectangle and the annulus -/

/-- Helper: the content of `thm4_2_1_c` (Ch. IV §2), placed here because of the import order (Ch04/S02 imports this
file, and Examples 1.1 and 1.2 need it): if `0 < λ_Ω(Γ) < ∞`, two extremal metrics of equal area agree almost
everywhere on `Ω` (the same proof, through the helpers moved here from Ch04/S02). -/
theorem gm4b_extremal_ae_eq {Ω : Set ℂ} {Γ : Set (Set ℂ)} (hpos : 0 < extremalLengthGM Ω Γ)
    (hfin : extremalLengthGM Ω Γ < ⊤) {ρ₁ ρ₂ : ℂ → ℝ≥0∞} (hρ₁ : IsExtremalMetricGM Ω Γ ρ₁)
    (hρ₂ : IsExtremalMetricGM Ω Γ ρ₂) (hA : rhoArea ρ₁ Ω = rhoArea ρ₂ Ω) : ρ₁ =ᵐ[volume.restrict Ω] ρ₂ := by
  obtain ⟨hρ₁m, hr₁⟩ := hρ₁
  obtain ⟨hρ₂m, hr₂⟩ := hρ₂
  have h₁₂ : pathRhoLength Γ ρ₁ ^ 2 / rhoArea ρ₁ Ω = pathRhoLength Γ ρ₂ ^ 2 / rhoArea ρ₂ Ω := hr₁.trans hr₂.symm
  have hc₂ : 2⁻¹ * rhoArea ρ₁ Ω ^ (-(1 / 2 : ℝ)) = 2⁻¹ * rhoArea ρ₂ Ω ^ (-(1 / 2 : ℝ)) := by rw [hA]
  obtain ⟨hL, hA1, hA4⟩ := gm4a_rho3_bounds hρ₁m hρ₂m h₁₂ rfl hc₂
  have hmem := gm4a_rho3_mem (gm4a_mem_densitiesP0.1 hρ₁m).1 (gm4a_mem_densitiesP0.1 hρ₂m).1 _ _ hA1 hA4
  have hge := gm4a_le_div_of_le_one hL hA1
  have heq := le_antisymm ((gm4a_ratio_le (Γ := Γ) hmem).trans hr₁.symm.le) hge
  have h1 := gm4a_eq_one_of_div_eq (by rw [hr₁]; exact hpos) (by rw [hr₁]; exact hfin) hL hA1 hA4 heq
  obtain ⟨hc0, hctop, hf, -⟩ := gm4a_coeff Γ hρ₁m rfl
  obtain ⟨-, -, hg, -⟩ := gm4a_coeff Γ hρ₂m hc₂
  have hae := gm4a_ae_eq_of_rhoArea_add ((gm4a_mem_densitiesP0.1 hρ₁m).1.const_mul _)
    ((gm4a_mem_densitiesP0.1 hρ₂m).1.const_mul _) (by rw [hf, hg]; exact gm4a_quarter_add_lt_top)
    (by rw [h1, hf, hg]; exact gm4a_one_eq_quarters)
  exact gm4a_ae_eq_of_const_mul hc0 hctop hae

/-- Helper: a positive finite multiple of an extremal metric is extremal. -/
theorem gm4b_isExtremalMetricGM_const_mul {Ω : Set ℂ} {Γ : Set (Set ℂ)} {ρ : ℂ → ℝ≥0∞}
    (hρ : IsExtremalMetricGM Ω Γ ρ) {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ⊤) :
    IsExtremalMetricGM Ω Γ (fun z => c * ρ z) := by
  obtain ⟨hm, hr⟩ := hρ
  obtain ⟨hmeas, h0, htop⟩ := gm4a_mem_densitiesP0.1 hm
  have hA : rhoArea (fun z => c * ρ z) Ω = c ^ 2 * rhoArea ρ Ω := LiZhongQC.rhoArea_const_mul ρ Ω hc
  have hL : pathRhoLength Γ (fun z => c * ρ z) = c * pathRhoLength Γ ρ := by
    rw [gm4a_pathRhoLength_eq, gm4a_pathRhoLength_eq, ENNReal.mul_iInf_of_ne hc₀ hc]
    refine iInf_congr fun γ => ?_
    rw [ENNReal.mul_iInf_of_ne hc₀ hc]
    exact iInf_congr fun _ => lintegral_const_mul c hmeas
  refine ⟨gm4a_mem_densitiesP0.2 ⟨hmeas.const_mul c, ?_, ?_⟩, ?_⟩
  · rw [hA]
    exact ENNReal.mul_pos (pow_ne_zero 2 hc₀) h0.ne'
  · rw [hA]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top hc.lt_top) htop
  · rw [hL, hA, mul_pow, ENNReal.mul_div_mul_left _ _ (pow_ne_zero 2 hc₀) (ENNReal.pow_ne_top hc), hr]

/-- Helper: every extremal metric of a family with `0 < λ < ∞` that has a constant extremal metric (resp. an extremal
metric `ρ₀`) is a constant multiple of it almost everywhere: `ρ = c ρ₀` a.e. for some finite `c > 0`. -/
theorem gm4b_extremal_eq_const_mul {Ω : Set ℂ} {Γ : Set (Set ℂ)} (hpos : 0 < extremalLengthGM Ω Γ)
    (hfin : extremalLengthGM Ω Γ < ⊤) {ρ₀ ρ : ℂ → ℝ≥0∞} (hρ₀ : IsExtremalMetricGM Ω Γ ρ₀)
    (hρ : IsExtremalMetricGM Ω Γ ρ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ρ =ᵐ[volume.restrict Ω] fun z => c * ρ₀ z := by
  obtain ⟨hm₀, -⟩ := id hρ₀
  obtain ⟨hm, -⟩ := id hρ
  obtain ⟨-, h₀0, h₀t⟩ := gm4a_mem_densitiesP0.1 hm₀
  obtain ⟨-, h0, ht⟩ := gm4a_mem_densitiesP0.1 hm
  set q := rhoArea ρ Ω / rhoArea ρ₀ Ω with hq
  have hq0 : q ≠ 0 := ENNReal.div_ne_zero.2 ⟨h0.ne', h₀t.ne⟩
  have hqt : q ≠ ⊤ := ENNReal.div_ne_top ht.ne h₀0.ne'
  set c := q ^ (1 / 2 : ℝ) with hcdef
  have hc0 : c ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hq0) hqt).ne'
  have hct : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hqt
  have hc2 : c ^ 2 = q := by
    rw [hcdef, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hext := gm4b_isExtremalMetricGM_const_mul hρ₀ hc0 hct
  refine ⟨c, hc0, hct, gm4b_extremal_ae_eq hpos hfin hρ hext ?_⟩
  rw [LiZhongQC.rhoArea_const_mul ρ₀ Ω hct, hc2, hq, ENNReal.div_mul_cancel h₀0.ne' h₀t.ne]

/-- Helper (rectangle, lower bound): a curve joining the vertical sides of `(0, ℓ) × (0, h)` has length `≥ ℓ` (its
real projection covers `(0, ℓ)`). -/
theorem gm4b_rect_joining_ge {ℓ h : ℝ} (hℓ : 0 < ℓ) {γ : Set ℂ}
    (hγ : γ ∈ joiningFamily (Ioo 0 ℓ ×ℂ Ioo 0 h) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h)) :
    ENNReal.ofReal ℓ ≤ μH[1] γ := by
  have _ := hℓ
  obtain ⟨-, f, hfc, hfi, hf0, hf1, hfγ⟩ := hγ
  rw [Complex.mem_reProdIm] at hf0 hf1
  simp only [Set.mem_singleton_iff] at hf0 hf1
  obtain ⟨hf0re, -⟩ := hf0
  obtain ⟨hf1re, -⟩ := hf1
  rw [hfγ]
  have hsub : Ioo 0 ℓ ⊆ Complex.re '' (f '' Ioo 0 1) := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hcont : ContinuousOn (fun x : ℝ => (f x).re) (Icc 0 1) :=
      Complex.continuous_re.comp_continuousOn hfc
    have hmem : t ∈ Icc ((fun x : ℝ => (f x).re) 0) ((fun x : ℝ => (f x).re) 1) := by
      simp only [Set.mem_Icc, hf0re, hf1re]
      exact ⟨ht0.le, ht1.le⟩
    obtain ⟨x, hx, hxt⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont hmem
    rw [Set.mem_Icc] at hx
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hxt
      simp only [hf0re] at hxt
      exact (ne_of_gt ht0) hxt.symm
    have hx1 : x ≠ 1 := by
      intro h
      rw [h] at hxt
      simp only [hf1re] at hxt
      exact (ne_of_lt ht1) hxt.symm
    exact ⟨f x, ⟨x, ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩, rfl⟩, hxt⟩
  calc ENNReal.ofReal ℓ = μH[1] (Ioo 0 ℓ) := by
        rw [hausdorffMeasure_real, Real.volume_Ioo, sub_zero]
    _ ≤ μH[1] (Complex.re '' (f '' Ioo 0 1)) := measure_mono hsub
    _ ≤ μH[1] (f '' Ioo 0 1) := by
        have hre : LipschitzWith 1 Complex.re := by
          refine LipschitzWith.of_dist_le_mul fun a b => ?_
          simpa [dist_eq_norm, Real.dist_eq] using abs_re_le_norm (a - b)
        simpa using hre.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1) (f '' Ioo 0 1)

/-- Helper: the image of a bounded nontrivial interval under an affine map `t ↦ c + t v` (`v ≠ 0`) is a rectifiable
arc (a segment of a line). -/
theorem gm4b_isRectifiableArc_affine {c v : ℂ} (hv : v ≠ 0) {I : Set ℝ} (hI : I.OrdConnected) (hn : I.Nontrivial)
    (hb : Bornology.IsBounded I) : IsRectifiableArc ((fun t : ℝ => c + t * v) '' I) := by
  have hemb : IsEmbedding (fun t : ℝ => c + t * v) := by
    have h1 : IsEmbedding (fun t : ℝ => (t : ℂ)) := Complex.isometry_ofReal.isEmbedding
    have h2 := (Homeomorph.mulRight₀ v hv).isEmbedding
    have h3 := (Homeomorph.addLeft c).isEmbedding
    exact h3.comp (h2.comp h1)
  refine ⟨⟨I, hI, hn, fun t => (((c + t * v : ℂ)) : ExtPlane), ?_, ?_⟩, ?_⟩
  · exact OnePoint.isOpenEmbedding_coe.isEmbedding.comp (hemb.comp IsEmbedding.subtypeVal)
  · rw [LiZhongQC.toExt, image_image]
  · have hlip : LipschitzWith ‖v‖₊ (fun t : ℝ => c + t * v) := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      simp only [dist_eq_norm]
      rw [show c + a * v - (c + b * v) = ((a - b : ℝ) : ℂ) * v by push_cast; ring, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, mul_comm]
      rfl
    have h := hlip.hausdorffMeasure_image_le zero_le_one I
    refine lt_of_le_of_lt h ?_
    rw [hausdorffMeasure_real]
    exact ENNReal.mul_lt_top (by simp) hb.measure_lt_top

/-- Helper: the horizontal segment at height `y ∈ (0, h)` is a member of the joining family of the vertical sides of
the rectangle `(0, ℓ) × (0, h)`. -/
theorem gm4b_rect_seg_mem {ℓ h y : ℝ} (hℓ : 0 < ℓ) (hy : y ∈ Ioo 0 h) :
    (fun t : ℝ => (y : ℂ) * I + t * 1) '' Ioo 0 ℓ ∈
      joiningFamily (Ioo 0 ℓ ×ℂ Ioo 0 h) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h) := by
  set S : Set ℂ := (fun t : ℝ => (y : ℂ) * I + t * 1) '' Ioo 0 ℓ with hS
  set f : ℝ → ℂ := fun s => (y : ℂ) * I + ((ℓ * s : ℝ) : ℂ) * 1 with hf
  have hSsub : S ⊆ Ioo 0 ℓ ×ℂ Ioo 0 h := by
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_reProdIm]
    refine ⟨?_, ?_⟩ <;> simp [ht.1, ht.2, hy.1, hy.2]
  have himg : f '' Ioo 0 1 = S := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨ℓ * s, ⟨mul_pos hℓ hs.1, by nlinarith [hs.2]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t / ℓ, ⟨div_pos ht.1 hℓ, by rw [div_lt_one hℓ]; exact ht.2⟩, ?_⟩
      simp only [hf]
      rw [mul_div_cancel₀ _ hℓ.ne']
  have harc : IsRectifiableArc S :=
    gm4b_isRectifiableArc_affine (c := (y : ℂ) * I) (v := 1) one_ne_zero ordConnected_Ioo
      ⟨ℓ / 3, ⟨by positivity, by linarith⟩, 2 * ℓ / 3, ⟨by positivity, by linarith⟩, by
        intro h; linarith⟩ (Metric.isBounded_Ioo 0 ℓ)
  refine ⟨⟨fun _ => S, fun n => ⟨harc, hSsub⟩, (iUnion_const S).symm⟩, f, ?_, ?_, ?_, ?_, himg.symm⟩
  · fun_prop
  · intro a _ b _ hab
    have h1 : ℓ * a = ℓ * b := by
      have := congrArg Complex.re hab
      simpa [hf] using this
    exact mul_left_cancel₀ hℓ.ne' h1
  · rw [mem_reProdIm]
    refine ⟨by simp [hf], ?_⟩
    simp [hf, hy.1.le, hy.2.le]
  · rw [mem_reProdIm]
    refine ⟨by simp [hf], ?_⟩
    simp [hf, hy.1.le, hy.2.le]

/-- Helper: Cauchy–Schwarz, `(∫ f)² ≤ μ(univ) ∫ f²`, on a general measure space. -/
theorem gm4b_lintegral_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) : (∫⁻ x, f x ∂μ) ^ 2 ≤ μ univ * ∫⁻ x, f x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ≥0∞)) (g := f) aemeasurable_const hf
  simp only [Pi.mul_apply, lintegral_const, ENNReal.rpow_two, one_pow, one_mul] at h
  calc (∫⁻ x, f x ∂μ) ^ 2
      ≤ (μ univ ^ (1 / 2 : ℝ) * (∫⁻ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left' (by simpa using h) 2
    _ = μ univ * ∫⁻ x, f x ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

/-- Helper (rectangle, Cauchy–Schwarz on the segments): if `L` is at most the integral of `G x` over `(0, b)` for
every `x ∈ (0, a)`, then `a L² ≤ b ∫_0^a ∫_0^b G²`. -/
theorem gm4b_rect_core {a b : ℝ} {G : ℝ → ℝ → ℝ≥0∞} (hG : ∀ x, Measurable (G x))
    {L : ℝ≥0∞} (hL : ∀ x ∈ Ioo 0 a, L ≤ ∫⁻ y in Ioo 0 b, G x y) :
    ENNReal.ofReal a * L ^ 2 ≤ ENNReal.ofReal b * ∫⁻ x in Ioo 0 a, ∫⁻ y in Ioo 0 b, G x y ^ 2 := by
  have h1 : ∀ x ∈ Ioo 0 a, L ^ 2 ≤ ENNReal.ofReal b * ∫⁻ y in Ioo 0 b, G x y ^ 2 := fun x hx => by
    calc L ^ 2 ≤ (∫⁻ y in Ioo 0 b, G x y) ^ 2 := pow_le_pow_left' (hL x hx) 2
      _ ≤ (volume.restrict (Ioo 0 b)) univ * ∫⁻ y in Ioo 0 b, G x y ^ 2 :=
          gm4b_lintegral_sq_le _ (hG x).aemeasurable
      _ = ENNReal.ofReal b * ∫⁻ y in Ioo 0 b, G x y ^ 2 := by
          rw [Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]
  calc ENNReal.ofReal a * L ^ 2 = ∫⁻ _ in Ioo 0 a, L ^ 2 := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero, mul_comm]
    _ ≤ ∫⁻ x in Ioo 0 a, ENNReal.ofReal b * ∫⁻ y in Ioo 0 b, G x y ^ 2 := setLIntegral_mono' measurableSet_Ioo h1
    _ = ENNReal.ofReal b * ∫⁻ x in Ioo 0 a, ∫⁻ y in Ioo 0 b, G x y ^ 2 := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Helper (arithmetic): `a X ≤ b A` gives `X / A ≤ b / a` in `[0, ∞]`, for `0 < A < ∞`. -/
theorem gm4b_div_le_of_mul_le {a b : ℝ} (ha : 0 < a) {X A : ℝ≥0∞} (hA0 : A ≠ 0) (hAt : A ≠ ⊤)
    (h : ENNReal.ofReal a * X ≤ ENNReal.ofReal b * A) : X / A ≤ ENNReal.ofReal (b / a) := by
  rw [ENNReal.div_le_iff hA0 hAt]
  have ha0 : ENNReal.ofReal a ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 ha
  calc X = (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal a * X) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal b * A) := by gcongr
    _ = ENNReal.ofReal (b / a) * A := by
        rw [ENNReal.ofReal_div_of_pos ha, ENNReal.div_eq_inv_mul, mul_assoc]

/-- Helper (rectangle, vertical segments): if the family `Γ` contains all vertical segments, then
`L²/A ≤ h/ℓ` for every metric. -/
theorem gm4b_rect_vseg_ratio_le {ℓ h : ℝ} (hℓ : 0 < ℓ) {Γ : Set (Set ℂ)}
    (hΓ : ∀ x ∈ Ioo 0 ℓ, (fun t : ℝ => (x : ℂ) + t * I) '' Ioo 0 h ∈ Γ) {ρ : ℂ → ℝ≥0∞}
    (hρ : ρ ∈ densitiesP0 (Ioo 0 ℓ ×ℂ Ioo 0 h)) :
    pathRhoLength Γ ρ ^ 2 / rhoArea ρ (Ioo 0 ℓ ×ℂ Ioo 0 h) ≤ ENNReal.ofReal (h / ℓ) := by
  obtain ⟨hm, hA0, hAt⟩ := gm4a_mem_densitiesP0.1 hρ
  have hR : Ioo 0 ℓ ×ℂ Ioo 0 h = LiZhongQC.rectangle ℓ h := (LiZhongQC.rectangle_eq_reProdIm ℓ h).symm
  have hA : rhoArea ρ (Ioo 0 ℓ ×ℂ Ioo 0 h) = ∫⁻ x in Ioo 0 ℓ, ∫⁻ y in Ioo 0 h, ρ ((x : ℂ) + (y : ℂ) * I) ^ 2 := by
    rw [gm4a_rhoArea_eq, hR]
    exact LiZhongQC.setLIntegral_rectangle (hm.pow_const 2)
  have hcore := gm4b_rect_core (G := fun x y => ρ ((x : ℂ) + (y : ℂ) * I)) (fun x => hm.comp (by fun_prop))
    (L := pathRhoLength Γ ρ) fun x hx => by
      refine (iInf₂_le _ (hΓ x hx)).trans_eq ?_
      rw [gm4b_lintegral_line (c := (x : ℂ)) (u := I) (by simp) measurableSet_Ioo hm]
  rw [← hA] at hcore
  exact gm4b_div_le_of_mul_le hℓ hA0.ne' hAt.ne hcore

/-- Helper (rectangle, horizontal segments): if the family `Γ` contains all horizontal segments, then
`L²/A ≤ ℓ/h` for every metric. -/
theorem gm4b_rect_hseg_ratio_le {ℓ h : ℝ} (hh : 0 < h) {Γ : Set (Set ℂ)}
    (hΓ : ∀ y ∈ Ioo 0 h, (fun t : ℝ => (y : ℂ) * I + t * 1) '' Ioo 0 ℓ ∈ Γ) {ρ : ℂ → ℝ≥0∞}
    (hρ : ρ ∈ densitiesP0 (Ioo 0 ℓ ×ℂ Ioo 0 h)) :
    pathRhoLength Γ ρ ^ 2 / rhoArea ρ (Ioo 0 ℓ ×ℂ Ioo 0 h) ≤ ENNReal.ofReal (ℓ / h) := by
  obtain ⟨hm, hA0, hAt⟩ := gm4a_mem_densitiesP0.1 hρ
  have hR : Ioo 0 ℓ ×ℂ Ioo 0 h = LiZhongQC.rectangle ℓ h := (LiZhongQC.rectangle_eq_reProdIm ℓ h).symm
  have hmeas : Measurable fun p : ℝ × ℝ => ρ ((p.1 : ℂ) + (p.2 : ℂ) * I) ^ 2 :=
    (hm.comp (by fun_prop)).pow_const 2
  have hA : rhoArea ρ (Ioo 0 ℓ ×ℂ Ioo 0 h) = ∫⁻ y in Ioo 0 h, ∫⁻ x in Ioo 0 ℓ, ρ ((x : ℂ) + (y : ℂ) * I) ^ 2 := by
    rw [gm4a_rhoArea_eq, hR, LiZhongQC.setLIntegral_rectangle (hm.pow_const 2)]
    exact lintegral_lintegral_swap hmeas.aemeasurable
  have hcore := gm4b_rect_core (G := fun y x => ρ ((x : ℂ) + (y : ℂ) * I)) (fun y => hm.comp (by fun_prop))
    (L := pathRhoLength Γ ρ) fun y hy => by
      refine (iInf₂_le _ (hΓ y hy)).trans_eq ?_
      rw [gm4b_lintegral_line (c := (y : ℂ) * I) (u := 1) norm_one measurableSet_Ioo hm]
      refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
      rw [mul_one, add_comm]
  rw [← hA] at hcore
  exact gm4b_div_le_of_mul_le hh hA0.ne' hAt.ne hcore

/-- Helper (rectangle, upper bound): for every metric, `L²/A ≤ ℓ/h` (horizontal segments, Cauchy–Schwarz, Fubini). -/
theorem gm4b_rect_ratio_le {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) {ρ : ℂ → ℝ≥0∞}
    (hρ : ρ ∈ densitiesP0 (Ioo 0 ℓ ×ℂ Ioo 0 h)) :
    pathRhoLength (joiningFamily (Ioo 0 ℓ ×ℂ Ioo 0 h) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h)) ρ ^ 2 /
      rhoArea ρ (Ioo 0 ℓ ×ℂ Ioo 0 h) ≤ ENNReal.ofReal (ℓ / h) := by
  have _ := hℓ
  exact gm4b_rect_hseg_ratio_le hh (fun y hy => gm4b_rect_seg_mem hℓ hy) hρ

/-- Helper (rectangle, the metric `ρ = 1`): it is a metric of area `ℓh`, and the joining family has `1`-length `ℓ`. -/
theorem gm4b_rect_one {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) :
    (fun _ => (1 : ℝ≥0∞)) ∈ densitiesP0 (Ioo 0 ℓ ×ℂ Ioo 0 h) ∧
      rhoArea (fun _ => (1 : ℝ≥0∞)) (Ioo 0 ℓ ×ℂ Ioo 0 h) = ENNReal.ofReal (ℓ * h) ∧
      pathRhoLength (joiningFamily (Ioo 0 ℓ ×ℂ Ioo 0 h) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h)) (fun _ => 1) =
        ENNReal.ofReal ℓ := by
  have hR : (Ioo 0 ℓ ×ℂ Ioo 0 h) = LiZhongQC.rectangle ℓ h := LiZhongQC.rectangle_eq_reProdIm ℓ h |>.symm
  have hvol : volume (Ioo 0 ℓ ×ℂ Ioo 0 h) = ENNReal.ofReal (ℓ * h) := by
    rw [hR, LiZhongQC.volume_rectangle, ← ENNReal.ofReal_mul hℓ.le]
  have hmeas : Measurable (fun _ : ℂ => (1 : ℝ≥0∞)) := measurable_const
  have hlint : ∀ {D : Set ℂ}, ∫⁻ z in D, (1 : ℝ≥0∞) = volume D := by
    intro D
    rw [lintegral_one, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  have hA : rhoArea (fun _ => (1 : ℝ≥0∞)) (Ioo 0 ℓ ×ℂ Ioo 0 h) = ENNReal.ofReal (ℓ * h) := by
    rw [gm4a_rhoArea_eq]
    simp only [one_pow]
    rw [hlint, hvol]
  have hpos : (0 : ℝ≥0∞) < rhoArea (fun _ => (1 : ℝ≥0∞)) (Ioo 0 ℓ ×ℂ Ioo 0 h) := by
    rw [hA]
    exact ENNReal.ofReal_pos.2 (mul_pos hℓ hh)
  have htop : rhoArea (fun _ => (1 : ℝ≥0∞)) (Ioo 0 ℓ ×ℂ Ioo 0 h) < ⊤ := by
    rw [hA]
    exact ENNReal.ofReal_lt_top
  have hmem : (fun _ => (1 : ℝ≥0∞)) ∈ densitiesP0 (Ioo 0 ℓ ×ℂ Ioo 0 h) :=
    gm4a_mem_densitiesP0.2 ⟨hmeas, hpos, htop⟩
  set f : ℝ → ℂ := fun t => (ℓ * t : ℂ) + (h / 2 : ℂ) * I with hf
  have hfre : ∀ t : ℝ, (f t).re = ℓ * t := by intro t; simp [hf]
  have hfim : ∀ t : ℝ, (f t).im = h / 2 := by intro t; simp [hf]
  have hcurve : f '' Ioo 0 1 ⊆ Ioo 0 ℓ ×ℂ Ioo 0 h := by
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_reProdIm]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hfre]; exact mul_pos hℓ ht.1
    · rw [hfre]; nlinarith [ht.2, hℓ]
    · rw [hfim]; linarith
    · rw [hfim]; linarith
  have hseg : f '' Ioo 0 1 ∈
      joiningFamily (Ioo 0 ℓ ×ℂ Ioo 0 h) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h) := by
    refine ⟨?_, f, ?_, ?_, ?_, ?_, rfl⟩
    · refine ⟨fun _ => f '' Ioo 0 1, fun n => ⟨?_, hcurve⟩, ?_⟩
      · have himg : f '' Ioo 0 1 = (fun t : ℝ => ((h / 2 : ℂ) * I) + t * (ℓ : ℂ)) '' Ioo 0 1 :=
          image_congr fun t _ => by simp only [hf]; ring
        rw [himg]
        exact gm4b_isRectifiableArc_affine (by exact_mod_cast hℓ.ne') ordConnected_Ioo
          ⟨1 / 3, ⟨by norm_num, by norm_num⟩, 2 / 3, ⟨by norm_num, by norm_num⟩, by norm_num⟩ (Metric.isBounded_Ioo 0 1)
      · rw [iUnion_const]
    · fun_prop
    · intro a ha b hb hab
      have h1 : ℓ * a = ℓ * b := by
        have := congrArg Complex.re hab
        simpa [hf] using this
      exact mul_left_cancel₀ hℓ.ne' h1
    · rw [mem_reProdIm]
      refine ⟨?_, ?_, ?_⟩
      · simp [hf]
      · rw [hfim]; linarith
      · rw [hfim]; linarith
    · rw [mem_reProdIm]
      refine ⟨?_, ?_, ?_⟩
      · simp [hf]
      · rw [hfim]; linarith
      · rw [hfim]; linarith
  have hone : ∀ γ : Set ℂ, ∫⁻ z in γ, (1 : ℝ≥0∞) ∂μH[1] = μH[1] γ := fun γ => by simp
  have hlen : μH[1] (f '' Ioo 0 1) = ENNReal.ofReal ℓ := by
    have himg2 : f '' Ioo 0 1 = (fun t : ℝ => ((h / 2 : ℂ) * I) + t * 1) '' Ioo 0 ℓ := by
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨ℓ * t, ⟨mul_pos hℓ ht.1, by nlinarith [ht.2]⟩, by simp only [hf]; push_cast; ring⟩
      · rintro ⟨s, hs, rfl⟩
        refine ⟨s / ℓ, ⟨div_pos hs.1 hℓ, by rw [div_lt_one hℓ]; exact hs.2⟩, ?_⟩
        have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
        simp only [hf]
        push_cast
        field_simp
        ring
    have hgl := gm4b_lintegral_line (c := (h / 2 : ℂ) * I) (u := 1) norm_one
      (A := Ioo (0 : ℝ) ℓ) measurableSet_Ioo (ρ := fun _ : ℂ => (1 : ℝ≥0∞)) measurable_const
    rw [hone] at hgl
    rw [himg2, hgl]
    simp [Real.volume_Ioo]
  refine ⟨hmem, hA, ?_⟩
  simp only [pathRhoLength, hone]
  exact le_antisymm ((iInf₂_le (f '' Ioo 0 1) hseg).trans_eq hlen)
    (le_iInf₂ fun γ hγ => gm4b_rect_joining_ge hℓ hγ)

/-- Helper (rectangle, separating curves): a curve separating the vertical sides of `(0, ℓ) × (0, h)` meets every
horizontal segment, so it has length `≥ h`. -/
theorem gm4b_rect_sep_ge {ℓ h : ℝ} (hh : 0 < h) {γ : Set ℂ}
    (hγ : γ ∈ separatingFamily (Ioo 0 ℓ ×ℂ Ioo 0 h) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h)) :
    ENNReal.ofReal h ≤ μH[1] γ := by
  have _ := hh
  obtain ⟨hpc, -, hsep⟩ := hγ
  by_cases hℓ : 0 < ℓ
  swap
  · exfalso
    obtain ⟨s, hs, -⟩ := hpc
    obtain ⟨⟨I', -, hn, g, -, hgC⟩, -⟩ := (hs 0).1
    obtain ⟨t, ht⟩ := hn.nonempty
    have hmem : g t ∈ LiZhongQC.toExt (s 0) := hgC ▸ mem_image_of_mem g ht
    obtain ⟨z, hz, -⟩ := hmem
    have h1 := (hs 0).2 hz
    rw [mem_reProdIm] at h1
    exact hℓ (h1.1.1.trans h1.1.2)
  have hsub : Ioo 0 h ⊆ Complex.im '' γ := by
    intro y hy
    by_contra hno
    set g : ℝ → ℂ := fun t => (t : ℂ) + (y : ℂ) * I with hg
    have hgc : Continuous g := by fun_prop
    set Hy : Set ℂ := g '' Ioo 0 ℓ with hHy
    have hHy_conn : IsPreconnected Hy := isPreconnected_Ioo.image g hgc.continuousOn
    have hz0H : g (ℓ / 2) ∈ Hy := ⟨ℓ / 2, ⟨half_pos hℓ, half_lt_self hℓ⟩, rfl⟩
    have hHyR : Hy ⊆ Ioo 0 ℓ ×ℂ Ioo 0 h \ γ := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨?_, fun hmem => hno ⟨_, hmem, by simp [hg]⟩⟩
      rw [mem_reProdIm]
      simp [hg, ht.1, ht.2, hy.1, hy.2]
    have hHyK : Hy ⊆ connectedComponentIn (Ioo 0 ℓ ×ℂ Ioo 0 h \ γ) (g (ℓ / 2)) :=
      hHy_conn.subset_connectedComponentIn hz0H hHyR
    have hcl : g '' closure (Ioo 0 ℓ) ⊆ closure Hy := image_closure_subset_closure_image hgc
    rw [closure_Ioo hℓ.ne] at hcl
    refine hsep (g (ℓ / 2)) (hHyR hz0H) ⟨⟨g 0, closure_mono hHyK (hcl ⟨0, ⟨le_rfl, hℓ.le⟩, rfl⟩), ?_⟩,
      ⟨g ℓ, closure_mono hHyK (hcl ⟨ℓ, ⟨hℓ.le, le_rfl⟩, rfl⟩), ?_⟩⟩
    · rw [mem_reProdIm]
      simp [hg, hy.1.le, hy.2.le]
    · rw [mem_reProdIm]
      simp [hg, hy.1.le, hy.2.le]
  have him : LipschitzWith 1 Complex.im := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simpa [dist_eq_norm, Real.dist_eq] using abs_im_le_norm (a - b)
  calc ENNReal.ofReal h = μH[1] (Ioo 0 h) := by
        rw [hausdorffMeasure_real, Real.volume_Ioo, sub_zero]
    _ ≤ μH[1] (Complex.im '' γ) := measure_mono hsub
    _ ≤ μH[1] γ := by
        simpa using him.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1) γ

/-- Helper: the vertical segment at abscissa `x ∈ (0, ℓ)` is a curve of the separating family of the vertical sides of
the rectangle `(0, ℓ) × (0, h)`. -/
theorem gm4b_rect_vseg_sep_mem {ℓ h x : ℝ} (hh : 0 < h) (hx : x ∈ Ioo 0 ℓ) :
    (fun t : ℝ => (x : ℂ) + t * I) '' Ioo 0 h ∈
      separatingFamily (Ioo 0 ℓ ×ℂ Ioo 0 h) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h) := by
  set S : Set ℂ := (fun t : ℝ => (x : ℂ) + t * I) '' Ioo 0 h with hS
  have hSsub : S ⊆ Ioo 0 ℓ ×ℂ Ioo 0 h := by
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_reProdIm]
    refine ⟨?_, ?_⟩ <;> simp [hx.1, hx.2, ht.1, ht.2]
  have harc : IsRectifiableArc S :=
    gm4b_isRectifiableArc_affine (c := (x : ℂ)) (v := I) I_ne_zero ordConnected_Ioo
      ⟨h / 3, ⟨by positivity, by linarith⟩, 2 * h / 3, ⟨by positivity, by linarith⟩, by
        intro h'; linarith⟩ (Metric.isBounded_Ioo 0 h)
  refine ⟨⟨fun _ => S, fun n => ⟨harc, hSsub⟩, (iUnion_const S).symm⟩,
    ⟨{S}, finite_singleton _, (sUnion_singleton _).symm, fun c hc => Or.inl ?_⟩, ?_⟩
  · rw [mem_singleton_iff] at hc
    subst hc
    exact harc.1
  · intro z hz hboth
    obtain ⟨⟨p, hpK, hpE⟩, ⟨q, hqK, hqF⟩⟩ := hboth
    set K := connectedComponentIn (Ioo 0 ℓ ×ℂ Ioo 0 h \ S) z with hK
    have hKsub : K ⊆ Ioo 0 ℓ ×ℂ Ioo 0 h \ S := connectedComponentIn_subset _ _
    have hKconn : IsPreconnected K := isPreconnected_connectedComponentIn
    have hsplit : K ⊆ {w : ℂ | w.re < x} ∪ {w : ℂ | x < w.re} := by
      intro w hw
      obtain ⟨hwR, hwS⟩ := hKsub hw
      rcases lt_trichotomy w.re x with h1 | h1 | h1
      · exact Or.inl h1
      · exfalso
        apply hwS
        rw [mem_reProdIm] at hwR
        refine ⟨w.im, hwR.2, ?_⟩
        apply Complex.ext <;> simp [h1]
      · exact Or.inr h1
    rcases hKconn.subset_or_subset (isOpen_lt Complex.continuous_re continuous_const)
      (isOpen_lt continuous_const Complex.continuous_re)
      (Set.disjoint_left.2 fun w (hw1 : w.re < x) (hw2 : x < w.re) => lt_irrefl _ (hw1.trans hw2)) hsplit with h1 | h1
    · have hcl : closure K ⊆ {w : ℂ | w.re ≤ x} :=
        closure_minimal (h1.trans fun w (hw : w.re < x) => (le_of_lt hw : w.re ≤ x))
          (isClosed_le Complex.continuous_re continuous_const)
      have h2 : q.re ≤ x := hcl hqK
      rw [mem_reProdIm] at hqF
      have h3 : q.re = ℓ := by simpa using hqF.1
      linarith [hx.2]
    · have hcl : closure K ⊆ {w : ℂ | x ≤ w.re} :=
        closure_minimal (h1.trans fun w (hw : x < w.re) => (le_of_lt hw : x ≤ w.re))
          (isClosed_le continuous_const Complex.continuous_re)
      have h2 : x ≤ p.re := hcl hpK
      rw [mem_reProdIm] at hpE
      have h3 : p.re = 0 := by simpa using hpE.1
      linarith [hx.1]

/-- Helper: the vertical segment at abscissa `x ∈ (0, ℓ)` is a member of the joining family of the horizontal sides of
the rectangle `(0, ℓ) × (0, h)`. -/
theorem gm4b_rect_vseg_join_mem {ℓ h x : ℝ} (hh : 0 < h) (hx : x ∈ Ioo 0 ℓ) :
    (fun t : ℝ => (x : ℂ) + t * I) '' Ioo 0 h ∈
      joiningFamily (Ioo 0 ℓ ×ℂ Ioo 0 h) (Icc 0 ℓ ×ℂ {0}) (Icc 0 ℓ ×ℂ {h}) := by
  set S : Set ℂ := (fun t : ℝ => (x : ℂ) + t * I) '' Ioo 0 h with hS
  set f : ℝ → ℂ := fun s => (x : ℂ) + ((h * s : ℝ) : ℂ) * I with hf
  have hSsub : S ⊆ Ioo 0 ℓ ×ℂ Ioo 0 h := by
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_reProdIm]
    refine ⟨?_, ?_⟩ <;> simp [hx.1, hx.2, ht.1, ht.2]
  have himg : f '' Ioo 0 1 = S := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨h * s, ⟨mul_pos hh hs.1, by nlinarith [hs.2]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t / h, ⟨div_pos ht.1 hh, by rw [div_lt_one hh]; exact ht.2⟩, ?_⟩
      simp only [hf]
      rw [mul_div_cancel₀ _ hh.ne']
  have harc : IsRectifiableArc S :=
    gm4b_isRectifiableArc_affine (c := (x : ℂ)) (v := I) I_ne_zero ordConnected_Ioo
      ⟨h / 3, ⟨by positivity, by linarith⟩, 2 * h / 3, ⟨by positivity, by linarith⟩, by
        intro h'; linarith⟩ (Metric.isBounded_Ioo 0 h)
  refine ⟨⟨fun _ => S, fun n => ⟨harc, hSsub⟩, (iUnion_const S).symm⟩, f, ?_, ?_, ?_, ?_, himg.symm⟩
  · fun_prop
  · intro a _ b _ hab
    have h1 : h * a = h * b := by
      have := congrArg Complex.im hab
      simpa [hf] using this
    exact mul_left_cancel₀ hh.ne' h1
  · rw [mem_reProdIm]
    refine ⟨?_, by simp [hf]⟩
    simp [hf, hx.1.le, hx.2.le]
  · rw [mem_reProdIm]
    refine ⟨?_, by simp [hf]⟩
    simp [hf, hx.1.le, hx.2.le]

/-- Helper (rectangle, separating curves, upper bound): for every metric, `L²/A ≤ h/ℓ` (vertical segments). -/
theorem gm4b_rect_sep_ratio_le {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) {ρ : ℂ → ℝ≥0∞}
    (hρ : ρ ∈ densitiesP0 (Ioo 0 ℓ ×ℂ Ioo 0 h)) :
    pathRhoLength (separatingFamily (Ioo 0 ℓ ×ℂ Ioo 0 h) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h)) ρ ^ 2 /
      rhoArea ρ (Ioo 0 ℓ ×ℂ Ioo 0 h) ≤ ENNReal.ofReal (h / ℓ) := by
  exact gm4b_rect_vseg_ratio_le hℓ (fun x hx => gm4b_rect_vseg_sep_mem hh hx) hρ

/-- Helper (rectangle, the horizontal sides): `d_R(bottom, top) = h/ℓ`, by the isometry `z ↦ i z̄`, which exchanges
the two pairs of sides and the lengths `ℓ`, `h`. -/
theorem gm4b_rect_horizontal {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) :
    extremalDistGM (Ioo 0 ℓ ×ℂ Ioo 0 h) (Icc 0 ℓ ×ℂ {0}) (Icc 0 ℓ ×ℂ {h}) = ENNReal.ofReal (h / ℓ) := by
  rw [extremalDistGM, gm4a_extremalLengthGM_eq]
  refine le_antisymm (iSup₂_le fun ρ hρ => gm4b_rect_vseg_ratio_le hℓ (fun x hx => gm4b_rect_vseg_join_mem hh hx) hρ) ?_
  obtain ⟨hmem, hA, -⟩ := gm4b_rect_one hℓ hh
  rw [mul_comm ℓ h] at hA
  refine le_iSup₂_of_le (fun _ => (1 : ℝ≥0∞)) hmem ?_
  have hone : ∀ γ : Set ℂ, ∫⁻ z in γ, (1 : ℝ≥0∞) ∂μH[1] = μH[1] γ := fun γ => by simp
  have hL : ENNReal.ofReal h ≤ pathRhoLength
      (joiningFamily (Ioo 0 ℓ ×ℂ Ioo 0 h) (Icc 0 ℓ ×ℂ {0}) (Icc 0 ℓ ×ℂ {h})) (fun _ => (1 : ℝ≥0∞)) := by
    rw [gm4a_pathRhoLength_eq]
    refine le_iInf₂ fun γ hγ => ?_
    obtain ⟨-, f, hfc, hfi, hf0, hf1, hfγ⟩ := hγ
    rw [mem_reProdIm] at hf0 hf1
    simp only [Set.mem_singleton_iff] at hf0 hf1
    obtain ⟨-, hf0im⟩ := hf0
    obtain ⟨-, hf1im⟩ := hf1
    rw [hone, hfγ]
    have hsub : Ioo 0 h ⊆ Complex.im '' (f '' Ioo 0 1) := by
      intro t ht
      obtain ⟨ht0, ht1⟩ := ht
      have hcont : ContinuousOn (fun x : ℝ => (f x).im) (Icc 0 1) :=
        Complex.continuous_im.comp_continuousOn hfc
      have hmem' : t ∈ Icc ((fun x : ℝ => (f x).im) 0) ((fun x : ℝ => (f x).im) 1) := by
        simp only [Set.mem_Icc, hf0im, hf1im]
        exact ⟨ht0.le, ht1.le⟩
      obtain ⟨x, hx, hxt⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont hmem'
      rw [Set.mem_Icc] at hx
      have hx0 : x ≠ 0 := by
        intro h'
        rw [h'] at hxt
        simp only [hf0im] at hxt
        exact (ne_of_gt ht0) hxt.symm
      have hx1 : x ≠ 1 := by
        intro h'
        rw [h'] at hxt
        simp only [hf1im] at hxt
        exact (ne_of_lt ht1) hxt.symm
      exact ⟨f x, ⟨x, ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩, rfl⟩, hxt⟩
    have him : LipschitzWith 1 Complex.im := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      simpa [dist_eq_norm, Real.dist_eq] using abs_im_le_norm (a - b)
    calc ENNReal.ofReal h = μH[1] (Ioo 0 h) := by
          rw [hausdorffMeasure_real, Real.volume_Ioo, sub_zero]
      _ ≤ μH[1] (Complex.im '' (f '' Ioo 0 1)) := measure_mono hsub
      _ ≤ μH[1] (f '' Ioo 0 1) := by
          simpa using him.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1) (f '' Ioo 0 1)
  have harith : ENNReal.ofReal (h / ℓ) = ENNReal.ofReal h ^ 2 / ENNReal.ofReal (h * ℓ) := by
    rw [← ENNReal.ofReal_pow hh.le, ← ENNReal.ofReal_div_of_pos (mul_pos hh hℓ)]
    congr 1
    field_simp
  rw [hA, harith]
  exact ENNReal.div_le_div_right (pow_le_pow_left' hL 2) _

/-- Helper (annulus, lower bound): a curve joining the boundary circles of `{r < |z| < R}` has
`∫_γ |z|⁻¹ dμH[1] ≥ log(R/r)` (`gm4b_hausdorff_logNorm_le`). -/
theorem gm4b_annulus_joining_ge {r R : ℝ} (hr : 0 < r) (hrR : r < R) {γ : Set ℂ}
    (hγ : γ ∈ joiningFamily (annulus r R) (sphere 0 r) (sphere 0 R)) :
    ENNReal.ofReal (Real.log (R / r)) ≤ ∫⁻ z in γ, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] := by
  have hR : 0 < R := hr.trans hrR
  obtain ⟨hpc, f, hfc, hfi, hf0, hf1, hfγ⟩ := hγ
  have hγsub : γ ⊆ annulus r R := by
    obtain ⟨s, hs, rfl⟩ := hpc
    exact iUnion_subset fun n => (hs n).2
  have h0 : (0 : ℂ) ∉ γ := fun h => by
    have := (hγsub h).1
    rw [norm_zero] at this
    linarith
  have hf0n : ‖f 0‖ = r := by simpa using hf0
  have hf1n : ‖f 1‖ = R := by simpa using hf1
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ 0 := by
    intro t ht h
    rcases eq_or_ne t 0 with rfl | ht0
    · rw [h, norm_zero] at hf0n
      linarith
    rcases eq_or_ne t 1 with rfl | ht1
    · rw [h, norm_zero] at hf1n
      linarith
    exact h0 (hfγ ▸ ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩, h⟩ : (0 : ℂ) ∈ γ)
  have hcont : ContinuousOn (fun t : ℝ => Real.log ‖f t‖) (Icc 0 1) :=
    ContinuousOn.log (continuous_norm.comp_continuousOn hfc) fun t ht => norm_ne_zero_iff.2 (hne t ht)
  have hsub : Ioo (Real.log r) (Real.log R) ⊆ (fun z : ℂ => Real.log ‖z‖) '' γ := by
    intro t ht
    have hmem : t ∈ Icc ((fun x : ℝ => Real.log ‖f x‖) 0) ((fun x : ℝ => Real.log ‖f x‖) 1) := by
      simp only [Set.mem_Icc, hf0n, hf1n]
      exact ⟨ht.1.le, ht.2.le⟩
    obtain ⟨x, hx, hxt⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont hmem
    rw [Set.mem_Icc] at hx
    have hx0 : x ≠ 0 := by
      intro h'
      rw [h'] at hxt
      simp only [hf0n] at hxt
      exact (ne_of_gt ht.1) hxt.symm
    have hx1 : x ≠ 1 := by
      intro h'
      rw [h'] at hxt
      simp only [hf1n] at hxt
      exact (ne_of_lt ht.2) hxt.symm
    exact ⟨f x, hfγ ▸ ⟨x, ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩, rfl⟩, hxt⟩
  calc ENNReal.ofReal (Real.log (R / r)) = μH[1] (Ioo (Real.log r) (Real.log R)) := by
        rw [hausdorffMeasure_real, Real.volume_Ioo, Real.log_div hR.ne' hr.ne']
    _ ≤ μH[1] ((fun z : ℂ => Real.log ‖z‖) '' γ) := measure_mono hsub
    _ ≤ ∫⁻ z in γ, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] :=
        gm4b_hausdorff_logNorm_le (gm4b_isPathCurve_measurableSet hpc) h0

/-- Helper: the radial segment in the direction `u`, `|u| = 1`, is a member of the joining family of the boundary
circles of the annulus `{r < |z| < R}`. -/
theorem gm4b_annulus_radial_mem {r R : ℝ} (hr : 0 < r) (hrR : r < R) {u : ℂ} (hu : ‖u‖ = 1) :
    (fun t : ℝ => (0 : ℂ) + t * u) '' Ioo r R ∈ joiningFamily (annulus r R) (sphere 0 r) (sphere 0 R) := by
  set S : Set ℂ := (fun t : ℝ => (0 : ℂ) + t * u) '' Ioo r R with hS
  set f : ℝ → ℂ := fun s => (0 : ℂ) + ((r + s * (R - r) : ℝ) : ℂ) * u with hf
  have hnorm : ∀ t : ℝ, 0 ≤ t → ‖(0 : ℂ) + (t : ℂ) * u‖ = t := by
    intro t ht
    rw [zero_add, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg ht]
  have hSsub : S ⊆ annulus r R := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨by rw [hnorm t (hr.le.trans ht.1.le)]; exact ht.1, by rw [hnorm t (hr.le.trans ht.1.le)]; exact ht.2⟩
  have hRr : 0 < R - r := sub_pos.2 hrR
  have himg : f '' Ioo 0 1 = S := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨r + s * (R - r), ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(t - r) / (R - r), ⟨div_pos (sub_pos.2 ht.1) hRr, by rw [div_lt_one hRr]; linarith [ht.2]⟩, ?_⟩
      simp only [hf]
      congr 2
      field_simp
      ring_nf
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact zero_ne_one hu
  have harc : IsRectifiableArc S :=
    gm4b_isRectifiableArc_affine (c := 0) (v := u) hu0 ordConnected_Ioo
      ⟨r + (R - r) / 3, ⟨by linarith, by linarith⟩, r + 2 * (R - r) / 3, ⟨by linarith, by linarith⟩, by
        intro h; linarith⟩ (Metric.isBounded_Ioo r R)
  refine ⟨⟨fun _ => S, fun n => ⟨harc, hSsub⟩, (iUnion_const S).symm⟩, f, ?_, ?_, ?_, ?_, himg.symm⟩
  · fun_prop
  · intro a _ b _ hab
    have h1 : (r + a * (R - r) : ℝ) = (r + b * (R - r) : ℝ) := by
      have := mul_right_cancel₀ hu0 (add_left_cancel hab)
      exact_mod_cast this
    have h2 : a * (R - r) = b * (R - r) := by linarith
    exact mul_right_cancel₀ hRr.ne' h2
  · rw [mem_sphere_zero_iff_norm]
    simp only [hf]
    rw [hnorm _ (by nlinarith)]
    ring
  · rw [mem_sphere_zero_iff_norm]
    simp only [hf]
    rw [hnorm _ (by nlinarith)]
    ring

/-- Helper: `∫_a^b ds/s = log(b/a)` as a lower integral. -/
theorem gm4b_lintegral_inv {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∫⁻ s in Ioo a b, ENNReal.ofReal (1 / s) = ENNReal.ofReal (Real.log (b / a)) := by
  have hint : IntegrableOn (fun t : ℝ => 1 / t) (Ioo a b) :=
    ((continuousOn_const.div continuousOn_id (fun t ht => (ha.trans_le ht.1).ne')).integrableOn_Icc).mono_set
      Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => (one_div_pos.2 (ha.trans ht.1)).le)]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
  simp only [one_div]
  exact integral_inv_of_pos ha (ha.trans hab)

/-- Helper: weighted Cauchy–Schwarz, `(∫_a^b g)² ≤ log(b/a) ∫_a^b s g(s)² ds`. -/
theorem gm4b_lintegral_sq_weight {a b : ℝ} (ha : 0 < a) (hab : a < b) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ s in Ioo a b, g s) ^ 2 ≤
      ENNReal.ofReal (Real.log (b / a)) * ∫⁻ s in Ioo a b, ENNReal.ofReal s * g s ^ 2 := by
  set μ' : Measure ℝ := (volume.restrict (Ioo a b)).withDensity fun s => ENNReal.ofReal (1 / s) with hμ
  have hd : Measurable fun s : ℝ => ENNReal.ofReal (1 / s) := (measurable_const.div measurable_id).ennreal_ofReal
  have hf : Measurable fun s => ENNReal.ofReal s * g s := measurable_id.ennreal_ofReal.mul hg
  have hpos : ∀ s ∈ Ioo a b, 0 < s := fun s hs => ha.trans hs.1
  have h1 : ∫⁻ s, (ENNReal.ofReal s * g s) ∂μ' = ∫⁻ s in Ioo a b, g s := by
    rw [hμ, lintegral_withDensity_eq_lintegral_mul _ hd hf]
    refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (one_div_pos.2 (hpos s hs)).le, one_div, inv_mul_cancel₀ (hpos s hs).ne',
      ENNReal.ofReal_one, one_mul]
  have h2 : μ' univ = ENNReal.ofReal (Real.log (b / a)) := by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_restrict MeasurableSet.univ, univ_inter,
      gm4b_lintegral_inv ha hab]
  have h3 : ∫⁻ s, (ENNReal.ofReal s * g s) ^ 2 ∂μ' = ∫⁻ s in Ioo a b, ENNReal.ofReal s * g s ^ 2 := by
    rw [hμ, lintegral_withDensity_eq_lintegral_mul _ hd (hf.pow_const 2)]
    refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    simp only [Pi.mul_apply]
    have hs0 := hpos s hs
    rw [mul_pow, ← mul_assoc, ← ENNReal.ofReal_pow hs0.le, ← ENNReal.ofReal_mul (one_div_pos.2 hs0).le]
    congr 2
    field_simp
  calc (∫⁻ s in Ioo a b, g s) ^ 2 = (∫⁻ s, (ENNReal.ofReal s * g s) ∂μ') ^ 2 := by rw [h1]
    _ ≤ μ' univ * ∫⁻ s, (ENNReal.ofReal s * g s) ^ 2 ∂μ' := gm4b_lintegral_sq_le μ' hf.aemeasurable
    _ = _ := by rw [h2, h3]

/-- Helper: polar coordinates are `(s, θ) ↦ s e^{iθ}`. -/
theorem gm4b_polarSymm (s θ : ℝ) : Complex.polarCoord.symm (s, θ) = (0 : ℂ) + s * exp (θ * I) := by
  rw [Complex.polarCoord_symm_apply, zero_add, exp_mul_I]
  push_cast
  rfl

/-- Helper: polar coordinates on an annulus, `∬_{r<|z|<R} F = ∫_r^R ∫_{-π}^{π} s F(s e^{iθ}) dθ ds`. -/
theorem gm4b_lintegral_annulus_polar {r R : ℝ} (hr : 0 < r) {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z in annulus r R, F z =
      ∫⁻ s in Ioo r R, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s * F ((0 : ℂ) + s * exp (θ * I)) := by
  have hmeas : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 * F ((0 : ℂ) + p.1 * exp (p.2 * I)) :=
    measurable_fst.ennreal_ofReal.mul (hF.comp (by fun_prop))
  have key : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • (annulus r R).indicator F (Complex.polarCoord.symm p) =
        (Ioo r R ×ˢ (univ : Set ℝ)).indicator
          (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * F ((0 : ℂ) + p.1 * exp (p.2 * I))) p := by
    rintro ⟨s, θ⟩ ⟨hs, -⟩
    have hs0 : (0 : ℝ) < s := hs
    have hnorm : ‖Complex.polarCoord.symm (s, θ)‖ = s := by
      rw [Complex.norm_polarCoord_symm]
      exact abs_of_pos hs0
    by_cases hmem : s ∈ Ioo r R
    · have hmem' : Complex.polarCoord.symm (s, θ) ∈ annulus r R := by
        show r < ‖Complex.polarCoord.symm (s, θ)‖ ∧ ‖Complex.polarCoord.symm (s, θ)‖ < R
        rw [hnorm]
        exact hmem
      rw [indicator_of_mem hmem', indicator_of_mem (show ((s, θ) : ℝ × ℝ) ∈ Ioo r R ×ˢ (univ : Set ℝ) from
        ⟨hmem, mem_univ _⟩), smul_eq_mul, gm4b_polarSymm]
    · have hmem' : Complex.polarCoord.symm (s, θ) ∉ annulus r R := by
        show ¬ (r < ‖Complex.polarCoord.symm (s, θ)‖ ∧ ‖Complex.polarCoord.symm (s, θ)‖ < R)
        rw [hnorm]
        exact hmem
      rw [indicator_of_notMem hmem', indicator_of_notMem (show ((s, θ) : ℝ × ℝ) ∉ Ioo r R ×ˢ (univ : Set ℝ) from
        fun h => hmem h.1), smul_zero]
  have hT : (Ioo r R ×ˢ (univ : Set ℝ)) ∩ (polarCoord.target : Set (ℝ × ℝ)) = Ioo r R ×ˢ Ioo (-π) π := by
    ext ⟨s, θ⟩
    simp only [show (polarCoord.target : Set (ℝ × ℝ)) = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl, mem_inter_iff, mem_prod,
      mem_Ioi, mem_Ioo, mem_univ, and_true]
    constructor
    · rintro ⟨h3, -, h2⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩
      exact ⟨h3, hr.trans h3.1, h2⟩
  rw [← lintegral_indicator (LiZhongQC.isOpen_annulus r R).measurableSet, ← Complex.lintegral_comp_polarCoord_symm,
    setLIntegral_congr_fun polarCoord.open_target.measurableSet key,
    setLIntegral_indicator (measurableSet_Ioo.prod MeasurableSet.univ), hT, Measure.volume_eq_prod,
    ← Measure.prod_restrict, lintegral_prod _ hmeas.aemeasurable]

/-- Helper (annulus, Cauchy–Schwarz along the rays): if `L ≤ ∫_r^R G(θ, s) ds` for every angle `θ ∈ (-π, π)`, then
`2π L² ≤ log(R/r) ∫∫ s G² ds dθ`. -/
theorem gm4b_annulus_core1 {r R : ℝ} (hr : 0 < r) (hrR : r < R) {G : ℝ → ℝ → ℝ≥0∞}
    (hG : ∀ θ, Measurable (G θ)) {L : ℝ≥0∞} (hL : ∀ θ ∈ Ioo (-π) π, L ≤ ∫⁻ s in Ioo r R, G θ s) :
    ENNReal.ofReal (2 * π) * L ^ 2 ≤
      ENNReal.ofReal (Real.log (R / r)) * ∫⁻ θ in Ioo (-π) π, ∫⁻ s in Ioo r R, ENNReal.ofReal s * G θ s ^ 2 := by
  have h1 : ∀ θ ∈ Ioo (-π) π, L ^ 2 ≤
      ENNReal.ofReal (Real.log (R / r)) * ∫⁻ s in Ioo r R, ENNReal.ofReal s * G θ s ^ 2 := fun θ hθ =>
    (pow_le_pow_left' (hL θ hθ) 2).trans (gm4b_lintegral_sq_weight hr hrR (hG θ))
  calc ENNReal.ofReal (2 * π) * L ^ 2 = ∫⁻ _ in Ioo (-π) π, L ^ 2 := by
        rw [setLIntegral_const, Real.volume_Ioo, show π - -π = 2 * π by ring, mul_comm]
    _ ≤ ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (Real.log (R / r)) * ∫⁻ s in Ioo r R, ENNReal.ofReal s * G θ s ^ 2 :=
        setLIntegral_mono' measurableSet_Ioo h1
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Helper (annulus, upper bound): for every metric, `L²/A ≤ (1/2π) log(R/r)` (radial segments, polar coordinates,
Cauchy–Schwarz). -/
theorem gm4b_annulus_ratio_le {r R : ℝ} (hr : 0 < r) (hrR : r < R) {ρ : ℂ → ℝ≥0∞}
    (hρ : ρ ∈ densitiesP0 (annulus r R)) :
    pathRhoLength (joiningFamily (annulus r R) (sphere 0 r) (sphere 0 R)) ρ ^ 2 / rhoArea ρ (annulus r R) ≤
      ENNReal.ofReal (1 / (2 * π) * Real.log (R / r)) := by
  obtain ⟨hm, hA0, hAt⟩ := gm4a_mem_densitiesP0.1 hρ
  have hmeas2 : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * ρ ((0 : ℂ) + p.1 * exp (p.2 * I)) ^ 2 :=
    measurable_fst.ennreal_ofReal.mul ((hm.comp (by fun_prop)).pow_const 2)
  have hA : rhoArea ρ (annulus r R) =
      ∫⁻ θ in Ioo (-π) π, ∫⁻ s in Ioo r R, ENNReal.ofReal s * ρ ((0 : ℂ) + s * exp (θ * I)) ^ 2 := by
    rw [gm4a_rhoArea_eq, gm4b_lintegral_annulus_polar hr (hm.pow_const 2)]
    exact lintegral_lintegral_swap hmeas2.aemeasurable
  have hcore := gm4b_annulus_core1 hr hrR (G := fun θ s => ρ ((0 : ℂ) + s * exp (θ * I)))
    (fun θ => hm.comp (by fun_prop)) (L := pathRhoLength (joiningFamily (annulus r R) (sphere 0 r) (sphere 0 R)) ρ)
    fun θ hθ => by
      refine (iInf₂_le _ (gm4b_annulus_radial_mem hr hrR (u := exp (θ * I)) (norm_exp_ofReal_mul_I θ))).trans_eq ?_
      rw [gm4b_lintegral_line (c := 0) (u := exp (θ * I)) (norm_exp_ofReal_mul_I θ) measurableSet_Ioo hm]
  rw [← hA] at hcore
  have h := gm4b_div_le_of_mul_le (a := 2 * π) (b := Real.log (R / r)) (by positivity) hA0.ne' hAt.ne hcore
  rwa [show Real.log (R / r) / (2 * π) = 1 / (2 * π) * Real.log (R / r) by ring] at h

/-- Helper (annulus, the metric `c/|z|`): for `c > 0` it is a metric of area `2πc² log(R/r)`, and the joining family
has `c/|z|`-length `c log(R/r)`. -/
theorem gm4b_annulus_metric {r R : ℝ} (hr : 0 < r) (hrR : r < R) {c : ℝ} (hc : 0 < c) :
    (fun z : ℂ => ENNReal.ofReal (c / ‖z‖)) ∈ densitiesP0 (annulus r R) ∧
      rhoArea (fun z : ℂ => ENNReal.ofReal (c / ‖z‖)) (annulus r R) =
        ENNReal.ofReal (2 * π * c ^ 2 * Real.log (R / r)) ∧
      pathRhoLength (joiningFamily (annulus r R) (sphere 0 r) (sphere 0 R)) (fun z => ENNReal.ofReal (c / ‖z‖)) =
        ENNReal.ofReal (c * Real.log (R / r)) := by
  have hR : 0 < R := hr.trans hrR
  have hRr : 0 < R / r := div_pos hR hr
  have hlogpos : 0 < Real.log (R / r) := Real.log_pos (by rw [one_lt_div hr]; linarith)
  have hmeas : Measurable fun z : ℂ => ENNReal.ofReal (c / ‖z‖) :=
    Measurable.ennreal_ofReal (measurable_const.div measurable_norm)
  have hAm : MeasurableSet (annulus r R) := (LiZhongQC.isOpen_annulus r R).measurableSet
  -- (2) the area, via polar coordinates
  have harea : rhoArea (fun z : ℂ => ENNReal.ofReal (c / ‖z‖)) (annulus r R) =
      ENNReal.ofReal (2 * π * c ^ 2 * Real.log (R / r)) := by
    rw [gm4a_rhoArea_eq]
    have hcongr : ∀ z ∈ annulus r R, ENNReal.ofReal (c / ‖z‖) ^ 2 =
        ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (1 / ‖z‖ ^ 2) := by
      intro z hz
      have hzpos : 0 < ‖z‖ := hr.trans hz.1
      rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ c / ‖z‖),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ c ^ 2)]
      congr 1
      field_simp
    rw [setLIntegral_congr_fun hAm hcongr, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      LiZhongQC.lintegral_annulus_inv_normSq hr hrR,
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * π by positivity),
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ c ^ 2 by positivity)]
    congr 1
    ring
  refine ⟨gm4a_mem_densitiesP0.2 ⟨hmeas, ?_, ?_⟩, harea, ?_⟩
  · rw [harea]
    exact ENNReal.ofReal_pos.2 (by positivity)
  · rw [harea]
    exact ENNReal.ofReal_lt_top
  · -- (3) the length
    rw [gm4a_pathRhoLength_eq]
    have hrew : ∀ γ : Set ℂ, ∫⁻ z in γ, ENNReal.ofReal (c / ‖z‖) ∂μH[1] =
        ENNReal.ofReal c * ∫⁻ z in γ, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] := fun γ => by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun z => ?_
      rw [← ENNReal.ofReal_mul hc.le, div_eq_mul_inv]
    refine le_antisymm ?_ ?_
    · refine (iInf₂_le _ (gm4b_annulus_radial_mem hr hrR (u := 1) norm_one)).trans_eq ?_
      rw [gm4b_lintegral_line (c := 0) (u := 1) norm_one measurableSet_Ioo hmeas]
      have hcongr : ∫⁻ t in Ioo r R, ENNReal.ofReal (c / ‖(0 : ℂ) + (t : ℂ) * 1‖) =
          ∫⁻ t in Ioo r R, ENNReal.ofReal (c / t) :=
        setLIntegral_congr_fun measurableSet_Ioo fun t ht => by
          rw [zero_add, mul_one, Complex.norm_real, Real.norm_of_nonneg (hr.le.trans ht.1.le)]
      have hint : IntegrableOn (fun t : ℝ => c / t) (Ioo r R) :=
        ((continuousOn_const.div continuousOn_id (fun t ht => (hr.trans_le ht.1).ne')).integrableOn_Icc).mono_set
          Ioo_subset_Icc_self
      rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal hint
        (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => div_nonneg hc.le (hr.trans ht.1).le)]
      congr 1
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hrR.le]
      simp only [div_eq_mul_inv c]
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hr hR]
    · refine le_iInf₂ fun γ hγ => ?_
      rw [hrew, ENNReal.ofReal_mul hc.le]
      exact mul_le_mul' le_rfl (gm4b_annulus_joining_ge hr hrR hγ)

/-- Helper (annulus, separating curves): a curve separating the boundary circles meets every radial segment, so
`∫_γ |z|⁻¹ dμH[1] ≥ 2π` (`gm4b_hausdorff_arg_le`). -/
theorem gm4b_annulus_sep_ge {r R : ℝ} (hr : 0 < r) (hrR : r < R) {γ : Set ℂ}
    (hγ : γ ∈ separatingFamily (annulus r R) (sphere 0 r) (sphere 0 R)) :
    ENNReal.ofReal (2 * π) ≤ ∫⁻ z in γ, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] := by
  obtain ⟨hpc, -, hsep⟩ := hγ
  have hR : 0 < R := hr.trans hrR
  have hmeas : MeasurableSet γ := gm4b_isPathCurve_measurableSet hpc
  have hhit : ∀ θ ∈ Ioo (-π) π, ∃ w ∈ γ, w ∈ slitPlane ∧ arg w = θ := by
    intro θ hθ
    set u : ℂ := exp (θ * I) with hu
    have hun : ‖u‖ = 1 := norm_exp_ofReal_mul_I θ
    have harg : arg u = θ := by
      rw [hu, exp_mul_I]
      exact arg_cos_add_sin_mul_I ⟨hθ.1, hθ.2.le⟩
    set g : ℝ → ℂ := fun t => (0 : ℂ) + t * u with hg
    have hgc : Continuous g := by fun_prop
    have hgn : ∀ t : ℝ, 0 ≤ t → ‖g t‖ = t := by
      intro t ht
      simp only [hg, zero_add, norm_mul, hun, mul_one, Complex.norm_real, Real.norm_of_nonneg ht]
    have hgargs : ∀ t : ℝ, 0 < t → g t ∈ slitPlane ∧ arg (g t) = θ := by
      intro t ht
      have h1 : arg (g t) = θ := by
        simp only [hg, zero_add]
        rw [arg_real_mul u ht, harg]
      refine ⟨mem_slitPlane_iff_arg.2 ⟨by rw [h1]; exact hθ.2.ne, ?_⟩, h1⟩
      intro h
      have := hgn t ht.le
      rw [h, norm_zero] at this
      exact ht.ne this
    by_contra hno
    have hno' : ∀ t ∈ Ioo r R, g t ∉ γ := fun t ht hmem =>
      hno ⟨g t, hmem, (hgargs t (hr.trans ht.1)).1, (hgargs t (hr.trans ht.1)).2⟩
    set Sθ : Set ℂ := g '' Ioo r R with hS
    have hSA : Sθ ⊆ annulus r R \ γ := by
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨⟨by rw [hgn t (hr.trans ht.1).le]; exact ht.1, by rw [hgn t (hr.trans ht.1).le]; exact ht.2⟩,
        hno' t ht⟩
    have hconn : IsPreconnected Sθ := isPreconnected_Ioo.image g hgc.continuousOn
    have hm : g ((r + R) / 2) ∈ Sθ := ⟨(r + R) / 2, ⟨by linarith, by linarith⟩, rfl⟩
    have hK : Sθ ⊆ connectedComponentIn (annulus r R \ γ) (g ((r + R) / 2)) :=
      hconn.subset_connectedComponentIn hm hSA
    have hcl : g '' closure (Ioo r R) ⊆ closure Sθ := image_closure_subset_closure_image hgc
    rw [closure_Ioo hrR.ne] at hcl
    refine hsep (g ((r + R) / 2)) (hSA hm) ⟨⟨g r, closure_mono hK (hcl ⟨r, ⟨le_rfl, hrR.le⟩, rfl⟩), ?_⟩,
      ⟨g R, closure_mono hK (hcl ⟨R, ⟨hrR.le, le_rfl⟩, rfl⟩), ?_⟩⟩
    · rw [mem_sphere_zero_iff_norm, hgn r hr.le]
    · rw [mem_sphere_zero_iff_norm, hgn R hR.le]
  have hsub : Ioo (-π) π ⊆ arg '' (γ ∩ slitPlane) := fun θ hθ => by
    obtain ⟨w, hw, hws, hwa⟩ := hhit θ hθ
    exact ⟨w, ⟨hw, hws⟩, hwa⟩
  calc ENNReal.ofReal (2 * π) = μH[1] (Ioo (-π) π) := by
        rw [hausdorffMeasure_real, Real.volume_Ioo]
        congr 1
        ring
    _ ≤ μH[1] (arg '' (γ ∩ slitPlane)) := measure_mono hsub
    _ ≤ ∫⁻ z in γ ∩ slitPlane, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] :=
        gm4b_hausdorff_arg_le (hmeas.inter isOpen_slitPlane.measurableSet) inter_subset_right
    _ ≤ ∫⁻ z in γ, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] := lintegral_mono_set inter_subset_left

/-- Helper: a real parametrization that is an embedding of a nontrivial interval, with image of finite linear measure,
parametrizes a rectifiable arc. -/
theorem gm4b_isRectifiableArc_of_embedding {I : Set ℝ} (hI : I.OrdConnected) (hn : I.Nontrivial) {k : ℝ → ℂ}
    (hk : IsEmbedding (I.domRestrict k)) (hfin : μH[1] (k '' I) < ⊤) : IsRectifiableArc (k '' I) := by
  refine ⟨⟨I, hI, hn, fun t => ((k t : ℂ) : ExtPlane), ?_, ?_⟩, hfin⟩
  · exact OnePoint.isOpenEmbedding_coe.isEmbedding.comp hk
  · rw [LiZhongQC.toExt, image_image]

/-- Helper: `θ ↦ s e^{iθ}` is an embedding of `(-π, π)` (the inverse is the argument). -/
theorem gm4b_circle_arc_emb {s : ℝ} (hs : 0 < s) :
    IsEmbedding ((Ioo (-π) π).domRestrict fun θ : ℝ => (s : ℂ) * exp (θ * I)) := by
  have harg : ∀ θ ∈ Ioo (-π) π, arg ((s : ℂ) * exp (θ * I)) = θ := fun θ hθ => by
    rw [arg_real_mul _ hs, exp_mul_I]
    exact arg_cos_add_sin_mul_I ⟨hθ.1, hθ.2.le⟩
  have hslit : ∀ θ ∈ Ioo (-π) π, (s : ℂ) * exp (θ * I) ∈ slitPlane := fun θ hθ => by
    refine mem_slitPlane_iff_arg.2 ⟨by rw [harg θ hθ]; exact hθ.2.ne, ?_⟩
    exact mul_ne_zero (by exact_mod_cast hs.ne') (exp_ne_zero _)
  set ψ : Ioo (-π) π → slitPlane := fun θ => ⟨(s : ℂ) * exp ((θ : ℝ) * I), hslit θ.1 θ.2⟩ with hψ
  have hψc : Continuous ψ := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hga : Continuous fun w : slitPlane => arg (w : ℂ) :=
    continuous_iff_continuousAt.2 fun w => (continuousAt_arg w.2).comp continuous_subtype_val.continuousAt
  have hcomp : (fun w : slitPlane => arg (w : ℂ)) ∘ ψ = Subtype.val := by
    funext θ
    exact harg θ.1 θ.2
  have hψe : IsEmbedding ψ :=
    IsEmbedding.of_comp hψc hga (by rw [hcomp]; exact IsEmbedding.subtypeVal)
  exact IsEmbedding.subtypeVal.comp hψe

/-- Helper: a circle has finite linear measure. -/
theorem gm4b_hausdorff_sphere_lt_top {s : ℝ} (hs : 0 < s) : μH[1] (sphere (0 : ℂ) s) < ⊤ := by
  have h := gm4b_lintegral_sphere hs (ρ := fun _ => (1 : ℝ≥0∞)) measurable_const
  simp only [lintegral_const, Measure.restrict_apply_univ, one_mul, Real.volume_Ioo, sub_zero] at h
  rw [h]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- Helper: a circle in the annulus is a curve of a path family in the annulus (two open arcs). -/
theorem gm4b_circle_isPathCurve {r R s : ℝ} (hr : 0 < r) (hrs : r < s) (hsR : s < R) :
    IsPathCurve (annulus r R) (sphere 0 s) := by
  have hs : 0 < s := hr.trans hrs
  have hk := gm4b_circle_arc_emb hs
  set A₁ : Set ℂ := (fun θ : ℝ => (s : ℂ) * exp (θ * I)) '' Ioo (-π) π with hA₁
  set A₂ : Set ℂ := (fun θ : ℝ => -((s : ℂ) * exp (θ * I))) '' Ioo (-π) π with hA₂
  have hnorm : ∀ θ : ℝ, ‖(s : ℂ) * exp (θ * I)‖ = s := fun θ => by
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hs.le]
  have hsub₁ : A₁ ⊆ sphere 0 s := by
    rintro _ ⟨θ, -, rfl⟩
    rw [mem_sphere_zero_iff_norm]
    exact hnorm θ
  have hsub₂ : A₂ ⊆ sphere 0 s := by
    rintro _ ⟨θ, -, rfl⟩
    rw [mem_sphere_zero_iff_norm, norm_neg]
    exact hnorm θ
  have hsphA : sphere (0 : ℂ) s ⊆ annulus r R := fun z hz => by
    rw [mem_sphere_zero_iff_norm] at hz
    exact ⟨hz ▸ hrs, hz ▸ hsR⟩
  have hfin := gm4b_hausdorff_sphere_lt_top hs
  have hnt : (Ioo (-π) π).Nontrivial := ⟨0, ⟨by linarith [Real.pi_pos], Real.pi_pos⟩, 1, ⟨by linarith [Real.pi_pos],
    by linarith [Real.pi_gt_three]⟩, by norm_num⟩
  have hArc₁ : IsRectifiableArc A₁ :=
    gm4b_isRectifiableArc_of_embedding ordConnected_Ioo hnt hk ((measure_mono hsub₁).trans_lt hfin)
  have hArc₂ : IsRectifiableArc A₂ :=
    gm4b_isRectifiableArc_of_embedding ordConnected_Ioo hnt ((Homeomorph.neg ℂ).isEmbedding.comp hk)
      ((measure_mono hsub₂).trans_lt hfin)
  refine ⟨fun n => if n = 0 then A₁ else A₂, fun n => ?_, ?_⟩
  · by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]
      exact ⟨hArc₁, hsub₁.trans hsphA⟩
    · simp only [hn, ↓reduceIte]
      exact ⟨hArc₂, hsub₂.trans hsphA⟩
  · ext z
    constructor
    · intro hz
      have hzn : ‖z‖ = s := mem_sphere_zero_iff_norm.1 hz
      by_cases harg : arg z = π
      · refine mem_iUnion.2 ⟨1, ?_⟩
        simp only [one_ne_zero, ↓reduceIte]
        refine ⟨0, ⟨by linarith [Real.pi_pos], Real.pi_pos⟩, ?_⟩
        have h := norm_mul_exp_arg_mul_I z
        rw [harg, hzn, exp_pi_mul_I] at h
        simp only [ofReal_zero, zero_mul, exp_zero, mul_one]
        rw [← h]
        ring
      · refine mem_iUnion.2 ⟨0, ?_⟩
        simp only [↓reduceIte]
        refine ⟨arg z, ⟨neg_pi_lt_arg z, lt_of_le_of_ne (arg_le_pi z) harg⟩, ?_⟩
        have h := norm_mul_exp_arg_mul_I z
        rw [hzn] at h
        exact h
    · intro hz
      obtain ⟨n, hn⟩ := mem_iUnion.1 hz
      by_cases h0 : n = 0
      · simp only [h0, ↓reduceIte] at hn
        exact hsub₁ hn
      · simp only [h0, ↓reduceIte] at hn
        exact hsub₂ hn

/-- Helper: a circle is the image of a closed path. -/
theorem gm4b_circle_closed {s : ℝ} (hs : 0 < s) :
    ∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ g 0 = g 1 ∧ sphere (0 : ℂ) s = g '' Icc 0 1 := by
  refine ⟨fun t => (s : ℂ) * exp (((2 * π * t : ℝ) : ℂ) * I), by fun_prop, ?_, ?_⟩
  · simp only [mul_zero, ofReal_zero, zero_mul, exp_zero, mul_one]
    push_cast
    rw [exp_two_pi_mul_I, mul_one]
  · ext z
    constructor
    · intro hz
      have hzn : ‖z‖ = s := mem_sphere_zero_iff_norm.1 hz
      have hpi := Real.pi_pos
      by_cases h0 : 0 ≤ arg z
      · refine ⟨arg z / (2 * π), ⟨by positivity, ?_⟩, ?_⟩
        · rw [div_le_one (by positivity)]
          linarith [arg_le_pi z]
        · have h := norm_mul_exp_arg_mul_I z
          rw [hzn] at h
          simp only
          rw [show 2 * π * (arg z / (2 * π)) = arg z by field_simp]
          exact h
      · rw [not_le] at h0
        refine ⟨(arg z + 2 * π) / (2 * π), ⟨by apply div_nonneg <;> linarith [neg_pi_lt_arg z], ?_⟩, ?_⟩
        · rw [div_le_one (by positivity)]
          linarith
        · have h := norm_mul_exp_arg_mul_I z
          rw [hzn] at h
          simp only
          rw [show 2 * π * ((arg z + 2 * π) / (2 * π)) = arg z + 2 * π by field_simp]
          push_cast
          rw [add_mul, exp_add, exp_two_pi_mul_I, mul_one]
          exact h
    · rintro ⟨t, -, rfl⟩
      rw [mem_sphere_zero_iff_norm, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hs.le]

/-- Helper: the circle `|z| = s` separates the boundary circles of the annulus `{r < |z| < R}` (`r < s < R`). -/
theorem gm4b_circle_sep {r R s : ℝ} (hrs : r < s) (hsR : s < R) :
    IsSeparatingIn (annulus r R) (sphere 0 s) (sphere 0 r) (sphere 0 R) := by
  intro z hz hboth
  obtain ⟨⟨p, hpK, hpE⟩, ⟨q, hqK, hqF⟩⟩ := hboth
  set K := connectedComponentIn (annulus r R \ sphere 0 s) z with hK
  have hKsub : K ⊆ annulus r R \ sphere 0 s := connectedComponentIn_subset _ _
  have hKconn : IsPreconnected K := isPreconnected_connectedComponentIn
  have hsplit : K ⊆ {w : ℂ | ‖w‖ < s} ∪ {w : ℂ | s < ‖w‖} := by
    intro w hw
    obtain ⟨-, hwS⟩ := hKsub hw
    rw [mem_sphere_zero_iff_norm] at hwS
    rcases lt_or_gt_of_ne hwS with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  rcases hKconn.subset_or_subset (isOpen_lt continuous_norm continuous_const)
    (isOpen_lt continuous_const continuous_norm)
    (Set.disjoint_left.2 fun w (hw1 : ‖w‖ < s) (hw2 : s < ‖w‖) => lt_irrefl _ (hw1.trans hw2)) hsplit with h1 | h1
  · have hcl : closure K ⊆ {w : ℂ | ‖w‖ ≤ s} :=
      closure_minimal (h1.trans fun w (hw : ‖w‖ < s) => (le_of_lt hw : ‖w‖ ≤ s))
        (isClosed_le continuous_norm continuous_const)
    have h2 : ‖q‖ ≤ s := hcl hqK
    rw [mem_sphere_zero_iff_norm] at hqF
    linarith
  · have hcl : closure K ⊆ {w : ℂ | s ≤ ‖w‖} :=
      closure_minimal (h1.trans fun w (hw : s < ‖w‖) => (le_of_lt hw : s ≤ ‖w‖))
        (isClosed_le continuous_const continuous_norm)
    have h2 : s ≤ ‖p‖ := hcl hpK
    rw [mem_sphere_zero_iff_norm] at hpE
    linarith

/-- Helper (annulus, circles): the circles `|z| = s`, `r < s < R`, are closed curves of a path family in the annulus
separating the boundary circles. -/
theorem gm4b_annulus_circle_mem {r R s : ℝ} (hr : 0 < r) (hrs : r < s) (hsR : s < R) :
    IsPathCurve (annulus r R) (sphere 0 s) ∧
      (∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ g 0 = g 1 ∧ sphere 0 s = g '' Icc 0 1) ∧
      IsSeparatingIn (annulus r R) (sphere 0 s) (sphere 0 r) (sphere 0 R) ∧
      sphere (0 : ℂ) s ∈ separatingFamily (annulus r R) (sphere 0 r) (sphere 0 R) := by
  have hcl := gm4b_circle_closed (hr.trans hrs)
  have hpc := gm4b_circle_isPathCurve hr hrs hsR
  have hsep := gm4b_circle_sep (r := r) (R := R) hrs hsR
  exact ⟨hpc, hcl, hsep, hpc, ⟨{sphere 0 s}, finite_singleton _, (sUnion_singleton _).symm, fun c hc => by
    rw [mem_singleton_iff] at hc
    subst hc
    exact Or.inr hcl⟩, hsep⟩

/-- Helper: `z ↦ s e^{iz}` is a conformal map of the strip `-π < Re z < π`. -/
theorem gm4b_expStripSym_conformal {s : ℝ} (hs : 0 < s) :
    IsConformalOnto (fun z : ℂ => (s : ℂ) * exp (z * I)) {z : ℂ | -π < z.re ∧ z.re < π}
      ((fun z : ℂ => (s : ℂ) * exp (z * I)) '' {z : ℂ | -π < z.re ∧ z.re < π}) := by
  refine ⟨fun z _ => by fun_prop, fun a ha b hb hab => ?_, rfl⟩
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have h : exp (a * I) = exp (b * I) := mul_left_cancel₀ hs0 hab
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have hre : a.re - b.re = 2 * π * n := by
    have := congrArg Complex.im hn
    simp at this
    linarith
  have hn0 : n = 0 := by
    have h1 : |(2 * π * n : ℝ)| < 2 * π := by
      rw [← hre, abs_lt]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at h1
    have h2 : |(n : ℝ)| < 1 := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [Real.pi_pos]
    exact_mod_cast abs_lt.1 h2 |>.elim (fun h3 h4 => by
      have : (-1 : ℤ) < n ∧ n < 1 := ⟨by exact_mod_cast h3, by exact_mod_cast h4⟩
      omega)
  rw [hn0] at hn
  simp only [Int.cast_zero, zero_mul, add_zero] at hn
  exact mul_right_cancel₀ I_ne_zero hn

/-- Helper: linear measure on a circle, with the angle in `(-π, π)`. -/
theorem gm4b_lintegral_sphere_sym {s : ℝ} (hs : 0 < s) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    ∫⁻ z in sphere (0 : ℂ) s, ρ z ∂μH[1] =
      ∫⁻ θ in Ioo (-π) π, ρ (s * exp (θ * I)) * ENNReal.ofReal s := by
  set φ : ℂ → ℂ := fun z => (s : ℂ) * exp (z * I) with hφdef
  set Ω : Set ℂ := {z : ℂ | -π < z.re ∧ z.re < π} with hΩdef
  have hΩ : IsOpen Ω := (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hφ := gm4b_expStripSym_conformal hs
  set S : Set ℂ := (fun t : ℝ => (0 : ℂ) + t * 1) '' Ioo (-π) π with hSdef
  have hSm : MeasurableSet S := by
    have hiso : Isometry (fun t : ℝ => (0 : ℂ) + t * 1) := by
      refine Isometry.of_dist_eq fun x y => ?_
      simp [dist_eq_norm, ← ofReal_sub]
    exact hiso.isClosedEmbedding.measurableEmbedding.measurableSet_image.2 measurableSet_Ioo
  have hSΩ : S ⊆ Ω := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hΩdef]
    simpa using ht
  have hderiv : ∀ t : ℝ, ‖deriv φ ((0 : ℂ) + t * 1)‖ₑ = ENNReal.ofReal s := by
    intro t
    have h : HasDerivAt φ ((s : ℂ) * (exp (((0 : ℂ) + t * 1) * I) * I)) ((0 : ℂ) + t * 1) := by
      have := ((hasDerivAt_id ((0 : ℂ) + t * 1)).mul_const I).cexp.const_mul (s : ℂ)
      simpa [hφdef] using this
    rw [h.deriv, ← ofReal_norm]
    congr 1
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le, norm_I, mul_one]
    rw [show ((0 : ℂ) + t * 1) * I = ((t : ℂ)) * I by ring, norm_exp_ofReal_mul_I, mul_one]
  have hsub : φ '' S ⊆ sphere 0 s := by
    rintro _ ⟨_, ⟨t, -, rfl⟩, rfl⟩
    simp only [hφdef, mem_sphere_zero_iff_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
    rw [show ((0 : ℂ) + t * 1) * I = ((t : ℂ)) * I by ring, norm_exp_ofReal_mul_I, mul_one]
  have hsup : sphere (0 : ℂ) s ⊆ φ '' S ∪ {-(s : ℂ)} := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    by_cases hzs : arg z = π
    · right
      have := norm_mul_exp_arg_mul_I z
      rw [hzs, hz, exp_pi_mul_I] at this
      simp only [mem_singleton_iff]
      rw [← this]
      ring
    left
    have hθI : Ioo (-π) π (arg z) := ⟨neg_pi_lt_arg z, lt_of_le_of_ne (arg_le_pi z) hzs⟩
    refine ⟨(0 : ℂ) + (arg z) * 1, ⟨arg z, hθI, rfl⟩, ?_⟩
    simp only [hφdef]
    rw [show ((0 : ℂ) + (arg z : ℝ) * 1) * I = ((arg z : ℝ) : ℂ) * I by ring, ← hz]
    exact norm_mul_exp_arg_mul_I z
  have hae : (sphere (0 : ℂ) s : Set ℂ) =ᵐ[μH[1]] φ '' S := by
    have hnull : μH[1] ({-(s : ℂ)} : Set ℂ) = 0 := by
      have : NullSingletonClass (μH[1] : Measure ℂ) :=
        MeasureTheory.Measure.nullSingletonClass_hausdorff ℂ one_pos
      exact measure_singleton _
    refine (ae_eq_set).2 ⟨?_, ?_⟩
    · exact measure_mono_null (fun z hz => by
        rcases hsup hz.1 with h | h
        · exact absurd h hz.2
        · exact h) hnull
    · rw [sdiff_eq_empty.2 hsub, measure_empty]
  rw [setLIntegral_congr hae, gm4b_lintegral_image_conformal hΩ hφ hSm hSΩ hρ,
    gm4b_lintegral_line (c := 0) (u := 1) norm_one measurableSet_Ioo]
  · refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
    rw [hderiv t]
    congr 2
    simp only [zero_add, mul_one]
  · exact hρ.comp (by fun_prop) |>.mul ((measurable_deriv φ).enorm)

/-- Helper (annulus, Cauchy–Schwarz along the circles): if `L ≤ ∫_{-π}^{π} G(s, θ) s dθ` for every radius
`s ∈ (r, R)`, then `log(R/r) L² ≤ 2π ∫∫ s G² dθ ds`. -/
theorem gm4b_annulus_core2 {r R : ℝ} (hr : 0 < r) (hrR : r < R) {G : ℝ → ℝ → ℝ≥0∞}
    (hG : ∀ s, Measurable (G s)) {L : ℝ≥0∞}
    (hL : ∀ s ∈ Ioo r R, L ≤ ∫⁻ θ in Ioo (-π) π, G s θ * ENNReal.ofReal s) :
    ENNReal.ofReal (Real.log (R / r)) * L ^ 2 ≤
      ENNReal.ofReal (2 * π) * ∫⁻ s in Ioo r R, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s * G s θ ^ 2 := by
  have h1 : ∀ s ∈ Ioo r R, ENNReal.ofReal (1 / s) * L ^ 2 ≤
      ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s * G s θ ^ 2 := by
    intro s hs
    have hs0 : 0 < s := hr.trans hs.1
    have hss : ENNReal.ofReal (1 / s) * ENNReal.ofReal s ^ 2 = ENNReal.ofReal s := by
      rw [← ENNReal.ofReal_pow hs0.le, ← ENNReal.ofReal_mul (one_div_pos.2 hs0).le]
      congr 1
      field_simp
    have hGs : Measurable fun θ => G s θ * ENNReal.ofReal s := (hG s).mul measurable_const
    calc ENNReal.ofReal (1 / s) * L ^ 2
        ≤ ENNReal.ofReal (1 / s) * (∫⁻ θ in Ioo (-π) π, G s θ * ENNReal.ofReal s) ^ 2 :=
          mul_le_mul' le_rfl (pow_le_pow_left' (hL s hs) 2)
      _ ≤ ENNReal.ofReal (1 / s) * ((volume.restrict (Ioo (-π) π)) univ *
            ∫⁻ θ in Ioo (-π) π, (G s θ * ENNReal.ofReal s) ^ 2) :=
          mul_le_mul' le_rfl (gm4b_lintegral_sq_le _ hGs.aemeasurable)
      _ = ENNReal.ofReal (1 / s) * (ENNReal.ofReal (2 * π) *
            ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s ^ 2 * G s θ ^ 2) := by
          rw [Measure.restrict_apply_univ, Real.volume_Ioo, show π - -π = 2 * π by ring]
          congr 3
          funext θ
          rw [mul_pow, mul_comm]
      _ = ENNReal.ofReal (2 * π) * ((ENNReal.ofReal (1 / s) * ENNReal.ofReal s ^ 2) *
            ∫⁻ θ in Ioo (-π) π, G s θ ^ 2) := by
          rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
          ring
      _ = ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s * G s θ ^ 2 := by
          rw [hss, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hd : Measurable fun s : ℝ => ENNReal.ofReal (1 / s) :=
    (measurable_const.div measurable_id).ennreal_ofReal
  calc ENNReal.ofReal (Real.log (R / r)) * L ^ 2
      = ∫⁻ s in Ioo r R, ENNReal.ofReal (1 / s) * L ^ 2 := by
        rw [lintegral_mul_const _ hd, gm4b_lintegral_inv hr hrR]
    _ ≤ ∫⁻ s in Ioo r R, ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s * G s θ ^ 2 :=
        setLIntegral_mono' measurableSet_Ioo h1
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Helper (annulus, separating curves, upper bound): for every metric and every family of curves containing the
circles `|z| = s`, `r < s < R`, `L²/A ≤ 2π/log(R/r)` (circles, polar coordinates, Cauchy–Schwarz). -/
theorem gm4b_annulus_circles_ratio_le {r R : ℝ} (hr : 0 < r) (hrR : r < R) {Γ : Set (Set ℂ)}
    (hΓ : ∀ s ∈ Ioo r R, sphere (0 : ℂ) s ∈ Γ) {ρ : ℂ → ℝ≥0∞} (hρ : ρ ∈ densitiesP0 (annulus r R)) :
    pathRhoLength Γ ρ ^ 2 / rhoArea ρ (annulus r R) ≤ ENNReal.ofReal (2 * π / Real.log (R / r)) := by
  obtain ⟨hm, hA0, hAt⟩ := gm4a_mem_densitiesP0.1 hρ
  have hA : rhoArea ρ (annulus r R) =
      ∫⁻ s in Ioo r R, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s * ρ ((0 : ℂ) + s * exp (θ * I)) ^ 2 := by
    rw [gm4a_rhoArea_eq, gm4b_lintegral_annulus_polar hr (hm.pow_const 2)]
  have hcore := gm4b_annulus_core2 hr hrR (G := fun s θ => ρ ((0 : ℂ) + s * exp (θ * I)))
    (fun s => hm.comp (by fun_prop)) (L := pathRhoLength Γ ρ) fun s hs => by
      refine (iInf₂_le _ (hΓ s hs)).trans_eq ?_
      rw [gm4b_lintegral_sphere_sym (hr.trans hs.1) hm]
      simp only [zero_add]
  rw [← hA] at hcore
  have hlog : 0 < Real.log (R / r) := Real.log_pos (by rw [one_lt_div hr]; exact hrR)
  exact gm4b_div_le_of_mul_le hlog hA0.ne' hAt.ne hcore

/-- Helper (rectangle): `λ_R` of the family joining the vertical sides is `ℓ/h` (`gm4b_rect_one`,
`gm4b_rect_joining_ge`, `gm4b_rect_ratio_le`). -/
theorem gm4b_rect_value {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) :
    extremalLengthGM (Ioo 0 ℓ ×ℂ Ioo 0 h) (joiningFamily (Ioo 0 ℓ ×ℂ Ioo 0 h) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h)) =
      ENNReal.ofReal (ℓ / h) := by
  refine le_antisymm ?_ ?_
  · rw [gm4a_extremalLengthGM_eq]
    exact iSup₂_le fun ρ hρ => gm4b_rect_ratio_le hℓ hh hρ
  · rw [gm4a_extremalLengthGM_eq]
    refine le_iSup₂_of_le (fun _ => (1 : ℝ≥0∞)) (gm4b_rect_one hℓ hh).1 ?_
    obtain ⟨-, hA, hL⟩ := gm4b_rect_one hℓ hh
    have hval : pathRhoLength (joiningFamily (Ioo 0 ℓ ×ℂ Ioo 0 h) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h))
        (fun _ => (1 : ℝ≥0∞)) ^ 2 / rhoArea (fun _ => (1 : ℝ≥0∞)) (Ioo 0 ℓ ×ℂ Ioo 0 h) =
        ENNReal.ofReal (ℓ / h) := by
      rw [hA, hL, ENNReal.ofReal_mul hℓ.le, pow_two,
        ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_ne_zero_iff.2 hℓ) ENNReal.ofReal_ne_top,
        ← ENNReal.ofReal_div_of_pos hh]
    exact le_of_eq hval.symm

/-- Helper (rectangle): `d*_R` of the vertical sides is `h/ℓ` (`gm4b_rect_sep_ge`, `gm4b_rect_sep_ratio_le`). -/
theorem gm4b_rect_sep_value {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) :
    conjExtremalDistGM (Ioo 0 ℓ ×ℂ Ioo 0 h) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h) = ENNReal.ofReal (h / ℓ) := by
  unfold conjExtremalDistGM
  rw [gm4a_extremalLengthGM_eq]
  refine le_antisymm (iSup₂_le fun ρ hρ => gm4b_rect_sep_ratio_le hℓ hh hρ) ?_
  obtain ⟨hmem, harea, -⟩ := gm4b_rect_one hℓ hh
  refine le_iSup₂_of_le (fun _ => (1 : ℝ≥0∞)) hmem ?_
  have hL : ENNReal.ofReal h ≤ pathRhoLength
      (separatingFamily (Ioo 0 ℓ ×ℂ Ioo 0 h) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h))
      (fun _ => (1 : ℝ≥0∞)) := by
    rw [gm4a_pathRhoLength_eq]
    refine le_iInf₂ fun γ hγ => ?_
    simpa using gm4b_rect_sep_ge hh hγ
  have harith : ENNReal.ofReal (h / ℓ) =
      ENNReal.ofReal h ^ 2 / ENNReal.ofReal (ℓ * h) := by
    rw [← ENNReal.ofReal_pow hh.le, ← ENNReal.ofReal_div_of_pos (mul_pos hℓ hh)]
    congr 1
    field_simp
  rw [harith, harea]
  exact ENNReal.div_le_div_right (ENNReal.pow_le_pow_left (n := 2) hL) _

/-- Helper (arithmetic): `(ofReal a)² / ofReal (a b) = ofReal (a / b)` for `a, b > 0`. -/
theorem gm4b_ofReal_sq_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ENNReal.ofReal a ^ 2 / ENNReal.ofReal (a * b) = ENNReal.ofReal (a / b) := by
  rw [← ENNReal.ofReal_pow ha.le, ← ENNReal.ofReal_div_of_pos (mul_pos ha hb)]
  congr 1
  field_simp

/-- Helper (annulus): `d_A(C_r, C_R) = (1/2π) log(R/r)` (`gm4b_annulus_metric`, `gm4b_annulus_joining_ge`,
`gm4b_annulus_ratio_le`). -/
theorem gm4b_annulus_value {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    extremalDistGM (annulus r R) (sphere 0 r) (sphere 0 R) = ENNReal.ofReal (1 / (2 * π) * Real.log (R / r)) := by
  show extremalLengthGM (annulus r R) (joiningFamily (annulus r R) (sphere 0 r) (sphere 0 R)) =
    ENNReal.ofReal (1 / (2 * π) * Real.log (R / r))
  refine le_antisymm ?_ ?_
  · rw [gm4a_extremalLengthGM_eq]
    exact iSup₂_le fun ρ hρ => gm4b_annulus_ratio_le hr hrR hρ
  · obtain ⟨hmem, hA, hL⟩ := gm4b_annulus_metric hr hrR (c := 1) one_pos
    have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).2 hrR)
    have htwo : (0 : ℝ) < 2 * π := by positivity
    have hratio : pathRhoLength (joiningFamily (annulus r R) (sphere 0 r) (sphere 0 R))
          (fun z : ℂ => ENNReal.ofReal (1 / ‖z‖)) ^ 2 /
          rhoArea (fun z : ℂ => ENNReal.ofReal (1 / ‖z‖)) (annulus r R) =
        ENNReal.ofReal (1 / (2 * π) * Real.log (R / r)) := by
      have e1 : (1 : ℝ) * Real.log (R / r) = Real.log (R / r) := by ring
      have e2 : 2 * π * 1 ^ 2 * Real.log (R / r) = Real.log (R / r) * (2 * π) := by ring
      rw [hL, hA, e1, e2, gm4b_ofReal_sq_div hlog htwo]
      congr 1
      ring
    rw [← hratio]
    exact gm4a_ratio_le hmem

/-- Helper (annulus): every metric `c/|z|`, `c > 0`, is extremal for the joining family. -/
theorem gm4b_annulus_isExtremal {r R : ℝ} (hr : 0 < r) (hrR : r < R) {c : ℝ} (hc : 0 < c) :
    IsExtremalMetricGM (annulus r R) (joiningFamily (annulus r R) (sphere 0 r) (sphere 0 R))
      fun z => ENNReal.ofReal (c / ‖z‖) := by
  obtain ⟨hmem, hA, hL⟩ := gm4b_annulus_metric hr hrR hc
  have hval : extremalLengthGM (annulus r R) (joiningFamily (annulus r R) (sphere 0 r) (sphere 0 R)) =
      ENNReal.ofReal (1 / (2 * π) * Real.log (R / r)) := gm4b_annulus_value hr hrR
  refine ⟨hmem, ?_⟩
  rw [hL, hA, hval]
  have hLpos : 0 < Real.log (R / r) := Real.log_pos (by rw [one_lt_div hr]; exact hrR)
  have hnum : (0 : ℝ) ≤ c * Real.log (R / r) := by positivity
  have hden : (0 : ℝ) < 2 * π * c ^ 2 * Real.log (R / r) := by positivity
  rw [← ENNReal.ofReal_pow hnum, ← ENNReal.ofReal_div_of_pos hden]
  congr 1
  field_simp

/-- Helper (annulus): the separating family and the family of closed separating curves both have extremal length
`2π/log(R/r)` (`gm4b_annulus_sep_ge`, `gm4b_annulus_circle_mem`, `gm4b_annulus_circles_ratio_le`). -/
theorem gm4b_annulus_sep_value {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    conjExtremalDistGM (annulus r R) (sphere 0 r) (sphere 0 R) = ENNReal.ofReal (2 * π / Real.log (R / r)) ∧
      extremalLengthGM (annulus r R) {γ | IsPathCurve (annulus r R) γ ∧
        (∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ g 0 = g 1 ∧ γ = g '' Icc 0 1) ∧
        IsSeparatingIn (annulus r R) γ (sphere 0 r) (sphere 0 R)} = ENNReal.ofReal (2 * π / Real.log (R / r)) := by
  constructor
  · -- (1) separating family
    have hup : extremalLengthGM (annulus r R) (separatingFamily (annulus r R) (sphere 0 r) (sphere 0 R))
        ≤ ENNReal.ofReal (2 * π / Real.log (R / r)) := by
      rw [gm4a_extremalLengthGM_eq]
      refine iSup₂_le fun ρ hρ => ?_
      exact gm4b_annulus_circles_ratio_le hr hrR (fun s hs => (gm4b_annulus_circle_mem hr hs.1 hs.2).2.2.2) hρ
    have hlow : ENNReal.ofReal (2 * π / Real.log (R / r)) ≤
        extremalLengthGM (annulus r R) (separatingFamily (annulus r R) (sphere 0 r) (sphere 0 R)) := by
      set ρ : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖⁻¹) with hρ
      have hmem : ρ ∈ densitiesP0 (annulus r R) := by
        have h := (gm4b_annulus_metric hr hrR (c := 1) one_pos).1
        simpa [hρ, one_div] using h
      have hA : rhoArea ρ (annulus r R) = ENNReal.ofReal (2 * π * 1 ^ 2 * Real.log (R / r)) := by
        simpa [hρ, one_div] using (gm4b_annulus_metric hr hrR (c := 1) one_pos).2.1
      have hL : ENNReal.ofReal (2 * π) ≤ pathRhoLength
          (separatingFamily (annulus r R) (sphere 0 r) (sphere 0 R)) ρ := by
        rw [gm4a_pathRhoLength_eq]
        refine le_iInf₂ fun γ hγ => ?_
        have h := gm4b_annulus_sep_ge hr hrR hγ
        simpa [hρ] using h
      have hlog : 0 < Real.log (R / r) := Real.log_pos (by rw [lt_div_iff₀ hr]; linarith)
      have hpos : (0 : ℝ) < 2 * π * Real.log (R / r) := by positivity
      have hkey : (ENNReal.ofReal (2 * π)) ^ 2 / ENNReal.ofReal (2 * π * 1 ^ 2 * Real.log (R / r)) ≤
          pathRhoLength (separatingFamily (annulus r R) (sphere 0 r) (sphere 0 R)) ρ ^ 2 / rhoArea ρ (annulus r R) := by
        rw [hA]
        gcongr
      have harith : ENNReal.ofReal (2 * π / Real.log (R / r)) =
          (ENNReal.ofReal (2 * π)) ^ 2 / ENNReal.ofReal (2 * π * 1 ^ 2 * Real.log (R / r)) := by
        rw [← ENNReal.ofReal_pow (by positivity), one_pow, mul_one,
          ← ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < 2 * π * Real.log (R / r))]
        congr 1
        field_simp
      rw [harith]
      exact hkey.trans (gm4a_ratio_le hmem)
    exact le_antisymm hup hlow
  · -- (2) closed separating curves
    have hup : extremalLengthGM (annulus r R) {γ | IsPathCurve (annulus r R) γ ∧
        (∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ g 0 = g 1 ∧ γ = g '' Icc 0 1) ∧
        IsSeparatingIn (annulus r R) γ (sphere 0 r) (sphere 0 R)} ≤
        ENNReal.ofReal (2 * π / Real.log (R / r)) := by
      rw [gm4a_extremalLengthGM_eq]
      refine iSup₂_le fun ρ hρ => ?_
      apply gm4b_annulus_circles_ratio_le hr hrR (fun s hs => ?_) hρ
      obtain ⟨h1, h2, h3, h4⟩ := gm4b_annulus_circle_mem hr hs.1 hs.2
      exact ⟨h1, h2, h3⟩
    have hlow : ENNReal.ofReal (2 * π / Real.log (R / r)) ≤
        extremalLengthGM (annulus r R) {γ | IsPathCurve (annulus r R) γ ∧
        (∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ g 0 = g 1 ∧ γ = g '' Icc 0 1) ∧
        IsSeparatingIn (annulus r R) γ (sphere 0 r) (sphere 0 R)} := by
      set ρ : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖⁻¹) with hρ
      have hmem : ρ ∈ densitiesP0 (annulus r R) := by
        have h := (gm4b_annulus_metric hr hrR (c := 1) one_pos).1
        simpa [hρ, one_div] using h
      have hA : rhoArea ρ (annulus r R) = ENNReal.ofReal (2 * π * 1 ^ 2 * Real.log (R / r)) := by
        simpa [hρ, one_div] using (gm4b_annulus_metric hr hrR (c := 1) one_pos).2.1
      have hmemsep : ∀ γ, IsPathCurve (annulus r R) γ →
          (∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ g 0 = g 1 ∧ γ = g '' Icc 0 1) →
          IsSeparatingIn (annulus r R) γ (sphere 0 r) (sphere 0 R) →
          γ ∈ separatingFamily (annulus r R) (sphere 0 r) (sphere 0 R) := by
        intro γ hγc hgc hsep
        obtain ⟨g, hg, hg0, rfl⟩ := hgc
        refine ⟨hγc, ⟨{g '' Icc 0 1}, Set.finite_singleton _, (sUnion_singleton _).symm, ?_⟩, hsep⟩
        intro c hc
        rw [Set.mem_singleton_iff] at hc
        subst hc
        exact Or.inr ⟨g, hg, hg0, rfl⟩
      have hL : ENNReal.ofReal (2 * π) ≤ pathRhoLength
          {γ | IsPathCurve (annulus r R) γ ∧
            (∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ g 0 = g 1 ∧ γ = g '' Icc 0 1) ∧
            IsSeparatingIn (annulus r R) γ (sphere 0 r) (sphere 0 R)} ρ := by
        rw [gm4a_pathRhoLength_eq]
        refine le_iInf₂ fun γ hγ => ?_
        have h := gm4b_annulus_sep_ge hr hrR (hmemsep γ hγ.1 hγ.2.1 hγ.2.2)
        simpa [hρ] using h
      have hpos : (0 : ℝ) < 2 * π * Real.log (R / r) := by
        have hlog : 0 < Real.log (R / r) := Real.log_pos (by rw [lt_div_iff₀ hr]; linarith)
        positivity
      have hkey : (ENNReal.ofReal (2 * π)) ^ 2 / ENNReal.ofReal (2 * π * 1 ^ 2 * Real.log (R / r)) ≤
          pathRhoLength {γ | IsPathCurve (annulus r R) γ ∧
            (∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ g 0 = g 1 ∧ γ = g '' Icc 0 1) ∧
            IsSeparatingIn (annulus r R) γ (sphere 0 r) (sphere 0 R)} ρ ^ 2 / rhoArea ρ (annulus r R) := by
        rw [hA]
        gcongr
      have harith : ENNReal.ofReal (2 * π / Real.log (R / r)) =
          (ENNReal.ofReal (2 * π)) ^ 2 / ENNReal.ofReal (2 * π * 1 ^ 2 * Real.log (R / r)) := by
        rw [← ENNReal.ofReal_pow (by positivity), one_pow, mul_one,
          ← ENNReal.ofReal_div_of_pos hpos]
        congr 1
        field_simp
      rw [harith]
      exact hkey.trans (gm4a_ratio_le hmem)
    exact le_antisymm hup hlow

/-- Helper (arithmetic): `2π/log(R/r) = ((1/2π) log(R/r))⁻¹` in `[0, ∞]` for `r < R`. -/
theorem gm4b_annulus_inv {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ENNReal.ofReal (2 * π / Real.log (R / r)) = (ENNReal.ofReal (1 / (2 * π) * Real.log (R / r)))⁻¹ := by
  have hL : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).2 hrR)
  rw [← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  field_simp

/-- Helper (arithmetic): `k · ofReal (1/|z|) = ofReal (k.toReal / |z|)` for finite `k`. -/
theorem gm4b_mul_ofReal_inv_norm {k : ℝ≥0∞} (hk : k ≠ ⊤) (z : ℂ) :
    k * ENNReal.ofReal (1 / ‖z‖) = ENNReal.ofReal (k.toReal / ‖z‖) := by
  conv_lhs => rw [← ENNReal.ofReal_toReal hk]
  rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, mul_one_div]

/-- **Example 1.1** (the rectangle; (1.4); Ch. IV §1; cited at P1:5929, 6151, in the Notes P1:6500, and in App. H,
P3:4752 "the length–area proof of Example IV.1.1", P3:4895 "as in the rectangle example"). If
`R = {(x, y) : 0 < x < ℓ, 0 < y < h}` is a rectangle of length `ℓ` and height `h`, then the extremal distance between
the vertical sides `E` and `F` is (1.4) `d_R(E, F) = ℓ/h`.
Modelling: `ℓ, h > 0` (a rectangle); the vertical sides are closed segments `{0} × [0, h]` and `{ℓ} × [0, h]`. -/
theorem eq4_1_4 {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) {R E F : Set ℂ} (hR : R = Ioo 0 ℓ ×ℂ Ioo 0 h)
    (hE : E = {0} ×ℂ Icc 0 h) (hF : F = {ℓ} ×ℂ Icc 0 h) :
    extremalDistGM R E F = ENNReal.ofReal (ℓ / h) := by
  subst hR hE hF
  exact gm4b_rect_value hℓ hh

/-- **Example 1.1** (the rectangle; Ch. IV §1), the extremal metrics. In the situation of (1.4), equality holds in
(1.6) when `ρ = 1`, and every extremal metric is constant almost everywhere.
Modelling: "constant almost everywhere" is with respect to area measure on `R`. -/
theorem example4_1_1_b {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) {R E F : Set ℂ} (hR : R = Ioo 0 ℓ ×ℂ Ioo 0 h)
    (hE : E = {0} ×ℂ Icc 0 h) (hF : F = {ℓ} ×ℂ Icc 0 h) :
    IsExtremalMetricGM R (joiningFamily R E F) (fun _ => 1) ∧
      ∀ ρ : ℂ → ℝ≥0∞, IsExtremalMetricGM R (joiningFamily R E F) ρ →
        ∃ c : ℝ≥0∞, ρ =ᵐ[volume.restrict R] fun _ => c := by
  subst hR hE hF
  obtain ⟨hmem, hA, hL⟩ := gm4b_rect_one hℓ hh
  have hval := gm4b_rect_value hℓ hh
  have hone : IsExtremalMetricGM (Ioo 0 ℓ ×ℂ Ioo 0 h)
      (joiningFamily (Ioo 0 ℓ ×ℂ Ioo 0 h) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h)) (fun _ => 1) :=
    ⟨hmem, by rw [hL, hA, hval, gm4b_ofReal_sq_div hℓ hh]⟩
  refine ⟨hone, fun ρ hρ => ?_⟩
  obtain ⟨c, -, -, hc⟩ := gm4b_extremal_eq_const_mul (by rw [hval]; exact ENNReal.ofReal_pos.2 (div_pos hℓ hh))
    (by rw [hval]; exact ENNReal.ofReal_lt_top) hone hρ
  exact ⟨c, by simpa using hc⟩

/-- **Example 1.1** (the rectangle; Ch. IV §1), the conjugate extremal distance. In the situation of (1.4), the
conjugate extremal distance is the extremal distance between the two horizontal sides of `R`, and
`d*_R(E, F) = h/ℓ`. -/
theorem example4_1_1_c {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) {R E F : Set ℂ} (hR : R = Ioo 0 ℓ ×ℂ Ioo 0 h)
    (hE : E = {0} ×ℂ Icc 0 h) (hF : F = {ℓ} ×ℂ Icc 0 h) :
    conjExtremalDistGM R E F = extremalDistGM R (Icc 0 ℓ ×ℂ {0}) (Icc 0 ℓ ×ℂ {h}) ∧
      conjExtremalDistGM R E F = ENNReal.ofReal (h / ℓ) := by
  subst hR hE hF
  exact ⟨(gm4b_rect_sep_value hℓ hh).trans (gm4b_rect_horizontal hℓ hh).symm, gm4b_rect_sep_value hℓ hh⟩

/-! ### GM4-D helpers (-e8): extremal distance of a quadrilateral through a canonical map -/

/-- Helper: the finite value of a map at a point whose image is the finite point `c`. -/
theorem gm4d_finiteMap_coe (φ : ExtPlane → ExtPlane) (c z : ℂ) (h : φ (z : ExtPlane) = (c : ExtPlane)) :
    LehtoVirtanen1973.finiteMap φ z = c := by
  show LehtoVirtanen1973.finiteValue (φ (z : ExtPlane)) = c
  rw [h]
  rfl

/-- Helper: `finiteValue` is the left inverse of the inclusion `ℂ → ℂ̄`. -/
theorem gm4d_finiteValue_coe (c : ℂ) : LehtoVirtanen1973.finiteValue (c : ExtPlane) = c := rfl

/-- Helper: the value of `derivDensity` (unfolding). -/
theorem gm4d_derivDensity_apply (φ : ExtPlane → ExtPlane) (D : Set ℂ) (z : ℂ) :
    derivDensity φ D z = D.indicator (fun z => ENNReal.ofReal ‖deriv (LehtoVirtanen1973.finiteMap φ) z‖) z := rfl

/-- Helper (plane model): for a canonical map `φ` of the quadrilateral `Q` onto `(0, ℓ) × (0, 1)`, the plane map
`ψ = finiteMap φ` is a conformal map (in the sense of `IsConformalOnto`) of the open finite part `Ω` of `Q` into the
rectangle, and its image misses at most one point of the rectangle (the image of `∞` when `∞ ∈ Q`). -/
theorem gm4d_plane_conformal (Q : Quadrilateral) {ℓ : ℝ} {φ : ExtPlane → ExtPlane}
    (hφ : IsCanonicalMap Q.dom Q.vert ℓ 1 φ) {Ω : Set ℂ} {ψ : ℂ → ℂ} (hΩ : Ω = finitePart Q.dom)
    (hψ : ψ = LehtoVirtanen1973.finiteMap φ) :
    IsOpen Ω ∧ IsConformalOnto ψ Ω (ψ '' Ω) ∧ ψ '' Ω ⊆ Ioo 0 ℓ ×ℂ Ioo 0 1 ∧
      (Ioo 0 ℓ ×ℂ Ioo 0 1 \ ψ '' Ω).Subsingleton := by
  obtain ⟨hℓ, h1, ⟨hDom, hcont, hinj, hdiff⟩, himg, hhomeo, hvert⟩ := hφ
  subst hΩ hψ
  have hRe : Ioo 0 ℓ ×ℂ Ioo 0 1 = LiZhongQC.rectangle ℓ 1 := (LiZhongQC.rectangle_eq_reProdIm ℓ 1).symm
  have hopen : IsOpen (finitePart Q.dom) := hDom.1.preimage OnePoint.continuous_coe
  have hfin : ∀ z ∈ finitePart Q.dom, (φ (z : ExtPlane) = ((LehtoVirtanen1973.finiteMap φ z : ℂ) : ExtPlane)) ∧
      LehtoVirtanen1973.finiteMap φ z ∈ LiZhongQC.rectangle ℓ 1 := by
    intro z hz
    have hmem : φ (z : ExtPlane) ∈ toExt (LiZhongQC.rectangle ℓ 1) := himg ▸ mem_image_of_mem φ hz
    obtain ⟨w, hw, hw'⟩ := hmem
    have hz' : LehtoVirtanen1973.finiteMap φ z = w := by
      exact gm4d_finiteMap_coe φ w z hw'.symm
    rw [hz']
    exact ⟨hw'.symm, hw⟩
  have hdiffz : ∀ z ∈ finitePart Q.dom, DifferentiableAt ℂ (LehtoVirtanen1973.finiteMap φ) z := fun z hz =>
    LehtoVirtanen1973.lv12_differentiableAt_of_localRep hopen (fun w hw => (hfin w hw).1) hz (hdiff _ hz)
  refine ⟨hopen, ⟨fun z hz => (hdiffz z hz).differentiableWithinAt, fun a ha b hb hab => ?_, rfl⟩, ?_, ?_⟩
  · apply OnePoint.coe_injective
    apply hinj ha hb
    rw [(hfin a ha).1, (hfin b hb).1, hab]
  · rintro _ ⟨z, hz, rfl⟩
    rw [hRe]
    exact (hfin z hz).2
  · rintro w1 ⟨hw1, hw1'⟩ w2 ⟨hw2, hw2'⟩
    rw [hRe] at hw1 hw2
    have key : ∀ w ∈ LiZhongQC.rectangle ℓ 1, w ∉ LehtoVirtanen1973.finiteMap φ '' finitePart Q.dom →
        φ OnePoint.infty = (w : ExtPlane) := by
      intro w hw hwn
      have hmem : (w : ExtPlane) ∈ φ '' Q.dom := himg ▸ ⟨w, hw, rfl⟩
      obtain ⟨p, hp, hpw⟩ := hmem
      induction p using OnePoint.rec with
      | infty => exact hpw
      | coe z =>
        exfalso
        apply hwn
        refine ⟨z, hp, ?_⟩
        have := (hfin z hp).1
        rw [hpw] at this
        exact (OnePoint.coe_injective this).symm
    have e1 := key w1 hw1 hw1'
    have e2 := key w2 hw2 hw2'
    exact OnePoint.coe_injective (e1.symm.trans e2)

/-- Helper (topology of a side): a homeomorphism `f` of `X` onto `X'`, three points `a, b, c` of `X`, and a splitting of
`X' \ {f a, f b}` into two disjoint relatively open connected pieces `L ∌ f c` and `M ∋ f c`: the side from `a` to `b`
(`a`, `b` and the points whose component of `X \ {a, b}` differs from that of `c`) is mapped onto `L ∪ {f a, f b}`. -/
theorem gm4d_side_aux {X X' : Set ExtPlane} {f G : ExtPlane → ExtPlane} (hf : ContinuousOn f X) (hinj : InjOn f X)
    (himg : f '' X = X') (hG : ContinuousOn G X') (hGf : ∀ p ∈ X, G (f p) = p) {a b c : ExtPlane} (ha : a ∈ X)
    (hb : b ∈ X) (hc : c ∈ X) (hca : c ≠ a) (hcb : c ≠ b) {L M : Set ExtPlane} (hLc : IsPreconnected L)
    (hMc : IsPreconnected M) (hLM : X' \ {f a, f b} = L ∪ M) (hdisj : Disjoint L M) {O₁ O₂ : Set ExtPlane}
    (hO₁L : O₁ ∩ (X' \ {f a, f b}) = L) (hO₂M : O₂ ∩ (X' \ {f a, f b}) = M) (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    (hcM : f c ∈ M) :
    f '' {p ∈ X | p = a ∨ p = b ∨ connectedComponentIn (X \ {a, b}) p ≠ connectedComponentIn (X \ {a, b}) c} =
      L ∪ {f a, f b} := by
  classical
  set A : Set ExtPlane := X \ {a, b} with hA
  have hAX : A ⊆ X := Set.sdiff_subset
  have hA' : f '' A = X' \ {f a, f b} := by
    rw [hA, hinj.image_sdiff, himg, inter_eq_right.2 (insert_subset ha (singleton_subset_iff.2 hb)), image_pair]
  have hLX : L ⊆ X' \ {f a, f b} := hLM ▸ subset_union_left
  have hMX : M ⊆ X' \ {f a, f b} := hLM ▸ subset_union_right
  have hiffL : ∀ w ∈ X' \ {f a, f b}, w ∈ O₁ ↔ w ∈ L := fun w hw =>
    ⟨fun h => hO₁L ▸ ⟨h, hw⟩, fun h => by
      have : w ∈ O₁ ∩ (X' \ {f a, f b}) := hO₁L.symm ▸ h
      exact this.1⟩
  have hiffM : ∀ w ∈ X' \ {f a, f b}, w ∈ O₂ ↔ w ∈ M := fun w hw =>
    ⟨fun h => hO₂M ▸ ⟨h, hw⟩, fun h => by
      have : w ∈ O₂ ∩ (X' \ {f a, f b}) := hO₂M.symm ▸ h
      exact this.1⟩
  set U1 : Set ExtPlane := {p ∈ A | f p ∈ L} with hU1
  set U2 : Set ExtPlane := {p ∈ A | f p ∈ M} with hU2
  have hfA : ∀ p ∈ A, f p ∈ X' \ {f a, f b} := fun p hp => hA' ▸ mem_image_of_mem f hp
  have hGL : ∀ {S : Set ExtPlane}, S ⊆ X' \ {f a, f b} → G '' S = {p ∈ A | f p ∈ S} := by
    intro S hS
    ext p
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨q, hq, rfl⟩ := hA' ▸ hS hw
      refine ⟨by rw [hGf q (hAX hq)]; exact hq, by rw [hGf q (hAX hq)]; exact hw⟩
    · rintro ⟨hp, hpS⟩
      exact ⟨f p, hpS, hGf p (hAX hp)⟩
  have hU1c : IsPreconnected U1 := by
    have := hLc.image G (hG.mono (hLX.trans Set.sdiff_subset))
    rwa [hGL hLX] at this
  have hU2c : IsPreconnected U2 := by
    have := hMc.image G (hG.mono (hMX.trans Set.sdiff_subset))
    rwa [hGL hMX] at this
  have hAsplit : ∀ p ∈ A, p ∈ U1 ∨ p ∈ U2 := by
    intro p hp
    have := hfA p hp
    rw [hLM] at this
    rcases this with h | h
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, h⟩
  have hU12 : ∀ p, p ∈ U1 → p ∈ U2 → False := fun p h1 h2 => Set.disjoint_left.1 hdisj h1.2 h2.2
  obtain ⟨u1, hu1, hu1X⟩ := (continuousOn_iff'.1 hf) O₁ hO₁
  obtain ⟨u2, hu2, hu2X⟩ := (continuousOn_iff'.1 hf) O₂ hO₂
  have hmem : ∀ {u O : Set ExtPlane}, (f ⁻¹' O ∩ X = u ∩ X) → ∀ q ∈ A, (q ∈ u ↔ f q ∈ O) := by
    intro u O hu q hq
    constructor
    · intro h
      have : q ∈ u ∩ X := ⟨h, hAX hq⟩
      rw [← hu] at this
      exact this.1
    · intro h
      have : q ∈ f ⁻¹' O ∩ X := ⟨h, hAX hq⟩
      rw [hu] at this
      exact this.1
  have hmem1 : ∀ q ∈ A, q ∈ u1 ↔ f q ∈ L := fun q hq => (hmem hu1X q hq).trans (hiffL _ (hfA q hq))
  have hmem2 : ∀ q ∈ A, q ∈ u2 ↔ f q ∈ M := fun q hq => (hmem hu2X q hq).trans (hiffM _ (hfA q hq))
  have hcomp : ∀ p ∈ A, (p ∈ U1 ∧ connectedComponentIn A p = U1) ∨ (p ∈ U2 ∧ connectedComponentIn A p = U2) := by
    intro p hp
    have hpre : IsPreconnected (connectedComponentIn A p) := isPreconnected_connectedComponentIn
    have hsub : connectedComponentIn A p ⊆ A := connectedComponentIn_subset _ _
    have hpc : p ∈ connectedComponentIn A p := mem_connectedComponentIn hp
    have hcov : connectedComponentIn A p ⊆ u1 ∪ u2 := fun q hq => by
      rcases hAsplit q (hsub hq) with h | h
      · exact Or.inl ((hmem1 q (hsub hq)).2 h.2)
      · exact Or.inr ((hmem2 q (hsub hq)).2 h.2)
    have hdis : connectedComponentIn A p ∩ (u1 ∩ u2) = ∅ := by
      ext q
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
      rintro ⟨hq, h1, h2⟩
      exact Set.disjoint_left.1 hdisj ((hmem1 q (hsub hq)).1 h1) ((hmem2 q (hsub hq)).1 h2)
    rcases isPreconnected_iff_subset_of_disjoint.1 hpre u1 u2 hu1 hu2 hcov hdis with h | h
    · left
      have hU : connectedComponentIn A p ⊆ U1 := fun q hq => ⟨hsub hq, (hmem1 q (hsub hq)).1 (h hq)⟩
      exact ⟨hU hpc, subset_antisymm hU (hU1c.subset_connectedComponentIn (hU hpc) fun q hq => hq.1)⟩
    · right
      have hU : connectedComponentIn A p ⊆ U2 := fun q hq => ⟨hsub hq, (hmem2 q (hsub hq)).1 (h hq)⟩
      exact ⟨hU hpc, subset_antisymm hU (hU2c.subset_connectedComponentIn (hU hpc) fun q hq => hq.1)⟩
  have hcA : c ∈ A := ⟨hc, by simp [hca, hcb]⟩
  have hcU2 : c ∈ U2 := ⟨hcA, hcM⟩
  have hcc : connectedComponentIn A c = U2 := by
    rcases hcomp c hcA with h | h
    · exact absurd hcU2 (fun h2 => hU12 c h.1 h2)
    · exact h.2
  ext w
  constructor
  · rintro ⟨p, ⟨hpX, hp⟩, rfl⟩
    by_cases hpab : p = a ∨ p = b
    · rcases hpab with rfl | rfl
      · exact Or.inr (mem_insert _ _)
      · exact Or.inr (mem_insert_of_mem _ (mem_singleton _))
    · have hpA : p ∈ A := ⟨hpX, by simpa using hpab⟩
      rcases hp with h | h | h
      · exact absurd (Or.inl h) hpab
      · exact absurd (Or.inr h) hpab
      · rcases hcomp p hpA with h' | h'
        · exact Or.inl h'.1.2
        · exact absurd (h'.2.trans hcc.symm) h
  · rintro (hw | hw)
    · obtain ⟨p, hpA, rfl⟩ := hA' ▸ hLX hw
      have hpU1 : p ∈ U1 := ⟨hpA, hw⟩
      refine ⟨p, ⟨hAX hpA, Or.inr (Or.inr ?_)⟩, rfl⟩
      rcases hcomp p hpA with h' | h'
      · rw [h'.2, hcc]
        intro h
        exact hU12 p hpU1 (h ▸ hpU1)
      · exact absurd h'.1 (fun h2 => hU12 p hpU1 h2)
    · rcases hw with rfl | hw
      · exact ⟨a, ⟨ha, Or.inl rfl⟩, rfl⟩
      · rw [mem_singleton_iff] at hw
        exact ⟨b, ⟨hb, Or.inr (Or.inl rfl)⟩, hw.symm⟩

/-- Helper (the left side of the rectangle, as a piece of its boundary). -/
theorem gm4d_rect_left {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ {I, (0 : ℂ)} =
        ({0} ×ℂ Ioo 0 1) ∪ ((Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ ({0} ×ℂ Icc 0 1)) ∧
      Disjoint ({0} ×ℂ Ioo 0 1) ((Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ ({0} ×ℂ Icc 0 1)) ∧
      IsPreconnected ({0} ×ℂ Ioo 0 1) ∧
      IsPreconnected ((Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ ({0} ×ℂ Icc 0 1)) ∧
      {z : ℂ | -1 < z.re ∧ z.re < ℓ / 2 ∧ 0 < z.im ∧ z.im < 1} ∩
          ((Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ {I, (0 : ℂ)}) = {0} ×ℂ Ioo 0 1 ∧
      ({0} ×ℂ Icc 0 1)ᶜ ∩ ((Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ {I, (0 : ℂ)}) =
        ((Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ ({0} ×ℂ Icc 0 1)) ∧
      (ℓ : ℂ) ∈ ((Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ ({0} ×ℂ Icc 0 1)) ∧
      ({0} ×ℂ Icc 0 1) = ({0} ×ℂ Ioo 0 1) ∪ {I, (0 : ℂ)} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext z
    simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_Ioo, mem_insert_iff, mem_singleton_iff, mem_union,
      Complex.ext_iff, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im]
    constructor <;> intro h <;> grind
  · rw [Set.disjoint_left]
    intro z hz hz'
    simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_Ioo, mem_singleton_iff] at hz hz'
    grind
  · have : ({0} ×ℂ Ioo 0 1) = (fun t : ℝ => (t : ℂ) * I) '' Ioo 0 1 := by
      ext z
      simp only [mem_reProdIm, mem_singleton_iff, mem_image, mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨z.im, h2, Complex.ext (by simp [h1]) (by simp)⟩
      · rintro ⟨t, ht, rfl⟩
        simpa using ht
    rw [this]
    exact isPreconnected_Ioo.image _ (by fun_prop)
  · have hset : ((Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ ({0} ×ℂ Icc 0 1)) =
        ((fun t : ℝ => (t : ℂ)) '' Ioc 0 ℓ ∪ (fun t : ℝ => (ℓ : ℂ) + t * I) '' Icc 0 1) ∪
          (fun t : ℝ => (t : ℂ) + I) '' Ioc 0 ℓ := by
      ext z
      simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_Ioo, mem_Ioc, mem_singleton_iff, mem_union, mem_image,
        Complex.ext_iff]
      constructor
      · intro h
        by_cases hre : z.re = ℓ
        · exact Or.inl (Or.inr ⟨z.im, by grind, by simp [hre], by simp⟩)
        · by_cases him : z.im = 0
          · exact Or.inl (Or.inl ⟨z.re, by grind, by simp, by simp [him]⟩)
          · exact Or.inr ⟨z.re, by grind, by simp, by simp; grind⟩
      · rintro ((⟨t, ht, h1, h2⟩ | ⟨t, ht, h1, h2⟩) | ⟨t, ht, h1, h2⟩) <;> simp at h1 h2 <;> grind
    rw [hset]
    have h1 : IsPreconnected ((fun t : ℝ => (t : ℂ)) '' Ioc 0 ℓ) := isPreconnected_Ioc.image _ (by fun_prop)
    have h2 : IsPreconnected ((fun t : ℝ => (ℓ : ℂ) + t * I) '' Icc 0 1) :=
      isPreconnected_Icc.image _ (by fun_prop)
    have h3 : IsPreconnected ((fun t : ℝ => (t : ℂ) + I) '' Ioc 0 ℓ) := isPreconnected_Ioc.image _ (by fun_prop)
    refine IsPreconnected.union (ℓ + I) ?_ ?_ (h1.union (ℓ : ℂ) ⟨ℓ, ⟨hℓ, le_rfl⟩, rfl⟩ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩ h2) h3
    · exact Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, by simp⟩
    · exact ⟨ℓ, ⟨hℓ, le_rfl⟩, rfl⟩
  · ext z
    simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_Ioo, mem_insert_iff,
      mem_singleton_iff, Complex.ext_iff, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im]
    constructor <;> intro h <;> grind
  · ext z
    simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_Ioo, mem_insert_iff,
      mem_singleton_iff, Complex.ext_iff, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im]
    constructor <;> intro h <;> grind
  · simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_Ioo, mem_singleton_iff, Complex.ofReal_re, Complex.ofReal_im]
    grind
  · ext z
    simp only [mem_union, mem_reProdIm, mem_Icc, mem_Ioo, mem_insert_iff, mem_singleton_iff, Complex.ext_iff,
      Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im]
    constructor <;> intro h <;> grind

/-- Helper (the right side of the rectangle, as a piece of its boundary). -/
theorem gm4d_rect_right {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ {(ℓ : ℂ), (ℓ : ℂ) + I} =
        ({ℓ} ×ℂ Ioo 0 1) ∪ ((Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ ({ℓ} ×ℂ Icc 0 1)) ∧
      Disjoint ({ℓ} ×ℂ Ioo 0 1) ((Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ ({ℓ} ×ℂ Icc 0 1)) ∧
      IsPreconnected ({ℓ} ×ℂ Ioo 0 1) ∧
      IsPreconnected ((Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ ({ℓ} ×ℂ Icc 0 1)) ∧
      {z : ℂ | ℓ / 2 < z.re ∧ z.re < ℓ + 1 ∧ 0 < z.im ∧ z.im < 1} ∩
          ((Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ {(ℓ : ℂ), (ℓ : ℂ) + I}) = {ℓ} ×ℂ Ioo 0 1 ∧
      ({ℓ} ×ℂ Icc 0 1)ᶜ ∩ ((Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ {(ℓ : ℂ), (ℓ : ℂ) + I}) =
        ((Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ ({ℓ} ×ℂ Icc 0 1)) ∧
      I ∈ ((Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ ({ℓ} ×ℂ Icc 0 1)) ∧
      ({ℓ} ×ℂ Icc 0 1) = ({ℓ} ×ℂ Ioo 0 1) ∪ {(ℓ : ℂ), (ℓ : ℂ) + I} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext z
    simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_Ioo, mem_insert_iff, mem_singleton_iff, mem_union,
      Complex.ext_iff, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_re, add_im]
    constructor <;> intro h <;> grind
  · rw [Set.disjoint_left]
    intro z hz hz'
    simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_Ioo, mem_singleton_iff] at hz hz'
    grind
  · have : ({ℓ} ×ℂ Ioo 0 1) = (fun t : ℝ => (ℓ : ℂ) + t * I) '' Ioo 0 1 := by
      ext z
      simp only [mem_reProdIm, mem_singleton_iff, mem_image, mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨z.im, h2, Complex.ext (by simp [h1]) (by simp)⟩
      · rintro ⟨t, ht, rfl⟩
        simpa using ht
    rw [this]
    exact isPreconnected_Ioo.image _ (by fun_prop)
  · have hset : ((Icc 0 ℓ ×ℂ Icc 0 1 \ (Ioo 0 ℓ ×ℂ Ioo 0 1)) \ ({ℓ} ×ℂ Icc 0 1)) =
        ((fun t : ℝ => (t : ℂ)) '' Ico 0 ℓ ∪ (fun t : ℝ => (t : ℂ) * I) '' Icc 0 1) ∪
          (fun t : ℝ => (t : ℂ) + I) '' Ico 0 ℓ := by
      ext z
      simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_Ioo, mem_Ico, mem_singleton_iff, mem_union, mem_image,
        Complex.ext_iff]
      constructor
      · intro h
        by_cases hre : z.re = 0
        · exact Or.inl (Or.inr ⟨z.im, by grind, by simp [hre], by simp⟩)
        · by_cases him : z.im = 0
          · exact Or.inl (Or.inl ⟨z.re, by grind, by simp, by simp [him]⟩)
          · exact Or.inr ⟨z.re, by grind, by simp, by simp; grind⟩
      · rintro ((⟨t, ht, h1, h2⟩ | ⟨t, ht, h1, h2⟩) | ⟨t, ht, h1, h2⟩) <;> simp at h1 h2 <;> grind
    rw [hset]
    have h1 : IsPreconnected ((fun t : ℝ => (t : ℂ)) '' Ico 0 ℓ) := isPreconnected_Ico.image _ (by fun_prop)
    have h2 : IsPreconnected ((fun t : ℝ => (t : ℂ) * I) '' Icc 0 1) :=
      isPreconnected_Icc.image _ (by fun_prop)
    have h3 : IsPreconnected ((fun t : ℝ => (t : ℂ) + I) '' Ico 0 ℓ) := isPreconnected_Ico.image _ (by fun_prop)
    refine IsPreconnected.union I ?_ ?_ (h1.union (0 : ℂ) ⟨0, ⟨le_rfl, hℓ⟩, by simp⟩ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩ h2) h3
    · exact Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, by simp⟩
    · exact ⟨0, ⟨le_rfl, hℓ⟩, by simp⟩
  · ext z
    simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_Ioo, mem_insert_iff,
      mem_singleton_iff, Complex.ext_iff, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_re,
      add_im]
    constructor <;> intro h <;> grind
  · ext z
    simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_Ioo, mem_insert_iff,
      mem_singleton_iff, Complex.ext_iff, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_re,
      add_im]
    constructor <;> intro h <;> grind
  · simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_Ioo, mem_singleton_iff, Complex.I_re, Complex.I_im]
    grind
  · ext z
    simp only [mem_union, mem_reProdIm, mem_Icc, mem_Ioo, mem_insert_iff, mem_singleton_iff, Complex.ext_iff,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_re, add_im]
    constructor <;> intro h <;> grind

/-- Helper (sides): a canonical map carries the sides `Q.side 3` and `Q.side 1` onto the left and the right side of the
rectangle (the homeomorphic extension to the closures maps the boundary Jordan curve onto the boundary of the rectangle,
the vertices to the corners, and so components of the boundary minus two vertices to those of the rectangle). -/
theorem gm4d_side_image (Q : Quadrilateral) {ℓ : ℝ} {φ : ExtPlane → ExtPlane}
    (hφ : IsCanonicalMap Q.dom Q.vert ℓ 1 φ) :
    φ '' Q.side 3 = toExt ({0} ×ℂ Icc 0 1) ∧ φ '' Q.side 1 = toExt ({ℓ} ×ℂ Icc 0 1) := by
  obtain ⟨hℓ, h1, ⟨hDom, hcont, hinj, hdiff⟩, himg, hhomeo, hvert⟩ := hφ
  obtain ⟨hDomOpen, -⟩ := hDom
  have hRe : LiZhongQC.rectangle ℓ 1 = Ioo 0 ℓ ×ℂ Ioo 0 1 := LiZhongQC.rectangle_eq_reProdIm ℓ 1
  rw [hRe] at himg hhomeo
  set Rc : Set ℂ := Icc 0 ℓ ×ℂ Icc 0 1 with hRc
  set R : Set ℂ := Ioo 0 ℓ ×ℂ Ioo 0 1 with hR
  have hcoe : Function.Injective ((↑) : ℂ → ExtPlane) := OnePoint.coe_injective
  have hRccpt : IsCompact (toExt Rc) :=
    (IsCompact.reProdIm isCompact_Icc isCompact_Icc).image OnePoint.continuous_coe
  have hclos : closure (toExt R) = toExt Rc := by
    refine subset_antisymm (closure_minimal (image_mono ?_) hRccpt.isClosed) ?_
    · exact reProdIm_subset_iff.2 (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
    · have h := image_closure_subset_closure_image (f := ((↑) : ℂ → ExtPlane)) (s := R) OnePoint.continuous_coe
      refine subset_trans ?_ h
      refine image_mono ?_
      rw [hR, closure_reProdIm, closure_Ioo hℓ.ne, closure_Ioo one_ne_zero.symm]
  rw [hclos] at hhomeo
  have hfront : φ '' frontier Q.dom = toExt (Rc \ R) := by
    rw [hDomOpen.frontier_eq, hhomeo.2.1.image_sdiff, inter_eq_right.2 subset_closure, hhomeo.2.2.1, himg]
    exact (image_sdiff hcoe _ _).symm
  have hv : ∀ i, φ (Q.vert i) = LiZhongQC.rectVert ℓ 1 i := hvert
  have e3 : φ (Q.vert 3) = ((I : ℂ) : ExtPlane) := by
    rw [hv 3]
    simp [LiZhongQC.rectVert]
  have e0 : φ (Q.vert (3 + 1)) = ((0 : ℂ) : ExtPlane) := by
    rw [hv]
    simp [LiZhongQC.rectVert]
  have e1' : φ (Q.vert (3 + 2)) = ((ℓ : ℂ) : ExtPlane) := by
    rw [hv]
    simp [LiZhongQC.rectVert]
  have e1 : φ (Q.vert 1) = ((ℓ : ℂ) : ExtPlane) := by
    rw [hv]
    simp [LiZhongQC.rectVert]
  have e2 : φ (Q.vert (1 + 1)) = (((ℓ : ℂ) + I : ℂ) : ExtPlane) := by
    rw [hv]
    simp [LiZhongQC.rectVert]
  have e3' : φ (Q.vert (1 + 2)) = ((I : ℂ) : ExtPlane) := by
    rw [hv]
    simp [LiZhongQC.rectVert]
  have hfr : ContinuousOn φ (frontier Q.dom) := hhomeo.1.mono frontier_subset_closure
  have hinjf : InjOn φ (frontier Q.dom) := hhomeo.2.1.mono frontier_subset_closure
  have hGc : ContinuousOn (Function.invFunOn φ (closure Q.dom)) (toExt (Rc \ R)) := by
    refine hhomeo.2.2.2.mono ?_
    exact image_mono Set.sdiff_subset
  have hGf : ∀ p ∈ frontier Q.dom, Function.invFunOn φ (closure Q.dom) (φ p) = p := fun p hp =>
    hhomeo.2.1.leftInvOn_invFunOn (frontier_subset_closure hp)
  have hℓc : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hℓ.ne'
  have hn1 : Q.vert (3 + 2) ≠ Q.vert 3 := fun h => by
    have := hcoe ((e1'.symm.trans (congrArg φ h)).trans e3)
    exact hℓc (by simpa using congrArg Complex.re this)
  have hn2 : Q.vert (3 + 2) ≠ Q.vert (3 + 1) := fun h => by
    have := hcoe ((e1'.symm.trans (congrArg φ h)).trans e0)
    exact hℓc this
  have hn3 : Q.vert (1 + 2) ≠ Q.vert 1 := fun h => by
    have := hcoe ((e3'.symm.trans (congrArg φ h)).trans e1)
    exact hℓc (by simpa using (congrArg Complex.re this).symm)
  have hn4 : Q.vert (1 + 2) ≠ Q.vert (1 + 1) := fun h => by
    have := hcoe ((e3'.symm.trans (congrArg φ h)).trans e2)
    exact hℓc (by simpa using (congrArg Complex.re this).symm)
  have hdiffExt : ∀ S T : Set ℂ, toExt (S \ T) = toExt S \ toExt T := fun S T => image_sdiff hcoe S T
  have hpairExt : ∀ x y : ℂ, toExt {x, y} = {(x : ExtPlane), (y : ExtPlane)} := fun x y => image_pair _ x y
  have hunionExt : ∀ S T : Set ℂ, toExt (S ∪ T) = toExt S ∪ toExt T := fun S T => image_union _ S T
  have hextc : ∀ {S : Set ℂ} {T : Set ℂ}, toExt S ∩ toExt T = toExt (S ∩ T) := fun {S T} =>
    (image_inter hcoe).symm
  have hdiffC : ∀ {S C : Set ℂ}, (toExt C)ᶜ ∩ toExt S = toExt (C ᶜ ∩ S) ∨ True := fun {S C} => Or.inr trivial
  have hcompl : ∀ {S C : Set ℂ}, (toExt C)ᶜ ∩ toExt S = toExt (S \ C) := by
    intro S C
    rw [inter_comm, ← Set.sdiff_eq]
    exact (image_sdiff hcoe S C).symm
  have hclosedC : ∀ {C : Set ℂ}, IsCompact C → IsOpen ((toExt C)ᶜ) := fun {C} hC =>
    (hC.image OnePoint.continuous_coe).isClosed.isOpen_compl
  constructor
  · -- the left side
    obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8⟩ := gm4d_rect_left hℓ
    have hset : toExt (Rc \ R) \ {φ (Q.vert 3), φ (Q.vert (3 + 1))} =
        toExt ((Rc \ R) \ {I, (0 : ℂ)}) := by
      rw [e3, e0, hdiffExt (Rc \ R) {I, (0 : ℂ)}, hpairExt]
    have hopen : IsOpen {z : ℂ | -1 < z.re ∧ z.re < ℓ / 2 ∧ 0 < z.im ∧ z.im < 1} :=
      (isOpen_lt continuous_const continuous_re).inter ((isOpen_lt continuous_re continuous_const).inter
        ((isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)))
    have key := gm4d_side_aux hfr hinjf hfront hGc hGf (Q.vert_mem 3) (Q.vert_mem (3 + 1)) (Q.vert_mem (3 + 2))
      hn1 hn2 (L := toExt ({0} ×ℂ Ioo 0 1))
      (M := toExt (((Rc \ R) \ ({0} ×ℂ Icc 0 1))))
      (hA3.image _ OnePoint.continuous_coe.continuousOn) (hA4.image _ OnePoint.continuous_coe.continuousOn)
      (by rw [hset, hA1, hunionExt]) ((Set.disjoint_image_iff hcoe).2 hA2)
      (O₁ := toExt {z : ℂ | -1 < z.re ∧ z.re < ℓ / 2 ∧ 0 < z.im ∧ z.im < 1})
      (O₂ := (toExt ({0} ×ℂ Icc 0 1))ᶜ)
      (by rw [hset, hextc, hA5])
      (by rw [hset, hcompl, Set.sdiff_eq_compl_inter, hA6])
      (OnePoint.isOpen_image_coe.2 hopen) (hclosedC (IsCompact.reProdIm isCompact_singleton isCompact_Icc))
      (by rw [e1']; exact ⟨ℓ, hA7, rfl⟩)
    exact key.trans (by rw [e3, e0, hA8, hunionExt, hpairExt])
  · -- the right side
    obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8⟩ := gm4d_rect_right hℓ
    have hset : toExt (Rc \ R) \ {φ (Q.vert 1), φ (Q.vert (1 + 1))} =
        toExt ((Rc \ R) \ {(ℓ : ℂ), (ℓ : ℂ) + I}) := by
      rw [e1, e2, hdiffExt (Rc \ R) {(ℓ : ℂ), (ℓ : ℂ) + I}, hpairExt]
    have hopen : IsOpen {z : ℂ | ℓ / 2 < z.re ∧ z.re < ℓ + 1 ∧ 0 < z.im ∧ z.im < 1} :=
      (isOpen_lt continuous_const continuous_re).inter ((isOpen_lt continuous_re continuous_const).inter
        ((isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)))
    have key := gm4d_side_aux hfr hinjf hfront hGc hGf (Q.vert_mem 1) (Q.vert_mem (1 + 1)) (Q.vert_mem (1 + 2))
      hn3 hn4 (L := toExt ({ℓ} ×ℂ Ioo 0 1))
      (M := toExt (((Rc \ R) \ ({ℓ} ×ℂ Icc 0 1))))
      (hA3.image _ OnePoint.continuous_coe.continuousOn) (hA4.image _ OnePoint.continuous_coe.continuousOn)
      (by rw [hset, hA1, hunionExt]) ((Set.disjoint_image_iff hcoe).2 hA2)
      (O₁ := toExt {z : ℂ | ℓ / 2 < z.re ∧ z.re < ℓ + 1 ∧ 0 < z.im ∧ z.im < 1})
      (O₂ := (toExt ({ℓ} ×ℂ Icc 0 1))ᶜ)
      (by rw [hset, hextc, hA5])
      (by rw [hset, hcompl, Set.sdiff_eq_compl_inter, hA6])
      (OnePoint.isOpen_image_coe.2 hopen) (hclosedC (IsCompact.reProdIm isCompact_singleton isCompact_Icc))
      (by rw [e3']; exact ⟨I, hA7, rfl⟩)
    exact key.trans (by rw [e1, e2, hA8, hunionExt, hpairExt])

/-- Helper: the closure of the open rectangle in `ℂ̄` is the image of the closed rectangle. -/
theorem gm4d_closure_rect {ℓ : ℝ} (hℓ : 0 < ℓ) :
    closure (toExt (Ioo 0 ℓ ×ℂ Ioo 0 1)) = toExt (Icc 0 ℓ ×ℂ Icc 0 1) := by
  have hRccpt : IsCompact (toExt (Icc 0 ℓ ×ℂ Icc 0 1)) :=
    (IsCompact.reProdIm isCompact_Icc isCompact_Icc).image OnePoint.continuous_coe
  refine subset_antisymm (closure_minimal (image_mono ?_) hRccpt.isClosed) ?_
  · exact reProdIm_subset_iff.2 (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  · have h := image_closure_subset_closure_image (f := ((↑) : ℂ → ExtPlane)) (s := Ioo 0 ℓ ×ℂ Ioo 0 1)
      OnePoint.continuous_coe
    refine subset_trans ?_ h
    refine image_mono ?_
    rw [closure_reProdIm, closure_Ioo hℓ.ne, closure_Ioo one_ne_zero.symm]

/-- Helper (the inverse of a canonical map on the closed rectangle): `G` is the inverse of `φ` on the closure; it is a
continuous injection of the closed rectangle, with `φ ∘ G = id`; it agrees with the inverse of the plane map `ψ` on the
image of `ψ`, sends the (at most one) missing interior point of the rectangle to `∞`, and maps the left and the right
side of the rectangle into `Q.side 3` and `Q.side 1`. -/
theorem gm4d_G_facts (Q : Quadrilateral) {ℓ : ℝ} {φ : ExtPlane → ExtPlane}
    (hφ : IsCanonicalMap Q.dom Q.vert ℓ 1 φ) {Ω : Set ℂ} {ψ : ℂ → ℂ} (hΩ : Ω = finitePart Q.dom)
    (hψ : ψ = LehtoVirtanen1973.finiteMap φ) {G : ExtPlane → ExtPlane}
    (hG : G = Function.invFunOn φ (closure Q.dom)) :
    (∀ w ∈ Icc 0 ℓ ×ℂ Icc 0 1, G (w : ExtPlane) ∈ closure Q.dom ∧ φ (G (w : ExtPlane)) = w) ∧
      ContinuousOn (fun w : ℂ => G (w : ExtPlane)) (Icc 0 ℓ ×ℂ Icc 0 1) ∧
      InjOn (fun w : ℂ => G (w : ExtPlane)) (Icc 0 ℓ ×ℂ Icc 0 1) ∧
      (∀ w ∈ ψ '' Ω, G (w : ExtPlane) = ((Function.invFunOn ψ Ω w : ℂ) : ExtPlane)) ∧
      (∀ w ∈ Ioo 0 ℓ ×ℂ Ioo 0 1, w ∉ ψ '' Ω → G (w : ExtPlane) = OnePoint.infty) ∧
      (∀ w ∈ Icc 0 ℓ ×ℂ Icc 0 1, ∀ w' ∈ Icc 0 ℓ ×ℂ Icc 0 1, G (w : ExtPlane) = OnePoint.infty →
        G (w' : ExtPlane) = OnePoint.infty → w = w') ∧
      (∀ w ∈ {0} ×ℂ Icc 0 1, G (w : ExtPlane) ∈ Q.side 3) ∧ (∀ w ∈ {ℓ} ×ℂ Icc 0 1, G (w : ExtPlane) ∈ Q.side 1) := by
  have hside := gm4d_side_image Q hφ
  obtain ⟨hplane1, hconf, hsub, hZ⟩ := gm4d_plane_conformal Q hφ hΩ hψ
  obtain ⟨hℓ, h1, ⟨hDom, hcont, hinj, hdiff⟩, himg, hhomeo, hvert⟩ := hφ
  have hRe : LiZhongQC.rectangle ℓ 1 = Ioo 0 ℓ ×ℂ Ioo 0 1 := LiZhongQC.rectangle_eq_reProdIm ℓ 1
  rw [hRe] at himg hhomeo
  rw [gm4d_closure_rect hℓ] at hhomeo
  subst hG hΩ hψ
  have hcoe : Function.Injective ((↑) : ℂ → ExtPlane) := OnePoint.coe_injective
  have hrt : ∀ w ∈ Icc 0 ℓ ×ℂ Icc 0 1, ∃ p ∈ closure Q.dom, φ p = (w : ExtPlane) := fun w hw => by
    have : (w : ExtPlane) ∈ φ '' closure Q.dom := hhomeo.2.2.1 ▸ ⟨w, hw, rfl⟩
    obtain ⟨p, hp, hpw⟩ := this
    exact ⟨p, hp, hpw⟩
  have hGinv : ∀ w ∈ Icc 0 ℓ ×ℂ Icc 0 1, Function.invFunOn φ (closure Q.dom) (w : ExtPlane) ∈ closure Q.dom ∧
      φ (Function.invFunOn φ (closure Q.dom) (w : ExtPlane)) = w := fun w hw =>
    ⟨Function.invFunOn_mem (hrt w hw), Function.invFunOn_eq (hrt w hw)⟩
  have hfin : ∀ z ∈ finitePart Q.dom, φ (z : ExtPlane) = ((LehtoVirtanen1973.finiteMap φ z : ℂ) : ExtPlane) := by
    intro z hz
    have hmem : φ (z : ExtPlane) ∈ toExt (Ioo 0 ℓ ×ℂ Ioo 0 1) := himg ▸ mem_image_of_mem φ hz
    obtain ⟨w, hw, hw'⟩ := hmem
    have hz' : LehtoVirtanen1973.finiteMap φ z = w := by
      exact gm4d_finiteMap_coe φ w z hw'.symm
    rw [hz']
    exact hw'.symm
  have hmemRc : ∀ w ∈ Ioo 0 ℓ ×ℂ Ioo 0 1, w ∈ Icc 0 ℓ ×ℂ Icc 0 1 := fun w hw =>
    reProdIm_subset_iff.2 (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) hw
  refine ⟨hGinv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hhomeo.2.2.2.comp OnePoint.continuous_coe.continuousOn fun w hw => ⟨w, hw, rfl⟩
  · intro w hw w' hw' h
    apply hcoe
    rw [← (hGinv w hw).2, ← (hGinv w' hw').2]
    exact congrArg φ h
  · rintro _ ⟨z, hz, rfl⟩
    have h1 : Function.invFunOn φ (closure Q.dom) (φ (z : ExtPlane)) = (z : ExtPlane) :=
      hhomeo.2.1.leftInvOn_invFunOn (subset_closure hz)
    rw [← hfin z hz, h1, hconf.2.1.leftInvOn_invFunOn hz]
  · intro w hw hwn
    have hmem : (w : ExtPlane) ∈ φ '' Q.dom := himg ▸ ⟨w, hw, rfl⟩
    obtain ⟨p, hp, hpw⟩ := hmem
    induction p using OnePoint.rec with
    | infty =>
      have h1 : Function.invFunOn φ (closure Q.dom) (φ OnePoint.infty) = OnePoint.infty :=
        hhomeo.2.1.leftInvOn_invFunOn (subset_closure hp)
      rw [← hpw, h1]
    | coe z =>
      exfalso
      apply hwn
      refine ⟨z, hp, ?_⟩
      have := hfin z hp
      rw [hpw] at this
      exact (hcoe this).symm
  · intro w hw w' hw' h h'
    have e1 := (hGinv w hw).2
    have e2 := (hGinv w' hw').2
    rw [h] at e1
    rw [h'] at e2
    exact hcoe (e1.symm.trans e2)
  · intro w hw
    have hwc : (w : ExtPlane) ∈ toExt ({0} ×ℂ Icc 0 1) := ⟨w, hw, rfl⟩
    rw [← hside.1] at hwc
    obtain ⟨p, hp, hpw⟩ := hwc
    have hwRc : w ∈ Icc 0 ℓ ×ℂ Icc 0 1 := by
      rw [mem_reProdIm] at hw ⊢
      simp only [mem_singleton_iff] at hw
      exact ⟨by simp [hw.1, hℓ.le], hw.2⟩
    have hpc : p ∈ closure Q.dom := frontier_subset_closure hp.1
    have : Function.invFunOn φ (closure Q.dom) (w : ExtPlane) = p := by
      refine hhomeo.2.1 (hGinv w hwRc).1 hpc ?_
      rw [(hGinv w hwRc).2, hpw]
    rw [this]
    exact hp
  · intro w hw
    have hwc : (w : ExtPlane) ∈ toExt ({ℓ} ×ℂ Icc 0 1) := ⟨w, hw, rfl⟩
    rw [← hside.2] at hwc
    obtain ⟨p, hp, hpw⟩ := hwc
    have hwRc : w ∈ Icc 0 ℓ ×ℂ Icc 0 1 := by
      rw [mem_reProdIm] at hw ⊢
      simp only [mem_singleton_iff] at hw
      exact ⟨by simp [hw.1, hℓ.le], hw.2⟩
    have hpc : p ∈ closure Q.dom := frontier_subset_closure hp.1
    have : Function.invFunOn φ (closure Q.dom) (w : ExtPlane) = p := by
      refine hhomeo.2.1 (hGinv w hwRc).1 hpc ?_
      rw [(hGinv w hwRc).2, hpw]
    rw [this]
    exact hp

/-- Helper (crossing, joining curves): the image `ψ(γ)` of a curve `γ` joining `E` and `F` in `Ω` has linear measure
`≥ ℓ` (its real part covers `(0, ℓ)`, since `ψ ∘ f` extends continuously to the endpoints, which go to the left and
right sides). -/
theorem gm4d_crossing (Q : Quadrilateral) {ℓ : ℝ} {φ : ExtPlane → ExtPlane}
    (hφ : IsCanonicalMap Q.dom Q.vert ℓ 1 φ) {Ω E F : Set ℂ} {ψ : ℂ → ℂ} (hΩ : Ω = finitePart Q.dom)
    (hE : E = finitePart (Q.side 3)) (hF : F = finitePart (Q.side 1)) (hψ : ψ = LehtoVirtanen1973.finiteMap φ)
    {γ : Set ℂ} (hγ : γ ∈ joiningFamily Ω E F) : ENNReal.ofReal ℓ ≤ μH[1] (ψ '' γ) := by
  subst hΩ hE hF hψ
  have hside := gm4d_side_image Q hφ
  obtain ⟨hℓ, h1, ⟨hDom, hcont, hinj, hdiff⟩, himg, hhomeo, hvert⟩ := hφ
  have hRe : LiZhongQC.rectangle ℓ 1 = Ioo 0 ℓ ×ℂ Ioo 0 1 := LiZhongQC.rectangle_eq_reProdIm ℓ 1
  rw [hRe] at himg hhomeo
  rw [gm4d_closure_rect hℓ] at hhomeo
  have hsubc : ∀ {Ω' γ : Set ℂ}, IsPathCurve Ω' γ → γ ⊆ Ω' := fun {Ω' γ} h => by
    obtain ⟨s, hs, rfl⟩ := h
    exact iUnion_subset fun n => (hs n).2
  obtain ⟨hpc, f, hfc, hfi, hf0, hf1, hfγ⟩ := hγ
  have hγΩ := hsubc hpc
  have hf0' : ((f 0 : ℂ) : ExtPlane) ∈ Q.side 3 := hf0
  have hf1' : ((f 1 : ℂ) : ExtPlane) ∈ Q.side 1 := hf1
  have hcl : ∀ t ∈ Icc (0 : ℝ) 1, ((f t : ℂ) : ExtPlane) ∈ closure Q.dom := by
    intro t ht
    by_cases h0 : t = 0
    · rw [h0]
      exact frontier_subset_closure hf0'.1
    by_cases h1' : t = 1
    · rw [h1']
      exact frontier_subset_closure hf1'.1
    have : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1'⟩
    exact subset_closure (hγΩ (hfγ ▸ mem_image_of_mem f this))
  have hhc : ContinuousOn (fun t : ℝ => φ ((f t : ℂ) : ExtPlane)) (Icc 0 1) :=
    hhomeo.1.comp (OnePoint.continuous_coe.comp_continuousOn hfc) hcl
  have hfinite : ∀ t ∈ Icc (0 : ℝ) 1, ∃ c ∈ Icc 0 ℓ ×ℂ Icc 0 1, φ ((f t : ℂ) : ExtPlane) = (c : ExtPlane) := by
    intro t ht
    have : φ ((f t : ℂ) : ExtPlane) ∈ toExt (Icc 0 ℓ ×ℂ Icc 0 1) :=
      hhomeo.2.2.1 ▸ mem_image_of_mem φ (hcl t ht)
    obtain ⟨c, hc, hct⟩ := this
    exact ⟨c, hc, hct.symm⟩
  set k : ℝ → ℂ := fun t => LehtoVirtanen1973.finiteValue (φ ((f t : ℂ) : ExtPlane)) with hk
  have hkc : ∀ t ∈ Icc (0 : ℝ) 1, φ ((f t : ℂ) : ExtPlane) = (k t : ExtPlane) := by
    intro t ht
    obtain ⟨c, hc, hct⟩ := hfinite t ht
    simp only [hk, hct, gm4d_finiteValue_coe]
  have hkcont : ContinuousOn k (Icc 0 1) := by
    intro t ht
    obtain ⟨c, hc, hct⟩ := hfinite t ht
    have hfv : ContinuousAt LehtoVirtanen1973.finiteValue (φ ((f t : ℂ) : ExtPlane)) := by
      rw [hct]
      exact LehtoVirtanen1973.lv15_finiteValue_continuousAt c
    exact ContinuousAt.comp_continuousWithinAt (f := fun t : ℝ => φ ((f t : ℂ) : ExtPlane)) hfv (hhc t ht)
  have hk0 : (k 0).re = 0 := by
    have hmem : φ ((f 0 : ℂ) : ExtPlane) ∈ toExt ({0} ×ℂ Icc 0 1) := hside.1 ▸ mem_image_of_mem φ hf0'
    obtain ⟨c, hc, hct⟩ := hmem
    have : k 0 = c := by
      apply OnePoint.coe_injective
      rw [← hkc 0 ⟨le_rfl, zero_le_one⟩, ← hct]
    rw [this]
    simpa using hc.1
  have hk1 : (k 1).re = ℓ := by
    have hmem : φ ((f 1 : ℂ) : ExtPlane) ∈ toExt ({ℓ} ×ℂ Icc 0 1) := hside.2 ▸ mem_image_of_mem φ hf1'
    obtain ⟨c, hc, hct⟩ := hmem
    have : k 1 = c := by
      apply OnePoint.coe_injective
      rw [← hkc 1 ⟨zero_le_one, le_rfl⟩, ← hct]
    rw [this]
    simpa using hc.1
  have hkψ : ∀ t ∈ Ioo (0 : ℝ) 1, k t = LehtoVirtanen1973.finiteMap φ (f t) := fun t ht => rfl
  have hsub : Ioo 0 ℓ ⊆ Complex.re '' (LehtoVirtanen1973.finiteMap φ '' γ) := by
    intro x hx
    have hcontre : ContinuousOn (fun t : ℝ => (k t).re) (Icc 0 1) := Complex.continuous_re.comp_continuousOn hkcont
    have hmem : x ∈ Icc ((fun t : ℝ => (k t).re) 0) ((fun t : ℝ => (k t).re) 1) := by
      simp only [hk0, hk1]
      exact ⟨hx.1.le, hx.2.le⟩
    obtain ⟨t, ht, htx⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcontre hmem
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp only [hk0] at htx
      exact hx.1.ne htx
    have ht1 : t ≠ 1 := by
      rintro rfl
      simp only [hk1] at htx
      exact hx.2.ne htx.symm
    have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    refine ⟨k t, ⟨f t, ?_, (hkψ t htI).symm⟩, htx⟩
    exact hfγ ▸ mem_image_of_mem f htI
  have hre : LipschitzWith 1 Complex.re := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simpa [dist_eq_norm, Real.dist_eq] using abs_re_le_norm (a - b)
  calc ENNReal.ofReal ℓ = μH[1] (Ioo 0 ℓ) := by
        rw [hausdorffMeasure_real, Real.volume_Ioo, sub_zero]
    _ ≤ μH[1] (Complex.re '' (LehtoVirtanen1973.finiteMap φ '' γ)) := measure_mono hsub
    _ ≤ μH[1] (LehtoVirtanen1973.finiteMap φ '' γ) := by
        simpa using hre.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1) (LehtoVirtanen1973.finiteMap φ '' γ)

/-- Helper (a segment of the rectangle pulled back): for a segment `w0 + s (w1 - w0)` of the closed rectangle, interior
points in the open rectangle, on which `G` never takes the value `∞`, the finite values of `G` along it form a
continuous injective path in `Ω`-closure, with `φ ∘ f` the segment, and interior points in `Ω`. -/
theorem gm4d_seg_arc (Q : Quadrilateral) {ℓ : ℝ} {φ : ExtPlane → ExtPlane}
    (hφ : IsCanonicalMap Q.dom Q.vert ℓ 1 φ) {Ω : Set ℂ} {ψ : ℂ → ℂ} (hΩ : Ω = finitePart Q.dom)
    (hψ : ψ = LehtoVirtanen1973.finiteMap φ) {G : ExtPlane → ExtPlane}
    (hG : G = Function.invFunOn φ (closure Q.dom)) {w0 w1 : ℂ} (hne : w0 ≠ w1)
    (h0 : w0 ∈ Icc 0 ℓ ×ℂ Icc 0 1) (h1 : w1 ∈ Icc 0 ℓ ×ℂ Icc 0 1)
    (hin : ∀ s ∈ Ioo (0 : ℝ) 1, w0 + s * (w1 - w0) ∈ Ioo 0 ℓ ×ℂ Ioo 0 1)
    (hinf : ∀ s ∈ Icc (0 : ℝ) 1, G ((w0 + s * (w1 - w0) : ℂ) : ExtPlane) ≠ OnePoint.infty) :
    ∃ f : ℝ → ℂ, ContinuousOn f (Icc 0 1) ∧ InjOn f (Icc 0 1) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, φ ((f s : ℂ) : ExtPlane) = ((w0 + s * (w1 - w0) : ℂ) : ExtPlane) ∧
        ((f s : ℂ) : ExtPlane) ∈ closure Q.dom) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, f s ∈ Ω ∧ ψ (f s) = w0 + s * (w1 - w0)) := by
  obtain ⟨hGinv, hGcont, hGinj, -, -, -, -, -⟩ := gm4d_G_facts Q hφ hΩ hψ hG
  obtain ⟨hℓ, hh1, ⟨hDom, hcont, hinj, hdiff⟩, himg, hhomeo, hvert⟩ := hφ
  have hRe : LiZhongQC.rectangle ℓ 1 = Ioo 0 ℓ ×ℂ Ioo 0 1 := LiZhongQC.rectangle_eq_reProdIm ℓ 1
  rw [hRe] at himg hhomeo
  rw [gm4d_closure_rect hℓ] at hhomeo
  subst hΩ hψ
  set wseg : ℝ → ℂ := fun s => w0 + s * (w1 - w0) with hwseg
  have hwRc : ∀ s ∈ Icc (0 : ℝ) 1, wseg s ∈ Icc 0 ℓ ×ℂ Icc 0 1 := by
    intro s hs
    by_cases hs0 : s = 0
    · simpa [hwseg, hs0] using h0
    by_cases hs1 : s = 1
    · simpa [hwseg, hs1] using h1
    exact reProdIm_subset_iff.2 (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
      (hin s ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hs1⟩)
  have hwcont : Continuous wseg := by fun_prop
  have hcoe_fv : ∀ x : ExtPlane, x ≠ OnePoint.infty → x = ((LehtoVirtanen1973.finiteValue x : ℂ) : ExtPlane) := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact absurd rfl hx
    | coe c => rfl
  set f : ℝ → ℂ := fun s => LehtoVirtanen1973.finiteValue (G ((wseg s : ℂ) : ExtPlane)) with hf
  have hfG : ∀ s ∈ Icc (0 : ℝ) 1, ((f s : ℂ) : ExtPlane) = G ((wseg s : ℂ) : ExtPlane) := fun s hs =>
    (hcoe_fv _ (hinf s hs)).symm
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hc : ContinuousWithinAt (fun s => G ((wseg s : ℂ) : ExtPlane)) (Icc 0 1) s :=
      ((hGcont _ (hwRc s hs)).comp hwcont.continuousWithinAt fun t ht => hwRc t ht)
    have hfv : ContinuousAt LehtoVirtanen1973.finiteValue (G ((wseg s : ℂ) : ExtPlane)) := by
      have h := hcoe_fv _ (hinf s hs)
      rw [h]
      exact LehtoVirtanen1973.lv15_finiteValue_continuousAt _
    exact ContinuousAt.comp_continuousWithinAt (f := fun s => G ((wseg s : ℂ) : ExtPlane)) hfv hc
  · intro s hs t ht hst
    have h1 : G ((wseg s : ℂ) : ExtPlane) = G ((wseg t : ℂ) : ExtPlane) := by
      rw [← hfG s hs, ← hfG t ht, hst]
    have h2 := hGinj (hwRc s hs) (hwRc t ht) h1
    have h3 : (s : ℂ) * (w1 - w0) = (t : ℂ) * (w1 - w0) := by
      have : w0 + (s : ℂ) * (w1 - w0) = w0 + (t : ℂ) * (w1 - w0) := h2
      exact add_left_cancel this
    have hw : w1 - w0 ≠ 0 := sub_ne_zero.2 hne.symm
    exact_mod_cast mul_right_cancel₀ hw h3
  · intro s hs
    refine ⟨?_, ?_⟩
    · rw [hfG s hs]
      exact (hGinv _ (hwRc s hs)).2
    · rw [hfG s hs]
      exact (hGinv _ (hwRc s hs)).1
  · intro s hs
    have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
    have hphi : φ ((f s : ℂ) : ExtPlane) = ((wseg s : ℂ) : ExtPlane) := by
      rw [hfG s hsI]
      exact (hGinv _ (hwRc s hsI)).2
    have hmemD : ((f s : ℂ) : ExtPlane) ∈ Q.dom := by
      have hmem : φ ((f s : ℂ) : ExtPlane) ∈ φ '' Q.dom := by
        rw [himg, hphi]
        exact ⟨wseg s, hin s hs, rfl⟩
      obtain ⟨p, hp, hpe⟩ := hmem
      have hcl : ((f s : ℂ) : ExtPlane) ∈ closure Q.dom := by
        rw [hfG s hsI]
        exact (hGinv _ (hwRc s hsI)).1
      have : p = ((f s : ℂ) : ExtPlane) := hhomeo.2.1 (subset_closure hp) hcl hpe
      rw [← this]
      exact hp
    refine ⟨hmemD, ?_⟩
    exact gm4d_finiteMap_coe φ (w0 + s * (w1 - w0)) (f s) hphi

/-- Helper (membership in the sides): a finite point of the closure whose image lies on the left (right) side of the
rectangle lies on `Q.side 3` (`Q.side 1`). -/
theorem gm4d_side_pre (Q : Quadrilateral) {ℓ : ℝ} {φ : ExtPlane → ExtPlane}
    (hφ : IsCanonicalMap Q.dom Q.vert ℓ 1 φ) {p : ExtPlane} (hp : p ∈ closure Q.dom) :
    (φ p ∈ toExt ({0} ×ℂ Icc 0 1) → p ∈ Q.side 3) ∧ (φ p ∈ toExt ({ℓ} ×ℂ Icc 0 1) → p ∈ Q.side 1) := by
  have hside := gm4d_side_image Q hφ
  obtain ⟨hℓ, h1, ⟨hDom, hcont, hinj, hdiff⟩, himg, hhomeo, hvert⟩ := hφ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← hside.1] at h
    obtain ⟨q, hq, hqp⟩ := h
    have hqc : q ∈ closure Q.dom := frontier_subset_closure hq.1
    have : q = p := hhomeo.2.1 hqc hp hqp
    rw [← this]
    exact hq
  · rw [← hside.2] at h
    obtain ⟨q, hq, hqp⟩ := h
    have hqc : q ∈ closure Q.dom := frontier_subset_closure hq.1
    have : q = p := hhomeo.2.1 hqc hp hqp
    rw [← this]
    exact hq

/-- Helper (crossing, separating curves): the image `ψ(γ)` of a curve `γ` separating `E` from `F` in `Ω` has linear
measure `≥ 1` (it meets every horizontal segment of the rectangle off the height of the missing point). -/
theorem gm4d_sep_crossing (Q : Quadrilateral) {ℓ : ℝ} {φ : ExtPlane → ExtPlane}
    (hφ : IsCanonicalMap Q.dom Q.vert ℓ 1 φ) {Ω E F : Set ℂ} {ψ : ℂ → ℂ} (hΩ : Ω = finitePart Q.dom)
    (hE : E = finitePart (Q.side 3)) (hF : F = finitePart (Q.side 1)) (hψ : ψ = LehtoVirtanen1973.finiteMap φ)
    {γ : Set ℂ} (hγ : γ ∈ separatingFamily Ω E F) : 1 ≤ μH[1] (ψ '' γ) := by
  have hG := gm4d_G_facts Q hφ hΩ hψ (G := Function.invFunOn φ (closure Q.dom)) rfl
  obtain ⟨hGinv, hGcont, hGinj, hGψ, hGinf, hGuniq, hGL, hGR⟩ := hG
  have hℓ : 0 < ℓ := hφ.1
  obtain ⟨hpc, ⟨s, hsfin, hγs, harcs⟩, hsep⟩ := hγ
  have hsubc : ∀ {Ω' γ : Set ℂ}, IsPathCurve Ω' γ → γ ⊆ Ω' := fun {Ω' γ} h => by
    obtain ⟨s, hs, rfl⟩ := h
    exact iUnion_subset fun n => (hs n).2
  have hγΩ : γ ⊆ Ω := hsubc hpc
  set Y0 : Set ℝ := {y | ∃ w ∈ Icc 0 ℓ ×ℂ Icc 0 1, w.im = y ∧
    Function.invFunOn φ (closure Q.dom) (w : ExtPlane) = OnePoint.infty} with hY0
  have hY0sub : Y0.Subsingleton := by
    rintro _ ⟨w, hw, rfl, hwi⟩ _ ⟨w', hw', rfl, hwi'⟩
    rw [hGuniq w hw w' hw' hwi hwi']
  have hY0null : volume Y0 = 0 := hY0sub.finite.measure_zero volume
  have hhit : ∀ y ∈ Ioo (0 : ℝ) 1, y ∉ Y0 → y ∈ Complex.im '' (ψ '' γ) := by
    intro y hy hyY
    by_contra hno
    have hre : ∀ s' : ℝ, ((y : ℂ) * I + (s' : ℂ) * ((ℓ : ℂ) + y * I - y * I)).re = s' * ℓ := by
      intro s'
      simp
    have him' : ∀ s' : ℝ, ((y : ℂ) * I + (s' : ℂ) * ((ℓ : ℂ) + y * I - y * I)).im = y := by
      intro s'
      simp
    have hw : ∀ s' ∈ Icc (0 : ℝ) 1, ((y : ℂ) * I + s' * ((ℓ : ℂ) + y * I - y * I) : ℂ) ∈ Icc 0 ℓ ×ℂ Icc 0 1 := by
      intro s' hs'
      rw [mem_reProdIm, hre, him']
      exact ⟨⟨mul_nonneg hs'.1 hℓ.le, by nlinarith [hs'.2]⟩, hy.1.le, hy.2.le⟩
    have hin : ∀ s' ∈ Ioo (0 : ℝ) 1, ((y : ℂ) * I + s' * ((ℓ : ℂ) + y * I - y * I) : ℂ) ∈ Ioo 0 ℓ ×ℂ Ioo 0 1 := by
      intro s' hs'
      rw [mem_reProdIm, hre, him']
      exact ⟨⟨mul_pos hs'.1 hℓ, by nlinarith [hs'.2]⟩, hy.1, hy.2⟩
    have hinf : ∀ s' ∈ Icc (0 : ℝ) 1, Function.invFunOn φ (closure Q.dom)
        (((y : ℂ) * I + s' * ((ℓ : ℂ) + y * I - y * I) : ℂ) : ExtPlane) ≠ OnePoint.infty := by
      intro s' hs' h
      exact hyY ⟨_, hw s' hs', him' s', h⟩
    have hne : (y : ℂ) * I ≠ (ℓ : ℂ) + y * I := by
      intro h
      have := congrArg Complex.re h
      simp at this
      exact hℓ.ne' this.symm
    obtain ⟨f, hfc, hfi, hfφ, hfΩ⟩ := gm4d_seg_arc Q hφ hΩ hψ rfl hne (by simpa using hw 0 ⟨le_rfl, zero_le_one⟩)
      (by have h := hw 1 ⟨zero_le_one, le_rfl⟩; simpa [add_comm] using h) hin hinf
    -- the open arc misses `γ`
    set K : Set ℂ := f '' Ioo 0 1 with hK
    have hKΩ : K ⊆ Ω := by
      rintro _ ⟨s', hs', rfl⟩
      exact (hfΩ s' hs').1
    have hKγ : K ⊆ Ω \ γ := by
      rintro _ ⟨s', hs', rfl⟩
      refine ⟨(hfΩ s' hs').1, fun hmem => hno ⟨ψ (f s'), ⟨f s', hmem, rfl⟩, ?_⟩⟩
      rw [(hfΩ s' hs').2]
      simp
    have hKconn : IsPreconnected K := isPreconnected_Ioo.image f (hfc.mono Ioo_subset_Icc_self)
    have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have hm : f (1 / 2) ∈ K := mem_image_of_mem f hhalf
    have hKc : K ⊆ connectedComponentIn (Ω \ γ) (f (1 / 2)) := hKconn.subset_connectedComponentIn hm hKγ
    have hcl : f '' closure (Ioo (0 : ℝ) 1) ⊆ closure K :=
      (hfc.mono (by rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)])).image_closure
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hcl
    have hcl0 : ((f 0 : ℂ) : ExtPlane) ∈ closure Q.dom := (hfφ 0 ⟨le_rfl, zero_le_one⟩).2
    have hcl1 : ((f 1 : ℂ) : ExtPlane) ∈ closure Q.dom := (hfφ 1 ⟨zero_le_one, le_rfl⟩).2
    have hp0 : ((f 0 : ℂ) : ExtPlane) ∈ Q.side 3 := by
      refine (gm4d_side_pre Q hφ hcl0).1 ?_
      rw [(hfφ 0 ⟨le_rfl, zero_le_one⟩).1]
      refine ⟨(y : ℂ) * I, ⟨by simp, by simpa using ⟨hy.1.le, hy.2.le⟩⟩, ?_⟩
      simp
    have hp1 : ((f 1 : ℂ) : ExtPlane) ∈ Q.side 1 := by
      refine (gm4d_side_pre Q hφ hcl1).2 ?_
      rw [(hfφ 1 ⟨zero_le_one, le_rfl⟩).1]
      refine ⟨(ℓ : ℂ) + y * I, ⟨by simp, by simpa using ⟨hy.1.le, hy.2.le⟩⟩, ?_⟩
      simp [add_comm]
    exact hsep (f (1 / 2)) (hKγ hm) ⟨⟨f 0, closure_mono hKc (hcl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩), by rw [hE]; exact hp0⟩,
      ⟨f 1, closure_mono hKc (hcl ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩), by rw [hF]; exact hp1⟩⟩
  have him : LipschitzWith 1 Complex.im := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simpa [dist_eq_norm, Real.dist_eq] using abs_im_le_norm (a - b)
  calc (1 : ℝ≥0∞) = μH[1] (Ioo (0 : ℝ) 1 \ Y0) := by
        rw [hausdorffMeasure_real, measure_sdiff_null hY0null, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one]
    _ ≤ μH[1] (Complex.im '' (ψ '' γ)) := measure_mono fun y hy => hhit y hy.1 hy.2
    _ ≤ μH[1] (ψ '' γ) := by
        simpa using him.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1) (ψ '' γ)

/-- Helper (finite lengths): for the inverse `g` of the conformal map `ψ`, the integral of `|g'|` over the part of
the image whose preimage lies in a ball is finite (Cauchy–Schwarz and the area of the ball). This gives, for almost
every line, the finite length of the preimage of a parallel segment. -/
theorem gm4d_deriv_finite (Q : Quadrilateral) {ℓ : ℝ} {φ : ExtPlane → ExtPlane}
    (hφ : IsCanonicalMap Q.dom Q.vert ℓ 1 φ) {Ω : Set ℂ} {ψ : ℂ → ℂ} (hΩ : Ω = finitePart Q.dom)
    (hψ : ψ = LehtoVirtanen1973.finiteMap φ) (N : ℝ) :
    ∫⁻ w in ψ '' Ω ∩ {w | ‖Function.invFunOn ψ Ω w‖ < N}, ‖deriv (Function.invFunOn ψ Ω) w‖ₑ < ⊤ := by
  subst hΩ hψ
  obtain ⟨hopen, hconf, hsub, hZ⟩ := gm4d_plane_conformal Q hφ rfl rfl
  set Ω := finitePart Q.dom with hΩ
  set ψ := LehtoVirtanen1973.finiteMap φ with hψ
  set Ω' := ψ '' Ω with hΩ'
  have hopen' : IsOpen Ω' := hconf.isOpen hopen
  have hg : LiZhongQC.IsConformalOnto (Function.invFunOn ψ Ω) Ω' Ω := hconf.symm hopen
  set g := Function.invFunOn ψ Ω with hgdef
  set W : Set ℂ := Ω' ∩ g ⁻¹' (ball 0 N) with hW
  have hWopen : IsOpen W := hg.1.continuousOn.isOpen_inter_preimage hopen' isOpen_ball
  have hconfW : LiZhongQC.IsConformalOnto g W (g '' W) :=
    ⟨hg.1.mono inter_subset_left, hg.2.1.mono inter_subset_left, rfl⟩
  have hgW : g '' W ⊆ ball 0 N := by
    rintro _ ⟨w, hw, rfl⟩
    exact hw.2
  have hvolR : volume (Ioo 0 ℓ ×ℂ Ioo 0 1) < ⊤ := by
    rw [← LiZhongQC.rectangle_eq_reProdIm, LiZhongQC.volume_rectangle]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have h1 := LiZhongQC.lintegral_image_conformal hWopen hconfW (fun _ => (1 : ℝ≥0∞))
  simp only [lintegral_const, Measure.restrict_apply_univ, one_mul, mul_one] at h1
  have h2 : ∫⁻ z in W, ‖deriv g z‖ₑ ^ 2 < ⊤ := by
    rw [← h1]
    exact (measure_mono hgW).trans_lt measure_ball_lt_top
  have h3 := LiZhongQC.setLIntegral_sq_le (s := W) (ρ := fun z => ‖deriv g z‖ₑ) (measurable_deriv g).enorm
  have h4 : volume W * ∫⁻ z in W, ‖deriv g z‖ₑ ^ 2 < ⊤ :=
    ENNReal.mul_lt_top (((measure_mono (inter_subset_left.trans hsub)).trans_lt hvolR)) h2
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [show Ω' ∩ {w | ‖g w‖ < N} = W by ext w; simp [hW]] at hcon
  rw [hcon, ENNReal.top_pow two_ne_zero, top_le_iff] at h3
  exact h4.ne h3

/-- Helper (an arc of `Ω` over a segment is a Jordan arc): if `f` is continuous on `[0, 1]`, takes values in `Ω` on
`(0, 1)` and `ψ ∘ f` is the affine parametrization `w0 + s (w1 - w0)` of a segment with `w0 ≠ w1`, then `f((0, 1))` is a
Jordan arc (the inverse is the affine inverse of `ψ`). -/
theorem gm4d_arc_jordan {Ω : Set ℂ} {ψ : ℂ → ℂ} (hψc : ContinuousOn ψ Ω) {f : ℝ → ℂ}
    (hfc : ContinuousOn f (Icc 0 1)) {w0 w1 : ℂ} (hne : w0 ≠ w1)
    (hfΩ : ∀ s ∈ Ioo (0 : ℝ) 1, f s ∈ Ω ∧ ψ (f s) = w0 + s * (w1 - w0)) :
    IsJordanArc (toExt (f '' Ioo 0 1)) := by
  have hw : w1 - w0 ≠ 0 := sub_ne_zero.2 hne.symm
  set F' : Ioo (0 : ℝ) 1 → Ω := fun s => ⟨f s, (hfΩ s s.2).1⟩ with hF'
  have hF'c : Continuous F' := by
    refine Continuous.subtype_mk ?_ _
    exact (hfc.mono Ioo_subset_Icc_self).comp_continuous continuous_subtype_val fun s => s.2
  set L : Ω → ℝ := fun z => ((ψ z - w0) / (w1 - w0)).re with hL
  have hLc : Continuous L := by
    refine Complex.continuous_re.comp (Continuous.div_const ?_ _)
    exact (hψc.comp_continuous continuous_subtype_val fun z => z.2).sub continuous_const
  have hcomp : L ∘ F' = Subtype.val := by
    funext s
    simp only [Function.comp_apply, hL, hF', (hfΩ s s.2).2]
    rw [show w0 + (s : ℂ) * (w1 - w0) - w0 = (s : ℂ) * (w1 - w0) by ring, mul_div_assoc, div_self hw, mul_one]
    simp
  have hemb : IsEmbedding F' := IsEmbedding.of_comp hF'c hLc (hcomp ▸ IsEmbedding.subtypeVal)
  refine ⟨Ioo 0 1, ordConnected_Ioo, ⟨1 / 3, ⟨by norm_num, by norm_num⟩, 2 / 3, ⟨by norm_num, by norm_num⟩, by norm_num⟩,
    fun s => ((f s : ℂ) : ExtPlane), ?_, ?_⟩
  · have : (Ioo (0 : ℝ) 1).domRestrict (fun s => ((f s : ℂ) : ExtPlane)) =
        ((↑) : ℂ → ExtPlane) ∘ Subtype.val ∘ F' := rfl
    rw [this]
    exact OnePoint.isOpenEmbedding_coe.isEmbedding.comp (IsEmbedding.subtypeVal.comp hemb)
  · rw [LiZhongQC.toExt, image_image]

/-- Helper (almost every line has finite truncated length): with `g = ψ⁻¹` and `h_n` the indicator of
`ψ(Ω) ∩ {|g| < n}` times `|g'|`, for almost every height (abscissa) the integral of `h_n` along the horizontal
(vertical) line is finite, for all `n`. -/
theorem gm4d_deriv_ae (Q : Quadrilateral) {ℓ : ℝ} {φ : ExtPlane → ExtPlane}
    (hφ : IsCanonicalMap Q.dom Q.vert ℓ 1 φ) {Ω : Set ℂ} {ψ : ℂ → ℂ} (hΩ : Ω = finitePart Q.dom)
    (hψ : ψ = LehtoVirtanen1973.finiteMap φ) :
    (∀ᵐ y ∂(volume.restrict (Ioo (0 : ℝ) 1)), ∀ n : ℕ,
      (∫⁻ x in Ioo (0 : ℝ) ℓ, (ψ '' Ω ∩ {w | ‖Function.invFunOn ψ Ω w‖ < n}).indicator
        (fun w => ‖deriv (Function.invFunOn ψ Ω) w‖ₑ) (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I)) < ⊤) ∧
    (∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) ℓ)), ∀ n : ℕ,
      (∫⁻ y in Ioo (0 : ℝ) 1, (ψ '' Ω ∩ {w | ‖Function.invFunOn ψ Ω w‖ < n}).indicator
        (fun w => ‖deriv (Function.invFunOn ψ Ω) w‖ₑ) (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I)) < ⊤) := by
  obtain ⟨hopen, hconf, hsub, hZ⟩ := gm4d_plane_conformal Q hφ hΩ hψ
  have hfin := fun n : ℕ => gm4d_deriv_finite Q hφ hΩ hψ (n : ℝ)
  have hopen' : IsOpen (ψ '' Ω) := hconf.isOpen hopen
  have hg : LiZhongQC.IsConformalOnto (Function.invFunOn ψ Ω) (ψ '' Ω) Ω := hconf.symm hopen
  set g := Function.invFunOn ψ Ω with hgdef
  set W : ℕ → Set ℂ := fun n => ψ '' Ω ∩ {w | ‖g w‖ < n} with hW
  have hWopen : ∀ n, IsOpen (W n) := fun n => by
    have := hg.1.continuousOn.isOpen_inter_preimage hopen' (isOpen_ball (x := (0 : ℂ)) (ε := (n : ℝ)))
    convert this using 2
    ext w
    simp
  set h : ℕ → ℂ → ℝ≥0∞ := fun n => (W n).indicator fun w => ‖deriv g w‖ₑ with hh
  have hhm : ∀ n, Measurable (h n) := fun n =>
    ((measurable_deriv g).enorm).indicator (hWopen n).measurableSet
  have hRe : Ioo 0 ℓ ×ℂ Ioo 0 1 = LiZhongQC.rectangle ℓ 1 := (LiZhongQC.rectangle_eq_reProdIm ℓ 1).symm
  have htot : ∀ n, (∫⁻ x in Ioo (0 : ℝ) ℓ, ∫⁻ y in Ioo (0 : ℝ) 1, h n (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I)) < ⊤ := fun n => by
    rw [← LiZhongQC.setLIntegral_rectangle (hhm n), ← hRe]
    rw [hh, lintegral_indicator (hWopen n).measurableSet, Measure.restrict_restrict (hWopen n).measurableSet,
      inter_eq_left.2 ((inter_subset_left).trans hsub)]
    exact hfin n
  have hmeas2 : ∀ n, Measurable fun p : ℝ × ℝ => h n ((p.1 : ℂ) + (p.2 : ℂ) * I) := fun n =>
    (hhm n).comp (by fun_prop)
  constructor
  · refine ae_all_iff.2 fun n => ?_
    have hswap : ∫⁻ y in Ioo (0 : ℝ) 1, ∫⁻ x in Ioo (0 : ℝ) ℓ, h n (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I) =
        ∫⁻ x in Ioo (0 : ℝ) ℓ, ∫⁻ y in Ioo (0 : ℝ) 1, h n (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I) :=
      (lintegral_lintegral_swap (hmeas2 n).aemeasurable).symm
    exact ae_lt_top ((hmeas2 n).lintegral_prod_left' (μ := volume.restrict (Ioo 0 ℓ))) (by
      rw [hswap]
      exact (htot n).ne)
  · refine ae_all_iff.2 fun n => ?_
    exact ae_lt_top ((hmeas2 n).lintegral_prod_right' (ν := volume.restrict (Ioo (0 : ℝ) 1))) (htot n).ne

/-- Helper (good heights): for almost every height `y ∈ (0, 1)` the horizontal segment of the rectangle is the image
`ψ(γ)` of a curve `γ` of the joining family (the preimage is a Jordan arc of finite length, with endpoints on `E`
and `F`). -/
theorem gm4d_good_heights (Q : Quadrilateral) {ℓ : ℝ} {φ : ExtPlane → ExtPlane}
    (hφ : IsCanonicalMap Q.dom Q.vert ℓ 1 φ) {Ω E F : Set ℂ} {ψ : ℂ → ℂ} (hΩ : Ω = finitePart Q.dom)
    (hE : E = finitePart (Q.side 3)) (hF : F = finitePart (Q.side 1)) (hψ : ψ = LehtoVirtanen1973.finiteMap φ) :
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ y ∈ Ioo (0 : ℝ) 1, y ∉ N → ∃ γ ∈ joiningFamily Ω E F,
      ψ '' γ = (fun t : ℝ => (y : ℂ) * I + t * 1) '' Ioo 0 ℓ := by
  subst hE hF
  have hside := gm4d_side_image Q hφ
  obtain ⟨hGinv, hGcont, hGinj, hGψ, hGinf, hGuniq, hGL, hGR⟩ :=
    gm4d_G_facts Q hφ hΩ hψ (G := Function.invFunOn φ (closure Q.dom)) rfl
  have hℓ : 0 < ℓ := hφ.1
  obtain ⟨hopen, hconf, hsub, hZ⟩ := gm4d_plane_conformal Q hφ hΩ hψ
  obtain ⟨hae, -⟩ := gm4d_deriv_ae Q hφ hΩ hψ
  have hopen' : IsOpen (ψ '' Ω) := hconf.isOpen hopen
  have hg : LiZhongQC.IsConformalOnto (Function.invFunOn ψ Ω) (ψ '' Ω) Ω := hconf.symm hopen
  set g := Function.invFunOn ψ Ω with hgdef
  set Y0 : Set ℝ := {y | ∃ w ∈ Icc 0 ℓ ×ℂ Icc 0 1, w.im = y ∧
    Function.invFunOn φ (closure Q.dom) (w : ExtPlane) = OnePoint.infty} with hY0
  have hY0sub : Y0.Subsingleton := by
    rintro _ ⟨w, hw, rfl, hwi⟩ _ ⟨w', hw', rfl, hwi'⟩
    rw [hGuniq w hw w' hw' hwi hwi']
  have hY0null : volume Y0 = 0 := hY0sub.finite.measure_zero volume
  set P : ℝ → Prop := fun y => ∀ n : ℕ, (∫⁻ x in Ioo (0 : ℝ) ℓ, ((ψ '' Ω ∩ {w | ‖g w‖ < n}).indicator
    (fun w => ‖deriv g w‖ₑ)) (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I)) < ⊤ with hP
  have hBnull : volume {y | y ∈ Ioo (0 : ℝ) 1 ∧ ¬ P y} = 0 := by
    have h := (ae_restrict_iff' measurableSet_Ioo).1 hae
    rw [ae_iff] at h
    have hsub' : {y | y ∈ Ioo (0 : ℝ) 1 ∧ ¬ P y} ⊆ {a | ¬ (a ∈ Ioo (0 : ℝ) 1 → P a)} := fun y hy hh => hy.2 (hh hy.1)
    exact measure_mono_null hsub' h
  refine ⟨Y0 ∪ {y | y ∈ Ioo (0 : ℝ) 1 ∧ ¬ P y}, measure_union_null hY0null hBnull, fun y hy hyN => ?_⟩
  have hyY : y ∉ Y0 := fun h => hyN (Or.inl h)
  have hyP : P y := by
    by_contra h
    exact hyN (Or.inr ⟨hy, h⟩)
  have hre : ∀ s' : ℝ, ((y : ℂ) * I + (s' : ℂ) * ((ℓ : ℂ) + y * I - y * I)).re = s' * ℓ := by
    intro s'
    simp
  have him' : ∀ s' : ℝ, ((y : ℂ) * I + (s' : ℂ) * ((ℓ : ℂ) + y * I - y * I)).im = y := by
    intro s'
    simp
  have hw : ∀ s' ∈ Icc (0 : ℝ) 1, ((y : ℂ) * I + s' * ((ℓ : ℂ) + y * I - y * I) : ℂ) ∈ Icc 0 ℓ ×ℂ Icc 0 1 := by
    intro s' hs'
    rw [mem_reProdIm, hre, him']
    exact ⟨⟨mul_nonneg hs'.1 hℓ.le, by nlinarith [hs'.2]⟩, hy.1.le, hy.2.le⟩
  have hin : ∀ s' ∈ Ioo (0 : ℝ) 1, ((y : ℂ) * I + s' * ((ℓ : ℂ) + y * I - y * I) : ℂ) ∈ Ioo 0 ℓ ×ℂ Ioo 0 1 := by
    intro s' hs'
    rw [mem_reProdIm, hre, him']
    exact ⟨⟨mul_pos hs'.1 hℓ, by nlinarith [hs'.2]⟩, hy.1, hy.2⟩
  have hinf : ∀ s' ∈ Icc (0 : ℝ) 1, Function.invFunOn φ (closure Q.dom)
      (((y : ℂ) * I + s' * ((ℓ : ℂ) + y * I - y * I) : ℂ) : ExtPlane) ≠ OnePoint.infty := by
    intro s' hs' h
    exact hyY ⟨_, hw s' hs', him' s', h⟩
  have hne : (y : ℂ) * I ≠ (ℓ : ℂ) + y * I := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hℓ.ne' this.symm
  obtain ⟨f, hfc, hfi, hfφ, hfΩ⟩ := gm4d_seg_arc Q hφ hΩ hψ rfl hne (by simpa using hw 0 ⟨le_rfl, zero_le_one⟩)
    (by have h := hw 1 ⟨zero_le_one, le_rfl⟩; simpa [add_comm] using h) hin hinf
  have hψc : ContinuousOn ψ Ω := hconf.1.continuousOn
  set γ : Set ℂ := f '' Ioo 0 1 with hγ
  have hγΩ : γ ⊆ Ω := by
    rintro _ ⟨s, hs, rfl⟩
    exact (hfΩ s hs).1
  have hψγ : ψ '' γ = (fun t : ℝ => (y : ℂ) * I + t * 1) '' Ioo 0 ℓ := by
    ext w
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨s * ℓ, ⟨mul_pos hs.1 hℓ, by nlinarith [hs.2]⟩, ?_⟩
      rw [(hfΩ s hs).2]
      simp only [mul_one]
      push_cast
      ring
    · rintro ⟨t, ht, rfl⟩
      refine ⟨f (t / ℓ), ⟨t / ℓ, ⟨div_pos ht.1 hℓ, by rw [div_lt_one hℓ]; exact ht.2⟩, rfl⟩, ?_⟩
      rw [(hfΩ (t / ℓ) ⟨div_pos ht.1 hℓ, by rw [div_lt_one hℓ]; exact ht.2⟩).2]
      have hℓc : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hℓ.ne'
      push_cast
      field_simp
      ring
  -- finite length
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hseg : (fun t : ℝ => (y : ℂ) * I + t * 1) '' Ioo 0 ℓ ⊆ ψ '' Ω := by
    rw [← hψγ]
    exact image_mono hγΩ
  have hgγ : g '' ((fun t : ℝ => (y : ℂ) * I + t * 1) '' Ioo 0 ℓ) = γ := by
    rw [← hψγ, image_image]
    refine (image_congr fun z hz => hconf.2.1.leftInvOn_invFunOn (hγΩ hz)).trans (image_id γ)
  have hsegm : MeasurableSet ((fun t : ℝ => (y : ℂ) * I + t * 1) '' Ioo 0 ℓ) := by
    have hiso : Isometry (fun t : ℝ => (y : ℂ) * I + t * 1) := by
      refine Isometry.of_dist_eq fun a b => ?_
      simp [dist_eq_norm, ← ofReal_sub]
    exact hiso.isClosedEmbedding.measurableEmbedding.measurableSet_image.2 measurableSet_Ioo
  have hlen : μH[1] γ < ⊤ := by
    rw [← hgγ]
    refine lt_of_le_of_lt (gm4b_hausdorff_image_le hopen' hg hsegm hseg) ?_
    rw [gm4b_lintegral_line (c := (y : ℂ) * I) (u := 1) norm_one measurableSet_Ioo (measurable_deriv g).enorm]
    refine lt_of_le_of_lt (le_of_eq ?_) (hyP n)
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have hts : (t / ℓ) ∈ Ioo (0 : ℝ) 1 := ⟨div_pos ht.1 hℓ, by rw [div_lt_one hℓ]; exact ht.2⟩
    have hmem : (y : ℂ) * I + t * 1 ∈ ψ '' Ω := hseg ⟨t, ht, rfl⟩
    have hgval : g ((y : ℂ) * I + t * 1) = f (t / ℓ) := by
      have : (y : ℂ) * I + t * 1 = ψ (f (t / ℓ)) := by
        rw [(hfΩ (t / ℓ) hts).2]
        have hℓc : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hℓ.ne'
        push_cast
        field_simp
        ring
      rw [this]
      exact hconf.2.1.leftInvOn_invFunOn (hfΩ (t / ℓ) hts).1
    have hbd : ‖g ((y : ℂ) * I + t * 1)‖ < n := by
      rw [hgval]
      exact lt_of_le_of_lt (hC _ ⟨hts.1.le, hts.2.le⟩) hn
    rw [add_comm ((y : ℂ) * I) _, mul_one] at hmem hbd ⊢
    simp only [indicator_of_mem (show (t : ℂ) + y * I ∈ ψ '' Ω ∩ {w | ‖g w‖ < n} from ⟨hmem, hbd⟩)]
  have hcl0 : ((f 0 : ℂ) : ExtPlane) ∈ closure Q.dom := (hfφ 0 ⟨le_rfl, zero_le_one⟩).2
  have hcl1 : ((f 1 : ℂ) : ExtPlane) ∈ closure Q.dom := (hfφ 1 ⟨zero_le_one, le_rfl⟩).2
  have hp0 : ((f 0 : ℂ) : ExtPlane) ∈ Q.side 3 := by
    refine (gm4d_side_pre Q hφ hcl0).1 ?_
    rw [(hfφ 0 ⟨le_rfl, zero_le_one⟩).1]
    refine ⟨(y : ℂ) * I, ⟨by simp, by simpa using ⟨hy.1.le, hy.2.le⟩⟩, ?_⟩
    simp
  have hp1 : ((f 1 : ℂ) : ExtPlane) ∈ Q.side 1 := by
    refine (gm4d_side_pre Q hφ hcl1).2 ?_
    rw [(hfφ 1 ⟨zero_le_one, le_rfl⟩).1]
    refine ⟨(ℓ : ℂ) + y * I, ⟨by simp, by simpa using ⟨hy.1.le, hy.2.le⟩⟩, ?_⟩
    simp [add_comm]
  have hjordan := gm4d_arc_jordan hψc hfc hne hfΩ
  refine ⟨γ, ⟨⟨fun _ => γ, fun _ => ⟨⟨hjordan, hlen⟩, hγΩ⟩, (iUnion_const γ).symm⟩, f, hfc, hfi, hp0, hp1, rfl⟩, hψγ⟩

/-- Helper (good abscissae): for almost every `x ∈ (0, ℓ)` the vertical segment of the rectangle is, up to a finite
set, the image `ψ(γ)` of a curve `γ` of the separating family (a finite union of Jordan arcs of finite length). -/
theorem gm4d_good_abscissae (Q : Quadrilateral) {ℓ : ℝ} {φ : ExtPlane → ExtPlane}
    (hφ : IsCanonicalMap Q.dom Q.vert ℓ 1 φ) {Ω E F : Set ℂ} {ψ : ℂ → ℂ} (hΩ : Ω = finitePart Q.dom)
    (hE : E = finitePart (Q.side 3)) (hF : F = finitePart (Q.side 1)) (hψ : ψ = LehtoVirtanen1973.finiteMap φ) :
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ x ∈ Ioo 0 ℓ, x ∉ N → ∃ γ ∈ separatingFamily Ω E F,
      ψ '' γ =ᵐ[μH[1]] (fun t : ℝ => (x : ℂ) + t * I) '' Ioo 0 1 := by
  subst hE hF
  have hside := gm4d_side_image Q hφ
  obtain ⟨hGinv, hGcont, hGinj, hGψ, hGinf, hGuniq, hGL, hGR⟩ :=
    gm4d_G_facts Q hφ hΩ hψ (G := Function.invFunOn φ (closure Q.dom)) rfl
  have hℓ : 0 < ℓ := hφ.1
  obtain ⟨hopen, hconf, hsub, hZ⟩ := gm4d_plane_conformal Q hφ hΩ hψ
  obtain ⟨-, hae⟩ := gm4d_deriv_ae Q hφ hΩ hψ
  have hopen' : IsOpen (ψ '' Ω) := hconf.isOpen hopen
  have hg : LiZhongQC.IsConformalOnto (Function.invFunOn ψ Ω) (ψ '' Ω) Ω := hconf.symm hopen
  set g := Function.invFunOn ψ Ω with hgdef
  have hφcoe : ∀ z ∈ Ω, φ (z : ExtPlane) = ((ψ z : ℂ) : ExtPlane) := by
    intro z hz
    have hmem : φ (z : ExtPlane) ∈ toExt (Ioo 0 ℓ ×ℂ Ioo 0 1) := by
      have h := hφ.2.2.2.1
      rw [LiZhongQC.rectangle_eq_reProdIm] at h
      rw [← h]
      exact mem_image_of_mem φ (by rw [hΩ] at hz; exact hz)
    obtain ⟨w, hw, hw'⟩ := hmem
    have hz' : ψ z = w := by
      rw [hψ]
      exact gm4d_finiteMap_coe φ w z hw'.symm
    rw [hz']
    exact hw'.symm
  set X0 : Set ℝ := {x | ∃ w ∈ Icc 0 ℓ ×ℂ Icc 0 1, w.re = x ∧
    Function.invFunOn φ (closure Q.dom) (w : ExtPlane) = OnePoint.infty} with hX0
  have hX0sub : X0.Subsingleton := by
    rintro _ ⟨w, hw, rfl, hwi⟩ _ ⟨w', hw', rfl, hwi'⟩
    rw [hGuniq w hw w' hw' hwi hwi']
  have hX0null : volume X0 = 0 := hX0sub.finite.measure_zero volume
  set P : ℝ → Prop := fun x => ∀ n : ℕ, (∫⁻ y in Ioo (0 : ℝ) 1, ((ψ '' Ω ∩ {w | ‖g w‖ < n}).indicator
    (fun w => ‖deriv g w‖ₑ)) (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I)) < ⊤ with hP
  have hBnull : volume {x | x ∈ Ioo (0 : ℝ) ℓ ∧ ¬ P x} = 0 := by
    have h := (ae_restrict_iff' measurableSet_Ioo).1 hae
    rw [ae_iff] at h
    have hsub' : {x | x ∈ Ioo (0 : ℝ) ℓ ∧ ¬ P x} ⊆ {a | ¬ (a ∈ Ioo (0 : ℝ) ℓ → P a)} := fun x hx hh => hx.2 (hh hx.1)
    exact measure_mono_null hsub' h
  refine ⟨X0 ∪ {x | x ∈ Ioo (0 : ℝ) ℓ ∧ ¬ P x}, measure_union_null hX0null hBnull, fun x hx hxN => ?_⟩
  have hxX : x ∉ X0 := fun h => hxN (Or.inl h)
  have hxP : P x := by
    by_contra h
    exact hxN (Or.inr ⟨hx, h⟩)
  have hre : ∀ s' : ℝ, ((x : ℂ) + (s' : ℂ) * ((x : ℂ) + I - x)).re = x := by
    intro s'
    simp
  have him' : ∀ s' : ℝ, ((x : ℂ) + (s' : ℂ) * ((x : ℂ) + I - x)).im = s' := by
    intro s'
    simp
  have hw : ∀ s' ∈ Icc (0 : ℝ) 1, ((x : ℂ) + s' * ((x : ℂ) + I - x) : ℂ) ∈ Icc 0 ℓ ×ℂ Icc 0 1 := by
    intro s' hs'
    rw [mem_reProdIm, hre, him']
    exact ⟨⟨hx.1.le, hx.2.le⟩, hs'⟩
  have hin : ∀ s' ∈ Ioo (0 : ℝ) 1, ((x : ℂ) + s' * ((x : ℂ) + I - x) : ℂ) ∈ Ioo 0 ℓ ×ℂ Ioo 0 1 := by
    intro s' hs'
    rw [mem_reProdIm, hre, him']
    exact ⟨hx, hs'⟩
  have hinf : ∀ s' ∈ Icc (0 : ℝ) 1, Function.invFunOn φ (closure Q.dom)
      (((x : ℂ) + s' * ((x : ℂ) + I - x) : ℂ) : ExtPlane) ≠ OnePoint.infty := by
    intro s' hs' h
    exact hxX ⟨_, hw s' hs', hre s', h⟩
  have hne : (x : ℂ) ≠ (x : ℂ) + I := by
    intro h
    have := congrArg Complex.im h
    simp at this
  obtain ⟨f, hfc, hfi, hfφ, hfΩ⟩ := gm4d_seg_arc Q hφ hΩ hψ rfl hne (by simpa using hw 0 ⟨le_rfl, zero_le_one⟩)
    (by simpa using hw 1 ⟨zero_le_one, le_rfl⟩) hin hinf
  have hψc : ContinuousOn ψ Ω := hconf.1.continuousOn
  set γ : Set ℂ := f '' Ioo 0 1 with hγ
  have hγΩ : γ ⊆ Ω := by
    rintro _ ⟨s, hs, rfl⟩
    exact (hfΩ s hs).1
  have hψγ : ψ '' γ = (fun t : ℝ => (x : ℂ) + t * I) '' Ioo 0 1 := by
    ext w
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨s, hs, ?_⟩
      rw [(hfΩ s hs).2]
      ring
    · rintro ⟨t, ht, rfl⟩
      refine ⟨f t, ⟨t, ht, rfl⟩, ?_⟩
      rw [(hfΩ t ht).2]
      ring
  -- finite length
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hseg : (fun t : ℝ => (x : ℂ) + t * I) '' Ioo 0 1 ⊆ ψ '' Ω := by
    rw [← hψγ]
    exact image_mono hγΩ
  have hgγ : g '' ((fun t : ℝ => (x : ℂ) + t * I) '' Ioo 0 1) = γ := by
    rw [← hψγ, image_image]
    refine (image_congr fun z hz => hconf.2.1.leftInvOn_invFunOn (hγΩ hz)).trans (image_id γ)
  have hsegm : MeasurableSet ((fun t : ℝ => (x : ℂ) + t * I) '' Ioo 0 1) := by
    have hiso : Isometry (fun t : ℝ => (x : ℂ) + t * I) := by
      refine Isometry.of_dist_eq fun a b => ?_
      rw [dist_eq_norm, Real.dist_eq, show (x : ℂ) + a * I - ((x : ℂ) + b * I) = ((a - b : ℝ) : ℂ) * I by push_cast; ring,
        norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    exact hiso.isClosedEmbedding.measurableEmbedding.measurableSet_image.2 measurableSet_Ioo
  have hlen : μH[1] γ < ⊤ := by
    rw [← hgγ]
    refine lt_of_le_of_lt (gm4b_hausdorff_image_le hopen' hg hsegm hseg) ?_
    rw [gm4b_lintegral_line (c := (x : ℂ)) (u := I) (by simp) measurableSet_Ioo (measurable_deriv g).enorm]
    refine lt_of_le_of_lt (le_of_eq ?_) (hxP n)
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have hmem : (x : ℂ) + t * I ∈ ψ '' Ω := hseg ⟨t, ht, rfl⟩
    have hgval : g ((x : ℂ) + t * I) = f t := by
      have : (x : ℂ) + t * I = ψ (f t) := by
        rw [(hfΩ t ht).2]
        ring
      rw [this]
      exact hconf.2.1.leftInvOn_invFunOn (hfΩ t ht).1
    have hbd : ‖g ((x : ℂ) + t * I)‖ < n := by
      rw [hgval]
      exact lt_of_le_of_lt (hC _ ⟨ht.1.le, ht.2.le⟩) hn
    simp only [indicator_of_mem (show (x : ℂ) + t * I ∈ ψ '' Ω ∩ {w | ‖g w‖ < n} from ⟨hmem, hbd⟩)]
  have hjordan := gm4d_arc_jordan hψc hfc hne hfΩ
  have hpc : IsPathCurve Ω γ := ⟨fun _ => γ, fun _ => ⟨⟨hjordan, hlen⟩, hγΩ⟩, (iUnion_const γ).symm⟩
  -- separation
  have hsep : IsSeparatingIn Ω γ (finitePart (Q.side 3)) (finitePart (Q.side 1)) := by
    intro z hz hboth
    obtain ⟨⟨p, hpK, hpE⟩, ⟨q, hqK, hqF⟩⟩ := hboth
    set K := connectedComponentIn (Ω \ γ) z with hK
    have hKsub : K ⊆ Ω \ γ := connectedComponentIn_subset _ _
    have hKconn : IsPreconnected K := isPreconnected_connectedComponentIn
    have hxne : ∀ w ∈ K, (ψ w).re ≠ x := by
      intro w hw hre'
      obtain ⟨hwΩ, hwγ⟩ := hKsub hw
      have hψR : ψ w ∈ Ioo 0 ℓ ×ℂ Ioo 0 1 := hsub ⟨w, hwΩ, rfl⟩
      have hψmem : ψ w ∈ ψ '' γ := by
        rw [hψγ]
        exact ⟨(ψ w).im, (mem_reProdIm.1 hψR).2, Complex.ext (by simp [hre']) (by simp)⟩
      obtain ⟨w', hw'γ, hw'⟩ := hψmem
      have : w' = w := hconf.2.1 (hγΩ hw'γ) hwΩ hw'
      exact hwγ (this ▸ hw'γ)
    set u1 : Set ℂ := Ω ∩ ψ ⁻¹' {a | a.re < x} with hu1d
    set u2 : Set ℂ := Ω ∩ ψ ⁻¹' {a | x < a.re} with hu2d
    have hu1 : IsOpen u1 := hψc.isOpen_inter_preimage hopen (isOpen_lt continuous_re continuous_const)
    have hu2 : IsOpen u2 := hψc.isOpen_inter_preimage hopen (isOpen_lt continuous_const continuous_re)
    have hKu : K ⊆ u1 ∪ u2 := fun w hw => by
      rcases lt_or_gt_of_ne (hxne w hw) with h | h
      · exact Or.inl ⟨(hKsub hw).1, h⟩
      · exact Or.inr ⟨(hKsub hw).1, h⟩
    have hdisj : Disjoint u1 u2 := Set.disjoint_left.2 fun w hw1 hw2 => lt_asymm (show (ψ w).re < x from hw1.2) (show x < (ψ w).re from hw2.2)
    -- closure of `K`
    have hKΩ : K ⊆ Ω := fun w hw => (hKsub hw).1
    have hclos : ∀ q ∈ closure K, ((q : ℂ) : ExtPlane) ∈ closure Q.dom ∧ ∀ A : Set ℂ, IsCompact A →
        (∀ w ∈ K, ψ w ∈ A) → φ ((q : ℂ) : ExtPlane) ∈ toExt A := by
      intro q hq
      have h1 : ((q : ℂ) : ExtPlane) ∈ closure (((↑) : ℂ → ExtPlane) '' K) :=
        image_closure_subset_closure_image OnePoint.continuous_coe ⟨q, hq, rfl⟩
      have hKD : ((↑) : ℂ → ExtPlane) '' K ⊆ closure Q.dom := by
        rintro _ ⟨w, hw, rfl⟩
        exact subset_closure (by rw [hΩ] at hKΩ; exact hKΩ hw)
      have hcl' : closure (((↑) : ℂ → ExtPlane) '' K) ⊆ closure Q.dom := closure_minimal hKD isClosed_closure
      refine ⟨hcl' h1, fun A hA hKA => ?_⟩
      have hcont : ContinuousOn φ (closure (((↑) : ℂ → ExtPlane) '' K)) := hφ.2.2.2.2.1.1.mono hcl'
      have h2 : φ ((q : ℂ) : ExtPlane) ∈ closure (φ '' (((↑) : ℂ → ExtPlane) '' K)) :=
        hcont.image_closure ⟨_, h1, rfl⟩
      have h3 : φ '' (((↑) : ℂ → ExtPlane) '' K) ⊆ toExt A := by
        rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨ψ w, hKA w hw, (hφcoe w (hKΩ hw)).symm⟩
      exact (hA.image OnePoint.continuous_coe).isClosed.closure_subset_iff.2 h3 h2
    rcases hKconn.subset_or_subset hu1 hu2 hdisj hKu with h1 | h1
    · -- `K` lies left of the line: its closure cannot reach the right side
      obtain ⟨hqc, hqA⟩ := hclos q hqK
      have hA : IsCompact (Icc 0 ℓ ×ℂ Icc 0 1 ∩ {a : ℂ | a.re ≤ x}) :=
        (IsCompact.reProdIm isCompact_Icc isCompact_Icc).inter_right (isClosed_le continuous_re continuous_const)
      have hmem := hqA _ hA (fun w hw => ⟨reProdIm_subset_iff.2 (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
        (hsub ⟨w, (hKsub hw).1, rfl⟩), le_of_lt (show (ψ w).re < x from (h1 hw).2)⟩)
      obtain ⟨a, ⟨-, hax⟩, hqa⟩ := hmem
      have hqF' : ((q : ℂ) : ExtPlane) ∈ Q.side 1 := hqF
      have hr : φ ((q : ℂ) : ExtPlane) ∈ toExt ({ℓ} ×ℂ Icc 0 1) := hside.2 ▸ mem_image_of_mem φ hqF'
      obtain ⟨b, hb, hbq⟩ := hr
      have : a = b := OnePoint.coe_injective (hqa.trans hbq.symm)
      have hare : a.re = ℓ := by rw [this]; simpa using hb.1
      have hax' : a.re ≤ x := hax
      linarith [hx.2, hax', hare]
    · obtain ⟨hpc', hpA⟩ := hclos p hpK
      have hA : IsCompact (Icc 0 ℓ ×ℂ Icc 0 1 ∩ {a : ℂ | x ≤ a.re}) :=
        (IsCompact.reProdIm isCompact_Icc isCompact_Icc).inter_right (isClosed_le continuous_const continuous_re)
      have hmem := hpA _ hA (fun w hw => ⟨reProdIm_subset_iff.2 (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
        (hsub ⟨w, (hKsub hw).1, rfl⟩), le_of_lt (show x < (ψ w).re from (h1 hw).2)⟩)
      obtain ⟨a, ⟨-, hax⟩, hpa⟩ := hmem
      have hpE' : ((p : ℂ) : ExtPlane) ∈ Q.side 3 := hpE
      have hr : φ ((p : ℂ) : ExtPlane) ∈ toExt ({0} ×ℂ Icc 0 1) := hside.1 ▸ mem_image_of_mem φ hpE'
      obtain ⟨b, hb, hbp⟩ := hr
      have : a = b := OnePoint.coe_injective (hpa.trans hbp.symm)
      have hare : a.re = 0 := by rw [this]; simpa using hb.1
      have hax' : x ≤ a.re := hax
      linarith [hx.1, hax', hare]
  refine ⟨γ, ⟨hpc, ⟨{γ}, finite_singleton _, (sUnion_singleton γ).symm, fun c hc => ?_⟩, hsep⟩, ?_⟩
  · rw [mem_singleton_iff] at hc
    subst hc
    exact Or.inl hjordan
  · rw [hψγ]

/-- Helper (the metric `|ψ'|`): its area is `ℓ` and its length on a Borel curve of `Ω` is the linear measure of the
image. -/
theorem gm4d_deriv_density (Q : Quadrilateral) {ℓ : ℝ} {φ : ExtPlane → ExtPlane}
    (hφ : IsCanonicalMap Q.dom Q.vert ℓ 1 φ) {Ω : Set ℂ} {ψ : ℂ → ℂ} (hΩ : Ω = finitePart Q.dom)
    (hψ : ψ = LehtoVirtanen1973.finiteMap φ) :
    derivDensity φ Ω ∈ LiZhongQC.densitiesP0 Ω ∧ LiZhongQC.rhoArea (derivDensity φ Ω) Ω = ENNReal.ofReal ℓ ∧
      ∀ γ : Set ℂ, MeasurableSet γ → γ ⊆ Ω → ∫⁻ z in γ, derivDensity φ Ω z ∂μH[1] = μH[1] (ψ '' γ) := by
  subst hΩ hψ
  obtain ⟨hopen, hconf, hsub, hZ⟩ := gm4d_plane_conformal Q hφ rfl rfl
  have hℓ : 0 < ℓ := hφ.1
  have heq : derivDensity φ (finitePart Q.dom) = (finitePart Q.dom).indicator
      fun z => (fun _ : ℂ => (1 : ℝ≥0∞)) (LehtoVirtanen1973.finiteMap φ z) *
        ‖deriv (LehtoVirtanen1973.finiteMap φ) z‖ₑ := by
    funext z
    rw [gm4d_derivDensity_apply]
    simp only [one_mul, ofReal_norm]
  have hmeas : Measurable (derivDensity φ (finitePart Q.dom)) := by
    rw [heq]
    exact LiZhongQC.measurable_pullback_density hopen hconf.1.continuousOn measurable_const
  have hnull : volume (Ioo 0 ℓ ×ℂ Ioo 0 1 \ LehtoVirtanen1973.finiteMap φ '' finitePart Q.dom) = 0 :=
    hZ.finite.measure_zero volume
  have hvol : volume (LehtoVirtanen1973.finiteMap φ '' finitePart Q.dom) = ENNReal.ofReal ℓ := by
    have hR : volume (Ioo 0 ℓ ×ℂ Ioo 0 1) = ENNReal.ofReal ℓ := by
      rw [← LiZhongQC.rectangle_eq_reProdIm, LiZhongQC.volume_rectangle, ENNReal.ofReal_one, mul_one]
    refine le_antisymm ((measure_mono hsub).trans hR.le) ?_
    calc ENNReal.ofReal ℓ = volume (Ioo 0 ℓ ×ℂ Ioo 0 1) := hR.symm
      _ ≤ volume (Ioo 0 ℓ ×ℂ Ioo 0 1 \ LehtoVirtanen1973.finiteMap φ '' finitePart Q.dom) +
          volume (LehtoVirtanen1973.finiteMap φ '' finitePart Q.dom) := by
          refine le_trans (measure_mono ?_) (measure_union_le _ _)
          intro z hz
          by_cases h : z ∈ LehtoVirtanen1973.finiteMap φ '' finitePart Q.dom
          · exact Or.inr h
          · exact Or.inl ⟨hz, h⟩
      _ = volume (LehtoVirtanen1973.finiteMap φ '' finitePart Q.dom) := by rw [hnull, zero_add]
  have hA : LiZhongQC.rhoArea (derivDensity φ (finitePart Q.dom)) (finitePart Q.dom) = ENNReal.ofReal ℓ := by
    rw [heq, LiZhongQC.rhoArea_pullback hopen hconf (fun _ => (1 : ℝ≥0∞)), gm4a_rhoArea_eq]
    simp only [one_pow, lintegral_const, Measure.restrict_apply_univ, one_mul]
    exact hvol
  refine ⟨gm4a_mem_densitiesP0.2 ⟨hmeas, hA ▸ ENNReal.ofReal_pos.2 hℓ, hA ▸ ENNReal.ofReal_lt_top⟩, hA, ?_⟩
  intro γ hγ hγΩ
  have h := gm4b_lintegral_image_conformal hopen hconf hγ hγΩ (ρ := fun _ => (1 : ℝ≥0∞)) measurable_const
  simp only [lintegral_const, Measure.restrict_apply_univ, one_mul] at h
  refine Eq.trans ?_ h.symm
  refine setLIntegral_congr_fun hγ fun z hz => ?_
  rw [gm4d_derivDensity_apply]
  simp only [indicator_of_mem (hγΩ hz), ofReal_norm]

/-- Helper (pull-back of a metric to the rectangle): every metric `ρ` of `Ω` has a pull-back `ρ'` which is a metric of
the rectangle of the same area, and `∫_γ ρ = ∫_{ψ(γ)} ρ'` for every Borel `γ ⊆ Ω`. -/
theorem gm4d_pullback (Q : Quadrilateral) {ℓ : ℝ} {φ : ExtPlane → ExtPlane}
    (hφ : IsCanonicalMap Q.dom Q.vert ℓ 1 φ) {Ω : Set ℂ} {ψ : ℂ → ℂ} (hΩ : Ω = finitePart Q.dom)
    (hψ : ψ = LehtoVirtanen1973.finiteMap φ) {ρ : ℂ → ℝ≥0∞} (hρ : ρ ∈ LiZhongQC.densitiesP0 Ω) :
    ∃ ρ' ∈ LiZhongQC.densitiesP0 (Ioo 0 ℓ ×ℂ Ioo 0 1),
      LiZhongQC.rhoArea ρ' (Ioo 0 ℓ ×ℂ Ioo 0 1) = LiZhongQC.rhoArea ρ Ω ∧
        ∀ γ : Set ℂ, MeasurableSet γ → γ ⊆ Ω → ∫⁻ z in γ, ρ z ∂μH[1] = ∫⁻ w in ψ '' γ, ρ' w ∂μH[1] := by
  subst hΩ hψ
  obtain ⟨hopen, hconf, hsub, hZ⟩ := gm4d_plane_conformal Q hφ rfl rfl
  obtain ⟨hρm, hρ0, hρt⟩ := gm4a_mem_densitiesP0.1 hρ
  set Ω := finitePart Q.dom with hΩ
  set ψ := LehtoVirtanen1973.finiteMap φ with hψ
  set Ω' := ψ '' Ω with hΩ'
  have hopen' : IsOpen Ω' := hconf.isOpen hopen
  have hg : LiZhongQC.IsConformalOnto (Function.invFunOn ψ Ω) Ω' Ω := hconf.symm hopen
  set g := Function.invFunOn ψ Ω with hgdef
  set ρ' : ℂ → ℝ≥0∞ := Ω'.indicator fun w => ρ (g w) * ‖deriv g w‖ₑ with hρ'
  have hρ'm : Measurable ρ' := LiZhongQC.measurable_pullback_density hopen' hg.1.continuousOn hρm
  have hA : ∀ D : Set ℂ, Ω' ⊆ D → LiZhongQC.rhoArea ρ' D = LiZhongQC.rhoArea ρ Ω := by
    intro D hD
    have h1 : LiZhongQC.rhoArea ρ' D = LiZhongQC.rhoArea ρ' Ω' := by
      rw [gm4a_rhoArea_eq, gm4a_rhoArea_eq]
      have e : (fun z => ρ' z ^ 2) = Ω'.indicator (fun z => (ρ (g z) * ‖deriv g z‖ₑ) ^ 2) := by
        funext z
        by_cases hz : z ∈ Ω' <;> simp [hρ', hz]
      rw [e, lintegral_indicator hopen'.measurableSet, lintegral_indicator hopen'.measurableSet,
        Measure.restrict_restrict hopen'.measurableSet, Measure.restrict_restrict hopen'.measurableSet,
        inter_eq_left.2 hD, inter_self]
    rw [h1]
    exact LiZhongQC.rhoArea_pullback hopen' hg ρ
  have hAR : LiZhongQC.rhoArea ρ' (Ioo 0 ℓ ×ℂ Ioo 0 1) = LiZhongQC.rhoArea ρ Ω := hA _ hsub
  refine ⟨ρ', gm4a_mem_densitiesP0.2 ⟨hρ'm, hAR ▸ hρ0, hAR ▸ hρt⟩, hAR, ?_⟩
  intro γ hγ hγΩ
  have hψγ : MeasurableSet (ψ '' γ) :=
    hγ.image_of_continuousOn_injOn (hconf.1.continuousOn.mono hγΩ) (hconf.2.1.mono hγΩ)
  have hsubγ : ψ '' γ ⊆ Ω' := image_mono hγΩ
  have hback : g '' (ψ '' γ) = γ := by
    rw [image_image]
    exact (image_congr fun z hz => hconf.2.1.leftInvOn_invFunOn (hγΩ hz)).trans (image_id γ)
  have h := gm4b_lintegral_image_conformal hopen' hg hψγ hsubγ hρm
  rw [hback] at h
  rw [h]
  exact setLIntegral_congr_fun hψγ fun w hw => by simp only [hρ', indicator_of_mem (hsubγ hw)]

/-- Helper (Cauchy–Schwarz on the segments, up to a null set of abscissae): as `gm4b_rect_core`, with the bound on `L`
required off a null set `Y`. -/
theorem gm4d_rect_core_null {a b : ℝ} {G : ℝ → ℝ → ℝ≥0∞} (hG : ∀ x, Measurable (G x)) {L : ℝ≥0∞} {Y : Set ℝ}
    (hY : volume Y = 0) (hL : ∀ x ∈ Ioo 0 a, x ∉ Y → L ≤ ∫⁻ y in Ioo 0 b, G x y) :
    ENNReal.ofReal a * L ^ 2 ≤ ENNReal.ofReal b * ∫⁻ x in Ioo 0 a, ∫⁻ y in Ioo 0 b, G x y ^ 2 := by
  have h1 : ∀ᵐ x ∂(volume.restrict (Ioo 0 a)), L ^ 2 ≤ ENNReal.ofReal b * ∫⁻ y in Ioo 0 b, G x y ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hY)] with x hx hxY
    calc L ^ 2 ≤ (∫⁻ y in Ioo 0 b, G x y) ^ 2 := pow_le_pow_left' (hL x hx hxY) 2
      _ ≤ (volume.restrict (Ioo 0 b)) univ * ∫⁻ y in Ioo 0 b, G x y ^ 2 :=
          gm4b_lintegral_sq_le _ (hG x).aemeasurable
      _ = ENNReal.ofReal b * ∫⁻ y in Ioo 0 b, G x y ^ 2 := by
          rw [Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]
  calc ENNReal.ofReal a * L ^ 2 = ∫⁻ _ in Ioo 0 a, L ^ 2 := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero, mul_comm]
    _ ≤ ∫⁻ x in Ioo 0 a, ENNReal.ofReal b * ∫⁻ y in Ioo 0 b, G x y ^ 2 := lintegral_mono_ae h1
    _ = ENNReal.ofReal b * ∫⁻ x in Ioo 0 a, ∫⁻ y in Ioo 0 b, G x y ^ 2 := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Helper (rectangle, horizontal segments off a null set of heights): if the family `Γ` contains the horizontal
segment at every height `y ∈ (0, h) \ Y`, `Y` null, then `L²/A ≤ ℓ/h` for every metric. -/
theorem gm4d_rect_hseg_ratio_le_null {ℓ h : ℝ} (hh : 0 < h) {Y : Set ℝ} (hY : volume Y = 0) {Γ : Set (Set ℂ)}
    (hΓ : ∀ y ∈ Ioo 0 h, y ∉ Y → (fun t : ℝ => (y : ℂ) * I + t * 1) '' Ioo 0 ℓ ∈ Γ) {ρ : ℂ → ℝ≥0∞}
    (hρ : ρ ∈ LiZhongQC.densitiesP0 (Ioo 0 ℓ ×ℂ Ioo 0 h)) :
    pathRhoLength Γ ρ ^ 2 / LiZhongQC.rhoArea ρ (Ioo 0 ℓ ×ℂ Ioo 0 h) ≤ ENNReal.ofReal (ℓ / h) := by
  obtain ⟨hm, hA0, hAt⟩ := gm4a_mem_densitiesP0.1 hρ
  have hR : Ioo 0 ℓ ×ℂ Ioo 0 h = LiZhongQC.rectangle ℓ h := (LiZhongQC.rectangle_eq_reProdIm ℓ h).symm
  have hmeas : Measurable fun p : ℝ × ℝ => ρ ((p.1 : ℂ) + (p.2 : ℂ) * I) ^ 2 :=
    (hm.comp (by fun_prop)).pow_const 2
  have hA : LiZhongQC.rhoArea ρ (Ioo 0 ℓ ×ℂ Ioo 0 h) =
      ∫⁻ y in Ioo 0 h, ∫⁻ x in Ioo 0 ℓ, ρ ((x : ℂ) + (y : ℂ) * I) ^ 2 := by
    rw [gm4a_rhoArea_eq, hR, LiZhongQC.setLIntegral_rectangle (hm.pow_const 2)]
    exact lintegral_lintegral_swap hmeas.aemeasurable
  have hcore := gm4d_rect_core_null (G := fun y x => ρ ((x : ℂ) + (y : ℂ) * I)) (fun y => hm.comp (by fun_prop))
    (L := pathRhoLength Γ ρ) hY fun y hy hyY => by
      refine (iInf₂_le _ (hΓ y hy hyY)).trans_eq ?_
      rw [gm4b_lintegral_line (c := (y : ℂ) * I) (u := 1) norm_one measurableSet_Ioo hm]
      refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
      rw [mul_one, add_comm]
  rw [← hA] at hcore
  exact gm4b_div_le_of_mul_le hh hA0.ne' hAt.ne hcore

/-- Helper (rectangle, vertical segments up to null sets): if for every abscissa `x ∈ (0, ℓ) \ Y`, `Y` null, the family
`Γ` has a curve that equals the vertical segment `μH[1]`-almost everywhere, then `L²/A ≤ h/ℓ`. -/
theorem gm4d_rect_vseg_ratio_le_null {ℓ h : ℝ} (hℓ : 0 < ℓ) {Y : Set ℝ} (hY : volume Y = 0) {Γ : Set (Set ℂ)}
    (hΓ : ∀ x ∈ Ioo 0 ℓ, x ∉ Y → ∃ γ ∈ Γ, γ =ᵐ[μH[1]] (fun t : ℝ => (x : ℂ) + t * I) '' Ioo 0 h) {ρ : ℂ → ℝ≥0∞}
    (hρ : ρ ∈ LiZhongQC.densitiesP0 (Ioo 0 ℓ ×ℂ Ioo 0 h)) :
    pathRhoLength Γ ρ ^ 2 / LiZhongQC.rhoArea ρ (Ioo 0 ℓ ×ℂ Ioo 0 h) ≤ ENNReal.ofReal (h / ℓ) := by
  obtain ⟨hm, hA0, hAt⟩ := gm4a_mem_densitiesP0.1 hρ
  have hR : Ioo 0 ℓ ×ℂ Ioo 0 h = LiZhongQC.rectangle ℓ h := (LiZhongQC.rectangle_eq_reProdIm ℓ h).symm
  have hA : LiZhongQC.rhoArea ρ (Ioo 0 ℓ ×ℂ Ioo 0 h) =
      ∫⁻ x in Ioo 0 ℓ, ∫⁻ y in Ioo 0 h, ρ ((x : ℂ) + (y : ℂ) * I) ^ 2 := by
    rw [gm4a_rhoArea_eq, hR]
    exact LiZhongQC.setLIntegral_rectangle (hm.pow_const 2)
  have hcore := gm4d_rect_core_null (G := fun x y => ρ ((x : ℂ) + (y : ℂ) * I)) (fun x => hm.comp (by fun_prop))
    (L := pathRhoLength Γ ρ) hY fun x hx hxY => by
      obtain ⟨γ, hγΓ, hae⟩ := hΓ x hx hxY
      refine (iInf₂_le _ hγΓ).trans_eq ?_
      rw [setLIntegral_congr hae, gm4b_lintegral_line (c := (x : ℂ)) (u := I) (by simp) measurableSet_Ioo hm]
  rw [← hA] at hcore
  exact gm4b_div_le_of_mul_le hℓ hA0.ne' hAt.ne hcore

/-- **Unlabelled** (Ch. IV §1, P1:5929–5935; cited at P1:5944, 6229). Let `Ω` be a Jordan domain, let
`E = [ζ₁, ζ₂]` and `F = [ζ₃, ζ₄]` be two disjoint subarcs of `∂Ω`, where `ζ₁, ζ₂, ζ₃, ζ₄` are listed in the
counterclockwise ordering of `∂Ω`, and let `φ` be the conformal mapping from `Ω` to the rectangle
`{0 < x < ℓ, 0 < y < 1}` with `ζ₁, ζ₂, ζ₃, ζ₄ ↦ i, 0, ℓ, ℓ + i` [OCR: "i, 0, , and ℓ + i"]. By conformal
invariance `ℓ = d_Ω(E, F)`, and the extremal metrics for `d_Ω(E, F)` are the constant multiples of `|φ'|`.
Modelling: the Jordan domain with its four points is the quadrilateral `Q` of LV with the vertices relabelled
cyclically, `Q.vert = (ζ₂, ζ₃, ζ₄, ζ₁)`, so that `E = Q.side 3`, `F = Q.side 1`, and `φ` is a canonical map of `Q`
onto `R(0, ℓ, ℓ + i, i)` (`LehtoVirtanen1973.IsCanonicalMap`, which includes the homeomorphic extension to the
closure); `d_Ω` is taken on finite parts (Chapter IV is planar); `|φ'|` is `LehtoVirtanen1973.derivDensity φ` on the
finite part of `Ω`; the constants are positive (`c = 0` is not a metric). "The extremal metrics are the constant
multiples of `|φ'|`" is stated as two claims (module docstring): every `c |φ'|`, `c > 0`, is an extremal metric,
and every extremal metric equals some `c |φ'|` almost everywhere for area measure on `Ω`. -/
theorem quadrilateral_extremalDist (Q : Quadrilateral) {ℓ : ℝ} {φ : ExtPlane → ExtPlane}
    (hφ : IsCanonicalMap Q.dom Q.vert ℓ 1 φ) :
    extremalDistGM (finitePart Q.dom) (finitePart (Q.side 3)) (finitePart (Q.side 1)) = ENNReal.ofReal ℓ ∧
      (∀ c : ℝ, 0 < c → IsExtremalMetricGM (finitePart Q.dom)
          (joiningFamily (finitePart Q.dom) (finitePart (Q.side 3)) (finitePart (Q.side 1)))
          (fun z => ENNReal.ofReal c * derivDensity φ (finitePart Q.dom) z)) ∧
      ∀ ρ : ℂ → ℝ≥0∞, IsExtremalMetricGM (finitePart Q.dom)
          (joiningFamily (finitePart Q.dom) (finitePart (Q.side 3)) (finitePart (Q.side 1))) ρ →
        ∃ c : ℝ, 0 < c ∧ ρ =ᵐ[volume.restrict (finitePart Q.dom)]
          fun z => ENNReal.ofReal c * derivDensity φ (finitePart Q.dom) z := by
  have hsubc : ∀ {Ω' γ : Set ℂ}, IsPathCurve Ω' γ → γ ⊆ Ω' := fun {Ω' γ} h => by
    obtain ⟨s, hs, rfl⟩ := h
    exact iUnion_subset fun n => (hs n).2
  set Ω : Set ℂ := finitePart Q.dom with hΩ
  set ψ : ℂ → ℂ := LehtoVirtanen1973.finiteMap φ with hψ
  set Γ : Set (Set ℂ) := joiningFamily Ω (finitePart (Q.side 3)) (finitePart (Q.side 1)) with hΓ
  have hℓ : 0 < ℓ := hφ.1
  obtain ⟨-, -, -, -⟩ := gm4d_plane_conformal Q hφ hΩ hψ
  obtain ⟨hmem0, hA0, hL0⟩ := gm4d_deriv_density Q hφ hΩ hψ
  obtain ⟨N, hN, hgood⟩ := gm4d_good_heights Q hφ hΩ (E := finitePart (Q.side 3)) (F := finitePart (Q.side 1)) rfl rfl hψ
  have hmeas : ∀ γ ∈ Γ, MeasurableSet γ ∧ γ ⊆ Ω := fun γ hγ =>
    ⟨gm4b_isPathCurve_measurableSet (hγ.1),
      hsubc (hγ.1)⟩
  have hL : ENNReal.ofReal ℓ ≤ pathRhoLength Γ (derivDensity φ Ω) := by
    rw [gm4a_pathRhoLength_eq]
    refine le_iInf₂ fun γ hγ => ?_
    rw [hL0 γ (hmeas γ hγ).1 (hmeas γ hγ).2]
    exact gm4d_crossing Q hφ hΩ rfl rfl hψ hγ
  have hup : ∀ ρ ∈ LiZhongQC.densitiesP0 Ω,
      pathRhoLength Γ ρ ^ 2 / LiZhongQC.rhoArea ρ Ω ≤ ENNReal.ofReal ℓ := by
    intro ρ hρ
    obtain ⟨ρ', hρ', hA', hint⟩ := gm4d_pullback Q hφ hΩ hψ hρ
    have h1 : pathRhoLength Γ ρ ≤ pathRhoLength (image ψ '' Γ) ρ' := by
      rw [gm4a_pathRhoLength_eq, gm4a_pathRhoLength_eq, iInf_image]
      refine le_iInf₂ fun γ hγ => ?_
      rw [← hint γ (hmeas γ hγ).1 (hmeas γ hγ).2]
      exact iInf₂_le γ hγ
    have h2 := gm4d_rect_hseg_ratio_le_null (ℓ := ℓ) (h := 1) one_pos hN (Γ := image ψ '' Γ)
      (fun y hy hyN => by
        obtain ⟨γ, hγ, hψγ⟩ := hgood y hy hyN
        exact ⟨γ, hγ, hψγ⟩) hρ'
    rw [div_one] at h2
    rw [← hA']
    exact le_trans (by gcongr) h2
  have hone : (ENNReal.ofReal ℓ) ^ 2 / ENNReal.ofReal ℓ = ENNReal.ofReal ℓ := by
    have := gm4b_ofReal_sq_div hℓ one_pos
    rwa [mul_one, div_one] at this
  have hratio : pathRhoLength Γ (derivDensity φ Ω) ^ 2 / LiZhongQC.rhoArea (derivDensity φ Ω) Ω =
      ENNReal.ofReal ℓ := by
    refine le_antisymm (hup _ hmem0) ?_
    rw [hA0]
    calc ENNReal.ofReal ℓ = ENNReal.ofReal ℓ ^ 2 / ENNReal.ofReal ℓ := hone.symm
      _ ≤ _ := ENNReal.div_le_div_right (pow_le_pow_left' hL 2) _
  have hlam : extremalLengthGM Ω Γ = ENNReal.ofReal ℓ := by
    refine le_antisymm ?_ (hratio ▸ gm4a_ratio_le hmem0)
    rw [gm4a_extremalLengthGM_eq]
    exact iSup₂_le hup
  have hext : IsExtremalMetricGM Ω Γ (derivDensity φ Ω) := ⟨hmem0, hratio.trans hlam.symm⟩
  refine ⟨hlam, fun c hc => ?_, fun ρ hρ => ?_⟩
  · exact gm4b_isExtremalMetricGM_const_mul hext (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top
  · obtain ⟨c, hc0, hct, hρc⟩ := gm4b_extremal_eq_const_mul
      (by rw [hlam]; exact ENNReal.ofReal_pos.2 hℓ) (by rw [hlam]; exact ENNReal.ofReal_lt_top) hext hρ
    refine ⟨c.toReal, ENNReal.toReal_pos hc0 hct, ?_⟩
    rwa [ENNReal.ofReal_toReal hct]

/-- **Formula (1.7)** (Ch. IV §1; cited at P1:5944, 6084). For the quadrilateral of `quadrilateral_extremalDist`
(`E = [ζ₁, ζ₂]`, `F = [ζ₃, ζ₄]`), `d_Ω(E, F) d*_Ω(E, F) = ℓ · (1/ℓ) = 1`.
Modelling: as in `quadrilateral_extremalDist`; the product is taken in `[0, ∞]`, where it is a product of two finite
positive numbers. -/
theorem eq4_1_7 (Q : Quadrilateral) :
    extremalDistGM (finitePart Q.dom) (finitePart (Q.side 3)) (finitePart (Q.side 1)) *
      conjExtremalDistGM (finitePart Q.dom) (finitePart (Q.side 3)) (finitePart (Q.side 1)) = 1 := by
  have hsubc : ∀ {Ω' γ : Set ℂ}, IsPathCurve Ω' γ → γ ⊆ Ω' := fun {Ω' γ} h => by
    obtain ⟨s, hs, rfl⟩ := h
    exact iUnion_subset fun n => (hs n).2
  obtain ⟨φ, hφ⟩ := LehtoVirtanen1973.exists_canonicalMap_normalized Q
  have hℓ : 0 < Q.module := hφ.1
  set Ω : Set ℂ := finitePart Q.dom with hΩ
  set ψ : ℂ → ℂ := LehtoVirtanen1973.finiteMap φ with hψ
  set Γ : Set (Set ℂ) := separatingFamily Ω (finitePart (Q.side 3)) (finitePart (Q.side 1)) with hΓ
  have h1 := (quadrilateral_extremalDist Q hφ).1
  obtain ⟨hmem0, hA0, hL0⟩ := gm4d_deriv_density Q hφ hΩ hψ
  obtain ⟨N, hN, hgood⟩ := gm4d_good_abscissae Q hφ hΩ (E := finitePart (Q.side 3)) (F := finitePart (Q.side 1)) rfl rfl hψ
  have hmeas : ∀ γ ∈ Γ, MeasurableSet γ ∧ γ ⊆ Ω := fun γ hγ =>
    ⟨gm4b_isPathCurve_measurableSet hγ.1, hsubc hγ.1⟩
  have hL : 1 ≤ pathRhoLength Γ (derivDensity φ Ω) := by
    rw [gm4a_pathRhoLength_eq]
    refine le_iInf₂ fun γ hγ => ?_
    rw [hL0 γ (hmeas γ hγ).1 (hmeas γ hγ).2]
    exact gm4d_sep_crossing Q hφ hΩ rfl rfl hψ hγ
  have hup : ∀ ρ ∈ LiZhongQC.densitiesP0 Ω,
      pathRhoLength Γ ρ ^ 2 / LiZhongQC.rhoArea ρ Ω ≤ ENNReal.ofReal (1 / Q.module) := by
    intro ρ hρ
    obtain ⟨ρ', hρ', hA', hint⟩ := gm4d_pullback Q hφ hΩ hψ hρ
    have h1 : pathRhoLength Γ ρ ≤ pathRhoLength (image ψ '' Γ) ρ' := by
      rw [gm4a_pathRhoLength_eq, gm4a_pathRhoLength_eq, iInf_image]
      refine le_iInf₂ fun γ hγ => ?_
      rw [← hint γ (hmeas γ hγ).1 (hmeas γ hγ).2]
      exact iInf₂_le γ hγ
    have h2 := gm4d_rect_vseg_ratio_le_null (ℓ := Q.module) (h := 1) hℓ hN (Γ := image ψ '' Γ)
      (fun x hx hxN => by
        obtain ⟨γ, hγ, hψγ⟩ := hgood x hx hxN
        exact ⟨ψ '' γ, ⟨γ, hγ, rfl⟩, hψγ⟩) hρ'
    rw [← hA']
    exact le_trans (by gcongr) h2
  have h2 : conjExtremalDistGM Ω (finitePart (Q.side 3)) (finitePart (Q.side 1)) =
      ENNReal.ofReal (1 / Q.module) := by
    refine le_antisymm ?_ ?_
    · rw [conjExtremalDistGM, gm4a_extremalLengthGM_eq]
      exact iSup₂_le hup
    · refine le_trans ?_ (gm4a_ratio_le hmem0)
      rw [hA0, ENNReal.ofReal_div_of_pos hℓ, ENNReal.ofReal_one, ← one_pow 2]
      exact ENNReal.div_le_div_right (pow_le_pow_left' hL 2) _
  rw [h1, h2, ← ENNReal.ofReal_mul hℓ.le, mul_one_div_cancel hℓ.ne', ENNReal.ofReal_one]

/-- **Example 1.2** (the annulus; Ch. IV §1; cited at P1:6231, in Chapter V, P1:6961 "by the serial rule and
Example IV.1.2", P1:7733 "the annulus example", and in App. H, P3:4915). The extremal distance between the two
boundary circles `C_r` and `C_R` of the annulus `A = {z : r < |z| < R}` is `d_A(C_r, C_R) = (1/2π) log(R/r)`.
Modelling: `0 < r < R < ∞` ("Since (1.3) is a supremum, we can assume `0 < r < R < ∞`", P1:5952: the degenerate
annuli, where the value is `∞`, are reduced to this case and are not stated); `C_r` is the circle `|z| = r`. -/
theorem example4_1_2_a {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    extremalDistGM (annulus r R) (sphere 0 r) (sphere 0 R) = ENNReal.ofReal (1 / (2 * π) * Real.log (R / r)) := by
  exact gm4b_annulus_value hr hrR

/-- **Example 1.2** (the annulus; Ch. IV §1), the extremal metrics. Equality holds in (1.8) and (1.9) for
`ρ = c/|z|`, where `c` is a positive constant, and every extremal metric equals some `c/|z|` almost everywhere: the
extremal metrics for `d_A(C_r, C_R)` have the form `c/|z|`.
Modelling: as in `example4_1_2_a`; "almost everywhere" is with respect to area measure on `A`. The book's "equality
holds in (1.8) if and only if `ρ(z) = c/|z|` a.e., …, and for such `ρ` we also get equality in (1.9)" is stated as
the two claims of the module docstring: every `c/|z|`, `c > 0`, is an extremal metric, and every extremal metric
equals some `c/|z|` a.e.; a metric equal to `c/|z|` a.e. that vanishes on a radial segment is not extremal. -/
theorem example4_1_2_b {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    (∀ c : ℝ, 0 < c → IsExtremalMetricGM (annulus r R) (joiningFamily (annulus r R) (sphere 0 r) (sphere 0 R))
        fun z => ENNReal.ofReal (c / ‖z‖)) ∧
      ∀ ρ : ℂ → ℝ≥0∞, IsExtremalMetricGM (annulus r R) (joiningFamily (annulus r R) (sphere 0 r) (sphere 0 R)) ρ →
        ∃ c : ℝ, 0 < c ∧ ρ =ᵐ[volume.restrict (annulus r R)] fun z => ENNReal.ofReal (c / ‖z‖) := by
  have hval := gm4b_annulus_value hr hrR
  have hpos : 0 < (1 : ℝ) / (2 * π) * Real.log (R / r) :=
    mul_pos (by positivity) (Real.log_pos ((one_lt_div hr).2 hrR))
  refine ⟨fun c hc => gm4b_annulus_isExtremal hr hrR hc, fun ρ hρ => ?_⟩
  obtain ⟨k, hk0, hk, hkρ⟩ := gm4b_extremal_eq_const_mul
    (by rw [show extremalLengthGM _ _ = extremalDistGM (annulus r R) (sphere 0 r) (sphere 0 R) from rfl, hval];
        exact ENNReal.ofReal_pos.2 hpos)
    (by rw [show extremalLengthGM _ _ = extremalDistGM (annulus r R) (sphere 0 r) (sphere 0 R) from rfl, hval];
        exact ENNReal.ofReal_lt_top)
    (gm4b_annulus_isExtremal hr hrR one_pos) hρ
  refine ⟨k.toReal, ENNReal.toReal_pos hk0 hk, ?_⟩
  filter_upwards [hkρ] with z hz
  rw [hz, gm4b_mul_ofReal_inv_norm hk]

/-- **Example 1.2** (the annulus; Ch. IV §1), the conjugate extremal distance. `d*_A(C_r, C_R)` is the extremal
length of the family of closed curves in `A` separating the two boundary circles, and
`d*_A(C_r, C_R) = 2π/log(R/r) = 1/d_A(C_r, C_R)`.
Modelling: as in `example4_1_2_a`; `d*_A` is defined with `separatingFamily` (finite unions of arcs and closed curves,
module docstring); the family of closed curves in `A` separating the circles is the set of the images `g([0, 1])` of
closed paths `g` (`g(0) = g(1)`) that are curves of a path family in `A` and separate `C_r` from `C_R`
(`IsSeparatingIn`), and the first conjunct says that its extremal length is `d*_A(C_r, C_R)`. -/
theorem example4_1_2_c {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    extremalLengthGM (annulus r R) {γ | IsPathCurve (annulus r R) γ ∧
        (∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ g 0 = g 1 ∧ γ = g '' Icc 0 1) ∧
        IsSeparatingIn (annulus r R) γ (sphere 0 r) (sphere 0 R)} =
        conjExtremalDistGM (annulus r R) (sphere 0 r) (sphere 0 R) ∧
      conjExtremalDistGM (annulus r R) (sphere 0 r) (sphere 0 R) = ENNReal.ofReal (2 * π / Real.log (R / r)) ∧
      conjExtremalDistGM (annulus r R) (sphere 0 r) (sphere 0 R) =
        (extremalDistGM (annulus r R) (sphere 0 r) (sphere 0 R))⁻¹ := by
  obtain ⟨hsep, hclosed⟩ := gm4b_annulus_sep_value hr hrR
  exact ⟨hclosed.trans hsep.symm, hsep, by rw [hsep, gm4b_annulus_value hr hrR, gm4b_annulus_inv hr hrR]⟩

/-- The family of curves in the ring domain `B` separating the two components of `∂B` (helper, Ch. IV §1,
P1:5978): the curves in the finite part of `B` separating the finite parts of the boundary components through `x`
and `y`. -/
def ringSepFamily (B : Set ExtPlane) (x y : ExtPlane) : Set (Set ℂ) :=
  separatingFamily (finitePart B) (finitePart (connectedComponentIn (frontier B) x))
    (finitePart (connectedComponentIn (frontier B) y))

/-- **Definition** (module of a ring domain, Ch. IV §1, P1:5978–5981). For a ring domain `Ω` (a doubly connected
plane domain) and the family `Γ` of curves in `Ω` separating the two components of `∂Ω`, the quantity
`λ_Ω(Γ)⁻¹` is the module of the ring domain, `mod(Ω)`.
Modelling: `Ω ⊆ ℂ*` with boundary in `ℂ*`; `Γ = ringSepFamily Ω x y` for points `x`, `y` of the two boundary
components, on finite parts (Chapter IV is planar). The separating family is symmetric in the two components, so the
supremum over the labellings is over a one-point set for a ring domain. Junk: `0` when `∂Ω` has only one component,
and a supremum over pairs of components when it has three or more (not a ring domain). For a degenerate ring domain
(a boundary component is a point) the value is `∞`, as intended; for the point `∞` the finite part of that component
is empty, so `IsSeparatingIn … ∅` holds for every curve, the family contains arbitrarily short arcs, `λ = 0` and the
value is `∞`. The book's normalization is kept: LV's `LehtoVirtanen1973.ringModule` and the project's
`LiZhongQC.dcModulus` are `log(R/r)`, and stated constants depend on the factor `1/2π` (leader ruling B10). -/
def ringModGM (B : Set ExtPlane) : ℝ≥0∞ :=
  ⨆ (x : ExtPlane) (_ : x ∈ frontier B) (y : ExtPlane) (_ : y ∈ frontier B)
    (_ : connectedComponentIn (frontier B) x ≠ connectedComponentIn (frontier B) y),
    (extremalLengthGM (finitePart B) (ringSepFamily B x y))⁻¹

/-- **Unlabelled** (Ch. IV §1, P1:5978–5981; cited for `mod` in Chapter V, P1:7179, 7201, 7367, 7392, and in
Chapter VII, P2:2426–2429). If `ψ : Ω → A = {r < |z| < R}` is a conformal map of the ring domain `Ω` onto an
annulus, then the module of the family `Γ` of curves in `Ω` separating the two components of `∂Ω` is
`λ_Ω(Γ)⁻¹ = mod(Ω) = (1/2π) log(R/r)`, and an extremal metric is `|ψ'(z)|/|ψ(z)|`.
Modelling: `0 < r < R < ∞` (the non-degenerate annuli, as in Example 1.2); `ψ` is a conformal map of `Ω ⊆ ℂ*` in
the sense of LV (`LehtoVirtanen1973.IsConformalMap`); `|ψ'|/|ψ|` is `LehtoVirtanen1973.logDerivDensity ψ` on the
finite part of `Ω`; the extremal-metric claim is stated for both labellings of the boundary components. -/
theorem ringModGM_annulus {B : Set ExtPlane} (hB : IsRingDomain B) {ψ : ExtPlane → ExtPlane} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hψ : IsConformalMap ψ B) (hψB : ψ '' B = toExt (annulus r R)) :
    ringModGM B = ENNReal.ofReal (1 / (2 * π) * Real.log (R / r)) ∧
      ∀ x ∈ frontier B, ∀ y ∈ frontier B,
        connectedComponentIn (frontier B) x ≠ connectedComponentIn (frontier B) y →
          (extremalLengthGM (finitePart B) (ringSepFamily B x y))⁻¹ = ringModGM B ∧
          IsExtremalMetricGM (finitePart B) (ringSepFamily B x y) (logDerivDensity ψ (finitePart B)) := by
  sorry

end GarnettMarshall2005
