import References.GardinerLakic2000.Ch18.S01_FiniteEarthquakes

/-!
# Gardiner–Lakic 2000, Ch. 18 §18.2 General earthquakes

Source `teichmuller.txt`, lines 13320–13364 (Chapter 18, §18.2).

* Definition (the hyperbolic line of `𝔻` with endpoints `a, b ∈ S¹`) — `hypLine`
* Definition 1 (geodesic lamination; gaps; strata, l. 13324) — `IsGeodesicLamination`, `laminationSet`,
  `laminationStrata`
* Definition (weakly separates, l. 13332) — `WeaklySeparates`
* Definition 2 (`𝓛`-left earthquake and its comparison maps, l. 13330) — `IsDiscMobiusFn`, `IsLeftEarthquake`,
  `IsRightEarthquake`
* Theorem 2 (general earthquake theorem, Thurston, l. 13334; the parallel right statement, l. 13337) —
  `thm18_2_left`, `thm18_2_right`
* Definition (the ideal triangle with vertices on `S¹`; limiting maps of finite earthquakes, `𝒜`, l. 13340–13345) —
  `idealTriangle`, `IsLimitingMap`
* Lemma 6 (l. 13347) — `lemma18_6`
* Lemma 7 (l. 13350) — `lemma18_7`
* Lemma 8 (l. 13354) — `lemma18_8`

Not items: `bd(T)` and the reconstruction of a stratum from it (l. 13328, U−); the proof of Theorem 2. Modelling
(E0.7): the hyperbolic plane is the disc `𝔻` (the book's own model in the definitions; its proof works in `ℍ`;
near miss batch A's `IsHypLine`, a line of `ℍ` without named endpoints); a
geodesic lamination is given by the set `Λ` of endpoint pairs of its lines (`Sym2 ℂ`), its point set being the union
of the lines. A Möbius map of `𝔻` is a map `ℂ → ℂ` agreeing on `𝔻̄` with an element of
`Pommerenke1992.mobDisc`; "hyperbolic with axis weakly separating `T₁` from `T₂`" is stated through its two fixed
points on `S¹`. Definition 2 as printed does
not say in which direction the comparison maps translate; "left" is read as in §18.1 [reading]: `E` moves every
boundary point of `T₂` to the left relative to three boundary points of `T₁` (`leftOf ≥ 0`). A leaf where `E` is
discontinuous is a line of `Λ` containing a point where `E` is not continuous. Lemmas 6–8 are stated for a fixed
ascending sequence `Sₙ` of finite subsets of `S¹` with dense union, through `IsLimitingMap` [reading, E0.7]: `M` is a
limit of the Möbius maps `Eₙ = h_n` on triangles `Tₙ` of finite left earthquakes realizing `h` on `Sₙ`, whose vertices
converge to `a, b, c` (a triangle if distinct, a line if `b = c`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold Classical

noncomputable section

namespace GardinerLakic2000

/-- **Definition** (the hyperbolic line of `𝔻` joining `a, b ∈ S¹`). A diameter if `b = −a`, otherwise the arc in `𝔻`
of the circle orthogonal to `S¹` through `a, b` (centre `(a + b)/(1 + Re(b ā))`). -/
def hypLine (a b : ℂ) : Set ℂ :=
  if b = -a then {z | z ∈ ball (0 : ℂ) 1 ∧ ∃ t : ℝ, z = t * a}
  else {z | z ∈ ball (0 : ℂ) 1 ∧ ‖z - (a + b) / (1 + (b * conj a).re)‖ ^ 2 =
    ‖(a + b) / (1 + (b * conj a).re)‖ ^ 2 - 1}

/-- Helper (§18.2). The point set `⋃_{ab ∈ Λ} L_ab` of the lamination. -/
def laminationSet (Λ : Set (Sym2 ℂ)) : Set ℂ := ⋃ (a : ℂ) (b : ℂ) (_ : s(a, b) ∈ Λ), hypLine a b

/-- **Definition 1** (geodesic lamination, §18.2, l. 13324). A closed subset of the hyperbolic plane that is a disjoint
union of non-intersecting hyperbolic lines. -/
def IsGeodesicLamination (Λ : Set (Sym2 ℂ)) : Prop :=
  (∀ a b : ℂ, s(a, b) ∈ Λ → a ∈ sphere (0 : ℂ) 1 ∧ b ∈ sphere (0 : ℂ) 1 ∧ a ≠ b) ∧
    (∀ a b c d : ℂ, s(a, b) ∈ Λ → s(c, d) ∈ Λ → ¬ AreLinked a b c d) ∧
    closure (laminationSet Λ) ∩ ball 0 1 ⊆ laminationSet Λ

/-- **Definition 1** (gaps and strata, §18.2, l. 13324). The strata of `Λ`: its lines and its gaps (the components
of the complement in `𝔻`). -/
def laminationStrata (Λ : Set (Sym2 ℂ)) : Set (Set ℂ) :=
  {T | (∃ a b : ℂ, s(a, b) ∈ Λ ∧ T = hypLine a b) ∨
    ∃ z ∈ ball (0 : ℂ) 1 \ laminationSet Λ, T = connectedComponentIn (ball (0 : ℂ) 1 \ laminationSet Λ) z}

/-- **Definition** (§18.2, l. 13332). The hyperbolic line `L` weakly separates `T₁` from `T₂`: every path in `𝔻`
from a point of `T₁` to a point of `T₂` meets `L`. -/
def WeaklySeparates (L T₁ T₂ : Set ℂ) : Prop :=
  ∀ z₁ ∈ T₁, ∀ z₂ ∈ T₂, ∀ γ : Path z₁ z₂, (∀ t, γ t ∈ ball (0 : ℂ) 1) → ∃ t, γ t ∈ L

/-- Helper (§18.2). `M` agrees on the closed disc with a Möbius map of `𝔻` (an element of
`Pommerenke1992.mobDisc`). -/
def IsDiscMobiusFn (M : ℂ → ℂ) : Prop :=
  ∃ τ ∈ Pommerenke1992.mobDisc, ∀ z ∈ closedBall (0 : ℂ) 1, τ z = ((M z : ℂ) : LiZhongQC.ExtPlane)

/-- **Definition 2** (`𝓛`-left earthquake, §18.2, l. 13330). A bijection `E` of the closed disc, equal on each stratum
`T` to a Möbius map `M_T` of `𝔻`, whose comparison maps `M_{T₁}⁻¹ ∘ M_{T₂}` are hyperbolic with axis weakly separating
`T₁` from `T₂` (or the identity when `T₁` is a line on the boundary of `T₂`), translating to the left.
[CORRECTION] (AUDIT5_GL1518 G15-5, G15-8) `E = M_T` also at the ideal points `closure T ∩ S¹` of each stratum, so that
the values of `E` on `S¹` are the boundary values of the strata maps (the book's `E` on `S¹`). With `E = M_T` on `T` only,
the values on `S¹` were free: `Λ = ∅`, `E = id` on `𝔻`, `E = h` on `S¹` was a left earthquake for every `h`, and for
`h = id` both `E = id` and `E = −z` on `𝔻` (`id` on `S¹`) were left earthquakes extending `h`, so `thm18_2_left` was
false. At the common ideal points of two strata the comparison map fixes the point (an endpoint of its axis).
[CORRECTION] (AUDITR2_GL1518 G1) As in the book, the comparison map may be the identity only for a line on the
frontier of the other stratum; otherwise it is a genuine hyperbolic map. Before, a leaf with zero shear could be
added to any lamination (`h = id`: `Λ = ∅` and `Λ = {s(1, −1)}`), and the uniqueness `Λ = Λ'` failed. -/
def IsLeftEarthquake (Λ : Set (Sym2 ℂ)) (E : ℂ → ℂ) : Prop :=
  BijOn E (closedBall 0 1) (closedBall 0 1) ∧
  ∃ M : Set ℂ → ℂ → ℂ,
    (∀ T ∈ laminationStrata Λ, IsDiscMobiusFn (M T) ∧ EqOn E (M T) (T ∪ closure T ∩ sphere 0 1)) ∧
    (∀ T₁ ∈ laminationStrata Λ, ∀ T₂ ∈ laminationStrata Λ, T₁ ≠ T₂ →
      ((∃ a b : ℂ, s(a, b) ∈ Λ ∧ ((T₁ = hypLine a b ∧ T₁ ⊆ frontier T₂) ∨ (T₂ = hypLine a b ∧ T₂ ⊆ frontier T₁))) ∧
        ∀ z, M T₁ z = M T₂ z) ∨ (∃ z, M T₁ z ≠ M T₂ z) ∧ ∃ x y : ℂ, x ∈ sphere (0 : ℂ) 1 ∧ y ∈ sphere (0 : ℂ) 1 ∧ x ≠ y ∧
        M T₂ x = M T₁ x ∧ M T₂ y = M T₁ y ∧ WeaklySeparates (hypLine x y) T₁ T₂) ∧
    ∀ T₁ ∈ laminationStrata Λ, ∀ T₂ ∈ laminationStrata Λ, ∀ a ∈ closure T₁ ∩ sphere 0 1,
      ∀ b ∈ closure T₁ ∩ sphere 0 1, ∀ c ∈ closure T₁ ∩ sphere 0 1, IsCCW3 a b c →
        ∀ x ∈ closure T₂ ∩ sphere 0 1, x ∉ closure T₁ → 0 ≤ leftOf E a b c x

/-- **Definition 2**, the right earthquake (§18.2, l. 13337). As `IsLeftEarthquake`, translating to the right
([CORRECTION] AUDIT5_GL1518 G15-5: `E = M_T` on `T ∪ (closure T ∩ S¹)`, as for the left earthquake). -/
def IsRightEarthquake (Λ : Set (Sym2 ℂ)) (E : ℂ → ℂ) : Prop :=
  BijOn E (closedBall 0 1) (closedBall 0 1) ∧
  ∃ M : Set ℂ → ℂ → ℂ,
    (∀ T ∈ laminationStrata Λ, IsDiscMobiusFn (M T) ∧ EqOn E (M T) (T ∪ closure T ∩ sphere 0 1)) ∧
    (∀ T₁ ∈ laminationStrata Λ, ∀ T₂ ∈ laminationStrata Λ, T₁ ≠ T₂ →
      ((∃ a b : ℂ, s(a, b) ∈ Λ ∧ ((T₁ = hypLine a b ∧ T₁ ⊆ frontier T₂) ∨ (T₂ = hypLine a b ∧ T₂ ⊆ frontier T₁))) ∧
        ∀ z, M T₁ z = M T₂ z) ∨ (∃ z, M T₁ z ≠ M T₂ z) ∧ ∃ x y : ℂ, x ∈ sphere (0 : ℂ) 1 ∧ y ∈ sphere (0 : ℂ) 1 ∧ x ≠ y ∧
        M T₂ x = M T₁ x ∧ M T₂ y = M T₁ y ∧ WeaklySeparates (hypLine x y) T₁ T₂) ∧
    ∀ T₁ ∈ laminationStrata Λ, ∀ T₂ ∈ laminationStrata Λ, ∀ a ∈ closure T₁ ∩ sphere 0 1,
      ∀ b ∈ closure T₁ ∩ sphere 0 1, ∀ c ∈ closure T₁ ∩ sphere 0 1, IsCCW3 a b c →
        ∀ x ∈ closure T₂ ∩ sphere 0 1, x ∉ closure T₁ → leftOf E a b c x ≤ 0

/-- **Theorem 2** (general earthquake theorem, Thurston, §18.2, l. 13334). Every orientation-preserving homeomorphism
`h` of `S¹` is the restriction of a left earthquake `E` for a lamination `Λ`; `h` determines `Λ`, and `E` on every
stratum except the leaves where `E` is discontinuous; on such a leaf all choices have the same image leaf. -/
theorem thm18_2_left {h : ℂ → ℂ} (hh : Pommerenke1992.IsSensePreservingCircleHomeo h) :
    (∃ (Λ : Set (Sym2 ℂ)) (E : ℂ → ℂ), IsGeodesicLamination Λ ∧ IsLeftEarthquake Λ E ∧
      ∀ z ∈ sphere (0 : ℂ) 1, E z = h z) ∧
    ∀ (Λ Λ' : Set (Sym2 ℂ)) (E E' : ℂ → ℂ), IsGeodesicLamination Λ → IsLeftEarthquake Λ E →
      (∀ z ∈ sphere (0 : ℂ) 1, E z = h z) → IsGeodesicLamination Λ' → IsLeftEarthquake Λ' E' →
      (∀ z ∈ sphere (0 : ℂ) 1, E' z = h z) →
        Λ = Λ' ∧ ∀ T ∈ laminationStrata Λ, ((∀ z ∈ T, ContinuousAt E z) → EqOn E E' T) ∧ E '' T = E' '' T := by
  sorry

/-- **Theorem 2** (§18.2, l. 13337), the parallel statement for right earthquakes. -/
theorem thm18_2_right {h : ℂ → ℂ} (hh : Pommerenke1992.IsSensePreservingCircleHomeo h) :
    (∃ (Λ : Set (Sym2 ℂ)) (E : ℂ → ℂ), IsGeodesicLamination Λ ∧ IsRightEarthquake Λ E ∧
      ∀ z ∈ sphere (0 : ℂ) 1, E z = h z) ∧
    ∀ (Λ Λ' : Set (Sym2 ℂ)) (E E' : ℂ → ℂ), IsGeodesicLamination Λ → IsRightEarthquake Λ E →
      (∀ z ∈ sphere (0 : ℂ) 1, E z = h z) → IsGeodesicLamination Λ' → IsRightEarthquake Λ' E' →
      (∀ z ∈ sphere (0 : ℂ) 1, E' z = h z) →
        Λ = Λ' ∧ ∀ T ∈ laminationStrata Λ, ((∀ z ∈ T, ContinuousAt E z) → EqOn E E' T) ∧ E '' T = E' '' T := by
  sorry

/-- Helper (§18.2, l. 13340–13345). The closed ideal triangle of `𝔻` with vertices `a, b, c ∈ S¹` (for `b = c`, the
line `ab`): the points of `𝔻` not strictly beyond a side. -/
def idealTriangle (a b c : ℂ) : Set ℂ :=
  if b = c then hypLine a b
  else {z ∈ ball (0 : ℂ) 1 | ∀ x y w : ℂ, (x, y, w) ∈ ({(a, b, c), (b, c, a), (c, a, b)} : Set (ℂ × ℂ × ℂ)) →
    z ∈ hypLine x y ∨ connectedComponentIn (closedBall 0 1 \ closure (hypLine x y)) z =
      connectedComponentIn (closedBall 0 1 \ closure (hypLine x y)) w}

/-- **Definition** (limiting map, §18.2, l. 13340–13345). Along the ascending sequence `Sₙ`, `M : T → M(T)` is a limit
of the Möbius maps `Eₙ` (`Eₙ = h` at the vertices of a triangle `aₙbₙcₙ` of a finite left earthquake realizing `h` on
`Sₙ`, `Eₙ⁻¹ ∘ h` moving the other points of `Sₙ` to the left), whose vertices converge to `a, b, c`. -/
def IsLimitingMap (h : ℂ → ℂ) (S : ℕ → Finset ℂ) (M : ℂ → ℂ) (a b c : ℂ) : Prop :=
  IsDiscMobiusFn M ∧ ∃ (φ : ℕ → ℕ) (E : ℕ → ℂ → ℂ) (av bv cv : ℕ → ℂ), StrictMono φ ∧
    (∀ n, IsDiscMobiusFn (E n) ∧ IsCCW3 (av n) (bv n) (cv n) ∧
      (∃ (L : Finset (Sym2 ℂ)) (σ : Sym2 ℂ → ℝ), IsFiniteLeftEarthquake (S (φ n)) L σ h ∧
        IsLaminationTriangle (S (φ n)) L (av n) (bv n) (cv n)) ∧
      E n (av n) = h (av n) ∧ E n (bv n) = h (bv n) ∧ E n (cv n) = h (cv n) ∧
      ∀ x ∈ S (φ n), x ∉ ({av n, bv n, cv n} : Set ℂ) → 0 ≤ leftOf h (av n) (bv n) (cv n) x) ∧
    Tendsto av atTop (𝓝 a) ∧ Tendsto bv atTop (𝓝 b) ∧ Tendsto cv atTop (𝓝 c) ∧ a ≠ b ∧ a ≠ c ∧
    ∀ z ∈ closedBall (0 : ℂ) 1, Tendsto (fun n => E n z) atTop (𝓝 (M z))

/-- **Lemma 6** (§18.2, l. 13347). `𝔻 ⊆ ⋃_{M ∈ 𝒜} T_M`. -/
theorem lemma18_6 {h : ℂ → ℂ} (hh : Pommerenke1992.IsSensePreservingCircleHomeo h) {S : ℕ → Finset ℂ}
    (hS : Monotone S) (hSc : ∀ n, (↑(S n) : Set ℂ) ⊆ sphere 0 1) (hdense : closure (⋃ n, (↑(S n) : Set ℂ)) =
      sphere 0 1) :
    ∀ z ∈ ball (0 : ℂ) 1, ∃ (M : ℂ → ℂ) (a b c : ℂ), IsLimitingMap h S M a b c ∧ z ∈ idealTriangle a b c := by
  sorry

/-- **Lemma 7** (§18.2, l. 13350). For every limiting map `M`, `M⁻¹ ∘ h` fixes the endpoints of `T_M` and moves
every other point to the left. -/
theorem lemma18_7 {h : ℂ → ℂ} (hh : Pommerenke1992.IsSensePreservingCircleHomeo h) {S : ℕ → Finset ℂ}
    (hS : Monotone S) (hSc : ∀ n, (↑(S n) : Set ℂ) ⊆ sphere 0 1) (hdense : closure (⋃ n, (↑(S n) : Set ℂ)) =
      sphere 0 1) {M : ℂ → ℂ} {a b c : ℂ} (hM : IsLimitingMap h S M a b c) :
    M a = h a ∧ M b = h b ∧ M c = h c ∧
      (b ≠ c → ∀ x ∈ sphere (0 : ℂ) 1, x ∉ ({a, b, c} : Set ℂ) → 0 ≤ leftOf h a b c x) := by
  sorry

/-- **Lemma 8** (§18.2, l. 13354). Let `l₁ ⊆ T_{M₁}`, `l₂ ⊆ T_{M₂}` be distinct geodesic lines for limiting maps
`M₁ ≠ M₂`. Then `l₁ ∩ l₂ = ∅`, and `M₂⁻¹ ∘ M₁` is hyperbolic with axis separating `l₁` and `l₂`. -/
theorem lemma18_8 {h : ℂ → ℂ} (hh : Pommerenke1992.IsSensePreservingCircleHomeo h) {S : ℕ → Finset ℂ}
    (hS : Monotone S) (hSc : ∀ n, (↑(S n) : Set ℂ) ⊆ sphere 0 1) (hdense : closure (⋃ n, (↑(S n) : Set ℂ)) =
      sphere 0 1) {M₁ M₂ : ℂ → ℂ} {a₁ b₁ c₁ a₂ b₂ c₂ : ℂ} (hM₁ : IsLimitingMap h S M₁ a₁ b₁ c₁)
    (hM₂ : IsLimitingMap h S M₂ a₂ b₂ c₂) (hne : ∃ z, M₁ z ≠ M₂ z) {p₁ q₁ p₂ q₂ : ℂ}
    (hl₁ : hypLine p₁ q₁ ⊆ idealTriangle a₁ b₁ c₁) (hl₂ : hypLine p₂ q₂ ⊆ idealTriangle a₂ b₂ c₂)
    (hl : s(p₁, q₁) ≠ s(p₂, q₂)) :
    Disjoint (hypLine p₁ q₁) (hypLine p₂ q₂) ∧ ∃ x y : ℂ, x ∈ sphere (0 : ℂ) 1 ∧ y ∈ sphere (0 : ℂ) 1 ∧ x ≠ y ∧
      M₁ x = M₂ x ∧ M₁ y = M₂ y ∧ WeaklySeparates (hypLine x y) (hypLine p₁ q₁) (hypLine p₂ q₂) := by
  sorry

end GardinerLakic2000
