import References.LehtoVirtanen1973.Ch01.S05_TwoBasicProperties

/-!
# Lehto–Virtanen, Chapter I §6: Module of a ring domain

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. I §6
(pp. 30–38; `full.md` P1:773–1031).

Ring domains are doubly connected domains of `ℂ̄`; the module takes values in `(0, ∞]`. As in §4, the curve and density
classes of §6.2 are given the precision announced for III.4 (footnote 7): locally rectifiable curves in the finite part
of `B` and Borel densities with `0 < m_ρ < ∞` (footnotes 7, 8). The family `𝒞` uses closed rectifiable curves instead of
Jordan curves, which changes no infimum (the trace of a closed curve separating the two components of the complement
contains a separating Jordan curve of no greater `ρ`-length); the family `𝒞*` uses all locally rectifiable curves with a
limit point on each component of the complement, for which (6.2) is stated.

* Definition (ring domain, §6.1) — `IsRingDomain`
* Mapping theorem for ring domains (§6.1, quoted) — `ring_mapping_theorem`
* Definition (annulus with centre 0 (footnote 10); canonical mapping and canonical image; module `M(B)`, §6.1) —
  `annulusExt`, `IsCanonicalRingMap`, `ringModule`
* Unlabelled (§6.1, P1:785): the module is a conformal invariant and, when finite, determines the conformal
  equivalence class — `ringModule_conformal_invariant`, `ringModule_eq_iff_conformallyEquivalent`
* Unlabelled (§6.1, P1:779, 785): the ratio `r₂/r₁` is the same for all canonical images; `M(B) = ∞` iff a boundary
  component is a point — `ringModule_canonical_eq`, `ringModule_eq_top_iff`
* Definition (the families `𝒞` of separating curves and `𝒞*` of joining arcs, §6.2) — `ringSepCurves`,
  `ringJoinArcs`, `logDerivDensity`
* Theorem 6.1 (§6.2) — `thm1_6_1`
* Formula (6.2) (§6.2) — `eq1_6_2`
* Formula (6.3) and its equality case (§6.3) — `eq1_6_3`, `eq1_6_3_eq_iff`
* Formula (6.5) (§6.4) — `eq1_6_5`, `sphericalDensity`
* Lemma 6.1 (§6.4) — `lemma1_6_1`
* Definition (spherical diameter, §6.5) — `sphericalDiam`
* Lemma 6.2 (§6.5) — `lemma1_6_2`
* Lemma 6.3 (§6.6; with one `Bₙ` the monotonicity remark, P1:953, cited P1:963, 1050, 1521) — `lemma1_6_3_i`,
  `lemma1_6_3_ii`
* Definition (convergence of ring domains from inside, §6.7) — `RingConvergesFromInside`
* Lemma 6.4 (§6.7) — `lemma1_6_4`
* Definition (analytic ring domain, §6.7) — `IsAnalyticRing`
* Unlabelled (§6.7, P1:965): approximation of a ring domain from inside by analytic ring domains —
  `exists_analyticRing_fromInside`
* Lemma 6.5 (§6.8) — `lemma1_6_5_i`, `lemma1_6_5_ii`

The unlabelled remark on the two conformal classes of rings of infinite module (P1:787) is not stated.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius LRCurve)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-! ## §6.1 Definition of the module of a ring domain -/

/-- **Definition** (ring domain, Ch. I §6.1): a doubly connected domain of `ℂ̄`. -/
def IsRingDomain (B : Set ExtPlane) : Prop := IsNTuplyConnected B 2

/-- **Definition** (annulus with centre 0, footnote 10): `{z : r₁ < |z| < r₂}` with `0 ≤ r₁ < r₂ ≤ ∞`, bounded by
two concentric circles which may degenerate into points (`r₁ = 0`: the point `0`; `r₂ = ∞`: the point `∞`, not in
the annulus). -/
def annulusExt (r₁ : ℝ) (r₂ : ℝ≥0∞) : Set ExtPlane := toExt {z : ℂ | r₁ < ‖z‖ ∧ ENNReal.ofReal ‖z‖ < r₂}

/-- **Definition** (canonical mapping, Ch. I §6.1): a conformal mapping of `B` onto an annulus
`{0 ≤ r₁ < |z| < r₂ ≤ ∞}`, the canonical image of `B`. -/
def IsCanonicalRingMap (B : Set ExtPlane) (f : ExtPlane → ExtPlane) (r₁ : ℝ) (r₂ : ℝ≥0∞) : Prop :=
  0 ≤ r₁ ∧ ENNReal.ofReal r₁ < r₂ ∧ IsConformalMap f B ∧ f '' B = annulusExt r₁ r₂

open scoped Classical in
/-- **Definition** (module of a ring domain, Ch. I §6.1). `M(B) = log (r₂/r₁)` for a canonical image with `r₁ > 0`,
`r₂ < ∞` (the ratio is the same for all canonical images, `ringModule_canonical_eq`); `M(B) = ∞` if `r₁ = 0` or
`r₂ = ∞` for a canonical image. Junk: `0` when `B` has no canonical mapping (not a ring domain). -/
def ringModule (B : Set ExtPlane) : ℝ≥0∞ :=
  if ∃ (f : ExtPlane → ExtPlane) (r₁ : ℝ) (r₂ : ℝ≥0∞), IsCanonicalRingMap B f r₁ r₂ ∧ (r₁ = 0 ∨ r₂ = ⊤) then ⊤
  else ⨆ (f : ExtPlane → ExtPlane) (r₁ : ℝ) (r₂ : ℝ≥0∞) (_ : IsCanonicalRingMap B f r₁ r₂),
    ENNReal.ofReal (Real.log (r₂.toReal / r₁))

/-- **Mapping theorem for ring domains** (Ch. I §6.1, quoted). Every ring domain can be mapped conformally onto an
annulus `{0 ≤ r₁ < |z| < r₂ ≤ ∞}`. -/
theorem ring_mapping_theorem {B : Set ExtPlane} (hB : IsRingDomain B) :
    ∃ (f : ExtPlane → ExtPlane) (r₁ : ℝ) (r₂ : ℝ≥0∞), IsCanonicalRingMap B f r₁ r₂ := by
  sorry

/-- **Unlabelled** (Ch. I §6.1, P1:779). If `r₁ > 0` and `r₂ < ∞` for one canonical image of `B`, then the same holds
for every canonical image and the ratio `r₂/r₁` is the same for all of them. -/
theorem ringModule_canonical_eq {B : Set ExtPlane} (hB : IsRingDomain B) {f f' : ExtPlane → ExtPlane}
    {r₁ r₁' : ℝ} {r₂ r₂' : ℝ≥0∞} (h : IsCanonicalRingMap B f r₁ r₂) (h' : IsCanonicalRingMap B f' r₁' r₂')
    (h0 : 0 < r₁) (htop : r₂ < ⊤) : 0 < r₁' ∧ r₂' < ⊤ ∧ r₂'.toReal / r₁' = r₂.toReal / r₁ := by
  sorry

/-- **Unlabelled** (Ch. I §6.1, P1:785). `M(B) = ∞` if and only if at least one boundary component of `B` consists of
a single point. -/
theorem ringModule_eq_top_iff {B : Set ExtPlane} (hB : IsRingDomain B) :
    ringModule B = ⊤ ↔ ∃ x ∈ frontier B, connectedComponentIn (frontier B) x = {x} := by
  sorry

/-- **Unlabelled** (Ch. I §6.1, P1:785; cited P1:1072, 1523). The module of a ring domain is a conformal invariant. -/
theorem ringModule_conformal_invariant {B : Set ExtPlane} (hB : IsRingDomain B) {w : ExtPlane → ExtPlane}
    (hw : IsConformalMap w B) : ringModule (w '' B) = ringModule B := by
  sorry

/-- **Unlabelled** (Ch. I §6.1, P1:785). A finite module determines the conformal equivalence class of a ring
domain: two ring domains, one of finite module, are conformally equivalent iff their modules agree. -/
theorem ringModule_eq_iff_conformallyEquivalent {B B' : Set ExtPlane} (hB : IsRingDomain B)
    (hB' : IsRingDomain B') (hfin : ringModule B < ⊤) :
    ringModule B = ringModule B' ↔ ∃ w : ExtPlane → ExtPlane, IsConformalMap w B ∧ w '' B = B' := by
  sorry

/-! ## §6.2 Direct characterization of the module -/

/-- **Definition** (the family `𝒞`, Ch. I §6.2): closed rectifiable curves in the finite part of `B` which separate
the two components `(-B)₁`, `(-B)₂` of the complement of `B`. -/
def ringSepCurves (B : Set ExtPlane) : Set LRCurve :=
  {γ | γ.IsClosedCurve ∧ toExt γ.closedTrace ⊆ B ∧ ∀ x ∈ Bᶜ, ∀ y ∈ Bᶜ,
    connectedComponentIn Bᶜ x ≠ connectedComponentIn Bᶜ y →
      Separates (toExt γ.closedTrace) (connectedComponentIn Bᶜ x) (connectedComponentIn Bᶜ y)}

/-- **Definition** (the family `𝒞*`, Ch. I §6.2): locally rectifiable arcs in the finite part of `B` joining the
components of `-B`, i.e. having a limit point on each of `(-B)₁` and `(-B)₂`. -/
def ringJoinArcs (B : Set ExtPlane) : Set LRCurve :=
  {γ | toExt γ.trace ⊆ B ∧ ∃ x ∈ Bᶜ, ∃ y ∈ Bᶜ, connectedComponentIn Bᶜ x ≠ connectedComponentIn Bᶜ y ∧
    (∃ p ∈ connectedComponentIn Bᶜ x, p ∈ closure (toExt γ.trace)) ∧
      ∃ q ∈ connectedComponentIn Bᶜ y, q ∈ closure (toExt γ.trace)}

/-- The density `|f′/f|` on the finite part `D` of the domain of a canonical mapping `f` (`0` outside `D`; on `D` the
value `f(z)` lies in an annulus with `r₁ > 0` wherever it is used, so no division by zero occurs). -/
def logDerivDensity (f : ExtPlane → ExtPlane) (D : Set ℂ) : ℂ → ℝ≥0∞ :=
  D.indicator fun z => ENNReal.ofReal (‖deriv (finiteMap f) z‖ / ‖finiteMap f z‖)

/-- **Theorem 6.1** (Ch. I §6.2). The module of a ring domain `B` is
`M(B) = inf_{ρ ∈ P} 2π m_ρ(B) / (inf_{C ∈ 𝒞} l_ρ(C))²` (6.1), where the infimum is attained for `ρ = |f′/f|`, `f` a
canonical mapping.
Modelling: in `ℝ≥0∞`, including `M(B) = ∞`; the attainment is stated when `M(B) < ∞` (for `M(B) = ∞` the density
`|f′/f|` has infinite area and lies outside `P`). -/
theorem thm1_6_1 {B : Set ExtPlane} (hB : IsRingDomain B) :
    ringModule B = ⨅ ρ ∈ LiZhongQC.densitiesP0 (finitePart B),
      ENNReal.ofReal (2 * Real.pi) * LiZhongQC.rhoArea ρ (finitePart B) /
        (⨅ γ ∈ ringSepCurves B, γ.rhoLength ρ) ^ 2 ∧
    ∀ (f : ExtPlane → ExtPlane) (r₁ : ℝ) (r₂ : ℝ≥0∞), IsCanonicalRingMap B f r₁ r₂ → 0 < r₁ → r₂ < ⊤ →
      logDerivDensity f (finitePart B) ∈ LiZhongQC.densitiesP0 (finitePart B) ∧
      ringModule B =
        ENNReal.ofReal (2 * Real.pi) * LiZhongQC.rhoArea (logDerivDensity f (finitePart B)) (finitePart B) /
          (⨅ γ ∈ ringSepCurves B, γ.rhoLength (logDerivDensity f (finitePart B))) ^ 2 := by
  sorry

/-- **Formula (6.2)** (Ch. I §6.2). `M(B) = 2π sup_{ρ ∈ P} (inf_{C ∈ 𝒞*} l_ρ(C))² / m_ρ(B)`, where the supremum is
attained for `ρ = |f′/f|`, `f` a canonical mapping (stated when `M(B) < ∞`, as in `thm1_6_1`). -/
theorem eq1_6_2 {B : Set ExtPlane} (hB : IsRingDomain B) :
    ringModule B = ENNReal.ofReal (2 * Real.pi) * ⨆ ρ ∈ LiZhongQC.densitiesP0 (finitePart B),
      (⨅ γ ∈ ringJoinArcs B, γ.rhoLength ρ) ^ 2 / LiZhongQC.rhoArea ρ (finitePart B) ∧
    ∀ (f : ExtPlane → ExtPlane) (r₁ : ℝ) (r₂ : ℝ≥0∞), IsCanonicalRingMap B f r₁ r₂ → 0 < r₁ → r₂ < ⊤ →
      logDerivDensity f (finitePart B) ∈ LiZhongQC.densitiesP0 (finitePart B) ∧
      ringModule B = ENNReal.ofReal (2 * Real.pi) *
        ((⨅ γ ∈ ringJoinArcs B, γ.rhoLength (logDerivDensity f (finitePart B))) ^ 2 /
          LiZhongQC.rhoArea (logDerivDensity f (finitePart B)) (finitePart B)) := by
  sorry

/-! ## §6.3–6.4 Rengel-type estimates -/

/-- **Formula (6.3)** (Ch. I §6.3). The module of a ring domain `B` which separates the points `0` and `∞` satisfies
`M(B) ≤ (1/2π) ∬_B dσ/|z|²`. -/
theorem eq1_6_3 {B : Set ExtPlane} (hB : IsRingDomain B) (hsep : Separates B {((0 : ℂ) : ExtPlane)} {extInf}) :
    ringModule B ≤ ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ z in finitePart B, ENNReal.ofReal (1 / ‖z‖ ^ 2) := by
  sorry

/-- **Formula (6.3), equality case** (Ch. I §6.3, P1:881). Equality holds in (6.3) if and only if either `B` is an
annulus with centre `0` or `M(B)` is infinite. -/
theorem eq1_6_3_eq_iff {B : Set ExtPlane} (hB : IsRingDomain B)
    (hsep : Separates B {((0 : ℂ) : ExtPlane)} {extInf}) :
    ringModule B = ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ z in finitePart B, ENNReal.ofReal (1 / ‖z‖ ^ 2) ↔
      (∃ (r₁ : ℝ) (r₂ : ℝ≥0∞), 0 ≤ r₁ ∧ ENNReal.ofReal r₁ < r₂ ∧ B = annulusExt r₁ r₂) ∨ ringModule B = ⊤ := by
  sorry

/-- The spherical density `ρ(z) = (1 + |z|²)⁻¹` of §1.1 (Ch. I §6.4). -/
def sphericalDensity (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (1 / (1 + ‖z‖ ^ 2))

/-- **Formula (6.5)** (Ch. I §6.4). `M(B) ≤ 2π²/k₀²`, where `k₀` is the greatest lower bound of the spherical length
of the curves which separate `(-B)₁` and `(-B)₂`.
Modelling: in `ℝ≥0∞` (`k₀ = 0` gives the trivial bound `∞`). -/
theorem eq1_6_5 {B : Set ExtPlane} (hB : IsRingDomain B) :
    ringModule B ≤ ENNReal.ofReal (2 * Real.pi ^ 2) / (⨅ γ ∈ ringSepCurves B, γ.rhoLength sphericalDensity) ^ 2 := by
  sorry

/-- **Lemma 6.1** (Ch. I §6.4). If the ring domain `B` separates the pair of points `a₁, b₁` from the pair `a₂, b₂`
and the spherical distances satisfy `k(aᵢ, bᵢ) ≥ δ > 0`, `i = 1, 2`, then `M(B) ≤ π²/(2δ²)`. -/
theorem lemma1_6_1 {B : Set ExtPlane} (hB : IsRingDomain B) {a₁ b₁ a₂ b₂ : ExtPlane}
    (hsep : Separates B {a₁, b₁} {a₂, b₂}) {δ : ℝ} (hδ : 0 < δ) (h₁ : δ ≤ sphericalDist a₁ b₁)
    (h₂ : δ ≤ sphericalDist a₂ b₂) : ringModule B ≤ ENNReal.ofReal (Real.pi ^ 2 / (2 * δ ^ 2)) := by
  sorry

/-! ## §6.5–6.6 Degenerating ring domains; superadditivity -/

/-- **Definition** (spherical diameter, Ch. I §6.5): the supremum of `k(z₁, z₂)` over the set (`0` for the empty set;
every value is at most `π/2`). -/
def sphericalDiam (S : Set ExtPlane) : ℝ := sSup (Set.image2 sphericalDist S S)

/-- **Lemma 6.2** (Ch. I §6.5). Let `B` be a ring domain whose boundary components have spherical diameters `> δ` and
a mutual spherical distance `< ε`. Then, for `ε < δ`, `M(B) ≤ π² / log (tan (δ/2) / tan (ε/2))` (6.6). -/
theorem lemma1_6_2 {B : Set ExtPlane} (hB : IsRingDomain B) {δ ε : ℝ} (hεδ : ε < δ)
    (hdiam : ∀ x ∈ frontier B, δ < sphericalDiam (connectedComponentIn (frontier B) x))
    (hdist : ∃ p ∈ frontier B, ∃ q ∈ frontier B,
      connectedComponentIn (frontier B) p ≠ connectedComponentIn (frontier B) q ∧ sphericalDist p q < ε) :
    ringModule B ≤ ENNReal.ofReal (Real.pi ^ 2 / Real.log (Real.tan (δ / 2) / Real.tan (ε / 2))) := by
  sorry

/-- **Lemma 6.3** (Ch. I §6.6), superadditivity. Let `B, B₁, B₂, …` be ring domains such that the `Bₙ` are disjoint
subdomains of `B`. If every `Bₙ` separates `(-B)₁` and `(-B)₂`, then `∑ₙ M(Bₙ) ≤ M(B)` (6.7).
Modelling: the family is indexed by any type `ι`; a disjoint family of nonempty open subsets of `ℂ̄` is
countable, so this is the book's `n = 1, 2, …` (finite families included). -/
theorem lemma1_6_3_i {ι : Type*} {B : Set ExtPlane} (hB : IsRingDomain B) {Bn : ι → Set ExtPlane}
    (hBn : ∀ n, IsRingDomain (Bn n)) (hsub : ∀ n, Bn n ⊆ B) (hdisj : Pairwise fun m n => Disjoint (Bn m) (Bn n))
    (hsep : ∀ n, ∀ x ∈ Bᶜ, ∀ y ∈ Bᶜ, connectedComponentIn Bᶜ x ≠ connectedComponentIn Bᶜ y →
      Separates (Bn n) (connectedComponentIn Bᶜ x) (connectedComponentIn Bᶜ y)) :
    ∑' n, ringModule (Bn n) ≤ ringModule B := by
  sorry

/-- **Lemma 6.3** (Ch. I §6.6), equality case. If `B` is an annulus with finite module, then equality holds in (6.7)
if and only if every `Bₙ` is an annulus and `∑ m(Bₙ) = m(B)`.
Modelling: "annulus" is stated literally, with any centre; the book's proof shows the `Bₙ` are then concentric with
`B` (equality in (6.3) for `Bₙ` iff `Bₙ` is an annulus of the same centre). `B` is a non-degenerate annulus
`0 < r₁ < r₂ < ∞` ("finite module"). The family is indexed by any type `ι`; a disjoint family of nonempty open
subsets of `ℂ̄` is countable, so this is the book's `n = 1, 2, …` (finite families included). -/
theorem lemma1_6_3_ii {ι : Type*} {a : ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) {Bn : ι → Set ExtPlane}
    (hBn : ∀ n, IsRingDomain (Bn n)) (hsub : ∀ n, Bn n ⊆ toExt (LiZhongQC.annulusAt a r₁ r₂))
    (hdisj : Pairwise fun m n => Disjoint (Bn m) (Bn n))
    (hsep : ∀ n, ∀ x ∈ (toExt (LiZhongQC.annulusAt a r₁ r₂))ᶜ, ∀ y ∈ (toExt (LiZhongQC.annulusAt a r₁ r₂))ᶜ,
      connectedComponentIn (toExt (LiZhongQC.annulusAt a r₁ r₂))ᶜ x ≠
        connectedComponentIn (toExt (LiZhongQC.annulusAt a r₁ r₂))ᶜ y →
      Separates (Bn n) (connectedComponentIn (toExt (LiZhongQC.annulusAt a r₁ r₂))ᶜ x)
        (connectedComponentIn (toExt (LiZhongQC.annulusAt a r₁ r₂))ᶜ y)) :
    ∑' n, ringModule (Bn n) = ringModule (toExt (LiZhongQC.annulusAt a r₁ r₂)) ↔
      (∀ n, ∃ (c : ℂ) (s₁ s₂ : ℝ), 0 < s₁ ∧ s₁ < s₂ ∧ Bn n = toExt (LiZhongQC.annulusAt c s₁ s₂)) ∧
        ∑' n, volume (finitePart (Bn n)) = volume (LiZhongQC.annulusAt a r₁ r₂) := by
  sorry

/-! ## §6.7 Continuity of the module -/

/-- **Definition** (convergence from inside, Ch. I §6.7). `Bₙ ⊂ B` for every `n`, and for every `ε > 0`, for `n` large
every point of the component `(-Bₙ)ᵢ` of the complement of `Bₙ` containing `(-B)ᵢ` lies within a spherical distance
`< ε` of `(-B)ᵢ`, `i = 1, 2`. [OCR] The book prints `(-B₁)ᵢ` for `(-B)ᵢ`. -/
def RingConvergesFromInside (Bn : ℕ → Set ExtPlane) (B : Set ExtPlane) : Prop :=
  (∀ n, Bn n ⊆ B) ∧ ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ Bᶜ, ∀ z ∈ connectedComponentIn (Bn n)ᶜ x,
    ∃ z' ∈ connectedComponentIn Bᶜ x, sphericalDist z z' < ε

/-- **Lemma 6.4** (Ch. I §6.7). If `Bₙ` is a sequence of ring domains which converges to a ring domain `B` from
inside, then `lim M(Bₙ) = M(B)`. -/
theorem lemma1_6_4 {Bn : ℕ → Set ExtPlane} {B : Set ExtPlane} (hBn : ∀ n, IsRingDomain (Bn n))
    (hB : IsRingDomain B) (h : RingConvergesFromInside Bn B) :
    Tendsto (fun n => ringModule (Bn n)) atTop (𝓝 (ringModule B)) := by
  sorry

/-- **Definition** (analytic ring domain, Ch. I §6.7): a ring domain whose boundary consists of two analytic
curves. -/
def IsAnalyticRing (B : Set ExtPlane) : Prop :=
  IsRingDomain B ∧ ∀ x ∈ frontier B, IsAnalyticCurve (connectedComponentIn (frontier B) x)

/-- **Unlabelled** (Ch. I §6.7, P1:965). For every ring domain `B` there exists a sequence of analytic ring domains
`Bₙ`, `B̄ₙ ⊂ B`, which converges to `B` from inside. -/
theorem exists_analyticRing_fromInside {B : Set ExtPlane} (hB : IsRingDomain B) :
    ∃ Bn : ℕ → Set ExtPlane, (∀ n, IsAnalyticRing (Bn n) ∧ closure (Bn n) ⊆ B) ∧ RingConvergesFromInside Bn B := by
  sorry

/-! ## §6.8 Relations between the modules of ring domains and quadrilaterals -/

/-- **Lemma 6.5** (Ch. I §6.8). Let `Qₙ` be quadrilaterals having no common interior points. If `B` is a ring domain
which separates the a-sides of every `Qₙ`, then `∑ M(Qₙ) ≤ 2π / M(B)` (6.8). Any index type `ι`, as in Lemma 4.2.
Modelling: in `ℝ≥0∞` (for `M(B) = ∞` the bound is `0`; the hypothesis then admits no nondegenerate quadrilateral,
cf. the book's remark on degenerate ones). -/
theorem lemma1_6_5_i {ι : Type*} {Qn : ι → Quadrilateral} (hdisj : Pairwise fun m n => Disjoint (Qn m).dom (Qn n).dom)
    {B : Set ExtPlane} (hB : IsRingDomain B) (hsep : ∀ n, Separates B ((Qn n).side 0) ((Qn n).side 2)) :
    ∑' n, ENNReal.ofReal (Qn n).module ≤ ENNReal.ofReal (2 * Real.pi) / ringModule B := by
  sorry

/-- **Lemma 6.5** (Ch. I §6.8), equality case. If `B` is an annulus, then equality holds in (6.8) if and only if the
a-sides of each `Qₙ` lie on the boundary of `B`, the b-sides are radial segments, and `∑ m(Qₙ) = m(B)`.
Modelling: `B` is a non-degenerate annulus `0 < r₁ < r₂ < ∞`; for a degenerate annulus `M(B) = ∞` and no
nondegenerate quadrilateral satisfies the separation hypothesis. Any index type `ι`, as in Lemma 4.2. -/
theorem lemma1_6_5_ii {ι : Type*} {Qn : ι → Quadrilateral}
    (hdisj : Pairwise fun m n => Disjoint (Qn m).dom (Qn n).dom) {a : ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂)
    (hsep : ∀ n, Separates (toExt (LiZhongQC.annulusAt a r₁ r₂)) ((Qn n).side 0) ((Qn n).side 2)) :
    ∑' n, ENNReal.ofReal (Qn n).module =
        ENNReal.ofReal (2 * Real.pi) / ringModule (toExt (LiZhongQC.annulusAt a r₁ r₂)) ↔
      (∀ n, (Qn n).side 0 ⊆ frontier (toExt (LiZhongQC.annulusAt a r₁ r₂)) ∧
        (Qn n).side 2 ⊆ frontier (toExt (LiZhongQC.annulusAt a r₁ r₂)) ∧
        ∀ i ∈ ({1, 3} : Set (Fin 4)), ∃ θ : ℝ,
          (Qn n).side i = toExt ((fun t : ℝ => a + (t : ℂ) * exp ((θ : ℂ) * I)) '' Icc r₁ r₂)) ∧
      ∑' n, (Qn n).area = volume (LiZhongQC.annulusAt a r₁ r₂) := by
  sorry

end LehtoVirtanen1973
