import References.GardinerLakic2000.Ch17.S07_AsymptoticHamiltonSequences

/-!
# Gardiner–Lakic 2000, Ch. 18 §18.1 Finite earthquakes (with the chapter introduction)

Source `teichmuller.txt`, lines 13199–13319 (Chapter 18, introduction and §18.1).

* Definition (counterclockwise order on `S¹`; cyclic, order-preserving maps, l. 13208, 13263) — `IsCCW3`, `IsCCW4`,
  `IsCyclicOrderPreserving`
* Definition (adjacent points; lines joining points of `S`; finite lamination, l. 13210–13216) —
  `AreAdjacentOnCircle`, `AreLinked`, `IsFiniteLamination`
* Definition (the triangles of a finite lamination; border triangle and its midpoint, l. 13216–13220) —
  `IsLaminationTriangle`, `IsBorderTriangle`
* Lemma 1 (l. 13222) — `lemma18_1`
* Definition (the cross ratio `cr(Q)` and the amount `log λ` by which `h` moves `d` to the left relative to
  `a, b, c`, l. 13268–13284) — `crossRatioQ`, `leftShift`, `leftOf`
* Definition (comparison map on a line, l. 13244–13248) — `comparisonMap`
* Definition (finite left earthquake `h_σ` for a lamination with a nonnegative measure, l. 13234–13251; finite right
  earthquake, l. 13261) — `IsFiniteLeftEarthquake`, `IsFiniteRightEarthquake`
* Lemma 2 (l. 13253) — `lemma18_2`
* Definition (stratum of a finite earthquake, l. 13259) — `IsPartOfFiniteStratum`
* Theorem 1 (finite earthquake theorem, l. 13263; the parallel right statement, l. 13265) — `thm18_1_left`,
  `thm18_1_right`
* Lemma 3 (l. 13277) — `lemma18_3`
* Lemma 4 (l. 13298) — `lemma18_4`
* Lemma 5 (l. 13314) — `lemma18_5`

Not items: the Catalan count of topological types (l. 13214, a remark); the proofs. Modelling (leader calibration of
Part E, E0.7): the finite earthquake is characterized, not constructed. Points of `S¹` are complex numbers of modulus
`1`, `S` a finite set of them, lines are unordered pairs (`Sym2 ℂ`) of points of `S`, a measure on `𝓛` is a weight
function `σ : Sym2 ℂ → ℝ` vanishing off `𝓛`. Leftward isometric shearing along `𝓛` by the weights `σ` is
characterized by its effect on the quadrilaterals `a, b, c, d` (counterclockwise) of two adjacent triangles `abc`,
`acd`: `h` moves `d` to the left relative to `a, b, c` by exactly `σ(ac)` (Lemma 3's measure of leftward motion
`log(cr(h(Q))/cr(Q))`, invariant under post-composition by Möbius maps, so `h_σ` is determined up to such maps; the
book's comparison map `C_j` realizes this shear). `leftOf h a b c x` measures the motion of `x` relative to the
triple `a, b, c` in the cyclic rotation that puts `x` last. The printed "by Lemma 2" in the proof of Theorem 1
(l. 13309) is Lemma 3 [misprint].
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold Classical

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (ExtPlane)

/-- Helper (§18.1). `a, b, c ∈ S¹` are in counterclockwise order. -/
def IsCCW3 (a b c : ℂ) : Prop :=
  ∃ θ₁ θ₂ θ₃ : ℝ, θ₁ < θ₂ ∧ θ₂ < θ₃ ∧ θ₃ < θ₁ + 2 * π ∧ a = exp (θ₁ * I) ∧ b = exp (θ₂ * I) ∧ c = exp (θ₃ * I)

/-- Helper (§18.1). `a, b, c, d ∈ S¹` are in counterclockwise order. -/
def IsCCW4 (a b c d : ℂ) : Prop :=
  ∃ θ₁ θ₂ θ₃ θ₄ : ℝ, θ₁ < θ₂ ∧ θ₂ < θ₃ ∧ θ₃ < θ₄ ∧ θ₄ < θ₁ + 2 * π ∧ a = exp (θ₁ * I) ∧ b = exp (θ₂ * I) ∧
    c = exp (θ₃ * I) ∧ d = exp (θ₄ * I)

/-- **Definition** (§18.1, l. 13208, 13263). `h` is a cyclic, order-preserving map of the finite set `S ⊆ S¹` into
`S¹`: injective on `S`, with values on `S¹`, preserving counterclockwise order. -/
def IsCyclicOrderPreserving (S : Finset ℂ) (h : ℂ → ℂ) : Prop :=
  (↑S : Set ℂ) ⊆ sphere 0 1 ∧ InjOn h S ∧ (∀ a ∈ S, h a ∈ sphere (0 : ℂ) 1) ∧
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, IsCCW3 a b c → IsCCW3 (h a) (h b) (h c)

/-- **Definition** (adjacent points, §18.1, l. 13210). `a ≠ c` in `S` and one of the two arcs of `S¹ ∖ {a, c}`
contains no point of `S`. -/
def AreAdjacentOnCircle (S : Finset ℂ) (a c : ℂ) : Prop :=
  a ∈ S ∧ c ∈ S ∧ a ≠ c ∧ ∃ z ∈ sphere (0 : ℂ) 1 \ {a, c},
    Disjoint (connectedComponentIn (sphere (0 : ℂ) 1 \ {a, c}) z) (↑S : Set ℂ)

/-- Helper (§18.1, l. 13210). The hyperbolic lines `ab` and `cd` intersect: four distinct points of `S¹` with `c`, `d`
on different arcs of `S¹ ∖ {a, b}`. -/
def AreLinked (a b c d : ℂ) : Prop :=
  a ≠ b ∧ c ≠ d ∧ c ∉ ({a, b} : Set ℂ) ∧ d ∉ ({a, b} : Set ℂ) ∧
    connectedComponentIn (sphere (0 : ℂ) 1 \ {a, b}) c ≠ connectedComponentIn (sphere (0 : ℂ) 1 \ {a, b}) d

/-- **Definition** (finite lamination, §18.1, l. 13210). `n − 3` pairwise non-intersecting hyperbolic lines joining
non-adjacent points of `S` (`n = |S| ≥ 4`). -/
def IsFiniteLamination (S : Finset ℂ) (L : Finset (Sym2 ℂ)) : Prop :=
  4 ≤ S.card ∧ (↑S : Set ℂ) ⊆ sphere 0 1 ∧ L.card + 3 = S.card ∧
    (∀ a c : ℂ, s(a, c) ∈ L → a ∈ S ∧ c ∈ S ∧ a ≠ c ∧ ¬ AreAdjacentOnCircle S a c) ∧
    ∀ a b c d : ℂ, s(a, b) ∈ L → s(c, d) ∈ L → ¬ AreLinked a b c d

/-- **Definition** (the triangles of `𝓛`, §18.1, l. 13216). Distinct `a, b, c ∈ S` each of whose sides is a line of
`𝓛` or joins adjacent points of `S` (a boundary side). -/
def IsLaminationTriangle (S : Finset ℂ) (L : Finset (Sym2 ℂ)) (a b c : ℂ) : Prop :=
  a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ (s(a, b) ∈ L ∨ AreAdjacentOnCircle S a b) ∧
    (s(b, c) ∈ L ∨ AreAdjacentOnCircle S b c) ∧ (s(a, c) ∈ L ∨ AreAdjacentOnCircle S a c)

/-- **Definition** (border triangle, midpoint, §18.1, l. 13219–13220). A triangle `abc` (counterclockwise) of `𝓛`
with exactly one side `ac` in `𝓛`; `b` is its midpoint. -/
def IsBorderTriangle (S : Finset ℂ) (L : Finset (Sym2 ℂ)) (a b c : ℂ) : Prop :=
  IsLaminationTriangle S L a b c ∧ IsCCW3 a b c ∧ s(a, c) ∈ L ∧ AreAdjacentOnCircle S a b ∧ AreAdjacentOnCircle S b c

/-- **Lemma 1** (§18.1, l. 13222). A finite lamination on `n ≥ 4` points has at least two border triangles. -/
theorem lemma18_1 {S : Finset ℂ} {L : Finset (Sym2 ℂ)} (hL : IsFiniteLamination S L) :
    ∃ a b c a' b' c' : ℂ, IsBorderTriangle S L a b c ∧ IsBorderTriangle S L a' b' c' ∧ b ≠ b' := by
  sorry

/-- **Definition** (§18.1, l. 13280). The cross ratio `cr(Q) = (d − c)(b − a) / ((c − b)(a − d))`. -/
def crossRatioQ (a b c d : ℂ) : ℂ := (d - c) * (b - a) / ((c - b) * (a - d))

/-- **Definition** (§18.1, l. 13268–13284). The amount `log λ(a, b, c, d)`, `λ = cr(h(Q))/cr(Q)`, by which `h` moves
`d` to the left relative to `a, b, c` (to the right when negative). -/
def leftShift (h : ℂ → ℂ) (a b c d : ℂ) : ℝ :=
  Real.log (crossRatioQ (h a) (h b) (h c) (h d) / crossRatioQ a b c d).re

/-- Helper (§18.1). The leftward motion of `x` relative to the triple `{a, b, c}`, in the cyclic rotation of `a, b, c`
that puts `x` last in counterclockwise order. -/
def leftOf (h : ℂ → ℂ) (a b c x : ℂ) : ℝ :=
  if IsCCW4 a b c x then leftShift h a b c x else if IsCCW4 b c a x then leftShift h b c a x
  else leftShift h c a b x

/-- **Definition** (comparison map on a line, §18.1, l. 13244–13248). The hyperbolic Möbius map `C` with fixed points
`a₁`, `b₁` and multiplier `λ = e^μ`: `(C(z) − b₁)/(C(z) − a₁) = λ (z − b₁)/(z − a₁)`. -/
def comparisonMap (a₁ b₁ : ℂ) (μ : ℝ) (z : ℂ) : ℂ :=
  (b₁ - a₁ * (exp μ * (z - b₁) / (z - a₁))) / (1 - exp μ * (z - b₁) / (z - a₁))

/-- **Definition** (finite left earthquake, §18.1, l. 13234–13251). `h` on `S` is the finite left earthquake of the
lamination `𝓛` with the nonnegative weights `σ` (up to post-composition by a Möbius map): for every two adjacent
triangles `abc`, `acd` of `𝓛` (`a, b, c, d` counterclockwise), `h` moves `d` to the left relative to `a, b, c` by
`σ(ac)`. -/
def IsFiniteLeftEarthquake (S : Finset ℂ) (L : Finset (Sym2 ℂ)) (σ : Sym2 ℂ → ℝ) (h : ℂ → ℂ) : Prop :=
  IsFiniteLamination S L ∧ IsCyclicOrderPreserving S h ∧ (∀ l, 0 ≤ σ l) ∧ (∀ l, l ∉ L → σ l = 0) ∧
    ∀ a b c d : ℂ, IsCCW4 a b c d → IsLaminationTriangle S L a b c → IsLaminationTriangle S L a c d →
      s(a, c) ∈ L → leftShift h a b c d = σ s(a, c)

/-- **Definition** (finite right earthquake, §18.1, l. 13261). As `IsFiniteLeftEarthquake`, shearing to the right. -/
def IsFiniteRightEarthquake (S : Finset ℂ) (L : Finset (Sym2 ℂ)) (σ : Sym2 ℂ → ℝ) (h : ℂ → ℂ) : Prop :=
  IsFiniteLamination S L ∧ IsCyclicOrderPreserving S h ∧ (∀ l, 0 ≤ σ l) ∧ (∀ l, l ∉ L → σ l = 0) ∧
    ∀ a b c d : ℂ, IsCCW4 a b c d → IsLaminationTriangle S L a b c → IsLaminationTriangle S L a c d →
      s(a, c) ∈ L → leftShift h a b c d = -σ s(a, c)

/-- **Lemma 2** (§18.1, l. 13253). The finite left earthquake is determined by `𝓛` and `σ` up to post-composition by
a Möbius transformation preserving the circle (the constructions from different starting triangles differ by such a
map). -/
theorem lemma18_2 {S : Finset ℂ} {L : Finset (Sym2 ℂ)} {σ : Sym2 ℂ → ℝ} {h₁ h₂ : ℂ → ℂ}
    (h₁e : IsFiniteLeftEarthquake S L σ h₁) (h₂e : IsFiniteLeftEarthquake S L σ h₂) :
    ∃ B ∈ Pommerenke1992.mobDisc, ∀ z ∈ S, ((h₂ z : ℂ) : ExtPlane) = B (h₁ z) := by
  sorry

/-- **Definition** (stratum, §18.1, l. 13259). The triangle `abc` is a stratum or part of a stratum: no line of
positive weight separates two of its vertices. -/
def IsPartOfFiniteStratum (σ : Sym2 ℂ → ℝ) (a b c : ℂ) : Prop :=
  ∀ x y : ℂ, 0 < σ s(x, y) → ¬ AreLinked x y a b ∧ ¬ AreLinked x y b c ∧ ¬ AreLinked x y a c

/-- **Theorem 1** (finite earthquake theorem, §18.1, l. 13263). Every cyclic, order-preserving map `h` of a finite
`S ⊆ S¹` (`|S| ≥ 4`) into `S¹` is, up to post-composition by a Möbius transformation, a finite left earthquake for a
finite lamination with a nonnegative measure; `S` and `h` determine the measure. -/
theorem thm18_1_left {S : Finset ℂ} (hS : 4 ≤ S.card) {h : ℂ → ℂ} (hh : IsCyclicOrderPreserving S h) :
    (∃ (L : Finset (Sym2 ℂ)) (σ : Sym2 ℂ → ℝ), IsFiniteLeftEarthquake S L σ h) ∧
    ∀ (L L' : Finset (Sym2 ℂ)) (σ σ' : Sym2 ℂ → ℝ), IsFiniteLeftEarthquake S L σ h →
      IsFiniteLeftEarthquake S L' σ' h → σ = σ' := by
  sorry

/-- **Theorem 1** (§18.1, l. 13265), the parallel statement for finite right earthquakes. -/
theorem thm18_1_right {S : Finset ℂ} (hS : 4 ≤ S.card) {h : ℂ → ℂ} (hh : IsCyclicOrderPreserving S h) :
    (∃ (L : Finset (Sym2 ℂ)) (σ : Sym2 ℂ → ℝ), IsFiniteRightEarthquake S L σ h) ∧
    ∀ (L L' : Finset (Sym2 ℂ)) (σ σ' : Sym2 ℂ → ℝ), IsFiniteRightEarthquake S L σ h →
      IsFiniteRightEarthquake S L' σ' h → σ = σ' := by
  sorry

/-- Helper for `lemma18_3` (§18.1, l. 13277). The cross-ratio of four points of the unit circle is real
(`conj w = w⁻¹` on the circle). -/
theorem gl18_crossRatioQ_im {a b c d : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) :
    (crossRatioQ a b c d).im = 0 := by
  have hconj : ∀ w : ℂ, ‖w‖ = 1 → conj w = w⁻¹ := fun w hw => by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hw]
    simp
  have h0 : ∀ w : ℂ, ‖w‖ = 1 → w ≠ 0 := fun w hw h => by simp [h] at hw
  have ha0 := h0 a ha
  have hb0 := h0 b hb
  have hc0 := h0 c hc
  have hd0 := h0 d hd
  -- `conj` of each factor is the factor divided by `a b c d` (up to the signs, which cancel)
  set k : ℂ := a * b * c * d with hk
  have hk0 : k ≠ 0 := by simp [hk, ha0, hb0, hc0, hd0]
  have hnum : conj ((d - c) * (b - a)) = (d - c) * (b - a) / k := by
    rw [map_mul, map_sub, map_sub, hconj a ha, hconj b hb, hconj c hc, hconj d hd]
    field_simp
    ring
  have hden : conj ((c - b) * (a - d)) = (c - b) * (a - d) / k := by
    rw [map_mul, map_sub, map_sub, hconj a ha, hconj b hb, hconj c hc, hconj d hd]
    field_simp
    ring
  have hcr : conj (crossRatioQ a b c d) = crossRatioQ a b c d := by
    unfold crossRatioQ
    rw [map_div₀, hnum, hden, div_div_div_cancel_right₀ hk0]
  exact Complex.conj_eq_iff_im.1 hcr

/-- Helper for `lemma18_3` (§18.1, l. 13277). `cr(b, c, d, a) = cr(a, b, c, d)⁻¹`. -/
theorem gl18_crossRatioQ_rot (a b c d : ℂ) : crossRatioQ b c d a = (crossRatioQ a b c d)⁻¹ := by
  unfold crossRatioQ
  rw [inv_div]
  ring

/-- **Lemma 3** (§18.1, l. 13277). For `a, b, c, d` counterclockwise in `S`, either `h` moves `d` to the left relative
to `a, b, c` or it moves `a` to the left relative to `b, c, d`; and `h` moves `d` to the right relative to `a, b, c` iff
it moves `a` to the left relative to `b, c, d`. -/
theorem lemma18_3 {S : Finset ℂ} {h : ℂ → ℂ} (hh : IsCyclicOrderPreserving S h) {a b c d : ℂ} (ha : a ∈ S)
    (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) (hQ : IsCCW4 a b c d) :
    (0 ≤ leftShift h a b c d ∨ 0 ≤ leftShift h b c d a) ∧ (leftShift h a b c d ≤ 0 ↔ 0 ≤ leftShift h b c d a) := by
  -- the identity `λ(b, c, d, a) = λ(a, b, c, d)⁻¹` holds for any four points of the circle; the order is not used
  have _hQ := hQ
  obtain ⟨hS, -, hhS, -⟩ := hh
  have hn : ∀ w ∈ S, ‖w‖ = 1 := fun w hw => by simpa using hS hw
  have hhn : ∀ w ∈ S, ‖h w‖ = 1 := fun w hw => by simpa using hhS w hw
  -- `λ = cr(h Q)/cr(Q)` is real
  set lam : ℂ := crossRatioQ (h a) (h b) (h c) (h d) / crossRatioQ a b c d with hlam
  have h1 := gl18_crossRatioQ_im (hhn a ha) (hhn b hb) (hhn c hc) (hhn d hd)
  have h2 := gl18_crossRatioQ_im (hn a ha) (hn b hb) (hn c hc) (hn d hd)
  have hlam_im : lam.im = 0 := by
    rw [hlam, Complex.div_im, h1, h2]
    ring
  have hlam_eq : lam = (lam.re : ℂ) := Complex.ext (by simp) (by simp [hlam_im])
  -- `λ(b, c, d, a) = λ⁻¹`, whose real part is `(Re λ)⁻¹`
  have hrot : crossRatioQ (h b) (h c) (h d) (h a) / crossRatioQ b c d a = lam⁻¹ := by
    rw [gl18_crossRatioQ_rot (h a) (h b) (h c) (h d), gl18_crossRatioQ_rot a b c d, hlam, inv_div_inv, inv_div]
  have hshift : leftShift h b c d a = -leftShift h a b c d := by
    unfold leftShift
    rw [hrot, ← hlam, hlam_eq, ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re, Real.log_inv]
  rw [hshift]
  exact ⟨(le_total 0 (leftShift h a b c d)).imp id fun h' => neg_nonneg.2 h', neg_nonneg.symm⟩

/-- **Lemma 4** (§18.1, l. 13298). There is a triple `T = {a, b, c} ⊆ S` such that every point of `S ∖ T` is fixed or
moved to the left by `A_T ∘ h` (relative to `a, b, c`). -/
theorem lemma18_4 {S : Finset ℂ} (hS : 4 ≤ S.card) {h : ℂ → ℂ} (hh : IsCyclicOrderPreserving S h) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, IsCCW3 a b c ∧ ∀ x ∈ S, x ∉ ({a, b, c} : Set ℂ) → 0 ≤ leftOf h a b c x := by
  sorry

/-- **Lemma 5** (§18.1, l. 13314). If `a, b, c ∈ S₁`, `a` and `c` are adjacent in `S₁`, `h` is cyclic and
order-preserving on `S₁` and moves every point of `S₁` to the left relative to `a, b, c`, then the triangle `abc` is
a stratum or part of a stratum of the finite left earthquake of `h` on `S₁`. -/
theorem lemma18_5 {S₁ : Finset ℂ} {h : ℂ → ℂ} (hh : IsCyclicOrderPreserving S₁ h) {a b c : ℂ} (ha : a ∈ S₁)
    (hb : b ∈ S₁) (hc : c ∈ S₁) (hac : AreAdjacentOnCircle S₁ a c)
    (hleft : ∀ e ∈ S₁, e ∉ ({a, b, c} : Set ℂ) → 0 ≤ leftOf h a b c e) {L : Finset (Sym2 ℂ)} {σ : Sym2 ℂ → ℝ}
    (hE : IsFiniteLeftEarthquake S₁ L σ h) : IsPartOfFiniteStratum σ a b c := by
  sorry

end GardinerLakic2000
