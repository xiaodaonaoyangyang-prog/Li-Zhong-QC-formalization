import References.Common.HyperbolicSurface

/-!
# Imayoshi–Taniguchi, Chapter 3 §3.1: Hyperbolic geometry

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 3 §3.1 (`full.md` IT1:1522–1815,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Conventions: the Poincaré metric of `Δ` is `ds² = 4|dz|²/(1-|z|²)²` (curvature `-1`), that of `ℍ` is `|dz|/Im z`; these are
`LiZhongQC.poincareDensity unitDisc` and Mathlib's `UpperHalfPlane` metric. A Riemann surface `R = ℍ/Γ` is given by a
uniformization `p : ℍ → R` of a torsion-free Fuchsian group (`IsFuchsian`, `ActsFreely`, `IsUniformization`, as in
`References/Common/HyperbolicSurface.lean`); the hyperbolic metric `ds_R²` is read off through lifts (`References.hypDistSurf`,
`LiZhongQC.poincareLengthLoop`). A pair of pants of `R` is a relatively compact open subset `P ⊆ R` homeomorphic to the
three-holed disc `pantsModel` whose frontier is the union of three simple closed geodesics, pairwise equal or disjoint (two boundary
components of `P` may lie on the same geodesic of `R`, e.g. in a genus-2 "dumbbell" decomposition).

* Definition (Poincaré metric and distance on `Δ`, §3.1.1, IT1:1536) — exists: `LiZhongQC.poincareDist`,
  `LiZhongQC.poincareDensity`
* Proposition 3.1 (a) (Schwarz–Pick lemma, IT1:1550) — exists: `LiZhongQC.schwarz_pick_unitDisc`
* Proposition 3.1 (b) (equality case, IT1:1559) — `prop3_1_b`
* Corollary to Proposition 3.1 (holomorphic self-maps of `Δ` contract `ρ`, IT1:1586) — `prop3_1_cor`
* Definition (hyperbolic length, geodesic in `Δ`, §3.1.2, IT1:1604) — `IsGeodesicArcDisc`
* Proposition 3.2 (geodesics in `Δ`, IT1:1610) — `prop3_2`
* Definition (axis of a hyperbolic transformation, IT1:1628) — exists: `References.axisH`
* Definition (Poincaré metric on `H`, IT1:1630) — exists: `LiZhongQC.poincareDensity_upperHalf`
* Definition (hyperbolic metric on `R`, §3.1.3, IT1:1646) — exists: `References.hypDistSurf`
* Definition (`γ` covers `C_γ`, IT1:1648) — exists: `LiZhongQC.Covers`
* Unlabelled (`L_γ` is the unique geodesic in the free homotopy class of `C_γ`, IT1:1650) — `para3_1_3`
* Definition (closed geodesic `L_γ`, IT1:1650) — exists: `References.IsSimpleClosedGeodesicOf`
* Proposition 3.3 (`tr² = 4 cosh²(ℓ/2)`, IT1:1652) — `prop3_3`
* Unlabelled (cutting along geodesics gives triply connected pieces, §3.1.4, IT1:1674) — `pantsModel`, `para3_1_4_a`
* Definition (pair of pants of `R`, IT1:1680) — `IsPantsOf`
* Unlabelled (the stabilizer of a lift of a pair of pants, IT1:1685) — `stabSubgroup`, `para3_1_4_b`
* Definition (Nielsen extension and Nielsen kernel, IT1:1687) — `NielsenExtension`
* Unlabelled (`P` is the unique pair of pants of its Nielsen extension, IT1:1689) — `para3_1_4_c`
* Theorem 3.4 (existence of pairs of pants with given boundary lengths, §3.1.5, IT1:1697) — `thm3_4`
* Theorem 3.5 (lengths determine the pair of pants, IT1:1743) — `thm3_5`
* Corollary to Theorem 3.5 (reflection of a pair of pants, IT1:1799) — `IsAntiholomorphicMap`, `thm3_5_cor`
* Definition (reflection `J_P` of `P`, IT1:1805) — `thm3_5_cor`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (unitDisc LRCurve IsPathIn poincareDensity poincareDist IsConformalOnto IsFuchsian ActsFreely IsUniformization
  Covers IsHyperbolic slTrace translationLength freeHomotopyLength poincareLengthLoop FreelyHomotopic Loop)
open References (axisH IsSimpleClosedGeodesicOf HypSurfBdry IsTrouserCoreWithLengths)

/-! ## §3.1.1 The Poincaré metric -/

/-- **Proposition 3.1 (b)** (equality case of the Schwarz–Pick lemma, Ch. 3 §3.1.1). If a holomorphic `f : Δ → Δ` satisfies
`|f'(z)|/(1-|f(z)|²) = 1/(1-|z|²)` at one point of `Δ`, then `f` is a biholomorphic automorphism of `Δ` and equality holds
at every point. -/
theorem prop3_1_b {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hmaps : MapsTo f unitDisc unitDisc) {a : ℂ}
    (ha : a ∈ unitDisc) (heq : ‖deriv f a‖ / (1 - ‖f a‖ ^ 2) = 1 / (1 - ‖a‖ ^ 2)) :
    IsConformalOnto f unitDisc unitDisc ∧ ∀ z ∈ unitDisc, ‖deriv f z‖ / (1 - ‖f z‖ ^ 2) = 1 / (1 - ‖z‖ ^ 2) := by
  sorry

/-- **Corollary to Proposition 3.1** (Ch. 3 §3.1.1). Every holomorphic `f : Δ → Δ` is a contraction of the Poincaré distance:
`ρ(f(z₁), f(z₂)) ≤ ρ(z₁, z₂)`. -/
theorem prop3_1_cor {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hmaps : MapsTo f unitDisc unitDisc) {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ unitDisc) (h₂ : z₂ ∈ unitDisc) : poincareDist unitDisc (f z₁) (f z₂) ≤ poincareDist unitDisc z₁ z₂ := by
  sorry

/-! ## §3.1.2 Geodesics -/

/-- **Geodesic in `Δ`** (Ch. 3 §3.1.2): a rectifiable curve `γ` in `Δ` from `z₁` to `z₂` whose hyperbolic length
`ℓ(γ) = ∫_γ ds` equals the Poincaré distance `ρ(z₁, z₂)`. -/
def IsGeodesicArcDisc (z₁ z₂ : ℂ) (γ : LRCurve) : Prop :=
  IsPathIn unitDisc z₁ z₂ γ ∧
    γ.rhoLength (fun z => ENNReal.ofReal (poincareDensity unitDisc z)) = poincareDist unitDisc z₁ z₂

/-- **Proposition 3.2** (Ch. 3 §3.1.2). For arbitrary `z₁, z₂ ∈ Δ` there exists a geodesic connecting them; it is unique (as a
point set), and it is a subarc of a diameter or of a circle orthogonal to `∂Δ` (the circle `|z - c| = R` with `|c|² = 1 + R²`). -/
theorem prop3_2 {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitDisc) (h₂ : z₂ ∈ unitDisc) :
    ∃ γ : LRCurve, IsGeodesicArcDisc z₁ z₂ γ ∧
      (∀ γ' : LRCurve, IsGeodesicArcDisc z₁ z₂ γ' → γ'.toFun '' Icc 0 1 = γ.toFun '' Icc 0 1) ∧
      ((∃ c : ℂ, ‖c‖ = 1 ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∃ s : ℝ, γ.toFun t = s * c) ∨
        ∃ (c : ℂ) (R : ℝ), 0 < R ∧ ‖c‖ ^ 2 = 1 + R ^ 2 ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖γ.toFun t - c‖ = R) := by
  sorry

/-! ## §3.1.3 The hyperbolic metric on a Riemann surface -/

/-- **Unlabelled claim** (Ch. 3 §3.1.3, IT1:1650). If `γ ∈ Γ` is hyperbolic and covers the closed curve `α` of `R = ℍ/Γ`,
then the closed geodesic `L_γ = p(A_γ)` is the unique geodesic in the free homotopy class of `α`: it is the image of a loop
freely homotopic to `α` of the minimal length `freeHomotopyLength p α`, and every loop of that class of minimal length has
this image. -/
theorem para3_1_3 {R : Type} [TopologicalSpace R] [ChartedSpace ℂ R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → R} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) (hh : IsHyperbolic γ) {α : Loop R} (hcov : Covers p γ α) :
    (∃ β : Loop R, FreelyHomotopic α β ∧ poincareLengthLoop p β = freeHomotopyLength p α ∧
      range (β.2 : unitInterval → R) = p '' axisH γ) ∧
    ∀ β : Loop R, FreelyHomotopic α β → poincareLengthLoop p β = freeHomotopyLength p α →
      range (β.2 : unitInterval → R) = p '' axisH γ := by
  sorry

/-- **Proposition 3.3** (Ch. 3 §3.1.3). Let `γ(z) = (az + b)/(cz + d)` be a hyperbolic element of a Fuchsian model `Γ` of `R`
and `ℓ` the hyperbolic length of the closed geodesic `L_γ`. Then `tr²(γ) = (a + d)² = 4 cosh²(ℓ/2)`. -/
theorem prop3_3 {R : Type} [TopologicalSpace R] [ChartedSpace ℂ R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → R} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) (hh : IsHyperbolic γ) {α : Loop R} (hcov : Covers p γ α)
    {ℓ : ℝ} (hℓ : freeHomotopyLength p α = ENNReal.ofReal ℓ) :
    (slTrace γ) ^ 2 = 4 * Real.cosh (ℓ / 2) ^ 2 := by
  sorry

/-! ## §3.1.4 Pairs of pants -/

/-- **The model of a pair of pants** `P₀ = {|z| < 2} − ({|z+1| ≤ 1/2} ∪ {|z-1| ≤ 1/2})` (Ch. 3 §3.1.4): a triply connected
planar domain. -/
def pantsModel : Set ℂ := ball 0 2 \ (closedBall (-1) (1 / 2) ∪ closedBall 1 (1 / 2))

/-- **Pair of pants of `R`** (Ch. 3 §3.1.4, IT1:1680): a relatively compact open subset `P` of `R = ℍ/Γ` which is triply
connected (homeomorphic to `pantsModel`) and whose frontier is the union of three simple closed geodesics of `R` which are
pairwise equal or disjoint. **Correction** (IT-fix2, audit AUDIT3_IT finding 3): the geodesics were required to be pairwise
disjoint, which excludes a piece with two boundary components on the same geodesic of `R` (genus 2, system `{a, b, c}` with `a, b`
non-separating and `c` separating: the piece bounded by `a⁺, a⁻, c` has frontier `a ∪ c`), so `para3_2_1` was false there. Modelling: a subsurface of `R` (Hubbard's trouser is the abstract surface `References.IsTrouserCore`); topological
space only is needed, so the definition also applies to the quotient `P̂`. -/
def IsPantsOf {R : Type} [TopologicalSpace R] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (p : UpperHalfPlane → R) (P : Set R) : Prop :=
  IsOpen P ∧ IsCompact (closure P) ∧ Nonempty (↥P ≃ₜ ↥pantsModel) ∧
    ∃ C : Fin 3 → Set R, (∀ j, IsSimpleClosedGeodesicOf Γ p (C j)) ∧ (∀ i j, C i = C j ∨ Disjoint (C i) (C j)) ∧
      frontier P = ⋃ j, C j

/-- **Unlabelled claim** (Ch. 3 §3.1.4, IT1:1674). Cut `R` along a family `Y` of mutually disjoint simple closed geodesics; if
a relatively compact component `W` of the complement contains no further simple closed geodesic of `R`, then `W` is triply
connected, i.e. homeomorphic to `pantsModel`. -/
theorem para3_1_4_a {R : Type} [TopologicalSpace R] [ChartedSpace ℂ R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → R} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {Y : Set (Set R)}
    (hY : References.IsGeodesicMulticurve Γ p Y) {x : R} (hx : x ∉ ⋃₀ Y)
    (hW : IsCompact (closure (connectedComponentIn (⋃₀ Y)ᶜ x)))
    (hno : ¬∃ C : Set R, IsSimpleClosedGeodesicOf Γ p C ∧ C ⊆ connectedComponentIn (⋃₀ Y)ᶜ x) :
    Nonempty (↥(connectedComponentIn (⋃₀ Y)ᶜ x) ≃ₜ ↥pantsModel) := by
  sorry

/-- The subgroup `Γ_{P̃} = {γ ∈ Γ : γ(P̃) = P̃}` of `Γ` stabilizing a subset `S` of `ℍ`. -/
def stabSubgroup (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (S : Set UpperHalfPlane) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) where
  carrier := {γ | γ ∈ Γ ∧ (fun z => γ • z) '' S = S}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Γ.mul_mem ha hb, ?_⟩
    have : (fun z => (a * b) • z) '' S = (fun z => a • z) '' ((fun z => b • z) '' S) := by
      rw [Set.image_image]
      simp only [mul_smul]
    rw [this, hb', ha']
  one_mem' := ⟨Γ.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Γ.inv_mem ha, ?_⟩
    calc (fun z => a⁻¹ • z) '' S = (fun z => a⁻¹ • z) '' ((fun z => a • z) '' S) := by rw [ha']
      _ = S := by rw [Set.image_image]; simp

/-- **Nielsen extension** `P̂ = ℍ/Γ_{P̃}` of a pair of pants (Ch. 3 §3.1.4, IT1:1687): the orbit space of the stabilizer of a
component `P̃` of the preimage of `P`. (`P` is its Nielsen kernel.) -/
def NielsenExtension (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (S : Set UpperHalfPlane) : Type :=
  Quot fun z w : UpperHalfPlane => ∃ γ ∈ stabSubgroup Γ S, γ • z = w

/-- **Unlabelled claim** (Ch. 3 §3.1.4, IT1:1685). For a pair of pants `P` of `R = ℍ/Γ` and a component `P̃` of
`p⁻¹(P)`, the stabilizer `Γ_{P̃}` is a free group generated by two hyperbolic transformations, and `P = P̃/Γ_{P̃}`
(`p` maps `P̃` onto `P` and identifies exactly the `Γ_{P̃}`-equivalent points).
**Correction** (IT-fix2, audit AUDIT3_IT finding 4): the group `Γ_{P̃}` of Möbius maps is free; in `SL(2, ℝ)` the stabilizer contains
`−1` whenever `−1 ∈ Γ` (it fixes every set), and a free group has no element of order two. So the generation is read modulo `±1`
(`Γ_{P̃} · ⟨−1⟩ = ⟨A, B⟩ · ⟨−1⟩`) and `⟨A, B⟩` is the free lift; no hypothesis `−1 ∉ Γ` is added. -/
theorem para3_1_4_b {R : Type} [TopologicalSpace R] [ChartedSpace ℂ R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → R} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {P : Set R}
    (hP : IsPantsOf Γ p P) {z₀ : UpperHalfPlane} (hz₀ : p z₀ ∈ P)
    {S : Set UpperHalfPlane} (hS : S = connectedComponentIn (p ⁻¹' P) z₀) :
    (∃ A B : Matrix.SpecialLinearGroup (Fin 2) ℝ, IsHyperbolic A ∧ IsHyperbolic B ∧
      stabSubgroup Γ S ⊔ Subgroup.zpowers (-1) = Subgroup.closure {A, B} ⊔ Subgroup.zpowers (-1) ∧
      ∃ e : FreeGroup (Fin 2) ≃* ↥(Subgroup.closure {A, B}), e (FreeGroup.of 0) = ⟨A, Subgroup.subset_closure (by simp)⟩ ∧
        e (FreeGroup.of 1) = ⟨B, Subgroup.subset_closure (by simp)⟩) ∧
    p '' S = P ∧ ∀ z ∈ S, ∀ w ∈ S, p z = p w → ∃ γ ∈ stabSubgroup Γ S, γ • z = w := by
  sorry

/-- **Unlabelled claim** (Ch. 3 §3.1.4, IT1:1689). `P` is the unique pair of pants of its Nielsen extension `P̂ = ℍ/Γ_{P̃}`
(for the covering group `Γ_{P̃}` and the quotient map). -/
theorem para3_1_4_c {R : Type} [TopologicalSpace R] [ChartedSpace ℂ R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → R} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {P : Set R}
    (hP : IsPantsOf Γ p P) {z₀ : UpperHalfPlane} (hz₀ : p z₀ ∈ P)
    {S : Set UpperHalfPlane} (hS : S = connectedComponentIn (p ⁻¹' P) z₀) (Q : Set (NielsenExtension Γ S)) :
    IsPantsOf (stabSubgroup Γ S) (fun z => (Quot.mk _ z : NielsenExtension Γ S)) Q →
      Q = (fun z => (Quot.mk _ z : NielsenExtension Γ S)) '' S := by
  sorry

/-! ## §3.1.5 Existence and uniqueness of pairs of pants -/

/-- **Theorem 3.4** (Ch. 3 §3.1.5). For every triple `(a₁, a₂, a₃)` of positive numbers there is a Fuchsian model of a pair of
pants: a trouser core `ℍ ⊇ C`, `C/Γ`, with oriented boundary classes `A, B, C ∈ Γ` of translation lengths `a₁, a₂, a₃`
(`References.IsTrouserCoreWithLengths`: `⟨A, B⟩ = Γ`, `ABC = ±1`, the surface on the left of each axis). Modelling: Imayoshi–
Taniguchi's triply connected planar surface `Ω` with its pair of pants `P`; the boundary geodesics of `P` have the lengths
`a_j`. -/
theorem thm3_4 {a₁ a₂ a₃ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) (h₃ : 0 < a₃) :
    ∃ (S : HypSurfBdry) (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ), IsTrouserCoreWithLengths S A B C a₁ a₂ a₃ := by
  sorry

/-- **Theorem 3.5** (Ch. 3 §3.1.5). The complex structure of a pair of pants is uniquely determined by the hyperbolic lengths of
its ordered boundary components: if two trousers have oriented boundary classes `(A, B, C)`, `(A', B', C')` with equal lengths
`a_j > 0`, then the triples are conjugate in `SL(2, ℝ)` up to the sign of the lift (so that the identity of `ℍ`
conjugated by `T` is a conformal map of the pairs of pants taking `L_j` to `L'_j`). -/
theorem thm3_5 {a₁ a₂ a₃ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) (h₃ : 0 < a₃) {S S' : HypSurfBdry}
    {A B C A' B' C' : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hS : IsTrouserCoreWithLengths S A B C a₁ a₂ a₃)
    (hS' : IsTrouserCoreWithLengths S' A' B' C' a₁ a₂ a₃) :
    ∃ T : Matrix.SpecialLinearGroup (Fin 2) ℝ, (T * A * T⁻¹ = A' ∨ T * A * T⁻¹ = -A') ∧
      (T * B * T⁻¹ = B' ∨ T * B * T⁻¹ = -B') ∧ (T * C * T⁻¹ = C' ∨ T * C * T⁻¹ = -C') := by
  sorry

/-- **Anti-holomorphic map** between Riemann surfaces: continuous, and in local charts `conj ∘ (chart ∘ f ∘ chart⁻¹)` is
holomorphic at the chart image of every point. -/
def IsAntiholomorphicMap {A B : Type} [TopologicalSpace A] [ChartedSpace ℂ A] [TopologicalSpace B] [ChartedSpace ℂ B]
    (f : A → B) : Prop :=
  Continuous f ∧ ∀ x : A, DifferentiableAt ℂ (fun z => conj (chartAt ℂ (f x) (f ((chartAt ℂ x).symm z)))) (chartAt ℂ x x)

/-- **Corollary to Theorem 3.5 (reflection `J_P` of a pair of pants) [weaker]** (Ch. 3 §3.1.5, IT1:1799, and the definition at IT1:1805).
Every pair of pants `P` (an open subsurface of `R`) has an anti-holomorphic automorphism `J_P` of order two, which is not the
identity. Modelling: the description of the fixed-point set `F_{J_P}` as three geodesics orthogonal to the boundary is not
formalized (no notion of geodesic arc of `P` is available). -/
theorem thm3_5_cor {R : Type} [TopologicalSpace R] [ChartedSpace ℂ R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → R} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    (P : TopologicalSpace.Opens R) (hP : IsPantsOf Γ p (P : Set R)) :
    ∃ J : ↥P ≃ₜ ↥P, (∀ x, J (J x) = x) ∧ IsAntiholomorphicMap J ∧ ∃ x, J x ≠ x := by
  sorry

end ImayoshiTaniguchi1992
