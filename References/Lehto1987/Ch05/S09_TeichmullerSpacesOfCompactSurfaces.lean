import References.Lehto1987.Ch05.S08_UniquenessOfExtremalMappingsOfCompactSurfaces

/-!
# Lehto, Chapter V §9: Teichmüller spaces of compact surfaces

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. V §9 (`full.md`
P2:1737–1982).

Conventions (see §2, §5, §8). `S` is compact of genus `p > 1`, uniformized by `ℍ` (`p : ℍ → S`).
- `T_S` is `GardinerLakic2000.TeichSpace S p`, with the distance `GardinerLakic2000.teichDist` and the origin the class
  of the zero coefficient (hypothesis `0 ∈ beltramiBall S`).
- `Q_S` is `LiZhongQC.holQuadDiffSubmodule S`; its hyperbolic sup norm is that of the lift to `ℍ` (`hypSupNormRS`).
- The coefficients `k φ̄/|φ|` are `LiZhongQC.teichmullerBeltrami k φ`; a class `[k φ̄/|φ|]` is that of any element of
  `beltramiBall S` equal to this coefficient.
- The complex structure of `T_S` is that of §5 on the lifted model `LiZhongQC.TeichGamma Γ` (charts `IsBersChart`).
  A map `f : D → T_S` is holomorphic when it is so in these charts, pointwise on `𝕃`.

* Definition (the space `Q_S`, §9.1) — exists: `LiZhongQC.holQuadDiffSubmodule`
* Definition (the hyperbolic sup norm on `Q_S`, §9.1) — `hypSupNormRS`
* Unlabelled (§9.1, P2:1745–1751): every `p ∈ T_S` is `[kφ̄/|φ|]` with `‖φ‖ = 1`, uniquely for `p ≠ 0` —
  `para5_9_1`
* Theorem 9.1 (§9.1, Teichmüller imbedding) — `thm5_9_1`
* Formula (9.1) (§9.1) — `thm5_9_1` (the imbedding)
* Theorem 9.2 (§9.2) — exists: `LiZhongQC.thm29_1` (onto the unit ball of ℝ^(6p−6), for any linear isomorphism of
  Q_S, i.e. any basis)
* Formula (9.2) (§9.2) — exists: `LiZhongQC.thm29_1`
* Unlabelled (§9.2, P2:1807–1811): `T_S ≅ ℝ^{6p−6}`; the case `p = 1`; contractibility — omitted: U−
* Definition (straight line in `T_S`, §9.3) — `IsStraightLineT`
* Unlabelled (§9.3, P2:1815–1835): `x ↦ [(tanh x) φ̄/|φ|]` is a straight line through the origin — `para5_9_3_a`
* Unlabelled (§9.3, P2:1839): any two points of `T_p` lie on a straight line — `para5_9_3_b`
* Unlabelled (§9.4, P2:1845–1853): `f⁻¹` is a Teichmüller mapping for `(−ψ, k)` with terminal differential
  `−K²φ` — `para5_9_4`
* Formula (9.3) (§9.4) — `para5_9_4`
* Lemma 9.1 (§9.4) — `lemma5_9_1`
* Formula (9.4) (§9.4) — omitted: a step of the proof of Lemma 9.1
* Formula (9.5) (§9.4) — omitted: the dilatation of `f₂ ∘ f₁⁻¹`, a step
* Unlabelled (§9.4, P2:1880–1890): the maximal dilatations `K₁K₂` and `max(K₁/K₂, K₂/K₁)` — omitted: not cited
* Definition (Teichmüller disc, §9.5) — `para5_9_5`, `thm5_9_3` (stated through the map (9.6) whose image it is)
* Formula (9.6) (§9.5) — `para5_9_5`
* Unlabelled (§9.5, P2:1892–1894): `z ↦ [zφ̄/|φ|]` is injective and holomorphic — `para5_9_5`
* Theorem 9.3 (§9.5) — `thm5_9_3`
* Formula (9.7) (§9.6) — `eq5_9_7`
* Definition (hyperbolic distance of a disc-covered Riemann surface, §9.6) — `hypDistRS`
* Definition (Kobayashi pseudometric, §9.6) — `kobayashiPseudometric`
* Theorem 9.4 (§9.6, Royden) — `thm5_9_4`
* Formula (9.8) (§9.6) — omitted: a step of the proof of Theorem 9.4
* Unlabelled (§9.6, P2:1962, Royden): `Mod(S)` is the full group of biholomorphic automorphisms of `T_p`, `p > 1` —
  `para5_9_6`
* Unlabelled (§9.6, P2:1964–1966): consequences; the Teichmüller imbedding is not holomorphic — omitted: not cited
* Definition (surface of finite type, type `(p, n)`, punctures, §9.7) — exists: `LiZhongQC.IsFiniteType` (genus p,
  n punctures, m discs removed; type (p, n) is m = 0)
* Unlabelled (§9.7, P2:1974): a surface of type `(p, n)` has the disc as universal covering surface iff
  `2p − 2 + n > 0` — `para5_9_7`
* Theorem 9.5 (§9.7) — `thm5_9_5`
* Unlabelled (§9.7, P2:1980–1982): isomorphic spaces for type `(p, n)`; reduced spaces — omitted: remarks
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace Lehto1987

universe u

open LiZhongQC (toExt upperHalf lowerHalf unitDisc IsUniformization IsFuchsian ActsFreely HasGenus IsHolQuadDiff
  holQuadDiffSubmodule IsTeichmullerMap teichmullerBeltrami BeltramiGamma TeichGamma teichSetoidGamma
  teichDistanceGamma bersFunction IsFiniteType IsBiholomorphic)
open GardinerLakic2000 (beltramiBall teichRel TeichSpace liftQD liftBeltrami)
open Gehring1978 (hypNorm)

/-! ## §9.1 Teichmüller imbedding -/

/-- **Definition** (the hyperbolic sup norm `‖φ‖ = sup |φ|/η²` on `Q_S`, Ch. V §9.1): the norm of the lift of `φ` to
the universal covering surface `ℍ` (Lehto's density). -/
def hypSupNormRS {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (p : ℍ → S) (φ : S → ℂ → ℂ) : ℝ≥0∞ :=
  hypNorm (liftQD p φ) (toExt upperHalf)

/-- **Unlabelled** (Ch. V §9.1, P2:1745–1751). Every point of `T_S` has the representation `[kφ̄/|φ|]` with
`φ ∈ Q_S`, `‖φ‖ = 1` and `0 ≤ k < 1`; for points `≠ 0` the pair `(φ, k)` is unique. -/
theorem para5_9_1 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    (h0 : (0 : S → ℂ → ℂ) ∈ beltramiBall S) (P : TeichSpace S p) :
    (∃ (φ : S → ℂ → ℂ) (k : ℝ) (μ : beltramiBall S), φ ∈ holQuadDiffSubmodule S ∧ hypSupNormRS p φ = 1 ∧
      0 ≤ k ∧ k < 1 ∧ μ.1 = teichmullerBeltrami k φ ∧ Quot.mk (teichRel p) μ = P) ∧
    (P ≠ Quot.mk (teichRel p) ⟨0, h0⟩ → ∀ (φ φ' : S → ℂ → ℂ) (k k' : ℝ) (μ μ' : beltramiBall S),
      φ ∈ holQuadDiffSubmodule S → φ' ∈ holQuadDiffSubmodule S → hypSupNormRS p φ = 1 → hypSupNormRS p φ' = 1 →
      μ.1 = teichmullerBeltrami k φ → μ'.1 = teichmullerBeltrami k' φ' →
      Quot.mk (teichRel p) μ = P → Quot.mk (teichRel p) μ' = P → 0 < k → 0 < k' → k = k' ∧ φ = φ') := by
  sorry

/-- **Theorem 9.1** (Ch. V §9.1, Teichmüller imbedding). The mapping `[kφ̄/|φ|] ↦ kφ` (9.1), `φ ∈ Q_S`, `‖φ‖ = 1`,
`0 ≤ k < 1`, is a homeomorphism of `T_S` onto the open unit ball of `Q_S`.
Modelling: a map `E` with these values, bijective onto `{ψ ∈ Q_S | ‖ψ‖ < 1}`, continuous both ways (`ε–δ`, `τ` and
the sup norm) (near miss: `LiZhongQC.thm29_1`, a Euclidean norm). -/
theorem thm5_9_1 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) :
    ∃ E : TeichSpace S p → S → ℂ → ℂ,
      (∀ (φ : S → ℂ → ℂ) (k : ℝ) (μ : beltramiBall S), φ ∈ holQuadDiffSubmodule S → hypSupNormRS p φ = 1 →
        0 ≤ k → k < 1 → μ.1 = teichmullerBeltrami k φ → E (Quot.mk (teichRel p) μ) = (k : ℂ) • φ) ∧
      BijOn E univ {ψ | ψ ∈ holQuadDiffSubmodule S ∧ hypSupNormRS p ψ < 1} ∧
      (∀ P, ∀ ε > 0, ∃ δ > 0, ∀ Q, GardinerLakic2000.teichDist p P Q < δ →
        hypSupNormRS p (E P - E Q) < ENNReal.ofReal ε) ∧
      ∀ P, ∀ ε > 0, ∃ δ > 0, ∀ Q, hypSupNormRS p (E P - E Q) < ENNReal.ofReal δ →
        GardinerLakic2000.teichDist p P Q < ε := by
  sorry

/-! ## §9.3 Straight lines in Teichmüller space -/

/-- **Definition** (straight line in `T_S`, Ch. V §9.3): an isometry of the real axis into `T_S`. -/
def IsStraightLineT {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (p : ℍ → S) (L : ℝ → TeichSpace S p) :
    Prop :=
  ∀ x y : ℝ, GardinerLakic2000.teichDist p (L x) (L y) = |x - y|

/-- **Unlabelled** (Ch. V §9.3, P2:1815–1835). For `φ ∈ Q_S`, `φ ≠ 0`, the path `x ↦ [(tanh x) φ̄/|φ|]`,
`−∞ < x < ∞`, is a straight line in `T_S` through the origin.
Modelling: `L` given on the classes of the coefficients `(tanh x) φ̄/|φ|`. -/
theorem para5_9_3_a {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {φ : S → ℂ → ℂ}
    (hφ : φ ∈ holQuadDiffSubmodule S) (hne : φ ≠ 0) (h0 : (0 : S → ℂ → ℂ) ∈ beltramiBall S)
    {L : ℝ → TeichSpace S p}
    (hL : ∀ (x : ℝ) (μ : beltramiBall S), μ.1 = teichmullerBeltrami (Real.tanh x) φ → L x = Quot.mk (teichRel p) μ) :
    IsStraightLineT p L ∧ L 0 = Quot.mk (teichRel p) ⟨0, h0⟩ := by
  sorry

/-- **Unlabelled** (Ch. V §9.3, P2:1839). In the Teichmüller space `T_p`, any two points lie on a straight line. -/
theorem para5_9_3_b {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (P Q : TeichSpace S p) :
    ∃ (L : ℝ → TeichSpace S p) (x y : ℝ), IsStraightLineT p L ∧ L x = P ∧ L y = Q := by
  sorry

/-! ## §9.4 Composition of Teichmüller mappings -/

/-- **Unlabelled** (Ch. V §9.4, P2:1845–1853) and (9.3). If `f : S → S′` is a Teichmüller mapping determined by
`(φ, k)` with terminal differential `ψ`, then `f⁻¹` is a Teichmüller mapping determined by `(−ψ, k)`, and its terminal
differential is `−K²φ`, `K = (1 + k)/(1 − k)`. -/
theorem para5_9_4 {S S' : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] [TopologicalSpace S'] [T2Space S'] [ConnectedSpace S']
    [ChartedSpace ℂ S'] [IsManifold 𝓘(ℂ) ω S'] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) {f : S ≃ₜ S'}
    {φ : S → ℂ → ℂ} {ψ : S' → ℂ → ℂ} {k : ℝ} (hf : IsTeichmullerMap f φ ψ k) :
    IsTeichmullerMap f.symm (-ψ) (-((((1 + k) / (1 - k)) ^ 2 : ℝ) : ℂ) • φ) k := by
  sorry

/-- **Lemma 9.1** (Ch. V §9.4). Let `f₁ : S → S₁` and `f₂ : S → S₂` be Teichmüller mappings determined by `(φ₁, k₁)`
and `(φ₂, k₂)` such that `φ₂/φ₁` is a constant. Then `f₂ ∘ f₁⁻¹` is a Teichmüller mapping; up to constants, its
initial differential agrees with that of `f₁⁻¹` and its terminal differential with that of `f₂`.
Modelling: `f₂ ∘ f₁⁻¹` is `LiZhongQC.IsTeichmullerMap` for some `k`, with initial differential a non-zero multiple of
`−ψ₁` (the initial differential of `f₁⁻¹`) and terminal differential a non-zero multiple of `ψ₂` (`k = 0` allowed). -/
theorem lemma5_9_1 {S S₁ S₂ : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] [TopologicalSpace S₁] [T2Space S₁] [ConnectedSpace S₁]
    [ChartedSpace ℂ S₁] [IsManifold 𝓘(ℂ) ω S₁] [TopologicalSpace S₂] [T2Space S₂] [ConnectedSpace S₂]
    [ChartedSpace ℂ S₂] [IsManifold 𝓘(ℂ) ω S₂] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) {f₁ : S ≃ₜ S₁}
    {f₂ : S ≃ₜ S₂} {φ₁ φ₂ : S → ℂ → ℂ} {ψ₁ : S₁ → ℂ → ℂ} {ψ₂ : S₂ → ℂ → ℂ} {k₁ k₂ : ℝ}
    (h₁ : IsTeichmullerMap f₁ φ₁ ψ₁ k₁) (h₂ : IsTeichmullerMap f₂ φ₂ ψ₂ k₂) {c : ℂ} (hc : φ₂ = c • φ₁) :
    ∃ (k : ℝ) (a b : ℂ), a ≠ 0 ∧ b ≠ 0 ∧ IsTeichmullerMap (f₁.symm.trans f₂) (a • (-ψ₁)) (b • ψ₂) k := by
  sorry

/-! ## §9.5 Teichmüller discs -/

/-- **Unlabelled** (Ch. V §9.5, P2:1892–1894) and (9.6). For `φ ∈ Q_S`, `φ ≠ 0`, the mapping `z ↦ [zφ̄/|φ|]` of the
unit disc into `T_S` is injective and holomorphic.
The Teichmüller disc is used through this map, so it gets no definition of its own (in the lifted model it is
`GardinerLakic2000.teichmullerDisc`).
Modelling: injective on the classes; holomorphic: in the lifted model, the Bers imbedding of `[zφ̄/|φ|]` (through
lifted coefficients `ν z ∈ B(G)`) depends holomorphically on `z` at every point of `𝕃`. -/
theorem para5_9_5 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {φ : S → ℂ → ℂ}
    (hφ : φ ∈ holQuadDiffSubmodule S) (hne : φ ≠ 0) :
    (∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, ∀ μ₁ μ₂ : beltramiBall S,
      μ₁.1 = (fun x w => z₁ * conj (φ x w) / ‖φ x w‖) → μ₂.1 = (fun x w => z₂ * conj (φ x w) / ‖φ x w‖) →
      Quot.mk (teichRel p) μ₁ = Quot.mk (teichRel p) μ₂ → z₁ = z₂) ∧
    ∀ ν : ℂ → BeltramiGamma Γ, (∀ z ∈ unitDisc, ∀ᵐ w ∂(volume.restrict upperHalf),
      (ν z).1.1 w = liftBeltrami p (fun x v => z * conj (φ x v) / ‖φ x v‖) w) →
      ∀ w ∈ lowerHalf, DifferentiableOn ℂ (fun z => bersFunction (ν z).1.1 w) unitDisc := by
  sorry

/-- **Theorem 9.3** (Ch. V §9.5). The mapping `z ↦ [zφ̄/|φ|]` is an isometry of the hyperbolic unit disc (Lehto's
metric, closed formula) onto the Teichmüller disc determined by `φ`. -/
theorem thm5_9_3 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {φ : S → ℂ → ℂ}
    (hφ : φ ∈ holQuadDiffSubmodule S) (hne : φ ≠ 0) {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ unitDisc) (hz₂ : z₂ ∈ unitDisc)
    {μ₁ μ₂ : beltramiBall S} (hμ₁ : μ₁.1 = fun x w => z₁ * conj (φ x w) / ‖φ x w‖)
    (hμ₂ : μ₂.1 = fun x w => z₂ * conj (φ x w) / ‖φ x w‖) :
    GardinerLakic2000.teichDist p (Quot.mk (teichRel p) μ₁) (Quot.mk (teichRel p) μ₂) =
      (1 / 2) * Real.log ((‖1 - conj z₁ * z₂‖ + ‖z₁ - z₂‖) / (‖1 - conj z₁ * z₂‖ - ‖z₁ - z₂‖)) := by
  sorry

/-! ## §9.6 Complex structure and Teichmüller metric -/

/-- **Definition** (hyperbolic distance on a Riemann surface covered by the disc, Ch. IV §3.6 and V §9.6): the
infimum of the hyperbolic lengths (`hypLengthRS`) of the curves joining two points (not `Pommerenke1992.hypDistD`,
the distance of the disc itself). -/
def hypDistRS {S : Type u} [TopologicalSpace S] (p : ℍ → S) (a b : S) : ℝ≥0∞ :=
  ⨅ γ : Path a b, hypLengthRS p γ

/-- **Formula (9.7)** (Ch. V §9.6, Schwarz–Pick). If `f` maps the unit disc holomorphically into a Riemann surface `S`
which has the disc as universal covering surface, then `h(f(z₁), f(z₂)) ≤ h(z₁, z₂)`.
Modelling: the distance of `S` through its uniformization by `ℍ` (`hypDistRS`), Lehto's normalization; the disc
distance by its closed formula. -/
theorem eq5_9_7 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hp : IsUniformization Γ p) {f : ℂ → S} (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f unitDisc) {z₁ z₂ : ℂ}
    (hz₁ : z₁ ∈ unitDisc) (hz₂ : z₂ ∈ unitDisc) :
    hypDistRS p (f z₁) (f z₂) ≤
      ENNReal.ofReal ((1 / 2) * Real.log ((‖1 - conj z₁ * z₂‖ + ‖z₁ - z₂‖) / (‖1 - conj z₁ * z₂‖ - ‖z₁ - z₂‖))) := by
  sorry

/-- **Definition** (Kobayashi pseudometric, Ch. V §9.6): on a complex manifold `X`, the largest pseudometric `d` with
`d(f(z₁), f(z₂)) ≤ h(z₁, z₂)` for all holomorphic `f : D → X` and `z₁, z₂ ∈ D`.
Modelling: `X` is a type with a predicate `HolDisc` singling out the holomorphic maps of the disc; the supremum of
the admissible pseudometrics, `[0, ∞]`-valued; `h` is Lehto's hyperbolic distance of the disc. -/
def kobayashiPseudometric {X : Type*} (HolDisc : (ℂ → X) → Prop) (x y : X) : ℝ≥0∞ :=
  ⨆ (d : X → X → ℝ≥0∞) (_ : (∀ a, d a a = 0) ∧ (∀ a b, d a b = d b a) ∧ (∀ a b c, d a c ≤ d a b + d b c) ∧
    ∀ f, HolDisc f → ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, d (f z₁) (f z₂) ≤
      ENNReal.ofReal ((1 / 2) * Real.log ((‖1 - conj z₁ * z₂‖ + ‖z₁ - z₂‖) / (‖1 - conj z₁ * z₂‖ - ‖z₁ - z₂‖)))),
    d x y

/-- **Theorem 9.4** (Ch. V §9.6, Royden). In the Teichmüller space `T_p`, `p ≥ 1`, the hyperbolic (Kobayashi) metric
and the Teichmüller metric are the same.
Modelling: genus `p > 1` in the lifted model; a map `f : D → T_S` is holomorphic when, in every chart `h_μ` of §5,
`z ↦ h_μ(f(z))(w)` is holomorphic near every `z₀` with `f(z₀) ∈ V_μ`, for every `w ∈ 𝕃`, and `f` is continuous for
`τ_S` (the case `p = 1` is the disc model of §6). -/
theorem thm5_9_4 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    (h : BeltramiGamma Γ → TeichGamma Γ → ℂ → ℂ) (hh : ∀ μ, IsBersChart μ (h μ)) (P Q : TeichGamma Γ) :
    kobayashiPseudometric (fun f : ℂ → TeichGamma Γ =>
        (∀ z₀ ∈ unitDisc, ∀ ε > 0, ∃ δ > 0, ∀ z ∈ unitDisc, ‖z - z₀‖ < δ → teichDistanceGamma (f z) (f z₀) < ε) ∧
        ∀ μ : BeltramiGamma Γ, ∀ z₀ ∈ unitDisc, f z₀ ∈ bersDomainV (h μ) → ∃ r > (0 : ℝ),
          ∀ w ∈ lowerHalf, DifferentiableOn ℂ (fun z => h μ (f z) w) (Metric.ball z₀ r)) P Q =
      ENNReal.ofReal (teichDistanceGamma P Q) := by
  sorry

/-- **Unlabelled** (Ch. V §9.6, P2:1962, Royden). In `T_p`, `p > 1`, the modular group is the full group of
biholomorphic automorphisms.
Modelling: lifted model; a bijection `α` of `T_S` holomorphic in the charts of §5 (with holomorphic inverse) is the map
`α_μ` (4.11) of a lift `f^μ` of a quasiconformal self-mapping of `S` (`G^μ = G`).
**Correction** (Lehto-fix4, audit AUDITR2_Lehto note): the conclusion also asserts that for every `ν ∈ B(G)` a
representative `ν′ ∈ B(G)` of `α̃_μ ν` exists (true by `para5_5_4_a`, since `G^μ = G`), so that the clause on `ν′` cannot
hold vacuously. -/
theorem para5_9_6 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    (h : BeltramiGamma Γ → TeichGamma Γ → ℂ → ℂ) (hh : ∀ μ, IsBersChart μ (h μ)) {α : TeichGamma Γ → TeichGamma Γ}
    (hbij : Function.Bijective α)
    (hhol : ∀ ν₁ ν₂, ∃ G : (ℂ → ℂ) → ℂ → ℂ,
      IsHolomorphicFn (fun φ => hypNorm φ (toExt lowerHalf)) (fun φ => hypNorm φ (toExt lowerHalf))
        (h ν₁ '' (bersDomainV (h ν₁) ∩ α ⁻¹' bersDomainV (h ν₂))) G ∧
      ∀ P ∈ bersDomainV (h ν₁) ∩ α ⁻¹' bersDomainV (h ν₂), G (h ν₁ P) = h ν₂ (α P))
    (hholinv : ∀ ν₁ ν₂, ∃ G : (ℂ → ℂ) → ℂ → ℂ,
      IsHolomorphicFn (fun φ => hypNorm φ (toExt lowerHalf)) (fun φ => hypNorm φ (toExt lowerHalf))
        (h ν₁ '' (α '' bersDomainV (h ν₂) ∩ bersDomainV (h ν₁))) G ∧
      ∀ P ∈ bersDomainV (h ν₂), α P ∈ bersDomainV (h ν₁) → G (h ν₁ (α P)) = h ν₂ P) :
    ∃ μ : BeltramiGamma Γ, IsDeformationGroup Γ Γ μ.1.1 ∧
      ∀ ν : BeltramiGamma Γ, (∃ ν' : BeltramiGamma Γ, ∀ᵐ z : ℂ, ν'.1.1 z = alphaTilde μ.1.1 ν.1.1 z) ∧
        ∀ ν' : BeltramiGamma Γ, (∀ᵐ z : ℂ, ν'.1.1 z = alphaTilde μ.1.1 ν.1.1 z) →
          α (Quotient.mk (teichSetoidGamma Γ) ν) = Quotient.mk (teichSetoidGamma Γ) ν' := by
  sorry

/-! ## §9.7 Surfaces of finite type -/

/-- **Unlabelled** (Ch. V §9.7, P2:1974). A Riemann surface of type `(p, n)` admits the disc as universal covering
surface if and only if `2p − 2 + n > 0`.
Modelling: type `(p, n)` is `LiZhongQC.IsFiniteType S p n 0`; the disc covering is a uniformization by `ℍ`. -/
theorem para5_9_7 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {g n : ℕ} (hS : IsFiniteType S g n 0) :
    (∃ (Γ : Subgroup SL(2, ℝ)) (p : ℍ → S), IsFuchsian Γ ∧ ActsFreely Γ ∧ IsUniformization Γ p) ↔
      0 < 2 * (g : ℤ) - 2 + n := by
  sorry

/-- **Theorem 9.5** (Ch. V §9.7). The Teichmüller space of a Riemann surface of type `(p, n)`, `2p − 2 + n > 0`, is
homeomorphic to the euclidean space `ℝ^{6p−6+2n}`.
Modelling: a bijection onto `EuclideanSpace ℝ (Fin (6p + 2n − 6))` (no truncation: `6p + 2n ≥ 6` under the
hypothesis), continuous both ways (`ε–δ` for `τ`) (near miss: `LiZhongQC.teichDistanceFT_complete_metric`). -/
theorem thm5_9_5 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {g n : ℕ} (hS : IsFiniteType S g n 0) (hpos : 0 < 2 * (g : ℤ) - 2 + n)
    {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) :
    ∃ E : TeichSpace S p → EuclideanSpace ℝ (Fin (6 * g + 2 * n - 6)), Function.Bijective E ∧
      (∀ P, ∀ ε > 0, ∃ δ > 0, ∀ Q, GardinerLakic2000.teichDist p P Q < δ → dist (E P) (E Q) < ε) ∧
      ∀ P, ∀ ε > 0, ∃ δ > 0, ∀ Q, dist (E P) (E Q) < δ → GardinerLakic2000.teichDist p P Q < ε := by
  sorry

end Lehto1987
