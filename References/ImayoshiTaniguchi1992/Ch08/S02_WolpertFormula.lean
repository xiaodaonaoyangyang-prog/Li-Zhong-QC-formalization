import References.ImayoshiTaniguchi1992.Ch08.S01_FNDeformation

/-!
# Imayoshi–Taniguchi, Chapter 8 §8.2–§8.3: Gardiner's formula and Wolpert's formula

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 8 §8.2–§8.3 (`full.md`
IT2:1608–1968, folder `An Introduction to Teichmuller Spaces … 0ac64ea2`).

Conventions: as in `S01_FNDeformation`. Every point of `T(Γ)` is the base point of its own Fuchsian model, so the
statements are made **at the base point** of an arbitrary Fuchsian model `Γ` of a closed surface `S = ℍ/Γ` (genus `g ≥ 2`,
uniformization `p`); the tangent space is `B(H, Γ)/N(Γ)` (Beltrami differentials `μ ∈ Lehto1987.LinfG Γ`), the Weil–Petersson
metric at the base point is `g_WP(μ₁, μ₂) = 2 Re h(H[μ₁], H[μ₂])` (`gWPBase`), `ω_WP(μ₁, μ₂) = g_WP(iμ₁, μ₂)`
(`omegaWPBase`), and the differential of a function `f` is `dFn f μ = d/dt f(tμ)|_{t=0}` (`dFn`). `F` is a relatively compact
fundamental domain. The vector `∂/∂τ_C` is represented at the base point by `ν = fnTangentBeltrami` (8.1); the coordinate
vector `∂/∂ℓ_C` of a system of decomposing curves is characterized by `dℓ_k(∂/∂ℓ_j) = δ_{jk}`, `dτ_k(∂/∂ℓ_j) = 0`.
Wolpert's formula `ω_WP = Σ dτ_{C_j} ∧ dℓ_{C_j}` is stated as the values of `ω_WP` on this coordinate frame.
The elements `G, A, B ∈ Γ` of the Fenchel–Nielsen datum are given explicitly (`IsAdjacentPantsElements`, the conditions of
`ImayoshiTaniguchi1992.IsAdjacentPantsDatum` on explicit elements).

* Definition (geodesic length function `ℓ_C` and its differential `dℓ_C`, §8.2, IT2:1610) — exists: `ImayoshiTaniguchi1992.IsLengthFn`,
  `ImayoshiTaniguchi1992.dFn`
* Theorem 8.3 (Gardiner's formula, IT2:1622) — `thm8_3`
* Definition (FN vector field `∂/∂τ_C`, §8.3, IT2:1704) — exists: `ImayoshiTaniguchi1992.fnTangentBeltrami` (its representative at the
  base point)
* Definition (`g_WP`, `ω_WP` at the base point, Ch. 7 §7.3.2) — `gWPBase`, `omegaWPBase`
* Theorem 8.4 (`(i ∂/∂τ_C)^* = dℓ_C`, IT2:1712) — `thm8_4`
* Corollary to Theorem 8.4 (`ω_WP(∂/∂τ_C, ·) = dℓ_C`, IT2:1736) — `thm8_4_cor`
* Proposition 8.5 (reciprocity, IT2:1744) — `prop8_5`
* Theorem 8.6 (Wolpert's formula, IT2:1760) — `IsAdjacentPantsElements`, `thm8_6`
* Corollary to Theorem 8.6 (`ω_WP(∂/∂ℓ_C, ·) = -dτ_C`, IT2:1766) — `thm8_6_cor`
* Lemma 8.7 (IT2:1794) — deferred: needs the global Weil–Petersson 2-form on `T(R)` in Fenchel–Nielsen coordinates (the
  dependence of the coefficients `a_{ij}` on the point)
* Unlabelled (reflection-symmetric surfaces after FN deformations, IT2:1838) — deferred: needs the global Weil–Petersson 2-form and the
  mirror map on `T(R)`
* Definition (mirror surface `S*`, map `𝒥`, IT2:1842) — deferred: needs the conjugate atlas on marked surfaces and its action on `T(R)`
* Unlabelled (`𝒥` is an anti-holomorphic isometry fixing the base point, IT2:1869) — deferred: needs the mirror map
* Lemma 8.8 (a), (b), (c) ((8.10)–(8.12), IT2:1871) — deferred: needs the mirror map and the global Weil–Petersson form
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (upperHalf IsFuchsian ActsFreely IsUniformization IsCocompact HasGenus IsFundamentalDomainH IsHyperbolic Loop
  fMuSym)
open References (axisH IsSimpleClosedGeodesicOf)

/-- **`g_WP` at the base point** (Ch. 7 §7.3.2): `g_WP(μ₁, μ₂) = 2 Re h(H[μ₁], H[μ₂])` for `μ₁, μ₂ ∈ B(H, Γ)`, on the fundamental
domain `F`. -/
def gWPBase (F : Set ℂ) (μ₁ μ₂ : ℂ → ℂ) : ℝ := 2 * (hProd F (harmProj μ₁) (harmProj μ₂)).re

/-- **`ω_WP` at the base point**: `ω_WP(μ₁, μ₂) = g_WP(iμ₁, μ₂) = -2 Im h(H[μ₁], H[μ₂])`. -/
def omegaWPBase (F : Set ℂ) (μ₁ μ₂ : ℂ → ℂ) : ℝ := gWPBase F (fun z => Complex.I * μ₁ z) μ₂

/-- **Theorem 8.3 (Gardiner's formula)** (Ch. 8 §8.2). For a simple closed geodesic `C` of `R = H/Γ` covered by `γ₀ ∈ Γ`
(with finite real fixed points `a ≠ b`), the differential of the geodesic length function is
`(dℓ_C)_{p₀}(μ) = Re (μ, (2/π) Θ_C)_R` for every `μ ∈ B(H, Γ)`. -/
theorem thm8_3 {g : ℕ} {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hco : IsCocompact Γ)
    {γ₀ : Γ} (hh : IsHyperbolic γ₀) (hC : IsSimpleClosedGeodesicOf Γ p (p '' axisH γ₀)) {a b : ℝ} (hab : a ≠ b)
    (ha : mobH γ₀ a = a) (hb : mobH γ₀ b = b) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hFc : IsCompact (closure F))
    {ℓ : (ℂ → ℂ) → ℝ} (hℓ : IsLengthFn Γ γ₀ ℓ) {μ : ℂ → ℂ} (hμ : μ ∈ Lehto1987.LinfG Γ) :
    dFn ℓ μ = (pairingR F μ (fun z => ((2 / Real.pi : ℝ) : ℂ) * peterssonSeries Γ γ₀ a b z)).re := by
  sorry

/-- **Theorem 8.4** (Ch. 8 §8.3). For every simple closed geodesic `C`, `(i ∂/∂τ_C)^* = dℓ_C`: the Weil–Petersson metric dual of
the vector `i ∂/∂τ_C` (represented by `iν`) is the differential of the length function:
`g_WP(i ν, μ) = (dℓ_C)(μ)` for all `μ ∈ B(H, Γ)`. -/
theorem thm8_4 {g : ℕ} {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hco : IsCocompact Γ)
    {γ₀ : Γ} (hh : IsHyperbolic γ₀) (hC : IsSimpleClosedGeodesicOf Γ p (p '' axisH γ₀))
    {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : IsNormalizedBy A γ₀) {θ₀ : ℝ} (hθ : IsCollarAngle Γ γ₀ A θ₀)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hFc : IsCompact (closure F)) {ℓ : (ℂ → ℂ) → ℝ}
    (hℓ : IsLengthFn Γ γ₀ ℓ) {μ : ℂ → ℂ} (hμ : μ ∈ Lehto1987.LinfG Γ) :
    gWPBase F (fun z => Complex.I * fnTangentBeltrami Γ γ₀ A θ₀ z) μ = dFn ℓ μ := by
  sorry

/-- **Corollary to Theorem 8.4** (Ch. 8 §8.3). `ω_WP(∂/∂τ_C, ·) = dℓ_C(·)`. -/
theorem thm8_4_cor {g : ℕ} {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hco : IsCocompact Γ)
    {γ₀ : Γ} (hh : IsHyperbolic γ₀) (hC : IsSimpleClosedGeodesicOf Γ p (p '' axisH γ₀))
    {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : IsNormalizedBy A γ₀) {θ₀ : ℝ} (hθ : IsCollarAngle Γ γ₀ A θ₀)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hFc : IsCompact (closure F)) {ℓ : (ℂ → ℂ) → ℝ}
    (hℓ : IsLengthFn Γ γ₀ ℓ) {μ : ℂ → ℂ} (hμ : μ ∈ Lehto1987.LinfG Γ) :
    omegaWPBase F (fnTangentBeltrami Γ γ₀ A θ₀) μ = dFn ℓ μ := by
  sorry

/-- **Proposition 8.5 (reciprocity)** (Ch. 8 §8.3). For simple closed geodesics `C`, `C'` of `R`:
`∂ℓ_{C'}/∂τ_C = -∂ℓ_C/∂τ_{C'}`, i.e. `dℓ_{C'}(ν_C) = -dℓ_C(ν_{C'})`. -/
theorem prop8_5 {g : ℕ} {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hco : IsCocompact Γ)
    {γ₁ γ₂ : Γ} (hh₁ : IsHyperbolic γ₁) (hh₂ : IsHyperbolic γ₂) (hC₁ : IsSimpleClosedGeodesicOf Γ p (p '' axisH γ₁))
    (hC₂ : IsSimpleClosedGeodesicOf Γ p (p '' axisH γ₂)) {A₁ A₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hA₁ : IsNormalizedBy A₁ γ₁) (hA₂ : IsNormalizedBy A₂ γ₂) {θ₁ θ₂ : ℝ} (hθ₁ : IsCollarAngle Γ γ₁ A₁ θ₁)
    (hθ₂ : IsCollarAngle Γ γ₂ A₂ θ₂) {ℓ₁ ℓ₂ : (ℂ → ℂ) → ℝ} (hℓ₁ : IsLengthFn Γ γ₁ ℓ₁) (hℓ₂ : IsLengthFn Γ γ₂ ℓ₂) :
    dFn ℓ₂ (fnTangentBeltrami Γ γ₁ A₁ θ₁) = -dFn ℓ₁ (fnTangentBeltrami Γ γ₂ A₂ θ₂) := by
  sorry

/-- **The elements of the datum of Wolpert's formula** (Ch. 8 §8.3, Ch. 3 §3.2.3): the conditions of
`IsAdjacentPantsDatum` on explicit elements `G, A, B ∈ Γ` for the `j`-th curve of the decomposing system `L`: `G` hyperbolic
with `p '' axisH G = range (L j)`, two distinct lifted pants components `S₁`, `S₂` with `Γ_{S₁} = ⟨G, A⟩`, `Γ_{S₂} = ⟨G, B⟩` (modulo `±1`, IT-fix2) whose
closures contain `axisH G` and whose frontiers contain the axes of the hyperbolic `A`, `B`; with no junk for `footDisp`. -/
def IsAdjacentPantsElements {S : Type} [TopologicalSpace S] {N : ℕ} (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (p : UpperHalfPlane → S) (L : Fin N → Loop S) (j : Fin N)
    (G A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Prop :=
  G ∈ Γ ∧ A ∈ Γ ∧ B ∈ Γ ∧ IsFNElements G A B ∧ p '' axisH G = range ((L j).2 : unitInterval → S) ∧
    ∃ (y₁ y₂ : S) (w₁ w₂ : UpperHalfPlane),
      IsPantsOf Γ p (pantsComp L y₁) ∧ IsPantsOf Γ p (pantsComp L y₂) ∧ p w₁ ∈ pantsComp L y₁ ∧ p w₂ ∈ pantsComp L y₂ ∧
      pantsLift p (pantsComp L y₁) w₁ ≠ pantsLift p (pantsComp L y₂) w₂ ∧
      axisH G ⊆ closure (pantsLift p (pantsComp L y₁) w₁) ∧ axisH G ⊆ closure (pantsLift p (pantsComp L y₂) w₂) ∧
      stabSubgroup Γ (pantsLift p (pantsComp L y₁) w₁) ⊔ Subgroup.zpowers (-1) = Subgroup.closure {G, A} ⊔ Subgroup.zpowers (-1) ∧
      stabSubgroup Γ (pantsLift p (pantsComp L y₂) w₂) ⊔ Subgroup.zpowers (-1) = Subgroup.closure {G, B} ⊔ Subgroup.zpowers (-1) ∧
      axisH A ⊆ frontier (pantsLift p (pantsComp L y₁) w₁) ∧ axisH B ⊆ frontier (pantsLift p (pantsComp L y₂) w₂)

/-- **Theorem 8.6 (Wolpert's formula)** (Ch. 8 §8.3). For a system of decomposing curves `{C_j}_{j=1}^{3g-3}` with Fenchel–Nielsen
coordinates `(ℓ_j, τ_j)` (`τ_j = (ℓ_j/2π) θ_j`): `ω_WP = Σ_j dτ_{C_j} ∧ dℓ_{C_j}`. Stated on the coordinate frame
`∂/∂τ_j = ν_j` (`fnTangentBeltrami`), `∂/∂ℓ_j = μ_j` (`dℓ_k(μ_j) = δ_{jk}`, `dτ_k(μ_j) = 0`): `dτ_k(ν_j) = ± δ_{jk}` with one global sign
(IT's convention [weaker: sign]), `dℓ_k(ν_j) = 0`, and
`ω_WP(ν_i, ν_k) = 0`, `ω_WP(ν_i, μ_k) = δ_{ik}`, `ω_WP(μ_i, μ_k) = 0`. -/
theorem thm8_6 {g : ℕ} {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hco : IsCocompact Γ)
    {L : Fin (3 * g - 3) → Loop S} (hL : IsDecomposingSystemLoops Γ p L) (G A B : Fin (3 * g - 3) → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hD : ∀ j, IsAdjacentPantsElements Γ p L j (G j) (A j) (B j)) (hGΓ : ∀ j, G j ∈ Γ)
    (N : Fin (3 * g - 3) → Matrix.SpecialLinearGroup (Fin 2) ℝ) (θ₀ : Fin (3 * g - 3) → ℝ)
    (hN : ∀ j, IsNormalizedBy (N j) (G j)) (hθ : ∀ j, IsCollarAngle Γ (G j) (N j) (θ₀ j))
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hFc : IsCompact (closure F))
    (ℓ τ : Fin (3 * g - 3) → (ℂ → ℂ) → ℝ) (hℓ : ∀ j, IsLengthFn Γ (G j) (ℓ j)) (hτ : ∀ j, IsTwistFn Γ (G j) (A j) (B j) (τ j))
    (μ : Fin (3 * g - 3) → ℂ → ℂ) (hμ : ∀ j, μ j ∈ Lehto1987.LinfG Γ)
    (hμℓ : ∀ j k, dFn (ℓ k) (μ j) = if j = k then 1 else 0) (hμτ : ∀ j k, dFn (τ k) (μ j) = 0) :
    (∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ j k, dFn (τ k) (fnTangentBeltrami Γ ⟨G j, hGΓ j⟩ (N j) (θ₀ j)) =
        if j = k then s else 0) ∧
      (∀ j k, dFn (ℓ k) (fnTangentBeltrami Γ ⟨G j, hGΓ j⟩ (N j) (θ₀ j)) = 0) ∧
      (∀ i k, omegaWPBase F (fnTangentBeltrami Γ ⟨G i, hGΓ i⟩ (N i) (θ₀ i)) (fnTangentBeltrami Γ ⟨G k, hGΓ k⟩ (N k) (θ₀ k)) = 0) ∧
      (∀ i k, omegaWPBase F (fnTangentBeltrami Γ ⟨G i, hGΓ i⟩ (N i) (θ₀ i)) (μ k) = if i = k then 1 else 0) ∧
      ∀ i k, omegaWPBase F (μ i) (μ k) = 0 := by
  sorry

/-- **Corollary to Theorem 8.6** (Ch. 8 §8.3). For every simple closed geodesic `C_j` of a decomposing system,
`ω_WP(∂/∂ℓ_{C_j}, ·) = -dτ_{C_j}(·)` (up to the global sign of IT's twist convention [weaker]). -/
theorem thm8_6_cor {g : ℕ} {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hco : IsCocompact Γ)
    {L : Fin (3 * g - 3) → Loop S} (hL : IsDecomposingSystemLoops Γ p L) (G A B : Fin (3 * g - 3) → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hD : ∀ j, IsAdjacentPantsElements Γ p L j (G j) (A j) (B j)) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (hFc : IsCompact (closure F)) (ℓ τ : Fin (3 * g - 3) → (ℂ → ℂ) → ℝ) (hℓ : ∀ j, IsLengthFn Γ (G j) (ℓ j))
    (hτ : ∀ j, IsTwistFn Γ (G j) (A j) (B j) (τ j)) (μ : Fin (3 * g - 3) → ℂ → ℂ) (hμ : ∀ j, μ j ∈ Lehto1987.LinfG Γ)
    (hμℓ : ∀ j k, dFn (ℓ k) (μ j) = if j = k then 1 else 0) (hμτ : ∀ j k, dFn (τ k) (μ j) = 0) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ j (X : ℂ → ℂ), X ∈ Lehto1987.LinfG Γ → omegaWPBase F (μ j) X = -s * dFn (τ j) X := by
  sorry

end ImayoshiTaniguchi1992
