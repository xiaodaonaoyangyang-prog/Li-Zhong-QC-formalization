import References.GardinerLakic2000.Ch14.S09_Contraction

/-!
# Gardiner–Lakic 2000, Ch. 14 §14.10 Extremality in `AT`

Source `teichmuller.txt`, lines 11061–11113.

* Definition (Teichmüller's metric on `AT`: `d([g], [f]) = ½ log H[f ∘ g⁻¹]`, l. 11073, 11117–11127) — `asymDist`
* Theorem 8 (boundary-dilatation extremality, [EGL98a], l. 11064) — `thm14_8`
* Theorem 9 (Teichmüller contraction, [EGL98a], l. 11081) — `thm14_9`

Not items (DESIGN §3): Beltrami curve, disk and line, "efficient at two points" and the contraction `d ≤ d_P`
(l. 11073–11079), not used in later statements.

**Modelling.** `asymDist` is defined here, before its first use in Theorem 9 (the inventory placed it in §14.11). As
Part A's `teichDist`, it is the infimum over representatives: `½ log H*(f₁ ∘ g₁⁻¹)` over quasiconformal `f₁`, `g₁`
whose coefficients lie in the two `AT`-classes, which is `½ log H[f ∘ g⁻¹]`. In Theorem 8 the supremum over
degenerating sequences of `limsup |∬ φₙ μ|` is `β(μ)` (`betaOf`). In Theorem 9, `d_P` is `LiZhongQC.discPoincareDist`
(`d_P(0, t) = ½ log((1 + t)/(1 − t))`), `K₁ = (1 + k₁)/(1 − k₁)` is `H*(k₁ μ)` (l. 11091), and the coefficients
`k₁ μ`, `t μ` lie in `M(R)` because `‖μ‖∞ < 1/k₂`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsQCRS IsFuchsian IsUniformization discPoincareDist)

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

/-- **Definition** (Teichmüller's metric on `AT`, §14.10 l. 11073, §14.11 l. 11117–11127).
`d(P, Q) = ½ inf log H*(f₁ ∘ g₁⁻¹)` over quasiconformal `f₁`, `g₁` with coefficients in the classes `P`, `Q`. -/
def asymDist (p : UpperHalfPlane → R) (P Q : AsymTeichSpace R p) : ℝ :=
  sInf {d | ∃ (μ ν : beltramiBall R) (Y₀ Y₁ : RSBundle.{u}) (f₁ : R ≃ₜ Y₀.carrier) (g₁ : R ≃ₜ Y₁.carrier),
    Quot.mk (asymRel p) μ = P ∧ Quot.mk (asymRel p) ν = Q ∧ IsQCRS f₁ ∧ IsQCRS g₁ ∧
      HasBeltramiCoeff f₁ μ.1 ∧ HasBeltramiCoeff g₁ ν.1 ∧
      d = 1 / 2 * Real.log (boundaryDilatationStarK
        (beltramiCoeffRS (f₁ ∘ g₁.symm : Y₁.carrier → Y₀.carrier))).toReal}

variable [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R]

/-- **Theorem 8** (condition for boundary-dilatation extremality, §14.10, l. 11064; [EGL98a]). `H*(f) = H(f)` if and
only if `h* = sup_{φₙ} limsup_n |∬_R φₙ μ|` over the degenerating sequences. -/
theorem thm14_8 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (hdeg : ∃ φ : ℕ → R → ℂ → ℂ, IsDegeneratingSeq φ) (μ : beltramiBall R) :
    boundaryDilatationStarK μ.1 = boundaryDilatationH p (Quot.mk (teichRel p) μ) ↔ hStarOf μ.1 = betaOf μ.1 := by
  sorry

/-- **Theorem 9** (Teichmüller contraction, §14.10, l. 11081; [EGL98a]). Let `b*(μ) = 1`, `0 < k₁ < k₂ < 1`,
`‖μ‖∞ < 1/k₂`, `0 < λ₁ < 1` and `d(0, [k₁ μ]) < λ₁ d_P(0, k₁)`. Then
`d(0, [t μ]) ≤ [1 − (δ/2)(1 − k₂)²] d_P(0, t)` for `0 ≤ t ≤ k₂`, with
`δ = (1 − k₁)² (K₁ − K₁^{λ₁}) / (8 K₁² k₁)`. -/
theorem thm14_9 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (h0 : (0 : R → ℂ → ℂ) ∈ beltramiBall R) {μ : R → ℂ → ℂ}
    (hμ : μ ∈ beltramiSpace R) (hμ1 : boundaryDilatationStar μ = 1) {k₁ k₂ lam₁ : ℝ} (hk₁ : 0 < k₁)
    (hk₁₂ : k₁ < k₂) (hk₂ : k₂ < 1) (hμk₂ : beltramiNormRS μ < ENNReal.ofReal (1 / k₂)) (hlam : 0 < lam₁)
    (hlam1 : lam₁ < 1)
    (hd : ∀ h : (fun x z => (k₁ : ℂ) * μ x z) ∈ beltramiBall R,
      asymDist p (Quot.mk (asymRel p) ⟨0, h0⟩) (Quot.mk (asymRel p) ⟨_, h⟩) < lam₁ * discPoincareDist 0 k₁) :
    let K₁ := (1 + k₁) / (1 - k₁)
    let δ := (1 - k₁) ^ 2 * (K₁ - K₁ ^ lam₁) / (8 * K₁ ^ 2 * k₁)
    ∀ t ∈ Icc (0 : ℝ) k₂, ∀ h : (fun x z => (t : ℂ) * μ x z) ∈ beltramiBall R,
      asymDist p (Quot.mk (asymRel p) ⟨0, h0⟩) (Quot.mk (asymRel p) ⟨_, h⟩) ≤
        (1 - δ / 2 * (1 - k₂) ^ 2) * discPoincareDist 0 t := by
  sorry

end GardinerLakic2000
