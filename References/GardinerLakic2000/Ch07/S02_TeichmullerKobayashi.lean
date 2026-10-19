import References.GardinerLakic2000.Ch07.S01_KobayashiMetric

/-!
# Gardiner–Lakic 2000, Ch. 7 §7.2 Teichmüller's and Kobayashi's metrics

Source `teichmuller.txt`, lines 6225–6283.

* Definition (holomorphic maps of `Δ` into `T(G)` and into `M(G)`, l. 6226–6227, 6293) — `holDiscsT`, `holDiscsM`
* Proposition 1 ((7.5), l. 6249) — `prop7_1`
* Unlabelled (§7.2: `σ ≤ d`, l. 6269–6271, and (7.7) `d ≤ σ`, l. 6278, proved in §7.3; Royden, Gardiner; cited in the
  Ch. 8 introduction, l. 6534) — `para7_2_kobayashi_eq_teich`

Not items (DESIGN §3): (7.4) and (7.6) (steps), the holomorphy of `Φ : M → T` (l. 6226, built into `holDiscsT`).

**[CORRECTION] (7.5)** (l. 6253; GL8:6093): `tanh⁻¹`, not `½ tanh⁻¹` (see §7.1).

**Conventions (B0.3).** The Fuchsian model: `M = M(G)` is `LiZhongQC.BeltramiGamma Γ` and `T = T(G)` is
`LiZhongQC.TeichGamma Γ` with `LiZhongQC.teichDistanceGamma` (the book identifies `T(R)` with it, l. 6313;
`para5_2_teichGamma_equiv`). A disc `f : Δ → T(G)` is holomorphic when its Bers image `t ↦ Φ̄(f(t))(z)` is holomorphic
for every `z ∈ 𝕃` (the Bers map is a global chart, Theorem 6.1; the image is bounded, so weak holomorphy is strong
holomorphy). A disc `g : Δ → M(G)` is holomorphic when `t ↦ ∬_ℍ g(t) ψ` is holomorphic for every `ψ ∈ L¹(ℍ)` (A0.6).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (unitDisc upperHalf lowerHalf discPoincareDist BeltramiGamma TeichGamma bersMapGamma
  teichDistanceGamma IsFuchsian)

/-- **Definition** (§7.2, l. 6226; via Theorem 6.1). The holomorphic discs of `T(G)`: `f` with
`t ↦ Φ̄(f(t))(z)` holomorphic on `Δ` for every `z` in the lower half-plane. -/
def holDiscsT (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set (ℂ → TeichGamma Γ) :=
  {f | ∀ z ∈ lowerHalf, DifferentiableOn ℂ (fun t => bersMapGamma Γ (f t) z) unitDisc}

/-- **Definition** (§7.2, l. 6226, 6293; A0.6). The holomorphic discs of `M(G)`: `g` with `t ↦ ∬_ℍ g(t) ψ`
holomorphic on `Δ` for every integrable `ψ` on `ℍ`. -/
def holDiscsM (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set (ℂ → BeltramiGamma Γ) :=
  {g | ∀ ψ : ℂ → ℂ, Integrable ψ (volume.restrict upperHalf) →
    DifferentiableOn ℂ (fun t => ∫ z in upperHalf, (g t).1.1 z * ψ z) unitDisc}

/-- **Proposition 1** ((7.5), §7.2, l. 6249). On the unit ball `M` of the essentially bounded Beltrami
differentials, `σ_M(μ, ν) = tanh⁻¹ ‖(μ − ν)/(1 − ν̄μ)‖∞` [CORRECTION]. Modelling: the Fuchsian model `M(G)`; the
norm is `LiZhongQC.UniversalTeichmuller.dilatationDiffNorm` (the essential supremum over `ℍ`). -/
theorem prop7_1 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (μ ν : BeltramiGamma Γ) :
    kobayashiPseudo (holDiscsM Γ) μ ν =
      ENNReal.ofReal (discPoincareDist 0 (LiZhongQC.UniversalTeichmuller.dilatationDiffNorm μ.1.1 ν.1.1 : ℂ)) := by
  sorry

/-- **Unlabelled** (§7.2, l. 6271 and (7.7), l. 6278; Royden [Roy71], Gardiner [Gar84a]). Kobayashi's and
Teichmüller's metrics coincide on every Teichmüller space: `σ_T = d`. -/
theorem para7_2_kobayashi_eq_teich {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (p q : TeichGamma Γ) :
    kobayashiPseudo (holDiscsT Γ) p q = ENNReal.ofReal (teichDistanceGamma p q) := by
  sorry

end GardinerLakic2000
