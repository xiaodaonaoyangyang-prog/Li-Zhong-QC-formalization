import References.ImayoshiTaniguchi1992.Ch04.S02_BeltramiEquation
import LiZhongQC.Ch05.S21_UniversalTeichmuller

/-!
# Imayoshi–Taniguchi, Chapter 4 §4.3: Dependence on Beltrami coefficients (W2 batch I2)

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 4 §4.3 (`full.md` IT1:3540–3860,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Conventions: as in `Ch04/S02_BeltramiEquation`. The canonical `μ`-quasiconformal mapping `f^μ` of `Ĉ` (IT Theorem 4.30: the quasiconformal
map with complex dilatation `μ` fixing `0, 1, ∞`) is `LiZhongQC.normalizedSolution μ` (exactly `LiZhongQC.IsNormalizedSolution`, whose
existence for `‖μ‖∞ < 1` is `LiZhongQC.thm13_7_normalized_existence`); `B(ℂ)₁` is the set of measurable `μ` with `‖μ‖∞ < 1`
(`LiZhongQC.IsBeltramiCoeff μ univ k`, `k < 1`). The derivatives `(f^μ)_z`, `(f^μ)_z̄` are the almost everywhere derivatives
`LiZhongQC.dz`, `LiZhongQC.dzbar` (`f^μ` is differentiable a.e.). `‖h‖_{p,Δ}` is the `L^p` norm over the unit disc `Δ`.

* Proposition 4.36 (`f^μ → id` locally uniformly as `μ → 0`) — exists: `LiZhongQC.thm13_8_ahlfors_bers_continuous`
* Lemma 4.34 (`‖(f^μ)_z − 1‖_{p,Δ} → 0` as `‖μ‖∞ → 0`) — `lemma4_34`
* Lemma 4.35 (the integral formula (4.29) for `f^μ`) — `lemma4_35`
* Theorem 4.37 (first-order expansion of `f^{μ(t)}`) — `thm4_37`
* Corollary to Theorem 4.37 (the derivative of `f^{μ(t)}` for differentiable `μ(t)`) — `cor4_37`
* Lemma 4.41 (`log C_p` is convex in `1/p`) — exists: `LiZhongQC.thm11_2_riesz_thorin`

Omitted (U−): Lemmas 4.38, 4.39, 4.40 (Riesz' bound for the Hilbert transform, `‖Sφ‖_p ≤ (π/2) A_p ‖φ‖_p`, `T = −S∘S`): the
analytic estimates of §4.4 behind the constant `C_p` (the constant itself is `LiZhongQC.hilbertNorm`, Proposition 4.22).
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (normalizedSolution IsBeltramiCoeff hilbertNorm dz dzbar)

/-- **Lemma 4.34** (Ch. 4 §4.3.1, IT1:3542). For every `p > 2`, `‖(f^μ)_z − 1‖_{p,Δ} → 0` as `‖μ‖∞ → 0`, where `μ ∈ B(ℂ)₁`:
for every `ε > 0` there is `δ > 0` with `‖(f^μ)_z − 1‖_{p,Δ} < ε` for all `μ` with `‖μ‖∞ ≤ δ`. -/
theorem lemma4_34 {p : ℝ} (hp : 2 < p) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℂ → ℂ, IsBeltramiCoeff μ univ δ →
      eLpNorm (fun z => dz (normalizedSolution μ) z - 1) (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : ℂ) 1)) <
        ENNReal.ofReal ε := by
  sorry

/-- **Lemma 4.35** (Ch. 4 §4.3.2, IT1:3622). Fix `p` with `p > 8` arbitrarily. Let `μ` be an element of `B(ℂ)₁` satisfying
`‖μ‖∞ · C_p < 1`. Then the canonical `μ`-quasiconformal mapping `f^μ` of `Ĉ` satisfies the integral formula (4.29)
`f^μ(ζ) = ζ − (1/π) ∬_Δ (f^μ)_z̄(z) (1/(z − ζ) − ζ/(z − 1) + (ζ − 1)/z) dx dy
  − (1/π) ∬_Δ ((f̌^μ)_z̄(z)/(f̌^μ(z))²) (ζ² z/(1 − zζ) − ζ z/(1 − z)) dx dy` for every `ζ ∈ Δ`, where `f̌^μ(z) = 1/f^μ(1/z)`. -/
theorem lemma4_35 {p k : ℝ} (hp : 8 < p) (hk : 0 ≤ k) {μ : ℂ → ℂ} (hμ : IsBeltramiCoeff μ univ k) (hkp : k * hilbertNorm p < 1)
    {ζ : ℂ} (hζ : ζ ∈ Metric.ball (0 : ℂ) 1) :
    normalizedSolution μ ζ = ζ -
      (1 / Real.pi : ℂ) * (∫ z in Metric.ball (0 : ℂ) 1, dzbar (normalizedSolution μ) z *
        (1 / (z - ζ) - ζ / (z - 1) + (ζ - 1) / z)) -
      (1 / Real.pi : ℂ) * (∫ z in Metric.ball (0 : ℂ) 1,
        dzbar (fun w => 1 / normalizedSolution μ (1 / w)) z / (1 / normalizedSolution μ (1 / z)) ^ 2 *
          (ζ ^ 2 * z / (1 - z * ζ) - ζ * z / (1 - z))) := by
  sorry

/-- **Theorem 4.37** (Ch. 4 §4.3.3, IT1:3712). Let `{μ(t)}` be a family of Beltrami coefficients depending on a real or a complex
parameter `t`. Suppose that `‖μ(t)‖∞ → 0` as `t → 0`, and that `μ(t)` is differentiable at `t = 0`: `μ(t) = t ν + t ε(t)` with `ν`,
`ε(t) ∈ L^∞(ℂ)`, `‖ε(t)‖∞ → 0` as `t → 0`. Then `ḟ[ν](ζ) = lim_{t→0} (f^{μ(t)}(ζ) − ζ)/t` exists for every `ζ ∈ ℂ`, the
convergence is locally uniform on `ℂ`, and `ḟ[ν](ζ) = −(1/π) ∬_ℂ ν(z) ζ(ζ − 1)/(z(z − 1)(z − ζ)) dx dy`. -/
theorem thm4_37 {𝕜 : Type} [RCLike 𝕜] [NormedAlgebra 𝕜 ℂ] {μ : 𝕜 → ℂ → ℂ} {ν : ℂ → ℂ} {ε : 𝕜 → ℂ → ℂ}
    (hμ : ∀ᶠ t in 𝓝 (0 : 𝕜), ∃ k : ℝ, k < 1 ∧ IsBeltramiCoeff (μ t) univ k) (hlim : Tendsto (fun t => eLpNorm (μ t) ⊤ volume) (𝓝 0) (𝓝 0))
    (hν : MemLp ν ⊤ volume) (hε : ∀ᶠ t in 𝓝 (0 : 𝕜), MemLp (ε t) ⊤ volume) (hεlim : Tendsto (fun t => eLpNorm (ε t) ⊤ volume) (𝓝 0) (𝓝 0))
    (hexp : ∀ᶠ t in 𝓝 (0 : 𝕜), ∀ z, μ t z = t • ν z + t • ε t z) :
    TendstoLocallyUniformly (fun (t : 𝕜) (ζ : ℂ) => t⁻¹ • (normalizedSolution (μ t) ζ - ζ))
      (fun ζ => -(1 / Real.pi : ℂ) * ∫ z, ν z * (ζ * (ζ - 1) / (z * (z - 1) * (z - ζ)))) (𝓝[≠] 0) := by
  sorry

/-- **Corollary to Theorem 4.37** (Ch. 4 §4.3.3, IT1:3782). Let `{μ(t)}` be a family of Beltrami coefficients depending on a real or a
complex parameter `t`, differentiable at `t = 0`: `μ(t) = μ + t ν + t ε(t)` with `μ ∈ B(ℂ)₁`, `ν, ε(t) ∈ L^∞(ℂ)`,
`‖ε(t)‖∞ → 0`. Then `f^{μ(t)}(ζ) = f^μ(ζ) + t ḟ^μ[ν](ζ) + o(|t|)` locally uniformly on `ℂ` as `t → 0`, where
`ḟ^μ[ν](ζ) = −(1/π) ∬_ℂ ν(z) f^μ(ζ)(f^μ(ζ) − 1) ((f^μ)_z(z))² / (f^μ(z)(f^μ(z) − 1)(f^μ(z) − f^μ(ζ))) dx dy`. -/
theorem cor4_37 {𝕜 : Type} [RCLike 𝕜] [NormedAlgebra 𝕜 ℂ] {μ₀ : ℂ → ℂ} {μ : 𝕜 → ℂ → ℂ} {ν : ℂ → ℂ} {ε : 𝕜 → ℂ → ℂ} {k : ℝ} (hk : k < 1)
    (hμ₀ : IsBeltramiCoeff μ₀ univ k) (hμ : ∀ t, ∃ k : ℝ, k < 1 ∧ IsBeltramiCoeff (μ t) univ k) (hν : MemLp ν ⊤ volume)
    (hε : ∀ᶠ t in 𝓝 (0 : 𝕜), MemLp (ε t) ⊤ volume) (hεlim : Tendsto (fun t => eLpNorm (ε t) ⊤ volume) (𝓝 0) (𝓝 0))
    (hexp : ∀ᶠ t in 𝓝 (0 : 𝕜), ∀ z, μ t z = μ₀ z + t • ν z + t • ε t z) :
    TendstoLocallyUniformly
      (fun (t : 𝕜) (ζ : ℂ) => t⁻¹ • (normalizedSolution (μ t) ζ - normalizedSolution μ₀ ζ))
      (fun ζ => -(1 / Real.pi : ℂ) * ∫ z, ν z *
        (normalizedSolution μ₀ ζ * (normalizedSolution μ₀ ζ - 1) * dz (normalizedSolution μ₀) z ^ 2 /
          (normalizedSolution μ₀ z * (normalizedSolution μ₀ z - 1) * (normalizedSolution μ₀ z - normalizedSolution μ₀ ζ))))
      (𝓝[≠] 0) := by
  sorry

end ImayoshiTaniguchi1992
