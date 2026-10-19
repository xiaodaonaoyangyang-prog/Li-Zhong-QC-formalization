import References.Common.HyperbolicSurface
import References.GardinerLakic2000.Ch14.S04_GeneralizedAhlforsWeill

/-!
# Hubbard 2006, Chapter 6 §6.11: The Bers embedding is open (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H2` lines 3486–3575.

**Conventions.** The configuration is the installed `GardinerLakic2000.IsQCConfiguration C Ω Ω*` of a quasicircle `C`
through `∞` with complementary plane domains `Ω = D`, `Ω* = D*`, and the reflection `z ↦ z*` is
`GardinerLakic2000.IsReflectionGL C Ω Ω* j K` (a `K`-quasiconformal orientation reversing involution fixing `C`; the
equivariant reflection of Theorem 5.1.13, `thm5_1_13`, is such a reflection). The norm is `‖q‖_∞ = sup_{Ω} |q| / ρ_Ω²`
(`LiZhongQC.hyperbolicSupNorm`, `ρ_Ω = LiZhongQC.poincareDensity Ω`). The map `f` of equation (6.11.3) is
`f = w₁/w₂` on `D` and `(w₁(z*) + (z − z*) w₁'(z*)) / (w₂(z*) + (z − z*) w₂'(z*))` off `D`, with `w₁`, `w₂` solutions
of `w'' + q w / 2 = 0` with Wronskian `w₁ w₂' − w₂ w₁' = −1`; its values lie in `ℙ¹` (`ratioP1`).

* Thm 6.11.1 (the Bers embedding `Ψ_φ̃ : 𝒯_S → (Q^∞)^Γ(ℍ*)` is an open mapping) — deferred: needs the analytic structure
  of `𝒯_S` and the Bers embedding of a general quasiconformal surface `S` (with the ideal boundary)
* Thm 6.11.2 (for `‖q‖_∞ < ε(K)` the map `f` of (6.11.3) is a quasiconformal homeomorphism with the Beltrami
  coefficient (6.11.5)) — `ratioP1`, `thm6_11_2`
-/

open Set MeasureTheory
open scoped ComplexConjugate

namespace Hubbard2006

open LiZhongQC GardinerLakic2000

/-- The point `a / b` of `ℙ¹`, equal to `∞` if `b = 0`. -/
noncomputable def ratioP1 (a b : ℂ) : ExtPlane := if b = 0 then extInf else ((a / b : ℂ) : ExtPlane)

/-- **Theorem 6.11.2** (H2:3520). For `K ≥ 1` there is `ε > 0` and `K'`, depending only on `K`, such that for every
quasicircle configuration `(C, Ω, Ω*)` through `∞` with a `K`-quasireflection `j`, every holomorphic quadratic
differential `q` on `Ω` with `‖q‖_∞ < ε` and every pair of solutions `w₁`, `w₂` of `w'' + q w / 2 = 0` on `Ω` with
Wronskian `−1`, the map `f` of (6.11.3) (`f = w₁/w₂` on `Ω`, and the Möbius approximation at `z*` evaluated at `z`
on `Ω*`) is injective on `Ω ∪ Ω*`, `K'`-quasiconformal on `Ω*` (where finite), and its Beltrami coefficient on `Ω*` is
`q(z*) (z − z*)² (∂z*/∂z̄) / (2 + q(z*) (z − z*)² ∂z*/∂z)` (equation (6.11.5), `GardinerLakic2000.awSection`); on
`Ω` it is holomorphic, so the coefficient is `0`. -/
theorem thm6_11_2 (K : ℝ) :
    ∃ (ε K' : ℝ), 0 < ε ∧ ∀ (C : Set ExtPlane) (Ω Ωs : Set ℂ) (j : ℂ → ℂ) (q w₁ w₂ : ℂ → ℂ) (F : ℂ → ExtPlane),
      IsQCConfiguration C Ω Ωs → IsReflectionGL C Ω Ωs j K → DifferentiableOn ℂ q Ω →
      hyperbolicSupNorm q Ω < ENNReal.ofReal ε →
      DifferentiableOn ℂ w₁ Ω → DifferentiableOn ℂ w₂ Ω →
      (∀ z ∈ Ω, deriv (deriv w₁) z + q z * w₁ z / 2 = 0) → (∀ z ∈ Ω, deriv (deriv w₂) z + q z * w₂ z / 2 = 0) →
      (∀ z ∈ Ω, w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = -1) →
      (∀ z ∈ Ω, F z = ratioP1 (w₁ z) (w₂ z)) →
      (∀ z ∈ Ωs, F z = ratioP1 (w₁ (j z) + (z - j z) * deriv w₁ (j z)) (w₂ (j z) + (z - j z) * deriv w₂ (j z))) →
      InjOn F (Ω ∪ Ωs) ∧ IsKQC (fun z => extToC (F z)) {z | z ∈ Ωs ∧ F z ≠ extInf} K' ∧
        ∀ᵐ z ∂(volume.restrict Ωs), complexDilatation (fun w => extToC (F w)) z = awSection j q z := by
  sorry

end Hubbard2006
