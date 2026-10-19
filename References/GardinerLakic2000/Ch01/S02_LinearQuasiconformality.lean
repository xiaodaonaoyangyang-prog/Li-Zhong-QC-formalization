import LiZhongQC
import References.Gehring1978.S1_Introduction
import References.Katok1992.Ch02.S03_AlgebraicProperties
import References.Common.RiemannSurface

/-!
# Gardiner–Lakic 2000, Ch. 1 §1.2 Linear quasiconformality

F. P. Gardiner, N. Lakic, *Quasiconformal Teichmüller Theory* (2000), Chapter 1 *Quasiconformal mapping*, §1.2
(and §1.1, which has no items); source `teichmuller.txt`, lines 395–549.

* Definition (dilatation `K(T) = K(μ) = (1 + |μ|)/(1 − |μ|)`, (1.6), l. 474; used throughout) — `dilatationK`
* Definition (complex dilatation `μ = B/A` of `T(z) = Az + B z̄`, l. 470) — exists: `LiZhongQC.complexDilatation`
  (applied to the real-linear map, whose Wirtinger derivatives are A and B)
* Formula (1.9) (the action (1.7) of real-linear maps on Δ, l. 485–520; cited in (1.16) and Exercise 3) — `eq1_9`
* Formula (1.10) (hyperbolic distance on Δ, l. 525) — exists: `LiZhongQC.discPoincareDist` (the same
  (1/2) log((1 + r)/(1 − r)), r the pseudo-hyperbolic distance)

Not items (DESIGN §3): (1.3) (l. 450), `d(0, μ) = ½ log K(μ)` (l. 533) and `K(T₂ ∘ T₁) ≤ K(T₂)K(T₁)` with its equality
clause (l. 548), not cited (U−; the general inequality is Proposition 1.1). Note: the equality clause "only if `μ_{T₂}`
is a positive multiple of `μ_{T₁}`" needs the rotation `A₁/Ā₁` of (1.9) (it holds as printed when `A₁` is real).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (complexDilatation)

/-- **Definition** ((1.6), §1.2, l. 474). The dilatation `K(μ) = (1 + |μ|)/(1 − |μ|)` of a complex number `μ`
(`|μ| < 1`); for a real-linear map `T` with complex dilatation `μ`, `K(T) = K(μ)` is the eccentricity of the image of
the unit circle. Junk value for `|μ| ≥ 1` (never read). -/
def dilatationK (μ : ℂ) : ℝ := (1 + ‖μ‖) / (1 - ‖μ‖)

/-- **Formula (1.9)** (§1.2, l. 485–520). For orientation-preserving real-linear maps `T(z) = Az + B z̄` and
`T₁(z) = A₁z + B₁ z̄` (`|B| < |A|`, `|B₁| < |A₁|`), with `μ = B/A`, `μ₁ = B₁/A₁`, the complex dilatation of `T ∘ T₁⁻¹`
is `((μ − μ₁)/(1 − μ̄₁ μ)) · (1/θ₁)`, `θ₁ = Ā₁/A₁`. The inverse is written out as on l. 503:
`T₁⁻¹(w) = (Ā₁ w − B₁ w̄)/(|A₁|² − |B₁|²)`. -/
theorem eq1_9 {A B A₁ B₁ : ℂ} (h : ‖B‖ < ‖A‖) (h₁ : ‖B₁‖ < ‖A₁‖) (w : ℂ) :
    complexDilatation
        (fun w => A * ((conj A₁ * w - B₁ * conj w) / ((‖A₁‖ ^ 2 - ‖B₁‖ ^ 2 : ℝ) : ℂ)) +
          B * conj ((conj A₁ * w - B₁ * conj w) / ((‖A₁‖ ^ 2 - ‖B₁‖ ^ 2 : ℝ) : ℂ))) w =
      (B / A - B₁ / A₁) / (1 - conj (B₁ / A₁) * (B / A)) * (A₁ / conj A₁) := by
  have hA : A ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    exact absurd h (not_lt.2 (norm_nonneg B))
  have hA₁ : A₁ ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h₁
    exact absurd h₁ (not_lt.2 (norm_nonneg B₁))
  have hcA₁ : conj A₁ ≠ 0 := fun hc => hA₁ (by simpa using congrArg conj hc)
  have hD : (0 : ℝ) < ‖A₁‖ ^ 2 - ‖B₁‖ ^ 2 :=
    sub_pos.2 (pow_lt_pow_left₀ h₁ (norm_nonneg _) two_ne_zero)
  set D : ℂ := ((‖A₁‖ ^ 2 - ‖B₁‖ ^ 2 : ℝ) : ℂ) with hDdef
  have hD0 : D ≠ 0 := by
    rw [hDdef]
    exact Complex.ofReal_ne_zero.2 hD.ne'
  have hnum : A * conj A₁ - B * conj B₁ ≠ 0 := by
    intro hz
    rw [sub_eq_zero] at hz
    have e : ‖A‖ * ‖A₁‖ = ‖B‖ * ‖B₁‖ := by
      have e := congrArg (‖·‖) hz
      rwa [norm_mul, norm_mul, norm_conj, norm_conj] at e
    have lt : ‖B‖ * ‖B₁‖ < ‖A‖ * ‖A₁‖ := mul_lt_mul'' h h₁ (norm_nonneg _) (norm_nonneg _)
    linarith
  have hden : 1 - conj B₁ / conj A₁ * (B / A) ≠ 0 := by
    intro hz
    rw [sub_eq_zero] at hz
    have h1 : ‖conj B₁ / conj A₁ * (B / A)‖ < 1 := by
      rw [norm_mul, norm_div, norm_div, norm_conj, norm_conj, div_mul_div_comm,
        div_lt_one (mul_pos (norm_pos_iff.2 hA₁) (norm_pos_iff.2 hA))]
      exact mul_lt_mul'' h₁ h (norm_nonneg _) (norm_nonneg _)
    rw [← hz, norm_one] at h1
    exact lt_irrefl 1 h1
  have hfun : (fun w => A * ((conj A₁ * w - B₁ * conj w) / D) +
        B * conj ((conj A₁ * w - B₁ * conj w) / D)) =
      fun w => (A * conj A₁ - B * conj B₁) / D * w + (B * A₁ - A * B₁) / D * conj w := by
    funext z
    have hDc : conj D = D := by
      rw [hDdef]
      exact Complex.conj_ofReal _
    rw [map_div₀, hDc]
    simp only [map_sub, map_mul, Complex.conj_conj]
    ring
  rw [hfun]
  have hd : HasFDerivAt (fun w => (A * conj A₁ - B * conj B₁) / D * w +
        (B * A₁ - A * B₁) / D * conj w)
      (((A * conj A₁ - B * conj B₁) / D) • ContinuousLinearMap.id ℝ ℂ +
        ((B * A₁ - A * B₁) / D) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) w :=
    ((hasFDerivAt_id w).const_mul _).add (Complex.conjCLE.hasFDerivAt.const_mul _)
  have hfd : ∀ v : ℂ,
      fderiv ℝ (fun w => (A * conj A₁ - B * conj B₁) / D * w + (B * A₁ - A * B₁) / D * conj w) w v =
        (A * conj A₁ - B * conj B₁) / D * v + (B * A₁ - A * B₁) / D * conj v := fun v => by
    rw [hd.fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
  obtain ⟨hdz, hdzbar⟩ := LiZhongQC.h35c_dz_of_fderiv
    (f := fun w => (A * conj A₁ - B * conj B₁) / D * w + (B * A₁ - A * B₁) / D * conj w) hfd
  rw [complexDilatation, hdz, hdzbar, map_div₀ conj]
  field_simp [hA, hA₁, hcA₁, hden, hnum, hD0]

end GardinerLakic2000
