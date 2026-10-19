import References.GardinerLakic2000.Ch14.S04_GeneralizedAhlforsWeill

/-!
# Gardiner–Lakic 2000, Ch. 14 §14.5 Bers' `𝓛`-operators and §14.6 Inverse operators

Source `teichmuller.txt`, lines 10423–10552 (§14.6 from l. 10492 is merged into this file).

* Formula (14.23) (`𝓛`, l. 10428) — `bersLOmega`
* Formula (14.25) (`ṡ`, l. 10437, 10460) — `linSection`
* Unlabelled (`𝓛 ∘ ṡ = id`, `ṡ` bounded, l. 10464; used in Lemma 5) — `para14_5_section`
* Definition (vanishing Beltrami differential and quadratic differential, l. 10466) — exists:
  `GardinerLakic2000.bStarOmega` `GardinerLakic2000.boundedCuspForms0` (ν vanishing is b*(ν, Γ) = 0; φ vanishing is
  φ ∈ B₀)
* Unlabelled (`φ` vanishing implies `ṡ(φ)` vanishing, l. 10469; used in Lemma 5) — `para14_5_vanishing`
* Lemma 5 (l. 10471) — `lemma14_5`
* Theorem 4 ([EGL98b], l. 10474) — `thm14_4`
* Definition (the operator `𝓜`, (14.26) and the closing formula of §14.6, l. 10539, 10548) — `mOperator`
* Formula (14.24) (`𝓜` inverse to `𝓛`, l. 10452; cited in Theorem 4) — `eq14_24`

Not items (DESIGN §3): "`𝓛` is the derivative of `𝒮` at the origin" (l. 10432, explanation); the Riemann decompositions
`h = g ∘ f = v ∘ u` of §14.6 (l. 10493–10521, used to construct `𝓜`).

**Modelling.** Configurations and groups as in §14.4. `𝓛_D(μ)(z) = −(6/π) ∬_D μ(ζ)/(ζ − z)⁴`. `ṡ` is the derivative
of `s(tφ)` at `t = 0`, `ṡ(φ) = ½ (ζ − j(ζ))² φ(j(ζ)) j_ζ̄(ζ)` (l. 10437); (14.25) prints `−½` [misprint: with `−½`,
`𝓛 ∘ ṡ = −id` by the displayed formula at l. 10443]. In `𝓜` the closing formula prints the denominator
`(w_ζ(ζ) − w_z(z))⁴` for `(w(ζ) − w(z))⁴` [misprint: the change of variables `ŵ = w(ζ)` in (14.26) gives
`(w(ζ) − w(z))⁴`]. The data of §14.6: a symmetric `μ` (`μ(z̄) = conj μ(z)`, `‖μ‖∞ < 1`), `f` the normalized solution
with coefficient `μ` on `ℍ` and `0` on `ℍ*`, `Ω* = f(ℍ*)`, `Ω = f(ℍ)`, and `w` the normalized solution with coefficient
`(f⁻¹)^* μ` on `Ω*` and `0` on `Ω`; the book's `μ = −2y² conj S(f)` (l. 10529) only fixes notation [reading].

**[CORRECTION] (14.24).** With the book's curvature −4 density `ρ` (`ρ|dz| = |dζ|/(1 − |ζ|²)`, so `ρ⁻² = 4y²` on
`ℍ`) the printed identity
fails by the factor `4`: for `μ = 0` (`Ω = ℍ`, `w = id`) the reproducing formula
`φ(z) = (12/π) ∬_ℍ y² φ(ζ)/(z − ζ̄)⁴` gives `𝓛(ρ⁻² φ̄)(ζ) = −2 conj φ(ζ̄)` and then `𝓜(ρ⁻² conj 𝓛(ρ⁻² φ̄)) = 4φ`. It is
stated with the factor `4` (confirmed by the leader, Part D). The printed identity would need `ρ⁻² = 2y²`, the
Ahlfors–Weill weight `−2y²` that the book uses for `s`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (ExtPlane IsQuasiFuchsian normalizedSolution IsBeltramiCoeff upperHalf lowerHalf dz dzbar)

/-- **Formula (14.23)** (§14.5, l. 10428). `𝓛(μ)(z) = −(6/π) ∬_D μ(ζ)/(ζ − z)⁴ dξ dη`. -/
def bersLOmega (D : Set ℂ) (μ : ℂ → ℂ) (z : ℂ) : ℂ := -(6 / π : ℂ) * ∫ ζ in D, μ ζ / (ζ - z) ^ 4

/-- **Formula (14.25)** (§14.5, l. 10437, 10460; see the module docstring for the sign).
`ṡ(φ)(ζ) = ½ (ζ − j(ζ))² φ(j(ζ)) j_ζ̄(ζ)`. -/
def linSection (j : ℂ → ℂ) (φ : ℂ → ℂ) (ζ : ℂ) : ℂ := (ζ - j ζ) ^ 2 * φ (j ζ) * dzbar j ζ / 2

/-- **Definition** (`𝓜`, §14.6, l. 10539–10548). `𝓜(τ)(z) = −(6/π) ∬_{Ω*} τ(ζ) w_ζ(ζ)² w′(z)² / (w(ζ) − w(z))⁴`
(`z ∈ Ω`, `w` conformal on `Ω`). -/
def mOperator (w : ℂ → ℂ) (Ωs : Set ℂ) (τ : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(6 / π : ℂ) * ∫ ζ in Ωs, τ ζ * dz w ζ ^ 2 * deriv w z ^ 2 / (w ζ - w z) ^ 4

/-- **Unlabelled** (§14.5, l. 10464). For the Earle–Nag reflection `j` of a `Γ`-invariant configuration, `ṡ` maps
`B(Ω, Γ)` boundedly into `L∞(Ω*, Γ)` and is a section of `𝓛`: `𝓛_{Ω*} ∘ ṡ = id` on `B(Ω, Γ)`. -/
theorem para14_5_section {C : Set ExtPlane} {Ω Ωs : Set ℂ} {j : ℂ → ℂ} {K : ℝ}
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)} (hc : IsQCConfiguration C Ω Ωs) (hΓ : IsQuasiFuchsian Γ C)
    (hj : IsEarleNagReflection C Ω Ωs j) (hjK : IsReflectionGL C Ω Ωs j K) :
    (∀ φ ∈ boundedCuspFormsC Γ Ω, linSection j φ ∈ beltramiSpaceOmega Γ Ωs ∧
      ∀ z ∈ Ω, bersLOmega Ωs (linSection j φ) z = φ z) ∧
    ∃ M : ℝ, ∀ φ ∈ boundedCuspFormsC Γ Ω,
      eLpNorm (linSection j φ) ⊤ (volume.restrict Ωs) ≤ ENNReal.ofReal M * cuspNorm Ω φ := by
  sorry

/-- **Unlabelled** (§14.5, l. 10469). If `φ ∈ B(Ω, Γ)` is vanishing, then `ṡ(φ)` is a vanishing Beltrami differential
on `Ω*`. -/
theorem para14_5_vanishing {C : Set ExtPlane} {Ω Ωs : Set ℂ} {j : ℂ → ℂ} {K : ℝ}
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)} (hc : IsQCConfiguration C Ω Ωs) (hΓ : IsQuasiFuchsian Γ C)
    (hj : IsEarleNagReflection C Ω Ωs j) (hjK : IsReflectionGL C Ω Ωs j K) {φ : ℂ → ℂ}
    (hφ : φ ∈ boundedCuspForms0 (orbitMapsC Γ) Ω (boundedCuspFormsC Γ Ω)) :
    bStarOmega (orbitMapsC Γ) Ωs (linSection j φ) = 0 := by
  sorry

/-- **Lemma 5** (§14.5, l. 10471). If `φ = 𝓛(ρ⁻² ψ̄)` and `φ` is vanishing, then `ψ` is vanishing (`ψ ∈ B(Ω*, Γ)`,
`φ` on `Ω`). -/
theorem lemma14_5 {C : Set ExtPlane} {Ω Ωs : Set ℂ} {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    (hc : IsQCConfiguration C Ω Ωs) (hΓ : IsQuasiFuchsian Γ C) {ψ φ : ℂ → ℂ} (hψ : ψ ∈ boundedCuspFormsC Γ Ωs)
    (hφψ : ∀ z ∈ Ω, φ z = bersLOmega Ωs (fun ζ => (poincareDensityGL Ωs ζ ^ (-2 : ℤ) : ℝ) * conj (ψ ζ)) z)
    (hφ : φ ∈ boundedCuspForms0 (orbitMapsC Γ) Ω (boundedCuspFormsC Γ Ω)) :
    ψ ∈ boundedCuspForms0 (orbitMapsC Γ) Ωs (boundedCuspFormsC Γ Ωs) := by
  sorry

/-- **Theorem 4** (§14.5, l. 10474; [EGL98b]). Suppose `ν ∈ L∞(Ω, Γ)` is vanishing and `φ = 𝓛(ν)`. Then `ρ⁻² φ̄` is
vanishing: `φ ∈ B₀(Ω*, Γ)`. -/
theorem thm14_4 {C : Set ExtPlane} {Ω Ωs : Set ℂ} {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    (hc : IsQCConfiguration C Ω Ωs) (hΓ : IsQuasiFuchsian Γ C) {ν φ : ℂ → ℂ} (hν : ν ∈ beltramiSpaceOmega Γ Ω)
    (hν0 : bStarOmega (orbitMapsC Γ) Ω ν = 0) (hφB : φ ∈ boundedCuspFormsC Γ Ωs)
    (hφ : ∀ z ∈ Ωs, φ z = bersLOmega Ω ν z) :
    φ ∈ boundedCuspForms0 (orbitMapsC Γ) Ωs (boundedCuspFormsC Γ Ωs) := by
  sorry

/-- **Formula (14.24)** (§14.5, l. 10452; [CORRECTION] factor `4`, see the module docstring). In the setting of §14.6,
`𝓜(ρ⁻² conj 𝓛(ρ⁻² φ̄)) = 4 φ` on `Ω` for every `φ ∈ B(Ω)`.

`w` has coefficient `(f⁻¹)^*μ` on `Ω*`: the pull-back of `μ|𝕃` by the conformal map `f⁻¹ : Ω* → 𝕃`,
`μ(f⁻¹u) f′/conj f′` at `f⁻¹u`. With it `w ∘ f` has coefficient `μ` on all of `ℂ`, so `w ∘ f = h_μ` and `w` maps `Ω`
conformally onto `ℍ` (AUDIT5_GL L3: the phase `conj f′/f′` was reversed before).
Verification note: the identity, with the factor `4`, was checked at `μ = 0`, where it is the reproducing formula on
`ℍ`. For `μ ≠ 0` it rests on the book's derivation (l. 10523–10548: the derivative of `ρ_h ∘ ρ_{h⁻¹} = id`), which
identifies `𝓜 = w^* ∘ 𝓛_𝕃 ∘ w_*` as an inverse of `𝓛`. That derivation is a sketch and was not re-derived
independently.
[CORRECTION/modelling] (AUDITR2_GL614 R2-4) `μ` is the Ahlfors–Weill representative `μ = −2y² conj S(f)` of the book
(l. 10529: "let `μ = −2 y² conj S(f)`"), on `ℍ*` where `f` is conformal, and extended to `ℍ` by symmetry; this is `hAW`. For an
arbitrary symmetric `μ` the identity is false: `μ ≡ 1/2` is a trivial coefficient (`f` conformal on `ℍ*`, `Ω = ℍ`, `S(f) = 0`),
the left side depends on `w` and equals `4(1 + k) φ = 6 φ` for `φ(z) = e^{iz}`, the right side is `4 φ`. `μ ≡ 1/2` violates
`hAW` (`S(f) = 0` but `μ ≠ 0`). The case `μ = 0` is covered by `hAW`. -/
theorem eq14_24 {μ : ℂ → ℂ} {k : ℝ} (hk : k < 1) (hμ : IsBeltramiCoeff μ univ k)
    (hsym : ∀ z, μ (conj z) = conj (μ z))
    (hAW : ∀ z ∈ lowerHalf, μ z = -2 * ((z.im : ℝ) : ℂ) ^ 2 *
      conj (LiZhongQC.schwarzian (normalizedSolution (upperHalf.indicator μ)) z)) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ (normalizedSolution (upperHalf.indicator μ) '' upperHalf) ∧
      cuspNorm (normalizedSolution (upperHalf.indicator μ) '' upperHalf) φ < ⊤) :
    let f := normalizedSolution (upperHalf.indicator μ)
    let Ω := f '' upperHalf
    let Ωs := f '' lowerHalf
    let w := normalizedSolution (Ωs.indicator fun u =>
      μ (Function.invFun f u) * deriv f (Function.invFun f u) / conj (deriv f (Function.invFun f u)))
    ∀ z ∈ Ω, mOperator w Ωs (fun ζ => (poincareDensityGL Ωs ζ ^ (-2 : ℤ) : ℝ) *
        conj (bersLOmega Ω (fun u => (poincareDensityGL Ω u ^ (-2 : ℤ) : ℝ) * conj (φ u)) ζ)) z = 4 * φ z := by
  sorry

end GardinerLakic2000
