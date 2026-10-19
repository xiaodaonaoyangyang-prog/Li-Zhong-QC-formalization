import References.GardinerLakic2000.Ch04.S04_ReichStrebelInequality

/-!
# Gardiner–Lakic 2000, Ch. 4 §4.5 Surfaces of infinite analytic type

Source `teichmuller.txt`, lines 4017–4039 (and the chapter introduction, l. 3649–3657, for (4.1)).

* Formula (4.19) (the Reich–Strebel inequality on the disc for maps fixing `∂Δ` pointwise, l. 4020–4028) — `eq4_19`
* Formula (4.1) = (4.20) (the Reich–Strebel inequality on an arbitrary Riemann surface, l. 3656, 4030–4038; cited
  l. 4041) — `eq4_1`

Near miss: `LiZhongQC.thm35_2_main_inequality` (maps of `Δ` with equal boundary values; it gives (4.19) with the
signs `1 − μφ/|φ|` for `f₀ = f`, `f = id` read backwards, which is not plain unfolding).

**Conventions.** [misprint] l. 4020 prints `μ = f_z / f_z̄`; the Beltrami coefficient is `f_z̄ / f_z` (Theorem 3).
In the Fuchsian model (B0.1) the lifts of the self-maps of `ℍ/Γ` homotopic to the identity relative to the boundary
are the `Γ`-compatible maps with `f|ℝ = id` (l. 4030), i.e. the trivial coefficients `LiZhongQC.IsTrivialBeltrami`,
and `A(R)` is `LiZhongQC.integrableAutomorphicQD` with norm `∬_ω |φ|` over a fundamental domain `ω`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace GardinerLakic2000

/-- **Formula (4.19)** (§4.5, l. 4020–4028). If `f` is a quasiconformal self-map of `Δ` with `f(λ) = λ` for
`|λ| = 1` and `μ = f_z̄/f_z`, then for every `φ ∈ A(Δ)`,
`∬_Δ |φ| ≤ ∬_Δ |φ| |1 + μ φ/|φ||² / (1 − |μ|²)`. Modelling: the boundary values are those of the homeomorphic
extension `F` of `f` to the closed disc. -/
theorem eq4_19 {f : ℂ → ℂ} (hf : LiZhongQC.IsQuasiconformal f LiZhongQC.unitDisc)
    (hfs : f '' LiZhongQC.unitDisc = LiZhongQC.unitDisc) {F : LiZhongQC.ExtPlane → LiZhongQC.ExtPlane}
    (hF : LiZhongQC.IsHomeoExtension f LiZhongQC.unitDisc LiZhongQC.unitDisc F)
    (hbd : ∀ ζ : ℂ, ‖ζ‖ = 1 → F ζ = ζ) {φ : ℂ → ℂ} (hφ : φ ∈ LiZhongQC.integrableQD) :
    LiZhongQC.phiArea φ LiZhongQC.unitDisc ≤ ∫⁻ z in LiZhongQC.unitDisc, ENNReal.ofReal (‖φ z‖ *
      (‖1 + LiZhongQC.complexDilatation f z * (φ z / ‖φ z‖)‖ ^ 2 /
        (1 - ‖LiZhongQC.complexDilatation f z‖ ^ 2))) := by
  -- the Reich–Strebel main inequality (35.5) for the pair `(id, f)`, applied to `−φ`
  have hU : IsOpen LiZhongQC.unitDisc := isOpen_ball
  have hid1 : LiZhongQC.IsKQC id LiZhongQC.unitDisc 1 :=
    LiZhongQC.isKQC_one_of_conformal hU (LiZhongQC.isConformalOnto_id _)
  have hareaψ : LiZhongQC.phiArea (fun z => -φ z) LiZhongQC.unitDisc = LiZhongQC.phiArea φ LiZhongQC.unitDisc := by
    show ∫⁻ z in LiZhongQC.unitDisc, ENNReal.ofReal ‖-φ z‖ = ∫⁻ z in LiZhongQC.unitDisc, ENNReal.ofReal ‖φ z‖
    simp only [norm_neg]
  have hψ : (fun z => -φ z) ∈ LiZhongQC.integrableQD := ⟨hφ.1.neg, by rw [hareaψ]; exact hφ.2⟩
  have h := LiZhongQC.main_inequality_simplified ⟨1, hid1⟩ hf (image_id _) hfs
    (LiZhongQC.isHomeoExtension_id _) hF (fun ζ hζ => (hbd ζ hζ).symm) hψ
  have hmax : LiZhongQC.maxDilatation id LiZhongQC.unitDisc ≤ 1 := by
    have h1 := (LiZhongQC.isKQC_maxDilatation_le hid1).1
    rwa [ENNReal.ofReal_one] at h1
  rw [hareaψ] at h
  refine h.trans ((mul_le_mul_of_nonneg_right hmax zero_le).trans (le_of_eq ?_))
  rw [one_mul]
  refine lintegral_congr fun z => ?_
  congr 1
  show ‖-φ z‖ * (‖1 - LiZhongQC.complexDilatation f z * -φ z / ((‖-φ z‖ : ℝ) : ℂ)‖ ^ 2 /
    (1 - ‖LiZhongQC.complexDilatation f z‖ ^ 2)) = _
  rw [norm_neg, show (1 : ℂ) - LiZhongQC.complexDilatation f z * -φ z / ((‖φ z‖ : ℝ) : ℂ) =
    1 + LiZhongQC.complexDilatation f z * (φ z / ((‖φ z‖ : ℝ) : ℂ)) by ring]

/-- **Formula (4.1) = (4.20)** (§4.5, l. 3656, 4030–4038). Let `R = ℍ/Γ` be an arbitrary Riemann surface, `ω` a
fundamental domain (`Fd`), `μ` the Beltrami coefficient of a quasiconformal self-map of `R` homotopic to the identity
relative to the boundary, and `φ ∈ A(R)`. Then `∬_ω |φ| ≤ ∬_ω |φ| |1 + μ φ/|φ||² / (1 − |μ|²)`. Modelling: the
Fuchsian model (see the module docstring); `Γ` is a fixed-point free Fuchsian group (l. 4030). -/
theorem eq4_1 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : LiZhongQC.IsFuchsian Γ)
    (hfree : LiZhongQC.ActsFreely Γ) {Fd : Set ℂ} (hFd : LiZhongQC.IsFundamentalDomainH Γ Fd)
    (μ : LiZhongQC.BeltramiGamma Γ)
    (hμ : LiZhongQC.IsTrivialBeltrami Γ μ) {φ : ℂ → ℂ} (hφ : φ ∈ LiZhongQC.integrableAutomorphicQD Γ Fd) :
    LiZhongQC.phiArea φ Fd ≤ ∫⁻ z in Fd, ENNReal.ofReal (‖φ z‖ *
      (‖1 + μ.1.1 z * (φ z / ‖φ z‖)‖ ^ 2 / (1 - ‖μ.1.1 z‖ ^ 2))) := by
  sorry

end GardinerLakic2000
