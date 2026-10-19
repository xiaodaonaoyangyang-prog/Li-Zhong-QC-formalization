import References.GardinerLakic2000.Ch03.S01_IntegrableQuadraticDifferentials

/-!
# Gardiner–Lakic 2000, Ch. 3 §3.2 Poincaré theta series

Source `teichmuller.txt`, lines 2214–2337 (Chapter 3, §3.2).

* Definition (the Poincaré series `Θ(φ)(z) = Σ_{B ∈ Γ} φ(Bz) B′(z)²`, l. 2224) — `thetaGL` (the project's sum
  over the matrices of Γ ≤ SL(2,ℝ), divided by the multiplicity of each Möbius map; leader ruling A0.2)
* Theorem 4 (l. 2229; cited in Ch. 4, 6, 7, 14) — `thm3_4_a`, `thm3_4_b`, `thm3_4_c`
* Formula (3.9) (`∬_Δ |K(z, w)| = π ρ²(w)`, the Bergman kernel `K(z, w) = (1 − z w̄)⁻⁴`, l. 2245–2254) — `eq3_9`
* Formula (3.11) (the reproducing formula, l. 2281; cited in Ch. 14, l. 10064) — `eq3_11`
* Corollary 1 (`A(R)` separable, l. 2334) — `cor3_4_1`

Not items: (3.10), (3.12)–(3.14), steps of the proof. Modelling: Theorem 4 is stated in the ℍ model (leader ruling
A0.2): `A(Δ)` becomes `A(ℍ)` (holomorphic `φ` on `ℍ` with `∬_ℍ |φ| < ∞`; the Cayley map is an isometry, so the
constants `1` and `1/3` are unchanged) and `A(R)` is `A(Δ, Γ)` = `LiZhongQC.integrableAutomorphicQD Γ F`; the book's
Θ is `thetaGL` (`LiZhongQC.h36p_theta` divided by `m = |Γ ∩ {±1}|`). The group-free formulas (3.9), (3.11) stay
on the disc, with the Poincaré density `ρ(z) = (1 − |z|²)⁻¹`. Near miss for Theorem 4:
`LiZhongQC.poincare_series_surjective` (surjectivity only).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (h36p_theta h36p_m upperHalf unitDisc phiArea integrableAutomorphicQD IsFuchsian ActsFreely
  IsFundamentalDomainH IsUniformization quadDiffNorm)

/-- **Definition** (§3.2, l. 2224). The Poincaré series `Θ(φ)(z) = Σ_{B ∈ Γ} φ(Bz) B′(z)²` summed over the Möbius maps
of `Γ`: the project's sum over the matrices, `LiZhongQC.h36p_theta`, divided by the number `m` of elements of `Γ` in
`{1, −1}` (each map is counted `m` times there). -/
def thetaGL (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)) : ℂ)⁻¹ * h36p_theta Γ φ z

/-- Helper for `lemma3_2` and `eq3_9`: `B(w) − B(z) = (ad − bc)(w − z)/((cz + d)(cw + d))` for
`B(z) = (az + b)/(cz + d)`. -/
theorem gl3_mob_sub {a b c d z w : ℂ} (hz : c * z + d ≠ 0) (hw : c * w + d ≠ 0) :
    (a * w + b) / (c * w + d) - (a * z + b) / (c * z + d) =
      (a * d - b * c) * (w - z) / ((c * z + d) * (c * w + d)) := by
  rw [div_sub_div _ _ hw hz]
  congr 1 <;> ring

/-- Helper for `lemma3_2` and `eq3_9`: `B′(z) = (ad − bc)/(cz + d)²`. -/
theorem gl3_mob_deriv {a b c d z : ℂ} (hz : c * z + d ≠ 0) :
    deriv (fun w => (a * w + b) / (c * w + d)) z = (a * d - b * c) / (c * z + d) ^ 2 := by
  have h := (((hasDerivAt_id z).const_mul a).add_const b).div (((hasDerivAt_id z).const_mul c).add_const d) hz
  have h' : HasDerivAt (fun w => (a * w + b) / (c * w + d))
      ((a * 1 * (c * z + d) - (a * z + b) * (c * 1)) / (c * z + d) ^ 2) z := h
  rw [h'.deriv]
  congr 1
  ring

/-- Helper for `eq3_11`: Bochner change of variables under a conformal map, `∬_V g = ∬_U |f′|² g ∘ f`
(the `∫` form of LZ `lintegral_image_conformal`). -/
theorem gl3_integral_image_conformal {f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U)
    (hf : LiZhongQC.IsConformalOnto f U V) (g : ℂ → ℂ) :
    ∫ w in V, g w = ∫ z in U, (‖deriv f z‖ ^ 2 : ℝ) • g (f z) := by
  rw [← hf.2.2, integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet
    (fun z hz => ((hf.1.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) hf.2.1 g]
  refine setIntegral_congr_fun hU.measurableSet fun z _ => ?_
  simp only [LiZhongQC.det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg ‖deriv f z‖)]

/-- Helper for `eq3_11`: integrability is preserved by a conformal change of variables,
`g ∈ L¹(V) ⇔ |f′|² g ∘ f ∈ L¹(U)`. -/
theorem gl3_integrableOn_image_conformal {f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U)
    (hf : LiZhongQC.IsConformalOnto f U V) (g : ℂ → ℂ) :
    IntegrableOn g V ↔ IntegrableOn (fun z => (‖deriv f z‖ ^ 2 : ℝ) • g (f z)) U := by
  rw [← hf.2.2, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU.measurableSet
    (fun z hz => ((hf.1.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) hf.2.1 g]
  refine integrableOn_congr_fun (fun z _ => ?_) hU.measurableSet
  simp only [LiZhongQC.det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg ‖deriv f z‖)]

/-- **Theorem 4** (§3.2, l. 2229), convergence. For `φ ∈ A(ℍ)` the Poincaré series converges absolutely at every point
of `ℍ` and uniformly on compact subsets of `ℍ`. -/
theorem thm3_4_a {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ upperHalf) (hint : phiArea φ upperHalf < ⊤) :
    (∀ z ∈ upperHalf, Summable fun γ : Γ => ‖φ (h36p_m γ z) / ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4‖) ∧
      TendstoLocallyUniformlyOn
        (fun s : Finset Γ => fun z => ∑ γ ∈ s, φ (h36p_m γ z) / ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4)
        (h36p_theta Γ φ) atTop upperHalf := by
  -- the local summable majorant of `LiZhongQC.h36p_b_local` on `B(z, Im z/4)` and the Weierstrass M-test
  refine ⟨fun z hz => ?_, fun U hU z hz => ?_⟩
  · obtain ⟨u, hu, hle⟩ := LiZhongQC.h36p_b_local hΓ hφ hint hz
    have hz' : 0 < z.im := hz
    exact Summable.of_nonneg_of_le (fun γ => norm_nonneg _)
      (fun γ => hle γ z (mem_ball_self (by positivity))) hu
  · obtain ⟨u, hu, hle⟩ := LiZhongQC.h36p_b_local hΓ hφ hint hz
    have hz' : 0 < z.im := hz
    exact ⟨ball z (z.im / 4), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z (by positivity)),
      tendstoUniformlyOn_tsum hu (fun γ w hw => hle γ w hw) U hU⟩

/-- **Theorem 4** (§3.2, l. 2229), the operator. `Θ` (divided by `m`, see the module docstring) maps `A(ℍ)` into
`A(Δ, Γ)` with norm at most `1`, and onto it. -/
theorem thm3_4_b {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) :
    (∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ upperHalf → phiArea φ upperHalf < ⊤ →
      (thetaGL Γ φ) ∈ integrableAutomorphicQD Γ F ∧
      phiArea (thetaGL Γ φ) F ≤
        phiArea φ upperHalf) ∧
    ∀ ψ ∈ integrableAutomorphicQD Γ F, ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ upperHalf ∧ phiArea φ upperHalf < ⊤ ∧
      EqOn (thetaGL Γ φ) ψ upperHalf := by
  have _hfree := hfree
  have : Countable Γ := (LiZhongQC.h36p_countable hΓ).to_subtype
  have hFH : F ⊆ upperHalf := hF.1
  have hFm : MeasurableSet F := hF.2.1
  set m : ℂ := (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)) : ℂ) with hmdef
  have hm0 : m ≠ 0 := by
    rw [hmdef]
    exact_mod_cast (LiZhongQC.h36p_mult_pos (Γ := Γ)).ne'
  have hmE : ‖m⁻¹‖ₑ * (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)) : ℝ≥0∞) = 1 := by
    rw [enorm_inv hm0, hmdef, ← ofReal_norm, Complex.norm_natCast, ENNReal.ofReal_natCast]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast (LiZhongQC.h36p_mult_pos (Γ := Γ)).ne') (ENNReal.natCast_ne_top _)
  refine ⟨fun φ hφ hint => ?_, fun ψ hψ => ?_⟩
  · -- `∬_F |Θφ/m| ≤ m⁻¹ Σ_γ ∬_F |φ(γz)| |j(γ, z)|⁻⁴ = ∬_ℍ |φ|` (`LiZhongQC.h36p_b_sum_lintegral`)
    have hterm : ∀ γ : Γ, AEMeasurable
        (fun z => ‖φ (h36p_m γ.1 z) / ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4‖ₑ) (volume.restrict F) := fun γ =>
      (((LiZhongQC.h36p_b_term_diff hφ γ.1).continuousOn.mono hFH).aemeasurable hFm).enorm
    have hbound : phiArea (thetaGL Γ φ) F ≤ phiArea φ upperHalf := by
      calc phiArea (thetaGL Γ φ) F
          = ∫⁻ z in F, ‖m⁻¹‖ₑ * ‖h36p_theta Γ φ z‖ₑ := by
            unfold phiArea thetaGL
            refine lintegral_congr fun z => ?_
            rw [ofReal_norm, enorm_mul]
        _ ≤ ∫⁻ z in F, ‖m⁻¹‖ₑ * ∑' γ : Γ, ‖φ (h36p_m γ.1 z) / ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4‖ₑ := by
            refine lintegral_mono fun z => ?_
            gcongr
            exact enorm_tsum_le_tsum_enorm
        _ = ‖m⁻¹‖ₑ * ∑' γ : Γ, ∫⁻ z in F, ‖φ (h36p_m γ.1 z) / ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4‖ₑ := by
            rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_tsum hterm]
        _ = phiArea φ upperHalf := by
            rw [LiZhongQC.h36p_b_sum_lintegral hΓ hF hφ, ← mul_assoc, hmE, one_mul]
    refine ⟨⟨(LiZhongQC.h36p_b_theta_diff hΓ hφ hint).const_mul _, lt_of_le_of_lt hbound hint, ?_⟩, hbound⟩
    intro γ hγ z hz
    simp only [thetaGL]
    rw [mul_div_assoc, LiZhongQC.h36p_b_automorphic (Γ := Γ) φ γ hγ z hz]
  · -- onto: `LiZhongQC.h36p_theta_surj` gives `ψ = Θ f`, and `Θ(m f)/m = Θ f`
    obtain ⟨f, hf, hfA, hθ⟩ := LiZhongQC.h36p_theta_surj hΓ hF ψ hψ
    refine ⟨fun w => m * f w, hf.const_mul m, ?_, fun z hz => ?_⟩
    · unfold phiArea at hfA ⊢
      simp_rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfA
    · show m⁻¹ * h36p_theta Γ (fun w => m * f w) z = ψ z
      rw [hθ z hz]
      unfold h36p_theta
      simp_rw [mul_div_assoc]
      rw [tsum_mul_left, ← mul_assoc, inv_mul_cancel₀ hm0, one_mul]

/-- **Theorem 4** (§3.2, l. 2229), the ball. `Θ` maps the unit ball of `A(ℍ)` onto a subset of `A(Δ, Γ)` containing
the ball of radius `1/3`. -/
theorem thm3_4_c {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) :
    ∀ ψ ∈ integrableAutomorphicQD Γ F, phiArea ψ F ≤ 1 / 3 →
      ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ upperHalf ∧ phiArea φ upperHalf ≤ 1 ∧
        EqOn (thetaGL Γ φ) ψ upperHalf := by
  intro ψ hψ hψ3
  have _hfree := hfree
  have hFH : F ⊆ upperHalf := hF.1
  have hFm : MeasurableSet F := hF.2.1
  have hψc : ContinuousOn ψ upperHalf := hψ.1.continuousOn
  set m : ℂ := (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)) : ℂ) with hmdef
  have hm0 : m ≠ 0 := by
    rw [hmdef]
    exact_mod_cast (LiZhongQC.h36p_mult_pos (Γ := Γ)).ne'
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  -- **Duplicate note:** the Bergman-projection preimage `f = m⁻¹ (12/π) ∫_F (Im ζ)² ψ(ζ)/(ζ̄ − w)⁴` and the identity
  -- `ψ = Θ f` below repeat the construction inside `LiZhongQC.h36p_theta_surj` (which exports only `∬_ℍ |f| < ∞`);
  -- the explicit bound `∬_ℍ |m f| ≤ 3 ∬_F |ψ|` is what Theorem 4 needs
  set c : ℂ := m⁻¹ * (12 / π : ℂ) with hcdef
  set f : ℂ → ℂ := fun w => c * ∫ ζ in F, LiZhongQC.h36p_c_K ψ ζ w with hfdef
  have hθ : ∀ z ∈ upperHalf, ψ z = h36p_theta Γ f z := by
    intro z hz
    have hGi := LiZhongQC.h36p_c_Gz_int hΓ hF hψ hz
    have hU := LiZhongQC.h36p_c_unfold_int hΓ hF hGi
    have hR := LiZhongQC.h36p_c_rp_upper hψ.1 hz hGi
    have hterm : ∀ γ : Γ, c * (∫ ζ in F, LiZhongQC.h36p_c_K ψ ζ (h36p_m γ.1 z)) /
        ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4 =
        c * ∫ ζ in F, LiZhongQC.h36p_c_K ψ ζ (h36p_m γ.1 z) / ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4 := by
      intro γ
      rw [mul_div_assoc, integral_div]
    have hterm2 : ∀ γ : Γ, c * ∫ ζ in F, LiZhongQC.h36p_c_K ψ ζ (h36p_m γ.1⁻¹ z) /
        (((γ.1⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
          (γ.1⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) ^ 4 =
        c * ∫ ζ in F, ((‖(γ.1 1 0 : ℂ) * ζ + γ.1 1 1‖⁻¹ ^ 4 : ℝ) : ℂ) *
          LiZhongQC.h36p_c_K ψ (h36p_m γ.1 ζ) z := by
      intro γ
      congr 1
      exact setIntegral_congr_fun hFm fun ζ hζ => LiZhongQC.h36p_c_kinv hψ γ.2 (hFH hζ) hz
    have hre := (Equiv.inv Γ).tsum_eq (fun γ : Γ => c * ∫ ζ in F, LiZhongQC.h36p_c_K ψ ζ (h36p_m γ.1 z) /
      ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4)
    show ψ z = ∑' γ : Γ, c * (∫ ζ in F, LiZhongQC.h36p_c_K ψ ζ (h36p_m γ.1 z)) /
      ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4
    rw [tsum_congr hterm, ← hre]
    show ψ z = ∑' γ : Γ, c * ∫ ζ in F, LiZhongQC.h36p_c_K ψ ζ (h36p_m γ.1⁻¹ z) /
        (((γ.1⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
          (γ.1⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) ^ 4
    rw [tsum_congr hterm2, tsum_mul_left, hU, hR, hcdef]
    field_simp
    rw [hmdef]
  -- the candidate `φ = m f = (12/π) ∫_F K`
  have hmc : m * c = (12 / π : ℂ) := by
    rw [hcdef, ← mul_assoc, mul_inv_cancel₀ hm0, one_mul]
  refine ⟨fun w => m * f w, ((LiZhongQC.h36p_c_beta_diff hFm hFH hψc hψ.2.1).const_mul c).const_mul m, ?_,
    fun z hz => ?_⟩
  · -- `∬_ℍ |m f| ≤ (12/π) ∬_F ∬_ℍ |K| = (12/π) |𝔻| ∬_F |ψ|/4 = 3 ∬_F |ψ| ≤ 1`
    have hnorm : ‖(12 / π : ℂ)‖ = 12 / π := by
      rw [show (12 / π : ℂ) = ((12 / π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    have hA : ∫⁻ w in upperHalf, ENNReal.ofReal ‖∫ ζ in F, LiZhongQC.h36p_c_K ψ ζ w‖ ≤
        volume (ball (0 : ℂ) 1) * ∫⁻ ζ in F, ENNReal.ofReal (‖ψ ζ‖ / 4) := by
      calc ∫⁻ w in upperHalf, ENNReal.ofReal ‖∫ ζ in F, LiZhongQC.h36p_c_K ψ ζ w‖
          ≤ ∫⁻ w in upperHalf, ∫⁻ ζ in F, ENNReal.ofReal ‖LiZhongQC.h36p_c_K ψ ζ w‖ := by
            refine lintegral_mono fun w => ?_
            simp_rw [ofReal_norm]
            exact enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ ζ in F, ∫⁻ w in upperHalf, ENNReal.ofReal ‖LiZhongQC.h36p_c_K ψ ζ w‖ :=
            lintegral_lintegral_swap (LiZhongQC.h36p_c_K_aesm hψc hFm hFH).aemeasurable.norm.ennreal_ofReal
        _ = volume (ball (0 : ℂ) 1) * ∫⁻ ζ in F, ENNReal.ofReal (‖ψ ζ‖ / 4) := LiZhongQC.h36p_c_tonelli hFm hFH ψ
    have h4 : ∫⁻ ζ in F, ENNReal.ofReal (‖ψ ζ‖ / 4) = ENNReal.ofReal (1 / 4) * phiArea ψ F := by
      unfold phiArea
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun ζ => ?_
      rw [← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    have hconst : ENNReal.ofReal (12 / π) * (volume (ball (0 : ℂ) 1) * ENNReal.ofReal (1 / 4)) = 3 := by
      rw [Complex.volume_ball, ENNReal.ofReal_one, one_pow, one_mul, ← ENNReal.ofReal_coe_nnreal,
        NNReal.coe_real_pi, ← ENNReal.ofReal_mul Real.pi_pos.le, ← ENNReal.ofReal_mul (by positivity)]
      rw [show 12 / π * (π * (1 / 4)) = (3 : ℝ) by field_simp; norm_num]
      exact ENNReal.ofReal_ofNat 3
    calc phiArea (fun w => m * f w) upperHalf
        = ∫⁻ w in upperHalf, ENNReal.ofReal (12 / π) *
            ENNReal.ofReal ‖∫ ζ in F, LiZhongQC.h36p_c_K ψ ζ w‖ := by
          unfold phiArea
          refine lintegral_congr fun w => ?_
          rw [hfdef]
          simp only
          rw [← mul_assoc, hmc, norm_mul, hnorm, ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (12 / π) * ∫⁻ w in upperHalf, ENNReal.ofReal ‖∫ ζ in F, LiZhongQC.h36p_c_K ψ ζ w‖ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (12 / π) * (volume (ball (0 : ℂ) 1) * ∫⁻ ζ in F, ENNReal.ofReal (‖ψ ζ‖ / 4)) := by
          gcongr
      _ = 3 * phiArea ψ F := by
          rw [h4, ← mul_assoc, ← mul_assoc, mul_assoc (ENNReal.ofReal (12 / π)), hconst]
      _ ≤ 3 * (1 / 3) := by gcongr
      _ = 1 := by
          rw [one_div]
          exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  · show m⁻¹ * h36p_theta Γ (fun w => m * f w) z = ψ z
    rw [hθ z hz]
    unfold h36p_theta
    simp_rw [mul_div_assoc]
    rw [tsum_mul_left, ← mul_assoc, inv_mul_cancel₀ hm0, one_mul]

/-- Helper for `eq3_9`: `|w̄ζ + 1|² − |ζ + w|² = (1 − |ζ|²)(1 − |w|²)`. -/
theorem gl3_normSq_aut (ζ w : ℂ) :
    normSq (conj w * ζ + 1) - normSq (ζ + w) = (1 - normSq ζ) * (1 - normSq w) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

/-- Helper for `eq3_9`: for `|w| < 1` and `|ζ| < 1`, `w̄ζ + 1 ≠ 0` and `T_w(ζ) = (ζ + w)/(w̄ζ + 1)` lies in the disc. -/
theorem gl3_aut_mem {w ζ : ℂ} (hw : ‖w‖ < 1) (hζ : ‖ζ‖ < 1) :
    conj w * ζ + 1 ≠ 0 ∧ ‖(ζ + w) / (conj w * ζ + 1)‖ < 1 := by
  have hw2 : normSq w < 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  have hζ2 : normSq ζ < 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ζ]
  have hid := gl3_normSq_aut ζ w
  have hpos : 0 < (1 - normSq ζ) * (1 - normSq w) := mul_pos (by linarith) (by linarith)
  have hden : 0 < normSq (conj w * ζ + 1) := by
    have := Complex.normSq_nonneg (ζ + w)
    linarith
  refine ⟨fun h => by rw [h, map_zero] at hden; exact lt_irrefl 0 hden, ?_⟩
  have h1 : normSq ((ζ + w) / (conj w * ζ + 1)) < 1 := by
    rw [map_div₀, div_lt_one hden]
    linarith
  rw [Complex.normSq_eq_norm_sq] at h1
  nlinarith [norm_nonneg ((ζ + w) / (conj w * ζ + 1))]

/-- Helper for `eq3_9`: the disc automorphism `T_w(ζ) = (ζ + w)/(w̄ζ + 1)` (`|w| < 1`) maps the disc conformally onto
itself. -/
theorem gl3_aut_conformal {w : ℂ} (hw : ‖w‖ < 1) :
    LiZhongQC.IsConformalOnto (fun ζ => (ζ + w) / (conj w * ζ + 1)) unitDisc unitDisc := by
  have hww : 1 - w * conj w ≠ 0 := by
    rw [Complex.mul_conj, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_ne_zero,
      Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  have hmem : ∀ ζ ∈ unitDisc, ‖ζ‖ < 1 := fun ζ hζ => mem_ball_zero_iff.1 hζ
  refine ⟨fun ζ hζ => ?_, fun ζ₁ h₁ ζ₂ h₂ h => ?_, ?_⟩
  · have hd := (gl3_aut_mem hw (hmem ζ hζ)).1
    exact (((differentiableAt_id.add_const w).div ((differentiableAt_id.const_mul (conj w)).add_const 1)
      hd)).differentiableWithinAt
  · have hd₁ := (gl3_aut_mem hw (hmem ζ₁ h₁)).1
    have hd₂ := (gl3_aut_mem hw (hmem ζ₂ h₂)).1
    simp only at h
    rw [div_eq_div_iff hd₁ hd₂] at h
    have : (ζ₁ - ζ₂) * (1 - w * conj w) = 0 := by linear_combination h
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hww)
  · ext u
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      exact mem_ball_zero_iff.2 (gl3_aut_mem hw (hmem ζ hζ)).2
    · intro hu
      have hw' : ‖-w‖ < 1 := by rwa [norm_neg]
      obtain ⟨hd, hζ⟩ := gl3_aut_mem hw' (hmem u hu)
      rw [map_neg] at hd hζ
      have hD : 1 - conj w * u ≠ 0 := fun h => hd (by linear_combination h)
      have hrw : (u + -w) / (-conj w * u + 1) = (u - w) / (1 - conj w * u) := by
        congr 1
        ring
      rw [hrw] at hζ
      refine ⟨(u - w) / (1 - conj w * u), mem_ball_zero_iff.2 hζ, ?_⟩
      have e1 : (u - w) / (1 - conj w * u) + w = u * (1 - w * conj w) / (1 - conj w * u) := by
        rw [eq_div_iff hD, add_mul, div_mul_cancel₀ _ hD]
        ring
      have e2 : conj w * ((u - w) / (1 - conj w * u)) + 1 = (1 - w * conj w) / (1 - conj w * u) := by
        rw [eq_div_iff hD, add_mul, mul_assoc, div_mul_cancel₀ _ hD]
        ring
      show ((u - w) / (1 - conj w * u) + w) / (conj w * ((u - w) / (1 - conj w * u)) + 1) = u
      rw [e1, e2, div_div_div_cancel_right₀ hD, mul_div_cancel_right₀ _ hww]

/-- Helper for `eq3_9`: `T_w′(ζ) = (1 − |w|²)/(w̄ζ + 1)²`. -/
theorem gl3_aut_deriv {w ζ : ℂ} (hd : conj w * ζ + 1 ≠ 0) :
    deriv (fun ζ => (ζ + w) / (conj w * ζ + 1)) ζ = (1 - w * conj w) / (conj w * ζ + 1) ^ 2 := by
  simpa using gl3_mob_deriv (a := 1) (b := w) (c := conj w) (d := 1) (z := ζ) hd

/-- **Formula (3.9)** (§3.2, l. 2251–2254). For the Bergman kernel `K(z, w) = (1 − z w̄)⁻⁴` of the disc,
`∬_Δ |K(z, w)| dx dy = π ρ²(w)`, `ρ(w) = (1 − |w|²)⁻¹`. -/
theorem eq3_9 {w : ℂ} (hw : w ∈ unitDisc) :
    ∫ z in unitDisc, ‖(1 - z * conj w)⁻¹ ^ 4‖ = π * ((1 - ‖w‖ ^ 2)⁻¹) ^ 2 := by
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
  have hc : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hww : (1 : ℂ) - w * conj w = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hww0 : (1 : ℂ) - w * conj w ≠ 0 := by
    rw [hww, Complex.ofReal_ne_zero]
    exact hc.ne'
  have hconf := gl3_aut_conformal hw1
  have h := LiZhongQC.lintegral_image_conformal isOpen_ball hconf
    (fun u => ENNReal.ofReal ‖(1 - u * conj w)⁻¹ ^ 4‖)
  have hpt : ∀ ζ ∈ unitDisc, ‖deriv (fun ζ => (ζ + w) / (conj w * ζ + 1)) ζ‖ₑ ^ 2 *
      ENNReal.ofReal ‖(1 - (ζ + w) / (conj w * ζ + 1) * conj w)⁻¹ ^ 4‖ = ENNReal.ofReal (((1 - ‖w‖ ^ 2)⁻¹) ^ 2) := by
    intro ζ hζ
    have hd := (gl3_aut_mem hw1 (mem_ball_zero_iff.1 hζ)).1
    rw [gl3_aut_deriv hd]
    have hkey : ((1 - w * conj w) / (conj w * ζ + 1) ^ 2) ^ 2 * (1 - (ζ + w) / (conj w * ζ + 1) * conj w)⁻¹ ^ 4 =
        (((1 - w * conj w) ^ 2)⁻¹ : ℂ) := by
      have h1 : 1 - (ζ + w) / (conj w * ζ + 1) * conj w = (1 - w * conj w) / (conj w * ζ + 1) := by
        rw [eq_div_iff hd, sub_mul, div_mul_eq_mul_div, div_mul_cancel₀ _ hd]
        ring
      rw [h1]
      generalize conj w * ζ + 1 = D at hd ⊢
      generalize 1 - w * conj w = A at hww0 ⊢
      field_simp
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity), ← norm_pow,
      ← norm_mul, hkey, hww, ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity), inv_pow]
  beta_reduce at h
  rw [setLIntegral_congr_fun isOpen_ball.measurableSet hpt, setLIntegral_const] at h
  have hmeas : AEStronglyMeasurable (fun z : ℂ => (1 - z * conj w)⁻¹ ^ 4) (volume.restrict unitDisc) :=
    ((measurable_const.sub (measurable_id.mul_const _)).inv.pow_const 4).aestronglyMeasurable
  rw [integral_norm_eq_lintegral_enorm hmeas]
  have h2 : ∫⁻ z in unitDisc, ‖(1 - z * conj w)⁻¹ ^ 4‖ₑ =
      ∫⁻ z in unitDisc, ENNReal.ofReal ‖(1 - z * conj w)⁻¹ ^ 4‖ := by
    simp only [ofReal_norm]
  rw [h2, h]
  show (ENNReal.ofReal (((1 - ‖w‖ ^ 2)⁻¹) ^ 2) * volume (ball (0 : ℂ) 1)).toReal = _
  rw [Complex.volume_ball, ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity),
    ENNReal.coe_toReal, NNReal.coe_real_pi, mul_comm]

/-- Helper for `eq3_11`: `∫₀¹ 2π r (1 − r²)² dr = π/3`. -/
theorem gl3_radial_weight :
    ∫ r in Ioo (0 : ℝ) 1, 2 * π * r * (1 - r ^ 2) ^ 2 = π / 3 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r : ℝ => -(π * (1 - r ^ 2) ^ 3 / 3))]
  · norm_num
  · intro r _
    have h1 : HasDerivAt (fun r : ℝ => 1 - r ^ 2) (-(2 * r)) r := by
      have := (hasDerivAt_pow 2 r).const_sub 1
      convert this using 1
      norm_num
    have h3 := (((h1.pow 3).const_mul π).div_const 3).neg
    convert h3 using 1
    norm_num
    ring
  · exact (by fun_prop : Continuous fun r : ℝ => 2 * π * r * (1 - r ^ 2) ^ 2).intervalIntegrable 0 1

/-- Helper for `eq3_11`: the weighted area mean value at the centre, `∬_Δ (1 − |w|²)² F(w) = (π/3) F(0)` for `F`
holomorphic on the disc with `(1 − |w|²)² F` integrable (polar coordinates and the circle mean value property). -/
theorem gl3_weighted_mean {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F unitDisc)
    (hint : IntegrableOn (fun w => (((1 - ‖w‖ ^ 2) ^ 2 : ℝ) : ℂ) * F w) unitDisc) :
    ∫ w in unitDisc, (((1 - ‖w‖ ^ 2) ^ 2 : ℝ) : ℂ) * F w = (π / 3 : ℂ) * F 0 := by
  classical
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  set h : ℂ → ℂ := unitDisc.indicator fun w => (((1 - ‖w‖ ^ 2) ^ 2 : ℝ) : ℂ) * F w with hh
  have hhint : Integrable h := hint.integrable_indicator hΔ
  have hpolar : ⇑Complex.polarCoord.symm = fun p : ℝ × ℝ => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * I) :=
    funext Complex.polarCoord_symm_apply
  have hpc : Continuous ⇑Complex.polarCoord.symm := by rw [hpolar]; fun_prop
  have hhm : Measurable h := by
    rw [hh, ← piecewise_eq_indicator]
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hΔ
    exact (by fun_prop : Continuous fun w : ℂ => (((1 - ‖w‖ ^ 2) ^ 2 : ℝ) : ℂ)).continuousOn.mul hF.continuousOn
  have htarget : (polarCoord.target : Set (ℝ × ℝ)) = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  -- integrability on the product of the radial and angular measures
  have hprodint : Integrable (fun p : ℝ × ℝ => p.1 • h (Complex.polarCoord.symm p))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← htarget]
    refine ⟨(measurable_fst.smul (hhm.comp hpc.measurable)).aestronglyMeasurable, ?_⟩
    have h1 : ∫⁻ p in polarCoord.target, ‖p.1 • h (Complex.polarCoord.symm p)‖ₑ =
        ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • ‖h (Complex.polarCoord.symm p)‖ₑ := by
      refine setLIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
      have hp1 : 0 < p.1 := by rw [htarget] at hp; exact hp.1
      rw [enorm_smul, Real.enorm_eq_ofReal hp1.le, smul_eq_mul]
    show ∫⁻ p in polarCoord.target, ‖p.1 • h (Complex.polarCoord.symm p)‖ₑ < ⊤
    rw [h1, Complex.lintegral_comp_polarCoord_symm (fun w => ‖h w‖ₑ)]
    exact hhint.hasFiniteIntegral
  rw [← integral_indicator hΔ, ← Complex.integral_comp_polarCoord_symm, htarget, Measure.volume_eq_prod,
    ← Measure.prod_restrict, integral_prod _ hprodint]
  -- the angular integrals: `2π r (1 − r²)² F(0)` for `r < 1`, `0` for `r ≥ 1`
  have hin : ∀ r ∈ Ioi (0 : ℝ), ∫ θ in Ioo (-π) π, (r, θ).1 • h (Complex.polarCoord.symm (r, θ)) =
      (Iio (1 : ℝ)).indicator (fun r => ((2 * π * r * (1 - r ^ 2) ^ 2 : ℝ) : ℂ) * F 0) r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    have hnorm : ∀ θ : ℝ, ‖Complex.polarCoord.symm (r, θ)‖ = r := fun θ => by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr0]
    have hcm : ∀ θ : ℝ, Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := fun θ => by
      rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I]
      simp [Complex.ofReal_cos, Complex.ofReal_sin]
    by_cases hr1 : r < 1
    · rw [indicator_of_mem (show r ∈ Iio (1 : ℝ) from hr1)]
      have hmem : ∀ θ : ℝ, Complex.polarCoord.symm (r, θ) ∈ unitDisc := fun θ => by
        rw [show unitDisc = ball (0 : ℂ) 1 from rfl, mem_ball_zero_iff, hnorm θ]
        exact hr1
      have hval : ∀ θ : ℝ, (r, θ).1 • h (Complex.polarCoord.symm (r, θ)) =
          ((r * (1 - r ^ 2) ^ 2 : ℝ) : ℂ) * F (circleMap 0 r θ) := fun θ => by
        rw [hh, indicator_of_mem (hmem θ), hnorm θ, hcm θ, Complex.real_smul]
        push_cast
        ring
      simp only [hval]
      rw [integral_const_mul]
      -- the mean value property on the circle `|w| = r`
      have hdc : DiffContOnCl ℂ F (ball (0 : ℂ) |r|) := by
        rw [abs_of_pos hr0]
        refine DifferentiableOn.diffContOnCl ?_
        rw [closure_ball 0 hr0.ne']
        exact hF.mono (closedBall_subset_ball hr1)
      have hmv := hdc.circleAverage
      rw [Real.circleAverage_def, Complex.real_smul] at hmv
      have hper : ∫ θ in (-π)..(-π) + 2 * π, F (circleMap 0 r θ) = ∫ θ in (0 : ℝ)..0 + 2 * π, F (circleMap 0 r θ) :=
        ((periodic_circleMap 0 r).comp F).intervalIntegral_add_eq (-π) 0
      rw [show (-π : ℝ) + 2 * π = π by ring, zero_add] at hper
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), hper]
      have h2π : (2 * π : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
      have hint2 : ∫ θ in (0 : ℝ)..2 * π, F (circleMap 0 r θ) = 2 * π * F 0 := by
        have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
        rw [← hmv]
        push_cast
        field_simp
      rw [hint2]
      push_cast
      ring
    · rw [indicator_of_notMem (show r ∉ Iio (1 : ℝ) from hr1)]
      have hval : ∀ θ : ℝ, (r, θ).1 • h (Complex.polarCoord.symm (r, θ)) = 0 := fun θ => by
        have hnot : Complex.polarCoord.symm (r, θ) ∉ unitDisc := by
          rw [show unitDisc = ball (0 : ℂ) 1 from rfl, mem_ball_zero_iff, hnorm θ]
          exact hr1
        rw [hh, indicator_of_notMem hnot, smul_zero]
      simp only [hval, integral_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hin, setIntegral_indicator measurableSet_Iio,
    show Ioi (0 : ℝ) ∩ Iio 1 = Ioo 0 1 from Ioi_inter_Iio, integral_mul_const, integral_complex_ofReal,
    gl3_radial_weight]
  push_cast
  ring

/-- **Formula (3.11)** (the reproducing formula, §3.2, l. 2277–2281). If `φ` is holomorphic in the disc and
`ρ⁻² φ` is integrable, then `φ(z) = (3/π) ∬_Δ ρ(w)⁻² K(z, w) φ(w) du dv`. -/
theorem eq3_11 {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hint : IntegrableOn (fun w => (1 - ‖w‖ ^ 2) ^ 2 * φ w) unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    φ z = 3 / π * ∫ w in unitDisc, ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * (1 - z * conj w)⁻¹ ^ 4 * φ w := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hconf := gl3_aut_conformal hz1
  set T : ℂ → ℂ := fun ζ => (ζ + z) / (conj z * ζ + 1) with hT
  have hA : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hzz : (1 : ℂ) - z * conj z = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hden : ∀ ζ ∈ unitDisc, conj z * ζ + 1 ≠ 0 := fun ζ hζ =>
    (gl3_aut_mem hz1 (mem_ball_zero_iff.1 hζ)).1
  have hTmem : ∀ ζ ∈ unitDisc, T ζ ∈ unitDisc := fun ζ hζ =>
    mem_ball_zero_iff.2 (gl3_aut_mem hz1 (mem_ball_zero_iff.1 hζ)).2
  -- the transformed integrand:
  -- `|T′|² (1 − |Tζ|²)² (1 − z conj(Tζ))⁻⁴ φ(Tζ) = (1 − |ζ|²)² (z̄ζ + 1)⁻⁴ φ(Tζ)`
  have hkey : ∀ ζ ∈ unitDisc, (‖deriv T ζ‖ ^ 2 : ℝ) •
      ((((1 - ‖T ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) * (1 - z * conj (T ζ))⁻¹ ^ 4 * φ (T ζ)) =
        (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((conj z * ζ + 1)⁻¹ ^ 4 * φ (T ζ)) := by
    intro ζ hζ
    have hD := hden ζ hζ
    obtain ⟨D, hDdef⟩ : ∃ D : ℂ, D = conj z * ζ + 1 := ⟨_, rfl⟩
    have hDne : D ≠ 0 := hDdef ▸ hD
    have hDc : conj D = z * conj ζ + 1 := by rw [hDdef, map_add, map_mul, Complex.conj_conj, map_one]
    have hDcne : conj D ≠ 0 := (map_ne_zero _).2 hDne
    have hN : ((‖D‖ ^ 2 : ℝ) : ℂ) = D * conj D := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hDpos : 0 < ‖D‖ := norm_pos_iff.2 hDne
    have e1 : ‖deriv T ζ‖ ^ 2 = (1 - ‖z‖ ^ 2) ^ 2 / (‖D‖ ^ 2) ^ 2 := by
      rw [show deriv T ζ = (1 - z * conj z) / (conj z * ζ + 1) ^ 2 from gl3_aut_deriv hD, ← hDdef, hzz,
        norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
      ring
    have e2 : 1 - ‖T ζ‖ ^ 2 = (1 - ‖z‖ ^ 2) * (1 - ‖ζ‖ ^ 2) / ‖D‖ ^ 2 := by
      have hid := gl3_normSq_aut ζ z
      simp only [Complex.normSq_eq_norm_sq] at hid
      rw [← hDdef] at hid
      have hTn : ‖T ζ‖ = ‖ζ + z‖ / ‖D‖ := by
        rw [hT]
        simp only
        rw [norm_div, ← hDdef]
      rw [eq_div_iff (by positivity), hTn, div_pow, sub_mul, one_mul, div_mul_cancel₀ _ (by positivity)]
      linear_combination hid
    have e3 : (1 - z * conj (T ζ))⁻¹ = conj D / ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
      have h1 : 1 - z * conj (T ζ) = (1 - z * conj z) / conj D := by
        rw [hT]
        simp only
        rw [map_div₀, map_add, map_add, map_mul, Complex.conj_conj, map_one, ← hDc, eq_div_iff hDcne, sub_mul,
          one_mul, mul_assoc, div_mul_cancel₀ _ hDcne, hDc]
        ring
      rw [h1, inv_div, hzz]
    rw [e1, e2, e3, Complex.real_smul]
    push_cast
    push_cast at hN
    rw [hN]
    have hA' : (1 : ℂ) - (‖z‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hA.ne'
    rw [← hDdef]
    field_simp
  -- `(1 − |ζ|²)² (z̄ζ + 1)⁻⁴ φ(Tζ)` is holomorphic times the weight, and integrable
  set F : ℂ → ℂ := fun ζ => (conj z * ζ + 1)⁻¹ ^ 4 * φ (T ζ) with hFdef
  have hFd : DifferentiableOn ℂ F unitDisc := by
    intro ζ hζ
    have h1 : DifferentiableAt ℂ (fun ζ => (conj z * ζ + 1)⁻¹ ^ 4) ζ :=
      (((differentiableAt_id.const_mul (conj z)).add_const 1).inv (hden ζ hζ)).pow 4
    have h2 : DifferentiableAt ℂ (fun ζ => φ (T ζ)) ζ :=
      ((hφ _ (hTmem ζ hζ)).differentiableAt (isOpen_ball.mem_nhds (hTmem ζ hζ))).comp ζ
        ((hconf.1 ζ hζ).differentiableAt (isOpen_ball.mem_nhds hζ))
    exact (h1.mul h2).differentiableWithinAt
  have hint' : IntegrableOn (fun w : ℂ => (1 - ‖w‖ ^ 2) ^ 2 * φ w) unitDisc := hint
  have hintT := (gl3_integrableOn_image_conformal isOpen_ball hconf _).1 hint'
  have hK : ∀ w ∈ unitDisc, ‖(1 - z * conj w)⁻¹ ^ 4‖ ≤ ((1 - ‖z‖) ^ 4)⁻¹ := by
    intro w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    have hlow : 1 - ‖z‖ ≤ ‖1 - z * conj w‖ := by
      have h1 := norm_sub_norm_le (1 : ℂ) (z * conj w)
      rw [norm_one, norm_mul, Complex.norm_conj] at h1
      have : ‖z‖ * ‖w‖ ≤ ‖z‖ := mul_le_of_le_one_right (norm_nonneg _) hw1.le
      linarith
    have hpos : 0 < 1 - ‖z‖ := by linarith
    rw [norm_pow, norm_inv, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hlow 4)
  have hintF : IntegrableOn (fun ζ => (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) * F ζ) unitDisc := by
    refine Integrable.mono' (hintT.norm.const_mul ((1 - ‖z‖) ^ 4)⁻¹)
      ((by fun_prop : Continuous fun ζ : ℂ => (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ)).continuousOn.mul
        hFd.continuousOn |>.aestronglyMeasurable isOpen_ball.measurableSet) ?_
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with ζ hζ
    rw [hFdef]
    simp only
    rw [← hkey ζ hζ, norm_smul, norm_smul, norm_mul, norm_mul, norm_mul]
    have hnn : ‖(((1 - ‖T ζ‖ ^ 2) ^ 2 : ℝ) : ℂ)‖ = ‖(1 - (‖T ζ‖ : ℂ) ^ 2) ^ 2‖ := by
      congr 1
      push_cast
      ring
    rw [hnn]
    have hk := hK _ (hTmem ζ hζ)
    have h0 : 0 ≤ ‖(‖deriv T ζ‖ ^ 2 : ℝ)‖ * (‖(1 - (‖T ζ‖ : ℂ) ^ 2) ^ 2‖ * ‖φ (T ζ)‖) := by positivity
    calc ‖(‖deriv T ζ‖ ^ 2 : ℝ)‖ * (‖(1 - (‖T ζ‖ : ℂ) ^ 2) ^ 2‖ * ‖(1 - z * conj (T ζ))⁻¹ ^ 4‖ * ‖φ (T ζ)‖)
        = ‖(1 - z * conj (T ζ))⁻¹ ^ 4‖ * (‖(‖deriv T ζ‖ ^ 2 : ℝ)‖ * (‖(1 - (‖T ζ‖ : ℂ) ^ 2) ^ 2‖ * ‖φ (T ζ)‖)) := by
          ring
      _ ≤ ((1 - ‖z‖) ^ 4)⁻¹ * (‖(‖deriv T ζ‖ ^ 2 : ℝ)‖ * (‖(1 - (‖T ζ‖ : ℂ) ^ 2) ^ 2‖ * ‖φ (T ζ)‖)) :=
          mul_le_mul_of_nonneg_right hk h0
  -- the change of variables `w = T(ζ)` and the weighted mean value at `0`
  have hcv := gl3_integral_image_conformal isOpen_ball hconf
    (fun w => (((1 - ‖w‖ ^ 2) ^ 2 : ℝ) : ℂ) * (1 - z * conj w)⁻¹ ^ 4 * φ w)
  beta_reduce at hcv
  have hT0 : T 0 = z := by rw [hT]; simp
  have hwm := gl3_weighted_mean hFd hintF
  rw [show unitDisc = ball (0 : ℂ) 1 from rfl, hFdef] at hwm
  beta_reduce at hwm
  rw [hcv, setIntegral_congr_fun isOpen_ball.measurableSet hkey, hwm]
  simp only [mul_zero, zero_add, inv_one, one_pow, one_mul, hT0]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  field_simp

/-- **Corollary 1** (§3.2, l. 2334). For every hyperbolic Riemann surface `R`, `A(R)` is separable. -/
theorem cor3_4_1 {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] (hhyp : ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
      (p : UpperHalfPlane → R), IsFuchsian Γ ∧ ActsFreely Γ ∧ IsUniformization Γ p) :
    ∃ D ⊆ integrableHolQDSet R, D.Countable ∧
      ∀ φ ∈ integrableHolQDSet R, ∀ ε > (0 : ℝ≥0∞), ∃ ψ ∈ D, quadDiffNorm (φ - ψ) < ε := by
  -- a uniformized surface is second countable and nonempty; `A(R)` embeds isometrically into `L¹` of a subset of `ℂ`
  obtain ⟨_, p, -, -, hp⟩ := hhyp
  have := gl31_secondCountable hp
  have : Nonempty R := ⟨p UpperHalfPlane.I⟩
  exact gl31_separable

end GardinerLakic2000
