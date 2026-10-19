import LiZhongQC.Ch11.S36_Hamilton
import LiZhongQC.Lemmas.LowGenusQC
import LiZhongQC.Lemmas.FinitePunctureCompactification

/- Source: FoundationElementary.lean -/
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- An element of `SL(2, ℝ)` acting on `ℍ` as `τ ↦ τ + k` is `±(1 k; 0 1)` in coordinates. -/
theorem ft1e_translation_entries {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {k : ℝ}
    (h : ∀ τ : UpperHalfPlane, δ • τ = k +ᵥ τ) :
    δ 1 0 = 0 ∧ δ 1 1 = δ 0 0 ∧ δ 0 1 = k * δ 0 0 := by
  have key : ∀ τ : UpperHalfPlane,
      (δ 0 0 : ℂ) * τ + δ 0 1 = ((k : ℂ) + τ) * ((δ 1 0 : ℂ) * τ + δ 1 1) := by
    intro τ
    have h1 := congrArg (fun σ : UpperHalfPlane => (σ : ℂ)) (h τ)
    simp only [h36t_coe_smul, UpperHalfPlane.coe_vadd] at h1
    rw [div_eq_iff (h36t_den_ne δ τ)] at h1
    exact h1
  have h1 := key UpperHalfPlane.I
  have h2 := key (UpperHalfPlane.mk (2 * Complex.I) (by simp))
  have e1 := congrArg Complex.re h1
  have e2 := congrArg Complex.im h1
  have e3 := congrArg Complex.re h2
  norm_num [mul_pow] at e1 e2 e3
  have hc : δ 1 0 = 0 := by linarith
  refine ⟨hc, ?_, ?_⟩
  · rw [hc] at e2
    linarith
  · rw [hc] at e1
    have hd : δ 1 1 = δ 0 0 := by rw [hc] at e2; linarith
    rw [← hd]
    linarith

/-- Iterates of the parabolic `π₀` (acting as `τ ↦ τ + 1` in the coordinate `A`) act as `τ ↦ τ + k`. -/
theorem ft1e_zpow_smul {A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hπ : ∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ)) (k : ℤ) (τ : UpperHalfPlane) :
    π₀ ^ k • (A • τ) = A • ((k : ℝ) +ᵥ τ) := by
  induction k using Int.induction_on generalizing τ with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, mul_smul, hπ, ih, vadd_vadd]
    congr 2
    push_cast
    ring
  | pred k ih =>
    have hinv : π₀⁻¹ • (A • τ) = A • ((-1 : ℝ) +ᵥ τ) := by
      have := hπ ((-1 : ℝ) +ᵥ τ)
      rw [vadd_vadd, show (1 : ℝ) + -1 = 0 by ring, zero_vadd] at this
      rw [← this, inv_smul_smul]
    rw [zpow_sub_one, mul_smul, hinv, ih, vadd_vadd]
    congr 2
    push_cast
    ring

/-- A parabolic power `±π₀^k`, `k ≠ 0`, fixes only the cusp `A • ∞` of `ℂ̂`. -/
theorem ft1e_fix_unique {A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hπ : ∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ)) {k : ℤ} (hk : k ≠ 0)
    {s : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hs : s = π₀ ^ k ∨ s = -π₀ ^ k) {y : ExtPlane}
    (hy : mobiusSL (slRealToComplex s) y = y) : y = mobiusSL (slRealToComplex A) extInf := by
  set δ : Matrix.SpecialLinearGroup (Fin 2) ℝ := A⁻¹ * s * A with hδ
  have hδτ : ∀ τ : UpperHalfPlane, δ • τ = (k : ℝ) +ᵥ τ := by
    intro τ
    have hsA : s • (A • τ) = A • ((k : ℝ) +ᵥ τ) := by
      rcases hs with rfl | rfl
      · exact ft1e_zpow_smul hπ k τ
      · rw [s30l_neg_smul]
        exact ft1e_zpow_smul hπ k τ
    rw [hδ, mul_smul, mul_smul, hsA, inv_smul_smul]
  obtain ⟨hc, hd, hb⟩ := ft1e_translation_entries hδτ
  have ha : δ 0 0 ≠ 0 := by
    intro h0
    have hdet := k24_det_realR δ
    rw [hc, h0] at hdet
    simp at hdet
  -- conjugate the fixed point by `A`
  set y' := mobiusSL (slRealToComplex A⁻¹) y with hy'
  have hmap : slRealToComplex δ = (slRealToComplex A)⁻¹ * slRealToComplex s * slRealToComplex A := by
    simp only [hδ, slRealToComplex, map_mul, map_inv]
  have hfix : mobiusSL (slRealToComplex δ) y' = y' := by
    have hinvA : slRealToComplex A⁻¹ = (slRealToComplex A)⁻¹ := by
      simp only [slRealToComplex, map_inv]
    rw [hmap, k24_mobiusSL_mul, k24_mobiusSL_mul, hy', hinvA, k24_mobiusSL_apply_inv, hy]
  have hy_eq : y = mobiusSL (slRealToComplex A) y' := by
    have hinvA : slRealToComplex A⁻¹ = (slRealToComplex A)⁻¹ := by
      simp only [slRealToComplex, map_inv]
    rw [hy', hinvA, k24_mobiusSL_apply_inv]
  by_cases hinf : y' = OnePoint.infty
  · simpa only [hinf] using hy_eq
  · obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.1 hinf
    exfalso
    have hdetC : (δ 0 0 : ℂ) * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by exact_mod_cast k24_det_realR δ
    have hmem : ((z : ℂ) : ExtPlane) ∈ mobiusFixedPoints (δ 0 0) (δ 0 1) (δ 1 0) (δ 1 1) := by
      show mobiusExt _ _ _ _ _ = _
      rw [← k24_mobiusSL_real]
      simpa only [← hz] using hfix
    have hpoly := (mem_mobiusFixedPoints_coe_iff hdetC z).1 hmem
    rw [hc, hd, hb] at hpoly
    push_cast at hpoly
    have hk0 : ((k : ℝ) : ℂ) * (δ 0 0 : ℂ) = 0 := by linear_combination -hpoly
    rcases mul_eq_zero.1 hk0 with h | h
    · exact hk (by exact_mod_cast h)
    · exact ha (by exact_mod_cast h)

/-- **F1e (elementary groups are of the second kind).**  If `Γ` is trivial up to sign or cyclic parabolic, `Γ` has
ordinary points on `ℝ̂` (the limit set is empty, resp. the parabolic fixed point). -/
theorem ft1_elementary_ordinary (hΓ : IsFuchsian Γ)
    (hel : (∀ γ ∈ Γ, γ = 1 ∨ γ = -1) ∨
      ∃ A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ, π₀ ∈ Γ ∧
        (∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ)) ∧
        ∀ γ ∈ Γ, ∃ k : ℤ, γ = π₀ ^ k ∨ γ = -π₀ ^ k) :
    (ordinarySet Γ).Nonempty := by
  -- the limit set lies in a single point `ξ`
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ExtPlane, fuchsianLimitSet Γ ⊆ {ξ} := by
    have hcl := h36q_limitSet_subset_closure_fix hΓ
    rcases hel with htriv | ⟨A, π₀, -, hπ, hcyc⟩
    · refine ⟨extInf, hcl.trans ?_⟩
      have hempty : {y : ExtPlane | y ∈ closure (toExt upperHalf) ∧
          ∃ γ ∈ Γ, γ ≠ 1 ∧ γ ≠ -1 ∧ mobiusSL (slRealToComplex γ) y = y} = ∅ := by
        ext y
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_exists]
        intro _ γ hγ h1 h2
        rcases htriv γ hγ with h | h
        · exact absurd h h1
        · exact absurd h h2
      rw [hempty, closure_empty]
      exact empty_subset _
    · refine ⟨mobiusSL (slRealToComplex A) extInf, hcl.trans ?_⟩
      rw [← closure_singleton (x := mobiusSL (slRealToComplex A) extInf)]
      refine closure_mono ?_
      rintro y ⟨-, γ, hγ, h1, h2, hfix⟩
      obtain ⟨k, hk⟩ := hcyc γ hγ
      have hk0 : k ≠ 0 := by
        rintro rfl
        rcases hk with h | h
        · exact h1 (by simpa using h)
        · exact h2 (by simpa using h)
      exact ft1e_fix_unique hπ hk0 hk hfix
  -- a real point other than `ξ`
  obtain ⟨r, hr⟩ : ∃ r : ℝ, (((r : ℂ)) : ExtPlane) ≠ ξ := by
    by_cases h0 : (((0 : ℝ) : ℂ) : ExtPlane) = ξ
    · refine ⟨1, fun h1 => ?_⟩
      have := OnePoint.coe_injective (h1.trans h0.symm)
      norm_num at this
    · exact ⟨0, h0⟩
  refine ⟨((r : ℂ) : ExtPlane), ?_, fun h => hr (hξ h)⟩
  exact Or.inl ⟨(r : ℂ), by simp [realLine], rfl⟩

end LiZhongQC
end -- source noncomputable section

/- Source: FoundationFunnel.lean -/
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Iterates of `h₀` (acting as `z ↦ lam * z` in the coordinate `B`) act as `z ↦ lam ^ k * z`. -/
theorem ft4a_scale_zpow {B h₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {lam : ℝ}
    (hscale : ∀ τ : UpperHalfPlane, ((B⁻¹ • (h₀ • (B • τ)) : UpperHalfPlane) : ℂ) = (lam : ℂ) * (τ : ℂ))
    (k : ℤ) (τ : UpperHalfPlane) :
    ((B⁻¹ • (h₀ ^ k • (B • τ)) : UpperHalfPlane) : ℂ) = (lam : ℂ) ^ k * (τ : ℂ) := by
  have hlam : (lam : ℂ) ≠ 0 := by
    intro h0
    have := hscale UpperHalfPlane.I
    rw [h0, zero_mul] at this
    exact (B⁻¹ • (h₀ • (B • UpperHalfPlane.I))).ne_zero this
  induction k using Int.induction_on generalizing τ with
  | zero => simp
  | succ k ih =>
    set σ : UpperHalfPlane := B⁻¹ • (h₀ • (B • τ)) with hσ
    have hBσ : h₀ • (B • τ) = B • σ := by rw [hσ, smul_inv_smul]
    rw [zpow_add_one, mul_smul, hBσ, ih σ, hσ, hscale, zpow_add_one₀ hlam]
    ring
  | pred k ih =>
    set σ : UpperHalfPlane := B⁻¹ • (h₀⁻¹ • (B • τ)) with hσ
    have hBσ : h₀⁻¹ • (B • τ) = B • σ := by rw [hσ, smul_inv_smul]
    have hσv : (σ : ℂ) = (τ : ℂ) / lam := by
      have h1 := hscale σ
      rw [← hBσ, smul_inv_smul, inv_smul_smul] at h1
      field_simp
      rw [h1]
      ring
    rw [zpow_sub_one, mul_smul, hBσ, ih σ, hσv, zpow_sub_one₀ hlam]
    field_simp

/-- The actual point B(1) is ordinary under the funnel precision hypotheses.
Extracted from the existing F4a proof; the frozen existential theorem is its one-line wrapper. -/
theorem ft4a_one_ordinary (hΓ : IsFuchsian Γ) (B h₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam θ : ℝ)
    (hh : h₀ ∈ Γ) (hlam : 1 < lam) (hθ0 : 0 < θ) (hθπ : θ < π)
    (hscale : ∀ τ : UpperHalfPlane, ((B⁻¹ • (h₀ • (B • τ)) : UpperHalfPlane) : ℂ) = (lam : ℂ) * (τ : ℂ))
    (hprec : ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, arg (τ : ℂ) < θ →
        arg ((B⁻¹ • (γ • (B • τ)) : UpperHalfPlane) : ℂ) < θ → ∃ k : ℤ, γ = h₀ ^ k ∨ γ = -h₀ ^ k) :
    mobiusSL (slRealToComplex B) ((1 : ℂ) : ExtPlane) ∈ ordinarySet Γ := by
  -- `_hh`, `hθπ` are not needed: the sector's precise invariance alone makes `B • 1` ordinary
  have _hh := hh
  have _hθπ := hθπ
  set u : ExtPlane := mobiusSL (slRealToComplex B) (((1 : ℝ) : ℂ) : ExtPlane) with hu
  have hinvB : slRealToComplex B⁻¹ = (slRealToComplex B)⁻¹ := by
    simp only [slRealToComplex, map_inv]
  have hu1 : mobiusSL (slRealToComplex B⁻¹) u = (((1 : ℝ) : ℂ) : ExtPlane) := by
    rw [hu, hinvB, k24_mobiusSL_inv_apply]
  change u ∈ ordinarySet Γ
  refine ⟨?_, fun huΛ => ?_⟩
  · -- `B • 1 ∈ ℝ̂`
    rw [hu, k24_mobiusSL_real]
    by_cases hden : B 1 0 * 1 + B 1 1 = 0
    · rw [mobiusExt_ofReal_coe_of_eq_zero hden]
      exact Or.inr rfl
    · rw [mobiusExt_ofReal_coe hden]
      exact Or.inl ⟨_, by simp [realLine, Complex.div_im], rfl⟩
  -- an injective orbit sequence of `i` converging to `u`
  obtain ⟨γs, hinj, hlim⟩ := k22_t_limitSet_subset_orbitLim (k24_c_I_not_mem_limitSet hΓ) huΛ
  choose γr hγrΓ hγr using fun n => Subgroup.mem_map.1 (γs n).2
  have hγrinj : Function.Injective γr := fun n m h =>
    hinj (Subtype.ext (by rw [← hγr n, ← hγr m, h]))
  -- `w n = B⁻¹ γr n i → 1`
  set w : ℕ → UpperHalfPlane := fun n => B⁻¹ • (γr n • UpperHalfPlane.I) with hw
  have hwlim : Tendsto (fun n => ((w n : UpperHalfPlane) : ℂ)) atTop (𝓝 1) := by
    have hcont : Continuous (mobiusSL (slRealToComplex B⁻¹)) := by
      rw [k24_mobiusSL_real]
      refine continuous_mobiusExt ?_
      exact_mod_cast (k24_det_realR B⁻¹).symm ▸ one_ne_zero
    have h1 := (hcont.tendsto u).comp hlim
    rw [hu1] at h1
    have h2 : (fun n => mobiusSL (slRealToComplex B⁻¹) (mobiusSL (γs n) ((Complex.I : ℂ) : ExtPlane))) =
        fun n => ((((w n : UpperHalfPlane) : ℂ)) : ExtPlane) := by
      funext n
      have hI : ((Complex.I : ℂ) : ExtPlane) = (((UpperHalfPlane.I : UpperHalfPlane) : ℂ) : ExtPlane) := rfl
      rw [hI, ← hγr n]
      show mobiusSL (slRealToComplex B⁻¹) (mobiusSL (slRealToComplex (γr n)) _) = _
      rw [h36t_mobiusSL_coe, h36t_mobiusSL_coe]
    rw [Function.comp_def, h2] at h1
    have h3 := (OnePoint.isOpenEmbedding_coe (X := ℂ)).isInducing.tendsto_nhds_iff.2 h1
    simpa using h3
  -- eventually `w n` lies in the sector
  have hsec : ∀ᶠ n in atTop, arg ((w n : UpperHalfPlane) : ℂ) < θ := by
    have harg : ContinuousAt arg (1 : ℂ) := Complex.continuousAt_arg (by simp)
    have := (harg.tendsto.comp hwlim).eventually (gt_mem_nhds (by simpa using hθ0 : arg (1 : ℂ) < θ))
    exact this
  -- eventually `|log |w n|| < log lam / 2`
  have hlog : ∀ᶠ n in atTop, |Real.log ‖((w n : UpperHalfPlane) : ℂ)‖| < Real.log lam / 2 := by
    have hl : Tendsto (fun n => Real.log ‖((w n : UpperHalfPlane) : ℂ)‖) atTop (𝓝 0) := by
      have hn : Tendsto (fun n => ‖(w n : ℂ)‖) atTop (𝓝 (1 : ℝ)) := by
        simpa using hwlim.norm
      have hl := (Real.continuousAt_log (one_ne_zero : (1 : ℝ) ≠ 0)).tendsto.comp hn
      simpa only [Function.comp_def, Real.log_one] using hl
    have hpos : 0 < Real.log lam / 2 := by have := Real.log_pos hlam; linarith
    filter_upwards [hl.eventually (Metric.ball_mem_nhds 0 hpos)] with n hn
    simpa [Real.dist_eq] using hn
  obtain ⟨N, hN⟩ := (hsec.and hlog).exists_forall_of_atTop
  -- each `γr n γr N⁻¹` is `±h₀^(k n)`, and `w n = lam^(k n) w N`
  have hk : ∀ n, N ≤ n → ∃ k : ℤ, (γr n = h₀ ^ k * γr N ∨ γr n = -h₀ ^ k * γr N) ∧
      ((w n : UpperHalfPlane) : ℂ) = (lam : ℂ) ^ k * ((w N : UpperHalfPlane) : ℂ) := by
    intro n hn
    have hwn : B⁻¹ • ((γr n * (γr N)⁻¹) • (B • w N)) = w n := by
      simp only [hw, smul_inv_smul, mul_smul, inv_smul_smul]
    obtain ⟨k, hk⟩ := hprec (γr n * (γr N)⁻¹) (Γ.mul_mem (hγrΓ n) (Γ.inv_mem (hγrΓ N))) (w N) (hN N le_rfl).1
      (by rw [hwn]; exact (hN n hn).1)
    refine ⟨k, ?_, ?_⟩
    · rcases hk with h | h
      · left
        rw [← h, inv_mul_cancel_right]
      · right
        rw [← h, inv_mul_cancel_right]
    · rw [← hwn]
      rcases hk with h | h
      · rw [h, ft4a_scale_zpow hscale]
      · rw [h, s30l_neg_smul, ft4a_scale_zpow hscale]
  -- the exponents are eventually constant
  have hlamlog : 0 < Real.log lam := Real.log_pos hlam
  have hwN0 : ((w N : UpperHalfPlane) : ℂ) ≠ 0 := (w N).ne_zero
  have hlogk : ∀ n, N ≤ n → ∀ k : ℤ, ((w n : UpperHalfPlane) : ℂ) = (lam : ℂ) ^ k * ((w N : UpperHalfPlane) : ℂ) →
      Real.log ‖((w n : UpperHalfPlane) : ℂ)‖ = k * Real.log lam + Real.log ‖((w N : UpperHalfPlane) : ℂ)‖ := by
    intro n _ k hk
    rw [hk, norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith),
      Real.log_mul (zpow_ne_zero _ (by linarith)) (norm_ne_zero_iff.2 hwN0), Real.log_zpow]
  have hsame : ∀ (n m : ℕ) (k₁ k₂ : ℤ), N ≤ n → N ≤ m →
      ((w n : UpperHalfPlane) : ℂ) = (lam : ℂ) ^ k₁ * ((w N : UpperHalfPlane) : ℂ) →
      ((w m : UpperHalfPlane) : ℂ) = (lam : ℂ) ^ k₂ * ((w N : UpperHalfPlane) : ℂ) → k₁ = k₂ := by
    intro n m k₁ k₂ hn hm h1 h2
    have e1 := hlogk n hn k₁ h1
    have e2 := hlogk m hm k₂ h2
    have b1 := (hN n hn).2
    have b2 := (hN m hm).2
    have hdiff : |((k₁ : ℝ) - k₂)| * Real.log lam < Real.log lam := by
      have : |((k₁ : ℝ) - k₂) * Real.log lam| < Real.log lam := by
        rw [show ((k₁ : ℝ) - k₂) * Real.log lam =
          Real.log ‖((w n : UpperHalfPlane) : ℂ)‖ - Real.log ‖((w m : UpperHalfPlane) : ℂ)‖ by rw [e1, e2]; ring]
        calc _ ≤ |Real.log ‖((w n : UpperHalfPlane) : ℂ)‖| + |Real.log ‖((w m : UpperHalfPlane) : ℂ)‖| :=
              abs_sub _ _
          _ < Real.log lam / 2 + Real.log lam / 2 := add_lt_add b1 b2
          _ = Real.log lam := by ring
      rwa [abs_mul, abs_of_pos hlamlog] at this
    have hlt : |((k₁ : ℝ) - k₂)| < 1 := by
      by_contra hge
      push Not at hge
      nlinarith
    have habs : |k₁ - k₂| < (1 : ℤ) := by exact_mod_cast hlt
    obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
    omega
  -- three indices with the same exponent: two of the `γr` coincide
  obtain ⟨k₀, hk₀, hw₀⟩ := hk N le_rfl
  have hall : ∀ n, N ≤ n → γr n = h₀ ^ k₀ * γr N ∨ γr n = -h₀ ^ k₀ * γr N := by
    intro n hn
    obtain ⟨k, hkn, hwn⟩ := hk n hn
    rwa [hsame n N k k₀ hn le_rfl hwn hw₀] at hkn
  rcases hall N le_rfl with h0 | h0 <;> rcases hall (N + 1) (by omega) with h1 | h1 <;>
    rcases hall (N + 2) (by omega) with h2 | h2
  all_goals first
    | exact absurd (hγrinj (h0.trans h1.symm)) (by omega)
    | exact absurd (hγrinj (h0.trans h2.symm)) (by omega)
    | exact absurd (hγrinj (h1.trans h2.symm)) (by omega)

/-- **F4a (a funnel is ordinary).**  If the sector `{arg < θ}` is precisely invariant under `⟨h₀⟩` (up to sign) in the
coordinate `B`, where `h₀` acts as `z ↦ lam * z`, then the arc `B • (0, ∞)` consists of ordinary points; in particular
`b(Γ) ≠ ∅`. -/
theorem ft4_funnel_ordinary (hΓ : IsFuchsian Γ) (B h₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam θ : ℝ)
    (hh : h₀ ∈ Γ) (hlam : 1 < lam) (hθ0 : 0 < θ) (hθπ : θ < π)
    (hscale : ∀ τ : UpperHalfPlane, ((B⁻¹ • (h₀ • (B • τ)) : UpperHalfPlane) : ℂ) = (lam : ℂ) * (τ : ℂ))
    (hprec : ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, arg (τ : ℂ) < θ →
        arg ((B⁻¹ • (γ • (B • τ)) : UpperHalfPlane) : ℂ) < θ → ∃ k : ℤ, γ = h₀ ^ k ∨ γ = -h₀ ^ k) :
    (ordinarySet Γ).Nonempty := by
  exact ⟨_, ft4a_one_ordinary hΓ B h₀ lam θ hh hlam hθ0 hθπ hscale hprec⟩

end LiZhongQC
end -- source noncomputable section

/- Source: FoundationExceptional.lean -/
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- The inclusion `ℂ → ℂ̂` is holomorphic (it is the inverse of the finite chart). -/
theorem ft5_coe_mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℂ => (z : OnePoint ℂ)) := by
  intro z
  have hz : ((z : OnePoint ℂ)) ∈ (chartAt ℂ ((z : OnePoint ℂ))).source := mem_chart_source ℂ _
  have hzt : z ∈ (chartAt ℂ ((z : OnePoint ℂ))).target := by
    have h := (chartAt ℂ ((z : OnePoint ℂ))).map_source hz
    have e1 : chartAt ℂ ((z : OnePoint ℂ)) = RiemannDynamics.sphereChartFinite := rfl
    rw [e1, RiemannDynamics.sphereChartFinite_coe] at h
    rwa [e1]
  have h := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ)) (chart_mem_atlas ℂ ((z : OnePoint ℂ))) hzt
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
  show (w : OnePoint ℂ) = RiemannDynamics.sphereChartFinite.symm w
  rw [RiemannDynamics.sphereChartFinite_symm_apply]

/-- **Liouville through a uniformization.**  A holomorphic map `ℂ → S` into a surface uniformized by `ℍ` is constant:
it lifts continuously through the covering `p` (`ℂ` is simply connected), the lift is holomorphic (`p` is locally
biholomorphic), and its Cayley transform is a bounded entire function. -/
theorem ft5_entire_const {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {f : ℂ → S} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (z w : ℂ) : f z = f w := by
  obtain ⟨hcov, hpd, hps, -⟩ := hp
  obtain ⟨τ₀, hτ₀⟩ := hps (f 0)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := hcov.existsUnique_continuousMap_lifts ⟨f, hf.continuous⟩ 0 τ₀ hτ₀
  have hFp : ∀ z, p (F z) = f z := fun z => congrFun hF z
  let G : ℂ → ℂ := fun z => ((F z : UpperHalfPlane) : ℂ)
  have hGc : Continuous G := UpperHalfPlane.continuous_coe.comp F.continuous
  -- the lift is entire
  have hGd : Differentiable ℂ G := by
    intro z₀
    obtain ⟨U₀, hU₀o, hwU₀, hinj₀⟩ := hcov.isLocalHomeomorph.isLocallyInjective (F z₀)
    let c := chartAt ℂ (p (F z₀))
    let V : Set ℂ := (fun τ : UpperHalfPlane => (τ : ℂ)) '' (U₀ ∩ p ⁻¹' c.source)
    have hV : IsOpen V := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _
      (hU₀o.inter (c.open_source.preimage hcov.continuous))
    have hGV : G z₀ ∈ V := ⟨F z₀, ⟨hwU₀, mem_chart_source ℂ _⟩, rfl⟩
    refine tor_h_differentiableAt_of_comp_eq (h := fun v => c (p (UpperHalfPlane.ofComplex v)))
      (ψ := fun z => c (f z)) hV ?_ ?_ hGV hGc.continuousAt ?_
      (Eventually.of_forall fun z => by
        show c (p (UpperHalfPlane.ofComplex ((F z : UpperHalfPlane) : ℂ))) = c (f z)
        rw [UpperHalfPlane.ofComplex_apply, hFp])
    · rintro v ⟨τ, hτ, rfl⟩
      have hq : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun v => p (UpperHalfPlane.ofComplex v)) (τ : ℂ) :=
        (hpd _).comp (τ : ℂ) (UpperHalfPlane.mdifferentiableAt_ofComplex τ.im_pos)
      have hmem : (fun v => p (UpperHalfPlane.ofComplex v)) (τ : ℂ) ∈ c.source := by
        show p (UpperHalfPlane.ofComplex (τ : ℂ)) ∈ c.source
        rw [UpperHalfPlane.ofComplex_apply]
        exact hτ.2
      exact (tor_h_differentiableAt_chart_comp hq hmem).differentiableWithinAt
    · rintro v₁ ⟨τ₁, hτ₁, rfl⟩ v₂ ⟨τ₂, hτ₂, rfl⟩ he
      simp only [UpperHalfPlane.ofComplex_apply] at he
      have h12 : p τ₁ = p τ₂ := c.injOn hτ₁.2 hτ₂.2 he
      rw [hinj₀ hτ₁.1 hτ₂.1 h12]
    · refine tor_h_differentiableAt_chart_comp (hf z₀) ?_
      rw [← hFp z₀]
      exact mem_chart_source ℂ _
  -- the Cayley transform of the lift is bounded, hence constant
  have hne : ∀ z, G z + I ≠ 0 := by
    intro z h
    have := congrArg Complex.im h
    simp only [add_im, I_im, zero_im] at this
    have hpos : 0 < (G z).im := (F z).im_pos
    linarith
  let K : ℂ → ℂ := fun z => (G z - I) / (G z + I)
  have hKd : Differentiable ℂ K := fun z => ((hGd z).sub_const I).div ((hGd z).add_const I) (hne z)
  have hKb : Bornology.IsBounded (range K) := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset ?_
    rintro _ ⟨z, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    show ‖(G z - I) / (G z + I)‖ ≤ 1
    rw [norm_div, div_le_one (norm_pos_iff.2 (hne z))]
    have hpos : 0 < (G z).im := (F z).im_pos
    have h1 : ‖G z - I‖ ^ 2 ≤ ‖G z + I‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [sub_re, sub_im, add_re, add_im, I_re, I_im]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
  have hK := hKd.apply_eq_apply_of_bounded hKb z w
  have hG : G z = G w := by
    have hz := hne z
    have hw := hne w
    have h2 : (G z - I) * (G w + I) = (G w - I) * (G z + I) := by
      have := hK
      simp only [K] at this
      rw [div_eq_div_iff hz hw] at this
      linear_combination this
    have h3 : (2 * I) * (G z - G w) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h (mul_ne_zero two_ne_zero I_ne_zero)
    · exact sub_eq_zero.1 h
  have hFzw : F z = F w := UpperHalfPlane.ext hG
  rw [← hFp z, ← hFp w, hFzw]

/-- **F5 (hyperbolic surfaces are not exceptional).**  A surface uniformized by `ℍ` is not of type `(0,0,0)`,
`(0,1,0)`, `(1,0,0)` or `(0,2,0)`: otherwise `ℂ` maps non-constantly and holomorphically to `S` (the sphere model of
genus `0`, `exp`, the torus covering), the map lifts through `p` to `ℍ`, and Liouville makes it constant. -/
theorem ft5_not_exceptional {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {g n : ℕ}
    (hS : IsFiniteType S g n 0) : ¬ IsExceptionalType g n 0 := by
  classical
  intro hex
  obtain ⟨F₀⟩ := hS
  have hr : range F₀.ι = (↑F₀.P : Set F₀.X.carrier)ᶜ := by
    rw [F₀.range_ι]
    simp
  obtain ⟨e, -, g', hg'd, -, hright⟩ := s31hy_homeo_punctured F₀.P F₀.ι F₀.embedding F₀.holomorphic hr
  -- it suffices to find a non-constant holomorphic `ℂ → X` avoiding `P`
  suffices hmain : ∃ f₀ : ℂ → F₀.X.carrier, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₀ ∧ (∀ z, f₀ z ∉ F₀.P) ∧
      ∃ z w, f₀ z ≠ f₀ w by
    obtain ⟨f₀, hf₀d, hf₀P, z, w, hzw⟩ := hmain
    have hmem : ∀ z, f₀ z ∈ puncturedOpens F₀.P := fun z => hf₀P z
    have hcd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => (⟨f₀ z, hmem z⟩ : puncturedOpens F₀.P)) := by
      intro x
      have h := hf₀d x
      rw [mdifferentiableAt_iff] at h ⊢
      exact ⟨(hf₀d.continuous.subtype_mk hmem).continuousAt, h.2⟩
    have hconst := ft5_entire_const hp (hg'd.comp hcd) z w
    have h2 := congrArg e hconst
    simp only [Function.comp_apply, hright _] at h2
    exact hzw (congrArg Subtype.val h2)
  have hcase : (g = 0 ∧ n ≤ 2) ∨ (g = 1 ∧ n = 0) := by
    simp only [IsExceptionalType, Prod.mk.injEq] at hex
    omega
  rcases hcase with ⟨rfl, hn⟩ | ⟨rfl, rfl⟩
  · -- genus `0`: `X ≅ ℂ̂`; move one puncture to `∞`, the other one (if any) to `b`, and use `z ↦ b + e^z`
    obtain ⟨c, hcd, c', hc'd, hcl, hcr⟩ := s24q_sphere_model F₀.genus
    have hP2 : F₀.P.card ≤ 2 := by rw [F₀.card_P]; exact hn
    obtain ⟨T, hTd, T', hT'd, hTl, hTr, b, hTb⟩ : ∃ T : OnePoint ℂ → OnePoint ℂ,
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) T ∧ ∃ T' : OnePoint ℂ → OnePoint ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) T' ∧
        Function.LeftInverse T' T ∧ Function.RightInverse T' T ∧
        ∃ b : ℂ, ∀ x ∈ F₀.P, T (c x) = OnePoint.infty ∨ T (c x) = (b : OnePoint ℂ) := by
      rcases F₀.P.eq_empty_or_nonempty with hP | ⟨x₁, hx₁⟩
      · obtain ⟨T, -, hTd, T', hT'd, hTl, hTr⟩ := s24q_mb_homeo 1
        exact ⟨T, hTd, T', hT'd, hTl, hTr, 0, fun x hx => by simp [hP] at hx⟩
      -- a Möbius map `T₀` sending `c x₁` to `∞`
      obtain ⟨T₀, hT0inf, hT₀d, T₀', hT₀'d, hT₀l, hT₀r⟩ : ∃ T₀ : OnePoint ℂ → OnePoint ℂ,
          T₀ (c x₁) = OnePoint.infty ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) T₀ ∧
          ∃ T₀' : OnePoint ℂ → OnePoint ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) T₀' ∧
            Function.LeftInverse T₀' T₀ ∧ Function.RightInverse T₀' T₀ := by
        by_cases hcx : c x₁ = OnePoint.infty
        · obtain ⟨T, hT, hTd, T', hT'd, hTl, hTr⟩ := s24q_mb_homeo 1
          refine ⟨T, ?_, hTd, T', hT'd, hTl, hTr⟩
          rw [hT, hcx]
          show mobiusExt _ _ _ _ extInf = extInf
          exact mobiusExt_infty_of_eq (by simp)
        · obtain ⟨a, ha⟩ := OnePoint.ne_infty_iff_exists.1 hcx
          let γ : Matrix.SpecialLinearGroup (Fin 2) ℂ := ⟨!![0, 1; -1, a], by simp [Matrix.det_fin_two]⟩
          obtain ⟨T, hT, hTd, T', hT'd, hTl, hTr⟩ := s24q_mb_homeo γ
          refine ⟨T, ?_, hTd, T', hT'd, hTl, hTr⟩
          rw [hT, ← ha]
          show mobiusExt _ _ _ _ ((a : ℂ) : ExtPlane) = extInf
          exact mobiusExt_coe_of_eq_zero (by simp [γ])
      refine ⟨T₀, hT₀d, T₀', hT₀'d, hT₀l, hT₀r, ?_⟩
      rcases (F₀.P.erase x₁).eq_empty_or_nonempty with hE | ⟨x₂, hx₂⟩
      · refine ⟨0, fun x hx => Or.inl ?_⟩
        have : x = x₁ := by
          by_contra hne
          have : x ∈ F₀.P.erase x₁ := Finset.mem_erase.2 ⟨hne, hx⟩
          simp [hE] at this
        rw [this, hT0inf]
      · have hx₂ne : x₂ ≠ x₁ := (Finset.mem_erase.1 hx₂).1
        have hfin : T₀ (c x₂) ≠ OnePoint.infty := by
          intro h
          rw [← hT0inf] at h
          exact hx₂ne (c.injective (hT₀l.injective h))
        obtain ⟨b, hb⟩ : ∃ b : ℂ, T₀ (c x₂) = (b : OnePoint ℂ) := by
          obtain ⟨b, hb⟩ := OnePoint.ne_infty_iff_exists.1 hfin
          exact ⟨b, hb.symm⟩
        refine ⟨b, fun x hx => ?_⟩
        by_cases hx1 : x = x₁
        · exact Or.inl (hx1 ▸ hT0inf)
        · right
          have hcard : (F₀.P.erase x₁).card ≤ 1 := by
            rw [Finset.card_erase_of_mem hx₁]
            omega
          have : x = x₂ := Finset.card_le_one.1 hcard x (Finset.mem_erase.2 ⟨hx1, hx⟩) x₂ hx₂
          rw [this, hb]
    refine ⟨fun z => c' (T' ((b + Complex.exp z : ℂ) : OnePoint ℂ)), ?_, ?_, ?_⟩
    · exact hc'd.comp (hT'd.comp (ft5_coe_mdifferentiable.comp
        ((differentiable_const b).add Complex.differentiable_exp).mdifferentiable))
    · intro z hz
      have h1 : T (c (c' (T' ((b + Complex.exp z : ℂ) : OnePoint ℂ)))) = ((b + Complex.exp z : ℂ) : OnePoint ℂ) := by
        rw [hcr, hTr]
      rcases hTb _ hz with h | h
      · rw [h1] at h
        exact OnePoint.coe_ne_infty _ h
      · rw [h1] at h
        have := OnePoint.coe_injective h
        exact Complex.exp_ne_zero z (by linear_combination this)
    · refine ⟨0, Complex.log 2, fun h => ?_⟩
      have h3 := OnePoint.coe_injective (hTr.injective (hcr.injective h))
      rw [Complex.exp_zero, Complex.exp_log two_ne_zero] at h3
      norm_num at h3
  · -- genus `1`: the torus covering `ℂ → X`
    obtain ⟨-, q, -, hqd, hqs, -⟩ := s24q_torus_cover F₀.genus
    have hP : F₀.P = ∅ := Finset.card_eq_zero.1 F₀.card_P
    refine ⟨q, hqd, fun z => by simp [hP], ?_⟩
    obtain ⟨x⟩ := (inferInstance : Nonempty F₀.X.carrier)
    haveI : NeBot (𝓝[≠] x) := s31cg_punctured_nhds_neBot x
    obtain ⟨y, hy⟩ := (𝓝[≠] x).nonempty_of_mem self_mem_nhdsWithin
    obtain ⟨z, hz⟩ := hqs x
    obtain ⟨w, hw⟩ := hqs y
    exact ⟨z, w, by rw [hz, hw]; exact fun h => hy h.symm⟩

end LiZhongQC
end -- source noncomputable section
