import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.FoundationCuspEnds
import LiZhongQC.Lemmas.StrebelDoubleDomain
import LiZhongQC.Lemmas.F1CuspFamilySupport

/-! D1 C producer: upper and mirror cusp charts through local logarithm branches,
with no stub imports. Escape at real ordinary points uses the cusp-family
avoidance of F1CuspFamilySupport; at interior points it uses the cusp normal form
of FoundationCuspEnds for an auxiliary uniformization (ft0_quotient). -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- A real Möbius denominator does not vanish off the real axis. -/
theorem s36d1c_den_ne (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (g 1 0 : ℂ) * z + g 1 1 ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, zero_im] at him
  have hc : g 1 0 = 0 := by
    rcases mul_eq_zero.1 him with h0 | h0
    · exact h0
    · exact absurd h0 hz
  simp only [add_re, mul_re, ofReal_re, ofReal_im, hc, zero_mul, sub_zero, zero_add, zero_re] at hre
  have hdet := b33_d_det g
  rw [hc, hre] at hdet
  simp at hdet

/-- A real Möbius map sends the upper half-plane to itself. -/
theorem s36d1c_m_im_pos (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) {y : ℂ} (hy : 0 < y.im) :
    0 < (h36p_m g y).im := by
  have h := (g • (⟨y, hy⟩ : UpperHalfPlane)).im_pos
  change 0 < ((g • (⟨y, hy⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ).im at h
  rw [← h36p_m_coe] at h
  exact h

/-- C. Construct both cusp families from width-one normal forms and precise
invariance. Descend local logarithm branches through translation periodicity;
there is no global holomorphic lift to a horoball. The mirror chart conjugates
both the lift and disk coordinate, so it is holomorphic. A uniform q < 1 covers
all height-above-two tails. No funnel or ordinary-arc coverage is needed. -/
theorem s36d1_cusp_charts {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {E : Finset ℝ}
    (hE : ∀ e ∈ E, (((e : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ)
    {Ω : Set ℂ}
    (hΩ : ∀ z : ℂ, z ∈ Ω ↔ ((z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
      (∀ γ ∈ Γ, ∀ s ∈ E, (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) ∧
      (∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ))))
    {P : ℂ → S} (hPsurj : P '' Ω = univ)
    (hPfib : ∀ z ∈ Ω, ∀ w ∈ Ω, (P z = P w ↔ ∃ γ ∈ Γ, w = h36p_m γ z))
    (hPloc : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    {c : ℕ} (A π₀ : Fin c → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hcusp : ∀ i, π₀ i ∈ Γ ∧ ∀ τ : UpperHalfPlane,
      π₀ i • (A i • τ) = A i • ((1 : ℝ) +ᵥ τ))
    (hpc : ∀ i i' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im →
      1 < ((A i')⁻¹ • (γ • (A i • τ))).im →
      i = i' ∧ ∃ t : ℤ, γ = π₀ i ^ t ∨ γ = -π₀ i ^ t) :
    ∃ (χ : (Fin c ⊕ Fin c) → ℂ → S) (q : ℝ), 0 < q ∧ q < 1 ∧
      (∀ i, InjOn (χ i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (χ i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧
      ∀ V : Set ℂ, IsOpen V → V ⊆ {w | w ≠ 0 ∧ ‖w‖ < 1} → IsOpen (χ i '' V)) ∧
      (∀ i j, i ≠ j →
      Disjoint (χ i '' {w | w ≠ 0 ∧ ‖w‖ < 1}) (χ j '' {w | w ≠ 0 ∧ ‖w‖ < 1})) ∧
      (∀ x : S, ∃ N ∈ 𝓝 x, ∃ δ > (0 : ℝ),
      ∀ i w, w ≠ 0 → ‖w‖ < 1 → χ i w ∈ N → δ ≤ ‖w‖) ∧
      ((∀ i w, w ≠ 0 → ‖w‖ < 1 → ∃ τ : UpperHalfPlane,
        1 < τ.im ∧ χ (Sum.inl i) w = P ((A i • τ : UpperHalfPlane) : ℂ)) ∧
      (∀ i w, w ≠ 0 → ‖w‖ < 1 → ∃ τ : UpperHalfPlane,
        1 < τ.im ∧ χ (Sum.inr i) w = P (conj ((A i • τ : UpperHalfPlane) : ℂ)))) ∧
      (∀ i (τ : UpperHalfPlane), 2 < τ.im →
      (∃ w : ℂ, w ≠ 0 ∧ ‖w‖ ≤ q ∧ χ (Sum.inl i) w = P ((A i • τ : UpperHalfPlane) : ℂ)) ∧
      (∃ w : ℂ, w ≠ 0 ∧ ‖w‖ ≤ q ∧ χ (Sum.inr i) w = P (conj ((A i • τ : UpperHalfPlane) : ℂ)))) := by
  classical
  -- `hE` only fixes the domain `Ω`; the cusp charts never meet the removed real orbits.
  have _hE := hE
  have hΩim : ∀ z : ℂ, z.im ≠ 0 → z ∈ Ω := (s36a_omega hΓ hΩ).1
  have hUΩ : ∀ x : UpperHalfPlane, (x : ℂ) ∈ Ω := fun x => hΩim _ x.im_pos.ne'
  have hLΩ : ∀ x : UpperHalfPlane, conj (x : ℂ) ∈ Ω := fun x => hΩim _ (by
    rw [Complex.conj_im]
    exact neg_ne_zero.2 x.im_pos.ne')
  have hmconj : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ),
      h36p_m γ (conj z) = conj (h36p_m γ z) := fun γ z => b33_e_mobius_conj γ z
  have h2π : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  -- `P` is holomorphic and open on `Ω`
  have hPat : ∀ z ∈ Ω, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) P z := by
    intro z hz
    obtain ⟨d, hzd, hdΩ, hPd, hd, hdi⟩ := hPloc z hz
    have hevent : P =ᶠ[𝓝 z] d := by
      filter_upwards [d.open_source.mem_nhds hzd] with w hw
      exact hPd hw
    exact (hd.mdifferentiableAt (d.open_source.mem_nhds hzd)).congr_of_eventuallyEq hevent
  have hPopen : ∀ W : Set ℂ, IsOpen W → W ⊆ Ω → IsOpen (P '' W) := by
    intro W hWo hWΩ
    apply isOpen_iff_mem_nhds.mpr
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨d, hzd, hdΩ, hPd, hd, hdi⟩ := hPloc z (hWΩ hz)
    have hop : IsOpen (d '' (W ∩ d.source)) :=
      d.isOpen_image_of_subset_source (hWo.inter d.open_source) inter_subset_right
    have hmem : P z ∈ d '' (W ∩ d.source) :=
      ⟨z, ⟨hz, hzd⟩, (hPd hzd).symm⟩
    apply Filter.mem_of_superset (hop.mem_nhds hmem)
    rintro y ⟨w, hw, rfl⟩
    exact ⟨w, hw.1, hPd hw.2⟩
  have hconjopen : ∀ U : Set ℂ, IsOpen U → IsOpen (conj '' U) := by
    intro U hU
    rw [congrFun (Set.image_eq_preimage_of_inverse (f := ⇑(starRingEnd ℂ)) (g := ⇑(starRingEnd ℂ))
      Complex.conj_conj Complex.conj_conj) U]
    exact hU.preimage Complex.continuous_conj
  -- fibres of `P` over the upper half-plane and its mirror
  have hrelU : ∀ x y : UpperHalfPlane, P (x : ℂ) = P (y : ℂ) → ∃ γ ∈ Γ, y = γ • x := by
    intro x y h
    obtain ⟨γ, hγ, he⟩ := (hPfib _ (hUΩ x) _ (hUΩ y)).1 h
    exact ⟨γ, hγ, UpperHalfPlane.ext (he.trans (h36p_m_coe γ x))⟩
  have hrelL : ∀ x y : UpperHalfPlane, P (conj (x : ℂ)) = P (conj (y : ℂ)) → ∃ γ ∈ Γ, y = γ • x := by
    intro x y h
    obtain ⟨γ, hγ, he⟩ := (hPfib _ (hLΩ x) _ (hLΩ y)).1 h
    refine ⟨γ, hγ, UpperHalfPlane.ext ?_⟩
    have e := congrArg conj he
    rw [Complex.conj_conj, ← hmconj, Complex.conj_conj, h36p_m_coe] at e
    exact e
  have hrelUL : ∀ x y : UpperHalfPlane, P (x : ℂ) ≠ P (conj (y : ℂ)) := by
    intro x y h
    obtain ⟨γ, hγ, he⟩ := (hPfib _ (hUΩ x) _ (hLΩ y)).1 h
    rw [h36p_m_coe] at he
    have h1 := congrArg Complex.im he
    rw [Complex.conj_im] at h1
    have h2 := (γ • x).im_pos
    have h3 := y.im_pos
    change -y.im = (γ • x).im at h1
    linarith
  -- precise invariance of the horoballs
  have hcusprel : ∀ i j (τ τ' : UpperHalfPlane), 1 < τ.im → 1 < τ'.im → ∀ γ ∈ Γ,
      A j • τ' = γ • (A i • τ) → i = j ∧ ∃ m : ℤ, (τ' : ℂ) = τ + m := by
    intro i j τ τ' h1 h1' γ hγ he
    have hτ' : (A j)⁻¹ • (γ • (A i • τ)) = τ' := by rw [← he, inv_smul_smul]
    obtain ⟨hij, k, hk⟩ := hpc i j γ hγ τ h1 (by rw [hτ']; exact h1')
    subst hij
    refine ⟨rfl, k, ?_⟩
    have hk' : γ • (A i • τ) = A i • ((k : ℝ) +ᵥ τ) := by
      rcases hk with rfl | rfl
      · exact ft1e_zpow_smul (hcusp i).2 k τ
      · rw [s30l_neg_smul]
        exact ft1e_zpow_smul (hcusp i).2 k τ
    have hτk : τ' = (k : ℝ) +ᵥ τ := by
      rw [← hτ', hk', inv_smul_smul]
    rw [hτk, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  -- periodicity of both families
  have hperU : ∀ i (n : ℤ) (x : UpperHalfPlane),
      P ((A i • ((n : ℝ) +ᵥ x) : UpperHalfPlane) : ℂ) = P ((A i • x : UpperHalfPlane) : ℂ) := by
    intro i n x
    rw [← ft1e_zpow_smul (hcusp i).2 n x]
    refine ((hPfib _ (hUΩ (A i • x)) _ (hUΩ (π₀ i ^ n • (A i • x)))).2
      ⟨π₀ i ^ n, zpow_mem (hcusp i).1 n, ?_⟩).symm
    exact (h36p_m_coe _ _).symm
  have hperL : ∀ i (n : ℤ) (x : UpperHalfPlane),
      P (conj ((A i • ((n : ℝ) +ᵥ x) : UpperHalfPlane) : ℂ)) =
        P (conj ((A i • x : UpperHalfPlane) : ℂ)) := by
    intro i n x
    rw [← ft1e_zpow_smul (hcusp i).2 n x]
    refine ((hPfib _ (hLΩ (A i • x)) _ (hLΩ (π₀ i ^ n • (A i • x)))).2
      ⟨π₀ i ^ n, zpow_mem (hcusp i).1 n, ?_⟩).symm
    rw [hmconj, h36p_m_coe]
  -- the cusp coordinate `τ_w = log w / 2πi + i`
  have hτpos : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → 1 < (Complex.log w / (2 * π * I) + I).im := by
    intro w hw0 hw1
    rw [(ft2c_tau hw0).2]
    have : Real.log ‖w‖ < 0 := Real.log_neg (norm_pos_iff.2 hw0) hw1
    have hπ : 0 < π := Real.pi_pos
    have : Real.log ‖w‖ / (2 * π) < 0 := div_neg_of_neg_of_pos this (by positivity)
    linarith
  let tw : ℂ → UpperHalfPlane := fun w => UpperHalfPlane.ofComplex (Complex.log w / (2 * π * I) + I)
  have htw : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → ((tw w : UpperHalfPlane) : ℂ) = Complex.log w / (2 * π * I) + I := by
    intro w hw0 hw1
    show ((UpperHalfPlane.ofComplex _ : UpperHalfPlane) : ℂ) = _
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by linarith [hτpos w hw0 hw1])]
  have htwim : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → 1 < (tw w).im := fun w hw0 hw1 => by
    have : (tw w).im = ((tw w : UpperHalfPlane) : ℂ).im := rfl
    rw [this, htw w hw0 hw1]
    exact hτpos w hw0 hw1
  have htwexp : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → exp (2 * π * I * (((tw w : UpperHalfPlane) : ℂ) - I)) = w :=
    fun w hw0 hw1 => by rw [htw w hw0 hw1]; exact (ft2c_tau hw0).1
  have hnormexp : ∀ σ : UpperHalfPlane, ‖exp (2 * π * I * ((σ : ℂ) - I))‖ = Real.exp (-(2 * π) * (σ.im - 1)) := by
    intro σ
    rw [Complex.norm_exp]
    congr 1
    have : σ.im = (σ : ℂ).im := rfl
    rw [this]
    simp
  have hconjD : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → conj w ≠ 0 ∧ ‖conj w‖ < 1 := fun w hw0 hw1 =>
    ⟨(map_ne_zero _).2 hw0, by rwa [Complex.norm_conj]⟩
  -- local logarithm branches
  have hbranch : ∀ v₀ : ℂ, v₀ ≠ 0 → ‖v₀‖ < 1 → ∃ L : ℂ → ℂ, DifferentiableAt ℂ L v₀ ∧
      ∀ᶠ v in 𝓝 v₀, v ≠ 0 ∧ ‖v‖ < 1 ∧ exp (L v) = v ∧ (L v).re = Real.log ‖v‖ := by
    intro v₀ hv0 hv1
    obtain ⟨L, hLd, hL⟩ : ∃ L : ℂ → ℂ, DifferentiableAt ℂ L v₀ ∧
        ∀ᶠ v in 𝓝 v₀, exp (L v) = v ∧ (L v).re = Real.log ‖v‖ := by
      by_cases hs : v₀ ∈ slitPlane
      · refine ⟨Complex.log, Complex.differentiableAt_log hs, ?_⟩
        filter_upwards [isOpen_ne.mem_nhds hv0] with v hv
        exact ⟨Complex.exp_log hv, Complex.log_re v⟩
      · have hs' : -v₀ ∈ slitPlane := by
          rw [Complex.mem_slitPlane_iff] at hs ⊢
          push Not at hs
          obtain ⟨hre, him⟩ := hs
          left
          have hne : v₀.re ≠ 0 := fun h => hv0 (Complex.ext h him)
          simp only [neg_re]
          exact neg_pos.2 (lt_of_le_of_ne hre hne)
        refine ⟨fun v => Complex.log (-v) + π * I,
          ((Complex.differentiableAt_log hs').comp v₀ differentiableAt_id.neg).add_const _, ?_⟩
        filter_upwards [isOpen_ne.mem_nhds hv0] with v hv
        refine ⟨?_, ?_⟩
        · rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.2 hv), Complex.exp_pi_mul_I]
          ring
        · simp [Complex.log_re]
    refine ⟨L, hLd, ?_⟩
    filter_upwards [isOpen_ne.mem_nhds hv0, (isOpen_lt continuous_norm continuous_const).mem_nhds hv1, hL]
      with v h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hLim : ∀ (l w : ℂ), w ≠ 0 → ‖w‖ < 1 → l.re = Real.log ‖w‖ → 1 < (l / (2 * π * I) + I).im := by
    intro l w hw0 hw1 hre
    have h1 := hτpos w hw0 hw1
    have e1 := (ft2c_tau hw0).2
    have : (l / (2 * π * I) + I).im = 1 - Real.log ‖w‖ / (2 * π) := by
      have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
      simp only [add_im, I_im, Complex.div_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re,
        Complex.normSq_apply, hre]
      norm_num <;> field_simp <;> ring
    linarith
  -- the charts
  let χ : (Fin c ⊕ Fin c) → ℂ → S := Sum.elim
    (fun i w => P ((A i • tw w : UpperHalfPlane) : ℂ))
    (fun i w => P (conj ((A i • tw (conj w) : UpperHalfPlane) : ℂ)))
  have hχU : ∀ i w, χ (Sum.inl i) w = P ((A i • tw w : UpperHalfPlane) : ℂ) := fun i w => rfl
  have hχL : ∀ i w, χ (Sum.inr i) w = P (conj ((A i • tw (conj w) : UpperHalfPlane) : ℂ)) :=
    fun i w => rfl
  have hσU : ∀ i (w : ℂ) (σ : UpperHalfPlane), w ≠ 0 → ‖w‖ < 1 →
      exp (2 * π * I * ((σ : ℂ) - I)) = w → χ (Sum.inl i) w = P ((A i • σ : UpperHalfPlane) : ℂ) := by
    intro i w σ hw0 hw1 hσ
    rw [hχU]
    exact (ft2c_shift (p := fun x : UpperHalfPlane => P (x : ℂ)) (hperU i)
      (by rw [hσ, htwexp w hw0 hw1])).symm
  have hσL : ∀ i (w : ℂ) (σ : UpperHalfPlane), w ≠ 0 → ‖w‖ < 1 →
      exp (2 * π * I * ((σ : ℂ) - I)) = conj w →
      χ (Sum.inr i) w = P (conj ((A i • σ : UpperHalfPlane) : ℂ)) := by
    intro i w σ hw0 hw1 hσ
    obtain ⟨hc0, hc1⟩ := hconjD w hw0 hw1
    rw [hχL]
    exact (ft2c_shift (p := fun x : UpperHalfPlane => P (conj (x : ℂ))) (hperL i)
      (by rw [hσ, htwexp (conj w) hc0 hc1])).symm
  -- the explicit holomorphic lift through a branch
  have hlift : ∀ (i : Fin c) (L : ℂ → ℂ) (v : ℂ), v ≠ 0 → ‖v‖ < 1 → exp (L v) = v →
      (L v).re = Real.log ‖v‖ →
      ∃ σ : UpperHalfPlane, exp (2 * π * I * ((σ : ℂ) - I)) = v ∧
        ((A i • σ : UpperHalfPlane) : ℂ) = h36p_m (A i) (L v / (2 * π * I) + I) := by
    intro i L v hv0 hv1 hexp hre
    have hpos : 0 < (L v / (2 * π * I) + I).im := by linarith [hLim (L v) v hv0 hv1 hre]
    have hσ : ((UpperHalfPlane.ofComplex (L v / (2 * π * I) + I) : UpperHalfPlane) : ℂ) =
        L v / (2 * π * I) + I := by rw [UpperHalfPlane.ofComplex_apply_of_im_pos hpos]
    refine ⟨UpperHalfPlane.ofComplex (L v / (2 * π * I) + I), ?_, ?_⟩
    · rw [hσ, add_sub_cancel_right, mul_div_cancel₀ _ h2π, hexp]
    · rw [← h36p_m_coe, hσ]
  have hFd : ∀ (i : Fin c) (L : ℂ → ℂ) (v : ℂ), DifferentiableAt ℂ L v → v ≠ 0 → ‖v‖ < 1 →
      (L v).re = Real.log ‖v‖ →
      DifferentiableAt ℂ (fun u => h36p_m (A i) (L u / (2 * π * I) + I)) v ∧
        0 < (h36p_m (A i) (L v / (2 * π * I) + I)).im := by
    intro i L v hLd hv0 hv1 hre
    have hpos : 0 < (L v / (2 * π * I) + I).im := by linarith [hLim (L v) v hv0 hv1 hre]
    have hinner : DifferentiableAt ℂ (fun u => L u / (2 * π * I) + I) v := (hLd.div_const _).add_const _
    have hm := (s36x_m_hasDerivAt (A i) (s36d1c_den_ne (A i) hpos.ne')).differentiableAt
    have hcomp : DifferentiableAt ℂ (h36p_m (A i) ∘ fun u => L u / (2 * π * I) + I) v :=
      DifferentiableAt.comp v hm hinner
    exact ⟨hcomp, s36d1c_m_im_pos (A i) hpos⟩
  -- a lower bound for the coordinate from a height bound
  have hwlb : ∀ (Mt : ℝ) (w : ℂ), w ≠ 0 → ‖w‖ < 1 → (tw w).im ≤ Mt → Real.exp (-(2 * π) * Mt) ≤ ‖w‖ := by
    intro Mt w hw0 hw1 h2
    have h3 : (tw w).im = 1 - Real.log ‖w‖ / (2 * π) := by
      have : (tw w).im = ((tw w : UpperHalfPlane) : ℂ).im := rfl
      rw [this, htw w hw0 hw1, (ft2c_tau hw0).2]
    have hπ : 0 < π := Real.pi_pos
    have hlog : -(2 * π) * Mt ≤ Real.log ‖w‖ := by
      have : Real.log ‖w‖ / (2 * π) ≥ 1 - Mt := by linarith
      rw [ge_iff_le, le_div_iff₀ (by positivity)] at this
      nlinarith
    calc Real.exp (-(2 * π) * Mt) ≤ Real.exp (Real.log ‖w‖) := Real.exp_le_exp.2 hlog
      _ = ‖w‖ := Real.exp_log (norm_pos_iff.2 hw0)
  -- height bound near an interior point, from the cusp normal form of an auxiliary uniformization
  have hbound : ∀ z₁ : ℂ, 0 < z₁.im → ∃ ε > (0 : ℝ), ∃ Mt : ℝ, ∀ y ∈ ball z₁ ε, 0 < y.im ∧
      ∀ i (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ), γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im →
        ((γ • (A i • τ) : UpperHalfPlane) : ℂ) = y → τ.im ≤ Mt := by
    intro z₁ hz₁
    obtain ⟨S', iT, iC, iT2, iConn, iM, p, hp⟩ := ft0_quotient hΓ hfree
    have hnorm : ∀ i, ∀ (κ τ : UpperHalfPlane), 1 < τ.im → p (A i • τ) = p κ →
        τ.im ≤ max ((A i)⁻¹ • κ).im (1 / ((A i)⁻¹ • κ).im) := fun i =>
      (ft2c_cusp_normal hp hΓ (hcusp i).1 (hcusp i).2
        fun γ hγ τ h1 h2 => (hpc i i γ hγ τ h1 h2).2).2.2
    have hKim : ∀ y ∈ closedBall z₁ (z₁.im / 2), z₁.im / 2 ≤ y.im := by
      intro y hy
      have h1 : |y.im - z₁.im| ≤ ‖y - z₁‖ := by
        rw [← Complex.sub_im]
        exact Complex.abs_im_le_norm _
      rw [mem_closedBall, dist_eq_norm] at hy
      have := abs_le.1 (h1.trans hy)
      linarith [this.1]
    have hbd : ∀ i, ∃ M : ℝ, ∀ y ∈ closedBall z₁ (z₁.im / 2),
        (h36p_m (A i)⁻¹ y).im + 1 / (h36p_m (A i)⁻¹ y).im ≤ M := by
      intro i
      have hm : ContinuousOn (fun y => (h36p_m (A i)⁻¹ y).im) (closedBall z₁ (z₁.im / 2)) := by
        intro y hy
        have hy0 : y.im ≠ 0 := (by linarith [hKim y hy] : 0 < y.im).ne'
        exact (Complex.continuous_im.continuousAt.comp
          (s36x_m_hasDerivAt _ (s36d1c_den_ne _ hy0)).continuousAt).continuousWithinAt
      have hcont : ContinuousOn (fun y => (h36p_m (A i)⁻¹ y).im + 1 / (h36p_m (A i)⁻¹ y).im)
          (closedBall z₁ (z₁.im / 2)) :=
        ContinuousOn.add hm (continuousOn_const.div hm fun y hy =>
          (s36d1c_m_im_pos _ (by linarith [hKim y hy])).ne')
      obtain ⟨M, hM⟩ := ((isCompact_closedBall z₁ (z₁.im / 2)).image_of_continuousOn hcont).isBounded.bddAbove
      exact ⟨M, fun y hy => hM ⟨y, hy, rfl⟩⟩
    choose M hM using hbd
    set Mt : ℝ := 1 + ∑ i, |M i| with hMt
    have hMt : ∀ i, M i ≤ Mt := fun i => by
      rw [hMt]
      have := Finset.single_le_sum (f := fun j => |M j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      linarith [le_abs_self (M i)]
    refine ⟨z₁.im / 2, half_pos hz₁, Mt, fun y hy => ?_⟩
    have hyK : y ∈ closedBall z₁ (z₁.im / 2) := ball_subset_closedBall hy
    have hypos : 0 < y.im := by linarith [hKim y hyK]
    refine ⟨hypos, fun i γ hγ τ h1 he => ?_⟩
    let y' : UpperHalfPlane := ⟨y, hypos⟩
    have hpe : p (A i • τ) = p y' := (hp.2.2.2 (A i • τ) y').2 ⟨γ, hγ, UpperHalfPlane.ext he⟩
    have e : ((A i)⁻¹ • y').im = (h36p_m (A i)⁻¹ y).im :=
      congrArg Complex.im (h36p_m_coe _ y').symm
    have h2 := hnorm i y' τ h1 hpe
    rw [e] at h2
    have ha := s36d1c_m_im_pos (A i)⁻¹ hypos
    have h3 := max_le_add_of_nonneg ha.le (one_div_pos.2 ha).le
    exact ((h2.trans h3).trans (hM i y hyK)).trans (hMt i)
  refine ⟨χ, Real.exp (-(2 * π)), Real.exp_pos _, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [Real.exp_lt_one_iff]
    have := Real.pi_pos
    linarith
  · rintro (i | i)
    · refine ⟨?_, ?_, ?_⟩
      · -- injectivity
        rintro w₁ ⟨hw₁0, hw₁1⟩ w₂ ⟨hw₂0, hw₂1⟩ he
        rw [hχU, hχU] at he
        obtain ⟨γ, hγ, hγe⟩ := hrelU _ _ he
        obtain ⟨-, m, hm⟩ := hcusprel i i (tw w₁) (tw w₂) (htwim w₁ hw₁0 hw₁1) (htwim w₂ hw₂0 hw₂1)
          γ hγ hγe
        rw [← htwexp w₁ hw₁0 hw₁1, ← htwexp w₂ hw₂0 hw₂1, hm,
          show 2 * π * I * (((tw w₁ : UpperHalfPlane) : ℂ) + m - I) =
            2 * π * I * (((tw w₁ : UpperHalfPlane) : ℂ) - I) + m * (2 * π * I) by ring,
          Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      · -- holomorphy through a local branch
        rintro w₀ ⟨hw0, hw1⟩
        refine MDifferentiableAt.mdifferentiableWithinAt ?_
        obtain ⟨L, hLd, hL⟩ := hbranch w₀ hw0 hw1
        have heq : (fun w => P (h36p_m (A i) (L w / (2 * π * I) + I))) =ᶠ[𝓝 w₀] χ (Sum.inl i) := by
          filter_upwards [hL] with w hw
          obtain ⟨hw0', hw1', hexp, hre⟩ := hw
          obtain ⟨σ, hσ, hσc⟩ := hlift i L w hw0' hw1' hexp hre
          rw [hσU i w σ hw0' hw1' hσ, hσc]
        refine MDifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
        obtain ⟨h1, h2, -, h4⟩ := hL.self_of_nhds
        obtain ⟨hd, hpos⟩ := hFd i L w₀ hLd h1 h2 h4
        exact (hPat _ (hΩim _ hpos.ne')).comp w₀ hd.mdifferentiableAt
      · -- open images
        intro V hV hVsub
        have himg : χ (Sum.inl i) '' V = P '' ((fun σ : UpperHalfPlane => ((A i • σ : UpperHalfPlane) : ℂ)) ''
            {σ : UpperHalfPlane | exp (2 * π * I * ((σ : ℂ) - I)) ∈ V}) := by
          ext x
          constructor
          · rintro ⟨w, hw, rfl⟩
            obtain ⟨hw0, hw1⟩ := hVsub hw
            exact ⟨_, ⟨tw w, by rw [mem_setOf_eq, htwexp w hw0 hw1]; exact hw, rfl⟩, (hχU i w).symm⟩
          · rintro ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
            obtain ⟨hw0, hw1⟩ := hVsub hσ
            exact ⟨_, hσ, hσU i _ σ hw0 hw1 rfl⟩
        rw [himg]
        refine hPopen _ ?_ ?_
        · exact (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.comp (Homeomorph.smul (A i)).isOpenMap) _
            (hV.preimage (by fun_prop))
        · rintro _ ⟨σ, -, rfl⟩
          exact hUΩ _
    · refine ⟨?_, ?_, ?_⟩
      · -- injectivity of the mirror chart
        rintro w₁ ⟨hw₁0, hw₁1⟩ w₂ ⟨hw₂0, hw₂1⟩ he
        obtain ⟨hc₁0, hc₁1⟩ := hconjD w₁ hw₁0 hw₁1
        obtain ⟨hc₂0, hc₂1⟩ := hconjD w₂ hw₂0 hw₂1
        rw [hχL, hχL] at he
        obtain ⟨γ, hγ, hγe⟩ := hrelL _ _ he
        obtain ⟨-, m, hm⟩ := hcusprel i i (tw (conj w₁)) (tw (conj w₂)) (htwim _ hc₁0 hc₁1)
          (htwim _ hc₂0 hc₂1) γ hγ hγe
        have hcc : conj w₁ = conj w₂ := by
          rw [← htwexp _ hc₁0 hc₁1, ← htwexp _ hc₂0 hc₂1, hm,
            show 2 * π * I * (((tw (conj w₁) : UpperHalfPlane) : ℂ) + m - I) =
              2 * π * I * (((tw (conj w₁) : UpperHalfPlane) : ℂ) - I) + m * (2 * π * I) by ring,
            Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
        have e := congrArg conj hcc
        simpa only [Complex.conj_conj] using e
      · -- holomorphy: conjugate both the lift and the disk coordinate
        rintro w₀ ⟨hw0, hw1⟩
        refine MDifferentiableAt.mdifferentiableWithinAt ?_
        obtain ⟨hc0, hc1⟩ := hconjD w₀ hw0 hw1
        obtain ⟨L, hLd, hL⟩ := hbranch (conj w₀) hc0 hc1
        have hL' := (Complex.continuous_conj.tendsto w₀).eventually hL
        have heq : (fun w => P (conj (h36p_m (A i) (L (conj w) / (2 * π * I) + I)))) =ᶠ[𝓝 w₀]
            χ (Sum.inr i) := by
          filter_upwards [hL'] with w hw
          obtain ⟨hw0', hw1', hexp, hre⟩ := hw
          have hw0'' : w ≠ 0 := fun h => hw0' (by rw [h, map_zero])
          have hw1'' : ‖w‖ < 1 := by rwa [Complex.norm_conj] at hw1'
          obtain ⟨σ, hσ, hσc⟩ := hlift i L (conj w) hw0' hw1' hexp hre
          rw [hσL i w σ hw0'' hw1'' hσ, hσc]
        refine MDifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
        obtain ⟨h1, h2, -, h4⟩ := hL.self_of_nhds
        obtain ⟨hd, hpos⟩ := hFd i L (conj w₀) hLd h1 h2 h4
        have hd' : DifferentiableAt ℂ
            (fun w => conj (h36p_m (A i) (L (conj w) / (2 * π * I) + I))) w₀ :=
          differentiableAt_conj_conj_iff.2 hd
        have hmem : conj (h36p_m (A i) (L (conj w₀) / (2 * π * I) + I)) ∈ Ω := by
          refine hΩim _ ?_
          rw [Complex.conj_im]
          exact neg_ne_zero.2 hpos.ne'
        exact (hPat _ hmem).comp w₀ hd'.mdifferentiableAt
      · -- open images of the mirror chart
        intro V hV hVsub
        have himg : χ (Sum.inr i) '' V = P '' (conj '' ((fun σ : UpperHalfPlane =>
            ((A i • σ : UpperHalfPlane) : ℂ)) ''
              {σ : UpperHalfPlane | conj (exp (2 * π * I * ((σ : ℂ) - I))) ∈ V})) := by
          ext x
          constructor
          · rintro ⟨w, hw, rfl⟩
            obtain ⟨hw0, hw1⟩ := hVsub hw
            obtain ⟨hc0, hc1⟩ := hconjD w hw0 hw1
            refine ⟨_, ⟨_, ⟨tw (conj w), ?_, rfl⟩, rfl⟩, (hχL i w).symm⟩
            rw [mem_setOf_eq, htwexp _ hc0 hc1, Complex.conj_conj]
            exact hw
          · rintro ⟨_, ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩, rfl⟩
            obtain ⟨hw0, hw1⟩ := hVsub hσ
            exact ⟨_, hσ, hσL i _ σ hw0 hw1 (Complex.conj_conj _).symm⟩
        rw [himg]
        refine hPopen _ (hconjopen _ ?_) ?_
        · exact (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.comp (Homeomorph.smul (A i)).isOpenMap) _
            (hV.preimage (Complex.continuous_conj.comp (by fun_prop)))
        · rintro _ ⟨_, ⟨σ, -, rfl⟩, rfl⟩
          exact hLΩ _
  · -- disjointness
    rintro (i | i) (j | j) hij <;> rw [Set.disjoint_left] <;>
      rintro _ ⟨w, ⟨hw0, hw1⟩, rfl⟩ ⟨w', ⟨hw0', hw1'⟩, he⟩
    · rw [hχU, hχU] at he
      obtain ⟨γ, hγ, hγe⟩ := hrelU _ _ he
      exact hij (congrArg Sum.inl (hcusprel j i (tw w') (tw w) (htwim w' hw0' hw1') (htwim w hw0 hw1)
        γ hγ hγe).1.symm)
    · rw [hχU, hχL] at he
      exact hrelUL _ _ he.symm
    · rw [hχL, hχU] at he
      exact hrelUL _ _ he
    · obtain ⟨hc0, hc1⟩ := hconjD w hw0 hw1
      obtain ⟨hc0', hc1'⟩ := hconjD w' hw0' hw1'
      rw [hχL, hχL] at he
      obtain ⟨γ, hγ, hγe⟩ := hrelL _ _ he
      exact hij (congrArg Sum.inr (hcusprel j i (tw (conj w')) (tw (conj w)) (htwim _ hc0' hc1')
        (htwim _ hc0 hc1) γ hγ hγe).1.symm)
  · -- the ends leave every point
    intro x
    have hx : x ∈ P '' Ω := by rw [hPsurj]; exact mem_univ x
    obtain ⟨z₀, hz₀, rfl⟩ := hx
    obtain ⟨d, hzd, hdΩ, hPd, -, -⟩ := hPloc z₀ hz₀
    obtain ⟨ε₂, hε₂, hε₂d⟩ := Metric.mem_nhds_iff.mp (d.open_source.mem_nhds hzd)
    have hNmem : ∀ ε > (0 : ℝ), ε ≤ ε₂ → P '' ball z₀ ε ∈ 𝓝 (P z₀) := fun ε hε hεε =>
      (hPopen _ isOpen_ball fun y hy => hdΩ (hε₂d (ball_subset_ball hεε hy))).mem_nhds
        ⟨z₀, mem_ball_self hε, rfl⟩
    have hyΩ : ∀ ε, ε ≤ ε₂ → ∀ y ∈ ball z₀ ε, y ∈ Ω := fun ε hεε y hy =>
      hdΩ (hε₂d (ball_subset_ball hεε hy))
    -- a chart value equal to `P y` is a translate of the corresponding horoball point
    have hvalU : ∀ i (w y : ℂ), w ≠ 0 → ‖w‖ < 1 → y ∈ Ω → χ (Sum.inl i) w = P y →
        ∃ γ ∈ Γ, y = ((γ • (A i • tw w) : UpperHalfPlane) : ℂ) := by
      intro i w y hw0 hw1 hy he
      rw [hχU] at he
      obtain ⟨γ, hγ, hγe⟩ := (hPfib _ (hUΩ _) y hy).1 he
      exact ⟨γ, hγ, hγe.trans (h36p_m_coe _ _)⟩
    have hvalL : ∀ i (w y : ℂ), w ≠ 0 → ‖w‖ < 1 → y ∈ Ω → χ (Sum.inr i) w = P y →
        ∃ γ ∈ Γ, conj y = ((γ • (A i • tw (conj w)) : UpperHalfPlane) : ℂ) := by
      intro i w y hw0 hw1 hy he
      rw [hχL] at he
      obtain ⟨γ, hγ, hγe⟩ := (hPfib _ (hLΩ _) y hy).1 he
      refine ⟨γ, hγ, ?_⟩
      rw [hγe, hmconj, Complex.conj_conj, h36p_m_coe]
    rcases lt_trichotomy z₀.im 0 with hneg | hzero | hpos
    · -- lower half-plane: only the mirror family comes near, through the conjugate bound
      obtain ⟨ε₁, hε₁, Mt, hMt⟩ := hbound (conj z₀) (by rw [Complex.conj_im]; linarith)
      have hcb : ∀ y ∈ ball z₀ (min ε₁ ε₂), conj y ∈ ball (conj z₀) ε₁ := by
        intro y hy
        rw [mem_ball, dist_eq_norm, ← map_sub (starRingEnd ℂ), Complex.norm_conj, ← dist_eq_norm]
        exact lt_of_lt_of_le hy (min_le_left _ _)
      refine ⟨P '' ball z₀ (min ε₁ ε₂), hNmem _ (lt_min hε₁ hε₂) (min_le_right _ _),
        Real.exp (-(2 * π) * Mt), Real.exp_pos _, ?_⟩
      rintro (i | i) w hw0 hw1 ⟨y, hy, hPy⟩
      · exfalso
        obtain ⟨γ, hγ, hγe⟩ := hvalU i w y hw0 hw1 (hyΩ _ (min_le_right _ _) y hy) hPy.symm
        have h1 := (hMt _ (hcb y hy)).1
        rw [Complex.conj_im, hγe] at h1
        have h2 := (γ • (A i • tw w)).im_pos
        change 0 < -((γ • (A i • tw w) : UpperHalfPlane) : ℂ).im at h1
        change 0 < ((γ • (A i • tw w) : UpperHalfPlane) : ℂ).im at h2
        linarith
      · obtain ⟨hc0, hc1⟩ := hconjD w hw0 hw1
        obtain ⟨γ, hγ, hγe⟩ := hvalL i w y hw0 hw1 (hyΩ _ (min_le_right _ _) y hy) hPy.symm
        have hb := (hMt _ (hcb y hy)).2 i γ hγ (tw (conj w)) (htwim _ hc0 hc1) hγe.symm
        have := hwlb Mt (conj w) hc0 hc1 hb
        rwa [Complex.norm_conj] at this
    · -- a real ordinary point: no chart value comes near
      have hz₀R : (z₀ : ExtPlane) ∈ ordinarySet Γ :=
        Set.mem_diff_of_mem (Set.mem_union_left _ (Set.mem_image_of_mem ((↑) : ℂ → ExtPlane)
          (show z₀ ∈ realLine from hzero))) ((hΩ z₀).1 hz₀).1
      obtain ⟨V, hVo, hLV, hVd⟩ := ft1fas_cusp_family_avoids_ordinary_compact hΓ A π₀ hcusp hpc
        {(z₀ : ExtPlane)} isCompact_singleton (Set.singleton_subset_iff.2 hz₀R)
      have hz₀V : (z₀ : ExtPlane) ∈ V := hLV (Set.mem_singleton _)
      have hW : ((↑) : ℂ → ExtPlane) ⁻¹' V ∈ 𝓝 z₀ :=
        OnePoint.continuous_coe.continuousAt (hVo.mem_nhds hz₀V)
      obtain ⟨ε₃, hε₃, hε₃V⟩ := Metric.mem_nhds_iff.mp hW
      have hc₀ : conj z₀ = z₀ := Complex.conj_eq_iff_im.2 hzero
      refine ⟨P '' ball z₀ (min ε₃ ε₂), hNmem _ (lt_min hε₃ hε₂) (min_le_right _ _),
        1, one_pos, ?_⟩
      rintro (i | i) w hw0 hw1 ⟨y, hy, hPy⟩ <;> exfalso
      · obtain ⟨γ, hγ, hγe⟩ := hvalU i w y hw0 hw1 (hyΩ _ (min_le_right _ _) y hy) hPy.symm
        have hyV : (y : ExtPlane) ∈ V := hε₃V (ball_subset_ball (min_le_left _ _) hy)
        exact Set.disjoint_left.1 hVd hyV ⟨γ, hγ, i, tw w, htwim w hw0 hw1, by rw [hγe]⟩
      · obtain ⟨hc0, hc1⟩ := hconjD w hw0 hw1
        obtain ⟨γ, hγ, hγe⟩ := hvalL i w y hw0 hw1 (hyΩ _ (min_le_right _ _) y hy) hPy.symm
        have hcy : conj y ∈ ball z₀ ε₃ := by
          rw [mem_ball, dist_eq_norm, ← hc₀, ← map_sub (starRingEnd ℂ), Complex.norm_conj, ← dist_eq_norm]
          exact lt_of_lt_of_le hy (min_le_left _ _)
        have hyV : ((conj y : ℂ) : ExtPlane) ∈ V := hε₃V hcy
        exact Set.disjoint_left.1 hVd hyV ⟨γ, hγ, i, tw (conj w), htwim _ hc0 hc1, by rw [hγe]⟩
    · -- upper half-plane: only the upper family comes near, with a uniform height bound
      obtain ⟨ε₁, hε₁, Mt, hMt⟩ := hbound z₀ hpos
      refine ⟨P '' ball z₀ (min ε₁ ε₂), hNmem _ (lt_min hε₁ hε₂) (min_le_right _ _),
        Real.exp (-(2 * π) * Mt), Real.exp_pos _, ?_⟩
      rintro (i | i) w hw0 hw1 ⟨y, hy, hPy⟩
      · have hy₁ : y ∈ ball z₀ ε₁ := ball_subset_ball (min_le_left _ _) hy
        obtain ⟨γ, hγ, hγe⟩ := hvalU i w y hw0 hw1 (hyΩ _ (min_le_right _ _) y hy) hPy.symm
        exact hwlb Mt w hw0 hw1 ((hMt y hy₁).2 i γ hγ (tw w) (htwim w hw0 hw1) hγe.symm)
      · exfalso
        have hy₁ : y ∈ ball z₀ ε₁ := ball_subset_ball (min_le_left _ _) hy
        obtain ⟨γ, hγ, hγe⟩ := hvalL i w y hw0 hw1 (hyΩ _ (min_le_right _ _) y hy) hPy.symm
        have h1 := (hMt y hy₁).1
        have h2 := (γ • (A i • tw (conj w))).im_pos
        have h3 := congrArg Complex.im hγe
        rw [Complex.conj_im] at h3
        change -y.im = (γ • (A i • tw (conj w))).im at h3
        linarith
  · -- actual cusp ranges
    intro i w hw0 hw1
    exact ⟨tw w, htwim w hw0 hw1, hχU i w⟩
  · intro i w hw0 hw1
    obtain ⟨hc0, hc1⟩ := hconjD w hw0 hw1
    exact ⟨tw (conj w), htwim _ hc0 hc1, hχL i w⟩
  · -- uniform tail coverage
    intro i τ hτ
    have hlt : ‖exp (2 * π * I * ((τ : ℂ) - I))‖ < 1 := by
      rw [hnormexp, Real.exp_lt_one_iff]
      have := Real.pi_pos
      nlinarith
    have hle : ‖exp (2 * π * I * ((τ : ℂ) - I))‖ ≤ Real.exp (-(2 * π)) := by
      rw [hnormexp, Real.exp_le_exp]
      have := Real.pi_pos
      nlinarith
    have hne : exp (2 * π * I * ((τ : ℂ) - I)) ≠ 0 := Complex.exp_ne_zero _
    refine ⟨⟨_, hne, hle, hσU i _ τ hne hlt rfl⟩, ⟨conj (exp (2 * π * I * ((τ : ℂ) - I))),
      (map_ne_zero _).2 hne, by rwa [Complex.norm_conj], ?_⟩⟩
    exact hσL i _ τ ((map_ne_zero _).2 hne) (by rwa [Complex.norm_conj]) (Complex.conj_conj _).symm

end LiZhongQC
