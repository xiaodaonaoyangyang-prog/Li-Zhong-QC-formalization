import LiZhongQC.Lemmas.FoundationSmallSupport
import LiZhongQC.Lemmas.S36BersOrdinary
import LiZhongQC.Lemmas.StrebelDoubleDomain

/-! D1 G2 producer: the compact spherical double core from the complete F1 data.
The core is C, the height-[1,2] cusp period strips and the closed doubled funnel
period sectors, together with the mirror image of all of them. Upper points use
the F1 cover followed by a cusp translation or a funnel scaling; ordinary boundary
points use the funnel-arc cover and the scaling extended to the real line. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- A real Möbius denominator vanishes only at real points. -/
theorem s36d1g_den_ne (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) {q : ℂ} (hq : q.im ≠ 0) :
    (g 1 0 : ℂ) * q + g 1 1 ≠ 0 := by
  intro h0
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rwa [Matrix.det_fin_two] at h
  have h1 : g 1 0 * q.im = 0 := by
    have h := congrArg Complex.im h0
    simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, zero_im] at h
    exact h
  have h2 : g 1 0 * q.re + g 1 1 = 0 := by
    have h := congrArg Complex.re h0
    simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, zero_re] at h
    exact h
  have hc : g 1 0 = 0 := (mul_eq_zero.1 h1).resolve_right hq
  rw [hc, zero_mul, zero_add] at h2
  rw [hc, h2, mul_zero, mul_zero, sub_zero] at hdet
  exact zero_ne_one hdet

/-- Non-real finite points are not limit points of a Fuchsian group. -/
theorem s36d1g_coe_not_limit (hΓ : IsFuchsian Γ) {v : ℂ} (hv : v.im ≠ 0) :
    (v : ExtPlane) ∉ fuchsianLimitSet Γ := by
  intro h
  rcases s36a_limit_real hΓ h with ⟨w, hw, hwv⟩ | hinf
  · have hvR : v ∈ realLine := (OnePoint.coe_injective hwv) ▸ hw
    exact hv hvR
  · exact OnePoint.coe_ne_infty v (Set.mem_singleton_iff.1 hinf)

/-- A real Möbius map sends a non-real finite point to a non-real finite point. -/
theorem s36d1g_msl_nonreal (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    ∃ v : ℂ, v.im ≠ 0 ∧ mobiusSL (slRealToComplex g) (w : ExtPlane) = (v : ExtPlane) := by
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · have hc : 0 < (conj w).im := by
      rw [Complex.conj_im]
      linarith
    refine ⟨conj ((g • UpperHalfPlane.mk (conj w) hc : UpperHalfPlane) : ℂ), ?_, ?_⟩
    · rw [Complex.conj_im]
      exact neg_ne_zero.2 (g • UpperHalfPlane.mk (conj w) hc).im_pos.ne'
    · have e1 : mobiusSL (slRealToComplex g) (w : ExtPlane) = ((h36p_m g w : ℂ) : ExtPlane) :=
        s36x_msl_coe g (s36d1g_den_ne g hw)
      have e2 : h36p_m g (conj (conj w)) = conj (h36p_m g (conj w)) := b33_e_mobius_conj g (conj w)
      have e3 : h36p_m g (conj w) = ((g • UpperHalfPlane.mk (conj w) hc : UpperHalfPlane) : ℂ) :=
        h36p_m_coe g (UpperHalfPlane.mk (conj w) hc)
      rw [e1, ← e3, ← e2, Complex.conj_conj]
  · refine ⟨((g • UpperHalfPlane.mk w hpos : UpperHalfPlane) : ℂ),
      (g • UpperHalfPlane.mk w hpos).im_pos.ne', ?_⟩
    exact h36t_mobiusSL_coe g (UpperHalfPlane.mk w hpos)

/-- An element acting on H as multiplication by a positive real is diagonal. -/
theorem s36d1g_scale_entries {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {μ : ℝ} (hμ : 0 < μ)
    (h : ∀ σ : UpperHalfPlane, ((δ • σ : UpperHalfPlane) : ℂ) = (μ : ℂ) * (σ : ℂ)) :
    δ 1 0 = 0 ∧ δ 0 1 = 0 ∧ δ 0 0 = μ * δ 1 1 := by
  have key : ∀ σ : UpperHalfPlane, (δ 0 0 : ℂ) * σ + δ 0 1 =
      (μ : ℂ) * σ * ((δ 1 0 : ℂ) * σ + δ 1 1) := by
    intro σ
    have hd := s36d1g_den_ne δ σ.im_pos.ne'
    have e : ((δ 0 0 : ℂ) * σ + δ 0 1) / ((δ 1 0 : ℂ) * σ + δ 1 1) = (μ : ℂ) * σ := by
      have e0 := h σ
      rw [← h36p_m_coe] at e0
      exact e0
    rwa [div_eq_iff hd] at e
  have h2I : 0 < (2 * Complex.I).im := by simp
  have k1 := key UpperHalfPlane.I
  have k2 := key (UpperHalfPlane.mk (2 * Complex.I) h2I)
  rw [UpperHalfPlane.coe_I] at k1
  rw [UpperHalfPlane.coe_mk] at k2
  have k1' : (((δ 0 1 + μ * δ 1 0 : ℝ)) : ℂ) + ((δ 0 0 - μ * δ 1 1 : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast
    linear_combination k1 + (μ : ℂ) * (δ 1 0 : ℂ) * Complex.I_sq
  have k2' : (((δ 0 1 + 4 * μ * δ 1 0 : ℝ)) : ℂ) +
      ((2 * δ 0 0 - 2 * μ * δ 1 1 : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast
    linear_combination k2 + 4 * (μ : ℂ) * (δ 1 0 : ℂ) * Complex.I_sq
  have r1 : δ 0 1 + μ * δ 1 0 = 0 := by
    have := congrArg Complex.re k1'
    simpa using this
  have i1 : δ 0 0 - μ * δ 1 1 = 0 := by
    have := congrArg Complex.im k1'
    simpa using this
  have r2 : δ 0 1 + 4 * μ * δ 1 0 = 0 := by
    have := congrArg Complex.re k2'
    simpa using this
  have h3 : (3 * μ) * δ 1 0 = 0 := by linarith
  have hc : δ 1 0 = 0 := (mul_eq_zero.1 h3).resolve_left (by positivity)
  refine ⟨hc, ?_, by linarith⟩
  rw [hc, mul_zero, add_zero] at r1
  exact r1

/-- The funnel scaling in the coordinate B extends to every finite real point. -/
theorem s36d1g_scale_ext (B h₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hscale : ∀ τ : UpperHalfPlane, ((B⁻¹ • (h₀ • (B • τ)) : UpperHalfPlane) : ℂ) = (lam : ℂ) * (τ : ℂ))
    (k : ℤ) (t : ℝ) :
    mobiusSL (slRealToComplex (h₀ ^ k)) (mobiusSL (slRealToComplex B) ((t : ℂ) : ExtPlane)) =
      mobiusSL (slRealToComplex B) (((lam ^ k * t : ℝ) : ℂ) : ExtPlane) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, δ = B⁻¹ * h₀ ^ k * B := ⟨_, rfl⟩
  have hδσ : ∀ σ : UpperHalfPlane, ((δ • σ : UpperHalfPlane) : ℂ) = ((lam ^ k : ℝ) : ℂ) * (σ : ℂ) := by
    intro σ
    rw [hδ, mul_smul, mul_smul, ft4a_scale_zpow hscale k σ, Complex.ofReal_zpow]
  obtain ⟨h10, h01, h00⟩ := s36d1g_scale_entries (zpow_pos hlam k) hδσ
  have hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe δ
    rwa [Matrix.det_fin_two] at h
  have h11 : δ 1 1 ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_sub, h10, mul_zero, neg_zero] at hdet
    exact zero_ne_one hdet
  have h11C : (δ 1 1 : ℂ) ≠ 0 := by exact_mod_cast h11
  have hden : (δ 1 0 : ℂ) * (t : ℂ) + δ 1 1 ≠ 0 := by
    rw [h10, Complex.ofReal_zero, zero_mul, zero_add]
    exact h11C
  have hmc : mobiusSL (slRealToComplex δ) ((t : ℂ) : ExtPlane) = ((h36p_m δ t : ℂ) : ExtPlane) :=
    s36x_msl_coe δ hden
  have hmδ : mobiusSL (slRealToComplex δ) ((t : ℂ) : ExtPlane) =
      (((lam ^ k * t : ℝ) : ℂ) : ExtPlane) := by
    rw [hmc]
    congr 1
    show ((δ 0 0 : ℂ) * t + δ 0 1) / ((δ 1 0 : ℂ) * t + δ 1 1) = ((lam ^ k * t : ℝ) : ℂ)
    rw [h10, h01, h00, Complex.ofReal_zero, zero_mul, zero_add, add_zero, div_eq_iff h11C]
    simp only [Complex.ofReal_mul]
    ring
  have hπk : h₀ ^ k = B * δ * B⁻¹ := by
    rw [hδ]
    group
  rw [hπk, k24_slReal_mul, k24_slReal_mul, k24_mobiusSL_mul, k24_mobiusSL_mul, k24_slReal_inv,
    k24_mobiusSL_inv_apply, hmδ]

/-- A real Möbius map commutes with conjugation at a lower half-plane point. -/
theorem s36d1g_msl_lower (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    mobiusSL (slRealToComplex g) ((conj (τ : ℂ) : ℂ) : ExtPlane) =
      ((conj ((g • τ : UpperHalfPlane) : ℂ) : ℂ) : ExtPlane) := by
  have hne : (conj (τ : ℂ)).im ≠ 0 := by
    rw [Complex.conj_im]
    exact neg_ne_zero.2 τ.im_pos.ne'
  have e1 : mobiusSL (slRealToComplex g) ((conj (τ : ℂ) : ℂ) : ExtPlane) =
      ((h36p_m g (conj (τ : ℂ)) : ℂ) : ExtPlane) := s36x_msl_coe g (s36d1g_den_ne g hne)
  have e2 : h36p_m g (conj (τ : ℂ)) = conj (h36p_m g τ) := b33_e_mobius_conj g τ
  rw [e1, e2, h36p_m_coe]

/-- G2. Compact spherical double core from the SAME complete F1 data.
Consume all seven frozen F1 conjuncts plus full funnel-arc ordinariness and
exhaustive spherical ordinary-arc coverage. Add closed doubled funnel period
sectors and height-[1,2] cusp strips to C and its mirror; retain actual compactness
in the ordinary spherical locus, including period arcs crossing infinity. -/
theorem s36d1_double_core (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {c m : ℕ} (C : Set UpperHalfPlane)
    (A π₀ : Fin c → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (B h : Fin m → Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam θ : Fin m → ℝ)
    (hC : IsCompact C)
    (hcusp : ∀ i, π₀ i ∈ Γ ∧ ∀ τ : UpperHalfPlane,
      π₀ i • (A i • τ) = A i • ((1 : ℝ) +ᵥ τ))
    (hfun : ∀ j, h j ∈ Γ ∧ 1 < lam j ∧ 0 < θ j ∧ θ j < π ∧
      ∀ τ : UpperHalfPlane, (((B j)⁻¹ • (h j • (B j • τ)) : UpperHalfPlane) : ℂ) =
        (lam j : ℂ) * (τ : ℂ))
    (hpc : ∀ i i' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im →
      1 < ((A i')⁻¹ • (γ • (A i • τ))).im →
      i = i' ∧ ∃ t : ℤ, γ = π₀ i ^ t ∨ γ = -π₀ i ^ t)
    (hpf : ∀ j j' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, arg (τ : ℂ) < θ j →
      arg (((B j')⁻¹ • (γ • (B j • τ)) : UpperHalfPlane) : ℂ) < θ j' →
      j = j' ∧ ∃ t : ℤ, γ = h j ^ t ∨ γ = -h j ^ t)
    (hcross : ∀ i j γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im →
      θ j ≤ arg (((B j)⁻¹ • (γ • (A i • τ)) : UpperHalfPlane) : ℂ))
    (hcover : ∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, γ • τ ∈ C ∨
      (∃ i, 1 < ((A i)⁻¹ • (γ • τ)).im) ∨
      ∃ j, arg (((B j)⁻¹ • (γ • τ) : UpperHalfPlane) : ℂ) < θ j)
    (harcord : ∀ j (t : ℝ), 0 < t →
      mobiusSL (slRealToComplex (B j)) ((t : ℂ) : ExtPlane) ∈ ordinarySet Γ)
    (harccover : ∀ x : ExtPlane, x ∈ ordinarySet Γ →
      ∃ γ ∈ Γ, ∃ j : Fin m, ∃ t : ℝ, 0 < t ∧
        x = mobiusSL (slRealToComplex (γ * B j)) ((t : ℂ) : ExtPlane)) :
    ∃ L : Set ExtPlane, IsCompact L ∧ L ⊆ (fuchsianLimitSet Γ)ᶜ ∧
      (∀ p : ExtPlane, p ∉ fuchsianLimitSet Γ → ∃ γ ∈ Γ,
      mobiusSL (slRealToComplex γ) p ∈ L ∨
      ∃ i : Fin c, ∃ τ : UpperHalfPlane, 2 < τ.im ∧
        (mobiusSL (slRealToComplex γ) p = (((A i • τ : UpperHalfPlane) : ℂ) : ExtPlane) ∨
         mobiusSL (slRealToComplex γ) p = ((conj ((A i • τ : UpperHalfPlane) : ℂ) : ℂ) : ExtPlane))) := by
  classical
  -- A covering compact core needs neither freeness nor the precise-invariance clauses;
  -- they serve the chart producers.
  have _ := hfree
  have _ := hpc
  have _ := hpf
  have _ := hcross
  let σ : ExtPlane ≃ₜ ExtPlane := Complex.conjCLE.toHomeomorph.onePointCongr
  have hσ : ∀ z : ℂ, σ (z : ExtPlane) = ((conj z : ℂ) : ExtPlane) := fun z => rfl
  have hσσ : ∀ y : ExtPlane, σ (σ y) = y := by
    intro y
    induction y using OnePoint.rec with
    | infty => rfl
    | coe z => rw [hσ, hσ, Complex.conj_conj]
  have hσlim : ∀ x ∈ fuchsianLimitSet Γ, σ x = x := by
    intro x hx
    rcases s36a_limit_real hΓ hx with ⟨w, hw, rfl⟩ | hinf
    · rw [hσ]
      congr 1
      exact Complex.conj_eq_iff_im.2 hw
    · rw [Set.mem_singleton_iff.1 hinf]
      rfl
  -- Pieces: C itself, the height-[1,2] cusp strips, and the closed doubled funnel sectors.
  let Q : Set ℂ := (fun x : ℝ × ℝ => (x.1 : ℂ) + (x.2 : ℂ) * I) '' (Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2)
  let F : ℝ × ℝ → ℂ := fun x => (x.1 : ℂ) * exp ((x.2 : ℂ) * I)
  let Sf : Fin m → Set ℂ := fun j => F '' (Icc (1 : ℝ) (lam j) ×ˢ Icc (-θ j) (θ j))
  let Lup : Set ExtPlane :=
    ((fun τ : UpperHalfPlane => ((τ : ℂ) : ExtPlane)) '' C ∪
      ⋃ i : Fin c, k24_mobiusSLHomeo (slRealToComplex (A i)) '' (((↑) : ℂ → ExtPlane) '' Q)) ∪
      ⋃ j : Fin m, k24_mobiusSLHomeo (slRealToComplex (B j)) '' (((↑) : ℂ → ExtPlane) '' Sf j)
  have hQ : IsCompact Q := (isCompact_Icc.prod isCompact_Icc).image
    ((Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hFc : Continuous F := (Complex.continuous_ofReal.comp continuous_fst).mul
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hLup : IsCompact Lup := by
    refine (IsCompact.union ?_ ?_).union ?_
    · exact hC.image (OnePoint.continuous_coe.comp UpperHalfPlane.continuous_coe)
    · exact isCompact_iUnion fun i =>
        (hQ.image OnePoint.continuous_coe).image (k24_mobiusSLHomeo _).continuous
    · exact isCompact_iUnion fun j =>
        (((isCompact_Icc.prod isCompact_Icc).image hFc).image OnePoint.continuous_coe).image
          (k24_mobiusSLHomeo _).continuous
  have hQmem : ∀ q : ℂ, q.re ∈ Icc (0 : ℝ) 1 → q.im ∈ Icc (1 : ℝ) 2 → q ∈ Q :=
    fun q h1 h2 => ⟨(q.re, q.im), ⟨h1, h2⟩, Complex.re_add_im q⟩
  have hSf : ∀ j (r φ : ℝ), r ∈ Icc (1 : ℝ) (lam j) → φ ∈ Icc (-θ j) (θ j) →
      (r : ℂ) * exp ((φ : ℂ) * I) ∈ Sf j :=
    fun j r φ hr hφ => ⟨(r, φ), ⟨hr, hφ⟩, rfl⟩
  have hmemX : ∀ τ ∈ C, (((τ : UpperHalfPlane) : ℂ) : ExtPlane) ∈ Lup :=
    fun τ hτ => Or.inl (Or.inl ⟨τ, hτ, rfl⟩)
  have hmemY : ∀ i (q : ℂ), q ∈ Q → mobiusSL (slRealToComplex (A i)) (q : ExtPlane) ∈ Lup :=
    fun i q hq => Or.inl (Or.inr (mem_iUnion.2 ⟨i, (q : ExtPlane), ⟨q, hq, rfl⟩, rfl⟩))
  have hmemZ : ∀ j (w : ℂ), w ∈ Sf j → mobiusSL (slRealToComplex (B j)) (w : ExtPlane) ∈ Lup :=
    fun j w hw => Or.inr (mem_iUnion.2 ⟨j, (w : ExtPlane), ⟨w, hw, rfl⟩, rfl⟩)
  -- Every piece is ordinary or non-real.
  have hLupord : Lup ⊆ (fuchsianLimitSet Γ)ᶜ := by
    rintro x ((⟨τ, -, rfl⟩ | hx) | hx)
    · exact s36d1g_coe_not_limit hΓ τ.im_pos.ne'
    · obtain ⟨i, _, ⟨q, hq, rfl⟩, rfl⟩ := mem_iUnion.1 hx
      obtain ⟨⟨u, v⟩, ⟨-, hv⟩, hq'⟩ := hq
      have hpos : 0 < q.im := by
        rw [← hq']
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add,
          add_zero]
        linarith [hv.1]
      have e : (k24_mobiusSLHomeo (slRealToComplex (A i))) ((q : ℂ) : ExtPlane) =
          (((A i • UpperHalfPlane.mk q hpos : UpperHalfPlane) : ℂ) : ExtPlane) :=
        h36t_mobiusSL_coe (A i) (UpperHalfPlane.mk q hpos)
      rw [e]
      exact s36d1g_coe_not_limit hΓ (A i • UpperHalfPlane.mk q hpos).im_pos.ne'
    · obtain ⟨j, _, ⟨w, hw, rfl⟩, rfl⟩ := mem_iUnion.1 hx
      obtain ⟨⟨r, φ⟩, ⟨hr, hφ⟩, hw'⟩ := hw
      obtain ⟨-, -, hθ0, hθπ, -⟩ := hfun j
      by_cases hφ0 : φ = 0
      · have hwr : w = (r : ℂ) := by
          rw [← hw', hφ0]
          simp [F]
        rw [hwr]
        exact (harcord j r (by linarith [hr.1])).2
      · have hsin : Real.sin φ ≠ 0 := fun h0 => hφ0
          ((Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [hφ.1]) (by linarith [hφ.2])).1 h0)
        have him : w.im ≠ 0 := by
          rw [← hw']
          show ((r : ℂ) * exp ((φ : ℂ) * I)).im ≠ 0
          rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
          exact mul_ne_zero (by linarith [hr.1]) hsin
        obtain ⟨v, hv, hmv⟩ := s36d1g_msl_nonreal (B j) him
        show mobiusSL (slRealToComplex (B j)) (w : ExtPlane) ∉ fuchsianLimitSet Γ
        rw [hmv]
        exact s36d1g_coe_not_limit hΓ hv
  -- The mirror image is ordinary too: the limit set is real, hence fixed by conjugation.
  have hLord : Lup ∪ σ '' Lup ⊆ (fuchsianLimitSet Γ)ᶜ := by
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact hLupord hx
    · intro hl
      have h1 := hσlim _ hl
      rw [hσσ] at h1
      have h2 : y ∈ fuchsianLimitSet Γ := by
        rw [h1]
        exact hl
      exact hLupord hy h2
  -- Ordinary boundary points: move along a funnel arc into the period segment [1, lam].
  have hreal : ∀ x ∈ ordinarySet Γ, ∃ γ ∈ Γ, mobiusSL (slRealToComplex γ) x ∈ Lup := by
    intro x hx
    obtain ⟨γ, hγ, j, t, ht, rfl⟩ := harccover x hx
    obtain ⟨hhj, hlam, hθ0, -, hscale⟩ := hfun j
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow ht hlam
    refine ⟨h j ^ (-n) * γ⁻¹, Γ.mul_mem (zpow_mem hhj _) (Γ.inv_mem hγ), ?_⟩
    have hmove : mobiusSL (slRealToComplex (h j ^ (-n) * γ⁻¹))
        (mobiusSL (slRealToComplex (γ * B j)) ((t : ℂ) : ExtPlane)) =
        mobiusSL (slRealToComplex (B j)) (((lam j ^ (-n) * t : ℝ) : ℂ) : ExtPlane) := by
      rw [k24_slReal_mul, k24_slReal_mul, k24_mobiusSL_mul, k24_mobiusSL_mul, k24_slReal_inv,
        k24_mobiusSL_inv_apply]
      exact s36d1g_scale_ext (B j) (h j) (by linarith) hscale (-n) t
    rw [hmove]
    have hpos : 0 < lam j ^ n := zpow_pos (by linarith) n
    have hr1 : 1 ≤ lam j ^ (-n) * t := by
      rw [zpow_neg, inv_mul_eq_div, one_le_div hpos]
      exact hn1
    have hr2 : lam j ^ (-n) * t ≤ lam j := by
      rw [zpow_neg, inv_mul_eq_div, div_le_iff₀ hpos, mul_comm,
        ← zpow_add_one₀ (by linarith : lam j ≠ 0)]
      exact hn2.le
    apply hmemZ j
    have hmem := hSf j (lam j ^ (-n) * t) 0 ⟨hr1, hr2⟩ ⟨by linarith, by linarith⟩
    simpa using hmem
  -- Upper half-plane points: the F1 cover, then a cusp translation or a funnel scaling.
  have hupc : ∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, (((γ • τ : UpperHalfPlane) : ℂ) : ExtPlane) ∈ Lup ∨
      ∃ i : Fin c, ∃ τ' : UpperHalfPlane, 2 < τ'.im ∧ γ • τ = A i • τ' := by
    intro τ
    obtain ⟨γ, hγ, hC' | ⟨i, hi⟩ | ⟨j, hj⟩⟩ := hcover τ
    · exact ⟨γ, hγ, Or.inl (hmemX _ hC')⟩
    · obtain ⟨hπ, htr⟩ := hcusp i
      obtain ⟨s, hs⟩ : ∃ s : UpperHalfPlane, s = (A i)⁻¹ • (γ • τ) := ⟨_, rfl⟩
      rw [← hs] at hi
      obtain ⟨t, ht⟩ : ∃ t : ℤ, t = ⌊s.re⌋ := ⟨_, rfl⟩
      have hf1 := Int.floor_le s.re
      have hf2 := Int.lt_floor_add_one s.re
      rw [← ht] at hf1 hf2
      obtain ⟨s', hs'⟩ : ∃ s' : UpperHalfPlane, s' = ((-t : ℤ) : ℝ) +ᵥ s := ⟨_, rfl⟩
      have hgs : (π₀ i ^ (-t) * γ) • τ = A i • s' := by
        rw [hs', mul_smul, ← smul_inv_smul (A i) (γ • τ), ← hs, ft1e_zpow_smul htr (-t) s]
      have him : s'.im = s.im := by rw [hs', UpperHalfPlane.vadd_im]
      have hre : s'.re = ((-t : ℤ) : ℝ) + s.re := by rw [hs', UpperHalfPlane.vadd_re]
      refine ⟨π₀ i ^ (-t) * γ, Γ.mul_mem (zpow_mem hπ _) hγ, ?_⟩
      by_cases h2 : s'.im ≤ 2
      · left
        rw [hgs, ← h36t_mobiusSL_coe (A i) s']
        apply hmemY i
        apply hQmem
        · show s'.re ∈ Icc (0 : ℝ) 1
          rw [hre, Set.mem_Icc]
          push_cast
          constructor <;> linarith
        · show s'.im ∈ Icc (1 : ℝ) 2
          exact ⟨by rw [him]; exact hi.le, h2⟩
      · right
        exact ⟨i, s', by linarith, hgs⟩
    · obtain ⟨hhj, hlam, hθ0, -, hscale⟩ := hfun j
      obtain ⟨w, hw⟩ : ∃ w : UpperHalfPlane, w = (B j)⁻¹ • (γ • τ) := ⟨_, rfl⟩
      rw [← hw] at hj
      have hw0 : 0 < ‖(w : ℂ)‖ := norm_pos_iff.2 w.ne_zero
      obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hw0 hlam
      obtain ⟨w2, hw2⟩ : ∃ w2 : UpperHalfPlane, w2 = (B j)⁻¹ • (h j ^ (-n) • (B j • w)) :=
        ⟨_, rfl⟩
      have hw2c : (w2 : ℂ) = (lam j : ℂ) ^ (-n) * w := by
        rw [hw2]
        exact ft4a_scale_zpow hscale (-n) w
      have hgs : (h j ^ (-n) * γ) • τ = B j • w2 := by
        rw [hw2, smul_inv_smul, mul_smul, hw, smul_inv_smul]
      refine ⟨h j ^ (-n) * γ, Γ.mul_mem (zpow_mem hhj _) hγ, Or.inl ?_⟩
      rw [hgs, ← h36t_mobiusSL_coe (B j) w2]
      apply hmemZ j
      have hpos : 0 < lam j ^ n := zpow_pos (by linarith) n
      have hnorm : ‖(w2 : ℂ)‖ = lam j ^ (-n) * ‖(w : ℂ)‖ := by
        rw [hw2c, norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
      have harg : arg (w2 : ℂ) = arg (w : ℂ) := by
        rw [hw2c, ← Complex.ofReal_zpow]
        exact Complex.arg_real_mul _ (zpow_pos (by linarith) _)
      have hr1 : 1 ≤ lam j ^ (-n) * ‖(w : ℂ)‖ := by
        rw [zpow_neg, inv_mul_eq_div, one_le_div hpos]
        exact hn1
      have hr2 : lam j ^ (-n) * ‖(w : ℂ)‖ ≤ lam j := by
        rw [zpow_neg, inv_mul_eq_div, div_le_iff₀ hpos, mul_comm,
          ← zpow_add_one₀ (by linarith : lam j ≠ 0)]
        exact hn2.le
      have ha0 : 0 ≤ arg (w : ℂ) := Complex.arg_nonneg_iff.2 w.im_pos.le
      have hmem := hSf j ‖(w2 : ℂ)‖ (arg (w2 : ℂ))
        ⟨by rw [hnorm]; exact hr1, by rw [hnorm]; exact hr2⟩
        ⟨by rw [harg]; linarith, by rw [harg]; exact hj.le⟩
      rwa [Complex.norm_mul_exp_arg_mul_I] at hmem
  refine ⟨Lup ∪ σ '' Lup, hLup.union (hLup.image σ.continuous), hLord, ?_⟩
  intro p hp
  induction p using OnePoint.rec with
  | infty =>
    obtain ⟨γ, hγ, hx⟩ := hreal extInf ⟨Or.inr rfl, hp⟩
    exact ⟨γ, hγ, Or.inl (Or.inl hx)⟩
  | coe z =>
    rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
    · have hc : 0 < (conj z).im := by
        rw [Complex.conj_im]
        linarith
      obtain ⟨γ, hγ, hγτ⟩ := hupc (UpperHalfPlane.mk (conj z) hc)
      have hz : (z : ExtPlane) =
          ((conj ((UpperHalfPlane.mk (conj z) hc : UpperHalfPlane) : ℂ) : ℂ) : ExtPlane) := by
        rw [UpperHalfPlane.coe_mk, Complex.conj_conj]
      have hmz : mobiusSL (slRealToComplex γ) (z : ExtPlane) =
          ((conj ((γ • UpperHalfPlane.mk (conj z) hc : UpperHalfPlane) : ℂ) : ℂ) : ExtPlane) := by
        rw [hz]
        exact s36d1g_msl_lower γ _
      refine ⟨γ, hγ, ?_⟩
      rw [hmz]
      rcases hγτ with hL | ⟨i, τ', hτ', heq⟩
      · exact Or.inl (Or.inr ⟨_, hL, rfl⟩)
      · exact Or.inr ⟨i, τ', hτ', Or.inr (by rw [heq])⟩
    · obtain ⟨γ, hγ, hx⟩ := hreal (z : ExtPlane) ⟨Or.inl ⟨z, hzero, rfl⟩, hp⟩
      exact ⟨γ, hγ, Or.inl (Or.inl hx)⟩
    · obtain ⟨γ, hγ, hγτ⟩ := hupc (UpperHalfPlane.mk z hpos)
      have hmz : mobiusSL (slRealToComplex γ) (z : ExtPlane) =
          (((γ • UpperHalfPlane.mk z hpos : UpperHalfPlane) : ℂ) : ExtPlane) :=
        h36t_mobiusSL_coe γ (UpperHalfPlane.mk z hpos)
      refine ⟨γ, hγ, ?_⟩
      rw [hmz]
      rcases hγτ with hL | ⟨i, τ', hτ', heq⟩
      · exact Or.inl (Or.inl hL)
      · exact Or.inr ⟨i, τ', hτ', Or.inl (by rw [heq])⟩

end LiZhongQC
