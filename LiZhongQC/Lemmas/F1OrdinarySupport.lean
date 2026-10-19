import LiZhongQC.Lemmas.F1CuspFamilySupport
import LiZhongQC.Lemmas.F1AssemblySupport
import LiZhongQC.Lemmas.F1LocalGeometry

/-! F1 ordinary-boundary support 003. Hyperbolic endpoints, a uniform angle gap
against the full cusp family, and exhaustive spherical ordinary-arc coverage.
Source-only candidate. No final decomposition or finite selection is assumed. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Both fixed endpoints of a normalized hyperbolic element are limit points, by positive
and negative iterates. This does not require the existence of a parabolic element. -/
theorem ft1fas_hyperbolic_endpoints_limit (hΓ : IsFuchsian Γ)
    (B h : Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam : ℝ)
    (hh : h ∈ Γ) (hlam : 1 < lam)
    (hscale : ∀ τ : UpperHalfPlane, ((B⁻¹ • (h • (B • τ)) : UpperHalfPlane) : ℂ) =
      (lam : ℂ) * (τ : ℂ)) :
    mobiusSL (slRealToComplex B) ((0 : ℂ) : ExtPlane) ∈ fuchsianLimitSet Γ ∧
      mobiusSL (slRealToComplex B) extInf ∈ fuchsianLimitSet Γ := by
  -- The literal limit-set definition admits a constant orbit of a fixed point,
  -- provided the group elements are distinct; injectivity is established below.
  have _ := hΓ
  have hlam0 : 0 < lam := zero_lt_one.trans hlam
  have hinj : Function.Injective (fun n : ℕ => h ^ n) := by
    intro m n hmn
    have heq : ((B⁻¹ • (h ^ m • (B • UpperHalfPlane.I)) : UpperHalfPlane) : ℂ) =
        ((B⁻¹ • (h ^ n • (B • UpperHalfPlane.I)) : UpperHalfPlane) : ℂ) :=
      congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) ℝ =>
        ((B⁻¹ • (g • (B • UpperHalfPlane.I)) : UpperHalfPlane) : ℂ)) hmn
    have hm := ft4a_scale_zpow hscale (m : ℤ) UpperHalfPlane.I
    have hn := ft4a_scale_zpow hscale (n : ℤ) UpperHalfPlane.I
    simp only [zpow_natCast] at hm hn
    rw [hm, hn] at heq
    have hreal : lam ^ m = lam ^ n := by
      have heq' := congrArg Complex.im heq
      simpa only [UpperHalfPlane.coe_I, Complex.mul_I_im,
        ← Complex.ofReal_pow, Complex.ofReal_re] using heq'
    exact pow_right_injective₀ hlam0 (ne_of_gt hlam) hreal
  let N : Matrix.SpecialLinearGroup (Fin 2) ℝ := B⁻¹ * h * B
  have hN : ∀ τ : UpperHalfPlane, ((N • τ : UpperHalfPlane) : ℂ) =
      (lam : ℂ) * (τ : ℂ) := by
    intro τ
    simpa only [N, mul_smul] using hscale τ
  have hcross : ∀ τ : UpperHalfPlane,
      (N 0 0 : ℂ) * (τ : ℂ) + N 0 1 =
        (lam : ℂ) * (τ : ℂ) * ((N 1 0 : ℂ) * (τ : ℂ) + N 1 1) := by
    intro τ
    have ht := hN τ
    rw [h36t_coe_smul] at ht
    exact (div_eq_iff (h36t_den_ne N τ)).mp ht
  let τ₂ : UpperHalfPlane := ⟨2 * Complex.I, by norm_num⟩
  have hb₁ : N 0 1 = -lam * N 1 0 := by
    have hr := congrArg Complex.re (hcross UpperHalfPlane.I)
    norm_num [Complex.mul_re, Complex.mul_im] at hr
    nlinarith
  have hb₂ : N 0 1 = -4 * lam * N 1 0 := by
    have hr := congrArg Complex.re (hcross τ₂)
    norm_num [τ₂, Complex.mul_re, Complex.mul_im] at hr
    nlinarith
  have hc : N 1 0 = 0 := by
    have hprod : lam * N 1 0 = 0 := by nlinarith
    exact (mul_eq_zero.mp hprod).resolve_left hlam0.ne'
  have hb : N 0 1 = 0 := by simpa only [hc, mul_zero] using hb₁
  have hd : N 1 1 ≠ 0 := by
    intro hd
    have hdet := k24_det_realR N
    rw [hd, hc] at hdet
    norm_num at hdet
  have hfix0 : mobiusSL (slRealToComplex N) ((0 : ℂ) : ExtPlane) =
      ((0 : ℂ) : ExtPlane) := by
    rw [k24_mobiusSL_real, mobiusExt_coe (by simpa using
      (show (N 1 1 : ℂ) ≠ 0 by exact_mod_cast hd))]
    simp [mobiusFn, hb]
  have hfixInf : mobiusSL (slRealToComplex N) extInf = extInf :=
    (s36a_mextinf N).2 hc
  have hconj : ∀ p : ExtPlane,
      mobiusSL (slRealToComplex h) (mobiusSL (slRealToComplex B) p) =
        mobiusSL (slRealToComplex B) (mobiusSL (slRealToComplex N) p) := by
    intro p
    rw [← k24_mobiusSL_mul, ← k24_mobiusSL_mul, ← k24_slReal_mul, ← k24_slReal_mul]
    have heq : h * B = B * N := by dsimp only [N]; group
    rw [heq]
  constructor
  · apply ft1fas_infinite_fixed_point_limit h hh hinj
    rw [hconj, hfix0]
  · apply ft1fas_infinite_fixed_point_limit h hh hinj
    rw [hconj, hfixInf]

/-- A single positive funnel sector can be shrunk uniformly against every translated
height-one cusp. Scaling periodicity extends a compact fundamental real arc to the full ray. -/
theorem ft1fas_funnel_cusp_angle_gap (hΓ : IsFuchsian Γ) {n : ℕ}
    (A π₀ : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hcusp : ∀ i, π₀ i ∈ Γ ∧ ∀ τ : UpperHalfPlane,
      π₀ i • (A i • τ) = A i • ((1 : ℝ) +ᵥ τ))
    (hpc : ∀ i i' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im →
      1 < ((A i')⁻¹ • (γ • (A i • τ))).im →
      i = i' ∧ ∃ k : ℤ, γ = π₀ i ^ k ∨ γ = -π₀ i ^ k)
    (B h : Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam θ : ℝ)
    (hh : h ∈ Γ) (hlam : 1 < lam) (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hscale : ∀ τ : UpperHalfPlane, ((B⁻¹ • (h • (B • τ)) : UpperHalfPlane) : ℂ) =
      (lam : ℂ) * (τ : ℂ))
    (harc : ∀ t : ℝ, 0 < t →
      mobiusSL (slRealToComplex B) ((t : ℂ) : ExtPlane) ∈ ordinarySet Γ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ θ ∧
      ∀ i γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im →
        ε ≤ arg ((B⁻¹ • (γ • (A i • τ)) : UpperHalfPlane) : ℂ) := by
  -- Only positivity of the incoming angle is needed for this shrinking step.
  have _ := hθπ
  let f : ℝ → ExtPlane := fun r => mobiusSL (slRealToComplex B) ((r : ℂ) : ExtPlane)
  have hf : Continuous f := by
    show Continuous (fun r : ℝ => mobiusSL (slRealToComplex B) ((r : ℂ) : ExtPlane))
    exact (k22_t_continuous _).comp (OnePoint.continuous_coe.comp Complex.continuous_ofReal)
  obtain ⟨V, hVo, hLV, hVS⟩ := ft1fas_cusp_family_avoids_ordinary_compact
    hΓ A π₀ hcusp hpc (f '' Set.Icc 1 lam) (isCompact_Icc.image hf) (by
      rintro p ⟨r, hr, rfl⟩
      exact harc r (zero_lt_one.trans_le hr.1))
  let P : ℝ × ℝ → ExtPlane := fun q => mobiusSL (slRealToComplex B)
    (((q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I) : ℂ) : ExtPlane)
  have hP : Continuous P := by
    show Continuous (fun q : ℝ × ℝ => mobiusSL (slRealToComplex B)
      (((q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I) : ℂ) : ExtPlane))
    exact (k22_t_continuous _).comp (OnePoint.continuous_coe.comp (by fun_prop))
  have hbase : Set.Icc (1 : ℝ) lam ×ˢ ({0} : Set ℝ) ⊆ P ⁻¹' V := by
    intro q hq
    have hq0 : q.2 = 0 := Set.mem_singleton_iff.mp hq.2
    have heq : P q = f q.1 := by simp [P, f, hq0]
    rw [Set.mem_preimage, heq]
    exact hLV ⟨q.1, hq.1, rfl⟩
  obtain ⟨U, W, hUo, hWo, hIU, h0W, hUW⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton (hVo.preimage hP) hbase
  have _ := hUo
  obtain ⟨η, hη, hηW⟩ := Metric.mem_nhds_iff.mp
    (hWo.mem_nhds (h0W (Set.mem_singleton 0)))
  let ε : ℝ := min η θ
  have hε : 0 < ε := lt_min hη hθ0
  have hεη : ε ≤ η := min_le_left _ _
  have hεθ : ε ≤ θ := min_le_right _ _
  have hsector : ∀ σ : UpperHalfPlane, 1 ≤ ‖(σ : ℂ)‖ → ‖(σ : ℂ)‖ ≤ lam →
      arg (σ : ℂ) < ε → (((B • σ : UpperHalfPlane) : ℂ) : ExtPlane) ∈ V := by
    intro σ hσ0 hσ1 hσarg
    have ha0 := (ft1g_arg_bounds σ).1
    have haW : arg (σ : ℂ) ∈ W := hηW (by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ha0] using
        hσarg.trans_le hεη)
    have hv : (‖(σ : ℂ)‖, arg (σ : ℂ)) ∈ P ⁻¹' V := hUW ⟨hIU ⟨hσ0, hσ1⟩, haW⟩
    change P (‖(σ : ℂ)‖, arg (σ : ℂ)) ∈ V at hv
    simpa only [P, Complex.norm_mul_exp_arg_mul_I, h36t_mobiusSL_coe] using hv
  refine ⟨ε, hε, hεθ, ?_⟩
  intro i γ hγ τ hτ
  by_contra hsmall
  have harg : arg ((B⁻¹ • (γ • (A i • τ)) : UpperHalfPlane) : ℂ) < ε := lt_of_not_ge hsmall
  let σ : UpperHalfPlane := B⁻¹ • (γ • (A i • τ))
  obtain ⟨k, hk0, hk1⟩ := ft1g_scale_to_annulus lam hlam σ
  let σ' : UpperHalfPlane := B⁻¹ • (h ^ k • (B • σ))
  have hσ' : (σ' : ℂ) = (lam : ℂ) ^ k * (σ : ℂ) := ft4a_scale_zpow hscale k σ
  have harg' : arg (σ' : ℂ) = arg (σ : ℂ) := by
    rw [hσ']
    have hcast : (lam : ℂ) ^ k = ((lam ^ k : ℝ) : ℂ) := by norm_cast
    rw [hcast]
    exact Complex.arg_real_mul _ (zpow_pos (zero_lt_one.trans hlam) k)
  have hv := hsector σ' (by simpa only [hσ'] using hk0)
    (by simpa only [hσ'] using hk1) (by rw [harg']; exact harg)
  apply Set.disjoint_left.mp hVS hv
  refine ⟨h ^ k * γ, Γ.mul_mem (Γ.zpow_mem hh k) hγ, i, τ, hτ, ?_⟩
  simp only [σ', σ, smul_inv_smul, mul_smul]

/-- Exhaustive ordinary-arc coverage from actual exterior components and a compact
orbit core. The proof must use ordinary neighborhoods avoiding that core, not just the
interior complement equality. Spherical formulation includes components crossing infinity. -/
theorem ft1fas_ordinary_arc_coverage (hΓ : IsFuchsian Γ)
    {N n m : ℕ} (C : Set UpperHalfPlane) (hC : IsCompact C)
    (W : Fin N → Set UpperHalfPlane) (e : (Fin n ⊕ Fin m) ≃ Fin N)
    (hWo : ∀ j, IsOpen (W j))
    (hdisj : ∀ i j γ, γ ∈ Γ →
      (((fun τ : UpperHalfPlane => γ • τ) '' W i) ∩ W j).Nonempty →
      i = j ∧ (fun τ : UpperHalfPlane => γ • τ) '' W i = W j)
    (hcover : (⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' C)ᶜ =
      ⋃ γ ∈ Γ, ⋃ j, (fun τ : UpperHalfPlane => γ • τ) '' W j)
    (A : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ) (δ : Fin n → ℝ)
    (B : Fin m → Matrix.SpecialLinearGroup (Fin 2) ℝ) (θ : Fin m → ℝ)
    (hc : ∀ i, 0 < δ i ∧ (fun τ : UpperHalfPlane => A i • τ) ⁻¹' W (e (Sum.inl i)) ⊆
      {τ : UpperHalfPlane | δ i < τ.im})
    (hf : ∀ j, 0 < θ j ∧ θ j < Real.pi ∧
      (fun τ : UpperHalfPlane => B j • τ) ⁻¹' W (e (Sum.inr j)) ⊆
        {τ : UpperHalfPlane | arg (τ : ℂ) < Real.pi - θ j})
    (hcLimit : ∀ i, mobiusSL (slRealToComplex (A i)) extInf ∈ fuchsianLimitSet Γ)
    (hfLimit : ∀ j, mobiusSL (slRealToComplex (B j)) ((0 : ℂ) : ExtPlane) ∈ fuchsianLimitSet Γ ∧
      mobiusSL (slRealToComplex (B j)) extInf ∈ fuchsianLimitSet Γ) :
    ∀ x : ExtPlane, x ∈ ordinarySet Γ →
      ∃ γ ∈ Γ, ∃ j : Fin m, ∃ t : ℝ, 0 < t ∧
        x = mobiusSL (slRealToComplex (γ * B j)) ((t : ℂ) : ExtPlane) := by
  classical
  intro x hx
  let E : (Γ × Fin N) → Set UpperHalfPlane := fun q =>
    (fun τ : UpperHalfPlane => q.1.1 • τ) '' W q.2
  have hEo : ∀ q, IsOpen (E q) := fun q => isOpenMap_smul q.1.1 _ (hWo q.2)
  have hEeq : ∀ q r, (E q ∩ E r).Nonempty → E q = E r := by
    intro q r hqr
    obtain ⟨z, ⟨u, hu, huz⟩, ⟨v, hv, hvz⟩⟩ := hqr
    have huz' : q.1.1 • u = z := huz
    have hvz' : r.1.1 • v = z := hvz
    have heq : (r.1.1⁻¹ * q.1.1) • u = v := by
      rw [mul_smul, huz', ← hvz', inv_smul_smul]
    have htrans := (hdisj q.2 r.2 (r.1.1⁻¹ * q.1.1)
      (Γ.mul_mem (Γ.inv_mem r.1.2) q.1.2) ⟨v, ⟨u, hu, heq⟩, hv⟩).2
    have hq : E q = (fun z : UpperHalfPlane => r.1.1 • z) ''
        ((fun τ : UpperHalfPlane => (r.1.1⁻¹ * q.1.1) • τ) '' W q.2) := by
      rw [Set.image_image]
      apply congrArg (fun f : UpperHalfPlane → UpperHalfPlane => f '' W q.2)
      funext τ
      simp only [Function.comp_def, mul_smul, smul_inv_smul]
    rw [hq, htrans]
    all_goals rfl
  obtain ⟨V, hVo, hxV, hVC⟩ := ft1fas_compact_saturation_avoids_ordinary hΓ C hC x hx
  have hVE : ∀ z : UpperHalfPlane, ((z : ℂ) : ExtPlane) ∈ V → ∃ q, z ∈ E q := by
    intro z hzV
    have hzC : z ∈ (⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' C)ᶜ := by
      intro hzC
      obtain ⟨γ, hγ, τ, hτ, hτz⟩ := Set.mem_iUnion₂.mp hzC
      exact Set.disjoint_left.mp hVC hzV ⟨γ, hγ, τ, hτ, by rw [← hτz]⟩
    rw [hcover] at hzC
    obtain ⟨γ, hγ, hzγ⟩ := Set.mem_iUnion₂.mp hzC
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hzγ
    exact ⟨(⟨γ, hγ⟩, j), hzj⟩
  -- Shrinking works on the real sphere, including infinity. Every pair of points
  -- in the smaller half-neighborhood is joined inside V by its geodesic segment.
  obtain ⟨V', hV', hV'V, hgeo⟩ := h36t_shrink hx.1 (hVo.mem_nhds hxV)
  obtain ⟨O, hOV', hOo, hxO⟩ := _root_.mem_nhds_iff.mp hV'
  have hxH : x ∈ closure (toExt upperHalf) := h36t_extRealLine_subset_closure hx.1
  obtain ⟨p, hpO, z, hz, hzp⟩ := mem_closure_iff.mp hxH O hOo hxO
  let a : UpperHalfPlane := ⟨z, hz⟩
  have haO : ((a : ℂ) : ExtPlane) ∈ O := by change (z : ExtPlane) ∈ O; rwa [hzp]
  obtain ⟨q₀, haq₀⟩ := hVE a (hV'V (hOV' haO))
  let R : Set UpperHalfPlane := ⋃ q : {q : Γ × Fin N // E q ≠ E q₀}, E q.1
  have hRo : IsOpen R := isOpen_iUnion fun q => hEo q.1
  have hER : Disjoint (E q₀) R := by
    apply Set.disjoint_left.mpr
    intro z hz₀ hzR
    obtain ⟨q, hzq⟩ := Set.mem_iUnion.mp hzR
    exact q.2 (hEeq q.1 q₀ ⟨z, hzq, hz₀⟩)
  have hOE : ∀ b : UpperHalfPlane, ((b : ℂ) : ExtPlane) ∈ O → b ∈ E q₀ := by
    intro b hbO
    let g : unitInterval → UpperHalfPlane := fun t => c36_d_geod a b t
    have hg : Continuous g := c36_d_geod_continuous.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_subtype_val))
    have hgc : Set.range g ⊆ E q₀ ∪ R := by
      rintro z ⟨t, rfl⟩
      obtain ⟨q, hq⟩ := hVE (g t) (hgeo a b (hOV' haO) (hOV' hbO) t)
      by_cases heq : E q = E q₀
      · exact Or.inl (heq ▸ hq)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨q, heq⟩, hq⟩)
    have haRange : a ∈ Set.range g := ⟨0, by simpa only [g, Set.Icc.coe_zero] using h36t_geod_zero a b⟩
    have hbRange : b ∈ Set.range g := ⟨1, by simpa only [g, Set.Icc.coe_one] using h36t_geod_one a b⟩
    rcases IsPreconnected.subset_or_subset (hEo q₀) hRo hER hgc
      (isPreconnected_range hg) with hleft | hright
    · exact hleft hbRange
    · exact (Set.disjoint_left.mp hER haq₀ (hright haRange)).elim
  -- Thus the entire smaller H half-neighborhood lies in one fixed translated
  -- exterior. Only now pass to its spherical closure.
  have hxE : x ∈ closure ((fun τ : UpperHalfPlane => ((τ : ℂ) : ExtPlane)) '' E q₀) := by
    apply _root_.mem_closure_iff.mpr
    intro U hUo hxU
    obtain ⟨p, hpUO, z, hz, hzp⟩ := mem_closure_iff.mp hxH (U ∩ O)
      (hUo.inter hOo) ⟨hxU, hxO⟩
    let b : UpperHalfPlane := ⟨z, hz⟩
    have hbO : ((b : ℂ) : ExtPlane) ∈ O := by change (z : ExtPlane) ∈ O; rw [hzp]; exact hpUO.2
    exact ⟨p, hpUO.1, b, hOE b hbO, hzp⟩
  have hreturn : ∀ D : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      mobiusSL (slRealToComplex (q₀.1.1 * D))
        (mobiusSL (slRealToComplex (q₀.1.1 * D)⁻¹) x) = x := by
    intro D
    rw [k24_slReal_inv, k24_mobiusSL_apply_inv]
  have hnotend : ∀ (D : Matrix.SpecialLinearGroup (Fin 2) ℝ) (p : ExtPlane),
      mobiusSL (slRealToComplex D) p ∈ fuchsianLimitSet Γ →
      mobiusSL (slRealToComplex (q₀.1.1 * D)⁻¹) x ≠ p := by
    intro D p hp heq
    apply hx.2
    have hlim := k22_t_limitSet_smul (Subgroup.mem_map_of_mem _ q₀.1.2) hp
    rw [← k24_mobiusSL_mul] at hlim
    change mobiusSL (slRealToComplex q₀.1.1 * slRealToComplex D) p ∈ _ at hlim
    rw [← k24_slReal_mul] at hlim
    rw [← heq, hreturn] at hlim
    exact hlim
  have hcoord : ∀ D : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      mobiusSL (slRealToComplex (q₀.1.1 * D)⁻¹) x ∈
        closure ((fun τ : UpperHalfPlane => ((τ : ℂ) : ExtPlane)) ''
          ((fun τ : UpperHalfPlane => D • τ) ⁻¹' W q₀.2)) := by
    intro D
    have hcl := mem_closure_image (k22_t_continuous (slRealToComplex (q₀.1.1 * D)⁻¹)).continuousAt hxE
    apply closure_mono ?_ hcl
    rintro p ⟨p₀, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨D⁻¹ • w, ?_, ?_⟩
    · change D • (D⁻¹ • w) ∈ W q₀.2
      simpa only [smul_inv_smul] using hw
    · rw [h36t_mobiusSL_coe]
      simp only [mul_inv_rev, mul_smul, inv_smul_smul]
  obtain ⟨idx, hidx⟩ := e.surjective q₀.2
  rcases idx with i | j
  · have hycl := hcoord (A i)
    rw [← hidx] at hycl
    have hyR := k24_real_mapsTo_extRealLine (q₀.1.1 * A i)⁻¹ hx.1
    rcases hyR with ⟨z, hzR, hzy⟩ | hyInf
    · let Z : Set ℂ := ((↑) : UpperHalfPlane → ℂ) ''
        ((fun τ : UpperHalfPlane => A i • τ) ⁻¹' W (e (Sum.inl i)))
      have hzcl : z ∈ closure Z := by
        rw [OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image]
        change (z : ExtPlane) ∈ closure (((↑) : ℂ → ExtPlane) '' Z)
        rw [hzy]
        simpa only [Z, Set.image_image, Function.comp_def] using hycl
      have hZ : Z ⊆ {z : ℂ | δ i ≤ z.im} := by
        rintro z ⟨τ, hτ, rfl⟩
        exact (show δ i < τ.im from (hc i).2 hτ).le
      have hb := closure_minimal hZ (isClosed_le continuous_const Complex.continuous_im) hzcl
      have hz0 : z.im = 0 := hzR
      change δ i ≤ z.im at hb
      linarith [(hc i).1]
    · exact (hnotend (A i) extInf (hcLimit i) (Set.mem_singleton_iff.mp hyInf)).elim
  · have hycl := hcoord (B j)
    rw [← hidx] at hycl
    have hyR := k24_real_mapsTo_extRealLine (q₀.1.1 * B j)⁻¹ hx.1
    rcases hyR with ⟨z, hzR, hzy⟩ | hyInf
    · let Z : Set ℂ := ((↑) : UpperHalfPlane → ℂ) ''
        ((fun τ : UpperHalfPlane => B j • τ) ⁻¹' W (e (Sum.inr j)))
      have hzcl : z ∈ closure Z := by
        rw [OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image]
        change (z : ExtPlane) ∈ closure (((↑) : ℂ → ExtPlane) '' Z)
        rw [hzy]
        simpa only [Z, Set.image_image, Function.comp_def] using hycl
      have hZ : Z ⊆ {z : ℂ | 0 ≤ Real.sin (θ j) * z.re + Real.cos (θ j) * z.im} := by
        rintro z ⟨τ, hτ, rfl⟩
        have harg : arg (τ : ℂ) < Real.pi - θ j := (hf j).2.2 hτ
        have ha0 := (ft1g_arg_bounds τ).1
        have hs : 0 < Real.sin (arg (τ : ℂ) + θ j) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [(hf j).1]) (by linarith)
        show 0 ≤ Real.sin (θ j) * (τ : ℂ).re + Real.cos (θ j) * (τ : ℂ).im
        calc
          0 ≤ ‖(τ : ℂ)‖ * Real.sin (arg (τ : ℂ) + θ j) :=
            (mul_pos (norm_pos_iff.mpr τ.ne_zero) hs).le
          _ = Real.sin (θ j) * (τ : ℂ).re + Real.cos (θ j) * (τ : ℂ).im := by
            rw [Real.sin_add]
            linear_combination Real.sin (θ j) * Complex.norm_mul_cos_arg (τ : ℂ) +
              Real.cos (θ j) * Complex.norm_mul_sin_arg (τ : ℂ)
      have hb := closure_minimal hZ (isClosed_le continuous_const
        ((continuous_const.mul Complex.continuous_re).add
          (continuous_const.mul Complex.continuous_im))) hzcl
      have hz0 : z.im = 0 := hzR
      have hsin : 0 < Real.sin (θ j) := Real.sin_pos_of_pos_of_lt_pi (hf j).1 (hf j).2.1
      have hzr : 0 ≤ z.re := by
        change 0 ≤ Real.sin (θ j) * z.re + Real.cos (θ j) * z.im at hb
        rw [hz0, mul_zero, add_zero] at hb
        exact (mul_nonneg_iff_of_pos_left hsin).mp hb
      have hzne : z.re ≠ 0 := by
        intro heq
        have hz : z = 0 := Complex.ext (by simpa using heq) (by simpa using hz0)
        apply hnotend (B j) ((0 : ℂ) : ExtPlane) (hfLimit j).1
        rw [← hzy, hz]
      have hzcast : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hz0]
      refine ⟨q₀.1.1, q₀.1.2, j, z.re, lt_of_le_of_ne hzr (Ne.symm hzne), ?_⟩
      rw [hzcast, hzy, hreturn]
    · exact (hnotend (B j) extInf (hfLimit j).2 (Set.mem_singleton_iff.mp hyInf)).elim

end LiZhongQC
