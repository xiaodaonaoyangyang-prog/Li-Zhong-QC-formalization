import LiZhongQC.Ch08.S30_ModularGroupDiscontinuity

open Complex Set Metric Filter Topology unitInterval
open scoped Manifold ContDiff UpperHalfPlane

/-!
# Lifts of loops to `ℍ` (R83, S27 `[c]`, `[d1]`, `[d2]`; dev pieces by 下属3, banked by 下属1)

* `s83sg_lift_loop` [c]: a 1-periodic loop through `p₀ τ₀` lifts to an equivariant line through `τ₀`.
* `s83sg_lift_inj_meet` [d1]: lifts of simple loops meeting only at the base point are injective and meet once.
* `s83sg_lift_cross` [d2]: the disc chart at the centre gives the local two-sidedness of the lift `a` at `a 0`.
-/

noncomputable section
namespace LiZhongQC

universe u



/-- Equivariant extension of a segment `c : [0,1] → ℍ` with `c 1 = m • c 0` to a line `a (t+1) = m • a t`. -/
theorem s83sg_equiv_ext (m : Matrix.SpecialLinearGroup (Fin 2) ℝ) (c : ℝ → UpperHalfPlane)
    (hc : Continuous c) (h1 : c 1 = m • c 0) :
    ∃ a : ℝ → UpperHalfPlane, Continuous a ∧ (∀ t, a (t + 1) = m • a t) ∧
      ∀ t, 0 ≤ t → t ≤ 1 → a t = c t := by
  have hmz : ∀ n : ℤ, Continuous (fun x : UpperHalfPlane => (m ^ n) • x) := fun n =>
    (s27t_mdifferentiable_smul (m ^ n)).continuous
  have heq : ∀ (n : ℤ) (t : ℝ), (n : ℝ) ≤ t → t ≤ n + 1 →
      m ^ ⌊t⌋ • c (Int.fract t) = m ^ n • c (t - n) := by
    intro n t h0 h1'
    rcases h1'.lt_or_eq with hlt | heq
    · have hf : ⌊t⌋ = n := Int.floor_eq_iff.2 ⟨h0, hlt⟩
      rw [hf, Int.fract, hf]
    · have hf : ⌊t⌋ = n + 1 := by
        rw [Int.floor_eq_iff]
        push_cast
        exact ⟨heq.ge, by linarith⟩
      have hfr : Int.fract t = 0 := by
        rw [Int.fract, hf]
        push_cast
        linarith
      rw [hf, hfr, zpow_add_one, mul_smul, ← h1]
      congr 2
      linarith
  refine ⟨fun t => m ^ ⌊t⌋ • c (Int.fract t), ?_, ?_, ?_⟩
  · have hloc : LocallyFinite (fun n : ℤ => Set.Icc (n : ℝ) (n + 1)) := by
      intro x
      refine ⟨Set.Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
      refine (Set.finite_Icc (⌊x⌋ - 2) (⌊x⌋ + 1)).subset ?_
      rintro n ⟨y, ⟨hy1, hy2⟩, hy3, hy4⟩
      have hx1 := Int.floor_le x
      have hx2 := Int.lt_floor_add_one x
      constructor
      · by_contra hn
        have : n ≤ ⌊x⌋ - 3 := by omega
        have : (n : ℝ) ≤ ⌊x⌋ - 3 := by exact_mod_cast this
        linarith
      · by_contra hn
        have : ⌊x⌋ + 2 ≤ n := by omega
        have : (⌊x⌋ : ℝ) + 2 ≤ n := by exact_mod_cast this
        linarith
    refine hloc.continuous ?_ (fun n => isClosed_Icc) ?_
    · refine Set.eq_univ_of_forall fun t => ?_
      refine Set.mem_iUnion.2 ⟨⌊t⌋, Int.floor_le t, ?_⟩
      exact (Int.lt_floor_add_one t).le
    · intro n
      have hcont : Continuous (fun t : ℝ => m ^ n • c (t - n)) :=
        (hmz n).comp (hc.comp (continuous_id.sub continuous_const))
      exact hcont.continuousOn.congr fun t ht => heq n t ht.1 ht.2
  · intro t
    show m ^ ⌊t + 1⌋ • c (Int.fract (t + 1)) = m • (m ^ ⌊t⌋ • c (Int.fract t))
    rw [Int.floor_add_one, Int.fract_add_one, add_comm, zpow_one_add, mul_smul]
  · intro t h0 h1'
    show m ^ ⌊t⌋ • c (Int.fract t) = c t
    have := heq 0 t (by simpa using h0) (by simpa using h1')
    rw [this]
    simp


/-- Integer shifts of an equivariant line. -/
theorem s83sg_equiv_zpow (m : Matrix.SpecialLinearGroup (Fin 2) ℝ) (a : ℝ → UpperHalfPlane)
    (hper : ∀ t, a (t + 1) = m • a t) (t : ℝ) : ∀ n : ℤ, a (t + n) = m ^ n • a t := by
  intro n
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show t + (((k : ℤ) + 1 : ℤ) : ℝ) = (t + ((k : ℤ) : ℝ)) + 1 by push_cast; ring, hper, ih, ← mul_smul,
      ← zpow_one_add, add_comm 1 (k : ℤ)]
  | pred k ih =>
    have h := hper (t + ((-(k : ℤ) - 1 : ℤ) : ℝ))
    rw [show t + ((-(k : ℤ) - 1 : ℤ) : ℝ) + 1 = t + ((-(k : ℤ) : ℤ) : ℝ) by push_cast; ring, ih] at h
    have h2 : a (t + ((-(k : ℤ) - 1 : ℤ) : ℝ)) = m⁻¹ • (m ^ (-(k : ℤ)) • a t) := by
      rw [h, inv_smul_smul]
    rw [h2, ← mul_smul, ← zpow_neg_one, ← zpow_add]
    congr 2
    ring

/-- **[c, lifting of a loop]**  A 1-periodic loop `α` in `S₀` through `p₀ τ₀` lifts to a continuous line `a` in `ℍ`
through `τ₀` that is equivariant under the deck element `γ⁻¹` where `ρ γ` is the class of `α` (`ρ` as in
`s83sg_deck_pi1`). -/
theorem s83sg_lift_loop {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀]
    [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (τ₀ : UpperHalfPlane) (ρ : Γ₀ →* FundamentalGroup S₀ (p₀ τ₀))
    (hρ : ∀ (γ : Γ₀) (c : Path τ₀ ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ • τ₀))
        (L : Path (p₀ τ₀) (p₀ τ₀)), (∀ t, L t = p₀ (c t)) →
        ρ γ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L))
    {α : ℝ → S₀} (hα : Continuous α) (hper : ∀ t, α (t + 1) = α t) (h0 : α 0 = p₀ τ₀) :
    ∃ (γ : Γ₀) (a : ℝ → UpperHalfPlane), Continuous a ∧ a 0 = τ₀ ∧ (∀ t, p₀ (a t) = α t) ∧
      (∀ t, a (t + 1) = ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹) • a t) ∧
      ∀ L : Path (p₀ τ₀) (p₀ τ₀), (∀ t : I, L t = α t) →
        ρ γ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L) := by
  obtain ⟨hcov, -, -, hfib⟩ := hp₀
  let P : C(I, S₀) := ⟨fun t => α t, hα.comp continuous_subtype_val⟩
  have hP0 : P 0 = p₀ τ₀ := by
    show α ((0 : I) : ℝ) = p₀ τ₀
    simpa using h0
  let Lf : C(I, UpperHalfPlane) := hcov.liftPath P τ₀ hP0
  have hL0 : Lf 0 = τ₀ := hcov.liftPath_zero P τ₀ hP0
  have hLp : ∀ t, p₀ (Lf t) = α t := fun t => congrFun (hcov.liftPath_lifts P τ₀ hP0) t
  have hL1 : p₀ τ₀ = p₀ (Lf 1) := by
    rw [hLp]
    show p₀ τ₀ = α ((1 : I) : ℝ)
    simpa [h0] using (hper 0).symm
  obtain ⟨γ', hγ'Γ, hγ'⟩ := (hfib τ₀ (Lf 1)).1 hL1
  let γ : Γ₀ := ⟨γ', hγ'Γ⟩⁻¹
  have hγinv : ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ = γ' := by
    show ((⟨γ', hγ'Γ⟩⁻¹ : Γ₀) : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ = γ'
    simp
  let cext : ℝ → UpperHalfPlane := fun t => Lf (Set.projIcc 0 1 zero_le_one t)
  have hcext : Continuous cext := Lf.continuous.comp continuous_projIcc
  have hc1 : cext 1 = γ' • cext 0 := by
    show Lf (Set.projIcc 0 1 zero_le_one 1) = γ' • Lf (Set.projIcc 0 1 zero_le_one 0)
    have e1 : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = 1 := by simp
    have e0 : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := by simp
    rw [e1, e0, hL0, hγ']
  obtain ⟨a, ha, hper', hext⟩ := s83sg_equiv_ext γ' cext hcext hc1
  have ha0 : a 0 = τ₀ := by
    rw [hext 0 le_rfl zero_le_one]
    show Lf (Set.projIcc 0 1 zero_le_one 0) = τ₀
    have e0 : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := by simp
    rw [e0, hL0]
  -- the lift covers `α`
  have hapow : ∀ t, a t = γ' ^ ⌊t⌋ • cext (Int.fract t) := by
    intro t
    have hz : ∀ n : ℤ, a (t + n) = γ' ^ n • a t := s83sg_equiv_zpow γ' a hper' t
    have := hz (-⌊t⌋)
    have hfr : t + ((-⌊t⌋ : ℤ) : ℝ) = Int.fract t := by
      rw [Int.fract]; push_cast; ring
    rw [hfr] at this
    have h01 : a (Int.fract t) = cext (Int.fract t) :=
      hext _ (Int.fract_nonneg t) (Int.fract_lt_one t).le
    rw [h01] at this
    rw [this, ← mul_smul, ← zpow_add]
    simp
  have hpa : ∀ t, p₀ (a t) = α t := by
    intro t
    rw [hapow t]
    have hinv : p₀ (γ' ^ ⌊t⌋ • cext (Int.fract t)) = p₀ (cext (Int.fract t)) :=
      ((hfib _ _).2 ⟨γ' ^ ⌊t⌋, Γ₀.zpow_mem hγ'Γ _, rfl⟩).symm
    rw [hinv]
    have hp1 : p₀ (cext (Int.fract t)) = α (Int.fract t) := by
      show p₀ (Lf (Set.projIcc 0 1 zero_le_one (Int.fract t))) = _
      rw [hLp]
      have : ((Set.projIcc (0 : ℝ) 1 zero_le_one (Int.fract t) : I) : ℝ) = Int.fract t :=
        Set.projIcc_of_mem zero_le_one ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩ ▸ rfl
      rw [this]
    rw [hp1]
    have hperiod : Function.Periodic α 1 := hper
    have := hperiod.sub_int_mul_eq ⌊t⌋ (x := t)
    rw [mul_one] at this
    rw [Int.fract]
    exact this
  refine ⟨γ, a, ha, ha0, hpa, ?_, ?_⟩
  · intro t
    rw [hper', hγinv]
  · intro L hL
    have hend : (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ • τ₀ = Lf 1 := by
      rw [hγinv, hγ']
    let c : Path τ₀ ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ • τ₀) :=
      (show Path τ₀ (Lf 1) from ⟨Lf, hL0, rfl⟩).cast rfl hend
    exact hρ γ c L fun t => by
      rw [hL t]
      exact (hLp t).symm




/-- **[d1, injectivity and meeting of lifts]**  Lifts of simple loops are injective lines, and lifts of two loops
meeting only at the base point meet only there, once the deck elements have no coincident powers. -/
theorem s83sg_lift_inj_meet {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀]
    [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {α β : ℝ → S₀} {a b : ℝ → UpperHalfPlane}
    {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ₀) (hδ : δ ∈ Γ₀)
    (haα : ∀ t, p₀ (a t) = α t) (hbβ : ∀ t, p₀ (b t) = β t)
    (haγ : ∀ t, a (t + 1) = γ • a t) (hbδ : ∀ t, b (t + 1) = δ • b t) (h0 : a 0 = b 0)
    (hαs : ∀ s t, α s = α t → ∃ n : ℤ, s = t + n) (hβs : ∀ s t, β s = β t → ∃ n : ℤ, s = t + n)
    (hαβ : ∀ s t, α s = β t → (∃ m : ℤ, s = m) ∧ ∃ n : ℤ, t = n)
    (hpa : ∀ n : ℤ, n ≠ 0 → γ ^ n ≠ 1 ∧ γ ^ n ≠ -1) (hpb : ∀ n : ℤ, n ≠ 0 → δ ^ n ≠ 1 ∧ δ ^ n ≠ -1)
    (hpab : ∀ m n : ℤ, γ ^ m = δ ^ n ∨ γ ^ m = -δ ^ n → m = 0 ∧ n = 0) :
    Function.Injective a ∧ Function.Injective b ∧ ∀ s t, a s = b t → s = 0 ∧ t = 0 := by
  have hfree : ActsFreely Γ₀ := s27g_actsFreely hp₀
  have hinj : ∀ (x : Matrix.SpecialLinearGroup (Fin 2) ℝ) (c : ℝ → UpperHalfPlane) (d : ℝ → S₀),
      x ∈ Γ₀ → (∀ t, p₀ (c t) = d t) → (∀ t, c (t + 1) = x • c t) →
      (∀ s t, d s = d t → ∃ n : ℤ, s = t + n) →
      (∀ n : ℤ, n ≠ 0 → x ^ n ≠ 1 ∧ x ^ n ≠ -1) → Function.Injective c := by
    intro x c d hx hcd hper hsimple hpow s t hst
    obtain ⟨n, hn⟩ := hsimple s t (by rw [← hcd, ← hcd, hst])
    by_contra hne
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hn)
    have h1 : c (t + n) = x ^ n • c t := s83sg_equiv_zpow x c hper t n
    rw [← hn, hst] at h1
    have h2 := hfree (x ^ n) (Γ₀.zpow_mem hx n) (c t) h1.symm
    rcases h2 with h2 | h2
    · exact (hpow n hn0).1 h2
    · exact (hpow n hn0).2 h2
  refine ⟨hinj γ a α hγ haα haγ hαs hpa, hinj δ b β hδ hbβ hbδ hβs hpb, ?_⟩
  intro s t hst
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := hαβ s t (by rw [← haα, ← hbβ, hst])
  subst hm hn
  have e1 : a (0 + (m : ℝ)) = γ ^ m • a 0 := s83sg_equiv_zpow γ a haγ 0 m
  have e2 : b (0 + (n : ℝ)) = δ ^ n • b 0 := s83sg_equiv_zpow δ b hbδ 0 n
  rw [zero_add] at e1 e2
  have h3 : (δ ^ n)⁻¹ • (γ ^ m • a 0) = a 0 := by
    rw [← e1, hst, e2, h0, inv_smul_smul]
  have h4 := hfree ((δ ^ n)⁻¹ * γ ^ m) (Γ₀.mul_mem (Γ₀.inv_mem (Γ₀.zpow_mem hδ n)) (Γ₀.zpow_mem hγ m))
    (a 0) (by rw [mul_smul]; exact h3)
  have h5 := hpab m n (by
    rcases h4 with h4 | h4
    · left; exact (inv_mul_eq_one.1 h4).symm
    · right
      have h6 := (inv_mul_eq_iff_eq_mul.1 h4)
      rw [mul_neg, mul_one] at h6
      exact h6)
  rw [h5.1, h5.2]
  simp




/-- The open sector `{z : 0 < ‖z‖ < ρ, |arg (z e^{-ic})| < κ}`. -/
theorem s83sg_sector_open (c κ ρ : ℝ) (hκ : κ ≤ Real.pi) :
    IsOpen {z : ℂ | z ≠ 0 ∧ ‖z‖ < ρ ∧
      |Complex.arg (z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I))| < κ} := by
  have hg : Continuous (fun z : ℂ => z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I)) :=
    continuous_id.mul continuous_const
  have hE : Complex.exp (((-c : ℝ) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have harg : ContinuousOn Complex.arg Complex.slitPlane := fun x hx =>
    (Complex.continuousAt_arg hx).continuousWithinAt
  have h1 : IsOpen (Complex.slitPlane ∩ Complex.arg ⁻¹' Set.Ioo (-κ) κ) :=
    harg.isOpen_inter_preimage Complex.isOpen_slitPlane isOpen_Ioo
  have h2 : IsOpen ((fun z : ℂ => z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I)) ⁻¹'
      (Complex.slitPlane ∩ Complex.arg ⁻¹' Set.Ioo (-κ) κ) ∩ Metric.ball 0 ρ) :=
    (h1.preimage hg).inter Metric.isOpen_ball
  convert h2 using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioo, mem_ball_zero_iff,
    abs_lt]
  constructor
  · rintro ⟨hz, hn, hab⟩
    refine ⟨⟨?_, hab⟩, hn⟩
    rw [Complex.mem_slitPlane_iff_arg]
    refine ⟨?_, mul_ne_zero hz hE⟩
    intro h
    have := hab.2
    linarith [h]
  · rintro ⟨⟨hs, hab⟩, hn⟩
    refine ⟨?_, hn, hab⟩
    intro hz
    rw [hz, zero_mul] at hs
    exact Complex.slitPlane_ne_zero hs rfl


theorem s83sg_arg_polar (r φ : ℝ) (hr : 0 < r) (hφ : φ ∈ Set.Ioc (-Real.pi) Real.pi) :
    Complex.arg ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) = φ := by
  rw [Complex.exp_mul_I]
  exact Complex.arg_mul_cos_add_sin_mul_I hr hφ

/-- Polar description of the sector. -/
theorem s83sg_sector_polar (c κ ρ : ℝ) (hκ : κ ≤ Real.pi) :
    {z : ℂ | z ≠ 0 ∧ ‖z‖ < ρ ∧ |Complex.arg (z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I))| < κ} =
      (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (((p.2 + c : ℝ) : ℂ) * Complex.I)) ''
        (Set.Ioo 0 ρ ×ˢ Set.Ioo (-κ) κ) := by
  have hEn : ∀ z : ℂ, ‖z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I)‖ = ‖z‖ := by
    intro z
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hcancel : Complex.exp (((-c : ℝ) : ℂ) * Complex.I) * Complex.exp ((c : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    push_cast
    rw [← add_mul]
    simp
  ext z
  constructor
  · rintro ⟨hz, hn, hab⟩
    refine ⟨(‖z‖, Complex.arg (z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I))),
      ⟨⟨norm_pos_iff.2 hz, hn⟩, abs_lt.1 hab⟩, ?_⟩
    show ((‖z‖ : ℝ) : ℂ) * Complex.exp (((Complex.arg (z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I)) + c : ℝ) : ℂ)
      * Complex.I) = z
    have h := Complex.norm_mul_exp_arg_mul_I (z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I))
    rw [hEn] at h
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, ← mul_assoc, h, mul_assoc, hcancel, mul_one]
  · rintro ⟨⟨r, φ⟩, ⟨⟨hr0, hrρ⟩, hφ1, hφ2⟩, rfl⟩
    have hK : Complex.exp (((φ + c : ℝ) : ℂ) * Complex.I) * Complex.exp (((-c : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((φ : ℂ) * Complex.I) := by
      rw [← Complex.exp_add, ← add_mul]
      congr 2
      push_cast
      ring
    have hw : ((r : ℂ) * Complex.exp (((φ + c : ℝ) : ℂ) * Complex.I)) * Complex.exp (((-c : ℝ) : ℂ) * Complex.I) =
        (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) := by
      rw [mul_assoc, hK]
    have hn : ‖(r : ℂ) * Complex.exp (((φ + c : ℝ) : ℂ) * Complex.I)‖ = r := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    refine ⟨?_, by rw [hn]; exact hrρ, ?_⟩
    · intro h0
      have h0' : (r : ℂ) * Complex.exp (((φ + c : ℝ) : ℂ) * Complex.I) = 0 := h0
      rw [h0', norm_zero] at hn
      exact hr0.ne hn
    · show |Complex.arg ((r : ℂ) * Complex.exp (((φ + c : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((-c : ℝ) : ℂ) * Complex.I))| < κ
      rw [hw, s83sg_arg_polar r φ hr0 ⟨by linarith, by linarith⟩]
      exact abs_lt.2 ⟨hφ1, hφ2⟩


theorem s83sg_sector_connected (c κ ρ : ℝ) (hκ0 : 0 < κ) (hκ : κ ≤ Real.pi) (hρ : 0 < ρ) :
    IsConnected {z : ℂ | z ≠ 0 ∧ ‖z‖ < ρ ∧
      |Complex.arg (z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I))| < κ} := by
  rw [s83sg_sector_polar c κ ρ hκ]
  refine ((isConnected_Ioo hρ).prod (isConnected_Ioo (by linarith))).image _ ?_
  exact (by fun_prop : Continuous (fun p : ℝ × ℝ =>
    (p.1 : ℂ) * Complex.exp (((p.2 + c : ℝ) : ℂ) * Complex.I))).continuousOn

/-- Flipping the sign of `w` exchanges the sector of half-width `κ` with the complementary one. -/
theorem s83sg_arg_neg_cmp {w : ℂ} (hw : w ≠ 0) (κ : ℝ) :
    |Complex.arg (-w)| < Real.pi - κ ↔ κ < |Complex.arg w| := by
  have hle := Complex.arg_le_pi w
  have hlt := Complex.neg_pi_lt_arg w
  have hle' := Complex.arg_le_pi (-w)
  have hlt' := Complex.neg_pi_lt_arg (-w)
  by_cases h1 : 0 < w.im ∨ (w.im = 0 ∧ w.re < 0)
  · have h := Complex.arg_neg_eq_arg_sub_pi_iff.2 h1
    rw [h] at hlt' ⊢
    have hpos : 0 < Complex.arg w := by linarith
    rw [abs_of_pos hpos, abs_lt]
    constructor
    · rintro ⟨h2, -⟩
      linarith
    · intro h2
      constructor <;> linarith
  · have h2 : w.im < 0 ∨ (w.im = 0 ∧ 0 < w.re) := by
      push Not at h1
      rcases lt_trichotomy w.im 0 with h | h | h
      · exact Or.inl h
      · right
        refine ⟨h, ?_⟩
        rcases lt_trichotomy w.re 0 with hr | hr | hr
        · exact absurd hr (not_lt.2 (h1.2 h))
        · exact absurd (Complex.ext (by simpa using hr) (by simpa using h)) hw
        · exact hr
      · exact absurd h (not_lt.2 (h1.1))
    have h := Complex.arg_neg_eq_arg_add_pi_iff.2 h2
    rw [h] at hle' ⊢
    have hneg : Complex.arg w ≤ 0 := by linarith
    rw [abs_of_nonpos hneg, abs_lt]
    constructor
    · rintro ⟨-, h3⟩
      linarith
    · intro h3
      constructor <;> linarith


theorem s83sg_exp_rot (c d : ℝ) :
    Complex.exp (((-c : ℝ) : ℂ) * Complex.I) * Complex.exp ((d : ℂ) * Complex.I) =
      Complex.exp (((d - c : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add, ← add_mul]
  congr 2
  push_cast
  ring

/-- Polar representation `z = ‖z‖ e^{i (arg (z e^{-ic}) + c)}`. -/
theorem s83sg_polar_rep (c : ℝ) {z : ℂ} :
    z = (‖z‖ : ℂ) * Complex.exp (((Complex.arg (z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I)) + c : ℝ) : ℂ) *
      Complex.I) := by
  have hEn : ‖z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I)‖ = ‖z‖ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hcancel : Complex.exp (((-c : ℝ) : ℂ) * Complex.I) * Complex.exp ((c : ℂ) * Complex.I) = 1 := by
    rw [s83sg_exp_rot]; simp
  have h := Complex.norm_mul_exp_arg_mul_I (z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I))
  rw [hEn] at h
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, ← mul_assoc, h, mul_assoc, hcancel, mul_one]


theorem s83sg_ray_rot (s θ d : ℝ) :
    (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (((-d : ℝ) : ℂ) * Complex.I) =
      (s : ℂ) * Complex.exp (((θ - d : ℝ) : ℂ) * Complex.I) := by
  rw [mul_assoc, mul_comm (Complex.exp ((θ : ℂ) * Complex.I)), s83sg_exp_rot]

theorem s83sg_ray_norm (s θ : ℝ) (hs : 0 < s) : ‖(s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = s := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]

theorem s83sg_sector_split (θ0 θ1 θ2 θ3 ρ : ℝ) (h01 : θ0 < θ1) (h12 : θ1 < θ2) (h23 : θ2 < θ3)
    (h3 : θ3 < θ0 + 2 * Real.pi) (hρ : 0 < ρ) :
    ∃ Sp Sm : Set ℂ, IsOpen Sp ∧ IsOpen Sm ∧ IsConnected Sp ∧ IsConnected Sm ∧ Disjoint Sp Sm ∧
      Metric.ball (0 : ℂ) ρ \ ({z : ℂ | ∃ s : ℝ, 0 ≤ s ∧ s < ρ ∧ z = (s : ℂ) * Complex.exp ((θ0 : ℂ) * Complex.I)} ∪
        {z : ℂ | ∃ s : ℝ, 0 ≤ s ∧ s < ρ ∧ z = (s : ℂ) * Complex.exp ((θ2 : ℂ) * Complex.I)}) = Sp ∪ Sm ∧
      (∀ s : ℝ, 0 < s → s < ρ → (s : ℂ) * Complex.exp ((θ1 : ℂ) * Complex.I) ∈ Sp) ∧
      (∀ s : ℝ, 0 < s → s < ρ → (s : ℂ) * Complex.exp ((θ3 : ℂ) * Complex.I) ∈ Sm) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (θ0 + θ2) / 2 := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (θ2 - θ0) / 2 := ⟨_, rfl⟩
  have hpi := Real.pi_pos
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  have hκπ : κ < Real.pi := by rw [hκ]; linarith
  have hflip : Complex.exp (((-(c + Real.pi) : ℝ) : ℂ) * Complex.I) =
      -Complex.exp (((-c : ℝ) : ℂ) * Complex.I) := by
    have : ((-(c + Real.pi) : ℝ) : ℂ) * Complex.I =
        ((-c : ℝ) : ℂ) * Complex.I + (-((Real.pi : ℂ) * Complex.I)) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one, mul_neg_one]
  have hE0 : Complex.exp (((-c : ℝ) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hmemS2 : ∀ z : ℂ, z ∈ {z : ℂ | z ≠ 0 ∧ ‖z‖ < ρ ∧
      |Complex.arg (z * Complex.exp (((-(c + Real.pi) : ℝ) : ℂ) * Complex.I))| < Real.pi - κ} ↔
      (z ≠ 0 ∧ ‖z‖ < ρ ∧ κ < |Complex.arg (z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I))|) := by
    intro z
    simp only [Set.mem_ofPred_eq]
    rw [hflip, mul_neg]
    constructor
    · rintro ⟨hz, hn, h⟩
      exact ⟨hz, hn, (s83sg_arg_neg_cmp (mul_ne_zero hz hE0) κ).1 h⟩
    · rintro ⟨hz, hn, h⟩
      exact ⟨hz, hn, (s83sg_arg_neg_cmp (mul_ne_zero hz hE0) κ).2 h⟩
  have hmκ : -κ ∈ Set.Ioc (-Real.pi) Real.pi := ⟨by linarith, by linarith⟩
  have hpκ : κ ∈ Set.Ioc (-Real.pi) Real.pi := ⟨by linarith, by linarith⟩
  have hray : ∀ (θ ψ : ℝ), θ - c = ψ → ψ ∈ Set.Ioc (-Real.pi) Real.pi → ∀ z : ℂ, z ≠ 0 →
      ((∃ s : ℝ, 0 ≤ s ∧ s < ρ ∧ z = (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ↔
        (‖z‖ < ρ ∧ Complex.arg (z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I)) = ψ)) := by
    intro θ ψ hθψ hψ z hz
    constructor
    · rintro ⟨s, hs0, hsρ, rfl⟩
      have hs : 0 < s := by
        rcases hs0.lt_or_eq with h | h
        · exact h
        · exfalso; apply hz; rw [← h]; simp
      refine ⟨by rw [s83sg_ray_norm s θ hs]; exact hsρ, ?_⟩
      rw [s83sg_ray_rot, hθψ]
      exact s83sg_arg_polar s ψ hs hψ
    · rintro ⟨hn, harg⟩
      refine ⟨‖z‖, norm_nonneg _, hn, ?_⟩
      have hθ : ψ + c = θ := by linarith
      calc z = (‖z‖ : ℂ) * Complex.exp (((Complex.arg (z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I)) + c : ℝ) : ℂ) *
            Complex.I) := s83sg_polar_rep c
        _ = _ := by rw [harg, hθ]
  have hray0 := hray θ0 (-κ) (by rw [hc, hκ]; ring) hmκ
  have hray2 := hray θ2 κ (by rw [hc, hκ]; ring) hpκ
  refine ⟨{z : ℂ | z ≠ 0 ∧ ‖z‖ < ρ ∧ |Complex.arg (z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I))| < κ},
    {z : ℂ | z ≠ 0 ∧ ‖z‖ < ρ ∧
      |Complex.arg (z * Complex.exp (((-(c + Real.pi) : ℝ) : ℂ) * Complex.I))| < Real.pi - κ},
    s83sg_sector_open c κ ρ hκπ.le, s83sg_sector_open (c + Real.pi) (Real.pi - κ) ρ (by linarith),
    s83sg_sector_connected c κ ρ hκ0 hκπ.le hρ,
    s83sg_sector_connected (c + Real.pi) (Real.pi - κ) ρ (by linarith) (by linarith) hρ, ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro z h1 h2
    have h2' := (hmemS2 z).1 h2
    linarith [h1.2.2, h2'.2.2]
  · ext z
    simp only [Set.mem_sdiff, Set.mem_union, Metric.mem_ball, dist_zero_right, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hn, hnr⟩
      have hz : z ≠ 0 := by
        rintro rfl
        exact hnr (Or.inl ⟨0, le_rfl, hρ, by simp⟩)
      rcases lt_trichotomy |Complex.arg (z * Complex.exp (((-c : ℝ) : ℂ) * Complex.I))| κ with hlt | heq | hgt
      · exact Or.inl ⟨hz, hn, hlt⟩
      · exfalso
        rcases (abs_eq hκ0.le).1 heq with h | h
        · exact hnr (Or.inr ((hray2 z hz).2 ⟨hn, h⟩))
        · exact hnr (Or.inl ((hray0 z hz).2 ⟨hn, h⟩))
      · exact Or.inr ((hmemS2 z).2 ⟨hz, hn, hgt⟩)
    · rintro (⟨hz, hn, hlt⟩ | h2)
      · refine ⟨hn, ?_⟩
        rintro (h | h)
        · have := ((hray0 z hz).1 h).2
          rw [this, abs_neg, abs_of_pos hκ0] at hlt
          exact lt_irrefl _ hlt
        · have := ((hray2 z hz).1 h).2
          rw [this, abs_of_pos hκ0] at hlt
          exact lt_irrefl _ hlt
      · obtain ⟨hz, hn, hgt⟩ := (hmemS2 z).1 h2
        refine ⟨hn, ?_⟩
        rintro (h | h)
        · have := ((hray0 z hz).1 h).2
          rw [this, abs_neg, abs_of_pos hκ0] at hgt
          exact lt_irrefl _ hgt
        · have := ((hray2 z hz).1 h).2
          rw [this, abs_of_pos hκ0] at hgt
          exact lt_irrefl _ hgt
  · intro s hs hsρ
    have hne : (s : ℂ) * Complex.exp ((θ1 : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hs.ne') (Complex.exp_ne_zero _)
    refine ⟨hne, by rw [s83sg_ray_norm s θ1 hs]; exact hsρ, ?_⟩
    rw [s83sg_ray_rot]
    have h1 : θ1 - c ∈ Set.Ioo (-κ) κ := ⟨by rw [hc, hκ]; linarith, by rw [hc, hκ]; linarith⟩
    rw [s83sg_arg_polar s (θ1 - c) hs ⟨by linarith [h1.1], by linarith [h1.2]⟩]
    exact abs_lt.2 h1
  · intro s hs hsρ
    have hne : (s : ℂ) * Complex.exp ((θ3 : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hs.ne') (Complex.exp_ne_zero _)
    refine ⟨hne, by rw [s83sg_ray_norm s θ3 hs]; exact hsρ, ?_⟩
    rw [s83sg_ray_rot]
    have h1 : θ3 - (c + Real.pi) ∈ Set.Ioo (-(Real.pi - κ)) (Real.pi - κ) :=
      ⟨by rw [hc, hκ]; linarith, by rw [hc, hκ]; linarith⟩
    rw [s83sg_arg_polar s _ hs ⟨by linarith [h1.1], by linarith [h1.2]⟩]
    exact abs_lt.2 h1




/-- **[d2, the crossing upstairs]**  The disc chart `e` at the centre pulls back, through the sheet of `p₀` at `τ₀`,
to the local two-sidedness `hcross` of `a` at `a 0` (the two rays of `α` cut a small disc into two open sectors; the
germs of `b` lie in the two sectors). -/
theorem s83sg_lift_cross {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀]
    [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {α β : ℝ → S₀} {a b : ℝ → UpperHalfPlane}
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ₀) (ha : Continuous a) (hb : Continuous b)
    (haα : ∀ t, p₀ (a t) = α t) (hbβ : ∀ t, p₀ (b t) = β t) (haγ : ∀ t, a (t + 1) = γ • a t)
    (h0 : a 0 = b 0) (hpa : ∀ n : ℤ, n ≠ 0 → γ ^ n ≠ 1 ∧ γ ^ n ≠ -1)
    (e : OpenPartialHomeomorph S₀ ℂ) (ε θ₀ θ₁ θ₂ θ₃ : ℝ) (hα0 : α 0 ∈ e.source) (he0 : e (α 0) = 0)
    (het : e.target = Metric.ball 0 1) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (h01 : θ₀ < θ₁) (h12 : θ₁ < θ₂) (h23 : θ₂ < θ₃) (h3 : θ₃ < θ₀ + 2 * Real.pi)
    (hαe : ∀ t : ℝ, α t ∈ e.source ↔ ∃ n : ℤ, |t - n| < ε)
    (hαp : ∀ t, 0 < t → t < ε → e (α t) = ((t / ε : ℝ) : ℂ) * Complex.exp (θ₀ * Complex.I))
    (hαm : ∀ t, -ε < t → t < 0 → e (α t) = ((-t / ε : ℝ) : ℂ) * Complex.exp (θ₂ * Complex.I))
    (hβp : ∀ t, 0 < t → t < ε → e (β t) = ((t / ε : ℝ) : ℂ) * Complex.exp (θ₁ * Complex.I))
    (hβm : ∀ t, -ε < t → t < 0 → e (β t) = ((-t / ε : ℝ) : ℂ) * Complex.exp (θ₃ * Complex.I)) :
    ∃ N Wp Wm : Set UpperHalfPlane, IsOpen N ∧ a 0 ∈ N ∧ IsOpen Wp ∧ IsOpen Wm ∧
      IsConnected Wp ∧ IsConnected Wm ∧ Disjoint Wp Wm ∧ N \ range a = Wp ∪ Wm ∧
      (∃ ε > 0, ∀ s, 0 < s → s < ε → b s ∈ Wp) ∧ (∃ ε > 0, ∀ s, -ε < s → s < 0 → b s ∈ Wm) := by
  -- the freeness hypothesis `hpa` is not needed here: injectivity of the chart does all the work
  -- likewise `het` (the chart target) and `hε2` (`ε < 1/2`) are not needed; the statement stays true without them
  have _hpa := hpa
  have _het := het
  have _hε2 := hε2
  obtain ⟨hcov, -, -, hfib⟩ := hp₀
  -- periodicity of `α`
  have hαper : ∀ t, α (t + 1) = α t := by
    intro t
    rw [← haα, ← haα, haγ]
    exact ((hfib _ _).2 ⟨γ, hγ, rfl⟩).symm
  have hαz : ∀ (t : ℝ) (n : ℤ), α (t + n) = α t := by
    intro t n
    have hp : Function.Periodic α 1 := hαper
    have := (hp.int_mul n) t
    simpa using this
  -- the chart `E = e ∘ p₀` near `a 0`
  obtain ⟨q, hxq, hpq⟩ := hcov.isLocalHomeomorph (a 0)
  let E : OpenPartialHomeomorph UpperHalfPlane ℂ := q.trans e
  have hEx : ∀ x, E x = e (p₀ x) := fun x => by rw [hpq]; rfl
  have hEsrc : ∀ x, x ∈ E.source ↔ x ∈ q.source ∧ q x ∈ e.source := fun x => by
    show x ∈ (q.trans e).source ↔ _
    rw [OpenPartialHomeomorph.trans_source]
    rfl
  have hx0 : a 0 ∈ E.source := by
    rw [hEsrc]
    refine ⟨hxq, ?_⟩
    rw [← hpq]
    rw [haα]
    exact hα0
  have hE0 : E (a 0) = 0 := by rw [hEx, haα, he0]
  have hEsrc_e : ∀ x ∈ E.source, p₀ x ∈ e.source := by
    intro x hx
    have := ((hEsrc x).1 hx).2
    rwa [← hpq] at this
  have hEt : E (a 0) ∈ E.target := E.map_source hx0
  obtain ⟨ρ0, hρ0, hρ0t⟩ : ∃ ρ0 > 0, Metric.ball (0 : ℂ) ρ0 ⊆ E.target := by
    have : E.target ∈ 𝓝 (0 : ℂ) := E.open_target.mem_nhds (by rwa [hE0] at hEt)
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 this
    exact ⟨r, hr, hsub⟩
  have hb0 : b 0 ∈ E.source := h0 ▸ hx0
  obtain ⟨ε1, hε1, hε1a, hε1b⟩ : ∃ ε1 > 0, (∀ t : ℝ, |t| < ε1 → a t ∈ E.source) ∧
      (∀ t : ℝ, |t| < ε1 → b t ∈ E.source) := by
    have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), a t ∈ E.source :=
      ha.continuousAt.preimage_mem_nhds (E.open_source.mem_nhds hx0)
    have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), b t ∈ E.source :=
      hb.continuousAt.preimage_mem_nhds (E.open_source.mem_nhds hb0)
    obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.1 (h1.and h2)
    refine ⟨r, hr, fun t ht => (h (by simpa [Real.dist_eq] using ht)).1,
      fun t ht => (h (by simpa [Real.dist_eq] using ht)).2⟩
  obtain ⟨ρ, hρ, hρρ0, hρ1, hρε⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ0 ∧ ρ ≤ 1 ∧ ε * ρ ≤ ε1 := by
    refine ⟨min ρ0 (min 1 (ε1 / ε)), lt_min hρ0 (lt_min one_pos (div_pos hε1 hε)), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), ?_⟩
    have : min ρ0 (min 1 (ε1 / ε)) ≤ ε1 / ε := (min_le_right _ _).trans (min_le_right _ _)
    calc ε * min ρ0 (min 1 (ε1 / ε)) ≤ ε * (ε1 / ε) := mul_le_mul_of_nonneg_left this hε.le
      _ = ε1 := by field_simp
  have hball_t : Metric.ball (0 : ℂ) ρ ⊆ E.target := fun z hz =>
    hρ0t (Metric.ball_subset_ball hρρ0 hz)
  have hEsymm : ∀ z ∈ E.target, E (E.symm z) = z := fun z hz => E.right_inv hz
  have hsymm_src : ∀ z ∈ E.target, E.symm z ∈ E.source := fun z hz => E.map_target hz
  have hasymm0 : E.symm 0 = a 0 := by
    have := E.left_inv hx0
    rwa [hE0] at this
  -- the rays lie on the line `a`
  have hray_a : ∀ z : ℂ,
      ((∃ s : ℝ, 0 ≤ s ∧ s < ρ ∧ z = (s : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)) ∨
        (∃ s : ℝ, 0 ≤ s ∧ s < ρ ∧ z = (s : ℂ) * Complex.exp ((θ₂ : ℂ) * Complex.I))) →
      E.symm z ∈ range a := by
    rintro z (⟨s, hs0, hsρ, rfl⟩ | ⟨s, hs0, hsρ, rfl⟩)
    · rcases hs0.lt_or_eq with hs | hs
      · have ht : |ε * s| < ε1 := by
          rw [abs_of_pos (mul_pos hε hs)]
          calc ε * s < ε * ρ := mul_lt_mul_of_pos_left hsρ hε
            _ ≤ ε1 := hρε
        have htε : ε * s < ε := by nlinarith [hρ1, hsρ, hε]
        have hax := hε1a _ ht
        have hE : E (a (ε * s)) = (s : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I) := by
          rw [hEx, haα, hαp _ (mul_pos hε hs) htε]
          congr 2
          field_simp
        refine ⟨ε * s, ?_⟩
        rw [← E.left_inv hax, hE]
      · refine ⟨0, ?_⟩
        rw [← hasymm0, ← hs]
        simp
    · rcases hs0.lt_or_eq with hs | hs
      · have ht : |-(ε * s)| < ε1 := by
          rw [abs_neg, abs_of_pos (mul_pos hε hs)]
          calc ε * s < ε * ρ := mul_lt_mul_of_pos_left hsρ hε
            _ ≤ ε1 := hρε
        have htε : ε * s < ε := by nlinarith [hρ1, hsρ, hε]
        have hax := hε1a _ ht
        have hE : E (a (-(ε * s))) = (s : ℂ) * Complex.exp ((θ₂ : ℂ) * Complex.I) := by
          rw [hEx, haα, hαm _ (by linarith) (by linarith [mul_pos hε hs])]
          congr 2
          field_simp
        refine ⟨-(ε * s), ?_⟩
        rw [← E.left_inv hax, hE]
      · refine ⟨0, ?_⟩
        rw [← hasymm0, ← hs]
        simp
  obtain ⟨Sp, Sm, hSpo, hSmo, hSpc, hSmc, hSdisj, hSeq, hgermp, hgermm⟩ :=
    s83sg_sector_split θ₀ θ₁ θ₂ θ₃ ρ h01 h12 h23 h3 hρ
  have hSp_sub : Sp ⊆ E.target := by
    intro z hz
    have h : z ∈ Sp ∪ Sm := Or.inl hz
    rw [← hSeq] at h
    exact hball_t h.1
  have hSm_sub : Sm ⊆ E.target := by
    intro z hz
    have h : z ∈ Sp ∪ Sm := Or.inr hz
    rw [← hSeq] at h
    exact hball_t h.1
  have hNeq : E.symm '' Metric.ball (0 : ℂ) ρ \ range a = E.symm '' (Sp ∪ Sm) := by
    rw [← hSeq]
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hxa⟩
      refine ⟨z, ⟨hz, fun hR => hxa (hray_a z hR)⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzR⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rintro ⟨t, ht⟩
      have hzt : z ∈ E.target := hball_t hz
      have hxs : a t ∈ E.source := ht ▸ hsymm_src z hzt
      have hEz : E (a t) = z := by rw [ht]; exact hEsymm z hzt
      rw [hEx, haα] at hEz
      have hαt : α t ∈ e.source := haα t ▸ hEsrc_e _ hxs
      obtain ⟨n, hn⟩ := (hαe t).1 hαt
      have hαu : α (t - n) = α t := by
        have := hαz (t - n) n
        rw [sub_add_cancel] at this
        exact this.symm
      rw [← hαu] at hEz
      have hzn : ‖z‖ < ρ := by simpa using hz
      rcases lt_trichotomy (t - n) 0 with hu | hu | hu
      · have hz2 := hαm (t - n) (by rw [abs_lt] at hn; linarith [hn.1]) hu
        rw [hz2] at hEz
        have hpos : 0 < -(t - n) / ε := div_pos (by linarith) hε
        apply hzR
        refine Or.inr ⟨-(t - n) / ε, hpos.le, ?_, hEz.symm⟩
        rw [← hEz, s83sg_ray_norm _ _ hpos] at hzn
        exact hzn
      · rw [hu, hα0 |> fun _ => (rfl : α 0 = α 0)] at hEz
        rw [he0] at hEz
        apply hzR
        refine Or.inl ⟨0, le_rfl, hρ, ?_⟩
        rw [← hEz]
        simp
      · have hz2 := hαp (t - n) hu (by rw [abs_lt] at hn; linarith [hn.2])
        rw [hz2] at hEz
        have hpos : 0 < (t - n) / ε := div_pos hu hε
        apply hzR
        refine Or.inl ⟨(t - n) / ε, hpos.le, ?_, hEz.symm⟩
        rw [← hEz, s83sg_ray_norm _ _ hpos] at hzn
        exact hzn
  have hsrc_symm : E.symm.source = E.target := rfl
  refine ⟨E.symm '' Metric.ball 0 ρ, E.symm '' Sp, E.symm '' Sm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact E.symm.isOpen_image_of_subset_source Metric.isOpen_ball hball_t
  · exact ⟨0, Metric.mem_ball_self hρ, hasymm0⟩
  · exact E.symm.isOpen_image_of_subset_source hSpo hSp_sub
  · exact E.symm.isOpen_image_of_subset_source hSmo hSm_sub
  · exact hSpc.image _ (E.continuousOn_symm.mono hSp_sub)
  · exact hSmc.image _ (E.continuousOn_symm.mono hSm_sub)
  · rw [Set.disjoint_left]
    rintro x ⟨z1, hz1, rfl⟩ ⟨z2, hz2, h12'⟩
    have := congrArg E h12'
    rw [hEsymm z1 (hSp_sub hz1), hEsymm z2 (hSm_sub hz2)] at this
    exact Set.disjoint_left.1 hSdisj hz1 (this ▸ hz2)
  · rw [hNeq, Set.image_union]
  · refine ⟨ε * ρ, mul_pos hε hρ, fun s hs hsδ => ?_⟩
    have hsε : s < ε := lt_of_lt_of_le hsδ (by nlinarith)
    have hs1 : |s| < ε1 := by
      rw [abs_of_pos hs]; exact lt_of_lt_of_le hsδ hρε
    have hbx := hε1b s hs1
    have hE : E (b s) = ((s / ε : ℝ) : ℂ) * Complex.exp ((θ₁ : ℂ) * Complex.I) := by
      rw [hEx, hbβ, hβp s hs hsε]
    have hpos : 0 < s / ε := div_pos hs hε
    have hlt : s / ε < ρ := by rw [div_lt_iff₀ hε]; linarith
    refine ⟨_, hgermp _ hpos hlt, ?_⟩
    rw [← hE, E.left_inv hbx]
  · refine ⟨ε * ρ, mul_pos hε hρ, fun s hs hsδ => ?_⟩
    have hsε : -ε < s := by nlinarith
    have hs1 : |s| < ε1 := by
      rw [abs_of_neg hsδ]; linarith
    have hbx := hε1b s hs1
    have hE : E (b s) = ((-s / ε : ℝ) : ℂ) * Complex.exp ((θ₃ : ℂ) * Complex.I) := by
      rw [hEx, hbβ, hβm s hsε hsδ]
    have hpos : 0 < -s / ε := div_pos (by linarith) hε
    have hlt : -s / ε < ρ := by rw [div_lt_iff₀ hε]; linarith
    refine ⟨_, hgermm _ hpos hlt, ?_⟩
    rw [← hE, E.left_inv hbx]


end LiZhongQC
