import LiZhongQC.Lemmas.FiniteTypeTeichData
import LiZhongQC.Lemmas.FiniteTypeTeichBasic
import LiZhongQC.Lemmas.S32wThm323
import LiZhongQC.Lemmas.S32wThm324

/-!
# §32.3 The Teichmüller space of a surface of finite type: Teichmüller data and the unit ball

`markedFiniteType_teichmuller_data` and `teichSpaceFiniteType_ball` were moved here from
`LiZhongQC.Ch09.S32_FiniteTypeTeichmuller` (leader decision R82, 2026-10-16), statements and docstrings
byte-identical. Their proofs need the dimension formula (31.2) (`thm31_1_admissibleQD_finrank`,
`LiZhongQC.Lemmas.QDDimension`) and the closed-surface Teichmüller theory of `LiZhongQC.Lemmas.UniformizedTeichmuller`,
which import §31 but not §32.

Helpers (prefix `s82td_`): a homeomorphism carrying two Teichmüller structures has the same `k` and
proportional initial differentials (comparison of the Beltrami coefficients `k ζ̄_z/ζ_z` in natural
parameters); the identity theorem for holomorphic quadratic differentials on a connected surface; a
Teichmüller map with `k = 0` is biholomorphic.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- **[S8] Homotopic admissible Teichmüller maps have the same data.**  Two admissible Teichmüller maps `S₀ → S` in
one homotopy class are both extremal (Theorem 32.3), hence equal, so (`s82td_data_unique`) for `k₁ > 0` they have the
same `k` and proportional initial differentials. -/
theorem s82td_homotopic_data {g n m : ℕ} (hex : ¬ IsExceptionalType g n m) (F₀ : FiniteTypeStructure S₀ g n m)
    (F₁ : FiniteTypeStructure S g n m) {f₁ f₂ : S₀ ≃ₜ S} {q₁ q₂ : S₀ → ℂ → ℂ} {q₁' q₂' : S → ℂ → ℂ} {k₁ k₂ : ℝ}
    (h₁ : IsAdmissibleTeichmullerMap F₀ f₁ q₁ q₁' k₁) (h₂ : IsAdmissibleTeichmullerMap F₀ f₂ q₂ q₂' k₂)
    (hhom : ContinuousMap.Homotopic (f₁ : C(S₀, S)) (f₂ : C(S₀, S))) (hk : 0 < k₁) :
    k₂ = k₁ ∧ ∃ c : ℝ, 0 < c ∧ q₂ = (c : ℂ) • q₁ := by
  have h1 := s32w_thm32_3_uniqueness_gnm hex F₀ F₁ h₁ h₂.2.qc hhom
  have h2 := s32w_thm32_3_uniqueness_gnm hex F₀ F₁ h₂ h₁.2.qc hhom.symm
  have hfun : ⇑f₁ = ⇑f₂ := h2.2 (le_antisymm h1.1 h2.1)
  have hf : f₂ = f₁ := Homeomorph.ext fun x => (congrFun hfun x).symm
  subst hf
  exact s82td_data_unique h₁.2 h₂.2 hk

/-- **[S9] An admissible Teichmüller map with `k > 0` is not homotopic to a biholomorphism**: the biholomorphism has
`K = 1`, so by Theorem 32.3 it equals the Teichmüller map, which then has `k = 0`. -/
theorem s82td_not_homotopic_biholomorphic {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m) {f₀ h : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ}
    {q' : S → ℂ → ℂ} {k : ℝ} (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k) (hk : 0 < k) (hh : IsBiholomorphic h)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S)) (h : C(S₀, S))) : False := by
  have hh1 : IsKQCRS h 1 := (isKQCRS_one_iff h).2 hh
  have hK : maxDilatationRS h = 1 :=
    le_antisymm (by simpa using maxDilatationRS_le hh1) (s29_m_one_le_maxDilatationRS ⟨1, hh1⟩)
  have h1 := s32w_thm32_3_uniqueness_gnm hex F₀ F₁ hf₀ ⟨1, hh1⟩ hhom
  have hK0 : maxDilatationRS f₀ = 1 :=
    le_antisymm (hK ▸ h1.1) (s29_m_one_le_maxDilatationRS hf₀.2.qc)
  have hfun : ⇑h = ⇑f₀ := h1.2 (hK.trans hK0.symm)
  have hf : h = f₀ := Homeomorph.ext fun x => congrFun hfun x
  subst hf
  exact hk.ne' (s82td_biholomorphic_k_eq_zero hh hf₀.2)

/-- **[stub, FROZEN with 下属2] The deformation chart** (blueprint L32309–L32311): a real linear coordinate `e` on
`Q̃(S₀)` and a bijection `Φ` of the open unit ball onto `T_{g,n,m}` with `Φ 0` the base point and, for `v ≠ 0`, `Φ v`
the class of a marked surface reached by an admissible Teichmüller map with `k = ‖v‖` and direction `v/‖v‖ = e q/‖e q‖`. -/
theorem s82td_deformation_chart {g n m : ℕ} (hex : ¬ IsExceptionalType g n m) (F₀ : FiniteTypeStructure S₀ g n m) :
    ∃ (e : admissibleQDInterior F₀ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))))
      (Φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))) → TeichSpaceFiniteType S₀ g n m),
      InjOn Φ (ball 0 1) ∧
      (∀ p : TeichSpaceFiniteType S₀ g n m, ∃ v ∈ ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))) 1, Φ v = p) ∧
      Φ 0 = Quot.mk _ ⟨⟨S₀, F₀⟩, Homeomorph.refl S₀, isQCRS_refl⟩ ∧
      ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))) 1, v ≠ 0 →
        ∃ (A : MarkedFiniteTypeRS S₀ g n m) (f : S₀ ≃ₜ A.X.carrier) (q : admissibleQDInterior F₀) (q' : A.X.carrier → ℂ → ℂ) (k : ℝ),
          Quot.mk _ A = Φ v ∧ ContinuousMap.Homotopic (A.marking : C(S₀, A.X.carrier)) (f : C(S₀, A.X.carrier)) ∧
          IsAdmissibleTeichmullerMap F₀ f q.1 q' k ∧ 0 < k ∧ k < 1 ∧ ‖v‖ = k ∧ v = (k / ‖e q‖) • e q := by
  classical
  haveI := s82td_finiteDimensional hex F₀
  let e : admissibleQDInterior F₀ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [finrank_euclideanSpace_fin])
  have hdir : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))), v ≠ 0 →
      ‖e (e.symm (‖v‖⁻¹ • v))‖ = 1 := by
    intro v hv
    rw [LinearEquiv.apply_symm_apply, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
  have hR : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))),
      ∃ A : MarkedFiniteTypeRS S₀ g n m,
        v ∈ ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))) 1 → v ≠ 0 →
          ∃ q' : A.X.carrier → ℂ → ℂ, IsAdmissibleTeichmullerMap F₀ A.marking (e.symm (‖v‖⁻¹ • v)).1 q' ‖v‖ := by
    intro v
    by_cases hv : v ∈ ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))) 1 ∧ v ≠ 0
    · have hq0 : (e.symm (‖v‖⁻¹ • v)).1 ≠ 0 := by
        intro h0
        have h1 : e.symm (‖v‖⁻¹ • v) = 0 := Subtype.ext h0
        have h2 := hdir v hv.2
        rw [h1, map_zero, norm_zero] at h2
        exact zero_ne_one h2
      obtain ⟨A, q', hA⟩ := s82td_realize hex F₀ (e.symm (‖v‖⁻¹ • v)).2 hq0 (norm_pos_iff.2 hv.2)
        (mem_ball_zero_iff.1 hv.1)
      exact ⟨A, fun _ _ => ⟨q', hA⟩⟩
    · exact ⟨⟨⟨S₀, F₀⟩, Homeomorph.refl S₀, isQCRS_refl⟩, fun h1 h2 => absurd ⟨h1, h2⟩ hv⟩
  choose Af hAf using hR
  let o : TeichSpaceFiniteType S₀ g n m := Quot.mk _ ⟨⟨S₀, F₀⟩, Homeomorph.refl S₀, isQCRS_refl⟩
  let Φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))) → TeichSpaceFiniteType S₀ g n m :=
    fun v => if v = 0 then o else Quot.mk _ (Af v)
  have hΦ0 : Φ 0 = o := if_pos rfl
  have hΦv : ∀ v, v ≠ 0 → Φ v = Quot.mk _ (Af v) := fun v hv => if_neg hv
  have hcoe : ∀ {Y : FiniteTypeRS.{u} g n m} (c : S₀ ≃ₜ Y.carrier),
      (((Homeomorph.refl S₀).trans c : S₀ ≃ₜ Y.carrier) : C(S₀, Y.carrier)) = (c : C(S₀, Y.carrier)) := by
    intro Y c
    ext x
    rfl
  -- a non-zero parameter is not the base point
  have hne0 : ∀ w ∈ ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))) 1, w ≠ 0 →
      o ≠ Quot.mk _ (Af w) := by
    intro w hw hw0 hvw
    obtain ⟨q', hA⟩ := hAf w hw hw0
    obtain ⟨c, hc, hh⟩ := (ft_quotient_exact _ _).1 hvw
    have hh' : ContinuousMap.Homotopic (c : C(S₀, (Af w).X.carrier)) ((Af w).marking : C(S₀, (Af w).X.carrier)) := by
      have := hcoe (Y := (Af w).X) c
      rw [← this]
      exact hh
    exact s82td_not_homotopic_biholomorphic hex F₀ (Af w).X.structure' hA (norm_pos_iff.2 hw0) hc hh'.symm
  refine ⟨e, Φ, ?_, ?_, hΦ0, ?_⟩
  · -- injectivity on the ball
    intro v hv w hw hvw
    by_cases hv0 : v = 0
    · by_cases hw0 : w = 0
      · rw [hv0, hw0]
      · exfalso
        have h1 : o = Quot.mk _ (Af w) := by rw [← hΦ0, ← hv0, hvw, hΦv w hw0]
        exact hne0 w hw hw0 h1
    · by_cases hw0 : w = 0
      · exfalso
        have h1 : o = Quot.mk _ (Af v) := by rw [← hΦ0, ← hw0, ← hvw, hΦv v hv0]
        exact hne0 v hv hv0 h1
      · rw [hΦv v hv0, hΦv w hw0] at hvw
        obtain ⟨c, hc, hh⟩ := (ft_quotient_exact _ _).1 hvw
        obtain ⟨qv', hAv⟩ := hAf v hv hv0
        obtain ⟨qw', hAw⟩ := hAf w hw hw0
        obtain ⟨q'', hT''⟩ := utm_x_teichmullerMap_trans hAv.2 hc
        obtain ⟨hkk, cc, hcc, hqq⟩ := s82td_homotopic_data hex F₀ (Af w).X.structure' ⟨hAv.1, hT''⟩ hAw hh
          (norm_pos_iff.2 hv0)
        have hsub : e.symm (‖w‖⁻¹ • w) = cc • e.symm (‖v‖⁻¹ • v) := by
          apply Subtype.ext
          rw [hqq]
          funext x z
          simp [Complex.real_smul]
        have h1 : ‖w‖⁻¹ • w = cc • (‖v‖⁻¹ • v) := by
          have := congrArg e hsub
          rwa [LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.apply_symm_apply] at this
        have n1 := hdir w hw0
        have n2 := hdir v hv0
        rw [LinearEquiv.apply_symm_apply] at n1 n2
        have hcc1 : cc = 1 := by
          have := congrArg norm h1
          rw [n1, norm_smul, n2, mul_one, Real.norm_eq_abs, abs_of_pos hcc] at this
          exact this.symm
        rw [hcc1, one_smul, hkk] at h1
        have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
        calc v = ‖v‖ • (‖v‖⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ hvn, one_smul]
          _ = ‖v‖ • (‖v‖⁻¹ • w) := by rw [h1]
          _ = w := by rw [smul_smul, mul_inv_cancel₀ hvn, one_smul]
  · -- every point is reached
    intro p
    obtain ⟨A, rfl⟩ := Quot.exists_rep p
    obtain ⟨f₀, hhom, hcase⟩ := s32w_thm32_4 hex F₀ A.X.structure' A.marking A.qc
    have hcase' : IsBiholomorphic f₀ ∨ ∃ (q : S₀ → ℂ → ℂ) (q' : A.X.carrier → ℂ → ℂ) (k : ℝ),
        IsAdmissibleTeichmullerMap F₀ f₀ q q' k ∧ 0 < k := by
      rcases hcase with hb | ⟨q, q', k, hT⟩
      · exact Or.inl hb
      · rcases eq_or_lt_of_le hT.2.k_nonneg with hk0 | hkpos
        · subst hk0
          exact Or.inl (s82td_k0_biholomorphic hT.2)
        · exact Or.inr ⟨q, q', k, hT, hkpos⟩
    rcases hcase' with hb | ⟨q, q', k, hT, hkpos⟩
    · refine ⟨0, mem_ball_self one_pos, ?_⟩
      rw [hΦ0]
      apply Quot.sound
      refine ⟨f₀, hb, ?_⟩
      have := hcoe (Y := A.X) f₀
      rw [this]
      exact hhom.symm
    · set u := e ⟨q, hT.1⟩ with hu_def
      have hu : u ≠ 0 := by
        intro h0
        apply hT.2.initial_ne
        have h1 : (⟨q, hT.1⟩ : admissibleQDInterior F₀) = 0 := e.injective (h0.trans (map_zero e).symm)
        exact congrArg Subtype.val h1
      have hun : 0 < ‖u‖ := norm_pos_iff.2 hu
      set v := (k / ‖u‖) • u with hv_def
      have hvn : ‖v‖ = k := by
        rw [hv_def, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hkpos, abs_norm, div_mul_cancel₀ _ hun.ne']
      have hv0 : v ≠ 0 := by
        intro h
        rw [h, norm_zero] at hvn
        exact hkpos.ne hvn
      have hvb : v ∈ ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))) 1 := by
        rw [mem_ball_zero_iff, hvn]
        exact hT.2.k_lt_one
      refine ⟨v, hvb, ?_⟩
      rw [hΦv v hv0]
      obtain ⟨q₂', hA⟩ := hAf v hvb hv0
      have hdirv : e.symm (‖v‖⁻¹ • v) = ‖u‖⁻¹ • (⟨q, hT.1⟩ : admissibleQDInterior F₀) := by
        apply e.injective
        rw [LinearEquiv.apply_symm_apply, map_smul, ← hu_def, hvn, hv_def, smul_smul]
        congr 1
        field_simp
      rw [hdirv, hvn] at hA
      have hT2 := s29_e12_teichMap_smul hA.2 hun
      have hq_eq : ((‖u‖ : ℝ) : ℂ) • (‖u‖⁻¹ • (⟨q, hT.1⟩ : admissibleQDInterior F₀)).1 = q := by
        funext x z
        have hun0 : ((‖u‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hun.ne'
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
        push_cast
        field_simp
      rw [hq_eq] at hT2
      have hc := s82td_same_data_biholomorphic hT2 hT.2
      apply Quot.sound
      refine ⟨(Af v).marking.symm.trans f₀, hc, ?_⟩
      have h3 : (((Af v).marking.trans ((Af v).marking.symm.trans f₀) : S₀ ≃ₜ A.X.carrier) : C(S₀, A.X.carrier)) =
          (f₀ : C(S₀, A.X.carrier)) := by
        ext x
        simp
      rw [h3]
      exact hhom.symm
  · -- the Teichmüller data of `Φ v`
    intro v hv hv0
    obtain ⟨q', hA⟩ := hAf v hv hv0
    refine ⟨Af v, (Af v).marking, e.symm (‖v‖⁻¹ • v), q', ‖v‖, (hΦv v hv0).symm, ContinuousMap.Homotopic.refl _,
      hA, norm_pos_iff.2 hv0, mem_ball_zero_iff.1 hv, rfl, ?_⟩
    rw [hdir v hv0, LinearEquiv.apply_symm_apply, div_one, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hv0),
      one_smul]

/-! ## Moved book theorems -/

/-- §32.3: every marked surface `(S, f)` corresponds to a Teichmüller map `f₀ : S₀ → S` in the class
of `f` with admissible differential `ω`, unique up to a positive factor, and to `k ∈ [0, 1)`;
equivalent marked surfaces give the same `(ω, k)` (the Beltrami differential is unchanged by
composition with a conformal map). -/
theorem s82td_markedFiniteType_teichmuller_data {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (m₁ : MarkedFiniteTypeRS S₀ g n m) :
    ∃ (f₀ : S₀ ≃ₜ m₁.X.carrier) (k : ℝ), 0 ≤ k ∧ k < 1 ∧
      ContinuousMap.Homotopic (m₁.marking : C(S₀, m₁.X.carrier)) (f₀ : C(S₀, m₁.X.carrier)) ∧
      ((k = 0 ∧ IsBiholomorphic f₀) ∨ (0 < k ∧ ∃ (q : S₀ → ℂ → ℂ) (q' : m₁.X.carrier → ℂ → ℂ),
        IsAdmissibleTeichmullerMap F₀ f₀ q q' k ∧
        ∀ (q₂ : S₀ → ℂ → ℂ) (q₂' : m₁.X.carrier → ℂ → ℂ) (k₂ : ℝ) (f₂ : S₀ ≃ₜ m₁.X.carrier),
          IsAdmissibleTeichmullerMap F₀ f₂ q₂ q₂' k₂ →
          ContinuousMap.Homotopic (m₁.marking : C(S₀, m₁.X.carrier)) (f₂ : C(S₀, m₁.X.carrier)) →
          k₂ = k ∧ ∃ c : ℝ, 0 < c ∧ q₂ = (c : ℂ) • q)) := by
  obtain ⟨f₀, hhom, hcase⟩ := s32w_thm32_4 hex F₀ m₁.X.structure' m₁.marking m₁.qc
  rcases hcase with hb | ⟨q, q', k, hT⟩
  · exact ⟨f₀, 0, le_rfl, one_pos, hhom, Or.inl ⟨rfl, hb⟩⟩
  · rcases eq_or_lt_of_le hT.2.k_nonneg with hk0 | hkpos
    · subst hk0
      exact ⟨f₀, 0, le_rfl, one_pos, hhom, Or.inl ⟨rfl, s82td_k0_biholomorphic hT.2⟩⟩
    · refine ⟨f₀, k, hT.2.k_nonneg, hT.2.k_lt_one, hhom, Or.inr ⟨hkpos, q, q', hT, ?_⟩⟩
      intro q₂ q₂' k₂ f₂ hT₂ hhom₂
      have h02 : ContinuousMap.Homotopic (f₀ : C(S₀, m₁.X.carrier)) (f₂ : C(S₀, m₁.X.carrier)) :=
        hhom.symm.trans hhom₂
      -- both maps are extremal in the class (Theorem 32.3), so they coincide
      have h1 := s32w_thm32_3_uniqueness_gnm hex F₀ m₁.X.structure' hT hT₂.2.qc h02
      have h2 := s32w_thm32_3_uniqueness_gnm hex F₀ m₁.X.structure' hT₂ hT.2.qc h02.symm
      have hfun : ⇑f₀ = ⇑f₂ := h2.2 (le_antisymm h1.1 h2.1)
      have hf : f₂ = f₀ := Homeomorph.ext fun x => (congrFun hfun x).symm
      subst hf
      exact s82td_data_unique hT.2 hT₂.2 hkpos

/-- **§32.3**: `T_{g,n,m}` is in bijection with the open unit ball of `ℝ^{6g-6+2n+3m}`, via the
Teichmüller data `(k, ω)`, `ω` normalized on the unit sphere of `Q̃(S₀)` (in a basis). -/
theorem s82td_teichSpaceFiniteType_ball {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) :
    (Module.finrank ℝ (admissibleQDInterior F₀) : ℤ) = 6 * g - 6 + 2 * n + 3 * m ∧
      ∃ Φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))) → TeichSpaceFiniteType S₀ g n m,
        InjOn Φ (ball 0 1) ∧ ∀ p, ∃ v ∈ ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))) 1, Φ v = p := by
  obtain ⟨-, Φ, hinj, hsurj, -, -⟩ := s82td_deformation_chart hex F₀
  exact ⟨s82td_finrank_interior hex F₀, Φ, hinj, hsurj⟩

section RelocatedS32

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- §32.3: every marked surface `(S, f)` corresponds to a Teichmüller map `f₀ : S₀ → S` in the class
of `f` with admissible differential `ω`, unique up to a positive factor, and to `k ∈ [0, 1)`;
equivalent marked surfaces give the same `(ω, k)` (the Beltrami differential is unchanged by
composition with a conformal map). -/
theorem markedFiniteType_teichmuller_data {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (m₁ : MarkedFiniteTypeRS S₀ g n m) :
    ∃ (f₀ : S₀ ≃ₜ m₁.X.carrier) (k : ℝ), 0 ≤ k ∧ k < 1 ∧
      ContinuousMap.Homotopic (m₁.marking : C(S₀, m₁.X.carrier)) (f₀ : C(S₀, m₁.X.carrier)) ∧
      ((k = 0 ∧ IsBiholomorphic f₀) ∨ (0 < k ∧ ∃ (q : S₀ → ℂ → ℂ) (q' : m₁.X.carrier → ℂ → ℂ),
        IsAdmissibleTeichmullerMap F₀ f₀ q q' k ∧
        ∀ (q₂ : S₀ → ℂ → ℂ) (q₂' : m₁.X.carrier → ℂ → ℂ) (k₂ : ℝ) (f₂ : S₀ ≃ₜ m₁.X.carrier),
          IsAdmissibleTeichmullerMap F₀ f₂ q₂ q₂' k₂ →
          ContinuousMap.Homotopic (m₁.marking : C(S₀, m₁.X.carrier)) (f₂ : C(S₀, m₁.X.carrier)) →
          k₂ = k ∧ ∃ c : ℝ, 0 < c ∧ q₂ = (c : ℂ) • q)) := by
  exact s82td_markedFiniteType_teichmuller_data hex F₀ m₁

/-- **§32.3**: `T_{g,n,m}` is in bijection with the open unit ball of `ℝ^{6g-6+2n+3m}`, via the
Teichmüller data `(k, ω)`, `ω` normalized on the unit sphere of `Q̃(S₀)` (in a basis). -/
theorem teichSpaceFiniteType_ball {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) :
    (Module.finrank ℝ (admissibleQDInterior F₀) : ℤ) = 6 * g - 6 + 2 * n + 3 * m ∧
      ∃ Φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))) → TeichSpaceFiniteType S₀ g n m,
        InjOn Φ (ball 0 1) ∧ ∀ p, ∃ v ∈ ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))) 1, Φ v = p := by
  exact s82td_teichSpaceFiniteType_ball hex F₀

end RelocatedS32

end LiZhongQC
