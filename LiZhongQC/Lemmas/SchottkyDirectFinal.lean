import LiZhongQC.Lemmas.UniformizedTeichmuller
import LiZhongQC.Lemmas.FiniteTypeTeichData
import LiZhongQC.Lemmas.S32wDTTeich
import LiZhongQC.Lemmas.SchottkyDirectD2
import LiZhongQC.Lemmas.SchottkyDirectD3a

/-!
# thm32_2 direct route: final assembly (R82, `SchottkyDirectFinal`)

`s82dx_thm32_2_existence_gn` is Theorem 32.2 (`thm32_2_existence_gn`, S32:559) with its statement unchanged,
proved by the direct Hamilton route on the torsion-free uniformization of the punctured base (no covers):
D2 (Dirichlet domain, `SchottkyDirectD2`), D3a (`SchottkyDirectD3a`), D3 `s82dx_hfin`, D4 `s82dx_teich`,
D5 `s82dx_descend`, D6 the assembly.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

noncomputable section
namespace LiZhongQC

universe u

/-- **[D3, stub] `hfin` of `thm36_2_finite_type` for a finite-type surface** (from D3a, `utm_x_descent`
and `s82td_finiteDimensional`). -/
theorem s82dx_hfin {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀]
    [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g n : ℕ} (hex : ¬ IsExceptionalType g n 0)
    (F₀ : FiniteTypeStructure S₀ g n 0)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (hΓ : IsFuchsian Γ₀) {F : Set ℂ} (hF : IsFundamentalDomainH Γ₀ F) :
    Module.Finite ℂ (Submodule.span ℂ ((fun φ => upperHalf.indicator φ) '' integrableAutomorphicQD Γ₀ F)) := by
  classical
  have : FiniteDimensional ℝ (admissibleQDInterior F₀) := s82td_finiteDimensional hex F₀
  set b := Module.finBasis ℝ (admissibleQDInterior F₀) with hb
  set v : Fin (Module.finrank ℝ (admissibleQDInterior F₀)) → (ℂ → ℂ) :=
    fun i => upperHalf.indicator (utm_liftQD ((b i : admissibleQDInterior F₀) : S₀ → ℂ → ℂ) p₀) with hv
  -- the lift is real linear
  have hzero : ∀ z, utm_liftQD (0 : S₀ → ℂ → ℂ) p₀ z = 0 := fun z => by
    rw [show (0 : S₀ → ℂ → ℂ) = (0 : ℂ) • (0 : S₀ → ℂ → ℂ) by simp, utm_x_liftQD_smul, zero_mul]
  have hsum : ∀ (s : Finset (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))) (c : _ → ℝ) (z : ℂ),
      utm_liftQD (∑ i ∈ s, c i • ((b i : admissibleQDInterior F₀) : S₀ → ℂ → ℂ)) p₀ z =
        ∑ i ∈ s, (c i : ℂ) * utm_liftQD ((b i : admissibleQDInterior F₀) : S₀ → ℂ → ℂ) p₀ z := by
    intro s c z
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact hzero z
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, utm_x_liftQD_add, ih]
      have e : c i • ((b i : admissibleQDInterior F₀) : S₀ → ℂ → ℂ) =
          (c i : ℂ) • ((b i : admissibleQDInterior F₀) : S₀ → ℂ → ℂ) := by
        funext x w
        simp [Complex.real_smul]
      rw [e, utm_x_liftQD_smul]
  have hle : Submodule.span ℂ ((fun φ => upperHalf.indicator φ) '' integrableAutomorphicQD Γ₀ F) ≤
      Submodule.span ℂ (range v) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨q, hq, hqφ⟩ := utm_x_descent hp₀ hφ.1 hφ.2.2
    have hqA := s82dx_integrable_admissible F₀ hp₀ hΓ hF hφ hq hqφ
    have hqsum : q = ∑ i, (b.repr ⟨q, hqA⟩ i) • ((b i : admissibleQDInterior F₀) : S₀ → ℂ → ℂ) := by
      have h : ((∑ i, b.repr ⟨q, hqA⟩ i • b i : admissibleQDInterior F₀) : S₀ → ℂ → ℂ) = q := by
        rw [b.sum_repr]
      push_cast at h
      exact h.symm
    have hind : upperHalf.indicator φ = ∑ i, ((b.repr ⟨q, hqA⟩ i : ℝ) : ℂ) • v i := by
      funext z
      rw [Finset.sum_apply]
      by_cases hz : z ∈ upperHalf
      · rw [indicator_of_mem hz, ← hqφ z hz]
        conv_lhs => rw [hqsum]
        rw [hsum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, hv, indicator_of_mem hz]
      · rw [indicator_of_notMem hz]
        symm
        refine Finset.sum_eq_zero fun i _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, hv, indicator_of_notMem hz, mul_zero]
    show upperHalf.indicator φ ∈ Submodule.span ℂ (range v)
    rw [hind]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have : FiniteDimensional ℂ (Submodule.span ℂ (range v)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  exact Submodule.finiteDimensional_of_le hle

/-- **Equal boundary values give the same conjugated group element** (the `(⇐)` half of `chi_eq_iff`, which needs no
density of fixed points): if `f^{μ₁} = f^{μ₂}` on `ℝ`, then for `γ ∈ Γ` one Möbius map `A` satisfies
`f^{μᵢ} ∘ γ = A ∘ f^{μᵢ}` on `ℍ` for both `i` (the two candidates of `b33_d_def` agree at three real points). -/
theorem s82dx_chi_eq {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {μ₁ μ₂ : BeltramiGamma Γ}
    (hR : teichSetoidGamma Γ μ₁ μ₂) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀ z ∈ upperHalf, fMuSym μ₁.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (fMuSym μ₁.1.1 z)) ∧
      (∀ z ∈ upperHalf, fMuSym μ₂.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (fMuSym μ₂.1.1 z)) := by
  obtain ⟨e₁, he₁, -, hsym₁, -, -⟩ := b33_d_sym_facts μ₁
  obtain ⟨e₂, he₂, -, -, -, -⟩ := b33_d_sym_facts μ₂
  obtain ⟨A₁, h₁⟩ := b33_d_def μ₁ hγ
  obtain ⟨A₂, h₂⟩ := b33_d_def μ₂ hγ
  have hR' : ∀ x : ℝ, e₁ x = e₂ x := fun x => by rw [he₁, he₂]; exact hR x
  rw [← he₁] at h₁
  rw [← he₂] at h₂
  have hreal₁ : ∀ t : ℝ, (e₁ t).im = 0 := fun t => by
    have h := hsym₁ t
    rw [Complex.conj_ofReal] at h
    exact Complex.conj_eq_iff_im.1 h.symm
  have key : ∀ k : ℝ, k ≠ 0 → ∃ u : ℝ, e₁ ((-(γ 1 1 / γ 1 0) + k : ℝ) : ℂ) = u ∧ A₁ 1 0 * u + A₁ 1 1 ≠ 0 ∧
      A₂ 1 0 * u + A₂ 1 1 ≠ 0 ∧
      mobiusFn (A₁ 0 0) (A₁ 0 1) (A₁ 1 0) (A₁ 1 1) (u : ℂ) = mobiusFn (A₂ 0 0) (A₂ 0 1) (A₂ 1 0) (A₂ 1 1) u := by
    intro k hk
    have hx := b33_d_nonpole γ hk
    set x : ℝ := -(γ 1 1 / γ 1 0) + k
    obtain ⟨u, hu⟩ : ∃ u : ℝ, e₁ x = u := ⟨_, (b33_d_ofReal_re (hreal₁ x)).symm⟩
    obtain ⟨hA₁, hE₁⟩ := b33_d_ext_real e₁.continuous e₁.injective h₁ hx
    obtain ⟨hA₂, hE₂⟩ := b33_d_ext_real e₂.continuous e₂.injective h₂ hx
    rw [← hR' x, hu] at hA₂ hE₂
    rw [hu] at hA₁ hE₁
    rw [b33_d_mobiusFn_ofReal, hR'] at hE₁
    rw [b33_d_mobiusFn_ofReal] at hE₂
    refine ⟨u, hu, by exact_mod_cast hA₁, by exact_mod_cast hA₂, hE₁.symm.trans hE₂⟩
  obtain ⟨u₁, hu₁, a₁, b₁, c₁⟩ := key 1 one_ne_zero
  obtain ⟨u₂, hu₂, a₂, b₂, c₂⟩ := key 2 two_ne_zero
  obtain ⟨u₃, hu₃, a₃, b₃, c₃⟩ := key 3 three_ne_zero
  have hne : ∀ {k l : ℝ} {u v : ℝ}, k ≠ l → e₁ ((-(γ 1 1 / γ 1 0) + k : ℝ) : ℂ) = u →
      e₁ ((-(γ 1 1 / γ 1 0) + l : ℝ) : ℂ) = v → u ≠ v := by
    intro k l u v hkl hu hv huv
    apply hkl
    have h1 := e₁.injective (hu.trans ((congrArg _ huv).trans hv.symm))
    have h2 := ofReal_injective h1
    linarith
  have hA : ∀ w ∈ upperHalf, mobiusFn (A₁ 0 0) (A₁ 0 1) (A₁ 1 0) (A₁ 1 1) w =
      mobiusFn (A₂ 0 0) (A₂ 0 1) (A₂ 1 0) (A₂ 1 1) w := by
    refine b33_d_eqOn_of_three (hne (by norm_num) hu₁ hu₂) (hne (by norm_num) hu₁ hu₃) (hne (by norm_num) hu₂ hu₃)
      ?_ ?_ ?_
    · intro t ht
      rcases ht with rfl | rfl | rfl <;> assumption
    · intro t ht
      rcases ht with rfl | rfl | rfl <;> assumption
    · intro t ht
      rcases ht with rfl | rfl | rfl <;> assumption
  refine ⟨A₁, fun z hz => ?_, fun z hz => ?_⟩
  · rw [← he₁]; exact h₁ z hz
  · rw [← he₂, h₂ z hz]
    exact (b33_d_mobiusFn_eq_of_eqOn hA _).symm

/-- **[D5, stub] Descent of an extremal representative.**  Let `f : S₀ → S` be quasiconformal between
surfaces uniformized by `ℍ/Γ₀`, `ℍ/Γ₁`, with lift `F`, and let `μ₀ ∈ M(Γ₀)` have the same boundary values as
the Beltrami coefficient `μ` of `F`.  Then `f^{μ₀}` (conjugated by the Möbius map `M` with `F = M f^{μ}`)
conjugates `Γ₀` onto `Γ₁` (a Möbius map is determined by its action on `ℝ̂`), so it descends to a
quasiconformal homeomorphism `f₀ : S₀ → S` with Beltrami lift `μ₀`, homotopic to `f` modulo the
boundary (`thm36_1`, geodesic homotopy: equal boundary values), in particular freely homotopic.

Note: `hΓ₀` is not used by this proof (the descent only uses the two uniformizations: free action and
fibres equal to orbits); it is kept so that the statement is unchanged. -/
theorem s82dx_descend {S₀ S : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀]
    [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    {p₁ : UpperHalfPlane → S} (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁)
    (hΓ₀ : IsFuchsian Γ₀) {f : S₀ ≃ₜ S} (hf : IsQCRS f) {F : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hF : IsLift p₀ p₁ f F) (μ μ₀ : BeltramiGamma Γ₀)
    (hμ : ∀ᵐ τ ∂(volume.restrict upperHalf), μ.1.1 τ = complexDilatation (liftToC F) τ)
    (h : teichSetoidGamma Γ₀ μ₀ μ) :
    ∃ f₀ : S₀ ≃ₜ S, IsQCRS f₀ ∧ ContinuousMap.Homotopic (f₀ : C(S₀, S)) (f : C(S₀, S)) ∧
      ∃ F₀ : UpperHalfPlane ≃ₜ UpperHalfPlane, IsLift p₀ p₁ f₀ F₀ ∧
        ∀ᵐ τ ∂(volume.restrict upperHalf), complexDilatation (liftToC F₀) τ = μ₀.1.1 τ := by
  classical
  -- `hΓ₀` is not needed: the descent only uses the uniformizations (free action, fibres = orbits)
  have _hΓ₀ := hΓ₀
  obtain ⟨K, hK⟩ := hf
  have hFq : IsKQC (liftToC F) upperHalf K := h23l_lift_isKQC hp₀ hp₁ hK hF
  -- the normalized solutions `f^μ`, `f^{μ₀}` and the induced homeomorphisms of `ℍ`
  obtain ⟨k, hk0, hk1, hμk⟩ := bg_beltramiH_upper μ.1
  obtain ⟨-, hN, hKμ, -⟩ := bg_sym_spec hk0 hk1 hμk
  obtain ⟨hUμ, -, -, hQμ, hDμ⟩ := fMuSym_upperHalf hk0 hk1 hμk
  obtain ⟨Fμ, hFμ⟩ := b33_d_homeo_upper hKμ hN.2.1 hUμ
  obtain ⟨k₀, hk₀0, hk₀1, hμk₀⟩ := bg_beltramiH_upper μ₀.1
  obtain ⟨-, hN₀, hKμ₀, -⟩ := bg_sym_spec hk₀0 hk₀1 hμk₀
  obtain ⟨hUμ₀, -, -, hQμ₀, hDμ₀⟩ := fMuSym_upperHalf hk₀0 hk₀1 hμk₀
  obtain ⟨Fμ₀, hFμ₀⟩ := b33_d_homeo_upper hKμ₀ hN₀.2.1 hUμ₀
  -- the new lift `F₀ = F ∘ (f^μ)⁻¹ ∘ f^{μ₀}`
  set F₀ : UpperHalfPlane ≃ₜ UpperHalfPlane := (Fμ₀.trans Fμ.symm).trans F with hF₀def
  have hF₀ : ∀ τ, F₀ τ = F (Fμ.symm (Fμ₀ τ)) := fun τ => rfl
  -- it has the deck correspondence of `F`
  have hdeck : ∀ γ ∈ Γ₀, ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, (∀ τ, F (γ • τ) = δ • F τ) →
      ∀ τ, F₀ (γ • τ) = δ • F₀ τ := by
    intro γ hγ δ hδ τ
    obtain ⟨A, hA₀, hA⟩ := s82dx_chi_eq h hγ
    have e₀ := (b33_d_rel_iff hFμ₀ γ A).1 hA₀
    have e₁ := (b33_d_rel_iff hFμ γ A).1 hA
    have e₂ : Fμ.symm (A • Fμ₀ τ) = γ • Fμ.symm (Fμ₀ τ) := by
      apply Fμ.injective
      rw [Fμ.apply_symm_apply, e₁, Fμ.apply_symm_apply]
    rw [hF₀, hF₀, e₀ τ, e₂, hδ]
  have h₀₁ : ∀ γ ∈ Γ₀, ∃ δ ∈ Γ₁, ∀ τ, F₀ (γ • τ) = δ • F₀ τ := fun γ hγ => by
    obtain ⟨δ, hδ, hγδ⟩ := h23l_deck hp₀ hp₁ hF hγ
    exact ⟨δ, hδ, hdeck γ hγ δ hγδ⟩
  have h₁₀ : ∀ δ ∈ Γ₁, ∃ γ ∈ Γ₀, ∀ τ, F₀ (γ • τ) = δ • F₀ τ := fun δ hδ => by
    obtain ⟨γ, hγ, hγδ⟩ := s24q_deck_surj hp₀ hp₁ hF hδ
    exact ⟨γ, hγ, hdeck γ hγ δ hγδ⟩
  obtain ⟨f₀, hf₀⟩ := s24q_descend hp₀ hp₁ F₀ h₀₁ h₁₀
  -- `liftToC F₀ = A ∘ f^{μ₀}` on `ℍ`, with `A = liftToC F ∘ (f^μ)⁻¹` conformal
  set A : ℂ → ℂ := liftToC F ∘ Function.invFunOn (fMuSym μ.1.1) upperHalf with hAdef
  have hAc : IsConformalOnto A (fMuSym μ.1.1 '' upperHalf) (liftToC F '' upperHalf) :=
    bg_conformal_of_dilatation_eq hQμ hFq (by
      filter_upwards [hμ, hDμ] with z h1 h2
      rw [h2]; exact h1.symm)
  rw [hUμ] at hAc
  have hinjμ : InjOn (fMuSym μ.1.1) upperHalf := hQμ.2.2.1.2.1
  have hEq : EqOn (liftToC F₀) (A ∘ fMuSym μ₀.1.1) upperHalf := fun z hz => by
    set τ : UpperHalfPlane := ⟨z, hz⟩
    have hzτ : z = (τ : ℂ) := rfl
    have hmem : ∃ a ∈ upperHalf, fMuSym μ.1.1 a = fMuSym μ₀.1.1 z :=
      ⟨Fμ.symm (Fμ₀ τ), (Fμ.symm (Fμ₀ τ)).2, by rw [← hFμ, Fμ.apply_symm_apply, hzτ, hFμ₀]⟩
    have hinv : Function.invFunOn (fMuSym μ.1.1) upperHalf (fMuSym μ₀.1.1 z) = (Fμ.symm (Fμ₀ τ) : ℂ) :=
      hinjμ (Function.invFunOn_mem hmem) (Fμ.symm (Fμ₀ τ)).2
        (by rw [Function.invFunOn_eq hmem, ← hFμ, Fμ.apply_symm_apply, hzτ, hFμ₀])
    show liftToC F₀ z = liftToC F (Function.invFunOn (fMuSym μ.1.1) upperHalf (fMuSym μ₀.1.1 z))
    rw [hinv, hzτ, h23l_liftToC_coe, h23l_liftToC_coe, hF₀]
  have hAq : IsKQC A upperHalf 1 := isKQC_one_of_conformal isOpen_upperHalf hAc
  have hF₀q : IsKQC (liftToC F₀) upperHalf ((1 + k₀) / (1 - k₀) * 1) :=
    ad_isKQC_congr (thm7_1_comp hQμ₀ hAq hUμ₀.le) hEq
  refine ⟨f₀, ⟨_, s24q_isKQCRS hp₀ hp₁ hf₀ hF₀q⟩, ?_, F₀, hf₀, ?_⟩
  · -- Theorem 23.1 with `γ₁ = 1`: `F₀` and `F` induce the same `γ ↦ δ`
    refine (thm23_1_homotopy_iff hp₀ hp₁ f₀ f hf₀ hF).2 ⟨1, Γ₁.one_mem, fun γ hγ τ => ?_⟩
    obtain ⟨δ, -, hγδ⟩ := h23l_deck hp₀ hp₁ hF hγ
    rw [one_smul, inv_one, one_smul, hdeck γ hγ δ hγδ, hγδ, Homeomorph.apply_symm_apply,
      Homeomorph.apply_symm_apply]
  · -- the dilatation: `A` is conformal, so `μ_{A ∘ f^{μ₀}} = μ_{f^{μ₀}} = μ₀`
    have hAd : DifferentiableOn ℂ A upperHalf := hAc.1
    filter_upwards [thm9_3_differentiable_ae hQμ₀, hDμ₀, ae_restrict_mem isOpen_upperHalf.measurableSet]
      with z hzd hzμ hz
    have hwz : fMuSym μ₀.1.1 z ∈ upperHalf := hUμ₀ ▸ mem_image_of_mem _ hz
    have hev : liftToC F₀ =ᶠ[𝓝 z] A ∘ fMuSym μ₀.1.1 :=
      Filter.eventually_of_mem (isOpen_upperHalf.mem_nhds hz) hEq
    have hfd : fderiv ℝ (liftToC F₀) z = fderiv ℝ (A ∘ fMuSym μ₀.1.1) z := hev.fderiv_eq
    have hcd : complexDilatation (liftToC F₀) z = complexDilatation (A ∘ fMuSym μ₀.1.1) z := by
      unfold complexDilatation dz dzbar
      rw [hfd]
    rw [hcd, complexDilatation_comp_conformal_left hzd
      ((hAd _ hwz).differentiableAt (isOpen_upperHalf.mem_nhds hwz))
      (deriv_ne_zero_of_injOn isOpen_upperHalf hAd hAc.2.1 hwz), hzμ]

/-- A map `c` with `c ∘ D = D'`, for a holomorphic surjective local homeomorphism `D` and a holomorphic `D'`, is
holomorphic: near `D e`, `c = D' ∘ (D|_U)⁻¹` with `D|_U` a holomorphic open embedding (`s31qr_open_embedding_inverse`). -/
theorem s82dx_mdiff_of_comp {E Y Z : Type*} [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ω E]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℂ) ω Z] {D : E → Y} (hD : IsLocalHomeomorph D) (hDd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) D)
    (hDs : Function.Surjective D) {D' : E → Z} (hD'd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) D') {c : Y → Z}
    (hc : ∀ e, c (D e) = D' e) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) c := by
  intro y
  obtain ⟨e₀, rfl⟩ := hDs y
  obtain ⟨h, he₀, hDh⟩ := hD e₀
  set U : TopologicalSpace.Opens E := ⟨h.source, h.open_source⟩ with hU
  have : Nonempty U := ⟨⟨e₀, he₀⟩⟩
  set g : U → Y := fun x => D x with hg
  have hval : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x : U => (x : E)) :=
    (contMDiff_subtype_val (n := ω)).mdifferentiable (by simp)
  have hgemb : Topology.IsOpenEmbedding g := by
    have h1 := h.isOpenEmbedding_restrict
    have h2 : g = h.source.domRestrict h := by
      funext x
      simp only [hg, Set.domRestrict_apply, hDh]
    rw [h2]
    exact h1
  have hgd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := fun x => (hDd _).comp x (hval x)
  have hy : D e₀ ∈ range g := ⟨⟨e₀, he₀⟩, rfl⟩
  have hinv := s31qr_open_embedding_inverse hgemb hgd hy
  have hev : c =ᶠ[𝓝 (D e₀)] fun y => D' ((hgemb.toOpenPartialHomeomorph g).symm y : E) := by
    filter_upwards [hgemb.isOpen_range.mem_nhds hy] with y hy'
    obtain ⟨x, rfl⟩ := hy'
    rw [hgemb.toOpenPartialHomeomorph_left_inv g]
    exact hc x
  have hD'U : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun x : U => D' x)
      ((hgemb.toOpenPartialHomeomorph g).symm (D e₀)) :=
    (hD'd _).comp _ (hval _)
  exact (hD'U.comp (D e₀) hinv).congr_of_eventuallyEq hev

/-- The lifted coefficient `s27u_liftCoeff p₀ f` (chart-read dilatation of `f ∘ p₀`) is the complex dilatation of any
lift `F` of `f` (the charts of `p₁` are local biholomorphisms, `complexDilatation_comp_conformal_left`). -/
theorem s82dx_liftCoeff_of_lift {S₀ S : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    {p₁ : UpperHalfPlane → S} (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁)
    {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K) {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p₀ p₁ f F) :
    ∀ᵐ τ ∂(volume.restrict upperHalf), s27u_liftCoeff p₀ f τ = complexDilatation (liftToC F) τ := by
  have hFq := h23l_lift_isKQC hp₀ hp₁ hf hF
  filter_upwards [thm9_3_differentiable_ae hFq, ae_restrict_mem isOpen_upperHalf.measurableSet] with z hzd hz
  have hz' : 0 < z.im := hz
  set τ : UpperHalfPlane := ⟨z, hz'⟩ with hτ
  set y : S := p₁ (F τ) with hy
  have hpz : utm_pext p₀ z = p₀ τ := s27u_pext_coe p₀ τ
  have hfy : f (utm_pext p₀ z) = y := by rw [hpz, hy, hF τ]
  rw [s27u_liftCoeff_of_mem p₀ f hz, hfy]
  have hloc : ∀ w ∈ upperHalf, chartAt ℂ y (f (utm_pext p₀ w)) = chartAt ℂ y (utm_pext p₁ (liftToC F w)) := by
    intro w hw
    have hw' : 0 < w.im := hw
    have h1 : liftToC F w = (F ⟨w, hw'⟩ : ℂ) := h23l_liftToC_coe F ⟨w, hw'⟩
    have h2 : utm_pext p₀ w = p₀ ⟨w, hw'⟩ := s27u_pext_coe p₀ ⟨w, hw'⟩
    rw [h1, h2, s27u_pext_coe p₁, hF]
  have hev : (fun w => chartAt ℂ y (f (utm_pext p₀ w))) =ᶠ[𝓝 z]
      (fun v => chartAt ℂ y (utm_pext p₁ v)) ∘ liftToC F :=
    Filter.eventually_of_mem (isOpen_upperHalf.mem_nhds hz) hloc
  have hcd : complexDilatation (fun w => chartAt ℂ y (f (utm_pext p₀ w))) z =
      complexDilatation ((fun v => chartAt ℂ y (utm_pext p₁ v)) ∘ liftToC F) z := by
    unfold complexDilatation dz dzbar
    rw [hev.fderiv_eq]
  have hq0 : IsHolQuadDiff (0 : S → ℂ → ℂ) := (holQuadDiffSubmodule S).zero_mem
  obtain ⟨U, -, hτU, -, -, hU⟩ := utm_liftQD_local hq0 hp₁ (F τ) y (mem_chart_source ℂ _)
  obtain ⟨-, hder, hne, -⟩ := hU _ hτU
  have hFz : liftToC F z = (F τ : ℂ) := h23l_liftToC_coe F τ
  rw [hcd, complexDilatation_comp_conformal_left hzd (by rw [hFz]; exact hder.differentiableAt)
    (by rw [hFz]; exact hne)]

/-- The lifted coefficient of a Teichmüller map `f` with initial differential `q ≠ 0` is `k ψ̄/|ψ|` a.e., `ψ` the
lift of `q` (non-compact version of `utm_x_liftCoeff_teichmullerMap`). -/
theorem s82dx_liftCoeff_teich {S₀ S₁ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀]
    [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [TopologicalSpace S₁] [ChartedSpace ℂ S₁]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ}
    (hf : IsTeichmullerMap f q q' k) (hq0 : q ≠ 0) :
    ∀ᵐ τ ∂(volume.restrict upperHalf), s27u_liftCoeff p₀ f τ = utm_x_tcoeff k (utm_liftQD q p₀) τ := by
  have hZ0 : volume {τ | τ ∈ upperHalf ∧ utm_liftQD q p₀ τ = 0} = 0 :=
    (utm_x1_liftQD_zeros_countable hf.initial hq0 hp₀).measure_zero _
  filter_upwards [ae_restrict_mem isOpen_upperHalf.measurableSet,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hZ0)] with τ hτ hτZ
  rw [s27u_liftCoeff_of_mem p₀ f hτ]
  exact (utm_x1_lift_pointwise hp₀ hf hτ fun h0 => hτZ ⟨hτ, h0⟩).symm

/-- **[D4, stub] The descended extremal map is an admissible Teichmüller map.**  Let `f₀ : S₀ → S` be
quasiconformal with a lift `F₀'` whose complex dilatation is `k ψ̄/|ψ|` a.e. on `ℍ`, `ψ` the lift of an admissible
`q ≠ 0`, `0 < k < 1`.  Then `f₀` is a Teichmüller map with initial differential `q`.  Route: the Teichmüller map
`T : S₀ → X` of `(q, k)` (`s82td_realize`) has the same lifted coefficient (`utm_x1_lift_pointwise`); uniformization
transport (`s27u_proj_mdifferentiable`) with the common normalized solution gives holomorphic coverings `D_T`, `D_f`
of `X`, `S` with `(f₀ ∘ T⁻¹) ∘ D_T = D_f`, so `c = f₀ ∘ T⁻¹` is biholomorphic, and `f₀ = c ∘ T`
(`s32w_dt_teich_comp`). -/
theorem s82dx_teich {S₀ S : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀]
    [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n : ℕ} (hex : ¬ IsExceptionalType g n 0)
    (F₀ : FiniteTypeStructure S₀ g n 0)
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    {p₁ : UpperHalfPlane → S} (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁)
    {f₀ : S₀ ≃ₜ S} (hf₀ : IsQCRS f₀) {F₀' : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF₀' : IsLift p₀ p₁ f₀ F₀')
    {q : S₀ → ℂ → ℂ} (hq : q ∈ admissibleQDInterior F₀) (hq0 : q ≠ 0) {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1)
    (hdil : ∀ᵐ τ ∂(volume.restrict upperHalf), complexDilatation (liftToC F₀') τ =
      (k : ℂ) * conj (utm_liftQD q p₀ τ) / (‖utm_liftQD q p₀ τ‖ : ℂ)) :
    ∃ q' : S → ℂ → ℂ, IsAdmissibleTeichmullerMap F₀ f₀ q q' k := by
  classical
  obtain ⟨Kf, hKf⟩ := hf₀
  -- the Teichmüller map `T` of `(q, k)`
  obtain ⟨A, qA, hT⟩ := s82td_realize hex F₀ hq hq0 hk0 hk1
  obtain ⟨KT, hKT⟩ := A.qc
  -- both lifted coefficients are `k ψ̄/|ψ|`
  have hae : ∀ᵐ τ ∂(volume.restrict upperHalf),
      s27u_liftCoeff p₀ A.marking τ = s27u_liftCoeff p₀ f₀ τ := by
    filter_upwards [s82dx_liftCoeff_teich hp₀ hT.2 hq0, s82dx_liftCoeff_of_lift hp₀ hp₁ hKf hF₀', hdil]
      with τ h1 h2 h3
    rw [h1, h2, h3]
    rfl
  have hKf1 : (1 : ℝ) ≤ Kf := hKf.1
  have hKT1 : (1 : ℝ) ≤ KT := hKT.1
  have kf0 : 0 ≤ (Kf - 1) / (Kf + 1) := div_nonneg (by linarith) (by linarith)
  have kf1 : (Kf - 1) / (Kf + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have kT0 : 0 ≤ (KT - 1) / (KT + 1) := div_nonneg (by linarith) (by linarith)
  have kT1 : (KT - 1) / (KT + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hbf := s27u_liftCoeff_isBeltramiCoeff hp₀ hKf
  have hbT := s27u_liftCoeff_isBeltramiCoeff hp₀ hKT
  have heq : s27u_fSym (s27u_liftCoeff p₀ A.marking) = s27u_fSym (s27u_liftCoeff p₀ f₀) :=
    s27u_fSym_congr_ae kT0 kT1 hbT kf0 kf1 hbf hae
  -- the common normalized solution `G` and the transported uniformizations `D_T`, `D_f`
  obtain ⟨-, hN, hKG, -⟩ := s27u_sym_spec kf0 kf1 hbf
  obtain ⟨G, hG⟩ := b33_d_homeo_upper hKG hN.2.1 (s27u_fSym_upperHalf kf0 kf1 hbf).1
  have hGT : ∀ τ, (G τ : ℂ) = s27u_fSym (s27u_liftCoeff p₀ A.marking) τ := fun τ => by rw [heq, hG]
  have hDf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (s27u_proj p₀ f₀ G) := s27u_proj_mdifferentiable hp₀ hKf hG
  have hDT : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (s27u_proj p₀ A.marking G) := s27u_proj_mdifferentiable hp₀ hKT hGT
  have hcovf : IsCoveringMap (s27u_proj p₀ f₀ G) := (hp₀.1.comp_homeomorph G.symm).homeomorph_comp f₀
  have hcovT : IsCoveringMap (s27u_proj p₀ A.marking G) :=
    (hp₀.1.comp_homeomorph G.symm).homeomorph_comp A.marking
  have hsT : Function.Surjective (s27u_proj p₀ A.marking G) := fun y => by
    obtain ⟨τ, hτ⟩ := hp₀.2.2.1 (A.marking.symm y)
    exact ⟨G τ, by simp [s27u_proj, hτ]⟩
  have hsf : Function.Surjective (s27u_proj p₀ f₀ G) := fun y => by
    obtain ⟨τ, hτ⟩ := hp₀.2.2.1 (f₀.symm y)
    exact ⟨G τ, by simp [s27u_proj, hτ]⟩
  -- `c = f₀ ∘ T⁻¹` is biholomorphic: `c ∘ D_T = D_f`
  set c : A.X.carrier ≃ₜ S := A.marking.symm.trans f₀ with hcdef
  have hc1 : ∀ w, c (s27u_proj p₀ A.marking G w) = s27u_proj p₀ f₀ G w := fun w => by
    simp [hcdef, s27u_proj]
  have hc2 : ∀ w, c.symm (s27u_proj p₀ f₀ G w) = s27u_proj p₀ A.marking G w := fun w => by
    rw [← hc1, c.symm_apply_apply]
  have hcB : IsBiholomorphic (c : A.X.carrier → S) :=
    ⟨s82dx_mdiff_of_comp hcovT.isLocalHomeomorph hDT hsT hDf hc1, c.symm,
      s82dx_mdiff_of_comp hcovf.isLocalHomeomorph hDf hsf hDT hc2,
      fun x => c.symm_apply_apply x, fun y => c.apply_symm_apply y⟩
  obtain ⟨Q', hQ'⟩ := s32w_dt_teich_comp A.marking c hcB hT.2
  have hfe : A.marking.trans c = f₀ := by
    ext x
    simp [hcdef]
  rw [hfe] at hQ'
  exact ⟨Q', hq, hQ'⟩


section
variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- **Book helper for Theorem 32.2** (`thm32_2_existence_gn`, S32:559; statement identical), the direct Hamilton
route: lift the coefficient of `f` to `μ ∈ M(Γ₀)`, take an extremal representative `μ₀ ∼ μ`
(`exists_extremal_mod_boundary`), descend `f^{μ₀}` to `f₀ ≃ f` (D5); by `thm36_2_finite_type` (with D2, D3) `μ₀ = 0`
(`f₀` conformal) or `μ₀ = k φ̄/|φ|`, `φ` the lift of an admissible `q ≠ 0` (`utm_x_descent`, D3a), and `f₀` is an
admissible Teichmüller map (D4). -/
theorem s82dx_thm32_2_existence_gn {g n : ℕ} (hex : ¬ IsExceptionalType g n 0) (F₀ : FiniteTypeStructure S₀ g n 0)
    (F₁ : FiniteTypeStructure S g n 0) (f : S₀ ≃ₜ S) (hf : IsQCRS f) :
    ∃ f₀ : S₀ ≃ₜ S, ContinuousMap.Homotopic (f : C(S₀, S)) (f₀ : C(S₀, S)) ∧
      (IsBiholomorphic f₀ ∨ ∃ (q : S₀ → ℂ → ℂ) (q' : S → ℂ → ℂ) (k : ℝ), IsAdmissibleTeichmullerMap F₀ f₀ q q' k) := by
  classical
  obtain ⟨Γ₀, p₀, hΓ₀, hfree₀, hp₀⟩ := (finiteType_hyperbolic F₀ hex).1 rfl
  obtain ⟨Γ₁, p₁, -, -, hp₁⟩ := (finiteType_hyperbolic F₁ hex).1 rfl
  obtain ⟨τ₀⟩ : Nonempty UpperHalfPlane := inferInstance
  obtain ⟨τ₁, hτ₁⟩ := hp₁.2.2.1 (f (p₀ τ₀))
  obtain ⟨F, hF, -⟩ := exists_lift hp₀ hp₁ f τ₀ τ₁ hτ₁
  obtain ⟨K, hK⟩ := hf
  -- the lifted coefficient `μ ∈ M(Γ₀)` and its extremal representative `μ₀`
  obtain ⟨μb, hμb, hΓμ⟩ := s27u_liftCoeff_beltramiH hp₀ ⟨K, hK⟩
  set μ : BeltramiGamma Γ₀ := ⟨μb, hΓμ⟩ with hμdef
  have hμ : ∀ᵐ τ ∂(volume.restrict upperHalf), μ.1.1 τ = complexDilatation (liftToC F) τ := by
    filter_upwards [s82dx_liftCoeff_of_lift hp₀ hp₁ hK hF] with τ h
    show μb.1 τ = _
    rw [hμb]
    exact h
  obtain ⟨μ₀, hμ₀μ, hext⟩ := exists_extremal_mod_boundary hΓ₀ μ
  -- D5: the descended representative `f₀ ≃ f` with lifted coefficient `μ₀`
  obtain ⟨f₀, hf₀q, hhom, F₀', hF₀', hdil₀⟩ := s82dx_descend hp₀ hp₁ hΓ₀ ⟨K, hK⟩ hF μ μ₀ hμ hμ₀μ
  refine ⟨f₀, hhom.symm, ?_⟩
  -- `μ₀ = 0`: the lift of `f₀` is conformal, so `f₀` is biholomorphic
  have hcase0 : (μ₀.1.1 =ᵐ[volume.restrict upperHalf] 0) → IsBiholomorphic f₀ := by
    intro h0
    obtain ⟨K₀, hK₀⟩ := hf₀q
    have hFq : IsKQC (liftToC F₀') upperHalf K₀ := h23l_lift_isKQC hp₀ hp₁ hK₀ hF₀'
    have hidc : IsConformalOnto id upperHalf (id '' upperHalf) :=
      ⟨differentiableOn_id, injOn_id _, rfl⟩
    have hidq : IsKQC id upperHalf 1 := isKQC_one_of_conformal isOpen_upperHalf hidc
    have hconf := bg_conformal_of_dilatation_eq hidq hFq (by
      filter_upwards [hdil₀, h0] with z h1 h2
      rw [h1, h2]
      show (0 : ℂ) = complexDilatation id z
      unfold complexDilatation dzbar
      simp)
    rw [image_id] at hconf
    have hinv : EqOn (liftToC F₀') (liftToC F₀' ∘ Function.invFunOn id upperHalf) upperHalf := fun z hz => by
      have hex' : ∃ a ∈ upperHalf, id a = z := ⟨z, hz, rfl⟩
      show liftToC F₀' z = liftToC F₀' (Function.invFunOn id upperHalf z)
      rw [show Function.invFunOn id upperHalf z = z from Function.invFunOn_eq hex']
    have h1 : IsKQC (liftToC F₀') upperHalf 1 :=
      ad_isKQC_congr (isKQC_one_of_conformal isOpen_upperHalf hconf) hinv
    exact (isKQCRS_one_iff f₀).1 (s24q_isKQCRS hp₀ hp₁ hF₀' h1)
  -- Hamilton: `μ₀ = 0` or `μ₀ = k φ̄/|φ|`
  obtain ⟨Fd, hFd⟩ := s82dx_exists_fundamentalDomain hΓ₀ hfree₀
  rcases thm36_2_finite_type hΓ₀ hfree₀ hFd (s82dx_hfin hex F₀ hp₀ hΓ₀ hFd) μ₀ hext with
    h0 | ⟨φ, hφA, hφ1, -, hφμ⟩
  · exact Or.inl (hcase0 h0)
  set k := beltramiNormH μ₀.1.1 with hkdef
  by_cases hk0 : k = 0
  · refine Or.inl (hcase0 ?_)
    filter_upwards [c36_c_ae_le_normH μ₀.1] with z hz
    rw [← hkdef, hk0] at hz
    exact norm_le_zero_iff.1 hz
  have hkpos : 0 < k := lt_of_le_of_ne (beltramiNormH_nonneg _) (Ne.symm hk0)
  have hk1 : k < 1 := beltramiNormH_lt_one μ₀.1
  -- `φ` descends to an admissible `q ≠ 0` (D3a)
  obtain ⟨q, hq, hqφ⟩ := utm_x_descent hp₀ hφA.1 hφA.2.2
  have hq0 : q ≠ 0 := by
    rintro rfl
    have hφ0 : ∀ τ ∈ upperHalf, φ τ = 0 := fun τ hτ => by
      rw [← hqφ τ hτ, show (0 : S₀ → ℂ → ℂ) = (0 : ℂ) • (0 : S₀ → ℂ → ℂ) by simp, utm_x_liftQD_smul, zero_mul]
    have h0 : phiArea φ Fd = 0 := by
      unfold phiArea
      rw [setLIntegral_congr_fun hFd.2.1 (fun z hz => by rw [hφ0 z (hFd.1 hz), norm_zero, ENNReal.ofReal_zero]),
        lintegral_zero]
    rw [h0] at hφ1
    exact zero_ne_one hφ1
  have hqA := s82dx_integrable_admissible F₀ hp₀ hΓ₀ hFd hφA hq hqφ
  -- D4: `f₀` is an admissible Teichmüller map
  obtain ⟨q', hT⟩ := s82dx_teich hex F₀ hp₀ hp₁ hf₀q hF₀' hqA hq0 hkpos hk1 (by
    filter_upwards [hdil₀, hφμ, ae_restrict_mem isOpen_upperHalf.measurableSet] with τ h1 h2 hτ
    rw [h1, h2, hqφ τ hτ])
  exact Or.inr ⟨q, q', k, hT⟩

end

section RelocatedS32

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- **Theorem 32.2**: let `S₀`, `S₁` be non-exceptional surfaces of type `(g, n)` and `f : S₀ → S₁`
a quasiconformal homeomorphism.  Then the homotopy class of `f` contains a Teichmüller map `f₀`
whose associated quadratic differential is admissible (or `f₀` is conformal). -/
theorem thm32_2_existence_gn {g n : ℕ} (hex : ¬ IsExceptionalType g n 0) (F₀ : FiniteTypeStructure S₀ g n 0)
    (F₁ : FiniteTypeStructure S g n 0) (f : S₀ ≃ₜ S) (hf : IsQCRS f) :
    ∃ f₀ : S₀ ≃ₜ S, ContinuousMap.Homotopic (f : C(S₀, S)) (f₀ : C(S₀, S)) ∧
      (IsBiholomorphic f₀ ∨ ∃ (q : S₀ → ℂ → ℂ) (q' : S → ℂ → ℂ) (k : ℝ), IsAdmissibleTeichmullerMap F₀ f₀ q q' k) := by
  exact s82dx_thm32_2_existence_gn hex F₀ F₁ f hf

end RelocatedS32

end LiZhongQC
