import LiZhongQC.Ch11.S36_Hamilton
import LiZhongQC.Lemmas.HyperbolicSurfaceArea
import LiZhongQC.Lemmas.UniformizedUniqueness
import LiZhongQC.Lemmas.SchottkyDirectD3a
import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.StrebelGammaTransport
import LiZhongQC.Lemmas.StrebelSurfaceLambda
import LiZhongQC.Lemmas.StrebelGammaMapFacts
import LiZhongQC.Lemmas.StrebelDoubleDomain


/-! Existing approved Step A helpers, separated from the pending double-foundation
assembly. All proof bodies below are unchanged. The later assembly imports shared
chart measurability from StrebelFirstKind. This module does not establish the frozen double inequality. -/
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ### G1b, Step A (`s36a_`): the reflected map `g̃` on `ℂ` -/

/-- **The reflected map.**  `g̃ = (f^ν)⁻¹ ∘ f^μ` on all of `ℂ` (the inverse taken on `univ`) is a `K`-q.c.
homeomorphism of `ℂ` which agrees on `ℍ` with the map `g` of the frozen statements (inverse taken on `ℍ`), is the
identity on `ℝ` (since `ν ∼ μ`), commutes with `conj`, maps `ℍ` and `𝕃` onto themselves, and commutes with `Γ` off
`ℝ`. -/
theorem s36a_gt (μ ν : BeltramiGamma Γ) (hrel : teichSetoidGamma Γ ν μ) :
    ∃ K : ℝ, IsKQC (Function.invFunOn (fMuSym ν.1.1) univ ∘ fMuSym μ.1.1) univ K ∧
      (Function.invFunOn (fMuSym ν.1.1) univ ∘ fMuSym μ.1.1) '' univ = univ ∧
      (∀ z ∈ upperHalf, (Function.invFunOn (fMuSym ν.1.1) univ ∘ fMuSym μ.1.1) z =
        (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z) ∧
      (∀ x : ℝ, (Function.invFunOn (fMuSym ν.1.1) univ ∘ fMuSym μ.1.1) (x : ℂ) = x) ∧
      (∀ z, (Function.invFunOn (fMuSym ν.1.1) univ ∘ fMuSym μ.1.1) (conj z) =
        conj ((Function.invFunOn (fMuSym ν.1.1) univ ∘ fMuSym μ.1.1) z)) ∧
      (∀ z ∈ upperHalf, (Function.invFunOn (fMuSym ν.1.1) univ ∘ fMuSym μ.1.1) z ∈ upperHalf) ∧
      ∀ γ ∈ Γ, ∀ z : ℂ, z.im ≠ 0 →
        (Function.invFunOn (fMuSym ν.1.1) univ ∘ fMuSym μ.1.1) (h36p_m γ z) =
          h36p_m γ ((Function.invFunOn (fMuSym ν.1.1) univ ∘ fMuSym μ.1.1) z) := by
  obtain ⟨hNν, hsν, -⟩ := c36_c_fMuSym_spec ν.1 (c36_c_normH_lt_one ν.1) le_rfl
  obtain ⟨hNμ, hsμ, -⟩ := c36_c_fMuSym_spec μ.1 (c36_c_normH_lt_one μ.1) le_rfl
  obtain ⟨Kg, hgK, hgimg, hcomm⟩ := str_g_facts μ ν hrel
  obtain ⟨-, hνs⟩ := str_fMu_facts ν
  obtain ⟨-, hμs⟩ := str_fMu_facts μ
  set f := fMuSym ν.1.1 with hf
  set f₀ := fMuSym μ.1.1 with hf₀
  obtain ⟨hKν, hfs, -, -⟩ := hNν
  obtain ⟨hKμ, hf₀s, -, -⟩ := hNμ
  set a := Function.invFunOn f univ with hadef
  have hfi : Function.Injective f := Set.injOn_univ.1 hKν.2.2.1.2.1
  have hfsurj : ∀ w, ∃ y, f y = w := fun w => by
    have : w ∈ f '' univ := by rw [hfs]; trivial
    obtain ⟨y, -, hy⟩ := this
    exact ⟨y, hy⟩
  have haf : ∀ w, f (a w) = w := fun w => by
    obtain ⟨y, hy⟩ := hfsurj w
    exact Function.invFunOn_eq ⟨y, mem_univ _, hy⟩
  have hfa : ∀ y, a (f y) = y := fun y => hfi (haf (f y))
  have haK : IsKQC a univ (((1 + beltramiNormH ν.1.1) / (1 - beltramiNormH ν.1.1))) := by
    have h := thm7_2_inv hKν
    rwa [hfs] at h
  have hGK := thm7_1_comp hKμ haK (by rw [hf₀s])
  have hGimg : (a ∘ f₀) '' univ = univ := by
    rw [image_comp, hf₀s, eq_univ_iff_forall]
    intro y
    exact ⟨f y, mem_univ _, hfa y⟩
  -- agreement with the inverse on `ℍ`
  have hagree : ∀ z ∈ upperHalf, (a ∘ f₀) z = (Function.invFunOn f upperHalf ∘ f₀) z := by
    intro z hz
    have hex : ∃ w ∈ upperHalf, f w = f₀ z := by
      have : f₀ z ∈ f '' upperHalf := by
        rw [hνs]
        exact hμs ▸ mem_image_of_mem _ hz
      obtain ⟨w, hw, hw'⟩ := this
      exact ⟨w, hw, hw'⟩
    show a (f₀ z) = Function.invFunOn f upperHalf (f₀ z)
    exact hfi ((haf _).trans (Function.invFunOn_eq hex).symm)
  have hreal : ∀ x : ℝ, (a ∘ f₀) (x : ℂ) = x := by
    intro x
    show a (f₀ x) = x
    rw [show f₀ x = f x from (hrel x).symm, hfa]
  have hconj : ∀ z, (a ∘ f₀) (conj z) = conj ((a ∘ f₀) z) := by
    intro z
    show a (f₀ (conj z)) = conj (a (f₀ z))
    apply hfi
    rw [haf, hsμ, hsν, haf]
  have hH : ∀ z ∈ upperHalf, (a ∘ f₀) z ∈ upperHalf := fun z hz => by
    rw [hagree z hz]
    have h1 := mem_image_of_mem (Function.invFunOn f upperHalf ∘ f₀) hz
    rw [hgimg] at h1
    exact h1
  refine ⟨_, hGK, hGimg, hagree, hreal, hconj, hH, fun γ hγ z hz => ?_⟩
  have hmconj : ∀ w : ℂ, h36p_m γ (conj w) = conj (h36p_m γ w) := fun w =>
    b33_e_mobius_conj γ w
  rcases lt_or_gt_of_ne hz with hlt | hgt
  · -- `z ∈ 𝕃`: reflect to `ℍ`
    have hcz : conj z ∈ upperHalf := by
      show 0 < (conj z).im
      rw [Complex.conj_im]
      linarith
    have h1 := hcomm γ hγ (conj z) hcz
    rw [← hagree _ hcz, ← hagree _ (h36p_m_mem γ hcz), hmconj, hconj, hconj] at h1
    have h2 := congrArg conj h1
    simp only [Complex.conj_conj] at h2
    rw [h2, ← hmconj, Complex.conj_conj]
  · have h1 := hcomm γ hγ z hgt
    rw [← hagree _ hgt, ← hagree _ (h36p_m_mem γ hgt)] at h1
    exact h1

/-- `λ(ψ, G)(z) = λ(ψ, g)(z)` when `G = g` near `z`. -/
theorem s36a_lam_congr {ψ G g : ℂ → ℂ} {z : ℂ} (h : G =ᶠ[𝓝 z] g) :
    lambdaStretchPlane ψ ψ G z = lambdaStretchPlane ψ ψ g z := by
  unfold lambdaStretchPlane dz dzbar
  rw [h.fderiv_eq, h.self_of_nhds]

/-- Wirtinger derivatives of a map commuting with `conj`: `∂G(z̄) = conj ∂G(z)`, `∂̄G(z̄) = conj ∂̄G(z)`. -/
theorem s36a_dz_conj {G : ℂ → ℂ} (hG : ∀ z, G (conj z) = conj (G z)) (z : ℂ) :
    dz G (conj z) = conj (dz G z) ∧ dzbar G (conj z) = conj (dzbar G z) := by
  have hGfun : (fun w => conj (G (conj w))) = G := funext fun w => by rw [hG, Complex.conj_conj]
  by_cases hd : DifferentiableAt ℝ G z
  · have hd' : DifferentiableAt ℝ G (conj (conj z)) := by rwa [Complex.conj_conj]
    obtain ⟨-, h1, h2⟩ := abR_x_dz_dzbar_conj hd'
    rw [hGfun, Complex.conj_conj] at h1 h2
    exact ⟨h1, h2⟩
  · have hd' : ¬ DifferentiableAt ℝ G (conj z) := by
      intro h
      apply hd
      have := (abR_x_dz_dzbar_conj (h := G) (z := z) h).1
      rwa [hGfun] at this
    simp [dz, dzbar, fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd']

/-- **Reflection.**  `λ(ψ, G)(z̄) = λ(ψ*, G)(z)` for `G` commuting with `conj`, `ψ* = conj ∘ ψ ∘ conj`. -/
theorem s36a_reflect {ψ G : ℂ → ℂ} (hG : ∀ z, G (conj z) = conj (G z)) (z : ℂ) :
    lambdaStretchPlane ψ ψ G (conj z) =
      lambdaStretchPlane (fun w => conj (ψ (conj w))) (fun w => conj (ψ (conj w))) G z := by
  obtain ⟨h1, h2⟩ := s36a_dz_conj hG z
  unfold lambdaStretchPlane
  simp only [Complex.norm_conj]
  have e3 : conj (dz G z) + conj (dzbar G z) * (ψ (conj z) / ((‖ψ (conj z)‖ : ℝ) : ℂ)) =
      conj (dz G z + dzbar G z * (conj (ψ (conj z)) / ((‖ψ (conj z)‖ : ℝ) : ℂ))) := by
    simp [map_add, map_mul, map_div₀, Complex.conj_ofReal]
  rw [hG, h1, h2, e3, Complex.norm_conj]

/-! ### Step A (b): the reflected geodesic homotopy and the descent through `P` -/

/-- `ofComplex` is continuous at points of `ℍ`. -/
theorem s36a_ofC_cont {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt (fun w : ℂ => (UpperHalfPlane.ofComplex w : UpperHalfPlane)) z := by
  have hsrc : UpperHalfPlane.ofComplex.source = upperHalf := by
    ext w
    simp [UpperHalfPlane.ofComplex, upperHalf]
  exact UpperHalfPlane.ofComplex.continuousAt (by rw [hsrc]; exact hz)

/-- `ofComplex` followed by the coercion is the identity on `ℍ`. -/
theorem s36a_ofC_coe {z : ℂ} (hz : 0 < z.im) : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = z := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-- **The reflected geodesic homotopy** from `G` to the identity: on `ℍ` the hyperbolic geodesic interpolation from
`G z` to `z`, on `𝕃` its mirror image, the identity on `ℝ`.  It is continuous on `ℂ × [0, 1]` (near a real point
the geodesic segment between two nearby points stays nearby), preserves `ℍ`, `𝕃` and `ℝ`, and commutes with `Γ`. -/
theorem s36a_geodH {G : ℂ → ℂ} (hGc : Continuous G) (hGH : ∀ z ∈ upperHalf, G z ∈ upperHalf)
    (hGconj : ∀ z, G (conj z) = conj (G z)) (hGr : ∀ x : ℝ, G (x : ℂ) = x)
    (hGΓ : ∀ γ ∈ Γ, ∀ z : ℂ, z.im ≠ 0 → G (h36p_m γ z) = h36p_m γ (G z)) :
    ∃ H : ℂ × unitInterval → ℂ, Continuous H ∧ (∀ z, H (z, 0) = G z) ∧ (∀ z, H (z, 1) = z) ∧
      (∀ z t, 0 < z.im → 0 < (H (z, t)).im) ∧ (∀ z t, z.im < 0 → (H (z, t)).im < 0) ∧
      (∀ z t, z.im = 0 → H (z, t) = z) ∧
      ∀ γ ∈ Γ, ∀ z t, z.im ≠ 0 → H (h36p_m γ z, t) = h36p_m γ (H (z, t)) := by
  classical
  set FUp : ℂ × unitInterval → ℂ := fun x =>
    ((c36_d_geod (UpperHalfPlane.ofComplex (G x.1)) (UpperHalfPlane.ofComplex x.1) (x.2 : ℝ) :
      UpperHalfPlane) : ℂ) with hFUp
  set FLo : ℂ × unitInterval → ℂ := fun x =>
    conj ((c36_d_geod (UpperHalfPlane.ofComplex (G (conj x.1))) (UpperHalfPlane.ofComplex (conj x.1))
      (x.2 : ℝ) : UpperHalfPlane) : ℂ) with hFLo
  set H : ℂ × unitInterval → ℂ := fun x =>
    if 0 < x.1.im then FUp x else if x.1.im < 0 then FLo x else x.1 with hH
  have Hpos : ∀ x : ℂ × unitInterval, 0 < x.1.im → H x = FUp x := fun x hx => by
    simp only [hH, if_pos hx]
  have Hneg : ∀ x : ℂ × unitInterval, x.1.im < 0 → H x = FLo x := fun x hx => by
    simp only [hH, if_neg (not_lt.2 hx.le), if_pos hx]
  have Hzero : ∀ x : ℂ × unitInterval, x.1.im = 0 → H x = x.1 := fun x hx => by
    simp only [hH, if_neg (not_lt.2 hx.le), if_neg (not_lt.2 hx.ge)]
  have hconjpos : ∀ z : ℂ, z.im < 0 → 0 < (conj z).im := fun z hz => by
    rw [Complex.conj_im]; linarith
  have hGpos : ∀ z : ℂ, 0 < z.im → 0 < (G z).im := fun z hz => hGH z hz
  have hreal_eq : ∀ z : ℂ, z.im = 0 → z = ((z.re : ℝ) : ℂ) := fun z hz =>
    Complex.ext (by simp) (by simp [hz])
  have hconjm : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℂ), h36p_m γ (conj w) = conj (h36p_m γ w) :=
    fun γ w => b33_e_mobius_conj γ w
  -- endpoints
  have h0 : ∀ z, H (z, 0) = G z := by
    intro z
    rcases lt_trichotomy z.im 0 with hlt | heq | hgt
    · rw [Hneg _ hlt]
      simp only [hFLo, Set.Icc.coe_zero, h36t_geod_zero]
      rw [s36a_ofC_coe (hGpos _ (hconjpos z hlt)), hGconj, Complex.conj_conj]
    · rw [Hzero _ heq]
      conv_rhs => rw [hreal_eq z heq, hGr]
      exact hreal_eq z heq
    · rw [Hpos _ hgt]
      simp only [hFUp, Set.Icc.coe_zero, h36t_geod_zero]
      rw [s36a_ofC_coe (hGpos _ hgt)]
  have h1 : ∀ z, H (z, 1) = z := by
    intro z
    rcases lt_trichotomy z.im 0 with hlt | heq | hgt
    · rw [Hneg _ hlt]
      simp only [hFLo, Set.Icc.coe_one, h36t_geod_one]
      rw [s36a_ofC_coe (hconjpos z hlt), Complex.conj_conj]
    · exact Hzero _ heq
    · rw [Hpos _ hgt]
      simp only [hFUp, Set.Icc.coe_one, h36t_geod_one]
      exact s36a_ofC_coe hgt
  -- signs
  have hpos : ∀ z t, 0 < z.im → 0 < (H (z, t)).im := fun z t hz => by
    rw [Hpos (z, t) hz]
    exact UpperHalfPlane.coe_im_pos _
  have hneg : ∀ z t, z.im < 0 → (H (z, t)).im < 0 := fun z t hz => by
    rw [Hneg (z, t) hz]
    simp only [hFLo, Complex.conj_im]
    exact neg_neg_of_pos (UpperHalfPlane.coe_im_pos _)
  -- equivariance
  have hofsmul : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℂ), 0 < w.im →
      UpperHalfPlane.ofComplex (h36p_m γ w) = γ • UpperHalfPlane.ofComplex w := by
    intro γ w hw
    have : h36p_m γ w = ((γ • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ) := by
      rw [← h36p_m_coe, s36a_ofC_coe hw]
    rw [this, UpperHalfPlane.ofComplex_apply]
  have hequiv_pos : ∀ γ ∈ Γ, ∀ z t, 0 < z.im →
      FUp (h36p_m γ z, t) = h36p_m γ (FUp (z, t)) := by
    intro γ hγ z t hz
    simp only [hFUp]
    rw [hGΓ γ hγ z (ne_of_gt hz), hofsmul γ _ (hGpos z hz), hofsmul γ z hz, h36t_geod_smul, h36p_m_coe]
  have hequiv : ∀ γ ∈ Γ, ∀ z t, z.im ≠ 0 → H (h36p_m γ z, t) = h36p_m γ (H (z, t)) := by
    intro γ hγ z t hz
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · have hcz := hconjpos z hlt
      have hγz : (h36p_m γ z).im < 0 := by
        have h2 : 0 < (h36p_m γ (conj z)).im := h36p_m_mem γ hcz
        rw [hconjm, Complex.conj_im] at h2
        linarith
      rw [Hneg (h36p_m γ z, t) hγz, Hneg (z, t) hlt]
      simp only [hFLo]
      have h3 := hequiv_pos γ hγ (conj z) t hcz
      simp only [hFUp] at h3
      rw [← hconjm, h3, hconjm]
    · rw [Hpos (h36p_m γ z, t) (h36p_m_mem γ hgt), Hpos (z, t) hgt]
      exact hequiv_pos γ hγ z t hgt
  -- continuity
  have hFUpc : ∀ x : ℂ × unitInterval, 0 < x.1.im → ContinuousAt FUp x := by
    rintro ⟨z, t⟩ hz
    have hA : ContinuousAt (fun x : ℂ × unitInterval =>
        (UpperHalfPlane.ofComplex (G x.1), UpperHalfPlane.ofComplex x.1, (x.2 : ℝ))) (z, t) := by
      refine ContinuousAt.prodMk ?_ (ContinuousAt.prodMk ?_ ?_)
      · exact (s36a_ofC_cont (hGpos z hz)).comp (f := fun x : ℂ × unitInterval => G x.1)
          (hGc.continuousAt.comp continuous_fst.continuousAt)
      · exact (s36a_ofC_cont hz).comp (f := fun x : ℂ × unitInterval => x.1) continuous_fst.continuousAt
      · exact (continuous_subtype_val.comp continuous_snd).continuousAt
    exact UpperHalfPlane.continuous_coe.continuousAt.comp
      (f := fun x : ℂ × unitInterval => c36_d_geod (UpperHalfPlane.ofComplex (G x.1))
        (UpperHalfPlane.ofComplex x.1) (x.2 : ℝ))
      (c36_d_geod_continuous.continuousAt.comp hA)
  have hFLoc : ∀ x : ℂ × unitInterval, x.1.im < 0 → ContinuousAt FLo x := by
    rintro ⟨z, t⟩ hz
    have hcz := hconjpos z hz
    have hm : Continuous (fun x : ℂ × unitInterval => ((conj x.1, x.2) : ℂ × unitInterval)) :=
      (Complex.continuous_conj.comp continuous_fst).prodMk continuous_snd
    have hC : ContinuousAt (fun x : ℂ × unitInterval => FUp (conj x.1, x.2)) (z, t) :=
      ContinuousAt.comp (g := FUp) (f := fun x : ℂ × unitInterval => ((conj x.1, x.2) : ℂ × unitInterval))
        (x := (z, t)) (hFUpc (conj z, t) hcz) hm.continuousAt
    have hD : ContinuousAt (fun x : ℂ × unitInterval => conj (FUp (conj x.1, x.2))) (z, t) :=
      ContinuousAt.comp (g := fun w : ℂ => conj w) (f := fun x : ℂ × unitInterval => FUp (conj x.1, x.2))
        (x := (z, t)) Complex.continuous_conj.continuousAt hC
    have hEq : FLo = fun x : ℂ × unitInterval => conj (FUp (conj x.1, x.2)) := by
      funext x
      rfl
    rw [hEq]
    exact hD
  have hcont : Continuous H := by
    rw [continuous_iff_continuousAt]
    rintro ⟨z₀, t₀⟩
    rcases lt_trichotomy z₀.im 0 with hlt | heq | hgt
    · have hU : {x : ℂ × unitInterval | x.1.im < 0} ∈ 𝓝 (z₀, t₀) :=
        (isOpen_lt (continuous_im.comp continuous_fst) continuous_const).mem_nhds hlt
      exact (hFLoc _ hlt).congr (Filter.eventuallyEq_of_mem hU fun x hx => (Hneg x hx).symm)
    · -- a real point: `H` stays within `ε` of `z₀`
      have hz₀c : conj z₀ = z₀ := Complex.conj_eq_iff_im.2 heq
      have hGz₀ : G z₀ = z₀ := by rw [hreal_eq z₀ heq, hGr]
      rw [Metric.continuousAt_iff]
      intro ε hε
      obtain ⟨δ₁, hδ₁, hGδ⟩ := Metric.continuousAt_iff.1 hGc.continuousAt ε hε
      refine ⟨min δ₁ ε, lt_min hδ₁ hε, ?_⟩
      rintro ⟨z, t⟩ hx
      have hzd : dist z z₀ < min δ₁ ε := lt_of_le_of_lt (le_max_left _ _) (by simpa [Prod.dist_eq] using hx)
      have hzε : dist z z₀ < ε := lt_of_lt_of_le hzd (min_le_right _ _)
      have hGzε : dist (G z) z₀ < ε := by
        have := hGδ (lt_of_lt_of_le hzd (min_le_left _ _))
        rwa [hGz₀] at this
      have hconjd : ∀ w : ℂ, dist (conj w) z₀ = dist w z₀ := fun w => by
        conv_lhs => rw [← hz₀c]
        exact Complex.dist_conj_conj w z₀
      have hz₀r : ((z₀.re : ℝ) : ℂ) = z₀ := (hreal_eq z₀ heq).symm
      rw [Hzero (z₀, t₀) heq]
      have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      rcases lt_trichotomy z.im 0 with hlt' | heq' | hgt'
      · rw [Hneg (z, t) hlt']
        simp only [hFLo]
        rw [hconjd]
        have hcz := hconjpos z hlt'
        have hb : dist ((UpperHalfPlane.ofComplex (conj z) : UpperHalfPlane) : ℂ) ((z₀.re : ℝ) : ℂ) < ε := by
          rw [s36a_ofC_coe hcz, hz₀r, hconjd]; exact hzε
        have ha : dist ((UpperHalfPlane.ofComplex (G (conj z)) : UpperHalfPlane) : ℂ) ((z₀.re : ℝ) : ℂ) < ε := by
          rw [s36a_ofC_coe (hGpos _ hcz), hz₀r, hGconj, hconjd]; exact hGzε
        have := h36t_geod_dist_lt _ _ z₀.re ha hb ht0 ht1
        rwa [hz₀r] at this
      · rw [Hzero (z, t) heq']
        exact hzε
      · rw [Hpos (z, t) hgt']
        simp only [hFUp]
        have hb : dist ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) ((z₀.re : ℝ) : ℂ) < ε := by
          rw [s36a_ofC_coe hgt', hz₀r]; exact hzε
        have ha : dist ((UpperHalfPlane.ofComplex (G z) : UpperHalfPlane) : ℂ) ((z₀.re : ℝ) : ℂ) < ε := by
          rw [s36a_ofC_coe (hGpos _ hgt'), hz₀r]; exact hGzε
        have := h36t_geod_dist_lt _ _ z₀.re ha hb ht0 ht1
        rwa [hz₀r] at this
    · have hU : {x : ℂ × unitInterval | 0 < x.1.im} ∈ 𝓝 (z₀, t₀) :=
        (isOpen_lt continuous_const (continuous_im.comp continuous_fst)).mem_nhds hgt
      exact (hFUpc _ hgt).congr (Filter.eventuallyEq_of_mem hU fun x hx => (Hpos x hx).symm)
  exact ⟨H, hcont, h0, h1, hpos, hneg, fun z t hz => Hzero (z, t) hz, hequiv⟩

/-- `P` is continuous on `Ω` (it agrees with a local homeomorphism near every point). -/
theorem s36a_Pcont {S : Type} [TopologicalSpace S] {Ω : Set ℂ} {P : ℂ → S}
    (hPe : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source) :
    ∀ z ∈ Ω, ContinuousAt P z := by
  intro z hz
  obtain ⟨e, hze, -, hPe'⟩ := hPe z hz
  exact (e.continuousAt hze).congr (Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hze)
    fun w hw => (hPe' hw).symm)

/-- **Descent through `P`.**  A map `Φ : Ω × T → Ω`, continuous on `Ω × T` and compatible with the fibres of `P`,
descends to a continuous map `φ : S × T → S` with `φ (P z, t) = P (Φ (z, t))`. -/
theorem s36a_descend {S : Type} [TopologicalSpace S] {T : Type} [TopologicalSpace T]
    {Ω : Set ℂ} {P : ℂ → S} (hPs : P '' Ω = univ)
    (hPe : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source)
    {Φ : ℂ × T → ℂ} (hΦc : ∀ z ∈ Ω, ∀ t, ContinuousAt Φ (z, t)) (hΦΩ : ∀ z ∈ Ω, ∀ t, Φ (z, t) ∈ Ω)
    (hcomp : ∀ z ∈ Ω, ∀ w ∈ Ω, P z = P w → ∀ t, P (Φ (z, t)) = P (Φ (w, t))) :
    ∃ φ : S × T → S, Continuous φ ∧ ∀ z ∈ Ω, ∀ t, φ (P z, t) = P (Φ (z, t)) := by
  classical
  have hsec : ∀ s : S, ∃ z ∈ Ω, P z = s := fun s => by
    have : s ∈ P '' Ω := by rw [hPs]; trivial
    obtain ⟨z, hz, h⟩ := this
    exact ⟨z, hz, h⟩
  choose sec hsecΩ hsecP using hsec
  have hPc := s36a_Pcont hPe
  refine ⟨fun x => P (Φ (sec x.1, x.2)), ?_, fun z hz t => hcomp _ (hsecΩ _) z hz (hsecP _) t⟩
  rw [continuous_iff_continuousAt]
  rintro ⟨s, t⟩
  obtain ⟨e, hze, heΩ, hPe'⟩ := hPe (sec s) (hsecΩ s)
  have hst : s ∈ e.target := by
    rw [← hsecP s, hPe' hze]
    exact e.map_source hze
  have heq : ∀ x ∈ e.target ×ˢ (univ : Set T),
      P (Φ (e.symm x.1, x.2)) = (fun x : S × T => P (Φ (sec x.1, x.2))) x := by
    rintro ⟨s', t'⟩ ⟨hs', -⟩
    have hP' : P (e.symm s') = s' := by rw [hPe' (e.map_target hs'), e.right_inv hs']
    exact (hcomp _ (hsecΩ s') _ (heΩ (e.map_target hs')) ((hsecP s').trans hP'.symm) t').symm
  have hnhds : e.target ×ˢ (univ : Set T) ∈ 𝓝 (s, t) :=
    prod_mem_nhds (e.open_target.mem_nhds hst) univ_mem
  have hcont : ContinuousAt (fun x : S × T => P (Φ (e.symm x.1, x.2))) (s, t) := by
    have hes : e.symm s ∈ Ω := heΩ (e.map_target hst)
    have h1 : ContinuousAt (fun x : S × T => (e.symm x.1, x.2)) (s, t) :=
      ((e.continuousAt_symm hst).comp continuous_fst.continuousAt).prodMk continuous_snd.continuousAt
    have h2 : ContinuousAt (fun x : S × T => Φ (e.symm x.1, x.2)) (s, t) :=
      (hΦc _ hes t).comp (f := fun x : S × T => (e.symm x.1, x.2)) h1
    exact (hPc _ (hΦΩ _ hes t)).comp (f := fun x : S × T => Φ (e.symm x.1, x.2)) h2
  exact hcont.congr (Filter.eventuallyEq_of_mem hnhds heq)

/-- Around a point of `Ω`, the chart expression `v ↦ φ_x (P v)` is conformal (holomorphic and injective), hence
`1`-q.c. -/
theorem s36a_conf_chart {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    {Ω : Set ℂ} {P : ℂ → S}
    (hPe : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    (x : S) {ζ : ℂ} (hζ : ζ ∈ Ω) (hx : P ζ ∈ (chartAt ℂ x).source) :
    ∃ V : Set ℂ, IsOpen V ∧ ζ ∈ V ∧ V ⊆ Ω ∧ (∀ v ∈ V, P v ∈ (chartAt ℂ x).source) ∧
      IsKQC (fun v => chartAt ℂ x (P v)) V 1 := by
  obtain ⟨e, hζe, heΩ, hPe', hed, -⟩ := hPe ζ hζ
  set V : Set ℂ := e.source ∩ e ⁻¹' (chartAt ℂ x).source with hVdef
  have hVo : IsOpen V := e.continuousOn.isOpen_inter_preimage e.open_source (chartAt ℂ x).open_source
  have hζV : ζ ∈ V := ⟨hζe, by show e ζ ∈ (chartAt ℂ x).source; rw [← hPe' hζe]; exact hx⟩
  refine ⟨V, hVo, hζV, fun v hv => heΩ hv.1, fun v hv => by rw [hPe' hv.1]; exact hv.2,
    isKQC_one_of_conformal hVo ⟨fun v hv => ?_, fun v hv w hw hvw => ?_, rfl⟩⟩
  · have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun v => chartAt ℂ x (e v)) v :=
      (mdifferentiableAt_atlas (chart_mem_atlas ℂ x) hv.2).comp v
        ((hed v hv.1).mdifferentiableAt (e.open_source.mem_nhds hv.1))
    have h2 := mdifferentiableAt_iff_differentiableAt.1 h1
    have hev : (fun v => chartAt ℂ x (P v)) =ᶠ[𝓝 v] (fun v => chartAt ℂ x (e v)) :=
      Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hv.1) fun w hw => by simp only [hPe' hw]
    exact (h2.congr_of_eventuallyEq hev).differentiableWithinAt
  · simp only at hvw
    rw [hPe' hv.1, hPe' hw.1] at hvw
    exact e.injOn hv.1 hw.1 ((chartAt ℂ x).injOn hv.2 hw.2 hvw)

/-- **The descended map is `K`-q.c.**: locally `φ_{h x} ∘ h ∘ φ_x⁻¹ = (φ_{h x} ∘ P) ∘ G ∘ (φ_x ∘ P)⁻¹`. -/
theorem s36a_hqc {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    {Ω : Set ℂ} {P : ℂ → S} (hPs : P '' Ω = univ)
    (hPe : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    {G : ℂ → ℂ} {K : ℝ} (hGK : IsKQC G univ K) (hGΩ : ∀ z ∈ Ω, G z ∈ Ω) (h : S ≃ₜ S)
    (hh : ∀ z ∈ Ω, h (P z) = P (G z)) : IsKQCRS h K := by
  have hK1 : (1 : ℝ) ≤ K := hGK.2.1
  refine ⟨hK1, fun x => s23_lg (s23_localMapDomain_isOpen h.continuous x) hK1
    (s23_c1_injOn_localMapExpr h.injective x) fun z₀ hz₀ => ?_⟩
  obtain ⟨hz₀t, hz₀s⟩ := hz₀
  have hp₀ : (chartAt ℂ x).symm z₀ ∈ P '' Ω := by rw [hPs]; trivial
  obtain ⟨ζ₀, hζ₀, hPζ₀⟩ := hp₀
  have hx0 : P ζ₀ ∈ (chartAt ℂ x).source := by rw [hPζ₀]; exact (chartAt ℂ x).map_target hz₀t
  obtain ⟨V₀, hV₀o, hζV₀, hV₀Ω, hV₀s, hψ₀⟩ := s36a_conf_chart hPe x hζ₀ hx0
  have hx1 : P (G ζ₀) ∈ (chartAt ℂ (h x)).source := by
    rw [← hh ζ₀ hζ₀, hPζ₀]
    exact hz₀s
  obtain ⟨V₁, hV₁o, hζV₁, -, -, hψ₁⟩ := s36a_conf_chart hPe (h x) (hGΩ ζ₀ hζ₀) hx1
  set ψ₀ : ℂ → ℂ := fun v => chartAt ℂ x (P v) with hψ₀def
  have hGcont : Continuous G := continuousOn_univ.1 hGK.2.2.1.1
  set V : Set ℂ := V₀ ∩ G ⁻¹' V₁ with hVdef
  have hVo : IsOpen V := hV₀o.inter (hV₁o.preimage hGcont)
  have hζV : ζ₀ ∈ V := ⟨hζV₀, hζV₁⟩
  have h1 := thm7_2_inv (ac_t_isKQC_restrict hψ₀ hVo inter_subset_left)
  have hinvV : ∀ w ∈ ψ₀ '' V, Function.invFunOn ψ₀ V w ∈ V ∧ ψ₀ (Function.invFunOn ψ₀ V w) = w := by
    rintro w ⟨v, hv, rfl⟩
    exact ⟨Function.invFunOn_mem ⟨v, hv, rfl⟩, Function.invFunOn_eq ⟨v, hv, rfl⟩⟩
  have h2 := thm7_1_comp h1 hGK (subset_univ _)
  have h3 := thm7_1_comp h2 hψ₁ (by
    rintro _ ⟨w, hw, rfl⟩
    exact (hinvV w hw).1.2)
  rw [one_mul, mul_one] at h3
  set W : Set ℂ := ψ₀ '' V ∩ localMapDomain h x with hWdef
  have hWo : IsOpen W := h1.1.inter (s23_localMapDomain_isOpen h.continuous x)
  have hz₀W : z₀ ∈ W := by
    refine ⟨⟨ζ₀, hζV, ?_⟩, hz₀t, hz₀s⟩
    show chartAt ℂ x (P ζ₀) = z₀
    rw [hPζ₀, (chartAt ℂ x).right_inv hz₀t]
  refine ⟨W, hWo, hz₀W, inter_subset_right,
    ad_isKQC_congr (ac_t_isKQC_restrict h3 hWo inter_subset_left) fun w hw => ?_⟩
  obtain ⟨hvV, hvw⟩ := hinvV w hw.1
  set v := Function.invFunOn ψ₀ V w with hv
  have hPv : (chartAt ℂ x).symm w = P v := by
    rw [← hvw]
    exact (chartAt ℂ x).left_inv (hV₀s v hvV.1)
  simp only [Function.comp_apply]
  unfold localMapExpr
  rw [hPv, hh v (hV₀Ω hvV.1)]

/-- `G' = (f^μ)⁻¹ ∘ f^ν` inverts `G = (f^ν)⁻¹ ∘ f^μ` on `ℂ`. -/
theorem s36a_gt_inv (μ ν : BeltramiGamma Γ) :
    ∀ z, (Function.invFunOn (fMuSym μ.1.1) univ ∘ fMuSym ν.1.1)
      ((Function.invFunOn (fMuSym ν.1.1) univ ∘ fMuSym μ.1.1) z) = z := by
  obtain ⟨hNν, -, -⟩ := c36_c_fMuSym_spec ν.1 (c36_c_normH_lt_one ν.1) le_rfl
  obtain ⟨hNμ, -, -⟩ := c36_c_fMuSym_spec μ.1 (c36_c_normH_lt_one μ.1) le_rfl
  obtain ⟨-, hfs, -, -⟩ := hNν
  obtain ⟨hKμ, -, -, -⟩ := hNμ
  have hμi : Function.Injective (fMuSym μ.1.1) := Set.injOn_univ.1 hKμ.2.2.1.2.1
  intro z
  have h1 : fMuSym ν.1.1 (Function.invFunOn (fMuSym ν.1.1) univ (fMuSym μ.1.1 z)) = fMuSym μ.1.1 z := by
    have : fMuSym μ.1.1 z ∈ fMuSym ν.1.1 '' univ := by rw [hfs]; trivial
    obtain ⟨y, -, hy⟩ := this
    exact Function.invFunOn_eq ⟨y, mem_univ _, hy⟩
  show Function.invFunOn (fMuSym μ.1.1) univ
    (fMuSym ν.1.1 (Function.invFunOn (fMuSym ν.1.1) univ (fMuSym μ.1.1 z))) = z
  rw [h1]
  exact hμi (Function.invFunOn_eq ⟨z, mem_univ _, rfl⟩)

/-- **The descended map and homotopy.**  `G` descends to a q.c. homeomorphism `h` of `S` homotopic to the identity
(the reflected geodesic homotopy from `G` to `id`). -/
theorem s36a_h {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [IsManifold 𝓘(ℂ) ω S]
    {Ω : Set ℂ} (hΩH : ∀ z : ℂ, z.im ≠ 0 → z ∈ Ω) (hΩc : ∀ z ∈ Ω, conj z ∈ Ω)
    (hΩΓ : ∀ γ ∈ Γ, ∀ z ∈ Ω, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 ∧ h36p_m γ z ∈ Ω)
    {P : ℂ → S} (hPs : P '' Ω = univ) (hPf : ∀ z ∈ Ω, ∀ w ∈ Ω, (P z = P w ↔ ∃ γ ∈ Γ, w = h36p_m γ z))
    (hPe : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    (μ ν : BeltramiGamma Γ) (hrel : teichSetoidGamma Γ ν μ) :
    ∃ h : S ≃ₜ S, IsQCRS h ∧ ContinuousMap.Homotopic (h : C(S, S)) (ContinuousMap.id S) ∧
      ∀ z ∈ Ω, h (P z) = P ((Function.invFunOn (fMuSym ν.1.1) univ ∘ fMuSym μ.1.1) z) := by
  classical
  have _hΩc := hΩc
  have hPe3 : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source :=
    fun z hz => by
      obtain ⟨e, h1, h2, h3, -⟩ := hPe z hz
      exact ⟨e, h1, h2, h3⟩
  have hreal_m : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ), z.im = 0 → (h36p_m γ z).im = 0 := by
    intro γ z hz
    have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hz])
    rw [hz']
    show (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) ((z.re : ℝ) : ℂ)).im = 0
    rw [b33_e_mobius_real]
    exact Complex.ofReal_im _
  -- the homotopy for a map `G` of the type of `s36a_gt`, descended
  have hdesc : ∀ μ' ν' : BeltramiGamma Γ, teichSetoidGamma Γ ν' μ' →
      ∃ φ : S × unitInterval → S, Continuous φ ∧
        (∀ z ∈ Ω, φ (P z, 0) = P ((Function.invFunOn (fMuSym ν'.1.1) univ ∘ fMuSym μ'.1.1) z)) ∧
        ∀ z ∈ Ω, φ (P z, 1) = P z := by
    intro μ' ν' hrel'
    obtain ⟨K, hGK, -, -, hGr, hGc, hGH, hGΓ⟩ := s36a_gt μ' ν' hrel'
    set G := Function.invFunOn (fMuSym ν'.1.1) univ ∘ fMuSym μ'.1.1 with hGdef
    have hGcont : Continuous G := continuousOn_univ.1 hGK.2.2.1.1
    obtain ⟨H, hHc, hH0, hH1, hHpos, hHneg, hHreal, hHΓ⟩ := s36a_geodH hGcont hGH hGc hGr hGΓ
    have hHΩ : ∀ z ∈ Ω, ∀ t, H (z, t) ∈ Ω := by
      intro z hz t
      rcases lt_trichotomy z.im 0 with hlt | heq | hgt
      · exact hΩH _ (ne_of_lt (hHneg z t hlt))
      · rw [hHreal z t heq]; exact hz
      · exact hΩH _ (ne_of_gt (hHpos z t hgt))
    have hcomp : ∀ z ∈ Ω, ∀ w ∈ Ω, P z = P w → ∀ t, P (H (z, t)) = P (H (w, t)) := by
      intro z hz w hw hzw t
      obtain ⟨γ, hγ, rfl⟩ := (hPf z hz w hw).1 hzw
      by_cases him : z.im = 0
      · rw [hHreal z t him, hHreal _ t (hreal_m γ z him)]
        exact hzw
      · rw [hHΓ γ hγ z t him]
        exact (hPf _ (hHΩ z hz t) _ (hΩΓ γ hγ _ (hHΩ z hz t)).2).2 ⟨γ, hγ, rfl⟩
    obtain ⟨φ, hφc, hφ⟩ := s36a_descend (T := unitInterval) hPs hPe3 (fun z _ t => hHc.continuousAt)
      hHΩ hcomp
    exact ⟨φ, hφc, fun z hz => by rw [hφ z hz, hH0], fun z hz => by rw [hφ z hz, hH1]⟩
  obtain ⟨φ, hφc, hφ0, hφ1⟩ := hdesc μ ν hrel
  obtain ⟨φ', hφ'c, hφ'0, -⟩ := hdesc ν μ ((teichSetoidGamma Γ).iseqv.symm hrel)
  obtain ⟨K, hGK, -, -, hGr, hGc, hGH, -⟩ := s36a_gt μ ν hrel
  obtain ⟨-, hG'K, -, -, hG'r, hG'c, hG'H, -⟩ := s36a_gt ν μ ((teichSetoidGamma Γ).iseqv.symm hrel)
  set G := Function.invFunOn (fMuSym ν.1.1) univ ∘ fMuSym μ.1.1 with hGdef
  set G' := Function.invFunOn (fMuSym μ.1.1) univ ∘ fMuSym ν.1.1 with hG'def
  have hGG' : ∀ z, G (G' z) = z := s36a_gt_inv ν μ
  have hG'G : ∀ z, G' (G z) = z := s36a_gt_inv μ ν
  have hΩmap : ∀ (F : ℂ → ℂ), (∀ z ∈ upperHalf, F z ∈ upperHalf) → (∀ z, F (conj z) = conj (F z)) →
      (∀ x : ℝ, F (x : ℂ) = x) → ∀ z ∈ Ω, F z ∈ Ω := by
    intro F hFH hFc hFr z hz
    rcases lt_trichotomy z.im 0 with hlt | heq | hgt
    · have hcz : conj z ∈ upperHalf := by
        show 0 < (conj z).im
        rw [Complex.conj_im]
        linarith
      have h1 : 0 < (F (conj z)).im := hFH _ hcz
      rw [hFc, Complex.conj_im] at h1
      exact hΩH _ (by linarith)
    · have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [heq])
      rw [hz', hFr, ← hz']
      exact hz
    · exact hΩH _ (ne_of_gt (hFH z hgt))
  have hGΩ := hΩmap G hGH hGc hGr
  have hG'Ω := hΩmap G' hG'H hG'c hG'r
  have hsurj : ∀ s : S, ∃ z ∈ Ω, P z = s := fun s => by
    have : s ∈ P '' Ω := by rw [hPs]; trivial
    obtain ⟨z, hz, h⟩ := this
    exact ⟨z, hz, h⟩
  set h₀ : S → S := fun s => φ (s, 0) with hh₀
  set h₁ : S → S := fun s => φ' (s, 0) with hh₁
  have hh₀P : ∀ z ∈ Ω, h₀ (P z) = P (G z) := hφ0
  have hh₁P : ∀ z ∈ Ω, h₁ (P z) = P (G' z) := hφ'0
  let h : S ≃ₜ S :=
    { toFun := h₀
      invFun := h₁
      left_inv := fun s => by
        obtain ⟨z, hz, rfl⟩ := hsurj s
        rw [hh₀P z hz, hh₁P _ (hGΩ z hz), hG'G]
      right_inv := fun s => by
        obtain ⟨z, hz, rfl⟩ := hsurj s
        rw [hh₁P z hz, hh₀P _ (hG'Ω z hz), hGG']
      continuous_toFun := hφc.comp (continuous_id.prodMk continuous_const)
      continuous_invFun := hφ'c.comp (continuous_id.prodMk continuous_const) }
  have hhP : ∀ z ∈ Ω, h (P z) = P (G z) := hh₀P
  refine ⟨h, ⟨K, s36a_hqc hPs hPe hGK hGΩ h hhP⟩, ⟨?_⟩, hhP⟩
  exact
    { toFun := fun x => φ (x.2, x.1)
      continuous_toFun := hφc.comp (continuous_snd.prodMk continuous_fst)
      map_zero_left := fun s => rfl
      map_one_left := fun s => by
        obtain ⟨z, hz, rfl⟩ := hsurj s
        exact hφ1 z hz }

/-! ### Step A (c): descent of `ψ` through `P` -/

/-- **Local chart expression of `P`.**  Near `z ∈ Ω` with `P z` in the chart source at `x`, `H = φ_x ∘ P` is a
local biholomorphism: it has a non-vanishing derivative on an open `U ∋ z`, and a holomorphic local inverse `L`
with `L (H z) = z` and `L w ∈ U`, `H (L w) = w` near `H z`. -/
theorem s36a_Hloc {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    {Ω : Set ℂ} {P : ℂ → S}
    (hPe : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    (x : S) {z : ℂ} (hz : z ∈ Ω) (hx : P z ∈ (chartAt ℂ x).source) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ Ω ∧ (∀ w ∈ U, P w ∈ (chartAt ℂ x).source ∧
        HasDerivAt (fun v => chartAt ℂ x (P v)) (deriv (fun v => chartAt ℂ x (P v)) w) w ∧
        deriv (fun v => chartAt ℂ x (P v)) w ≠ 0) ∧
      ∃ L : ℂ → ℂ, L (chartAt ℂ x (P z)) = z ∧ DifferentiableAt ℂ L (chartAt ℂ x (P z)) ∧
        (∀ w ∈ U, L (chartAt ℂ x (P w)) = w) ∧
        ∀ᶠ w' in 𝓝 (chartAt ℂ x (P z)), L w' ∈ U ∧ chartAt ℂ x (P (L w')) = w' := by
  obtain ⟨e, hze, heΩ, hPe', hed, hesd⟩ := hPe z hz
  set H : ℂ → ℂ := fun v => chartAt ℂ x (P v) with hHdef
  set U : Set ℂ := e.source ∩ e ⁻¹' (chartAt ℂ x).source with hUdef
  have hUo : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source (chartAt ℂ x).open_source
  have hPU : ∀ w ∈ U, P w = e w := fun w hw => hPe' hw.1
  have hxs : ∀ w ∈ U, P w ∈ (chartAt ℂ x).source := fun w hw => by rw [hPU w hw]; exact hw.2
  have hzU : z ∈ U := ⟨hze, by show e z ∈ (chartAt ℂ x).source; rw [← hPe' hze]; exact hx⟩
  have hHd : ∀ w ∈ U, DifferentiableAt ℂ H w := by
    intro w hw
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun v => chartAt ℂ x (e v)) w :=
      (mdifferentiableAt_atlas (chart_mem_atlas ℂ x) hw.2).comp w
        ((hed w hw.1).mdifferentiableAt (e.open_source.mem_nhds hw.1))
    have hev : H =ᶠ[𝓝 w] (fun v => chartAt ℂ x (e v)) :=
      Filter.eventuallyEq_of_mem (hUo.mem_nhds hw) fun v hv => by simp only [hHdef, hPU v hv]
    exact (mdifferentiableAt_iff_differentiableAt.1 h1).congr_of_eventuallyEq hev
  set L : ℂ → ℂ := fun w' => e.symm ((chartAt ℂ x).symm w') with hLdef
  have hHt : ∀ w ∈ U, H w ∈ (chartAt ℂ x).target := fun w hw => (chartAt ℂ x).map_source (hxs w hw)
  have hsH : ∀ w ∈ U, (chartAt ℂ x).symm (H w) = e w := fun w hw => by
    show (chartAt ℂ x).symm (chartAt ℂ x (P w)) = e w
    rw [(chartAt ℂ x).left_inv (hxs w hw), hPU w hw]
  have hLH : ∀ w ∈ U, L (H w) = w := fun w hw => by
    show e.symm ((chartAt ℂ x).symm (H w)) = w
    rw [hsH w hw, e.left_inv hw.1]
  have hLd : ∀ w ∈ U, DifferentiableAt ℂ L (H w) := by
    intro w hw
    have het : e w ∈ e.target := e.map_source hw.1
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun w' => e.symm ((chartAt ℂ x).symm w')) (H w) := by
      have hc : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x).symm (H w) :=
        mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ x) (hHt w hw)
      have he := (hesd ((chartAt ℂ x).symm (H w)) (by rw [hsH w hw]; exact het)).mdifferentiableAt
        (e.open_target.mem_nhds (by rw [hsH w hw]; exact het))
      exact he.comp (H w) hc
    exact mdifferentiableAt_iff_differentiableAt.1 h1
  have hne : ∀ w ∈ U, deriv H w ≠ 0 := by
    intro w hw
    have h1 : HasDerivAt (L ∘ H) (deriv L (H w) * deriv H w) w :=
      (hLd w hw).hasDerivAt.comp w (hHd w hw).hasDerivAt
    have hev : (L ∘ H) =ᶠ[𝓝 w] id :=
      Filter.eventuallyEq_of_mem (hUo.mem_nhds hw) fun v hv => hLH v hv
    have h2 : HasDerivAt (L ∘ H) 1 w := (hasDerivAt_id w).congr_of_eventuallyEq hev
    have h3 := h1.unique h2
    intro h0
    rw [h0, mul_zero] at h3
    exact zero_ne_one h3
  refine ⟨U, hUo, hzU, fun w hw => heΩ hw.1, fun w hw => ⟨hxs w hw, (hHd w hw).hasDerivAt, hne w hw⟩,
    L, hLH z hzU, hLd z hzU, hLH, ?_⟩
  have hHz : H z ∈ (chartAt ℂ x).target := hHt z hzU
  have hsz : (chartAt ℂ x).symm (H z) ∈ e.target := by rw [hsH z hzU]; exact e.map_source hze
  have hev1 : ∀ᶠ w' in 𝓝 (H z), w' ∈ (chartAt ℂ x).target := (chartAt ℂ x).open_target.mem_nhds hHz
  have hev2 : ∀ᶠ w' in 𝓝 (H z), (chartAt ℂ x).symm w' ∈ e.target :=
    ((chartAt ℂ x).continuousAt_symm hHz).preimage_mem_nhds (e.open_target.mem_nhds hsz)
  filter_upwards [hev1, hev2] with w' h1 h2
  have hLs : L w' ∈ e.source := e.map_target h2
  have heL : e (L w') = (chartAt ℂ x).symm w' := e.right_inv h2
  have hLU : L w' ∈ U := ⟨hLs, by show e (L w') ∈ (chartAt ℂ x).source; rw [heL]; exact (chartAt ℂ x).map_target h1⟩
  refine ⟨hLU, ?_⟩
  show chartAt ℂ x (P (L w')) = w'
  rw [hPU _ hLU, heL, (chartAt ℂ x).right_inv h1]

/-- **Independence of the lift**: `ψ(γ w) / H'(γ w)² = ψ(w) / H'(w)²` for `γ ∈ Γ`, `H = φ_x ∘ P` (`H ∘ γ = H` near
`w`, `γ'(w) = (c w + d)⁻²` and `ψ(γ w) = ψ(w) (c w + d)⁴`). -/
theorem s36a_quot_inv {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩΓ : ∀ γ ∈ Γ, ∀ z ∈ Ω, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 ∧ h36p_m γ z ∈ Ω)
    {P : ℂ → S} (hPf : ∀ z ∈ Ω, ∀ w ∈ Ω, (P z = P w ↔ ∃ γ ∈ Γ, w = h36p_m γ z))
    (hPe : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    {ψ : ℂ → ℂ} (hψΓ : ∀ γ ∈ Γ, ∀ z ∈ Ω, ψ (h36p_m γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = ψ z)
    (x : S) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {w : ℂ} (hw : w ∈ Ω)
    (hx : P w ∈ (chartAt ℂ x).source) :
    ψ (h36p_m γ w) / deriv (fun v => chartAt ℂ x (P v)) (h36p_m γ w) ^ 2 =
      ψ w / deriv (fun v => chartAt ℂ x (P v)) w ^ 2 := by
  set H : ℂ → ℂ := fun v => chartAt ℂ x (P v) with hHdef
  obtain ⟨hden, hγw⟩ := hΩΓ γ hγ w hw
  have hPγ : ∀ v ∈ Ω, P (h36p_m γ v) = P v := fun v hv =>
    ((hPf v hv _ (hΩΓ γ hγ v hv).2).2 ⟨γ, hγ, rfl⟩).symm
  have hxγ : P (h36p_m γ w) ∈ (chartAt ℂ x).source := by rw [hPγ w hw]; exact hx
  obtain ⟨U, -, hγwU, -, hU, -⟩ := s36a_Hloc hPe x hγw hxγ
  have hmob : HasDerivAt (h36p_m γ) (1 / ((γ 1 0 : ℂ) * w + γ 1 1) ^ 2) w := utm_b_hasDerivAt_mob γ hden
  have hcomp : HasDerivAt (H ∘ h36p_m γ) (deriv H (h36p_m γ w) * (1 / ((γ 1 0 : ℂ) * w + γ 1 1) ^ 2)) w :=
    (hU _ hγwU).2.1.comp w hmob
  have hev : H =ᶠ[𝓝 w] (H ∘ h36p_m γ) :=
    Filter.eventuallyEq_of_mem (hΩo.mem_nhds hw) fun v hv => by
      simp only [Function.comp_apply, hHdef, hPγ v hv]
  have hderiv : deriv H w = deriv H (h36p_m γ w) * (1 / ((γ 1 0 : ℂ) * w + γ 1 1) ^ 2) :=
    (hcomp.congr_of_eventuallyEq hev).deriv
  have hψ' : ψ (h36p_m γ w) = ψ w * ((γ 1 0 : ℂ) * w + γ 1 1) ^ 4 := by
    have h := hψΓ γ hγ w hw
    rw [div_eq_iff (pow_ne_zero 4 hden)] at h
    exact h
  have hne := (hU _ hγwU).2.2
  rw [hderiv, hψ']
  field_simp

/-- **Descent of `ψ`** to a holomorphic quadratic differential `q` on `S` with `P^* q = ψ` on `Ω`. -/
theorem s36a_q {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [IsManifold 𝓘(ℂ) ω S]
    {Ω : Set ℂ} (hΩΓ : ∀ γ ∈ Γ, ∀ z ∈ Ω, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 ∧ h36p_m γ z ∈ Ω)
    {P : ℂ → S} (hPs : P '' Ω = univ) (hPf : ∀ z ∈ Ω, ∀ w ∈ Ω, (P z = P w ↔ ∃ γ ∈ Γ, w = h36p_m γ z))
    (hPe : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    {ψ : ℂ → ℂ} (hψd : DifferentiableOn ℂ ψ Ω)
    (hψΓ : ∀ γ ∈ Γ, ∀ z ∈ Ω, ψ (h36p_m γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = ψ z) :
    ∃ q : S → ℂ → ℂ, IsHolQuadDiff q ∧ ∀ z ∈ Ω, ∀ x : S, P z ∈ (chartAt ℂ x).source →
      DifferentiableAt ℂ (fun w => chartAt ℂ x (P w)) z ∧
      ψ z = q x (chartAt ℂ x (P z)) * deriv (fun w => chartAt ℂ x (P w)) z ^ 2 := by
  classical
  have hΩo : IsOpen Ω := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨e, hze, hes, -⟩ := hPe z hz
    exact Filter.mem_of_superset (e.open_source.mem_nhds hze) hes
  have hsec : ∀ s : S, ∃ z ∈ Ω, P z = s := fun s => by
    have : s ∈ P '' Ω := by rw [hPs]; trivial
    obtain ⟨z, hz, h⟩ := this
    exact ⟨z, hz, h⟩
  choose sec hsecΩ hsecP using hsec
  set q : S → ℂ → ℂ := fun x => (chartAt ℂ x).target.indicator fun w =>
    ψ (sec ((chartAt ℂ x).symm w)) / deriv (fun v => chartAt ℂ x (P v)) (sec ((chartAt ℂ x).symm w)) ^ 2
    with hqdef
  -- the value at a lifted point
  have happ : ∀ (x : S) (τ : ℂ), τ ∈ Ω → P τ ∈ (chartAt ℂ x).source →
      q x (chartAt ℂ x (P τ)) = ψ τ / deriv (fun v => chartAt ℂ x (P v)) τ ^ 2 := by
    intro x τ hτ hx
    have ht : chartAt ℂ x (P τ) ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hx
    have hs : (chartAt ℂ x).symm (chartAt ℂ x (P τ)) = P τ := (chartAt ℂ x).left_inv hx
    simp only [hqdef]
    rw [indicator_of_mem ht, hs]
    obtain ⟨γ, hγ, hγτ⟩ := (hPf τ hτ _ (hsecΩ (P τ))).1 (hsecP (P τ)).symm
    rw [hγτ]
    exact s36a_quot_inv hΩo hΩΓ hPf hPe hψΓ x hγ hτ hx
  -- the transformation law
  have hD : IsDiffFamily 2 0 q := by
    refine ⟨fun x w hw => ?_, fun x y w hw hwx => ?_⟩
    · simp only [hqdef]
      rw [indicator_of_notMem hw]
    · obtain ⟨τ, hτΩ, hpτ⟩ := (show (chartAt ℂ y).symm w ∈ P '' Ω by rw [hPs]; trivial)
      have hsy : (chartAt ℂ y).symm w ∈ (chartAt ℂ y).source := (chartAt ℂ y).map_target hw
      have hwy : chartAt ℂ y (P τ) = w := by
        rw [hpτ]
        exact (chartAt ℂ y).right_inv hw
      have hTw : chartTransition x y w = chartAt ℂ x (P τ) := by
        unfold chartTransition
        rw [hpτ]
      have hKy := happ y τ hτΩ (by rw [hpτ]; exact hsy)
      have hKx := happ x τ hτΩ (by rw [hpτ]; exact hwx)
      rw [hwy] at hKy
      rw [hTw, hKx, hKy]
      obtain ⟨hTd, -⟩ := s23_transition x y hw hwx
      obtain ⟨Uy, hUyo, hτUy, -, hUy, -⟩ := s36a_Hloc hPe y hτΩ (by rw [hpτ]; exact hsy)
      have hyd : DifferentiableAt ℂ (fun v => chartAt ℂ y (P v)) τ := (hUy τ hτUy).2.1.differentiableAt
      have hev : (fun v => chartAt ℂ x (P v)) =ᶠ[𝓝 τ] chartTransition x y ∘ fun v => chartAt ℂ y (P v) := by
        filter_upwards [hUyo.mem_nhds hτUy] with v hv
        show chartAt ℂ x (P v) = chartAt ℂ x ((chartAt ℂ y).symm (chartAt ℂ y (P v)))
        rw [(chartAt ℂ y).left_inv (hUy v hv).1]
      have hyτ : (fun v => chartAt ℂ y (P v)) τ = w := hwy
      have hder : deriv (fun v => chartAt ℂ x (P v)) τ =
          deriv (chartTransition x y) w * deriv (fun v => chartAt ℂ y (P v)) τ := by
        rw [hev.deriv_eq]
        rw [← hyτ] at hTd ⊢
        exact (hTd.hasDerivAt.comp τ hyd.hasDerivAt).deriv
      rw [hder]
      have hne := (hUy τ hτUy).2.2
      obtain ⟨-, hTne⟩ := s23_transition x y hw hwx
      norm_num
      field_simp
  -- holomorphy on the chart targets
  have hH : ∀ x : S, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := by
    intro x w hw
    obtain ⟨τ, hτΩ, hpτ⟩ := (show (chartAt ℂ x).symm w ∈ P '' Ω by rw [hPs]; trivial)
    have hsx : (chartAt ℂ x).symm w ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hw
    have hxτ : P τ ∈ (chartAt ℂ x).source := by rw [hpτ]; exact hsx
    have hHτ : chartAt ℂ x (P τ) = w := by rw [hpτ]; exact (chartAt ℂ x).right_inv hw
    obtain ⟨U, hUo, hτU, hUΩ, hU, L, hLτ, hLd, -, hLev⟩ := s36a_Hloc hPe x hτΩ hxτ
    rw [hHτ] at hLτ hLd hLev
    have hev2 : ∀ᶠ w' in 𝓝 w, q x w' = ψ (L w') / deriv (fun v => chartAt ℂ x (P v)) (L w') ^ 2 := by
      filter_upwards [hLev] with w' hw'
      obtain ⟨hLU, hHL⟩ := hw'
      have h := happ x (L w') (hUΩ hLU) (hU _ hLU).1
      rw [hHL] at h
      exact h
    have hψd' : DifferentiableAt ℂ ψ (L w) := by
      rw [hLτ]
      exact hψd.differentiableAt (hΩo.mem_nhds hτΩ)
    have hdd : DifferentiableAt ℂ (deriv (fun v => chartAt ℂ x (P v))) (L w) := by
      rw [hLτ]
      have hdiffU : DifferentiableOn ℂ (fun v => chartAt ℂ x (P v)) U := fun v hv =>
        (hU v hv).2.1.differentiableAt.differentiableWithinAt
      exact (hdiffU.deriv hUo).differentiableAt (hUo.mem_nhds hτU)
    have hne : deriv (fun v => chartAt ℂ x (P v)) (L w) ^ 2 ≠ 0 := by
      rw [hLτ]
      exact pow_ne_zero 2 (hU τ hτU).2.2
    have hdiff : DifferentiableAt ℂ
        (fun w' => ψ (L w') / deriv (fun v => chartAt ℂ x (P v)) (L w') ^ 2) w :=
      (hψd'.comp w hLd).div ((hdd.comp w hLd).pow 2) hne
    exact (hdiff.congr_of_eventuallyEq hev2).differentiableWithinAt
  have hq : IsHolQuadDiff q :=
    (⟨hD, hH⟩ : IsDiffFamily 2 0 q ∧ ∀ x : S, DifferentiableOn ℂ (q x) (chartAt ℂ x).target)
  refine ⟨q, hq, fun z hz x hx => ?_⟩
  obtain ⟨U, -, hzU, -, hU, -⟩ := s36a_Hloc hPe x hz hx
  refine ⟨(hU z hzU).2.1.differentiableAt, ?_⟩
  rw [happ x z hz hx]
  exact (div_mul_cancel₀ _ (pow_ne_zero 2 (hU z hzU).2.2)).symm

/-- **(T4') The stretching function of `h` at `P z` is `λ(ψ, G)(z)`** (the proof of `str_lambda` with the local
sheets of `P`). -/
theorem s36a_T4 {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [IsManifold 𝓘(ℂ) ω S]
    {Ω : Set ℂ} (hΩo : IsOpen Ω) {P : ℂ → S}
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) {ψ : ℂ → ℂ}
    (hqψ : ∀ z ∈ Ω, ∀ x : S, P z ∈ (chartAt ℂ x).source →
      DifferentiableAt ℂ (fun w => chartAt ℂ x (P w)) z ∧
      ψ z = q x (chartAt ℂ x (P z)) * deriv (fun w => chartAt ℂ x (P w)) z ^ 2)
    (hPe : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    {G : ℂ → ℂ} (hGc : Continuous G) (hGΩ : ∀ z ∈ Ω, G z ∈ Ω) (h : S ≃ₜ S)
    (hh : ∀ z ∈ Ω, h (P z) = P (G z)) {z : ℂ} (hz : z ∈ Ω) :
    s26v_lam q h (P z) = ENNReal.ofReal (lambdaStretchPlane ψ ψ G z) := by
  have _hq := hq
  have hGz : G z ∈ Ω := hGΩ z hz
  set s := P z with hs
  have hpe' : P (G z) = h s := (hh z hz).symm
  obtain ⟨U0, hU0o, hzU0, hU0Ω, hU0, k0, hk0z, hk0d, hk0H, hHk0⟩ :=
    s36a_Hloc hPe s hz (mem_chart_source ℂ s)
  obtain ⟨U1, hU1o, hzU1, hU1Ω, hU1, k1, hk1z, hk1d, hk1H, -⟩ :=
    s36a_Hloc hPe (h s) hGz (by rw [hpe']; exact mem_chart_source ℂ (h s))
  set H : ℂ → ℂ := fun v => chartAt ℂ s (P v) with hH
  set ψ₁ : ℂ → ℂ := fun v => chartAt ℂ (h s) (P v) with hψ₁
  have hHz : H z = chartAt ℂ s s := rfl
  have hψz : ψ₁ (G z) = chartAt ℂ (h s) (h s) := by simp only [hψ₁, hpe']
  set a : ℂ := deriv H z with ha
  set b : ℂ := deriv ψ₁ (G z) with hb
  set L : ℂ → ℂ := localMapExprAt h s (chartAt ℂ s s) with hL
  have hev : (L ∘ H) =ᶠ[𝓝 z] (ψ₁ ∘ G) := by
    filter_upwards [hU0o.mem_nhds hzU0] with v hv
    simp only [Function.comp_apply, hL, localMapExprAt, hH, hψ₁]
    rw [(chartAt ℂ s).left_inv (mem_chart_source ℂ s), (chartAt ℂ s).left_inv (hU0 v hv).1,
      hh v (hU0Ω hv)]
  have hLz : L (chartAt ℂ s s) = chartAt ℂ (h s) (h s) := by
    have := hev.self_of_nhds
    simp only [Function.comp_apply] at this
    rw [← hHz, this, hψz]
  have hd0 : DifferentiableAt ℂ H z := (hU0 z hzU0).2.1.differentiableAt
  have hd1 : DifferentiableAt ℂ ψ₁ (G z) := (hU1 (G z) hzU1).2.1.differentiableAt
  have hk0H' : ∀ᶠ w in 𝓝 z, k0 (H w) = w :=
    Filter.eventually_of_mem (hU0o.mem_nhds hzU0) fun w hw => hk0H w hw
  have hHk0' : ∀ᶠ u in 𝓝 (H z), H (k0 u) = u := hHk0.mono fun _ h => h.2
  have hk1H' : ∀ᶠ w in 𝓝 (G z), k1 (ψ₁ w) = w :=
    Filter.eventually_of_mem (hU1o.mem_nhds hzU1) fun w hw => hk1H w hw
  have hgc : ContinuousAt G z := hGc.continuousAt
  obtain ⟨hdzR, hdzbarR⟩ := s23_wirtinger_comp_right (g := L) (T := H) (S := k0) hd0 hk0d hk0H' hHk0'
  obtain ⟨hdzL, hdzbarL⟩ := s23_wirtinger_comp_left (g := G) (h := ψ₁) (k := k1) hgc hd1
    (by rw [show ψ₁ (G z) = chartAt ℂ (h s) (P (G z)) from rfl]; exact hk1d) hk1H'
  have e1 : dz L (chartAt ℂ s s) * a = b * dz G z := by
    have h1 : dz (L ∘ H) z = dz (ψ₁ ∘ G) z := by simp only [dz, hev.fderiv_eq]
    rw [hdzR, hdzL, hHz] at h1
    exact h1
  have e2 : dzbar L (chartAt ℂ s s) * conj a = b * dzbar G z := by
    have h1 : dzbar (L ∘ H) z = dzbar (ψ₁ ∘ G) z := by simp only [dzbar, hev.fderiv_eq]
    rw [hdzbarR, hdzbarL, hHz] at h1
    exact h1
  have ha0 : a ≠ 0 := (hU0 z hzU0).2.2
  have hQ : ψ z = q s (chartAt ℂ s s) * a ^ 2 := (hqψ z hz s (mem_chart_source ℂ s)).2
  have hQ' : ψ (G z) = q (h s) (chartAt ℂ (h s) (h s)) * b ^ 2 := by
    have := (hqψ (G z) hGz (h s) (by rw [hpe']; exact mem_chart_source ℂ (h s))).2
    rw [this, hpe']
  have hlam : lambdaStretch q q h s (chartAt ℂ s s) =
      lambdaStretchPlane (q s) (q (h s)) L (chartAt ℂ s s) := by
    simp only [lambdaStretch, hL, (chartAt ℂ s).left_inv (mem_chart_source ℂ s)]
  show ENNReal.ofReal (lambdaStretch q q h s (chartAt ℂ s s)) = _
  congr 1
  rw [hlam]
  unfold lambdaStretchPlane
  rw [hLz]
  have halg := s26v_b_lambdaPlane_alg (dz L (chartAt ℂ s s)) (dzbar L (chartAt ℂ s s))
    (q s (chartAt ℂ s s)) a ha0 (Real.sqrt ‖q (h s) (chartAt ℂ (h s) (h s))‖)
  rw [← halg, ← hQ, e1, e2]
  have hfac : b * dz G z + b * dzbar G z * (ψ z / ((‖ψ z‖ : ℝ) : ℂ)) =
      b * (dz G z + dzbar G z * (ψ z / ((‖ψ z‖ : ℝ) : ℂ))) := by ring
  rw [hfac, norm_mul]
  have hsq : Real.sqrt ‖ψ (G z)‖ = Real.sqrt ‖q (h s) (chartAt ℂ (h s) (h s))‖ * ‖b‖ := by
    rw [hQ', norm_mul, norm_pow, Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rw [hsq]
  ring

/-! ### Step A (d): surface integrals on `Ω/Γ` as integrals over `F ∪ conj F` -/

/-- `S = P(Ω)` is Lindelöf. -/
theorem s36a_lindelof {S : Type} [TopologicalSpace S] {Ω : Set ℂ} {P : ℂ → S} (hPs : P '' Ω = univ)
    (hPe : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source) :
    IsLindelof (univ : Set S) := by
  rw [← hPs]
  exact (HereditarilyLindelofSpace.isLindelof Ω).image_of_continuousOn
    fun z hz => (s36a_Pcont hPe z hz).continuousWithinAt

/-- **(T3') Surface integrals through `P`**: for a chart-invariant integrand, the surface integral against `|q|` is
the integral over `F ∪ conj F`, written as two integrals over `F`. -/
theorem s36a_T3 {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [IsManifold 𝓘(ℂ) ω S]
    [MeasurableSpace S] [BorelSpace S] (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F)
    {Ω : Set ℂ} (hΩH : ∀ z : ℂ, z.im ≠ 0 → z ∈ Ω) (hΩc : ∀ z ∈ Ω, conj z ∈ Ω)
    (hΩΓ : ∀ γ ∈ Γ, ∀ z ∈ Ω, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 ∧ h36p_m γ z ∈ Ω)
    {P : ℂ → S} (hPs : P '' Ω = univ) (hPf : ∀ z ∈ Ω, ∀ w ∈ Ω, (P z = P w ↔ ∃ γ ∈ Γ, w = h36p_m γ z))
    (hPe : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    {ψ : ℂ → ℂ} (hψd : DifferentiableOn ℂ ψ Ω)
    (hψΓ : ∀ γ ∈ Γ, ∀ z ∈ Ω, ψ (h36p_m γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = ψ z)
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q)
    (hqψ : ∀ z ∈ Ω, ∀ x : S, P z ∈ (chartAt ℂ x).source →
      DifferentiableAt ℂ (fun w => chartAt ℂ x (P w)) z ∧
      ψ z = q x (chartAt ℂ x (P z)) * deriv (fun w => chartAt ℂ x (P w)) z ^ 2)
    {U : S → ℝ≥0∞} (hU : Measurable U) :
    surfaceIntegral q (fun y z => U ((chartAt ℂ y).symm z)) =
      (∫⁻ z in F, U (P z) * ENNReal.ofReal ‖ψ z‖) +
        ∫⁻ z in F, U (P (conj z)) * ENNReal.ofReal ‖conj (ψ (conj z))‖ := by
  classical
  obtain ⟨S', _, _, _, _, _, p', hp'⟩ := ft0_quotient hΓ hfree
  letI : MeasurableSpace S' := borel S'
  haveI : BorelSpace S' := ⟨rfl⟩
  have hFH : F ⊆ upperHalf := hF.1
  have hFm : MeasurableSet F := hF.2.1
  have hΔ : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  have hΛ : MeasurableSet lowerHalf := isOpen_lowerHalf.measurableSet
  have hPe3 : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source :=
    fun z hz => by
      obtain ⟨e, h1, h2, h3, -⟩ := hPe z hz
      exact ⟨e, h1, h2, h3⟩
  have hΩo : IsOpen Ω := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨e, hze, hes, -⟩ := hPe3 z hz
    exact Filter.mem_of_superset (e.open_source.mem_nhds hze) hes
  have hPc := s36a_Pcont hPe3
  have hIΩ : Complex.I ∈ Ω := hΩH _ (by simp)
  have hconjm : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℂ), h36p_m γ (conj w) = conj (h36p_m γ w) :=
    fun γ w => b33_e_mobius_conj γ w
  have hlow : ∀ z : ℂ, z ∈ lowerHalf ↔ conj z ∈ upperHalf := fun z => by
    show z.im < 0 ↔ 0 < (conj z).im
    rw [Complex.conj_im]
    constructor <;> intro h <;> linarith
  -- measurable versions of `P` and `ψ`
  set Pm : ℂ → S := Ω.piecewise P (fun _ => P Complex.I) with hPmdef
  have hPm : Measurable Pm := ContinuousOn.measurable_piecewise
    (fun z hz => (hPc z hz).continuousWithinAt) continuousOn_const hΩo.measurableSet
  have hPmΩ : ∀ z ∈ Ω, Pm z = P z := fun z hz => Set.piecewise_eq_of_mem _ _ _ hz
  set ψm : ℂ → ℂ := Ω.piecewise ψ (fun _ => 0) with hψmdef
  have hψm : Measurable ψm := ContinuousOn.measurable_piecewise hψd.continuousOn continuousOn_const
    hΩo.measurableSet
  have hψmΩ : ∀ z ∈ Ω, ψm z = ψ z := fun z hz => Set.piecewise_eq_of_mem _ _ _ hz
  set w : ℂ → ℝ≥0∞ := fun z => U (Pm z) * ENNReal.ofReal ‖ψm z‖ with hwdef
  have hwm : Measurable w := (hU.comp hPm).mul (ENNReal.measurable_ofReal.comp hψm.norm)
  have hwΩ : ∀ z ∈ Ω, w z = U (P z) * ENNReal.ofReal ‖ψ z‖ := fun z hz => by
    simp only [hwdef, hPmΩ z hz, hψmΩ z hz]
  set wUp : ℂ → ℝ≥0∞ := upperHalf.indicator w with hwUp
  set wLo : ℂ → ℝ≥0∞ := upperHalf.indicator (fun z => w (conj z)) with hwLo
  have hwUpm : Measurable wUp := hwm.indicator hΔ
  have hwLom : Measurable wLo := (hwm.comp Complex.continuous_conj.measurable).indicator hΔ
  -- covariance of the weights
  have hnormΓ : ∀ γ ∈ Γ, ∀ z ∈ Ω,
      ‖ψ (h36p_m γ z)‖ * ‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4 = ‖ψ z‖ := by
    intro γ hγ z hz
    have hden := (hΩΓ γ hγ z hz).1
    have h := hψΓ γ hγ z hz
    rw [← h, norm_div, norm_pow, div_eq_mul_inv, inv_pow]
  have hPγ : ∀ γ ∈ Γ, ∀ z ∈ Ω, P (h36p_m γ z) = P z := fun γ hγ z hz =>
    ((hPf z hz _ (hΩΓ γ hγ z hz).2).2 ⟨γ, hγ, rfl⟩).symm
  have hcovUp : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      wUp (h36p_m γ z) * ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) = wUp z := by
    intro γ hγ z hz
    have hzΩ : z ∈ Ω := hΩH z (ne_of_gt hz)
    have hγz := h36p_m_mem γ hz
    simp only [hwUp]
    rw [indicator_of_mem hγz, indicator_of_mem hz, hwΩ _ (hΩΓ γ hγ z hzΩ).2, hwΩ z hzΩ, hPγ γ hγ z hzΩ,
      mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _), hnormΓ γ hγ z hzΩ]
  have hcovLo : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      wLo (h36p_m γ z) * ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) = wLo z := by
    intro γ hγ z hz
    have hcz : conj z ∈ Ω := hΩc _ (hΩH z (ne_of_gt hz))
    have hγz := h36p_m_mem γ hz
    have hden' : ‖(γ 1 0 : ℂ) * conj z + γ 1 1‖ = ‖(γ 1 0 : ℂ) * z + γ 1 1‖ := by
      rw [← Complex.norm_conj]
      simp [map_add, map_mul, Complex.conj_ofReal]
    simp only [hwLo]
    rw [indicator_of_mem hγz, indicator_of_mem hz, ← hconjm, hwΩ _ (hΩΓ γ hγ _ hcz).2, hwΩ _ hcz,
      hPγ γ hγ _ hcz, mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _), ← hden', hnormΓ γ hγ _ hcz]
  -- `p'`-fibres are `Γ`-orbits
  have hpfib : ∀ a ∈ upperHalf, ∀ b ∈ upperHalf,
      s22gm_projectionExtension p' a = s22gm_projectionExtension p' b → ∃ γ ∈ Γ, b = h36p_m γ a := by
    intro a ha b hb hab
    have e1 : s22gm_projectionExtension p' a = p' ⟨a, ha⟩ := s22gm_projectionExtension_coe p' ⟨a, ha⟩
    have e2 : s22gm_projectionExtension p' b = p' ⟨b, hb⟩ := s22gm_projectionExtension_coe p' ⟨b, hb⟩
    rw [e1, e2] at hab
    obtain ⟨γ, hγ, hγab⟩ := (hp'.2.2.2 _ _).1 hab
    refine ⟨γ, hγ, ?_⟩
    have := congrArg UpperHalfPlane.coe hγab
    rw [← h36p_m_coe] at this
    exact this.symm
  have hpfib' : ∀ a ∈ upperHalf, ∀ γ ∈ Γ,
      s22gm_projectionExtension p' (h36p_m γ a) = s22gm_projectionExtension p' a := by
    intro a ha γ hγ
    have hγa := h36p_m_mem γ ha
    have e2 : s22gm_projectionExtension p' a = p' ⟨a, ha⟩ := s22gm_projectionExtension_coe p' ⟨a, ha⟩
    rw [show h36p_m γ a = ((γ • (⟨a, ha⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) from h36p_m_coe γ ⟨a, ha⟩,
      s22gm_projectionExtension_coe, e2]
    exact ((hp'.2.2.2 _ _).2 ⟨γ, hγ, rfl⟩).symm
  -- sheets and the chart partition
  have hsec : ∀ s : S, ∃ z ∈ Ω, P z = s := fun s => by
    have : s ∈ P '' Ω := by rw [hPs]; trivial
    obtain ⟨z, hz, h⟩ := this
    exact ⟨z, hz, h⟩
  choose τ hτΩ hτP using hsec
  choose E hτE hEΩ hPE hEd hEsd using fun s => hPe (τ s) (hτΩ s)
  set V : S → Set S := fun s => (chartAt ℂ s).source ∩ (E s).target with hVdef
  have hVo : ∀ s, IsOpen (V s) := fun s => (chartAt ℂ s).open_source.inter (E s).open_target
  have hVp : ∀ s, s ∈ V s := fun s =>
    ⟨mem_chart_source ℂ s, by
      have h := (E s).map_source (hτE s)
      rwa [← hPE s (hτE s), hτP s] at h⟩
  have hNe : Nonempty S := ⟨P Complex.I⟩
  have hL := s36a_lindelof hPs hPe3
  obtain ⟨x, Pc, hP, hPV, hPcm⟩ := str_exists_partition hL V hVo hVp (fun s => inter_subset_left)
  rw [s26v_surfaceIntegral_eq_tsum hq U hP]
  -- the planar pieces
  set Lp : ℕ → Set ℂ := fun i => (E (x i)).source ∩ Pm ⁻¹' Pc i with hLp
  have hLpm : ∀ i, MeasurableSet (Lp i) := fun i => (E (x i)).open_source.measurableSet.inter (hPm (hPcm i))
  have hLpΩ : ∀ i, Lp i ⊆ Ω := fun i z hz => hEΩ _ hz.1
  have hLpP : ∀ i, ∀ z ∈ Lp i, P z ∈ Pc i := fun i z hz => by rw [← hPmΩ z (hLpΩ i hz)]; exact hz.2
  have hLpinj : ∀ i, ∀ a ∈ Lp i, ∀ b ∈ Lp i, P a = P b → a = b := by
    intro i a ha b hb hab
    rw [hPE _ ha.1, hPE _ hb.1] at hab
    exact (E (x i)).injOn ha.1 hb.1 hab
  set AUp : ℕ → Set ℂ := fun i => Lp i ∩ upperHalf with hAUp
  set ALo : ℕ → Set ℂ := fun i => (fun z => conj z) ⁻¹' (Lp i ∩ lowerHalf) with hALo
  have hAUpm : ∀ i, MeasurableSet (AUp i) := fun i => (hLpm i).inter hΔ
  have hALom : ∀ i, MeasurableSet (ALo i) := fun i =>
    Complex.continuous_conj.measurable ((hLpm i).inter hΛ)
  have hAUpH : ∀ i, AUp i ⊆ upperHalf := fun i => inter_subset_right
  have hALoH : ∀ i, ALo i ⊆ upperHalf := fun i z hz => by
    have h : (conj z).im < 0 := hz.2
    show 0 < z.im
    rw [Complex.conj_im] at h
    linarith
  -- `pext p'` is injective on the pieces
  have hinjUp : ∀ i, InjOn (s22gm_projectionExtension p') (AUp i) := by
    intro i a ha b hb hab
    obtain ⟨γ, hγ, rfl⟩ := hpfib a (hAUpH i ha) b (hAUpH i hb) hab
    exact hLpinj i a ha.1 _ hb.1 (hPγ γ hγ a (hLpΩ i ha.1)).symm
  have hinjLo : ∀ i, InjOn (s22gm_projectionExtension p') (ALo i) := by
    intro i a ha b hb hab
    obtain ⟨γ, hγ, rfl⟩ := hpfib a (hALoH i ha) b (hALoH i hb) hab
    have hca : conj a ∈ Lp i := ha.1
    have hcb : conj (h36p_m γ a) ∈ Lp i := hb.1
    have hPc' : P (conj (h36p_m γ a)) = P (conj a) := by
      rw [← hconjm, hPγ γ hγ _ (hLpΩ i hca)]
    have h2 := hLpinj i _ hcb _ hca hPc'
    have h3 := congrArg conj h2
    simp only [Complex.conj_conj] at h3
    exact h3.symm
  -- membership in the saturations
  have hmemUp : ∀ i, ∀ z ∈ upperHalf, (s22gm_projectionExtension p' z ∈ s22gm_projectionExtension p' '' AUp i ↔
      Pm z ∈ Pc i) := by
    intro i z hz
    have hzΩ : z ∈ Ω := hΩH z (ne_of_gt hz)
    constructor
    · rintro ⟨a, ha, hpa⟩
      obtain ⟨γ, hγ, rfl⟩ := hpfib a (hAUpH i ha) z hz hpa
      rw [hPmΩ _ hzΩ, hPγ γ hγ a (hLpΩ i ha.1)]
      exact hLpP i a ha.1
    · intro hzP
      rw [hPmΩ z hzΩ] at hzP
      have hV := hPV i hzP
      set v := (E (x i)).symm (P z) with hv
      have hvs : v ∈ (E (x i)).source := (E (x i)).map_target hV.2
      have hPv : P v = P z := by rw [hPE _ hvs, (E (x i)).right_inv hV.2]
      obtain ⟨γ, hγ, hγv⟩ := (hPf z hzΩ v (hEΩ _ hvs)).1 hPv.symm
      have hvH : v ∈ upperHalf := by rw [hγv]; exact h36p_m_mem γ hz
      refine ⟨v, ⟨⟨hvs, ?_⟩, hvH⟩, ?_⟩
      · show Pm v ∈ Pc i
        rw [hPmΩ v (hEΩ _ hvs), hPv]
        exact hzP
      · rw [hγv]
        exact hpfib' z hz γ hγ
  have hmemLo : ∀ i, ∀ z ∈ upperHalf, (s22gm_projectionExtension p' z ∈ s22gm_projectionExtension p' '' ALo i ↔
      Pm (conj z) ∈ Pc i) := by
    intro i z hz
    have hczΩ : conj z ∈ Ω := hΩc _ (hΩH z (ne_of_gt hz))
    constructor
    · rintro ⟨a, ha, hpa⟩
      obtain ⟨γ, hγ, rfl⟩ := hpfib a (hALoH i ha) z hz hpa
      have hca : conj a ∈ Lp i := ha.1
      rw [hPmΩ _ hczΩ, ← hconjm, hPγ γ hγ _ (hLpΩ i hca)]
      exact hLpP i _ hca
    · intro hzP
      rw [hPmΩ _ hczΩ] at hzP
      have hV := hPV i hzP
      set v := (E (x i)).symm (P (conj z)) with hv
      have hvs : v ∈ (E (x i)).source := (E (x i)).map_target hV.2
      have hPv : P v = P (conj z) := by rw [hPE _ hvs, (E (x i)).right_inv hV.2]
      obtain ⟨γ, hγ, hγv⟩ := (hPf _ hczΩ v (hEΩ _ hvs)).1 hPv.symm
      have hczL : conj z ∈ lowerHalf := by
        show (conj z).im < 0
        rw [Complex.conj_im]
        linarith [show (0 : ℝ) < z.im from hz]
      have hvL : v ∈ lowerHalf := by
        rw [hγv, hconjm]
        show (conj (h36p_m γ z)).im < 0
        rw [Complex.conj_im]
        linarith [show (0 : ℝ) < (h36p_m γ z).im from h36p_m_mem γ hz]
      refine ⟨conj v, ⟨?_, ?_⟩, ?_⟩
      · show conj (conj v) ∈ Lp i
        rw [Complex.conj_conj]
        refine ⟨hvs, ?_⟩
        show Pm v ∈ Pc i
        rw [hPmΩ v (hEΩ _ hvs), hPv]
        exact hzP
      · show conj (conj v) ∈ lowerHalf
        rw [Complex.conj_conj]
        exact hvL
      · rw [hγv, hconjm, Complex.conj_conj]
        exact hpfib' z hz γ hγ
  -- the term of piece `i`
  have hterm : ∀ i, ∫⁻ z in chartAt ℂ (x i) '' Pc i,
      U ((chartAt ℂ (x i)).symm z) * ENNReal.ofReal ‖q (x i) z‖ =
      (∫⁻ z in F, (Pm ⁻¹' Pc i).indicator wUp z) +
        ∫⁻ z in F, ((fun z => Pm (conj z)) ⁻¹' Pc i).indicator wLo z := by
    intro i
    set s := x i with hs
    have hPs' : Pc i ⊆ (chartAt ℂ s).source := (hP.1 i).1
    set H : ℂ → ℂ := fun v => chartAt ℂ s (P v) with hH
    have hHinj : InjOn H (Lp i) := fun a ha b hb hab =>
      hLpinj i a ha b hb ((chartAt ℂ s).injOn (hPs' (hLpP i a ha)) (hPs' (hLpP i b hb)) hab)
    have hlaw : ∀ z ∈ Lp i, HasDerivAt H (deriv H z) z ∧ ‖ψ z‖ = ‖q s (H z)‖ * ‖deriv H z‖ ^ 2 := by
      intro z hz
      obtain ⟨hd, hψz⟩ := hqψ z (hLpΩ i hz) s (hPs' (hLpP i z hz))
      exact ⟨hd.hasDerivAt, by rw [hψz, norm_mul, norm_pow]⟩
    have himg : chartAt ℂ s '' Pc i = H '' Lp i := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        have haV := hPV i ha
        set v := (E s).symm a with hv
        have hvs : v ∈ (E s).source := (E s).map_target haV.2
        have hPv : P v = a := by rw [hPE s hvs, (E s).right_inv haV.2]
        refine ⟨v, ⟨hvs, ?_⟩, by simp only [hH, hPv]⟩
        show Pm v ∈ Pc i
        rw [hPmΩ v (hEΩ s hvs), hPv]
        exact ha
      · rintro ⟨z, hz, rfl⟩
        exact ⟨P z, hLpP i z hz, rfl⟩
    have hae : (Lp i \ upperHalf : Set ℂ) =ᵐ[volume] (Lp i ∩ lowerHalf : Set ℂ) := by
      refine ae_eq_set.2 ⟨measure_mono_null ?_ gzE_volume_im_eq_zero,
        measure_mono_null ?_ gzE_volume_im_eq_zero⟩
      · rintro z ⟨⟨hzL, hzH⟩, hz2⟩
        have h1 : ¬ 0 < z.im := hzH
        have h2 : ¬ z.im < 0 := fun h => hz2 ⟨hzL, h⟩
        show z.im = 0
        linarith [not_lt.1 h1, not_lt.1 h2]
      · rintro z ⟨⟨hzL, hzΛ⟩, hz2⟩
        exfalso
        have hzΛ' : z.im < 0 := hzΛ
        exact hz2 ⟨hzL, fun h => lt_asymm hzΛ' (show 0 < z.im from h)⟩
    have hsplit : ∫⁻ z in Lp i, w z = (∫⁻ z in AUp i, w z) + ∫⁻ z in Lp i ∩ lowerHalf, w z := by
      rw [← lintegral_inter_add_sdiff _ (Lp i) hΔ, setLIntegral_congr hae]
    have hLo := gzE_conj_measurePreserving.setLIntegral_comp_preimage ((hLpm i).inter hΛ) hwm
    calc ∫⁻ z in chartAt ℂ s '' Pc i, U ((chartAt ℂ s).symm z) * ENNReal.ofReal ‖q s z‖
        = ∫⁻ z in H '' Lp i, U ((chartAt ℂ s).symm z) * ENNReal.ofReal ‖q s z‖ := by rw [himg]
      _ = ∫⁻ z in Lp i, ENNReal.ofReal (‖deriv H z‖ ^ 2) *
            (U ((chartAt ℂ s).symm (H z)) * ENNReal.ofReal ‖q s (H z)‖) :=
          str_cov_local (hLpm i) (fun z hz => (hlaw z hz).1) hHinj _
      _ = ∫⁻ z in Lp i, w z := by
          refine setLIntegral_congr_fun (hLpm i) fun z hz => ?_
          have hzΩ := hLpΩ i hz
          rw [hwΩ z hzΩ, (hlaw z hz).2, ENNReal.ofReal_mul (norm_nonneg _)]
          simp only [hH]
          rw [(chartAt ℂ s).left_inv (hPs' (hLpP i z hz))]
          ring
      _ = (∫⁻ z in AUp i, w z) + ∫⁻ z in Lp i ∩ lowerHalf, w z := hsplit
      _ = _ := by
          congr 1
          · have hps := s22gm_lintegral_partial_sheet hp' hΓ hF (hAUpm i) (hAUpH i) (hinjUp i) hwUpm hcovUp
            have e1 : ∫⁻ z in AUp i, w z = ∫⁻ z in AUp i, wUp z :=
              setLIntegral_congr_fun (hAUpm i) fun z hz => by simp only [hwUp, indicator_of_mem (hAUpH i hz)]
            have e2 : ∫⁻ z in F, (s22gm_projectionExtension p' ⁻¹'
                (s22gm_projectionExtension p' '' AUp i)).indicator wUp z =
                ∫⁻ z in F, (Pm ⁻¹' Pc i).indicator wUp z := by
              refine setLIntegral_congr_fun hFm fun z hz => ?_
              by_cases h : Pm z ∈ Pc i
              · rw [indicator_of_mem (show z ∈ Pm ⁻¹' Pc i from h),
                  indicator_of_mem (show z ∈ s22gm_projectionExtension p' ⁻¹'
                    (s22gm_projectionExtension p' '' AUp i) from (hmemUp i z (hFH hz)).2 h)]
              · rw [indicator_of_notMem (show z ∉ Pm ⁻¹' Pc i from h),
                  indicator_of_notMem (show z ∉ s22gm_projectionExtension p' ⁻¹'
                    (s22gm_projectionExtension p' '' AUp i) from fun h' => h ((hmemUp i z (hFH hz)).1 h'))]
            rw [e1, ← hps, e2]
          · have hps := s22gm_lintegral_partial_sheet hp' hΓ hF (hALom i) (hALoH i) (hinjLo i) hwLom hcovLo
            have e1 : ∫⁻ z in (fun z => conj z) ⁻¹' (Lp i ∩ lowerHalf), w (conj z) =
                ∫⁻ z in ALo i, wLo z :=
              setLIntegral_congr_fun (hALom i) fun z hz => by simp only [hwLo, indicator_of_mem (hALoH i hz)]
            have e2 : ∫⁻ z in F, (s22gm_projectionExtension p' ⁻¹'
                (s22gm_projectionExtension p' '' ALo i)).indicator wLo z =
                ∫⁻ z in F, ((fun z => Pm (conj z)) ⁻¹' Pc i).indicator wLo z := by
              refine setLIntegral_congr_fun hFm fun z hz => ?_
              by_cases h : Pm (conj z) ∈ Pc i
              · rw [indicator_of_mem (show z ∈ (fun z => Pm (conj z)) ⁻¹' Pc i from h),
                  indicator_of_mem (show z ∈ s22gm_projectionExtension p' ⁻¹'
                    (s22gm_projectionExtension p' '' ALo i) from (hmemLo i z (hFH hz)).2 h)]
              · rw [indicator_of_notMem (show z ∉ (fun z => Pm (conj z)) ⁻¹' Pc i from h),
                  indicator_of_notMem (show z ∉ s22gm_projectionExtension p' ⁻¹'
                    (s22gm_projectionExtension p' '' ALo i) from fun h' => h ((hmemLo i z (hFH hz)).1 h'))]
            rw [← hLo, e1, ← hps, e2]
  -- sum over the pieces
  have hpart : ∀ (Q : ℂ → S) (f : ℂ → ℝ≥0∞) (z : ℂ), ∑' i, (Q ⁻¹' Pc i).indicator f z = f z := by
    intro Q f z
    obtain ⟨i₀, hi₀⟩ := mem_iUnion.1 (hP.2.2.symm ▸ mem_univ (Q z) : Q z ∈ ⋃ i, Pc i)
    rw [tsum_eq_single i₀ (fun j hj => indicator_of_notMem
      (show z ∉ Q ⁻¹' Pc j from fun h => Set.disjoint_left.1 (hP.2.1 hj) h hi₀) _)]
    exact indicator_of_mem (show z ∈ Q ⁻¹' Pc i₀ from hi₀) _
  rw [tsum_congr hterm, ENNReal.tsum_add,
    ← lintegral_tsum (fun i => (hwUpm.indicator (hPm (hPcm i))).aemeasurable),
    ← lintegral_tsum (fun i => (hwLom.indicator (show MeasurableSet ((fun z => Pm (conj z)) ⁻¹' Pc i) from
      (hPm.comp Complex.continuous_conj.measurable) (hPcm i))).aemeasurable)]
  simp only [hpart]
  congr 1
  · refine setLIntegral_congr_fun hFm fun z hz => ?_
    simp only [hwUp, indicator_of_mem (hFH hz)]
    exact hwΩ z (hΩH z (ne_of_gt (hFH hz)))
  · refine setLIntegral_congr_fun hFm fun z hz => ?_
    simp only [hwLo, indicator_of_mem (hFH hz)]
    rw [hwΩ _ (hΩc _ (hΩH z (ne_of_gt (hFH hz)))), Complex.norm_conj]

/-- **Admissibility** of a holomorphic quadratic differential of finite norm on a non-exceptional surface of type
`(g, n, 0)` (lift it to an `ℍ`-uniformization; `s82dx_integrable_admissible`). -/
theorem s36a_adm {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] [MeasurableSpace S] [BorelSpace S] {g n : ℕ} (hex : ¬ IsExceptionalType g n 0)
    (F₀ : FiniteTypeStructure S g n 0) {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hfin : quadDiffNorm q < ⊤) :
    q ∈ admissibleQDInterior F₀ := by
  obtain ⟨Γ', p', hΓ', hfree', hp'⟩ := (finiteType_hyperbolic F₀ hex).1 rfl
  obtain ⟨F', h1, h2, h3, h4, h5⟩ := s82dx_dirichlet hΓ' hfree'
  have hF' : IsFundamentalDomainH Γ' F' := ⟨h1, h2, h3, h4, h5⟩
  have hφd : DifferentiableOn ℂ (utm_liftQD q p') upperHalf := utm_liftQD_differentiableOn hq hp'
  have hφΓ : ∀ γ ∈ Γ', ∀ z ∈ upperHalf,
      utm_liftQD q p' ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 =
        utm_liftQD q p' z := by
    intro γ hγ z hz
    have h := utm_b_liftQD_automorphic q hp' hγ hz
    have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := h36t_den_ne γ ⟨z, hz⟩
    rw [← h]
    show utm_liftQD q p' (utm_b_mob γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 =
      utm_liftQD q p' (utm_b_mob γ z) * (1 / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) ^ 2
    field_simp
  have hT1 := str_surfaceIntegral_eq hp' hΓ' hF' hq hφd hφΓ (fun τ _ => rfl) (U := fun _ => 1) measurable_const
  have hnorm : quadDiffNorm q = phiArea (utm_liftQD q p') F' := by
    simp only [quadDiffNorm, phiArea]
    rw [hT1]
    simp
  exact s82dx_integrable_admissible F₀ hp' hΓ' hF' ⟨hφd, hnorm ▸ hfin, hφΓ⟩ hq (fun τ _ => rfl)


end LiZhongQC
