import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller

/-!
# §33 Bers 嵌入 — The Bers embedding

* §33.1 models of `T_g`: the space `M(G₀)` of `G₀`-compatible Beltrami coefficients (33.1); the
  equivalence (33.2) `f̃|ℝ = f̃'|ℝ`; the symmetric extension (33.3) and the maps `f^μ`; (33.4);
  the deformations `G^μ = f^μ G₀ (f^μ)⁻¹` and `S^μ = ℍ/G^μ`; `T(S₀) ≅ M(G₀)/∼`; the model
  `T(G₀) = {χ_μ}` (33.5)–(33.7); the model `{f^μ|ℝ}` (33.8); the maps `f_μ` and Lemma 33.1
  (33.9)–(33.10); the model `{f_μ|𝕃}`
                                        — `BeltramiGamma`, `symmetricExtension`, `fMuSym`,
                                          `teichSetoidGamma`, `TeichGamma`, `lemma33_1`
* §33.2 the Teichmüller space `T(G₀)` of a Fuchsian group; `G₀ = {I}` gives the universal
  Teichmüller space                     — `teichGamma_bot_equiv_universal`
* §33.3 `φ_μ = S_{f_μ}|𝕃`, `‖φ_μ‖ < 3/2`, the automorphy `φ_μ = (φ_μ ∘ γ) γ'²`, the Banach space
  `Q(G₀, 𝕃)` and the Bers embedding `Ψ`  — `automorphicQD`, `bersMapGamma`
* §33.4 the distance formula `d_T([μ], [ν]) = ½ ln((1 + δ)/(1 - δ))`; Lemma 33.2 (`Ψ` continuous);
  Lemma 33.3 (`Ψ([0])` is an interior point); Lemma 33.4 (Earle), (33.11); Theorem 33.1 (Bers:
  `Ψ(T(S₀))` is a connected open set), (33.12); `dim_ℂ Q(G₀, 𝕃) = 3g - 3` and the complex
  coordinates of `T(S₀)`                — `lemma33_2`, `lemma33_3`, `lemma33_4_earle`,
                                          `thm33_1_bers`, `thm33_dimension`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

/-! ## §33.1 Models of `T_g` -/

/-- (33.1): the set `M(G₀)` of bounded measurable functions `μ` on `ℍ` (extended by `0`) with
`μ(γz) conj γ'(z)/γ'(z) = μ(z)` for `γ ∈ G₀` and `‖μ‖_∞ < 1`. -/
def BeltramiGamma (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type :=
  {μ : BeltramiH // IsGammaCompatible Γ μ.1}

/-- §33.1: the complex dilatation of a normalized lift of a marked surface lies in `M(G₀)`.

**Correction.**  The hypothesis `[IsManifold 𝓘(ℂ) ω S₀]` was missing: with twisted (merely
topologically compatible) charts a non-quasiconformal equivariant lift passes the hypotheses, and
the statement was **false**. -/
theorem normalizedLift_beltrami_mem {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
    [IsManifold 𝓘(ℂ) ω S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀)
    (m : MarkedRS S₀) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → m.X.carrier}
    (hp : IsUniformization Γ p) {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {G : ExtPlane → ExtPlane}
    (hF : IsNormalizedLift p₀ p m.marking F G) :
    ∃ μ : BeltramiGamma Γ₀, ∀ᵐ z ∂(volume.restrict upperHalf), μ.1.1 z = complexDilatation (liftToC F) z := by
  -- the lift `F` is `K`-q.c. on `ℍ` and its dilatation is `Γ₀`-automorphic (S23)
  obtain ⟨K, hK⟩ := m.qc
  obtain ⟨hFK, hcompat⟩ := lift_isKQC_automorphic hp₀ hp hK hF.1
  have hK1 : (1 : ℝ) ≤ K := hFK.2.1
  -- `μ`: the dilatation of `F`, cut off to `ℍ`
  set μ : ℂ → ℂ := upperHalf.indicator (complexDilatation (liftToC F)) with hμdef
  have hbound : ∀ᵐ z ∂(volume.restrict upperHalf),
      ‖complexDilatation (liftToC F) z‖ ≤ (K - 1) / (K + 1) :=
    (isKQC_maxDilatation_le hFK).2
  have hk0 : 0 ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hH : IsBeltramiCoeff μ univ ((K - 1) / (K + 1)) := by
    refine ⟨(((measurable_dzbar _).div (measurable_dz _)).indicator
      isOpen_upperHalf.measurableSet).aestronglyMeasurable, ?_⟩
    rw [Measure.restrict_univ]
    have h2 := (ae_restrict_iff' isOpen_upperHalf.measurableSet).1 hbound
    filter_upwards [h2] with z hz
    by_cases hzU : z ∈ upperHalf
    · rw [hμdef, indicator_of_mem hzU]
      exact hz hzU
    · rw [hμdef, indicator_of_notMem hzU, norm_zero]
      exact hk0
  have hBH : (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff μ univ k) ∧ ∀ z : ℂ, z.im ≤ 0 → μ z = 0 :=
    ⟨⟨(K - 1) / (K + 1), hk0, (div_lt_one (by linarith)).2 (by linarith), hH⟩,
      fun z hz => by
        rw [hμdef]
        exact indicator_of_notMem (show z ∉ upperHalf from fun hu => absurd hz (not_le.2 hu)) _⟩
  -- `Γ₀`-compatibility: `γ` maps `ℍ` to itself
  have hcompatμ : IsGammaCompatible Γ₀ μ := by
    intro γ hγ
    filter_upwards [hcompat γ hγ, ae_restrict_mem isOpen_upperHalf.measurableSet] with z hz hzU
    have hγz : ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) ∈ upperHalf := by
      have h := h36t_coe_smul γ ⟨z, hzU⟩
      show 0 < (((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)).im
      rw [show z = ((⟨z, hzU⟩ : UpperHalfPlane) : ℂ) from rfl, ← h]
      exact UpperHalfPlane.coe_im_pos _
    rw [hμdef, indicator_of_mem hzU, indicator_of_mem hγz]
    exact hz
  refine ⟨⟨⟨μ, hBH⟩, hcompatμ⟩, ?_⟩
  filter_upwards [ae_restrict_mem isOpen_upperHalf.measurableSet] with z hz
  exact indicator_of_mem hz _

/-- (33.3): the symmetric extension `μ(z) = conj μ(z̄)` of `μ` to the lower half-plane. -/
def symmetricExtension (μ : ℂ → ℂ) (z : ℂ) : ℂ := if z.im < 0 then conj (μ (conj z)) else μ z

/-- §33.1: `f^μ`, the quasiconformal map of the plane with the symmetrically extended complex
dilatation, fixing `0, 1, ∞`. -/
def fMuSym (μ : ℂ → ℂ) : ℂ → ℂ := normalizedSolution (symmetricExtension μ)

/-! ### Bers-Γ track interface (coordinator 553e2d): `f^μ`, Lemma 33.1 and the Bers map of `T(G₀)` -/

/-- A property which holds a.e. on `ℍ` and a.e. on `𝕃` holds a.e. on `ℂ` (the real axis is null). -/
theorem bg_ae_of_halves {p : ℂ → Prop} (hU : ∀ᵐ z ∂(volume.restrict upperHalf), p z)
    (hL : ∀ᵐ z ∂(volume.restrict lowerHalf), p z) : ∀ᵐ z, p z := by
  have hnull : ∀ᵐ z : ℂ, z ∉ {w : ℂ | w.im = 0} :=
    measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
  rw [ae_restrict_iff' isOpen_upperHalf.measurableSet] at hU
  rw [ae_restrict_iff' isOpen_lowerHalf.measurableSet] at hL
  filter_upwards [hU, hL, hnull] with z h1 h2 h3
  rcases lt_or_gt_of_ne (h3 : z.im ≠ 0) with h | h
  · exact h2 h
  · exact h1 h

/-- Two maps which agree on an open set have the same complex dilatation there. -/
theorem bg_dilatation_congr {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (h : EqOn f g U) {z : ℂ}
    (hz : z ∈ U) : complexDilatation f z = complexDilatation g z := by
  have hev : f =ᶠ[𝓝 z] g := Filter.eventually_of_mem (hU.mem_nhds hz) h
  simp only [complexDilatation, dz, dzbar, hev.fderiv_eq]

/-- The complex dilatation of the reflected map `z ↦ conj (f (conj z))` at `z` is the conjugate of that of `f` at
`conj z` (`abR_x_dz_dzbar_conj`; where `f` is not differentiable both sides vanish). -/
theorem bg_dilatation_conj (f : ℂ → ℂ) (z : ℂ) :
    complexDilatation (fun w => conj (f (conj w))) z = conj (complexDilatation f (conj z)) := by
  by_cases hd : DifferentiableAt ℝ f (conj z)
  · obtain ⟨-, h1, h2⟩ := abR_x_dz_dzbar_conj hd
    rw [complexDilatation, complexDilatation, h1, h2, map_div₀]
  · have hd' : ¬ DifferentiableAt ℝ (fun w => conj (f (conj w))) z := by
      intro h
      apply hd
      have h' : DifferentiableAt ℝ (fun w => conj (f (conj w))) (conj (conj z)) := by
        rwa [Complex.conj_conj]
      simpa only [Complex.conj_conj] using (abR_x_dz_dzbar_conj h').1
    simp [complexDilatation, dz, dzbar, fderiv_zero_of_not_differentiableAt hd,
      fderiv_zero_of_not_differentiableAt hd']

/-- A coefficient of `M`, restricted to `ℍ`: `‖μ‖ ≤ k < 1` a.e. on `ℍ`. -/
theorem bg_beltramiH_upper (μ : BeltramiH) : ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff μ.1 upperHalf k := by
  obtain ⟨⟨k, hk0, hk1, hm, hb⟩, -⟩ := μ.2
  rw [Measure.restrict_univ] at hm hb
  exact ⟨k, hk0, hk1, hm.restrict, ae_restrict_of_ae hb⟩

/-- Two quasiconformal maps of an open set `D` with a.e. equal complex dilatations differ by a conformal map: `g ∘ f⁻¹`
maps `f(D)` conformally onto `g(D)` (`same_dilatation_conformal`). -/
theorem bg_conformal_of_dilatation_eq {f g : ℂ → ℂ} {D : Set ℂ} {K₁ K₂ : ℝ} (hf : IsKQC f D K₁)
    (hg : IsKQC g D K₂) (h : ∀ᵐ z ∂(volume.restrict D), complexDilatation g z = complexDilatation f z) :
    IsConformalOnto (g ∘ Function.invFunOn f D) (f '' D) (g '' D) := by
  obtain ⟨hμ, hfs⟩ := thm10_2_genHomeoSolution_of_isKQC hf
  have hgs := nxS_genHomeoSolution_congr (thm10_2_genHomeoSolution_of_isKQC hg).2 h
  have hK1 : (1 : ℝ) ≤ K₁ := hf.2.1
  have hk : (K₁ - 1) / (K₁ + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  obtain ⟨φ, hφ, hgφ⟩ := same_dilatation_conformal hf.1 hk hμ hfs hgs
  have heq : EqOn (g ∘ Function.invFunOn f D) φ (f '' D) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Function.comp_apply, hf.2.2.1.2.1.leftInvOn_invFunOn hz, hgφ z hz]
  exact ⟨hφ.1.congr heq, hφ.2.1.congr heq.symm, heq.image_eq.trans hφ.2.2⟩

/-- Post-composition with a conformal map: if `g` is `K`-q.c. on `D` and `φ` is conformal on an open set `U ⊇ g(D)`,
then `φ ∘ g` is `K`-q.c. on `D`, with the complex dilatation of `g` a.e. -/
theorem bg_comp_conformal {g φ : ℂ → ℂ} {D U V : Set ℂ} {K : ℝ} (hg : IsKQC g D K) (hU : IsOpen U)
    (hφ : IsConformalOnto φ U V) (hgU : g '' D ⊆ U) :
    IsKQC (φ ∘ g) D K ∧ ∀ᵐ z ∂(volume.restrict D), complexDilatation (φ ∘ g) z = complexDilatation g z := by
  have h1 := thm7_1_comp hg (isKQC_one_of_conformal hU hφ) hgU
  rw [mul_one] at h1
  refine ⟨h1, ?_⟩
  filter_upwards [thm9_3_differentiable_ae hg, ae_restrict_mem hg.1.measurableSet] with z hz hzD
  have hU' : g z ∈ U := hgU (mem_image_of_mem g hzD)
  exact complexDilatation_comp_conformal_left hz (hφ.1.differentiableAt (hU.mem_nhds hU'))
    (deriv_ne_zero_of_injOn hU hφ.1 hφ.2.1 hU')

/-- Complex conjugation maps `𝕃` onto `ℍ`: the preimage of `ℍ` under `z ↦ z̄` is `𝕃`. -/
theorem bg_s_conj_preimage_upperHalf : (fun z : ℂ => conj z) ⁻¹' upperHalf = lowerHalf := by
  ext z
  simp only [mem_preimage, upperHalf, lowerHalf, mem_ofPred_eq, Complex.conj_im, neg_pos]

/-- The symmetric extension of a Beltrami coefficient on `ℍ` bounded by `k` is a Beltrami coefficient on `ℂ` bounded
by `k`: on `𝕃` it is `conj ∘ μ ∘ conj`, conjugation maps `𝕃` measure-preservingly onto `ℍ`, and `ℝ` is null. -/
theorem bg_s_beltrami {μ : ℂ → ℂ} {k : ℝ} (hμ : IsBeltramiCoeff μ upperHalf k) :
    IsBeltramiCoeff (symmetricExtension μ) univ k := by
  have hmp : MeasurePreserving (fun z : ℂ => conj z) (volume.restrict lowerHalf)
      (volume.restrict upperHalf) := by
    have h := gzE_conj_measurePreserving.restrict_preimage isOpen_upperHalf.measurableSet
    rwa [bg_s_conj_preimage_upperHalf] at h
  rw [IsBeltramiCoeff, Measure.restrict_univ]
  refine ⟨?_, ?_⟩
  · -- measurability: `conj ∘ μ ∘ conj` on `𝕃`, and `μ` on `{Im z ≥ 0} = ℍ ∪ ℝ` with `ℝ` null
    have hL : AEStronglyMeasurable (fun z => conj (μ (conj z))) (volume.restrict lowerHalf) :=
      Complex.continuous_conj.comp_aestronglyMeasurable (hμ.1.comp_measurePreserving hmp)
    have hC : AEStronglyMeasurable μ (volume.restrict lowerHalfᶜ) := by
      have hsplit : lowerHalfᶜ = upperHalf ∪ {z : ℂ | z.im = 0} := by
        ext z
        simp only [mem_compl_iff, lowerHalf, upperHalf, mem_union, mem_ofPred_eq, not_lt]
        constructor
        · intro h
          rcases h.lt_or_eq with h | h
          · exact Or.inl h
          · exact Or.inr h.symm
        · rintro (h | h)
          · exact h.le
          · exact h.ge
      rw [hsplit, aestronglyMeasurable_union_iff]
      refine ⟨hμ.1, ?_⟩
      rw [Measure.restrict_eq_zero.2 gzE_volume_im_eq_zero]
      exact aestronglyMeasurable_zero_measure μ
    classical
    have heq : symmetricExtension μ = lowerHalf.piecewise (fun z => conj (μ (conj z))) μ := by
      funext z
      by_cases hz : z.im < 0
      · rw [Set.piecewise_eq_of_mem lowerHalf _ _ (show z ∈ lowerHalf from hz), symmetricExtension,
          ite_eq_left hz]
      · rw [Set.piecewise_eq_of_notMem lowerHalf _ _ (show z ∉ lowerHalf from hz), symmetricExtension,
          ite_eq_right hz]
    rw [heq]
    exact hL.piecewise isOpen_lowerHalf.measurableSet.nullMeasurableSet hC
  · -- the bound: `σ = μ` on `ℍ`, and `‖σ z‖ = ‖μ z̄‖` on `𝕃`
    refine bg_ae_of_halves ?_ ?_
    · filter_upwards [hμ.2, ae_restrict_mem isOpen_upperHalf.measurableSet] with z h1 h2
      rw [symmetricExtension, ite_eq_right (not_lt.2 (le_of_lt h2))]
      exact h1
    · filter_upwards [hmp.quasiMeasurePreserving.ae hμ.2,
        ae_restrict_mem isOpen_lowerHalf.measurableSet] with z h1 h2
      rw [symmetricExtension, ite_eq_left (show z.im < 0 from h2), Complex.norm_conj]
      exact h1

/-- The symmetric extension is symmetric off `ℝ`: `conj σ(z̄) = σ(z)` for `Im z ≠ 0`. -/
theorem bg_s_symm_conj (μ : ℂ → ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    conj (symmetricExtension μ (conj z)) = symmetricExtension μ z := by
  rcases lt_or_gt_of_ne hz with h | h
  · have hc : ¬ (conj z).im < 0 := by
      rw [Complex.conj_im]
      linarith
    rw [symmetricExtension, ite_eq_right hc, symmetricExtension, ite_eq_left h]
  · have hc : (conj z).im < 0 := by
      rw [Complex.conj_im]
      linarith
    rw [symmetricExtension, ite_eq_left hc, Complex.conj_conj, Complex.conj_conj, symmetricExtension,
      ite_eq_right (not_lt.2 h.le)]

/-- The unique normalized solution `f` for a symmetric extension commutes with the reflection `z ↦ z̄`:
`z ↦ conj f(z̄)` is again a normalized solution for it (`abR_x_isKQC_conj`, `bg_dilatation_conj`, and `bg_s_symm_conj`
off the null line `ℝ`), so it is `f` by uniqueness. -/
theorem bg_s_conj_comm {μ f : ℂ → ℂ} (hN : IsNormalizedSolution f (symmetricExtension μ))
    (huniq : ∀ g : ℂ → ℂ, IsNormalizedSolution g (symmetricExtension μ) → g = f) (z : ℂ) :
    f (conj z) = conj (f z) := by
  obtain ⟨⟨K, hK⟩, hs, h0, h1, hd⟩ := hN
  have hgK : IsKQC (fun w => conj (f (conj w))) univ K := by
    have h := abR_x_isKQC_conj hK
    rwa [preimage_univ] at h
  have hgs : (fun w => conj (f (conj w))) '' univ = univ := by
    refine eq_univ_of_forall fun w => ?_
    have hw : conj w ∈ f '' univ := by
      rw [hs]
      exact mem_univ _
    obtain ⟨v, -, hv⟩ := hw
    exact ⟨conj v, mem_univ _, by simp only [Complex.conj_conj, hv]⟩
  have hnull : ∀ᵐ w : ℂ, w ∉ {v : ℂ | v.im = 0} :=
    measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
  have hgd : ∀ᵐ w, complexDilatation (fun w => conj (f (conj w))) w = symmetricExtension μ w := by
    filter_upwards [gzE_conj_measurePreserving.quasiMeasurePreserving.ae hd, hnull] with w hw1 hw2
    rw [bg_dilatation_conj, hw1]
    exact bg_s_symm_conj μ hw2
  have hg : IsNormalizedSolution (fun w => conj (f (conj w))) (symmetricExtension μ) :=
    ⟨⟨_, hgK⟩, hgs, by simp [h0], by simp [h1], hgd⟩
  have h := congrFun (huniq _ hg) z
  rw [← h, Complex.conj_conj]

/-- A `K`-q.c. self-map `Ψ` of `ℂ` which is real on `ℝ` and fixes `0` and `1` cannot map `ℍ` onto `𝕃`: otherwise `-Ψ`
would be a `K`-q.c. self-map of `ℍ` fixing `∞` with boundary values `x ↦ -Re Ψ(x)`, which are increasing by
`b4_qs_monotone` but take the values `0` at `0` and `-1` at `1` (the argument of `ut_w0_not_swap`). -/
theorem bg_s_not_swap {Ψ : ℂ → ℂ} {K : ℝ} (hΨ : IsKQC Ψ univ K) (hs : Ψ '' univ = univ)
    (hreal : ∀ x : ℝ, (Ψ x).im = 0) (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1) : Ψ '' upperHalf ≠ lowerHalf := by
  intro hswap
  obtain ⟨e, he⟩ := t1_homeomorph hΨ hs
  set E : ExtPlane ≃ₜ ExtPlane := (e.trans (Homeomorph.neg ℂ)).onePointCongr with hEdef
  have hEc : ∀ z : ℂ, E (z : ExtPlane) = ((-Ψ z : ℂ) : ExtPlane) := fun z => by
    rw [hEdef, Homeomorph.onePointCongr_apply, OnePoint.map_some, Homeomorph.trans_apply,
      Homeomorph.coe_neg, he]
  obtain ⟨hK, -⟩ := b4_rat_affine_comp hΨ hs (0 : ℂ) (0 : ℂ) one_ne_zero (neg_ne_zero.2 one_ne_zero)
  have hfun : (fun z => (-1 : ℂ) * Ψ (1 * z + 0) + 0) = fun z => -Ψ z := by
    funext z
    simp
  rw [hfun] at hK
  have hgK : IsKQC (fun z => -Ψ z) upperHalf K :=
    ac_t_isKQC_restrict hK isOpen_upperHalf (subset_univ _)
  have hgs : (fun z => -Ψ z) '' upperHalf = upperHalf := by
    rw [← Set.image_image (fun w : ℂ => -w) Ψ, hswap]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      show 0 < (-z).im
      rw [Complex.neg_im]
      exact neg_pos.2 hz
    · intro hw
      refine ⟨-w, ?_, neg_neg w⟩
      show (-w).im < 0
      rw [Complex.neg_im]
      exact neg_neg_iff_pos.2 hw
  have htoExt : E '' toExt upperHalf = toExt upperHalf := by
    unfold toExt
    rw [Set.image_image]
    simp_rw [hEc]
    rw [← Set.image_image (fun w : ℂ => (w : ExtPlane)) (fun z => -Ψ z), hgs]
  have hext : IsHomeoExtension (fun z => -Ψ z) upperHalf upperHalf E := by
    refine ⟨fun z _ => hEc z, E.continuous.continuousOn, E.injective.injOn, ?_⟩
    rw [Homeomorph.image_closure, htoExt]
  have hmono := (b4_qs_monotone (h := fun x : ℝ => -(Ψ x).re)
    ⟨hgK, hgs, E, hext, rfl, fun x => by
      rw [hEc]
      congr 1
      exact Complex.ext (by simp) (by simp [hreal x])⟩).1
  have h01 := hmono (show (0 : ℝ) < 1 from one_pos)
  norm_num [h0, h1] at h01

/-- A `K`-q.c. self-map `Ψ` of `ℂ` fixing `0` and `1` and commuting with `z ↦ z̄` maps `ℍ` onto `ℍ`: `Ψ(z)` is real
only for real `z` (symmetry and injectivity), so the connected set `Ψ(ℍ)` lies in `ℍ` or in `𝕃`; by symmetry and
surjectivity it is then all of `ℍ` or all of `𝕃`, and the latter is excluded by `bg_s_not_swap`. -/
theorem bg_s_image_upperHalf {Ψ : ℂ → ℂ} {K : ℝ} (hΨ : IsKQC Ψ univ K) (hs : Ψ '' univ = univ)
    (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1) (hsym : ∀ z, Ψ (conj z) = conj (Ψ z)) : Ψ '' upperHalf = upperHalf := by
  obtain ⟨e, he⟩ := t1_homeomorph hΨ hs
  have hc : Continuous Ψ := he ▸ e.continuous
  have hinj : Function.Injective Ψ := he ▸ e.injective
  have hsurj : Function.Surjective Ψ := he ▸ e.surjective
  -- `Ψ` is real exactly on `ℝ`
  have hreal : ∀ x : ℝ, (Ψ x).im = 0 := fun x => by
    have h := hsym x
    rw [Complex.conj_ofReal] at h
    exact Complex.conj_eq_iff_im.1 h.symm
  have hre : ∀ z : ℂ, z.im = 0 → (Ψ z).im = 0 := fun z hz => by
    have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by rw [hz, Complex.ofReal_im])
    rw [hz']
    exact hreal z.re
  have hnr : ∀ z : ℂ, z.im ≠ 0 → (Ψ z).im ≠ 0 := fun z hz him => by
    have h : Ψ (conj z) = Ψ z := by rw [hsym, Complex.conj_eq_iff_im.2 him]
    exact hz (Complex.conj_eq_iff_im.1 (hinj h))
  have hconj : ∀ z : ℂ, z.im < 0 → conj z ∈ upperHalf := fun z hz => by
    show 0 < (conj z).im
    rw [Complex.conj_im]
    linarith
  -- `Ψ(ℍ)` is preconnected and misses `ℝ`
  have hor : Ψ '' upperHalf ⊆ upperHalf ∨ Ψ '' upperHalf ⊆ lowerHalf := by
    refine (isConnected_upperHalf.isPreconnected.image Ψ hc.continuousOn).subset_or_subset
      isOpen_upperHalf isOpen_lowerHalf ?_ ?_
    · exact Set.disjoint_left.2 fun z h₁ h₂ => lt_asymm (show 0 < z.im from h₁) (show z.im < 0 from h₂)
    · rintro _ ⟨z, hz, rfl⟩
      rcases lt_or_gt_of_ne (hnr z (show 0 < z.im from hz).ne') with h | h
      · exact Or.inr h
      · exact Or.inl h
  rcases hor with hU | hU
  · refine subset_antisymm hU fun w hw => ?_
    obtain ⟨z, rfl⟩ := hsurj w
    have hw' : 0 < (Ψ z).im := hw
    rcases lt_trichotomy z.im 0 with h | h | h
    · have h2 : 0 < (Ψ (conj z)).im := hU (mem_image_of_mem Ψ (hconj z h))
      rw [hsym, Complex.conj_im] at h2
      linarith
    · rw [hre z h] at hw'
      exact absurd hw' (lt_irrefl 0)
    · exact ⟨z, h, rfl⟩
  · refine absurd (subset_antisymm hU fun w hw => ?_) (bg_s_not_swap hΨ hs hreal h0 h1)
    obtain ⟨z, rfl⟩ := hsurj w
    have hw' : (Ψ z).im < 0 := hw
    rcases lt_trichotomy z.im 0 with h | h | h
    · have h2 : (Ψ (conj z)).im < 0 := hU (mem_image_of_mem Ψ (hconj z h))
      rw [hsym, Complex.conj_im] at h2
      linarith
    · rw [hre z h] at hw'
      exact absurd hw' (lt_irrefl 0)
    · exact ⟨z, h, rfl⟩

/-- **S0** (the symmetric solution): for `‖μ‖ ≤ k < 1` a.e. on `ℍ`, the symmetric extension `μ(z) = conj μ(z̄)` is a
Beltrami coefficient on `ℂ` bounded by `k` (conjugation preserves null sets and `ℝ` is null), `f^μ` is its normalized
solution, `(1 + k)/(1 - k)`-q.c. on `ℂ`, and every normalized solution for it equals `f^μ` (Theorem 13.7). -/
theorem bg_sym_spec {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ upperHalf k) :
    IsBeltramiCoeff (symmetricExtension μ) univ k ∧ IsNormalizedSolution (fMuSym μ) (symmetricExtension μ) ∧
      IsKQC (fMuSym μ) univ ((1 + k) / (1 - k)) ∧
      ∀ g : ℂ → ℂ, IsNormalizedSolution g (symmetricExtension μ) → g = fMuSym μ := by
  have hσ := bg_s_beltrami hμ
  obtain ⟨f₀, hf₀, hK, huniq⟩ := thm13_7_normalized_existence hk₀ hk hσ
  have hex : ∃ f : ℂ → ℂ, IsNormalizedSolution f (symmetricExtension μ) := ⟨f₀, hf₀⟩
  have hspec : IsNormalizedSolution (fMuSym μ) (symmetricExtension μ) := by
    rw [fMuSym, normalizedSolution, dite_eq_left hex]
    exact hex.choose_spec
  have heq : fMuSym μ = f₀ := huniq _ hspec
  refine ⟨hσ, hspec, ?_, fun g hg => (huniq g hg).trans heq.symm⟩
  rw [heq]
  exact hK

/-- §33.1: `f^μ` maps `ℍ` onto itself (and `ℝ` onto `ℝ`, `𝕃` onto `𝕃`), commutes with the reflection
`z ↦ z̄`, and `f^μ|ℍ` is the normalized lift `f̃`. -/
theorem fMuSym_upperHalf {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ upperHalf k) :
    fMuSym μ '' upperHalf = upperHalf ∧ (∀ x : ℝ, (fMuSym μ x).im = 0) ∧
      (∀ z, fMuSym μ (conj z) = conj (fMuSym μ z)) ∧ IsKQC (fMuSym μ) upperHalf ((1 + k) / (1 - k)) ∧
      ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation (fMuSym μ) z = μ z := by
  obtain ⟨-, hN, hK, huniq⟩ := bg_sym_spec hk₀ hk hμ
  have hsym : ∀ z, fMuSym μ (conj z) = conj (fMuSym μ z) := bg_s_conj_comm hN huniq
  obtain ⟨-, hs, h0, h1, hd⟩ := hN
  have hreal : ∀ x : ℝ, (fMuSym μ x).im = 0 := fun x => by
    have h := hsym x
    rw [Complex.conj_ofReal] at h
    exact Complex.conj_eq_iff_im.1 h.symm
  refine ⟨bg_s_image_upperHalf hK hs h0 h1 hsym, hreal, hsym,
    ac_t_isKQC_restrict hK isOpen_upperHalf (subset_univ _), ?_⟩
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem isOpen_upperHalf.measurableSet] with z hz1 hz2
  rw [hz1, symmetricExtension, ite_eq_right (not_lt.2 (le_of_lt hz2))]

/-- **(33.4)**: `μ ∼ μ'` iff `f^μ|ℝ = f^{μ'}|ℝ`; this is the equivalence (33.2) of marked surfaces
in terms of Beltrami coefficients. -/
def teichSetoidGamma (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Setoid (BeltramiGamma Γ) where
  r μ ν := ∀ x : ℝ, fMuSym μ.1.1 x = fMuSym ν.1.1 x
  iseqv := ⟨fun _ _ => rfl, fun h x => (h x).symm, fun h₁ h₂ x => (h₁ x).trans (h₂ x)⟩

/-- **§33.1 / §33.2**: the Teichmüller space `T(G₀) = M(G₀)/∼` of the Fuchsian group `G₀`. -/
def TeichGamma (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type :=
  Quotient (teichSetoidGamma Γ)

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ### Stage T3 (s27t, coordinator 553e2d): glue for `teichGamma_equiv_teichSpace` (prefix `s33v_`)

`e [μ] = [X^μ, id]`, where `X^μ` is a marked surface of `S = ℍ/Γ` whose lifted coefficient is `μ` a.e. on `ℍ` (S27
`s27v_exists_marked`, from the S27 T3 stubs [A1], [A2]).  Well defined and injective: Theorem 27.1 through the
uniformization transport (S27 `s27v_equiv_iff_fSym`) and U11 (`s27u_fSym_congr_ae`); surjective: the lifted coefficient
of a marked surface lies in `M(Γ)` (`s27u_liftCoeff_beltramiH`) and its `X^μ` is equivalent to it; the characterization
clause is Theorem 27.1 again, with the UT data of `m` and of `X^μ`.  No new stub. -/

/-- S27's verbatim copy `s27u_fSym` of `f^μ` is S33's `fMuSym`. -/
theorem s33v_fSym_eq : s27u_fSym = fMuSym := by
  rfl

/-- **`X^μ` for `μ ∈ M(Γ₀)`** (S27 `s27v_exists_marked` + U11): a marked surface of `S = ℍ/Γ₀` whose symmetric solution
is `f^μ` (its lifted coefficient is `μ` a.e. on `ℍ`). -/
theorem s33v_marked {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ₀ p) (μ : BeltramiGamma Γ₀) :
    ∃ m : MarkedRS S, s27u_fSym (s27u_liftCoeff p m.marking) = s27u_fSym μ.1.1 := by
  obtain ⟨k, hk0, hk1, hμ⟩ := bg_beltramiH_upper μ.1
  obtain ⟨m, hm⟩ := s27v_exists_marked hp hk0 hk1 hμ μ.2
  obtain ⟨k', hk0', hk1', hμ'⟩ := s27v_liftCoeff_bound hp m
  exact ⟨m, s27u_fSym_congr_ae hk0' hk1' hμ' hk0 hk1 hμ hm⟩

/-- **§33.1: `T(G₀) ≅ T(S₀)`** (proved glue; the statement of `teichGamma_equiv_teichSpace`).  `e [μ] = [X^μ]`
(`s33v_marked`); the inverse sends `[m]` to the class of its lifted coefficient (`s27u_liftCoeff_beltramiH`); both are
well defined and mutually inverse by `s27v_equiv_iff_fSym` (Theorem 27.1 through UT); `e [μ] = [m]` iff the normalized
lift of `m` (from UT) has the boundary values `f^μ` on `ℝ`, again by Theorem 27.1. -/
theorem s33v_teichGamma_equiv_teichSpace {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g)
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    ∃ e : TeichGamma Γ ≃ TeichSpace S, ∀ (μ : BeltramiGamma Γ) (m : MarkedRS S),
      e (Quotient.mk _ μ) = Quot.mk _ m ↔
        ∃ (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p' : UpperHalfPlane → m.X.carrier)
          (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (G : ExtPlane → ExtPlane),
          IsUniformization Γ' p' ∧ IsNormalizedLift p p' m.marking F G ∧
          ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = ((fMuSym μ.1.1 x : ℂ) : ExtPlane) := by
  have _ := hΓ
  have _ := hfree
  choose M hM using fun μ : BeltramiGamma Γ => s33v_marked hp μ
  choose B hB using fun m : MarkedRS S => s27u_liftCoeff_beltramiH hp m.qc
  have hiff : ∀ m₁ m₂ : MarkedRS S, m₁.Equiv m₂ ↔
      ∀ x : ℝ, s27u_fSym (s27u_liftCoeff p m₁.marking) x = s27u_fSym (s27u_liftCoeff p m₂.marking) x :=
    fun m₁ m₂ => s27v_equiv_iff_fSym hg hS hp m₁ m₂
  have hB' : ∀ m : MarkedRS S, s27u_fSym (B m).1 = s27u_fSym (s27u_liftCoeff p m.marking) := fun m => by
    rw [(hB m).1]
  let e : TeichGamma Γ ≃ TeichSpace S :=
    { toFun := Quotient.lift (fun μ => (Quot.mk _ (M μ) : TeichSpace S)) fun μ ν hμν => by
        refine Quot.sound ((hiff _ _).2 fun x => ?_)
        rw [hM μ, hM ν]
        exact hμν x
      invFun := Quot.lift (fun m => (Quotient.mk _ (⟨B m, (hB m).2⟩ : BeltramiGamma Γ) : TeichGamma Γ))
        fun m₁ m₂ h => by
          refine Quotient.sound (s := teichSetoidGamma Γ) fun x => ?_
          show s27u_fSym (B m₁).1 x = s27u_fSym (B m₂).1 x
          rw [hB' m₁, hB' m₂]
          exact (hiff m₁ m₂).1 h x
      left_inv := fun q => by
        induction q using Quotient.inductionOn with
        | h μ =>
          refine Quotient.sound (s := teichSetoidGamma Γ) fun x => ?_
          show s27u_fSym (B (M μ)).1 x = s27u_fSym μ.1.1 x
          rw [hB' (M μ), hM μ]
      right_inv := fun t => by
        induction t using Quot.inductionOn with
        | h m =>
          refine Quot.sound ((hiff _ _).2 fun x => ?_)
          exact (congrFun (hM ⟨B m, (hB m).2⟩) x).trans (congrFun (hB' m) x) }
  refine ⟨e, fun μ m => ?_⟩
  show (Quot.mk _ (M μ) : TeichSpace S) = Quot.mk _ m ↔ _
  rw [← s33v_fSym_eq]
  constructor
  · intro h
    have hE : (M μ).Equiv m := markedRS_equiv_equivalence.eqvGen_iff.1 (Quot.eqvGen_exact h)
    obtain ⟨Γ', p', F, G, hp', hN, -, hG⟩ := s27u_exists_uniformization hp m
    refine ⟨Γ', p', F, G, hp', hN, fun x => ?_⟩
    rw [hG x, ← (hiff _ _).1 hE x, hM μ]
  · rintro ⟨Γ', p', F, G, hp', hN, hG⟩
    obtain ⟨Γ₁, p₁, F₁, G₁, hp₁, hN₁, -, hG₁⟩ := s27u_exists_uniformization hp (M μ)
    refine Quot.sound ((thm27_1 hg hS hp (M μ) m hp₁ hp' hN₁ hN).2 fun x => ?_)
    rw [hG₁ x, hG x, hM μ]

/-- §33.1: `f^μ` projects to a quasiconformal map `f : S₀ → S^μ = ℍ/G^μ`, and `[S^μ, f]`
corresponds to `[μ]`: `T(S₀) ≅ M(G₀)/∼` (for `S₀ = ℍ/G₀` compact of genus `g > 1`; the
equivalence (33.2) holds for all Fuchsian groups of the first kind). -/
theorem teichGamma_equiv_teichSpace {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g)
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    ∃ e : TeichGamma Γ ≃ TeichSpace S, ∀ (μ : BeltramiGamma Γ) (m : MarkedRS S),
      e (Quotient.mk _ μ) = Quot.mk _ m ↔
        ∃ (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p' : UpperHalfPlane → m.X.carrier)
          (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (G : ExtPlane → ExtPlane),
          IsUniformization Γ' p' ∧ IsNormalizedLift p p' m.marking F G ∧
          ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = ((fMuSym μ.1.1 x : ℂ) : ExtPlane) := by
  exact s33v_teichGamma_equiv_teichSpace hg hS hΓ hfree hp

/-- The map equal to `g` on the closed lower half-plane `{Im z ≤ 0}` and to `g ∘ Φ` on `ℍ`, for a continuous
bijection `g` of `ℂ` and a continuous injective `Φ` which fixes every real point and maps `ℍ` onto `ℍ`, is a
continuous bijection of `ℂ`: the two formulas agree on `ℝ`, and `{Im z ≤ 0}` and `ℍ` are not mixed before `g` is
applied, so injectivity and surjectivity reduce to those of `g` and `Φ`. -/
theorem bg_f_piecewise {g Φ : ℂ → ℂ} (hgc : Continuous g) (hgi : Function.Injective g)
    (hgs : Function.Surjective g) (hΦc : Continuous Φ) (hΦi : Function.Injective Φ)
    (hΦx : ∀ x : ℝ, Φ x = x) (hΦU : Φ '' upperHalf = upperHalf) :
    Continuous (fun z : ℂ => if z.im ≤ 0 then g z else g (Φ z)) ∧
      Function.Injective (fun z : ℂ => if z.im ≤ 0 then g z else g (Φ z)) ∧
      (fun z : ℂ => if z.im ≤ 0 then g z else g (Φ z)) '' univ = univ := by
  -- `Φ` fixes every point of the real axis and maps `ℍ` into `ℍ`
  have hreal : ∀ w : ℂ, w.im = 0 → Φ w = w := fun w hw => by
    have hw' : ((w.re : ℝ) : ℂ) = w := Complex.ext (by simp) (by simp [hw])
    rw [← hw', hΦx]
  have hΦim : ∀ w : ℂ, 0 < w.im → 0 < (Φ w).im := fun w hw => by
    have hm : Φ w ∈ Φ '' upperHalf := mem_image_of_mem Φ hw
    rw [hΦU] at hm
    exact hm
  -- the two formulas
  have hR1 : ∀ w : ℂ, w.im ≤ 0 → (if w.im ≤ 0 then g w else g (Φ w)) = g w := fun w hw =>
    ite_eq_left hw
  have hR2 : ∀ w : ℂ, 0 < w.im → (if w.im ≤ 0 then g w else g (Φ w)) = g (Φ w) := fun w hw =>
    ite_eq_right (not_le.2 hw)
  refine ⟨?_, ?_, ?_⟩
  · -- continuity: the two formulas agree on `ℝ`
    refine Continuous.if_le hgc (hgc.comp hΦc) Complex.continuous_im continuous_const fun w hw => ?_
    show g w = g (Φ w)
    rw [hreal w hw]
  · -- injectivity: `{Im z ≤ 0}` and `ℍ` are not mixed
    intro a b hab
    have hab' : (if a.im ≤ 0 then g a else g (Φ a)) = (if b.im ≤ 0 then g b else g (Φ b)) := hab
    rcases le_or_gt a.im 0 with ha | ha <;> rcases le_or_gt b.im 0 with hb | hb
    · rw [hR1 a ha, hR1 b hb] at hab'
      exact hgi hab'
    · rw [hR1 a ha, hR2 b hb] at hab'
      have h1 := hΦim b hb
      rw [← hgi hab'] at h1
      linarith
    · rw [hR2 a ha, hR1 b hb] at hab'
      have h1 := hΦim a ha
      rw [hgi hab'] at h1
      linarith
    · rw [hR2 a ha, hR2 b hb] at hab'
      exact hΦi (hgi hab')
  · -- surjectivity: a preimage under `g` in `ℍ` is hit through `Φ(ℍ) = ℍ`
    refine eq_univ_of_forall fun w => ?_
    obtain ⟨v, rfl⟩ := hgs w
    rcases le_or_gt v.im 0 with hv | hv
    · exact ⟨v, mem_univ v, hR1 v hv⟩
    · have hm : v ∈ Φ '' upperHalf := by
        rw [hΦU]
        exact hv
      obtain ⟨z, hz, rfl⟩ := hm
      exact ⟨z, mem_univ z, hR2 z hz⟩

/-- **L1** ((⇒) of Lemma 33.1).  If `f^{μ₁} = f^{μ₂}` on `ℝ`, then `Φ := (f^{μ₂})⁻¹ ∘ f^{μ₁}` fixes `ℝ` pointwise and maps
`ℍ` onto `ℍ`; `F := f_{μ₂} ∘ Φ` on `ℍ` and `F := f_{μ₂}` on `{Im z ≤ 0}` is a homeomorphism of `ℂ`, q.c. on `ℍ` with
dilatation `μ₁` (`f_{μ₂} ∘ (f^{μ₂})⁻¹` is conformal on `ℍ`: `bg_conformal_of_dilatation_eq`, `bg_comp_conformal`) and
conformal on `𝕃`, hence q.c. on `ℂ` (`UniversalTeichmuller.ut2_ruh_glue`), normalized, with dilatation `μ₁` a.e., so
`F = f_{μ₁}` (`thm13_5_uniqueness_plane`); on `ℝ` this is `f_{μ₁} = f_{μ₂}`. -/
theorem bg_l_forward {μ₁ μ₂ : BeltramiH} (h : ∀ x : ℝ, fMuSym μ₁.1 x = fMuSym μ₂.1 x) :
    ∀ x : ℝ, normalizedSolution μ₁.1 x = normalizedSolution μ₂.1 x := by
  -- the symmetric solutions `f^{μⱼ}` and the normalized solutions `f_{μⱼ}`
  obtain ⟨k₁, hk₁0, hk₁1, hμ₁⟩ := bg_beltramiH_upper μ₁
  obtain ⟨k₂, hk₂0, hk₂1, hμ₂⟩ := bg_beltramiH_upper μ₂
  obtain ⟨hP₁U, -, -, hP₁KU, hP₁d⟩ := fMuSym_upperHalf hk₁0 hk₁1 hμ₁
  obtain ⟨hP₂U, -, -, hP₂KU, hP₂d⟩ := fMuSym_upperHalf hk₂0 hk₂1 hμ₂
  obtain ⟨-, -, hP₁K, -⟩ := bg_sym_spec hk₁0 hk₁1 hμ₁
  obtain ⟨-, ⟨-, hP₂s, -⟩, hP₂K, -⟩ := bg_sym_spec hk₂0 hk₂1 hμ₂
  obtain ⟨hQ₁qc, hQ₁s, hQ₁0, hQ₁1, hQ₁d⟩ := ut_spec μ₁
  obtain ⟨⟨KQ₂, hQ₂K⟩, hQ₂s, hQ₂0, hQ₂1, hQ₂d⟩ := ut_spec μ₂
  set P₁ := fMuSym μ₁.1
  set P₂ := fMuSym μ₂.1
  set Q₂ := normalizedSolution μ₂.1
  have hK1 : (1 : ℝ) ≤ (1 + k₁) / (1 - k₁) := hP₁KU.2.1
  have hP₁c : Continuous P₁ := continuousOn_univ.1 hP₁K.2.2.1.1
  have hP₁i : Function.Injective P₁ := injOn_univ.1 hP₁K.2.2.1.2.1
  have hQ₂c : Continuous Q₂ := continuousOn_univ.1 hQ₂K.2.2.1.1
  have hQ₂i : Function.Injective Q₂ := injOn_univ.1 hQ₂K.2.2.1.2.1
  have hQ₂surj : Function.Surjective Q₂ := fun w => by
    have hw : w ∈ Q₂ '' univ := by
      rw [hQ₂s]
      exact mem_univ w
    obtain ⟨z, -, hz⟩ := hw
    exact ⟨z, hz⟩
  -- `Φ = (f^{μ₂})⁻¹ ∘ f^{μ₁}` fixes `ℝ` pointwise and maps `ℍ` onto `ℍ`
  obtain ⟨e₂, he₂⟩ := t1_homeomorph hP₂K hP₂s
  have hsymm : ∀ z, e₂.symm (P₂ z) = z := fun z => by
    rw [← he₂]
    exact e₂.symm_apply_apply z
  set Φ : ℂ → ℂ := fun z => e₂.symm (P₁ z)
  have hΦx : ∀ x : ℝ, Φ x = x := fun x => by
    show e₂.symm (P₁ x) = x
    rw [h x, hsymm]
  have hΦU : Φ '' upperHalf = upperHalf := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hm : P₁ z ∈ P₂ '' upperHalf := by
        rw [hP₂U, ← hP₁U]
        exact mem_image_of_mem P₁ hz
      obtain ⟨v, hv, hvz⟩ := hm
      show e₂.symm (P₁ z) ∈ upperHalf
      rw [← hvz, hsymm]
      exact hv
    · intro hw
      have hm : P₂ w ∈ P₁ '' upperHalf := by
        rw [hP₁U, ← hP₂U]
        exact mem_image_of_mem P₂ hw
      obtain ⟨z, hz, hzw⟩ := hm
      refine ⟨z, hz, ?_⟩
      show e₂.symm (P₁ z) = w
      rw [hzw, hsymm]
  -- the glued map `F`: `f_{μ₂}` on `{Im z ≤ 0}`, `f_{μ₂} ∘ Φ` on `ℍ`
  set F : ℂ → ℂ := fun z => if z.im ≤ 0 then Q₂ z else Q₂ (Φ z)
  obtain ⟨hFc, hFi, hFs⟩ := bg_f_piecewise (Φ := Φ) hQ₂c hQ₂i hQ₂surj (e₂.symm.continuous.comp hP₁c)
    (e₂.symm.injective.comp hP₁i) hΦx hΦU
  -- on `ℍ`: `F = φ ∘ f^{μ₁}` with `φ = f_{μ₂} ∘ (f^{μ₂})⁻¹` conformal on `ℍ`
  have hQ₂KU : IsKQC Q₂ upperHalf KQ₂ := ac_t_isKQC_restrict hQ₂K isOpen_upperHalf (subset_univ _)
  have hdil₂ : ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation Q₂ z = complexDilatation P₂ z := by
    filter_upwards [ae_restrict_of_ae hQ₂d, hP₂d] with z h1 h2
    rw [h1, h2]
  have hφ := bg_conformal_of_dilatation_eq hP₂KU hQ₂KU hdil₂
  rw [hP₂U] at hφ
  obtain ⟨hcKU, hcdU⟩ := bg_comp_conformal hP₁KU isOpen_upperHalf hφ hP₁U.subset
  have hinv : ∀ w ∈ upperHalf, Function.invFunOn P₂ upperHalf w = e₂.symm w := fun w hw => by
    rw [← hP₂U] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    rw [hP₂KU.2.2.1.2.1.leftInvOn_invFunOn hv, hsymm]
  have hEqU : EqOn F ((Q₂ ∘ Function.invFunOn P₂ upperHalf) ∘ P₁) upperHalf := fun z hz => by
    have hP₁z : P₁ z ∈ upperHalf := hP₁U ▸ mem_image_of_mem P₁ hz
    show (if z.im ≤ 0 then Q₂ z else Q₂ (e₂.symm (P₁ z))) = Q₂ (Function.invFunOn P₂ upperHalf (P₁ z))
    rw [ite_eq_right (not_le.2 (show 0 < z.im from hz)), hinv _ hP₁z]
  have hFKU : IsKQC F upperHalf ((1 + k₁) / (1 - k₁)) := ad_isKQC_congr hcKU hEqU
  have hFdU : ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation F z = μ₁.1 z := by
    filter_upwards [hcdU, hP₁d, ae_restrict_mem isOpen_upperHalf.measurableSet] with z h1 h2 hz
    rw [bg_dilatation_congr isOpen_upperHalf hEqU hz, h1, h2]
  -- on `𝕃`: `F = f_{μ₂}` is conformal
  have hEqL : EqOn F Q₂ lowerHalf := fun z hz => ite_eq_left (le_of_lt (show z.im < 0 from hz))
  have hFKL : IsKQC F lowerHalf ((1 + k₁) / (1 - k₁)) :=
    ad_isKQC_congr ((isKQC_one_of_conformal isOpen_lowerHalf (ut_conformal_lowerHalf μ₂)).mono hK1) hEqL
  have hFdL : ∀ᵐ z ∂(volume.restrict lowerHalf), complexDilatation F z = μ₁.1 z := by
    filter_upwards [ae_restrict_of_ae hQ₂d, ae_restrict_mem isOpen_lowerHalf.measurableSet] with z h1 hz
    rw [bg_dilatation_congr isOpen_lowerHalf hEqL hz, h1, μ₂.2.2 z (le_of_lt hz), μ₁.2.2 z (le_of_lt hz)]
  -- `F` is a normalized q.c. map of `ℂ` with dilatation `μ₁`, hence `F = f_{μ₁}`
  have hFhom : IsHomeomorphOnto F univ (F '' univ) :=
    qcl_f_isHomeomorphOnto_of_injOn isOpen_univ hFc.continuousOn (injOn_of_injective hFi)
  have hFK : IsKQC F univ ((1 + k₁) / (1 - k₁)) := UniversalTeichmuller.ut2_ruh_glue hK1 hFhom hFKU hFKL
  have hF0 : F 0 = 0 := (ite_eq_left (le_of_eq Complex.zero_im)).trans hQ₂0
  have hF1 : F 1 = 1 := (ite_eq_left (le_of_eq Complex.one_im)).trans hQ₂1
  have hFQ₁ : F = normalizedSolution μ₁.1 := by
    refine thm13_5_uniqueness_plane ⟨_, hFK⟩ hQ₁qc hFs hQ₁s ?_ hF0 hF1 hQ₁0 hQ₁1
    filter_upwards [bg_ae_of_halves hFdU hFdL, hQ₁d] with z h1 h2
    rw [h1, h2]
  -- on `ℝ`: `f_{μ₁} = F = f_{μ₂}`
  intro x
  rw [← hFQ₁]
  exact ite_eq_left (le_of_eq (Complex.ofReal_im x))

/-- The reflection across `ℝ` of a homeomorphism `Φ` of `ℂ` which fixes `{Im z ≤ 0}` pointwise: the map equal to `Φ`
on `{Im z ≥ 0}` and to `z ↦ conj (Φ (conj z))` on `𝕃` is a continuous bijection of `ℂ`.  (`Φ` maps `ℍ` into `ℍ`, since a
point of `ℍ` sent into `{Im z ≤ 0}` would be sent to a fixed point, and dually `Φ⁻¹` maps `ℍ` into `ℍ`.) -/
theorem bg_b_refl_spec (Φ : ℂ ≃ₜ ℂ) (hfix : ∀ z : ℂ, z.im ≤ 0 → Φ z = z) :
    ∃ Ψ : ℂ → ℂ, Continuous Ψ ∧ Function.Injective Ψ ∧ Function.Surjective Ψ ∧
      (∀ z : ℂ, 0 ≤ z.im → Ψ z = Φ z) ∧ ∀ z : ℂ, z.im < 0 → Ψ z = conj (Φ (conj z)) := by
  -- `Φ` maps `ℍ` into `ℍ` and `{Im z ≥ 0}` into itself
  have hU : ∀ z : ℂ, 0 < z.im → 0 < (Φ z).im := fun z hz => by
    rcases le_or_gt (Φ z).im 0 with hle | hlt
    · have h2 : Φ z = z := Φ.injective (hfix _ hle)
      rw [h2] at hle
      linarith
    · exact hlt
  have hU' : ∀ z : ℂ, 0 ≤ z.im → 0 ≤ (Φ z).im := fun z hz => by
    rcases hz.lt_or_eq with hlt | heq
    · exact (hU z hlt).le
    · rw [hfix z heq.ge]
      exact hz
  -- `Φ⁻¹` maps `ℍ` into `ℍ`
  have hUs : ∀ w : ℂ, 0 < w.im → 0 < (Φ.symm w).im := fun w hw => by
    rcases le_or_gt (Φ.symm w).im 0 with hle | hlt
    · have h2 := hfix _ hle
      rw [Homeomorph.apply_symm_apply] at h2
      rw [← h2] at hle
      linarith
    · exact hlt
  have hconj : ∀ z : ℂ, z.im < 0 → 0 < (conj z).im := fun z hz => by
    rw [Complex.conj_im]
    linarith
  refine ⟨fun z => if 0 ≤ z.im then Φ z else conj (Φ (conj z)), ?_, ?_, ?_,
    fun z hz => ite_eq_left hz, fun z hz => ite_eq_right (not_le.2 hz)⟩
  · -- continuity: the two formulas agree on `ℝ`
    refine Continuous.if_le Φ.continuous
      (Complex.continuous_conj.comp (Φ.continuous.comp Complex.continuous_conj))
      continuous_const Complex.continuous_im fun z hz => ?_
    have hz' : z.im = 0 := hz.symm
    have hcz : conj z = z := Complex.conj_eq_iff_im.2 hz'
    show Φ z = conj (Φ (conj z))
    rw [hcz, hfix z hz'.le, hcz]
  · -- injectivity: `{Im z ≥ 0}` and `𝕃` are both invariant
    intro a b hab
    dsimp only at hab
    rcases le_or_gt 0 a.im with ha | ha <;> rcases le_or_gt 0 b.im with hb | hb
    · rw [ite_eq_left ha, ite_eq_left hb] at hab
      exact Φ.injective hab
    · rw [ite_eq_left ha, ite_eq_right (not_le.2 hb)] at hab
      have h1 := hU' a ha
      have h2 := hU _ (hconj b hb)
      rw [hab, Complex.conj_im] at h1
      linarith
    · rw [ite_eq_right (not_le.2 ha), ite_eq_left hb] at hab
      have h1 := hU' b hb
      have h2 := hU _ (hconj a ha)
      rw [← hab, Complex.conj_im] at h1
      linarith
    · rw [ite_eq_right (not_le.2 ha), ite_eq_right (not_le.2 hb)] at hab
      have h1 : Φ (conj a) = Φ (conj b) := by
        have h := congrArg conj hab
        rwa [Complex.conj_conj, Complex.conj_conj] at h
      have h2 := congrArg conj (Φ.injective h1)
      rwa [Complex.conj_conj, Complex.conj_conj] at h2
  · -- surjectivity
    intro w
    rcases lt_trichotomy w.im 0 with hw | hw | hw
    · refine ⟨conj (Φ.symm (conj w)), ?_⟩
      have h0 : 0 < (Φ.symm (conj w)).im := hUs _ (hconj w hw)
      have h1 : ¬ 0 ≤ (conj (Φ.symm (conj w))).im := by
        rw [Complex.conj_im]
        linarith
      show (if 0 ≤ (conj (Φ.symm (conj w))).im then Φ (conj (Φ.symm (conj w)))
        else conj (Φ (conj (conj (Φ.symm (conj w)))))) = w
      rw [ite_eq_right h1, Complex.conj_conj, Homeomorph.apply_symm_apply, Complex.conj_conj]
    · refine ⟨w, ?_⟩
      show (if 0 ≤ w.im then Φ w else conj (Φ (conj w))) = w
      rw [ite_eq_left hw.ge, hfix w hw.le]
    · refine ⟨Φ.symm w, ?_⟩
      show (if 0 ≤ (Φ.symm w).im then Φ (Φ.symm w) else conj (Φ (conj (Φ.symm w)))) = w
      rw [ite_eq_left (hUs w hw).le, Homeomorph.apply_symm_apply]

/-- **L2** ((⇐) of Lemma 33.1).  If `f_{μ₁} = f_{μ₂}` on `ℝ`, then they agree on `{Im z ≤ 0}` and `f_{μ₁}(ℍ) = f_{μ₂}(ℍ)`
(`ut_welding`), so `Φ := f_{μ₂}⁻¹ ∘ f_{μ₁}` is the identity on `{Im z ≤ 0}` and maps `ℍ` onto `ℍ`; `H := f^{μ₂} ∘ Φ` on
`{Im z ≥ 0}`, extended to `𝕃` by the reflection `H(z) = conj H(z̄)`, is a homeomorphism of `ℂ`, q.c. on `ℍ` with
dilatation `μ₁` (`f^{μ₂} ∘ f_{μ₂}⁻¹` is conformal on `f_{μ₂}(ℍ)`) and on `𝕃` with dilatation `conj μ₁(z̄)`
(`bg_dilatation_conj`), hence the normalized solution for `symmetricExtension μ₁`, i.e. `H = f^{μ₁}` (`bg_sym_spec`); on
`ℝ` this is `f^{μ₁} = f^{μ₂}`. -/
theorem bg_l_backward {μ₁ μ₂ : BeltramiH} (h : ∀ x : ℝ, normalizedSolution μ₁.1 x = normalizedSolution μ₂.1 x) :
    ∀ x : ℝ, fMuSym μ₁.1 x = fMuSym μ₂.1 x := by
  -- the coefficients, `f^{μⱼ}` (`bg_sym_spec`, `fMuSym_upperHalf`) and `f_{μⱼ}` (`ut_spec`)
  obtain ⟨k₁, hk₁0, hk₁1, hμ₁⟩ := bg_beltramiH_upper μ₁
  obtain ⟨k₂, hk₂0, hk₂1, hμ₂⟩ := bg_beltramiH_upper μ₂
  obtain ⟨-, -, -, hP₁uniq⟩ := bg_sym_spec hk₁0 hk₁1 hμ₁
  obtain ⟨-, ⟨-, hP₂s, hP₂0, hP₂1, -⟩, hP₂K, -⟩ := bg_sym_spec hk₂0 hk₂1 hμ₂
  obtain ⟨-, -, hP₂conj, hP₂KU, hP₂d⟩ := fMuSym_upperHalf hk₂0 hk₂1 hμ₂
  obtain ⟨⟨K₁, hQ₁K⟩, hQ₁s, -, -, hQ₁d⟩ := ut_spec μ₁
  obtain ⟨⟨K₂, hQ₂K⟩, hQ₂s, -, -, hQ₂d⟩ := ut_spec μ₂
  obtain ⟨hwL, hwU⟩ := ut_welding h
  obtain ⟨e₁, he₁⟩ := t1_homeomorph hQ₁K hQ₁s
  obtain ⟨e₂, he₂⟩ := t1_homeomorph hQ₂K hQ₂s
  have hP₂c : Continuous (fMuSym μ₂.1) := continuousOn_univ.1 hP₂K.2.2.1.1
  have hP₂i : Function.Injective (fMuSym μ₂.1) := injOn_univ.1 hP₂K.2.2.1.2.1
  have hP₂surj : Function.Surjective (fMuSym μ₂.1) := fun w => by
    have hw : w ∈ fMuSym μ₂.1 '' univ := by
      rw [hP₂s]
      exact mem_univ w
    obtain ⟨z, -, hz⟩ := hw
    exact ⟨z, hz⟩
  have hQ₂i : Function.Injective (normalizedSolution μ₂.1) := injOn_univ.1 hQ₂K.2.2.1.2.1
  -- `Φ = f_{μ₂}⁻¹ ∘ f_{μ₁}` fixes `{Im z ≤ 0}` pointwise; `Ψ` is its reflection across `ℝ`
  have hΦQ : ∀ z, normalizedSolution μ₁.1 z = normalizedSolution μ₂.1 ((e₁.trans e₂.symm) z) := fun z => by
    rw [Homeomorph.trans_apply, ← he₂, Homeomorph.apply_symm_apply, he₁]
  have hfix : ∀ z : ℂ, z.im ≤ 0 → (e₁.trans e₂.symm) z = z := fun z hz => by
    rw [Homeomorph.trans_apply, he₁, hwL z hz, ← he₂, Homeomorph.symm_apply_apply]
  obtain ⟨Ψ, hΨc, hΨi, hΨs, hΨU, hΨL⟩ := bg_b_refl_spec (e₁.trans e₂.symm) hfix
  have hΨfix : ∀ z : ℂ, z.im = 0 → Ψ z = z := fun z hz => by
    rw [hΨU z hz.ge, hfix z hz.le]
  -- on `ℍ`: `H = f^{μ₂} ∘ Ψ = (f^{μ₂} ∘ f_{μ₂}⁻¹) ∘ f_{μ₁}`, where `f^{μ₂} ∘ f_{μ₂}⁻¹` is conformal on `f_{μ₂}(ℍ)`
  have hQ₁U : IsKQC (normalizedSolution μ₁.1) upperHalf K₁ :=
    ac_t_isKQC_restrict hQ₁K isOpen_upperHalf (subset_univ _)
  have hQ₂U : IsKQC (normalizedSolution μ₂.1) upperHalf K₂ :=
    ac_t_isKQC_restrict hQ₂K isOpen_upperHalf (subset_univ _)
  have hdil : ∀ᵐ z ∂(volume.restrict upperHalf),
      complexDilatation (fMuSym μ₂.1) z = complexDilatation (normalizedSolution μ₂.1) z := by
    filter_upwards [hP₂d, ae_restrict_of_ae hQ₂d] with z h1 h2
    rw [h1, h2]
  have hψ := bg_conformal_of_dilatation_eq hQ₂U hP₂KU hdil
  have hopen : IsOpen (normalizedSolution μ₂.1 '' upperHalf) := by
    rw [← he₂]
    exact e₂.isOpenMap _ isOpen_upperHalf
  have hcomp := bg_comp_conformal hQ₁U hopen hψ hwU.subset
  have hEqU : EqOn (fMuSym μ₂.1 ∘ Ψ)
      ((fMuSym μ₂.1 ∘ Function.invFunOn (normalizedSolution μ₂.1) upperHalf) ∘ normalizedSolution μ₁.1)
      upperHalf := by
    intro z hz
    have hmem : normalizedSolution μ₁.1 z ∈ normalizedSolution μ₂.1 '' upperHalf := by
      rw [← hwU]
      exact mem_image_of_mem _ hz
    have h1 : Function.invFunOn (normalizedSolution μ₂.1) upperHalf (normalizedSolution μ₁.1 z) =
        (e₁.trans e₂.symm) z :=
      hQ₂i ((Function.invFunOn_eq hmem).trans (hΦQ z))
    show fMuSym μ₂.1 (Ψ z) =
      fMuSym μ₂.1 (Function.invFunOn (normalizedSolution μ₂.1) upperHalf (normalizedSolution μ₁.1 z))
    rw [h1, hΨU z (le_of_lt hz)]
  have hHU : IsKQC (fMuSym μ₂.1 ∘ Ψ) upperHalf K₁ := ad_isKQC_congr hcomp.1 hEqU
  have hdHU : ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation (fMuSym μ₂.1 ∘ Ψ) z = μ₁.1 z := by
    filter_upwards [hcomp.2, ae_restrict_of_ae hQ₁d, ae_restrict_mem isOpen_upperHalf.measurableSet]
      with z h1 h2 hz
    rw [bg_dilatation_congr isOpen_upperHalf hEqU hz, h1, h2]
  -- on `𝕃`: `H(z) = conj H(z̄)`
  have hpre : conj ⁻¹' upperHalf = lowerHalf := by
    ext z
    show 0 < (conj z).im ↔ z.im < 0
    rw [Complex.conj_im, neg_pos]
  have hEqL : EqOn (fMuSym μ₂.1 ∘ Ψ) (fun z => conj ((fMuSym μ₂.1 ∘ Ψ) (conj z))) lowerHalf := by
    intro z hz
    have hz' : z.im < 0 := hz
    have hcz : 0 ≤ (conj z).im := by
      rw [Complex.conj_im]
      linarith
    show fMuSym μ₂.1 (Ψ z) = conj (fMuSym μ₂.1 (Ψ (conj z)))
    rw [hΨL z hz', hΨU (conj z) hcz, hP₂conj]
  have hHL : IsKQC (fMuSym μ₂.1 ∘ Ψ) lowerHalf K₁ := by
    have h1 := abR_x_isKQC_conj hHU
    rw [hpre] at h1
    exact ad_isKQC_congr h1 hEqL
  have hdHL : ∀ᵐ z ∂(volume.restrict lowerHalf),
      complexDilatation (fMuSym μ₂.1 ∘ Ψ) z = symmetricExtension μ₁.1 z := by
    have hmp : MeasurePreserving (fun z : ℂ => conj z) (volume.restrict (conj ⁻¹' upperHalf))
        (volume.restrict upperHalf) :=
      gzE_conj_measurePreserving.restrict_preimage isOpen_upperHalf.measurableSet
    rw [hpre] at hmp
    filter_upwards [hmp.quasiMeasurePreserving.ae hdHU, ae_restrict_mem isOpen_lowerHalf.measurableSet]
      with z h1 hz
    have h1' : complexDilatation (fMuSym μ₂.1 ∘ Ψ) (conj z) = μ₁.1 (conj z) := h1
    rw [bg_dilatation_congr isOpen_lowerHalf hEqL hz, bg_dilatation_conj, h1']
    exact (ite_eq_left (show z.im < 0 from hz)).symm
  have hdHU' : ∀ᵐ z ∂(volume.restrict upperHalf),
      complexDilatation (fMuSym μ₂.1 ∘ Ψ) z = symmetricExtension μ₁.1 z := by
    filter_upwards [hdHU, ae_restrict_mem isOpen_upperHalf.measurableSet] with z h1 hz
    rw [h1]
    exact (ite_eq_right (not_lt.2 (le_of_lt (show 0 < z.im from hz)))).symm
  -- `H` is a normalized solution for `symmetricExtension μ₁`, hence `H = f^{μ₁}`
  have hHhom : IsHomeomorphOnto (fMuSym μ₂.1 ∘ Ψ) univ ((fMuSym μ₂.1 ∘ Ψ) '' univ) :=
    qcl_f_isHomeomorphOnto_of_injOn isOpen_univ (hP₂c.comp hΨc).continuousOn
      (injOn_of_injective (hP₂i.comp hΨi))
  have hHK : IsKQC (fMuSym μ₂.1 ∘ Ψ) univ K₁ := UniversalTeichmuller.ut2_ruh_glue hQ₁K.2.1 hHhom hHU hHL
  have hHs : (fMuSym μ₂.1 ∘ Ψ) '' univ = univ := by
    rw [image_univ]
    exact (hP₂surj.comp hΨs).range_eq
  have hH0 : (fMuSym μ₂.1 ∘ Ψ) 0 = 0 := by
    show fMuSym μ₂.1 (Ψ 0) = 0
    rw [hΨfix 0 Complex.zero_im, hP₂0]
  have hH1 : (fMuSym μ₂.1 ∘ Ψ) 1 = 1 := by
    show fMuSym μ₂.1 (Ψ 1) = 1
    rw [hΨfix 1 Complex.one_im, hP₂1]
  have hNS : IsNormalizedSolution (fMuSym μ₂.1 ∘ Ψ) (symmetricExtension μ₁.1) :=
    ⟨⟨K₁, hHK⟩, hHs, hH0, hH1, bg_ae_of_halves hdHU' hdHL⟩
  intro x
  rw [← hP₁uniq _ hNS]
  show fMuSym μ₂.1 (Ψ x) = fMuSym μ₂.1 x
  rw [hΨfix x (Complex.ofReal_im x)]

/-- **Lemma 33.1** (33.9)–(33.10): for bounded measurable `μ₁, μ₂` on `ℍ` with `‖μⱼ‖_∞ < 1`,
`f^{μ₁}|ℝ = f^{μ₂}|ℝ` iff `f_{μ₁}|ℝ = f_{μ₂}|ℝ`, where `f_μ` is the normalized map with dilatation `μ`
on `ℍ` and `0` on `𝕃`. -/
theorem lemma33_1 (μ₁ μ₂ : BeltramiH) :
    (∀ x : ℝ, fMuSym μ₁.1 x = fMuSym μ₂.1 x) ↔ ∀ x : ℝ, normalizedSolution μ₁.1 x = normalizedSolution μ₂.1 x := by
  exact ⟨bg_l_forward, bg_l_backward⟩

/-- §33.1: since `f_μ` is conformal in `𝕃`, `f_μ|𝕃` determines `f_μ|ℝ` and conversely; so
`{f_μ|𝕃 : μ ∈ M(G₀)}` (a family of univalent functions) is a model of `T(S₀)` (or `T(G₀)`). -/
theorem fMu_lower_model (μ₁ μ₂ : BeltramiH) :
    EqOn (normalizedSolution μ₁.1) (normalizedSolution μ₂.1) lowerHalf ↔
      ∀ x : ℝ, normalizedSolution μ₁.1 x = normalizedSolution μ₂.1 x := by
  constructor
  · intro h x
    obtain ⟨⟨K₁, hK₁⟩, -⟩ := ut_spec μ₁
    obtain ⟨⟨K₂, hK₂⟩, -⟩ := ut_spec μ₂
    have hcl : EqOn (normalizedSolution μ₁.1) (normalizedSolution μ₂.1) (closure lowerHalf) :=
      h.of_subset_closure (hK₁.2.2.1.1.mono (subset_univ _)) (hK₂.2.2.1.1.mono (subset_univ _))
        subset_closure subset_rfl
    refine hcl ?_
    rw [show lowerHalf = {z : ℂ | z.im < 0} from rfl, Complex.closure_setOfPred_im_lt]
    show ((x : ℂ)).im ≤ 0
    rw [Complex.ofReal_im]
  · intro h z hz
    exact (ut_welding h).1 z (le_of_lt hz)

/-! ## §33.2 The Teichmüller space of a Fuchsian group -/

/-- §33.2: for the trivial group every `μ` with `‖μ‖_∞ < 1` is compatible, `M({I}) = M` and
`T({I}) = T` is the universal Teichmüller space of §21. -/
theorem teichGamma_bot_equiv_universal :
    (∀ μ : BeltramiH, IsGammaCompatible ⊥ μ.1) ∧ Nonempty (TeichGamma ⊥ ≃ UniversalTeichmuller) := by
  have hc : ∀ μ : BeltramiH, IsGammaCompatible ⊥ μ.1 := by
    intro μ γ hγ
    rw [Subgroup.mem_bot] at hγ
    subst hγ
    refine Filter.Eventually.of_forall fun z => ?_
    simp
  exact ⟨hc, ⟨Quotient.congr ⟨fun μ => μ.1, fun μ => ⟨μ, hc μ⟩, fun _ => rfl, fun _ => rfl⟩
    fun μ ν => lemma33_1 μ.1 ν.1⟩⟩

/-! ## §33.3 The Bers embedding -/

/-- The space `Q(G₀, 𝕃)` of holomorphic quadratic differentials on the lower half-plane which are
automorphic for `G₀`: `φ(γz) γ'(z)² = φ(z)`, `γ ∈ G₀`, `z ∈ 𝕃` (as functions vanishing off `𝕃`).
With the norm `‖φ‖ = sup_{z ∈ 𝕃} |y² φ(z)|` it is a Banach space, a subspace of `A(𝕃)`. -/
def automorphicQD (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Submodule ℂ (ℂ → ℂ) where
  carrier := {φ | DifferentiableOn ℂ φ lowerHalf ∧ (∀ z, z ∉ lowerHalf → φ z = 0) ∧
    ∀ γ ∈ Γ, ∀ z ∈ lowerHalf,
      φ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z}
  add_mem' := by
    rintro φ ψ ⟨h₁, h₂, h₃⟩ ⟨k₁, k₂, k₃⟩
    refine ⟨h₁.add k₁, fun z hz => by simp [h₂ z hz, k₂ z hz], fun γ hγ z hz => ?_⟩
    simp only [Pi.add_apply]
    rw [add_div, h₃ γ hγ z hz, k₃ γ hγ z hz]
  zero_mem' := ⟨differentiableOn_const 0, fun _ _ => rfl, fun _ _ _ _ => by simp⟩
  smul_mem' := by
    rintro c φ ⟨h₁, h₂, h₃⟩
    refine ⟨h₁.const_smul c, fun z hz => by simp [h₂ z hz], fun γ hγ z hz => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_div_assoc, h₃ γ hγ z hz]

/-- §33.3: `φ_μ = S_{f_μ}|𝕃`, the Schwarzian derivative of the univalent function `f_μ|𝕃`. -/
def bersFunctionGamma (μ : BeltramiGamma Γ) : ℂ → ℂ := bersFunction μ.1.1

/-! ### S33-B track interface (coordinator 553e2d): (33.11), MOB, the sharp Bers bound -/

/-- (A) The pole `-d/c` of `γ ∈ SL(2, ℝ)` is real (or absent), so `cz + d ≠ 0` on `𝕃`: if `c ≠ 0` then
`Im (cz + d) = c Im z ≠ 0`, and if `c = 0` then `ad = 1` forces `d ≠ 0`. -/
theorem bg2_a_den_ne (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z ∈ lowerHalf) :
    (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := by
  intro h0
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have h1 : γ 1 0 * z.im = 0 := by
    have h := congrArg Complex.im h0
    simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, zero_im] at h
    exact h
  have h2 : γ 1 0 * z.re + γ 1 1 = 0 := by
    have h := congrArg Complex.re h0
    simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, zero_re] at h
    exact h
  have hc : γ 1 0 = 0 := (mul_eq_zero.1 h1).resolve_right (show z.im < 0 from hz).ne
  rw [hc, zero_mul, zero_add] at h2
  rw [hc, h2, mul_zero, mul_zero, sub_zero] at hdet
  exact zero_ne_one hdet

/-- (A) `γ ∈ SL(2, ℝ)` maps `𝕃` into `𝕃`: `Im (γ z) = Im z/|cz + d|²` (`im_realMobius`, `ad - bc = 1`). -/
theorem bg2_a_mem (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z ∈ lowerHalf) :
    mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z ∈ lowerHalf := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  show (realMobius (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z).im < 0
  rw [im_realMobius, hdet, one_mul]
  exact div_neg_of_neg_of_pos hz (normSq_pos.2 (bg2_a_den_ne γ hz))

/-- (A) The chain rule for `f_μ ∘ γ` on `𝕃`: `S_{f_μ ∘ γ}(z) = S_{f_μ}(γ z)/(cz + d)⁴` (`eq19_1_chain_rule`, with
`γ'(z) = (cz + d)⁻²` from `hasDerivAt_mobius`, `S_γ = 0` from `schwarzian_mobius`, and `f_μ` conformal at `γ z ∈ 𝕃`). -/
theorem bg2_a_chain (μ : BeltramiH) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z ∈ lowerHalf) :
    schwarzian (normalizedSolution μ.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z =
      schwarzian (normalizedSolution μ.1) (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) /
        ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 := by
  have hconf := ut_conformal_lowerHalf μ
  have hden := bg2_a_den_ne γ hz
  have hw := bg2_a_mem γ hz
  have hdetC : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have hA : AnalyticAt ℂ (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z :=
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => (γ 0 0 : ℂ) * w + γ 0 1) z).div
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => (γ 1 0 : ℂ) * w + γ 1 1) z) hden
  have hd : deriv (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z = 1 / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 := by
    have h := (hasDerivAt_mobius (a := (γ 0 0 : ℂ)) (b := (γ 0 1 : ℂ)) hden).deriv
    rw [hdetC] at h
    exact h
  have hd0 : deriv (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z ≠ 0 := by
    rw [hd]
    exact one_div_ne_zero (pow_ne_zero 2 hden)
  have hS : schwarzian (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z = 0 :=
    schwarzian_mobius (by rw [hdetC]; exact one_ne_zero) z
  rw [eq19_1_chain_rule hA hd0 (hconf.1.analyticAt (isOpen_lowerHalf.mem_nhds hw))
    (deriv_ne_zero_of_injOn isOpen_lowerHalf hconf.1 hconf.2.1 hw), hS, add_zero, hd]
  field_simp

/-- **A** ((33.11) for any `μ ∈ M`): `φ_μ ∈ Q(G₀, 𝕃)` iff `S_{f_μ ∘ γ} = S_{f_μ}` on `𝕃` for every `γ ∈ G₀`.  `φ_μ` is
holomorphic on `𝕃` and vanishes off it (as in `bersMapU_mem`); `γ ∈ SL(2, ℝ)` maps `𝕃` into `𝕃`, with `γ' = (cz + d)⁻²` and
`S_γ = 0` (`schwarzian_mobius`), so `S_{f_μ ∘ γ}(z) = S_{f_μ}(γ z)/(cz + d)⁴` (`eq19_1_chain_rule`), and automorphy at `z` is
`S_{f_μ ∘ γ}(z) = S_{f_μ}(z)`. -/
theorem bg2_auto_iff (μ : BeltramiH) :
    bersFunction μ.1 ∈ automorphicQD Γ ↔
      ∀ γ ∈ Γ, EqOn (schwarzian (normalizedSolution μ.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)))
        (schwarzian (normalizedSolution μ.1)) lowerHalf := by
  have hconf := ut_conformal_lowerHalf μ
  -- automorphy at `z` is `S_{f_μ ∘ γ}(z) = S_{f_μ}(z)`
  have hkey : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ z ∈ lowerHalf,
      bersFunction μ.1 ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 =
        schwarzian (normalizedSolution μ.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z := by
    intro γ z hz
    change lowerHalf.indicator (schwarzian (normalizedSolution μ.1))
      (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) / _ = _
    rw [indicator_of_mem (bg2_a_mem γ hz), bg2_a_chain μ γ hz]
  constructor
  · intro hmem γ hγ z hz
    obtain ⟨-, -, h3⟩ := hmem
    rw [← hkey γ z hz, h3 γ hγ z hz, bersFunction, indicator_of_mem hz]
  · intro h
    refine ⟨?_, fun z hz => indicator_of_notMem hz _, fun γ hγ z hz => ?_⟩
    · refine (schwarzian_holomorphic isOpen_lowerHalf
        (isLocUnivMero_of_isConformalOnto isOpen_lowerHalf hconf)).congr fun z hz => ?_
      exact indicator_of_mem hz _
    · rw [hkey γ z hz, h γ hγ hz, bersFunction, indicator_of_mem hz]

/-- **N** (normalization): a `K`-q.c. map `G` of the plane onto itself with complex dilatation `μ` a.e. (`μ ∈ M`) is `f_μ`
up to an affine map: `f_μ = (G - G 0)/(G 1 - G 0)` (`bB_l_affine_isKQC`, `s23_dilatation_comp_left`,
`thm13_5_uniqueness_plane`). -/
theorem bg2_normalize (μ : BeltramiH) {G : ℂ → ℂ} {K : ℝ} (hG : IsKQC G univ K) (hs : G '' univ = univ)
    (hd : ∀ᵐ z, complexDilatation G z = μ.1 z) :
    ∀ z, normalizedSolution μ.1 z = (G z - G 0) / (G 1 - G 0) := by
  have ha : G 1 - G 0 ≠ 0 := fun h =>
    one_ne_zero (hG.2.2.1.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
  obtain ⟨hK, hs'⟩ := bB_l_affine_isKQC hG hs (G 0) ha
  have hGc : Continuous G := continuousOn_univ.1 hG.2.2.1.1
  have hdil : ∀ z, complexDilatation (fun ζ => (G ζ - G 0) / (G 1 - G 0)) z = complexDilatation G z := by
    intro z
    have h := s23_dilatation_comp_left (g := G) (z := z) (h := fun w => (w - G 0) / (G 1 - G 0))
      (k := fun u => (G 1 - G 0) * u + G 0) hGc.continuousAt (by fun_prop) (by fun_prop)
      (Eventually.of_forall fun w => by field_simp; ring)
    exact h
  have heq := thm13_5_uniqueness_plane (ut_spec μ).1 ⟨K, hK⟩ (ut_spec μ).2.1 hs' ?_ (ut_spec μ).2.2.1
    (ut_spec μ).2.2.2.1 (by simp) (by simp [div_self ha])
  · exact fun z => congrFun heq z
  · filter_upwards [(ut_spec μ).2.2.2.2, hd] with z h1 h2
    rw [h1, hdil z, h2]

/-- A real Möbius transformation of determinant `1` has its pole on the real axis: `c z + d ≠ 0` for `Im z ≠ 0`. -/
theorem bg2_d_den_ne_zero {a b c d : ℝ} (h : a * d - b * c = 1) {z : ℂ} (hz : z.im ≠ 0) :
    (c : ℂ) * z + d ≠ 0 := by
  intro h0
  have him : c * z.im = 0 := by simpa using congrArg Complex.im h0
  have hc : c = 0 := (mul_eq_zero.1 him).resolve_right hz
  have hd : d = 0 := by simpa [hc] using congrArg Complex.re h0
  rw [hc, hd, mul_zero, mul_zero, sub_zero] at h
  exact zero_ne_one h

/-- The derivative of `z ↦ (a z + b)/(c z + d)` with `a d - b c = 1` off its pole is `1/(c z + d)²`. -/
theorem bg2_d_deriv {a b c d : ℂ} (h : a * d - b * c = 1) {z : ℂ} (hz : c * z + d ≠ 0) :
    HasDerivAt (mobiusFn a b c d) (1 / (c * z + d) ^ 2) z := by
  have h1 : HasDerivAt (fun y : ℂ => a * y + b) a z := by
    simpa using ((hasDerivAt_id' z).const_mul a).add_const b
  have h2 : HasDerivAt (fun y : ℂ => c * y + d) c z := by
    simpa using ((hasDerivAt_id' z).const_mul c).add_const d
  have h3 := h1.fun_div h2 hz
  have he : a * (c * z + d) - (a * z + b) * c = 1 := by rw [← h]; ring
  rw [he] at h3
  exact h3

/-- The complex dilatation of `g ∘ T` for `T z = (a z + b)/(c z + d)` with `a d - b c = 1`, off the pole:
`μ_{g ∘ T}(z) = μ_g(T z) (c z + d)²/conj (c z + d)²` (`s23_dilatation_comp_right` with the inverse `(d w - b)/(-c w + a)`,
and `T'(z) = (c z + d)⁻²`). -/
theorem bg2_d_dil_mobius (g : ℂ → ℂ) {a b c d : ℂ} (h : a * d - b * c = 1) {z : ℂ} (hz : c * z + d ≠ 0) :
    complexDilatation (g ∘ mobiusFn a b c d) z =
      complexDilatation g (mobiusFn a b c d z) * ((c * z + d) ^ 2 / conj ((c * z + d) ^ 2)) := by
  have hne : a * d - b * c ≠ 0 := by rw [h]; exact one_ne_zero
  have hne' : d * a - -b * -c ≠ 0 := by rw [show d * a - -b * -c = a * d - b * c by ring]; exact hne
  have hT := bg2_d_deriv h hz
  have hden : -c * mobiusFn a b c d z + a ≠ 0 := mobiusFn_inv_den_ne_zero hne hz
  have hS : DifferentiableAt ℂ (mobiusFn d (-b) (-c) a) (mobiusFn a b c d z) := by
    show DifferentiableAt ℂ (fun w => (d * w + -b) / (-c * w + a)) (mobiusFn a b c d z)
    exact DifferentiableAt.fun_div (by fun_prop) (by fun_prop) hden
  have hST : ∀ᶠ w in 𝓝 z, mobiusFn d (-b) (-c) a (mobiusFn a b c d w) = w := by
    have hc : Continuous fun w : ℂ => c * w + d := by fun_prop
    filter_upwards [hc.continuousAt.eventually_ne hz] with w hw
    exact mobiusFn_inv_apply hne hw
  have hTS : ∀ᶠ u in 𝓝 (mobiusFn a b c d z), mobiusFn a b c d (mobiusFn d (-b) (-c) a u) = u := by
    have hc : Continuous fun u : ℂ => -c * u + a := by fun_prop
    filter_upwards [hc.continuousAt.eventually_ne hden] with u hu
    have h' := mobiusFn_inv_apply hne' hu
    simpa only [neg_neg] using h'
  rw [s23_dilatation_comp_right hT.differentiableAt hS hST hTS, hT.deriv]
  congr 1
  have hsq : (c * z + d) ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hsq' : conj ((c * z + d) ^ 2) ≠ 0 := (map_ne_zero _).2 hsq
  rw [map_div₀, map_one]
  field_simp

/-- `μ_{f_μ} = μ` a.e. pulls back through a Möbius transformation `T` (`a d - b c ≠ 0`) on an open set `U` free of its
pole: `μ_{f_μ}(T z) = μ(T z)` for a.e. `z ∈ U` (`T` is conformal on `U`, `isKQC_one_of_conformal`, `s23_c2_ae_pullback`). -/
theorem bg2_d_pullback (μ : BeltramiH) {a b c d : ℂ} (h : a * d - b * c ≠ 0) {U : Set ℂ} (hU : IsOpen U)
    (hpole : ∀ z ∈ U, c * z + d ≠ 0) :
    ∀ᵐ z ∂(volume.restrict U),
      complexDilatation (normalizedSolution μ.1) (mobiusFn a b c d z) = μ.1 (mobiusFn a b c d z) := by
  have hconf : IsConformalOnto (mobiusFn a b c d) U (mobiusFn a b c d '' U) := by
    refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ heq => ?_, rfl⟩
    · have hd : DifferentiableAt ℂ (fun w => (a * w + b) / (c * w + d)) z :=
        DifferentiableAt.fun_div (by fun_prop) (by fun_prop) (hpole z hz)
      exact hd.differentiableWithinAt
    · rw [← mobiusFn_inv_apply h (hpole z₁ hz₁), ← mobiusFn_inv_apply h (hpole z₂ hz₂), heq]
  have hae : ∀ᵐ u ∂(volume.restrict univ), complexDilatation (normalizedSolution μ.1) u = μ.1 u := by
    rw [Measure.restrict_univ]
    exact (ut_spec μ).2.2.2.2
  exact s23_c2_ae_pullback (P := fun u => complexDilatation (normalizedSolution μ.1) u = μ.1 u)
    (isKQC_one_of_conformal hU hconf) (subset_univ _) hae

/-- **D** (the dilatation of `f_μ ∘ γ`): for `μ ∈ M(G₀)` and `γ ∈ G₀`, `μ_{f_μ ∘ γ} = μ` a.e.  Off the (real) pole,
`μ_{f_μ ∘ γ}(z) = μ_{f_μ}(γ z) conj γ'(z)/γ'(z) = μ_{f_μ}(γ z) (cz + d)²/conj (cz + d)²` (`s23_dilatation_comp_right`, with
the Möbius inverse of `γ`); `μ_{f_μ} = μ` a.e. pulls back through the conformal `γ` (`s23_c2_ae_pullback`); on `ℍ` this is
`μ(z)` a.e. by `G₀`-compatibility, on `𝕃` both sides vanish (`γ(𝕃) ⊆ 𝕃`), and `ℝ` is null. -/
theorem bg2_dil_comp (μ : BeltramiGamma Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) :
    ∀ᵐ z, complexDilatation (normalizedSolution μ.1.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z = μ.1.1 z := by
  have hdetR : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast hdetR
  have hne : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 ≠ 0 := by rw [hdet]; exact one_ne_zero
  have hpole : ∀ z : ℂ, z.im ≠ 0 → (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := fun z hz => bg2_d_den_ne_zero hdetR hz
  refine bg_ae_of_halves ?_ ?_
  · filter_upwards [bg2_d_pullback μ.1 hne isOpen_upperHalf fun z hz => hpole z (show 0 < z.im from hz).ne',
      μ.2 γ hγ, ae_restrict_mem isOpen_upperHalf.measurableSet] with z h1 h2 hz
    rw [bg2_d_dil_mobius _ hdet (hpole z (show 0 < z.im from hz).ne'), h1]
    exact h2.symm
  · filter_upwards [bg2_d_pullback μ.1 hne isOpen_lowerHalf fun z hz => hpole z (show z.im < 0 from hz).ne,
      ae_restrict_mem isOpen_lowerHalf.measurableSet] with z h1 hz
    have hz' : z.im < 0 := hz
    have hTz : (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z).im ≤ 0 := by
      rw [mobiusFn_im_real, hdetR, one_mul]
      exact div_nonpos_of_nonpos_of_nonneg hz'.le (Complex.normSq_nonneg _)
    rw [bg2_d_dil_mobius _ hdet (hpole z hz'.ne), h1, μ.1.2.2 _ hTz, μ.1.2.2 z hz'.le, zero_mul]

/-- **M0** (MOB, affine case `c = 0`): `γ z = (a z + b)/d` is affine and conformal on `ℂ`, so `f_μ ∘ γ` is a q.c. map of the
plane onto itself with dilatation `μ` a.e. (`bg2_dil_comp`), hence `f_μ = A ∘ f_μ ∘ γ` for an affine `A` (`bg2_normalize`),
i.e. `f_μ ∘ γ = A⁻¹ ∘ f_μ`. -/
theorem bg2_mob_affine (μ : BeltramiGamma Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (hc : γ 1 0 = 0) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ ∀ z : ℂ,
      normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        (a * normalizedSolution μ.1.1 z + b) / (c * normalizedSolution μ.1.1 z + d) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  rw [hc, mul_zero, sub_zero] at hdet
  have h00 : (γ 0 0 : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]
    rintro h
    rw [h, zero_mul] at hdet
    exact zero_ne_one hdet
  have h11 : (γ 1 1 : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]
    rintro h
    rw [h, mul_zero] at hdet
    exact zero_ne_one hdet
  -- `γ z = (γ₀₀ z + γ₀₁)/γ₁₁` is affine with nonzero slope
  have hT : mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) =
      fun u => (u - (-(γ 0 1 : ℂ) / γ 0 0)) / ((γ 1 1 : ℂ) / γ 0 0) := by
    funext u
    simp only [mobiusFn, hc, ofReal_zero, zero_mul, zero_add]
    field_simp
    ring
  have hTc : IsConformalOnto (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) univ univ := by
    rw [hT]
    exact nxE_affine_isConformalOnto (div_ne_zero h11 h00)
  -- `G = f_μ ∘ γ` is a q.c. map of the plane onto itself with dilatation `μ` a.e.
  obtain ⟨K, hK⟩ := (ut_spec μ.1).1
  have hG := thm7_1_comp (isKQC_one_of_conformal isOpen_univ hTc) hK (subset_univ _)
  have hs : (normalizedSolution μ.1.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) '' univ = univ := by
    rw [image_comp, hTc.2.2, (ut_spec μ.1).2.1]
  have hN := bg2_normalize μ.1 hG hs (bg2_dil_comp μ hγ)
  set G := normalizedSolution μ.1.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
  have hΔ : G 1 - G 0 ≠ 0 := fun h =>
    one_ne_zero (hG.2.2.1.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
  -- `f_μ = (G - G 0)/(G 1 - G 0)`, i.e. `f_μ ∘ γ = (G 1 - G 0) f_μ + G 0`
  refine ⟨G 1 - G 0, G 0, 0, 1, by simpa using hΔ, fun z => ?_⟩
  rw [hN z, zero_mul, zero_add, div_one, mul_div_cancel₀ _ hΔ, sub_add_cancel]
  rfl

/-- The inversion conjugate `z ↦ 1/(f(p + q/(z + r)) - f(p))` (`q ≠ 0`) of a `K`-q.c. map `f` of the plane onto itself is a
homeomorphism of the plane onto itself: it is `z ↦ nxInvConj e₁ (z + r)` for the plane homeomorphism
`e₁ s = f(p + q s) - f(p)` fixing `0` (`nxI1_exists_homeo`; compare `b4_qc_conj_isHomeomorphOnto`). -/
theorem bg2_m1_isHomeomorphOnto {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hs : f '' univ = univ)
    (p q r : ℂ) (hq : q ≠ 0) :
    IsHomeomorphOnto (fun z : ℂ => (f (p + q * (z + r)⁻¹) - f p)⁻¹) univ univ := by
  obtain ⟨e, rfl⟩ := t1_homeomorph hf hs
  set e₁ : ℂ ≃ₜ ℂ := ((Homeomorph.mulLeft₀ q hq).trans (Homeomorph.addLeft p)).trans
    (e.trans (Homeomorph.subRight (e p))) with he₁
  have h0 : e₁ 0 = 0 := by simp [he₁]
  obtain ⟨E, hE⟩ := nxI1_exists_homeo e₁ h0
  have hG : ⇑((Homeomorph.addRight r).trans E) = fun z : ℂ => (e (p + q * (z + r)⁻¹) - e p)⁻¹ := by
    funext z
    simp [hE, nxInvConj, he₁]
  rw [← hG]
  exact nxI1_isHomeomorphOnto_of_homeomorph _

/-- The inversion conjugate `z ↦ 1/(f(p + q/(z + r)) - f(p))` (`q ≠ 0`) of a `K`-q.c. map `f` of the plane is `K`-q.c. off
the pole `-r`: `z ↦ p + q/(z + r)` is conformal there with values `≠ p`, and `w ↦ 1/(w - f(p))` is conformal off `f(p)`
(`thm7_1_comp`; compare `b4_qc_conj_isKQC`). -/
theorem bg2_m1_isKQC {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (p q r : ℂ) (hq : q ≠ 0) :
    IsKQC (fun z : ℂ => (f (p + q * (z + r)⁻¹) - f p)⁻¹) {-r}ᶜ K := by
  have hT : IsKQC (fun z : ℂ => p + q * (z + r)⁻¹) {-r}ᶜ 1 := by
    refine isKQC_one_of_conformal (D' := (fun z : ℂ => p + q * (z + r)⁻¹) '' {-r}ᶜ)
      isOpen_compl_singleton ⟨fun z hz => ?_, fun a _ b _ hab => ?_, rfl⟩
    · have h1 : z + r ≠ 0 := fun h => hz (mem_singleton_iff.mpr (eq_neg_of_add_eq_zero_left h))
      have h2 : DifferentiableAt ℂ (fun w : ℂ => p + q * (w + r)⁻¹) z := by fun_prop (disch := exact h1)
      exact h2.differentiableWithinAt
    · exact add_right_cancel (inv_injective (mul_left_cancel₀ hq (add_left_cancel hab)))
  have h1 := thm7_1_comp hT hf (subset_univ _)
  have hsub : (f ∘ fun z : ℂ => p + q * (z + r)⁻¹) '' {-r}ᶜ ⊆ {f p}ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ h
    have heq := hf.2.2.1.2.1 (mem_univ _) (mem_univ _) (mem_singleton_iff.mp h)
    rw [add_eq_left, mul_eq_zero, inv_eq_zero] at heq
    rcases heq with h0 | h0
    · exact hq h0
    · exact hz (mem_singleton_iff.mpr (eq_neg_of_add_eq_zero_left h0))
  have h2 := thm7_1_comp h1 (b4_qc_invShift_isKQC (f p)) hsub
  rw [one_mul, mul_one] at h2
  exact h2

/-- The pole of `γ` (`c ≠ 0`): `c z + d = 0` iff `z = -d/c`. -/
theorem bg2_m1_pole_iff {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : γ 1 0 ≠ 0) (z : ℂ) :
    (γ 1 0 : ℂ) * z + γ 1 1 = 0 ↔ z = -((γ 1 1 : ℂ) / γ 1 0) := by
  have hc' : (γ 1 0 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

/-- `γ z = a/c - (1/c²)/(z + d/c)` off the pole `-d/c` of `γ` (`c ≠ 0`, `ad - bc = 1`). -/
theorem bg2_m1_mobius_eq {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : γ 1 0 ≠ 0) {z : ℂ}
    (hz : z ≠ -((γ 1 1 : ℂ) / γ 1 0)) :
    mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z =
      (γ 0 0 : ℂ) / γ 1 0 + -((γ 1 0 : ℂ) ^ 2)⁻¹ * (z + (γ 1 1 : ℂ) / γ 1 0)⁻¹ := by
  have hc' : (γ 1 0 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := fun h => hz ((bg2_m1_pole_iff hc z).1 h)
  have hzr : z + (γ 1 1 : ℂ) / γ 1 0 = ((γ 1 0 : ℂ) * z + γ 1 1) / γ 1 0 := by
    field_simp
  have hden' : z * (γ 1 0 : ℂ) + γ 1 1 ≠ 0 := by rwa [mul_comm]
  rw [mobiusFn, hzr, inv_div]
  field_simp
  linear_combination -hdet

/-- **M1** (MOB, pole case `c ≠ 0`): with `w₀ = f_μ(γ ∞) = f_μ(a/c)`, the map `G = N ∘ f_μ ∘ γ` (`N w = 1/(w - w₀)`) is
`z ↦ nxInvConj e₁ (z + d/c)` for the plane homeomorphism `e₁ s = f_μ(a/c - s/c²) - w₀` fixing `0` (as `γ z = a/c - 1/(c(cz + d))`),
hence a homeomorphism of the plane (`nxI1_exists_homeo`, compare `b4_qc_conj_isHomeomorphOnto`); it is q.c. off the pole
`-d/c` (`N`, `f_μ`, `γ` there), hence on `ℂ` (`b4_isKQC_univ_of_punctured`), with dilatation `μ` a.e. (`bg2_dil_comp` and
`s23_dilatation_comp_left` for `N`); `bg2_normalize` then gives `f_μ ∘ γ = N⁻¹ ∘ A⁻¹ ∘ f_μ` off the pole. -/
theorem bg2_mob_pole (μ : BeltramiGamma Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (hc : γ 1 0 ≠ 0) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ ∀ z : ℂ, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 →
      normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        (a * normalizedSolution μ.1.1 z + b) / (c * normalizedSolution μ.1.1 z + d) := by
  obtain ⟨K, hK⟩ := (ut_spec μ.1).1
  have hs := (ut_spec μ.1).2.1
  have hc' : (γ 1 0 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc
  obtain ⟨p, hp⟩ : ∃ p : ℂ, p = (γ 0 0 : ℂ) / γ 1 0 := ⟨_, rfl⟩
  obtain ⟨q, hq'⟩ : ∃ q : ℂ, q = -((γ 1 0 : ℂ) ^ 2)⁻¹ := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℂ, r = (γ 1 1 : ℂ) / γ 1 0 := ⟨_, rfl⟩
  have hq : q ≠ 0 := by
    rw [hq']
    exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hc'))
  have hM : ∀ z : ℂ, z ≠ -r → mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z = p + q * (z + r)⁻¹ := by
    intro z hz
    subst hp hq' hr
    exact bg2_m1_mobius_eq hc hz
  have hpole : ∀ z : ℂ, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 ↔ z ≠ -r := by
    intro z
    rw [hr]
    exact not_congr (bg2_m1_pole_iff hc z)
  set f := normalizedSolution μ.1.1 with hf
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, G = fun z => (f (p + q * (z + r)⁻¹) - f p)⁻¹ := ⟨_, rfl⟩
  have hGh : IsHomeomorphOnto G univ univ := hG ▸ bg2_m1_isHomeomorphOnto hK hs p q r hq
  have hGK : IsKQC G univ K := b4_isKQC_univ_of_punctured hGh (hG ▸ bg2_m1_isKQC hK p q r hq)
  have hfc : Continuous f := continuousOn_univ.1 hK.2.2.1.1
  have hfi : Function.Injective f := fun a b hab => hK.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
  -- off the pole, `f (γ z) ≠ f p`
  have hne : ∀ z : ℂ, z ≠ -r → f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) - f p ≠ 0 := by
    intro z hz h
    have h1 := hfi (sub_eq_zero.1 h)
    rw [hM z hz, add_eq_left, mul_eq_zero, inv_eq_zero] at h1
    rcases h1 with h0 | h0
    · exact hq h0
    · exact hz (eq_neg_of_add_eq_zero_left h0)
  have hGd : ∀ᵐ z, complexDilatation G z = μ.1.1 z := by
    filter_upwards [bg2_dil_comp μ hγ, compl_mem_ae_iff.mpr (measure_singleton (-r))] with z h1 h2
    have hz : z ≠ -r := h2
    rw [← h1]
    have heq : EqOn G ((fun w => (w - f p)⁻¹) ∘ (f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1))) {-r}ᶜ := by
      intro w hw
      simp only [hG, Function.comp_apply, hM w hw]
    rw [abR_t_complexDilatation_congr isOpen_compl_singleton heq h2]
    have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := (hpole z).2 hz
    have hMc : ContinuousAt (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z := by
      unfold mobiusFn
      exact ((continuousAt_const.mul continuousAt_id).add continuousAt_const).div
        ((continuousAt_const.mul continuousAt_id).add continuousAt_const) hden
    refine s23_dilatation_comp_left (k := fun u => f p + u⁻¹) (hfc.continuousAt.comp hMc) ?_ ?_ ?_
    · exact (differentiableAt_id.sub (differentiableAt_const _)).inv (hne z hz)
    · exact (differentiableAt_const _).add (differentiableAt_id.inv (inv_ne_zero (hne z hz)))
    · exact Eventually.of_forall fun w => by
        simp only [inv_inv]
        ring
  have hnorm : ∀ z, f z = (G z - G 0) / (G 1 - G 0) := bg2_normalize μ.1 hGK hGh.2.2.1 hGd
  have hΔ : G 1 - G 0 ≠ 0 := fun h =>
    one_ne_zero (hGh.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
  refine ⟨f p * (G 1 - G 0), f p * G 0 + 1, G 1 - G 0, G 0, ?_, fun z hz => ?_⟩
  · intro h
    apply hΔ
    linear_combination -h
  · have hz' : z ≠ -r := (hpole z).1 hz
    have hGz : G z = (f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) - f p)⁻¹ := by
      simp only [hG, hM z hz']
    have hD : (G 1 - G 0) * f z + G 0 = (f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) - f p)⁻¹ := by
      rw [← hGz, hnorm z]
      field_simp
      ring
    have hnum : f p * (G 1 - G 0) * f z + (f p * G 0 + 1) = f p * ((G 1 - G 0) * f z + G 0) + 1 := by
      ring
    rw [hnum, hD]
    have := hne z hz'
    field_simp
    ring

/-- **MOB**: for `μ ∈ M(G₀)` and `γ ∈ G₀`, `S_{f_μ ∘ γ} = S_{f_μ}` on `𝕃`: near each point of `𝕃` (which misses the real pole
of `γ`), `f_μ ∘ γ = M ∘ f_μ` with `M` Möbius (`bg2_mob_affine`, `bg2_mob_pole`), and `S_{M ∘ f_μ} = S_{f_μ}` since `f_μ` is
holomorphic with `f_μ' ≠ 0` on `𝕃` (`schwarzian_congr`, `schwarzian_mobius_comp_analytic`). -/
theorem bg2_mob (μ : BeltramiGamma Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) :
    EqOn (schwarzian (normalizedSolution μ.1.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)))
      (schwarzian (normalizedSolution μ.1.1)) lowerHalf := by
  intro z hz
  have hconf := ut_conformal_lowerHalf μ.1
  have hA : AnalyticAt ℂ (normalizedSolution μ.1.1) z := hconf.1.analyticAt (isOpen_lowerHalf.mem_nhds hz)
  have hA' : deriv (normalizedSolution μ.1.1) z ≠ 0 := deriv_ne_zero_of_injOn isOpen_lowerHalf hconf.1 hconf.2.1 hz
  -- the pole of `γ` is real, so it misses `𝕃`
  have hden : ∀ w ∈ lowerHalf, (γ 1 0 : ℂ) * w + γ 1 1 ≠ 0 := by
    intro w hw h0
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe γ
      rwa [Matrix.det_fin_two] at h
    have h1 : γ 1 0 * w.im = 0 := by
      have h := congrArg Complex.im h0
      simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, zero_im] at h
      exact h
    have h2 : γ 1 0 * w.re + γ 1 1 = 0 := by
      have h := congrArg Complex.re h0
      simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, zero_re] at h
      exact h
    have hc : γ 1 0 = 0 :=
      (mul_eq_zero.1 h1).resolve_right (show w.im < 0 from hw).ne
    rw [hc, zero_mul, zero_add] at h2
    rw [hc, h2, mul_zero, mul_zero, sub_zero] at hdet
    exact zero_ne_one hdet
  obtain ⟨a, b, c, d, hdet, hrel⟩ : ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ ∀ w ∈ lowerHalf,
      normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) w) =
        (a * normalizedSolution μ.1.1 w + b) / (c * normalizedSolution μ.1.1 w + d) := by
    rcases eq_or_ne (γ 1 0) 0 with hc | hc
    · obtain ⟨a, b, c, d, hdet, h⟩ := bg2_mob_affine μ hγ hc
      exact ⟨a, b, c, d, hdet, fun w _ => h w⟩
    · obtain ⟨a, b, c, d, hdet, h⟩ := bg2_mob_pole μ hγ hc
      exact ⟨a, b, c, d, hdet, fun w hw => h w (hden w hw)⟩
  have hev : (normalizedSolution μ.1.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) =ᶠ[𝓝[≠] z]
      fun w => (a * normalizedSolution μ.1.1 w + b) / (c * normalizedSolution μ.1.1 w + d) := by
    filter_upwards [nhdsWithin_le_nhds (isOpen_lowerHalf.mem_nhds hz)] with w hw
    exact hrel w hw
  rw [schwarzian_congr hev]
  exact schwarzian_mobius_comp_analytic hA hA' hdet

/-- **S** (the sharp Bers bound): for `μ ∈ M`, `|S_{f_μ}(z)| (Im z)² ≤ (3/2) ‖μ‖_∞` on `𝕃`, with `‖μ‖_∞` the essential
supremum over `ℍ`.  For `‖μ‖_∞ > 0`: the disc `bB_disc` from `0` to `μ` (endpoint `t = ‖μ‖_∞`),
`Φ(t) = S_{f_{ν_t}}(z) (Im z)²` holomorphic on the unit disc (`bB_schwarzian_holo`), `|Φ| ≤ 3/2` (one Kraus term,
`bB_sd_kraus_pt`), `Φ(0) = S_id(z) (Im z)² = 0` (`bB_l_normalizedSolution_zero`, `bB_l_schwarzian_id`), and the
Schwarz lemma (`Complex.dist_le_div_mul_dist_of_mapsTo_ball`); for `‖μ‖_∞ = 0`, `μ ∼ 0` and `S_{f_μ} = S_id = 0` on `𝕃`. -/
theorem bg2_sharp_pt (μ : BeltramiH) {z : ℂ} (hz : z ∈ lowerHalf) :
    ‖schwarzian (normalizedSolution μ.1) z‖ * z.im ^ 2 ≤
      3 / 2 * UniversalTeichmuller.dilatationDiffNorm μ.1 0 := by
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀ : BeltramiH, μ₀.1 = 0 := ⟨⟨0, bB_l_zero_mem⟩, rfl⟩
  rw [← hμ₀]
  have hid : ∀ w, schwarzian (normalizedSolution μ₀.1) w = 0 := fun w => by
    rw [hμ₀, bB_l_normalizedSolution_zero, bB_l_schwarzian_id]
  have hd0 : 0 ≤ UniversalTeichmuller.dilatationDiffNorm μ.1 μ₀.1 := ENNReal.toReal_nonneg
  obtain ⟨hd1, hv⟩ := UniversalTeichmuller.ut_v_eq μ μ₀
  rcases hd0.eq_or_lt with h0 | hpos
  · -- `‖μ‖_∞ = 0`: `μ ∼ 0`, so `S_{f_μ} = S_id = 0` on `𝕃`
    have hv0 : ut_v μ μ₀ = 0 := by
      rw [hv, ← h0]
      norm_num
    have hS := congrFun (bersFunction_eq_of_equiv (UniversalTeichmuller.ut2_equiv_of_v_eq_zero hv0)) z
    simp only [bersFunction, indicator_of_mem hz] at hS
    rw [hS, hid, norm_zero, zero_mul, ← h0, mul_zero]
  · -- the disc from `0` to `μ`, and the Schwarz lemma with `Φ(0) = 0`, `|Φ| ≤ 3/2`
    obtain ⟨ν, hhol, hk, hν0, hν1⟩ := bB_disc μ₀ μ hpos
    have ht : ((UniversalTeichmuller.dilatationDiffNorm μ.1 μ₀.1 : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hd0]
      exact hd1
    have hΦ0 : schwarzian (normalizedSolution (ν 0).1) z * ((z.im ^ 2 : ℝ) : ℂ) = 0 := by
      rw [hν0, hid, zero_mul]
    have hmaps : MapsTo (fun s => schwarzian (normalizedSolution (ν s).1) z * ((z.im ^ 2 : ℝ) : ℂ))
        (ball 0 1) (closedBall (schwarzian (normalizedSolution (ν 0).1) z * ((z.im ^ 2 : ℝ) : ℂ)) (3 / 2)) := by
      intro s _
      rw [mem_closedBall, hΦ0, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (sq_nonneg _)]
      exact bB_sd_kraus_pt (ν s) hz
    have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball ((bB_schwarzian_holo hhol hk hz).mul_const _) hmaps ht
    rw [hΦ0, dist_zero_right, dist_zero_right, div_one, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (sq_nonneg _), hν1, Complex.norm_real, Real.norm_of_nonneg hd0] at h
    exact h

/-- `φ_μ ∈ A(𝕃)` with `‖φ_μ‖ ≤ (3/2) ‖μ‖_∞ < 3/2` (`bg2_sharp_pt` is uniform in `z`, and `‖μ‖_∞ < 1`). -/
theorem bg2_bers_mem (μ : BeltramiH) :
    bersFunction μ.1 ∈ bersSpaceL ∧ bersNormL (bersFunction μ.1) < ENNReal.ofReal (3 / 2) := by
  have hconf := ut_conformal_lowerHalf μ
  have hd1 : UniversalTeichmuller.dilatationDiffNorm μ.1 0 < 1 :=
    (UniversalTeichmuller.ut_v_eq μ ⟨0, bB_l_zero_mem⟩).1
  have hle : bersNormL (bersFunction μ.1) ≤
      ENNReal.ofReal (3 / 2 * UniversalTeichmuller.dilatationDiffNorm μ.1 0) := by
    unfold bersNormL
    refine iSup₂_le fun z hz => ?_
    rw [bersFunction, indicator_of_mem hz]
    exact ENNReal.ofReal_le_ofReal (bg2_sharp_pt μ hz)
  have hlt : bersNormL (bersFunction μ.1) < ENNReal.ofReal (3 / 2) :=
    hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by linarith))
  refine ⟨⟨?_, hlt.trans ENNReal.ofReal_lt_top⟩, hlt⟩
  refine (schwarzian_holomorphic isOpen_lowerHalf
    (isLocUnivMero_of_isConformalOnto isOpen_lowerHalf hconf)).congr fun z hz => ?_
  exact indicator_of_mem hz _

/-- §33.3: `‖φ_μ‖ < 3/2` (`f_μ|𝕃` is univalent with a quasiconformal extension), and `φ_μ` is
automorphic: `γ_μ = f_μ γ f_μ⁻¹` is a Möbius transformation, so
`φ_μ = S_{γ_μ ∘ f_μ} = S_{f_μ ∘ γ} = (φ_μ ∘ γ) γ'²`; hence `φ_μ ∈ Q(G₀, 𝕃)`. -/
theorem bersFunctionGamma_mem (hΓ : IsFuchsian Γ) (μ : BeltramiGamma Γ) :
    bersFunctionGamma μ ∈ automorphicQD Γ ∧ bersFunctionGamma μ ∈ bersSpaceL ∧
      bersNormL (bersFunctionGamma μ) < ENNReal.ofReal (3 / 2) := by
  have _hΓ := hΓ
  exact ⟨(bg2_auto_iff μ.1).2 fun γ hγ => bg2_mob μ hγ, (bg2_bers_mem μ.1).1, (bg2_bers_mem μ.1).2⟩

/-- §33.3: `Ψ` is well defined on `T(G₀)`: equivalent coefficients give the same `φ_μ`. -/
theorem bersFunctionGamma_eq_of_equiv {μ ν : BeltramiGamma Γ} (h : teichSetoidGamma Γ μ ν) :
    bersFunctionGamma μ = bersFunctionGamma ν := by
  exact bersFunction_eq_of_equiv ((lemma33_1 μ.1 ν.1).1 h)

/-- **§33.3 (Bers 嵌入).**  The Bers embedding `Ψ : T(S₀) → Q(G₀, 𝕃)`, `[μ] ↦ φ_μ = S_{f_μ}|𝕃`
(computed on a representative); its image is a bounded subset of the Banach space `Q(G₀, 𝕃)`. -/
def bersMapGamma (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : TeichGamma Γ) : ℂ → ℂ :=
  bersFunctionGamma (Quotient.out p)

/-- §33.3: `Ψ(p)` is the value on any representative, lies in `Q(G₀, 𝕃)` and has norm `< 3/2`. -/
theorem bersMapGamma_mem (hΓ : IsFuchsian Γ) (p : TeichGamma Γ) :
    bersMapGamma Γ p ∈ automorphicQD Γ ∧ bersNormL (bersMapGamma Γ p) < ENNReal.ofReal (3 / 2) ∧
      ∀ μ : BeltramiGamma Γ, Quotient.mk _ μ = p → bersFunctionGamma μ = bersMapGamma Γ p := by
  obtain ⟨h1, -, h3⟩ := bersFunctionGamma_mem hΓ (Quotient.out p)
  exact ⟨h1, h3, fun μ hμ =>
    bersFunctionGamma_eq_of_equiv (Quotient.exact (hμ.trans (Quotient.out_eq p).symm))⟩

/-! ## §33.4 The Bers embedding theorem -/

/-- `Ψ(p)` is `φ_μ` for any representative `μ` of `p` (`bersFunctionGamma_eq_of_equiv`). -/
theorem bg_bersMapGamma_eq {p : TeichGamma Γ} {μ : BeltramiGamma Γ} (h : Quotient.mk _ μ = p) :
    bersMapGamma Γ p = bersFunction μ.1.1 := by
  subst h
  exact bersFunctionGamma_eq_of_equiv (Quotient.exact (Quotient.out_eq _))

/-- §33.4: `δ([μ], [ν]) = inf {‖(μ' - ν')/(1 - ν̄'μ')‖_∞ : μ' ∈ [μ], ν' ∈ [ν]}`.

Written as the `sInf` of a set of reals; the nested form `⨅ μ ν (_ : …), …` is identically `0` in `ℝ`
(an infimum over an empty proposition is `sInf ∅ = 0`), as for `UniversalTeichmuller.dist`
(corrected 2026-09-25). -/
def teichDeltaGamma (p q : TeichGamma Γ) : ℝ :=
  sInf {d | ∃ μ ν : BeltramiGamma Γ, Quotient.mk _ μ = p ∧ Quotient.mk _ ν = q ∧
    d = UniversalTeichmuller.dilatationDiffNorm μ.1.1 ν.1.1}

/-- §33.4: the Teichmüller distance on `T(G₀)`, `d_T([μ], [ν]) = ½ ln((1 + δ)/(1 - δ))` (the same
computation as (21.4)). -/
def teichDistanceGamma (p q : TeichGamma Γ) : ℝ :=
  (1 / 2) * Real.log ((1 + teichDeltaGamma p q) / (1 - teichDeltaGamma p q))

/-- `0 ≤ δ(p, q) < 1`, and below every `b > δ(p, q)` lies some `‖(μ - ν)/(1 - ν̄μ)‖_∞` with representatives `μ ∈ p`,
`ν ∈ q`: the set whose infimum is `teichDeltaGamma p q` is nonempty (`Quotient.out`) and contained in `[0, 1)`
(`UniversalTeichmuller.ut_v_eq`), so its `sInf` is not a junk value. -/
theorem bg_d_teichDelta_spec (p q : TeichGamma Γ) :
    0 ≤ teichDeltaGamma p q ∧ teichDeltaGamma p q < 1 ∧
      ∀ b : ℝ, teichDeltaGamma p q < b → ∃ μ ν : BeltramiGamma Γ, Quotient.mk _ μ = p ∧ Quotient.mk _ ν = q ∧
        UniversalTeichmuller.dilatationDiffNorm μ.1.1 ν.1.1 < b := by
  have hmem : ∀ d ∈ {d | ∃ μ ν : BeltramiGamma Γ, Quotient.mk _ μ = p ∧ Quotient.mk _ ν = q ∧
      d = UniversalTeichmuller.dilatationDiffNorm μ.1.1 ν.1.1}, 0 ≤ d ∧ d < 1 := by
    rintro d ⟨μ, ν, -, -, rfl⟩
    exact ⟨ENNReal.toReal_nonneg, (UniversalTeichmuller.ut_v_eq μ.1 ν.1).1⟩
  have hne : {d | ∃ μ ν : BeltramiGamma Γ, Quotient.mk _ μ = p ∧ Quotient.mk _ ν = q ∧
      d = UniversalTeichmuller.dilatationDiffNorm μ.1.1 ν.1.1}.Nonempty :=
    ⟨_, Quotient.out p, Quotient.out q, Quotient.out_eq p, Quotient.out_eq q, rfl⟩
  obtain ⟨d₀, hd₀⟩ := hne
  refine ⟨le_csInf ⟨d₀, hd₀⟩ fun d hd => (hmem d hd).1,
    (csInf_le ⟨0, fun d hd => (hmem d hd).1⟩ hd₀).trans_lt (hmem d₀ hd₀).2, fun b hb => ?_⟩
  obtain ⟨d, ⟨μ, ν, hμ, hν, rfl⟩, hdb⟩ := exists_lt_of_csInf_lt ⟨d₀, hd₀⟩ hb
  exact ⟨μ, ν, hμ, hν, hdb⟩

/-- Helper for `s33d_K_eq`: `UniversalTeichmuller.ut_v_eq` for two q.c. maps on `ℍ` (instead of the normalized
plane solutions).  If `g`, `f` are q.c. on `ℍ` with complex dilatations `μ`, `ν` a.e., the maximal dilatation of
`f ∘ g⁻¹` on `g(ℍ)` is `(1 + d)/(1 - d)`, `d = ‖(μ - ν)/(1 - ν̄μ)‖_∞ < 1`. -/
theorem s33d_plane_K {f g : ℂ → ℂ} {Kf Kg : ℝ} (hf : IsKQC f upperHalf Kf) (hg : IsKQC g upperHalf Kg)
    {μ ν : ℂ → ℂ} (hμ : ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation g z = μ z)
    (hν : ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation f z = ν z) :
    UniversalTeichmuller.dilatationDiffNorm μ ν < 1 ∧
      maxDilatation (f ∘ Function.invFunOn g upperHalf) (g '' upperHalf) =
        ENNReal.ofReal ((1 + UniversalTeichmuller.dilatationDiffNorm μ ν) /
          (1 - UniversalTeichmuller.dilatationDiffNorm μ ν)) := by
  classical
  set D : Set ℂ := upperHalf with hD
  have hKg1 : (1 : ℝ) ≤ Kg := hg.2.1
  have hKf1 : (1 : ℝ) ≤ Kf := hf.2.1
  set kg : ℝ := (Kg - 1) / (Kg + 1) with hkg
  set kf : ℝ := (Kf - 1) / (Kf + 1) with hkf
  have hkg0 : 0 ≤ kg := div_nonneg (by linarith) (by linarith)
  have hkg1 : kg < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hkf0 : 0 ≤ kf := div_nonneg (by linarith) (by linarith)
  have hkf1 : kf < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hbμ : ∀ᵐ z ∂(volume.restrict D), ‖μ z‖ ≤ kg := by
    filter_upwards [hμ, (isKQC_maxDilatation_le hg).2] with z h1 h2
    rw [← h1]
    exact h2
  have hbν : ∀ᵐ z ∂(volume.restrict D), ‖ν z‖ ≤ kf := by
    filter_upwards [hν, (isKQC_maxDilatation_le hf).2] with z h1 h2
    rw [← h1]
    exact h2
  set ρ : ℂ → ℝ := fun z => ‖(μ z - ν z) / (1 - conj (ν z) * μ z)‖ with hρdef
  have hk0 : 0 ≤ max kg kf := le_max_of_le_left hkg0
  have hk1 : max kg kf < 1 := max_lt hkg1 hkf1
  have hc1 : 2 * max kg kf / (1 + max kg kf ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith [sq_nonneg (1 - max kg kf)]
  have hρc : ∀ᵐ z ∂(volume.restrict D), ρ z ≤ 2 * max kg kf / (1 + max kg kf ^ 2) := by
    filter_upwards [hbμ, hbν] with z h1 h2
    exact ahQ_pseudo_bound hk0 hk1 (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _))
  set F := f ∘ Function.invFunOn g D with hF
  have hleft : LeftInvOn (Function.invFunOn g D) g D := hg.2.2.1.2.1.leftInvOn_invFunOn
  have hright : ∀ w ∈ g '' D, g (Function.invFunOn g D w) = w := fun w hw => Function.invFunOn_eq hw
  have hinv : IsKQC (Function.invFunOn g D) (g '' D) Kg := thm7_2_inv hg
  have hinvimg : Function.invFunOn g D '' (g '' D) = D := hleft.image_image
  have hFK : IsKQC F (g '' D) (Kg * Kf) := thm7_1_comp hinv hf (by rw [hinvimg])
  have hgm : MeasurableSet (g '' D) := (isOpen_image_of_isKQC hg).measurableSet
  have hJF : ∀ᵐ z ∂(volume.restrict D), 0 < jacobian F (g z) := by
    have h := abT_ae_image hinv (p := fun z => 0 < jacobian F (g z)) (by
      filter_upwards [thm9_6_cor2_jacobian_pos hFK, ae_restrict_mem hgm] with w hw hwm
      show 0 < jacobian F (g (Function.invFunOn g D w))
      rw [hright w hwm]
      exact hw)
    rwa [hinvimg] at h
  have hpt : ∀ᵐ z ∂(volume.restrict D),
      ENNReal.ofReal ((‖dz F (g z)‖ + ‖dzbar F (g z)‖) / (‖dz F (g z)‖ - ‖dzbar F (g z)‖)) =
        ENNReal.ofReal ((1 + ρ z) / (1 - ρ z)) := by
    have hC := ahQ_comp_inv_dilatation hf hg
    have hJf := thm9_6_cor2_jacobian_pos hg
    filter_upwards [hC, hJf, hJF, hμ, hν] with z hCz hJfz hJFz h1 h2
    have hdz : dz g z ≠ 0 := by
      intro h0
      unfold jacobian at hJfz
      rw [h0, norm_zero] at hJfz
      nlinarith [norm_nonneg (dzbar g z)]
    have hdzF : dz F (g z) ≠ 0 := by
      intro h0
      unfold jacobian at hJFz
      rw [h0, norm_zero] at hJFz
      nlinarith [norm_nonneg (dzbar F (g z))]
    have hμF : ‖dzbar F (g z) / dz F (g z)‖ = ρ z := by
      change ‖complexDilatation F (g z)‖ = _
      rw [hCz, h1, h2, norm_mul, UniversalTeichmuller.ut_e_norm_quot_symm, norm_div (dz g z), Complex.norm_conj,
        div_self (norm_ne_zero_iff.2 hdz), mul_one]
    rw [UniversalTeichmuller.ut_e_quot_eq hdzF, hμF]
  have hm : volume.restrict D ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact isOpen_upperHalf.measure_ne_zero volume ⟨I, by simp [upperHalf]⟩
  have hnn : ∀ x : ℂ, (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := fun x => (ofReal_norm x).symm
  have hd : UniversalTeichmuller.dilatationDiffNorm μ ν =
      (essSup (fun z => ENNReal.ofReal (ρ z)) (volume.restrict D)).toReal := by
    simp only [UniversalTeichmuller.dilatationDiffNorm, hnn, hρdef]
    rfl
  have hkey : maxDilatation F (g '' D) =
      ENNReal.ofReal ((1 + UniversalTeichmuller.dilatationDiffNorm μ ν) /
        (1 - UniversalTeichmuller.dilatationDiffNorm μ ν)) := by
    rw [maxDilatation, UniversalTeichmuller.ut_e_essSup_image hg, essSup_congr_ae hpt,
      UniversalTeichmuller.ut_e_essSup_quot hm hc1 (fun z => norm_nonneg _) hρc, hd]
  have hd1 : UniversalTeichmuller.dilatationDiffNorm μ ν < 1 := by
    refine lt_of_le_of_lt ?_ hc1
    rw [hd]
    refine ENNReal.toReal_le_of_le_ofReal (div_nonneg (by linarith) (by positivity))
      (essSup_le_of_ae_le _ ?_)
    filter_upwards [hρc] with z hz
    exact ENNReal.ofReal_le_ofReal hz
  exact ⟨hd1, hkey⟩

/-- Helper for `s33d_K_eq`: the maximal dilatation of a q.c. map of uniformized surfaces is that of its lift to `ℍ`
(`h23l_lift_isKQC` and `s27v_isKQCRS_of_lift` in both directions). -/
theorem s33d_K_lift {A B : Type u} [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A]
    [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B] [Nonempty A]
    {Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → A}
    {p₂ : UpperHalfPlane → B} (hp₁ : IsUniformization Γ₁ p₁) (hp₂ : IsUniformization Γ₂ p₂) {f : A ≃ₜ B}
    (hf : IsQCRS f) {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p₁ p₂ f F) :
    maxDilatationRS f = maxDilatation (liftToC F) upperHalf := by
  have hK0 := s29_m_isKQCRS_maxDil hf
  have hne : (upperHalf : Set ℂ).Nonempty := ⟨I, by simp [upperHalf]⟩
  have hfin := s29_m_maxDilatationRS_ne_top hf
  obtain ⟨K, hK⟩ := hf
  have hl1 : IsKQC (liftToC F) upperHalf K := h23l_lift_isKQC hp₁ hp₂ hK hF
  have hl0 := h23l_lift_isKQC hp₁ hp₂ hK0 hF
  have hfin' : maxDilatation (liftToC F) upperHalf ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (isKQC_maxDilatation_le hl1).1
  obtain ⟨-, hl2⟩ := UniversalTeichmuller.ut_md_isKQC_toReal hl1 hne
  apply le_antisymm
  · have := maxDilatationRS_le (s27v_isKQCRS_of_lift hp₁ hp₂ hF hl2)
    rwa [ENNReal.ofReal_toReal hfin'] at this
  · have := (isKQC_maxDilatation_le hl0).1
    rwa [ENNReal.ofReal_toReal hfin] at this

/-- Helper for `s33d_K_eq`: `maxDilatation` only depends on the function on the open set. -/
theorem s33d_maxDil_congr {f h : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hfh : EqOn f h D) :
    maxDilatation f D = maxDilatation h D := by
  unfold maxDilatation
  refine essSup_congr_ae ?_
  filter_upwards [ae_restrict_mem hD.measurableSet] with z hz
  have hev : f =ᶠ[𝓝 z] h := Filter.eventuallyEq_of_mem (hD.mem_nhds hz) hfh
  simp only [dz, dzbar, hev.fderiv_eq (𝕜 := ℝ)]

/-- Helper for `teichDistanceGamma_eq` (`s33d_`): the surface version of `UniversalTeichmuller.ut_v_eq`.  For a
marked surface `m` of `S = ℍ/Γ` and a q.c. map `g` out of `m.X`, with `μ₁ = s27u_liftCoeff p m.marking` and
`ν₁ = s27u_liftCoeff p (g ∘ m.marking)` the lifted coefficients of the two markings, the maximal dilatation of `g` is
`(1 + d)/(1 - d)`, `d = ‖(μ₁ - ν₁)/(1 - ν̄₁μ₁)‖_∞`: at `m(p z)` the local dilatation of `g` has modulus
`|(ν₁ - μ₁)/(1 - μ̄₁ν₁)|(z)` (composition law), and the essential supremum over the charts of `X` is the essential
supremum over `ℍ` (`p` is a surjective local homeomorphism, `m` preserves null sets). -/
theorem s33d_K_eq {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    (m : MarkedRS S) {Y : Type u} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (g : m.X.carrier ≃ₜ Y) (hg : IsQCRS g) :
    maxDilatationRS g = ENNReal.ofReal
      ((1 + UniversalTeichmuller.dilatationDiffNorm (s27u_liftCoeff p m.marking)
          (s27u_liftCoeff p (m.marking.trans g))) /
        (1 - UniversalTeichmuller.dilatationDiffNorm (s27u_liftCoeff p m.marking)
          (s27u_liftCoeff p (m.marking.trans g)))) := by
  classical
  haveI : Nonempty m.X.carrier := ⟨m.marking (p UpperHalfPlane.I)⟩
  haveI : T2Space Y := g.symm.isEmbedding.t2Space
  haveI : ConnectedSpace Y := g.surjective.connectedSpace g.continuous
  haveI : CompactSpace Y := g.surjective.compactSpace g.continuous
  obtain ⟨K₁, hK₁⟩ := m.qc
  obtain ⟨K₂, hK₂⟩ := hg
  have hqc' : IsQCRS (m.marking.trans g) := ⟨_, (eq23_4 hK₁ hK₂).1⟩
  let m' : MarkedRS S := ⟨⟨Y⟩, m.marking.trans g, hqc'⟩
  obtain ⟨Γ₁, p₁, F₁, G₁, hp₁, hN₁, hF₁, -⟩ := s27u_exists_uniformization hp m
  obtain ⟨Γ₂, p₂, F₂, G₂, hp₂, hN₂, hF₂, -⟩ := s27u_exists_uniformization hp m'
  have hlift : IsLift p₁ p₂ g (F₁.symm.trans F₂) := by
    intro w
    show p₂ (F₂ (F₁.symm w)) = g (p₁ w)
    have h2 := hN₂.1 (F₁.symm w)
    have h1 := hN₁.1 (F₁.symm w)
    rw [F₁.apply_symm_apply] at h1
    rw [h2, h1]
    rfl
  rw [s33d_K_lift hp₁ hp₂ ⟨K₂, hK₂⟩ hlift]
  obtain ⟨k₁, hk₁0, hk₁1, hμ₁⟩ := s27v_liftCoeff_bound hp m
  obtain ⟨k₂, hk₂0, hk₂1, hμ₂⟩ := s27v_liftCoeff_bound hp m'
  obtain ⟨himg₁, -, -, hKQ₁, hd₁⟩ := s27u_fSym_upperHalf hk₁0 hk₁1 hμ₁
  obtain ⟨-, -, -, hKQ₂, hd₂⟩ := s27u_fSym_upperHalf hk₂0 hk₂1 hμ₂
  obtain ⟨-, hK⟩ := s33d_plane_K hKQ₂ hKQ₁ hd₁ hd₂
  rw [himg₁] at hK
  have hcong : maxDilatation (liftToC (F₁.symm.trans F₂)) upperHalf =
      maxDilatation (s27u_fSym (s27u_liftCoeff p m'.marking) ∘
        Function.invFunOn (s27u_fSym (s27u_liftCoeff p m.marking)) upperHalf) upperHalf := by
    refine s33d_maxDil_congr isOpen_upperHalf fun w hw => ?_
    have hw' : 0 < w.im := hw
    set τ : UpperHalfPlane := F₁.symm (UpperHalfPlane.ofComplex w) with hτ
    have h1 : s27u_fSym (s27u_liftCoeff p m.marking) (τ : ℂ) = w := by
      rw [← hF₁ τ, hτ, F₁.apply_symm_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
    have h2 : Function.invFunOn (s27u_fSym (s27u_liftCoeff p m.marking)) upperHalf w = (τ : ℂ) := by
      rw [← h1]
      exact hKQ₁.2.2.1.2.1.leftInvOn_invFunOn τ.coe_im_pos
    simp only [Function.comp_apply]
    rw [h2, ← hF₂ τ, h23l_liftToC_eq _ hw]
    rfl
  rw [hcong, hK]

/-- Helper for `teichDistanceGamma_eq`: if `e` is an equivalence with the characterization clause of
`teichGamma_equiv_teichSpace` and `e [μ] = [m]`, then the symmetric solution of the lifted coefficient of `m` has
the boundary values `f^μ|ℝ` (the normalized lift of `m` from `s27u_exists_uniformization` and the normalized lift of
the clause have the same boundary values by Theorem 27.1, `thm27_1` with `m₁ = m₂ = m`). -/
theorem s33d_fSym_char {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g)
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) (e : TeichGamma Γ ≃ TeichSpace S)
    (he : ∀ (μ : BeltramiGamma Γ) (m : MarkedRS S),
      e (Quotient.mk _ μ) = Quot.mk _ m ↔
        ∃ (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p' : UpperHalfPlane → m.X.carrier)
          (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (G : ExtPlane → ExtPlane),
          IsUniformization Γ' p' ∧ IsNormalizedLift p p' m.marking F G ∧
          ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = ((fMuSym μ.1.1 x : ℂ) : ExtPlane))
    (μ : BeltramiGamma Γ) (m : MarkedRS S) (h : e (Quotient.mk _ μ) = Quot.mk _ m) :
    ∀ x : ℝ, s27u_fSym (s27u_liftCoeff p m.marking) x = fMuSym μ.1.1 x := by
  obtain ⟨Γ', p', F, G, hp', hN, hG⟩ := (he μ m).1 h
  obtain ⟨Γ₁, p₁, F₁, G₁, hp₁, hN₁, -, hG₁⟩ := s27u_exists_uniformization hp m
  intro x
  have h1 := (thm27_1 hg hS hp m m hp₁ hp' hN₁ hN).1 (markedRS_equiv_equivalence.refl m) x
  rw [hG₁ x, hG x] at h1
  exact OnePoint.coe_injective h1

/-- Helper for `s33d_ge`, `s33d_le`: `x ↦ ½ ln((1 + x)/(1 - x))` is monotone on `[0, 1)`. -/
theorem s33d_phi_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    (1 / 2) * Real.log ((1 + x) / (1 - x)) ≤ (1 / 2) * Real.log ((1 + y) / (1 - y)) := by
  have h1 : 0 < 1 - y := by linarith
  have h2 : 0 < 1 - x := by linarith
  refine mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos (by linarith) h2) ?_) (by norm_num)
  rw [div_le_div_iff₀ h2 h1]
  nlinarith

/-- Helper for `teichDistanceGamma_eq` (the inequality `≥`): every competitor `(m₁, m₂, g)` in the infimum defining
`teichDistance (e a) (e b)` gives representatives `μ' = liftCoeff m₁ ∈ a`, `ν' = liftCoeff (g ∘ m₁) ∈ b`
(`s33d_fSym_char`; `⟨X₂, g ∘ m₁⟩ ∼ m₂` by `markedRS_equiv_same_surface`, then `s27v_equiv_iff_fSym`) with
`K[g] = (1 + d(μ', ν'))/(1 - d(μ', ν'))` (`s33d_K_eq`), and `δ(a, b) ≤ d(μ', ν')`. -/
theorem s33d_ge {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g)
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    (e : TeichGamma Γ ≃ TeichSpace S)
    (he : ∀ (μ : BeltramiGamma Γ) (m : MarkedRS S),
      e (Quotient.mk _ μ) = Quot.mk _ m ↔
        ∃ (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p' : UpperHalfPlane → m.X.carrier)
          (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (G : ExtPlane → ExtPlane),
          IsUniformization Γ' p' ∧ IsNormalizedLift p p' m.marking F G ∧
          ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = ((fMuSym μ.1.1 x : ℂ) : ExtPlane))
    (a b : TeichGamma Γ) :
    (1 / 2) * Real.log ((1 + teichDeltaGamma a b) / (1 - teichDeltaGamma a b)) ≤ teichDistance (e a) (e b) := by
  classical
  obtain ⟨μ, rfl⟩ := Quotient.exists_rep a
  obtain ⟨ν, rfl⟩ := Quotient.exists_rep b
  obtain ⟨hδ0, hδ1, -⟩ := bg_d_teichDelta_spec (Quotient.mk _ μ) (Quotient.mk _ ν)
  unfold teichDistance
  refine le_csInf (s29_m_teichSet_nonempty (e (Quotient.mk _ μ)) (e (Quotient.mk _ ν))) ?_
  rintro d ⟨m₁, m₂, gm, h₁, h₂, hq0, hhom, rfl⟩
  obtain ⟨K₁, hK₁⟩ := m₁.qc
  obtain ⟨K₂, hK₂⟩ := hq0
  have hqc' : IsQCRS (m₁.marking.trans gm) := ⟨_, (eq23_4 hK₁ hK₂).1⟩
  set m' : MarkedRS S := ⟨m₂.X, m₁.marking.trans gm, hqc'⟩ with hm'
  have hgen : HasGenus m₂.X.carrier g := hasGenus_of_homeomorph hS m₂.marking
  have hequiv : m'.Equiv m₂ :=
    markedRS_equiv_same_surface m₂.X (m₁.marking.trans gm) m₂.marking hqc' m₂.qc hg hgen hhom
  have h₂' : e (Quotient.mk _ ν) = Quot.mk _ m' := h₂.symm.trans (Quot.sound hequiv).symm
  have hf1 := s33d_fSym_char hg hS hp e he μ m₁ h₁.symm
  have hf2 := s33d_fSym_char hg hS hp e he ν m' h₂'
  obtain ⟨B1, hB1, hB1c⟩ := s27u_liftCoeff_beltramiH hp m₁.qc
  obtain ⟨B2, hB2, hB2c⟩ := s27u_liftCoeff_beltramiH hp hqc'
  let β1 : BeltramiGamma Γ := ⟨B1, hB1c⟩
  let β2 : BeltramiGamma Γ := ⟨B2, hB2c⟩
  have hq1 : (Quotient.mk (teichSetoidGamma Γ) β1) = Quotient.mk _ μ := Quotient.sound (fun x => by
    show fMuSym B1.1 x = fMuSym μ.1.1 x
    rw [hB1]
    exact hf1 x)
  have hq2 : (Quotient.mk (teichSetoidGamma Γ) β2) = Quotient.mk _ ν := Quotient.sound (fun x => by
    show fMuSym B2.1 x = fMuSym ν.1.1 x
    rw [hB2]
    exact hf2 x)
  have hδd : teichDeltaGamma (Quotient.mk _ μ) (Quotient.mk _ ν) ≤
      UniversalTeichmuller.dilatationDiffNorm B1.1 B2.1 :=
    csInf_le ⟨0, by rintro _ ⟨μ', ν', -, -, rfl⟩; exact ENNReal.toReal_nonneg⟩ ⟨β1, β2, hq1, hq2, rfl⟩
  have hd1 : UniversalTeichmuller.dilatationDiffNorm B1.1 B2.1 < 1 := (UniversalTeichmuller.ut_v_eq B1 B2).1
  have hd0 : 0 ≤ UniversalTeichmuller.dilatationDiffNorm B1.1 B2.1 := ENNReal.toReal_nonneg
  have hK := s33d_K_eq hp m₁ gm ⟨K₂, hK₂⟩
  rw [← hB1, ← hB2] at hK
  rw [hK, ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))]
  exact s33d_phi_mono hδ0 hδd hd1

/-- Helper for `s33d_le`: `dilatationDiffNorm` depends only on the almost-everywhere class (on `ℍ`) of its
arguments. -/
theorem s33d_dd_congr {μ₁ μ₂ ν₁ ν₂ : ℂ → ℂ} (h1 : ∀ᵐ z ∂(volume.restrict upperHalf), μ₁ z = μ₂ z)
    (h2 : ∀ᵐ z ∂(volume.restrict upperHalf), ν₁ z = ν₂ z) :
    UniversalTeichmuller.dilatationDiffNorm μ₁ ν₁ = UniversalTeichmuller.dilatationDiffNorm μ₂ ν₂ := by
  unfold UniversalTeichmuller.dilatationDiffNorm
  congr 1
  refine essSup_congr_ae ?_
  filter_upwards [h1, h2] with z a b
  rw [a, b]

/-- Helper for `s33d_le`: a marked surface of `S` whose lifted coefficient is `μ` a.e. on `ℍ` (`s27v_exists_marked`),
and whose symmetric solution `s27u_fSym` is that of `μ` (`s27u_fSym_congr_ae`). -/
theorem s33d_marked_rep {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) (μ : BeltramiGamma Γ) :
    ∃ m : MarkedRS S, (∀ᵐ z ∂(volume.restrict upperHalf), s27u_liftCoeff p m.marking z = μ.1.1 z) ∧
      s27u_fSym (s27u_liftCoeff p m.marking) = s27u_fSym μ.1.1 := by
  obtain ⟨k, hk0, hk1, hμ⟩ := bg_beltramiH_upper μ.1
  obtain ⟨m, hm⟩ := s27v_exists_marked hp hk0 hk1 hμ μ.2
  obtain ⟨k', hk0', hk1', hμ'⟩ := s27v_liftCoeff_bound hp m
  exact ⟨m, hm, s27u_fSym_congr_ae hk0' hk1' hμ' hk0 hk1 hμ hm⟩

/-- Helper for `s33d_le`: for representatives `μ' ∈ a`, `ν' ∈ b`, `d_T(e a, e b) ≤ ½ ln((1 + d)/(1 - d))`,
`d = ‖(μ' - ν')/(1 - ν̄'μ')‖_∞`. -/
theorem s33d_le_pair {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) (e : TeichGamma Γ ≃ TeichSpace S)
    (he : ∀ (μ : BeltramiGamma Γ) (m : MarkedRS S),
      e (Quotient.mk _ μ) = Quot.mk _ m ↔
        ∃ (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p' : UpperHalfPlane → m.X.carrier)
          (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (G : ExtPlane → ExtPlane),
          IsUniformization Γ' p' ∧ IsNormalizedLift p p' m.marking F G ∧
          ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = ((fMuSym μ.1.1 x : ℂ) : ExtPlane))
    (μ ν : BeltramiGamma Γ) :
    teichDistance (e (Quotient.mk _ μ)) (e (Quotient.mk _ ν)) ≤
      (1 / 2) * Real.log ((1 + UniversalTeichmuller.dilatationDiffNorm μ.1.1 ν.1.1) /
        (1 - UniversalTeichmuller.dilatationDiffNorm μ.1.1 ν.1.1)) := by
  classical
  obtain ⟨m₁, hm₁, hf₁⟩ := s33d_marked_rep hp μ
  obtain ⟨m₂, hm₂, hf₂⟩ := s33d_marked_rep hp ν
  -- `e [μ] = [m₁]`: the normalized lift of `m₁` has the boundary values `f^μ`
  have hchar : ∀ (μ' : BeltramiGamma Γ) (m : MarkedRS S), s27u_fSym (s27u_liftCoeff p m.marking) = s27u_fSym μ'.1.1 →
      e (Quotient.mk _ μ') = Quot.mk _ m := by
    intro μ' m hf
    refine (he μ' m).2 ?_
    obtain ⟨Γ₁, p₁, F₁, G₁, hp₁, hN₁, -, hG₁⟩ := s27u_exists_uniformization hp m
    refine ⟨Γ₁, p₁, F₁, G₁, hp₁, hN₁, fun x => ?_⟩
    rw [hG₁ x, hf]
    rfl
  have h₁ := hchar μ m₁ hf₁
  have h₂ := hchar ν m₂ hf₂
  obtain ⟨K₁, hK₁⟩ := m₁.qc
  obtain ⟨K₂, hK₂⟩ := m₂.qc
  set gm : m₁.X.carrier ≃ₜ m₂.X.carrier := m₁.marking.symm.trans m₂.marking with hgm
  have hgq : IsQCRS gm := ⟨_, (eq23_4 (s29_m_isKQCRS_symm hK₁) hK₂).1⟩
  have hcomp : m₁.marking.trans gm = m₂.marking := by
    ext x
    simp [hgm]
  have hhom : ContinuousMap.Homotopic ((m₁.marking.trans gm : S ≃ₜ m₂.X.carrier) : C(S, m₂.X.carrier))
      (m₂.marking : C(S, m₂.X.carrier)) := by
    rw [hcomp]
  have hmem : (1 / 2) * Real.log (maxDilatationRS gm).toReal ∈
      s29_m_teichSet (e (Quotient.mk _ μ)) (e (Quotient.mk _ ν)) :=
    ⟨m₁, m₂, gm, h₁.symm, h₂.symm, hgq, hhom, rfl⟩
  have hK := s33d_K_eq hp m₁ gm hgq
  rw [hcomp] at hK
  have hdd := s33d_dd_congr hm₁ hm₂
  rw [hdd] at hK
  have hd1 := (UniversalTeichmuller.ut_v_eq μ.1 ν.1).1
  have hd0 : 0 ≤ UniversalTeichmuller.dilatationDiffNorm μ.1.1 ν.1.1 := ENNReal.toReal_nonneg
  calc teichDistance (e (Quotient.mk _ μ)) (e (Quotient.mk _ ν))
      ≤ (1 / 2) * Real.log (maxDilatationRS gm).toReal :=
        csInf_le (s29_m_teichSet_bddBelow _ _) hmem
    _ = _ := by
        rw [hK, ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))]

/-- Helper for `teichDistanceGamma_eq` (the inequality `≤`): for representatives `μ' ∈ a`, `ν' ∈ b` the marked
surfaces `X^{μ'}`, `X^{ν'}` (`s27v_exists_marked`, with lifted coefficients `μ'`, `ν'` a.e.) have
`e a = [X^{μ'}]`, `e b = [X^{ν'}]` (the clause, with `s27u_fSym_congr_ae`), and `g = m₂ ∘ m₁⁻¹` has `g ∘ m₁ = m₂`
and `K[g] = (1 + d(μ', ν'))/(1 - d(μ', ν'))` (`s33d_K_eq`); then `δ(a, b)` is approximated by `d(μ', ν')`
(`bg_d_teichDelta_spec`) and `½ log((1 + x)/(1 - x))` is continuous and monotone on `[0, 1)`. -/
theorem s33d_le {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g)
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    (e : TeichGamma Γ ≃ TeichSpace S)
    (he : ∀ (μ : BeltramiGamma Γ) (m : MarkedRS S),
      e (Quotient.mk _ μ) = Quot.mk _ m ↔
        ∃ (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p' : UpperHalfPlane → m.X.carrier)
          (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (G : ExtPlane → ExtPlane),
          IsUniformization Γ' p' ∧ IsNormalizedLift p p' m.marking F G ∧
          ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = ((fMuSym μ.1.1 x : ℂ) : ExtPlane))
    (a b : TeichGamma Γ) :
    teichDistance (e a) (e b) ≤ (1 / 2) * Real.log ((1 + teichDeltaGamma a b) / (1 - teichDeltaGamma a b)) := by
  classical
  obtain ⟨hδ0, hδ1, happ⟩ := bg_d_teichDelta_spec a b
  obtain ⟨μ₀, rfl⟩ := Quotient.exists_rep a
  obtain ⟨ν₀, rfl⟩ := Quotient.exists_rep b
  set δ := teichDeltaGamma (Quotient.mk _ μ₀) (Quotient.mk _ ν₀) with hδ
  have hbound : ∀ b' : ℝ, δ < b' → b' < 1 → teichDistance (e (Quotient.mk _ μ₀)) (e (Quotient.mk _ ν₀)) ≤
      (1 / 2) * Real.log ((1 + b') / (1 - b')) := by
    intro b' hb' hb1
    obtain ⟨μ, ν, hμ, hν, hlt⟩ := happ b' hb'
    have := s33d_le_pair hp e he μ ν
    rw [hμ, hν] at this
    refine this.trans ?_
    exact s33d_phi_mono ENNReal.toReal_nonneg hlt.le hb1
  have hc : ContinuousAt (fun x : ℝ => (1 / 2) * Real.log ((1 + x) / (1 - x))) δ := by
    have h1 : (1 + δ) / (1 - δ) ≠ 0 := div_ne_zero (by linarith) (by linarith)
    have h2 : ContinuousAt (fun x : ℝ => (1 + x) / (1 - x)) δ :=
      (continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id) (by linarith)
    exact (h2.log h1).const_mul _
  have hlim : Filter.Tendsto (fun x : ℝ => (1 / 2) * Real.log ((1 + x) / (1 - x))) (nhdsWithin δ (Ioi δ))
      (𝓝 ((1 / 2) * Real.log ((1 + δ) / (1 - δ)))) := hc.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hδ1] with b' hb'
  exact hbound b' hb'.1 hb'.2

/-- §33.4: under `T(G₀) ≅ T(S₀)` the distance `teichDistanceGamma` is the Teichmüller distance of
§29 (the infimum of `½ ln K` over the maps `f_ν ∘ f_μ⁻¹` in the class). -/
theorem teichDistanceGamma_eq {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g)
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    ∃ e : TeichGamma Γ ≃ TeichSpace S, ∀ a b, teichDistanceGamma a b = teichDistance (e a) (e b) := by
  obtain ⟨e, he⟩ := teichGamma_equiv_teichSpace hg hS hΓ hfree hp
  refine ⟨e, fun a b => ?_⟩
  unfold teichDistanceGamma
  exact le_antisymm (s33d_ge hg hS hΓ hfree hp e he a b) (s33d_le hg hS hΓ hfree hp e he a b)

/-- The ε–δ computation of Lemma 33.2: if `0 ≤ x < 1` and `½ ln((1 + x)/(1 - x)) < δ/2`, then `x < (e^δ - 1)/2`
(`(1 + x)/(1 - x) < e^δ` gives `x (e^δ + 1) < e^δ - 1`, and `e^δ + 1 ≥ 2`). -/
theorem bg_d_lt_of_log_lt {x δ : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (h : (1 / 2) * Real.log ((1 + x) / (1 - x)) < δ / 2) : x < (Real.exp δ - 1) / 2 := by
  have hlog : Real.log ((1 + x) / (1 - x)) < δ := by linarith
  rw [Real.log_lt_iff_lt_exp (div_pos (by linarith) (by linarith)), div_lt_iff₀ (by linarith)] at hlog
  nlinarith

/-- **Lemma 33.2**: `Ψ` is continuous: `‖φ_μ - φ_ν‖ = ‖S_{f_μ ∘ f_ν⁻¹}‖_{f_ν(𝕃)} ≤ 3 ‖(μ-ν)/(1-ν̄μ)‖_∞`
(Lemma 21.1), so `d_T([μ], [ν]) < δ/2` implies `‖φ_μ - φ_ν‖ < (3/2)(e^δ - 1)`. -/
theorem lemma33_2 (hΓ : IsFuchsian Γ) (p q : TeichGamma Γ) {δ : ℝ} (hδ : 0 < δ)
    (hd : teichDistanceGamma p q < δ / 2) :
    bersNormL (bersMapGamma Γ p - bersMapGamma Γ q) < ENNReal.ofReal (3 / 2 * (Real.exp δ - 1)) := by
  have _hΓ := hΓ
  obtain ⟨h0, h1, hrep⟩ := bg_d_teichDelta_spec p q
  obtain ⟨μ, ν, hμ, hν, hμν⟩ := hrep _ (bg_d_lt_of_log_lt h0 h1 hd)
  rw [bg_bersMapGamma_eq hμ, bg_bersMapGamma_eq hν]
  have hE : 1 < Real.exp δ := Real.one_lt_exp_iff.2 hδ
  refine (eq21_10 ν.1 μ.1).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 ?_)
  linarith

/-- The scaled coefficient `t μ` (`t` clamped to `[0, 1]`, `ut_scale`) of a `G₀`-compatible `μ` is again
`G₀`-compatible: the compatibility identity is linear in `μ`. -/
theorem bg_p_scale_compat (μ : BeltramiGamma Γ) (t : ℝ) : IsGammaCompatible Γ (ut_scale μ.1 t).1 := by
  intro γ hγ
  filter_upwards [μ.2 γ hγ] with z hz
  simp only [ut_scale]
  rw [hz]
  ring

/-- Along the path `t ↦ t μ`, at `z ∈ 𝕃`: `|φ_{tμ}(z) - φ_{t₀μ}(z)| (Im z)² ≤ 3 |t - t₀| k/(1 - k²)` when
`‖μ‖_∞ ≤ k < 1` (`(21.10)` with `UniversalTeichmuller.ut_d_scale_le`). -/
theorem bg_p_pt_le (μ : BeltramiH) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hμ : IsBeltramiCoeff μ.1 univ k)
    {z : ℂ} (hz : z ∈ lowerHalf) (t t₀ : ℝ) :
    ‖bersFunction (ut_scale μ t).1 z - bersFunction (ut_scale μ t₀).1 z‖ * z.im ^ 2 ≤
      3 * (|t - t₀| * k / (1 - k ^ 2)) := by
  have hk2 : 0 < 1 - k ^ 2 := by nlinarith
  have hC : 0 ≤ 3 * (|t - t₀| * k / (1 - k ^ 2)) := by positivity
  have h1 : ENNReal.ofReal (‖(bersFunction (ut_scale μ t).1 - bersFunction (ut_scale μ t₀).1) z‖ * z.im ^ 2) ≤
      bersNormL (bersFunction (ut_scale μ t).1 - bersFunction (ut_scale μ t₀).1) := by
    unfold bersNormL
    exact le_iSup₂_of_le z hz le_rfl
  have h2 := eq21_10 (ut_scale μ t₀) (ut_scale μ t)
  have h3 := UniversalTeichmuller.ut_d_scale_le μ hk0 hk1 hμ t t₀
  have h4 : ENNReal.ofReal (3 * UniversalTeichmuller.dilatationDiffNorm (ut_scale μ t).1 (ut_scale μ t₀).1) ≤
      ENNReal.ofReal (3 * (|t - t₀| * k / (1 - k ^ 2))) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have h5 := (h1.trans h2).trans h4
  rw [ENNReal.ofReal_le_ofReal_iff hC] at h5
  exact h5

/-- Along the path `t ↦ t μ`, each value `t ↦ φ_{tμ}(z)` is continuous: Lipschitz for `z ∈ 𝕃` (`bg_p_pt_le`),
identically `0` off `𝕃`. -/
theorem bg_p_continuous (μ : BeltramiH) (z : ℂ) : Continuous fun t : ℝ => bersFunction (ut_scale μ t).1 z := by
  by_cases hz : z ∈ lowerHalf
  · obtain ⟨k, hk0, hk1, hμ⟩ := μ.2.1
    have hy : 0 < z.im ^ 2 := by
      have hz' : z.im < 0 := hz
      nlinarith
    refine (LipschitzWith.of_dist_le' (K := 3 * k / (1 - k ^ 2) / z.im ^ 2) fun t t₀ => ?_).continuous
    rw [dist_eq_norm, Real.dist_eq]
    calc ‖bersFunction (ut_scale μ t).1 z - bersFunction (ut_scale μ t₀).1 z‖
        ≤ 3 * (|t - t₀| * k / (1 - k ^ 2)) / z.im ^ 2 := (le_div_iff₀ hy).2 (bg_p_pt_le μ hk0 hk1 hμ hz t t₀)
      _ = 3 * k / (1 - k ^ 2) / z.im ^ 2 * |t - t₀| := by ring
  · simp only [bersFunction, Set.indicator_of_notMem hz]
    exact continuous_const

/-- §33.4: `Ψ(T(S₀))` is arc-wise connected (`T(S₀)` is, and `Ψ` is continuous). -/
theorem bersImage_pathConnected (hΓ : IsFuchsian Γ) : IsPathConnected (range (bersMapGamma Γ)) := by
  have _hΓ := hΓ
  let μ₀ : BeltramiGamma Γ :=
    ⟨⟨0, ⟨0, le_refl 0, zero_lt_one, aestronglyMeasurable_const, by simp⟩, fun _ _ => rfl⟩,
      fun _ _ => Filter.Eventually.of_forall fun _ => by simp⟩
  refine ⟨bersFunction 0, ⟨Quotient.mk _ μ₀, bg_bersMapGamma_eq (μ := μ₀) rfl⟩, ?_⟩
  rintro _ ⟨p, rfl⟩
  obtain ⟨μ, rfl⟩ := Quotient.exists_rep p
  refine ⟨{ toFun := fun t => bersFunction (ut_scale μ.1 t).1
            continuous_toFun := continuous_pi fun z => (bg_p_continuous μ.1 z).comp continuous_subtype_val
            source' := ?_
            target' := ?_ },
    fun t => ⟨Quotient.mk _ ⟨ut_scale μ.1 t, bg_p_scale_compat μ t⟩,
      bg_bersMapGamma_eq (μ := ⟨ut_scale μ.1 t, bg_p_scale_compat μ t⟩) rfl⟩⟩
  · show bersFunction (ut_scale μ.1 ((0 : unitInterval) : ℝ)).1 = bersFunction 0
    congr 1
    funext z
    simp [ut_scale]
  · show bersFunction (ut_scale μ.1 ((1 : unitInterval) : ℝ)).1 = bersMapGamma Γ (Quotient.mk _ μ)
    rw [bg_bersMapGamma_eq (μ := μ) rfl]
    congr 1
    funext z
    simp [ut_scale]

/-- The origin `[0]` of `T(G₀)`. -/
def TeichGamma.origin (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : TeichGamma Γ :=
  Quotient.mk _ ⟨⟨0, ⟨0, le_refl 0, zero_lt_one, aestronglyMeasurable_const, by simp⟩, fun _ _ => rfl⟩,
    fun _ _ => Filter.Eventually.of_forall fun _ => by simp⟩

/-! ### Lemma 33.3 track interface (coordinator 553e2d): the explicit Ahlfors–Weill extension on `𝕃`

`𝕃` is exhausted by the discs `Dₙ = B(-(n + 2) i, (n + 2) - 1/(n + 2))` (`D̄ₙ ⊆ 𝕃`, `Dₙ ↑ 𝕃`).  The circle reflection
`gₙ` in `∂Dₙ` has the SHARP invariant bound `‖gₙ z - z‖² ‖dgₙ‖ η_{Dₙ}(gₙ z)² = 4`, so Stage B of Theorem 20.3
(`t203_Setting` with `c₀ = 4`, `c₀ s < 2`) applies whenever `sup_{𝕃} |φ(z)| (Im z)² ≤ s < 1/2`.  The limit of the
extensions `Fₙ` is identified pointwise on `ℍ`, where `gₙ z → z̄`: there it is the Ahlfors–Weill map
`(w₁(z̄) + (z - z̄) w₁'(z̄) : w₂(z̄) + (z - z̄) w₂'(z̄))`, whose complex dilatation is exactly `-2 (Im z)² φ(z̄)` ((20.10)
with `g = conj`). -/

/-- The circle reflection `z ↦ c + r²/conj(z - c)` in `∂B(c, r)`. -/
def l333_crefl (c : ℂ) (r : ℝ) (z : ℂ) : ℂ := c + (r : ℂ) ^ 2 / conj (z - c)

/-- The centre `-(n + 2) i` of the `n`-th disc of the exhaustion of `𝕃`. -/
def l333_ctr (n : ℕ) : ℂ := -((n : ℂ) + 2) * I

/-- The radius `(n + 2) - 1/(n + 2)` of the `n`-th disc of the exhaustion of `𝕃`. -/
def l333_rad (n : ℕ) : ℝ := (n : ℝ) + 2 - 1 / ((n : ℝ) + 2)

/-- The `n`-th disc `Dₙ = B(-(n + 2) i, (n + 2) - 1/(n + 2))` of the exhaustion of `𝕃` (top point `-i/(n + 2)`). -/
def l333_disc (n : ℕ) : Set ℂ := ball (l333_ctr n) (l333_rad n)

/-- The reflection `gₙ` in the circle `∂Dₙ`. -/
def l333_refl (n : ℕ) : ℂ → ℂ := l333_crefl (l333_ctr n) (l333_rad n)

/-- The Stage B extension `Fₙ = t203_ext w₁ w₂ gₙ D̄ₙ cₙ` of `(w₁ : w₂)|Dₙ` to `ℂ̄`. -/
def l333_F (w₁ w₂ : ℂ → ℂ) (n : ℕ) : ExtPlane → ExtPlane :=
  t203_ext w₁ w₂ (l333_refl n) (closure (l333_disc n)) (l333_ctr n)

/-- The Ahlfors–Weill map on `ℍ`: `E(z) = (w₁(z̄) + (z - z̄) w₁'(z̄) : w₂(z̄) + (z - z̄) w₂'(z̄))`. -/
def l333_E (w₁ w₂ : ℂ → ℂ) (z : ℂ) : ExtPlane :=
  t203_ratio (w₁ (conj z) + (z - conj z) * deriv w₁ (conj z)) (w₂ (conj z) + (z - conj z) * deriv w₂ (conj z))

/-- The coefficient `μ = 1_ℍ · (-2 (Im z)² φ(z̄))` of Lemma 33.3. -/
def l333_mu (φ : ℂ → ℂ) : ℂ → ℂ := upperHalf.indicator fun z => -2 * (z.im : ℂ) ^ 2 * φ (conj z)

/-- The affine map `z ↦ (z - c)/r` maps `B(c, r)` conformally onto `Δ`. -/
theorem l333_ra_conformal (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsConformalOnto (fun z => (z - c) / (r : ℂ)) (ball c r) unitDisc := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  refine ⟨((differentiable_id.sub_const c).div_const (r : ℂ)).differentiableOn, ?_, ?_⟩
  · intro x _ y _ hxy
    have := (div_left_inj' hr0).mp hxy
    simpa using this
  · ext w
    simp only [mem_image, unitDisc, mem_ball, dist_eq_norm, sub_zero]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [norm_div, norm_real, Real.norm_of_nonneg hr.le, div_lt_one hr]
      exact hz
    · intro hw
      refine ⟨c + r * w, ?_, ?_⟩
      · rw [add_sub_cancel_left, norm_mul, norm_real, Real.norm_of_nonneg hr.le]
        nlinarith [norm_nonneg w]
      · rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hr0]

/-- The derivative of the circle reflection: `‖dg z‖ ≤ r²/|z - c|²` for `z ≠ c`. -/
theorem l333_ra_norm_fderiv_le (c : ℂ) (r : ℝ) {z : ℂ} (hz : z ≠ c) :
    ‖fderiv ℝ (l333_crefl c r) z‖ ≤ r ^ 2 / ‖z - c‖ ^ 2 := by
  have hu : z - c ≠ 0 := sub_ne_zero.mpr hz
  have h1 : HasDerivAt (fun w : ℂ => (w - c)⁻¹) (-(1 : ℂ) / (z - c) ^ 2) z :=
    ((hasDerivAt_id z).sub_const c).inv hu
  have h2 := (h1.hasFDerivAt.restrictScalars ℝ)
  have h3 := (Complex.conjCLE.hasFDerivAt (x := (z - c)⁻¹)).comp z h2
  have h4 := (h3.const_mul ((r : ℂ) ^ 2)).const_add c
  have heq : (fun y => c + (r : ℂ) ^ 2 * (conjCLE ∘ fun w : ℂ => (w - c)⁻¹) y) = l333_crefl c r := by
    funext y
    simp [l333_crefl, div_eq_mul_inv]
  rw [heq] at h4
  rw [h4.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearEquiv.coe_coe, conjCLE_apply, smul_eq_mul, norm_mul, Complex.norm_conj, norm_pow, norm_real,
    Real.norm_eq_abs, sq_abs, norm_div, norm_neg, norm_one]
  apply le_of_eq
  ring

/-- **REFL-A** (the disc `B(c, r)`): `z ↦ (z - c)/r` maps it conformally onto `Δ`, and its Poincaré density is
`η(ζ) = 2r/(r² - |ζ - c|²)` (`poincareDensity_well_defined`). -/
theorem l333_ball_density (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsConformalOnto (fun z => (z - c) / (r : ℂ)) (ball c r) unitDisc ∧
      ∀ ζ ∈ ball c r, poincareDensity (ball c r) ζ = 2 * r / (r ^ 2 - ‖ζ - c‖ ^ 2) := by
  have hf := l333_ra_conformal c hr
  refine ⟨hf, fun ζ hζ => ?_⟩
  have hd : HasDerivAt (fun z => (z - c) / (r : ℂ)) (1 / (r : ℂ)) ζ :=
    ((hasDerivAt_id ζ).sub_const c).div_const (r : ℂ)
  rw [(poincareDensity_well_defined isOpen_ball hf hf hζ).2, hd.deriv]
  have hlt : ‖ζ - c‖ < r := by rwa [mem_ball, dist_eq_norm] at hζ
  have hpos : 0 < r ^ 2 - ‖ζ - c‖ ^ 2 := by nlinarith [norm_nonneg (ζ - c)]
  rw [norm_div, norm_div, norm_one, norm_real, Real.norm_of_nonneg hr.le, div_pow]
  have hr2 : r ^ 2 ≠ 0 := by positivity
  rw [one_sub_div hr2]
  field_simp

/-- **REFL-A** (the sharp invariant bound): for the circle reflection `g` in `∂B(c, r)` and `|z - c| > r`,
`‖g z - z‖² ‖dg z‖ η(g z)² ≤ 4`.  It is `= 4`: with `R = |z - c|`, `|g z - z| = (R² - r²)/R`, `‖dg z‖ = r²/R²` and
`η(g z) = 2R²/(r (R² - r²))`. -/
theorem l333_crefl_bound (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ z ∈ (closure (ball c r))ᶜ, ‖l333_crefl c r z - z‖ ^ 2 * ‖fderiv ℝ (l333_crefl c r) z‖ *
      poincareDensity (ball c r) (l333_crefl c r z) ^ 2 ≤ 4 := by
  intro z hz
  rw [closure_ball c hr.ne', mem_compl_iff, mem_closedBall, dist_eq_norm, not_le] at hz
  have hRpos : 0 < ‖z - c‖ := hr.trans hz
  have hu : z - c ≠ 0 := norm_pos_iff.mp hRpos
  have hcu : conj (z - c) ≠ 0 := (map_ne_zero _).mpr hu
  have hgc : l333_crefl c r z - c = (r : ℂ) ^ 2 / conj (z - c) := by
    rw [l333_crefl, add_sub_cancel_left]
  have hngc : ‖l333_crefl c r z - c‖ = r ^ 2 / ‖z - c‖ := by
    rw [hgc, norm_div, Complex.norm_conj, norm_pow, norm_real, Real.norm_of_nonneg hr.le]
  have hmem : l333_crefl c r z ∈ ball c r := by
    rw [mem_ball, dist_eq_norm, hngc, div_lt_iff₀ hRpos]
    nlinarith
  have hgz : l333_crefl c r z - z = ((r : ℂ) ^ 2 - (‖z - c‖ : ℂ) ^ 2) / conj (z - c) := by
    have h := mul_conj' (z - c)
    rw [eq_div_iff hcu, l333_crefl, sub_mul, add_mul, div_mul_cancel₀ _ hcu]
    linear_combination (-1 : ℂ) * h
  have hngz : ‖l333_crefl c r z - z‖ = (‖z - c‖ ^ 2 - r ^ 2) / ‖z - c‖ := by
    have hre : ((r : ℂ) ^ 2 - (‖z - c‖ : ℂ) ^ 2) = ((r ^ 2 - ‖z - c‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hgz, norm_div, Complex.norm_conj, hre, norm_real, Real.norm_eq_abs,
      abs_of_neg (by nlinarith), neg_sub]
  have hdens : poincareDensity (ball c r) (l333_crefl c r z) =
      2 * ‖z - c‖ ^ 2 / (r * (‖z - c‖ ^ 2 - r ^ 2)) := by
    rw [(l333_ball_density c hr).2 _ hmem, hngc]
    have hd : ‖z - c‖ ^ 2 - r ^ 2 ≠ 0 := by nlinarith
    field_simp
  have hF := l333_ra_norm_fderiv_le c r (sub_ne_zero.mp hu)
  have hd : 0 < ‖z - c‖ ^ 2 - r ^ 2 := by nlinarith
  rw [hngz, hdens]
  calc ((‖z - c‖ ^ 2 - r ^ 2) / ‖z - c‖) ^ 2 * ‖fderiv ℝ (l333_crefl c r) z‖ *
        (2 * ‖z - c‖ ^ 2 / (r * (‖z - c‖ ^ 2 - r ^ 2))) ^ 2
      ≤ ((‖z - c‖ ^ 2 - r ^ 2) / ‖z - c‖) ^ 2 * (r ^ 2 / ‖z - c‖ ^ 2) *
        (2 * ‖z - c‖ ^ 2 / (r * (‖z - c‖ ^ 2 - r ^ 2))) ^ 2 := by gcongr
    _ = 4 := by
      field_simp
      ring

/-- The exterior of `B̄(c, r)` is `{z | r < ‖z - c‖}`. -/
theorem l333_rb_mem_ext {c : ℂ} {r : ℝ} (hr : 0 < r) {z : ℂ} :
    z ∈ (closure (ball c r))ᶜ ↔ r < ‖z - c‖ := by
  rw [closure_ball c hr.ne', mem_compl_iff, mem_closedBall, dist_eq_norm, not_le]

/-- `g z - c = r²/conj(z - c)`, and its norm is `r²/‖z - c‖`. -/
theorem l333_rb_norm_sub (c : ℂ) (r : ℝ) (z : ℂ) :
    ‖l333_crefl c r z - c‖ = r ^ 2 / ‖z - c‖ := by
  rw [l333_crefl, add_sub_cancel_left, norm_div, Complex.norm_conj, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- The circle reflection is an involution off the centre: `g (g z) = z` for `z ≠ c`. -/
theorem l333_rb_invol (c : ℂ) {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ c) :
    l333_crefl c r (l333_crefl c r z) = z := by
  have hzc : z - c ≠ 0 := sub_ne_zero.mpr hz
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [l333_crefl, add_sub_cancel_left, map_div₀, map_pow, conj_conj, Complex.conj_ofReal]
  field_simp
  ring

/-- The circle reflection fixes the circle `‖z - c‖ = r` pointwise. -/
theorem l333_rb_fix (c : ℂ) (r : ℝ) {z : ℂ} (hz : ‖z - c‖ = r) : l333_crefl c r z = z := by
  have hmc : (z - c) * conj (z - c) = (r : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    push_cast; ring
  by_cases h0 : z - c = 0
  · have hr : (r : ℂ) = 0 := by
      have : r = 0 := by rw [← hz, h0, norm_zero]
      simp [this]
    simp [l333_crefl, hr, sub_eq_zero.mp h0]
  · have hc0 : conj (z - c) ≠ 0 := by rwa [ne_eq, map_eq_zero]
    rw [l333_crefl, ← hmc, mul_div_assoc, div_self hc0, mul_one]
    ring

/-- The circle reflection is continuous (indeed `C^∞`) off its centre. -/
theorem l333_rb_contDiffAt (c : ℂ) (r : ℝ) {z : ℂ} (hz : z ≠ c) :
    ContDiffAt ℝ 1 (l333_crefl c r) z := by
  have hc0 : conj (z - c) ≠ 0 := by rw [ne_eq, map_eq_zero, sub_eq_zero]; exact hz
  have hconj : ContDiffAt ℝ 1 (fun w : ℂ => conj (w - c)) z :=
    (Complex.conjCLE.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
  have h : ContDiffAt ℝ 1 (fun w : ℂ => c + (r : ℂ) ^ 2 * (conj (w - c))⁻¹) z :=
    contDiffAt_const.add (contDiffAt_const.mul (hconj.fun_inv hc0))
  have he : l333_crefl c r = fun w : ℂ => c + (r : ℂ) ^ 2 * (conj (w - c))⁻¹ := by
    funext w
    rw [l333_crefl, div_eq_mul_inv]
  rw [he]
  exact h

/-- **REFL-B** (the circle reflection is a Stage B reflection): `g = l333_crefl c r` is `C¹` off `B̄(c, r)` and maps it
injectively onto `B(c, r) ∖ {c}` (`g ∘ g = id` off `c`).  `conj ∘ g = c̄ + r²/(z - c)` is conformal, hence `1`-q.c.
(`isKQC_one_of_conformal`).  `g` fixes the circle `|z - c| = r` pointwise and is continuous there, and `g z → c` as
`z → ∞`. -/
theorem l333_crefl_reflection (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ContDiffOn ℝ 1 (l333_crefl c r) (closure (ball c r))ᶜ ∧
      IsPlanarQCReflection (closure (ball c r))ᶜ (ball c r \ {c}) (l333_crefl c r) 1 ∧
      Tendsto (l333_crefl c r) (cocompact ℂ ⊓ 𝓟 (closure (ball c r))ᶜ) (𝓝 c) := by
  have hne : ∀ z ∈ (closure (ball c r))ᶜ, z ≠ c := fun z hz h => by
    rw [l333_rb_mem_ext hr, h, sub_self, norm_zero] at hz
    exact absurd hz (not_lt.mpr hr.le)
  have hopen : IsOpen (closure (ball c r))ᶜ := isClosed_closure.isOpen_compl
  have hinj : InjOn (l333_crefl c r) (closure (ball c r))ᶜ := fun z hz w hw hzw => by
    rw [← l333_rb_invol c hr (hne z hz), hzw, l333_rb_invol c hr (hne w hw)]
  refine ⟨fun z hz => (l333_rb_contDiffAt c r (hne z hz)).contDiffWithinAt, ⟨hinj, ?_, ?_, ?_⟩, ?_⟩
  · ext ζ
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [l333_rb_mem_ext hr] at hz
      have hpos : 0 < ‖z - c‖ := hr.trans hz
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, l333_rb_norm_sub, div_lt_iff₀ hpos, sq]
        exact mul_lt_mul_of_pos_left hz hr
      · intro h
        have h' : ‖l333_crefl c r z - c‖ = 0 := by rw [mem_singleton_iff.mp h, sub_self, norm_zero]
        rw [l333_rb_norm_sub] at h'
        exact absurd h' (div_pos (pow_pos hr 2) hpos).ne'
    · rintro ⟨hζb, hζc⟩
      have hζc' : ζ ≠ c := hζc
      rw [mem_ball, dist_eq_norm] at hζb
      have hpos : 0 < ‖ζ - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζc')
      refine ⟨l333_crefl c r ζ, ?_, l333_rb_invol c hr hζc'⟩
      rw [l333_rb_mem_ext hr, l333_rb_norm_sub, lt_div_iff₀ hpos, sq]
      exact mul_lt_mul_of_pos_left hζb hr
  · refine isKQC_one_of_conformal hopen ⟨?_, ?_, rfl⟩
    · intro z hz
      have hzc : z - c ≠ 0 := sub_ne_zero.mpr (hne z hz)
      have heq : (fun w => conj (l333_crefl c r w)) =ᶠ[𝓝 z]
          fun w => conj c + (r : ℂ) ^ 2 / (w - c) := Filter.Eventually.of_forall fun w => by
        simp [l333_crefl, map_div₀, Complex.conj_ofReal]
      have hd : DifferentiableAt ℂ (fun w => conj c + (r : ℂ) ^ 2 / (w - c)) z :=
        (differentiableAt_const _).fun_add ((differentiableAt_const _).fun_div
          (differentiableAt_id.sub_const c) hzc)
      exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt
    · intro z hz w hw hzw
      exact hinj hz hw (star_injective hzw)
  · rintro p ⟨hp, -⟩
    rw [frontier_compl, closure_ball c hr.ne', frontier_closedBall c hr.ne', mem_sphere,
      dist_eq_norm] at hp
    have hpc : p ≠ c := fun h => by
      rw [h, sub_self, norm_zero] at hp
      exact hr.ne' hp.symm
    have hcont := (l333_rb_contDiffAt c r hpc).continuousAt.tendsto
    rw [l333_rb_fix c r hp] at hcont
    exact hcont.mono_left nhdsWithin_le_nhds
  · refine Tendsto.mono_left ?_ inf_le_left
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hd := tendsto_dist_right_cocompact_atTop c
    have h0 : Tendsto (fun z => r ^ 2 / dist z c) (cocompact ℂ) (𝓝 0) :=
      tendsto_const_nhds.div_atTop hd
    refine h0.congr fun z => ?_
    rw [l333_rb_norm_sub, dist_eq_norm]

/-- The radius of the `n`-th disc is at least `3/2`. -/
theorem l333_exh_rad_ge (n : ℕ) : 3 / 2 ≤ l333_rad n := by
  unfold l333_rad
  have hm : (2 : ℝ) ≤ (n : ℝ) + 2 := by
    have := n.cast_nonneg (α := ℝ)
    linarith
  have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hm
  linarith

/-- The imaginary part of the centre `-(n + 2) i`. -/
theorem l333_exh_ctr_im (n : ℕ) : (l333_ctr n).im = -((n : ℝ) + 2) := by
  simp [l333_ctr]

/-- The real part of the centre `-(n + 2) i`. -/
theorem l333_exh_ctr_re (n : ℕ) : (l333_ctr n).re = 0 := by
  simp [l333_ctr]

/-- On the closed disc `D̄ₙ`, `Im z ≤ -1/(n + 2)`. -/
theorem l333_exh_closure_im {n : ℕ} {z : ℂ} (hz : z ∈ closure (l333_disc n)) :
    z.im ≤ -(1 / ((n : ℝ) + 2)) := by
  have hr : 0 < l333_rad n := by linarith [l333_exh_rad_ge n]
  rw [l333_disc, closure_ball _ hr.ne', mem_closedBall, dist_eq_norm] at hz
  have h1 : |(z - l333_ctr n).im| ≤ ‖z - l333_ctr n‖ := abs_im_le_norm _
  rw [sub_im, l333_exh_ctr_im] at h1
  have h2 := (abs_le.1 (h1.trans hz)).2
  unfold l333_rad at h2
  linarith

/-- Consecutive centres are at distance `1`. -/
theorem l333_exh_dist_ctr (n : ℕ) : dist (l333_ctr n) (l333_ctr (n + 1)) = 1 := by
  rw [dist_eq_norm]
  have h : l333_ctr n - l333_ctr (n + 1) = I := by
    simp only [l333_ctr]
    push_cast
    ring
  rw [h, norm_I]

/-- The algebraic identity `gₙ(z) - z̄ = (r² - m² - z̄²)/(z̄ - i m)` with `m = n + 2`. -/
theorem l333_exh_refl_sub (n : ℕ) (z : ℂ) (hne : conj z - ((n : ℂ) + 2) * I ≠ 0) :
    l333_refl n z - conj z =
      ((l333_rad n : ℂ) ^ 2 - ((n : ℂ) + 2) ^ 2 - conj z ^ 2) / (conj z - ((n : ℂ) + 2) * I) := by
  have hc : conj (z - l333_ctr n) = conj z - ((n : ℂ) + 2) * I := by
    simp only [l333_ctr, map_sub, map_mul, map_neg, map_add, map_natCast, map_ofNat, conj_I]
    ring
  simp only [l333_refl, l333_crefl]
  rw [hc]
  field_simp
  simp only [l333_ctr]
  ring_nf
  simp only [I_sq]
  ring

/-- **EXH** (the discs): `0 < rₙ`, and `Dₙ` is open with compact closure `D̄ₙ ⊆ 𝕃` (`Im ≤ -1/(n + 2)` on it) containing
its centre.  The discs increase (`|cₙ - cₙ₊₁| + rₙ ≤ rₙ₊₁`) and exhaust `𝕃`. -/
theorem l333_disc_facts :
    (∀ n, 0 < l333_rad n ∧ IsOpen (l333_disc n) ∧ IsCompact (closure (l333_disc n)) ∧
      closure (l333_disc n) ⊆ lowerHalf ∧ l333_ctr n ∈ l333_disc n) ∧
      Monotone l333_disc ∧ ⋃ n, l333_disc n = lowerHalf := by
  have hr : ∀ n, 0 < l333_rad n := fun n => by linarith [l333_exh_rad_ge n]
  have hcl : ∀ n, closure (l333_disc n) ⊆ lowerHalf := fun n z hz => by
    have h := l333_exh_closure_im hz
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    show z.im < 0
    linarith
  refine ⟨fun n => ⟨hr n, isOpen_ball, ?_, hcl n, mem_ball_self (hr n)⟩, ?_, ?_⟩
  · rw [l333_disc, closure_ball _ (hr n).ne']
    exact isCompact_closedBall _ _
  · refine monotone_nat_of_le_succ fun n => ball_subset_ball' ?_
    rw [l333_exh_dist_ctr]
    unfold l333_rad
    push_cast
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have : 1 / ((n : ℝ) + 1 + 2) ≤ 1 / ((n : ℝ) + 2) := one_div_le_one_div_of_le h2 (by linarith)
    linarith
  · apply Subset.antisymm
    · exact iUnion_subset fun n => subset_closure.trans (hcl n)
    · intro z hz
      have hz' : z.im < 0 := hz
      set x := z.re with hx
      set y := -z.im with hy
      have hy0 : 0 < y := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt ((x ^ 2 + y ^ 2 + 2) / (2 * y))
      refine mem_iUnion.2 ⟨n, ?_⟩
      rw [l333_disc, mem_ball, dist_eq_norm]
      refine lt_of_pow_lt_pow_left₀ 2 (hr n).le ?_
      rw [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, l333_exh_ctr_re, l333_exh_ctr_im]
      rw [div_lt_iff₀ (by positivity)] at hn
      unfold l333_rad
      set m : ℝ := (n : ℝ) + 2 with hm
      have hm0 : 0 < m := by positivity
      have hnm : (n : ℝ) < m := by linarith
      have h1 : (m - 1 / m) ^ 2 = m ^ 2 - 2 + (1 / m) ^ 2 := by
        field_simp
        ring
      rw [h1]
      have h3 : 0 < (1 / m) ^ 2 := by positivity
      have h4 : x ^ 2 + y ^ 2 + 2 < m * (2 * y) := hn.trans_le (mul_le_mul_of_nonneg_right hnm.le (by positivity))
      have h5 : z.im = -y := by rw [hy]; ring
      rw [h5]
      nlinarith

/-- **EXH** (`gₙ z → z̄`): with `m = n + 2`, `gₙ(z) - z̄ = (1/m² - 2 - z̄²)/(z̄ - i m) → 0`. -/
theorem l333_refl_tendsto (z : ℂ) : Tendsto (fun n => l333_refl n z) atTop (𝓝 (conj z)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hlim : Tendsto (fun n : ℕ => (2 + ‖z‖ ^ 2) / ((n : ℝ) + (2 - ‖z‖))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  refine squeeze_zero_norm' ?_ hlim
  obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  set m : ℝ := (n : ℝ) + 2 with hm
  have hmz : ‖z‖ + 2 < m := by linarith
  have hM : ‖((n : ℂ) + 2) * I‖ = m := by
    rw [norm_mul, norm_I, mul_one, show ((n : ℂ) + 2) = ((m : ℝ) : ℂ) by rw [hm]; push_cast; ring,
      Complex.norm_of_nonneg (by positivity)]
  have hden : m - ‖z‖ ≤ ‖conj z - ((n : ℂ) + 2) * I‖ := by
    have h := norm_sub_norm_le (((n : ℂ) + 2) * I) (conj z)
    rw [hM, Complex.norm_conj, norm_sub_rev] at h
    exact h
  have hden0 : 0 < m - ‖z‖ := by linarith
  have hne : conj z - ((n : ℂ) + 2) * I ≠ 0 := norm_pos_iff.1 (hden0.trans_le hden)
  have hnum : ‖(l333_rad n : ℂ) ^ 2 - ((n : ℂ) + 2) ^ 2 - conj z ^ 2‖ ≤ 2 + ‖z‖ ^ 2 := by
    have h1 : (l333_rad n : ℂ) ^ 2 - ((n : ℂ) + 2) ^ 2 = (((l333_rad n) ^ 2 - m ^ 2 : ℝ) : ℂ) := by
      rw [hm]
      push_cast
      ring
    have h2 : |(l333_rad n) ^ 2 - m ^ 2| ≤ 2 := by
      have hm0 : 0 < m := by positivity
      have h3 : (l333_rad n) ^ 2 - m ^ 2 = (1 / m) ^ 2 - 2 := by
        unfold l333_rad
        rw [← hm]
        field_simp
        ring
      have h4 : (1 / m) ^ 2 ≤ 1 := by
        have : 1 / m ≤ 1 := by rw [div_le_one hm0]; linarith [norm_nonneg z]
        have h5 : 0 ≤ 1 / m := by positivity
        nlinarith
      rw [h3, abs_le]
      constructor <;> nlinarith [sq_nonneg (1 / m)]
    rw [h1]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_conj]
    linarith
  rw [l333_exh_refl_sub n z hne, norm_div]
  have heq : (n : ℝ) + (2 - ‖z‖) = m - ‖z‖ := by rw [hm]; ring
  rw [heq]
  exact div_le_div₀ (by positivity) hnum hden0 hden

/-- **SET** (the Stage B setting on `Dₙ`): let `w₁, w₂` solve `w'' + (φ/2) w = 0` on `𝕃` with Wronskian `1`, and let
`|φ(z)| (Im z)² ≤ s < 1/2` on `𝕃`.  Then `t203_Setting 𝕃 Dₙ w₁ w₂ φ gₙ cₙ 1 4 s` holds: `|φ| ≤ s η_𝕃² ≤ s η_{Dₙ}²` on
`Dₙ` (`poincareDensity_lowerHalf`, `t203_density_mono`), and `4 s < 2`. -/
theorem l333_setting {φ w₁ w₂ : ℂ → ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 2)
    (hφ : ∀ z ∈ lowerHalf, ‖φ z‖ * z.im ^ 2 ≤ s) (hw₁ : DifferentiableOn ℂ w₁ lowerHalf)
    (hw₂ : DifferentiableOn ℂ w₂ lowerHalf)
    (hode : ∀ z ∈ lowerHalf, deriv (deriv w₁) z + φ z / 2 * w₁ z = 0 ∧ deriv (deriv w₂) z + φ z / 2 * w₂ z = 0 ∧
      w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = 1) (n : ℕ) :
    t203_Setting lowerHalf (l333_disc n) w₁ w₂ φ (l333_refl n) (l333_ctr n) 1 4 s := by
  obtain ⟨hdisc, -, -⟩ := l333_disc_facts
  obtain ⟨hr, hDo, hK, hcl, hp⟩ := hdisc n
  obtain ⟨hC1, hR, hT⟩ := l333_crefl_reflection (l333_ctr n) hr
  have hconf : IsConformalOnto (fun z => (z - l333_ctr n) / (l333_rad n : ℂ)) (l333_disc n) unitDisc :=
    (l333_ball_density (l333_ctr n) hr).1
  have hconfL : IsConformalOnto (cayley ∘ fun w : ℂ => -w) lowerHalf unitDisc :=
    isConformalOnto_cayley.comp isConformalOnto_neg_lowerHalf
  refine ⟨isOpen_lowerHalf, hDo, hK, hcl, ⟨_, hconf⟩, hw₁, hw₂, hode, hp, hC1, hR, hT,
    l333_crefl_bound (l333_ctr n) hr, hs0, by linarith, fun ζ hζ => ?_⟩
  have hζL : ζ ∈ lowerHalf := hcl (subset_closure hζ)
  have hζim : ζ.im < 0 := hζL
  have hmono := t203_density_mono isOpen_lowerHalf hDo (subset_closure.trans hcl) hconfL hconf hζ
  rw [poincareDensity_lowerHalf hζL] at hmono
  have h0 : 0 ≤ 1 / |ζ.im| := by positivity
  have hsq : (1 / |ζ.im|) ^ 2 ≤ poincareDensity (l333_disc n) ζ ^ 2 := pow_le_pow_left₀ h0 hmono 2
  have him2 : 0 < ζ.im ^ 2 := by nlinarith
  have heq : (1 / |ζ.im|) ^ 2 = 1 / ζ.im ^ 2 := by rw [div_pow, one_pow, sq_abs]
  have h1 : ‖φ ζ‖ ≤ s * (1 / ζ.im ^ 2) := by
    rw [mul_one_div, le_div_iff₀ him2]
    exact hφ ζ hζL
  calc ‖φ ζ‖ ≤ s * (1 / ζ.im ^ 2) := h1
    _ = s * (1 / |ζ.im|) ^ 2 := by rw [heq]
    _ ≤ s * poincareDensity (l333_disc n) ζ ^ 2 := mul_le_mul_of_nonneg_left hsq hs0

/-- The lower half-plane `𝕃` is simply connected: it is convex (the preimage of `(-∞, 0)` under `Im`), hence
contractible. -/
theorem l333_fam_isSimplyConnected_lowerHalf : IsSimplyConnected lowerHalf := by
  have hc : Convex ℝ lowerHalf := (convex_Iio (0 : ℝ)).linear_preimage Complex.imLm
  have _hct : ContractibleSpace ↥lowerHalf := hc.contractibleSpace ⟨-I, by simp [lowerHalf]⟩
  exact SimplyConnectedSpace.ofContractible _

/-- **ODE** (the fundamental system on `𝕃`): for `φ` holomorphic on `𝕃` (convex, so simply connected) there are
solutions `w₁, w₂` of `w'' + (φ/2) w = 0` with Wronskian `1` (`eq19_2_ode`).  `f = w₁/w₂` is locally univalent
meromorphic with `S_f = φ`, and `meroToExt f = (w₁ : w₂)` on `𝕃` (`t203_ode_meroToExt`). -/
theorem l333_ode {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ lowerHalf) :
    ∃ w₁ w₂ : ℂ → ℂ, DifferentiableOn ℂ w₁ lowerHalf ∧ DifferentiableOn ℂ w₂ lowerHalf ∧
      (∀ z ∈ lowerHalf, deriv (deriv w₁) z + φ z / 2 * w₁ z = 0 ∧ deriv (deriv w₂) z + φ z / 2 * w₂ z = 0 ∧
        w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = 1) ∧
      IsLocUnivMero (fun z => w₁ z / w₂ z) lowerHalf ∧
      (∀ z ∈ lowerHalf, schwarzian (fun z => w₁ z / w₂ z) z = φ z) ∧
      ∀ z ∈ lowerHalf, meroToExt (fun z => w₁ z / w₂ z) z = t203_ratio (w₁ z) (w₂ z) := by
  obtain ⟨w₁, w₂, hw₁, hw₂, hode, hloc, hS⟩ :=
    eq19_2_ode isOpen_lowerHalf bA_isConnected_lowerHalf l333_fam_isSimplyConnected_lowerHalf hφ
  refine ⟨w₁, w₂, hw₁, hw₂, hode, hloc, hS, fun z hz => ?_⟩
  have hA₁ : AnalyticAt ℂ w₁ z := hw₁.analyticAt (isOpen_lowerHalf.mem_nhds hz)
  have hA₂ : AnalyticAt ℂ w₂ z := hw₂.analyticAt (isOpen_lowerHalf.mem_nhds hz)
  have hW := (hode z hz).2.2
  have hne : w₂ z = 0 → w₁ z ≠ 0 := by
    intro h0 h1
    rw [h0, h1] at hW
    simp at hW
  have hor : w₂ z ≠ 0 ∨ deriv w₂ z ≠ 0 := by
    refine (em (w₂ z = 0)).elim (fun h0 => Or.inr fun h1 => ?_) Or.inl
    rw [h0, h1] at hW
    simp at hW
  exact t203_ode_meroToExt hA₁ hA₂ hne (neh_eventually_ne_zero hA₂ hor) Filter.EventuallyEq.rfl

/-- **FAM** (the family), under the hypotheses of `l333_setting`:
* every `Fₙ` is a homeomorphism of `ℂ̄` (`t203_covering`, `t203_ext_continuous`, `t203_ext_locInj`) equal to `(w₁ : w₂)`
  on `Dₙ`;
* in every Möbius chart at finite points it is `C¹` with `|∂̄| < |∂|` and `|∂̄| ≤ (4 s/2) |∂|` (`t203_ext_contDiffAt`);
* at each `z ∈ ℍ`, `Fₙ(z) → E(z)` (`t203_c1_ext_out`, `l333_refl_tendsto`, `t203_cont_ratio_tendsto`; the limit pair is
  not `(0, 0)` because the Wronskian is `1`). -/
theorem l333_family {φ w₁ w₂ : ℂ → ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 2)
    (hφ : ∀ z ∈ lowerHalf, ‖φ z‖ * z.im ^ 2 ≤ s) (hw₁ : DifferentiableOn ℂ w₁ lowerHalf)
    (hw₂ : DifferentiableOn ℂ w₂ lowerHalf)
    (hode : ∀ z ∈ lowerHalf, deriv (deriv w₁) z + φ z / 2 * w₁ z = 0 ∧ deriv (deriv w₂) z + φ z / 2 * w₂ z = 0 ∧
      w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = 1) :
    (∀ n, Function.Bijective (l333_F w₁ w₂ n) ∧ Continuous (l333_F w₁ w₂ n) ∧
      (∀ z ∈ l333_disc n, l333_F w₁ w₂ n z = t203_ratio (w₁ z) (w₂ z)) ∧
      ∀ a b c d : ℂ, a * d - b * c ≠ 0 → ∀ z : ℂ, mobiusExt a b c d (l333_F w₁ w₂ n z) ≠ extInf →
        ContDiffAt ℝ 1 (fun w : ℂ => extToC (mobiusExt a b c d (l333_F w₁ w₂ n w))) z ∧
        ‖dzbar (fun w : ℂ => extToC (mobiusExt a b c d (l333_F w₁ w₂ n w))) z‖ <
          ‖dz (fun w : ℂ => extToC (mobiusExt a b c d (l333_F w₁ w₂ n w))) z‖ ∧
        ‖dzbar (fun w : ℂ => extToC (mobiusExt a b c d (l333_F w₁ w₂ n w))) z‖ ≤
          4 * s / 2 * ‖dz (fun w : ℂ => extToC (mobiusExt a b c d (l333_F w₁ w₂ n w))) z‖) ∧
      ∀ z ∈ upperHalf, Tendsto (fun n => l333_F w₁ w₂ n (z : ExtPlane)) atTop (𝓝 (l333_E w₁ w₂ z)) := by
  have hSet : ∀ n, t203_Setting lowerHalf (l333_disc n) w₁ w₂ φ (l333_refl n) (l333_ctr n) 1 4 s :=
    fun n => l333_setting hs0 hs hφ hw₁ hw₂ hode n
  refine ⟨fun n => ⟨t203_covering (t203_ext_continuous (hSet n)) (t203_ext_locInj (hSet n)),
    t203_ext_continuous (hSet n), fun z hz => ?_, fun a b c d hdet z hz => t203_ext_contDiffAt (hSet n) hdet hz⟩,
    fun z hz => ?_⟩
  · exact t203_c1_ext_in (w₁ := w₁) (w₂ := w₂) (g := l333_refl n) (p := l333_ctr n) (subset_closure hz)
  obtain ⟨hdisc, -, -⟩ := l333_disc_facts
  have hzim : 0 < z.im := hz
  have hzn : ∀ n, z ∉ closure (l333_disc n) := by
    intro n hzc
    have h1 : z.im < 0 := (hdisc n).2.2.2.1 hzc
    linarith
  have hconj : conj z ∈ lowerHalf := by
    show (conj z).im < 0
    rw [conj_im]
    linarith
  have hev : (fun n => l333_F w₁ w₂ n (z : ExtPlane)) = fun n =>
      t203_ratio (w₁ (l333_refl n z) + (z - l333_refl n z) * deriv w₁ (l333_refl n z))
        (w₂ (l333_refl n z) + (z - l333_refl n z) * deriv w₂ (l333_refl n z)) :=
    funext fun n => t203_c1_ext_out (w₁ := w₁) (w₂ := w₂) (g := l333_refl n) (p := l333_ctr n) (hzn n)
  rw [hev]
  have hg := l333_refl_tendsto z
  have hU : lowerHalf ∈ 𝓝 (conj z) := isOpen_lowerHalf.mem_nhds hconj
  have cw₁ : ContinuousAt w₁ (conj z) := (hw₁.differentiableAt hU).continuousAt
  have cw₂ : ContinuousAt w₂ (conj z) := (hw₂.differentiableAt hU).continuousAt
  have cd₁ : ContinuousAt (deriv w₁) (conj z) :=
    ((hw₁.deriv isOpen_lowerHalf).differentiableAt hU).continuousAt
  have cd₂ : ContinuousAt (deriv w₂) (conj z) :=
    ((hw₂.deriv isOpen_lowerHalf).differentiableAt hU).continuousAt
  have hu := (cw₁.tendsto.comp hg).add ((tendsto_const_nhds (x := z)).sub hg |>.mul (cd₁.tendsto.comp hg))
  have hv := (cw₂.tendsto.comp hg).add ((tendsto_const_nhds (x := z)).sub hg |>.mul (cd₂.tendsto.comp hg))
  refine t203_cont_ratio_tendsto hu hv fun hb ha => ?_
  have hW := (hode (conj z) hconj).2.2
  have h1 : (w₁ (conj z) + (z - conj z) * deriv w₁ (conj z)) * deriv w₂ (conj z) -
      (w₂ (conj z) + (z - conj z) * deriv w₂ (conj z)) * deriv w₁ (conj z) = 1 := by
    rw [← hW]
    ring
  rw [ha, hb] at h1
  simp at h1

/-- An affine map after a fractional linear transformation: `(M(w) - p)/q` for `M = mobiusExt α β κ δ` and `q ≠ 0` is
`mobiusExt (α - pκ) (β - pδ) (qκ) (qδ)`. -/
theorem l333_lim_mobius_affine {α β κ δ : ℂ} (p : ℂ) {q : ℂ} (hq : q ≠ 0) (w : ExtPlane) :
    mobiusExt 1 (-p) 0 q (mobiusExt α β κ δ w) = mobiusExt (α - p * κ) (β - p * δ) (q * κ) (q * δ) w := by
  have hden : ∀ x : ℂ, (0 : ℂ) * x + q ≠ 0 := fun x => by simpa using hq
  induction w using OnePoint.rec with
  | infty =>
    by_cases hκ : κ = 0
    · rw [mobiusExt_infty_of_eq hκ, mobiusExt_infty_of_eq rfl, mobiusExt_infty_of_eq (by rw [hκ, mul_zero])]
    · rw [mobiusExt_infty_of_ne hκ, mobiusExt_infty_of_ne (mul_ne_zero hq hκ), mobiusExt_coe (hden _)]
      congr 1
      simp only [mobiusFn]
      field_simp
      ring
  | coe z =>
    by_cases hz : κ * z + δ = 0
    · rw [mobiusExt_coe_of_eq_zero hz, mobiusExt_infty_of_eq rfl,
        mobiusExt_coe_of_eq_zero (by linear_combination q * hz)]
    · have hz' : q * κ * z + q * δ ≠ 0 := by
        rw [show q * κ * z + q * δ = q * (κ * z + δ) by ring]
        exact mul_ne_zero hq hz
      rw [mobiusExt_coe hz, mobiusExt_coe (hden _), mobiusExt_coe hz']
      congr 1
      simp only [mobiusFn]
      rw [div_eq_div_iff (hden _) hz']
      linear_combination q * div_mul_cancel₀ (α * z + β) hz

/-- The Möbius packaging of `t203_package`: if `A ∘ G ∘ T = ĥ` with `A, T` Möbius and `h` a `K'`-q.c. map of `ℂ` onto
`ℂ`, then a Möbius `M` sending `G ∞` to `∞` makes `M ∘ G` the extension of a `K'`-q.c. map `g` of `ℂ` onto `ℂ`
(`t203_pack_core`, with `M = id` or `M(w) = 1/(w - G ∞)`). -/
theorem l333_lim_pack {G A T : ExtPlane → ExtPlane} {h : ℂ → ℂ} {K' : ℝ} (hA : IsMobius A) (hT : IsMobius T)
    (hh : IsKQC h univ K') (hhs : h '' univ = univ) (hG : ∀ p, A (G (T p)) = OnePoint.map h p) :
    ∃ α β κ δ : ℂ, α * δ - β * κ ≠ 0 ∧ ∃ g : ℂ → ℂ, IsKQC g univ K' ∧ g '' univ = univ ∧
      ∀ p, mobiusExt α β κ δ (G p) = OnePoint.map g p := by
  obtain ⟨a₁, b₁, c₁, d₁, hdet₁, rfl⟩ := hA
  obtain ⟨a₂, b₂, c₂, d₂, hdet₂, rfl⟩ := hT
  have hdet₁' : d₁ * a₁ - -b₁ * -c₁ ≠ 0 := by
    rwa [show d₁ * a₁ - -b₁ * -c₁ = a₁ * d₁ - b₁ * c₁ by ring]
  have hdet₂' : d₂ * a₂ - -b₂ * -c₂ ≠ 0 := by
    rwa [show d₂ * a₂ - -b₂ * -c₂ = a₂ * d₂ - b₂ * c₂ by ring]
  have hGe : ∀ p, G p = mobiusExt d₁ (-b₁) (-c₁) a₁ (OnePoint.map h (mobiusExt d₂ (-b₂) (-c₂) a₂ p)) := by
    intro p
    have h1 := hG (mobiusExt d₂ (-b₂) (-c₂) a₂ p)
    have h2 : mobiusExt a₂ b₂ c₂ d₂ (mobiusExt d₂ (-b₂) (-c₂) a₂ p) = p := by
      simpa only [neg_neg] using mobiusExt_inv_apply hdet₂' p
    rw [h2] at h1
    rw [← h1, mobiusExt_inv_apply hdet₁]
  by_cases hq : G extInf = extInf
  · have hΦ : ∀ p, mobiusExt 1 0 0 1 (G p) =
        mobiusExt d₁ (-b₁) (-c₁) a₁ (OnePoint.map h (mobiusExt d₂ (-b₂) (-c₂) a₂ p)) := fun p => by
      rw [t203_pack_mobius_id, hGe]
    have hinf : mobiusExt 1 0 0 1 (G extInf) = extInf := by
      rw [t203_pack_mobius_id, hq]
    obtain ⟨g, hg, hgs, hgp⟩ := t203_pack_core hh hhs hdet₁' hdet₂' hΦ hinf
    exact ⟨1, 0, 0, 1, by norm_num, g, hg, hgs, hgp⟩
  · obtain ⟨q, hq'⟩ := OnePoint.ne_infty_iff_exists.1 hq
    have hdet₃ : -c₁ * (-b₁ - q * a₁) - a₁ * (d₁ - q * -c₁) ≠ 0 := by
      intro h0
      apply hdet₁
      linear_combination -h0
    have hΦ : ∀ p, mobiusExt 0 1 1 (-q) (G p) = mobiusExt (-c₁) a₁ (d₁ - q * -c₁) (-b₁ - q * a₁)
        (OnePoint.map h (mobiusExt d₂ (-b₂) (-c₂) a₂ p)) := fun p => by
      rw [hGe, s20l_tp_mobius_comp q hdet₁']
    have hinf : mobiusExt 0 1 1 (-q) (G extInf) = extInf := by
      rw [← hq']
      exact mobiusExt_coe_of_eq_zero (by ring)
    obtain ⟨g, hg, hgs, hgp⟩ := t203_pack_core hh hhs hdet₃ hdet₂' hΦ hinf
    exact ⟨0, 1, 1, -q, by norm_num, g, hg, hgs, hgp⟩

/-- **LIM** (the limit with pointwise identification): the conclusion of `t203_limit`, plus: the limit `G` is the
pointwise limit of the `Fₙ` at every finite point where they converge.  At `z ∈ D`, `Fₙ z = f z` eventually.  Off `D`,
`z ≠ z₃ = T ∞`, so for large `n` `A(Fₙ z)` is finite and is the value at `T⁻¹ z` of the normalized plane maps, which
converge to `h`. -/
theorem l333_limit {D : Set ℂ} {f : ℂ → ℂ} {Dn : ℕ → Set ℂ} {F : ℕ → ExtPlane → ExtPlane} {k K' : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hK' : (1 + k) / (1 - k) ≤ K') (hDne : D.Nonempty) (hDo : IsOpen D)
    (hmono : Monotone Dn) (hopen : ∀ n, IsOpen (Dn n)) (hU : ⋃ n, Dn n = D)
    (hF : ∀ n, Function.Bijective (F n) ∧ Continuous (F n) ∧ (∀ z ∈ Dn n, F n z = meroToExt f z) ∧
      ∀ a b c d : ℂ, a * d - b * c ≠ 0 → ∀ z : ℂ, mobiusExt a b c d (F n z) ≠ extInf →
        ContDiffAt ℝ 1 (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z ∧
        ‖dzbar (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z‖ <
          ‖dz (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z‖ ∧
        ‖dzbar (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z‖ ≤
          k * ‖dz (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z‖) :
    ∃ (G A T : ExtPlane → ExtPlane) (h : ℂ → ℂ), IsMobius A ∧ IsMobius T ∧ IsKQC h univ K' ∧ h '' univ = univ ∧
      (∀ p, A (G (T p)) = OnePoint.map h p) ∧ (∀ z ∈ D, G z = meroToExt f z) ∧
      ∀ (z : ℂ) (e : ExtPlane), Tendsto (fun n => F n (z : ExtPlane)) atTop (𝓝 e) → G z = e := by
  have _hopen := hopen
  obtain ⟨z₃, hz₃⟩ := hDne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hDo z₃ hz₃
  have hε2 : 0 < ε / 2 := half_pos hε
  set r : ℂ := ((ε / 2 : ℝ) : ℂ) with hrdef
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.2 hε2.ne'
  have hnr : ‖r‖ = ε / 2 := by rw [hrdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε2]
  have hz₁D : z₃ + r ∈ D := hball (by rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hnr]; linarith)
  have hz₂D : z₃ + r / 2 ∈ D := hball (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_div, hnr, Complex.norm_two]
    linarith)
  have hmemU : ∀ z ∈ D, ∃ n, z ∈ Dn n := fun z hz => mem_iUnion.1 (by rw [hU]; exact hz)
  -- the three points lie in one `Dₙ`, and `Fₙ` is `f` there from `N` on
  obtain ⟨N, hN1, hN2, hN3⟩ : ∃ N, z₃ + r ∈ Dn N ∧ z₃ + r / 2 ∈ Dn N ∧ z₃ ∈ Dn N := by
    obtain ⟨N₁, hN₁⟩ := hmemU _ hz₁D
    obtain ⟨N₂, hN₂⟩ := hmemU _ hz₂D
    obtain ⟨N₃, hN₃⟩ := hmemU _ hz₃
    exact ⟨N₁ + N₂ + N₃, hmono (by omega) hN₁, hmono (by omega) hN₂, hmono (by omega) hN₃⟩
  have hF1 : ∀ n, N ≤ n → F n ((z₃ + r : ℂ) : ExtPlane) = meroToExt f (z₃ + r) := fun n hn =>
    (hF n).2.2.1 _ (hmono hn hN1)
  have hF2 : ∀ n, N ≤ n → F n ((z₃ + r / 2 : ℂ) : ExtPlane) = meroToExt f (z₃ + r / 2) := fun n hn =>
    (hF n).2.2.1 _ (hmono hn hN2)
  have hF3 : ∀ n, N ≤ n → F n (z₃ : ExtPlane) = meroToExt f z₃ := fun n hn =>
    (hF n).2.2.1 _ (hmono hn hN3)
  -- the three values are distinct (`F N` is injective)
  have hne12 : meroToExt f (z₃ + r) ≠ meroToExt f (z₃ + r / 2) := by
    intro h
    have h' := OnePoint.coe_injective ((hF N).1.1 ((hF1 N le_rfl).trans (h.trans (hF2 N le_rfl).symm)))
    apply hr
    linear_combination 2 * h'
  have hne13 : meroToExt f (z₃ + r) ≠ meroToExt f z₃ := by
    intro h
    have h' := OnePoint.coe_injective ((hF N).1.1 ((hF1 N le_rfl).trans (h.trans (hF3 N le_rfl).symm)))
    apply hr
    linear_combination h'
  have hne23 : meroToExt f (z₃ + r / 2) ≠ meroToExt f z₃ := by
    intro h
    have h' := OnePoint.coe_injective ((hF N).1.1 ((hF2 N le_rfl).trans (h.trans (hF3 N le_rfl).symm)))
    apply hr
    linear_combination 2 * h'
  obtain ⟨a, b, c, d, hdet, hA0, hA1, hAinf⟩ := t203_lim_three hne12 hne13 hne23
  -- the normalized plane maps of `A ∘ F (m + N) ∘ T`
  set hn : ℕ → ℂ → ℂ := fun m w => extToC (mobiusExt a b c d (F (m + N) (mobiusExt z₃ (z₃ + r) 1 1 w)))
    with hhn
  have hnorm : ∀ m, IsKQCNormalizedPlane (hn m) K' := fun m => by
    have hmN : N ≤ m + N := Nat.le_add_left N m
    exact t203_lim_normalized hk0 hk1 hK' hdet hr (hF (m + N)).1 (hF (m + N)).2.1
      (by rw [hF1 _ hmN, hA0]) (by rw [hF2 _ hmN, hA1]) (by rw [hF3 _ hmN, hAinf])
      fun z hz => (hF (m + N)).2.2.2 a b c d hdet z hz
  -- the limit
  obtain ⟨φ, hφ, h, hlim⟩ := t203_lim_nf_extract hnorm
  have hh := t203_lim_nf_limit (fun m => hnorm (φ m)) hlim
  have hpt : ∀ w, Tendsto (fun m => hn (φ m) w) atTop (𝓝 (h w)) := fun w =>
    (tendstoLocallyUniformlyOn_univ.2 hlim).tendsto_at (mem_univ w)
  have hTdet : z₃ * 1 - (z₃ + r) * 1 ≠ 0 := by
    intro h
    apply hr
    linear_combination -h
  set eA := mobiusHomeomorph a b c d hdet with heA
  set eT := mobiusHomeomorph z₃ (z₃ + r) 1 1 hTdet with heT
  have hTinf : eT extInf = (z₃ : ExtPlane) := by
    show mobiusExt z₃ (z₃ + r) 1 1 extInf = _
    rw [mobiusExt_infty_of_ne one_ne_zero, div_one]
  refine ⟨fun p => eA.symm (OnePoint.map h (eT.symm p)), mobiusExt a b c d, mobiusExt z₃ (z₃ + r) 1 1, h,
    ⟨a, b, c, d, hdet, rfl⟩, ⟨z₃, z₃ + r, 1, 1, hTdet, rfl⟩, hh.1, hh.2.1, fun p => ?_, fun z hz => ?_,
    fun z e he => ?_⟩
  · show eA (eA.symm (OnePoint.map h (eT.symm (eT p)))) = _
    rw [Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]
  · show eA.symm (OnePoint.map h (eT.symm z)) = meroToExt f z
    rw [Homeomorph.symm_apply_eq]
    have key : ∀ q : ExtPlane, eT.symm (z : ExtPlane) = q → OnePoint.map h q = eA (meroToExt f z) := by
      intro q hq
      induction q using OnePoint.rec with
      | infty =>
        -- `z = T ∞ = z₃`
        have hz3 : z = z₃ := by
          have h1 := (Homeomorph.symm_apply_eq eT).1 hq
          rw [hTinf] at h1
          exact OnePoint.coe_injective h1
        rw [OnePoint.map_infty, hz3]
        exact hAinf.symm
      | coe w =>
        rw [OnePoint.map_some]
        have hzT : (z : ExtPlane) = eT w := (Homeomorph.symm_apply_eq eT).1 hq
        obtain ⟨n₀, hn₀⟩ := hmemU z hz
        have hFz : ∀ m, n₀ ≤ m → F (m + N) (z : ExtPlane) = meroToExt f z := fun m hm =>
          (hF (m + N)).2.2.1 z (hmono (by omega) hn₀)
        -- `A(f z)` is finite: otherwise `F (n₀ + N) z = F (n₀ + N) z₃`, so `z = z₃ = T ∞`
        have hfin : eA (meroToExt f z) ≠ extInf := by
          intro hinf'
          have h1 : eA (F (n₀ + N) (z : ExtPlane)) = eA (F (n₀ + N) (z₃ : ExtPlane)) := by
            rw [hFz n₀ le_rfl, hF3 _ (Nat.le_add_left N n₀), hinf']
            exact hAinf.symm
          have h2 := OnePoint.coe_injective ((hF (n₀ + N)).1.1 (eA.injective h1))
          rw [h2, ← hTinf, Homeomorph.symm_apply_apply] at hq
          exact OnePoint.infty_ne_coe w hq
        obtain ⟨c', hc'⟩ := OnePoint.ne_infty_iff_exists.1 hfin
        -- the plane maps are eventually constant `= c'` at `w`
        have hval : ∀ m, n₀ ≤ m → hn m w = c' := fun m hm => by
          show extToC (mobiusExt a b c d (F (m + N) (eT w))) = c'
          rw [← hzT, hFz m hm]
          show extToC (eA (meroToExt f z)) = c'
          rw [← hc']
          rfl
        have hlimw : h w = c' := tendsto_nhds_unique (hpt w) (tendsto_const_nhds.congr'
          (eventually_atTop.2 ⟨n₀, fun m hm => (hval (φ m) (hm.trans (hφ.id_le m))).symm⟩))
        rw [hlimw]
        exact hc'
    exact key _ rfl
  · -- the pointwise limit at every finite point is `G z`
    show eA.symm (OnePoint.map h (eT.symm z)) = e
    rw [Homeomorph.symm_apply_eq]
    have hsub : Tendsto (fun m => φ m + N) atTop atTop :=
      tendsto_atTop_mono (fun m => Nat.le_add_right (φ m) N) hφ.tendsto_atTop
    have hAe : Tendsto (fun m => eA (F (φ m + N) (z : ExtPlane))) atTop (𝓝 (eA e)) :=
      (eA.continuous.tendsto e).comp (he.comp hsub)
    have key : ∀ q : ExtPlane, eT.symm (z : ExtPlane) = q → OnePoint.map h q = eA e := by
      intro q hq
      induction q using OnePoint.rec with
      | infty =>
        -- `z = T ∞ = z₃`, where `Fₙ z = f z₃` from `N` on
        have hz3 : z = z₃ := by
          have h1 := (Homeomorph.symm_apply_eq eT).1 hq
          rw [hTinf] at h1
          exact OnePoint.coe_injective h1
        have hlim3 : Tendsto (fun n => F n (z : ExtPlane)) atTop (𝓝 (meroToExt f z₃)) :=
          tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => by rw [hz3]; exact (hF3 n hn).symm⟩)
        rw [OnePoint.map_infty, tendsto_nhds_unique he hlim3]
        exact hAinf.symm
      | coe w =>
        rw [OnePoint.map_some]
        have hzT : (z : ExtPlane) = eT w := (Homeomorph.symm_apply_eq eT).1 hq
        -- `A(Fₙ z)` is finite from `N` on: otherwise `Fₙ z = Fₙ z₃`, so `z = z₃ = T ∞`
        have hfin : ∀ n, N ≤ n → eA (F n (z : ExtPlane)) ≠ extInf := by
          intro n hn hinf'
          have h1 : eA (F n (z : ExtPlane)) = eA (F n (z₃ : ExtPlane)) := by
            rw [hinf', hF3 n hn]
            exact hAinf.symm
          have h2 := OnePoint.coe_injective ((hF n).1.1 (eA.injective h1))
          rw [h2, ← hTinf, Homeomorph.symm_apply_apply] at hq
          exact OnePoint.infty_ne_coe w hq
        -- so the plane maps at `w` are `A(F_{m + N} z)`
        have hval : ∀ m, ((hn m w : ℂ) : ExtPlane) = eA (F (m + N) (z : ExtPlane)) := fun m => by
          show ((extToC (mobiusExt a b c d (F (m + N) (eT w))) : ℂ) : ExtPlane) = _
          rw [← hzT]
          obtain ⟨c', hc'⟩ := OnePoint.ne_infty_iff_exists.1 (hfin (m + N) (Nat.le_add_left N m))
          show ((extToC (eA (F (m + N) (z : ExtPlane))) : ℂ) : ExtPlane) = _
          rw [← hc']
          rfl
        have h1 : Tendsto (fun m => eA (F (φ m + N) (z : ExtPlane))) atTop (𝓝 ((h w : ℂ) : ExtPlane)) :=
          ((OnePoint.continuous_coe.tendsto _).comp (hpt w)).congr fun m => hval (φ m)
        exact tendsto_nhds_unique h1 hAe
    exact key _ rfl

/-- **NORM** (normalization): let `A ∘ G ∘ T = ĥ` with `A, T` Möbius and `h` a `K'`-q.c. map of `ℂ` onto `ℂ`.  Then a
Möbius `M` makes `M ∘ G` the extension of a normalized `K'`-q.c. map `H` of the plane: `M` sends `G ∞, G 0, G 1` to
`∞, 0, 1`, via `t203_pack_core` as in `t203_package`, then an affine normalization. -/
theorem l333_normalize {G A T : ExtPlane → ExtPlane} {h : ℂ → ℂ} {K' : ℝ} (hA : IsMobius A) (hT : IsMobius T)
    (hh : IsKQC h univ K') (hhs : h '' univ = univ) (hG : ∀ p, A (G (T p)) = OnePoint.map h p) :
    ∃ α β κ δ : ℂ, α * δ - β * κ ≠ 0 ∧ ∃ H : ℂ → ℂ, IsKQC H univ K' ∧ H '' univ = univ ∧ H 0 = 0 ∧ H 1 = 1 ∧
      ∀ p, mobiusExt α β κ δ (G p) = OnePoint.map H p := by
  obtain ⟨α₀, β₀, κ₀, δ₀, hdet₀, g₀, hg₀, hg₀s, hM₀⟩ := l333_lim_pack hA hT hh hhs hG
  obtain ⟨e₀, he₀⟩ := t203_pack_homeo hg₀ hg₀s
  have hg₀i : Function.Injective g₀ := by
    rw [← he₀]
    exact e₀.injective
  have hq : g₀ 1 - g₀ 0 ≠ 0 := sub_ne_zero.2 fun h0 => one_ne_zero (hg₀i h0)
  obtain ⟨L, hL⟩ : ∃ L : ℂ → ℂ, L = fun w => (1 * w + -g₀ 0) / (0 * w + (g₀ 1 - g₀ 0)) := ⟨_, rfl⟩
  have hLc : IsConformalOnto L univ univ := by
    rw [hL]
    exact aw_ext_affine_conformal hq
  have hLg : IsKQC (L ∘ g₀) univ K' := by
    simpa using thm7_1_comp hg₀ (isKQC_one_of_conformal isOpen_univ hLc) (subset_univ _)
  refine ⟨α₀ - g₀ 0 * κ₀, β₀ - g₀ 0 * δ₀, (g₀ 1 - g₀ 0) * κ₀, (g₀ 1 - g₀ 0) * δ₀, ?_, L ∘ g₀, hLg, ?_, ?_, ?_,
    fun p => ?_⟩
  · rw [show (α₀ - g₀ 0 * κ₀) * ((g₀ 1 - g₀ 0) * δ₀) - (β₀ - g₀ 0 * δ₀) * ((g₀ 1 - g₀ 0) * κ₀) =
      (g₀ 1 - g₀ 0) * (α₀ * δ₀ - β₀ * κ₀) by ring]
    exact mul_ne_zero hq hdet₀
  · rw [image_comp, hg₀s, hLc.2.2]
  · show L (g₀ 0) = 0
    rw [hL]
    simp
  · show L (g₀ 1) = 1
    rw [hL]
    show (1 * g₀ 1 + -g₀ 0) / (0 * g₀ 1 + (g₀ 1 - g₀ 0)) = 1
    rw [div_eq_one_iff_eq (by simpa using hq)]
    ring
  · rw [← l333_lim_mobius_affine (g₀ 0) hq, hM₀]
    induction p using OnePoint.rec with
    | infty =>
      rw [OnePoint.map_infty, OnePoint.map_infty]
      exact mobiusExt_infty_of_eq rfl
    | coe z =>
      rw [OnePoint.map_some, OnePoint.map_some, mobiusExt_coe (show (0 : ℂ) * g₀ z + (g₀ 1 - g₀ 0) ≠ 0 by
        simpa using hq), hL]
      rfl

/-- `∂ conj = 0` and `∂̄ conj = 1`. -/
theorem l333_mux_dz_conj (z : ℂ) :
    DifferentiableAt ℝ (fun w : ℂ => conj w) z ∧ dz (fun w : ℂ => conj w) z = 0 ∧
      dzbar (fun w : ℂ => conj w) z = 1 := by
  have h : HasFDerivAt (fun w : ℂ => conj w) (conjCLE : ℂ →L[ℝ] ℂ) z := conjCLE.hasFDerivAt
  refine ⟨h.differentiableAt, ?_, ?_⟩
  · rw [dz, h.fderiv]
    simp only [ContinuousLinearEquiv.coe_coe, conjCLE_apply, map_one, conj_I]
    linear_combination (1 / 2 : ℂ) * I_sq
  · rw [dzbar, h.fderiv]
    simp only [ContinuousLinearEquiv.coe_coe, conjCLE_apply, map_one, conj_I]
    linear_combination (-1 / 2 : ℂ) * I_sq

/-- The pair entering `E` never vanishes (Wronskian `1`). -/
theorem l333_mux_pair_ne {w₁ w₂ : ℂ → ℂ} {ζ u : ℂ} (hW : w₁ ζ * deriv w₂ ζ - w₂ ζ * deriv w₁ ζ = 1) :
    w₁ ζ + u * deriv w₁ ζ ≠ 0 ∨ w₂ ζ + u * deriv w₂ ζ ≠ 0 := by
  by_cases hD0 : w₂ ζ + u * deriv w₂ ζ = 0
  · exact Or.inl (t203_num_ne_zero hW hD0)
  · exact Or.inr hD0

/-- **MU** (the exact dilatation, (20.10) with `g = conj`): if a Möbius `M` sends `E(z)` to the finite value `H(z)` on
`ℍ`, then `μ_H(z) = -2 (Im z)² φ(z̄)` on `ℍ`.  Here `M ∘ E` is the `E` of the normalized pair
`(α w₁ + β w₂, κ w₁ + δ w₂)/σ` with `σ² = αδ - βκ` (`t203_c1_mobius_ratio`), which again solves `w'' + (φ/2) w = 0` with
Wronskian `1`.  So `H = N/D` near `z`, and `t203_mu_F` applies with `∂ conj = 0`, `∂̄ conj = 1`,
`(z - z̄)² = -4 (Im z)²` and `a = φ(z̄)/2`. -/
theorem l333_mu_exact {φ w₁ w₂ H : ℂ → ℂ} {α β κ δ : ℂ} (hdet : α * δ - β * κ ≠ 0)
    (hw₁ : DifferentiableOn ℂ w₁ lowerHalf) (hw₂ : DifferentiableOn ℂ w₂ lowerHalf)
    (hode : ∀ z ∈ lowerHalf, deriv (deriv w₁) z + φ z / 2 * w₁ z = 0 ∧ deriv (deriv w₂) z + φ z / 2 * w₂ z = 0 ∧
      w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = 1)
    (hH : ∀ z ∈ upperHalf, mobiusExt α β κ δ (l333_E w₁ w₂ z) = ((H z : ℂ) : ExtPlane)) {z : ℂ}
    (hz : z ∈ upperHalf) : complexDilatation H z = -2 * (z.im : ℂ) ^ 2 * φ (conj z) := by
  obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_pow_nat_eq (α * δ - β * κ) two_pos
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    apply hdet
    rw [← hσ]
    ring
  have hdet' : α / σ * (δ / σ) - β / σ * (κ / σ) = 1 := by
    rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, ← hσ, pow_two]
    exact div_self (mul_ne_zero hσ0 hσ0)
  set A₁ : ℂ → ℂ := fun y => α / σ * w₁ y + β / σ * w₂ y
  set A₂ : ℂ → ℂ := fun y => κ / σ * w₁ y + δ / σ * w₂ y
  have hconjL : ∀ y ∈ upperHalf, conj y ∈ lowerHalf := fun y hy => by
    simp only [upperHalf, lowerHalf, mem_ofPred_eq, conj_im] at hy ⊢
    linarith
  -- `M ∘ E` is the `E` of the normalized pair
  have hME : ∀ y ∈ upperHalf, mobiusExt α β κ δ (l333_E w₁ w₂ y) =
      t203_ratio (A₁ (conj y) + (y - conj y) * deriv A₁ (conj y))
        (A₂ (conj y) + (y - conj y) * deriv A₂ (conj y)) := by
    intro y hy
    have hyL := hconjL y hy
    obtain ⟨e1, -⟩ := t203_ode_comb_deriv isOpen_lowerHalf hw₁ hw₂ (α / σ) (β / σ) hyL
    obtain ⟨e2, -⟩ := t203_ode_comb_deriv isOpen_lowerHalf hw₁ hw₂ (κ / σ) (δ / σ) hyL
    rw [l333_E, t203_c1_mobius_ratio hσ0 (l333_mux_pair_ne (hode _ hyL).2.2), e1, e2]
    congr 1 <;> ring
  -- `H = N/D` near `z`
  have hev : H =ᶠ[𝓝 z] fun w => (A₁ (conj w) + (w - conj w) * deriv A₁ (conj w)) /
      (A₂ (conj w) + (w - conj w) * deriv A₂ (conj w)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_im).mem_nhds hz] with y hy
    have h := (hH y hy).symm.trans (hME y hy)
    have hD : A₂ (conj y) + (y - conj y) * deriv A₂ (conj y) ≠ 0 :=
      t203_c1_ratio_ne (h ▸ OnePoint.coe_ne_infty (H y))
    have h2 := congrArg extToC h
    rw [t203_c1_extToC_ratio hD] at h2
    exact h2
  have hDz : A₂ (conj z) + (z - conj z) * deriv A₂ (conj z) ≠ 0 := by
    have h := (hH z hz).symm.trans (hME z hz)
    exact t203_c1_ratio_ne (h ▸ OnePoint.coe_ne_infty (H z))
  -- the ODE data at `conj z`
  have hzL := hconjL z hz
  have hA₁d : DifferentiableOn ℂ A₁ lowerHalf := (hw₁.const_mul _).add (hw₂.const_mul _)
  have hA₂d : DifferentiableOn ℂ A₂ lowerHalf := (hw₁.const_mul _).add (hw₂.const_mul _)
  obtain ⟨e1, e1'⟩ := t203_ode_comb_deriv isOpen_lowerHalf hw₁ hw₂ (α / σ) (β / σ) hzL
  obtain ⟨e2, e2'⟩ := t203_ode_comb_deriv isOpen_lowerHalf hw₁ hw₂ (κ / σ) (δ / σ) hzL
  obtain ⟨o1, o2, hW⟩ := hode (conj z) hzL
  have hn := isOpen_lowerHalf.mem_nhds hzL
  obtain ⟨a1, b1⟩ := t203_ode_hasDerivAt (a := φ (conj z) / 2) (hA₁d.differentiableAt hn)
    ((hA₁d.deriv isOpen_lowerHalf).differentiableAt hn)
    (by rw [e1']; linear_combination α / σ * o1 + β / σ * o2)
  obtain ⟨a2, b2⟩ := t203_ode_hasDerivAt (a := φ (conj z) / 2) (hA₂d.differentiableAt hn)
    ((hA₂d.deriv isOpen_lowerHalf).differentiableAt hn)
    (by rw [e2']; linear_combination κ / σ * o1 + δ / σ * o2)
  have hWA : A₁ (conj z) * deriv A₂ (conj z) - A₂ (conj z) * deriv A₁ (conj z) = 1 := by
    rw [e1, e2]
    exact (neh_wronskian_comb (a := α / σ) (b := β / σ) (c := κ / σ) (d := δ / σ) hW).trans hdet'
  obtain ⟨hg, hdz, hdzbar⟩ := l333_mux_dz_conj z
  have hmu := t203_mu_F (A₁ := A₁) (B₁ := deriv A₁) (A₂ := A₂) (B₂ := deriv A₂) (g := fun w => conj w)
    (z := z) (a := φ (conj z) / 2) hg a1 b1 a2 b2 hWA hDz
  obtain ⟨c1, c2⟩ := t203_c1_dz_congr hev
  rw [complexDilatation, c1, c2]
  rw [complexDilatation, hdz, hdzbar] at hmu
  rw [hmu, Complex.sub_conj]
  push_cast
  linear_combination (2 * (z.im : ℂ) ^ 2 * φ (conj z)) * I_sq

/-- Conjugation maps `ℍ` into `𝕃`. -/
theorem l333_bel_conj_mem {z : ℂ} (hz : z ∈ upperHalf) : conj z ∈ lowerHalf := by
  have h : 0 < z.im := hz
  show (conj z).im < 0
  rw [Complex.conj_im]
  linarith

/-- Pointwise `Γ`-compatibility of `l333_mu φ` at `z ∈ ℍ` for one real Möbius map `(a z + b)/(c z + d)` of
determinant `1`, given the automorphy of `φ` at `z̄ ∈ 𝕃`. -/
theorem l333_bel_compat_pt {φ : ℂ → ℂ} {a b c d : ℝ} (hdet : a * d - b * c = 1) {z : ℂ} (hz : z ∈ upperHalf)
    (haut : φ ((a * conj z + b) / (c * conj z + d)) / ((c : ℂ) * conj z + d) ^ 4 = φ (conj z)) :
    l333_mu φ z = l333_mu φ ((a * z + b) / (c * z + d)) * (((c : ℂ) * z + d) ^ 2 / conj (((c : ℂ) * z + d) ^ 2)) := by
  have hy : 0 < z.im := hz
  have hden : (c : ℂ) * z + d ≠ 0 := bg2_d_den_ne_zero hdet hy.ne'
  have hdenc : (c : ℂ) * conj z + d ≠ 0 := bg2_d_den_ne_zero hdet (by rw [Complex.conj_im]; linarith)
  have hcj : conj ((c : ℂ) * z + d) = (c : ℂ) * conj z + d := by simp
  have hns : ((normSq ((c : ℂ) * z + d) : ℝ) : ℂ) = ((c : ℂ) * z + d) * ((c : ℂ) * conj z + d) := by
    rw [← Complex.mul_conj, hcj]
  have hnpos : 0 < normSq ((c : ℂ) * z + d) := Complex.normSq_pos.2 hden
  have him : ((a * z + b) / (c * z + d)).im = z.im / normSq ((c : ℂ) * z + d) := by
    have h := im_realMobius (a := a) (b := b) (c := c) (d := d) (w := z)
    rw [hdet, one_mul] at h
    exact h
  have hγz : (a * z + b) / (c * z + d) ∈ upperHalf := by
    show 0 < ((a * z + b) / (c * z + d)).im
    rw [him]
    positivity
  have hconjγz : conj (((a : ℂ) * z + b) / (c * z + d)) = (a * conj z + b) / (c * conj z + d) := by
    simp [map_div₀]
  have hA : φ ((a * conj z + b) / (c * conj z + d)) = φ (conj z) * ((c : ℂ) * conj z + d) ^ 4 := by
    rw [← haut, div_mul_cancel₀ _ (pow_ne_zero 4 hdenc)]
  unfold l333_mu
  rw [Set.indicator_of_mem hz, Set.indicator_of_mem hγz, hconjγz, him, hA, map_pow, hcj]
  push_cast
  rw [hns]
  field_simp

/-- **BEL** (`μ ∈ M`): let `φ` be holomorphic on `𝕃` with `|φ(z)| (Im z)² ≤ s < 1/2` there.  Then `μ = l333_mu φ` is
measurable (continuous on the open set `ℍ`, zero off it), satisfies `|μ| ≤ 2s < 1` everywhere (`Im z̄ = -Im z`), and
vanishes on `Im z ≤ 0`. -/
theorem l333_mu_mem {φ : ℂ → ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 2) (hφd : DifferentiableOn ℂ φ lowerHalf)
    (hφ : ∀ z ∈ lowerHalf, ‖φ z‖ * z.im ^ 2 ≤ s) :
    (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff (l333_mu φ) univ k) ∧ ∀ z : ℂ, z.im ≤ 0 → l333_mu φ z = 0 := by
  have hUo : IsOpen upperHalf := isOpen_upperHalf
  refine ⟨⟨2 * s, by linarith, by linarith, ?_, ?_⟩, fun z hz => ?_⟩
  · rw [Measure.restrict_univ]
    unfold l333_mu
    rw [aestronglyMeasurable_indicator_iff hUo.measurableSet]
    refine ContinuousOn.aestronglyMeasurable ?_ hUo.measurableSet
    refine ContinuousOn.mul (by fun_prop) ?_
    exact hφd.continuousOn.comp continuous_conj.continuousOn fun w hw => l333_bel_conj_mem hw
  · rw [Measure.restrict_univ]
    refine ae_of_all _ fun z => ?_
    unfold l333_mu
    by_cases hz : z ∈ upperHalf
    · rw [Set.indicator_of_mem hz]
      have h := hφ (conj z) (l333_bel_conj_mem hz)
      rw [Complex.conj_im, neg_sq] at h
      simp only [norm_mul, norm_neg, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      nlinarith
    · rw [Set.indicator_of_notMem hz, norm_zero]
      linarith
  · unfold l333_mu
    apply Set.indicator_of_notMem
    show ¬ (0 < z.im)
    linarith

/-- **BEL** (`Γ`-compatibility): for `φ ∈ Q(G₀, 𝕃)`, `μ = l333_mu φ` satisfies `μ(z) = μ(γz) (cz + d)²/conj((cz + d)²)`
at EVERY `z ∈ ℍ`.  Here `γz ∈ ℍ`, `conj(γz) = γ z̄`, `Im γz = Im z/|cz + d|²`, automorphy gives
`φ(γ z̄) = φ(z̄)(c z̄ + d)⁴` at `z̄ ∈ 𝕃`, and `(cz + d)(c z̄ + d) = |cz + d|²`. -/
theorem l333_mu_compat {φ : ℂ → ℂ} (hφ : φ ∈ automorphicQD Γ) : IsGammaCompatible Γ (l333_mu φ) := by
  obtain ⟨_, _, haut⟩ := hφ
  intro γ hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact h
  refine ae_restrict_of_forall_mem isOpen_upperHalf.measurableSet fun z hz => ?_
  exact l333_bel_compat_pt hdet hz (haut γ hγ (conj z) (l333_bel_conj_mem hz))

/-- **CORE** (the explicit Ahlfors–Weill theorem on `𝕃`, sharp radius `1/2`): let `φ` be holomorphic on `𝕃` with
`|φ(z)| (Im z)² ≤ s < 1/2` there.  Then there is a normalized q.c. map `H` of the plane, holomorphic on `𝕃` with
`S_H = φ` there, whose complex dilatation at every `z ∈ ℍ` is exactly `-2 (Im z)² φ(z̄)`.  Proof: ODE, SET/FAM, LIM with
`k = 2s`, NORM; on `𝕃`, `aw_ext_analyticAt`/`aw_ext_schwarzian`; on `ℍ` the limit is `E` (FAM + LIM), then MU. -/
theorem l333_core {φ : ℂ → ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 2) (hφd : DifferentiableOn ℂ φ lowerHalf)
    (hφ : ∀ z ∈ lowerHalf, ‖φ z‖ * z.im ^ 2 ≤ s) :
    ∃ (H : ℂ → ℂ) (K : ℝ), IsKQC H univ K ∧ H '' univ = univ ∧ H 0 = 0 ∧ H 1 = 1 ∧
      DifferentiableOn ℂ H lowerHalf ∧ (∀ z ∈ lowerHalf, schwarzian H z = φ z) ∧
      ∀ z ∈ upperHalf, complexDilatation H z = -2 * (z.im : ℂ) ^ 2 * φ (conj z) := by
  obtain ⟨w₁, w₂, hw₁, hw₂, hode, hloc, hSf, hmero⟩ := l333_ode hφd
  obtain ⟨hfam, hconv⟩ := l333_family hs0 hs hφ hw₁ hw₂ hode
  obtain ⟨hdisc, hmono, hU⟩ := l333_disc_facts
  have hk0 : 0 ≤ 4 * s / 2 := by positivity
  have hk1 : 4 * s / 2 < 1 := by linarith
  obtain ⟨G, A, T, h, hA, hT, hh, hhs, hG, hGD, hGlim⟩ :=
    l333_limit (D := lowerHalf) (f := fun z => w₁ z / w₂ z) (Dn := l333_disc) (F := l333_F w₁ w₂)
      hk0 hk1 le_rfl ⟨-I, by simp [lowerHalf]⟩ isOpen_lowerHalf hmono (fun n => (hdisc n).2.1) hU
      fun n => ⟨(hfam n).1, (hfam n).2.1, fun z hz => ((hfam n).2.2.1 z hz).trans
        (hmero z ((hdisc n).2.2.2.1 (subset_closure hz))).symm, (hfam n).2.2.2⟩
  obtain ⟨α, β, κ, δ, hdet, H, hH, hHs, hH0, hH1, hM⟩ := l333_normalize hA hT hh hhs hG
  have hGv : ∀ v ∈ lowerHalf, mobiusExt α β κ δ (meroToExt (fun z => w₁ z / w₂ z) v) = ((H v : ℂ) : ExtPlane) := by
    intro v hv
    rw [← hGD v hv, hM]
    rfl
  refine ⟨H, (1 + 4 * s / 2) / (1 - 4 * s / 2), hH, hHs, hH0, hH1,
    fun v hv => (aw_ext_analyticAt isOpen_lowerHalf hloc hGv hv).differentiableAt.differentiableWithinAt,
    fun v hv => (aw_ext_schwarzian isOpen_lowerHalf hloc hdet hGv hv).trans (hSf v hv), fun z hz => ?_⟩
  refine l333_mu_exact hdet hw₁ hw₂ hode (fun y hy => ?_) hz
  rw [← hGlim y _ (hconv y hy), hM]
  rfl

/-- **Lemma 33.3**: `Ψ([0]) = 0` is an interior point of `Ψ(T(S₀))`: every `φ ∈ Q(G₀, 𝕃)` with
`‖φ‖ < 1/2` is `φ_μ` for `μ(z) = -2y² φ(z̄)` (`z = x + iy ∈ ℍ`), which lies in `M(G₀)`: `‖μ‖_∞ = 2‖φ‖ < 1`
and `(μ ∘ γ) conj γ'/γ' = μ`.  (The function `ψ = w₁/w₂` with `S_ψ = φ` is univalent with a
quasiconformal extension of dilatation `μ`, Theorem 20.3, and differs from `f_μ` by a Möbius map.) -/
theorem lemma33_3 (hΓ : IsFuchsian Γ) :
    bersMapGamma Γ (TeichGamma.origin Γ) = 0 ∧
      ∀ φ ∈ automorphicQD Γ, bersNormL φ < ENNReal.ofReal (1 / 2) →
        ∃ μ : BeltramiGamma Γ, (∀ z ∈ upperHalf, μ.1.1 z = -2 * (z.im : ℂ) ^ 2 * φ (conj z)) ∧
          bersMapGamma Γ (Quotient.mk _ μ) = φ := by
  have _hΓ := hΓ
  refine ⟨?_, fun φ hφ hn => ?_⟩
  · refine (bg_bersMapGamma_eq (p := TeichGamma.origin Γ) (μ := ⟨⟨0, ⟨0, le_refl 0, zero_lt_one,
      aestronglyMeasurable_const, by simp⟩, fun _ _ => rfl⟩, fun _ _ => Filter.Eventually.of_forall fun _ => by simp⟩)
      rfl).trans ?_
    funext z
    show lowerHalf.indicator (schwarzian (normalizedSolution (0 : ℂ → ℂ))) z = 0
    rw [bB_l_normalizedSolution_zero]
    by_cases hz : z ∈ lowerHalf
    · rw [indicator_of_mem hz, bB_l_schwarzian_id]
    · rw [indicator_of_notMem hz]
  obtain ⟨hle, hs0, hs⟩ := t203_t_toReal hn
  have hφs : ∀ z ∈ lowerHalf, ‖φ z‖ * z.im ^ 2 ≤ (bersNormL φ).toReal := by
    intro z hz
    have h1 : ENNReal.ofReal (‖φ z‖ * z.im ^ 2) ≤ bersNormL φ := by
      unfold bersNormL
      exact le_iSup₂_of_le z hz le_rfl
    exact (ENNReal.ofReal_le_ofReal_iff hs0).1 (h1.trans hle)
  obtain ⟨hφd, hφ0, -⟩ := id hφ
  obtain ⟨H, K, hH, hHs, hH0, hH1, hHd, hHS, hHμ⟩ := l333_core hs0 hs hφd hφs
  have hmem := l333_mu_mem hs0 hs hφd hφs
  let μ : BeltramiGamma Γ := ⟨⟨l333_mu φ, hmem⟩, l333_mu_compat hφ⟩
  have hsol : normalizedSolution (l333_mu φ) = H := by
    obtain ⟨hq, hsq, hq0, hq1, hd⟩ := ut_spec μ.1
    refine thm13_5_uniqueness_plane hq ⟨K, hH⟩ hsq hHs ?_ hq0 hq1 hH0 hH1
    have hnull : ∀ᵐ z : ℂ, z ∉ {w : ℂ | w.im = 0} := measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
    filter_upwards [hd, hnull] with z h1 h2
    rw [h1]
    show l333_mu φ z = complexDilatation H z
    rcases lt_or_gt_of_ne (h2 : z.im ≠ 0) with hlt | hgt
    · have hdiff : DifferentiableAt ℂ H z := hHd.differentiableAt (isOpen_lowerHalf.mem_nhds hlt)
      have hbar : dzbar H z = 0 := (cauchyRiemann_iff.1 hdiff).2
      rw [complexDilatation, hbar, zero_div]
      exact hmem.2 z hlt.le
    · rw [hHμ z hgt]
      exact indicator_of_mem (show z ∈ upperHalf from hgt) _
  refine ⟨μ, fun z hz => show l333_mu φ z = _ from indicator_of_mem hz _, ?_⟩
  rw [bg_bersMapGamma_eq (μ := μ) rfl]
  funext z
  show lowerHalf.indicator (schwarzian (normalizedSolution (l333_mu φ))) z = φ z
  rw [hsol]
  by_cases hz : z ∈ lowerHalf
  · rw [indicator_of_mem hz, hHS z hz]
  · rw [indicator_of_notMem hz, hφ0 z hz]

/-! ### b33 track (coordinator 553e2d), part E: Earle's lemma via the pull-back coefficient -/

/-- `bg2_normalize` for an arbitrary normalized solution `g` (not only `f_μ`, `μ ∈ M`). -/
theorem b33_e_normalize {g τ G : ℂ → ℂ} {K : ℝ} (hg : IsNormalizedSolution g τ) (hG : IsKQC G univ K)
    (hs : G '' univ = univ) (hd : ∀ᵐ z, complexDilatation G z = τ z) :
    ∀ z, g z = (G z - G 0) / (G 1 - G 0) := by
  have ha : G 1 - G 0 ≠ 0 := fun h =>
    one_ne_zero (hG.2.2.1.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
  obtain ⟨hK, hs'⟩ := bB_l_affine_isKQC hG hs (G 0) ha
  have hGc : Continuous G := continuousOn_univ.1 hG.2.2.1.1
  have hdil : ∀ z, complexDilatation (fun ζ => (G ζ - G 0) / (G 1 - G 0)) z = complexDilatation G z := by
    intro z
    exact s23_dilatation_comp_left (g := G) (z := z) (h := fun w => (w - G 0) / (G 1 - G 0))
      (k := fun u => (G 1 - G 0) * u + G 0) hGc.continuousAt (by fun_prop) (by fun_prop)
      (Eventually.of_forall fun w => by field_simp; ring)
  obtain ⟨hq, hsq, hq0, hq1, hgd⟩ := hg
  have heq := thm13_5_uniqueness_plane hq ⟨K, hK⟩ hsq hs' ?_ hq0 hq1 (by simp) (by simp [div_self ha])
  · exact fun z => congrFun heq z
  · filter_upwards [hgd, hd] with z h1 h2
    rw [h1, hdil z, h2]

/-- A real Möbius map sends real points to real points (as a complex number: `mobiusFn` of real data). -/
theorem b33_e_mobius_real (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x : ℝ) :
    mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (x : ℂ) =
      (((γ 0 0 * x + γ 0 1) / (γ 1 0 * x + γ 1 1) : ℝ) : ℂ) := by
  simp only [mobiusFn]
  push_cast
  ring

/-- `(a⁻¹).im = 0` for `a.im = 0`. -/
theorem b33_e_inv_im {a : ℂ} (ha : a.im = 0) : (a⁻¹).im = 0 := by
  rw [Complex.inv_im, ha, neg_zero, zero_div]

/-- **MOB core** (generic): let `f` be a `K`-q.c. map of the plane onto itself with `f 0 = 0` such that `f ∘ γ` has
a.e. the dilatation `τ` of a normalized solution `g`.  Then `f ∘ γ = M ∘ g` on all of `ℂ` for a Möbius `M = (A, B, C,
D)`, with real coefficients when `f` is real on `ℝ`. -/
theorem b33_e_mob_core {f g τ : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hfs : f '' univ = univ) (hf0 : f 0 = 0)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hd : ∀ᵐ z, complexDilatation (f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z = τ z)
    (hg : IsNormalizedSolution g τ) :
    ∃ A B C D : ℂ, A * D - B * C ≠ 0 ∧
      (∀ z : ℂ, f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) = mobiusFn A B C D (g z)) ∧
      ((∀ x : ℝ, (f x).im = 0) → A.im = 0 ∧ B.im = 0 ∧ C.im = 0 ∧ D.im = 0) := by
  have hdetR : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · -- the affine case (`bg2_mob_affine`)
    have hdet1 := hdetR
    rw [hc, mul_zero, sub_zero] at hdet1
    have h00 : (γ 0 0 : ℂ) ≠ 0 := by
      rw [ofReal_ne_zero]
      rintro h
      rw [h, zero_mul] at hdet1
      exact zero_ne_one hdet1
    have h11 : (γ 1 1 : ℂ) ≠ 0 := by
      rw [ofReal_ne_zero]
      rintro h
      rw [h, mul_zero] at hdet1
      exact zero_ne_one hdet1
    have hT : mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) =
        fun u => (u - (-(γ 0 1 : ℂ) / γ 0 0)) / ((γ 1 1 : ℂ) / γ 0 0) := by
      funext u
      simp only [mobiusFn, hc, ofReal_zero, zero_mul, zero_add]
      field_simp
      ring
    have hTc : IsConformalOnto (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) univ univ := by
      rw [hT]
      exact nxE_affine_isConformalOnto (div_ne_zero h11 h00)
    have hG := thm7_1_comp (isKQC_one_of_conformal isOpen_univ hTc) hf (subset_univ _)
    have hs : (f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) '' univ = univ := by
      rw [image_comp, hTc.2.2, hfs]
    have hN := b33_e_normalize hg hG hs hd
    set G := f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) with hGdef
    have hΔ : G 1 - G 0 ≠ 0 := fun h =>
      one_ne_zero (hG.2.2.1.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
    refine ⟨G 1 - G 0, G 0, 0, 1, by simpa using hΔ, fun z => ?_, fun hreal => ?_⟩
    · show G z = ((G 1 - G 0) * g z + G 0) / (0 * g z + 1)
      rw [hN z, zero_mul, zero_add, div_one, mul_div_cancel₀ _ hΔ, sub_add_cancel]
    · have hG0 : (G 0).im = 0 := by
        have h := b33_e_mobius_real γ 0
        rw [ofReal_zero] at h
        simp only [hGdef, Function.comp_apply, h, hreal]
      have hG1 : (G 1).im = 0 := by
        have h := b33_e_mobius_real γ 1
        rw [ofReal_one] at h
        simp only [hGdef, Function.comp_apply, h, hreal]
      refine ⟨by rw [sub_im, hG0, hG1, sub_zero], hG0, zero_im, one_im⟩
  · -- the pole case (`bg2_mob_pole`), now with the pole itself
    have hs := hfs
    have hc' : (γ 1 0 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc
    obtain ⟨p, hp⟩ : ∃ p : ℂ, p = (γ 0 0 : ℂ) / γ 1 0 := ⟨_, rfl⟩
    obtain ⟨q, hq'⟩ : ∃ q : ℂ, q = -((γ 1 0 : ℂ) ^ 2)⁻¹ := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r : ℂ, r = (γ 1 1 : ℂ) / γ 1 0 := ⟨_, rfl⟩
    have hq : q ≠ 0 := by
      rw [hq']
      exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hc'))
    have hM : ∀ z : ℂ, z ≠ -r → mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z = p + q * (z + r)⁻¹ := by
      intro z hz
      subst hp hq' hr
      exact bg2_m1_mobius_eq hc hz
    have hpole : ∀ z : ℂ, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 ↔ z ≠ -r := by
      intro z
      rw [hr]
      exact not_congr (bg2_m1_pole_iff hc z)
    obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, G = fun z => (f (p + q * (z + r)⁻¹) - f p)⁻¹ := ⟨_, rfl⟩
    have hGh : IsHomeomorphOnto G univ univ := hG ▸ bg2_m1_isHomeomorphOnto hf hs p q r hq
    have hGK : IsKQC G univ K := b4_isKQC_univ_of_punctured hGh (hG ▸ bg2_m1_isKQC hf p q r hq)
    have hfc : Continuous f := continuousOn_univ.1 hf.2.2.1.1
    have hfi : Function.Injective f := fun a b hab => hf.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
    have hne : ∀ z : ℂ, z ≠ -r → f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) - f p ≠ 0 := by
      intro z hz h
      have h1 := hfi (sub_eq_zero.1 h)
      rw [hM z hz, add_eq_left, mul_eq_zero, inv_eq_zero] at h1
      rcases h1 with h0 | h0
      · exact hq h0
      · exact hz (eq_neg_of_add_eq_zero_left h0)
    have hGd : ∀ᵐ z, complexDilatation G z = τ z := by
      filter_upwards [hd, compl_mem_ae_iff.mpr (measure_singleton (-r))] with z h1 h2
      have hz : z ≠ -r := h2
      rw [← h1]
      have heq : EqOn G ((fun w => (w - f p)⁻¹) ∘ (f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1))) {-r}ᶜ := by
        intro w hw
        simp only [hG, Function.comp_apply, hM w hw]
      rw [abR_t_complexDilatation_congr isOpen_compl_singleton heq h2]
      have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := (hpole z).2 hz
      have hMc : ContinuousAt (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z := by
        unfold mobiusFn
        exact ((continuousAt_const.mul continuousAt_id).add continuousAt_const).div
          ((continuousAt_const.mul continuousAt_id).add continuousAt_const) hden
      refine s23_dilatation_comp_left (k := fun u => f p + u⁻¹) (hfc.continuousAt.comp hMc) ?_ ?_ ?_
      · exact (differentiableAt_id.sub (differentiableAt_const _)).inv (hne z hz)
      · exact (differentiableAt_const _).add (differentiableAt_id.inv (inv_ne_zero (hne z hz)))
      · exact Eventually.of_forall fun w => by
          simp only [inv_inv]
          ring
    have hnorm : ∀ z, g z = (G z - G 0) / (G 1 - G 0) := b33_e_normalize hg hGK hGh.2.2.1 hGd
    have hΔ : G 1 - G 0 ≠ 0 := fun h =>
      one_ne_zero (hGh.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
    have hGg : ∀ z, (G 1 - G 0) * g z + G 0 = G z := fun z => by
      rw [hnorm z]
      field_simp
      ring
    refine ⟨f p * (G 1 - G 0), f p * G 0 + 1, G 1 - G 0, G 0, ?_, fun z => ?_, fun hreal => ?_⟩
    · intro h
      apply hΔ
      linear_combination -h
    · by_cases hz' : z = -r
      · -- the pole: both sides are Lean's `0`
        have hden : (γ 1 0 : ℂ) * z + γ 1 1 = 0 := by
          by_contra h
          exact ((hpole z).1 h) hz'
        have hGr : G z = 0 := by
          rw [hG]
          show (f (p + q * (z + r)⁻¹) - f p)⁻¹ = 0
          rw [hz', neg_add_cancel, inv_zero, mul_zero, add_zero, sub_self, inv_zero]
        rw [mobiusFn, hden, div_zero, hf0, mobiusFn, hGg z, hGr, div_zero]
      · have hGz : G z = (f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) - f p)⁻¹ := by
          simp only [hG, hM z hz']
        have hnum : f p * (G 1 - G 0) * g z + (f p * G 0 + 1) = f p * ((G 1 - G 0) * g z + G 0) + 1 := by
          ring
        show f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
          (f p * (G 1 - G 0) * g z + (f p * G 0 + 1)) / ((G 1 - G 0) * g z + G 0)
        rw [hnum, hGg z, hGz]
        have := hne z hz'
        field_simp
        ring
    · -- real coefficients: `p`, `q`, `r` are real
      have hpR : p = ((γ 0 0 / γ 1 0 : ℝ) : ℂ) := by rw [hp]; push_cast; ring
      have hqR : q = ((-(γ 1 0 ^ 2)⁻¹ : ℝ) : ℂ) := by rw [hq']; push_cast; ring
      have hrR : r = ((γ 1 1 / γ 1 0 : ℝ) : ℂ) := by rw [hr]; push_cast; ring
      have hfp : (f p).im = 0 := by rw [hpR]; exact hreal _
      have hGx : ∀ x : ℝ, (G x).im = 0 := by
        intro x
        rw [hG]
        apply b33_e_inv_im
        rw [sub_im, hfp, sub_zero, hpR, hqR, hrR]
        have e : (((γ 0 0 / γ 1 0 : ℝ) : ℂ) + ((-(γ 1 0 ^ 2)⁻¹ : ℝ) : ℂ) * ((x : ℂ) + ((γ 1 1 / γ 1 0 : ℝ) : ℂ))⁻¹) =
            ((γ 0 0 / γ 1 0 + (-(γ 1 0 ^ 2)⁻¹) * (x + γ 1 1 / γ 1 0)⁻¹ : ℝ) : ℂ) := by
          push_cast
          ring
        rw [e]
        exact hreal _
      have hG0 : (G 0).im = 0 := by simpa using hGx 0
      have hG1 : (G 1).im = 0 := by simpa using hGx 1
      refine ⟨?_, ?_, by rw [sub_im, hG0, hG1, sub_zero], hG0⟩
      · rw [mul_im, hfp, sub_im, hG0, hG1]
        ring
      · rw [add_im, mul_im, hfp, hG0, one_im]
        ring




/-- The real points where `C e(x) + D = 0` form a subsingleton (`e` injective, `(C, D) ≠ 0`). -/
theorem b33_e_rg_pole_subsingleton (e : ℂ ≃ₜ ℂ) {C D : ℂ} (hCD : ¬ (C = 0 ∧ D = 0)) :
    {x : ℝ | C * e x + D = 0}.Subsingleton := by
  intro x₁ h₁ x₂ h₂
  have h₁' : C * e x₁ + D = 0 := h₁
  have h₂' : C * e x₂ + D = 0 := h₂
  by_cases hC : C = 0
  · rw [hC, zero_mul, zero_add] at h₁'
    exact absurd ⟨hC, h₁'⟩ hCD
  · have he : e x₁ = e x₂ := mul_left_cancel₀ hC (by linear_combination h₁' - h₂')
    exact_mod_cast e.injective he

open Bornology in
/-- `x ↦ e x` tends to `∞` along `ℝ`. -/
theorem b33_e_rg_tendsto (e : ℂ ≃ₜ ℂ) :
    Tendsto (fun x : ℝ => e x) (cobounded ℝ) (cobounded ℂ) := by
  have h1 : Tendsto (fun x : ℝ => (x : ℂ)) (cobounded ℝ) (cobounded ℂ) :=
    Complex.isometry_ofReal.antilipschitzWith.tendsto_cobounded
  have h2 : Tendsto e (cobounded ℂ) (cobounded ℂ) := by
    rw [Metric.cobounded_eq_cocompact]
    exact e.map_cocompact.le
  exact h2.comp h1

open Bornology in
/-- **Rigidity**: two normalized q.c. maps `h, k` of the plane with `M ∘ h = M' ∘ k` on `ℝ` (Möbius `M, M'`; Lean
values at the poles allowed) agree on `ℝ`. -/
theorem b33_e_mob_rigid {h k : ℂ → ℂ} {K K' : ℝ} (hh : IsKQC h univ K) (hhs : h '' univ = univ)
    (hk : IsKQC k univ K') (hks : k '' univ = univ) (hh0 : h 0 = 0) (hh1 : h 1 = 1) (hk0 : k 0 = 0)
    (hk1 : k 1 = 1) {A B C D A' B' C' D' : ℂ} (hdet : A * D - B * C ≠ 0) (hdet' : A' * D' - B' * C' ≠ 0)
    (hrel : ∀ x : ℝ, mobiusFn A B C D (h x) = mobiusFn A' B' C' D' (k x)) :
    ∀ x : ℝ, h x = k x := by
  obtain ⟨eh, rfl⟩ := t1_homeomorph hh hhs
  obtain ⟨ek, rfl⟩ := t1_homeomorph hk hks
  -- `T = M⁻¹ ∘ M'` in polynomial form
  set α := D * A' - B * C' with hα
  set β := D * B' - B * D' with hβ
  set κ := A * C' - C * A' with hκ
  set δ := A * D' - C * B' with hδ
  have hdetT : α * δ - β * κ ≠ 0 := by
    have e : α * δ - β * κ = (A * D - B * C) * (A' * D' - B' * C') := by
      simp only [hα, hβ, hκ, hδ]
      ring
    rw [e]
    exact mul_ne_zero hdet hdet'
  -- the exceptional set is finite
  have hCD : ¬ (C = 0 ∧ D = 0) := fun ⟨h1, h2⟩ => hdet (by rw [h1, h2]; ring)
  have hCD' : ¬ (C' = 0 ∧ D' = 0) := fun ⟨h1, h2⟩ => hdet' (by rw [h1, h2]; ring)
  set E : Set ℝ := {x : ℝ | C * eh x + D = 0} ∪ {x : ℝ | C' * ek x + D' = 0} with hE
  have hEfin : E.Finite :=
    (b33_e_rg_pole_subsingleton eh hCD).finite.union (b33_e_rg_pole_subsingleton ek hCD').finite
  -- the polynomial relation off `E`, then everywhere (it is closed)
  have hRoff : ∀ x : ℝ, x ∉ E → eh x * (κ * ek x + δ) = α * ek x + β := by
    intro x hx
    have h1 : C * eh x + D ≠ 0 := fun h0 => hx (Or.inl h0)
    have h2 : C' * ek x + D' ≠ 0 := fun h0 => hx (Or.inr h0)
    have h := hrel x
    rw [mobiusFn, mobiusFn, div_eq_div_iff h1 h2] at h
    simp only [hα, hβ, hκ, hδ]
    linear_combination h
  have hR : ∀ x : ℝ, eh x * (κ * ek x + δ) = α * ek x + β := by
    have hcl : IsClosed {x : ℝ | eh x * (κ * ek x + δ) = α * ek x + β} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hdense : Dense Eᶜ := hEfin.countable.dense_compl ℝ
    have hsub : Eᶜ ⊆ {x : ℝ | eh x * (κ * ek x + δ) = α * ek x + β} := fun x hx => hRoff x hx
    have h := closure_minimal hsub hcl
    rw [hdense.closure_eq] at h
    exact fun x => h (mem_univ x)
  -- `κ = 0`: otherwise `h x → α/κ` along `ℝ`, but `h x → ∞`
  have hκ0 : κ = 0 := by
    by_contra hκ0
    have hk : Tendsto (fun x : ℝ => ek x) (cobounded ℝ) (cobounded ℂ) := b33_e_rg_tendsto ek
    have hT : Tendsto (fun x : ℝ => mobiusFn α β κ δ (ek x)) (cobounded ℝ) (𝓝 (α / κ)) :=
      (tendsto_mobiusFn_cobounded_of_ne hκ0).comp hk
    have hne : ∀ᶠ x : ℝ in cobounded ℝ, κ * ek x + δ ≠ 0 :=
      ((tendsto_affine_cobounded hκ0 δ).comp hk).eventually (eventually_ne_cobounded 0)
    have hev : (fun x : ℝ => mobiusFn α β κ δ (ek x)) =ᶠ[cobounded ℝ] fun x : ℝ => eh x := by
      filter_upwards [hne] with x hx
      rw [mobiusFn, div_eq_iff hx, hR x]
    exact (hT.congr' hev).not_tendsto (disjoint_nhds_cobounded _) (b33_e_rg_tendsto eh)
  have hδ0 : δ ≠ 0 := by
    intro h0
    apply hdetT
    rw [hκ0, h0]
    ring
  have hR0 := hR 0
  have hR1 := hR 1
  simp only [ofReal_zero, ofReal_one, hh0, hh1, hk0, hk1, hκ0] at hR0 hR1
  intro x
  have hx := hR x
  rw [hκ0] at hx
  apply mul_left_cancel₀ hδ0
  linear_combination hx - ek x * hR1 + (ek x - 1) * hR0



/-- Real Möbius maps commute with conjugation, pole included. -/
theorem b33_e_mobius_conj (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) :
    mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (conj z) = conj (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) := by
  simp only [mobiusFn, map_div₀, map_add, map_mul, Complex.conj_ofReal]

/-- `bg2_d_pullback` for an arbitrary map `f` with `μ_f = τ` a.e. -/
theorem b33_e_d_pullback {f τ : ℂ → ℂ} (hd : ∀ᵐ u, complexDilatation f u = τ u) {a b c d : ℂ}
    (h : a * d - b * c ≠ 0) {U : Set ℂ} (hU : IsOpen U) (hpole : ∀ z ∈ U, c * z + d ≠ 0) :
    ∀ᵐ z ∂(volume.restrict U), complexDilatation f (mobiusFn a b c d z) = τ (mobiusFn a b c d z) := by
  have hconf : IsConformalOnto (mobiusFn a b c d) U (mobiusFn a b c d '' U) := by
    refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ heq => ?_, rfl⟩
    · have hd : DifferentiableAt ℂ (fun w => (a * w + b) / (c * w + d)) z :=
        DifferentiableAt.fun_div (by fun_prop) (by fun_prop) (hpole z hz)
      exact hd.differentiableWithinAt
    · rw [← mobiusFn_inv_apply h (hpole z₁ hz₁), ← mobiusFn_inv_apply h (hpole z₂ hz₂), heq]
  have hae : ∀ᵐ u ∂(volume.restrict univ), complexDilatation f u = τ u := by
    rw [Measure.restrict_univ]
    exact hd
  exact s23_c2_ae_pullback (P := fun u => complexDilatation f u = τ u)
    (isKQC_one_of_conformal hU hconf) (subset_univ _) hae

/-- The pullback coefficient `μ_γ`: the complex dilatation of `f^μ ∘ γ`, cut off to `ℍ`. -/
def b33_e_pbCoeff (μ : ℂ → ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ℂ → ℂ :=
  upperHalf.indicator (complexDilatation (fMuSym μ ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)))

/-- The pull-back coefficient `1_ℍ μ_{f^μ ∘ γ}` lies in `M`: bounded by `k < 1`, zero on `Im z ≤ 0`. -/
theorem b33_e_pb_mem (μ : BeltramiH) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff (b33_e_pbCoeff μ.1 γ) univ k) ∧
      ∀ z : ℂ, z.im ≤ 0 → b33_e_pbCoeff μ.1 γ z = 0 := by
  obtain ⟨k, hk0, hk1, hμ⟩ := bg_beltramiH_upper μ
  obtain ⟨-, -, hK, -⟩ := bg_sym_spec hk0 hk1 hμ
  have hdetR : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hne : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 ≠ 0 := by
    have h : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast hdetR
    rw [h]
    exact one_ne_zero
  have hpole : ∀ z ∈ upperHalf, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 :=
    fun z hz => bg2_d_den_ne_zero hdetR (show 0 < z.im from hz).ne'
  have hconf : IsConformalOnto (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) upperHalf
      (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) '' upperHalf) := by
    refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ heq => ?_, rfl⟩
    · have hd : DifferentiableAt ℂ (fun w => ((γ 0 0 : ℂ) * w + γ 0 1) / ((γ 1 0 : ℂ) * w + γ 1 1)) z :=
        DifferentiableAt.fun_div (by fun_prop) (by fun_prop) (hpole z hz)
      exact hd.differentiableWithinAt
    · rw [← mobiusFn_inv_apply hne (hpole z₁ hz₁), ← mobiusFn_inv_apply hne (hpole z₂ hz₂), heq]
  set K' := 1 * ((1 + k) / (1 - k)) with hK'
  have hFK : IsKQC (fMuSym μ.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) upperHalf K' :=
    thm7_1_comp (isKQC_one_of_conformal isOpen_upperHalf hconf) hK (subset_univ _)
  have hK1 : 1 ≤ K' := hFK.2.1
  obtain ⟨-, hb⟩ := isKQC_maxDilatation_le hFK
  rw [ae_restrict_iff' isOpen_upperHalf.measurableSet] at hb
  refine ⟨⟨(K' - 1) / (K' + 1), div_nonneg (by linarith) (by linarith),
    (div_lt_one (by linarith)).2 (by linarith), ?_, ?_⟩,
    fun z hz => ?_⟩
  · exact (((measurable_dzbar _).div (measurable_dz _)).indicator
      isOpen_upperHalf.measurableSet).aestronglyMeasurable
  · rw [Measure.restrict_univ]
    filter_upwards [hb] with z hz
    by_cases hzU : z ∈ upperHalf
    · rw [b33_e_pbCoeff, indicator_of_mem hzU]
      exact hz hzU
    · rw [b33_e_pbCoeff, indicator_of_notMem hzU, norm_zero]
      exact div_nonneg (by linarith) (by linarith)
  · rw [b33_e_pbCoeff]
    exact indicator_of_notMem (fun hu : z ∈ upperHalf => absurd hz (not_le.2 hu)) _

/-- The pullback coefficient as an element of `M`. -/
def b33_e_pb (μ : BeltramiH) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : BeltramiH :=
  ⟨b33_e_pbCoeff μ.1 γ, b33_e_pb_mem μ γ⟩

/-- **PB-sym** (dilatation): `μ_{f^μ ∘ γ}` is a.e. the symmetric extension of the pull-back coefficient `μ_γ` (`f^μ ∘
γ` commutes with `z ↦ z̄`). -/
theorem b33_e_pb_sym_dil (μ : BeltramiH) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ∀ᵐ z, complexDilatation (fMuSym μ.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z =
      symmetricExtension (b33_e_pb μ γ).1 z := by
  obtain ⟨k, hk0, hk1, hμ⟩ := bg_beltramiH_upper μ
  obtain ⟨-, -, hsym, -, -⟩ := fMuSym_upperHalf hk0 hk1 hμ
  set F := fMuSym μ.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) with hFdef
  have hF : (fun w => conj (F (conj w))) = F := by
    funext w
    simp only [hFdef, Function.comp_apply, b33_e_mobius_conj, hsym, Complex.conj_conj]
  have hnull : ∀ᵐ z : ℂ, z ∉ {w : ℂ | w.im = 0} :=
    measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
  filter_upwards [hnull] with z hz
  rcases lt_or_gt_of_ne (hz : z.im ≠ 0) with hlt | hgt
  · have hc : conj z ∈ upperHalf := by
      show 0 < (conj z).im
      rw [conj_im]
      linarith
    rw [symmetricExtension, ite_eq_left hlt]
    show complexDilatation F z = conj (upperHalf.indicator (complexDilatation F) (conj z))
    rw [indicator_of_mem hc, ← bg_dilatation_conj, hF]
  · rw [symmetricExtension, ite_eq_right (not_lt.2 hgt.le)]
    show complexDilatation F z = upperHalf.indicator (complexDilatation F) z
    rw [indicator_of_mem (show z ∈ upperHalf from hgt)]

/-- **PB-L** (dilatation): `μ_{f_μ ∘ γ} = μ_γ` a.e. -/
theorem b33_e_pb_L_dil (μ : BeltramiH) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ∀ᵐ z, complexDilatation (normalizedSolution μ.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z =
      (b33_e_pb μ γ).1 z := by
  obtain ⟨k, hk0, hk1, hμ⟩ := bg_beltramiH_upper μ
  obtain ⟨-, ⟨-, -, -, -, hσd⟩, -, -⟩ := bg_sym_spec hk0 hk1 hμ
  have hdetR : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast hdetR
  have hne : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 ≠ 0 := by rw [hdet]; exact one_ne_zero
  have hpole : ∀ z : ℂ, z.im ≠ 0 → (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := fun z hz => bg2_d_den_ne_zero hdetR hz
  refine bg_ae_of_halves ?_ ?_
  · filter_upwards [bg2_d_pullback μ hne isOpen_upperHalf fun z hz => hpole z (show 0 < z.im from hz).ne',
      b33_e_d_pullback hσd hne isOpen_upperHalf fun z hz => hpole z (show 0 < z.im from hz).ne',
      ae_restrict_mem isOpen_upperHalf.measurableSet] with z h1 h2 hz
    have hz' : 0 < z.im := hz
    have hTz : 0 < (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z).im := by
      rw [mobiusFn_im_real, hdetR, one_mul]
      exact div_pos hz' (normSq_pos.2 (hpole z hz'.ne'))
    show _ = upperHalf.indicator (complexDilatation (fMuSym μ.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1))) z
    rw [indicator_of_mem hz, bg2_d_dil_mobius _ hdet (hpole z hz'.ne'), bg2_d_dil_mobius _ hdet (hpole z hz'.ne'),
      h1, h2, symmetricExtension, ite_eq_right (not_lt.2 hTz.le)]
  · filter_upwards [bg2_d_pullback μ hne isOpen_lowerHalf fun z hz => hpole z (show z.im < 0 from hz).ne,
      ae_restrict_mem isOpen_lowerHalf.measurableSet] with z h1 hz
    have hz' : z.im < 0 := hz
    have hTz : (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z).im ≤ 0 := by
      rw [mobiusFn_im_real, hdetR, one_mul]
      exact div_nonpos_of_nonpos_of_nonneg hz'.le (Complex.normSq_nonneg _)
    show _ = upperHalf.indicator (complexDilatation (fMuSym μ.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1))) z
    rw [indicator_of_notMem (show z ∉ upperHalf from fun h => absurd (h : 0 < z.im) (not_lt.2 hz'.le)),
      bg2_d_dil_mobius _ hdet (hpole z hz'.ne), h1, μ.2.2 _ hTz, zero_mul]

/-- Real coefficients from complex ones with zero imaginary parts. -/
theorem b33_e_real_coeffs {A B C D : ℂ} (hdet : A * D - B * C ≠ 0) (hA : A.im = 0) (hB : B.im = 0)
    (hC : C.im = 0) (hD : D.im = 0) :
    A.re * D.re - B.re * C.re ≠ 0 ∧ ∀ w : ℂ, mobiusFn A B C D w = mobiusFn A.re B.re C.re D.re w := by
  have eA : ((A.re : ℝ) : ℂ) = A := Complex.ext (by simp) (by simp [hA])
  have eB : ((B.re : ℝ) : ℂ) = B := Complex.ext (by simp) (by simp [hB])
  have eC : ((C.re : ℝ) : ℂ) = C := Complex.ext (by simp) (by simp [hC])
  have eD : ((D.re : ℝ) : ℂ) = D := Complex.ext (by simp) (by simp [hD])
  refine ⟨fun h => hdet ?_, fun w => by rw [eA, eB, eC, eD]⟩
  rw [← eA, ← eB, ← eC, ← eD]
  exact_mod_cast h

/-- **PB-sym**: `f^μ ∘ γ = N ∘ f^{μ_γ}` on `ℂ` for a real Möbius `N`. -/
theorem b33_e_pb_sym (μ : BeltramiH) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ∃ A B C D : ℝ, A * D - B * C ≠ 0 ∧ ∀ z : ℂ,
      fMuSym μ.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) = mobiusFn A B C D (fMuSym (b33_e_pb μ γ).1 z) := by
  obtain ⟨k, hk0, hk1, hμ⟩ := bg_beltramiH_upper μ
  obtain ⟨-, ⟨-, hs, h0, -, -⟩, hK, -⟩ := bg_sym_spec hk0 hk1 hμ
  obtain ⟨-, hreal, -⟩ := fMuSym_upperHalf hk0 hk1 hμ
  obtain ⟨k', hk0', hk1', hμ'⟩ := bg_beltramiH_upper (b33_e_pb μ γ)
  obtain ⟨-, hN', -, -⟩ := bg_sym_spec hk0' hk1' hμ'
  obtain ⟨A, B, C, D, hdet, hrel, hR⟩ := b33_e_mob_core hK hs h0 γ (b33_e_pb_sym_dil μ γ) hN'
  obtain ⟨hA, hB, hC, hD⟩ := hR hreal
  obtain ⟨hdet', heq⟩ := b33_e_real_coeffs hdet hA hB hC hD
  exact ⟨A.re, B.re, C.re, D.re, hdet', fun z => (hrel z).trans (heq _)⟩

/-- **PB-L**: `f_μ ∘ γ = M ∘ f_{μ_γ}` on `ℂ` for a Möbius `M`. -/
theorem b33_e_pb_L (μ : BeltramiH) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ∃ A B C D : ℂ, A * D - B * C ≠ 0 ∧ ∀ z : ℂ,
      normalizedSolution μ.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn A B C D (normalizedSolution (b33_e_pb μ γ).1 z) := by
  obtain ⟨⟨K, hK⟩, hs, h0, -, -⟩ := ut_spec μ
  obtain ⟨A, B, C, D, hdet, hrel, -⟩ := b33_e_mob_core hK hs h0 γ (b33_e_pb_L_dil μ γ) (ut_spec (b33_e_pb μ γ))
  exact ⟨A, B, C, D, hdet, hrel⟩

/-- `S_{f_μ ∘ γ} = S_{f_{μ_γ}}` on `𝕃` (PB-L and the Möbius invariance of the Schwarzian). -/
theorem b33_e_pb_schwarzian (μ : BeltramiH) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    EqOn (schwarzian (normalizedSolution μ.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)))
      (schwarzian (normalizedSolution (b33_e_pb μ γ).1)) lowerHalf := by
  obtain ⟨A, B, C, D, hdet, hrel⟩ := b33_e_pb_L μ γ
  have hfun : normalizedSolution μ.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) =
      fun w => (A * normalizedSolution (b33_e_pb μ γ).1 w + B) / (C * normalizedSolution (b33_e_pb μ γ).1 w + D) :=
    funext fun w => hrel w
  intro z hz
  have hconf := ut_conformal_lowerHalf (b33_e_pb μ γ)
  rw [hfun]
  exact schwarzian_mobius_comp_analytic (hconf.1.analyticAt (isOpen_lowerHalf.mem_nhds hz))
    (deriv_ne_zero_of_injOn isOpen_lowerHalf hconf.1 hconf.2.1 hz) hdet

/-- `(f^μ)⁻¹` on the real line: `invFunOn (f^μ) ℝ x` is real and `f^μ` maps it back to `x` (`f^μ` maps `ℝ` onto `ℝ`).
-/
theorem b33_e_fMuSym_invFunOn_real (μ : BeltramiH) (x : ℝ) :
    (Function.invFunOn (fMuSym μ.1) {z : ℂ | z.im = 0} x).im = 0 ∧
      fMuSym μ.1 (Function.invFunOn (fMuSym μ.1) {z : ℂ | z.im = 0} x) = x := by
  obtain ⟨k, hk0, hk1, hμ⟩ := bg_beltramiH_upper μ
  obtain ⟨hU, -, hsym, -, -⟩ := fMuSym_upperHalf hk0 hk1 hμ
  obtain ⟨-, ⟨-, hs, -⟩, -⟩ := bg_sym_spec hk0 hk1 hμ
  have hnU : (x : ℂ) ∉ upperHalf := fun h => by
    have h' : 0 < ((x : ℂ)).im := h
    rw [ofReal_im] at h'
    exact lt_irrefl 0 h'
  have hex : ∃ w ∈ {z : ℂ | z.im = 0}, fMuSym μ.1 w = x := by
    have hx : (x : ℂ) ∈ fMuSym μ.1 '' univ := by
      rw [hs]
      exact mem_univ _
    obtain ⟨w, -, hw⟩ := hx
    refine ⟨w, ?_, hw⟩
    show w.im = 0
    rcases lt_trichotomy w.im 0 with h | h | h
    · exfalso
      have hc : conj w ∈ upperHalf := by
        show 0 < (conj w).im
        rw [conj_im]
        linarith
      have h1 : fMuSym μ.1 (conj w) ∈ upperHalf := hU ▸ mem_image_of_mem _ hc
      rw [hsym, hw, conj_ofReal] at h1
      exact hnU h1
    · exact h
    · exfalso
      have h1 : fMuSym μ.1 w ∈ upperHalf := hU ▸ mem_image_of_mem _ (show w ∈ upperHalf from h)
      rw [hw] at h1
      exact hnU h1
  exact Function.invFunOn_pos hex


/-- **Earle** (one `γ ∈ SL(2, ℝ)`, no group): `S_{f_μ ∘ γ} = S_{f_μ}` on `𝕃` iff `f^μ ∘ γ ∘ (f^μ)⁻¹|ℝ` is a real
Möbius transformation (PB, `bA_equiv_of_schwarzian_eq`, `lemma33_1`, rigidity). -/
theorem b33_e_earle (μ : BeltramiH) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    EqOn (schwarzian (normalizedSolution μ.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)))
        (schwarzian (normalizedSolution μ.1)) lowerHalf ↔
      ∃ a b c d : ℝ, a * d - b * c ≠ 0 ∧ ∀ x : ℝ,
        fMuSym μ.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
            (Function.invFunOn (fMuSym μ.1) {z : ℂ | z.im = 0} x)) =
          mobiusFn a b c d x := by
  obtain ⟨A, B, C, D, hdetA, hrel⟩ := b33_e_pb_sym μ γ
  constructor
  · intro hS
    have hS' : ∀ z ∈ lowerHalf, schwarzian (normalizedSolution (b33_e_pb μ γ).1) z =
        schwarzian (normalizedSolution μ.1) z :=
      fun z hz => (b33_e_pb_schwarzian μ γ hz).symm.trans (hS hz)
    have hR : ∀ x : ℝ, fMuSym (b33_e_pb μ γ).1 x = fMuSym μ.1 x :=
      (lemma33_1 _ _).2 (bA_equiv_of_schwarzian_eq hS')
    refine ⟨A, B, C, D, hdetA, fun x => ?_⟩
    obtain ⟨him, hfx⟩ := b33_e_fMuSym_invFunOn_real μ x
    set w := Function.invFunOn (fMuSym μ.1) {z : ℂ | z.im = 0} (x : ℂ) with hwdef
    have hw : w = ((w.re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
    have hRw : fMuSym (b33_e_pb μ γ).1 w = fMuSym μ.1 w := by
      rw [hw]
      exact hR w.re
    rw [hrel w, hRw, hfx]
  · rintro ⟨a, b, c, d, hdet, hx⟩
    obtain ⟨k, hk0, hk1, hμ⟩ := bg_beltramiH_upper μ
    obtain ⟨-, hreal, -⟩ := fMuSym_upperHalf hk0 hk1 hμ
    obtain ⟨-, ⟨-, hs, h0, h1, -⟩, hK, -⟩ := bg_sym_spec hk0 hk1 hμ
    obtain ⟨k', hk0', hk1', hμ'⟩ := bg_beltramiH_upper (b33_e_pb μ γ)
    obtain ⟨-, ⟨-, hs', h0', h1', -⟩, hK', -⟩ := bg_sym_spec hk0' hk1' hμ'
    -- the hypothesis at the real points `x'`
    have hx' : ∀ x' : ℝ, fMuSym μ.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (x' : ℂ)) =
        mobiusFn a b c d (fMuSym μ.1 x') := by
      intro x'
      set y := (fMuSym μ.1 x').re with hydef
      have hy : (y : ℂ) = fMuSym μ.1 x' := Complex.ext (by simp [hydef]) (by simp [hreal x'])
      obtain ⟨-, hfx⟩ := b33_e_fMuSym_invFunOn_real μ y
      have hinj : Function.invFunOn (fMuSym μ.1) {z : ℂ | z.im = 0} (y : ℂ) = x' :=
        hK.2.2.1.2.1 (mem_univ _) (mem_univ _) (hfx.trans hy)
      have h := hx y
      rw [hinj, hy] at h
      exact h
    have hdetA' : (A : ℂ) * D - B * C ≠ 0 := by exact_mod_cast hdetA
    have hdet' : (a : ℂ) * d - b * c ≠ 0 := by exact_mod_cast hdet
    have hR : ∀ x : ℝ, fMuSym (b33_e_pb μ γ).1 x = fMuSym μ.1 x :=
      b33_e_mob_rigid hK' hs' hK hs h0' h1' h0 h1 hdetA' hdet' fun x => by rw [← hrel x, hx' x]
    have hB := bersFunction_eq_of_equiv ((lemma33_1 _ _).1 hR)
    intro z hz
    rw [b33_e_pb_schwarzian μ γ hz]
    have h := congrFun hB z
    simp only [bersFunction, indicator_of_mem hz] at h
    exact h

/-- **Earle** for any subgroup `Γ` (no Fuchsian hypothesis): `φ_μ ∈ Q(Γ, 𝕃)` iff every `f^μ γ (f^μ)⁻¹|ℝ`,
`γ ∈ Γ`, is a real Möbius transformation (`bg2_auto_iff` and `b33_e_earle`). -/
theorem b33_e_earle_group (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (μ : BeltramiH) :
    bersFunction μ.1 ∈ automorphicQD Γ ↔
      ∀ γ ∈ Γ, ∃ a b c d : ℝ, a * d - b * c ≠ 0 ∧ ∀ x : ℝ,
        fMuSym μ.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
            (Function.invFunOn (fMuSym μ.1) {z : ℂ | z.im = 0} x)) =
          mobiusFn a b c d x := by
  rw [bg2_auto_iff]
  exact forall₂_congr fun γ _ => b33_e_earle μ γ

/-- **Lemma 33.4 (Earle)**: for a measurable `μ` on `ℍ` with `‖μ‖_∞ < 1`, `φ_μ = S_{f_μ}|𝕃` belongs to
`Q(G₀, 𝕃)` iff `f^μ ∘ γ ∘ (f^μ)⁻¹|ℝ` is a fractional linear transformation for every `γ ∈ G₀`.
((33.11): `S_{f_μ ∘ γ|𝕃} = S_{f_μ|𝕃}` for all `γ`.)  The inverse `(f^μ)⁻¹|ℝ` is taken on the real line,
which `f^μ` maps onto itself (it maps `ℍ` onto `ℍ`, so a real point has no preimage in `ℍ`). -/
theorem lemma33_4_earle (hΓ : IsFuchsian Γ) (μ : BeltramiH) :
    bersFunction μ.1 ∈ automorphicQD Γ ↔
      ∀ γ ∈ Γ, ∃ a b c d : ℝ, a * d - b * c ≠ 0 ∧ ∀ x : ℝ,
        fMuSym μ.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
            (Function.invFunOn (fMuSym μ.1) {z : ℂ | z.im = 0} x)) =
          mobiusFn a b c d x := by
  have _hΓ := hΓ
  exact b33_e_earle_group Γ μ

/-! ### b33 track (coordinator 553e2d), part D: DEF, the deformation group `Γμ`, and `χ` -/

/-- `det γ = 1` in coordinates. -/
theorem b33_d_det (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rwa [Matrix.det_fin_two] at h

/-- The symmetric extension of a `γ`-compatible (on `ℍ`) coefficient is `γ`-compatible a.e. on all of `ℂ`:
on `𝕃` use `conj ∘ γ = γ ∘ conj` (`γ` real), `γ(𝕃) ⊆ 𝕃`, and pull the `ℍ`-identity back through `conj`. -/
theorem b33_d_sym_compat {μ : ℂ → ℂ} {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hμ : ∀ᵐ z ∂(volume.restrict upperHalf),
      μ z = μ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) *
        (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 / conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2))) :
    ∀ᵐ z, symmetricExtension μ z =
      symmetricExtension μ (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) *
        (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 / conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2)) := by
  have hdetR := b33_d_det γ
  have hmp : MeasurePreserving (fun z : ℂ => conj z) (volume.restrict lowerHalf)
      (volume.restrict upperHalf) := by
    have h := gzE_conj_measurePreserving.restrict_preimage isOpen_upperHalf.measurableSet
    rwa [bg_s_conj_preimage_upperHalf] at h
  refine bg_ae_of_halves ?_ ?_
  · filter_upwards [hμ, ae_restrict_mem isOpen_upperHalf.measurableSet] with z h1 hz
    have hz' : 0 < z.im := hz
    have hTz : 0 < (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z).im := by
      rw [mobiusFn_im_real, hdetR, one_mul]
      exact div_pos hz' (normSq_pos.2 (bg2_d_den_ne_zero hdetR hz'.ne'))
    rw [symmetricExtension, ite_eq_right (not_lt.2 hz'.le), symmetricExtension, ite_eq_right (not_lt.2 hTz.le)]
    exact h1
  · filter_upwards [hmp.quasiMeasurePreserving.ae hμ,
      ae_restrict_mem isOpen_lowerHalf.measurableSet] with z h1 hz
    have hz' : z.im < 0 := hz
    have hTz : (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z).im < 0 := by
      rw [mobiusFn_im_real, hdetR, one_mul]
      exact div_neg_of_neg_of_pos hz' (normSq_pos.2 (bg2_d_den_ne_zero hdetR hz'.ne))
    have hconjT : conj (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        (γ 0 0 * conj z + γ 0 1) / (γ 1 0 * conj z + γ 1 1) := by
      simp [mobiusFn, map_div₀, map_add, map_mul, Complex.conj_ofReal]
    rw [symmetricExtension, ite_eq_left hz', symmetricExtension, ite_eq_left hTz, h1, map_mul, hconjT]
    congr 1
    simp [map_div₀, map_pow, map_add, map_mul, Complex.conj_ofReal]

/-- `bg2_d_pullback` for an arbitrary map `f` with dilatation `σ` a.e. -/
theorem b33_d_pullback {f σ : ℂ → ℂ} (hd : ∀ᵐ u, complexDilatation f u = σ u) {a b c d : ℂ}
    (h : a * d - b * c ≠ 0) {U : Set ℂ} (hU : IsOpen U) (hpole : ∀ z ∈ U, c * z + d ≠ 0) :
    ∀ᵐ z ∂(volume.restrict U),
      complexDilatation f (mobiusFn a b c d z) = σ (mobiusFn a b c d z) := by
  have hconf : IsConformalOnto (mobiusFn a b c d) U (mobiusFn a b c d '' U) := by
    refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ heq => ?_, rfl⟩
    · have hd : DifferentiableAt ℂ (fun w => (a * w + b) / (c * w + d)) z :=
        DifferentiableAt.fun_div (by fun_prop) (by fun_prop) (hpole z hz)
      exact hd.differentiableWithinAt
    · rw [← mobiusFn_inv_apply h (hpole z₁ hz₁), ← mobiusFn_inv_apply h (hpole z₂ hz₂), heq]
  have hae : ∀ᵐ u ∂(volume.restrict univ), complexDilatation f u = σ u := by
    rw [Measure.restrict_univ]
    exact hd
  exact s23_c2_ae_pullback (P := fun u => complexDilatation f u = σ u)
    (isKQC_one_of_conformal hU hconf) (subset_univ _) hae

/-- **D'** (`bg2_dil_comp` generalized): if `f` has dilatation `σ` a.e. and `σ` is `γ`-compatible a.e. on `ℂ`,
then `f ∘ γ` has dilatation `σ` a.e. -/
theorem b33_d_dil_comp {f σ : ℂ → ℂ} (hd : ∀ᵐ u, complexDilatation f u = σ u)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hσ : ∀ᵐ z, σ z = σ (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) *
      (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 / conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2))) :
    ∀ᵐ z, complexDilatation (f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z = σ z := by
  have hdetR := b33_d_det γ
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast hdetR
  have hne : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 ≠ 0 := by rw [hdet]; exact one_ne_zero
  have hU : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  have hpole : ∀ z ∈ {z : ℂ | z.im ≠ 0}, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 :=
    fun z hz => bg2_d_den_ne_zero hdetR hz
  have hnull : ∀ᵐ z : ℂ, z ∉ {w : ℂ | w.im = 0} :=
    measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
  have hpb := b33_d_pullback hd hne hU hpole
  rw [ae_restrict_iff' hU.measurableSet] at hpb
  filter_upwards [hpb, hσ, hnull] with z h1 h2 h3
  have h3' : z.im ≠ 0 := h3
  rw [bg2_d_dil_mobius _ hdet (hpole z h3'), h1 h3', ← h2]

/-- **N'** (`bg2_normalize` generalized): a `K`-q.c. self-map `G` of `ℂ` with dilatation `σ` a.e. is the normalized
solution `f` of `σ` up to an affine map. -/
theorem b33_d_normalize {f σ : ℂ → ℂ} (hf : IsNormalizedSolution f σ) {G : ℂ → ℂ} {K : ℝ}
    (hG : IsKQC G univ K) (hs : G '' univ = univ) (hd : ∀ᵐ z, complexDilatation G z = σ z) :
    ∀ z, f z = (G z - G 0) / (G 1 - G 0) := by
  have ha : G 1 - G 0 ≠ 0 := fun h =>
    one_ne_zero (hG.2.2.1.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
  obtain ⟨hK, hs'⟩ := bB_l_affine_isKQC hG hs (G 0) ha
  have hGc : Continuous G := continuousOn_univ.1 hG.2.2.1.1
  have hdil : ∀ z, complexDilatation (fun ζ => (G ζ - G 0) / (G 1 - G 0)) z = complexDilatation G z := by
    intro z
    exact s23_dilatation_comp_left (g := G) (z := z) (h := fun w => (w - G 0) / (G 1 - G 0))
      (k := fun u => (G 1 - G 0) * u + G 0) hGc.continuousAt (by fun_prop) (by fun_prop)
      (Eventually.of_forall fun w => by field_simp; ring)
  obtain ⟨hfq, hfs, hf0, hf1, hfd⟩ := hf
  have heq := thm13_5_uniqueness_plane hfq ⟨K, hK⟩ hfs hs' ?_ hf0 hf1 (by simp) (by simp [div_self ha])
  · exact fun z => congrFun heq z
  · filter_upwards [hfd, hd] with z h1 h2
    rw [h1, hdil z, h2]

/-- A complex number with zero imaginary part is the coercion of its real part. -/
theorem b33_d_ofReal_re {w : ℂ} (h : w.im = 0) : ((w.re : ℝ) : ℂ) = w :=
  Complex.ext (by simp) (by simp [h])

/-- A real Möbius map at a real point is real. -/
theorem b33_d_mobiusFn_ofReal (a b c d x : ℝ) :
    mobiusFn a b c d (x : ℂ) = (((a * x + b) / (c * x + d) : ℝ) : ℂ) := by
  simp [mobiusFn]

/-- **M0'** (`bg2_mob_affine` generalized; two coefficients, REAL output): if `f ∘ γ` (`γ` affine) has the dilatation
`τ`
of the normalized solution `g`, then `f ∘ γ = A ∘ g` with `A` real affine (`g = f`, `τ = σ` is MOB). -/
theorem b33_d_mob_affine2 {f σ g τ : ℂ → ℂ} (hf : IsNormalizedSolution f σ) (hg : IsNormalizedSolution g τ)
    (hreal : ∀ x : ℝ, (f x).im = 0)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : γ 1 0 = 0)
    (hγd : ∀ᵐ z, complexDilatation (f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z = τ z) :
    ∃ a b c d : ℝ, a * d - b * c ≠ 0 ∧ ∀ z : ℂ,
      f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) = mobiusFn a b c d (g z) := by
  have hdet := b33_d_det γ
  rw [hc, mul_zero, sub_zero] at hdet
  have h00 : (γ 0 0 : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]
    rintro h
    rw [h, zero_mul] at hdet
    exact zero_ne_one hdet
  have h11 : (γ 1 1 : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]
    rintro h
    rw [h, mul_zero] at hdet
    exact zero_ne_one hdet
  have hT : mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) =
      fun u => (u - (-(γ 0 1 : ℂ) / γ 0 0)) / ((γ 1 1 : ℂ) / γ 0 0) := by
    funext u
    simp only [mobiusFn, hc, ofReal_zero, zero_mul, zero_add]
    field_simp
    ring
  have hTc : IsConformalOnto (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) univ univ := by
    rw [hT]
    exact nxE_affine_isConformalOnto (div_ne_zero h11 h00)
  obtain ⟨K, hK⟩ := hf.1
  have hG := thm7_1_comp (isKQC_one_of_conformal isOpen_univ hTc) hK (subset_univ _)
  have hs : (f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) '' univ = univ := by
    rw [image_comp, hTc.2.2, hf.2.1]
  have hN := b33_d_normalize hg hG hs hγd
  set G := f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) with hGdef
  have hΔ : G 1 - G 0 ≠ 0 := fun h =>
    one_ne_zero (hG.2.2.1.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
  -- `G 0`, `G 1` are real
  have hG0 : (G 0).im = 0 := by
    have : G 0 = f (((γ 0 0 * 0 + γ 0 1) / (γ 1 0 * 0 + γ 1 1) : ℝ) : ℂ) := by
      rw [hGdef, Function.comp_apply, ← b33_d_mobiusFn_ofReal]; simp
    rw [this]; exact hreal _
  have hG1 : (G 1).im = 0 := by
    have : G 1 = f (((γ 0 0 * 1 + γ 0 1) / (γ 1 0 * 1 + γ 1 1) : ℝ) : ℂ) := by
      rw [hGdef, Function.comp_apply, ← b33_d_mobiusFn_ofReal]; simp
    rw [this]; exact hreal _
  have hA : (((G 1 - G 0).re : ℝ) : ℂ) = G 1 - G 0 := b33_d_ofReal_re (by simp [hG0, hG1])
  have hB : (((G 0).re : ℝ) : ℂ) = G 0 := b33_d_ofReal_re hG0
  refine ⟨(G 1 - G 0).re, (G 0).re, 0, 1, ?_, fun z => ?_⟩
  · intro h
    apply hΔ
    rw [← hA]
    simp only [mul_one, mul_zero, sub_zero] at h
    rw [h, ofReal_zero]
  · conv_rhs => unfold mobiusFn
    rw [hA, hB, hN z]
    simp only [ofReal_zero, zero_mul, zero_add, ofReal_one, div_one]
    rw [mul_div_cancel₀ _ hΔ, sub_add_cancel]
    rfl

/-- **M1'** (`bg2_mob_pole` generalized; two coefficients, REAL output): if `f ∘ γ` (`γ 1 0 ≠ 0`) has the dilatation
`τ` of the normalized solution `g`, then `f ∘ γ = A ∘ g` off the pole of `γ`, with `A` real Möbius. -/
theorem b33_d_mob_pole2 {f σ g τ : ℂ → ℂ} (hf : IsNormalizedSolution f σ) (hg : IsNormalizedSolution g τ)
    (hreal : ∀ x : ℝ, (f x).im = 0)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : γ 1 0 ≠ 0)
    (hγd : ∀ᵐ z, complexDilatation (f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z = τ z) :
    ∃ a b c d : ℝ, a * d - b * c ≠ 0 ∧ ∀ z : ℂ, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 →
      f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) = mobiusFn a b c d (g z) := by
  obtain ⟨K, hK⟩ := hf.1
  have hs := hf.2.1
  have hc' : (γ 1 0 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc
  set p₀ : ℝ := γ 0 0 / γ 1 0 with hp₀
  set q₀ : ℝ := -(γ 1 0 ^ 2)⁻¹ with hq₀
  set r₀ : ℝ := γ 1 1 / γ 1 0 with hr₀
  set p : ℂ := (p₀ : ℂ) with hp
  set q : ℂ := (q₀ : ℂ) with hq'
  set r : ℂ := (r₀ : ℂ) with hr
  have hq : q ≠ 0 := by
    rw [hq', hq₀, ofReal_ne_zero]
    exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hc))
  have hM : ∀ z : ℂ, z ≠ -r → mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z = p + q * (z + r)⁻¹ := by
    intro z hz
    have hz' : z ≠ -((γ 1 1 : ℂ) / γ 1 0) := by
      rw [hr, hr₀] at hz; push_cast at hz; exact hz
    rw [bg2_m1_mobius_eq hc hz', hp, hq', hr, hp₀, hq₀, hr₀]
    push_cast
    ring
  have hpole : ∀ z : ℂ, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 ↔ z ≠ -r := by
    intro z
    rw [hr, hr₀]
    push_cast
    exact not_congr (bg2_m1_pole_iff hc z)
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, G = fun z => (f (p + q * (z + r)⁻¹) - f p)⁻¹ := ⟨_, rfl⟩
  have hGh : IsHomeomorphOnto G univ univ := hG ▸ bg2_m1_isHomeomorphOnto hK hs p q r hq
  have hGK : IsKQC G univ K := b4_isKQC_univ_of_punctured hGh (hG ▸ bg2_m1_isKQC hK p q r hq)
  have hfc : Continuous f := continuousOn_univ.1 hK.2.2.1.1
  have hfi : Function.Injective f := fun a b hab => hK.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
  have hne : ∀ z : ℂ, z ≠ -r → f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) - f p ≠ 0 := by
    intro z hz h
    have h1 := hfi (sub_eq_zero.1 h)
    rw [hM z hz, add_eq_left, mul_eq_zero, inv_eq_zero] at h1
    rcases h1 with h0 | h0
    · exact hq h0
    · exact hz (eq_neg_of_add_eq_zero_left h0)
  have hGd : ∀ᵐ z, complexDilatation G z = τ z := by
    filter_upwards [hγd, compl_mem_ae_iff.mpr (measure_singleton (-r))] with z h1 h2
    have hz : z ≠ -r := h2
    rw [← h1]
    have heq : EqOn G ((fun w => (w - f p)⁻¹) ∘ (f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1))) {-r}ᶜ := by
      intro w hw
      simp only [hG, Function.comp_apply, hM w hw]
    rw [abR_t_complexDilatation_congr isOpen_compl_singleton heq h2]
    have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := (hpole z).2 hz
    have hMc : ContinuousAt (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z := by
      unfold mobiusFn
      exact ((continuousAt_const.mul continuousAt_id).add continuousAt_const).div
        ((continuousAt_const.mul continuousAt_id).add continuousAt_const) hden
    refine s23_dilatation_comp_left (k := fun u => f p + u⁻¹) (hfc.continuousAt.comp hMc) ?_ ?_ ?_
    · exact (differentiableAt_id.sub (differentiableAt_const _)).inv (hne z hz)
    · exact (differentiableAt_const _).add (differentiableAt_id.inv (inv_ne_zero (hne z hz)))
    · exact Eventually.of_forall fun w => by
        simp only [inv_inv]
        ring
  have hnorm : ∀ z, g z = (G z - G 0) / (G 1 - G 0) := b33_d_normalize hg hGK hGh.2.2.1 hGd
  have hΔ : G 1 - G 0 ≠ 0 := fun h =>
    one_ne_zero (hGh.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
  -- realness of `f p`, `G 0`, `G 1`
  have hfp : (f p).im = 0 := hreal p₀
  have hGr : ∀ x : ℝ, (G x).im = 0 := by
    intro x
    have hx : p + q * ((x : ℂ) + r)⁻¹ = ((p₀ + q₀ * (x + r₀)⁻¹ : ℝ) : ℂ) := by
      rw [hp, hq', hr]; push_cast; ring
    rw [hG]
    simp only
    rw [hx, Complex.inv_im, Complex.sub_im, hreal, hfp, sub_zero, neg_zero, zero_div]
  have hG0 : (G 0).im = 0 := by simpa using hGr 0
  have hG1 : (G 1).im = 0 := by simpa using hGr 1
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ, (a₀ : ℂ) = f p * (G 1 - G 0) :=
    ⟨_, b33_d_ofReal_re (by simp [hfp, hG0, hG1])⟩
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : ℝ, (b₀ : ℂ) = f p * G 0 + 1 :=
    ⟨_, b33_d_ofReal_re (by simp [hfp, hG0])⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, (c₀ : ℂ) = G 1 - G 0 := ⟨_, b33_d_ofReal_re (by simp [hG0, hG1])⟩
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : ℝ, (d₀ : ℂ) = G 0 := ⟨_, b33_d_ofReal_re hG0⟩
  refine ⟨a₀, b₀, c₀, d₀, ?_, fun z hz => ?_⟩
  · intro h
    apply hΔ
    have h' : ((a₀ * d₀ - b₀ * c₀ : ℝ) : ℂ) = 0 := by rw [h]; simp
    push_cast at h'
    rw [ha₀, hb₀, hc₀, hd₀] at h'
    linear_combination -h'
  · have hz' : z ≠ -r := (hpole z).1 hz
    conv_rhs => unfold mobiusFn
    rw [ha₀, hb₀, hc₀, hd₀]
    have hGz : G z = (f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) - f p)⁻¹ := by
      simp only [hG, hM z hz']
    have hD : (G 1 - G 0) * g z + G 0 = (f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) - f p)⁻¹ := by
      rw [← hGz, hnorm z]
      field_simp
      ring
    have hnum : f p * (G 1 - G 0) * g z + (f p * G 0 + 1) = f p * ((G 1 - G 0) * g z + G 0) + 1 := by
      ring
    rw [hnum, hD]
    have := hne z hz'
    field_simp
    ring

/-- Rescaling a real Möbius map with positive determinant to `SL(2, ℝ)`. -/
theorem b33_d_rescale {a b c d : ℝ} (h : 0 < a * d - b * c) :
    ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ w : ℂ,
      mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) w = mobiusFn a b c d w := by
  set s : ℝ := (Real.sqrt (a * d - b * c))⁻¹ with hs
  have hsq : Real.sqrt (a * d - b * c) ^ 2 = a * d - b * c := Real.sq_sqrt h.le
  have hs0 : s ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 h).ne'
  have hdet : (!![s * a, s * b; s * c, s * d] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.det_fin_two_of, hs]
    have hne : Real.sqrt (a * d - b * c) ≠ 0 := (Real.sqrt_pos.2 h).ne'
    field_simp
    linarith [hsq]
  refine ⟨⟨_, hdet⟩, fun w => ?_⟩
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  unfold mobiusFn
  push_cast
  have hs0' : (s : ℂ) ≠ 0 := ofReal_ne_zero.2 hs0
  rw [show (s : ℂ) * a * w + s * b = s * (a * w + b) by ring,
    show (s : ℂ) * c * w + s * d = s * (c * w + d) by ring, mul_div_mul_left _ _ hs0']

/-- **DEF**: for `μ ∈ M(G₀)` and `γ ∈ G₀`, `f^μ ∘ γ = γ' ∘ f^μ` on `ℍ` for some `γ' ∈ SL(2, ℝ)`. -/
theorem b33_d_def (μ : BeltramiGamma Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) :
    ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ z ∈ upperHalf,
      fMuSym μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (fMuSym μ.1.1 z) := by
  obtain ⟨k, hk0, hk1, hμ⟩ := bg_beltramiH_upper μ.1
  obtain ⟨-, hN, -, -⟩ := bg_sym_spec hk0 hk1 hμ
  obtain ⟨hU, hreal, -, -, -⟩ := fMuSym_upperHalf hk0 hk1 hμ
  have hσ := b33_d_sym_compat (μ.2 γ hγ)
  have hγd := b33_d_dil_comp hN.2.2.2.2 hσ
  have hdetR := b33_d_det γ
  -- a real Möbius `A` with `f ∘ γ = A ∘ f` off the (real) pole of `γ`
  obtain ⟨a, b, c, d, hne, hrel⟩ : ∃ a b c d : ℝ, a * d - b * c ≠ 0 ∧ ∀ z ∈ upperHalf,
      fMuSym μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) = mobiusFn a b c d (fMuSym μ.1.1 z) := by
    rcases eq_or_ne (γ 1 0) 0 with hc | hc
    · obtain ⟨a, b, c, d, hne, h⟩ := b33_d_mob_affine2 hN hN hreal hc hγd
      exact ⟨a, b, c, d, hne, fun z _ => h z⟩
    · obtain ⟨a, b, c, d, hne, h⟩ := b33_d_mob_pole2 hN hN hreal hc hγd
      exact ⟨a, b, c, d, hne, fun z hz => h z (bg2_d_den_ne_zero hdetR (show 0 < z.im from hz).ne')⟩
  -- the determinant is positive: `A` maps `f(I) ∈ ℍ` into `ℍ`
  have hpos : 0 < a * d - b * c := by
    have hI : (I : ℂ) ∈ upperHalf := by show (0 : ℝ) < I.im; simp
    have h1 : fMuSym μ.1.1 I ∈ upperHalf := hU ▸ mem_image_of_mem _ hI
    have h2 : fMuSym μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) I) ∈ upperHalf :=
      hU ▸ mem_image_of_mem _ (mobiusFn_mem_upperHalf (by rw [hdetR]; exact one_pos) hI)
    rw [hrel I hI] at h2
    have h2' : 0 < (mobiusFn a b c d (fMuSym μ.1.1 I)).im := h2
    rw [mobiusFn_im_real] at h2'
    have h1' : 0 < (fMuSym μ.1.1 I).im := h1
    rcases lt_or_gt_of_ne hne with h | h
    · exfalso
      have := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h.le h1'.le)
        (Complex.normSq_nonneg ((c : ℂ) * fMuSym μ.1.1 I + d))
      linarith
    · exact h
  obtain ⟨γ', hγ'⟩ := b33_d_rescale hpos
  exact ⟨γ', fun z hz => by rw [hγ', hrel z hz]⟩

/-- `mobiusFn` of `g ∈ SL(2, ℝ)` on `ℍ` is Mathlib's action `g • τ`. -/
theorem b33_d_mobiusFn_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    mobiusFn (g 0 0) (g 0 1) (g 1 0) (g 1 1) (τ : ℂ) = ((g • τ : UpperHalfPlane) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mobiusFn]

/-- The conjugate group `{γ' | ∃ γ ∈ Γ, F ∘ γ = γ' ∘ F}` of `Γ` by a map `F : ℍ → ℍ` (a subgroup for any `F`). -/
def b33_d_conjGroup (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (F : UpperHalfPlane → UpperHalfPlane) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) where
  carrier := {γ' | ∃ γ ∈ Γ, ∀ τ, F (γ • τ) = γ' • F τ}
  mul_mem' := by
    rintro a b ⟨γa, hγa, ha⟩ ⟨γb, hγb, hb⟩
    exact ⟨γa * γb, Γ.mul_mem hγa hγb, fun τ => by rw [mul_smul, ha, hb, mul_smul]⟩
  one_mem' := ⟨1, Γ.one_mem, fun τ => by rw [one_smul, one_smul]⟩
  inv_mem' := by
    rintro a ⟨γ, hγ, h⟩
    refine ⟨γ⁻¹, Γ.inv_mem hγ, fun τ => ?_⟩
    have h' := h (γ⁻¹ • τ)
    rw [smul_inv_smul] at h'
    rw [h', inv_smul_smul]

/-- An element of `SL(2, ℝ)` acting trivially on `ℍ` is diagonal scalar. -/
theorem b33_d_coeffs_of_smul_eq_self {k : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hk : ∀ τ : UpperHalfPlane, k • τ = τ) : k 1 0 = 0 ∧ k 0 1 = 0 ∧ k 0 0 = k 1 1 := by
  have key : ∀ t : ℝ, 0 < t →
      (k 0 0 : ℂ) * ((t : ℂ) * I) + k 0 1 = ((t : ℂ) * I) * ((k 1 0 : ℂ) * ((t : ℂ) * I) + k 1 1) := by
    intro t ht
    have hτ : 0 < ((t : ℂ) * I).im := by simpa using ht
    have h := congrArg UpperHalfPlane.coe (hk ⟨(t : ℂ) * I, hτ⟩)
    rw [← b33_d_mobiusFn_smul] at h
    have hden : ((k 1 0 : ℂ) * ((t : ℂ) * I) + k 1 1) ≠ 0 :=
      mobiusFn_den_ne_zero_real (by rw [b33_d_det k]; exact one_ne_zero) hτ
    simp only [mobiusFn] at h
    rw [div_eq_iff hden] at h
    exact h
  have h1 := key 1 one_pos
  have h2 := key 2 two_pos
  have e1 := congrArg Complex.re h1
  have e2 := congrArg Complex.im h1
  have e3 := congrArg Complex.re h2
  simp at e1 e2 e3
  refine ⟨by linarith, by linarith, by linarith⟩

/-- An element of `SL(2, ℝ)` which is diagonal scalar is `±1`. -/
theorem b33_d_eq_one_or_neg_one {k : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h10 : k 1 0 = 0) (h01 : k 0 1 = 0)
    (hd : k 0 0 = k 1 1) : k = 1 ∨ k = -1 := by
  have hdet := b33_d_det k
  rw [h10, mul_zero, sub_zero, ← hd] at hdet
  have hsq : (k 0 0 - 1) * (k 0 0 + 1) = 0 := by linear_combination hdet
  rcases mul_eq_zero.1 hsq with h | h
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10] <;> linarith
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10] <;> linarith

/-- Two elements of `SL(2, ℝ)` with the same action on `ℍ` agree up to sign. -/
theorem b33_d_eq_or_eq_neg {g h : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hgh : ∀ τ : UpperHalfPlane, g • τ = h • τ) : g = h ∨ g = -h := by
  have hk : ∀ τ : UpperHalfPlane, (h⁻¹ * g) • τ = τ := fun τ => by rw [mul_smul, hgh, inv_smul_smul]
  obtain ⟨h10, h01, hd⟩ := b33_d_coeffs_of_smul_eq_self hk
  have hg : g = h * (h⁻¹ * g) := (mul_inv_cancel_left h g).symm
  rcases b33_d_eq_one_or_neg_one h10 h01 hd with h1 | h1
  · left
    rw [hg, h1, mul_one]
  · right
    rw [hg, h1, mul_neg, mul_one]

/-- The conjugate of a Fuchsian group by a homeomorphism of `ℍ` is Fuchsian: `γ'C ∩ C ≠ ∅` iff
`γ(F⁻¹C) ∩ F⁻¹C ≠ ∅`, `F⁻¹C` is compact, and each `γ` has at most the two lifts `±γ'`. -/
theorem b33_d_conjGroup_isFuchsian (hΓ : IsFuchsian Γ) (F : UpperHalfPlane ≃ₜ UpperHalfPlane) :
    IsFuchsian (b33_d_conjGroup Γ F) := by
  intro C hC
  have hC' : IsCompact (F ⁻¹' C) := F.isCompact_preimage.2 hC
  have hS := hΓ _ hC'
  have hL : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      {γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ | ∀ τ, F (γ • τ) = γ' • F τ}.Finite := by
    intro γ
    by_cases hne : ∃ γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ τ, F (γ • τ) = γ₀ • F τ
    · obtain ⟨γ₀, h₀⟩ := hne
      refine (Set.toFinite {γ₀, -γ₀}).subset fun γ' hγ' => ?_
      have hw : ∀ w, γ' • w = γ₀ • w := fun w => by
        obtain ⟨τ, rfl⟩ := F.surjective w
        rw [← hγ' τ, h₀ τ]
      rcases b33_d_eq_or_eq_neg hw with h | h
      · exact Or.inl h
      · exact Or.inr h
    · push Not at hne
      refine Set.Finite.subset Set.finite_empty fun γ' hγ' => ?_
      simp only [mem_ofPred_eq] at hγ'
      obtain ⟨τ, hτ⟩ := hne γ'
      exact absurd (hγ' τ) hτ
  refine (hS.biUnion fun γ _ => hL γ).subset ?_
  rintro γ' ⟨⟨γ, hγ, hrel⟩, x, ⟨τ, hτC, rfl⟩, hxC⟩
  refine mem_iUnion₂.2 ⟨γ, ⟨hγ, γ • F.symm τ, ⟨F.symm τ, ?_, rfl⟩, ?_⟩, hrel⟩
  · show F (F.symm τ) ∈ C
    rw [F.apply_symm_apply]
    exact hτC
  · show F (γ • F.symm τ) ∈ C
    rw [hrel, F.apply_symm_apply]
    exact hxC

/-- `f^μ|ℍ` as a homeomorphism of `ℍ`. -/
theorem b33_d_homeo_upper {f : ℂ → ℂ} {K : ℝ} (hK : IsKQC f univ K) (hs : f '' univ = univ)
    (hU : f '' upperHalf = upperHalf) : ∃ F : UpperHalfPlane ≃ₜ UpperHalfPlane, ∀ τ, (F τ : ℂ) = f τ := by
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  have hiff : ∀ z : ℂ, 0 < z.im ↔ 0 < (e z).im := by
    intro z
    constructor
    · intro hz
      have hm : f z ∈ f '' upperHalf := mem_image_of_mem f hz
      rw [hU] at hm
      rw [he]
      exact hm
    · intro hz
      have hm : e z ∈ upperHalf := hz
      rw [he, ← hU] at hm
      obtain ⟨w, hw, hfw⟩ := hm
      rw [← he] at hfw
      rw [← e.injective hfw]
      exact hw
  have hiff' : ∀ τ : UpperHalfPlane, 0 < (e.symm τ).im := fun τ =>
    (hiff _).2 (by rw [e.apply_symm_apply]; exact τ.coe_im_pos)
  refine ⟨{ toFun := fun τ => ⟨e τ, (hiff τ).1 τ.coe_im_pos⟩
            invFun := fun τ => ⟨e.symm τ, hiff' τ⟩
            left_inv := fun τ => UpperHalfPlane.ext (by simp)
            right_inv := fun τ => UpperHalfPlane.ext (by simp)
            continuous_toFun := UpperHalfPlane.isEmbedding_coe.continuous_iff.2
              (e.continuous.comp UpperHalfPlane.continuous_coe)
            continuous_invFun := UpperHalfPlane.isEmbedding_coe.continuous_iff.2
              (e.symm.continuous.comp UpperHalfPlane.continuous_coe) }, fun τ => ?_⟩
  show e τ = f τ
  rw [he]

/-- The conjugation relation on `ℍ` in terms of the `SL(2, ℝ)`-action. -/
theorem b33_d_rel_iff {f : ℂ → ℂ} {F : UpperHalfPlane → UpperHalfPlane} (hF : ∀ τ, (F τ : ℂ) = f τ)
    (γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (∀ z ∈ upperHalf, f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (f z)) ↔ ∀ τ, F (γ • τ) = γ' • F τ := by
  constructor
  · intro h τ
    apply UpperHalfPlane.ext
    rw [hF, ← b33_d_mobiusFn_smul, h τ τ.2, ← hF, b33_d_mobiusFn_smul]
  · intro h z hz
    have h' := congrArg UpperHalfPlane.coe (h ⟨z, hz⟩)
    rw [hF, ← b33_d_mobiusFn_smul, ← b33_d_mobiusFn_smul, hF] at h'
    exact h'

/-! ### chi_eq_iff helpers -/

/-- `mobiusFn` is unchanged by `A ↦ -A`. -/
theorem b33_d_mobiusFn_neg (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℂ) :
    mobiusFn ((-A) 0 0) ((-A) 0 1) ((-A) 1 0) ((-A) 1 1) w = mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) w := by
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, ofReal_neg, mobiusFn]
  rw [show -(A 0 0 : ℂ) * w + -(A 0 1 : ℂ) = -((A 0 0 : ℂ) * w + A 0 1) by ring,
    show -(A 1 0 : ℂ) * w + -(A 1 1 : ℂ) = -((A 1 0 : ℂ) * w + A 1 1) by ring, neg_div_neg_eq]

/-- Two elements of `SL(2, ℝ)` agreeing on `ℍ` define the same function on `ℂ`. -/
theorem b33_d_mobiusFn_eq_of_eqOn {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h : ∀ w ∈ upperHalf, mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) w = mobiusFn (B 0 0) (B 0 1) (B 1 0) (B 1 1) w)
    (w : ℂ) : mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) w = mobiusFn (B 0 0) (B 0 1) (B 1 0) (B 1 1) w := by
  have hs : ∀ τ : UpperHalfPlane, A • τ = B • τ := fun τ => by
    apply UpperHalfPlane.ext
    rw [← b33_d_mobiusFn_smul, ← b33_d_mobiusFn_smul, h τ τ.2]
  rcases b33_d_eq_or_eq_neg hs with h' | h'
  · rw [h']
  · rw [h', b33_d_mobiusFn_neg]

/-- A quadratic `α t² + β t + c` with three distinct real roots vanishes identically. -/
theorem b33_d_quad_three {α β c x y z : ℝ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : α * x ^ 2 + β * x + c = 0) (hy : α * y ^ 2 + β * y + c = 0) (hz : α * z ^ 2 + β * z + c = 0) :
    α = 0 ∧ β = 0 ∧ c = 0 := by
  have h1 : α * (x + y) + β = 0 := by
    have : (x - y) * (α * (x + y) + β) = 0 := by linear_combination hx - hy
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hxy)
  have h2 : α * (x + z) + β = 0 := by
    have : (x - z) * (α * (x + z) + β) = 0 := by linear_combination hx - hz
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hxz)
  have hα : α = 0 := by
    have : (y - z) * α = 0 := by linear_combination h1 - h2
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hyz)
  have hβ : β = 0 := by rw [hα] at h1; linarith
  refine ⟨hα, hβ, ?_⟩
  rw [hα, hβ] at hx
  linarith

/-- An element of `SL(2, ℝ)` with three distinct real fixed points (roots of `c x² + (d - a) x - b`) is `±1`. -/
theorem b33_d_eq_pm_one_of_three {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {x y z : ℝ} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (hx : γ 1 0 * x ^ 2 + (γ 1 1 - γ 0 0) * x - γ 0 1 = 0)
    (hy : γ 1 0 * y ^ 2 + (γ 1 1 - γ 0 0) * y - γ 0 1 = 0)
    (hz : γ 1 0 * z ^ 2 + (γ 1 1 - γ 0 0) * z - γ 0 1 = 0) : γ = 1 ∨ γ = -1 := by
  obtain ⟨h1, h2, h3⟩ := b33_d_quad_three (α := γ 1 0) (β := γ 1 1 - γ 0 0) (c := -γ 0 1) hxy hxz hyz
    (by linarith) (by linarith) (by linarith)
  exact b33_d_eq_one_or_neg_one h1 (by linarith) (by linarith)

/-- For a real non-pole `x`, `γ x = x` iff `x` is a root of the fixed-point quadratic. -/
theorem b33_d_fix_iff (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {x : ℝ} (hx : γ 1 0 * x + γ 1 1 ≠ 0) :
    mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (x : ℂ) = x ↔
      γ 1 0 * x ^ 2 + (γ 1 1 - γ 0 0) * x - γ 0 1 = 0 := by
  have hx' : ((γ 1 0 * x + γ 1 1 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hx
  rw [mobiusFn]
  push_cast at hx' ⊢
  rw [div_eq_iff hx']
  constructor
  · intro h
    have h' : ((γ 0 0 * x + γ 0 1 : ℝ) : ℂ) = ((x * (γ 1 0 * x + γ 1 1) : ℝ) : ℂ) := by push_cast; exact h
    have h'' := ofReal_injective h'
    linear_combination -h''
  · intro h
    have h' : γ 0 0 * x + γ 0 1 = x * (γ 1 0 * x + γ 1 1) := by linear_combination -h
    exact_mod_cast h'

/-- A point of `fuchsianFixedPoints Γ` is a genuine real fixed point, off the pole, of some `γ ∈ Γ`, `γ ≠ ±1`. -/
theorem b33_d_fixedPoints_spec {x : ℝ} (hx : x ∈ fuchsianFixedPoints Γ) :
    ∃ γ ∈ Γ, γ ≠ 1 ∧ γ ≠ -1 ∧ γ 1 0 * x + γ 1 1 ≠ 0 ∧
      γ 1 0 * x ^ 2 + (γ 1 1 - γ 0 0) * x - γ 0 1 = 0 := by
  obtain ⟨γ, hγ, h1, h2, hq⟩ := hx
  refine ⟨γ, hγ, h1, h2, fun h0 => ?_, hq⟩
  have hdet := b33_d_det γ
  -- `c x + d = 0` and the quadratic give `c (c x² + (d - a) x - b) = (cx + d)(cx - a) + (ad - bc) = 1 ≠ 0`
  have : γ 1 0 * (γ 1 0 * x ^ 2 + (γ 1 1 - γ 0 0) * x - γ 0 1) =
      (γ 1 0 * x + γ 1 1) * (γ 1 0 * x - γ 0 0) + (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0) := by ring
  rw [hq, h0, hdet, mul_zero, zero_mul, zero_add] at this
  exact zero_ne_one this

/-- **P1** (extension of the conjugation relation to `ℝ`): if `g` is a continuous injection with `g ∘ γ = A ∘ g` on
`ℍ` and `x ∈ ℝ` is not the pole of `γ`, then `g x` is not the pole of `A` (else `A ∘ g → ∞` while `g ∘ γ` stays
bounded along `𝓝[ℍ] x`) and `g (γ x) = A (g x)` (limits along `𝓝[ℍ] x`). -/
theorem b33_d_ext_real {g : ℂ → ℂ} (hgc : Continuous g) (hginj : Function.Injective g)
    {γ A : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hrel : ∀ z ∈ upperHalf, g (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
      mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (g z))
    {x : ℝ} (hx : γ 1 0 * x + γ 1 1 ≠ 0) :
    (A 1 0 : ℂ) * g x + A 1 1 ≠ 0 ∧
      g (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) x) = mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (g x) := by
  have hcl : (x : ℂ) ∈ closure upperHalf := by
    rw [scExt_closure_upperHalf]
    show (0 : ℝ) ≤ (x : ℂ).im
    simp
  have : (𝓝[upperHalf] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hxden : (γ 1 0 : ℂ) * x + γ 1 1 ≠ 0 := by exact_mod_cast hx
  have hγc : ContinuousAt (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) x := by
    unfold mobiusFn
    exact ((continuousAt_const.mul continuousAt_id).add continuousAt_const).div
      ((continuousAt_const.mul continuousAt_id).add continuousAt_const) hxden
  have T1 : Tendsto (fun z => g (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z)) (𝓝[upperHalf] (x : ℂ))
      (𝓝 (g (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) x))) :=
    (hgc.continuousAt.comp hγc).tendsto.mono_left nhdsWithin_le_nhds
  have hev : (fun z => g (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z)) =ᶠ[𝓝[upperHalf] (x : ℂ)]
      fun z => mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (g z) :=
    eventually_nhdsWithin_of_forall hrel
  have hdetA : (A 0 0 : ℂ) * A 1 1 - A 0 1 * A 1 0 ≠ 0 := by
    have h := b33_d_det A
    have h' : ((A 0 0 * A 1 1 - A 0 1 * A 1 0 : ℝ) : ℂ) = 1 := by rw [h]; simp
    push_cast at h'
    rw [h']
    exact one_ne_zero
  have hden : (A 1 0 : ℂ) * g x + A 1 1 ≠ 0 := by
    intro h0
    have T2 : Tendsto g (𝓝[upperHalf] (x : ℂ)) (𝓝[≠] (g x)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨(hgc.tendsto _).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz h
      have hzx := hginj h
      have hz' : (0 : ℝ) < z.im := hz
      rw [hzx] at hz'
      simp at hz'
    have T3 := (tendsto_mobiusFn_pole hdetA h0).comp T2
    have T4 := T1.congr' hev
    rw [← tendsto_norm_atTop_iff_cobounded] at T3
    exact not_tendsto_atTop_of_tendsto_nhds T4.norm T3
  refine ⟨hden, ?_⟩
  have hAc : ContinuousAt (mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1)) (g x) := by
    unfold mobiusFn
    exact ((continuousAt_const.mul continuousAt_id).add continuousAt_const).div
      ((continuousAt_const.mul continuousAt_id).add continuousAt_const) hden
  have T3 : Tendsto (fun z => mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (g z)) (𝓝[upperHalf] (x : ℂ))
      (𝓝 (mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (g x))) :=
    (hAc.comp hgc.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique (T1.congr' hev) T3

/-- The inverse relation: `e⁻¹ ∘ A = γ ∘ e⁻¹` on `ℍ` when `e ∘ γ = A ∘ e` on `ℍ` and `e(ℍ) = ℍ`. -/
theorem b33_d_inv_rel (e : ℂ ≃ₜ ℂ) (hU : ⇑e '' upperHalf = upperHalf)
    {γ A : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hrel : ∀ z ∈ upperHalf, e (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
      mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (e z)) :
    ∀ w ∈ upperHalf, e.symm (mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) w) =
      mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (e.symm w) := by
  intro w hw
  rw [← hU] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  rw [e.symm_apply_apply, ← hrel z hz, e.symm_apply_apply]

/-- `x ↦ Re e(x)` is strictly increasing on `ℝ` for a homeomorphism `e` of `ℂ`, real on `ℝ`, fixing `0` and `1`. -/
theorem b33_d_strictMono (e : ℂ ≃ₜ ℂ) (hreal : ∀ x : ℝ, (e x).im = 0) (h0 : e 0 = 0) (h1 : e 1 = 1) :
    StrictMono fun x : ℝ => (e x).re := by
  have hc : Continuous fun x : ℝ => (e x).re :=
    Complex.continuous_re.comp (e.continuous.comp Complex.continuous_ofReal)
  have hi : Function.Injective fun x : ℝ => (e x).re := by
    intro x y hxy
    have hxy' : e x = e y := Complex.ext hxy (by rw [hreal, hreal])
    exact ofReal_injective (e.injective hxy')
  rcases hc.strictMono_of_inj hi with h | h
  · exact h
  · exfalso
    have := h (show (0 : ℝ) < 1 from one_pos)
    simp [h0, h1] at this
    linarith

/-- `e` maps `ℝ` onto `ℝ`, for a homeomorphism `e` of `ℂ` commuting with `conj` and mapping `ℍ` onto `ℍ`. -/
theorem b33_d_surj_real (e : ℂ ≃ₜ ℂ) (hU : ⇑e '' upperHalf = upperHalf)
    (hsym : ∀ z, e (conj z) = conj (e z)) (u : ℝ) : ∃ x : ℝ, e x = u := by
  set z := e.symm u with hz
  have hez : e z = u := e.apply_symm_apply _
  have hzim : z.im = 0 := by
    rcases lt_trichotomy z.im 0 with h | h | h
    · exfalso
      have hc : conj z ∈ upperHalf := by
        show (0 : ℝ) < (conj z).im
        rw [Complex.conj_im]
        linarith
      have hm : e (conj z) ∈ upperHalf := hU ▸ mem_image_of_mem _ hc
      rw [hsym, hez, Complex.conj_ofReal] at hm
      have : (0 : ℝ) < (u : ℂ).im := hm
      simp at this
    · exact h
    · exfalso
      have hm : e z ∈ upperHalf := hU ▸ mem_image_of_mem _ (show z ∈ upperHalf from h)
      rw [hez] at hm
      have : (0 : ℝ) < (u : ℂ).im := hm
      simp at this
  exact ⟨z.re, by rw [b33_d_ofReal_re hzim, hez]⟩

/-- **Fixed-point step** of `chi_eq_iff` (⇒): two symmetric normalized homeomorphisms `e₁, e₂` conjugating the same
`γ ≠ ±1` to the same `A` agree at every real fixed point `x` of `γ`: otherwise `e₁⁻¹(e₂ x)` and `e₂⁻¹(e₁ x)` are
further fixed points of `γ`, so (a quadratic has ≤ 2 roots) they coincide, contradicting monotonicity. -/
theorem b33_d_fixed_eq (e₁ e₂ : ℂ ≃ₜ ℂ) (hU₁ : ⇑e₁ '' upperHalf = upperHalf) (hU₂ : ⇑e₂ '' upperHalf = upperHalf)
    (hsym₁ : ∀ z, e₁ (conj z) = conj (e₁ z)) (hsym₂ : ∀ z, e₂ (conj z) = conj (e₂ z))
    (h0₁ : e₁ 0 = 0) (h1₁ : e₁ 1 = 1) (h0₂ : e₂ 0 = 0) (h1₂ : e₂ 1 = 1)
    {γ A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ1 : γ ≠ 1) (hγ2 : γ ≠ -1)
    (hrel₁ : ∀ z ∈ upperHalf, e₁ (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
      mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (e₁ z))
    (hrel₂ : ∀ z ∈ upperHalf, e₂ (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
      mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (e₂ z))
    {x : ℝ} (hx : γ 1 0 * x + γ 1 1 ≠ 0) (hq : γ 1 0 * x ^ 2 + (γ 1 1 - γ 0 0) * x - γ 0 1 = 0) :
    e₁ x = e₂ x := by
  have hreal₁ : ∀ t : ℝ, (e₁ t).im = 0 := fun t => by
    have h := hsym₁ t
    rw [Complex.conj_ofReal] at h
    exact Complex.conj_eq_iff_im.1 h.symm
  have hreal₂ : ∀ t : ℝ, (e₂ t).im = 0 := fun t => by
    have h := hsym₂ t
    rw [Complex.conj_ofReal] at h
    exact Complex.conj_eq_iff_im.1 h.symm
  have hfix : mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (x : ℂ) = x := (b33_d_fix_iff γ hx).2 hq
  -- the real values `u₁ = e₁ x`, `u₂ = e₂ x` are fixed points of `A`, off its pole
  obtain ⟨u₁, hu₁⟩ : ∃ u : ℝ, e₁ x = u := ⟨_, (b33_d_ofReal_re (hreal₁ x)).symm⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u : ℝ, e₂ x = u := ⟨_, (b33_d_ofReal_re (hreal₂ x)).symm⟩
  obtain ⟨hA₁, hE₁⟩ := b33_d_ext_real e₁.continuous e₁.injective hrel₁ hx
  obtain ⟨hA₂, hE₂⟩ := b33_d_ext_real e₂.continuous e₂.injective hrel₂ hx
  rw [hfix, hu₁] at hE₁
  rw [hfix, hu₂] at hE₂
  rw [hu₁] at hA₁
  rw [hu₂] at hA₂
  have hAu₁ : A 1 0 * u₁ + A 1 1 ≠ 0 := by exact_mod_cast hA₁
  have hAu₂ : A 1 0 * u₂ + A 1 1 ≠ 0 := by exact_mod_cast hA₂
  rw [hu₁, hu₂]
  by_contra hne
  have hne' : u₁ ≠ u₂ := fun h => hne (by rw [h])
  -- preimages of the other fixed point are fixed points of `γ`
  obtain ⟨y, hy⟩ := b33_d_surj_real e₁ hU₁ hsym₁ u₂
  obtain ⟨x', hx'⟩ := b33_d_surj_real e₂ hU₂ hsym₂ u₁
  obtain ⟨hγy, hEy⟩ := b33_d_ext_real e₁.symm.continuous e₁.symm.injective (b33_d_inv_rel e₁ hU₁ hrel₁) hAu₂
  obtain ⟨hγx', hEx'⟩ := b33_d_ext_real e₂.symm.continuous e₂.symm.injective (b33_d_inv_rel e₂ hU₂ hrel₂) hAu₁
  have hsy : e₁.symm u₂ = y := by rw [← hy, e₁.symm_apply_apply]
  have hsx' : e₂.symm u₁ = x' := by rw [← hx', e₂.symm_apply_apply]
  rw [← hE₂, hsy] at hEy
  rw [← hE₁, hsx'] at hEx'
  rw [hsy] at hγy
  rw [hsx'] at hγx'
  have hγy' : γ 1 0 * y + γ 1 1 ≠ 0 := by exact_mod_cast hγy
  have hγx'' : γ 1 0 * x' + γ 1 1 ≠ 0 := by exact_mod_cast hγx'
  have hqy := (b33_d_fix_iff γ hγy').1 hEy.symm
  have hqx' := (b33_d_fix_iff γ hγx'').1 hEx'.symm
  have hxy : x ≠ y := fun h => hne' (ofReal_injective (by rw [← hu₁, ← hy, h]))
  have hxx' : x ≠ x' := fun h => hne' (ofReal_injective (by rw [← hx', ← hu₂, h]))
  by_cases hyx' : y = x'
  · subst hyx'
    have hm₁ := b33_d_strictMono e₁ hreal₁ h0₁ h1₁
    have hm₂ := b33_d_strictMono e₂ hreal₂ h0₂ h1₂
    have r₁ : ∀ t : ℝ, ∀ v : ℝ, e₁ t = v → (e₁ t).re = v := fun t v h => by rw [h, ofReal_re]
    have r₂ : ∀ t : ℝ, ∀ v : ℝ, e₂ t = v → (e₂ t).re = v := fun t v h => by rw [h, ofReal_re]
    rcases lt_or_gt_of_ne hxy with h | h
    · have a1 := hm₁ h
      have a2 := hm₂ h
      simp only [r₁ _ _ hu₁, r₁ _ _ hy, r₂ _ _ hu₂, r₂ _ _ hx'] at a1 a2
      linarith
    · have a1 := hm₁ h
      have a2 := hm₂ h
      simp only [r₁ _ _ hu₁, r₁ _ _ hy, r₂ _ _ hu₂, r₂ _ _ hx'] at a1 a2
      linarith
  · rcases b33_d_eq_pm_one_of_three hxy hxx' hyx' hq hqy hqx' with h | h
    · exact hγ1 h
    · exact hγ2 h

/-- (⇐) core: two elements of `SL(2, ℝ)` agreeing at three distinct real points (off both poles) agree on `ℍ`. -/
theorem b33_d_eqOn_of_three {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ} {u v w : ℝ}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hA : ∀ t ∈ ({u, v, w} : Set ℝ), A 1 0 * t + A 1 1 ≠ 0)
    (hB : ∀ t ∈ ({u, v, w} : Set ℝ), B 1 0 * t + B 1 1 ≠ 0)
    (hAB : ∀ t ∈ ({u, v, w} : Set ℝ),
      mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (t : ℂ) = mobiusFn (B 0 0) (B 0 1) (B 1 0) (B 1 1) (t : ℂ)) :
    ∀ z ∈ upperHalf,
      mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) z = mobiusFn (B 0 0) (B 0 1) (B 1 0) (B 1 1) z := by
  have hP : ∀ t ∈ ({u, v, w} : Set ℝ),
      (A 0 0 * B 1 0 - B 0 0 * A 1 0) * t ^ 2 + (A 0 0 * B 1 1 + A 0 1 * B 1 0 - B 0 0 * A 1 1 - B 0 1 * A 1 0) * t
        + (A 0 1 * B 1 1 - B 0 1 * A 1 1) = 0 := by
    intro t ht
    have h := hAB t ht
    rw [b33_d_mobiusFn_ofReal, b33_d_mobiusFn_ofReal] at h
    have h' := ofReal_injective h
    rw [div_eq_div_iff (hA t ht) (hB t ht)] at h'
    linear_combination h'
  obtain ⟨hα, hβ, hc⟩ := b33_d_quad_three huv huw hvw (hP u (by simp)) (hP v (by simp)) (hP w (by simp))
  intro z hz
  have hdA : (A 1 0 : ℂ) * z + A 1 1 ≠ 0 := mobiusFn_den_ne_zero_real (by rw [b33_d_det A]; exact one_ne_zero) hz
  have hdB : (B 1 0 : ℂ) * z + B 1 1 ≠ 0 := mobiusFn_den_ne_zero_real (by rw [b33_d_det B]; exact one_ne_zero) hz
  unfold mobiusFn
  rw [div_eq_div_iff hdA hdB]
  have hα' : ((A 0 0 * B 1 0 - B 0 0 * A 1 0 : ℝ) : ℂ) = 0 := by rw [hα]; simp
  have hβ' : ((A 0 0 * B 1 1 + A 0 1 * B 1 0 - B 0 0 * A 1 1 - B 0 1 * A 1 0 : ℝ) : ℂ) = 0 := by rw [hβ]; simp
  have hc' : ((A 0 1 * B 1 1 - B 0 1 * A 1 1 : ℝ) : ℂ) = 0 := by rw [hc]; simp
  push_cast at hα' hβ' hc'
  linear_combination z ^ 2 * hα' + z * hβ' + hc'

/-- A non-pole of `γ` on each vertical line `x = -d/c + k`, `k ≠ 0`. -/
theorem b33_d_nonpole (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {k : ℝ} (hk : k ≠ 0) :
    γ 1 0 * (-(γ 1 1 / γ 1 0) + k) + γ 1 1 ≠ 0 := by
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · have hdet := b33_d_det γ
    rw [hc, mul_zero, sub_zero] at hdet
    rw [hc, zero_mul, zero_add]
    rintro h
    rw [h, mul_zero] at hdet
    exact zero_ne_one hdet
  · rw [mul_add, mul_neg, mul_div_cancel₀ _ hc]
    simpa using mul_ne_zero hc hk

/-- Equality on a dense subset of `ℝ` extends to `ℝ`. -/
theorem b33_d_eq_of_dense {S : Set ℝ} (hS : Dense S) {f₁ f₂ : ℂ → ℂ} (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (h : ∀ x ∈ S, f₁ x = f₂ x) (x : ℝ) : f₁ x = f₂ x :=
  congrFun (Continuous.ext_on hS (h₁.comp continuous_ofReal) (h₂.comp continuous_ofReal) h) x

/-- The facts about `f^μ` used in `chi_eq_iff`, packaged with a homeomorphism. -/
theorem b33_d_sym_facts (μ : BeltramiGamma Γ) :
    ∃ e : ℂ ≃ₜ ℂ, ⇑e = fMuSym μ.1.1 ∧ ⇑e '' upperHalf = upperHalf ∧
      (∀ z, e (conj z) = conj (e z)) ∧ e 0 = 0 ∧ e 1 = 1 := by
  obtain ⟨k, hk0, hk1, hμ⟩ := bg_beltramiH_upper μ.1
  obtain ⟨-, hN, hK, -⟩ := bg_sym_spec hk0 hk1 hμ
  obtain ⟨hU, -, hsym, -, -⟩ := fMuSym_upperHalf hk0 hk1 hμ
  obtain ⟨e, he⟩ := t1_homeomorph hK hN.2.1
  refine ⟨e, he, he ▸ hU, fun z => by rw [he]; exact hsym z, by rw [he]; exact hN.2.2.1,
    by rw [he]; exact hN.2.2.2.1⟩

/-- §33.1: for every `μ ∈ M(G₀)`, `f^μ ∘ γ ∘ (f^μ)⁻¹` (`γ ∈ G₀`) is a conformal self-map of `ℍ`
(similarity principle), hence a real Möbius transformation; the deformation
`G^μ = {f^μ γ (f^μ)⁻¹}` is a Fuchsian group isomorphic to `G₀` (of the first kind when `G₀` is). -/
theorem exists_deformation_group (hΓ : IsFuchsian Γ) (μ : BeltramiGamma Γ) :
    ∃ Γμ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ), IsFuchsian Γμ ∧
      (∀ γ ∈ Γ, ∃ γ' ∈ Γμ, ∀ z ∈ upperHalf,
        fMuSym μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
          mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (fMuSym μ.1.1 z)) ∧
      ∀ γ' ∈ Γμ, ∃ γ ∈ Γ, ∀ z ∈ upperHalf,
        fMuSym μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
          mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (fMuSym μ.1.1 z) := by
  obtain ⟨k, hk0, hk1, hμ⟩ := bg_beltramiH_upper μ.1
  obtain ⟨-, hN, hK, -⟩ := bg_sym_spec hk0 hk1 hμ
  obtain ⟨hU, -⟩ := fMuSym_upperHalf hk0 hk1 hμ
  obtain ⟨F, hF⟩ := b33_d_homeo_upper hK hN.2.1 hU
  refine ⟨b33_d_conjGroup Γ F, b33_d_conjGroup_isFuchsian hΓ F, fun γ hγ => ?_, ?_⟩
  · obtain ⟨γ', hγ'⟩ := b33_d_def μ hγ
    exact ⟨γ', ⟨γ, hγ, (b33_d_rel_iff hF γ γ').1 hγ'⟩, hγ'⟩
  · rintro γ' ⟨γ, hγ, h⟩
    exact ⟨γ, hγ, (b33_d_rel_iff hF γ γ').2 h⟩

/-- (33.5)–(33.7): the isomorphism `χ_μ : γ ↦ f^μ γ (f^μ)⁻¹` depends only on `[μ]`, and
`[μ₁] ↦ χ_{μ₁}` is injective: if `χ_{μ₁} = χ_{μ₂}` then `f^{μ₁}` and `f^{μ₂}` agree at all fixed
points of elements of `G₀`, which are dense in `ℝ` (for `G₀` of the first kind), so `[μ₁] = [μ₂]`.
Thus `T(G₀) := {χ_μ : μ ∈ M(G₀)}` is a model of `T(S₀)`, as is `{f^μ|ℝ}` (33.8). -/
theorem chi_eq_iff (hΓ : IsFuchsian Γ) (hdense : Dense (fuchsianFixedPoints Γ)) (μ₁ μ₂ : BeltramiGamma Γ) :
    (∀ γ ∈ Γ, ∀ w ∈ upperHalf, fMuSym μ₁.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
        (Function.invFunOn (fMuSym μ₁.1.1) upperHalf w)) =
      fMuSym μ₂.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (Function.invFunOn (fMuSym μ₂.1.1) upperHalf w))) ↔
      teichSetoidGamma Γ μ₁ μ₂ := by
  have _hΓ := hΓ
  obtain ⟨e₁, he₁, hU₁, hsym₁, h0₁, h1₁⟩ := b33_d_sym_facts μ₁
  obtain ⟨e₂, he₂, hU₂, hsym₂, h0₂, h1₂⟩ := b33_d_sym_facts μ₂
  -- DEF, rewritten through `e₁`, `e₂`, turns the left side into `χ₁(γ) = χ₂(γ)` on `ℍ`
  have hchi : ∀ γ ∈ Γ, ∃ A₁ A₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀ z ∈ upperHalf, e₁ (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (A₁ 0 0) (A₁ 0 1) (A₁ 1 0) (A₁ 1 1) (e₁ z)) ∧
      (∀ z ∈ upperHalf, e₂ (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (A₂ 0 0) (A₂ 0 1) (A₂ 1 0) (A₂ 1 1) (e₂ z)) ∧
      ∀ w ∈ upperHalf,
        (e₁ (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (Function.invFunOn e₁ upperHalf w)) =
          e₂ (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (Function.invFunOn e₂ upperHalf w)) ↔
        mobiusFn (A₁ 0 0) (A₁ 0 1) (A₁ 1 0) (A₁ 1 1) w = mobiusFn (A₂ 0 0) (A₂ 0 1) (A₂ 1 0) (A₂ 1 1) w) := by
    intro γ hγ
    obtain ⟨A₁, h₁⟩ := b33_d_def μ₁ hγ
    obtain ⟨A₂, h₂⟩ := b33_d_def μ₂ hγ
    rw [← he₁] at h₁
    rw [← he₂] at h₂
    refine ⟨A₁, A₂, h₁, h₂, fun w hw => ?_⟩
    have hw₁ : ∃ a ∈ upperHalf, e₁ a = w := by rw [← hU₁] at hw; exact hw
    have hw₂ : ∃ a ∈ upperHalf, e₂ a = w := by rw [← hU₂] at hw; exact hw
    rw [h₁ _ (Function.invFunOn_mem hw₁), Function.invFunOn_eq hw₁, h₂ _ (Function.invFunOn_mem hw₂),
      Function.invFunOn_eq hw₂]
  show _ ↔ ∀ x : ℝ, fMuSym μ₁.1.1 x = fMuSym μ₂.1.1 x
  rw [← he₁, ← he₂]
  constructor
  · -- (⇒) fixed points of `Γ` are dense and `e₁ = e₂` there
    intro hL
    refine b33_d_eq_of_dense hdense e₁.continuous e₂.continuous fun x hx => ?_
    obtain ⟨γ, hγ, hγ1, hγ2, hxp, hq⟩ := b33_d_fixedPoints_spec hx
    obtain ⟨A₁, A₂, h₁, h₂, hiff⟩ := hchi γ hγ
    have hA := b33_d_mobiusFn_eq_of_eqOn fun w hw => (hiff w hw).1 (hL γ hγ w hw)
    have h₂' : ∀ z ∈ upperHalf, e₂ (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (A₁ 0 0) (A₁ 0 1) (A₁ 1 0) (A₁ 1 1) (e₂ z) := fun z hz => by rw [h₂ z hz, hA]
    exact b33_d_fixed_eq e₁ e₂ hU₁ hU₂ hsym₁ hsym₂ h0₁ h1₁ h0₂ h1₂ hγ1 hγ2 h₁ h₂' hxp hq
  · -- (⇐) `χ₁(γ) = χ₂(γ)` at three real points, hence on `ℍ`
    intro hR γ hγ w hw
    obtain ⟨A₁, A₂, h₁, h₂, hiff⟩ := hchi γ hγ
    refine (hiff w hw).2 ?_
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
      rw [← hR x, hu] at hA₂ hE₂
      rw [hu] at hA₁ hE₁
      rw [b33_d_mobiusFn_ofReal, hR] at hE₁
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
    refine b33_d_eqOn_of_three (hne (by norm_num) hu₁ hu₂) (hne (by norm_num) hu₁ hu₃) (hne (by norm_num) hu₂ hu₃)
      ?_ ?_ ?_ w hw
    · intro t ht
      rcases ht with rfl | rfl | rfl <;> assumption
    · intro t ht
      rcases ht with rfl | rfl | rfl <;> assumption
    · intro t ht
      rcases ht with rfl | rfl | rfl <;> assumption

/-- (33.11): `φ_μ ∈ Q(G₀, 𝕃)` iff `S_{f_μ ∘ γ|𝕃} = S_{f_μ|𝕃}` for all `γ ∈ G₀`. -/
theorem eq33_11 (μ : BeltramiH) :
    bersFunction μ.1 ∈ automorphicQD Γ ↔
      ∀ γ ∈ Γ, EqOn (schwarzian (normalizedSolution μ.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)))
        (schwarzian (normalizedSolution μ.1)) lowerHalf := by
  exact bg2_auto_iff μ

/-- The translated coefficient `λ` with `f^λ = f^μ ∘ (f^{μ₀})⁻¹` (the coefficient of the composite
map, which is again in `M(G^{μ₀})`): `λ` is determined a.e. by `μ` and `μ₀`.  Like every element of
`M(G^{μ₀})` it is supported in `ℍ` (`f^λ` is then the map with the symmetric extension of `λ`); the
composite's dilatation on `𝕃` is its mirror image and is not part of `λ`. -/
def translatedBeltrami (μ₀ μ : ℂ → ℂ) : ℂ → ℂ :=
  upperHalf.indicator fun w => complexDilatation (fMuSym μ ∘ Function.invFunOn (fMuSym μ₀) univ) w

/-! ### b33 track (coordinator 553e2d), part T: the translation `χ` (33.12) and Theorem 33.1 -/

/-! ### C0: generic helpers -/

/-- The triangle inequality for `bersNormL`. -/
theorem b33_t_bersNormL_add_le (φ ψ : ℂ → ℂ) : bersNormL (φ + ψ) ≤ bersNormL φ + bersNormL ψ := by
  unfold bersNormL
  refine iSup₂_le fun z hz => ?_
  calc ENNReal.ofReal (‖(φ + ψ) z‖ * z.im ^ 2)
      ≤ ENNReal.ofReal (‖φ z‖ * z.im ^ 2) + ENNReal.ofReal (‖ψ z‖ * z.im ^ 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Pi.add_apply, ← add_mul]
        exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (sq_nonneg _)
    _ ≤ _ := add_le_add (le_iSup₂_of_le z hz le_rfl) (le_iSup₂_of_le z hz le_rfl)

/-- `∀ x : ℝ` statements are `∀ z` with `Im z = 0` statements. -/
theorem b33_t_forall_real_iff {F G : ℂ → ℂ} : (∀ x : ℝ, F x = G x) ↔ ∀ z : ℂ, z.im = 0 → F z = G z := by
  refine ⟨fun h z hz => ?_, fun h x => h x (Complex.ofReal_im x)⟩
  have hz' : ((z.re : ℝ) : ℂ) = z := Complex.ext rfl (by simp [hz])
  rw [← hz']
  exact h z.re

/-- The bundle of facts on `f^μ` for `μ ∈ M`. -/
theorem b33_t_fs_spec (μ : BeltramiH) :
    ∃ K : ℝ, IsKQC (fMuSym μ.1) univ K ∧ fMuSym μ.1 '' univ = univ ∧ fMuSym μ.1 0 = 0 ∧ fMuSym μ.1 1 = 1 ∧
      (∀ z, fMuSym μ.1 (conj z) = conj (fMuSym μ.1 z)) ∧ fMuSym μ.1 '' upperHalf = upperHalf ∧
      ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation (fMuSym μ.1) z = μ.1 z := by
  obtain ⟨k, hk0, hk1, hμ⟩ := bg_beltramiH_upper μ
  obtain ⟨-, ⟨-, hs, h0, h1, -⟩, hK, -⟩ := bg_sym_spec hk0 hk1 hμ
  obtain ⟨hU, -, hsym, -, hd⟩ := fMuSym_upperHalf hk0 hk1 hμ
  exact ⟨_, hK, hs, h0, h1, hsym, hU, hd⟩

/-- The bundle of facts on `(f^{μ₀})⁻¹ = invFunOn f^{μ₀} univ`. -/
theorem b33_t_fs_inv_spec (μ₀ : BeltramiH) :
    ∃ K : ℝ, IsKQC (Function.invFunOn (fMuSym μ₀.1) univ) univ K ∧
      (∀ z, Function.invFunOn (fMuSym μ₀.1) univ (fMuSym μ₀.1 z) = z) ∧
      (∀ w, fMuSym μ₀.1 (Function.invFunOn (fMuSym μ₀.1) univ w) = w) ∧
      (∀ w, Function.invFunOn (fMuSym μ₀.1) univ (conj w) = conj (Function.invFunOn (fMuSym μ₀.1) univ w)) := by
  obtain ⟨K, hK, hs, -, -, hsym, -, -⟩ := b33_t_fs_spec μ₀
  have hleft : ∀ z, Function.invFunOn (fMuSym μ₀.1) univ (fMuSym μ₀.1 z) = z := fun z =>
    hK.2.2.1.2.1.leftInvOn_invFunOn (mem_univ z)
  have hright : ∀ w, fMuSym μ₀.1 (Function.invFunOn (fMuSym μ₀.1) univ w) = w := fun w => by
    apply Function.invFunOn_eq
    have hw : w ∈ fMuSym μ₀.1 '' univ := by rw [hs]; exact mem_univ w
    obtain ⟨z, hz, hzw⟩ := hw
    exact ⟨z, hz, hzw⟩
  refine ⟨K, ?_, hleft, hright, fun w => ?_⟩
  · have h := thm7_2_inv hK
    rwa [hs] at h
  · conv_lhs => rw [← hright w, ← hsym, hleft]

/-- `f^μ` maps `ℝ` exactly onto `ℝ`. -/
theorem b33_t_fs_real (μ : BeltramiH) :
    (∀ z : ℂ, z.im = 0 → (fMuSym μ.1 z).im = 0) ∧ (∀ z : ℂ, (fMuSym μ.1 z).im = 0 → z.im = 0) ∧
      ∀ x : ℂ, x.im = 0 → ∃ y : ℂ, y.im = 0 ∧ fMuSym μ.1 y = x := by
  obtain ⟨K, hK, hs, -, -, hsym, -, -⟩ := b33_t_fs_spec μ
  have hinj : Function.Injective (fMuSym μ.1) := injOn_univ.1 hK.2.2.1.2.1
  have h1 : ∀ z : ℂ, z.im = 0 → (fMuSym μ.1 z).im = 0 := fun z hz => by
    have h := hsym z
    rw [Complex.conj_eq_iff_im.2 hz] at h
    exact Complex.conj_eq_iff_im.1 h.symm
  have h2 : ∀ z : ℂ, (fMuSym μ.1 z).im = 0 → z.im = 0 := fun z hz => by
    have h : fMuSym μ.1 (conj z) = fMuSym μ.1 z := by rw [hsym, Complex.conj_eq_iff_im.2 hz]
    exact Complex.conj_eq_iff_im.1 (hinj h)
  refine ⟨h1, h2, fun x hx => ?_⟩
  have hx' : x ∈ fMuSym μ.1 '' univ := by rw [hs]; exact mem_univ x
  obtain ⟨y, -, hy⟩ := hx'
  exact ⟨y, h2 y (hy ▸ hx), hy⟩

/-- `invFunOn F ℝ` at a real value of an injective `F` with a real preimage. -/
theorem b33_t_invFunOn_real {F : ℂ → ℂ} (hFi : Function.Injective F) {x y : ℂ} (hy : y.im = 0) (hFy : F y = x) :
    Function.invFunOn F {z : ℂ | z.im = 0} x = y :=
  hFi ((Function.invFunOn_eq ⟨y, hy, hFy⟩).trans hFy.symm)

/-- `φ_μ = φ_ν` iff `μ ∼ ν` (Bers map injective + well defined). -/
theorem b33_t_bf_eq_iff (μ ν : BeltramiH) : bersFunction μ.1 = bersFunction ν.1 ↔ teichSetoid μ ν := by
  refine ⟨fun h => bA_equiv_of_schwarzian_eq fun z hz => ?_, bersFunction_eq_of_equiv⟩
  have h' := congrFun h z
  simp only [bersFunction, indicator_of_mem hz] at h'
  exact h'

/-- **S-uniqueness**: a normalized q.c. self-map `G` of `ℂ` commuting with `z ↦ z̄` is `f^{1_ℍ μ_G}`. -/
theorem b33_t_fMuSym_eq_of_conj {G : ℂ → ℂ} {K : ℝ} (hG : IsKQC G univ K) (hs : G '' univ = univ)
    (h0 : G 0 = 0) (h1 : G 1 = 1) (hsym : ∀ z, G (conj z) = conj (G z)) :
    fMuSym (upperHalf.indicator (complexDilatation G)) = G := by
  obtain ⟨⟨k, hk0, hk1, hν⟩, -⟩ := ut_rg_indicator_mem hG
  have hνU : IsBeltramiCoeff (upperHalf.indicator (complexDilatation G)) upperHalf k := by
    obtain ⟨hm, hb⟩ := hν
    rw [Measure.restrict_univ] at hm hb
    exact ⟨hm.restrict, ae_restrict_of_ae hb⟩
  obtain ⟨-, -, -, huniq⟩ := bg_sym_spec hk0 hk1 hνU
  refine (huniq G ⟨⟨K, hG⟩, hs, h0, h1, ?_⟩).symm
  have hnull : ∀ᵐ w : ℂ, w ∉ {v : ℂ | v.im = 0} :=
    measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
  have hGc : (fun w => conj (G (conj w))) = G := funext fun w => by rw [hsym, Complex.conj_conj]
  filter_upwards [hnull] with z hz
  rcases lt_or_gt_of_ne (hz : z.im ≠ 0) with h | h
  · have hcz : conj z ∈ upperHalf := by
      show 0 < (conj z).im
      rw [Complex.conj_im]
      linarith
    rw [symmetricExtension, ite_eq_left h, indicator_of_mem hcz, ← bg_dilatation_conj, hGc]
  · rw [symmetricExtension, ite_eq_right (not_lt.2 h.le), indicator_of_mem (show z ∈ upperHalf from h)]

/-! ### C1: the translated coefficient `λ(μ) = translatedBeltrami μ₀ μ` -/

/-- `f^μ ∘ (f^{μ₀})⁻¹` is a normalized q.c. self-map of `ℂ` commuting with `z ↦ z̄`. -/
theorem b33_t_tb_comp_spec (μ₀ μ : BeltramiH) :
    ∃ K : ℝ, IsKQC (fMuSym μ.1 ∘ Function.invFunOn (fMuSym μ₀.1) univ) univ K ∧
      (fMuSym μ.1 ∘ Function.invFunOn (fMuSym μ₀.1) univ) '' univ = univ ∧
      (fMuSym μ.1 ∘ Function.invFunOn (fMuSym μ₀.1) univ) 0 = 0 ∧
      (fMuSym μ.1 ∘ Function.invFunOn (fMuSym μ₀.1) univ) 1 = 1 ∧
      ∀ z, (fMuSym μ.1 ∘ Function.invFunOn (fMuSym μ₀.1) univ) (conj z) =
        conj ((fMuSym μ.1 ∘ Function.invFunOn (fMuSym μ₀.1) univ) z) := by
  obtain ⟨K, hK, hs, h0, h1, hsym, -, -⟩ := b33_t_fs_spec μ
  obtain ⟨K₀, -, -, h₀0, h₀1, -, -, -⟩ := b33_t_fs_spec μ₀
  obtain ⟨Kg, hg, hleft, -, hgsym⟩ := b33_t_fs_inv_spec μ₀
  have hg0 : Function.invFunOn (fMuSym μ₀.1) univ 0 = 0 := by
    have h := hleft 0
    rwa [h₀0] at h
  have hg1 : Function.invFunOn (fMuSym μ₀.1) univ 1 = 1 := by
    have h := hleft 1
    rwa [h₀1] at h
  refine ⟨Kg * K, thm7_1_comp hg hK (subset_univ _), ?_, by simp [hg0, h0], by simp [hg1, h1],
    fun z => by simp only [Function.comp_apply, hgsym, hsym]⟩
  rw [image_comp]
  have hgs : Function.invFunOn (fMuSym μ₀.1) univ '' univ = univ :=
    eq_univ_of_forall fun z => ⟨_, mem_univ _, hleft z⟩
  rw [hgs, hs]

/-- `λ(μ) ∈ M`. -/
theorem b33_t_tb_mem (μ₀ μ : BeltramiH) :
    (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff (translatedBeltrami μ₀.1 μ.1) univ k) ∧
      ∀ z : ℂ, z.im ≤ 0 → translatedBeltrami μ₀.1 μ.1 z = 0 := by
  obtain ⟨K, hK, -⟩ := b33_t_tb_comp_spec μ₀ μ
  exact ut_rg_indicator_mem hK

/-- `λ(μ)` as an element of `M`. -/
def b33_t_tb (μ₀ μ : BeltramiH) : BeltramiH := ⟨translatedBeltrami μ₀.1 μ.1, b33_t_tb_mem μ₀ μ⟩

/-- **KEY**: `f^{λ(μ)} = f^μ ∘ (f^{μ₀})⁻¹` (everywhere). -/
theorem b33_t_tb_fMuSym (μ₀ μ : BeltramiH) :
    fMuSym (translatedBeltrami μ₀.1 μ.1) = fMuSym μ.1 ∘ Function.invFunOn (fMuSym μ₀.1) univ := by
  obtain ⟨K, hK, hs, h0, h1, hsym⟩ := b33_t_tb_comp_spec μ₀ μ
  exact b33_t_fMuSym_eq_of_conj hK hs h0 h1 hsym

/-- Clauses (1)/(6): `μ ∼ ν ↔ λ(μ) ∼ λ(ν)` (`(f^{μ₀})⁻¹` is a bijection of `ℝ`). -/
theorem b33_t_tb_equiv (μ₀ μ ν : BeltramiH) : teichSetoid μ ν ↔ teichSetoid (b33_t_tb μ₀ μ) (b33_t_tb μ₀ ν) := by
  have e1 := lemma33_1 μ ν
  have e2 := lemma33_1 (b33_t_tb μ₀ μ) (b33_t_tb μ₀ ν)
  change (∀ x : ℝ, normalizedSolution μ.1 x = normalizedSolution ν.1 x) ↔
    ∀ x : ℝ, normalizedSolution (b33_t_tb μ₀ μ).1 x = normalizedSolution (b33_t_tb μ₀ ν).1 x
  rw [← e1, ← e2]
  show (∀ x : ℝ, fMuSym μ.1 x = fMuSym ν.1 x) ↔
    ∀ x : ℝ, fMuSym (translatedBeltrami μ₀.1 μ.1) x = fMuSym (translatedBeltrami μ₀.1 ν.1) x
  rw [b33_t_tb_fMuSym, b33_t_tb_fMuSym, b33_t_forall_real_iff, b33_t_forall_real_iff]
  obtain ⟨-, -, hleft, -, hgsym⟩ := b33_t_fs_inv_spec μ₀
  obtain ⟨hR1, -, -⟩ := b33_t_fs_real μ₀
  constructor
  · intro h z hz
    refine h _ ?_
    have hc := hgsym z
    rw [Complex.conj_eq_iff_im.2 hz] at hc
    exact Complex.conj_eq_iff_im.1 hc.symm
  · intro h z hz
    have h' := h (fMuSym μ₀.1 z) (hR1 z hz)
    simp only [Function.comp_apply, hleft] at h'
    exact h'

/-- Clause (3) core: `λ(μ₀) = 0`. -/
theorem b33_t_tb_self (μ₀ : BeltramiH) : translatedBeltrami μ₀.1 μ₀.1 = 0 := by
  obtain ⟨-, -, -, hright, -⟩ := b33_t_fs_inv_spec μ₀
  have hid : fMuSym μ₀.1 ∘ Function.invFunOn (fMuSym μ₀.1) univ = id := funext hright
  funext z
  simp only [translatedBeltrami, hid, td_complexDilatation_id, Pi.zero_apply]
  by_cases hz : z ∈ upperHalf
  · rw [indicator_of_mem hz]
  · rw [indicator_of_notMem hz]

/-- `φ_0 = 0`. -/
theorem b33_t_bf_zero : bersFunction (0 : ℂ → ℂ) = 0 := by
  funext z
  have hS : schwarzian (normalizedSolution (0 : ℂ → ℂ)) = 0 := by
    rw [bB_l_normalizedSolution_zero]
    exact funext bB_l_schwarzian_id
  simp only [bersFunction, hS, Set.indicator_zero', Pi.zero_apply]

/-- The pull-back `1_ℍ μ_{f^ν ∘ f^{μ₀}}` (so that `λ` of it is equivalent to `ν`), as an element of `M`. -/
theorem b33_t_pb_comp_spec (μ₀ ν : BeltramiH) :
    ∃ K : ℝ, IsKQC (fMuSym ν.1 ∘ fMuSym μ₀.1) univ K ∧ (fMuSym ν.1 ∘ fMuSym μ₀.1) '' univ = univ ∧
      (fMuSym ν.1 ∘ fMuSym μ₀.1) 0 = 0 ∧ (fMuSym ν.1 ∘ fMuSym μ₀.1) 1 = 1 ∧
      (∀ z, (fMuSym ν.1 ∘ fMuSym μ₀.1) (conj z) = conj ((fMuSym ν.1 ∘ fMuSym μ₀.1) z)) ∧
      (fMuSym ν.1 ∘ fMuSym μ₀.1) '' upperHalf = upperHalf := by
  obtain ⟨K, hK, hs, h0, h1, hsym, hU, -⟩ := b33_t_fs_spec ν
  obtain ⟨K₀, hK₀, hs₀, h₀0, h₀1, hsym₀, hU₀, -⟩ := b33_t_fs_spec μ₀
  refine ⟨K₀ * K, thm7_1_comp hK₀ hK (subset_univ _), by rw [image_comp, hs₀, hs], by simp [h₀0, h0],
    by simp [h₀1, h1], fun z => by simp only [Function.comp_apply, hsym₀, hsym], by rw [image_comp, hU₀, hU]⟩

/-- `1_ℍ μ_{f^ν ∘ f^{μ₀}} ∈ M`. -/
def b33_t_pb (μ₀ ν : BeltramiH) : BeltramiH :=
  ⟨upperHalf.indicator (complexDilatation (fMuSym ν.1 ∘ fMuSym μ₀.1)),
    ut_rg_indicator_mem (b33_t_pb_comp_spec μ₀ ν).choose_spec.1⟩

/-- `f^{μ'} = f^ν ∘ f^{μ₀}` for the pull-back `μ' = 1_ℍ μ_{f^ν ∘ f^{μ₀}}`. -/
theorem b33_t_pb_fMuSym (μ₀ ν : BeltramiH) : fMuSym (b33_t_pb μ₀ ν).1 = fMuSym ν.1 ∘ fMuSym μ₀.1 := by
  obtain ⟨K, hK, hs, h0, h1, hsym, -⟩ := b33_t_pb_comp_spec μ₀ ν
  exact b33_t_fMuSym_eq_of_conj hK hs h0 h1 hsym

/-- `f^{λ(pb ν)} = f^ν`. -/
theorem b33_t_tb_pb_fMuSym (μ₀ ν : BeltramiH) :
    fMuSym (translatedBeltrami μ₀.1 (b33_t_pb μ₀ ν).1) = fMuSym ν.1 := by
  obtain ⟨-, -, -, hright, -⟩ := b33_t_fs_inv_spec μ₀
  rw [b33_t_tb_fMuSym, b33_t_pb_fMuSym]
  funext w
  simp only [Function.comp_apply, hright]

/-- Clause (7) core: `λ(pb ν) ∼ ν`. -/
theorem b33_t_tb_pb_equiv (μ₀ ν : BeltramiH) : teichSetoid (b33_t_tb μ₀ (b33_t_pb μ₀ ν)) ν :=
  (lemma33_1 (b33_t_tb μ₀ (b33_t_pb μ₀ ν)) ν).1 fun x => by
    show fMuSym (translatedBeltrami μ₀.1 (b33_t_pb μ₀ ν).1) x = fMuSym ν.1 x
    rw [b33_t_tb_pb_fMuSym]

/-! ### C2: the distance / continuity clause (4) -/

/-- The pseudo-hyperbolic invariance of `(a, b) ↦ |(a - b)/(1 - b̄a)|` under `x ↦ θ (x - c)/(1 - c̄x)`. -/
theorem b33_t_one_sub_ne {u v : ℂ} (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) : 1 - conj u * v ≠ 0 := by
  intro h
  have h1 : conj u * v = 1 := (sub_eq_zero.1 h).symm
  have h2 : ‖conj u * v‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg u, norm_nonneg v]
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

/-- The pseudo-hyperbolic quantity `|(a - b)/(1 - b̄a)|` is invariant under a disc automorphism `w ↦ θ (w - c)/(1 -
c̄w)`, `|θ| = 1`. -/
theorem b33_t_pseudo_inv {a b c θ : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hc : ‖c‖ < 1) (hθ : ‖θ‖ = 1) :
    ‖((a - c) / (1 - conj c * a) * θ - (b - c) / (1 - conj c * b) * θ) /
        (1 - conj ((b - c) / (1 - conj c * b) * θ) * ((a - c) / (1 - conj c * a) * θ))‖ =
      ‖(a - b) / (1 - conj b * a)‖ := by
  have hD1 : 1 - conj c * a ≠ 0 := b33_t_one_sub_ne hc ha
  have hD2 : 1 - conj c * b ≠ 0 := b33_t_one_sub_ne hc hb
  have hD2' : 1 - c * conj b ≠ 0 := by
    have h := (map_ne_zero (starRingEnd ℂ)).2 hD2
    rwa [map_sub, map_one, map_mul, Complex.conj_conj] at h
  have hD2c : 1 - conj b * c ≠ 0 := by rwa [mul_comm]
  have hE : 1 - conj b * a ≠ 0 := b33_t_one_sub_ne hb ha
  have hcc : 1 - conj c * c ≠ 0 := b33_t_one_sub_ne hc hc
  have hD1c : 1 - a * conj c ≠ 0 := by rwa [mul_comm]
  have hD2c' : 1 - b * conj c ≠ 0 := by rwa [mul_comm]
  have hEc : 1 - a * conj b ≠ 0 := by rwa [mul_comm]
  have hccc : 1 - c * conj c ≠ 0 := by rwa [mul_comm]
  have hD2'c : 1 - conj b * c ≠ 0 := hD2c
  have hθθ : conj θ * θ = 1 := by
    rw [Complex.conj_mul', hθ]
    norm_num
  set A := (a - c) / (1 - conj c * a) with hA
  set B := (b - c) / (1 - conj c * b) with hB
  have hcB : conj B = (conj b - conj c) / (1 - c * conj b) := by
    rw [hB, map_div₀, map_sub, map_sub, map_one, map_mul, Complex.conj_conj]
  have hden : 1 - conj (B * θ) * (A * θ) = 1 - conj B * A := by
    rw [map_mul]
    linear_combination (-(conj B * A)) * hθθ
  have hM : 1 - conj B * A = (1 - conj c * c) * (1 - conj b * a) / ((1 - c * conj b) * (1 - conj c * a)) := by
    rw [hcB, hA]
    field_simp
    ring
  have hMne : 1 - conj B * A ≠ 0 := by
    rw [hM]
    exact div_ne_zero (mul_ne_zero hcc hE) (mul_ne_zero hD2' hD1)
  have hN : A * θ - B * θ = θ * ((a - b) * (1 - conj c * c) / ((1 - conj c * a) * (1 - conj c * b))) := by
    rw [hA, hB]
    field_simp
    ring
  have hkey : (A * θ - B * θ) / (1 - conj (B * θ) * (A * θ)) =
      θ * ((a - b) / (1 - conj b * a)) * ((1 - c * conj b) / (1 - conj c * b)) := by
    rw [hden, hN, hM]
    field_simp
  rw [hkey, norm_mul, norm_mul, hθ, one_mul, norm_div (1 - c * conj b)]
  have hn : ‖1 - c * conj b‖ = ‖1 - conj c * b‖ := by
    rw [← Complex.norm_conj (1 - c * conj b), map_sub, map_one, map_mul, Complex.conj_conj, mul_comm]
  rw [hn, div_self (norm_ne_zero_iff.2 hD2), mul_one]

/-- **Right translation preserves `‖(μ - ν)/(1 - ν̄μ)‖_∞`**: at `w = f^{μ₀}(z)`, `λ(μ)(w) = θ A_{μ₀(z)}(μ(z))`
(`ahQ_comp_inv_dilatation`), and `ess sup` transports through `f^{μ₀}|ℍ` (`ut_e_essSup_image`). -/
theorem b33_t_dd_tb (μ₀ μ ν : BeltramiH) :
    UniversalTeichmuller.dilatationDiffNorm (translatedBeltrami μ₀.1 μ.1) (translatedBeltrami μ₀.1 ν.1) =
      UniversalTeichmuller.dilatationDiffNorm μ.1 ν.1 := by
  obtain ⟨K₀, hK₀, -, -, -, -, hU₀, hd₀⟩ := b33_t_fs_spec μ₀
  obtain ⟨Kμ, hKμ, -, -, -, -, -, hdμ⟩ := b33_t_fs_spec μ
  obtain ⟨Kν, hKν, -, -, -, -, -, hdν⟩ := b33_t_fs_spec ν
  obtain ⟨⟨k₀, -, hk₀1, -, hb₀⟩, -⟩ := μ₀.2
  obtain ⟨⟨kμ, -, hkμ1, -, hbμ⟩, -⟩ := μ.2
  obtain ⟨⟨kν, -, hkν1, -, hbν⟩, -⟩ := ν.2
  rw [Measure.restrict_univ] at hb₀ hbμ hbν
  have hK₀U : IsKQC (fMuSym μ₀.1) upperHalf K₀ := ac_t_isKQC_restrict hK₀ isOpen_upperHalf (subset_univ _)
  unfold UniversalTeichmuller.dilatationDiffNorm
  congr 1
  conv_lhs => rw [← hU₀]
  rw [UniversalTeichmuller.ut_e_essSup_image hK₀U]
  refine essSup_congr_ae ?_
  have hCμ := ahQ_comp_inv_dilatation hKμ hK₀
  have hCν := ahQ_comp_inv_dilatation hKν hK₀
  have hJ := thm9_6_cor2_jacobian_pos hK₀
  rw [Measure.restrict_univ] at hCμ hCν hJ
  filter_upwards [ae_restrict_of_ae hCμ, ae_restrict_of_ae hCν, ae_restrict_of_ae hJ, hd₀, hdμ, hdν,
    ae_restrict_of_ae hb₀, ae_restrict_of_ae hbμ, ae_restrict_of_ae hbν,
    ae_restrict_mem isOpen_upperHalf.measurableSet] with z h1 h2 hJz e0 eμ eν b0 bμ bν hz
  have hfz : fMuSym μ₀.1 z ∈ upperHalf := hU₀ ▸ mem_image_of_mem _ hz
  have hdz : dz (fMuSym μ₀.1) z ≠ 0 := by
    intro h0
    unfold jacobian at hJz
    rw [h0, norm_zero] at hJz
    nlinarith [norm_nonneg (dzbar (fMuSym μ₀.1) z)]
  have hθ : ‖dz (fMuSym μ₀.1) z / conj (dz (fMuSym μ₀.1) z)‖ = 1 := by
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hdz)]
  have hLmu : translatedBeltrami μ₀.1 μ.1 (fMuSym μ₀.1 z) =
      (μ.1 z - μ₀.1 z) / (1 - conj (μ₀.1 z) * μ.1 z) * (dz (fMuSym μ₀.1) z / conj (dz (fMuSym μ₀.1) z)) := by
    rw [translatedBeltrami, indicator_of_mem hfz, h1, eμ, e0]
  have hLnu : translatedBeltrami μ₀.1 ν.1 (fMuSym μ₀.1 z) =
      (ν.1 z - μ₀.1 z) / (1 - conj (μ₀.1 z) * ν.1 z) * (dz (fMuSym μ₀.1) z / conj (dz (fMuSym μ₀.1) z)) := by
    rw [translatedBeltrami, indicator_of_mem hfz, h2, eν, e0]
  have key := b33_t_pseudo_inv (bμ.trans_lt hkμ1) (bν.trans_lt hkν1) (b0.trans_lt hk₀1) hθ
  show ((‖(translatedBeltrami μ₀.1 μ.1 (fMuSym μ₀.1 z) - translatedBeltrami μ₀.1 ν.1 (fMuSym μ₀.1 z)) /
      (1 - conj (translatedBeltrami μ₀.1 ν.1 (fMuSym μ₀.1 z)) * translatedBeltrami μ₀.1 μ.1 (fMuSym μ₀.1 z))‖₊ :
        ℝ≥0∞)) = ‖(μ.1 z - ν.1 z) / (1 - conj (ν.1 z) * μ.1 z)‖₊
  rw [hLmu, hLnu]
  congr 1
  exact NNReal.eq (by rw [coe_nnnorm, coe_nnnorm]; exact key)

/-- Clause (4) core. -/
theorem b33_t_tb_cont (μ₀ μ : BeltramiH) : ∀ ε > 0, ∃ δ > 0, ∀ ν : BeltramiH,
    bersNormL (bersFunction ν.1 - bersFunction μ.1) < ENNReal.ofReal δ →
      bersNormL (bersFunction (translatedBeltrami μ₀.1 ν.1) - bersFunction (translatedBeltrami μ₀.1 μ.1)) <
        ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := thm21_2_inverse_continuous (Quotient.mk teichSetoid μ) (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun ν hν => ?_⟩
  have hd : UniversalTeichmuller.dist (Quotient.mk teichSetoid μ) (Quotient.mk teichSetoid ν) < ε / 3 := by
    refine hδε _ ?_
    rwa [aw_t_bersMapU_mk, aw_t_bersMapU_mk]
  obtain ⟨μ', ν', hμ', hν', hv⟩ := UniversalTeichmuller.ut_dist_lt (Quotient.mk teichSetoid μ)
    (Quotient.mk teichSetoid ν) (ε := ε / 3 - UniversalTeichmuller.dist (Quotient.mk teichSetoid μ)
      (Quotient.mk teichSetoid ν)) (by linarith)
  have hμμ' : teichSetoid (b33_t_tb μ₀ μ') (b33_t_tb μ₀ μ) := (b33_t_tb_equiv μ₀ μ' μ).1 (Quotient.exact hμ')
  have hνν' : teichSetoid (b33_t_tb μ₀ ν') (b33_t_tb μ₀ ν) := (b33_t_tb_equiv μ₀ ν' ν).1 (Quotient.exact hν')
  have e1 : bersFunction (translatedBeltrami μ₀.1 μ.1) = bersFunction (b33_t_tb μ₀ μ').1 :=
    (bersFunction_eq_of_equiv hμμ').symm
  have e2 : bersFunction (translatedBeltrami μ₀.1 ν.1) = bersFunction (b33_t_tb μ₀ ν').1 :=
    (bersFunction_eq_of_equiv hνν').symm
  rw [e1, e2]
  refine (eq21_10 (b33_t_tb μ₀ μ') (b33_t_tb μ₀ ν')).trans_lt ?_
  obtain ⟨hd1, hveq⟩ := UniversalTeichmuller.ut_v_eq μ' ν'
  have hd0 : 0 ≤ UniversalTeichmuller.dilatationDiffNorm μ'.1 ν'.1 := ENNReal.toReal_nonneg
  have hdd : UniversalTeichmuller.dilatationDiffNorm (b33_t_tb μ₀ ν').1 (b33_t_tb μ₀ μ').1 =
      UniversalTeichmuller.dilatationDiffNorm μ'.1 ν'.1 := by
    rw [UniversalTeichmuller.ut_d_symm]
    exact b33_t_dd_tb μ₀ μ' ν'
  rw [hdd]
  refine (ENNReal.ofReal_lt_ofReal_iff hε).2 ?_
  have := bB_le_log_quot hd0 hd1
  linarith

/-! ### C3: the automorphy clause (5) -/

/-- `ad - bc ≠ 0` for `γ ∈ SL(2, ℝ)`, as complex numbers. -/
theorem b33_t_det_ne (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ((γ 0 0 : ℝ) : ℂ) * (γ 1 1 : ℝ) - (γ 0 1 : ℝ) * (γ 1 0 : ℝ) ≠ 0 := by
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at h
  have h' : ((γ 0 0 : ℝ) : ℂ) * (γ 1 1 : ℝ) - (γ 0 1 : ℝ) * (γ 1 0 : ℝ) = 1 := by exact_mod_cast h
  rw [h']
  exact one_ne_zero

/-- `mobiusFn a b c d` is continuous off its pole. -/
theorem b33_t_mobius_continuousAt {a b c d z : ℂ} (hz : c * z + d ≠ 0) : ContinuousAt (mobiusFn a b c d) z := by
  unfold mobiusFn
  exact ((continuousAt_const.mul continuousAt_id).add continuousAt_const).div
    ((continuousAt_const.mul continuousAt_id).add continuousAt_const) hz

/-- **CR**: a conjugacy `f ∘ γ = γ' ∘ f` on `ℍ` (`f` a homeomorphism of `ℂ` with `f 0 = 0`) extends to every real
point, including the pole of `γ`, where both sides are Lean's `0` (`f(γ(pole)) = f 0 = 0`, and `f(pole)` is then the
pole of `γ'`: `tendsto_mobiusFn_pole`, `Homeomorph.map_cocompact`, `disjoint_nhds_cobounded`). -/
theorem b33_t_conj_real {f : ℂ → ℂ} (hf : Continuous f) (hfi : Function.Injective f)
    (hfc : Tendsto f (Bornology.cobounded ℂ) (Bornology.cobounded ℂ)) (h0 : f 0 = 0)
    {γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hrel : ∀ z ∈ upperHalf, f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
      mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (f z)) (x : ℝ) :
    f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) x) = mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (f x) := by
  set T := mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) with hT
  set T' := mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) with hT'
  set L := 𝓝[upperHalf] (x : ℂ) with hL
  have : L.NeBot := by
    rw [hL, ← mem_closure_iff_nhdsWithin_neBot]
    have hcl : closure upperHalf = {z : ℂ | 0 ≤ z.im} := closure_setOfPred_lt_im 0
    rw [hcl]
    show 0 ≤ (x : ℂ).im
    simp
  have hev : (f ∘ T) =ᶠ[L] (T' ∘ f) := eventually_nhdsWithin_of_forall fun z hz => hrel z hz
  have hfL : Tendsto f L (𝓝 (f x)) := (hf.tendsto _).mono_left nhdsWithin_le_nhds
  have hfL' : Tendsto f L (𝓝[≠] (f x)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hfL, eventually_nhdsWithin_of_forall fun z hz h => ?_⟩
    have h1 : z = x := hfi h
    have h2 : 0 < z.im := hz
    rw [h1, ofReal_im] at h2
    exact lt_irrefl 0 h2
  -- if `f ∘ T → y` along `L`, then `f x` is not the pole of `γ'` and `T' (f x) = y`
  have hA : ∀ y : ℂ, Tendsto (f ∘ T) L (𝓝 y) → T' (f x) = y := by
    intro y hy
    have hy' : Tendsto (T' ∘ f) L (𝓝 y) := hy.congr' hev
    by_cases hden : (γ' 1 0 : ℂ) * f x + γ' 1 1 = 0
    · exfalso
      have hinf : Tendsto (T' ∘ f) L (Bornology.cobounded ℂ) :=
        (tendsto_mobiusFn_pole (b33_t_det_ne γ') hden).comp hfL'
      exact hy'.not_tendsto (disjoint_nhds_cobounded y) hinf
    · exact tendsto_nhds_unique ((b33_t_mobius_continuousAt hden).tendsto.comp hfL) hy'
  by_cases hpole : (γ 1 0 : ℂ) * x + γ 1 1 = 0
  · -- the pole of `γ`: `T x = 0`, and `f x` must be the pole of `γ'`
    have hTx : T x = 0 := by
      show ((γ 0 0 : ℂ) * x + γ 0 1) / ((γ 1 0 : ℂ) * x + γ 1 1) = 0
      rw [hpole, div_zero]
    rw [hTx, h0]
    have hden : (γ' 1 0 : ℂ) * f x + γ' 1 1 = 0 := by
      by_contra hden
      have hinf : Tendsto (f ∘ T) L (Bornology.cobounded ℂ) := by
        have hLle : L ≤ 𝓝[≠] (x : ℂ) := nhdsWithin_mono _ fun z hz h => by
          have h2 : 0 < z.im := hz
          rw [h, ofReal_im] at h2
          exact lt_irrefl 0 h2
        exact hfc.comp ((tendsto_mobiusFn_pole (b33_t_det_ne γ) hpole).mono_left hLle)
      exact (((b33_t_mobius_continuousAt hden).tendsto.comp hfL).congr' hev.symm).not_tendsto
        (disjoint_nhds_cobounded _) hinf
    show 0 = ((γ' 0 0 : ℂ) * f x + γ' 0 1) / ((γ' 1 0 : ℂ) * f x + γ' 1 1)
    rw [hden, div_zero]
  · exact (hA _ ((hf.tendsto _).comp ((b33_t_mobius_continuousAt hpole).tendsto.mono_left
      nhdsWithin_le_nhds))).symm

/-- For a conjugate pair `(γ, γ')` (`f^{μ₀} γ = γ' f^{μ₀}` on `ℍ`): `f^{λ} γ' (f^{λ})⁻¹ = f^μ γ (f^μ)⁻¹` on `ℝ`. -/
theorem b33_t_conj_pair_real (μ₀ μ : BeltramiH) {γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hrel : ∀ z ∈ upperHalf, fMuSym μ₀.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
      mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (fMuSym μ₀.1 z)) (x : ℝ) :
    fMuSym (translatedBeltrami μ₀.1 μ.1) (mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1)
        (Function.invFunOn (fMuSym (translatedBeltrami μ₀.1 μ.1)) {z : ℂ | z.im = 0} x)) =
      fMuSym μ.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
        (Function.invFunOn (fMuSym μ.1) {z : ℂ | z.im = 0} x)) := by
  obtain ⟨K₀, hK₀, hs₀, h₀0, -, -, -, -⟩ := b33_t_fs_spec μ₀
  obtain ⟨-, -, hleft, -, -⟩ := b33_t_fs_inv_spec μ₀
  obtain ⟨hR₀, -, -⟩ := b33_t_fs_real μ₀
  obtain ⟨-, -, hRs⟩ := b33_t_fs_real μ
  obtain ⟨Kμ, hKμ, -⟩ := b33_t_fs_spec μ
  obtain ⟨e₀, he₀⟩ := t1_homeomorph hK₀ hs₀
  have hfc : Tendsto (fMuSym μ₀.1) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
    rw [← he₀, cobounded_eq_cocompact]
    exact e₀.map_cocompact.le
  have hCR := b33_t_conj_real (he₀ ▸ e₀.continuous) (he₀ ▸ e₀.injective) hfc h₀0 hrel
  -- `y` = the real preimage of `x` under `f^μ`; `f^{μ₀} y` is the real preimage under `f^λ`
  obtain ⟨y, hy, hyx⟩ := hRs (x : ℂ) (Complex.ofReal_im x)
  have hinjμ : Function.Injective (fMuSym μ.1) := injOn_univ.1 hKμ.2.2.1.2.1
  have hinjL : Function.Injective (fMuSym (translatedBeltrami μ₀.1 μ.1)) := by
    rw [b33_t_tb_fMuSym]
    obtain ⟨Kg, hg, -⟩ := b33_t_fs_inv_spec μ₀
    exact hinjμ.comp (injOn_univ.1 hg.2.2.1.2.1)
  have h1 : Function.invFunOn (fMuSym μ.1) {z : ℂ | z.im = 0} x = y := b33_t_invFunOn_real hinjμ hy hyx
  have h2 : Function.invFunOn (fMuSym (translatedBeltrami μ₀.1 μ.1)) {z : ℂ | z.im = 0} x = fMuSym μ₀.1 y := by
    refine b33_t_invFunOn_real hinjL (hR₀ y hy) ?_
    rw [b33_t_tb_fMuSym, Function.comp_apply, hleft, hyx]
  have hy' : ((y.re : ℝ) : ℂ) = y := Complex.ext rfl (by simp [hy])
  have h3 := hCR y.re
  rw [hy'] at h3
  rw [h1, h2, ← h3, b33_t_tb_fMuSym, Function.comp_apply, hleft]

/-- Clause (5) core (from Earle for `Γ` and for `Γμ₀`). -/
theorem b33_t_tb_auto_iff (μ₀ : BeltramiH) {Γμ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓμ₀ : (∀ γ ∈ Γ, ∃ γ' ∈ Γμ₀, ∀ z ∈ upperHalf,
      fMuSym μ₀.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (fMuSym μ₀.1 z)) ∧
      ∀ γ' ∈ Γμ₀, ∃ γ ∈ Γ, ∀ z ∈ upperHalf,
        fMuSym μ₀.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
          mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (fMuSym μ₀.1 z)) (μ : BeltramiH) :
    bersFunction μ.1 ∈ automorphicQD Γ ↔ bersFunction (translatedBeltrami μ₀.1 μ.1) ∈ automorphicQD Γμ₀ := by
  rw [b33_e_earle_group Γ μ, show translatedBeltrami μ₀.1 μ.1 = (b33_t_tb μ₀ μ).1 from rfl,
    b33_e_earle_group Γμ₀ (b33_t_tb μ₀ μ)]
  constructor
  · intro h γ' hγ'
    obtain ⟨γ, hγ, hrel⟩ := hΓμ₀.2 γ' hγ'
    obtain ⟨a, b, c, d, hdet, hM⟩ := h γ hγ
    exact ⟨a, b, c, d, hdet, fun x => (b33_t_conj_pair_real μ₀ μ hrel x).trans (hM x)⟩
  · intro h γ hγ
    obtain ⟨γ', hγ', hrel⟩ := hΓμ₀.1 γ hγ
    obtain ⟨a, b, c, d, hdet, hM⟩ := h γ' hγ'
    exact ⟨a, b, c, d, hdet, fun x => (b33_t_conj_pair_real μ₀ μ hrel x).symm.trans (hM x)⟩

/-! ### C4: `χ` and the assembly of (33.12) -/

open scoped Classical in
/-- `χ(φ) = φ_{λ(μ)}` for any `μ` with `φ_μ = φ` (and `0` off the range). -/
def b33_t_chi (μ₀ : BeltramiH) (φ : ℂ → ℂ) : ℂ → ℂ :=
  if h : ∃ μ : BeltramiH, bersFunction μ.1 = φ then bersFunction (translatedBeltrami μ₀.1 h.choose.1) else 0

/-- Clause (1). -/
theorem b33_t_tb_bf_congr (μ₀ μ ν : BeltramiH) (h : bersFunction μ.1 = bersFunction ν.1) :
    bersFunction (translatedBeltrami μ₀.1 μ.1) = bersFunction (translatedBeltrami μ₀.1 ν.1) :=
  (b33_t_bf_eq_iff (b33_t_tb μ₀ μ) (b33_t_tb μ₀ ν)).2 ((b33_t_tb_equiv μ₀ μ ν).1 ((b33_t_bf_eq_iff μ ν).1 h))

/-- Clause (2). -/
theorem b33_t_chi_spec (μ₀ μ : BeltramiH) :
    b33_t_chi μ₀ (bersFunction μ.1) = bersFunction (translatedBeltrami μ₀.1 μ.1) := by
  have h : ∃ ν : BeltramiH, bersFunction ν.1 = bersFunction μ.1 := ⟨μ, rfl⟩
  rw [b33_t_chi, dite_eq_left h]
  exact b33_t_tb_bf_congr μ₀ _ _ h.choose_spec

/-- §33.4 (the translation `χ` in the proof of Theorem 33.1): for `μ₀ ∈ M(G₀)` the map
`χ : φ_μ ↦ φ_λ`, `f^λ = f^μ ∘ (f^{μ₀})⁻¹`, is well defined and continuous on `Ψ(T)` (the universal
Teichmüller space), bijective with continuous inverse (of the same form, with `λ₀` the coefficient
of `(f^{μ₀})⁻¹`), and sends `φ_{μ₀}` to `0`.  (33.12): `f^λ γ̃ (f^λ)⁻¹ = f^μ γ (f^μ)⁻¹` for
`γ̃ = f^{μ₀} γ (f^{μ₀})⁻¹`, so by Lemma 33.4 `χ` maps `Q(G₀, 𝕃) ∩ Ψ(T)` onto `Q(G^{μ₀}, 𝕃) ∩ Ψ(T)`.
Here `G^{μ₀} = f^{μ₀} G₀ (f^{μ₀})⁻¹` exactly: every `γ ∈ G₀` has a conjugate in `Γμ₀` and every element of
`Γμ₀` is such a conjugate. -/
theorem eq33_12_translation (hΓ : IsFuchsian Γ) (μ₀ : BeltramiGamma Γ) {Γμ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓμ₀ : (∀ γ ∈ Γ, ∃ γ' ∈ Γμ₀, ∀ z ∈ upperHalf,
      fMuSym μ₀.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (fMuSym μ₀.1.1 z)) ∧
      ∀ γ' ∈ Γμ₀, ∃ γ ∈ Γ, ∀ z ∈ upperHalf,
        fMuSym μ₀.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
          mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (fMuSym μ₀.1.1 z)) :
    ∃ χ : (ℂ → ℂ) → (ℂ → ℂ),
      (∀ μ ν : BeltramiH, bersFunction μ.1 = bersFunction ν.1 →
        bersFunction (translatedBeltrami μ₀.1.1 μ.1) = bersFunction (translatedBeltrami μ₀.1.1 ν.1)) ∧
      (∀ μ : BeltramiH, χ (bersFunction μ.1) = bersFunction (translatedBeltrami μ₀.1.1 μ.1)) ∧
      χ (bersFunction μ₀.1.1) = 0 ∧
      (∀ μ : BeltramiH, ∀ ε > 0, ∃ δ > 0, ∀ ν : BeltramiH,
        bersNormL (bersFunction ν.1 - bersFunction μ.1) < ENNReal.ofReal δ →
          bersNormL (χ (bersFunction ν.1) - χ (bersFunction μ.1)) < ENNReal.ofReal ε) ∧
      (∀ μ : BeltramiH, bersFunction μ.1 ∈ automorphicQD Γ ↔ χ (bersFunction μ.1) ∈ automorphicQD Γμ₀) ∧
      InjOn χ (range fun μ : BeltramiH => bersFunction μ.1) ∧
      χ '' (range fun μ : BeltramiH => bersFunction μ.1) = range fun μ : BeltramiH => bersFunction μ.1 := by
  have _hΓ := hΓ
  refine ⟨b33_t_chi μ₀.1, b33_t_tb_bf_congr μ₀.1, b33_t_chi_spec μ₀.1, ?_, ?_, ?_, ?_, ?_⟩
  · -- (3)
    rw [b33_t_chi_spec μ₀.1 μ₀.1, b33_t_tb_self]
    exact b33_t_bf_zero
  · -- (4)
    intro μ ε hε
    obtain ⟨δ, hδ, h⟩ := b33_t_tb_cont μ₀.1 μ ε hε
    refine ⟨δ, hδ, fun ν hν => ?_⟩
    rw [b33_t_chi_spec, b33_t_chi_spec]
    exact h ν hν
  · -- (5)
    intro μ
    rw [b33_t_chi_spec]
    exact b33_t_tb_auto_iff μ₀.1 hΓμ₀ μ
  · -- (6)
    rintro _ ⟨μ, rfl⟩ _ ⟨ν, rfl⟩ h
    simp only at h ⊢
    rw [b33_t_chi_spec, b33_t_chi_spec] at h
    exact (b33_t_bf_eq_iff μ ν).2 ((b33_t_tb_equiv μ₀.1 μ ν).2
      ((b33_t_bf_eq_iff (b33_t_tb μ₀.1 μ) (b33_t_tb μ₀.1 ν)).1 h))
  · -- (7)
    ext φ
    constructor
    · rintro ⟨_, ⟨μ, rfl⟩, rfl⟩
      exact ⟨b33_t_tb μ₀.1 μ, (b33_t_chi_spec μ₀.1 μ).symm⟩
    · rintro ⟨ν, rfl⟩
      refine ⟨bersFunction (b33_t_pb μ₀.1 ν).1, ⟨_, rfl⟩, ?_⟩
      rw [b33_t_chi_spec]
      exact (b33_t_bf_eq_iff (b33_t_tb μ₀.1 (b33_t_pb μ₀.1 ν)) ν).2 (b33_t_tb_pb_equiv μ₀.1 ν)

/-! ### C5: Theorem 33.1 (Bers) -/

/-- **COMPAT**: if `H ∘ γ = A ∘ H` on `ℍ` (`γ, A ∈ SL(2, ℝ)`, `H` q.c. with `H(ℍ) ⊆ ℍ`), then `1_ℍ μ_H` satisfies the
`γ`-compatibility identity a.e. on `ℍ` (`bg2_d_dil_mobius` for `H ∘ γ`, `complexDilatation_comp_conformal_left` for
`A ∘ H`). -/
theorem b33_t_compat_of_conj {H : ℂ → ℂ} {K : ℝ} (hH : IsKQC H univ K) (hHU : ∀ z ∈ upperHalf, H z ∈ upperHalf)
    {γ A : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hrel : ∀ z ∈ upperHalf, H (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
      mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (H z)) :
    ∀ᵐ z ∂(volume.restrict upperHalf), upperHalf.indicator (complexDilatation H) z =
      upperHalf.indicator (complexDilatation H) ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) *
        (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 / conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2)) := by
  have hdetR : ∀ M : Matrix.SpecialLinearGroup (Fin 2) ℝ, M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := fun M => by
    have h := Matrix.SpecialLinearGroup.det_coe M
    rwa [Matrix.det_fin_two] at h
  have hdetC : ∀ M : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (M 0 0 : ℂ) * M 1 1 - M 0 1 * M 1 0 = 1 := fun M => by exact_mod_cast hdetR M
  have hdiff := thm9_3_differentiable_ae hH
  rw [Measure.restrict_univ] at hdiff
  filter_upwards [ae_restrict_of_ae hdiff, ae_restrict_mem isOpen_upperHalf.measurableSet] with z hdz hz
  have hz' : 0 < z.im := hz
  have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := bg2_d_den_ne_zero (hdetR γ) hz'.ne'
  have hγz : mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z ∈ upperHalf := by
    show 0 < (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z).im
    rw [mobiusFn_im_real, hdetR γ, one_mul]
    exact div_pos hz' (Complex.normSq_pos.2 hden)
  have hHz : 0 < (H z).im := hHU z hz
  have hdenA : (A 1 0 : ℂ) * H z + A 1 1 ≠ 0 := bg2_d_den_ne_zero (hdetR A) hHz.ne'
  have hA := bg2_d_deriv (hdetC A) hdenA
  have e1 := bg2_d_dil_mobius H (hdetC γ) hden
  have e2 : complexDilatation (H ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z =
      complexDilatation (mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) ∘ H) z :=
    bg_dilatation_congr isOpen_upperHalf (fun w hw => hrel w hw) hz
  have e3 : complexDilatation (mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) ∘ H) z = complexDilatation H z :=
    complexDilatation_comp_conformal_left hdz hA.differentiableAt
      (by rw [hA.deriv]; exact one_div_ne_zero (pow_ne_zero 2 hdenA))
  change upperHalf.indicator (complexDilatation H) z =
    upperHalf.indicator (complexDilatation H) (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) *
      (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 / conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2))
  rw [indicator_of_mem hz, indicator_of_mem hγz, ← e3, ← e2, e1]

/-- **PB**: for `λ' ∈ M(Γμ₀)`, the pull-back `μ' = 1_ℍ μ_{f^{λ'} ∘ f^{μ₀}}` is `Γ`-compatible:
`f^{μ'} ∘ γ = f^{λ'} ∘ γ' ∘ f^{μ₀} = A ∘ f^{μ'}` on `ℍ` (conjugate pair `(γ, γ')`, DEF for `λ'`). -/
theorem b33_t_pb_compat (μ₀ : BeltramiH) {Γμ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (lam : BeltramiH)
    (hΓμ₀ : ∀ γ ∈ Γ, ∃ γ' ∈ Γμ₀, ∀ z ∈ upperHalf,
      fMuSym μ₀.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (fMuSym μ₀.1 z))
    (hdef : ∀ γ' ∈ Γμ₀, ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ z ∈ upperHalf,
      fMuSym lam.1 (mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) z) =
        mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (fMuSym lam.1 z)) :
    IsGammaCompatible Γ (b33_t_pb μ₀ lam).1 := by
  intro γ hγ
  obtain ⟨γ', hγ', hrel₀⟩ := hΓμ₀ γ hγ
  obtain ⟨A, hA⟩ := hdef γ' hγ'
  obtain ⟨K, hK, -, -, -, -, hU⟩ := b33_t_pb_comp_spec μ₀ lam
  obtain ⟨-, -, -, -, -, -, hU₀, -⟩ := b33_t_fs_spec μ₀
  have hHU : ∀ z ∈ upperHalf, (fMuSym lam.1 ∘ fMuSym μ₀.1) z ∈ upperHalf := fun z hz =>
    hU ▸ mem_image_of_mem _ hz
  refine b33_t_compat_of_conj hK hHU (A := A) fun z hz => ?_
  have hz₀ : fMuSym μ₀.1 z ∈ upperHalf := hU₀ ▸ mem_image_of_mem _ hz
  simp only [Function.comp_apply]
  rw [hrel₀ z hz, hA _ hz₀]

/-- **Theorem 33.1 (Bers)**: `Ψ(T(S₀))` is a connected open subset of `Q(G₀, 𝕃)`.  (Every
`φ_{μ₀} ∈ Ψ(T(S₀))` is an interior point: the translation `χ` is a homeomorphism of
`Q(G₀, 𝕃) ∩ Ψ(T)` onto `Q(G^{μ₀}, 𝕃) ∩ Ψ(T)` sending `φ_{μ₀}` to `0`, which is interior by Lemma
33.3.) -/
theorem thm33_1_bers (hΓ : IsFuchsian Γ) :
    IsConnected (range (bersMapGamma Γ)) ∧
      ∀ p : TeichGamma Γ, ∃ ε > 0, ∀ φ ∈ automorphicQD Γ,
        bersNormL (φ - bersMapGamma Γ p) < ENNReal.ofReal ε → ∃ q : TeichGamma Γ, bersMapGamma Γ q = φ := by
  refine ⟨(bersImage_pathConnected hΓ).isConnected, fun p => ?_⟩
  set μ₀ : BeltramiGamma Γ := Quotient.out p with hμ₀
  have hp : bersMapGamma Γ p = bersFunction μ₀.1.1 := rfl
  obtain ⟨Γμ₀, hFμ₀, hΓμ₀1, hΓμ₀2⟩ := exists_deformation_group hΓ μ₀
  obtain ⟨χ, -, c2, c3, c4, c5, c6, -⟩ := eq33_12_translation hΓ μ₀ ⟨hΓμ₀1, hΓμ₀2⟩
  obtain ⟨ε₁, hε₁, hopen⟩ := thm21_3_open (Quotient.mk teichSetoid μ₀.1)
  obtain ⟨δ₂, hδ₂, hcont⟩ := c4 μ₀.1 (1 / 2) (by norm_num)
  refine ⟨min ε₁ δ₂, lt_min hε₁ hδ₂, fun φ hφ hlt => ?_⟩
  rw [hp] at hlt
  have hlt₁ : bersNormL (φ - bersFunction μ₀.1.1) < ENNReal.ofReal ε₁ :=
    hlt.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hlt₂ : bersNormL (φ - bersFunction μ₀.1.1) < ENNReal.ofReal δ₂ :=
    hlt.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  -- `φ ∈ A(𝕃)`
  have hφL : φ ∈ bersSpaceL := by
    refine ⟨hφ.1, ?_⟩
    have h := b33_t_bersNormL_add_le (φ - bersFunction μ₀.1.1) (bersFunction μ₀.1.1)
    rw [sub_add_cancel] at h
    exact h.trans_lt (ENNReal.add_lt_top.2 ⟨hlt₁.trans ENNReal.ofReal_lt_top, (bg2_bers_mem μ₀.1).1.2⟩)
  -- `φ = φ_ν` (Theorem 21.3)
  obtain ⟨q, hq⟩ := hopen φ hφL (by rwa [aw_t_bersMapU_mk])
  set ν : BeltramiH := Quotient.out q with hνdef
  have hν : bersFunction ν.1 = φ := by
    funext z
    by_cases hz : z ∈ lowerHalf
    · exact hq hz
    · rw [bersFunction, indicator_of_notMem hz, hφ.2.1 z hz]
  -- `χ φ ∈ Q(Γμ₀)` with `‖χ φ‖ < 1/2`
  have hsmall : bersNormL (χ φ) < ENNReal.ofReal (1 / 2) := by
    have h := hcont ν (by rw [hν]; exact hlt₂)
    rwa [c3, hν, sub_zero] at h
  have hauto : χ φ ∈ automorphicQD Γμ₀ := by
    have h := (c5 ν).1 (by rw [hν]; exact hφ)
    rwa [hν] at h
  -- Lemma 33.3 for `Γμ₀`
  obtain ⟨lam, -, hlam⟩ := (lemma33_3 hFμ₀).2 (χ φ) hauto hsmall
  rw [bg_bersMapGamma_eq rfl] at hlam
  -- the `Γ`-compatible pull-back `μ'`
  have hdef : ∀ γ' ∈ Γμ₀, ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ z ∈ upperHalf,
      fMuSym lam.1.1 (mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) z) =
        mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (fMuSym lam.1.1 z) := fun γ' hγ' => by
    obtain ⟨Γl, -, hc, -⟩ := exists_deformation_group hFμ₀ lam
    obtain ⟨A, -, hA⟩ := hc γ' hγ'
    exact ⟨A, hA⟩
  let μ' : BeltramiGamma Γ := ⟨b33_t_pb μ₀.1 lam.1, b33_t_pb_compat μ₀.1 lam.1 hΓμ₀1 hdef⟩
  refine ⟨Quotient.mk _ μ', ?_⟩
  rw [bg_bersMapGamma_eq rfl]
  have hχ : χ (bersFunction (b33_t_pb μ₀.1 lam.1).1) = χ φ := by
    rw [c2, ← hlam]
    exact (b33_t_bf_eq_iff (b33_t_tb μ₀.1 (b33_t_pb μ₀.1 lam.1)) lam.1).2 (b33_t_tb_pb_equiv μ₀.1 lam.1)
  exact c6 ⟨_, rfl⟩ ⟨ν, hν⟩ hχ

/-- §33.4: `Ψ` is injective (equivalent coefficients ⟺ equal `f_μ|𝕃`, Lemma 33.1), so `T(S₀)` is
homeomorphic to a bounded domain of `Q(G₀, 𝕃)`. -/
theorem bersMapGamma_injective (hΓ : IsFuchsian Γ) : Function.Injective (bersMapGamma Γ) := by
  have _hΓ := hΓ
  intro p q hpq
  have hS : ∀ z ∈ lowerHalf, schwarzian (normalizedSolution (Quotient.out p).1.1) z =
      schwarzian (normalizedSolution (Quotient.out q).1.1) z := by
    intro z hz
    have h := congrFun hpq z
    simp only [bersMapGamma, bersFunctionGamma, bersFunction, indicator_of_mem hz] at h
    exact h
  rw [← Quotient.out_eq p, ← Quotient.out_eq q]
  exact Quotient.sound ((lemma33_1 (Quotient.out p).1 (Quotient.out q).1).2 (bA_equiv_of_schwarzian_eq hS))

/-- Complex conjugation commutes with the Möbius map of a real matrix. -/
theorem s33dim_conj_mob (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℂ) :
    conj (utm_b_mob γ w) = utm_b_mob γ (conj w) := by
  simp [utm_b_mob, map_div₀, Complex.conj_ofReal]

/-- A real Möbius map sends `𝕃` to `𝕃`. -/
theorem s33dim_mob_lower (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z ∈ lowerHalf) :
    utm_b_mob γ z ∈ lowerHalf := by
  have hzim : 0 < (conj z).im := by
    rw [Complex.conj_im]
    exact neg_pos.2 hz
  have h := utm_b_mob_im_pos γ hzim
  rw [← s33dim_conj_mob, Complex.conj_im] at h
  show (utm_b_mob γ z).im < 0
  linarith

/-- The reflection `z ↦ conj (ψ (conj z))`, extended by `0`, of a holomorphic automorphic form on `ℍ`
is an element of `automorphicQD Γ`. -/
theorem s33dim_reflect_mem {ψ : ℂ → ℂ} (hd : DifferentiableOn ℂ ψ upperHalf)
    (hψ : ∀ γ ∈ Γ, ∀ z ∈ upperHalf, ψ (utm_b_mob γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = ψ z) :
    lowerHalf.indicator (fun w => conj (ψ (conj w))) ∈ automorphicQD Γ := by
  refine ⟨?_, fun z hz => indicator_of_notMem hz _, fun γ hγ z hz => ?_⟩
  · have hf : DifferentiableOn ℂ (fun w => conj (ψ (conj w))) lowerHalf := by
      intro w hw
      have hw' : conj w ∈ upperHalf := by
        show 0 < (conj w).im
        rw [Complex.conj_im]
        exact neg_pos.2 hw
      have h1 : DifferentiableAt ℂ ψ (conj w) := (hd _ hw').differentiableAt (isOpen_upperHalf.mem_nhds hw')
      have h2 := h1.conj_conj
      rw [Complex.conj_conj] at h2
      exact h2.differentiableWithinAt
    exact hf.congr (fun w hw => indicator_of_mem hw _)
  · have hz' : conj z ∈ upperHalf := by
      show 0 < (conj z).im
      rw [Complex.conj_im]
      exact neg_pos.2 hz
    have hγz := s33dim_mob_lower γ hz
    have h := hψ γ hγ (conj z) hz'
    have h2 := congrArg conj h
    rw [map_div₀, map_pow] at h2
    have hc : conj ((γ 1 0 : ℂ) * conj z + γ 1 1) = (γ 1 0 : ℂ) * z + γ 1 1 := by
      simp [Complex.conj_ofReal]
    rw [hc, ← s33dim_conj_mob] at h2
    show (lowerHalf.indicator (fun w => conj (ψ (conj w))) (utm_b_mob γ z)) /
      ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = lowerHalf.indicator (fun w => conj (ψ (conj w))) z
    rw [indicator_of_mem hγz, indicator_of_mem hz]
    simpa using h2

/-- The converse reflection of an element of `automorphicQD Γ` is a holomorphic automorphic form on `ℍ`. -/
theorem s33dim_unreflect {φ : ℂ → ℂ} (hφ : φ ∈ automorphicQD Γ) :
    DifferentiableOn ℂ (fun w => conj (φ (conj w))) upperHalf ∧
      ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
        conj (φ (conj (utm_b_mob γ z))) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = conj (φ (conj z)) := by
  have hlow : ∀ z ∈ upperHalf, conj z ∈ lowerHalf := fun z hz => by
    show (conj z).im < 0
    rw [Complex.conj_im]
    exact neg_lt_zero.2 hz
  refine ⟨?_, fun γ hγ z hz => ?_⟩
  · intro w hw
    have hw' := hlow w hw
    have h1 : DifferentiableAt ℂ φ (conj w) :=
      (hφ.1 _ hw').differentiableAt (isOpen_lowerHalf.mem_nhds hw')
    have h2 := h1.conj_conj
    rw [Complex.conj_conj] at h2
    exact h2.differentiableWithinAt
  · have h := hφ.2.2 γ hγ (conj z) (hlow z hz)
    have h2 := congrArg conj h
    rw [map_div₀, map_pow] at h2
    have hc : conj ((γ 1 0 : ℂ) * conj z + γ 1 1) = (γ 1 0 : ℂ) * z + γ 1 1 := by
      simp [Complex.conj_ofReal]
    rw [hc] at h2
    rw [s33dim_conj_mob]
    exact h2

/-- Reflection of the upper-half-plane lift gives a real-linear equivalence with the
lower-half-plane automorphic space. Its complex scalar law is conjugate-linear. -/
theorem s33dim_reflected_equiv
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    ∃ e : holQuadDiffSubmodule S ≃ₗ[ℝ] automorphicQD Γ,
      (∀ (q : holQuadDiffSubmodule S) (z : ℂ),
        (e q : ℂ → ℂ) z =
          lowerHalf.indicator (fun w => conj (utm_liftQD (q : S → ℂ → ℂ) p (conj w))) z) ∧
      (∀ (c : ℂ) (q : holQuadDiffSubmodule S), e (c • q) = conj c • e q) := by
  classical
  have hauto : ∀ q : holQuadDiffSubmodule S, lowerHalf.indicator
      (fun w => conj (utm_liftQD (q : S → ℂ → ℂ) p (conj w))) ∈ automorphicQD Γ := fun q =>
    s33dim_reflect_mem (utm_liftQD_differentiableOn q.2 hp) fun γ hγ z hz => by
      have h := utm_b_liftQD_automorphic (q : S → ℂ → ℂ) hp hγ hz
      generalize ((γ 1 0 : ℂ) * z + γ 1 1) = d at h ⊢
      rw [← h]
      ring
  have hconjc : ∀ (c : ℂ) (q : holQuadDiffSubmodule S),
      (⟨_, hauto (c • q)⟩ : automorphicQD Γ) = conj c • (⟨_, hauto q⟩ : automorphicQD Γ) := by
    intro c q
    apply Subtype.ext
    funext z
    show lowerHalf.indicator (fun w => conj (utm_liftQD ((c • q : holQuadDiffSubmodule S) : S → ℂ → ℂ) p (conj w))) z =
      conj c * lowerHalf.indicator (fun w => conj (utm_liftQD (q : S → ℂ → ℂ) p (conj w))) z
    by_cases hz : z ∈ lowerHalf
    · rw [indicator_of_mem hz, indicator_of_mem hz]
      show conj (utm_liftQD (c • (q : S → ℂ → ℂ)) p (conj z)) = _
      rw [utm_x_liftQD_smul, map_mul]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz, mul_zero]
  let L : holQuadDiffSubmodule S →ₗ[ℝ] automorphicQD Γ :=
    { toFun := fun q => ⟨_, hauto q⟩
      map_add' := fun q₁ q₂ => by
        apply Subtype.ext
        funext z
        show lowerHalf.indicator (fun w => conj (utm_liftQD (((q₁ + q₂ : holQuadDiffSubmodule S)) :
            S → ℂ → ℂ) p (conj w))) z =
          lowerHalf.indicator (fun w => conj (utm_liftQD (q₁ : S → ℂ → ℂ) p (conj w))) z +
            lowerHalf.indicator (fun w => conj (utm_liftQD (q₂ : S → ℂ → ℂ) p (conj w))) z
        by_cases hz : z ∈ lowerHalf
        · rw [indicator_of_mem hz, indicator_of_mem hz, indicator_of_mem hz]
          show conj (utm_liftQD ((q₁ : S → ℂ → ℂ) + (q₂ : S → ℂ → ℂ)) p (conj z)) = _
          rw [utm_x_liftQD_add, map_add]
        · rw [indicator_of_notMem hz, indicator_of_notMem hz, indicator_of_notMem hz, add_zero]
      map_smul' := fun r q => by
        apply Subtype.ext
        funext z
        have e1 : ((r • q : holQuadDiffSubmodule S) : S → ℂ → ℂ) = (r : ℂ) • (q : S → ℂ → ℂ) := by
          funext x y
          simp [Complex.real_smul]
        show lowerHalf.indicator (fun w => conj (utm_liftQD (((r • q : holQuadDiffSubmodule S)) :
            S → ℂ → ℂ) p (conj w))) z =
          r • lowerHalf.indicator (fun w => conj (utm_liftQD (q : S → ℂ → ℂ) p (conj w))) z
        rw [e1]
        by_cases hz : z ∈ lowerHalf
        · rw [indicator_of_mem hz, indicator_of_mem hz]
          show conj (utm_liftQD ((r : ℂ) • (q : S → ℂ → ℂ)) p (conj z)) = _
          rw [utm_x_liftQD_smul, map_mul, Complex.conj_ofReal, Complex.real_smul]
        · rw [indicator_of_notMem hz, indicator_of_notMem hz, smul_zero] }
  have hinj : Function.Injective L := by
    intro q₁ q₂ h
    have hd : L (q₁ - q₂) = 0 := by rw [map_sub, h, sub_self]
    by_contra hne
    have hne' : ((q₁ - q₂ : holQuadDiffSubmodule S) : S → ℂ → ℂ) ≠ 0 := fun h0 =>
      hne (sub_eq_zero.1 (Subtype.ext h0))
    obtain ⟨z, hz, hz0⟩ := utm_liftQD_ne (q₁ - q₂).2 hne' hp
    have hzl : conj z ∈ lowerHalf := by
      show (conj z).im < 0
      rw [Complex.conj_im]
      exact neg_lt_zero.2 hz
    have h1 := congrFun (congrArg Subtype.val hd) (conj z)
    have h2 : lowerHalf.indicator
        (fun w => conj (utm_liftQD (((q₁ - q₂ : holQuadDiffSubmodule S)) : S → ℂ → ℂ) p (conj w))) (conj z) = 0 := h1
    rw [indicator_of_mem hzl, Complex.conj_conj] at h2
    exact hz0 (by simpa using h2)
  have hsurj : Function.Surjective L := by
    intro φ
    obtain ⟨hd, hψ⟩ := s33dim_unreflect φ.2
    obtain ⟨q, hq, hql⟩ := utm_x_descent hp hd hψ
    refine ⟨⟨q, hq⟩, Subtype.ext (funext fun z => ?_)⟩
    show lowerHalf.indicator (fun w => conj (utm_liftQD q p (conj w))) z = (φ : ℂ → ℂ) z
    by_cases hz : z ∈ lowerHalf
    · rw [indicator_of_mem hz]
      have hzu : conj z ∈ upperHalf := by
        show 0 < (conj z).im
        rw [Complex.conj_im]
        exact neg_pos.2 hz
      rw [hql _ hzu]
      simp
    · rw [indicator_of_notMem hz]
      exact (φ.2.2.1 z hz).symm
  refine ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun q z => rfl, fun c q => ?_⟩
  exact hconjc c q

/-- The weighted value `|φ(z)| (Im z)²` of an automorphic quadratic differential is `Γ`-invariant on `𝕃`. -/
theorem s33dim_weighted_invariant (φ : automorphicQD Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : γ ∈ Γ) {z : ℂ} (hz : z ∈ lowerHalf) :
    ‖(φ : ℂ → ℂ) (utm_b_mob γ z)‖ * (utm_b_mob γ z).im ^ 2 = ‖(φ : ℂ → ℂ) z‖ * z.im ^ 2 := by
  have hden := bg2_a_den_ne γ hz
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have h := φ.2.2.2 γ hγ z hz
  have h1 : (φ : ℂ → ℂ) (utm_b_mob γ z) = (φ : ℂ → ℂ) z * ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 := by
    have h' : (φ : ℂ → ℂ) (utm_b_mob γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = (φ : ℂ → ℂ) z := h
    rwa [div_eq_iff (pow_ne_zero 4 hden)] at h'
  have him : (utm_b_mob γ z).im = z.im / Complex.normSq ((γ 1 0 : ℂ) * z + γ 1 1) :=
    utm_im_mobius hdet z
  have hd : 0 < ‖(γ 1 0 : ℂ) * z + γ 1 1‖ := norm_pos_iff.2 hden
  rw [h1, him, norm_mul, norm_pow, div_pow, Complex.normSq_eq_norm_sq]
  field_simp

/-- Compact uniformization makes the weighted supremum finite for every automorphic
quadratic differential, independently of whether it belongs to the Bers image. -/
theorem s33dim_weighted_finite
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S]
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    (φ : automorphicQD Γ) :
    bersNormL (φ : ℂ → ℂ) < ⊤ := by
  obtain ⟨K, hKc, hK⟩ := utm_exists_compact_translate hp
  set K' : Set ℂ := (fun w : UpperHalfPlane => conj (w : ℂ)) '' K with hK'
  have hK'c : IsCompact K' :=
    hKc.image (Complex.continuous_conj.comp UpperHalfPlane.continuous_coe)
  have hK'sub : K' ⊆ lowerHalf := by
    rintro _ ⟨w, -, rfl⟩
    show (conj (w : ℂ)).im < 0
    rw [Complex.conj_im]
    have := w.im_pos
    have h2 : (w : ℂ).im = w.im := rfl
    linarith
  have hcont : ContinuousOn (fun z : ℂ => ‖(φ : ℂ → ℂ) z‖ * z.im ^ 2) K' :=
    ((φ.2.1.continuousOn.mono hK'sub).norm).mul (Complex.continuous_im.pow 2).continuousOn
  obtain ⟨C, hC⟩ := hK'c.exists_bound_of_continuousOn hcont
  refine lt_of_le_of_lt (b := ENNReal.ofReal C) (iSup₂_le fun z hz => ?_) ENNReal.ofReal_lt_top
  have hzim : 0 < (conj z).im := by
    rw [Complex.conj_im]
    exact neg_pos.2 hz
  obtain ⟨γ, hγ, hγK⟩ := hK ⟨conj z, hzim⟩
  have hz' : utm_b_mob γ z ∈ K' := by
    refine ⟨γ • (⟨conj z, hzim⟩ : UpperHalfPlane), hγK, ?_⟩
    show conj (((γ • (⟨conj z, hzim⟩ : UpperHalfPlane) : UpperHalfPlane)) : ℂ) = utm_b_mob γ z
    rw [← utm_b_mob_smul γ hzim]
    simp [utm_b_mob]
  rw [← s33dim_weighted_invariant φ hγ hz]
  refine ENNReal.ofReal_le_ofReal ?_
  have := hC _ hz'
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

/-- The weighted supremum is definite on automorphic functions, including their
prescribed zero extension off the lower half-plane. -/
theorem s33dim_weighted_eq_zero_iff (φ : automorphicQD Γ) :
    bersNormL (φ : ℂ → ℂ) = 0 ↔ φ = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    funext z
    show (φ : ℂ → ℂ) z = 0
    by_cases hz : z ∈ lowerHalf
    · have h1 : ENNReal.ofReal (‖(φ : ℂ → ℂ) z‖ * z.im ^ 2) ≤ bersNormL (φ : ℂ → ℂ) :=
        le_iSup₂ (f := fun z (_ : z ∈ lowerHalf) => ENNReal.ofReal (‖(φ : ℂ → ℂ) z‖ * z.im ^ 2)) z hz
      rw [h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
      have him : 0 < z.im ^ 2 := by
        have : z.im < 0 := hz
        nlinarith
      have h2 : ‖(φ : ℂ → ℂ) z‖ ≤ 0 := by
        by_contra hcon
        rw [not_le] at hcon
        nlinarith
      exact norm_le_zero_iff.1 h2
    · exact φ.2.2.1 z hz
  · intro h
    rw [h]
    simp [bersNormL]

/-- `bersNormL` is homogeneous: `‖c φ‖ = |c| ‖φ‖`. -/
theorem s33dim_bers_smul (c : ℂ) (φ : ℂ → ℂ) :
    bersNormL (c • φ) = ENNReal.ofReal ‖c‖ * bersNormL φ := by
  unfold bersNormL
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun z => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun hz => ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg c)]
  congr 1
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

/-- Two norms on a finite-dimensional complex space are equivalent: a definite seminorm `N` is bounded
above and below by a positive multiple of the coordinate norm. -/
theorem s33dim_seminorm_equiv {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (N : Seminorm ℂ V) (hN : ∀ v, N v = 0 → v = 0) {n : ℕ} (e : V ≃ₗ[ℂ] (Fin n → ℂ)) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ v, a * ‖e v‖ ≤ N v ∧ N v ≤ b * ‖e v‖ := by
  letI : SeminormedAddCommGroup V := AddGroupSeminorm.toSeminormedAddCommGroup N.toAddGroupSeminorm
  letI : NormedAddCommGroup V := NormedAddCommGroup.ofSeparation (fun v hv => hN v hv)
  letI : NormedSpace ℂ V := ⟨fun c v => (N.smul' c v).le⟩
  let T : V ≃L[ℂ] (Fin n → ℂ) := e.toContinuousLinearEquiv
  refine ⟨(‖(T : V →L[ℂ] (Fin n → ℂ))‖ + 1)⁻¹, ‖(T.symm : (Fin n → ℂ) →L[ℂ] V)‖ + 1, by positivity,
    by positivity, fun v => ⟨?_, ?_⟩⟩
  · have h1 : ‖T v‖ ≤ ‖(T : V →L[ℂ] (Fin n → ℂ))‖ * ‖v‖ := (T : V →L[ℂ] (Fin n → ℂ)).le_opNorm v
    have h2 : (‖(T : V →L[ℂ] (Fin n → ℂ))‖ + 1)⁻¹ * ‖e v‖ ≤ ‖v‖ := by
      rw [inv_mul_le_iff₀ (by positivity)]
      have : ‖e v‖ = ‖T v‖ := rfl
      rw [this]
      nlinarith [norm_nonneg v, norm_nonneg (T : V →L[ℂ] (Fin n → ℂ))]
    exact h2
  · have h1 : ‖v‖ ≤ ‖(T.symm : (Fin n → ℂ) →L[ℂ] V)‖ * ‖T v‖ := by
      have := (T.symm : (Fin n → ℂ) →L[ℂ] V).le_opNorm (T v)
      simpa using this
    have : ‖e v‖ = ‖T v‖ := rfl
    rw [this]
    have h0 : ‖v‖ = N v := rfl
    rw [← h0]
    nlinarith [norm_nonneg (T v), norm_nonneg (T.symm : (Fin n → ℂ) →L[ℂ] V)]

/-- In positive finite coordinates, the finite weighted supremum has positive
two-sided bounds. Only the coordinate space carries a norm in this statement. -/
theorem s33dim_coordinate_comparison {n : ℕ} (hn : 0 < n)
    (e : automorphicQD Γ ≃L[ℂ] (Fin n → ℂ))
    (hfinite : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      (∀ φ : automorphicQD Γ,
        ENNReal.ofReal (a * ‖e φ‖) ≤ bersNormL (φ : ℂ → ℂ) ∧
          bersNormL (φ : ℂ → ℂ) ≤ ENNReal.ofReal (b * ‖e φ‖)) := by
  classical
  have hfd : FiniteDimensional ℂ (automorphicQD Γ) := e.toLinearEquiv.symm.finiteDimensional
  let N : Seminorm ℂ (automorphicQD Γ) :=
    Seminorm.of (fun φ => (bersNormL (φ : ℂ → ℂ)).toReal)
      (fun φ ψ => by
        have h1 := s21g_bersNormL_add_le (φ : ℂ → ℂ) (ψ : ℂ → ℂ)
        calc (bersNormL (((φ + ψ : automorphicQD Γ)) : ℂ → ℂ)).toReal
            ≤ (bersNormL (φ : ℂ → ℂ) + bersNormL (ψ : ℂ → ℂ)).toReal :=
              ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨(hfinite φ).ne, (hfinite ψ).ne⟩) h1
          _ = _ := ENNReal.toReal_add (hfinite φ).ne (hfinite ψ).ne)
      (fun c φ => by
        have h1 : ((c • φ : automorphicQD Γ) : ℂ → ℂ) = c • (φ : ℂ → ℂ) := rfl
        show (bersNormL ((c • φ : automorphicQD Γ) : ℂ → ℂ)).toReal = ‖c‖ * (bersNormL (φ : ℂ → ℂ)).toReal
        rw [h1, s33dim_bers_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg c)])
  have hN : ∀ φ, N φ = 0 → φ = 0 := fun φ h => by
    refine (s33dim_weighted_eq_zero_iff φ).1 ?_
    have h' : (bersNormL (φ : ℂ → ℂ)).toReal = 0 := h
    rcases (ENNReal.toReal_eq_zero_iff _).1 h' with h0 | h0
    · exact h0
    · exact absurd h0 (hfinite φ).ne
  obtain ⟨a, b, ha, hb, hab⟩ := s33dim_seminorm_equiv N hN e.toLinearEquiv
  refine ⟨a, b, ha, hb, fun φ => ⟨?_, ?_⟩⟩
  · have h1 := (hab φ).1
    have h2 : a * ‖e φ‖ ≤ (bersNormL (φ : ℂ → ℂ)).toReal := h1
    exact (ENNReal.ofReal_le_iff_le_toReal (hfinite φ).ne).2 h2
  · have h1 := (hab φ).2
    have h2 : (bersNormL (φ : ℂ → ℂ)).toReal ≤ b * ‖e φ‖ := h1
    exact (ENNReal.le_ofReal_iff_toReal_le (hfinite φ).ne (by positivity)).2 h2

/-- The positive lower comparison and the sharp Bers bound make the coordinate
image bounded. The subtype membership proof is supplied by `bersMapGamma_mem`. -/
theorem s33dim_coords_bounded {n : ℕ} (hΓ : IsFuchsian Γ)
    (e : automorphicQD Γ ≃L[ℂ] (Fin n → ℂ)) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ φ : automorphicQD Γ,
      ENNReal.ofReal (a * ‖e φ‖) ≤ bersNormL (φ : ℂ → ℂ)) :
    Bornology.IsBounded (range (fun t : TeichGamma Γ =>
      e (⟨bersMapGamma Γ t, (bersMapGamma_mem hΓ t).1⟩ : automorphicQD Γ))) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨3 / (2 * a), ?_⟩
  rintro _ ⟨t, rfl⟩
  have h1 := (bersMapGamma_mem hΓ t).2.1
  have h2 := hlower ⟨bersMapGamma Γ t, (bersMapGamma_mem hΓ t).1⟩
  have h3 : ENNReal.ofReal (a * ‖e ⟨bersMapGamma Γ t, (bersMapGamma_mem hΓ t).1⟩‖) <
      ENNReal.ofReal (3 / 2) := lt_of_le_of_lt h2 h1
  rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)] at h3
  show ‖e ⟨bersMapGamma Γ t, (bersMapGamma_mem hΓ t).1⟩‖ ≤ 3 / (2 * a)
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- The positive upper comparison turns the relative weighted balls in Theorem
33.1 into open coordinate balls. -/
theorem s33dim_coords_open {n : ℕ} (hΓ : IsFuchsian Γ)
    (e : automorphicQD Γ ≃L[ℂ] (Fin n → ℂ)) {b : ℝ} (hb : 0 < b)
    (hupper : ∀ φ : automorphicQD Γ,
      bersNormL (φ : ℂ → ℂ) ≤ ENNReal.ofReal (b * ‖e φ‖)) :
    IsOpen (range (fun t : TeichGamma Γ =>
      e (⟨bersMapGamma Γ t, (bersMapGamma_mem hΓ t).1⟩ : automorphicQD Γ))) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨t, rfl⟩
  obtain ⟨ε, hε, hball⟩ := (thm33_1_bers hΓ).2 t
  rw [Metric.mem_nhds_iff]
  refine ⟨ε / b, by positivity, fun y hy => ?_⟩
  set φt : automorphicQD Γ := ⟨bersMapGamma Γ t, (bersMapGamma_mem hΓ t).1⟩ with hφt
  set φ : automorphicQD Γ := e.symm y with hφ
  have hdist : ‖e (φ - φt)‖ < ε / b := by
    rw [map_sub, hφ, ContinuousLinearEquiv.apply_symm_apply]
    simpa [dist_eq_norm] using hy
  have h1 := hupper (φ - φt)
  have h2 : bersNormL ((φ - φt : automorphicQD Γ) : ℂ → ℂ) < ENNReal.ofReal ε := by
    refine lt_of_le_of_lt h1 ((ENNReal.ofReal_lt_ofReal_iff hε).2 ?_)
    rw [lt_div_iff₀ hb] at hdist
    linarith
  obtain ⟨q, hq⟩ := hball (φ : ℂ → ℂ) φ.2 (by simpa [φt] using h2)
  refine ⟨q, ?_⟩
  have h3 : (⟨bersMapGamma Γ q, (bersMapGamma_mem hΓ q).1⟩ : automorphicQD Γ) = φ := Subtype.ext hq
  show e ⟨bersMapGamma Γ q, (bersMapGamma_mem hΓ q).1⟩ = y
  rw [h3, hφ]
  exact e.apply_symm_apply y

/-- The connected raw Bers image remains connected in its automorphic subtype
and under any continuous linear coordinate equivalence. -/
theorem s33dim_coords_connected {n : ℕ} (hΓ : IsFuchsian Γ)
    (e : automorphicQD Γ ≃L[ℂ] (Fin n → ℂ)) :
    IsConnected (range (fun t : TeichGamma Γ =>
      e (⟨bersMapGamma Γ t, (bersMapGamma_mem hΓ t).1⟩ : automorphicQD Γ))) := by
  have hA := (thm33_1_bers hΓ).1
  set A' : Set (automorphicQD Γ) := Subtype.val ⁻¹' range (bersMapGamma Γ) with hA'def
  have himg : (Subtype.val : automorphicQD Γ → ℂ → ℂ) '' A' = range (bersMapGamma Γ) := by
    ext f
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact hφ
    · rintro ⟨t, rfl⟩
      exact ⟨⟨_, (bersMapGamma_mem hΓ t).1⟩, ⟨t, rfl⟩, rfl⟩
  have hA' : IsConnected A' := by
    refine ⟨?_, ?_⟩
    · obtain ⟨f, t, rfl⟩ := hA.nonempty
      exact ⟨⟨_, (bersMapGamma_mem hΓ t).1⟩, ⟨t, rfl⟩⟩
    · refine (Topology.IsInducing.subtypeVal.isPreconnected_image).1 ?_
      convert hA.isPreconnected using 1
  have h := hA'.image e e.continuous.continuousOn
  convert h using 1
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨_, (bersMapGamma_mem hΓ t).1⟩, ⟨t, rfl⟩, rfl⟩
  · rintro ⟨φ, ⟨t, ht⟩, rfl⟩
    refine ⟨t, ?_⟩
    have : (⟨bersMapGamma Γ t, (bersMapGamma_mem hΓ t).1⟩ : automorphicQD Γ) = φ := Subtype.ext ht
    show e ⟨bersMapGamma Γ t, (bersMapGamma_mem hΓ t).1⟩ = e φ
    rw [this]

/-- §33.4: `Q(G₀, 𝕃)` is the space of lifts of the holomorphic quadratic differentials of the
compact surface `𝕃/G₀`, hence a complex vector space of dimension `3g - 3`; choosing a basis
`φ₁, …, φ_{3g-3}`, `φ_μ = t₁φ₁ + ⋯ + t_{3g-3}φ_{3g-3}` gives complex coordinates `(t₁, …, t_{3g-3})`
on `T(S₀)`, which becomes a bounded domain of `ℂ^{3g-3}`. -/
theorem thm33_dimension {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    Module.finrank ℂ (automorphicQD Γ) = 3 * g - 3 ∧
      ∃ coords : TeichGamma Γ → Fin (3 * g - 3) → ℂ, Function.Injective coords ∧
        Bornology.IsBounded (range coords) ∧ IsOpen (range coords) ∧ IsConnected (range coords) := by
  classical
  -- The frozen freeness hypothesis is redundant once this uniformization is supplied.
  have _hfree := hfree
  letI : CompactSpace S := hS.1
  letI : FiniteDimensional ℂ (holQuadDiffSubmodule S) := k22q_finite_quadratic (S := S)
  obtain ⟨r, -, -⟩ := s33dim_reflected_equiv hp
  letI : FiniteDimensional ℝ (automorphicQD Γ) := r.finiteDimensional
  letI : FiniteDimensional ℂ (automorphicQD Γ) :=
    Module.Finite.of_restrictScalars_finite ℝ ℂ (automorphicQD Γ)
  have hdim : Module.finrank ℂ (automorphicQD Γ) = 3 * g - 3 := by
    have hrank := r.finrank_eq
    simp only [finrank_real_of_complex] at hrank
    rw [thm22_5_dim_quadratic_differentials hg hS] at hrank
    omega
  have hn : 0 < 3 * g - 3 := by omega
  have hdimcoords : Module.finrank ℂ (automorphicQD Γ) =
      Module.finrank ℂ (Fin (3 * g - 3) → ℂ) := by
    simpa only [Module.finrank_fin_fun] using hdim
  obtain ⟨e⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hdimcoords
  obtain ⟨a, b, ha, hb, hcompare⟩ :=
    s33dim_coordinate_comparison hn e (s33dim_weighted_finite hp)
  let coords : TeichGamma Γ → Fin (3 * g - 3) → ℂ := fun t =>
    e (⟨bersMapGamma Γ t, (bersMapGamma_mem hΓ t).1⟩ : automorphicQD Γ)
  refine ⟨hdim, coords, ?_, ?_, ?_, ?_⟩
  · intro t u htu
    apply bersMapGamma_injective hΓ
    have heq : (⟨bersMapGamma Γ t, (bersMapGamma_mem hΓ t).1⟩ : automorphicQD Γ) =
        (⟨bersMapGamma Γ u, (bersMapGamma_mem hΓ u).1⟩ : automorphicQD Γ) := e.injective htu
    exact congrArg (fun φ : automorphicQD Γ => (φ : ℂ → ℂ)) heq
  · exact s33dim_coords_bounded hΓ e ha (fun φ => (hcompare φ).1)
  · exact s33dim_coords_open hΓ e hb (fun φ => (hcompare φ).2)
  · exact s33dim_coords_connected hΓ e

/-- §33.4 (complex structure, used in §34): `Ψ` is holomorphic in the Beltrami coefficient: for a
holomorphic family `t ↦ μ_t` of `G₀`-compatible coefficients, `t ↦ φ_{μ_t}(z)` is holomorphic for
every `z ∈ 𝕃`. -/
theorem bers_holomorphic_dependence (hΓ : IsFuchsian Γ) {P : Set ℂ} (hP : IsOpen P)
    {μ : ℂ → BeltramiGamma Γ} (hhol : ∀ z, DifferentiableOn ℂ (fun t => (μ t).1.1 z) P)
    {k : ℝ} (hk : k < 1) (hbound : ∀ t ∈ P, ∀ z, ‖(μ t).1.1 z‖ ≤ k) :
    ∀ z ∈ lowerHalf, DifferentiableOn ℂ (fun t => bersFunctionGamma (μ t) z) P := by
  have _hΓ := hΓ
  intro z hz t₀ ht₀
  have hk₀ : 0 ≤ k := (norm_nonneg _).trans (hbound t₀ ht₀ 0)
  have hkP : ∀ t ∈ P, IsBeltramiCoeff (μ t).1.1 univ k := by
    intro t ht
    obtain ⟨_, -, -, hm, -⟩ := (μ t).1.2.1
    exact ⟨hm, Eventually.of_forall fun w => hbound t ht w⟩
  have hconf := fun t => ut_conformal_lowerHalf (μ t).1
  have ha : ∀ w ∈ lowerHalf, DifferentiableOn ℂ (fun t => normalizedSolution (μ t).1.1 w) P :=
    fun w _ => thm13_8_ahlfors_bers_holomorphic (μ := fun t => (μ t).1.1)
      (f := fun t => normalizedSolution (μ t).1.1) hP hk₀ hk hkP hhol (fun t _ => ut_spec (μ t).1) w
  obtain ⟨hd1, hd2, hd3⟩ := bB_h0_deriv123_holo (F := fun t => normalizedSolution (μ t).1.1) isOpen_lowerHalf ha
    (fun t _ => (hconf t).1) (bB_hs_bound (ν := fun t => (μ t).1) hP hk₀ hk hkP) z hz
  have hne : ∀ t, deriv (normalizedSolution (μ t).1.1) z ≠ 0 := fun t =>
    deriv_ne_zero_of_injOn isOpen_lowerHalf (hconf t).1 (hconf t).2.1 hz
  have hS : DifferentiableOn ℂ (fun t => bersFunctionGamma (μ t) z) P := by
    refine ((((hd3.mul hd1).sub (hd2.mul hd2)).div (hd1.pow 2) fun t _ => pow_ne_zero 2 (hne t)).sub
      (((hd2.div hd1 fun t _ => hne t).pow 2).const_mul (1 / 2))).congr fun t _ => ?_
    rw [bersFunctionGamma, bersFunction, indicator_of_mem hz]
    exact bB_hs_schwarzian_eq ((hconf t).1.analyticAt (isOpen_lowerHalf.mem_nhds hz)) (hne t)
  exact hS t₀ ht₀

end LiZhongQC
