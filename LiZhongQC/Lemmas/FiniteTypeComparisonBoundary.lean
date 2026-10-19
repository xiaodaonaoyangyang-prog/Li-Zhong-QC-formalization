import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
import LiZhongQC.Lemmas.UniformizedUniqueness
import LiZhongQC.Ch08.S29_TeichmullerMetric
import LiZhongQC.Lemmas.UniformizedTeichmuller
import LiZhongQC.Lemmas.FiniteTypeCover
import LiZhongQC.Lemmas.FiniteTypeComparisonZero
import LiZhongQC.Lemmas.SchottkyCollarFromDouble
import LiZhongQC.Lemmas.QDDimension
import LiZhongQC.Lemmas.QDDecompConjTransport
import LiZhongQC.Lemmas.FiniteTypePunctRefl
import LiZhongQC.Lemmas.S32wFoldPush
import LiZhongQC.Lemmas.S32wSymmExtPunctured
import LiZhongQC.Lemmas.S32wSymmetricExtension
import LiZhongQC.Lemmas.S32wDTPlanar

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u



theorem s82cmp_null_cover {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [SecondCountableTopology X] {B : Set X} (W : X → Set X) (hWo : ∀ p, IsOpen (W p)) (hWp : ∀ p, p ∈ W p)
    (hWs : ∀ p, W p ⊆ (chartAt ℂ p).source) (hB : ∀ p, volume (chartAt ℂ p '' (B ∩ W p)) = 0) (x : X) :
    volume (chartAt ℂ x '' (B ∩ (chartAt ℂ x).source)) = 0 := by
  obtain ⟨t, htc, ht⟩ := (isLindelof_univ (X := X)).elim_countable_subcover W hWo (fun p _ => mem_iUnion.2 ⟨p, hWp p⟩)
  have hsub : chartAt ℂ x '' (B ∩ (chartAt ℂ x).source) ⊆
      ⋃ p ∈ t, chartAt ℂ x '' (B ∩ W p ∩ (chartAt ℂ x).source) := by
    rintro _ ⟨q, ⟨hqB, hqs⟩, rfl⟩
    have := ht (mem_univ q)
    simp only [mem_iUnion] at this
    obtain ⟨p, hpt, hqp⟩ := this
    exact mem_biUnion hpt ⟨q, ⟨⟨hqB, hqp⟩, hqs⟩, rfl⟩
  refine measure_mono_null hsub ?_
  refine (measure_biUnion_null_iff htc).2 fun p _ => ?_
  set A : Set ℂ := chartAt ℂ p '' (B ∩ W p ∩ (chartAt ℂ x).source) with hAdef
  have hA0 : volume A = 0 :=
    measure_mono_null (image_mono (f := chartAt ℂ p)
      (show B ∩ W p ∩ (chartAt ℂ x).source ⊆ B ∩ W p from fun q hq => ⟨hq.1.1, hq.1.2⟩)) (hB p)
  have himg : chartAt ℂ x '' (B ∩ W p ∩ (chartAt ℂ x).source) = chartTransition x p '' A := by
    ext w
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨chartAt ℂ p q, ⟨q, hq, rfl⟩, ?_⟩
      simp only [chartTransition]
      rw [(chartAt ℂ p).left_inv (hWs p hq.1.2)]
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨q, hq, ?_⟩
      simp only [chartTransition]
      rw [(chartAt ℂ p).left_inv (hWs p hq.1.2)]
  rw [himg]
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ hA0
  rintro _ ⟨q, hq, rfl⟩
  have hz : chartAt ℂ p q ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (hWs p hq.1.2)
  have hzx : (chartAt ℂ p).symm (chartAt ℂ p q) ∈ (chartAt ℂ x).source := by
    rw [(chartAt ℂ p).left_inv (hWs p hq.1.2)]
    exact hq.2
  exact ((s23_transition_differentiableAt x p hz hzx).restrictScalars ℝ).differentiableWithinAt



/-- **The fixed set of an anticonformal involution is a null set in every chart** (it is locally a real line
in the fixed-point charts). -/
theorem s82cmp_fixed_null {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [T2Space X] [SecondCountableTopology X] {J : X ≃ₜ X} (hJ : IsAnticonformalInvolution J) (x : X) :
    volume (chartAt ℂ x '' ({p | J p = p} ∩ (chartAt ℂ x).source)) = 0 := by
  classical
  set Z : Set X := {p | J p = p} with hZ
  have hZc : IsClosed Z := isClosed_eq J.continuous continuous_id
  have hfix : ∀ p, J p = p → ∃ (wc : OpenPartialHomeomorph X ℂ) (r : ℝ), p ∈ wc.source ∧
      wc.target = ball 0 r ∧ wc.source ⊆ (chartAt ℂ p).source ∧
      (∀ z ∈ wc.target, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) wc.symm z) ∧
      (∀ q ∈ wc.source, J q ∈ wc.source ∧ wc (J q) = conj (wc q)) := by
    intro p hp
    obtain ⟨wc, r, hr, h1, h2, h3, h4, h5, h6, h7⟩ :=
      s31qc_fixed_chart_local hJ hp
        ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))
    exact ⟨wc, r, h1, h3, h4, h6, h7⟩
  let W : X → Set X := fun p =>
    if h : J p = p then (Classical.choose (hfix p h)).source else Zᶜ ∩ (chartAt ℂ p).source
  have hWo : ∀ p, IsOpen (W p) := by
    intro p
    by_cases h : J p = p
    · simp only [W, dif_pos h]
      exact (Classical.choose (hfix p h)).open_source
    · simp only [W, dif_neg h]
      exact hZc.isOpen_compl.inter (chartAt ℂ p).open_source
  have hWp : ∀ p, p ∈ W p := by
    intro p
    by_cases h : J p = p
    · simp only [W, dif_pos h]
      exact (Classical.choose_spec (Classical.choose_spec (hfix p h))).1
    · simp only [W, dif_neg h]
      exact ⟨h, mem_chart_source ℂ p⟩
  have hWs : ∀ p, W p ⊆ (chartAt ℂ p).source := by
    intro p
    by_cases h : J p = p
    · simp only [W, dif_pos h]
      exact (Classical.choose_spec (Classical.choose_spec (hfix p h))).2.2.1
    · simp only [W, dif_neg h]
      exact inter_subset_right
  have hB : ∀ p, volume (chartAt ℂ p '' (Z ∩ W p)) = 0 := by
    intro p
    by_cases h : J p = p
    · simp only [W, dif_pos h]
      obtain ⟨r, hps, hwt, hwU, hwd, hwJ⟩ := Classical.choose_spec (hfix p h)
      generalize Classical.choose (hfix p h) = wc at hps hwt hwU hwd hwJ ⊢
      set s : Set ℂ := {u | u.im = 0} ∩ wc.target with hs
      have hline : volume {u : ℂ | u.im = 0} = 0 := by
        have h0 := Measure.addHaar_submodule volume (LinearMap.ker Complex.imLm) (by
          intro htop
          have h1 : Complex.I ∈ LinearMap.ker Complex.imLm := by rw [htop]; trivial
          have h2 : Complex.imLm Complex.I = 0 := LinearMap.mem_ker.1 h1
          simp [Complex.imLm] at h2)
        convert h0 using 2
        ext u
        simp [Complex.imLm]
      have hs0 : volume s = 0 := measure_mono_null inter_subset_left hline
      have hsub : chartAt ℂ p '' (Z ∩ wc.source) ⊆ (fun u => chartAt ℂ p (wc.symm u)) '' s := by
        rintro _ ⟨q, ⟨hqZ, hqs⟩, rfl⟩
        refine ⟨wc q, ⟨?_, wc.map_source hqs⟩, by simp only [wc.left_inv hqs]⟩
        have h1 := (hwJ q hqs).2
        have hJq : J q = q := hqZ
        rw [hJq] at h1
        show (wc q).im = 0
        have := congrArg Complex.im h1
        simp at this
        linarith
      refine measure_mono_null hsub ?_
      refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ hs0
      intro u hu
      have hut : u ∈ wc.target := hu.2
      have hsrc : wc.symm u ∈ (chartAt ℂ p).source := hwU (wc.map_target hut)
      have hmd := hwd u hut
      have := (s23_mdifferentiableAt_iff (f := wc.symm) (x := u) (p := u) (y := p)
        (by simp) hsrc).1 hmd
      have hd : DifferentiableAt ℂ (fun z => chartAt ℂ p (wc.symm z)) u := by
        simpa [chartAt_self_eq] using this.2
      exact (hd.restrictScalars ℝ).differentiableWithinAt
    · simp only [W, dif_neg h]
      have : Z ∩ (Zᶜ ∩ (chartAt ℂ p).source) = ∅ := by
        ext q
        simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false]
        tauto
      rw [this]; simp
  exact s82cmp_null_cover W hWo hWp hWs hB x



/-- The real Fréchet derivative of `w ↦ conj (M (conj w))`. -/
theorem s82cmp_conjconj_fderiv (M : ℂ → ℂ) (z : ℂ) (hM : DifferentiableAt ℝ M (conj z)) :
    fderiv ℝ (fun w => conj (M (conj w))) z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℝ M (conj z)).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)) := by
  have h1 : HasFDerivAt (fun w : ℂ => conj w) (Complex.conjCLE : ℂ →L[ℝ] ℂ) z :=
    Complex.conjCLE.hasFDerivAt
  have h2 : HasFDerivAt M (fderiv ℝ M (conj z)) (conj z) := hM.hasFDerivAt
  have h3 := (Complex.conjCLE.hasFDerivAt (x := M (conj z))).comp z (h2.comp z h1)
  exact h3.fderiv

/-- `∂` and `∂̄` of `w ↦ conj (M (conj w))` are the conjugates of those of `M` at `conj w`. -/
theorem s82cmp_dz_conjconj (M : ℂ → ℂ) (z : ℂ) :
    dz (fun w => conj (M (conj w))) z = conj (dz M (conj z)) ∧
      dzbar (fun w => conj (M (conj w))) z = conj (dzbar M (conj z)) := by
  by_cases hM : DifferentiableAt ℝ M (conj z)
  · have h := s82cmp_conjconj_fderiv M z hM
    simp only [dz, dzbar, h]
    constructor
    · simp [map_neg, Complex.conj_I, Complex.conj_ofNat]
    · simp [map_neg, Complex.conj_I, Complex.conj_ofNat]
  · have hN : ¬ DifferentiableAt ℝ (fun w => conj (M (conj w))) z := by
      intro hd
      apply hM
      have hd' : DifferentiableAt ℝ (fun w => conj (M (conj w))) (conj (conj z)) := by
        rw [Complex.conj_conj]; exact hd
      have hcz : DifferentiableAt ℝ (fun w : ℂ => conj w) (conj z) := Complex.conjCLE.differentiableAt
      have h2 := hd'.comp (conj z) hcz
      have h3 := (Complex.conjCLE.differentiableAt (x := (fun w => conj (M (conj w))) (conj (conj z)))).comp
        (conj z) h2
      refine h3.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
      simp
    simp [dz, dzbar, fderiv_zero_of_not_differentiableAt hM, fderiv_zero_of_not_differentiableAt hN]

/-- The complex dilatation of the conjugate-conjugated map. -/
theorem s82cmp_dil_conjconj (M : ℂ → ℂ) (z : ℂ) :
    complexDilatation (fun w => conj (M (conj w))) z = conj (complexDilatation M (conj z)) := by
  obtain ⟨h1, h2⟩ := s82cmp_dz_conjconj M z
  rw [complexDilatation, complexDilatation, h1, h2, map_div₀]


/-- **`|μ|` is unchanged by an anticonformal sandwich** `L' = conj ∘ c ∘ L ∘ conj ∘ e₀` (with `c`, `e₀`
locally biholomorphic): `‖μ_{L'}(z₀)‖ = ‖μ_L(conj (e₀ z₀))‖`. -/
theorem s82cmp_norm_dil_reflect {L L' c e0 k s : ℂ → ℂ} {z0 : ℂ}
    (hev : L' =ᶠ[𝓝 z0] fun z => conj (c (L (conj (e0 z)))))
    (hLc : ContinuousAt L (conj (e0 z0)))
    (hc : DifferentiableAt ℂ c (L (conj (e0 z0)))) (hk : DifferentiableAt ℂ k (c (L (conj (e0 z0)))))
    (hkc : ∀ᶠ w in 𝓝 (L (conj (e0 z0))), k (c w) = w)
    (he : DifferentiableAt ℂ e0 z0) (hs : DifferentiableAt ℂ s (e0 z0))
    (hse : ∀ᶠ w in 𝓝 z0, s (e0 w) = w) (hes : ∀ᶠ u in 𝓝 (e0 z0), e0 (s u) = u) :
    ‖complexDilatation L' z0‖ = ‖complexDilatation L (conj (e0 z0))‖ := by
  set N : ℂ → ℂ := fun w => conj ((c ∘ L) (conj w)) with hN
  have h1 : complexDilatation L' z0 = complexDilatation (N ∘ e0) z0 := by
    simp only [complexDilatation, dz, dzbar, hev.fderiv_eq (𝕜 := ℝ)]
    rfl
  have h2 := s23_dilatation_comp_right (g := N) he hs hse hes
  have h3 : complexDilatation N (e0 z0) = conj (complexDilatation (c ∘ L) (conj (e0 z0))) :=
    s82cmp_dil_conjconj (c ∘ L) (e0 z0)
  have h4 : complexDilatation (c ∘ L) (conj (e0 z0)) = complexDilatation L (conj (e0 z0)) :=
    s23_dilatation_comp_left hLc hc hk hkc
  have hne : deriv e0 z0 ≠ 0 := s23_deriv_ne_zero he hs hse
  rw [h1, h2, h3, h4, norm_mul, Complex.norm_conj, norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.2 hne), mul_one]


/-- Basic facts on the local expressions of an anticonformal involution at `p`. -/
theorem s82cmp_involution_pair {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {J : X ≃ₜ X} (hJ : IsAnticonformalInvolution J) (p : X) :
    DifferentiableAt ℂ (fun z => conj (localMapExpr J p z)) (chartAt ℂ p p) ∧
      localMapExpr J p (chartAt ℂ p p) = chartAt ℂ (J p) (J p) ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ p p), localMapExpr J (J p) (localMapExpr J p z) = z := by
  have hps : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
  have hdom : chartAt ℂ p p ∈ localMapDomain J p :=
    ⟨(chartAt ℂ p).map_source hps, by
      show J ((chartAt ℂ p).symm (chartAt ℂ p p)) ∈ (chartAt ℂ (J p)).source
      rw [(chartAt ℂ p).left_inv hps]
      exact mem_chart_source ℂ (J p)⟩
  refine ⟨(hJ.2 p).differentiableAt ((s23_localMapDomain_isOpen J.continuous p).mem_nhds hdom), ?_, ?_⟩
  · simp only [localMapExpr, (chartAt ℂ p).left_inv hps]
  · have h1 : ∀ᶠ z in 𝓝 (chartAt ℂ p p), z ∈ (chartAt ℂ p).target :=
      (chartAt ℂ p).open_target.mem_nhds ((chartAt ℂ p).map_source hps)
    have hc : ContinuousAt (fun z => J ((chartAt ℂ p).symm z)) (chartAt ℂ p p) :=
      J.continuous.continuousAt.comp ((chartAt ℂ p).continuousAt_symm ((chartAt ℂ p).map_source hps))
    have h2 : ∀ᶠ z in 𝓝 (chartAt ℂ p p), J ((chartAt ℂ p).symm z) ∈ (chartAt ℂ (J p)).source := by
      refine hc.eventually_mem ?_
      show (chartAt ℂ (J p)).source ∈ 𝓝 (J ((chartAt ℂ p).symm (chartAt ℂ p p)))
      rw [(chartAt ℂ p).left_inv hps]
      exact (chartAt ℂ (J p)).open_source.mem_nhds (mem_chart_source ℂ (J p))
    filter_upwards [h1, h2] with z hz hz2
    simp only [localMapExpr]
    rw [(chartAt ℂ (J p)).left_inv hz2, hJ.1 p, hJ.1, (chartAt ℂ p).right_inv hz]

/-- **The dilatation quotient is invariant under reflections.**  If `F` commutes with anticonformal involutions
`J₀`, `J₁`, then `D_F(J₀ y) = D_F(y)` (read at the chart centres). -/
theorem s82cmp_D_reflect {X₀ X₁ : Type*} [TopologicalSpace X₀] [ChartedSpace ℂ X₀] [IsManifold 𝓘(ℂ) ω X₀]
    [TopologicalSpace X₁] [ChartedSpace ℂ X₁] [IsManifold 𝓘(ℂ) ω X₁]
    {J₀ : X₀ ≃ₜ X₀} {J₁ : X₁ ≃ₜ X₁} (hJ₀ : IsAnticonformalInvolution J₀) (hJ₁ : IsAnticonformalInvolution J₁)
    (F : X₀ ≃ₜ X₁) (hF : ∀ y, F (J₀ y) = J₁ (F y)) (y : X₀) :
    dilatationQuotient (localMapExpr F (J₀ y)) (chartAt ℂ (J₀ y) (J₀ y)) =
      dilatationQuotient (localMapExpr F y) (chartAt ℂ y y) := by
  classical
  set y' := J₀ y with hy'
  set w := F y with hw
  have hyy : J₀ y' = y := hJ₀.1 y
  have hFy' : F y' = J₁ w := hF y
  obtain ⟨hAd, hAc, hAB⟩ := s82cmp_involution_pair hJ₁ w
  obtain ⟨hBd, -, -⟩ := s82cmp_involution_pair hJ₁ (J₁ w)
  obtain ⟨hEd, hEc, hEB⟩ := s82cmp_involution_pair hJ₀ y
  obtain ⟨hE'd, hE'c, hE'B⟩ := s82cmp_involution_pair hJ₀ y'
  rw [hyy] at hE'c hE'B
  have hys : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have hy's : y' ∈ (chartAt ℂ y').source := mem_chart_source ℂ y'
  have hws : w ∈ (chartAt ℂ w).source := mem_chart_source ℂ w
  set e0 : ℂ → ℂ := fun z => conj (localMapExpr J₀ y' z) with he0
  set c : ℂ → ℂ := fun u => conj (localMapExpr J₁ w u) with hc
  set k : ℂ → ℂ := fun v => localMapExpr J₁ (J₁ w) (conj v) with hk
  set s : ℂ → ℂ := fun u => localMapExpr J₀ y (conj u) with hs
  set L : ℂ → ℂ := localMapExpr F y with hL
  set L' : ℂ → ℂ := localMapExpr F y' with hL'
  have hce : conj (e0 (chartAt ℂ y' y')) = chartAt ℂ y y := by
    simp only [he0, hE'c, Complex.conj_conj]
  have hLzy : L (chartAt ℂ y y) = chartAt ℂ w w := by
    simp only [hL, localMapExpr, (chartAt ℂ y).left_inv hys]
    rfl
  -- the local expression of `F` at `y'`
  have hev : L' =ᶠ[𝓝 (chartAt ℂ y' y')] fun z => conj (c (L (conj (e0 z)))) := by
    have h1 : ∀ᶠ z in 𝓝 (chartAt ℂ y' y'), z ∈ (chartAt ℂ y').target :=
      (chartAt ℂ y').open_target.mem_nhds ((chartAt ℂ y').map_source hy's)
    have hc1 : ContinuousAt (fun z => J₀ ((chartAt ℂ y').symm z)) (chartAt ℂ y' y') :=
      J₀.continuous.continuousAt.comp ((chartAt ℂ y').continuousAt_symm ((chartAt ℂ y').map_source hy's))
    have h2 : ∀ᶠ z in 𝓝 (chartAt ℂ y' y'), J₀ ((chartAt ℂ y').symm z) ∈ (chartAt ℂ y).source := by
      refine hc1.eventually_mem ?_
      show (chartAt ℂ y).source ∈ 𝓝 (J₀ ((chartAt ℂ y').symm (chartAt ℂ y' y')))
      rw [(chartAt ℂ y').left_inv hy's, hyy]
      exact (chartAt ℂ y).open_source.mem_nhds hys
    have hc2 : ContinuousAt (fun z => F (J₀ ((chartAt ℂ y').symm z))) (chartAt ℂ y' y') :=
      F.continuous.continuousAt.comp hc1
    have h3 : ∀ᶠ z in 𝓝 (chartAt ℂ y' y'), F (J₀ ((chartAt ℂ y').symm z)) ∈ (chartAt ℂ w).source := by
      refine hc2.eventually_mem ?_
      show (chartAt ℂ w).source ∈ 𝓝 (F (J₀ ((chartAt ℂ y').symm (chartAt ℂ y' y'))))
      rw [(chartAt ℂ y').left_inv hy's, hyy]
      exact (chartAt ℂ w).open_source.mem_nhds hws
    filter_upwards [h1, h2, h3] with z hz hz2 hz3
    simp only [hL', hc, he0, hL, localMapExpr, Complex.conj_conj]
    have key : J₁ (F (J₀ ((chartAt ℂ y').symm z))) = F ((chartAt ℂ y').symm z) := by
      rw [← hF, hJ₀.1]
    rw [hyy, (chartAt ℂ y).left_inv hz2, (chartAt ℂ w).left_inv hz3, key, hFy']
  have hLc : ContinuousAt L (conj (e0 (chartAt ℂ y' y'))) := by
    rw [hce]
    have h1 : ContinuousAt (fun z => (chartAt ℂ y).symm z) (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm ((chartAt ℂ y).map_source hys)
    have h2 : ContinuousAt (fun z => chartAt ℂ w (F ((chartAt ℂ y).symm z))) (chartAt ℂ y y) := by
      refine ContinuousAt.comp (g := chartAt ℂ w) ?_ (F.continuous.continuousAt.comp h1)
      show ContinuousAt (chartAt ℂ w) (F ((chartAt ℂ y).symm (chartAt ℂ y y)))
      rw [(chartAt ℂ y).left_inv hys]
      exact (chartAt ℂ w).continuousAt hws
    exact h2
  have hcL : L (conj (e0 (chartAt ℂ y' y'))) = chartAt ℂ w w := by rw [hce, hLzy]
  have hcd : DifferentiableAt ℂ c (L (conj (e0 (chartAt ℂ y' y')))) := by
    rw [hcL]; exact hAd
  have hkd : DifferentiableAt ℂ k (c (L (conj (e0 (chartAt ℂ y' y'))))) := by
    rw [hcL]
    have h1 : DifferentiableAt ℂ (fun z => conj (localMapExpr J₁ (J₁ w) z)) (chartAt ℂ (J₁ w) (J₁ w)) := hBd
    have h2 := h1.conj_conj
    have hczw : c (chartAt ℂ w w) = conj (chartAt ℂ (J₁ w) (J₁ w)) := by simp only [hc, hAc, Complex.conj_conj]
    rw [hczw]
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
    simp [hk]
  have hkc : ∀ᶠ v in 𝓝 (L (conj (e0 (chartAt ℂ y' y')))), k (c v) = v := by
    rw [hcL]
    filter_upwards [hAB] with v hv
    simpa [hk, hc, Complex.conj_conj] using hv
  have hed : DifferentiableAt ℂ e0 (chartAt ℂ y' y') := hE'd
  have hsd : DifferentiableAt ℂ s (e0 (chartAt ℂ y' y')) := by
    have h2 := hEd.conj_conj
    have : e0 (chartAt ℂ y' y') = conj (chartAt ℂ y y) := by
      rw [← hce, Complex.conj_conj]
    rw [this]
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
    simp [hs]
  have hse : ∀ᶠ z in 𝓝 (chartAt ℂ y' y'), s (e0 z) = z := by
    filter_upwards [hE'B] with z hz
    simpa [hs, he0, Complex.conj_conj] using hz
  have hes : ∀ᶠ u in 𝓝 (e0 (chartAt ℂ y' y')), e0 (s u) = u := by
    have hten : Tendsto (fun u : ℂ => conj u) (𝓝 (e0 (chartAt ℂ y' y'))) (𝓝 (chartAt ℂ y y)) := by
      rw [← hce]; exact (Complex.continuous_conj.tendsto _)
    filter_upwards [hten.eventually hEB] with u hu
    simp only [he0, hs]
    rw [hu, Complex.conj_conj]
  have key := s82cmp_norm_dil_reflect hev hLc hcd hkd hkc hed hsd hse hes
  rw [hce] at key
  unfold dilatationQuotient
  rw [key]


/-- **Chart independence of a pull-back relation, holomorphic case.**  If `r = Φ^* q` holds at `a` in the charts
`φ_a`, `φ_{Φ a}` (`hrel`), then in **any** charts `x ∋ a`, `ŷ ∋ Φ a`. -/
theorem s82cmp_chart_change {S Y : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {r : S → ℂ → ℂ} {q : Y → ℂ → ℂ} (hr : IsHolQuadDiff r) (hq : IsHolQuadDiff q)
    {Φ : S → Y} {a : S} (hΦd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) Φ a)
    (hrel : r a (chartAt ℂ a a) = q (Φ a) (chartAt ℂ (Φ a) (Φ a)) *
      deriv (fun v => chartAt ℂ (Φ a) (Φ ((chartAt ℂ a).symm v))) (chartAt ℂ a a) ^ 2)
    {x : S} {ŷ : Y} (hax : a ∈ (chartAt ℂ x).source) (hŷ : Φ a ∈ (chartAt ℂ ŷ).source) :
    r x (chartAt ℂ x a) = q ŷ (chartAt ℂ ŷ (Φ a)) *
      deriv (fun w => chartAt ℂ ŷ (Φ ((chartAt ℂ x).symm w))) (chartAt ℂ x a) ^ 2 := by
  classical
  set y' := Φ a with hy'
  set c' := chartAt ℂ y' y' with hc'
  set ca := chartAt ℂ a a with hca
  set w := chartAt ℂ x a with hw
  set z := chartAt ℂ ŷ y' with hz
  let Ta : ℂ → ℂ := fun v => chartAt ℂ y' (Φ ((chartAt ℂ a).symm v))
  let Tx : ℂ → ℂ := fun v => chartAt ℂ ŷ (Φ ((chartAt ℂ x).symm v))
  have hy'mem : y' ∈ (chartAt ℂ y').source := mem_chart_source ℂ y'
  have ha_mem : a ∈ (chartAt ℂ a).source := mem_chart_source ℂ a
  have hΦc : ContinuousAt Φ a := hΦd.continuousAt
  have hTx_d : DifferentiableAt ℂ Tx w := ((s23_mdifferentiableAt_iff hax hŷ).1 hΦd).2
  have hTa_d : DifferentiableAt ℂ Ta ca := ((s23_mdifferentiableAt_iff ha_mem hy'mem).1 hΦd).2
  have hrel'' : r a ca = q y' c' * deriv Ta ca ^ 2 := hrel
  -- transformation laws
  have hwt : w ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hax
  have hwsymm : (chartAt ℂ x).symm w = a := (chartAt ℂ x).left_inv hax
  have hzt : z ∈ (chartAt ℂ ŷ).target := (chartAt ℂ ŷ).map_source hŷ
  have hzsymm : (chartAt ℂ ŷ).symm z = y' := (chartAt ℂ ŷ).left_inv hŷ
  have hlawr : r x w = r a (chartTransition a x w) * deriv (chartTransition a x) w ^ 2 :=
    s26u_law hr x a hwt (by rw [hwsymm]; exact ha_mem)
  have hlawq : q ŷ z = q y' (chartTransition y' ŷ z) * deriv (chartTransition y' ŷ) z ^ 2 :=
    s26u_law hq ŷ y' hzt (by rw [hzsymm]; exact hy'mem)
  have hτw : chartTransition a x w = ca := by
    simp only [chartTransition, hwsymm]; rfl
  have hτz : chartTransition y' ŷ z = c' := by
    simp only [chartTransition, hzsymm]; rfl
  have hτd : DifferentiableAt ℂ (chartTransition a x) w :=
    s23_transition_differentiableAt a x hwt (by rw [hwsymm]; exact ha_mem)
  have hτzd : DifferentiableAt ℂ (chartTransition y' ŷ) z :=
    s23_transition_differentiableAt y' ŷ hzt (by rw [hzsymm]; exact hy'mem)
  have hTxw : Tx w = z := by simp only [Tx, hwsymm]; rfl
  have hchain_ev : (Ta ∘ chartTransition a x) =ᶠ[𝓝 w] (chartTransition y' ŷ ∘ Tx) := by
    have h1 : ContinuousAt (chartAt ℂ x).symm w := (chartAt ℂ x).continuousAt_symm hwt
    have h2 : ContinuousAt (fun v => Φ ((chartAt ℂ x).symm v)) w := by
      have : ContinuousAt Φ ((chartAt ℂ x).symm w) := by rw [hwsymm]; exact hΦc
      exact this.comp h1
    have h3 : ∀ᶠ v in 𝓝 w, Φ ((chartAt ℂ x).symm v) ∈ (chartAt ℂ ŷ).source := by
      refine h2.eventually ?_
      have : Φ ((chartAt ℂ x).symm w) ∈ (chartAt ℂ ŷ).source := by rw [hwsymm]; exact hŷ
      exact (chartAt ℂ ŷ).open_source.mem_nhds this
    have h4 : ∀ᶠ v in 𝓝 w, (chartAt ℂ x).symm v ∈ (chartAt ℂ a).source := by
      refine h1.eventually ?_
      rw [hwsymm]
      exact (chartAt ℂ a).open_source.mem_nhds ha_mem
    filter_upwards [h3, h4] with v hv3 hv4
    simp only [Function.comp, chartTransition, Ta, Tx]
    rw [(chartAt ℂ a).left_inv hv4, (chartAt ℂ ŷ).left_inv hv3]
  have hd1 : HasDerivAt (Ta ∘ chartTransition a x) (deriv Ta ca * deriv (chartTransition a x) w) w := by
    have hTa_h : HasDerivAt Ta (deriv Ta ca) (chartTransition a x w) := by
      rw [hτw]; exact hTa_d.hasDerivAt
    exact hTa_h.comp w hτd.hasDerivAt
  have hd2 : HasDerivAt (chartTransition y' ŷ ∘ Tx) (deriv (chartTransition y' ŷ) z * deriv Tx w) w := by
    have hτ_h : HasDerivAt (chartTransition y' ŷ) (deriv (chartTransition y' ŷ) z) (Tx w) := by
      rw [hTxw]; exact hτzd.hasDerivAt
    exact hτ_h.comp w hTx_d.hasDerivAt
  have hd1' : HasDerivAt (chartTransition y' ŷ ∘ Tx) (deriv Ta ca * deriv (chartTransition a x) w) w :=
    hd1.congr_of_eventuallyEq hchain_ev.symm
  have hchain : deriv Ta ca * deriv (chartTransition a x) w =
      deriv (chartTransition y' ŷ) z * deriv Tx w := hd1'.unique hd2
  calc r x w = r a ca * deriv (chartTransition a x) w ^ 2 := by rw [hlawr, hτw]
    _ = q y' c' * deriv Ta ca ^ 2 * deriv (chartTransition a x) w ^ 2 := by rw [hrel'']
    _ = q y' c' * (deriv Ta ca * deriv (chartTransition a x) w) ^ 2 := by ring
    _ = q y' c' * (deriv (chartTransition y' ŷ) z * deriv Tx w) ^ 2 := by rw [hchain]
    _ = (q y' c' * deriv (chartTransition y' ŷ) z ^ 2) * deriv Tx w ^ 2 := by ring
    _ = q ŷ z * deriv Tx w ^ 2 := by rw [hlawq, hτz]

/-- **Chart independence of a norm relation, anticonformal case.**  Same as `s82cmp_chart_change`, for a map `Φ`
anticonformal in all charts and with `‖r‖ = ‖Φ^* q‖` at `a`. -/
theorem s82cmp_chart_change_anti {S Y : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {r : S → ℂ → ℂ} {q : Y → ℂ → ℂ} (hr : IsHolQuadDiff r) (hq : IsHolQuadDiff q)
    {Φ : S → Y} {a : S} (hΦc : ContinuousAt Φ a)
    (hΦd : ∀ (x : S) (ŷ : Y), a ∈ (chartAt ℂ x).source → Φ a ∈ (chartAt ℂ ŷ).source →
      DifferentiableAt ℂ (fun w => conj (chartAt ℂ ŷ (Φ ((chartAt ℂ x).symm w)))) (chartAt ℂ x a))
    (hrel : ‖r a (chartAt ℂ a a)‖ = ‖q (Φ a) (chartAt ℂ (Φ a) (Φ a))‖ *
      ‖deriv (fun v => conj (chartAt ℂ (Φ a) (Φ ((chartAt ℂ a).symm v)))) (chartAt ℂ a a)‖ ^ 2)
    {x : S} {ŷ : Y} (hax : a ∈ (chartAt ℂ x).source) (hŷ : Φ a ∈ (chartAt ℂ ŷ).source) :
    ‖r x (chartAt ℂ x a)‖ = ‖q ŷ (chartAt ℂ ŷ (Φ a))‖ *
      ‖deriv (fun w => conj (chartAt ℂ ŷ (Φ ((chartAt ℂ x).symm w)))) (chartAt ℂ x a)‖ ^ 2 := by
  classical
  set y' := Φ a with hy'
  set c' := chartAt ℂ y' y' with hc'
  set ca := chartAt ℂ a a with hca
  set w := chartAt ℂ x a with hw
  set z := chartAt ℂ ŷ y' with hz
  let Ha : ℂ → ℂ := fun v => conj (chartAt ℂ y' (Φ ((chartAt ℂ a).symm v)))
  let Hx : ℂ → ℂ := fun v => conj (chartAt ℂ ŷ (Φ ((chartAt ℂ x).symm v)))
  have hy'mem : y' ∈ (chartAt ℂ y').source := mem_chart_source ℂ y'
  have ha_mem : a ∈ (chartAt ℂ a).source := mem_chart_source ℂ a
  have hHa_d : DifferentiableAt ℂ Ha ca := hΦd a y' ha_mem hy'mem
  have hHx_d : DifferentiableAt ℂ Hx w := hΦd x ŷ hax hŷ
  have hwt : w ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hax
  have hwsymm : (chartAt ℂ x).symm w = a := (chartAt ℂ x).left_inv hax
  have hzt : z ∈ (chartAt ℂ ŷ).target := (chartAt ℂ ŷ).map_source hŷ
  have hzsymm : (chartAt ℂ ŷ).symm z = y' := (chartAt ℂ ŷ).left_inv hŷ
  have hlawr : r x w = r a (chartTransition a x w) * deriv (chartTransition a x) w ^ 2 :=
    s26u_law hr x a hwt (by rw [hwsymm]; exact ha_mem)
  have hlawq : q ŷ z = q y' (chartTransition y' ŷ z) * deriv (chartTransition y' ŷ) z ^ 2 :=
    s26u_law hq ŷ y' hzt (by rw [hzsymm]; exact hy'mem)
  have hτw : chartTransition a x w = ca := by
    simp only [chartTransition, hwsymm]; rfl
  have hτz : chartTransition y' ŷ z = c' := by
    simp only [chartTransition, hzsymm]; rfl
  have hτd : DifferentiableAt ℂ (chartTransition a x) w :=
    s23_transition_differentiableAt a x hwt (by rw [hwsymm]; exact ha_mem)
  have hτzd : DifferentiableAt ℂ (chartTransition y' ŷ) z :=
    s23_transition_differentiableAt y' ŷ hzt (by rw [hzsymm]; exact hy'mem)
  have hHxw : Hx w = conj z := by simp only [Hx, hwsymm]; rfl
  -- the conjugated transition
  set K : ℂ → ℂ := fun u => conj (chartTransition y' ŷ (conj u)) with hK
  have hKhas : HasDerivAt K (conj (deriv (chartTransition y' ŷ) z)) (conj z) := by
    have h1 : HasDerivAt (chartTransition y' ŷ) (deriv (chartTransition y' ŷ) z) z := hτzd.hasDerivAt
    have h2 : HasDerivAt (chartTransition y' ŷ) (conj (conj (deriv (chartTransition y' ŷ) z)))
        (conj (conj z)) := by rw [Complex.conj_conj, Complex.conj_conj]; exact h1
    exact (hasDerivAt_conj_conj_iff (f := chartTransition y' ŷ)).2 h2
  have hchain_ev : (Ha ∘ chartTransition a x) =ᶠ[𝓝 w] (K ∘ Hx) := by
    have h1 : ContinuousAt (chartAt ℂ x).symm w := (chartAt ℂ x).continuousAt_symm hwt
    have h2 : ContinuousAt (fun v => Φ ((chartAt ℂ x).symm v)) w := by
      have : ContinuousAt Φ ((chartAt ℂ x).symm w) := by rw [hwsymm]; exact hΦc
      exact this.comp h1
    have h3 : ∀ᶠ v in 𝓝 w, Φ ((chartAt ℂ x).symm v) ∈ (chartAt ℂ ŷ).source := by
      refine h2.eventually ?_
      have : Φ ((chartAt ℂ x).symm w) ∈ (chartAt ℂ ŷ).source := by rw [hwsymm]; exact hŷ
      exact (chartAt ℂ ŷ).open_source.mem_nhds this
    have h4 : ∀ᶠ v in 𝓝 w, (chartAt ℂ x).symm v ∈ (chartAt ℂ a).source := by
      refine h1.eventually ?_
      rw [hwsymm]
      exact (chartAt ℂ a).open_source.mem_nhds ha_mem
    filter_upwards [h3, h4] with v hv3 hv4
    simp only [Function.comp, chartTransition, Ha, Hx, hK, Complex.conj_conj]
    rw [(chartAt ℂ a).left_inv hv4, (chartAt ℂ ŷ).left_inv hv3]
  have hd1 : HasDerivAt (Ha ∘ chartTransition a x) (deriv Ha ca * deriv (chartTransition a x) w) w := by
    have hHa_h : HasDerivAt Ha (deriv Ha ca) (chartTransition a x w) := by
      rw [hτw]; exact hHa_d.hasDerivAt
    exact hHa_h.comp w hτd.hasDerivAt
  have hd2 : HasDerivAt (K ∘ Hx) (conj (deriv (chartTransition y' ŷ) z) * deriv Hx w) w := by
    have hK_h : HasDerivAt K (conj (deriv (chartTransition y' ŷ) z)) (Hx w) := by
      rw [hHxw]; exact hKhas
    exact hK_h.comp w hHx_d.hasDerivAt
  have hd1' : HasDerivAt (K ∘ Hx) (deriv Ha ca * deriv (chartTransition a x) w) w :=
    hd1.congr_of_eventuallyEq hchain_ev.symm
  have hchain : deriv Ha ca * deriv (chartTransition a x) w =
      conj (deriv (chartTransition y' ŷ) z) * deriv Hx w := hd1'.unique hd2
  have hnorm : ‖deriv Ha ca‖ * ‖deriv (chartTransition a x) w‖ =
      ‖deriv (chartTransition y' ŷ) z‖ * ‖deriv Hx w‖ := by
    have := congrArg norm hchain
    simpa [norm_mul, Complex.norm_conj] using this
  have hlawr' : ‖r x w‖ = ‖r a ca‖ * ‖deriv (chartTransition a x) w‖ ^ 2 := by
    rw [hlawr, hτw, norm_mul, norm_pow]
  have hlawq' : ‖q ŷ z‖ = ‖q y' c'‖ * ‖deriv (chartTransition y' ŷ) z‖ ^ 2 := by
    rw [hlawq, hτz, norm_mul, norm_pow]
  calc ‖r x w‖ = ‖r a ca‖ * ‖deriv (chartTransition a x) w‖ ^ 2 := hlawr'
    _ = ‖q y' c'‖ * ‖deriv Ha ca‖ ^ 2 * ‖deriv (chartTransition a x) w‖ ^ 2 := by rw [hrel]
    _ = ‖q y' c'‖ * (‖deriv Ha ca‖ * ‖deriv (chartTransition a x) w‖) ^ 2 := by ring
    _ = ‖q y' c'‖ * (‖deriv (chartTransition y' ŷ) z‖ * ‖deriv Hx w‖) ^ 2 := by rw [hnorm]
    _ = (‖q y' c'‖ * ‖deriv (chartTransition y' ŷ) z‖ ^ 2) * ‖deriv Hx w‖ ^ 2 := by ring
    _ = ‖q ŷ z‖ * ‖deriv Hx w‖ ^ 2 := by rw [hlawq']



/-- Change of variables for the area integral through an injective map, norm form: if `‖rr w‖ = ‖qq (T w)‖ ‖T' w‖²`
on `M` and `T` is complex differentiable and injective on `M`, then `∫_{T(M)} F |qq| = ∫_M (F ∘ T) |rr|`. -/
theorem s82cmp_lintegral_pullback_norm {M : Set ℂ} (hM : MeasurableSet M) {T : ℂ → ℂ}
    (hd : ∀ w ∈ M, DifferentiableAt ℂ T w) (hinj : InjOn T M) {F : ℂ → ℝ≥0∞} {rr qq : ℂ → ℂ}
    (hrel : ∀ w ∈ M, ‖rr w‖ = ‖qq (T w)‖ * ‖deriv T w‖ ^ 2) :
    ∫⁻ z in T '' M, F z * ENNReal.ofReal ‖qq z‖ = ∫⁻ w in M, F (T w) * ENNReal.ofReal ‖rr w‖ := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hM
    (fun w hw => ((hd w hw).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt) hinj]
  refine setLIntegral_congr_fun hM fun w hw => ?_
  have hdw := hd w hw
  have hdet : (fderiv ℝ T w).det = ‖deriv T w‖ ^ 2 := by
    have e := det_fderiv_eq_jacobian (hdw.restrictScalars ℝ)
    rw [show (fderiv ℝ T w).det = LinearMap.det (fderiv ℝ T w : ℂ →ₗ[ℝ] ℂ) from rfl, e,
      jacobian, dz_eq_deriv hdw, (cauchyRiemann_iff.1 hdw).2, norm_zero]
    ring
  rw [hdet, abs_of_nonneg (by positivity), hrel w hw, ENNReal.ofReal_mul (norm_nonneg _)]
  ring

/-- **Area of a piece under a holomorphic injective map.**  The chart image of `Φ(A)` is measurable and its area
integral equals the pulled-back one over `A`, given the chart-wise relation `r = Φ^* Q`. -/
theorem s82cmp_piece_hol {S Y : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {Φ : S → Y} {x : S} {ŷ : Y} {A : Set S}
    (hAx : A ⊆ (chartAt ℂ x).source) (hAm : MeasurableSet (chartAt ℂ x '' A))
    (hΦd : ∀ a ∈ A, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) Φ a) (hinj : InjOn Φ A)
    (hŷ : Φ '' A ⊆ (chartAt ℂ ŷ).source) {r : S → ℂ → ℂ} {Q : Y → ℂ → ℂ}
    (hrel : ∀ a ∈ A, r x (chartAt ℂ x a) = Q ŷ (chartAt ℂ ŷ (Φ a)) *
      deriv (fun w => chartAt ℂ ŷ (Φ ((chartAt ℂ x).symm w))) (chartAt ℂ x a) ^ 2)
    (U : Y → ℝ≥0∞) :
    MeasurableSet (chartAt ℂ ŷ '' (Φ '' A)) ∧
      ∫⁻ z in chartAt ℂ ŷ '' (Φ '' A), U ((chartAt ℂ ŷ).symm z) * ENNReal.ofReal ‖Q ŷ z‖ =
        ∫⁻ w in chartAt ℂ x '' A, U (Φ ((chartAt ℂ x).symm w)) * ENNReal.ofReal ‖r x w‖ := by
  classical
  set T : ℂ → ℂ := fun w => chartAt ℂ ŷ (Φ ((chartAt ℂ x).symm w)) with hT
  have himg : T '' (chartAt ℂ x '' A) = chartAt ℂ ŷ '' (Φ '' A) := by
    ext z
    constructor
    · rintro ⟨w, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨Φ a, ⟨a, ha, rfl⟩, by simp only [hT, (chartAt ℂ x).left_inv (hAx ha)]⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨chartAt ℂ x a, ⟨a, ha, rfl⟩, by simp only [hT, (chartAt ℂ x).left_inv (hAx ha)]⟩
  have hd : ∀ w ∈ chartAt ℂ x '' A, DifferentiableAt ℂ T w := by
    rintro w ⟨a, ha, rfl⟩
    exact ((s23_mdifferentiableAt_iff (hAx ha) (hŷ ⟨a, ha, rfl⟩)).1 (hΦd a ha)).2
  have hTinj : InjOn T (chartAt ℂ x '' A) := by
    rintro w₁ ⟨a₁, ha₁, rfl⟩ w₂ ⟨a₂, ha₂, rfl⟩ h
    simp only [hT, (chartAt ℂ x).left_inv (hAx ha₁), (chartAt ℂ x).left_inv (hAx ha₂)] at h
    have h1 := (chartAt ℂ ŷ).injOn (hŷ ⟨a₁, ha₁, rfl⟩) (hŷ ⟨a₂, ha₂, rfl⟩) h
    rw [hinj ha₁ ha₂ h1]
  refine ⟨?_, ?_⟩
  · rw [← himg]
    exact hAm.image_of_continuousOn_injOn
      (continuousOn_of_forall_continuousAt fun w hw => (hd w hw).continuousAt) hTinj
  · rw [← himg]
    have hrel' : ∀ w ∈ chartAt ℂ x '' A, r x w = Q ŷ (T w) * deriv T w ^ 2 := by
      rintro w ⟨a, ha, rfl⟩
      have := hrel a ha
      simpa only [hT, (chartAt ℂ x).left_inv (hAx ha)] using this
    have key := s82cmp_lintegral_pullback (F := fun z => U ((chartAt ℂ ŷ).symm z)) hAm hd hTinj hrel'
    rw [key]
    refine setLIntegral_congr_fun hAm fun w hw => ?_
    obtain ⟨a, ha, rfl⟩ := hw
    simp only [hT, (chartAt ℂ x).left_inv (hAx ha)]
    rw [(chartAt ℂ ŷ).left_inv (hŷ ⟨a, ha, rfl⟩)]

/-- **Area of a piece under an anticonformal injective map** (norm relation `‖r‖ = ‖Φ^* Q‖`). -/
theorem s82cmp_piece_anti {S Y : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {Φ : S → Y} {x : S} {ŷ : Y} {A : Set S}
    (hAx : A ⊆ (chartAt ℂ x).source) (hAm : MeasurableSet (chartAt ℂ x '' A))
    (hΦd : ∀ a ∈ A, DifferentiableAt ℂ (fun w => conj (chartAt ℂ ŷ (Φ ((chartAt ℂ x).symm w))))
      (chartAt ℂ x a)) (hinj : InjOn Φ A)
    (hŷ : Φ '' A ⊆ (chartAt ℂ ŷ).source) {r : S → ℂ → ℂ} {Q : Y → ℂ → ℂ}
    (hrel : ∀ a ∈ A, ‖r x (chartAt ℂ x a)‖ = ‖Q ŷ (chartAt ℂ ŷ (Φ a))‖ *
      ‖deriv (fun w => conj (chartAt ℂ ŷ (Φ ((chartAt ℂ x).symm w)))) (chartAt ℂ x a)‖ ^ 2)
    (U : Y → ℝ≥0∞) :
    MeasurableSet (chartAt ℂ ŷ '' (Φ '' A)) ∧
      ∫⁻ z in chartAt ℂ ŷ '' (Φ '' A), U ((chartAt ℂ ŷ).symm z) * ENNReal.ofReal ‖Q ŷ z‖ =
        ∫⁻ w in chartAt ℂ x '' A, U (Φ ((chartAt ℂ x).symm w)) * ENNReal.ofReal ‖r x w‖ := by
  classical
  set T : ℂ → ℂ := fun w => chartAt ℂ ŷ (Φ ((chartAt ℂ x).symm w)) with hT
  set H : ℂ → ℂ := fun w => conj (T w) with hH
  set M : Set ℂ := chartAt ℂ x '' A with hM
  have hTimg : T '' M = chartAt ℂ ŷ '' (Φ '' A) := by
    ext z
    constructor
    · rintro ⟨w, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨Φ a, ⟨a, ha, rfl⟩, by simp only [hT, (chartAt ℂ x).left_inv (hAx ha)]⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨chartAt ℂ x a, ⟨a, ha, rfl⟩, by simp only [hT, (chartAt ℂ x).left_inv (hAx ha)]⟩
  have hd : ∀ w ∈ M, DifferentiableAt ℂ H w := by
    rintro w ⟨a, ha, rfl⟩
    exact hΦd a ha
  have hTinj : InjOn T M := by
    rintro w₁ ⟨a₁, ha₁, rfl⟩ w₂ ⟨a₂, ha₂, rfl⟩ h
    simp only [hT, (chartAt ℂ x).left_inv (hAx ha₁), (chartAt ℂ x).left_inv (hAx ha₂)] at h
    have h1 := (chartAt ℂ ŷ).injOn (hŷ ⟨a₁, ha₁, rfl⟩) (hŷ ⟨a₂, ha₂, rfl⟩) h
    rw [hinj ha₁ ha₂ h1]
  have hHinj : InjOn H M := by
    intro w₁ h₁ w₂ h₂ h
    exact hTinj h₁ h₂ (by simpa [hH] using congrArg conj h)
  have hTH : T = fun w => conj (H w) := by
    funext w; simp [hH]
  refine ⟨?_, ?_⟩
  · rw [← hTimg]
    refine hAm.image_of_continuousOn_injOn (continuousOn_of_forall_continuousAt fun w hw => ?_) hTinj
    rw [hTH]
    exact Complex.continuous_conj.continuousAt.comp (hd w hw).continuousAt
  · rw [← hTimg]
    have hHM : T '' M = conj ⁻¹' (H '' M) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, by simp [hH]⟩
      · rintro ⟨w, hw, hwz⟩
        exact ⟨w, hw, by simpa [hH] using congrArg conj hwz⟩
    set φ : ℂ → ℝ≥0∞ := fun z => U ((chartAt ℂ ŷ).symm z) * ENNReal.ofReal ‖Q ŷ z‖ with hφ
    have hmp := Complex.conjLIE.measurePreserving
    have hme : MeasurableEmbedding (Complex.conjLIE : ℂ → ℂ) := Complex.conjLIE.toHomeomorph.measurableEmbedding
    have e1 : ∫⁻ z in conj ⁻¹' (H '' M), φ z = ∫⁻ y in H '' M, φ (conj y) := by
      have := hmp.setLIntegral_comp_preimage_emb hme (fun y => φ (conj y)) (H '' M)
      have hcoe : ((Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) : ℂ → ℂ) = conj := rfl
      rw [hcoe] at this
      simpa [Complex.conj_conj] using this
    rw [hHM, e1]
    have hrel' : ∀ w ∈ M, ‖r x w‖ = ‖Q ŷ (conj (H w))‖ * ‖deriv H w‖ ^ 2 := by
      rintro w ⟨a, ha, rfl⟩
      have := hrel a ha
      simpa [hH, hT, (chartAt ℂ x).left_inv (hAx ha), Complex.conj_conj] using this
    have key := s82cmp_lintegral_pullback_norm (F := fun y => U ((chartAt ℂ ŷ).symm (conj y))) hAm hd hHinj
      (qq := fun y => Q ŷ (conj y)) (rr := r x) hrel'
    have e2 : ∀ y, φ (conj y) = U ((chartAt ℂ ŷ).symm (conj y)) * ENNReal.ofReal ‖Q ŷ (conj y)‖ := fun y => rfl
    simp_rw [e2]
    rw [key]
    refine setLIntegral_congr_fun hAm fun w hw => ?_
    obtain ⟨a, ha, rfl⟩ := hw
    simp only [hH, hT, Complex.conj_conj, (chartAt ℂ x).left_inv (hAx ha)]
    rw [(chartAt ℂ ŷ).left_inv (hŷ ⟨a, ha, rfl⟩)]


set_option maxHeartbeats 1600000 in
/-- **Area relation on a reflected double (D3).**  `D` is the disjoint union of the open half `G(S)`, its mirror
image `J(G(S))` and the fixed set of `J` (a null set); `q` is the pull-back of `Q` through `G` and `‖Q‖` is
`J`-invariant.  Then `∬_D U dA_Q = 2 ∬_S (U ∘ G) dA_q` for every `J`-invariant `U`. -/
theorem s82cmp_double_area {S D : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [SecondCountableTopology S] [Nonempty S]
    [TopologicalSpace D] [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ) ω D] [T2Space D] [SecondCountableTopology D]
    {Jd : D ≃ₜ D} (hJ : IsAnticonformalInvolution Jd)
    (hJnull : ∀ x : D, volume (chartAt ℂ x '' ({p | Jd p = p} ∩ (chartAt ℂ x).source)) = 0)
    {G : S → D} (hGe : Topology.IsOpenEmbedding G) (hGh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hdisj : Disjoint (range G) (range (Jd ∘ G)))
    (hcover : range G ∪ range (Jd ∘ G) ∪ {x | Jd x = x} = univ)
    {Q : D → ℂ → ℂ} {q : S → ℂ → ℂ} (hQ : IsHolQuadDiff Q) (hq : IsHolQuadDiff q)
    (hD2a : ∀ a, q a (chartAt ℂ a a) = Q (G a) (chartAt ℂ (G a) (G a)) *
      deriv (fun v => chartAt ℂ (G a) (G ((chartAt ℂ a).symm v))) (chartAt ℂ a a) ^ 2)
    (hD2b : ∀ y, ‖Q y (chartAt ℂ y y)‖ = ‖Q (Jd y) (chartAt ℂ (Jd y) (Jd y))‖ *
      ‖deriv (fun v => conj (chartAt ℂ (Jd y) (Jd ((chartAt ℂ y).symm v)))) (chartAt ℂ y y)‖ ^ 2)
    (U : D → ℝ≥0∞) (hU : ∀ y, U (Jd y) = U y) :
    surfaceIntegral Q (fun y z => U ((chartAt ℂ y).symm z)) =
      2 * surfaceIntegral q (fun x z => U (G ((chartAt ℂ x).symm z))) := by
  classical
  set Z : Set D := {p | Jd p = p} with hZ
  have hGinj : Function.Injective G := hGe.isEmbedding.injective
  have hJinv : ∀ y, Jd (Jd y) = y := hJ.1
  haveI : Nonempty D := ⟨G (Classical.arbitrary S)⟩
  -- anticonformality of `Jd` in all charts
  have hJd : ∀ (x a : D) {z : ℂ}, z ∈ (chartAt ℂ x).target →
      Jd ((chartAt ℂ x).symm z) ∈ (chartAt ℂ a).source →
      DifferentiableAt ℂ (fun w => conj (chartAt ℂ a (Jd ((chartAt ℂ x).symm w)))) z := by
    intro x a z hz ha
    have := s31dc_coord_diff (Homeomorph.refl D) isBiholomorphic_id hJ x a hz (by simpa using ha)
    simpa using this
  -- the subordinate neighbourhoods
  let V : S → Set S := fun s => (G ⁻¹' (chartAt ℂ (G s)).source) ∩
    ((Jd ∘ G) ⁻¹' (chartAt ℂ (Jd (G s))).source) ∩ (chartAt ℂ s).source
  have hVo : ∀ s, IsOpen (V s) := fun s =>
    (((chartAt ℂ (G s)).open_source.preimage hGe.continuous).inter
      ((chartAt ℂ (Jd (G s))).open_source.preimage (Jd.continuous.comp hGe.continuous))).inter
      (chartAt ℂ s).open_source
  have hVp : ∀ s, s ∈ V s := fun s => ⟨⟨mem_chart_source ℂ (G s), mem_chart_source ℂ (Jd (G s))⟩,
    mem_chart_source ℂ s⟩
  obtain ⟨x, P, hP, hPV⟩ := s82cmp_exists_chartPartition V hVo hVp (fun s => inter_subset_right)
  obtain ⟨x2, P2, hP2, -⟩ := s82cmp_exists_chartPartition (fun p : D => (chartAt ℂ p).source)
    (fun p => (chartAt ℂ p).open_source) (fun p => mem_chart_source ℂ p) (fun _ => subset_rfl)
  have hPx : ∀ i, P i ⊆ (chartAt ℂ (x i)).source := fun i => (hP.1 i).1
  have hPm : ∀ i, MeasurableSet (chartAt ℂ (x i) '' P i) := fun i => (hP.1 i).2
  have hGs : ∀ i, ∀ a ∈ P i, G a ∈ (chartAt ℂ (G (x i))).source := fun i a ha => (hPV i ha).1.1
  have hJs : ∀ i, ∀ a ∈ P i, Jd (G a) ∈ (chartAt ℂ (Jd (G (x i)))).source := fun i a ha => (hPV i ha).1.2
  -- the pieces over the half
  have hpiece : ∀ i, MeasurableSet (chartAt ℂ (G (x i)) '' (G '' P i)) ∧
      ∫⁻ z in chartAt ℂ (G (x i)) '' (G '' P i), U ((chartAt ℂ (G (x i))).symm z) *
          ENNReal.ofReal ‖Q (G (x i)) z‖ =
        ∫⁻ w in chartAt ℂ (x i) '' P i, U (G ((chartAt ℂ (x i)).symm w)) * ENNReal.ofReal ‖q (x i) w‖ := by
    intro i
    refine s82cmp_piece_hol (hPx i) (hPm i) (fun a _ => hGh a) (hGinj.injOn) ?_ ?_ U
    · rintro _ ⟨a, ha, rfl⟩
      exact hGs i a ha
    · intro a ha
      exact s82cmp_chart_change hq hQ (hGh a) (hD2a a) (hPx i ha) (hGs i a ha)
  have hJpiece : ∀ i, MeasurableSet (chartAt ℂ (Jd (G (x i))) '' (Jd '' (G '' P i))) ∧
      ∫⁻ z in chartAt ℂ (Jd (G (x i))) '' (Jd '' (G '' P i)), U ((chartAt ℂ (Jd (G (x i)))).symm z) *
          ENNReal.ofReal ‖Q (Jd (G (x i))) z‖ =
        ∫⁻ w in chartAt ℂ (x i) '' P i, U (G ((chartAt ℂ (x i)).symm w)) * ENNReal.ofReal ‖q (x i) w‖ := by
    intro i
    obtain ⟨hmA, hintA⟩ := hpiece i
    have hAx : G '' P i ⊆ (chartAt ℂ (G (x i))).source := by
      rintro _ ⟨a, ha, rfl⟩; exact hGs i a ha
    have hŷ : Jd '' (G '' P i) ⊆ (chartAt ℂ (Jd (G (x i)))).source := by
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩; exact hJs i a ha
    have hda : ∀ (c : D) (ŷ : D) (b : D), b ∈ (chartAt ℂ c).source → Jd b ∈ (chartAt ℂ ŷ).source →
        DifferentiableAt ℂ (fun w => conj (chartAt ℂ ŷ (Jd ((chartAt ℂ c).symm w)))) (chartAt ℂ c b) := by
      intro c ŷ b hb hjb
      refine hJd c ŷ ((chartAt ℂ c).map_source hb) ?_
      rw [(chartAt ℂ c).left_inv hb]; exact hjb
    obtain ⟨hmJ, hintJ⟩ := s82cmp_piece_anti (Φ := Jd) (r := Q) (Q := Q) hAx hmA
      (fun b hb => hda _ _ b (hAx hb) (hŷ ⟨b, hb, rfl⟩)) Jd.injective.injOn hŷ
      (fun b hb => s82cmp_chart_change_anti hQ hQ Jd.continuous.continuousAt
        (fun c ŷ hc hy => hda c ŷ b hc hy) (hD2b b) (hAx hb) (hŷ ⟨b, hb, rfl⟩)) U
    refine ⟨hmJ, ?_⟩
    rw [hintJ]
    simp_rw [hU]
    exact hintA
  -- the fixed set misses the open halves
  have hZO1 : Z ∩ range G = ∅ := by
    ext p
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hp ⟨s, hs⟩
    have hp' : Jd p = p := hp
    refine Set.disjoint_left.1 hdisj ⟨s, hs⟩ ⟨s, ?_⟩
    simp only [Function.comp_apply, hs, hp']
  have hZO2 : Z ∩ range (Jd ∘ G) = ∅ := by
    ext p
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hp ⟨s, hs⟩
    have hp' : Jd p = p := hp
    refine Set.disjoint_left.1 hdisj ⟨s, ?_⟩ ⟨s, hs⟩
    have h1 : Jd (Jd (G s)) = G s := hJinv _
    simp only [Function.comp_apply] at hs
    rw [hs, hp'] at h1
    exact h1.symm
  have hO1 : IsOpen (range G) := hGe.isOpen_range
  have hO2 : IsOpen (range (Jd ∘ G)) := (Jd.isOpenEmbedding.comp hGe).isOpen_range
  -- the index type and the lifted partition
  obtain ⟨hden⟩ := nonempty_denumerable (ℕ ⊕ ℕ ⊕ ℕ)
  letI := hden
  let e : (ℕ ⊕ ℕ ⊕ ℕ) ≃ ℕ := Denumerable.eqv _
  let xh : (ℕ ⊕ ℕ ⊕ ℕ) → D :=
    Sum.elim (fun i => G (x i)) (Sum.elim (fun i => Jd (G (x i))) (fun k => x2 k))
  let Ph : (ℕ ⊕ ℕ ⊕ ℕ) → Set D :=
    Sum.elim (fun i => G '' P i) (Sum.elim (fun i => Jd '' (G '' P i)) (fun k => P2 k ∩ Z))
  have hP2src : ∀ k, P2 k ⊆ (chartAt ℂ (x2 k)).source := fun k => (hP2.1 k).1
  have hZmeas : ∀ k, MeasurableSet (chartAt ℂ (x2 k) '' (P2 k ∩ Z)) := by
    intro k
    set φ := chartAt ℂ (x2 k) with hφ
    have hW : IsOpen (φ '' ((range G ∪ range (Jd ∘ G)) ∩ φ.source)) :=
      φ.isOpen_image_of_subset_source ((hO1.union hO2).inter φ.open_source) inter_subset_right
    have hZe : P2 k ∩ Z = P2 k \ (range G ∪ range (Jd ∘ G)) := by
      ext y
      constructor
      · rintro ⟨hyP, hyZ⟩
        refine ⟨hyP, fun hy => ?_⟩
        rcases hy with hy | hy
        · exact (eq_empty_iff_forall_notMem.1 hZO1) y ⟨hyZ, hy⟩
        · exact (eq_empty_iff_forall_notMem.1 hZO2) y ⟨hyZ, hy⟩
      · rintro ⟨hyP, hy⟩
        have hyc : y ∈ range G ∪ range (Jd ∘ G) ∪ Z := by rw [hcover]; trivial
        rcases hyc with hyc | hyc
        · exact absurd hyc hy
        · exact ⟨hyP, hyc⟩
    have himg : φ '' (P2 k ∩ Z) = φ '' P2 k \ φ '' ((range G ∪ range (Jd ∘ G)) ∩ φ.source) := by
      rw [hZe]
      ext z
      constructor
      · rintro ⟨y, ⟨hyP, hyO⟩, rfl⟩
        refine ⟨⟨y, hyP, rfl⟩, ?_⟩
        rintro ⟨y', ⟨hy'O, hy's⟩, hy'e⟩
        have := φ.injOn hy's (hP2src k hyP) hy'e
        subst this
        exact hyO hy'O
      · rintro ⟨⟨y, hyP, rfl⟩, hnot⟩
        exact ⟨y, ⟨hyP, fun hO => hnot ⟨y, ⟨hO, hP2src k hyP⟩, rfl⟩⟩, rfl⟩
    rw [himg]
    exact (hP2.1 k).2.diff hW.measurableSet
  have hZnull : ∀ k, volume (chartAt ℂ (x2 k) '' (P2 k ∩ Z)) = 0 := fun k =>
    measure_mono_null (image_mono (s := P2 k ∩ Z) (t := Z ∩ (chartAt ℂ (x2 k)).source)
      (fun y hy => ⟨hy.2, hP2src k hy.1⟩)) (hJnull (x2 k))
  have hPh_sub : ∀ j, Ph j ⊆ (chartAt ℂ (xh j)).source := by
    rintro (i | i | k)
    · rintro _ ⟨a, ha, rfl⟩; exact hGs i a ha
    · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩; exact hJs i a ha
    · exact inter_subset_left.trans (hP2src k)
  have hPh_meas : ∀ j, MeasurableSet (chartAt ℂ (xh j) '' Ph j) := by
    rintro (i | i | k)
    · exact (hpiece i).1
    · exact (hJpiece i).1
    · exact hZmeas k
  have hPh_disj : Pairwise (fun j j' => Disjoint (Ph j) (Ph j')) := by
    rintro (i | i | k) (j | j | l) hne
    · have hij : i ≠ j := fun h => hne (by rw [h])
      show Disjoint (G '' P i) (G '' P j)
      exact (Set.disjoint_image_iff hGinj).2 (hP.2.1 hij)
    · show Disjoint (G '' P i) (Jd '' (G '' P j))
      refine Set.disjoint_left.2 fun y hy hy' => ?_
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨_, ⟨b, hb, rfl⟩, hbb⟩ := hy'
      exact Set.disjoint_left.1 hdisj ⟨a, rfl⟩ ⟨b, hbb⟩
    · show Disjoint (G '' P i) (P2 l ∩ Z)
      refine Set.disjoint_left.2 fun y hy hy' => ?_
      obtain ⟨a, ha, rfl⟩ := hy
      exact (eq_empty_iff_forall_notMem.1 hZO1) _ ⟨hy'.2, ⟨a, rfl⟩⟩
    · show Disjoint (Jd '' (G '' P i)) (G '' P j)
      refine Set.disjoint_left.2 fun y hy hy' => ?_
      obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hy
      obtain ⟨b, hb, hbb⟩ := hy'
      exact Set.disjoint_left.1 hdisj ⟨b, hbb⟩ ⟨a, rfl⟩
    · have hij : i ≠ j := fun h => hne (by rw [h])
      show Disjoint (Jd '' (G '' P i)) (Jd '' (G '' P j))
      exact (Set.disjoint_image_iff Jd.injective).2 ((Set.disjoint_image_iff hGinj).2 (hP.2.1 hij))
    · show Disjoint (Jd '' (G '' P i)) (P2 l ∩ Z)
      refine Set.disjoint_left.2 fun y hy hy' => ?_
      obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hy
      exact (eq_empty_iff_forall_notMem.1 hZO2) _ ⟨hy'.2, ⟨a, rfl⟩⟩
    · show Disjoint (P2 k ∩ Z) (G '' P j)
      refine Set.disjoint_left.2 fun y hy hy' => ?_
      obtain ⟨a, ha, rfl⟩ := hy'
      exact (eq_empty_iff_forall_notMem.1 hZO1) _ ⟨hy.2, ⟨a, rfl⟩⟩
    · show Disjoint (P2 k ∩ Z) (Jd '' (G '' P j))
      refine Set.disjoint_left.2 fun y hy hy' => ?_
      obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hy'
      exact (eq_empty_iff_forall_notMem.1 hZO2) _ ⟨hy.2, ⟨a, rfl⟩⟩
    · have hkl : k ≠ l := fun h => hne (by rw [h])
      show Disjoint (P2 k ∩ Z) (P2 l ∩ Z)
      exact (hP2.2.1 hkl).mono inter_subset_left inter_subset_left
  have hPh_cover : (⋃ j, Ph j) = Set.univ := by
    rw [eq_univ_iff_forall]
    intro y
    have hyc : y ∈ range G ∪ range (Jd ∘ G) ∪ Z := by rw [hcover]; trivial
    rcases hyc with (⟨s, rfl⟩ | ⟨s, rfl⟩) | hyZ
    · obtain ⟨i, hi⟩ := mem_iUnion.1 (hP.2.2.symm ▸ mem_univ s : s ∈ ⋃ i, P i)
      exact mem_iUnion.2 ⟨Sum.inl i, ⟨s, hi, rfl⟩⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.1 (hP.2.2.symm ▸ mem_univ s : s ∈ ⋃ i, P i)
      exact mem_iUnion.2 ⟨Sum.inr (Sum.inl i), ⟨G s, ⟨s, hi, rfl⟩, rfl⟩⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.1 (hP2.2.2.symm ▸ mem_univ y : y ∈ ⋃ k, P2 k)
      exact mem_iUnion.2 ⟨Sum.inr (Sum.inr k), ⟨hk, hyZ⟩⟩
  have hPart : IsChartPartition D (fun n => xh (e.symm n)) (fun n => Ph (e.symm n)) := by
    refine ⟨fun n => ⟨hPh_sub _, hPh_meas _⟩, fun n m hnm => hPh_disj ?_, ?_⟩
    · intro h; exact hnm (e.symm.injective h)
    · rw [← hPh_cover]
      ext y
      simp only [mem_iUnion]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨e.symm n, hn⟩
      · rintro ⟨j, hj⟩
        exact ⟨e j, by simpa using hj⟩
  rw [s26v_surfaceIntegral_eq_tsum hQ U hPart, s26v_surfaceIntegral_eq_tsum hq (fun p => U (G p)) hP]
  set Gf : (ℕ ⊕ ℕ ⊕ ℕ) → ℝ≥0∞ := fun j =>
    ∫⁻ z in chartAt ℂ (xh j) '' Ph j, U ((chartAt ℂ (xh j)).symm z) * ENNReal.ofReal ‖Q (xh j) z‖ with hGf
  have hre : ∑' n, Gf (e.symm n) = ∑' j, Gf j := e.symm.tsum_eq Gf
  have hGn : (∑' n, ∫⁻ z in chartAt ℂ (xh (e.symm n)) '' Ph (e.symm n),
      U ((chartAt ℂ (xh (e.symm n))).symm z) * ENNReal.ofReal ‖Q (xh (e.symm n)) z‖) =
      ∑' n, Gf (e.symm n) := rfl
  rw [hGn, hre]
  have hsplit1 : ∑' j, Gf j = ∑' i, Gf (Sum.inl i) + ∑' j : ℕ ⊕ ℕ, Gf (Sum.inr j) :=
    (ENNReal.summable.hasSum (f := fun i => Gf (Sum.inl i))).sum
      (ENNReal.summable.hasSum (f := fun j : ℕ ⊕ ℕ => Gf (Sum.inr j))) |>.tsum_eq
  have hsplit2 : ∑' j : ℕ ⊕ ℕ, Gf (Sum.inr j) =
      ∑' i, Gf (Sum.inr (Sum.inl i)) + ∑' k, Gf (Sum.inr (Sum.inr k)) :=
    (ENNReal.summable.hasSum (f := fun i => Gf (Sum.inr (Sum.inl i)))).sum
      (ENNReal.summable.hasSum (f := fun k => Gf (Sum.inr (Sum.inr k)))) |>.tsum_eq
  have hzero : ∑' k, Gf (Sum.inr (Sum.inr k)) = 0 := by
    refine ENNReal.tsum_eq_zero.2 fun k => ?_
    exact setLIntegral_measure_zero _ _ (hZnull k)
  have hA : ∀ i, Gf (Sum.inl i) = ∫⁻ w in chartAt ℂ (x i) '' P i,
      U (G ((chartAt ℂ (x i)).symm w)) * ENNReal.ofReal ‖q (x i) w‖ := fun i => (hpiece i).2
  have hB : ∀ i, Gf (Sum.inr (Sum.inl i)) = ∫⁻ w in chartAt ℂ (x i) '' P i,
      U (G ((chartAt ℂ (x i)).symm w)) * ENNReal.ofReal ‖q (x i) w‖ := fun i => (hJpiece i).2
  rw [hsplit1, hsplit2, hzero, add_zero]
  simp_rw [hA, hB]
  rw [← two_mul]


section
variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
  [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

/-- **The comparison inequality for surfaces with boundary (`m ≠ 0`)**: lift to the Schottky doubles, apply the
case `m = 0` to the punctured doubles and descend through the reflection. -/
theorem s82cmp_core_boundary {g n m : ℕ} (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (Y : FiniteTypeRS.{u} g n m)
    (a : S₀ ≃ₜ Y.carrier) (ha : IsQCRS a) {h : S₀ ≃ₜ Y.carrier} {r : S₀ → ℂ → ℂ}
    {r' : Y.carrier → ℂ → ℂ} {k : ℝ} (hh : IsAdmissibleTeichmullerMap F₀ h r r' k) (hk : 0 < k)
    (hhom : ContinuousMap.Homotopic (h : C(S₀, Y.carrier)) (a : C(S₀, Y.carrier))) :
    quadDiffNorm r < ⊤ ∧ (quadDiffNorm r = 1 → maxDilatationRS h ≤ surfaceIntegral r
      (fun x z => ENNReal.ofReal (dilatationQuotient (localMapExprAt a x z) z))) := by
  classical
  haveI : Nonempty S₀ := ConnectedSpace.toNonempty
  haveI : Nonempty Y.carrier := ConnectedSpace.toNonempty
  haveI : SecondCountableTopology F₀.X.carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ℂ F₀.X.carrier
  haveI : SecondCountableTopology S₀ := F₀.embedding.isEmbedding.secondCountableTopology
  obtain ⟨Xd₀, J₀, ιd₀, Pd₀, hd₀⟩ := exists_schottkyDouble hm F₀
  obtain ⟨Xd₁, J₁, ιd₁, Pd₁, hd₁⟩ := exists_schottkyDouble hm Y.structure'
  haveI c0 : ConnectedSpace (puncturedOpens Pd₀) := s31hy_connected_punctured Pd₀
  haveI c1 : ConnectedSpace (puncturedOpens Pd₁) := s31hy_connected_punctured Pd₁
  haveI : SecondCountableTopology Xd₀.carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ℂ Xd₀.carrier
  obtain ⟨Fd₀⟩ := s31dm_punctured_fts Pd₀ hd₀.genus hd₀.card_Pd
  obtain ⟨Fd₁⟩ := s31dm_punctured_fts Pd₁ hd₁.genus hd₁.card_Pd
  have hexd := s82cmp_hex_double hm hex
  obtain ⟨fd, hfd, hfdqc, -⟩ := s32w_symmetric_extension hm F₀ Y.structure' hd₀ hd₁ h hh.2.qc
  obtain ⟨fda, hfda, hfdaqc, -⟩ := s32w_symmetric_extension hm F₀ Y.structure' hd₀ hd₁ a ha
  obtain ⟨fdp, fdpa, hfdp, hfdpa, hqcp, hqcpa, hhomd⟩ :=
    s32w_symm_ext_punctured hm hex F₀ Y.structure' hd₀ hd₁ hh.2.qc ha hfd hfda hfdqc hfdaqc hhom
  -- the halves in the punctured doubles
  have hr0 := s32w_double_range_off_Pd F₀ hd₀
  have hr1 := s32w_double_range_off_Pd Y.structure' hd₁
  let G₀ : C(S₀, puncturedOpens Pd₀) :=
    ⟨fun x => ⟨ιd₀ x, hr0 x⟩, Continuous.subtype_mk hd₀.embedding.continuous _⟩
  let G₁ : C(Y.carrier, puncturedOpens Pd₁) :=
    ⟨fun x => ⟨ιd₁ x, hr1 x⟩, Continuous.subtype_mk hd₁.embedding.continuous _⟩
  have hG₀ : ∀ x, (G₀ x : Xd₀.carrier) = ιd₀ x := fun x => rfl
  have hG₁ : ∀ x, (G₁ x : Xd₁.carrier) = ιd₁ x := fun x => rfl
  obtain ⟨hG₀e, hG₀h⟩ := s82cmp_punct_embedding Pd₀ hd₀.embedding hd₀.holomorphic G₀ hG₀
  obtain ⟨hG₁e, hG₁h⟩ := s82cmp_punct_embedding Pd₁ hd₁.embedding hd₁.holomorphic G₁ hG₁
  obtain ⟨Jd₀, hJd₀⟩ := s82cmp_punct_J Pd₀ J₀ hd₀.involution.1 hd₀.Pd_invariant
  obtain ⟨Jd₁, hJd₁⟩ := s82cmp_punct_J Pd₁ J₁ hd₁.involution.1 hd₁.Pd_invariant
  have hJa₀ : IsAnticonformalInvolution Jd₀ := s82cmp_opens_involution _ hd₀.involution Jd₀ hJd₀
  have hJa₁ : IsAnticonformalInvolution Jd₁ := s82cmp_opens_involution _ hd₁.involution Jd₁ hJd₁
  obtain ⟨Q, Q', hQadm, hD2a, hD2b⟩ :=
    s32w_double_teichmuller hm hex F₀ Y.structure' hd₀ hd₁ Fd₀ hh hk hfd hfdqc hfdp Jd₀ hJd₀ G₀ hG₀
  have hQ : IsHolQuadDiff Q := hQadm.2.initial
  have hq : IsHolQuadDiff r := hh.2.initial
  -- pointwise forms of the two relations
  have hD2a' : ∀ x, r x (chartAt ℂ x x) = Q (G₀ x) (chartAt ℂ (G₀ x) (G₀ x)) *
      deriv (fun v => chartAt ℂ (G₀ x) (G₀ ((chartAt ℂ x).symm v))) (chartAt ℂ x x) ^ 2 := by
    intro x
    have hmem : chartAt ℂ x x ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    have := congrFun (hD2a x) (chartAt ℂ x x)
    rw [Set.indicator_of_mem hmem, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at this
    exact this
  have hD2b' : ∀ y, ‖Q y (chartAt ℂ y y)‖ = ‖Q (Jd₀ y) (chartAt ℂ (Jd₀ y) (Jd₀ y))‖ *
      ‖deriv (fun v => conj (chartAt ℂ (Jd₀ y) (Jd₀ ((chartAt ℂ y).symm v)))) (chartAt ℂ y y)‖ ^ 2 := by
    intro y
    have hmem : chartAt ℂ y y ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source (mem_chart_source ℂ y)
    have := hD2b y (chartAt ℂ y y) hmem
    rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)] at this
    rw [this, norm_mul, Complex.norm_conj, norm_pow]
  -- the geometry of the double
  have hdisj : Disjoint (range G₀) (range (Jd₀ ∘ G₀)) := by
    rw [Set.disjoint_left]
    rintro y ⟨s, rfl⟩ ⟨s', hs'⟩
    refine Set.disjoint_left.1 hd₀.disjoint ⟨s, rfl⟩ ⟨s', ?_⟩
    have := congrArg Subtype.val hs'
    simpa [hJd₀, hG₀] using this
  have hcover : range G₀ ∪ range (Jd₀ ∘ G₀) ∪ {x | Jd₀ x = x} = univ := by
    rw [eq_univ_iff_forall]
    intro y
    have hy : y.1 ∈ range ιd₀ ∪ range (J₀ ∘ ιd₀) ∪ {x | J₀ x = x} ∪ (↑Pd₀ : Set Xd₀.carrier) := by
      rw [hd₀.cover]; trivial
    rcases hy with ((⟨s, hs⟩ | ⟨s, hs⟩) | hy) | hy
    · left; left; exact ⟨s, Subtype.ext hs⟩
    · left; right; exact ⟨s, Subtype.ext (by simpa [hJd₀, hG₀] using hs)⟩
    · right; exact Subtype.ext (by rw [hJd₀]; exact hy)
    · exact absurd hy y.2
  have hJnull : ∀ x : puncturedOpens Pd₀,
      volume (chartAt ℂ x '' ({p | Jd₀ p = p} ∩ (chartAt ℂ x).source)) = 0 := by
    intro x
    refine measure_mono_null ?_ (s82cmp_fixed_null hd₀.involution (x : Xd₀.carrier))
    rintro _ ⟨p, ⟨hp, hps⟩, rfl⟩
    have hps' : (p : Xd₀.carrier) ∈ (chartAt ℂ (x : Xd₀.carrier)).source := by
      have h2 := hps
      rwa [show chartAt ℂ x = (chartAt ℂ (x : Xd₀.carrier)).subtypeRestr ⟨x⟩ from rfl,
        OpenPartialHomeomorph.subtypeRestr_source] at h2
    exact ⟨p.1, ⟨by simpa [hJd₀] using congrArg Subtype.val hp, hps'⟩, rfl⟩
  -- the area relation
  have hArea : ∀ U : puncturedOpens Pd₀ → ℝ≥0∞, (∀ y, U (Jd₀ y) = U y) →
      surfaceIntegral Q (fun y z => U ((chartAt ℂ y).symm z)) =
        2 * surfaceIntegral r (fun x z => U (G₀ ((chartAt ℂ x).symm z))) := fun U hU =>
    s82cmp_double_area hJa₀ hJnull hG₀e hG₀h hdisj hcover hQ hq hD2a' hD2b' U hU
  have hnormQ : quadDiffNorm Q = 2 * quadDiffNorm r := hArea (fun _ => 1) (fun _ => rfl)
  -- the target as a surface of finite type
  let Y' : FiniteTypeRS.{u} (2 * g + m - 1) (2 * n) 0 := ⟨puncturedOpens Pd₁, Fd₁⟩
  have hcore := s82cmp_core_zero hexd Fd₀ Y' fdpa hqcpa hQadm hk hhomd
  have hfin : quadDiffNorm r < ⊤ := by
    have h1 := hcore.1
    rw [hnormQ] at h1
    exact lt_of_le_of_lt (by
      calc quadDiffNorm r = 1 * quadDiffNorm r := (one_mul _).symm
        _ ≤ 2 * quadDiffNorm r := by gcongr; norm_num) h1
  refine ⟨hfin, fun hn1 => ?_⟩
  have hqn : quadDiffNorm Q = 2 := by rw [hnormQ, hn1, mul_one]
  have hc : (0 : ℝ) < 1 / 2 := by norm_num
  have hT2 := s29_e12_teichMap_smul hQadm.2 hc
  have hQ1 : IsAdmissibleTeichmullerMap Fd₀ fdp (((1 / 2 : ℝ) : ℂ) • Q) (((1 / 2 : ℝ) : ℂ) • Q') k := by
    refine ⟨?_, hT2⟩
    have e : (((1 / 2 : ℝ) : ℂ) • Q) = ((1 / 2 : ℝ) • Q) := by
      funext x z; simp [Complex.real_smul]
    rw [e]
    exact (admissibleQDInterior Fd₀).smul_mem _ hQadm.1
  have hnorm2 : quadDiffNorm (((1 / 2 : ℝ) : ℂ) • Q) = 1 := by
    rw [s82cmp_quadDiffNorm_smul Q hc, hqn, one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have himp := (s82cmp_core_zero hexd Fd₀ Y' fdpa hqcpa hQ1 hk hhomd).2 hnorm2
  -- the dilatation density
  set Uf : puncturedOpens Pd₀ → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (dilatationQuotient (localMapExpr fdpa y) (chartAt ℂ y y)) with hUf
  have hF : ∀ y, fdpa (Jd₀ y) = Jd₁ (fdpa y) := by
    intro y
    apply Subtype.ext
    rw [hfdpa, hJd₀, hJd₁, hfdpa]
    exact hfda.2 _
  have hUJ : ∀ y, Uf (Jd₀ y) = Uf y := by
    intro y
    simp only [hUf]
    rw [s82cmp_D_reflect hJa₀ hJa₁ fdpa hF y]
  have hUG : ∀ x, Uf (G₀ x) = ENNReal.ofReal (dilatationQuotient (localMapExpr a x) (chartAt ℂ x x)) := by
    intro x
    simp only [hUf]
    have hloc : ∀ (Z : Type u) [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z] (y : Z),
        ∃ e : OpenPartialHomeomorph Z Z, y ∈ e.source ∧ EqOn (id : Z → Z) e e.source ∧
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target := by
      intro Z _ _ _ y
      exact ⟨OpenPartialHomeomorph.refl Z, trivial, fun _ _ => rfl, by simpa using mdifferentiableOn_id⟩
    rw [s82cmp_D_lift (pr₀ := (id : puncturedOpens Pd₀ → puncturedOpens Pd₀))
      (pr₁ := (id : puncturedOpens Pd₁ → puncturedOpens Pd₁)) hG₀e hG₀h hG₁e hG₁h continuous_id continuous_id
      (fun y _ => hloc _ y) (fun y _ => hloc _ y) (a := a) (f' := fdpa) fdpa.continuous
      (fun y s hs => by
        subst hs
        apply Subtype.ext
        show (fdpa (G₀ s) : Xd₁.carrier) = (G₁ (a s) : Xd₁.carrier)
        rw [hfdpa]
        exact hfda.1 s) (y := G₀ x) (s := x) rfl]
  -- assemble
  have hmax : maxDilatationRS h = maxDilatationRS fdp := by
    rw [(teichmullerMap_beltrami hh.2).2, (teichmullerMap_beltrami hQadm.2).2]
  rw [s82cmp_surfaceIntegral_Dil fdpa, s82cmp_surfaceIntegral_smul Q _ hc] at himp
  have hA := hArea Uf hUJ
  have hRHS : surfaceIntegral r (fun x z => ENNReal.ofReal (dilatationQuotient (localMapExprAt a x z) z)) =
      surfaceIntegral r (fun x z => Uf (G₀ ((chartAt ℂ x).symm z))) := by
    rw [s82cmp_surfaceIntegral_Dil a r]
    simp_rw [hUG]
  rw [hmax, hRHS]
  refine himp.trans (le_of_eq ?_)
  show ENNReal.ofReal (1 / 2) * surfaceIntegral Q (fun y z => Uf ((chartAt ℂ y).symm z)) = _
  rw [hA, ← mul_assoc, one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

end

end LiZhongQC
