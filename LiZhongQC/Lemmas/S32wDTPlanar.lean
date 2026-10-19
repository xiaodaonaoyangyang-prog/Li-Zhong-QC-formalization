import LiZhongQC.Lemmas.S32wDTTeich
import LiZhongQC.Lemmas.S32wSeamCoordinate
import LiZhongQC.Lemmas.FiniteTypeTeichData

open Complex Set Metric Filter Topology MeasureTheory
open scoped ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u v w

section Planar

/-- Two analytic parameters related by `ζ₂ ∘ v = ε · ζ₁ ∘ u` give a holomorphic composite `v ∘ u⁻¹`. -/
theorem s32w_dt_local_hol {ζ₁ ζ₂ u v uinv : ℂ → ℂ} {c a₁ a₂ ε : ℂ}
    (hζ₁ : AnalyticAt ℂ ζ₁ a₁) (hζ₂ : AnalyticAt ℂ ζ₂ a₂) (hζ₂d : deriv ζ₂ a₂ ≠ 0)
    (hu : u c = a₁) (hv : v c = a₂)
    (hrel : ∀ᶠ z in 𝓝 c, ζ₂ (v z) = ε * ζ₁ (u z)) (hvc : ContinuousAt v c)
    (huinv : ContinuousAt uinv a₁) (huinv0 : uinv a₁ = c) (huu : ∀ᶠ w in 𝓝 a₁, u (uinv w) = w) :
    DifferentiableAt ℂ (fun w => v (uinv w)) a₁ := by
  have hs : HasStrictDerivAt ζ₂ (deriv ζ₂ a₂) a₂ := hζ₂.hasStrictDerivAt
  set g := hs.localInverse ζ₂ (deriv ζ₂ a₂) a₂ hζ₂d with hg
  have hleft : ∀ᶠ x in 𝓝 a₂, g (ζ₂ x) = x := hs.eventually_left_inverse hζ₂d
  have hgd : HasStrictDerivAt g (deriv ζ₂ a₂)⁻¹ (ζ₂ a₂) := hs.to_localInverse hζ₂d
  have hc0 : ζ₂ a₂ = ε * ζ₁ a₁ := by
    have := hrel.self_of_nhds
    rwa [hv, hu] at this
  have hvu : ContinuousAt (fun w => v (uinv w)) a₁ := by
    have h1 : ContinuousAt v (uinv a₁) := by rw [huinv0]; exact hvc
    exact h1.comp huinv
  have hvu0 : v (uinv a₁) = a₂ := by rw [huinv0, hv]
  have e1 : ∀ᶠ w in 𝓝 a₁, g (ζ₂ (v (uinv w))) = v (uinv w) := by
    have := hvu.tendsto
    rw [hvu0] at this
    exact this.eventually hleft
  have e2 : ∀ᶠ w in 𝓝 a₁, ζ₂ (v (uinv w)) = ε * ζ₁ (u (uinv w)) := by
    have := huinv.tendsto
    rw [huinv0] at this
    exact this.eventually hrel
  have hev : (fun w => v (uinv w)) =ᶠ[𝓝 a₁] fun w => g (ε * ζ₁ w) := by
    filter_upwards [e1, e2, huu] with w h1 h2 h3
    rw [← h1, h2, h3]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have hζ1d : DifferentiableAt ℂ (fun w => ε * ζ₁ w) a₁ := (hζ₁.differentiableAt).const_mul ε
  have hgd' : DifferentiableAt ℂ g (ε * ζ₁ a₁) := by rw [← hc0]; exact hgd.hasDerivAt.differentiableAt
  exact hgd'.comp a₁ hζ1d

/-- A `K`-quasiconformal map which is holomorphic on an open set of full measure is conformal (`1`-q.c.). -/
theorem s32w_dt_one_qc_of_hol_ae {f : ℂ → ℂ} {D U : Set ℂ} {K : ℝ} (hf : IsKQC f D K)
    (hU : IsOpen U) (hUD : U ⊆ D) (hnull : volume (D \ U) = 0)
    (hhol : ∀ z ∈ U, DifferentiableAt ℂ f z) : IsKQC f D 1 := by
  have _hU := hU
  have _hUD := hUD
  refine (thm10_1_isKQC_iff hf.1 le_rfl hf.2.2.1).2 ⟨thm9_1_isACL hf, ?_⟩
  have hae : ∀ᵐ z ∂(volume.restrict D), z ∈ U := by
    rw [ae_restrict_iff' hf.1.measurableSet]
    filter_upwards [(measure_eq_zero_iff_ae_notMem.1 hnull)] with z hz hzD
    by_contra hzU
    exact hz ⟨hzD, hzU⟩
  filter_upwards [hae] with z hz
  have hb : dzbar f z = 0 := ((cauchyRiemann_iff).1 (hhol z hz)).2
  rw [hb]
  simp

end Planar

/-- Natural parameters are unique up to sign. -/
theorem s32w_dt_nat_param_unique {ζ ζ' : ℂ → ℂ} {c : ℂ} (hζ : AnalyticAt ℂ ζ c)
    (hζ' : AnalyticAt ℂ ζ' c) (hsq : ∀ᶠ z in 𝓝 c, deriv ζ z ^ 2 = deriv ζ' z ^ 2) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∀ᶠ z in 𝓝 c, ζ z - ζ c = ε * (ζ' z - ζ' c) := by
  have hA : AnalyticAt ℂ (fun z => deriv ζ z - deriv ζ' z) c := hζ.deriv.sub hζ'.deriv
  have hB : AnalyticAt ℂ (fun z => deriv ζ z + deriv ζ' z) c := hζ.deriv.add hζ'.deriv
  have hab : ∀ᶠ z in 𝓝 c, (deriv ζ z - deriv ζ' z) * (deriv ζ z + deriv ζ' z) = 0 :=
    hsq.mono fun z h => by linear_combination h
  have hder : ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∀ᶠ z in 𝓝 c, deriv ζ z = ε * deriv ζ' z := by
    rcases hA.eventually_eq_zero_or_eventually_ne_zero with h1 | h1
    · refine ⟨1, Or.inl rfl, h1.mono fun z hz => ?_⟩
      linear_combination hz
    · rcases hB.eventually_eq_zero_or_eventually_ne_zero with h2 | h2
      · refine ⟨-1, Or.inr rfl, h2.mono fun z hz => ?_⟩
        linear_combination hz
      · exfalso
        have h3 : ∀ᶠ z in 𝓝[≠] c, False := by
          filter_upwards [h1, h2, hab.filter_mono nhdsWithin_le_nhds] with z a b h
          exact mul_ne_zero a b h
        exact (h3.exists).elim fun _ h => h
  obtain ⟨ε, hε, hd⟩ := hder
  refine ⟨ε, hε, ?_⟩
  have hev : ∀ᶠ z in 𝓝 c, AnalyticAt ℂ ζ z ∧ AnalyticAt ℂ ζ' z ∧ deriv ζ z = ε * deriv ζ' z :=
    (hζ.eventually_analyticAt.and (hζ'.eventually_analyticAt.and hd))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hdiff : DifferentiableOn ℂ (fun z => ζ z - ε * ζ' z) (ball c r) := fun z hz =>
    ((hball z hz).1.differentiableAt.sub ((hball z hz).2.1.differentiableAt.const_mul ε)).differentiableWithinAt
  have hconst : ∀ z ∈ ball c r, (fun z => ζ z - ε * ζ' z) z = (fun z => ζ z - ε * ζ' z) c := by
    intro z hz
    refine isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected hdiff
      (fun w hw => ?_) hz (mem_ball_self hr)
    have h1 := hball w hw
    have e : deriv (fun z => ζ z - ε * ζ' z) w = deriv ζ w - ε * deriv ζ' w :=
      deriv_sub h1.1.differentiableAt (h1.2.1.differentiableAt.const_mul ε) |>.trans
        (by rw [deriv_const_mul _ h1.2.1.differentiableAt])
    rw [e, h1.2.2]; simp
  filter_upwards [ball_mem_nhds c hr] with z hz
  have := hconst z hz
  simp only at this
  linear_combination this
/-- **(E-planar)** Two natural parameters of the same quadratic differential give conformally compatible
stretches, hence a holomorphic composite `v ∘ u⁻¹`. -/
theorem s32w_dt_E_planar {k : ℝ} {ζι ζh ζ₁ ζ₂ u v uinv : ℂ → ℂ} {c a₁ : ℂ}
    (hζι : AnalyticAt ℂ ζι c) (hζh : AnalyticAt ℂ ζh c) (hι0 : ζι c = 0) (hh0 : ζh c = 0)
    (hsq : ∀ᶠ z in 𝓝 c, deriv ζι z ^ 2 = deriv ζh z ^ 2)
    (hζ₁ : AnalyticAt ℂ ζ₁ a₁) (hζ₂ : AnalyticAt ℂ ζ₂ (v c)) (hζ₂d : deriv ζ₂ (v c) ≠ 0)
    (hu : u c = a₁) (hvc : ContinuousAt v c)
    (hrι : ∀ᶠ z in 𝓝 c, ζ₁ (u z) = teichStretch k (ζι z))
    (hrh : ∀ᶠ z in 𝓝 c, ζ₂ (v z) = teichStretch k (ζh z))
    (huinv : ContinuousAt uinv a₁) (huinv0 : uinv a₁ = c) (huu : ∀ᶠ w in 𝓝 a₁, u (uinv w) = w) :
    DifferentiableAt ℂ (fun w => v (uinv w)) a₁ := by
  obtain ⟨ε, hε, hev⟩ := s32w_dt_nat_param_unique hζh hζι (hsq.mono fun z h => h.symm)
  have hrel : ∀ᶠ z in 𝓝 c, ζ₂ (v z) = ε * ζ₁ (u z) := by
    filter_upwards [hev, hrι, hrh] with z h1 h2 h3
    rw [h3, h2, hh0, hι0, sub_zero, sub_zero] at *
    have := eq26_4 k ε hε 0 (ζι z)
    rw [h1]
    simpa [teichStretch] using this
  exact s32w_dt_local_hol hζ₁ hζ₂ hζ₂d hu rfl hrel hvc huinv huinv0 huu

/-- A local analytic inverse. -/
theorem s32w_dt_inv_exists {σ : ℂ → ℂ} {a : ℂ} (hσ : AnalyticAt ℂ σ a) (hσd : deriv σ a ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (σ a) ∧ g (σ a) = a ∧ (∀ᶠ z in 𝓝 a, g (σ z) = z) ∧
      deriv g (σ a) ≠ 0 := by
  have hs := hσ.hasStrictDerivAt
  set g := hs.localInverse σ _ a hσd with hg
  have hga : AnalyticAt ℂ g (σ a) := hσ.analyticAt_localInverse hσd
  have hright : ∀ᶠ w in 𝓝 (σ a), σ (g w) = w := hs.eventually_right_inverse hσd
  have hleft : ∀ᶠ z in 𝓝 a, g (σ z) = z := hs.eventually_left_inverse hσd
  have hg0 : g (σ a) = a := hleft.self_of_nhds
  refine ⟨g, hga, hg0, hleft, ?_⟩
  have h7 : deriv (σ ∘ g) (σ a) = deriv σ (g (σ a)) * deriv g (σ a) :=
    deriv_comp (σ a) (by rw [hg0]; exact hσ.differentiableAt) hga.differentiableAt
  have h8 : (σ ∘ g) =ᶠ[𝓝 (σ a)] id := hright
  rw [h8.deriv_eq, deriv_id] at h7
  exact right_ne_zero_of_mul_eq_one h7.symm

/-- **(Transfer)** A natural parameter of `q` pulled along an analytic `σ` with nonzero derivative gives a
natural parameter `ζ ∘ σ⁻¹` of `R` whenever `deriv ζ ^ 2 = R ∘ σ * (deriv σ) ^ 2`. -/
theorem s32w_dt_nat_transfer {ζ σ R : ℂ → ℂ} {a : ℂ} (hζ : AnalyticAt ℂ ζ a) (hσ : AnalyticAt ℂ σ a)
    (hσd : deriv σ a ≠ 0)
    (hF : ∀ᶠ z in 𝓝 a, deriv ζ z ^ 2 = R (σ z) * deriv σ z ^ 2) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (σ a) ∧ g (σ a) = a ∧ (∀ᶠ w in 𝓝 (σ a), σ (g w) = w) ∧
      (∀ᶠ z in 𝓝 a, g (σ z) = z) ∧ deriv g (σ a) ≠ 0 ∧ AnalyticAt ℂ (fun w => ζ (g w)) (σ a) ∧
      ∀ᶠ w in 𝓝 (σ a), deriv (fun w => ζ (g w)) w ^ 2 = R w := by
  have hs := hσ.hasStrictDerivAt
  set g := hs.localInverse σ _ a hσd with hg
  have hga : AnalyticAt ℂ g (σ a) := hσ.analyticAt_localInverse hσd
  have hright : ∀ᶠ w in 𝓝 (σ a), σ (g w) = w := hs.eventually_right_inverse hσd
  have hleft : ∀ᶠ z in 𝓝 a, g (σ z) = z := hs.eventually_left_inverse hσd
  have hg0 : g (σ a) = a := hleft.self_of_nhds
  have hdg : deriv g (σ a) ≠ 0 := by
    have h7 : deriv (σ ∘ g) (σ a) = deriv σ (g (σ a)) * deriv g (σ a) :=
      deriv_comp (σ a) (by rw [hg0]; exact hσ.differentiableAt) hga.differentiableAt
    have h8 : (σ ∘ g) =ᶠ[𝓝 (σ a)] id := hright
    rw [h8.deriv_eq, deriv_id] at h7
    exact right_ne_zero_of_mul_eq_one h7.symm
  refine ⟨g, hga, hg0, hright, hleft, hdg, hζ.comp_of_eq hga hg0, ?_⟩
  have hgt : Tendsto g (𝓝 (σ a)) (𝓝 a) := by
    have := hga.continuousAt.tendsto
    rwa [hg0] at this
  filter_upwards [hright, hright.eventually_nhds, hga.eventually_analyticAt,
    hgt.eventually hζ.eventually_analyticAt, hgt.eventually hσ.eventually_analyticAt, hgt.eventually hF]
    with w h1 h6 h2 h3 h4 h5
  have hd : deriv σ (g w) * deriv g w = 1 := by
    have h7 : deriv (σ ∘ g) w = deriv σ (g w) * deriv g w := deriv_comp w h4.differentiableAt h2.differentiableAt
    have h8 : (σ ∘ g) =ᶠ[𝓝 w] id := h6
    rw [← h7, h8.deriv_eq, deriv_id]
  have h9 : deriv (fun w => ζ (g w)) w = deriv ζ (g w) * deriv g w :=
    deriv_comp w h3.differentiableAt h2.differentiableAt
  rw [h9, mul_pow, h5, h1, mul_assoc, ← mul_pow, hd]
  simp

section Global

variable {Y : Type u} {Z : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] [TopologicalSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Y] [IsManifold 𝓘(ℂ) ω Z]

/-- **(Global)** A quasiconformal homeomorphism holomorphic on an open set whose complement is chartwise null
is biholomorphic. -/
theorem s32w_dt_biholo_of_hol_ae (c : Y ≃ₜ Z) (hc : IsQCRS c) (O : Set Y) (hO : IsOpen O)
    (hhol : ∀ y ∈ O, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) c y)
    (hnull : ∀ x : Y, volume ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Oᶜ) = 0) :
    IsBiholomorphic c := by
  obtain ⟨K, -, hK⟩ := hc
  refine (isKQCRS_one_iff c).1 ⟨le_rfl, fun x => ?_⟩
  have hD : IsOpen (localMapDomain c x) := s23_localMapDomain_isOpen c.continuous x
  have hU : IsOpen (localMapDomain c x ∩ (chartAt ℂ x).symm ⁻¹' O) := by
    have h1 : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' O) :=
      (chartAt ℂ x).isOpen_inter_preimage_symm hO
    have h2 : localMapDomain c x ∩ (chartAt ℂ x).symm ⁻¹' O =
        localMapDomain c x ∩ ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' O) := by
      ext z
      constructor
      · rintro ⟨hz, hzO⟩
        exact ⟨hz, hz.1, hzO⟩
      · rintro ⟨hz, -, hzO⟩
        exact ⟨hz, hzO⟩
    rw [h2]
    exact hD.inter h1
  refine s32w_dt_one_qc_of_hol_ae (hK x) hU inter_subset_left ?_ ?_
  · refine measure_mono_null (fun z hz => ?_) (hnull x)
    exact ⟨hz.1.1, fun h => hz.2 ⟨hz.1, h⟩⟩
  · intro z hz
    exact s31qr_coordinate_differentiable x (c x) hz.1.1 hz.1.2 (hhol _ hz.2)

end Global

section NullTransfer

variable {Y : Type u} {Z : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] [TopologicalSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Y] [IsManifold 𝓘(ℂ) ω Z] [SecondCountableTopology Z]

/-- A quasiconformal homeomorphism of surfaces maps chartwise null sets to chartwise null sets. -/
theorem s32w_dt_qc_null (ι : Y ≃ₜ Z) (hι : IsQCRS ι) {N : Set Y}
    (hN : ∀ x : Y, volume ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' N) = 0) (y : Z) :
    volume ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (ι '' N)) = 0 := by
  classical
  obtain ⟨K, -, hK⟩ := hι
  refine measure_null_of_locally_null _ (fun w hw => ?_)
  obtain ⟨hwt, p, hpN, hp⟩ := hw
  set C : Set Y := (chartAt ℂ p).source ∩ ι ⁻¹' (chartAt ℂ (ι p)).source with hC
  have hCo : IsOpen C := (chartAt ℂ p).open_source.inter
    (ι.continuous.isOpen_preimage _ (chartAt ℂ (ι p)).open_source)
  have hpC : p ∈ C := ⟨mem_chart_source ℂ p, mem_chart_source ℂ (ι p)⟩
  set V : Set ℂ := (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (ι '' C) with hV
  have hVo : IsOpen V := (chartAt ℂ y).isOpen_inter_preimage_symm (ι.isOpenMap _ hCo)
  have hwV : w ∈ V := ⟨hwt, p, hpC, hp⟩
  set S : Set ℂ := ((chartAt ℂ p).target ∩ (chartAt ℂ p).symm ⁻¹' N) ∩ localMapDomain ι p ∩
    (chartAt ℂ p).symm ⁻¹' (ι ⁻¹' (chartAt ℂ y).source) with hS
  have hSnull : volume S = 0 :=
    measure_mono_null (fun z hz => hz.1.1) (hN p)
  have hSD : S ⊆ localMapDomain ι p := fun z hz => hz.1.2
  have heS : volume (localMapExpr ι p '' S) = 0 := thm9_6_cor1_null (hK p) hSD hSnull
  set T : ℂ → ℂ := fun z => chartAt ℂ y ((chartAt ℂ (ι p)).symm z) with hT
  have hΩ : DifferentiableOn ℝ T (localMapExpr ι p '' S) := by
    rintro z ⟨z', hz', rfl⟩
    have h1 : ι ((chartAt ℂ p).symm z') ∈ (chartAt ℂ (ι p)).source := hz'.1.2.2
    have h2 : localMapExpr ι p z' ∈ (chartAt ℂ (ι p)).target := (chartAt ℂ (ι p)).map_source h1
    have h3 : (chartAt ℂ (ι p)).symm (localMapExpr ι p z') ∈ (chartAt ℂ y).source := by
      have : (chartAt ℂ (ι p)).symm (localMapExpr ι p z') = ι ((chartAt ℂ p).symm z') :=
        (chartAt ℂ (ι p)).left_inv h1
      rw [this]
      exact hz'.2
    exact ((s23_transition_differentiableAt y (ι p) h2 h3).restrictScalars ℝ).differentiableWithinAt
  have hu : volume (T '' (localMapExpr ι p '' S)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hΩ heS
  refine ⟨T '' (localMapExpr ι p '' S), ?_, hu⟩
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine ⟨V, hVo.mem_nhds hwV, ?_⟩
  rintro w' ⟨hw'V, hw'W⟩
  obtain ⟨hw't, p', hp'C, hp'⟩ := hw'V
  obtain ⟨-, q, hqN, hq⟩ := hw'W
  have hqp : q = p' := ι.injective (hq.trans hp'.symm)
  subst hqp
  have hqs : q ∈ (chartAt ℂ p).source := hp'C.1
  have hqι : ι q ∈ (chartAt ℂ (ι p)).source := hp'C.2
  have hz't : chartAt ℂ p q ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source hqs
  have hsymm : (chartAt ℂ p).symm (chartAt ℂ p q) = q := (chartAt ℂ p).left_inv hqs
  have hqy : ι q ∈ (chartAt ℂ y).source := by
    rw [hq]; exact (chartAt ℂ y).map_target hw't
  refine ⟨localMapExpr ι p (chartAt ℂ p q), ⟨chartAt ℂ p q, ⟨⟨⟨hz't, ?_⟩, hz't, ?_⟩, ?_⟩, rfl⟩, ?_⟩
  · show (chartAt ℂ p).symm (chartAt ℂ p q) ∈ N
    rw [hsymm]; exact hqN
  · show ι ((chartAt ℂ p).symm (chartAt ℂ p q)) ∈ (chartAt ℂ (ι p)).source
    rw [hsymm]; exact hqι
  · show ι ((chartAt ℂ p).symm (chartAt ℂ p q)) ∈ (chartAt ℂ y).source
    rw [hsymm]; exact hqy
  · show chartAt ℂ y ((chartAt ℂ (ι p)).symm (chartAt ℂ (ι p) (ι ((chartAt ℂ p).symm (chartAt ℂ p q))))) = w'
    rw [hsymm, (chartAt ℂ (ι p)).left_inv hqι, hq, (chartAt ℂ y).right_inv hw't]

end NullTransfer

section SeamNull

/-- The real line in `ℂ` is null. -/
theorem s32w_dt_real_line_null : volume {z : ℂ | z.im = 0} = 0 := by
  have h : {z : ℂ | z.im = 0} = ((LinearMap.ker Complex.imLm : Submodule ℝ ℂ) : Set ℂ) := by
    ext z; simp
  rw [h]
  refine Measure.addHaar_submodule volume _ (fun htop => ?_)
  have : Complex.I ∈ (LinearMap.ker Complex.imLm : Submodule ℝ ℂ) := by rw [htop]; trivial
  simp at this

/-- The fixed curves of the involution of a Schottky double are chartwise null. -/
theorem s32w_dt_seam_null {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    (x₀ : Xd.carrier) :
    volume ((chartAt ℂ x₀).target ∩ (chartAt ℂ x₀).symm ⁻¹' {y | J y = y}) = 0 := by
  classical
  refine measure_null_of_locally_null _ (fun z₀ hz₀ => ?_)
  obtain ⟨hz₀t, hz₀J⟩ := hz₀
  set y₀ := (chartAt ℂ x₀).symm z₀ with hy₀
  obtain ⟨κ, r, hr, hsrc, hκ0, hsym, -, -, -, hdiff, -⟩ := s32w_seam_coordinate F hd (p := y₀) hz₀J
  set W : Set Xd.carrier := (chartAt ℂ y₀).source ∩ (chartAt ℂ x₀).source with hW
  have hy₀W : y₀ ∈ W := ⟨mem_chart_source ℂ y₀, (chartAt ℂ x₀).map_target hz₀t⟩
  have hκc : ContinuousAt κ 0 := κ.continuousAt (hsrc (mem_ball_self hr))
  have hev : ∀ᶠ w in 𝓝 (0 : ℂ), κ w ∈ W := by
    refine hκc.preimage_mem_nhds ?_
    rw [hκ0]
    exact ((chartAt ℂ y₀).open_source.inter (chartAt ℂ x₀).open_source).mem_nhds hy₀W
  obtain ⟨r', hr', hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set r'' := min r r' with hr''
  have hr''0 : 0 < r'' := lt_min hr hr'
  have hb1 : ball (0 : ℂ) r'' ⊆ ball 0 r := ball_subset_ball (min_le_left _ _)
  have hb2 : ball (0 : ℂ) r'' ⊆ ball 0 r' := ball_subset_ball (min_le_right _ _)
  set θ : ℂ → ℂ := fun w => chartAt ℂ x₀ (κ w) with hθ
  have hθd : ∀ w ∈ ball (0 : ℂ) r'', DifferentiableAt ℂ θ w := by
    intro w hw
    have hwW := hball w (hb2 hw)
    have hd1 : DifferentiableAt ℂ (fun z => chartAt ℂ y₀ (κ z)) w :=
      (hdiff w (hb1 hw)).differentiableAt (isOpen_ball.mem_nhds (hb1 hw))
    have hmem : chartAt ℂ y₀ (κ w) ∈ (chartAt ℂ y₀).target := (chartAt ℂ y₀).map_source hwW.1
    have hmem2 : (chartAt ℂ y₀).symm (chartAt ℂ y₀ (κ w)) ∈ (chartAt ℂ x₀).source := by
      rw [(chartAt ℂ y₀).left_inv hwW.1]; exact hwW.2
    have hd2 := s23_transition_differentiableAt x₀ y₀ hmem hmem2
    have hd3 : DifferentiableAt ℂ (chartTransition x₀ y₀ ∘ fun z => chartAt ℂ y₀ (κ z)) w :=
      DifferentiableAt.comp (g := chartTransition x₀ y₀) w hd2 hd1
    refine hd3.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hw] with v hv
    have hvW := hball v (hb2 hv)
    show chartAt ℂ x₀ (κ v) = chartAt ℂ x₀ ((chartAt ℂ y₀).symm (chartAt ℂ y₀ (κ v)))
    rw [(chartAt ℂ y₀).left_inv hvW.1]
  set L : Set ℂ := ball (0 : ℂ) r'' ∩ {z : ℂ | z.im = 0} with hL
  have hLnull : volume L = 0 := measure_mono_null inter_subset_right s32w_dt_real_line_null
  have hu : volume (θ '' L) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun w hw => ((hθd w hw.1).restrictScalars ℝ).differentiableWithinAt) hLnull
  refine ⟨θ '' L, ?_, hu⟩
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  have hVo : IsOpen ((chartAt ℂ x₀).target ∩ (chartAt ℂ x₀).symm ⁻¹' (κ '' ball (0 : ℂ) r'')) :=
    (chartAt ℂ x₀).isOpen_inter_preimage_symm
      (κ.isOpen_image_of_subset_source isOpen_ball (fun w hw => hsrc (hb1 hw)))
  refine ⟨_, hVo.mem_nhds ⟨hz₀t, 0, mem_ball_self hr''0, hκ0⟩, ?_⟩
  rintro w' ⟨⟨hw't, ζ, hζ, hζy⟩, -, hw'J⟩
  have hJ : J (κ ζ) = κ ζ := by rw [hζy]; exact hw'J
  obtain ⟨hcb, hceq⟩ := hsym ζ (hb1 hζ)
  have hcz : conj ζ = ζ := κ.injOn (hsrc hcb) (hsrc (hb1 hζ)) (by rw [hceq, hJ])
  have him : ζ.im = 0 := by
    have := congrArg Complex.im hcz
    simp only [Complex.conj_im] at this
    linarith
  refine ⟨ζ, ⟨hζ, him⟩, ?_⟩
  show chartAt ℂ x₀ (κ ζ) = w'
  rw [hζy, (chartAt ℂ x₀).right_inv hw't]

end SeamNull

section ECore

variable {Y : Type u} {W : Type v} {Z : Type w} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [TopologicalSpace W] [ChartedSpace ℂ W] [TopologicalSpace Z] [ChartedSpace ℂ Z]
  [IsManifold 𝓘(ℂ) ω Y] [IsManifold 𝓘(ℂ) ω W] [IsManifold 𝓘(ℂ) ω Z]

/-- **(E-core)** If `Φ` carries a natural parameter of `Q` at a regular point `p` to a holomorphic parameter
by the same stretch as the Teichmüller map `ι`, then `ι⁻¹ ∘ Φ` is holomorphic at `ι p`. -/
theorem s32w_dt_E_core {Q : Y → ℂ → ℂ} {q₁ : W → ℂ → ℂ} {k : ℝ} (ι : Y ≃ₜ W) (Φ : Y ≃ₜ Z)
    (hι : IsTeichmullerMap ι Q q₁ k) {p : Y} (hp : IsRegularPoint Q p) {ζt ζ₂ : ℂ → ℂ}
    (hζt : IsNaturalParameterAt Q p ζt)
    (hζ₂ : AnalyticAt ℂ ζ₂ (localMapExpr Φ p (chartAt ℂ p p)))
    (hζ₂d : deriv ζ₂ (localMapExpr Φ p (chartAt ℂ p p)) ≠ 0)
    (hrel : ∀ᶠ z in 𝓝 (chartAt ℂ p p), ζ₂ (localMapExpr Φ p z) = teichStretch k (ζt z)) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (ι.symm.trans Φ : W → Z) (ι p) := by
  obtain ⟨-, ζι, ζ₁, hζι, hζ₁, hrι⟩ := hι.regular p hp
  have hpc : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hpt : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have hqc : (chartAt ℂ (ι p)).symm (chartAt ℂ (ι p) (ι p)) = ι p :=
    (chartAt ℂ (ι p)).left_inv (mem_chart_source ℂ (ι p))
  have hqt : chartAt ℂ (ι p) (ι p) ∈ (chartAt ℂ (ι p)).target :=
    (chartAt ℂ (ι p)).map_source (mem_chart_source ℂ (ι p))
  set uinv : ℂ → ℂ := fun w => chartAt ℂ p (ι.symm ((chartAt ℂ (ι p)).symm w)) with huinv
  have hu : localMapExpr ι p (chartAt ℂ p p) = chartAt ℂ (ι p) (ι p) := by
    show chartAt ℂ (ι p) (ι ((chartAt ℂ p).symm (chartAt ℂ p p))) = _
    rw [hpc]
  have hcont0 : ContinuousAt (fun w => ι.symm ((chartAt ℂ (ι p)).symm w)) (chartAt ℂ (ι p) (ι p)) :=
    ι.symm.continuous.continuousAt.comp ((chartAt ℂ (ι p)).continuousAt_symm hqt)
  have hval : ι.symm ((chartAt ℂ (ι p)).symm (chartAt ℂ (ι p) (ι p))) = p := by
    rw [hqc, ι.symm_apply_apply]
  have hinvc : ContinuousAt uinv (chartAt ℂ (ι p) (ι p)) := by
    refine ContinuousAt.comp (g := chartAt ℂ p) ?_ hcont0
    rw [hval]
    exact (chartAt ℂ p).continuousAt (mem_chart_source ℂ p)
  have huinv0 : uinv (chartAt ℂ (ι p) (ι p)) = chartAt ℂ p p := by
    show chartAt ℂ p (ι.symm ((chartAt ℂ (ι p)).symm (chartAt ℂ (ι p) (ι p)))) = _
    rw [hval]
  have hsrc : ∀ᶠ w in 𝓝 (chartAt ℂ (ι p) (ι p)),
      w ∈ (chartAt ℂ (ι p)).target ∧ ι.symm ((chartAt ℂ (ι p)).symm w) ∈ (chartAt ℂ p).source := by
    refine Filter.Eventually.and ((chartAt ℂ (ι p)).open_target.mem_nhds hqt) ?_
    refine hcont0.preimage_mem_nhds ?_
    rw [hval]
    exact (chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p)
  have huu : ∀ᶠ w in 𝓝 (chartAt ℂ (ι p) (ι p)), localMapExpr ι p (uinv w) = w := by
    filter_upwards [hsrc] with w hw
    show chartAt ℂ (ι p) (ι ((chartAt ℂ p).symm (chartAt ℂ p (ι.symm ((chartAt ℂ (ι p)).symm w))))) = w
    rw [(chartAt ℂ p).left_inv hw.2, ι.apply_symm_apply, (chartAt ℂ (ι p)).right_inv hw.1]
  have hvc : ContinuousAt (localMapExpr Φ p) (chartAt ℂ p p) := by
    have h1 : ContinuousAt (fun z => Φ ((chartAt ℂ p).symm z)) (chartAt ℂ p p) :=
      Φ.continuous.continuousAt.comp ((chartAt ℂ p).continuousAt_symm hpt)
    refine ContinuousAt.comp (g := chartAt ℂ (Φ p)) ?_ h1
    show ContinuousAt (chartAt ℂ (Φ p)) (Φ ((chartAt ℂ p).symm (chartAt ℂ p p)))
    rw [hpc]
    exact (chartAt ℂ (Φ p)).continuousAt (mem_chart_source ℂ (Φ p))
  have hplanar := s32w_dt_E_planar hζι.1 hζt.1 hζι.2.1 hζt.2.1
    ((hζι.2.2.2.and hζt.2.2.2).mono fun z h => h.1.trans h.2.symm) (a₁ := chartAt ℂ (ι p) (ι p))
    hζ₁.1 hζ₂ hζ₂d hu hvc hrι hrel hinvc huinv0 huu
  have hy : (ι.symm.trans Φ : W → Z) (ι p) ∈ (chartAt ℂ (Φ p)).source := by
    show Φ (ι.symm (ι p)) ∈ _
    rw [ι.symm_apply_apply]
    exact mem_chart_source ℂ (Φ p)
  refine (s23_mdifferentiableAt_iff (f := (ι.symm.trans Φ : W → Z)) (x := ι p) (p := ι p) (y := Φ p)
    (mem_chart_source ℂ (ι p)) hy).2 ⟨(ι.symm.trans Φ).continuous.continuousAt, ?_⟩
  refine hplanar.congr_of_eventuallyEq ?_
  filter_upwards [hsrc] with w hw
  show chartAt ℂ (Φ p) (Φ (ι.symm ((chartAt ℂ (ι p)).symm w))) =
    chartAt ℂ (Φ p) (Φ ((chartAt ℂ p).symm (chartAt ℂ p (ι.symm ((chartAt ℂ (ι p)).symm w)))))
  rw [(chartAt ℂ p).left_inv hw.2]

end ECore

section E1

variable {Y₀ : Type u} {Y : Type v} {S : Type w} {Zc : Type u} [TopologicalSpace Y₀] [ChartedSpace ℂ Y₀]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [TopologicalSpace S] [ChartedSpace ℂ S]
  [TopologicalSpace Zc] [ChartedSpace ℂ Zc]
  [IsManifold 𝓘(ℂ) ω Y₀] [IsManifold 𝓘(ℂ) ω Y] [IsManifold 𝓘(ℂ) ω S] [IsManifold 𝓘(ℂ) ω Zc]

/-- **(E1)** On the positive half, the natural parameter of `q` transported to `Q`, and the parameter of
`q'` transported to the target double, satisfy the stretch relation for `Φ`. -/
theorem s32w_dt_E1 {G₀ : Y₀ → Y} {G₁ : S → Zc} (hG₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₀)
    (hG₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₁) (hi₀ : Function.Injective G₀) (hi₁ : Function.Injective G₁)
    {h : Y₀ ≃ₜ S} {Φ : Y ≃ₜ Zc} (hΦ : ∀ x, Φ (G₀ x) = G₁ (h x)) {q : Y₀ → ℂ → ℂ} {q' : S → ℂ → ℂ}
    {Q : Y → ℂ → ℂ} {k : ℝ} (hQ : IsDiffFamily 2 0 Q)
    (hD2a : ∀ x, ∀ z ∈ (chartAt ℂ x).target,
      q x z = s31qr_transportOn univ G₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x z)
    (hh : IsTeichmullerMap h q q' k) {x : Y₀} (hx : IsRegularPoint q x) :
    ∃ ζt ζ₂ : ℂ → ℂ, IsNaturalParameterAt Q (G₀ x) ζt ∧
      AnalyticAt ℂ ζ₂ (localMapExpr Φ (G₀ x) (chartAt ℂ (G₀ x) (G₀ x))) ∧
      deriv ζ₂ (localMapExpr Φ (G₀ x) (chartAt ℂ (G₀ x) (G₀ x))) ≠ 0 ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ (G₀ x) (G₀ x)),
        ζ₂ (localMapExpr Φ (G₀ x) z) = teichStretch k (ζt z) := by
  obtain ⟨-, ζh, ζe, hζh, hζe, hrel⟩ := hh.regular x hx
  have hxc : (chartAt ℂ x).symm (chartAt ℂ x x) = x := (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have hxt : chartAt ℂ x x ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have hbc : (chartAt ℂ (h x)).symm (chartAt ℂ (h x) (h x)) = h x :=
    (chartAt ℂ (h x)).left_inv (mem_chart_source ℂ (h x))
  have hbt : chartAt ℂ (h x) (h x) ∈ (chartAt ℂ (h x)).target :=
    (chartAt ℂ (h x)).map_source (mem_chart_source ℂ (h x))
  set σ : ℂ → ℂ := fun w => chartAt ℂ (G₀ x) (G₀ ((chartAt ℂ x).symm w)) with hσ
  have hσan : AnalyticAt ℂ σ (chartAt ℂ x x) := s32w_dt_coord_analytic hG₀ x (a := G₀ x) rfl
  have hσd : deriv σ (chartAt ℂ x x) ≠ 0 := by
    refine s31qr_coordinate_deriv_ne_zero (U := univ) isOpen_univ (H := G₀) (fun p _ => hG₀ p)
      hi₀.injOn x (G₀ x) hxt (mem_univ _) ?_
    rw [hxc]; exact mem_chart_source ℂ (G₀ x)
  have hσc : σ (chartAt ℂ x x) = chartAt ℂ (G₀ x) (G₀ x) := by
    show chartAt ℂ (G₀ x) (G₀ ((chartAt ℂ x).symm (chartAt ℂ x x))) = _
    rw [hxc]
  have hGc : ContinuousAt (fun w => G₀ ((chartAt ℂ x).symm w)) (chartAt ℂ x x) :=
    hG₀.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hxt)
  have hGsrc : ∀ᶠ w in 𝓝 (chartAt ℂ x x), G₀ ((chartAt ℂ x).symm w) ∈ (chartAt ℂ (G₀ x)).source := by
    refine hGc.preimage_mem_nhds ?_
    show (chartAt ℂ (G₀ x)).source ∈ 𝓝 (G₀ ((chartAt ℂ x).symm (chartAt ℂ x x)))
    rw [hxc]
    exact (chartAt ℂ (G₀ x)).open_source.mem_nhds (mem_chart_source ℂ (G₀ x))
  have hF : ∀ᶠ z in 𝓝 (chartAt ℂ x x),
      deriv ζh z ^ 2 = Q (G₀ x) (σ z) * deriv σ z ^ 2 := by
    filter_upwards [hζh.2.2.2, (chartAt ℂ x).open_target.mem_nhds hxt, hGsrc] with z h1 hzt hsrc
    rw [h1, hD2a x z hzt]
    exact s31qr_transport_local hQ x (G₀ x) hzt (mem_univ _) hsrc (hG₀ _)
  obtain ⟨g, hga, hg0, hright, hleft, hdg, hζan, hnat⟩ :=
    s32w_dt_nat_transfer hζh.1 hσan hσd hF
  rw [hσc] at hga hg0 hright hdg hζan hnat
  -- the target side
  have hb : Φ (G₀ x) = G₁ (h x) := hΦ x
  set τ₁ : ℂ → ℂ := fun w => chartAt ℂ (Φ (G₀ x)) (G₁ ((chartAt ℂ (h x)).symm w)) with hτ₁
  have hτan : AnalyticAt ℂ τ₁ (chartAt ℂ (h x) (h x)) :=
    s32w_dt_coord_analytic hG₁ (h x) (a := Φ (G₀ x)) hb.symm
  have hτd : deriv τ₁ (chartAt ℂ (h x) (h x)) ≠ 0 := by
    refine s31qr_coordinate_deriv_ne_zero (U := univ) isOpen_univ (H := G₁) (fun p _ => hG₁ p)
      hi₁.injOn (h x) (Φ (G₀ x)) hbt (mem_univ _) ?_
    rw [hbc, ← hb]; exact mem_chart_source ℂ _
  have hτc : τ₁ (chartAt ℂ (h x) (h x)) = chartAt ℂ (Φ (G₀ x)) (Φ (G₀ x)) := by
    show chartAt ℂ (Φ (G₀ x)) (G₁ ((chartAt ℂ (h x)).symm (chartAt ℂ (h x) (h x)))) = _
    rw [hbc, hb]
  obtain ⟨g₁, hg₁a, hg₁0, hg₁l, hdg₁⟩ := s32w_dt_inv_exists hτan hτd
  have hv0 : localMapExpr Φ (G₀ x) (chartAt ℂ (G₀ x) (G₀ x)) = τ₁ (chartAt ℂ (h x) (h x)) := by
    rw [hτc]
    show chartAt ℂ (Φ (G₀ x)) (Φ ((chartAt ℂ (G₀ x)).symm (chartAt ℂ (G₀ x) (G₀ x)))) = _
    rw [(chartAt ℂ (G₀ x)).left_inv (mem_chart_source ℂ (G₀ x))]
  have hgt : Tendsto g (𝓝 (chartAt ℂ (G₀ x) (G₀ x))) (𝓝 (chartAt ℂ x x)) := by
    have := hga.continuousAt.tendsto
    rwa [hg0] at this
  -- eventual facts at the source chart centre
  have hhc : ContinuousAt (localMapExpr h x) (chartAt ℂ x x) := by
    have h1 : ContinuousAt (fun z => h ((chartAt ℂ x).symm z)) (chartAt ℂ x x) :=
      h.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hxt)
    refine ContinuousAt.comp (g := chartAt ℂ (h x)) ?_ h1
    show ContinuousAt (chartAt ℂ (h x)) (h ((chartAt ℂ x).symm (chartAt ℂ x x)))
    rw [hxc]
    exact (chartAt ℂ (h x)).continuousAt (mem_chart_source ℂ (h x))
  have hhx : localMapExpr h x (chartAt ℂ x x) = chartAt ℂ (h x) (h x) := by
    show chartAt ℂ (h x) (h ((chartAt ℂ x).symm (chartAt ℂ x x))) = _
    rw [hxc]
  have hhsrc : ∀ᶠ w in 𝓝 (chartAt ℂ x x), h ((chartAt ℂ x).symm w) ∈ (chartAt ℂ (h x)).source := by
    have h1 : ContinuousAt (fun z => h ((chartAt ℂ x).symm z)) (chartAt ℂ x x) :=
      h.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hxt)
    refine h1.preimage_mem_nhds ?_
    show (chartAt ℂ (h x)).source ∈ 𝓝 (h ((chartAt ℂ x).symm (chartAt ℂ x x)))
    rw [hxc]
    exact (chartAt ℂ (h x)).open_source.mem_nhds (mem_chart_source ℂ (h x))
  have hleft₁ : ∀ᶠ w in 𝓝 (chartAt ℂ x x), g₁ (τ₁ (localMapExpr h x w)) = localMapExpr h x w := by
    have : Tendsto (localMapExpr h x) (𝓝 (chartAt ℂ x x)) (𝓝 (chartAt ℂ (h x) (h x))) := by
      have := hhc.tendsto
      rwa [hhx] at this
    exact this.eventually hg₁l
  have hrel' : ∀ᶠ w in 𝓝 (chartAt ℂ x x),
      ζe (localMapExpr h x w) = teichStretch k (ζh w) := hrel
  have hE : ∀ᶠ w in 𝓝 (chartAt ℂ x x), (g₁ (τ₁ (localMapExpr h x w)) = localMapExpr h x w) ∧
      (ζe (localMapExpr h x w) = teichStretch k (ζh w)) ∧
      (h ((chartAt ℂ x).symm w) ∈ (chartAt ℂ (h x)).source) ∧
      (G₀ ((chartAt ℂ x).symm w) ∈ (chartAt ℂ (G₀ x)).source) :=
    hleft₁.and (hrel'.and (hhsrc.and hGsrc))
  have hzfin : ∀ᶠ z in 𝓝 (chartAt ℂ (G₀ x) (G₀ x)),
      σ (g z) = z ∧ ((g₁ (τ₁ (localMapExpr h x (g z))) = localMapExpr h x (g z)) ∧
      (ζe (localMapExpr h x (g z)) = teichStretch k (ζh (g z))) ∧
      (h ((chartAt ℂ x).symm (g z)) ∈ (chartAt ℂ (h x)).source) ∧
      (G₀ ((chartAt ℂ x).symm (g z)) ∈ (chartAt ℂ (G₀ x)).source)) :=
    hright.and (hgt.eventually hE)
  refine ⟨fun w => ζh (g w), fun w => ζe (g₁ w), ⟨hζan, ?_, ?_, hnat⟩, ?_, ?_, ?_⟩
  · show ζh (g (chartAt ℂ (G₀ x) (G₀ x))) = 0
    rw [hg0]; exact hζh.2.1
  · have hd1 : DifferentiableAt ℂ ζh (g (chartAt ℂ (G₀ x) (G₀ x))) := by
      rw [hg0]; exact hζh.1.differentiableAt
    have : deriv (fun w => ζh (g w)) (chartAt ℂ (G₀ x) (G₀ x)) =
        deriv ζh (g (chartAt ℂ (G₀ x) (G₀ x))) * deriv g (chartAt ℂ (G₀ x) (G₀ x)) :=
      deriv_comp _ hd1 hga.differentiableAt
    rw [this, hg0]
    exact mul_ne_zero hζh.2.2.1 hdg
  · rw [hv0]
    exact hζe.1.comp_of_eq hg₁a hg₁0
  · rw [hv0]
    have hd1 : DifferentiableAt ℂ ζe (g₁ (τ₁ (chartAt ℂ (h x) (h x)))) := by
      rw [hg₁0]; exact hζe.1.differentiableAt
    have : deriv (fun w => ζe (g₁ w)) (τ₁ (chartAt ℂ (h x) (h x))) =
        deriv ζe (g₁ (τ₁ (chartAt ℂ (h x) (h x)))) * deriv g₁ (τ₁ (chartAt ℂ (h x) (h x))) :=
      deriv_comp _ hd1 hg₁a.differentiableAt
    rw [this, hg₁0]
    exact mul_ne_zero hζe.2.2.1 hdg₁
  · filter_upwards [hzfin] with z hz
    obtain ⟨hz1, hz2, hz3, hz4, hz5⟩ := hz
    -- the coordinate expression of `Φ` factors through `g z`
    have hfac : localMapExpr Φ (G₀ x) z = τ₁ (localMapExpr h x (g z)) := by
      show chartAt ℂ (Φ (G₀ x)) (Φ ((chartAt ℂ (G₀ x)).symm z)) =
        chartAt ℂ (Φ (G₀ x)) (G₁ ((chartAt ℂ (h x)).symm (chartAt ℂ (h x)
          (h ((chartAt ℂ x).symm (g z))))))
      rw [(chartAt ℂ (h x)).left_inv hz4]
      have hzz : (chartAt ℂ (G₀ x)).symm z = G₀ ((chartAt ℂ x).symm (g z)) := by
        have h0 : z = chartAt ℂ (G₀ x) (G₀ ((chartAt ℂ x).symm (g z))) := hz1.symm
        calc (chartAt ℂ (G₀ x)).symm z
            = (chartAt ℂ (G₀ x)).symm (chartAt ℂ (G₀ x) (G₀ ((chartAt ℂ x).symm (g z)))) :=
              congrArg _ h0
          _ = _ := (chartAt ℂ (G₀ x)).left_inv hz5
      rw [hzz, hΦ ((chartAt ℂ x).symm (g z))]
    show ζe (g₁ (localMapExpr Φ (G₀ x) z)) = teichStretch k (ζh (g z))
    rw [hfac, hz2, hz3]

end E1

section Mirror

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- The conjugated coordinate expression of an anticonformal map is analytic at the chart centre. -/
theorem s32w_dt_J_an {J : Y ≃ₜ Y} (hJ : IsAnticonformalInvolution J) (y : Y) :
    AnalyticAt ℂ (fun z => conj (chartAt ℂ (J y) (J ((chartAt ℂ y).symm z)))) (chartAt ℂ y y) := by
  have hyt : chartAt ℂ y y ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source (mem_chart_source ℂ y)
  have hyc : (chartAt ℂ y).symm (chartAt ℂ y y) = y := (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hdom : chartAt ℂ y y ∈ localMapDomain J y := by
    refine ⟨hyt, ?_⟩
    show J ((chartAt ℂ y).symm (chartAt ℂ y y)) ∈ (chartAt ℂ (J y)).source
    rw [hyc]; exact mem_chart_source ℂ (J y)
  have hopen : IsOpen (localMapDomain J y) := s23_localMapDomain_isOpen J.continuous y
  exact (hJ.2 y).analyticAt (hopen.mem_nhds hdom)

/-- The conjugated coordinate expression of an anticonformal involution has nonzero derivative. -/
theorem s32w_dt_J_deriv_ne {J : Y ≃ₜ Y} (hJ : IsAnticonformalInvolution J) (y : Y) :
    deriv (fun z => conj (chartAt ℂ (J y) (J ((chartAt ℂ y).symm z)))) (chartAt ℂ y y) ≠ 0 := by
  have hyt : chartAt ℂ y y ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source (mem_chart_source ℂ y)
  have hyc : (chartAt ℂ y).symm (chartAt ℂ y y) = y := (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hAn := s32w_dt_J_an hJ y
  set A : ℂ → ℂ := fun z => conj (chartAt ℂ (J y) (J ((chartAt ℂ y).symm z))) with hA
  set A' : ℂ → ℂ := fun z => conj (chartAt ℂ y (J ((chartAt ℂ (J y)).symm z))) with hA'
  have hA'an : AnalyticAt ℂ A' (chartAt ℂ (J y) (J y)) := by
    have h := s32w_dt_J_an hJ (J y)
    simp only [hJ.1 y] at h
    exact h
  set k : ℂ → ℂ := fun w => conj (A' (conj w)) with hk
  have hAc : A (chartAt ℂ y y) = conj (chartAt ℂ (J y) (J y)) := by
    show conj (chartAt ℂ (J y) (J ((chartAt ℂ y).symm (chartAt ℂ y y)))) = _
    rw [hyc]
  have hkd : DifferentiableAt ℂ k (A (chartAt ℂ y y)) := by
    rw [hAc]
    exact hA'an.differentiableAt.conj_conj
  have hsrc : ∀ᶠ z in 𝓝 (chartAt ℂ y y), z ∈ (chartAt ℂ y).target ∧
      J ((chartAt ℂ y).symm z) ∈ (chartAt ℂ (J y)).source := by
    refine Filter.Eventually.and ((chartAt ℂ y).open_target.mem_nhds hyt) ?_
    have hc : ContinuousAt (fun z => J ((chartAt ℂ y).symm z)) (chartAt ℂ y y) :=
      J.continuous.continuousAt.comp ((chartAt ℂ y).continuousAt_symm hyt)
    refine hc.preimage_mem_nhds ?_
    show (chartAt ℂ (J y)).source ∈ 𝓝 (J ((chartAt ℂ y).symm (chartAt ℂ y y)))
    rw [hyc]
    exact (chartAt ℂ (J y)).open_source.mem_nhds (mem_chart_source ℂ (J y))
  have hkA : ∀ᶠ z in 𝓝 (chartAt ℂ y y), k (A z) = z := by
    filter_upwards [hsrc] with z hz
    have h1 : conj (A z) = chartAt ℂ (J y) (J ((chartAt ℂ y).symm z)) := Complex.conj_conj _
    show conj (A' (conj (A z))) = z
    rw [h1]
    show conj (conj (chartAt ℂ y (J ((chartAt ℂ (J y)).symm
      (chartAt ℂ (J y) (J ((chartAt ℂ y).symm z))))))) = z
    rw [(chartAt ℂ (J y)).left_inv hz.2, hJ.1, Complex.conj_conj, (chartAt ℂ y).right_inv hz.1]
  exact s23_deriv_ne_zero hAn.differentiableAt hkd hkA

/-- The reflection law of a differential in a fixed chart. -/
theorem s32w_dt_Dfix {Q : Y → ℂ → ℂ} (hQ : IsDiffFamily 2 0 Q) {J : Y ≃ₜ Y}
    (hJ : IsAnticonformalInvolution J) {pm p : Y} (hpm : J pm = p)
    (hD2b : ∀ y z, z ∈ (chartAt ℂ y).target →
      Q y z = conj (Q (J ((chartAt ℂ y).symm z)) (chartAt ℂ (J ((chartAt ℂ y).symm z))
          (J ((chartAt ℂ y).symm z)))) *
        deriv (fun w => conj (chartAt ℂ (J ((chartAt ℂ y).symm z)) (J ((chartAt ℂ y).symm w)))) z ^ 2)
    {z : ℂ} (hz : z ∈ (chartAt ℂ pm).target) (hzs : J ((chartAt ℂ pm).symm z) ∈ (chartAt ℂ p).source) :
    Q pm z = conj (Q p (chartAt ℂ p (J ((chartAt ℂ pm).symm z)))) *
      deriv (fun w => conj (chartAt ℂ p (J ((chartAt ℂ pm).symm w)))) z ^ 2 := by
  subst hpm
  set u := (chartAt ℂ pm).symm z with hu
  set b := J u with hb
  have hbt : chartAt ℂ b b ∈ (chartAt ℂ b).target := (chartAt ℂ b).map_source (mem_chart_source ℂ b)
  have hbi : (chartAt ℂ b).symm (chartAt ℂ b b) = b := (chartAt ℂ b).left_inv (mem_chart_source ℂ b)
  have hl : Q b (chartAt ℂ b b) =
      Q (J pm) (chartAt ℂ (J pm) b) * deriv (chartTransition (J pm) b) (chartAt ℂ b b) ^ 2 := by
    have hh := hQ.2 (J pm) b (chartAt ℂ b b) hbt (by rw [hbi]; exact hzs)
    have he : chartTransition (J pm) b (chartAt ℂ b b) = chartAt ℂ (J pm) b := by
      change chartAt ℂ (J pm) ((chartAt ℂ b).symm (chartAt ℂ b b)) = _
      rw [hbi]
    simpa only [he, zpow_zero, mul_one, zpow_two, pow_two] using hh
  have hT := s23_transition_differentiableAt (J pm) b hbt (by rw [hbi]; exact hzs)
  have hpt : chartAt ℂ (J pm) b ∈ (chartAt ℂ (J pm)).target := (chartAt ℂ (J pm)).map_source hzs
  have hpb : (chartAt ℂ (J pm)).symm (chartAt ℂ (J pm) b) = b := (chartAt ℂ (J pm)).left_inv hzs
  have hT' := s23_transition_differentiableAt b (J pm) hpt (by rw [hpb]; exact mem_chart_source ℂ b)
  -- the two analytic coordinate expressions
  set A : ℂ → ℂ := fun w => conj (chartAt ℂ (J pm) (J ((chartAt ℂ pm).symm w))) with hA
  set B : ℂ → ℂ := fun w => conj (chartAt ℂ b (J ((chartAt ℂ pm).symm w))) with hB
  have hdom : z ∈ localMapDomain J pm := ⟨hz, hzs⟩
  have hopen : IsOpen (localMapDomain J pm) := s23_localMapDomain_isOpen J.continuous pm
  have hAd : DifferentiableAt ℂ A z := (hJ.2 pm).differentiableAt (hopen.mem_nhds hdom)
  have hcont : ContinuousAt (fun w => J ((chartAt ℂ pm).symm w)) z :=
    J.continuous.continuousAt.comp ((chartAt ℂ pm).continuousAt_symm hz)
  have hsrcb : ∀ᶠ w in 𝓝 z, J ((chartAt ℂ pm).symm w) ∈ (chartAt ℂ b).source :=
    hcont.preimage_mem_nhds ((chartAt ℂ b).open_source.mem_nhds (mem_chart_source ℂ b))
  have hsrcp : ∀ᶠ w in 𝓝 z, J ((chartAt ℂ pm).symm w) ∈ (chartAt ℂ (J pm)).source :=
    hcont.preimage_mem_nhds ((chartAt ℂ (J pm)).open_source.mem_nhds hzs)
  have hAz : conj (A z) = chartAt ℂ (J pm) b := by
    show conj (conj (chartAt ℂ (J pm) (J u))) = _
    rw [Complex.conj_conj]
  have hBz : conj (B z) = chartAt ℂ b b := by
    show conj (conj (chartAt ℂ b (J u))) = _
    rw [Complex.conj_conj]
  -- `B = ρ(T') ∘ A`
  have hBA : B =ᶠ[𝓝 z] fun w => conj (chartTransition b (J pm) (conj (A w))) := by
    filter_upwards [hsrcp] with w hw
    show conj (chartAt ℂ b (J ((chartAt ℂ pm).symm w))) =
      conj (chartAt ℂ b ((chartAt ℂ (J pm)).symm (conj (conj (chartAt ℂ (J pm)
        (J ((chartAt ℂ pm).symm w)))))))
    rw [Complex.conj_conj, (chartAt ℂ (J pm)).left_inv hw]
  have hAB : A =ᶠ[𝓝 z] fun w => conj (chartTransition (J pm) b (conj (B w))) := by
    filter_upwards [hsrcb] with w hw
    show conj (chartAt ℂ (J pm) (J ((chartAt ℂ pm).symm w))) =
      conj (chartAt ℂ (J pm) ((chartAt ℂ b).symm (conj (conj (chartAt ℂ b
        (J ((chartAt ℂ pm).symm w)))))))
    rw [Complex.conj_conj, (chartAt ℂ b).left_inv hw]
  have hT'd : DifferentiableAt ℂ (chartTransition b (J pm)) (conj (A z)) := by
    rw [hAz]; exact hT'
  have hBd : DifferentiableAt ℂ B z := by
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hBA
    have h1 : DifferentiableAt ℂ (fun w => conj (chartTransition b (J pm) (conj w))) (A z) := by
      have := hT'd.conj_conj
      rwa [Complex.conj_conj] at this
    exact h1.comp z hAd
  have hTd : DifferentiableAt ℂ (fun w => conj (chartTransition (J pm) b (conj w))) (B z) := by
    have h0 : DifferentiableAt ℂ (chartTransition (J pm) b) (conj (B z)) := by
      rw [hBz]; exact hT
    have := h0.conj_conj
    rwa [Complex.conj_conj] at this
  have hderA : deriv A z = conj (deriv (chartTransition (J pm) b) (chartAt ℂ b b)) * deriv B z := by
    rw [hAB.deriv_eq]
    have h1 := deriv_comp z hTd hBd
    have h2 : deriv (fun w => conj (chartTransition (J pm) b (conj w))) (B z) =
        conj (deriv (chartTransition (J pm) b) (conj (B z))) :=
      congrFun (deriv_conj_conj (f := chartTransition (J pm) b)) (B z)
    simp only [Function.comp_def] at h1
    rw [h1, h2, hBz]
  have hD := hD2b pm z hz
  have hAval : chartAt ℂ (J pm) b = conj (A z) := hAz.symm
  change Q pm z = conj (Q (J pm) (chartAt ℂ (J pm) b)) * deriv A z ^ 2
  rw [hD, hderA, mul_pow]
  have hQ2 : conj (Q b (chartAt ℂ b b)) =
      conj (Q (J pm) (chartAt ℂ (J pm) b)) * conj (deriv (chartTransition (J pm) b) (chartAt ℂ b b)) ^ 2 := by
    rw [hl]; simp
  show conj (Q b (chartAt ℂ b b)) * deriv B z ^ 2 = _
  rw [hQ2]
  ring

end Mirror

section Reflect

/-- The reflection `u ↦ conj (ζ (conj u))` of an analytic function is analytic. -/
theorem s32w_dt_refl_analytic {ζ : ℂ → ℂ} {a : ℂ} (hζ : AnalyticAt ℂ ζ a) :
    AnalyticAt ℂ (fun u => conj (ζ (conj u))) (conj a) := by
  have hev : ∀ᶠ w in 𝓝 a, DifferentiableAt ℂ ζ w := hζ.eventually_analyticAt.mono fun w hw => hw.differentiableAt
  have hev' : ∀ᶠ u in 𝓝 (conj a), DifferentiableAt ℂ ζ (conj u) := by
    have hc : Tendsto (fun u : ℂ => conj u) (𝓝 (conj a)) (𝓝 a) := by
      have := (Complex.continuous_conj.tendsto (conj a))
      rwa [Complex.conj_conj] at this
    exact hc.eventually hev
  have hdiff : ∀ᶠ u in 𝓝 (conj a), DifferentiableAt ℂ (fun u => conj (ζ (conj u))) u := by
    filter_upwards [hev'] with u hu
    have := hu.conj_conj
    rwa [Complex.conj_conj] at this
  obtain ⟨s, hs, hso, hsa⟩ := _root_.mem_nhds_iff.1 hdiff
  exact (DifferentiableOn.analyticAt (fun u hu => (hs hu).differentiableWithinAt)
    (hso.mem_nhds hsa))

/-- `teichStretch` commutes with complex conjugation. -/
theorem s32w_dt_stretch_conj (k : ℝ) (w : ℂ) : teichStretch k (conj w) = conj (teichStretch k w) := by
  simp [teichStretch, map_div₀]

/-- The reflected natural parameter is a natural parameter of the reflected differential. -/
theorem s32w_dt_refl_nat {ζ Qp A Q : ℂ → ℂ} {p₀ z₀ : ℂ} (hζ : AnalyticAt ℂ ζ p₀) (hζ0 : ζ p₀ = 0)
    (hζd : deriv ζ p₀ ≠ 0) (hnat : ∀ᶠ w in 𝓝 p₀, deriv ζ w ^ 2 = Qp w)
    (hA : AnalyticAt ℂ A z₀) (hAz : A z₀ = conj p₀) (hAd : deriv A z₀ ≠ 0)
    (hQ : ∀ᶠ z in 𝓝 z₀, Q z = conj (Qp (conj (A z))) * deriv A z ^ 2) :
    AnalyticAt ℂ (fun z => conj (ζ (conj (A z)))) z₀ ∧ conj (ζ (conj (A z₀))) = 0 ∧
      deriv (fun z => conj (ζ (conj (A z)))) z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 z₀, deriv (fun z => conj (ζ (conj (A z)))) z ^ 2 = Q z := by
  have hρ : AnalyticAt ℂ (fun u => conj (ζ (conj u))) (A z₀) := by
    have h := s32w_dt_refl_analytic hζ
    rw [hAz]; exact h
  have hAev : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ A z := hA.eventually_analyticAt
  have hAt : Tendsto A (𝓝 z₀) (𝓝 (A z₀)) := hA.continuousAt.tendsto
  have hρev : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ (fun u => conj (ζ (conj u))) (A z) :=
    hAt.eventually hρ.eventually_analyticAt
  have hcA : Tendsto (fun z => conj (A z)) (𝓝 z₀) (𝓝 p₀) := by
    have h1 : Tendsto (fun z => conj (A z)) (𝓝 z₀) (𝓝 (conj (A z₀))) :=
      (Complex.continuous_conj.tendsto (A z₀)).comp hAt
    rwa [hAz, Complex.conj_conj] at h1
  have hnatev : ∀ᶠ z in 𝓝 z₀, deriv ζ (conj (A z)) ^ 2 = Qp (conj (A z)) := hcA.eventually hnat
  have hder : ∀ z, DifferentiableAt ℂ (fun u => conj (ζ (conj u))) (A z) → DifferentiableAt ℂ A z →
      deriv (fun z => conj (ζ (conj (A z)))) z = conj (deriv ζ (conj (A z))) * deriv A z := by
    intro z h1 h2
    have h3 : deriv ((fun u => conj (ζ (conj u))) ∘ A) z =
        deriv (fun u => conj (ζ (conj u))) (A z) * deriv A z := deriv_comp z h1 h2
    have h4 : deriv (fun u => conj (ζ (conj u))) (A z) = conj (deriv ζ (conj (A z))) :=
      congrFun (deriv_conj_conj (f := ζ)) (A z)
    rw [← h4]; exact h3
  refine ⟨hρ.comp hA, ?_, ?_, ?_⟩
  · show conj (ζ (conj (A z₀))) = 0
    rw [hAz, Complex.conj_conj, hζ0]; simp
  · rw [hder z₀ hρ.differentiableAt hA.differentiableAt, hAz, Complex.conj_conj]
    exact mul_ne_zero ((map_ne_zero _).2 hζd) hAd
  · filter_upwards [hQ, hAev, hρev, hnatev] with z h1 h2 h3 h4
    rw [hder z h3.differentiableAt h2.differentiableAt, h1, mul_pow, ← map_pow, h4]

end Reflect

section E2

variable {Y₀ : Type u} {Y : Type v} {S : Type w} {Zc : Type u} [TopologicalSpace Y₀] [ChartedSpace ℂ Y₀]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [TopologicalSpace S] [ChartedSpace ℂ S]
  [TopologicalSpace Zc] [ChartedSpace ℂ Zc]
  [IsManifold 𝓘(ℂ) ω Y₀] [IsManifold 𝓘(ℂ) ω Y] [IsManifold 𝓘(ℂ) ω S] [IsManifold 𝓘(ℂ) ω Zc]

/-- **(E2)** The mirror half: the reflected data satisfy the stretch relation for `Φ` at the mirror point. -/
theorem s32w_dt_E2 {G₀ : Y₀ → Y} {G₁ : S → Zc} (hG₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₀)
    (hG₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₁) (hi₀ : Function.Injective G₀) (hi₁ : Function.Injective G₁)
    {h : Y₀ ≃ₜ S} {Φ : Y ≃ₜ Zc} (hΦ : ∀ x, Φ (G₀ x) = G₁ (h x)) {q : Y₀ → ℂ → ℂ} {q' : S → ℂ → ℂ}
    {Q : Y → ℂ → ℂ} {k : ℝ} (hQ : IsDiffFamily 2 0 Q)
    (hD2a : ∀ x, ∀ z ∈ (chartAt ℂ x).target,
      q x z = s31qr_transportOn univ G₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x z)
    (hh : IsTeichmullerMap h q q' k) {x : Y₀} (hx : IsRegularPoint q x)
    {Jy : Y ≃ₜ Y} {Jz : Zc ≃ₜ Zc} (hJy : IsAnticonformalInvolution Jy)
    (hJz : IsAnticonformalInvolution Jz) (hΦJ : ∀ y, Φ (Jy y) = Jz (Φ y))
    (hD2b : ∀ y z, z ∈ (chartAt ℂ y).target →
      Q y z = conj (Q (Jy ((chartAt ℂ y).symm z)) (chartAt ℂ (Jy ((chartAt ℂ y).symm z))
          (Jy ((chartAt ℂ y).symm z)))) *
        deriv (fun w => conj (chartAt ℂ (Jy ((chartAt ℂ y).symm z)) (Jy ((chartAt ℂ y).symm w)))) z ^ 2)
    {pm : Y} (hpm : Jy pm = G₀ x) :
    ∃ ζt ζ₂ : ℂ → ℂ, IsNaturalParameterAt Q pm ζt ∧
      AnalyticAt ℂ ζ₂ (localMapExpr Φ pm (chartAt ℂ pm pm)) ∧
      deriv ζ₂ (localMapExpr Φ pm (chartAt ℂ pm pm)) ≠ 0 ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ pm pm), ζ₂ (localMapExpr Φ pm z) = teichStretch k (ζt z) := by
  obtain ⟨ζt₁, ζ₂₁, hζt, han, hdr, hrel₁⟩ := s32w_dt_E1 hG₀ hG₁ hi₀ hi₁ hΦ hQ hD2a hh hx
  have hpmt : chartAt ℂ pm pm ∈ (chartAt ℂ pm).target := (chartAt ℂ pm).map_source (mem_chart_source ℂ pm)
  have hpmc : (chartAt ℂ pm).symm (chartAt ℂ pm pm) = pm := (chartAt ℂ pm).left_inv (mem_chart_source ℂ pm)
  have hpt : chartAt ℂ (G₀ x) (G₀ x) ∈ (chartAt ℂ (G₀ x)).target :=
    (chartAt ℂ (G₀ x)).map_source (mem_chart_source ℂ (G₀ x))
  -- the coordinate change of the reflection on the source double
  set A : ℂ → ℂ := fun z => conj (chartAt ℂ (G₀ x) (Jy ((chartAt ℂ pm).symm z))) with hA
  have hAan : AnalyticAt ℂ A (chartAt ℂ pm pm) := by
    have := s32w_dt_J_an hJy pm
    rw [hpm] at this
    exact this
  have hAd : deriv A (chartAt ℂ pm pm) ≠ 0 := by
    have := s32w_dt_J_deriv_ne hJy pm
    rw [hpm] at this
    exact this
  have hAz : A (chartAt ℂ pm pm) = conj (chartAt ℂ (G₀ x) (G₀ x)) := by
    show conj (chartAt ℂ (G₀ x) (Jy ((chartAt ℂ pm).symm (chartAt ℂ pm pm)))) = _
    rw [hpmc, hpm]
  have hcont : ContinuousAt (fun w => Jy ((chartAt ℂ pm).symm w)) (chartAt ℂ pm pm) :=
    Jy.continuous.continuousAt.comp ((chartAt ℂ pm).continuousAt_symm hpmt)
  have hsrc : ∀ᶠ z in 𝓝 (chartAt ℂ pm pm), z ∈ (chartAt ℂ pm).target ∧
      Jy ((chartAt ℂ pm).symm z) ∈ (chartAt ℂ (G₀ x)).source := by
    refine Filter.Eventually.and ((chartAt ℂ pm).open_target.mem_nhds hpmt) ?_
    refine hcont.preimage_mem_nhds ?_
    show (chartAt ℂ (G₀ x)).source ∈ 𝓝 (Jy ((chartAt ℂ pm).symm (chartAt ℂ pm pm)))
    rw [hpmc, hpm]
    exact (chartAt ℂ (G₀ x)).open_source.mem_nhds (mem_chart_source ℂ (G₀ x))
  have hQev : ∀ᶠ z in 𝓝 (chartAt ℂ pm pm),
      Q pm z = conj (Q (G₀ x) (conj (A z))) * deriv A z ^ 2 := by
    filter_upwards [hsrc] with z hz
    have e : conj (A z) = chartAt ℂ (G₀ x) (Jy ((chartAt ℂ pm).symm z)) := Complex.conj_conj _
    rw [e]
    exact s32w_dt_Dfix hQ hJy hpm hD2b hz.1 hz.2
  obtain ⟨hηan, hη0, hηd, hηev⟩ := s32w_dt_refl_nat hζt.1 hζt.2.1 hζt.2.2.1 hζt.2.2.2 hAan hAz hAd hQev
  -- the target double
  have hrm : Jz (Φ pm) = Φ (G₀ x) := by rw [← hΦJ, hpm]
  have hqt : chartAt ℂ (Φ pm) (Φ pm) ∈ (chartAt ℂ (Φ pm)).target :=
    (chartAt ℂ (Φ pm)).map_source (mem_chart_source ℂ (Φ pm))
  set Λ : ℂ → ℂ := fun w => conj (chartAt ℂ (Φ (G₀ x)) (Jz ((chartAt ℂ (Φ pm)).symm w))) with hΛ
  have hΛan : AnalyticAt ℂ Λ (chartAt ℂ (Φ pm) (Φ pm)) := by
    have := s32w_dt_J_an hJz (Φ pm)
    rw [hrm] at this
    exact this
  have hΛd : deriv Λ (chartAt ℂ (Φ pm) (Φ pm)) ≠ 0 := by
    have := s32w_dt_J_deriv_ne hJz (Φ pm)
    rw [hrm] at this
    exact this
  have hΛc : Λ (chartAt ℂ (Φ pm) (Φ pm)) = conj (chartAt ℂ (Φ (G₀ x)) (Φ (G₀ x))) := by
    show conj (chartAt ℂ (Φ (G₀ x)) (Jz ((chartAt ℂ (Φ pm)).symm (chartAt ℂ (Φ pm) (Φ pm))))) = _
    rw [(chartAt ℂ (Φ pm)).left_inv (mem_chart_source ℂ (Φ pm)), hrm]
  have hvc1 : localMapExpr Φ (G₀ x) (chartAt ℂ (G₀ x) (G₀ x)) = chartAt ℂ (Φ (G₀ x)) (Φ (G₀ x)) := by
    show chartAt ℂ (Φ (G₀ x)) (Φ ((chartAt ℂ (G₀ x)).symm (chartAt ℂ (G₀ x) (G₀ x)))) = _
    rw [(chartAt ℂ (G₀ x)).left_inv (mem_chart_source ℂ (G₀ x))]
  have hvc2 : localMapExpr Φ pm (chartAt ℂ pm pm) = chartAt ℂ (Φ pm) (Φ pm) := by
    show chartAt ℂ (Φ pm) (Φ ((chartAt ℂ pm).symm (chartAt ℂ pm pm))) = _
    rw [hpmc]
  rw [hvc1] at han hdr
  have hρ : AnalyticAt ℂ (fun u => conj (ζ₂₁ (conj u))) (Λ (chartAt ℂ (Φ pm) (Φ pm))) := by
    rw [hΛc]
    exact s32w_dt_refl_analytic han
  -- continuity facts for the relation
  have hΦc : ContinuousAt (fun w => Φ ((chartAt ℂ pm).symm w)) (chartAt ℂ pm pm) :=
    Φ.continuous.continuousAt.comp ((chartAt ℂ pm).continuousAt_symm hpmt)
  have hΦsrc : ∀ᶠ z in 𝓝 (chartAt ℂ pm pm), Φ ((chartAt ℂ pm).symm z) ∈ (chartAt ℂ (Φ pm)).source := by
    refine hΦc.preimage_mem_nhds ?_
    show (chartAt ℂ (Φ pm)).source ∈ 𝓝 (Φ ((chartAt ℂ pm).symm (chartAt ℂ pm pm)))
    rw [hpmc]
    exact (chartAt ℂ (Φ pm)).open_source.mem_nhds (mem_chart_source ℂ (Φ pm))
  have hAt : Tendsto A (𝓝 (chartAt ℂ pm pm)) (𝓝 (A (chartAt ℂ pm pm))) := hAan.continuousAt.tendsto
  have hcA : Tendsto (fun z => conj (A z)) (𝓝 (chartAt ℂ pm pm)) (𝓝 (chartAt ℂ (G₀ x) (G₀ x))) := by
    have h1 : Tendsto (fun z => conj (A z)) (𝓝 (chartAt ℂ pm pm)) (𝓝 (conj (A (chartAt ℂ pm pm)))) :=
      (Complex.continuous_conj.tendsto (A (chartAt ℂ pm pm))).comp hAt
    rwa [hAz, Complex.conj_conj] at h1
  have hrel₂ : ∀ᶠ z in 𝓝 (chartAt ℂ pm pm),
      ζ₂₁ (localMapExpr Φ (G₀ x) (conj (A z))) = teichStretch k (ζt₁ (conj (A z))) :=
    hcA.eventually hrel₁
  refine ⟨fun z => conj (ζt₁ (conj (A z))), fun w => conj (ζ₂₁ (conj (Λ w))),
    ⟨hηan, hη0, hηd, hηev⟩, ?_, ?_, ?_⟩
  · rw [hvc2]
    exact hρ.comp hΛan
  · rw [hvc2]
    have hd1 : DifferentiableAt ℂ (fun u => conj (ζ₂₁ (conj u))) (Λ (chartAt ℂ (Φ pm) (Φ pm))) :=
      hρ.differentiableAt
    have h3 : deriv ((fun u => conj (ζ₂₁ (conj u))) ∘ Λ) (chartAt ℂ (Φ pm) (Φ pm)) =
        deriv (fun u => conj (ζ₂₁ (conj u))) (Λ (chartAt ℂ (Φ pm) (Φ pm))) *
          deriv Λ (chartAt ℂ (Φ pm) (Φ pm)) := deriv_comp _ hd1 hΛan.differentiableAt
    have h4 : deriv (fun u => conj (ζ₂₁ (conj u))) (Λ (chartAt ℂ (Φ pm) (Φ pm))) =
        conj (deriv ζ₂₁ (conj (Λ (chartAt ℂ (Φ pm) (Φ pm))))) :=
      congrFun (deriv_conj_conj (f := ζ₂₁)) _
    show deriv ((fun u => conj (ζ₂₁ (conj u))) ∘ Λ) (chartAt ℂ (Φ pm) (Φ pm)) ≠ 0
    rw [h3, h4, hΛc, Complex.conj_conj]
    exact mul_ne_zero ((map_ne_zero _).2 hdr) hΛd
  · filter_upwards [hsrc, hΦsrc, hrel₂] with z hz hc hr
    have hb := hz.2
    have e1 : conj (Λ (localMapExpr Φ pm z)) = localMapExpr Φ (G₀ x) (conj (A z)) := by
      show conj (conj (chartAt ℂ (Φ (G₀ x)) (Jz ((chartAt ℂ (Φ pm)).symm
          (chartAt ℂ (Φ pm) (Φ ((chartAt ℂ pm).symm z))))))) =
        chartAt ℂ (Φ (G₀ x)) (Φ ((chartAt ℂ (G₀ x)).symm (conj (A z))))
      rw [Complex.conj_conj, (chartAt ℂ (Φ pm)).left_inv hc, ← hΦJ]
      have : (chartAt ℂ (G₀ x)).symm (conj (A z)) = Jy ((chartAt ℂ pm).symm z) := by
        show (chartAt ℂ (G₀ x)).symm (conj (conj (chartAt ℂ (G₀ x) (Jy ((chartAt ℂ pm).symm z))))) = _
        rw [Complex.conj_conj]
        exact (chartAt ℂ (G₀ x)).left_inv hb
      rw [this]
    show conj (ζ₂₁ (conj (Λ (localMapExpr Φ pm z)))) = teichStretch k (conj (ζt₁ (conj (A z))))
    rw [e1, hr, s32w_dt_stretch_conj]

end E2

section Assembly

variable {Y₀ : Type u} {Y : Type v} {S : Type w} {Zc : Type u} {W : Type v}
  [TopologicalSpace Y₀] [ChartedSpace ℂ Y₀] [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [TopologicalSpace S] [ChartedSpace ℂ S] [TopologicalSpace Zc] [ChartedSpace ℂ Zc]
  [TopologicalSpace W] [ChartedSpace ℂ W]
  [IsManifold 𝓘(ℂ) ω Y₀] [IsManifold 𝓘(ℂ) ω Y] [IsManifold 𝓘(ℂ) ω S] [IsManifold 𝓘(ℂ) ω Zc]
  [IsManifold 𝓘(ℂ) ω W]

/-- The regular points of a holomorphic quadratic differential form an open set. -/
theorem s32w_dt_reg_open {Q : Y → ℂ → ℂ} (hQ : IsHolQuadDiff Q) : IsOpen {y | IsRegularPoint Q y} := by
  have hQ' : IsDiffFamily 2 0 Q ∧ ∀ x : Y, DifferentiableOn ℂ (Q x) (chartAt ℂ x).target := hQ
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hpt : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have hcont : ContinuousAt (Q p) (chartAt ℂ p p) :=
    ((hQ'.2 p).continuousOn.continuousAt ((chartAt ℂ p).open_target.mem_nhds hpt))
  have hne : ∀ᶠ z in 𝓝 (chartAt ℂ p p), Q p z ≠ 0 := hcont.eventually_ne hp
  have hct : Tendsto (chartAt ℂ p) (𝓝 p) (𝓝 (chartAt ℂ p p)) :=
    (chartAt ℂ p).continuousAt (mem_chart_source ℂ p)
  filter_upwards [hct.eventually hne, (chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p)]
    with p' h1 h2
  have := (s26d_a_isRegularPoint_iff hQ p ((chartAt ℂ p).map_source h2)).2 h1
  rwa [(chartAt ℂ p).left_inv h2] at this

/-- The non-regular points of a nonzero holomorphic quadratic differential are chartwise null. -/
theorem s32w_dt_nonreg_null [ConnectedSpace Y] [T1Space Y] {Q : Y → ℂ → ℂ} (hQ : IsHolQuadDiff Q)
    (hne : Q ≠ 0) (x : Y) :
    volume ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' {p | ¬ IsRegularPoint Q p}) = 0 := by
  refine measure_null_of_locally_null _ (fun z hz => ?_)
  obtain ⟨hzt, hzn⟩ := hz
  have hev := s26d_a_eventually_ne_zero hQ x hzt (s26d_a_frequently_regular hQ hne _)
  refine ⟨{z}, ?_, measure_singleton z⟩
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  obtain ⟨t, ht, hto, hzt'⟩ := _root_.mem_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  refine ⟨t, hto.mem_nhds hzt', ?_⟩
  rintro w ⟨hwt, hwt', hwn⟩
  by_contra hwz
  have h1 : Q x w ≠ 0 := ht hwt hwz
  apply hwn
  exact (s26d_a_isRegularPoint_iff hQ x hwt').2 h1

/-- If `Q` is regular at `G₀ x` then `q` is regular at `x` (the pull-back formula at the chart centre). -/
theorem s32w_dt_reg_back {G₀ : Y₀ → Y} (hG₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₀)
    (hi₀ : Function.Injective G₀) {q : Y₀ → ℂ → ℂ} {Q : Y → ℂ → ℂ}
    (hD2a : ∀ x, ∀ z ∈ (chartAt ℂ x).target,
      q x z = s31qr_transportOn univ G₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x z)
    {x : Y₀} (hQx : IsRegularPoint Q (G₀ x)) : IsRegularPoint q x := by
  have hxc : (chartAt ℂ x).symm (chartAt ℂ x x) = x := (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have hxt : chartAt ℂ x x ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have hd : deriv (fun w => chartAt ℂ (G₀ x) (G₀ ((chartAt ℂ x).symm w))) (chartAt ℂ x x) ≠ 0 := by
    refine s31qr_coordinate_deriv_ne_zero (U := univ) isOpen_univ (H := G₀) (fun p _ => hG₀ p)
      hi₀.injOn x (G₀ x) hxt (mem_univ _) ?_
    rw [hxc]; exact mem_chart_source ℂ (G₀ x)
  have h := hD2a x (chartAt ℂ x x) hxt
  rw [s31qd5_id_transport_apply univ G₀ Q x hxt (mem_univ _), hxc] at h
  show q x (chartAt ℂ x x) ≠ 0
  rw [h]
  exact mul_ne_zero hQx (pow_ne_zero 2 hd)

/-- Regularity transfers across the reflection. -/
theorem s32w_dt_reg_mirror {Q : Y → ℂ → ℂ} (hQ : IsDiffFamily 2 0 Q) {J : Y ≃ₜ Y}
    (hJ : IsAnticonformalInvolution J)
    (hD2b : ∀ y z, z ∈ (chartAt ℂ y).target →
      Q y z = conj (Q (J ((chartAt ℂ y).symm z)) (chartAt ℂ (J ((chartAt ℂ y).symm z))
          (J ((chartAt ℂ y).symm z)))) *
        deriv (fun w => conj (chartAt ℂ (J ((chartAt ℂ y).symm z)) (J ((chartAt ℂ y).symm w)))) z ^ 2)
    {pm p : Y} (hpm : J pm = p) (h : IsRegularPoint Q pm) : IsRegularPoint Q p := by
  have hpmt : chartAt ℂ pm pm ∈ (chartAt ℂ pm).target := (chartAt ℂ pm).map_source (mem_chart_source ℂ pm)
  have hpmc : (chartAt ℂ pm).symm (chartAt ℂ pm pm) = pm := (chartAt ℂ pm).left_inv (mem_chart_source ℂ pm)
  have hzs : J ((chartAt ℂ pm).symm (chartAt ℂ pm pm)) ∈ (chartAt ℂ p).source := by
    rw [hpmc, hpm]; exact mem_chart_source ℂ p
  have := s32w_dt_Dfix hQ hJ hpm hD2b hpmt hzs
  rw [hpmc, hpm] at this
  intro h0
  apply h
  show Q pm (chartAt ℂ pm pm) = 0
  rw [this]
  show conj (Q p (chartAt ℂ p p)) * _ = 0
  rw [h0]; simp

/-- **(D3)** The composite `ι⁻¹ ∘ Φ` is biholomorphic. -/
theorem s32w_dt_D3 [ConnectedSpace Y] [T1Space Y] [SecondCountableTopology W]
    {G₀ : Y₀ → Y} {G₁ : S → Zc} (hG₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₀)
    (hG₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₁) (hi₀ : Function.Injective G₀) (hi₁ : Function.Injective G₁)
    (hG₀o : IsOpenMap G₀) {h : Y₀ ≃ₜ S} {Φ : Y ≃ₜ Zc} (hΦ : ∀ x, Φ (G₀ x) = G₁ (h x))
    (hΦqc : IsQCRS Φ) {q : Y₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {Q : Y → ℂ → ℂ} {k : ℝ}
    (hQ : IsDiffFamily 2 0 Q) (hQhol : IsHolQuadDiff Q) (hQne : Q ≠ 0)
    (hD2a : ∀ x, ∀ z ∈ (chartAt ℂ x).target,
      q x z = s31qr_transportOn univ G₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x z)
    (hh : IsTeichmullerMap h q q' k) {q₁ : W → ℂ → ℂ} {ι : Y ≃ₜ W} (hι : IsTeichmullerMap ι Q q₁ k)
    {Jy : Y ≃ₜ Y} {Jz : Zc ≃ₜ Zc} (hJy : IsAnticonformalInvolution Jy)
    (hJz : IsAnticonformalInvolution Jz) (hΦJ : ∀ y, Φ (Jy y) = Jz (Φ y))
    (hD2b : ∀ y z, z ∈ (chartAt ℂ y).target →
      Q y z = conj (Q (Jy ((chartAt ℂ y).symm z)) (chartAt ℂ (Jy ((chartAt ℂ y).symm z))
          (Jy ((chartAt ℂ y).symm z)))) *
        deriv (fun w => conj (chartAt ℂ (Jy ((chartAt ℂ y).symm z)) (Jy ((chartAt ℂ y).symm w)))) z ^ 2)
    (hcov : ∀ y : Y, (∃ x, G₀ x = y) ∨ (∃ x, Jy (G₀ x) = y) ∨ Jy y = y)
    (hseam : ∀ x : Y, volume ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' {y | Jy y = y}) = 0) :
    IsBiholomorphic (ι.symm.trans Φ) := by
  have hcqc : IsQCRS (ι.symm.trans Φ) := s28q_isQCRS_trans (s28q_isQCRS_symm hι.qc) hΦqc
  set Gd : Set Y := {y | IsRegularPoint Q y ∧ ((∃ x, G₀ x = y) ∨ (∃ x, Jy (G₀ x) = y))} with hGd
  have hGdo : IsOpen Gd := by
    have h1 : IsOpen (range G₀ ∪ Jy '' range G₀) := by
      refine (hG₀o.isOpen_range).union ?_
      exact Jy.isOpenMap _ hG₀o.isOpen_range
    have h2 : Gd = {y | IsRegularPoint Q y} ∩ (range G₀ ∪ Jy '' range G₀) := by
      ext y
      constructor
      · rintro ⟨hy, hy2⟩
        refine ⟨hy, ?_⟩
        rcases hy2 with ⟨x, hx⟩ | ⟨x, hx⟩
        · exact Or.inl ⟨x, hx⟩
        · exact Or.inr ⟨G₀ x, ⟨x, rfl⟩, hx⟩
      · rintro ⟨hy, hy2⟩
        refine ⟨hy, ?_⟩
        rcases hy2 with ⟨x, hx⟩ | ⟨_, ⟨x, rfl⟩, hx⟩
        · exact Or.inl ⟨x, hx⟩
        · exact Or.inr ⟨x, hx⟩
    rw [h2]
    exact (s32w_dt_reg_open hQhol).inter h1
  set O : Set W := ι '' Gd with hO
  have hOo : IsOpen O := ι.isOpenMap _ hGdo
  have hhol : ∀ y' ∈ O, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (ι.symm.trans Φ : W → Zc) y' := by
    intro y' hy'
    obtain ⟨y, ⟨hyreg, hycase⟩, rfl⟩ := hy'
    rcases hycase with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · have hqx := s32w_dt_reg_back hG₀ hi₀ hD2a hyreg
      obtain ⟨ζt, ζ₂, hn, ha, hd, hr⟩ := s32w_dt_E1 hG₀ hG₁ hi₀ hi₁ hΦ hQ hD2a hh hqx
      exact s32w_dt_E_core ι Φ hι hyreg hn ha hd hr
    · have hp : IsRegularPoint Q (G₀ x) := s32w_dt_reg_mirror hQ hJy hD2b (hJy.1 _) hyreg
      have hqx := s32w_dt_reg_back hG₀ hi₀ hD2a hp
      obtain ⟨ζt, ζ₂, hn, ha, hd, hr⟩ := s32w_dt_E2 hG₀ hG₁ hi₀ hi₁ hΦ hQ hD2a hh hqx hJy hJz hΦJ hD2b
        (pm := Jy (G₀ x)) (hJy.1 _)
      exact s32w_dt_E_core ι Φ hι hyreg hn ha hd hr
  have hnull : ∀ x₀ : W, volume ((chartAt ℂ x₀).target ∩ (chartAt ℂ x₀).symm ⁻¹' Oᶜ) = 0 := by
    intro x₀
    have hN : ∀ x : Y, volume ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹'
        ({p | ¬ IsRegularPoint Q p} ∪ {y | Jy y = y})) = 0 := by
      intro x
      refine measure_mono_null (fun z hz => ?_)
        (measure_union_null (s32w_dt_nonreg_null hQhol hQne x) (hseam x))
      rcases hz.2 with h | h
      · exact Or.inl ⟨hz.1, h⟩
      · exact Or.inr ⟨hz.1, h⟩
    have hsub : Oᶜ ⊆ ι '' ({p | ¬ IsRegularPoint Q p} ∪ {y | Jy y = y}) := by
      intro w hw
      obtain ⟨y, rfl⟩ := ι.surjective w
      refine ⟨y, ?_, rfl⟩
      by_cases hr : IsRegularPoint Q y
      · right
        rcases hcov y with h | h | h
        · exact absurd (⟨y, ⟨hr, Or.inl h⟩, rfl⟩ : ι y ∈ ι '' Gd) hw
        · exact absurd (⟨y, ⟨hr, Or.inr h⟩, rfl⟩ : ι y ∈ ι '' Gd) hw
        · exact h
      · left; exact hr
    have h1 := s32w_dt_qc_null ι hι.qc hN x₀
    refine measure_mono_null (fun z (hz : z ∈ (chartAt ℂ x₀).target ∩ (chartAt ℂ x₀).symm ⁻¹' Oᶜ) => ?_) h1
    exact ⟨hz.1, hsub hz.2⟩
  exact s32w_dt_biholo_of_hol_ae _ hcqc O hOo hhol hnull

end Assembly

section Final

/-- **Symmetric extension of a Teichmüller map is a Teichmüller map of the punctured double.**
(Statement frozen with the approved extra hypothesis `hfdQ : IsQCRS fd`; the area conjunct (D3) of the
original proposal is not part of this statement.) -/
theorem s32w_double_teichmuller
    {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀] [ConnectedSpace S₀]
    [IsManifold 𝓘(ℂ) ω S₀]
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier}
    {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    (Fd₀ : FiniteTypeStructure (puncturedOpens Pd₀) (2 * g + m - 1) (2 * n) 0)
    {h : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ}
    (hh : IsAdmissibleTeichmullerMap F₀ h q q' k) (hk : 0 < k)
    {fd : Xd₀.carrier ≃ₜ Xd₁.carrier} (hfd : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ h fd)
    (hfdQ : IsQCRS fd)
    {fdp : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁} (hfdp : ∀ y, (fdp y : Xd₁.carrier) = fd y)
    (Jd₀ : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₀) (hJd₀ : ∀ y, (Jd₀ y : Xd₀.carrier) = J₀ y)
    (G₀ : C(S₀, ↥(puncturedOpens Pd₀))) (hG₀ : ∀ x, (G₀ x : Xd₀.carrier) = ιd₀ x) :
    ∃ (Q : puncturedOpens Pd₀ → ℂ → ℂ) (Q' : puncturedOpens Pd₁ → ℂ → ℂ),
      IsAdmissibleTeichmullerMap Fd₀ fdp Q Q' k ∧
      (∀ x, q x = (chartAt ℂ x).target.indicator fun z =>
        Q (G₀ ((chartAt ℂ x).symm z)) (chartAt ℂ (G₀ ((chartAt ℂ x).symm z)) (G₀ ((chartAt ℂ x).symm z))) *
          deriv (fun w => chartAt ℂ (G₀ ((chartAt ℂ x).symm z)) (G₀ ((chartAt ℂ x).symm w))) z ^ 2) ∧
      (∀ y z, z ∈ (chartAt ℂ y).target →
        Q y z = conj (Q (Jd₀ ((chartAt ℂ y).symm z))
            (chartAt ℂ (Jd₀ ((chartAt ℂ y).symm z)) (Jd₀ ((chartAt ℂ y).symm z)))) *
          deriv (fun w => conj (chartAt ℂ (Jd₀ ((chartAt ℂ y).symm z)) (Jd₀ ((chartAt ℂ y).symm w)))) z ^ 2) := by
  classical
  haveI : ConnectedSpace (puncturedOpens Pd₀) := s32w_punctured_connectedSpace Pd₀
  have hq := hh.1
  have hqne : q ≠ 0 := hh.2.initial_ne
  obtain ⟨Q, hQint, hD2a, hD2b, hQne'⟩ := s32w_dt_Q hm F₀ hd₀ Fd₀ Jd₀ hJd₀ G₀ hG₀ hq
  have hQne : Q ≠ 0 := hQne' hqne
  have hQhol : IsHolQuadDiff Q := (admissibleQDInterior_holomorphic Fd₀).1 Q hQint
  have hQfam : IsDiffFamily 2 0 Q := hQhol.1
  have hexd : ¬ IsExceptionalType (2 * g + m - 1) (2 * n) 0 := by
    intro hE
    apply hex
    unfold IsExceptionalType at hE
    rcases hE with h | h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨h1, h2, h3⟩ := h
    · have : g = 0 ∧ n = 0 ∧ m = 1 := by omega
      unfold IsExceptionalType
      simp [this.1, this.2.1, this.2.2]
    · exact absurd h2 (by omega)
    · have : g = 0 ∧ n = 0 ∧ m = 2 := by omega
      unfold IsExceptionalType
      simp [this.1, this.2.1, this.2.2]
    · have : g = 0 ∧ n = 1 ∧ m = 1 := by omega
      unfold IsExceptionalType
      simp [this.1, this.2.1, this.2.2]
    · exact absurd h3 (by omega)
    · exact absurd h3 (by omega)
    · exact absurd h3 (by omega)
  obtain ⟨A, q₁, hA⟩ := s82td_realize hexd Fd₀ hQint hQne hk hh.2.k_lt_one
  set ι := A.marking with hιdef
  have hι : IsTeichmullerMap ι Q q₁ k := hA.2
  haveI : SecondCountableTopology Xd₀.carrier := ChartedSpace.secondCountable_of_sigmaCompact ℂ Xd₀.carrier
  haveI : SecondCountableTopology A.X.carrier := ι.symm.isEmbedding.secondCountableTopology
  obtain ⟨Jd₁, hJd₁⟩ := s32w_restrict_reflection hd₁
  have hJy : IsAnticonformalInvolution Jd₀ :=
    s32w_dt_opens_involution (puncturedOpens Pd₀) Jd₀ J₀ hd₀.involution hJd₀
  have hJz : IsAnticonformalInvolution Jd₁ :=
    s32w_dt_opens_involution (puncturedOpens Pd₁) Jd₁ J₁ hd₁.involution hJd₁
  -- the half inclusions
  set G₁ : S → puncturedOpens Pd₁ := fun s => fdp (G₀ (h.symm s)) with hG₁def
  have hG₁c : Continuous G₁ := fdp.continuous.comp (G₀.continuous.comp h.symm.continuous)
  have hG₁coe : ∀ s, (G₁ s : Xd₁.carrier) = ιd₁ s := by
    intro s
    show ((fdp (G₀ (h.symm s)) : puncturedOpens Pd₁) : Xd₁.carrier) = _
    rw [hfdp, hG₀, hfd.1, h.apply_symm_apply]
  have hG₀m : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (G₀ : S₀ → puncturedOpens Pd₀) :=
    s32w_dt_mdiff_into_opens (puncturedOpens Pd₀) G₀ G₀.continuous ιd₀ hd₀.holomorphic hG₀
  have hG₁m : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₁ :=
    s32w_dt_mdiff_into_opens (puncturedOpens Pd₁) G₁ hG₁c ιd₁ hd₁.holomorphic hG₁coe
  have hi₀ : Function.Injective (G₀ : S₀ → puncturedOpens Pd₀) := fun a b hab =>
    hd₀.embedding.injective (by rw [← hG₀, ← hG₀, hab])
  have hi₁ : Function.Injective G₁ := fun a b hab =>
    hd₁.embedding.injective (by rw [← hG₁coe, ← hG₁coe, hab])
  have hG₀o : IsOpenMap (G₀ : S₀ → puncturedOpens Pd₀) := by
    intro U hU
    have : (G₀ : S₀ → puncturedOpens Pd₀) '' U = Subtype.val ⁻¹' (ιd₀ '' U) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, (hG₀ x).symm⟩
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, Subtype.ext (by rw [hG₀, hxy])⟩
    rw [this]
    exact (hd₀.embedding.isOpenMap U hU).preimage continuous_subtype_val
  have hΦ : ∀ x, fdp (G₀ x) = G₁ (h x) := fun x => by simp [hG₁def]
  have hΦqc : IsQCRS fdp := s32w_isQCRS_restrict_punctured hfdp hfdQ
  have hΦJ : ∀ y, fdp (Jd₀ y) = Jd₁ (fdp y) := by
    intro y
    apply Subtype.ext
    rw [hJd₁, hfdp, hfdp, hJd₀, hfd.2]
  have hcov : ∀ y : puncturedOpens Pd₀,
      (∃ x, G₀ x = y) ∨ (∃ x, Jd₀ (G₀ x) = y) ∨ Jd₀ y = y := by
    intro y
    have hyP : (y : Xd₀.carrier) ∉ (↑Pd₀ : Set Xd₀.carrier) := y.2
    have hc := hd₀.cover
    have hy : (y : Xd₀.carrier) ∈ (univ : Set Xd₀.carrier) := mem_univ _
    rw [← hc] at hy
    rcases hy with ((hy | hy) | hy) | hy
    · obtain ⟨x, hx⟩ := hy
      exact Or.inl ⟨x, Subtype.ext (by rw [hG₀, hx])⟩
    · obtain ⟨x, hx⟩ := hy
      exact Or.inr (Or.inl ⟨x, Subtype.ext (by rw [hJd₀, hG₀]; exact hx)⟩)
    · exact Or.inr (Or.inr (Subtype.ext (by rw [hJd₀]; exact hy)))
    · exact absurd hy hyP
  have hseam : ∀ x : puncturedOpens Pd₀, volume ((chartAt ℂ x).target ∩
      (chartAt ℂ x).symm ⁻¹' {y | Jd₀ y = y}) = 0 := by
    intro x
    obtain ⟨hx1, -, -⟩ := s32w_opens_chart_facts (puncturedOpens Pd₀) x
    refine measure_mono_null (fun z hz => ?_) (s32w_dt_seam_null F₀ hd₀ (x : Xd₀.carrier))
    obtain ⟨hz1, hz2⟩ := hx1 z hz.1
    refine ⟨hz1, ?_⟩
    have h1 : Jd₀ ((chartAt ℂ x).symm z) = (chartAt ℂ x).symm z := hz.2
    have h2 := congrArg Subtype.val h1
    rw [hJd₀, hz2] at h2
    show J₀ ((chartAt ℂ (x : Xd₀.carrier)).symm z) = _
    exact h2
  have hD2a' : ∀ x, ∀ z ∈ (chartAt ℂ x).target,
      q x z = s31qr_transportOn univ (G₀ : S₀ → puncturedOpens Pd₀)
        (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x z := by
    intro x z hz
    have h1 := congrFun (hD2a x) z
    rw [Set.indicator_of_mem hz] at h1
    rw [h1, s31qd5_id_transport_apply univ (G₀ : S₀ → puncturedOpens Pd₀) Q x hz (mem_univ _)]
  have hD3 : IsBiholomorphic (ι.symm.trans fdp) :=
    s32w_dt_D3 hG₀m hG₁m hi₀ hi₁ hG₀o hΦ hΦqc hQfam hQhol hQne hD2a' hh.2 hι hJy hJz hΦJ hD2b hcov hseam
  obtain ⟨Q', hT⟩ := s32w_dt_teich_comp ι (ι.symm.trans fdp) hD3 hι
  have hcomp : ι.trans (ι.symm.trans fdp) = fdp := Homeomorph.ext (fun y => by simp)
  rw [hcomp] at hT
  exact ⟨Q, Q', ⟨hQint, hT⟩, hD2a, hD2b⟩

end Final

end LiZhongQC
