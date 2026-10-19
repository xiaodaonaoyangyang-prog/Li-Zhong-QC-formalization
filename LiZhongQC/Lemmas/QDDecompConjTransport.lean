import LiZhongQC.Lemmas.QDSeamFill
import LiZhongQC.Lemmas.QDReflectionPuncturePoles

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u v

section Generic
variable {A : Type u} {B : Type v} [TopologicalSpace A] [ChartedSpace ℂ A]
  [TopologicalSpace B] [ChartedSpace ℂ B]

/-- The value of the canonical-point transport at a point of its piece. -/
theorem s31dc_transport_eq (U : Set B) (H : B → A) (C : ℂ →ₗ[ℝ] ℂ) (q : A → ℂ → ℂ)
    (x : B) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) (hU : (chartAt ℂ x).symm z ∈ U) :
    s31qr_transportOn U H C q x z =
      C (q (H ((chartAt ℂ x).symm z))
        (chartAt ℂ (H ((chartAt ℂ x).symm z)) (H ((chartAt ℂ x).symm z)))) *
        deriv (fun w => C (chartAt ℂ (H ((chartAt ℂ x).symm z))
          (H ((chartAt ℂ x).symm w)))) z ^ 2 := by
  simp only [s31qr_transportOn, hz, hU, and_self, if_true]

/-- The transport vanishes off the chart target. -/
theorem s31dc_transport_off_target (U : Set B) (H : B → A) (C : ℂ →ₗ[ℝ] ℂ) (q : A → ℂ → ℂ)
    (x : B) {z : ℂ} (hz : z ∉ (chartAt ℂ x).target) :
    s31qr_transportOn U H C q x z = 0 := by
  simp only [s31qr_transportOn, hz, false_and, if_false]

end Generic

/-- (S3) Conjugate transport is conjugate linear over `ℂ`. -/
theorem s31qd_conj_transport_smul {A B : Type*} [TopologicalSpace A] [ChartedSpace ℂ A]
    [TopologicalSpace B] [ChartedSpace ℂ B] (U : Set B) (H : B → A) (c : ℂ) (q : A → ℂ → ℂ) :
    s31qr_transportOn U H Complex.conjCLE.toLinearMap (c • q) =
      conj c • s31qr_transportOn U H Complex.conjCLE.toLinearMap q := by
  have hC : ∀ t : ℂ, Complex.conjCLE.toLinearMap t = conj t := fun t => rfl
  funext x z
  simp only [Pi.smul_apply]
  by_cases hz : z ∈ (chartAt ℂ x).target
  · by_cases hU : (chartAt ℂ x).symm z ∈ U
    · rw [s31dc_transport_eq U H _ (c • q) x hz hU, s31dc_transport_eq U H _ q x hz hU]
      simp only [hC, Pi.smul_apply, smul_eq_mul, map_mul]
      ring
    · rw [s31qr_transport_off_piece U H _ (c • q) x z hU, s31qr_transport_off_piece U H _ q x z hU,
        smul_zero]
  · rw [s31dc_transport_off_target U H _ (c • q) x hz, s31dc_transport_off_target U H _ q x hz,
      smul_zero]

section Conj
variable {Z : Type u} {Y : Type v} [TopologicalSpace Z] [ChartedSpace ℂ Z]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Z] [IsManifold 𝓘(ℂ) ω Y]

/-- The conjugated coordinate expression of `E ∘ J ∘ E⁻¹` is holomorphic in any fixed target chart. -/
theorem s31dc_coord_diff (E : Z ≃ₜ Y) (hE : IsBiholomorphic (E : Z → Y))
    {J : Z ≃ₜ Z} (hJ : IsAnticonformalInvolution J) (x a : Y) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target)
    (ha : E (J (E.symm ((chartAt ℂ x).symm z))) ∈ (chartAt ℂ a).source) :
    DifferentiableAt ℂ
      (fun w => conj (chartAt ℂ a (E (J (E.symm ((chartAt ℂ x).symm w)))))) z := by
  have hyy : E.symm ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (E.symm ((chartAt ℂ x).symm z))).source :=
    mem_chart_source ℂ _
  have hu : DifferentiableAt ℂ
      (fun w => chartAt ℂ (E.symm ((chartAt ℂ x).symm z)) (E.symm ((chartAt ℂ x).symm w))) z :=
    s31qr_coordinate_differentiable (H := (E.symm : Y → Z)) x _ hz hyy
      (hE.homeomorph_symm.1 _)
  have hu0t : chartAt ℂ (E.symm ((chartAt ℂ x).symm z)) (E.symm ((chartAt ℂ x).symm z)) ∈
      (chartAt ℂ (E.symm ((chartAt ℂ x).symm z))).target :=
    (chartAt ℂ _).map_source hyy
  have hsy : (chartAt ℂ (E.symm ((chartAt ℂ x).symm z))).symm
      (chartAt ℂ (E.symm ((chartAt ℂ x).symm z)) (E.symm ((chartAt ℂ x).symm z))) =
      E.symm ((chartAt ℂ x).symm z) := (chartAt ℂ _).left_inv hyy
  have hg := s31q2_return_after_involution_chart J hJ (E : Z → Y)
    (E.symm ((chartAt ℂ x).symm z)) a hu0t (by rw [hsy]; exact ha)
    (by rw [hsy]; exact hE.1 _)
  have hcont : ContinuousAt (fun w => E.symm ((chartAt ℂ x).symm w)) z :=
    E.symm.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz)
  have hev : (fun w => conj (chartAt ℂ a (E (J (E.symm ((chartAt ℂ x).symm w)))))) =ᶠ[𝓝 z]
      (fun v => conj (chartAt ℂ a (E (J ((chartAt ℂ (E.symm ((chartAt ℂ x).symm z))).symm v))))) ∘
        (fun w => chartAt ℂ (E.symm ((chartAt ℂ x).symm z)) (E.symm ((chartAt ℂ x).symm w))) := by
    filter_upwards [hcont.preimage_mem_nhds ((chartAt ℂ _).open_source.mem_nhds hyy)] with w hw
    simp only [Function.comp_apply]
    rw [(chartAt ℂ _).left_inv hw]
  exact (hg.comp z hu).congr_of_eventuallyEq hev

/-- The conjugate `E ∘ J ∘ E⁻¹` of an anticonformal involution by a biholomorphism is an
anticonformal involution. -/
theorem s31dc_involution (E : Z ≃ₜ Y) (hE : IsBiholomorphic (E : Z → Y))
    {J : Z ≃ₜ Z} (hJ : IsAnticonformalInvolution J) :
    ∃ K : Y ≃ₜ Y, (∀ y, K y = E (J (E.symm y))) ∧ IsAnticonformalInvolution K := by
  refine ⟨E.symm.trans (J.trans E), fun y => rfl, ?_, ?_⟩
  · intro p
    show E (J (E.symm (E (J (E.symm p))))) = p
    rw [E.symm_apply_apply, hJ.1, E.apply_symm_apply]
  · intro x z hz
    exact (s31dc_coord_diff E hE hJ x (E.symm.trans (J.trans E) x) hz.1 hz.2).differentiableWithinAt

end Conj

/-- (S1) The conjugate transport along the anticonformal involution `E ∘ J ∘ E⁻¹` of the compactified
double `Fd.X` maps admissible differentials of `Fd` (no holes; simple poles at `Fd.P`) to admissible
differentials. -/
theorem s31qd_conj_admissible
    (Xd : ClosedRS.{u}) (Pd : Finset Xd.carrier) {gd nd : ℕ}
    (Fd : FiniteTypeStructure (puncturedOpens Pd) gd nd 0)
    (E : Xd.carrier ≃ₜ Fd.X.carrier) (hE : IsBiholomorphic (E : Xd.carrier → Fd.X.carrier))
    (hP : ∀ p : Xd.carrier, p ∈ Pd ↔ E p ∈ Fd.P)
    {J : Xd.carrier ≃ₜ Xd.carrier} (hJ : IsAnticonformalInvolution J)
    (hJP : J '' (↑Pd : Set Xd.carrier) = ↑Pd)
    {Q : Fd.X.carrier → ℂ → ℂ} (hQ : IsAdmissibleQD Fd Q) :
    IsAdmissibleQD Fd (s31qr_transportOn univ (fun y : Fd.X.carrier => E (J (E.symm y)))
      Complex.conjCLE.toLinearMap Q) := by
  classical
  obtain ⟨K, hKe, hK⟩ := s31dc_involution E hE hJ
  have hfun : (fun y : Fd.X.carrier => E (J (E.symm y))) = K := funext fun y => (hKe y).symm
  rw [hfun]
  have hC : ∀ t : ℂ, Complex.conjCLE.toLinearMap t = conj t := fun t => rfl
  have hJmem : ∀ q : Xd.carrier, J q ∈ Pd ↔ q ∈ Pd := by
    intro q
    constructor
    · intro h
      have h' : J q ∈ J '' (↑Pd : Set Xd.carrier) := by
        rw [hJP]; exact Finset.mem_coe.2 h
      obtain ⟨r, hr, hrq⟩ := h'
      have := J.injective hrq
      rw [← this]
      exact Finset.mem_coe.1 hr
    · intro h
      have : J q ∈ J '' (↑Pd : Set Xd.carrier) := ⟨q, Finset.mem_coe.2 h, rfl⟩
      rw [hJP] at this
      exact Finset.mem_coe.1 this
  have hKP : ∀ p : Fd.X.carrier, K p ∈ Fd.P ↔ p ∈ Fd.P := by
    intro p
    rw [hKe, ← hP, hJmem, hP, E.apply_symm_apply]
  have hRange : range Fd.ι = (↑Fd.P : Set Fd.X.carrier)ᶜ := by simpa using Fd.range_ι
  have hU : IsOpen ((↑Fd.P : Set Fd.X.carrier)ᶜ) := Fd.P.finite_toSet.isClosed.isOpen_compl
  have hdiff : IsDiffFamily 2 0 (s31qr_transportOn univ K Complex.conjCLE.toLinearMap Q) :=
    s31qr_transport_family univ K _ (fun x z hz _ => s31qr_involution_coordinate K hK x hz) Q
  refine ⟨hdiff, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hRange]
    have hqd : ∀ a : Fd.X.carrier, DifferentiableOn ℂ (Q a)
        ((chartAt ℂ a).target ∩ (chartAt ℂ a).symm ⁻¹' (↑Fd.P : Set Fd.X.carrier)ᶜ) := by
      intro a
      have := hQ.2.1 a
      rwa [hRange] at this
    have hb := s31q2_conj_transport_holomorphic K hK (U := (↑Fd.P : Set Fd.X.carrier)ᶜ) hU
      (V := (↑Fd.P : Set Fd.X.carrier)ᶜ) hU (H := id)
      (fun p _ => mdifferentiableAt_id) (fun p hp => hp) hQ.1 hqd x
    have hpre : K ⁻¹' (↑Fd.P : Set Fd.X.carrier)ᶜ = (↑Fd.P : Set Fd.X.carrier)ᶜ := by
      ext p
      simp [hKP p]
    rw [hpre] at hb
    refine hb.congr ?_
    intro z hz
    have e1 := s31dc_transport_eq univ K Complex.conjCLE.toLinearMap Q x hz.1 (mem_univ _)
    have e2 := s31dc_transport_eq ((↑Fd.P : Set Fd.X.carrier)ᶜ) (id ∘ K)
      Complex.conjCLE.toLinearMap Q x hz.1 hz.2
    exact e1.trans e2.symm
  · intro x p hp hs
    have haP : K p ∈ Fd.P := (hKP p).2 hp
    have hw : chartAt ℂ x p ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hs
    have hleft : (chartAt ℂ x).symm (chartAt ℂ x p) = p := (chartAt ℂ x).left_inv hs
    obtain ⟨hzero, c, r, hr, he⟩ := hQ.2.2.1 (K p) (K p) haP (mem_chart_source ℂ (K p))
    let τ : ℂ → ℂ := fun w => conj (chartAt ℂ (K p) (K ((chartAt ℂ x).symm w)))
    let W : Set ℂ := (chartAt ℂ x).target ∩
      (chartAt ℂ x).symm ⁻¹' (K ⁻¹' (chartAt ℂ (K p)).source)
    have hWo : IsOpen W := (chartAt ℂ x).isOpen_inter_preimage_symm
      ((chartAt ℂ (K p)).open_source.preimage K.continuous)
    have hwW : chartAt ℂ x p ∈ W := by
      refine ⟨hw, ?_⟩
      show K ((chartAt ℂ x).symm (chartAt ℂ x p)) ∈ (chartAt ℂ (K p)).source
      rw [hleft]
      exact mem_chart_source ℂ (K p)
    have hτd : ∀ z ∈ W, DifferentiableAt ℂ τ z := fun z hz =>
      s31q2_return_after_involution_chart K hK id x (K p) hz.1 hz.2 mdifferentiableAt_id
    have hTd : DifferentiableOn ℂ τ W := fun z hz => (hτd z hz).differentiableWithinAt
    have hτa : AnalyticAt ℂ τ (chartAt ℂ x p) := hTd.analyticOnNhd hWo _ hwW
    have hinj : InjOn τ W := by
      intro z₁ h₁ z₂ h₂ he'
      have e1 : chartAt ℂ (K p) (K ((chartAt ℂ x).symm z₁)) =
          chartAt ℂ (K p) (K ((chartAt ℂ x).symm z₂)) := by
        have := congrArg conj he'
        simpa [τ] using this
      have e2 := (chartAt ℂ (K p)).injOn h₁.2 h₂.2 e1
      have e3 := K.injective e2
      calc z₁ = chartAt ℂ x ((chartAt ℂ x).symm z₁) := ((chartAt ℂ x).right_inv h₁.1).symm
        _ = chartAt ℂ x ((chartAt ℂ x).symm z₂) := by rw [e3]
        _ = z₂ := (chartAt ℂ x).right_inv h₂.1
    have hτd' : deriv τ (chartAt ℂ x p) ≠ 0 := deriv_ne_zero_of_injOn hWo hTd hinj hwW
    have hτ0 : τ (chartAt ℂ x p) = conj (chartAt ℂ (K p) (K p)) := by
      show conj (chartAt ℂ (K p) (K ((chartAt ℂ x).symm (chartAt ℂ x p)))) = _
      rw [hleft]
    have hloc : ∀ z ∈ W, s31qr_transportOn univ K Complex.conjCLE.toLinearMap Q x z =
        (fun u => conj (Q (K p) (conj u))) (τ z) * deriv τ z ^ 2 := by
      intro z hz
      have h := s31q2_conj_transport_local (U := univ) (H := id) (q := Q) hQ.1 K hK x (K p)
        hz.1 (mem_univ _) hz.2 mdifferentiableAt_id
      refine h.trans ?_
      change _ = conj (Q (K p) (conj (conj (chartAt ℂ (K p) (K ((chartAt ℂ x).symm z)))))) *
        deriv τ z ^ 2
      rw [Complex.conj_conj]
      rfl
    have hconj_t : Tendsto conj (𝓝[≠] (conj (chartAt ℂ (K p) (K p))))
        (𝓝[≠] (chartAt ℂ (K p) (K p))) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h := (Complex.continuous_conj.continuousAt
          (x := conj (chartAt ℂ (K p) (K p)))).tendsto
        rw [Complex.conj_conj] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu h
        apply hu
        have := congrArg conj h
        rw [Complex.conj_conj] at this
        exact this
    have hbar_exp : ∀ᶠ u in 𝓝[≠] (conj (chartAt ℂ (K p) (K p))),
        conj (Q (K p) (conj u)) =
          conj c / (u - conj (chartAt ℂ (K p) (K p))) + conj (r (conj u)) := by
      filter_upwards [hconj_t.eventually he] with u hu
      rw [hu]
      simp [map_add, map_div₀, map_sub]
    have hbar_an : AnalyticAt ℂ (fun u => conj (r (conj u))) (conj (chartAt ℂ (K p) (K p))) := by
      rw [Complex.analyticAt_iff_eventually_differentiableAt]
      have hdr : ∀ᶠ v in 𝓝 (chartAt ℂ (K p) (K p)), DifferentiableAt ℂ r v := by
        rw [Complex.analyticAt_iff_eventually_differentiableAt] at hr
        exact hr
      have hct : Tendsto conj (𝓝 (conj (chartAt ℂ (K p) (K p)))) (𝓝 (chartAt ℂ (K p) (K p))) := by
        have h := (Complex.continuous_conj.continuousAt
          (x := conj (chartAt ℂ (K p) (K p)))).tendsto
        rwa [Complex.conj_conj] at h
      filter_upwards [hct.eventually hdr] with u hu
      have := hu.conj_conj
      simpa [Function.comp_def] using this
    obtain ⟨hval, c', r', hr', hev'⟩ := s31qr_simple_pole_pullback
      (f := fun u => conj (Q (K p) (conj u))) (r := fun u => conj (r (conj u))) (τ := τ)
      (p := chartAt ℂ x p) (c := conj c) hτa hτd'
      (by
        show conj (Q (K p) (conj (τ (chartAt ℂ x p)))) = 0
        rw [hτ0, Complex.conj_conj, hzero, map_zero])
      (by rw [hτ0]; exact hbar_an)
      (by rw [hτ0]; exact hbar_exp)
    refine ⟨?_, c', r', hr', ?_⟩
    · rw [hloc _ hwW]
      exact hval
    · filter_upwards [nhdsWithin_le_nhds (s := {chartAt ℂ x p}ᶜ) (hWo.mem_nhds hwW), hev']
        with z hz1 hz2
      rw [hloc z hz1]
      exact hz2
  · intro x j
    exact Fin.elim0 j
  · intro x j
    exact Fin.elim0 j
  · intro x j
    exact Fin.elim0 j

/-- (S2) The conjugate transport along `E ∘ J ∘ E⁻¹` is an involution on quadratic differential
families (chain rule for the two antiholomorphic coordinate changes, `J ∘ J = id`, tensor law). -/
theorem s31qd_conj_involutive
    (Xd : ClosedRS.{u}) (Pd : Finset Xd.carrier) {gd nd : ℕ}
    (Fd : FiniteTypeStructure (puncturedOpens Pd) gd nd 0)
    (E : Xd.carrier ≃ₜ Fd.X.carrier) (hE : IsBiholomorphic (E : Xd.carrier → Fd.X.carrier))
    {J : Xd.carrier ≃ₜ Xd.carrier} (hJ : IsAnticonformalInvolution J)
    {Q : Fd.X.carrier → ℂ → ℂ} (hQ : IsDiffFamily 2 0 Q) :
    s31qr_transportOn univ (fun y : Fd.X.carrier => E (J (E.symm y))) Complex.conjCLE.toLinearMap
      (s31qr_transportOn univ (fun y : Fd.X.carrier => E (J (E.symm y))) Complex.conjCLE.toLinearMap Q) =
      Q := by
  classical
  obtain ⟨K, hKe, hK⟩ := s31dc_involution E hE hJ
  have hfun : (fun y : Fd.X.carrier => E (J (E.symm y))) = K := funext fun y => (hKe y).symm
  rw [hfun]
  have hC : ∀ t : ℂ, Complex.conjCLE.toLinearMap t = conj t := fun t => rfl
  have hKK : ∀ y, K (K y) = y := hK.1
  have hinner : ∀ b : Fd.X.carrier,
      s31qr_transportOn univ K Complex.conjCLE.toLinearMap Q b (chartAt ℂ b b) =
        conj (Q (K b) (chartAt ℂ (K b) (K b))) *
          deriv (fun v => conj (chartAt ℂ (K b) (K ((chartAt ℂ b).symm v))))
            (chartAt ℂ b b) ^ 2 := by
    intro b
    have hbt : chartAt ℂ b b ∈ (chartAt ℂ b).target :=
      (chartAt ℂ b).map_source (mem_chart_source ℂ b)
    have e := s31dc_transport_eq univ K Complex.conjCLE.toLinearMap Q b hbt (mem_univ _)
    rw [(chartAt ℂ b).left_inv (mem_chart_source ℂ b)] at e
    exact e
  funext x z
  by_cases hz : z ∈ (chartAt ℂ x).target
  swap
  · rw [s31dc_transport_off_target _ _ _ _ x hz, hQ.1 x z hz]
  obtain ⟨p, hp⟩ : ∃ p, p = (chartAt ℂ x).symm z := ⟨_, rfl⟩
  have hps : p ∈ (chartAt ℂ x).source := by rw [hp]; exact (chartAt ℂ x).map_target hz
  have e1 := s31dc_transport_eq univ K Complex.conjCLE.toLinearMap
    (s31qr_transportOn univ K Complex.conjCLE.toLinearMap Q) x hz (mem_univ _)
  rw [← hp] at e1
  rw [e1, hinner (K p), hKK p]
  simp only [hC]
  have hQx : Q x z = Q p (chartAt ℂ p p) * deriv (chartTransition p x) z ^ 2 := by
    have hh := hQ.2 p x z hz (by rw [← hp]; exact mem_chart_source ℂ p)
    have he : chartTransition p x z = chartAt ℂ p p := by
      change chartAt ℂ p ((chartAt ℂ x).symm z) = _
      rw [← hp]
    simpa only [he, zpow_zero, mul_one, zpow_two, pow_two] using hh
  have hbt : chartAt ℂ (K p) (K p) ∈ (chartAt ℂ (K p)).target :=
    (chartAt ℂ (K p)).map_source (mem_chart_source ℂ (K p))
  have hsb : (chartAt ℂ (K p)).symm (chartAt ℂ (K p) (K p)) = K p :=
    (chartAt ℂ (K p)).left_inv (mem_chart_source ℂ (K p))
  let f : ℂ → ℂ := fun w => conj (chartAt ℂ (K p) (K ((chartAt ℂ x).symm w)))
  let g : ℂ → ℂ := fun v => conj (chartAt ℂ p (K ((chartAt ℂ (K p)).symm v)))
  have hf : DifferentiableAt ℂ f z :=
    s31q2_return_after_involution_chart K hK (id : Fd.X.carrier → Fd.X.carrier) x (K p) hz
      (by rw [← hp]; exact mem_chart_source ℂ (K p)) mdifferentiableAt_id
  have hg : DifferentiableAt ℂ g (chartAt ℂ (K p) (K p)) :=
    s31q2_return_after_involution_chart K hK (id : Fd.X.carrier → Fd.X.carrier) (K p) p hbt
      (by rw [hsb, hKK]; exact mem_chart_source ℂ p) mdifferentiableAt_id
  have hfz : f z = conj (chartAt ℂ (K p) (K p)) := by
    show conj (chartAt ℂ (K p) (K ((chartAt ℂ x).symm z))) = _
    rw [← hp]
  have hcontK : ContinuousAt (fun w => K ((chartAt ℂ x).symm w)) z :=
    K.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz)
  have hnb : (chartAt ℂ (K p)).source ∈ 𝓝 (K ((chartAt ℂ x).symm z)) :=
    (chartAt ℂ (K p)).open_source.mem_nhds (by rw [← hp]; exact mem_chart_source ℂ (K p))
  have hev : (fun w => chartAt ℂ p ((chartAt ℂ x).symm w)) =ᶠ[𝓝 z]
      (conj ∘ g ∘ conj) ∘ f := by
    filter_upwards [hcontK.preimage_mem_nhds hnb] with w hw
    have hw' : K ((chartAt ℂ x).symm w) ∈ (chartAt ℂ (K p)).source := hw
    show chartAt ℂ p ((chartAt ℂ x).symm w) =
      conj (conj (chartAt ℂ p (K ((chartAt ℂ (K p)).symm
        (conj (conj (chartAt ℂ (K p) (K ((chartAt ℂ x).symm w)))))))))
    simp only [Complex.conj_conj]
    rw [(chartAt ℂ (K p)).left_inv hw', hKK]
  have hcc : HasDerivAt (conj ∘ g ∘ conj) (conj (deriv g (chartAt ℂ (K p) (K p))))
      (conj (chartAt ℂ (K p) (K p))) := hg.hasDerivAt.conj_conj
  have hcc' : HasDerivAt (conj ∘ g ∘ conj) (conj (deriv g (chartAt ℂ (K p) (K p)))) (f z) := by
    rw [hfz]
    exact hcc
  have hder : conj (deriv g (chartAt ℂ (K p) (K p))) * deriv f z =
      deriv (chartTransition p x) z := by
    change _ = deriv (fun w => chartAt ℂ p ((chartAt ℂ x).symm w)) z
    rw [hev.deriv_eq]
    exact (hcc'.comp z hf.hasDerivAt).deriv.symm
  rw [hQx, ← hder]
  simp only [map_mul, map_pow, Complex.conj_conj]
  ring

end LiZhongQC
