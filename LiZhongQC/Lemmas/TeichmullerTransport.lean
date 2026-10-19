import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
import LiZhongQC.Lemmas.UniformizedUniqueness
import LiZhongQC.Ch08.S29_TeichmullerMetric
import LiZhongQC.Lemmas.UniformizedTeichmuller
import LiZhongQC.Lemmas.Conformal
import LiZhongQC.Lemmas.QDReflectionTwoHalves
import LiZhongQC.Lemmas.QDDecompExtFixed
import LiZhongQC.Lemmas.QDSeamFill
import LiZhongQC.Lemmas.QDDecompConjTransport
import LiZhongQC.Lemmas.QDReflectionAfterHalves
import LiZhongQC.Lemmas.TeichmullerCommutesReflection

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u


section
variable {B : Type u} [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B]

/-- **Fixed-chart formula for the conjugate transport.**  Near the centre of the chart at `p`, the conjugate
transport of a holomorphic quadratic differential `q` through the anticonformal `J` is read in the chart at `p`
through the local expression `L = φ_{J p} ∘ J ∘ φ_p⁻¹`: `q̃_p(z) = conj (q_{J p}(L z)) · (conj ∘ L)'(z)²`. -/
theorem s82tt_transport_local {J : B ≃ₜ B} (hJ : IsAnticonformalInvolution J) {q : B → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (p : B) :
    ∀ᶠ z in 𝓝 (chartAt ℂ p p), s31qr_transportOn univ J Complex.conjCLE.toLinearMap q p z =
      conj (q (J p) (localMapExpr J p z)) * deriv (fun w => conj (localMapExpr J p w)) z ^ 2 := by
  have hps : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
  have hc0t : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source hps
  have hcont : ContinuousAt (fun z => J ((chartAt ℂ p).symm z)) (chartAt ℂ p p) :=
    J.continuous.continuousAt.comp ((chartAt ℂ p).continuousAt_symm hc0t)
  have hsrc : ∀ᶠ z in 𝓝 (chartAt ℂ p p), J ((chartAt ℂ p).symm z) ∈ (chartAt ℂ (J p)).source := by
    refine hcont.eventually_mem ?_
    show (chartAt ℂ (J p)).source ∈ 𝓝 (J ((chartAt ℂ p).symm (chartAt ℂ p p)))
    rw [(chartAt ℂ p).left_inv hps]
    exact (chartAt ℂ (J p)).open_source.mem_nhds (mem_chart_source ℂ (J p))
  filter_upwards [(chartAt ℂ p).open_target.mem_nhds hc0t, hsrc] with z hzt hzs
  rw [s31qd5_conj_transport_apply univ J q p hzt (mem_univ _)]
  set a : B := (chartAt ℂ p).symm z with ha
  set c : ℂ := chartAt ℂ (J a) (J a) with hc
  have hct : c ∈ (chartAt ℂ (J a)).target := (chartAt ℂ (J a)).map_source (mem_chart_source ℂ (J a))
  have hcs : (chartAt ℂ (J a)).symm c ∈ (chartAt ℂ (J p)).source := by
    rw [hc, (chartAt ℂ (J a)).left_inv (mem_chart_source ℂ (J a))]; exact hzs
  have hlaw := s26u_law hq (J a) (J p) hct hcs
  have hTc : chartTransition (J p) (J a) c = localMapExpr J p z := by
    simp only [chartTransition, hc, (chartAt ℂ (J a)).left_inv (mem_chart_source ℂ (J a))]
    rfl
  rw [hTc] at hlaw
  have hTd : DifferentiableAt ℂ (chartTransition (J p) (J a)) c :=
    s23_transition_differentiableAt (J p) (J a) hct hcs
  have hM : DifferentiableAt ℂ (fun w => conj (chartAt ℂ (J a) (J ((chartAt ℂ p).symm w)))) z :=
    s31qr_involution_coordinate J hJ p hzt
  have hMz : conj (chartAt ℂ (J a) (J ((chartAt ℂ p).symm z))) = conj c := rfl
  -- L = T ∘ (conj ∘ M ∘ ...) near z
  have hev : (fun w => conj (localMapExpr J p w)) =ᶠ[𝓝 z]
      fun w => (conj ∘ chartTransition (J p) (J a) ∘ conj)
        (conj (chartAt ℂ (J a) (J ((chartAt ℂ p).symm w)))) := by
    have hcont2 : ContinuousAt (fun w => J ((chartAt ℂ p).symm w)) z :=
      J.continuous.continuousAt.comp ((chartAt ℂ p).continuousAt_symm hzt)
    have h1 : ∀ᶠ w in 𝓝 z, J ((chartAt ℂ p).symm w) ∈ (chartAt ℂ (J a)).source :=
      hcont2.eventually_mem ((chartAt ℂ (J a)).open_source.mem_nhds (mem_chart_source ℂ (J a)))
    filter_upwards [h1] with w hw
    simp only [Function.comp_apply, conj_conj, chartTransition, localMapExpr]
    rw [(chartAt ℂ (J a)).left_inv hw]
  have hG : DifferentiableAt ℂ (conj ∘ chartTransition (J p) (J a) ∘ conj) (conj c) := hTd.conj_conj
  have hderiv : deriv (fun w => conj (localMapExpr J p w)) z =
      conj (deriv (chartTransition (J p) (J a)) c) *
        deriv (fun w => conj (chartAt ℂ (J a) (J ((chartAt ℂ p).symm w)))) z := by
    rw [hev.deriv_eq]
    have := deriv_comp z (h₂ := conj ∘ chartTransition (J p) (J a) ∘ conj)
      (h := fun w => conj (chartAt ℂ (J a) (J ((chartAt ℂ p).symm w)))) (by rw [hMz]; exact hG) hM
    simp only [Function.comp_def] at this ⊢
    rw [this, hMz]
    have hd := congrFun (deriv_conj_conj (f := chartTransition (J p) (J a))) (conj c)
    simp only [Function.comp_apply, conj_conj] at hd
    have hd' : deriv (fun x => conj (chartTransition (J p) (J a) (conj x))) (conj c) =
        conj (deriv (chartTransition (J p) (J a)) c) := hd
    rw [hd']
  rw [hderiv, hlaw]
  simp only [map_mul, map_pow]
  ring

end

section
variable {B : Type u} [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B]

theorem s82tt_L_center {J : B ≃ₜ B} (p : B) :
    localMapExpr J p (chartAt ℂ p p) = chartAt ℂ (J p) (J p) := (s23_h_center J p).2

theorem s82tt_L_continuousAt {J : B ≃ₜ B} (hJ : IsAnticonformalInvolution J) (p : B) :
    ContinuousAt (localMapExpr J p) (chartAt ℂ p p) := by
  have h := (s82rc_anti_local hJ.2 p).1.continuousAt
  have h2 : ContinuousAt (fun z => conj (conj (localMapExpr J p z))) (chartAt ℂ p p) :=
    Complex.continuous_conj.continuousAt.comp h
  simpa using h2

/-- A point is regular for the conjugate transport iff its mirror image is regular. -/
theorem s82tt_regular_iff {J : B ≃ₜ B} (hJ : IsAnticonformalInvolution J) {q : B → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (p : B) :
    IsRegularPoint (s31qr_transportOn univ J Complex.conjCLE.toLinearMap q) p ↔ IsRegularPoint q (J p) := by
  have h := (s82tt_transport_local hJ hq p).self_of_nhds
  rw [s82tt_L_center] at h
  have hd := (s82rc_anti_local hJ.2 p).2
  unfold IsRegularPoint
  rw [h]
  simp [hd]

/-- Natural parameters are transported by `ζ ↦ conj ∘ ζ ∘ L`. -/
theorem s82tt_natural {J : B ≃ₜ B} (hJ : IsAnticonformalInvolution J) {q : B → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (p : B) {ζ : ℂ → ℂ} (hζ : IsNaturalParameterAt q (J p) ζ) :
    IsNaturalParameterAt (s31qr_transportOn univ J Complex.conjCLE.toLinearMap q) p
      (fun z => conj (ζ (localMapExpr J p z))) := by
  obtain ⟨hζan, hζ0, hζd, hζq⟩ := hζ
  obtain ⟨hτan, hτd⟩ := s82rc_anti_local hJ.2 p
  set c0 : ℂ := chartAt ℂ p p with hc0
  set τ : ℂ → ℂ := fun z => conj (localMapExpr J p z) with hτ
  have hτ0 : τ c0 = conj (chartAt ℂ (J p) (J p)) := by simp only [hτ, hc0, s82tt_L_center]
  have hζc := s82rc_analyticAt_conj_conj hζan
  set ζc : ℂ → ℂ := fun u => conj (ζ (conj u)) with hζc_def
  have hcomp : (fun z => conj (ζ (localMapExpr J p z))) = ζc ∘ τ := by
    funext z; simp [hζc_def, hτ]
  have hζcan : AnalyticAt ℂ ζc (τ c0) := by rw [hτ0]; exact hζc
  have han : AnalyticAt ℂ (fun z => conj (ζ (localMapExpr J p z))) c0 := by
    rw [hcomp]; exact hζcan.comp hτan
  have hdζc : deriv ζc (τ c0) = conj (deriv ζ (chartAt ℂ (J p) (J p))) := by
    rw [hτ0]
    have := congrFun (deriv_conj_conj (f := ζ)) (conj (chartAt ℂ (J p) (J p)))
    simpa [Function.comp_def, hζc_def] using this
  refine ⟨han, ?_, ?_, ?_⟩
  · simp only [s82tt_L_center, hζ0, map_zero]
  · rw [hcomp, deriv_comp c0 hζcan.differentiableAt hτan.differentiableAt, hdζc]
    exact mul_ne_zero ((map_ne_zero _).2 hζd) hτd
  · -- the square of the derivative equals the transported differential near the centre
    have hLc := s82tt_L_continuousAt hJ p
    have hLc' : Tendsto (localMapExpr J p) (𝓝 c0) (𝓝 (chartAt ℂ (J p) (J p))) := by
      have := hLc.tendsto; rwa [s82tt_L_center] at this
    have h1 := hLc'.eventually hζq
    have h2 : ∀ᶠ z in 𝓝 c0, AnalyticAt ℂ τ z := hτan.eventually_analyticAt
    have hτc : ContinuousAt τ c0 := hτan.continuousAt
    have h3 : ∀ᶠ z in 𝓝 c0, AnalyticAt ℂ ζc (τ z) := by
      have := hζcan.eventually_analyticAt
      exact hτc.eventually this
    filter_upwards [s82tt_transport_local hJ hq p, h1, h2, h3] with z hz1 hz2 hz3 hz4
    rw [hz1, hcomp, deriv_comp z hz4.differentiableAt hz3.differentiableAt]
    have hdz : deriv ζc (τ z) = conj (deriv ζ (localMapExpr J p z)) := by
      have := congrFun (deriv_conj_conj (f := ζ)) (τ z)
      simp only [Function.comp_apply] at this
      have e : ζc = conj ∘ ζ ∘ conj := rfl
      rw [e, this]
      simp [hτ]
    rw [hdz, ← hz2]
    simp [hτ, mul_pow, map_pow]

end

theorem s82tt_meromorphic_conj_conj {g : ℂ → ℂ} {c : ℂ} (hg : MeromorphicAt g c) :
    MeromorphicAt (fun w => conj (g (conj w))) (conj c) := by
  obtain ⟨n, hn⟩ := hg
  refine ⟨n, ?_⟩
  have h := s82rc_analyticAt_conj_conj hn
  refine h.congr (Eventually.of_forall fun w => ?_)
  simp [map_pow]

theorem s82tt_order_conj_conj_of_eq {g : ℂ → ℂ} {c : ℂ} (hg : MeromorphicAt g c) {m : WithTop ℤ}
    (hm : meromorphicOrderAt g c = m) :
    meromorphicOrderAt (fun w => conj (g (conj w))) (conj c) = m := by
  have hgc := s82tt_meromorphic_conj_conj hg
  have hcont : Tendsto (fun w : ℂ => conj w) (𝓝[≠] (conj c)) (𝓝[≠] c) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (Complex.continuous_conj.tendsto (conj c)).mono_left (nhdsWithin_le_nhds (s := {conj c}ᶜ))
      rwa [conj_conj] at this
    · filter_upwards [self_mem_nhdsWithin] with w hw h
      have h' : conj w = c := h
      exact hw (by rw [← h', conj_conj] : w = conj c)
  induction m using WithTop.recTopCoe with
  | top =>
    rw [meromorphicOrderAt_eq_top_iff] at hm ⊢
    filter_upwards [hcont.eventually hm] with w hw
    simp [hw]
  | coe n =>
    obtain ⟨h, hh, hh0, hev⟩ := (meromorphicOrderAt_eq_int_iff hg).1 hm
    refine (meromorphicOrderAt_eq_int_iff hgc).2 ⟨fun w => conj (h (conj w)), ?_, ?_, ?_⟩
    · exact s82rc_analyticAt_conj_conj hh
    · simpa using hh0
    · filter_upwards [hcont.eventually hev] with w hw
      simp only [hw, smul_eq_mul, map_mul, map_zpow₀, map_sub, conj_conj]

theorem s82tt_order_conj_conj {g : ℂ → ℂ} {c : ℂ} :
    meromorphicOrderAt (fun w => conj (g (conj w))) (conj c) = meromorphicOrderAt g c := by
  by_cases hg : MeromorphicAt g c
  · exact s82tt_order_conj_conj_of_eq hg rfl
  · rw [meromorphicOrderAt_of_not_meromorphicAt hg, meromorphicOrderAt_of_not_meromorphicAt]
    intro h
    apply hg
    have := s82tt_meromorphic_conj_conj h
    simpa using this

section
variable {B : Type u} [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B]

/-- Zeros of order `n` are transported. -/
theorem s82tt_zero_iff {J : B ≃ₜ B} (hJ : IsAnticonformalInvolution J) {q : B → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (p : B) (n : ℕ) :
    IsZeroOfOrder (s31qr_transportOn univ J Complex.conjCLE.toLinearMap q) p n ↔ IsZeroOfOrder q (J p) n := by
  obtain ⟨hτan, hτd⟩ := s82rc_anti_local hJ.2 p
  set τ : ℂ → ℂ := fun z => conj (localMapExpr J p z) with hτ
  have hτ0 : τ (chartAt ℂ p p) = conj (chartAt ℂ (J p) (J p)) := by
    simp only [hτ, s82tt_L_center]
  have hev : (fun z => s31qr_transportOn univ J Complex.conjCLE.toLinearMap q p z) =ᶠ[𝓝 (chartAt ℂ p p)]
      fun z => (fun w => conj (q (J p) (conj w))) (τ z) * deriv τ z ^ 2 := by
    filter_upwards [s82tt_transport_local hJ hq p] with z hz
    rw [hz]
    simp [hτ]
  unfold IsZeroOfOrder
  have h1 : meromorphicOrderAt (s31qr_transportOn univ J Complex.conjCLE.toLinearMap q p) (chartAt ℂ p p) =
      meromorphicOrderAt (fun w => conj (q (J p) (conj w))) (conj (chartAt ℂ (J p) (J p))) := by
    rw [meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds)]
    exact (s31qr_quadratic_pullback_order (f := fun w => conj (q (J p) (conj w))) hτan hτd).trans
      (by rw [hτ0])
  rw [h1, s82tt_order_conj_conj]

end

section
variable {B : Type u} [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B]

/-- The conjugate transport of a holomorphic quadratic differential is a holomorphic quadratic differential. -/
theorem s82tt_hol {J : B ≃ₜ B} (hJ : IsAnticonformalInvolution J) {q : B → ℂ → ℂ}
    (hq : IsHolQuadDiff q) :
    IsHolQuadDiff (s31qr_transportOn univ J Complex.conjCLE.toLinearMap q) := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : B, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  refine ⟨s31qr_transport_family univ J _ (fun x z hz _ => s31qr_involution_coordinate J hJ x hz) q,
    fun x => ?_⟩
  have h := s31q2_conj_transport_holomorphic (A := B) J hJ (U := univ) isOpen_univ (V := univ) isOpen_univ
    (H := id) (fun p _ => mdifferentiableAt_id) (fun p _ => mem_univ _) (q := q) hq'.1
    (fun a => by simpa using hq'.2 a) x
  simpa using h

/-- A non-zero holomorphic quadratic differential has a regular point. -/
theorem s82tt_exists_regular {q : B → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) :
    ∃ p, IsRegularPoint q p := by
  by_contra hcon0
  have hcon : ∀ p, ¬ IsRegularPoint q p := fun p hp => hcon0 ⟨p, hp⟩
  apply hne
  funext x z
  by_cases hz : z ∈ (chartAt ℂ x).target
  · by_contra h0
    exact hcon _ ((s26u_isRegularPoint_iff hq x hz).2 (by simpa using h0))
  · exact hq.1.1 x z hz

theorem s82tt_ne {J : B ≃ₜ B} (hJ : IsAnticonformalInvolution J) {q : B → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (hne : q ≠ 0) :
    s31qr_transportOn univ J Complex.conjCLE.toLinearMap q ≠ 0 := by
  obtain ⟨p, hp⟩ := s82tt_exists_regular hq hne
  have hp' : IsRegularPoint (s31qr_transportOn univ J Complex.conjCLE.toLinearMap q) (J p) :=
    (s82tt_regular_iff hJ hq (J p)).2 (by rw [hJ.1 p]; exact hp)
  intro h0
  apply hp'
  rw [h0]; rfl

theorem s82tt_teichStretch_conj (k : ℝ) (x : ℂ) : teichStretch k (conj x) = conj (teichStretch k x) := by
  simp [teichStretch, map_div₀, map_add, map_mul, Complex.conj_ofReal]

end

section
variable {A : Type u} [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A]
variable {B : Type u} [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B]

/-- **A Teichmüller map commuting with anticonformal involutions is a Teichmüller map for the conjugate-transported
differentials**: if `f ∘ J₀ = J₁ ∘ f` and `f` is a Teichmüller map for `(q, q', k)`, then `f` is a Teichmüller map for
`(q̃, q̃', k)`, where `q̃ = s31qr_transportOn univ J₀ conj q` (its value on the chart target is
`conj (q (J₀ a) …) · (conj ∘ J₀)'²`, `s31qd5_conj_transport_apply`). -/
theorem s32w_t324_conj_teich {J₀ : A ≃ₜ A} {J₁ : B ≃ₜ B} (hJ₀ : IsAnticonformalInvolution J₀)
    (hJ₁ : IsAnticonformalInvolution J₁) {f : A ≃ₜ B} {q : A → ℂ → ℂ} {q' : B → ℂ → ℂ} {k : ℝ}
    (hf : IsTeichmullerMap f q q' k) (hcomm : ∀ y, f (J₀ y) = J₁ (f y)) :
    IsTeichmullerMap f (s31qr_transportOn univ J₀ Complex.conjCLE.toLinearMap q)
      (s31qr_transportOn univ J₁ Complex.conjCLE.toLinearMap q') k := by
  refine ⟨hf.qc, s82tt_hol hJ₀ hf.initial, s82tt_ne hJ₀ hf.initial hf.initial_ne,
    s82tt_hol hJ₁ hf.terminal, hf.k_nonneg, hf.k_lt_one, ?_, ?_⟩
  · intro p hp
    have hp1 : IsRegularPoint q (J₀ p) := (s82tt_regular_iff hJ₀ hf.initial p).1 hp
    obtain ⟨hreg', ζ₁, ζ₁', hn1, hn1', hrel⟩ := hf.regular (J₀ p) hp1
    have e : J₁ (f p) = f (J₀ p) := (hcomm p).symm
    have hreg'' : IsRegularPoint q' (J₁ (f p)) := by rw [e]; exact hreg'
    refine ⟨(s82tt_regular_iff hJ₁ hf.terminal (f p)).2 hreg'', fun z => conj (ζ₁ (localMapExpr J₀ p z)),
      fun z => conj (ζ₁' (localMapExpr J₁ (f p) z)), s82tt_natural hJ₀ hf.initial p hn1,
      s82tt_natural hJ₁ hf.terminal (f p) (by rw [e]; exact hn1'), ?_⟩
    have hps : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
    have hc0t : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source hps
    have hsymm : ContinuousAt (chartAt ℂ p).symm (chartAt ℂ p p) := (chartAt ℂ p).continuousAt_symm hc0t
    have hLc' : Tendsto (localMapExpr J₀ p) (𝓝 (chartAt ℂ p p)) (𝓝 (chartAt ℂ (J₀ p) (J₀ p))) := by
      have := (s82tt_L_continuousAt hJ₀ p).tendsto
      rwa [s82tt_L_center] at this
    have h1 := hLc'.eventually hrel
    have s2 : ∀ᶠ z in 𝓝 (chartAt ℂ p p), J₀ ((chartAt ℂ p).symm z) ∈ (chartAt ℂ (J₀ p)).source := by
      refine (J₀.continuous.continuousAt.comp hsymm).eventually_mem ?_
      show (chartAt ℂ (J₀ p)).source ∈ 𝓝 (J₀ ((chartAt ℂ p).symm (chartAt ℂ p p)))
      rw [(chartAt ℂ p).left_inv hps]
      exact (chartAt ℂ (J₀ p)).open_source.mem_nhds (mem_chart_source ℂ (J₀ p))
    have s3 : ∀ᶠ z in 𝓝 (chartAt ℂ p p), f ((chartAt ℂ p).symm z) ∈ (chartAt ℂ (f p)).source := by
      refine (f.continuous.continuousAt.comp hsymm).eventually_mem ?_
      show (chartAt ℂ (f p)).source ∈ 𝓝 (f ((chartAt ℂ p).symm (chartAt ℂ p p)))
      rw [(chartAt ℂ p).left_inv hps]
      exact (chartAt ℂ (f p)).open_source.mem_nhds (mem_chart_source ℂ (f p))
    filter_upwards [h1, s2, s3] with z hz1 hz2 hz3
    have key : localMapExpr J₁ (f p) (localMapExpr f p z) =
        localMapExpr f (J₀ p) (localMapExpr J₀ p z) := by
      simp only [localMapExpr]
      rw [(chartAt ℂ (f p)).left_inv hz3, (chartAt ℂ (J₀ p)).left_inv hz2, hcomm ((chartAt ℂ p).symm z), e]
    show conj (ζ₁' (localMapExpr J₁ (f p) (localMapExpr f p z))) =
      teichStretch k (conj (ζ₁ (localMapExpr J₀ p z)))
    rw [key, hz1, s82tt_teichStretch_conj]
  · intro p n hp
    have h1 := hf.zero (J₀ p) n ((s82tt_zero_iff hJ₀ hf.initial p n).1 hp)
    have e : J₁ (f p) = f (J₀ p) := (hcomm p).symm
    exact (s82tt_zero_iff hJ₁ hf.terminal (f p) n).2 (by rw [e]; exact h1)

end

end LiZhongQC
