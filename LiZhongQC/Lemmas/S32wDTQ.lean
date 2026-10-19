import LiZhongQC.Lemmas.QDDecompRestrictionIdentity
import LiZhongQC.Lemmas.QDSymmetricExtension
import LiZhongQC.Lemmas.QDDecompConjTransport
import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
import LiZhongQC.Lemmas.S32wSymmExtPunctured

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u v w

section Chain

variable {B : Type u} {A : Type v} {A' : Type w} [TopologicalSpace B] [ChartedSpace ℂ B]
  [TopologicalSpace A] [ChartedSpace ℂ A] [TopologicalSpace A'] [ChartedSpace ℂ A']
  [IsManifold 𝓘(ℂ) ω B] [IsManifold 𝓘(ℂ) ω A] [IsManifold 𝓘(ℂ) ω A']

/-- The coordinate expression of a holomorphic map at a chart centre is differentiable. -/
theorem s32w_dt_coord_center {H : B → A} {p : B} (hH : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H p) :
    DifferentiableAt ℂ (fun w => chartAt ℂ (H p) (H ((chartAt ℂ p).symm w))) (chartAt ℂ p p) := by
  have hz : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have hl : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have h := s31qr_coordinate_differentiable (H := H) p (H p) hz (by rw [hl]; exact mem_chart_source ℂ _)
    (by rw [hl]; exact hH)
  exact h

/-- Chain rule at chart centres for a composite of two holomorphic maps. -/
theorem s32w_dt_chain {H : B → A} {K : A → A'} {p : B} (hH : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H p)
    (hK : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) K (H p)) :
    deriv (fun w => chartAt ℂ (K (H p)) (K (H ((chartAt ℂ p).symm w)))) (chartAt ℂ p p) =
      deriv (fun v => chartAt ℂ (K (H p)) (K ((chartAt ℂ (H p)).symm v))) (chartAt ℂ (H p) (H p)) *
        deriv (fun w => chartAt ℂ (H p) (H ((chartAt ℂ p).symm w))) (chartAt ℂ p p) := by
  have hd1 := s32w_dt_coord_center hH
  have hd2 := s32w_dt_coord_center hK
  have hl : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hcont : ContinuousAt (fun w => H ((chartAt ℂ p).symm w)) (chartAt ℂ p p) := by
    have hz : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    have h1 : ContinuousAt (chartAt ℂ p).symm (chartAt ℂ p p) := (chartAt ℂ p).continuousAt_symm hz
    have h2 : ContinuousAt H ((chartAt ℂ p).symm (chartAt ℂ p p)) := by rw [hl]; exact hH.continuousAt
    exact h2.comp h1
  have hnb : (chartAt ℂ (H p)).source ∈ 𝓝 (H ((chartAt ℂ p).symm (chartAt ℂ p p))) := by
    rw [hl]
    exact (chartAt ℂ (H p)).open_source.mem_nhds (mem_chart_source ℂ (H p))
  have he : (fun w => chartAt ℂ (K (H p)) (K (H ((chartAt ℂ p).symm w)))) =ᶠ[𝓝 (chartAt ℂ p p)]
      fun w => (fun v => chartAt ℂ (K (H p)) (K ((chartAt ℂ (H p)).symm v)))
        (chartAt ℂ (H p) (H ((chartAt ℂ p).symm w))) := by
    filter_upwards [hcont.preimage_mem_nhds hnb] with w hw
    rw [(chartAt ℂ (H p)).left_inv hw]
  have hy : chartAt ℂ (H p) (H p) =
      (fun w => chartAt ℂ (H p) (H ((chartAt ℂ p).symm w))) (chartAt ℂ p p) := by
    show _ = chartAt ℂ (H p) (H ((chartAt ℂ p).symm (chartAt ℂ p p)))
    rw [hl]
  have := s31qd5_hasDerivAt_comp_eq (f := fun v => chartAt ℂ (K (H p)) (K ((chartAt ℂ (H p)).symm v)))
    (g := fun w => chartAt ℂ (H p) (H ((chartAt ℂ p).symm w))) (z := chartAt ℂ p p)
    (y := chartAt ℂ (H p) (H p)) hd1 hd2 hy he
  exact this.deriv

end Chain

section Center

variable {B : Type u} {A : Type v} {A' : Type w} [TopologicalSpace B] [ChartedSpace ℂ B]
  [TopologicalSpace A] [ChartedSpace ℂ A] [TopologicalSpace A'] [ChartedSpace ℂ A']

/-- Value at the chart centre of an identity transport. -/
theorem s32w_dt_cv_id (U : Set B) (H : B → A) (r : A → ℂ → ℂ) {p : B} (hp : p ∈ U) :
    s31qr_transportOn U H (LinearMap.id : ℂ →ₗ[ℝ] ℂ) r p (chartAt ℂ p p) =
      r (H p) (chartAt ℂ (H p) (H p)) *
        deriv (fun w => chartAt ℂ (H p) (H ((chartAt ℂ p).symm w))) (chartAt ℂ p p) ^ 2 := by
  have h0 := s31qd5_id_transport_apply U H r p ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
    (by rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]; exact hp)
  rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)] at h0
  exact h0

/-- Value at the chart centre of a conjugate transport. -/
theorem s32w_dt_cv_conj (U : Set B) (H : B → A) (r : A → ℂ → ℂ) {p : B} (hp : p ∈ U) :
    s31qr_transportOn U H Complex.conjCLE.toLinearMap r p (chartAt ℂ p p) =
      conj (r (H p) (chartAt ℂ (H p) (H p))) *
        deriv (fun w => conj (chartAt ℂ (H p) (H ((chartAt ℂ p).symm w)))) (chartAt ℂ p p) ^ 2 := by
  have h0 := s31qd5_conj_transport_apply U H r p ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
    (by rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]; exact hp)
  rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)] at h0
  exact h0

variable [IsManifold 𝓘(ℂ) ω B] [IsManifold 𝓘(ℂ) ω A] [IsManifold 𝓘(ℂ) ω A']

/-- Composition of identity transports at chart centres. -/
theorem s32w_dt_cv_comp (U : Set B) (V : Set A) (H : B → A) (K : A → A') (L : B → A')
    (hL : ∀ s, L s = K (H s)) (r : A' → ℂ → ℂ) {p : B} (hp : p ∈ U) (hHp : H p ∈ V)
    (hH : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H p) (hK : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) K (H p)) :
    s31qr_transportOn U H (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
        (s31qr_transportOn V K (LinearMap.id : ℂ →ₗ[ℝ] ℂ) r) p (chartAt ℂ p p) =
      s31qr_transportOn U L (LinearMap.id : ℂ →ₗ[ℝ] ℂ) r p (chartAt ℂ p p) := by
  have hLf : L = fun s => K (H s) := funext hL
  subst hLf
  rw [s32w_dt_cv_id U H _ hp, s32w_dt_cv_id V K r hHp, s32w_dt_cv_id U (fun s => K (H s)) r hp,
    s32w_dt_chain hH hK]
  ring

/-- Mixed composition: an identity transport along `H` after a conjugate transport along `K`. -/
theorem s32w_dt_cv_comp_conj_inner (H : B → A) (K : A → A') (L : B → A') (hL : ∀ s, L s = K (H s))
    (r : A' → ℂ → ℂ) {p : B} (hH : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H p)
    (hK : DifferentiableAt ℂ (fun v => conj (chartAt ℂ (K (H p)) (K ((chartAt ℂ (H p)).symm v))))
      (chartAt ℂ (H p) (H p))) :
    s31qr_transportOn univ H (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
        (s31qr_transportOn univ K Complex.conjCLE.toLinearMap r) p (chartAt ℂ p p) =
      s31qr_transportOn univ L Complex.conjCLE.toLinearMap r p (chartAt ℂ p p) := by
  have hLf : L = fun s => K (H s) := funext hL
  subst hLf
  rw [s32w_dt_cv_id univ H _ (mem_univ p), s32w_dt_cv_conj univ K r (mem_univ (H p)),
    s32w_dt_cv_conj univ (fun s => K (H s)) r (mem_univ p)]
  have hd1 := s32w_dt_coord_center hH
  have hl : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hcont : ContinuousAt (fun w => H ((chartAt ℂ p).symm w)) (chartAt ℂ p p) := by
    have hz : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    have h1 : ContinuousAt (chartAt ℂ p).symm (chartAt ℂ p p) := (chartAt ℂ p).continuousAt_symm hz
    have h2 : ContinuousAt H ((chartAt ℂ p).symm (chartAt ℂ p p)) := by rw [hl]; exact hH.continuousAt
    exact h2.comp h1
  have hnb : (chartAt ℂ (H p)).source ∈ 𝓝 (H ((chartAt ℂ p).symm (chartAt ℂ p p))) := by
    rw [hl]
    exact (chartAt ℂ (H p)).open_source.mem_nhds (mem_chart_source ℂ (H p))
  have he : (fun w => conj (chartAt ℂ (K (H p)) (K (H ((chartAt ℂ p).symm w))))) =ᶠ[𝓝 (chartAt ℂ p p)]
      fun w => (fun v => conj (chartAt ℂ (K (H p)) (K ((chartAt ℂ (H p)).symm v))))
        (chartAt ℂ (H p) (H ((chartAt ℂ p).symm w))) := by
    filter_upwards [hcont.preimage_mem_nhds hnb] with w hw
    rw [(chartAt ℂ (H p)).left_inv hw]
  have hy : chartAt ℂ (H p) (H p) =
      (fun w => chartAt ℂ (H p) (H ((chartAt ℂ p).symm w))) (chartAt ℂ p p) := by
    show _ = chartAt ℂ (H p) (H ((chartAt ℂ p).symm (chartAt ℂ p p)))
    rw [hl]
  have hder := (s31qd5_hasDerivAt_comp_eq
    (f := fun v => conj (chartAt ℂ (K (H p)) (K ((chartAt ℂ (H p)).symm v))))
    (g := fun w => chartAt ℂ (H p) (H ((chartAt ℂ p).symm w))) (z := chartAt ℂ p p)
    (y := chartAt ℂ (H p) (H p)) hd1 hK hy he).deriv
  rw [hder]
  ring

/-- Mixed composition: a conjugate transport along `H` after an identity transport along `K`. -/
theorem s32w_dt_cv_comp_conj_outer (H : B → A) (K : A → A') (L : B → A') (hL : ∀ s, L s = K (H s))
    (r : A' → ℂ → ℂ) {p : B}
    (hH : DifferentiableAt ℂ (fun w => conj (chartAt ℂ (H p) (H ((chartAt ℂ p).symm w)))) (chartAt ℂ p p))
    (hHc : ContinuousAt (fun w => H ((chartAt ℂ p).symm w)) (chartAt ℂ p p))
    (hK : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) K (H p)) :
    s31qr_transportOn univ H Complex.conjCLE.toLinearMap
        (s31qr_transportOn univ K (LinearMap.id : ℂ →ₗ[ℝ] ℂ) r) p (chartAt ℂ p p) =
      s31qr_transportOn univ L Complex.conjCLE.toLinearMap r p (chartAt ℂ p p) := by
  have hLf : L = fun s => K (H s) := funext hL
  subst hLf
  rw [s32w_dt_cv_conj univ H _ (mem_univ p), s32w_dt_cv_id univ K r (mem_univ (H p)),
    s32w_dt_cv_conj univ (fun s => K (H s)) r (mem_univ p)]
  have hd1 := s32w_dt_coord_center hK
  have hl : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hnb : (chartAt ℂ (H p)).source ∈ 𝓝 (H ((chartAt ℂ p).symm (chartAt ℂ p p))) := by
    rw [hl]
    exact (chartAt ℂ (H p)).open_source.mem_nhds (mem_chart_source ℂ (H p))
  have he : (fun w => conj (chartAt ℂ (K (H p)) (K (H ((chartAt ℂ p).symm w))))) =ᶠ[𝓝 (chartAt ℂ p p)]
      fun w => conj ((fun v => chartAt ℂ (K (H p)) (K ((chartAt ℂ (H p)).symm v)))
        (conj ((fun w => conj (chartAt ℂ (H p) (H ((chartAt ℂ p).symm w)))) w))) := by
    filter_upwards [hHc.preimage_mem_nhds hnb] with w hw
    simp only [Complex.conj_conj]
    rw [(chartAt ℂ (H p)).left_inv hw]
  have hy : conj (chartAt ℂ (H p) (H p)) =
      (fun w => conj (chartAt ℂ (H p) (H ((chartAt ℂ p).symm w)))) (chartAt ℂ p p) := by
    show _ = conj (chartAt ℂ (H p) (H ((chartAt ℂ p).symm (chartAt ℂ p p))))
    rw [hl]
  have hder := (s31qd5_hasDerivAt_conj_comp_eq
    (f := fun v => chartAt ℂ (K (H p)) (K ((chartAt ℂ (H p)).symm v)))
    (g := fun w => conj (chartAt ℂ (H p) (H ((chartAt ℂ p).symm w)))) (z := chartAt ℂ p p)
    (y := chartAt ℂ (H p) (H p)) hH hd1 hy he).deriv
  rw [hder]
  simp only [map_mul, map_pow]
  ring

end Center

section OpensLift

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- A map into an open subset whose composite with the inclusion is holomorphic is holomorphic. -/
theorem s32w_dt_mdiff_into_opens {Z : Type v} [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (U : TopologicalSpace.Opens X) (G : Z → U) (hGc : Continuous G) (ι : Z → X)
    (hι : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι) (hG : ∀ s, (G s : X) = ι s) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := by
  intro s
  obtain ⟨-, hV2, -⟩ := s32w_opens_chart_facts U (G s)
  have h := ((s23_mdifferentiableAt_iff (f := ι) (x := s) (p := s) (y := ι s)
    (mem_chart_source ℂ s) (mem_chart_source ℂ (ι s))).1 (hι s)).2
  refine (s23_mdifferentiableAt_iff (f := G) (x := s) (p := s) (y := G s)
    (mem_chart_source ℂ s) (mem_chart_source ℂ (G s))).2 ⟨hGc.continuousAt, ?_⟩
  have hfun : (fun z => chartAt ℂ (G s) (G ((chartAt ℂ s).symm z))) =
      fun z => chartAt ℂ (ι s) (ι ((chartAt ℂ s).symm z)) := by
    funext z
    rw [hV2, hG, hG]
  rw [hfun]
  exact h

/-- The restriction of an anticonformal involution to an invariant open subset. -/
theorem s32w_dt_opens_involution (U : TopologicalSpace.Opens X) (Jd : U ≃ₜ U) (J : X ≃ₜ X)
    (hJ : IsAnticonformalInvolution J) (hcoe : ∀ y, (Jd y : X) = J y) : IsAnticonformalInvolution Jd := by
  refine ⟨fun p => Subtype.ext (by rw [hcoe, hcoe, hJ.1]), fun y => ?_⟩
  obtain ⟨hU1, hU2, hU3⟩ := s32w_opens_chart_facts U y
  obtain ⟨hV1, hV2, hV3⟩ := s32w_opens_chart_facts U (Jd y)
  have hey : ((Jd y : U) : X) = J (y : X) := hcoe y
  have hdom : localMapDomain Jd y ⊆ localMapDomain J (y : X) := by
    intro z hz
    obtain ⟨hzt, hzs⟩ := hz
    obtain ⟨hz1, hz2⟩ := hU1 z hzt
    refine ⟨hz1, ?_⟩
    show J ((chartAt ℂ (y : X)).symm z) ∈ (chartAt ℂ (J (y : X))).source
    have h3 : ((Jd ((chartAt ℂ y).symm z) : U) : X) ∈ (chartAt ℂ ((Jd y : U) : X)).source := by
      have h4 : Jd ((chartAt ℂ y).symm z) ∈ (chartAt ℂ (Jd y)).source := hzs
      rw [hV3] at h4
      exact h4
    rw [hcoe ((chartAt ℂ y).symm z), hz2, hey] at h3
    exact h3
  have hEq : ∀ z ∈ localMapDomain Jd y, localMapExpr Jd y z = localMapExpr J (y : X) z := by
    intro z hz
    obtain ⟨hzt, -⟩ := hz
    obtain ⟨-, hz2⟩ := hU1 z hzt
    show chartAt ℂ (Jd y) (Jd ((chartAt ℂ y).symm z)) =
      chartAt ℂ (J (y : X)) (J ((chartAt ℂ (y : X)).symm z))
    rw [hV2, hcoe ((chartAt ℂ y).symm z), hz2, hey]
  have h := (hJ.2 (y : X)).mono hdom
  refine h.congr (fun z hz => ?_)
  rw [hEq z hz]

end OpensLift

/-- `pullbackQD` is the identity transport along `ι`. -/
theorem s32w_dt_pullback_eq {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (q : F.X.carrier → ℂ → ℂ) :
    pullbackQD F q = s31qr_transportOn univ F.ι (LinearMap.id : ℂ →ₗ[ℝ] ℂ) q := by
  classical
  funext x z
  by_cases hz : z ∈ (chartAt ℂ x).target
  · rw [s31qd5_id_transport_apply univ F.ι q x hz (mem_univ _)]
    simp only [pullbackQD, Set.indicator_of_mem hz]
  · simp only [pullbackQD, Set.indicator_of_notMem hz, s31qr_transportOn, hz, false_and, if_false]

/-- **(D1)** The symmetric extension `Q` of an admissible differential `q` on the punctured double. -/
theorem s32w_dt_Q {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀] [ConnectedSpace S₀]
    [IsManifold 𝓘(ℂ) ω S₀] {g n m : ℕ} (hm : m ≠ 0) (F₀ : FiniteTypeStructure S₀ g n m)
    {Xd₀ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {ιd₀ : S₀ → Xd₀.carrier}
    {Pd₀ : Finset Xd₀.carrier} (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀)
    (Fd₀ : FiniteTypeStructure (puncturedOpens Pd₀) (2 * g + m - 1) (2 * n) 0)
    (Jd₀ : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₀) (hJd₀ : ∀ y, (Jd₀ y : Xd₀.carrier) = J₀ y)
    (G₀ : C(S₀, ↥(puncturedOpens Pd₀))) (hG₀ : ∀ x, (G₀ x : Xd₀.carrier) = ιd₀ x)
    {q : S₀ → ℂ → ℂ} (hq : q ∈ admissibleQDInterior F₀) :
    ∃ Q ∈ admissibleQDInterior Fd₀,
      (∀ x, q x = (chartAt ℂ x).target.indicator fun z =>
        Q (G₀ ((chartAt ℂ x).symm z)) (chartAt ℂ (G₀ ((chartAt ℂ x).symm z)) (G₀ ((chartAt ℂ x).symm z))) *
          deriv (fun w => chartAt ℂ (G₀ ((chartAt ℂ x).symm z)) (G₀ ((chartAt ℂ x).symm w))) z ^ 2) ∧
      (∀ y z, z ∈ (chartAt ℂ y).target →
        Q y z = conj (Q (Jd₀ ((chartAt ℂ y).symm z))
            (chartAt ℂ (Jd₀ ((chartAt ℂ y).symm z)) (Jd₀ ((chartAt ℂ y).symm z)))) *
          deriv (fun w => conj (chartAt ℂ (Jd₀ ((chartAt ℂ y).symm z)) (Jd₀ ((chartAt ℂ y).symm w)))) z ^ 2) ∧
      (q ≠ 0 → Q ≠ 0) := by
  classical
  obtain ⟨q₀, hq₀, rfl⟩ := Submodule.mem_map.1 hq
  obtain ⟨T, hT⟩ := s31qi_seam_fill F₀ hm hd₀
  obtain ⟨E, hE, hEι, hEP⟩ := s31qr_fd_compactification Xd₀ Pd₀ Fd₀
  obtain ⟨h1, h2, h3, h4, h5⟩ := hT ⟨q₀, hq₀⟩
  set Tq : Xd₀.carrier → ℂ → ℂ := T ⟨q₀, hq₀⟩ with hTq
  set Qd : Fd₀.X.carrier → ℂ → ℂ :=
    s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Tq with hQd
  have hQdadm : IsAdmissibleQD Fd₀ Qd := s31qr_fd_transport_admissible Xd₀ Pd₀ Fd₀ E hE hEP h1 h2
    (fun a p hp hs => ⟨h5 a p hp hs, s31qi_puncture_poles F₀ hm hd₀ ⟨q₀, hq₀⟩ Tq h3 h4 a p hp hs⟩)
  have hfix := s31qd_ext_fixed F₀ hm hd₀ Fd₀ E hE hEP ⟨q₀, hq₀⟩ h1 h2 h3 h4 h5
  set Q : puncturedOpens Pd₀ → ℂ → ℂ := pullbackQD Fd₀ Qd with hQ
  have hQmem : Q ∈ admissibleQDInterior Fd₀ := Submodule.mem_map.2 ⟨Qd, hQdadm, rfl⟩
  have hQhol : IsHolQuadDiff Q := s32p_pullbackQD_isHolQuadDiff Fd₀ hQdadm
  have hQfam : IsDiffFamily 2 0 Q :=
    (hQhol : IsDiffFamily 2 0 Q ∧ ∀ x, DifferentiableOn ℂ (Q x) (chartAt ℂ x).target).1
  have hQeq : Q = s31qr_transportOn univ Fd₀.ι (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Qd :=
    s32w_dt_pullback_eq Fd₀ Qd
  have hG₀m : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₀ :=
    s32w_dt_mdiff_into_opens (puncturedOpens Pd₀) G₀ G₀.continuous ιd₀ hd₀.holomorphic hG₀
  have hι₀m : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Fd₀.ι := Fd₀.holomorphic
  have hEm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E : Xd₀.carrier → Fd₀.X.carrier) := hE.1
  have hEsm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E.symm : Fd₀.X.carrier → Xd₀.carrier) := hE.homeomorph_symm.1
  have hpb : IsHolQuadDiff (pullbackQD F₀ q₀) := s32p_pullbackQD_isHolQuadDiff F₀ hq₀
  have hpbfam : IsDiffFamily 2 0 (pullbackQD F₀ q₀) :=
    (hpb : IsDiffFamily 2 0 (pullbackQD F₀ q₀) ∧
      ∀ x, DifferentiableOn ℂ (pullbackQD F₀ q₀ x) (chartAt ℂ x).target).1
  -- (D2a) as an equality of quadratic-differential families, compared at the chart centres
  have hD2a : pullbackQD F₀ q₀ = s31qr_transportOn univ G₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q := by
    apply s31qd5_eq_of_centers hpbfam
    · exact s31qr_transport_family univ G₀ _
        (fun x z hz _ => s31qr_coordinate_differentiable x _ hz (mem_chart_source ℂ _) (hG₀m _)) Q
    · intro p
      have hmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun s => E (ιd₀ s)) p :=
        (hEm _).comp p (hd₀.holomorphic p)
      have hmd' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) E.symm ((fun s => E (ιd₀ s)) p) := hEsm _
      have e1 : s31qr_transportOn univ G₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q p (chartAt ℂ p p) =
          s31qr_transportOn univ (fun s => E (ιd₀ s)) (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Qd p (chartAt ℂ p p) := by
        rw [hQeq]
        exact s32w_dt_cv_comp univ univ G₀ Fd₀.ι (fun s => E (ιd₀ s))
          (fun s => by rw [← hEι, hG₀]) Qd (mem_univ _) (mem_univ _) (hG₀m p) (hι₀m _)
      have e2 : s31qr_transportOn univ (fun s => E (ιd₀ s)) (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Qd p
            (chartAt ℂ p p) =
          s31qr_transportOn univ ιd₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Tq p (chartAt ℂ p p) := by
        rw [hQd]
        exact s32w_dt_cv_comp univ univ (fun s => E (ιd₀ s)) E.symm ιd₀
          (fun s => (E.symm_apply_apply _).symm) Tq (mem_univ _) (mem_univ _) hmd hmd'
      have e3 : s31qr_transportOn univ ιd₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Tq p (chartAt ℂ p p) =
          s31qr_transportOn univ ιd₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
            (s31qr_positiveData F₀ hd₀ q₀) p (chartAt ℂ p p) := by
        rw [s32w_dt_cv_id univ ιd₀ Tq (mem_univ _), s32w_dt_cv_id univ ιd₀ _ (mem_univ _)]
        have hz : chartAt ℂ (ιd₀ p) (ιd₀ p) ∈ (chartAt ℂ (ιd₀ p)).target :=
          (chartAt ℂ (ιd₀ p)).map_source (mem_chart_source ℂ _)
        have h3c : Tq (ιd₀ p) (chartAt ℂ (ιd₀ p) (ιd₀ p)) =
            s31qr_positiveData F₀ hd₀ q₀ (ιd₀ p) (chartAt ℂ (ιd₀ p) (ιd₀ p)) :=
          h3 (ιd₀ p) _ hz
            (by rw [(chartAt ℂ (ιd₀ p)).left_inv (mem_chart_source ℂ _)]; exact ⟨p, rfl⟩)
        rw [h3c]
      have e4 : s31qr_transportOn univ ιd₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
            (s31qr_positiveData F₀ hd₀ q₀) p (chartAt ℂ p p) =
          s31qr_transportOn univ F₀.ι (LinearMap.id : ℂ →ₗ[ℝ] ℂ) q₀ p (chartAt ℂ p p) := by
        unfold s31qr_positiveData
        exact s32w_dt_cv_comp univ (range ιd₀) ιd₀ (s31qr_halfReturn F₀ hd₀) F₀.ι
          (fun s => (s31qr_halfReturn_image F₀ hd₀ s).symm) q₀ (mem_univ _) ⟨p, rfl⟩
          (hd₀.holomorphic p) (s31qr_halfReturn_holomorphic F₀ hd₀ ⟨p, rfl⟩)
      rw [s32w_dt_pullback_eq F₀ q₀, e1, e2, e3, e4]
  have hqeq : ∀ x, pullbackQD F₀ q₀ x = (chartAt ℂ x).target.indicator fun z =>
        Q (G₀ ((chartAt ℂ x).symm z)) (chartAt ℂ (G₀ ((chartAt ℂ x).symm z)) (G₀ ((chartAt ℂ x).symm z))) *
          deriv (fun w => chartAt ℂ (G₀ ((chartAt ℂ x).symm z)) (G₀ ((chartAt ℂ x).symm w))) z ^ 2 := by
    intro x
    funext z
    have h := congrFun (congrFun hD2a x) z
    by_cases hz : z ∈ (chartAt ℂ x).target
    · rw [h, s31qd5_id_transport_apply univ G₀ Q x hz (mem_univ _), Set.indicator_of_mem hz]
    · rw [h, Set.indicator_of_notMem hz]
      simp only [s31qr_transportOn, hz, false_and, if_false]
  refine ⟨Q, hQmem, hqeq, ?_, ?_⟩
  · -- (D2b): `Q` is fixed by the conjugate transport along `Jd₀`
    have hJa : IsAnticonformalInvolution Jd₀ :=
      s32w_dt_opens_involution (puncturedOpens Pd₀) Jd₀ J₀ hd₀.involution hJd₀
    obtain ⟨W, hWapp, hWa⟩ := s31dc_involution E hE hd₀.involution
    have hWι : ∀ s : puncturedOpens Pd₀, W (Fd₀.ι s) = Fd₀.ι (Jd₀ s) := fun s => by
      rw [hWapp, ← hEι s, E.symm_apply_apply, ← hEι (Jd₀ s), hJd₀]
    have hfixW : s31qr_transportOn univ (⇑W) Complex.conjCLE.toLinearMap Qd = Qd := by
      have hf : (fun y : Fd₀.X.carrier => E (J₀ (E.symm y))) = ⇑W := (funext hWapp).symm
      have := hfix
      rwa [hf] at this
    have hKfam : IsDiffFamily 2 0 (s31qr_transportOn univ Jd₀ Complex.conjCLE.toLinearMap Q) :=
      s31qr_transport_family univ Jd₀ _ (fun x z hz _ => s31qr_involution_coordinate Jd₀ hJa x hz) Q
    have hKQ : s31qr_transportOn univ Jd₀ Complex.conjCLE.toLinearMap Q = Q := by
      apply s31qd5_eq_of_centers hKfam hQfam
      intro p
      have hLeq : (fun s => W (Fd₀.ι s)) = fun s => Fd₀.ι (Jd₀ s) := funext hWι
      -- the `K`-side
      have k1 : s31qr_transportOn univ Jd₀ Complex.conjCLE.toLinearMap Q p (chartAt ℂ p p) =
          s31qr_transportOn univ (fun s => Fd₀.ι (Jd₀ s)) Complex.conjCLE.toLinearMap Qd p
            (chartAt ℂ p p) := by
        rw [hQeq]
        refine s32w_dt_cv_comp_conj_outer Jd₀ Fd₀.ι (fun s => Fd₀.ι (Jd₀ s)) (fun s => rfl) Qd
          (s31qd5_involution_coordinate_center Jd₀ hJa p) ?_ (hι₀m _)
        have hz : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
        exact Jd₀.continuous.continuousAt.comp ((chartAt ℂ p).continuousAt_symm hz)
      -- the `Q`-side
      have q1 : Q p (chartAt ℂ p p) =
          s31qr_transportOn univ (fun s => W (Fd₀.ι s)) Complex.conjCLE.toLinearMap Qd p
            (chartAt ℂ p p) := by
        have hQ2 : Q = s31qr_transportOn univ Fd₀.ι (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
            (s31qr_transportOn univ (⇑W) Complex.conjCLE.toLinearMap Qd) := by
          rw [hfixW]; exact hQeq
        rw [hQ2]
        exact s32w_dt_cv_comp_conj_inner Fd₀.ι (⇑W) (fun s => W (Fd₀.ι s)) (fun s => rfl) Qd
          (hι₀m p) (s31qd5_involution_coordinate_center W hWa (Fd₀.ι p))
      rw [k1, q1, hLeq]
    intro y z hz
    have h := congrFun (congrFun hKQ y) z
    rw [s31qd5_conj_transport_apply univ Jd₀ Q y hz (mem_univ _)] at h
    exact h.symm
  · intro hq0 hQ0
    apply hq0
    have h0 : s31qr_transportOn univ G₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
        (0 : puncturedOpens Pd₀ → ℂ → ℂ) = 0 := by
      funext x z
      simp only [s31qr_transportOn]
      split_ifs <;> simp
    have hD := hD2a
    rw [hQ0, h0] at hD
    exact hD

end LiZhongQC
