import LiZhongQC.Lemmas.QDReflectionAfterHalves
import LiZhongQC.Lemmas.QDReflectionPuncturePoles
import LiZhongQC.Lemmas.QDTransportZero
import LiZhongQC.Lemmas.QDSeamFill

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- Unfolding of an identity transport at a guarded point. -/
theorem s31qd5_id_transport_apply {A B : Type*} [TopologicalSpace A] [ChartedSpace ℂ A]
    [TopologicalSpace B] [ChartedSpace ℂ B] (U : Set B) (H : B → A) (q : A → ℂ → ℂ) (x : B) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) (hU : (chartAt ℂ x).symm z ∈ U) :
    s31qr_transportOn U H (LinearMap.id : ℂ →ₗ[ℝ] ℂ) q x z =
      q (H ((chartAt ℂ x).symm z)) (chartAt ℂ (H ((chartAt ℂ x).symm z)) (H ((chartAt ℂ x).symm z))) *
        deriv (fun w => chartAt ℂ (H ((chartAt ℂ x).symm z)) (H ((chartAt ℂ x).symm w))) z ^ 2 := by
  classical
  change (if z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ U then
    q (H ((chartAt ℂ x).symm z)) (chartAt ℂ (H ((chartAt ℂ x).symm z)) (H ((chartAt ℂ x).symm z))) *
      deriv (fun w => chartAt ℂ (H ((chartAt ℂ x).symm z)) (H ((chartAt ℂ x).symm w))) z ^ 2
    else 0) = _
  rw [if_pos ⟨hz, hU⟩]

/-- Unfolding of a conjugate transport at a guarded point. -/
theorem s31qd5_conj_transport_apply {A B : Type*} [TopologicalSpace A] [ChartedSpace ℂ A]
    [TopologicalSpace B] [ChartedSpace ℂ B] (U : Set B) (H : B → A) (q : A → ℂ → ℂ) (x : B) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) (hU : (chartAt ℂ x).symm z ∈ U) :
    s31qr_transportOn U H Complex.conjCLE.toLinearMap q x z =
      conj (q (H ((chartAt ℂ x).symm z))
        (chartAt ℂ (H ((chartAt ℂ x).symm z)) (H ((chartAt ℂ x).symm z)))) *
        deriv (fun w => conj (chartAt ℂ (H ((chartAt ℂ x).symm z)) (H ((chartAt ℂ x).symm w)))) z ^ 2 := by
  classical
  change (if z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ U then
    conj (q (H ((chartAt ℂ x).symm z))
      (chartAt ℂ (H ((chartAt ℂ x).symm z)) (H ((chartAt ℂ x).symm z)))) *
      deriv (fun w => conj (chartAt ℂ (H ((chartAt ℂ x).symm z)) (H ((chartAt ℂ x).symm w)))) z ^ 2
    else 0) = _
  rw [if_pos ⟨hz, hU⟩]

/-- The conjugate transport along an involution `J`, at the chart centre of a point `e`. -/
theorem s31qd5_involution_center {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (J : X ≃ₜ X)
    (Q : X → ℂ → ℂ) (e : X) :
    s31qr_transportOn univ J Complex.conjCLE.toLinearMap Q e (chartAt ℂ e e) =
      conj (Q (J e) (chartAt ℂ (J e) (J e))) *
        deriv (fun v => conj (chartAt ℂ (J e) (J ((chartAt ℂ e).symm v)))) (chartAt ℂ e e) ^ 2 := by
  have h0 := s31qd5_conj_transport_apply univ (J : X → X) Q e
    ((chartAt ℂ e).map_source (mem_chart_source ℂ e)) (mem_univ _)
  rw [(chartAt ℂ e).left_inv (mem_chart_source ℂ e)] at h0
  exact h0

/-- The conjugated coordinate expression of an anticonformal involution at a chart centre. -/
theorem s31qd5_involution_coordinate_center {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (J : X ≃ₜ X) (hJ : IsAnticonformalInvolution J) (e : X) :
    DifferentiableAt ℂ (fun v => conj (chartAt ℂ (J e) (J ((chartAt ℂ e).symm v)))) (chartAt ℂ e e) := by
  have h0 := s31qr_involution_coordinate J hJ e ((chartAt ℂ e).map_source (mem_chart_source ℂ e))
  rw [(chartAt ℂ e).left_inv (mem_chart_source ℂ e)] at h0
  exact h0

/-- Chain rule along an eventual factorization. -/
theorem s31qd5_hasDerivAt_comp_eq {f g Φ : ℂ → ℂ} {z y : ℂ} (hg : DifferentiableAt ℂ g z)
    (hf : DifferentiableAt ℂ f y) (hy : y = g z) (he : Φ =ᶠ[𝓝 z] fun w => f (g w)) :
    HasDerivAt Φ (deriv f y * deriv g z) z :=
  (HasDerivAt.comp_of_eq z hf.hasDerivAt hg.hasDerivAt hy).congr_of_eventuallyEq he

/-- Chain rule along an eventual factorization through `conj ∘ f ∘ conj`. -/
theorem s31qd5_hasDerivAt_conj_comp_eq {f g Φ : ℂ → ℂ} {z y : ℂ} (hg : DifferentiableAt ℂ g z)
    (hf : DifferentiableAt ℂ f y) (hy : conj y = g z)
    (he : Φ =ᶠ[𝓝 z] fun w => conj (f (conj (g w)))) :
    HasDerivAt Φ (conj (deriv f y) * deriv g z) z :=
  (HasDerivAt.comp_of_eq z hf.hasDerivAt.conj_conj hg.hasDerivAt hy).congr_of_eventuallyEq he

/-- A quadratic differential family is determined at a chart point by its value at the chart centre of the
corresponding point. -/
theorem s31qd5_eq_at_of_center {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
    {R₁ R₂ : B → ℂ → ℂ} (h₁ : IsDiffFamily 2 0 R₁) (h₂ : IsDiffFamily 2 0 R₂) (x : B) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target)
    (hc : R₁ ((chartAt ℂ x).symm z) (chartAt ℂ ((chartAt ℂ x).symm z) ((chartAt ℂ x).symm z)) =
      R₂ ((chartAt ℂ x).symm z) (chartAt ℂ ((chartAt ℂ x).symm z) ((chartAt ℂ x).symm z))) :
    R₁ x z = R₂ x z := by
  have hs : (chartAt ℂ x).symm z ∈ (chartAt ℂ ((chartAt ℂ x).symm z)).source := mem_chart_source ℂ _
  have hT : chartTransition ((chartAt ℂ x).symm z) x z =
      chartAt ℂ ((chartAt ℂ x).symm z) ((chartAt ℂ x).symm z) := rfl
  rw [h₁.2 _ x z hz hs, h₂.2 _ x z hz hs, hT, hc]

/-- Two quadratic differential families with the same chart-centre values are equal. -/
theorem s31qd5_eq_of_centers {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
    {R₁ R₂ : B → ℂ → ℂ} (h₁ : IsDiffFamily 2 0 R₁) (h₂ : IsDiffFamily 2 0 R₂)
    (hc : ∀ p : B, R₁ p (chartAt ℂ p p) = R₂ p (chartAt ℂ p p)) : R₁ = R₂ := by
  funext x z
  by_cases hz : z ∈ (chartAt ℂ x).target
  · exact s31qd5_eq_at_of_center h₁ h₂ x hz (hc _)
  · rw [h₁.1 x z hz, h₂.1 x z hz]

/-- Transfer of the conjugate transport through a biholomorphism `E`: transporting to `Yd` and then
reflecting along `E ∘ J ∘ E⁻¹` is the same as reflecting along `J` on `Xd` and then transporting. -/
theorem s31qd5_conj_transport_transfer {Xd Yd : ClosedRS.{u}} (E : Xd.carrier ≃ₜ Yd.carrier)
    (hE : IsBiholomorphic (E : Xd.carrier → Yd.carrier))
    {J : Xd.carrier ≃ₜ Xd.carrier} (hJ : IsAnticonformalInvolution J) (Q : Xd.carrier → ℂ → ℂ) :
    s31qr_transportOn univ (fun y : Yd.carrier => E (J (E.symm y))) Complex.conjCLE.toLinearMap
        (s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q) =
      s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
        (s31qr_transportOn univ J Complex.conjCLE.toLinearMap Q) := by
  have hEm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E : Xd.carrier → Yd.carrier) := hE.1
  have hEs : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E.symm : Yd.carrier → Xd.carrier) := hE.homeomorph_symm.1
  funext y z
  by_cases hz : z ∈ (chartAt ℂ y).target
  swap
  · simp only [s31qr_transportOn, hz, false_and, if_false]
  set p : Yd.carrier := (chartAt ℂ y).symm z
  set e : Xd.carrier := E.symm p
  set h : Yd.carrier := E (J e)
  have hz0e : chartAt ℂ e e ∈ (chartAt ℂ e).target := (chartAt ℂ e).map_source (mem_chart_source ℂ e)
  have hz0h : chartAt ℂ h h ∈ (chartAt ℂ h).target := (chartAt ℂ h).map_source (mem_chart_source ℂ h)
  have hlh : (chartAt ℂ h).symm (chartAt ℂ h h) = h := (chartAt ℂ h).left_inv (mem_chart_source ℂ h)
  have hz0J : chartAt ℂ (J e) (J e) ∈ (chartAt ℂ (J e)).target :=
    (chartAt ℂ (J e)).map_source (mem_chart_source ℂ (J e))
  have hlJ : (chartAt ℂ (J e)).symm (chartAt ℂ (J e) (J e)) = J e :=
    (chartAt ℂ (J e)).left_inv (mem_chart_source ℂ (J e))
  have hEh : E.symm h = J e := E.symm_apply_apply (J e)
  -- the four transports at their chart centres
  have hL : s31qr_transportOn univ (fun y : Yd.carrier => E (J (E.symm y))) Complex.conjCLE.toLinearMap
        (s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q) y z =
      conj (s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q h (chartAt ℂ h h)) *
        deriv (fun w => conj (chartAt ℂ h (E (J (E.symm ((chartAt ℂ y).symm w)))))) z ^ 2 :=
    s31qd5_conj_transport_apply _ _ _ y hz (mem_univ _)
  have hR : s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q h (chartAt ℂ h h) =
      Q (J e) (chartAt ℂ (J e) (J e)) *
        deriv (fun v => chartAt ℂ (J e) (E.symm ((chartAt ℂ h).symm v))) (chartAt ℂ h h) ^ 2 := by
    have h0 := s31qd5_id_transport_apply univ (E.symm : Yd.carrier → Xd.carrier) Q h hz0h (mem_univ _)
    rw [hlh, hEh] at h0
    exact h0
  have hRt : s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
        (s31qr_transportOn univ J Complex.conjCLE.toLinearMap Q) y z =
      s31qr_transportOn univ J Complex.conjCLE.toLinearMap Q e (chartAt ℂ e e) *
        deriv (fun w => chartAt ℂ e (E.symm ((chartAt ℂ y).symm w))) z ^ 2 :=
    s31qd5_id_transport_apply _ _ _ y hz (mem_univ _)
  have hK := s31qd5_involution_center J Q e
  -- the chain rule: both sides are the derivative of `conj ∘ φ_{Je} ∘ J ∘ E⁻¹ ∘ φ_y⁻¹`
  have hcont : ContinuousAt (fun w => E.symm ((chartAt ℂ y).symm w)) z :=
    E.symm.continuous.continuousAt.comp ((chartAt ℂ y).continuousAt_symm hz)
  have hcontJ : ContinuousAt (fun w => J (E.symm ((chartAt ℂ y).symm w))) z :=
    J.continuous.continuousAt.comp hcont
  have hcontE : ContinuousAt (fun w => E (J (E.symm ((chartAt ℂ y).symm w)))) z :=
    E.continuous.continuousAt.comp hcontJ
  have hN1 : (fun w => E.symm ((chartAt ℂ y).symm w)) ⁻¹' (chartAt ℂ e).source ∈ 𝓝 z :=
    hcont.preimage_mem_nhds ((chartAt ℂ e).open_source.mem_nhds (mem_chart_source ℂ e))
  have hN2 : (fun w => J (E.symm ((chartAt ℂ y).symm w))) ⁻¹' (chartAt ℂ (J e)).source ∈ 𝓝 z :=
    hcontJ.preimage_mem_nhds ((chartAt ℂ (J e)).open_source.mem_nhds (mem_chart_source ℂ (J e)))
  have hN3 : (fun w => E (J (E.symm ((chartAt ℂ y).symm w)))) ⁻¹' (chartAt ℂ h).source ∈ 𝓝 z :=
    hcontE.preimage_mem_nhds ((chartAt ℂ h).open_source.mem_nhds (mem_chart_source ℂ h))
  have hC : DifferentiableAt ℂ (fun w => chartAt ℂ e (E.symm ((chartAt ℂ y).symm w))) z :=
    s31qr_coordinate_differentiable (H := (E.symm : Yd.carrier → Xd.carrier)) y e hz
      (mem_chart_source ℂ e) (hEs _)
  have hB := s31qd5_involution_coordinate_center J hJ e
  have hΦ1 : HasDerivAt (fun w => conj (chartAt ℂ (J e) (J (E.symm ((chartAt ℂ y).symm w)))))
      (deriv (fun v => conj (chartAt ℂ (J e) (J ((chartAt ℂ e).symm v)))) (chartAt ℂ e e) *
        deriv (fun w => chartAt ℂ e (E.symm ((chartAt ℂ y).symm w))) z) z := by
    refine s31qd5_hasDerivAt_comp_eq hC hB rfl ?_
    filter_upwards [hN1] with w hw
    have hw' : E.symm ((chartAt ℂ y).symm w) ∈ (chartAt ℂ e).source := hw
    rw [(chartAt ℂ e).left_inv hw']
  have hψ : DifferentiableAt ℂ (fun v => chartAt ℂ h (E ((chartAt ℂ (J e)).symm v)))
      (chartAt ℂ (J e) (J e)) :=
    s31qr_coordinate_differentiable (H := (E : Xd.carrier → Yd.carrier)) (J e) h hz0J
      (by rw [hlJ]; exact mem_chart_source ℂ h) (by rw [hlJ]; exact hEm _)
  have hD2 : HasDerivAt (fun w => conj (chartAt ℂ h (E (J (E.symm ((chartAt ℂ y).symm w))))))
      (conj (deriv (fun v => chartAt ℂ h (E ((chartAt ℂ (J e)).symm v))) (chartAt ℂ (J e) (J e))) *
        deriv (fun w => conj (chartAt ℂ (J e) (J (E.symm ((chartAt ℂ y).symm w))))) z) z := by
    refine s31qd5_hasDerivAt_conj_comp_eq hΦ1.differentiableAt hψ rfl ?_
    filter_upwards [hN2] with w hw
    have hw' : J (E.symm ((chartAt ℂ y).symm w)) ∈ (chartAt ℂ (J e)).source := hw
    rw [Complex.conj_conj, (chartAt ℂ (J e)).left_inv hw']
  have hA : DifferentiableAt ℂ (fun v => chartAt ℂ (J e) (E.symm ((chartAt ℂ h).symm v)))
      (chartAt ℂ h h) :=
    s31qr_coordinate_differentiable (H := (E.symm : Yd.carrier → Xd.carrier)) h (J e) hz0h
      (by rw [hlh, hEh]; exact mem_chart_source ℂ (J e)) (hEs _)
  have hΦ2 : HasDerivAt (fun w => conj (chartAt ℂ (J e) (J (E.symm ((chartAt ℂ y).symm w)))))
      (conj (deriv (fun v => chartAt ℂ (J e) (E.symm ((chartAt ℂ h).symm v))) (chartAt ℂ h h)) *
        deriv (fun w => conj (chartAt ℂ h (E (J (E.symm ((chartAt ℂ y).symm w)))))) z) z := by
    refine s31qd5_hasDerivAt_conj_comp_eq hD2.differentiableAt hA rfl ?_
    filter_upwards [hN3] with w hw
    have hw' : E (J (E.symm ((chartAt ℂ y).symm w))) ∈ (chartAt ℂ h).source := hw
    rw [Complex.conj_conj, (chartAt ℂ h).left_inv hw', E.symm_apply_apply]
  have hkey := hΦ2.unique hΦ1
  rw [hL, hRt, hR, hK, map_mul, map_pow]
  linear_combination (conj (Q (J e) (chartAt ℂ (J e) (J e))) *
    (conj (deriv (fun v => chartAt ℂ (J e) (E.symm ((chartAt ℂ h).symm v))) (chartAt ℂ h h)) *
        deriv (fun w => conj (chartAt ℂ h (E (J (E.symm ((chartAt ℂ y).symm w)))))) z +
      deriv (fun v => conj (chartAt ℂ (J e) (J ((chartAt ℂ e).symm v)))) (chartAt ℂ e e) *
        deriv (fun w => chartAt ℂ e (E.symm ((chartAt ℂ y).symm w))) z)) * hkey

/-- (S5) The symmetric extension is fixed by the reflection: for the seam-filled data `Q` of an admissible
`q` (the conclusion of `s31qi_seam_fill` at `q`), the conjugate transport along `E ∘ J ∘ E⁻¹` of its
transport to `Fd.X` is that transport again. -/
theorem s31qd_ext_fixed {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {gd nd : ℕ} (Fd : FiniteTypeStructure (puncturedOpens Pd) gd nd 0)
    (E : Xd.carrier ≃ₜ Fd.X.carrier) (hE : IsBiholomorphic (E : Xd.carrier → Fd.X.carrier))
    (hP : ∀ p : Xd.carrier, p ∈ Pd ↔ E p ∈ Fd.P)
    (q : admissibleQDSpace F) {Q : Xd.carrier → ℂ → ℂ} (h1 : IsDiffFamily 2 0 Q)
    (h2 : ∀ a : Xd.carrier, DifferentiableOn ℂ (Q a)
      ((chartAt ℂ a).target ∩ (chartAt ℂ a).symm ⁻¹' (↑Pd : Set Xd.carrier)ᶜ))
    (h3 : ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range ιd →
      Q x z = s31qr_positiveData F hd (q : F.X.carrier → ℂ → ℂ) x z)
    (h4 : ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range (J ∘ ιd) →
      Q x z = s31qr_mirrorData F hd (q : F.X.carrier → ℂ → ℂ) x z)
    (h5 : ∀ a : Xd.carrier, ∀ p ∈ Pd, p ∈ (chartAt ℂ a).source → Q a (chartAt ℂ a p) = 0) :
    s31qr_transportOn univ (fun y : Fd.X.carrier => E (J (E.symm y))) Complex.conjCLE.toLinearMap
        (s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q) =
      s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q := by
  -- `hm` and `hP` belong to the frozen setting; the statement holds without them.
  have _hm := hm
  have _hP := hP
  have : Nonempty S := inferInstance
  have hJ := hd.involution
  have hJJ : ∀ p, J (J p) = p := hJ.1
  have hPc : IsOpen ((↑Pd : Set Xd.carrier)ᶜ) := Pd.finite_toSet.isClosed.isOpen_compl
  -- `K`: the reflection of `Q` along `J` on the double itself
  have hKfam : IsDiffFamily 2 0 (s31qr_transportOn univ J Complex.conjCLE.toLinearMap Q) :=
    s31qr_transport_family univ J _ (fun x z hz _ => s31qr_involution_coordinate J hJ x hz) Q
  -- centre values on the positive half
  have hcenPos : ∀ e : Xd.carrier, e ∈ range ιd →
      s31qr_transportOn univ J Complex.conjCLE.toLinearMap Q e (chartAt ℂ e e) = Q e (chartAt ℂ e e) := by
    intro e he
    have hz0 : chartAt ℂ e e ∈ (chartAt ℂ e).target := (chartAt ℂ e).map_source (mem_chart_source ℂ e)
    have hl : (chartAt ℂ e).symm (chartAt ℂ e e) = e := (chartAt ℂ e).left_inv (mem_chart_source ℂ e)
    have hz1 : chartAt ℂ (J e) (J e) ∈ (chartAt ℂ (J e)).target :=
      (chartAt ℂ (J e)).map_source (mem_chart_source ℂ (J e))
    have hl1 : (chartAt ℂ (J e)).symm (chartAt ℂ (J e) (J e)) = J e :=
      (chartAt ℂ (J e)).left_inv (mem_chart_source ℂ (J e))
    have hJe : J e ∈ range (J ∘ ιd) :=
      (s31qr_mirror_membership F hd (J e)).1 (by rw [hJJ e]; exact he)
    have hHe : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (s31qr_halfReturn F hd) e :=
      s31qr_halfReturn_holomorphic F hd he
    have hQe : Q e (chartAt ℂ e e) =
        (q : F.X.carrier → ℂ → ℂ) (s31qr_halfReturn F hd e)
          (chartAt ℂ (s31qr_halfReturn F hd e) (s31qr_halfReturn F hd e)) *
        deriv (fun w => chartAt ℂ (s31qr_halfReturn F hd e)
          (s31qr_halfReturn F hd ((chartAt ℂ e).symm w))) (chartAt ℂ e e) ^ 2 := by
      rw [h3 e _ hz0 (by rw [hl]; exact he)]
      have h0 := s31qd5_id_transport_apply (range ιd) (s31qr_halfReturn F hd)
        (q : F.X.carrier → ℂ → ℂ) e hz0 (by rw [hl]; exact he)
      rw [hl] at h0
      exact h0
    have hQJ : Q (J e) (chartAt ℂ (J e) (J e)) =
        conj ((q : F.X.carrier → ℂ → ℂ) (s31qr_halfReturn F hd e)
          (chartAt ℂ (s31qr_halfReturn F hd e) (s31qr_halfReturn F hd e))) *
        deriv (fun w => conj (chartAt ℂ (s31qr_halfReturn F hd e)
          (s31qr_halfReturn F hd (J ((chartAt ℂ (J e)).symm w))))) (chartAt ℂ (J e) (J e)) ^ 2 := by
      rw [h4 (J e) _ hz1 (by rw [hl1]; exact hJe)]
      have h0 := s31qd5_conj_transport_apply (range (J ∘ ιd)) (s31qr_halfReturn F hd ∘ J)
        (q : F.X.carrier → ℂ → ℂ) (J e) hz1 (by rw [hl1]; exact hJe)
      rw [hl1] at h0
      simp only [Function.comp_apply, hJJ e] at h0
      exact h0
    have hKe := s31qd5_involution_center J Q e
    have hB := s31qd5_involution_coordinate_center J hJ e
    have hM : DifferentiableAt ℂ (fun w => conj (chartAt ℂ (s31qr_halfReturn F hd e)
        (s31qr_halfReturn F hd (J ((chartAt ℂ (J e)).symm w))))) (chartAt ℂ (J e) (J e)) := by
      have h0 := s31qr_return_after_involution J hJ (s31qr_halfReturn F hd) (J e) hz1
        (by rw [hl1, hJJ e]; exact hHe)
      rw [hl1, hJJ e] at h0
      exact h0
    have hN : (fun w => J ((chartAt ℂ e).symm w)) ⁻¹' (chartAt ℂ (J e)).source ∈ 𝓝 (chartAt ℂ e e) :=
      (J.continuous.continuousAt.comp ((chartAt ℂ e).continuousAt_symm hz0)).preimage_mem_nhds
        ((chartAt ℂ (J e)).open_source.mem_nhds (by
          show J ((chartAt ℂ e).symm (chartAt ℂ e e)) ∈ (chartAt ℂ (J e)).source
          rw [hl]
          exact mem_chart_source ℂ (J e)))
    have hPder : HasDerivAt (fun w => chartAt ℂ (s31qr_halfReturn F hd e)
          (s31qr_halfReturn F hd ((chartAt ℂ e).symm w)))
        (conj (deriv (fun w => conj (chartAt ℂ (s31qr_halfReturn F hd e)
            (s31qr_halfReturn F hd (J ((chartAt ℂ (J e)).symm w))))) (chartAt ℂ (J e) (J e))) *
          deriv (fun v => conj (chartAt ℂ (J e) (J ((chartAt ℂ e).symm v)))) (chartAt ℂ e e))
        (chartAt ℂ e e) := by
      refine s31qd5_hasDerivAt_conj_comp_eq hB hM ?_ ?_
      · show conj (chartAt ℂ (J e) (J e)) =
          conj (chartAt ℂ (J e) (J ((chartAt ℂ e).symm (chartAt ℂ e e))))
        rw [hl]
      · filter_upwards [hN] with w hw
        have hw' : J ((chartAt ℂ e).symm w) ∈ (chartAt ℂ (J e)).source := hw
        simp only [Complex.conj_conj]
        rw [(chartAt ℂ (J e)).left_inv hw', hJJ]
    rw [hKe, hQJ, hQe, hPder.deriv, map_mul, map_pow, Complex.conj_conj]
    ring
  -- centre values on the mirror half
  have hcenMir : ∀ e : Xd.carrier, e ∈ range (J ∘ ιd) →
      s31qr_transportOn univ J Complex.conjCLE.toLinearMap Q e (chartAt ℂ e e) = Q e (chartAt ℂ e e) := by
    intro e he
    have hz0 : chartAt ℂ e e ∈ (chartAt ℂ e).target := (chartAt ℂ e).map_source (mem_chart_source ℂ e)
    have hl : (chartAt ℂ e).symm (chartAt ℂ e e) = e := (chartAt ℂ e).left_inv (mem_chart_source ℂ e)
    have hz1 : chartAt ℂ (J e) (J e) ∈ (chartAt ℂ (J e)).target :=
      (chartAt ℂ (J e)).map_source (mem_chart_source ℂ (J e))
    have hl1 : (chartAt ℂ (J e)).symm (chartAt ℂ (J e) (J e)) = J e :=
      (chartAt ℂ (J e)).left_inv (mem_chart_source ℂ (J e))
    have hJe : J e ∈ range ιd := (s31qr_mirror_membership F hd e).2 he
    have hHe : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (s31qr_halfReturn F hd) (J e) :=
      s31qr_halfReturn_holomorphic F hd hJe
    have hQe : Q e (chartAt ℂ e e) =
        conj ((q : F.X.carrier → ℂ → ℂ) (s31qr_halfReturn F hd (J e))
          (chartAt ℂ (s31qr_halfReturn F hd (J e)) (s31qr_halfReturn F hd (J e)))) *
        deriv (fun w => conj (chartAt ℂ (s31qr_halfReturn F hd (J e))
          (s31qr_halfReturn F hd (J ((chartAt ℂ e).symm w))))) (chartAt ℂ e e) ^ 2 := by
      rw [h4 e _ hz0 (by rw [hl]; exact he)]
      have h0 := s31qd5_conj_transport_apply (range (J ∘ ιd)) (s31qr_halfReturn F hd ∘ J)
        (q : F.X.carrier → ℂ → ℂ) e hz0 (by rw [hl]; exact he)
      rw [hl] at h0
      simp only [Function.comp_apply] at h0
      exact h0
    have hQJ : Q (J e) (chartAt ℂ (J e) (J e)) =
        (q : F.X.carrier → ℂ → ℂ) (s31qr_halfReturn F hd (J e))
          (chartAt ℂ (s31qr_halfReturn F hd (J e)) (s31qr_halfReturn F hd (J e))) *
        deriv (fun w => chartAt ℂ (s31qr_halfReturn F hd (J e))
          (s31qr_halfReturn F hd ((chartAt ℂ (J e)).symm w))) (chartAt ℂ (J e) (J e)) ^ 2 := by
      rw [h3 (J e) _ hz1 (by rw [hl1]; exact hJe)]
      have h0 := s31qd5_id_transport_apply (range ιd) (s31qr_halfReturn F hd)
        (q : F.X.carrier → ℂ → ℂ) (J e) hz1 (by rw [hl1]; exact hJe)
      rw [hl1] at h0
      exact h0
    have hKe := s31qd5_involution_center J Q e
    have hB := s31qd5_involution_coordinate_center J hJ e
    have hPd : DifferentiableAt ℂ (fun w => chartAt ℂ (s31qr_halfReturn F hd (J e))
        (s31qr_halfReturn F hd ((chartAt ℂ (J e)).symm w))) (chartAt ℂ (J e) (J e)) :=
      s31qr_coordinate_differentiable (H := s31qr_halfReturn F hd) (J e) (s31qr_halfReturn F hd (J e))
        hz1 (by rw [hl1]; exact mem_chart_source ℂ _) (by rw [hl1]; exact hHe)
    have hN : (fun w => J ((chartAt ℂ e).symm w)) ⁻¹' (chartAt ℂ (J e)).source ∈ 𝓝 (chartAt ℂ e e) :=
      (J.continuous.continuousAt.comp ((chartAt ℂ e).continuousAt_symm hz0)).preimage_mem_nhds
        ((chartAt ℂ (J e)).open_source.mem_nhds (by
          show J ((chartAt ℂ e).symm (chartAt ℂ e e)) ∈ (chartAt ℂ (J e)).source
          rw [hl]
          exact mem_chart_source ℂ (J e)))
    have hMder : HasDerivAt (fun w => conj (chartAt ℂ (s31qr_halfReturn F hd (J e))
          (s31qr_halfReturn F hd (J ((chartAt ℂ e).symm w)))))
        (conj (deriv (fun w => chartAt ℂ (s31qr_halfReturn F hd (J e))
            (s31qr_halfReturn F hd ((chartAt ℂ (J e)).symm w))) (chartAt ℂ (J e) (J e))) *
          deriv (fun v => conj (chartAt ℂ (J e) (J ((chartAt ℂ e).symm v)))) (chartAt ℂ e e))
        (chartAt ℂ e e) := by
      refine s31qd5_hasDerivAt_conj_comp_eq hB hPd ?_ ?_
      · show conj (chartAt ℂ (J e) (J e)) =
          conj (chartAt ℂ (J e) (J ((chartAt ℂ e).symm (chartAt ℂ e e))))
        rw [hl]
      · filter_upwards [hN] with w hw
        have hw' : J ((chartAt ℂ e).symm w) ∈ (chartAt ℂ (J e)).source := hw
        simp only [Complex.conj_conj]
        rw [(chartAt ℂ (J e)).left_inv hw']
    rw [hKe, hQJ, hQe, hMder.deriv, map_mul, map_pow]
    ring
  -- centre values at the punctures
  have hcenP : ∀ e : Xd.carrier, e ∈ Pd →
      s31qr_transportOn univ J Complex.conjCLE.toLinearMap Q e (chartAt ℂ e e) = Q e (chartAt ℂ e e) := by
    intro e he
    have hJe : J e ∈ Pd := by
      have h0 : J e ∈ J '' (↑Pd : Set Xd.carrier) := mem_image_of_mem J (Finset.mem_coe.2 he)
      rw [hd.Pd_invariant] at h0
      exact Finset.mem_coe.1 h0
    rw [s31qd5_involution_center J Q e, h5 (J e) (J e) hJe (mem_chart_source ℂ _),
      h5 e e he (mem_chart_source ℂ _)]
    simp
  -- agreement at every chart point over the two halves
  have hhalf : ∀ (x : Xd.carrier) (w : ℂ), w ∈ (chartAt ℂ x).target →
      (chartAt ℂ x).symm w ∈ range ιd ∪ range (J ∘ ιd) →
      s31qr_transportOn univ J Complex.conjCLE.toLinearMap Q x w = Q x w := by
    intro x w hw hp
    apply s31qd5_eq_at_of_center hKfam h1 x hw
    rcases hp with hp | hp
    · exact hcenPos _ hp
    · exact hcenMir _ hp
  -- centre values on the seam: density of the halves and continuity off `Pd`
  have hcenS : ∀ e : Xd.carrier, J e = e → e ∉ Pd →
      s31qr_transportOn univ J Complex.conjCLE.toLinearMap Q e (chartAt ℂ e e) = Q e (chartAt ℂ e e) := by
    intro e hfix hnP
    have hz0 : chartAt ℂ e e ∈ (chartAt ℂ e).target := (chartAt ℂ e).map_source (mem_chart_source ℂ e)
    have hl : (chartAt ℂ e).symm (chartAt ℂ e e) = e := (chartAt ℂ e).left_inv (mem_chart_source ℂ e)
    have hcl := s31q2_halves_dense F hd e hz0
    have hne : (𝓝[{w : ℂ | w ∈ (chartAt ℂ e).target ∧
        (chartAt ℂ e).symm w ∈ range ιd ∪ range (J ∘ ιd)}] (chartAt ℂ e e)).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 hcl
    have hQc : ContinuousAt (Q e) (chartAt ℂ e e) :=
      ((h2 e).differentiableAt (((chartAt ℂ e).isOpen_inter_preimage_symm hPc).mem_nhds
        ⟨hz0, by
          show (chartAt ℂ e).symm (chartAt ℂ e e) ∈ (↑Pd : Set Xd.carrier)ᶜ
          rw [hl]
          exact fun h => hnP (Finset.mem_coe.1 h)⟩)).continuousAt
    have hKd := s31q2_conj_transport_holomorphic J hJ hPc hPc (H := id)
      (fun _ _ => mdifferentiableAt_id) (fun _ hp => hp) h1 h2 e
    have hN' : (chartAt ℂ e).target ∩ (chartAt ℂ e).symm ⁻¹' (J ⁻¹' (↑Pd : Set Xd.carrier)ᶜ) ∈
        𝓝 (chartAt ℂ e e) :=
      ((chartAt ℂ e).isOpen_inter_preimage_symm (hPc.preimage J.continuous)).mem_nhds
        ⟨hz0, by
          show J ((chartAt ℂ e).symm (chartAt ℂ e e)) ∈ (↑Pd : Set Xd.carrier)ᶜ
          rw [hl, hfix]
          exact fun h => hnP (Finset.mem_coe.1 h)⟩
    have hKc : ContinuousAt (s31qr_transportOn univ J Complex.conjCLE.toLinearMap Q e)
        (chartAt ℂ e e) := by
      refine (hKd.differentiableAt hN').continuousAt.congr ?_
      filter_upwards [hN'] with w hw
      rw [s31qd5_conj_transport_apply (J ⁻¹' (↑Pd : Set Xd.carrier)ᶜ)
          (id ∘ (J : Xd.carrier → Xd.carrier)) Q e hw.1 hw.2,
        s31qd5_conj_transport_apply univ (J : Xd.carrier → Xd.carrier) Q e hw.1 (mem_univ _)]
      rfl
    have hT1 : Tendsto (s31qr_transportOn univ J Complex.conjCLE.toLinearMap Q e)
        (𝓝[{w : ℂ | w ∈ (chartAt ℂ e).target ∧
          (chartAt ℂ e).symm w ∈ range ιd ∪ range (J ∘ ιd)}] (chartAt ℂ e e))
        (𝓝 (s31qr_transportOn univ J Complex.conjCLE.toLinearMap Q e (chartAt ℂ e e))) :=
      hKc.tendsto.mono_left nhdsWithin_le_nhds
    have hT2 : Tendsto (s31qr_transportOn univ J Complex.conjCLE.toLinearMap Q e)
        (𝓝[{w : ℂ | w ∈ (chartAt ℂ e).target ∧
          (chartAt ℂ e).symm w ∈ range ιd ∪ range (J ∘ ιd)}] (chartAt ℂ e e))
        (𝓝 (Q e (chartAt ℂ e e))) := by
      refine (hQc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact (hhalf e w hw.1 hw.2).symm
    exact tendsto_nhds_unique hT1 hT2
  -- all centre values agree, so `K = Q`
  have hcen : ∀ e : Xd.carrier,
      s31qr_transportOn univ J Complex.conjCLE.toLinearMap Q e (chartAt ℂ e e) = Q e (chartAt ℂ e e) := by
    intro e
    by_cases hPe : e ∈ Pd
    · exact hcenP e hPe
    have hmem : e ∈ range ιd ∪ range (J ∘ ιd) ∪ {x | J x = x} ∪ ↑Pd := by
      rw [hd.cover]
      exact mem_univ e
    rcases hmem with ((he | he) | he) | he
    · exact hcenPos e he
    · exact hcenMir e he
    · exact hcenS e he hPe
    · exact absurd (Finset.mem_coe.1 he) hPe
  have hKQ : s31qr_transportOn univ J Complex.conjCLE.toLinearMap Q = Q :=
    s31qd5_eq_of_centers hKfam h1 hcen
  rw [s31qd5_conj_transport_transfer E hE hJ Q, hKQ]

end LiZhongQC
