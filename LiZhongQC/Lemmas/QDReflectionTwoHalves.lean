import LiZhongQC.Lemmas.FiniteTypeChartInverse

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u v

/-- A holomorphic open embedding has a holomorphic inverse on its actual range.
The inverse is the existing partial-homeomorphism inverse, not a new choice. -/
theorem s31qr_open_embedding_inverse
    {A : Type u} {B : Type v} [TopologicalSpace A] [ChartedSpace ℂ A]
    [TopologicalSpace B] [ChartedSpace ℂ B]
    [IsManifold 𝓘(ℂ) ω A] [IsManifold 𝓘(ℂ) ω B] [Nonempty A]
    {f : A → B} (hf : Topology.IsOpenEmbedding f)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {p : B} (hp : p ∈ range f) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (hf.toOpenPartialHomeomorph f).symm p := by
  let χ := chartAt ℂ p
  let U : Set A := f ⁻¹' χ.source
  let φ : A → ℂ := fun s => χ (f s)
  have hU : IsOpen U := χ.open_source.preimage hf.continuous
  have hi : InjOn φ U := by
    intro s hs t ht he
    exact hf.injective (χ.injOn hs ht he)
  have hm : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) φ U := by
    intro s hs
    exact ((mdifferentiableAt_atlas (chart_mem_atlas ℂ p) hs).comp s
      (hhol s)).mdifferentiableWithinAt
  have hpφ : χ p ∈ φ '' U := by
    obtain ⟨s, hs⟩ := hp
    refine ⟨s, ?_, ?_⟩
    · change f s ∈ χ.source
      rw [hs]
      exact mem_chart_source ℂ p
    · change χ (f s) = χ p
      rw [hs]
  have hInv := s31eg_coordinate_inverse hU hi hm hpφ
  have hc : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) χ p :=
    mdifferentiableAt_atlas (chart_mem_atlas ℂ p) (mem_chart_source ℂ p)
  have heq : (hf.toOpenPartialHomeomorph f).symm =ᶠ[𝓝 p]
      fun y => Function.invFunOn φ U (χ y) := by
    filter_upwards [(hf.isOpenMap.isOpen_range.inter χ.open_source).mem_nhds
      ⟨hp, mem_chart_source ℂ p⟩] with y hy
    have hey := hf.toOpenPartialHomeomorph_right_inv f hy.1
    have heU : (hf.toOpenPartialHomeomorph f).symm y ∈ U := by
      change f ((hf.toOpenPartialHomeomorph f).symm y) ∈ χ.source
      rw [hey]
      exact hy.2
    have hh := hi.leftInvOn_invFunOn heU
    change Function.invFunOn φ U (χ (f ((hf.toOpenPartialHomeomorph f).symm y))) =
      (hf.toOpenPartialHomeomorph f).symm y at hh
    rw [hey] at hh
    exact hh.symm
  exact (hInv.comp p hc).congr_of_eventuallyEq heq

section Transport
variable {A : Type u} {B : Type v} [TopologicalSpace A] [ChartedSpace ℂ A]
  [TopologicalSpace B] [ChartedSpace ℂ B]

/-- Actual coordinate transport on a specified open piece. C is identity for a
holomorphic map and complex conjugation for an antiholomorphic map.
The guards suppress all off-chart and off-piece values. -/
def s31qr_transportOn (U : Set B) (H : B → A) (C : ℂ →ₗ[ℝ] ℂ)
    (q : A → ℂ → ℂ) : B → ℂ → ℂ := by
  classical
  exact fun x z => if z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ U then
    C (q (H ((chartAt ℂ x).symm z))
      (chartAt ℂ (H ((chartAt ℂ x).symm z)) (H ((chartAt ℂ x).symm z)))) *
      deriv (fun w => C (chartAt ℂ (H ((chartAt ℂ x).symm z))
        (H ((chartAt ℂ x).symm w)))) z ^ 2
    else 0

theorem s31qr_transport_add (U : Set B) (H : B → A) (C : ℂ →ₗ[ℝ] ℂ)
    (q r : A → ℂ → ℂ) :
    s31qr_transportOn U H C (q + r) =
      s31qr_transportOn U H C q + s31qr_transportOn U H C r := by
  funext x z
  by_cases h : z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ U
  · simp only [s31qr_transportOn, h, and_self, if_pos, Pi.add_apply, map_add, add_mul]
  · simp only [s31qr_transportOn, h, if_false, Pi.add_apply, add_zero]

theorem s31qr_transport_real_smul (U : Set B) (H : B → A) (C : ℂ →ₗ[ℝ] ℂ)
    (c : ℝ) (q : A → ℂ → ℂ) :
    s31qr_transportOn U H C (c • q) = c • s31qr_transportOn U H C q := by
  funext x z
  by_cases h : z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ U
  · simp only [s31qr_transportOn, h, and_self, if_pos, Pi.smul_apply]
    rw [map_smul]
    simp only [Complex.real_smul]
    ring
  · simp only [s31qr_transportOn, h, if_false, Pi.smul_apply, smul_zero]

theorem s31qr_transport_off_piece (U : Set B) (H : B → A) (C : ℂ →ₗ[ℝ] ℂ)
    (q : A → ℂ → ℂ) (x : B) (z : ℂ) (hz : (chartAt ℂ x).symm z ∉ U) :
    s31qr_transportOn U H C q x z = 0 := by
  simp only [s31qr_transportOn, hz, and_false, if_false]

/-- The coordinate tensor law is assembled from actual first derivatives of H.
The hypothesis is a local geometric regularity condition on H and C, independent
of q; no differential extension or overlap conclusion is an input. -/
theorem s31qr_transport_family [IsManifold 𝓘(ℂ) ω B]
    (U : Set B) (H : B → A) (C : ℂ →ₗ[ℝ] ℂ)
    (hcoord : ∀ x : B, ∀ z ∈ (chartAt ℂ x).target,
      (chartAt ℂ x).symm z ∈ U →
        DifferentiableAt ℂ (fun w => C (chartAt ℂ (H ((chartAt ℂ x).symm z))
          (H ((chartAt ℂ x).symm w)))) z)
    (q : A → ℂ → ℂ) : IsDiffFamily 2 0 (s31qr_transportOn U H C q) := by
  constructor
  · intro x z hz
    simp only [s31qr_transportOn, hz, false_and, if_false]
  · intro x y z hz hs
    obtain ⟨hxt, _, hpoint⟩ := s23_transition_mem hz hs
    rw [zpow_zero, mul_one, zpow_two]
    by_cases hU : (chartAt ℂ y).symm z ∈ U
    · have hUx : (chartAt ℂ x).symm (chartTransition x y z) ∈ U := hpoint.symm ▸ hU
      have hd := hcoord x (chartTransition x y z) hxt hUx
      rw [hpoint] at hd
      have he :
          (fun w => C (chartAt ℂ (H ((chartAt ℂ y).symm z))
            (H ((chartAt ℂ y).symm w)))) =ᶠ[𝓝 z]
          (fun w => C (chartAt ℂ (H ((chartAt ℂ y).symm z))
            (H ((chartAt ℂ x).symm w)))) ∘ chartTransition x y := by
        filter_upwards [((chartAt ℂ y).isOpen_inter_preimage_symm
          (chartAt ℂ x).open_source).mem_nhds ⟨hz, hs⟩] with w hw
        change C (chartAt ℂ (H ((chartAt ℂ y).symm z)) (H ((chartAt ℂ y).symm w))) =
          C (chartAt ℂ (H ((chartAt ℂ y).symm z))
            (H ((chartAt ℂ x).symm (chartAt ℂ x ((chartAt ℂ y).symm w)))))
        rw [(chartAt ℂ x).left_inv hw.2]
      have hder := he.deriv_eq
      rw [deriv_comp z hd (s23_transition_differentiableAt x y hz hs)] at hder
      simp only [s31qr_transportOn, hz, hxt, hU, hUx, and_self, if_pos, hpoint]
      rw [hder]
      ring
    · have hUx : (chartAt ℂ x).symm (chartTransition x y z) ∉ U := by
        rwa [hpoint]
      simp only [s31qr_transportOn, hU, hUx, and_false, if_false, zero_mul]

/-- Holomorphic maps provide the geometric coordinate hypothesis for the
identity version of transportOn. -/
theorem s31qr_holomorphic_transport_family [IsManifold 𝓘(ℂ) ω A]
    [IsManifold 𝓘(ℂ) ω B] (U : Set B) (H : B → A)
    (hH : ∀ p ∈ U, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H p)
    (q : A → ℂ → ℂ) :
    IsDiffFamily 2 0 (s31qr_transportOn U H (LinearMap.id : ℂ →ₗ[ℝ] ℂ) q) := by
  apply s31qr_transport_family
  intro x z hz hp
  have h := (s23_mdifferentiableAt_iff
    ((chartAt ℂ x).map_target hz) (mem_chart_source ℂ (H ((chartAt ℂ x).symm z)))).1
      (hH _ hp)
  have hd := h.2
  rw [(chartAt ℂ x).right_inv hz] at hd
  exact hd

end Transport

section AntiholomorphicTransport
variable {A : Type u} {B : Type v} [TopologicalSpace A] [ChartedSpace ℂ A]
  [TopologicalSpace B] [ChartedSpace ℂ B]
  [IsManifold 𝓘(ℂ) ω A] [IsManifold 𝓘(ℂ) ω B]

/-- The antiholomorphic coordinate condition in the definition of J is valid
in any preferred source chart, not just the chart centred at the point. -/
theorem s31qr_involution_coordinate (J : B ≃ₜ B) (hJ : IsAnticonformalInvolution J)
    (x : B) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) :
    DifferentiableAt ℂ
      (fun w => conj (chartAt ℂ (J ((chartAt ℂ x).symm z))
        (J ((chartAt ℂ x).symm w)))) z := by
  let p := (chartAt ℂ x).symm z
  have hs : (chartAt ℂ x).symm z ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
  have hL : DifferentiableAt ℂ (fun w => conj (localMapExpr J p w))
      (chartTransition p x z) := by
    change DifferentiableAt ℂ (fun w => conj (localMapExpr J p w)) (chartAt ℂ p p)
    exact (hJ.2 p).differentiableAt
      ((s23_localMapDomain_isOpen J.continuous p).mem_nhds (s23_h_center J p).1)
  have hd := hL.comp z (s23_transition_differentiableAt p x hz hs)
  apply hd.congr_of_eventuallyEq
  filter_upwards [((chartAt ℂ x).isOpen_inter_preimage_symm
    (chartAt ℂ p).open_source).mem_nhds ⟨hz, hs⟩] with w hw
  change conj (chartAt ℂ (J p) (J ((chartAt ℂ x).symm w))) =
    conj (chartAt ℂ (J p) (J ((chartAt ℂ p).symm
      (chartAt ℂ p ((chartAt ℂ x).symm w)))))
  rw [(chartAt ℂ p).left_inv hw.2]

/-- Postcomposing the involution with a holomorphic return map gives the
conjugated holomorphic coordinate used in the actual mirror coefficient. -/
theorem s31qr_return_after_involution (J : B ≃ₜ B)
    (hJ : IsAnticonformalInvolution J) (H : B → A)
    (x : B) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (hH : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H (J ((chartAt ℂ x).symm z))) :
    DifferentiableAt ℂ (fun w => conj
      (chartAt ℂ (H (J ((chartAt ℂ x).symm z))) (H (J ((chartAt ℂ x).symm w))))) z := by
  let p := (chartAt ℂ x).symm z
  let t := J p
  let ψ : ℂ → ℂ := fun v => chartAt ℂ (H t) (H ((chartAt ℂ t).symm v))
  let η : ℂ → ℂ := fun w => conj (chartAt ℂ t (J ((chartAt ℂ x).symm w)))
  have hψ : DifferentiableAt ℂ ψ (chartAt ℂ t t) :=
    ((s23_mdifferentiableAt_iff (mem_chart_source ℂ t)
      (mem_chart_source ℂ (H t))).1 hH).2
  have hη : DifferentiableAt ℂ η z := s31qr_involution_coordinate J hJ x hz
  have hψc : DifferentiableAt ℂ (conj ∘ ψ ∘ conj) (η z) := hψ.conj_conj
  have hd := hψc.comp z hη
  apply hd.congr_of_eventuallyEq
  have ht : ContinuousAt (fun w => J ((chartAt ℂ x).symm w)) z :=
    J.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz)
  filter_upwards [ht.preimage_mem_nhds ((chartAt ℂ t).open_source.mem_nhds
    (mem_chart_source ℂ t))] with w hw
  change conj (chartAt ℂ (H t) (H (J ((chartAt ℂ x).symm w)))) =
    conj (chartAt ℂ (H t) (H ((chartAt ℂ t).symm
      (conj (conj (chartAt ℂ t (J ((chartAt ℂ x).symm w))))))))
  rw [Complex.conj_conj, (chartAt ℂ t).left_inv hw]

theorem s31qr_antiholomorphic_transport_family (U : Set B) (H : B → A)
    (hH : ∀ p ∈ U, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H p)
    (J : B ≃ₜ B) (hJ : IsAnticonformalInvolution J) (q : A → ℂ → ℂ) :
    IsDiffFamily 2 0 (s31qr_transportOn (J ⁻¹' U) (H ∘ J)
      Complex.conjCLE.toLinearMap q) := by
  apply s31qr_transport_family
  intro x z hz hp
  exact s31qr_return_after_involution J hJ H x hz (hH _ hp)

end AntiholomorphicTransport

section DoubleHalves
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
  [Nonempty S] {g n m : ℕ}
  (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
  {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
  (hd : IsSchottkyDouble F Xd J ιd Pd)

/-- The genuine return map from the positive half to the original compactification.
Its values outside the half are never used without a guard. -/
def s31qr_halfReturn : Xd.carrier → F.X.carrier :=
  fun p => F.ι ((hd.embedding.toOpenPartialHomeomorph ιd).symm p)

theorem s31qr_halfReturn_image (s : S) :
    s31qr_halfReturn F hd (ιd s) = F.ι s := by
  change F.ι ((hd.embedding.toOpenPartialHomeomorph ιd).symm (ιd s)) = F.ι s
  rw [hd.embedding.toOpenPartialHomeomorph_left_inv ιd]

theorem s31qr_halfReturn_holomorphic [IsManifold 𝓘(ℂ) ω S]
    {p : Xd.carrier} (hp : p ∈ range ιd) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (s31qr_halfReturn F hd) p := by
  exact (F.holomorphic _).comp p
    (s31qr_open_embedding_inverse hd.embedding hd.holomorphic hp)

section HalfGeometry
include F hd

/-- The involution exchanges precisely the two given half images. -/
theorem s31qr_mirror_membership (p : Xd.carrier) :
    J p ∈ range ιd ↔ p ∈ range (J ∘ ιd) := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change J (ιd s) = p
    rw [hs, hd.involution.1 p]
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change J (ιd s) = p at hs
    rw [← hs, hd.involution.1]

theorem s31qr_half_not_fixed {p : Xd.carrier} (hp : p ∈ range ιd) : J p ≠ p := by
  intro he
  have hm : p ∈ range (J ∘ ιd) := (s31qr_mirror_membership F hd p).1 (he.symm ▸ hp)
  exact Set.disjoint_left.1 hd.disjoint hp hm

/-- Outside the two actual halves only the seam and the listed punctures remain.
This does not assert the still-needed puncture/end correspondence. -/
theorem s31qr_outside_halves {p : Xd.carrier}
    (hp : p ∉ range ιd) (hm : p ∉ range (J ∘ ιd)) :
    J p = p ∨ p ∈ Pd := by
  have hc : p ∈ range ιd ∪ range (J ∘ ιd) ∪ {x | J x = x} ∪ (↑Pd : Set Xd.carrier) := by
    rw [hd.cover]
    trivial
  rcases hc with ((h | h) | h) | h
  · exact False.elim (hp h)
  · exact False.elim (hm h)
  · exact Or.inl h
  · exact Or.inr h

end HalfGeometry

/-- Coefficient data on the positive half, pushed forward by the inverse of ιd. -/
def s31qr_positiveData (q : F.X.carrier → ℂ → ℂ) : Xd.carrier → ℂ → ℂ :=
  s31qr_transportOn (range ιd) (s31qr_halfReturn F hd)
    (LinearMap.id : ℂ →ₗ[ℝ] ℂ) q

/-- Actual conjugate coefficient data on the mirror half. Both the coefficient
and the return coordinate are conjugated; the latter gives a holomorphic jet. -/
def s31qr_mirrorData (q : F.X.carrier → ℂ → ℂ) : Xd.carrier → ℂ → ℂ :=
  s31qr_transportOn (range (J ∘ ιd)) (s31qr_halfReturn F hd ∘ J)
    Complex.conjCLE.toLinearMap q

/-- This is only the two open-half data, with value zero elsewhere. It is NOT
claimed to be the analytic extension across the fixed curves. The collar
construction must replace the seam values before that claim can be made. -/
def s31qr_twoHalfData (q : F.X.carrier → ℂ → ℂ) : Xd.carrier → ℂ → ℂ :=
  s31qr_positiveData F hd q + s31qr_mirrorData F hd q

theorem s31qr_positive_family [IsManifold 𝓘(ℂ) ω S]
    (q : F.X.carrier → ℂ → ℂ) : IsDiffFamily 2 0 (s31qr_positiveData F hd q) :=
  s31qr_holomorphic_transport_family _ _ (fun _ hp => s31qr_halfReturn_holomorphic F hd hp) q

/-- Both the mirror geometry and its tensor transformation are derived from hd. -/
theorem s31qr_mirror_family [IsManifold 𝓘(ℂ) ω S]
    (q : F.X.carrier → ℂ → ℂ) : IsDiffFamily 2 0 (s31qr_mirrorData F hd q) := by
  have hsets : range (J ∘ ιd) = J ⁻¹' range ιd := by
    ext p
    exact (s31qr_mirror_membership F hd p).symm
  change IsDiffFamily 2 0 (s31qr_transportOn (range (J ∘ ιd))
    (s31qr_halfReturn F hd ∘ J) Complex.conjCLE.toLinearMap q)
  rw [hsets]
  exact s31qr_antiholomorphic_transport_family _ _
    (fun _ hp => s31qr_halfReturn_holomorphic F hd hp) J hd.involution q

/-- The guarded two-half data already have the global tensor transformation law.
This says nothing about regularity across the zero-filled seam. -/
theorem s31qr_twoHalf_family [IsManifold 𝓘(ℂ) ω S]
    (q : F.X.carrier → ℂ → ℂ) : IsDiffFamily 2 0 (s31qr_twoHalfData F hd q) := by
  exact (diffFamilySubmodule Xd.carrier 2 0).add_mem
    (s31qr_positive_family F hd q) (s31qr_mirror_family F hd q)

theorem s31qr_mirror_off_positive (q : F.X.carrier → ℂ → ℂ)
    (x : Xd.carrier) (z : ℂ) (hz : (chartAt ℂ x).symm z ∈ range ιd) :
    s31qr_mirrorData F hd q x z = 0 := by
  apply s31qr_transport_off_piece
  exact fun hm => Set.disjoint_left.1 hd.disjoint hz hm

theorem s31qr_positive_off_mirror (q : F.X.carrier → ℂ → ℂ)
    (x : Xd.carrier) (z : ℂ) (hz : (chartAt ℂ x).symm z ∈ range (J ∘ ιd)) :
    s31qr_positiveData F hd q x z = 0 := by
  apply s31qr_transport_off_piece
  exact fun hp => Set.disjoint_left.1 hd.disjoint hp hz

theorem s31qr_twoHalf_on_positive (q : F.X.carrier → ℂ → ℂ)
    (x : Xd.carrier) (z : ℂ) (hz : (chartAt ℂ x).symm z ∈ range ιd) :
    s31qr_twoHalfData F hd q x z = s31qr_positiveData F hd q x z := by
  change s31qr_positiveData F hd q x z + s31qr_mirrorData F hd q x z = _
  rw [s31qr_mirror_off_positive F hd q x z hz, add_zero]

theorem s31qr_twoHalf_on_mirror (q : F.X.carrier → ℂ → ℂ)
    (x : Xd.carrier) (z : ℂ) (hz : (chartAt ℂ x).symm z ∈ range (J ∘ ιd)) :
    s31qr_twoHalfData F hd q x z = s31qr_mirrorData F hd q x z := by
  change s31qr_positiveData F hd q x z + s31qr_mirrorData F hd q x z = _
  rw [s31qr_positive_off_mirror F hd q x z hz, zero_add]

theorem s31qr_twoHalf_add (q r : F.X.carrier → ℂ → ℂ) :
    s31qr_twoHalfData F hd (q + r) = s31qr_twoHalfData F hd q + s31qr_twoHalfData F hd r := by
  simp only [s31qr_twoHalfData, s31qr_positiveData, s31qr_mirrorData, s31qr_transport_add]
  abel

theorem s31qr_twoHalf_real_smul (c : ℝ) (q : F.X.carrier → ℂ → ℂ) :
    s31qr_twoHalfData F hd (c • q) = c • s31qr_twoHalfData F hd q := by
  simp only [s31qr_twoHalfData, s31qr_positiveData, s31qr_mirrorData,
    s31qr_transport_real_smul, smul_add]

/-- An explicitly constructed real-linear map on the two given open halves. -/
theorem s31qr_twoHalf_linear :
    ∃ T : (F.X.carrier → ℂ → ℂ) →ₗ[ℝ] (Xd.carrier → ℂ → ℂ),
      ∀ q, T q = s31qr_twoHalfData F hd q := by
  exact ⟨{ toFun := s31qr_twoHalfData F hd
           map_add' := s31qr_twoHalf_add F hd
           map_smul' := s31qr_twoHalf_real_smul F hd }, fun _ => rfl⟩

end DoubleHalves
end LiZhongQC
