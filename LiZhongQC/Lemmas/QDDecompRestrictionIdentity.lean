import LiZhongQC.Lemmas.QDReflectionAfterHalves
import LiZhongQC.Lemmas.QDReflectionPuncturePoles
import LiZhongQC.Lemmas.QDReflectionPunctureSeam
import LiZhongQC.Lemmas.QDDecompPuncturePole
import LiZhongQC.Lemmas.QDDecompExtFixed
open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- On the positive half, the transport to `Fd.X` of the seam-filled pull-back of `Q` is `Q` itself: the three
transports (`G`, the half return and `E⁻¹`) compose to the chart transition of `Fd.X`. -/
theorem s31qd_pos_agree {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    [IsManifold 𝓘(ℂ) ω S] [Nonempty S]
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {gd nd : ℕ} (Fd : FiniteTypeStructure (puncturedOpens Pd) gd nd 0)
    (E : Xd.carrier ≃ₜ Fd.X.carrier) (hE : IsBiholomorphic (E : Xd.carrier → Fd.X.carrier))
    {Q : Fd.X.carrier → ℂ → ℂ} (hQ : IsDiffFamily 2 0 Q) {q : F.X.carrier → ℂ → ℂ}
    (hqd : IsDiffFamily 2 0 q)
    (hq : ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range F.ι →
        q x z = s31qr_transportOn (range F.ι)
          (fun y : F.X.carrier => E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm y)))
          (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x z)
    {T : Xd.carrier → ℂ → ℂ} (hT : IsDiffFamily 2 0 T)
    (hTpos : ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range ιd →
        T x z = s31qr_positiveData F hd q x z)
    (x : Fd.X.carrier) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (hp : E.symm ((chartAt ℂ x).symm z) ∈ range ιd) :
    s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) T x z = Q x z := by
  classical
  obtain ⟨s, hs⟩ := hp
  set y : Fd.X.carrier := (chartAt ℂ x).symm z with hy
  set p : Xd.carrier := E.symm y with hpdef
  have hps : ιd s = p := hs
  set b : F.X.carrier := F.ι s with hbdef
  have hρs : (F.embedding.toOpenPartialHomeomorph F.ι).symm (F.ι s) = s :=
    F.embedding.toOpenPartialHomeomorph_left_inv F.ι
  have hhr : s31qr_halfReturn F hd p = b := by
    rw [← hps]
    exact s31qr_halfReturn_image F hd s
  let G : F.X.carrier → Fd.X.carrier := fun y' =>
    E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm y'))
  have hGb : G b = y := by
    change E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm (F.ι s))) = y
    rw [hρs, hps, hpdef, E.apply_symm_apply]
  have hHE : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) E.symm y := hE.homeomorph_symm.1 y
  have hHalf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (s31qr_halfReturn F hd) p :=
    s31qr_halfReturn_holomorphic F hd ⟨s, hps⟩
  have hGd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) G b :=
    (hE.1 _).comp _ ((hd.holomorphic _).comp _
      (s31qr_open_embedding_inverse F.embedding F.holomorphic ⟨s, rfl⟩))
  let φ₁ : ℂ → ℂ := fun w => chartAt ℂ p (E.symm ((chartAt ℂ x).symm w))
  let φ₂ : ℂ → ℂ := fun u => chartAt ℂ b (s31qr_halfReturn F hd ((chartAt ℂ p).symm u))
  let φ₃ : ℂ → ℂ := fun v => chartAt ℂ y (G ((chartAt ℂ b).symm v))
  have hpm : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have hleft : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hbm : chartAt ℂ b b ∈ (chartAt ℂ b).target := (chartAt ℂ b).map_source (mem_chart_source ℂ b)
  have hleftb : (chartAt ℂ b).symm (chartAt ℂ b b) = b := (chartAt ℂ b).left_inv (mem_chart_source ℂ b)
  have hsrc1 : E.symm ((chartAt ℂ x).symm z) ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
  have hsrc2 : s31qr_halfReturn F hd ((chartAt ℂ p).symm (chartAt ℂ p p)) ∈ (chartAt ℂ b).source := by
    rw [hleft, hhr]
    exact mem_chart_source ℂ b
  have hsrc3 : G ((chartAt ℂ b).symm (chartAt ℂ b b)) ∈ (chartAt ℂ y).source := by
    rw [hleftb, hGb]
    exact mem_chart_source ℂ y
  -- the three coordinate expressions
  have hz1 : s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) T x z =
      T p (chartAt ℂ p p) * deriv φ₁ z ^ 2 :=
    s31qr_transport_local (U := univ) (H := E.symm) hT x p hz (mem_univ _) hsrc1 hHE
  have hT2 : T p (chartAt ℂ p p) = s31qr_positiveData F hd q p (chartAt ℂ p p) :=
    hTpos p _ hpm (by rw [hleft]; exact ⟨s, hps⟩)
  have hpos : s31qr_positiveData F hd q p (chartAt ℂ p p) =
      q b (chartAt ℂ b b) * deriv φ₂ (chartAt ℂ p p) ^ 2 := by
    have h := s31qr_transport_local (U := range ιd) (H := s31qr_halfReturn F hd) hqd p b hpm
      (by rw [hleft]; exact ⟨s, hps⟩) hsrc2 (by rw [hleft]; exact hHalf)
    change s31qr_transportOn (range ιd) (s31qr_halfReturn F hd) (LinearMap.id : ℂ →ₗ[ℝ] ℂ) q p
      (chartAt ℂ p p) = _
    rw [h, hleft, hhr]
  have hq3 : q b (chartAt ℂ b b) = Q y (chartAt ℂ y y) * deriv φ₃ (chartAt ℂ b b) ^ 2 := by
    have hqb := hq b (chartAt ℂ b b) hbm (by rw [hleftb]; exact ⟨s, rfl⟩)
    have h := s31qr_transport_local (U := range F.ι) (H := G) hQ b y hbm
      (by rw [hleftb]; exact ⟨s, rfl⟩) hsrc3 (by rw [hleftb]; exact hGd)
    rw [hqb]
    change s31qr_transportOn (range F.ι) G (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q b (chartAt ℂ b b) = _
    rw [h, hleftb, hGb]
  have hQx : Q x z = Q y (chartAt ℂ y y) * deriv (chartTransition y x) z ^ 2 := by
    have hh := hQ.2 y x z hz (mem_chart_source ℂ y)
    have he : chartTransition y x z = chartAt ℂ y y := rfl
    simpa only [he, zpow_zero, mul_one, zpow_two, pow_two] using hh
  -- the chain rule
  have hd1 : DifferentiableAt ℂ φ₁ z :=
    s31qr_coordinate_differentiable (H := E.symm) x p hz hsrc1 hHE
  have hd2 : DifferentiableAt ℂ φ₂ (chartAt ℂ p p) :=
    s31qr_coordinate_differentiable (H := s31qr_halfReturn F hd) p b hpm hsrc2
      (by rw [hleft]; exact hHalf)
  have hd3 : DifferentiableAt ℂ φ₃ (chartAt ℂ b b) :=
    s31qr_coordinate_differentiable (H := G) b y hbm hsrc3 (by rw [hleftb]; exact hGd)
  have hφ1 : φ₁ z = chartAt ℂ p p := rfl
  have hφ2 : φ₂ (chartAt ℂ p p) = chartAt ℂ b b := by
    change chartAt ℂ b (s31qr_halfReturn F hd ((chartAt ℂ p).symm (chartAt ℂ p p))) = _
    rw [hleft, hhr]
  have hφ3 : φ₃ (chartAt ℂ b b) = chartAt ℂ y y := by
    change chartAt ℂ y (G ((chartAt ℂ b).symm (chartAt ℂ b b))) = _
    rw [hleftb, hGb]
  have hcu : ContinuousAt (fun w => E.symm ((chartAt ℂ x).symm w)) z :=
    E.symm.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz)
  have hev1 : ∀ᶠ w in 𝓝 z, E.symm ((chartAt ℂ x).symm w) ∈ (chartAt ℂ p).source ∩ range ιd := by
    apply hcu.preimage_mem_nhds
    exact Filter.inter_mem ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))
      (hd.embedding.isOpenMap.isOpen_range.mem_nhds ⟨s, hps⟩)
  have hcv : ContinuousAt (fun w => s31qr_halfReturn F hd (E.symm ((chartAt ℂ x).symm w))) z :=
    ContinuousAt.comp (g := s31qr_halfReturn F hd) (f := fun w => E.symm ((chartAt ℂ x).symm w))
      (x := z) hHalf.continuousAt hcu
  have hev2 : ∀ᶠ w in 𝓝 z,
      s31qr_halfReturn F hd (E.symm ((chartAt ℂ x).symm w)) ∈ (chartAt ℂ b).source := by
    apply hcv.preimage_mem_nhds
    change (chartAt ℂ b).source ∈ 𝓝 (s31qr_halfReturn F hd (E.symm ((chartAt ℂ x).symm z)))
    rw [show E.symm ((chartAt ℂ x).symm z) = p from rfl, hhr]
    exact (chartAt ℂ b).open_source.mem_nhds (mem_chart_source ℂ b)
  have hev : (fun w => φ₃ (φ₂ (φ₁ w))) =ᶠ[𝓝 z] chartTransition y x := by
    filter_upwards [hev1, hev2] with w hw1 hw2
    have h1 : (chartAt ℂ p).symm (φ₁ w) = E.symm ((chartAt ℂ x).symm w) :=
      (chartAt ℂ p).left_inv hw1.1
    have h2 : (chartAt ℂ b).symm (φ₂ (φ₁ w)) =
        s31qr_halfReturn F hd (E.symm ((chartAt ℂ x).symm w)) := by
      change (chartAt ℂ b).symm (chartAt ℂ b (s31qr_halfReturn F hd ((chartAt ℂ p).symm (φ₁ w)))) = _
      rw [h1]
      exact (chartAt ℂ b).left_inv hw2
    have h3 : G (s31qr_halfReturn F hd (E.symm ((chartAt ℂ x).symm w))) = (chartAt ℂ x).symm w := by
      obtain ⟨s', hs'⟩ := hw1.2
      rw [← hs', s31qr_halfReturn_image F hd s']
      change E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm (F.ι s'))) = _
      rw [F.embedding.toOpenPartialHomeomorph_left_inv F.ι, hs', E.apply_symm_apply]
    change chartAt ℂ y (G ((chartAt ℂ b).symm (φ₂ (φ₁ w)))) = chartAt ℂ y ((chartAt ℂ x).symm w)
    rw [h2, h3]
  have hd2' : DifferentiableAt ℂ φ₂ (φ₁ z) := by rw [hφ1]; exact hd2
  have hd3' : DifferentiableAt ℂ φ₃ (φ₂ (φ₁ z)) := by rw [hφ1, hφ2]; exact hd3
  have hchain : deriv (chartTransition y x) z =
      deriv φ₃ (chartAt ℂ b b) * (deriv φ₂ (chartAt ℂ p p) * deriv φ₁ z) := by
    rw [← hev.deriv_eq]
    have h21 : deriv (φ₂ ∘ φ₁) z = deriv φ₂ (φ₁ z) * deriv φ₁ z := deriv_comp z hd2' hd1
    have hd21 : DifferentiableAt ℂ (φ₂ ∘ φ₁) z := hd2'.comp z hd1
    have h321 : deriv (φ₃ ∘ (φ₂ ∘ φ₁)) z = deriv φ₃ ((φ₂ ∘ φ₁) z) * deriv (φ₂ ∘ φ₁) z :=
      deriv_comp z hd3' hd21
    change deriv (φ₃ ∘ (φ₂ ∘ φ₁)) z = _
    rw [h321, h21]
    simp only [Function.comp, hφ1, hφ2]
  rw [hz1, hT2, hpos, hq3, hQx, hchain]
  ring

/-- A transport depends on the family only through the value at the chart centre of the image point. -/
theorem s31qd_transport_congr_center {A B : Type*} [TopologicalSpace A] [ChartedSpace ℂ A]
    [TopologicalSpace B] [ChartedSpace ℂ B] (U : Set B) (H : B → A) (C : ℂ →ₗ[ℝ] ℂ)
    (q r : A → ℂ → ℂ) (x : B) (z : ℂ)
    (h : z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ U →
      q (H ((chartAt ℂ x).symm z)) (chartAt ℂ (H ((chartAt ℂ x).symm z)) (H ((chartAt ℂ x).symm z))) =
      r (H ((chartAt ℂ x).symm z)) (chartAt ℂ (H ((chartAt ℂ x).symm z)) (H ((chartAt ℂ x).symm z)))) :
    s31qr_transportOn U H C q x z = s31qr_transportOn U H C r x z := by
  classical
  by_cases hh : z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ U
  · simp only [s31qr_transportOn, hh, and_self, if_true]
    rw [h hh]
  · simp only [s31qr_transportOn, hh, if_false]

/-- (b) The final identity of the restriction: the boundary extension `q` of the pull-back of a
`T`-fixed admissible `Q` of `Fd` is an admissible differential of `F` whose seam-filled extension
transports back to `Q`. -/
theorem s31qd_restriction_from_extension {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {gd nd : ℕ} (Fd : FiniteTypeStructure (puncturedOpens Pd) gd nd 0)
    (E : Xd.carrier ≃ₜ Fd.X.carrier) (hE : IsBiholomorphic (E : Xd.carrier → Fd.X.carrier))
    (hP : ∀ p : Xd.carrier, p ∈ Pd ↔ E p ∈ Fd.P)
    (T0 : admissibleQDSpace F →ₗ[ℝ] (Xd.carrier → ℂ → ℂ))
    (hT0 : ∀ q : admissibleQDSpace F,
      IsDiffFamily 2 0 (T0 q) ∧
      (∀ a : Xd.carrier, DifferentiableOn ℂ (T0 q a)
        ((chartAt ℂ a).target ∩ (chartAt ℂ a).symm ⁻¹' (↑Pd : Set Xd.carrier)ᶜ)) ∧
      (∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range ιd →
        T0 q x z = s31qr_positiveData F hd (q : F.X.carrier → ℂ → ℂ) x z) ∧
      (∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range (J ∘ ιd) →
        T0 q x z = s31qr_mirrorData F hd (q : F.X.carrier → ℂ → ℂ) x z) ∧
      (∀ a : Xd.carrier, ∀ p ∈ Pd, p ∈ (chartAt ℂ a).source → T0 q a (chartAt ℂ a p) = 0))
    {Q : Fd.X.carrier → ℂ → ℂ} (hQ : IsAdmissibleQD Fd Q)
    (hfix : s31qr_transportOn univ (fun y : Fd.X.carrier => E (J (E.symm y)))
      Complex.conjCLE.toLinearMap Q = Q)
    (hext : ∃ q : F.X.carrier → ℂ → ℂ, IsDiffFamily 2 0 q ∧
      (∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range F.ι →
        q x z = s31qr_transportOn (range F.ι)
          (fun y : F.X.carrier => E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm y)))
          (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x z) ∧
      (∀ (x : F.X.carrier) (j : Fin m), ∀ z ∈ (chartAt ℂ x).target,
        (chartAt ℂ x).symm z ∈ interior (F.D j) → q x z = 0) ∧
      (∀ (x : F.X.carrier), ∀ p ∈ F.P, p ∈ (chartAt ℂ x).source → q x (chartAt ℂ x p) = 0) ∧
      (∀ (x : F.X.carrier) (j : Fin m),
        ContinuousOn (q x) ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (range F.ι ∪ frontier (F.D j)))) ∧
      (∀ (x : F.X.carrier) (j : Fin m) (c : ℝ → ℂ) (a b : ℝ), ContDiffOn ℝ 1 c (Icc a b) →
        c '' Icc a b ⊆ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' frontier (F.D j) →
        ∀ t ∈ Ioo a b, (q x (c t) * deriv c t ^ 2).im = 0)) :
    ∃ q : admissibleQDSpace F,
      s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) (T0 q) = Q := by
  classical
  haveI : Nonempty S := inferInstance
  obtain ⟨q, hqd, hqeq, hqint, hqP, hqcont, hqreal⟩ := hext
  let G : F.X.carrier → Fd.X.carrier := fun y' =>
    E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm y'))
  have hGd : ∀ b ∈ range F.ι, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) G b := fun b hb =>
    (hE.1 _).comp _ ((hd.holomorphic _).comp _
      (s31qr_open_embedding_inverse F.embedding F.holomorphic hb))
  have hRangeFd : range Fd.ι = (↑Fd.P : Set Fd.X.carrier)ᶜ := by simpa using Fd.range_ι
  have hqadm : IsAdmissibleQD F q := by
    refine ⟨hqd, ?_, ?_, hqcont, hqreal, hqint⟩
    · intro x
      have himage : MapsTo G (range F.ι) (range Fd.ι) := by
        rintro _ ⟨s, rfl⟩
        rw [hRangeFd]
        intro hmem
        have hGs : G (F.ι s) = E (ιd s) := by
          change E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm (F.ι s))) = _
          rw [F.embedding.toOpenPartialHomeomorph_left_inv F.ι]
        rw [hGs] at hmem
        exact (s31qi_Pd_off_halves F hm hd _ ((hP _).2 (Finset.mem_coe.1 hmem))).1 ⟨s, rfl⟩
      have h := s31qr_transport_holomorphic (U := range F.ι)
        F.embedding.isOpenMap.isOpen_range Fd.embedding.isOpenMap.isOpen_range hGd himage
        hQ.1 hQ.2.1 x
      exact h.congr (fun z hz => hqeq x z hz.1 hz.2)
    · intro x p hp hs
      exact ⟨hqP x p hp hs, s31qd_puncture_pole F hd Fd E hE hP hQ hqd hqeq hqP x p hp hs⟩
  let q' : admissibleQDSpace F := ⟨q, hqadm⟩
  refine ⟨q', ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hT0 q'
  set R : Fd.X.carrier → ℂ → ℂ :=
    s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) (T0 q') with hR
  have hRadm : IsAdmissibleQD Fd R := by
    refine s31qr_fd_transport_admissible Xd Pd Fd E hE hP h1 h2 ?_
    intro a p hp hs
    exact ⟨h5 a p hp hs, s31qi_puncture_poles F hm hd q' (T0 q') h3 h4 a p hp hs⟩
  have hRfix : s31qr_transportOn univ (fun y : Fd.X.carrier => E (J (E.symm y)))
      Complex.conjCLE.toLinearMap R = R :=
    s31qd_ext_fixed F hm hd Fd E hE hP q' h1 h2 h3 h4 h5
  apply s31qr_admissible_eq_of_range Fd hRadm hQ
  intro x z hz hrng
  -- agreement on the two halves
  have hPos : ∀ x z, z ∈ (chartAt ℂ x).target → E.symm ((chartAt ℂ x).symm z) ∈ range ιd →
      R x z = Q x z := fun x z hz hp =>
    s31qd_pos_agree F hd Fd E hE hQ.1 hqd hqeq h1 h3 x hz hp
  have hMir : ∀ x z, z ∈ (chartAt ℂ x).target →
      E.symm ((chartAt ℂ x).symm z) ∈ range (J ∘ ιd) → R x z = Q x z := by
    intro x z hz hp
    obtain ⟨s, hs⟩ := hp
    have hw : E.symm (E (J (E.symm ((chartAt ℂ x).symm z)))) = ιd s := by
      rw [E.symm_apply_apply, ← hs]
      exact hd.involution.1 _
    have hwt : chartAt ℂ (E (J (E.symm ((chartAt ℂ x).symm z))))
        (E (J (E.symm ((chartAt ℂ x).symm z)))) ∈
        (chartAt ℂ (E (J (E.symm ((chartAt ℂ x).symm z))))).target :=
      (chartAt ℂ _).map_source (mem_chart_source ℂ _)
    have hc := hPos (E (J (E.symm ((chartAt ℂ x).symm z)))) _ hwt (by
      rw [(chartAt ℂ _).left_inv (mem_chart_source ℂ _), hw]
      exact ⟨s, rfl⟩)
    have e1 := congrFun (congrFun hRfix x) z
    have e2 := congrFun (congrFun hfix x) z
    have e3 := s31qd_transport_congr_center (univ : Set Fd.X.carrier)
      (fun y : Fd.X.carrier => E (J (E.symm y))) Complex.conjCLE.toLinearMap R Q x z
      (fun _ => hc)
    rw [← e1, ← e2]
    exact e3.symm.symm
  have hA : ∀ x z, z ∈ (chartAt ℂ x).target →
      E.symm ((chartAt ℂ x).symm z) ∈ range ιd ∪ range (J ∘ ιd) → R x z = Q x z := by
    intro x z hz hp
    rcases hp with hp | hp
    · exact hPos x z hz hp
    · exact hMir x z hz hp
  -- density and continuity
  set y : Fd.X.carrier := (chartAt ℂ x).symm z with hy
  have hyP : y ∉ (↑Fd.P : Set Fd.X.carrier) := by
    have h0 := hrng
    rw [hRangeFd] at h0
    exact h0
  set p : Xd.carrier := E.symm y with hp
  have hpPd : p ∉ Pd := by
    intro h
    exact hyP (Finset.mem_coe.2 ((hP p).1 h |> fun h' => by rwa [hp, E.apply_symm_apply] at h'))
  have hpcl : p ∈ closure (range ιd ∪ range (J ∘ ιd)) := by
    have hcov : p ∈ range ιd ∪ range (J ∘ ιd) ∪ {x | J x = x} ∪ (↑Pd : Set Xd.carrier) := by
      rw [hd.cover]; trivial
    rcases hcov with ((h | h) | h) | h
    · exact subset_closure (Or.inl h)
    · exact subset_closure (Or.inr h)
    · have hfr : p ∈ frontier (range ιd) \ ↑Pd := by rw [← hd.fixed_curves]; exact h
      exact closure_mono subset_union_left (frontier_subset_closure hfr.1)
    · exact absurd (Finset.mem_coe.1 h) hpPd
  have hycl : y ∈ closure (E '' (range ιd ∪ range (J ∘ ιd))) := by
    have := image_closure_subset_closure_image E.continuous ⟨p, hpcl, rfl⟩
    rwa [hp, E.apply_symm_apply] at this
  have hys : y ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  have hycl' : y ∈ closure ((chartAt ℂ x).source ∩ E '' (range ιd ∪ range (J ∘ ιd))) :=
    (chartAt ℂ x).open_source.inter_closure ⟨hys, hycl⟩
  have hzcl : z ∈ closure ((chartAt ℂ x) '' ((chartAt ℂ x).source ∩
      E '' (range ιd ∪ range (J ∘ ιd)))) := by
    have := mem_closure_image ((chartAt ℂ x).continuousAt hys) hycl'
    rwa [show chartAt ℂ x y = z from (chartAt ℂ x).right_inv hz] at this
  have hWo : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' range Fd.ι) :=
    (chartAt ℂ x).isOpen_inter_preimage_symm Fd.embedding.isOpenMap.isOpen_range
  have hzW : z ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' range Fd.ι := ⟨hz, hrng⟩
  have hDc : ContinuousAt (fun w => R x w - Q x w) z :=
    (((hRadm.2.1 x).differentiableAt (hWo.mem_nhds hzW)).continuousAt).sub
      (((hQ.2.1 x).differentiableAt (hWo.mem_nhds hzW)).continuousAt)
  have hmem := mem_closure_image hDc hzcl
  have hsub : (fun w => R x w - Q x w) '' ((chartAt ℂ x) '' ((chartAt ℂ x).source ∩
      E '' (range ιd ∪ range (J ∘ ιd)))) ⊆ {0} := by
    rintro _ ⟨_, ⟨y', ⟨hy's, a, ha, rfl⟩, rfl⟩, rfl⟩
    have hwt : chartAt ℂ x (E a) ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hy's
    have := hA x _ hwt (by rw [(chartAt ℂ x).left_inv hy's, E.symm_apply_apply]; exact ha)
    simp [this]
  have h0 := closure_mono hsub hmem
  rw [isClosed_singleton.closure_eq] at h0
  exact sub_eq_zero.1 h0

end LiZhongQC
