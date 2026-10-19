import LiZhongQC.Lemmas.QDReflectionAfterHalves
import LiZhongQC.Lemmas.QDReflectionPuncturePoles
import LiZhongQC.Lemmas.QDSeamLocal
/-!
# Seam filling, preparation (`s31q2_`, Round78 QD lane, piece C2)

Facts used by the global gluing of `s31qi_seam_fill` that do not depend on the local reflection (C1):
`conj` is nowhere complex differentiable, the fixed set of an anticonformal involution has empty interior, the two
halves of a Schottky double are dense in every chart, and the mirror data are holomorphic on the mirror half.
-/

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u v

/-- Complex conjugation is not complex differentiable at any point: along real directions its difference
quotient is `1`, along imaginary directions `-1`. -/
theorem s31q2_not_differentiableAt_conj (z : ℂ) : ¬ DifferentiableAt ℂ (fun w : ℂ => conj w) z := by
  intro h
  set c := deriv (fun w : ℂ => conj w) z
  have hd : HasDerivAt (fun w : ℂ => conj w) c z := h.hasDerivAt
  -- real direction
  have h1 : HasDerivAt (fun w : ℂ => conj (z + w)) c 0 := by
    apply HasDerivAt.comp_const_add
    simpa using hd
  have h1r : HasDerivAt (fun t : ℝ => conj (z + (t : ℂ))) c 0 := by
    have := h1.comp_ofReal (z := (0 : ℝ))
    simpa using this
  have h1' : HasDerivAt (fun t : ℝ => conj (z + (t : ℂ))) 1 0 := by
    have e : (fun t : ℝ => conj (z + (t : ℂ))) = fun t : ℝ => conj z + (t : ℂ) := by
      funext t; simp [map_add, Complex.conj_ofReal]
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_add (conj z)
  have hc1 : c = 1 := h1r.unique h1'
  -- imaginary direction
  have h2 : HasDerivAt (fun w : ℂ => conj (z + I * w)) (c * I) 0 := by
    have hlin : HasDerivAt (fun w : ℂ => z + I * w) I 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul I).const_add z
    have hd' : HasDerivAt (fun w : ℂ => conj w) c (z + I * 0) := by simpa using hd
    exact HasDerivAt.comp (0 : ℂ) hd' hlin
  have h2r : HasDerivAt (fun t : ℝ => conj (z + I * (t : ℂ))) (c * I) 0 := by
    have := h2.comp_ofReal (z := (0 : ℝ))
    simpa using this
  have h2' : HasDerivAt (fun t : ℝ => conj (z + I * (t : ℂ))) (-I) 0 := by
    have e : (fun t : ℝ => conj (z + I * (t : ℂ))) = fun t : ℝ => conj z + (-I) * (t : ℂ) := by
      funext t; simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [e]
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (-I)).const_add (conj z)
  have hc2 : c * I = -I := h2r.unique h2'
  rw [hc1] at hc2
  have : (2 : ℂ) * I = 0 := by linear_combination hc2
  simp at this

section Involution
variable {B : Type v} [TopologicalSpace B] [ChartedSpace ℂ B]

/-- The fixed set of an anticonformal involution has empty interior: on an open set of fixed points the local
expression would be the identity, and its conjugate `conj` would be complex differentiable. -/
theorem s31q2_fixed_interior_empty (J : B ≃ₜ B) (hJ : IsAnticonformalInvolution J) :
    interior {r : B | J r = r} = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro p hp
  set S0 : Set B := {r : B | J r = r} with hS0
  have hU : S0 ∈ 𝓝 p := mem_interior_iff_mem_nhds.1 hp
  have hpS : p ∈ S0 := interior_subset hp
  have hpp : J p = p := hpS
  let c := chartAt ℂ p
  have hps : p ∈ c.source := mem_chart_source ℂ p
  have hdom : localMapDomain J p ∈ 𝓝 (c p) :=
    (s23_localMapDomain_isOpen J.continuous p).mem_nhds (s23_h_center J p).1
  have hdiff : DifferentiableAt ℂ (fun w => conj (localMapExpr J p w)) (c p) :=
    (hJ.2 p).differentiableAt hdom
  have hS : S0 ∩ c.source ∈ 𝓝 (c.symm (c p)) := by
    rw [c.left_inv hps]
    exact Filter.inter_mem hU (c.open_source.mem_nhds hps)
  have hnear : c.symm ⁻¹' (S0 ∩ c.source) ∈ 𝓝 (c p) :=
    (c.continuousAt_symm (c.map_source hps)).preimage_mem_nhds hS
  have hT : c.target ∈ 𝓝 (c p) := c.open_target.mem_nhds (c.map_source hps)
  have heq : (fun w => conj (localMapExpr J p w)) =ᶠ[𝓝 (c p)] fun w => conj w := by
    filter_upwards [hnear, hT] with w hw hwT
    change conj (chartAt ℂ (J p) (J (c.symm w))) = conj w
    have hJw : J (c.symm w) = c.symm w := hw.1
    rw [hpp, hJw]
    exact congrArg conj (c.right_inv hwT)
  exact s31q2_not_differentiableAt_conj (c p) (hdiff.congr_of_eventuallyEq heq.symm)

end Involution

section DoubleHalves
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [Nonempty S] {g n m : ℕ}
  (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
  {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
  (hd : IsSchottkyDouble F Xd J ιd Pd)

include F hd in
/-- **Density of the halves.**  In every chart, every point of the chart target is a limit of points whose
chart preimage lies in `ιd(S)` or in its mirror image: the complement of the two halves is the fixed set of `J`
(empty interior) together with the finite set `Pd`. -/
theorem s31q2_halves_dense (x : Xd.carrier) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) :
    z ∈ closure {w : ℂ | w ∈ (chartAt ℂ x).target ∧
      (chartAt ℂ x).symm w ∈ range ιd ∪ range (J ∘ ιd)} := by
  rw [_root_.mem_closure_iff]
  intro o ho hzo
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  set c := chartAt ℂ x
  -- the open set `W` of the chart preimage of `o`, minus `Pd`
  have hPc : IsClosed (↑Pd : Set Xd.carrier) := Pd.finite_toSet.isClosed
  set W : Set Xd.carrier := (c.source ∩ c ⁻¹' o) \ ↑Pd with hW
  have hWo : IsOpen W := (c.isOpen_inter_preimage ho).sdiff hPc
  have hWfix : W ⊆ {p | J p = p} := by
    rintro p ⟨⟨hps, hpo⟩, hpP⟩
    have hhalf : p ∉ range ιd ∪ range (J ∘ ιd) := by
      intro hp
      have : c p ∈ o ∩ {w : ℂ | w ∈ c.target ∧ c.symm w ∈ range ιd ∪ range (J ∘ ιd)} :=
        ⟨hpo, c.map_source hps, by rw [c.left_inv hps]; exact hp⟩
      rw [hne] at this
      exact this
    rcases s31qr_outside_halves F hd (fun h => hhalf (Or.inl h)) (fun h => hhalf (Or.inr h)) with h | h
    · exact h
    · exact absurd h hpP
  -- `W` is nonempty: `o ∩ target` is an infinite set, and `c.symm` is injective on it
  have hinf : (o ∩ c.target).Infinite := by
    have hopen : IsOpen (o ∩ c.target) := ho.inter c.open_target
    exact infinite_of_mem_nhds z (hopen.mem_nhds ⟨hzo, hz⟩)
  have himg : (c.symm '' (o ∩ c.target)).Infinite :=
    hinf.image (c.symm.injOn.mono inter_subset_right)
  obtain ⟨p, hp, hpP⟩ := (himg.sdiff Pd.finite_toSet).nonempty
  obtain ⟨w, ⟨hwo, hwt⟩, rfl⟩ := hp
  have hpW : c.symm w ∈ W := ⟨⟨c.map_target hwt, by simpa [c.right_inv hwt] using hwo⟩, hpP⟩
  have hint : c.symm w ∈ interior {p | J p = p} := interior_mono hWfix (by rw [hWo.interior_eq]; exact hpW)
  rw [s31q2_fixed_interior_empty J hd.involution] at hint
  exact hint

end DoubleHalves

section MirrorTransport
variable {A : Type u} {B : Type v} [TopologicalSpace A] [ChartedSpace ℂ A]
  [TopologicalSpace B] [ChartedSpace ℂ B]
  [IsManifold 𝓘(ℂ) ω A] [IsManifold 𝓘(ℂ) ω B]

/-- The conjugated return coordinate in an arbitrary fixed target chart `a` is holomorphic. -/
theorem s31q2_return_after_involution_chart (J : B ≃ₜ B) (hJ : IsAnticonformalInvolution J) (H : B → A)
    (x : B) (a : A) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (ha : H (J ((chartAt ℂ x).symm z)) ∈ (chartAt ℂ a).source)
    (hH : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H (J ((chartAt ℂ x).symm z))) :
    DifferentiableAt ℂ (fun w => conj (chartAt ℂ a (H (J ((chartAt ℂ x).symm w))))) z := by
  let t := J ((chartAt ℂ x).symm z)
  let ψ : ℂ → ℂ := fun v => chartAt ℂ a (H ((chartAt ℂ t).symm v))
  let η : ℂ → ℂ := fun w => conj (chartAt ℂ t (J ((chartAt ℂ x).symm w)))
  have hψ : DifferentiableAt ℂ ψ (chartAt ℂ t t) :=
    ((s23_mdifferentiableAt_iff (mem_chart_source ℂ t) ha).1 hH).2
  have hη : DifferentiableAt ℂ η z := s31qr_involution_coordinate J hJ x hz
  have hηz : η z = conj (chartAt ℂ t t) := rfl
  have hψc : DifferentiableAt ℂ (conj ∘ ψ ∘ conj) (η z) := by
    rw [hηz]
    have := hψ.conj_conj
    simpa using this
  have hd := hψc.comp z hη
  apply hd.congr_of_eventuallyEq
  have ht : ContinuousAt (fun w => J ((chartAt ℂ x).symm w)) z :=
    J.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz)
  filter_upwards [ht.preimage_mem_nhds ((chartAt ℂ t).open_source.mem_nhds
    (mem_chart_source ℂ t))] with w hw
  change conj (chartAt ℂ a (H (J ((chartAt ℂ x).symm w)))) =
    conj (chartAt ℂ a (H ((chartAt ℂ t).symm
      (conj (conj (chartAt ℂ t (J ((chartAt ℂ x).symm w))))))))
  rw [Complex.conj_conj, (chartAt ℂ t).left_inv hw]

/-- The conjugate transport in a fixed target chart `a`: the canonical-point formula of `s31qr_transportOn`
with `C = conj` agrees with the formula read in the chart `a`. -/
theorem s31q2_conj_transport_local {U : Set B} {H : B → A} {q : A → ℂ → ℂ} (hq : IsDiffFamily 2 0 q)
    (J : B ≃ₜ B) (hJ : IsAnticonformalInvolution J) (x : B) (a : A)
    {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) (hp : (chartAt ℂ x).symm z ∈ U)
    (ha : H (J ((chartAt ℂ x).symm z)) ∈ (chartAt ℂ a).source)
    (hH : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H (J ((chartAt ℂ x).symm z))) :
    s31qr_transportOn U (H ∘ J) Complex.conjCLE.toLinearMap q x z =
      conj (q a (chartAt ℂ a (H (J ((chartAt ℂ x).symm z))))) *
        deriv (fun w => conj (chartAt ℂ a (H (J ((chartAt ℂ x).symm w))))) z ^ 2 := by
  let b := H (J ((chartAt ℂ x).symm z))
  have hbt : chartAt ℂ b b ∈ (chartAt ℂ b).target :=
    (chartAt ℂ b).map_source (mem_chart_source ℂ b)
  have hbi : (chartAt ℂ b).symm (chartAt ℂ b b) = b :=
    (chartAt ℂ b).left_inv (mem_chart_source ℂ b)
  have hl : q b (chartAt ℂ b b) =
      q a (chartAt ℂ a b) * deriv (chartTransition a b) (chartAt ℂ b b) ^ 2 := by
    have hh := hq.2 a b (chartAt ℂ b b) hbt (by rw [hbi]; exact ha)
    have he : chartTransition a b (chartAt ℂ b b) = chartAt ℂ a b := by
      change chartAt ℂ a ((chartAt ℂ b).symm (chartAt ℂ b b)) = _
      rw [hbi]
    simpa only [he, zpow_zero, mul_one, zpow_two, pow_two] using hh
  have hbD := s31q2_return_after_involution_chart J hJ H x b hz (mem_chart_source ℂ b) hH
  have hτD := s23_transition_differentiableAt a b hbt (by rw [hbi]; exact ha)
  have hJc : ContinuousAt (fun w => J ((chartAt ℂ x).symm w)) z :=
    J.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz)
  have hc : ContinuousAt (fun w => H (J ((chartAt ℂ x).symm w))) z :=
    ContinuousAt.comp (g := H) hH.continuousAt hJc
  have he :
      (fun w => conj (chartAt ℂ a (H (J ((chartAt ℂ x).symm w))))) =ᶠ[𝓝 z]
      (conj ∘ chartTransition a b ∘ conj) ∘
        (fun w => conj (chartAt ℂ b (H (J ((chartAt ℂ x).symm w))))) := by
    filter_upwards [hc.preimage_mem_nhds ((chartAt ℂ b).open_source.mem_nhds
      (mem_chart_source ℂ b))] with w hw
    change conj (chartAt ℂ a (H (J ((chartAt ℂ x).symm w)))) =
      conj (chartAt ℂ a ((chartAt ℂ b).symm (conj (conj (chartAt ℂ b (H (J ((chartAt ℂ x).symm w))))))))
    rw [Complex.conj_conj, (chartAt ℂ b).left_inv hw]
  have hτc : HasDerivAt (conj ∘ chartTransition a b ∘ conj)
      (conj (deriv (chartTransition a b) (chartAt ℂ b b))) (conj (chartAt ℂ b b)) :=
    hτD.hasDerivAt.conj_conj
  have hd : deriv (fun w => conj (chartAt ℂ a (H (J ((chartAt ℂ x).symm w))))) z =
      conj (deriv (chartTransition a b) (chartAt ℂ b b)) *
        deriv (fun w => conj (chartAt ℂ b (H (J ((chartAt ℂ x).symm w))))) z := by
    rw [he.deriv_eq]
    exact (hτc.comp z hbD.hasDerivAt).deriv
  classical
  change (if z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ U then
    conj (q b (chartAt ℂ b b)) *
      deriv (fun w => conj (chartAt ℂ b (H (J ((chartAt ℂ x).symm w))))) z ^ 2 else 0) = _
  rw [if_pos ⟨hz, hp⟩, hl, hd]
  simp only [map_mul, map_pow]
  ring

/-- Holomorphy of a conjugate transport on its open piece. -/
theorem s31q2_conj_transport_holomorphic (J : B ≃ₜ B) (hJ : IsAnticonformalInvolution J)
    {U : Set B} (hU : IsOpen U) {V : Set A} (hV : IsOpen V) {H : B → A}
    (hH : ∀ p ∈ J ⁻¹' U, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H (J p))
    (himage : ∀ p ∈ J ⁻¹' U, H (J p) ∈ V) {q : A → ℂ → ℂ} (hq : IsDiffFamily 2 0 q)
    (hqd : ∀ a : A, DifferentiableOn ℂ (q a) ((chartAt ℂ a).target ∩ (chartAt ℂ a).symm ⁻¹' V))
    (x : B) :
    DifferentiableOn ℂ (s31qr_transportOn (J ⁻¹' U) (H ∘ J) Complex.conjCLE.toLinearMap q x)
      ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (J ⁻¹' U)) := by
  intro z hz
  let a := H (J ((chartAt ℂ x).symm z))
  have hJU : IsOpen (J ⁻¹' U) := hU.preimage J.continuous
  have hHc : ContinuousOn (fun p => H (J p)) (J ⁻¹' U) :=
    fun p hp => (hH p hp).continuousAt.comp J.continuous.continuousAt |>.continuousWithinAt
  let W : Set ℂ := (chartAt ℂ x).target ∩
    (chartAt ℂ x).symm ⁻¹' (J ⁻¹' U ∩ (fun p => H (J p)) ⁻¹' (chartAt ℂ a).source)
  have hWo : IsOpen W := (chartAt ℂ x).isOpen_inter_preimage_symm
    (hHc.isOpen_inter_preimage hJU (chartAt ℂ a).open_source)
  have hzW : z ∈ W := ⟨hz.1, hz.2, mem_chart_source ℂ a⟩
  have hTd : DifferentiableOn ℂ
      (fun w => conj (chartAt ℂ a (H (J ((chartAt ℂ x).symm w))))) W := by
    intro w hw
    exact (s31q2_return_after_involution_chart J hJ H x a hw.1 hw.2.2
      (hH _ hw.2.1)).differentiableWithinAt
  have hdd := hTd.deriv hWo
  have haV : (chartAt ℂ a).symm (chartAt ℂ a a) ∈ V := by
    rw [(chartAt ℂ a).left_inv (mem_chart_source ℂ a)]
    exact himage _ hz.2
  have hnb : (chartAt ℂ a).target ∩ (chartAt ℂ a).symm ⁻¹' V ∈ 𝓝 (chartAt ℂ a a) :=
    ((chartAt ℂ a).isOpen_inter_preimage_symm hV).mem_nhds
      ⟨(chartAt ℂ a).map_source (mem_chart_source ℂ a), haV⟩
  have hqAt : DifferentiableAt ℂ (q a) (chartAt ℂ a a) := (hqd a).differentiableAt hnb
  have hqc : DifferentiableAt ℂ (conj ∘ q a ∘ conj)
      (conj (chartAt ℂ a (H (J ((chartAt ℂ x).symm z))))) := by
    have := hqAt.conj_conj
    simpa using this
  have hmodel : DifferentiableAt ℂ
      (fun w => (conj ∘ q a ∘ conj) (conj (chartAt ℂ a (H (J ((chartAt ℂ x).symm w))))) *
        deriv (fun v => conj (chartAt ℂ a (H (J ((chartAt ℂ x).symm v))))) w ^ 2) z :=
    (hqc.comp z (hTd.differentiableAt (hWo.mem_nhds hzW))).mul
      ((hdd.differentiableAt (hWo.mem_nhds hzW)).pow 2)
  have he :
      s31qr_transportOn (J ⁻¹' U) (H ∘ J) Complex.conjCLE.toLinearMap q x =ᶠ[𝓝 z]
      (fun w => (conj ∘ q a ∘ conj) (conj (chartAt ℂ a (H (J ((chartAt ℂ x).symm w))))) *
        deriv (fun v => conj (chartAt ℂ a (H (J ((chartAt ℂ x).symm v))))) w ^ 2) := by
    filter_upwards [hWo.mem_nhds hzW] with w hw
    rw [s31q2_conj_transport_local hq J hJ x a hw.1 hw.2.1 hw.2.2 (hH _ hw.2.1)]
    simp only [Function.comp_apply, Complex.conj_conj]
  exact (hmodel.congr_of_eventuallyEq he).differentiableWithinAt

end MirrorTransport

/-- **Mirror holomorphy.**  The actual mirror data of an admissible `q` are holomorphic on the mirror half, in
every chart of the double. -/
theorem s31q2_mirror_holomorphic
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [Nonempty S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd)
    {q : F.X.carrier → ℂ → ℂ} (hq : IsAdmissibleQD F q) (x : Xd.carrier) :
    DifferentiableOn ℂ (s31qr_mirrorData F hd q x)
      ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' range (J ∘ ιd)) := by
  have hsets : range (J ∘ ιd) = J ⁻¹' range ιd := by
    ext p
    exact (s31qr_mirror_membership F hd p).symm
  change DifferentiableOn ℂ (s31qr_transportOn (range (J ∘ ιd))
    (s31qr_halfReturn F hd ∘ J) Complex.conjCLE.toLinearMap q x) _
  rw [hsets]
  apply s31q2_conj_transport_holomorphic J hd.involution hd.embedding.isOpenMap.isOpen_range
    F.embedding.isOpenMap.isOpen_range
    (fun p hp => s31qr_halfReturn_holomorphic F hd hp) _ hq.1 hq.2.1
  intro p hp
  obtain ⟨s, hs⟩ := hp
  refine ⟨s, ?_⟩
  change F.ι s = s31qr_halfReturn F hd (J p)
  rw [← hs, s31qr_halfReturn_image]




section SeamFill
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}

/-- The seam germ of C1 gives the limit of the two-half data along the halves at every point of the disc. -/
theorem s31q2_seam_limit [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    (q : admissibleQDSpace F) (x : Xd.carrier) {z₀ : ℂ} (hz₀ : z₀ ∈ (chartAt ℂ x).target)
    (hfix : J ((chartAt ℂ x).symm z₀) = (chartAt ℂ x).symm z₀)
    (hP : (chartAt ℂ x).symm z₀ ∉ Pd) :
    ∃ ε : ℝ, 0 < ε ∧ ball z₀ ε ⊆ (chartAt ℂ x).target ∧
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball z₀ ε) ∧
        (∀ z ∈ ball z₀ ε, ((chartAt ℂ x).symm z ∈ range ιd ∨ (chartAt ℂ x).symm z ∈ range (J ∘ ιd)) →
          H z = s31qr_twoHalfData F hd (q : F.X.carrier → ℂ → ℂ) x z) ∧
        ∀ z ∈ ball z₀ ε, Tendsto (s31qr_twoHalfData F hd (q : F.X.carrier → ℂ → ℂ) x)
          (𝓝[{w | w ∈ (chartAt ℂ x).target ∧
            ((chartAt ℂ x).symm w ∈ range ιd ∨ (chartAt ℂ x).symm w ∈ range (J ∘ ιd))}] z) (𝓝 (H z)) := by
  obtain ⟨ε, hε, hsub, H, hH, heq⟩ := s31qi_seam_local F hm hd q x hz₀ hfix hP
  refine ⟨ε, hε, hsub, H, hH, heq, fun z hz => ?_⟩
  have hc : Tendsto H (𝓝[{w | w ∈ (chartAt ℂ x).target ∧
      ((chartAt ℂ x).symm w ∈ range ιd ∨ (chartAt ℂ x).symm w ∈ range (J ∘ ιd))}] z) (𝓝 (H z)) :=
    ((hH z hz).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  apply hc.congr'
  filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz), self_mem_nhdsWithin] with w hw hwA
  exact heq w hw hwA.2

/-- **(C) The seam-filled two-half data.** -/
theorem s31qi_seam_fill [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd) :
    ∃ T : admissibleQDSpace F →ₗ[ℝ] (Xd.carrier → ℂ → ℂ), ∀ q : admissibleQDSpace F,
      IsDiffFamily 2 0 (T q) ∧
      (∀ a : Xd.carrier, DifferentiableOn ℂ (T q a)
        ((chartAt ℂ a).target ∩ (chartAt ℂ a).symm ⁻¹' (↑Pd : Set Xd.carrier)ᶜ)) ∧
      (∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range ιd →
        T q x z = s31qr_positiveData F hd (q : F.X.carrier → ℂ → ℂ) x z) ∧
      (∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range (J ∘ ιd) →
        T q x z = s31qr_mirrorData F hd (q : F.X.carrier → ℂ → ℂ) x z) ∧
      (∀ a : Xd.carrier, ∀ p ∈ Pd, p ∈ (chartAt ℂ a).source → T q a (chartAt ℂ a p) = 0) := by
  classical
  haveI : Nonempty S := inferInstance
  -- the halves and their chart pictures
  let hh : Xd.carrier → Prop := fun p => p ∈ range ιd ∨ p ∈ range (J ∘ ιd)
  let A : Xd.carrier → Set ℂ := fun x =>
    {w | w ∈ (chartAt ℂ x).target ∧ ((chartAt ℂ x).symm w ∈ range ιd ∨ (chartAt ℂ x).symm w ∈ range (J ∘ ιd))}
  let D : admissibleQDSpace F → Xd.carrier → ℂ → ℂ := fun q =>
    s31qr_twoHalfData F hd (q : F.X.carrier → ℂ → ℂ)
  let V : admissibleQDSpace F → Xd.carrier → ℂ → ℂ := fun q x z =>
    if z ∈ (chartAt ℂ x).target then
      (if hh ((chartAt ℂ x).symm z) then D q x z
        else if (chartAt ℂ x).symm z ∈ Pd then 0 else limUnder (𝓝[A x] z) (D q x))
    else 0
  have hRo : IsOpen (range ιd) := hd.embedding.isOpenMap.isOpen_range
  have hMo : IsOpen (range (J ∘ ιd)) := by
    rw [range_comp]
    exact J.isOpenMap _ hRo
  have hPc : IsClosed (↑Pd : Set Xd.carrier) := Pd.finite_toSet.isClosed
  -- density: `𝓝[A x] z` is nontrivial at every chart point
  have hneBot : ∀ x z, z ∈ (chartAt ℂ x).target → (𝓝[A x] z).NeBot := fun x z hz =>
    mem_closure_iff_nhdsWithin_neBot.1 (s31q2_halves_dense F hd x hz)
  -- a point of the target which is neither on a half nor in `Pd` is a fixed point of `J`
  have hfixOf : ∀ x z, z ∈ (chartAt ℂ x).target → ¬ hh ((chartAt ℂ x).symm z) →
      (chartAt ℂ x).symm z ∉ Pd → J ((chartAt ℂ x).symm z) = (chartAt ℂ x).symm z := by
    intro x z _ hh' hP
    rcases s31qr_outside_halves F hd (fun h => hh' (Or.inl h)) (fun h => hh' (Or.inr h)) with h | h
    · exact h
    · exact absurd h hP
  -- the seam values
  have hseam : ∀ q x z₀, z₀ ∈ (chartAt ℂ x).target → ¬ hh ((chartAt ℂ x).symm z₀) →
      (chartAt ℂ x).symm z₀ ∉ Pd →
      ∃ ε : ℝ, 0 < ε ∧ ball z₀ ε ⊆ (chartAt ℂ x).target ∧ ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball z₀ ε) ∧
        (∀ z ∈ ball z₀ ε, (chartAt ℂ x).symm z ∉ Pd → V q x z = H z) ∧
        ∀ z ∈ ball z₀ ε, Tendsto (D q x) (𝓝[A x] z) (𝓝 (H z)) := by
    intro q x z₀ hz₀ hh₀ hP₀
    obtain ⟨ε, hε, hsub, H, hH, heq, hlim⟩ :=
      s31q2_seam_limit F hm hd q x hz₀ (hfixOf x z₀ hz₀ hh₀ hP₀) hP₀
    refine ⟨ε, hε, hsub, H, hH, fun z hz hzP => ?_, hlim⟩
    have hzt := hsub hz
    by_cases hhz : hh ((chartAt ℂ x).symm z)
    · simp only [V, hzt, hhz, if_true]
      exact (heq z hz hhz).symm
    · simp only [V, hzt, hhz, hzP, if_true, if_false]
      haveI := hneBot x z hzt
      exact (hlim z hz).limUnder_eq
  have hseamT : ∀ q x z, z ∈ (chartAt ℂ x).target → ¬ hh ((chartAt ℂ x).symm z) →
      (chartAt ℂ x).symm z ∉ Pd → Tendsto (D q x) (𝓝[A x] z) (𝓝 (V q x z)) := by
    intro q x z hz hhz hzP
    obtain ⟨ε, hε, _, H, _, hV, hlim⟩ := hseam q x z hz hhz hzP
    rw [hV z (mem_ball_self hε) hzP]
    exact hlim z (mem_ball_self hε)
  -- linearity
  let T : admissibleQDSpace F →ₗ[ℝ] (Xd.carrier → ℂ → ℂ) :=
    { toFun := V
      map_add' := fun q r => by
        funext x z
        simp only [Pi.add_apply]
        by_cases hz : z ∈ (chartAt ℂ x).target
        · by_cases hhz : hh ((chartAt ℂ x).symm z)
          · simp only [V, D, hz, hhz, if_true, Submodule.coe_add]
            rw [s31qr_twoHalf_add]
            rfl
          · by_cases hzP : (chartAt ℂ x).symm z ∈ Pd
            · simp only [V, hz, hhz, hzP, if_true, if_false, add_zero]
            · have t := (hseamT q x z hz hhz hzP).add (hseamT r x z hz hhz hzP)
              have hD : D (q + r) x = D q x + D r x := by
                simp only [D, Submodule.coe_add]
                rw [s31qr_twoHalf_add]
                rfl
              haveI := hneBot x z hz
              have hval : V (q + r) x z = limUnder (𝓝[A x] z) (D (q + r) x) := by
                simp only [V, hz, hhz, hzP, if_true, if_false]
              rw [hval, hD]
              exact t.limUnder_eq
        · simp only [V, hz, if_false, add_zero]
      map_smul' := fun c q => by
        funext x z
        simp only [Pi.smul_apply, RingHom.id_apply]
        by_cases hz : z ∈ (chartAt ℂ x).target
        · by_cases hhz : hh ((chartAt ℂ x).symm z)
          · simp only [V, D, hz, hhz, if_true, Submodule.coe_smul]
            rw [s31qr_twoHalf_real_smul]
            rfl
          · by_cases hzP : (chartAt ℂ x).symm z ∈ Pd
            · simp only [V, hz, hhz, hzP, if_true, if_false, smul_zero]
            · have t := (hseamT q x z hz hhz hzP).const_smul c
              have hD : D (c • q) x = c • D q x := by
                simp only [D, Submodule.coe_smul]
                rw [s31qr_twoHalf_real_smul]
                rfl
              haveI := hneBot x z hz
              have hval : V (c • q) x z = limUnder (𝓝[A x] z) (D (c • q) x) := by
                simp only [V, hz, hhz, hzP, if_true, if_false]
              rw [hval, hD]
              exact t.limUnder_eq
        · simp only [V, hz, if_false, smul_zero] }
  refine ⟨T, fun q => ?_⟩
  have hTq : ∀ x z, T q x z = V q x z := fun _ _ => rfl
  -- values on the halves
  have hhalfV : ∀ x z, z ∈ (chartAt ℂ x).target → hh ((chartAt ℂ x).symm z) → V q x z = D q x z := by
    intro x z hz hhz
    simp only [V, hz, hhz, if_true]
  -- holomorphy of the two-half data on the halves
  have hDhol : ∀ x z, z ∈ (chartAt ℂ x).target → hh ((chartAt ℂ x).symm z) →
      DifferentiableAt ℂ (D q x) z := by
    intro x z hz hhz
    rcases hhz with hR | hM
    · have hO : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' range ιd) :=
        (chartAt ℂ x).isOpen_inter_preimage_symm hRo
      have hd1 := (s31qr_positive_holomorphic F hd q.2 x).differentiableAt (hO.mem_nhds ⟨hz, hR⟩)
      apply hd1.congr_of_eventuallyEq
      filter_upwards [hO.mem_nhds ⟨hz, hR⟩] with w hw
      exact s31qr_twoHalf_on_positive F hd _ x w hw.2
    · have hO : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' range (J ∘ ιd)) :=
        (chartAt ℂ x).isOpen_inter_preimage_symm hMo
      have hd1 := (s31q2_mirror_holomorphic F hd q.2 x).differentiableAt (hO.mem_nhds ⟨hz, hM⟩)
      apply hd1.congr_of_eventuallyEq
      filter_upwards [hO.mem_nhds ⟨hz, hM⟩] with w hw
      exact s31qr_twoHalf_on_mirror F hd _ x w hw.2
  have hHo : ∀ x, IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' {p | hh p}) := fun x =>
    (chartAt ℂ x).isOpen_inter_preimage_symm (hRo.union hMo)
  have hPo : ∀ x, IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (↑Pd : Set Xd.carrier)ᶜ) := fun x =>
    (chartAt ℂ x).isOpen_inter_preimage_symm hPc.isOpen_compl
  -- (ii) holomorphy off `Pd`, as an `At` statement
  have hholAt : ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∉ Pd →
      DifferentiableAt ℂ (V q x) z := by
    intro x z hz hzP
    by_cases hhz : hh ((chartAt ℂ x).symm z)
    · apply (hDhol x z hz hhz).congr_of_eventuallyEq
      filter_upwards [(hHo x).mem_nhds ⟨hz, hhz⟩] with w hw
      exact hhalfV x w hw.1 hw.2
    · obtain ⟨ε, hε, _, H, hH, hV, _⟩ := hseam q x z hz hhz hzP
      apply ((hH z (mem_ball_self hε)).differentiableAt).congr_of_eventuallyEq
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε), (hPo x).mem_nhds ⟨hz, hzP⟩] with w hw hwP
      exact hV w hw hwP.2
  refine ⟨⟨fun x z hz => ?_, fun x y z hz hs => ?_⟩, fun a z hz => ?_, fun x z hz hR => ?_,
    fun x z hz hM => ?_, fun a p hp hs => ?_⟩
  · -- (i) off the target
    simp only [hTq, V, hz, if_false]
  · -- (i) the tensor law
    rw [hTq, hTq, zpow_zero, mul_one, zpow_two]
    obtain ⟨hxt, _, hpoint⟩ := s23_transition_mem hz hs
    by_cases hhz : hh ((chartAt ℂ y).symm z)
    · have hhx : hh ((chartAt ℂ x).symm (chartTransition x y z)) := hpoint.symm ▸ hhz
      rw [hhalfV y z hz hhz, hhalfV x _ hxt hhx]
      have hlaw := (s31qr_twoHalf_family F hd (q : F.X.carrier → ℂ → ℂ)).2 x y z hz hs
      rw [zpow_zero, mul_one, zpow_two] at hlaw
      exact hlaw
    · have hhx : ¬ hh ((chartAt ℂ x).symm (chartTransition x y z)) := hpoint.symm ▸ hhz
      by_cases hzP : (chartAt ℂ y).symm z ∈ Pd
      · have hxP : (chartAt ℂ x).symm (chartTransition x y z) ∈ Pd := hpoint.symm ▸ hzP
        simp only [V, hz, hhz, hzP, hxt, hhx, hxP, if_true, if_false, zero_mul]
      · have hxP : (chartAt ℂ x).symm (chartTransition x y z) ∉ Pd := hpoint.symm ▸ hzP
        obtain ⟨ε₁, hε₁, hsub₁, H₁, hH₁, hV₁, _⟩ := hseam q y z hz hhz hzP
        obtain ⟨ε₂, hε₂, hsub₂, H₂, hH₂, hV₂, _⟩ := hseam q x _ hxt hhx hxP
        rw [hV₁ z (mem_ball_self hε₁) hzP, hV₂ _ (mem_ball_self hε₂) hxP]
        -- the transition and its derivative near `z`
        set τ := chartTransition x y with hτ
        have hOτ : IsOpen ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source) :=
          (chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x).open_source
        have hτd : DifferentiableOn ℂ τ ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source) :=
          fun w hw => (s23_transition_differentiableAt x y hw.1 hw.2).differentiableWithinAt
        have hτc : ContinuousAt τ z := (hτd.differentiableAt (hOτ.mem_nhds ⟨hz, hs⟩)).continuousAt
        have hdτc : ContinuousAt (deriv τ) z :=
          ((hτd.deriv hOτ).differentiableAt (hOτ.mem_nhds ⟨hz, hs⟩)).continuousAt
        have hH₂c : ContinuousAt H₂ (τ z) := (hH₂ _ (mem_ball_self hε₂)).continuousAt
        have hf₂ : Tendsto (fun w => H₂ (τ w) * deriv τ w ^ 2) (𝓝[A y] z)
            (𝓝 (H₂ (τ z) * deriv τ z ^ 2)) :=
          ((hH₂c.comp hτc).mul (hdτc.pow 2)).tendsto.mono_left nhdsWithin_le_nhds
        have hf₁ : Tendsto H₁ (𝓝[A y] z) (𝓝 (H₁ z)) :=
          (hH₁ z (mem_ball_self hε₁)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        have hball₂ : τ ⁻¹' ball (τ z) ε₂ ∈ 𝓝 z := hτc.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hε₂))
        have hev : H₁ =ᶠ[𝓝[A y] z] fun w => H₂ (τ w) * deriv τ w ^ 2 := by
          filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hε₁)),
            nhdsWithin_le_nhds (hOτ.mem_nhds ⟨hz, hs⟩), nhdsWithin_le_nhds hball₂, self_mem_nhdsWithin]
            with w hw₁ hwO hw₂ hwA
          obtain ⟨hwxt, _, hwpoint⟩ := s23_transition_mem hwO.1 hwO.2
          have hhw : hh ((chartAt ℂ x).symm (τ w)) := hwpoint.symm ▸ hwA.2
          have hwP : (chartAt ℂ y).symm w ∉ Pd := by
            intro hP
            rcases hwA.2 with h | h
            · exact (s31qi_Pd_off_halves F hm hd _ hP).1 h
            · exact (s31qi_Pd_off_halves F hm hd _ hP).2 h
          have hwxP : (chartAt ℂ x).symm (τ w) ∉ Pd := hwpoint.symm ▸ hwP
          rw [← hV₁ w hw₁ hwP, ← hV₂ _ hw₂ hwxP, hhalfV y w hwO.1 hwA.2, hhalfV x _ hwxt hhw]
          have hlaw := (s31qr_twoHalf_family F hd (q : F.X.carrier → ℂ → ℂ)).2 x y w hwO.1 hwO.2
          rw [zpow_zero, mul_one, zpow_two] at hlaw
          simp only [D]
          rw [hlaw, hτ]
          ring
        haveI := hneBot y z hz
        have := tendsto_nhds_unique (hf₁.congr' hev) hf₂
        rw [this]
        ring
  · -- (ii)
    exact (hholAt a z hz.1 hz.2).differentiableWithinAt
  · -- (iii)
    rw [hTq, hhalfV x z hz (Or.inl hR)]
    exact s31qr_twoHalf_on_positive F hd _ x z hR
  · -- (iv)
    rw [hTq, hhalfV x z hz (Or.inr hM)]
    exact s31qr_twoHalf_on_mirror F hd _ x z hM
  · -- (v)
    have hzt : chartAt ℂ a p ∈ (chartAt ℂ a).target := (chartAt ℂ a).map_source hs
    have hpp : (chartAt ℂ a).symm (chartAt ℂ a p) = p := (chartAt ℂ a).left_inv hs
    have hnh : ¬ hh ((chartAt ℂ a).symm (chartAt ℂ a p)) := by
      rw [hpp]
      rintro (h | h)
      · exact (s31qi_Pd_off_halves F hm hd p hp).1 h
      · exact (s31qi_Pd_off_halves F hm hd p hp).2 h
    have hPp : (chartAt ℂ a).symm (chartAt ℂ a p) ∈ Pd := by rw [hpp]; exact hp
    rw [hTq]
    simp only [V, hzt, hnh, hPp, if_true, if_false]

end SeamFill

end LiZhongQC
