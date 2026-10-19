import LiZhongQC.Lemmas.FiniteTypeUniqueness
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import LiZhongQC.Lemmas.SchottkyReflectionTransition
section SchottkyExteriorUniformizerBlock

/-! An exterior Jordan uniformizer retaining its analytic formula.
Unlike the topological shrinking map, the map on the finite exterior below
is a composition of a Mobius map and a conformal Jordan uniformizer. -/

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace LiZhongQC

/-- The bounded exterior model with the actual Mobius formula retained.
The selected pole lies inside J, hence never on the closed exterior. -/
theorem s78ra_exterior_mobius_model {J : Set ℂ} (hJ : IsJordanDomain J)
    (hb : Bornology.IsBounded J) :
    ∃ c ∈ J, ∃ W : Set ℂ, IsJordanDomain W ∧ Bornology.IsBounded W ∧
      let T := mobiusHomeomorph 0 1 1 (-c) (uq_j_inv_det c)
      T '' (closure (toExt J))ᶜ = toExt W ∧
      T '' (toExt J)ᶜ = closure (toExt W) ∧
      T '' frontier (toExt J) = frontier (toExt W) := by
  obtain ⟨c, hc⟩ := hJ.2.1.nonempty
  let T := mobiusHomeomorph 0 1 1 (-c) (uq_j_inv_det c)
  have hTc : T (c : ExtPlane) = extInf := uq_j_mobiusInv_apply_self c
  let B : Set ExtPlane := (closure (toExt J))ᶜ
  let C : Set ExtPlane := (toExt J)ᶜ
  obtain ⟨hBo, hBc, hBfr, hBcl⟩ := s31sh_jordan_exterior hJ hb
  have hCo : IsClosed C := (isOpen_toExt_iff.2 hJ.1).isClosed_compl
  have hBC : B ⊆ C := compl_subset_compl.2 subset_closure
  have hTC : extInf ∉ T '' C := by
    rintro ⟨p, hp, hpe⟩
    have hpc : p = (c : ExtPlane) := T.injective (hpe.trans hTc.symm)
    exact hp (hpc.symm ▸ coe_mem_toExt_iff.2 hc)
  let W : Set ℂ := ((↑) : ℂ → ExtPlane) ⁻¹' (T '' B)
  let K : Set ℂ := ((↑) : ℂ → ExtPlane) ⁻¹' (T '' C)
  have hWeq : toExt W = T '' B :=
    uq_j_toExt_preimage_coe (fun h => hTC (image_mono hBC h))
  have hKeq : toExt K = T '' C := uq_j_toExt_preimage_coe hTC
  have hKc : IsCompact K := by
    have h : IsClosed (toExt K) := by
      rw [hKeq]
      exact T.isClosedMap C hCo
    exact (OnePoint.isClosed_image_coe.1 h).2
  have hWK : W ⊆ K := preimage_mono (image_mono hBC)
  have hWb : Bornology.IsBounded W := hKc.isBounded.subset hWK
  have hWo : IsOpen W := by
    apply isOpen_toExt_iff.1
    rw [hWeq]
    exact T.isOpenMap B hBo
  have hWc : IsConnected W := by
    have h : IsConnected (toExt W) := by
      rw [hWeq]
      exact hBc.image T T.continuous.continuousOn
    refine ⟨?_, OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image.1 h.2⟩
    obtain ⟨p, hp⟩ := h.nonempty
    obtain ⟨z, hz, _⟩ := hp
    exact ⟨z, hz⟩
  have hWj : IsJordanCurve (frontier (toExt W)) := by
    rw [hWeq, ← T.image_frontier, hBfr]
    exact uq_isJordanCurve_image T hJ.2.2
  refine ⟨c, hc, W, ⟨hWo, hWc, hWj⟩, hWb, hWeq.symm, ?_, ?_⟩
  · rw [hWeq, ← T.image_closure, hBcl]
  · rw [hWeq, ← T.image_frontier, hBfr]

/-- The exterior of a bounded Jordan domain has a conformal coordinate
with a homeomorphic spherical extension to its boundary. The extension
maps the closed exterior onto the closed unit disc and the frontier onto
the unit circle. The formula on finite exterior points is retained.

No extension of a smooth boundary parametrization is used. -/
theorem s78ra_exterior_uniformizer {J : Set ℂ} (hJ : IsJordanDomain J)
    (hb : Bornology.IsBounded J) :
    ∃ (f : ℂ → ℂ) (F : ExtPlane → ExtPlane),
      DifferentiableOn ℂ f (closure J)ᶜ ∧ InjOn f (closure J)ᶜ ∧
      MapsTo f (closure J)ᶜ unitDisc ∧
      ContinuousOn F (toExt J)ᶜ ∧ InjOn F (toExt J)ᶜ ∧
      F '' (toExt J)ᶜ = closure (toExt unitDisc) ∧
      F '' (closure (toExt J))ᶜ = toExt unitDisc ∧
      F '' frontier (toExt J) = frontier (toExt unitDisc) ∧
      ∀ z ∈ (closure J)ᶜ, F (z : ExtPlane) = (f z : ExtPlane) := by
  obtain ⟨c, hc, W, hW, _, hTopen, hTclosed, hTfrontier⟩ :=
    s78ra_exterior_mobius_model hJ hb
  let T := mobiusHomeomorph 0 1 1 (-c) (uq_j_inv_det c)
  obtain ⟨φ, hφ, Φ, hΦ⟩ := s13x_th_exists_disc_uniformizer hW
  let t : ℂ → ℂ := mobiusFn 0 1 1 (-c)
  have havoid : ∀ z ∈ (closure J)ᶜ, z ≠ c := by
    intro z hz he
    exact hz (he.symm ▸ subset_closure hc)
  have hTcoe : ∀ z ∈ (closure J)ᶜ, T (z : ExtPlane) = (t z : ExtPlane) := by
    intro z hz
    exact uq_j_mobiusInv_coe (havoid z hz)
  have hmaps : MapsTo t (closure J)ᶜ W := by
    intro z hz
    apply coe_mem_toExt_iff.1
    rw [← hTopen, ← hTcoe z hz]
    refine ⟨(z : ExtPlane), ?_, rfl⟩
    rw [closure_toExt_of_isBounded' hb]
    exact fun h => hz (coe_mem_toExt_iff.1 h)
  have ht := uq_j_isConformalOnto_mobiusInv havoid
  have hdiff : DifferentiableOn ℂ (φ ∘ t) (closure J)ᶜ :=
    hφ.1.comp ht.1 hmaps
  have hinj : InjOn (φ ∘ t) (closure J)ᶜ := by
    intro z hz w hw he
    exact ht.2.1 hz hw (hφ.2.1 (hmaps hz) (hmaps hw) he)
  have hTc : MapsTo T (toExt J)ᶜ (closure (toExt W)) := by
    intro z hz
    rw [← hTclosed]
    exact mem_image_of_mem T hz
  have hΦopen : Φ '' toExt W = toExt unitDisc := by
    apply subset_antisymm
    · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rw [hΦ.1 z hz]
      exact coe_mem_toExt_iff.2 (hφ.mapsTo hz)
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hφ.2.2.symm ▸ hw
      exact ⟨(z : ExtPlane), ⟨z, hz, rfl⟩, hΦ.1 z hz⟩
  have hΦfrontier : Φ '' frontier (toExt W) = frontier (toExt unitDisc) := by
    have hUD : IsOpen (toExt unitDisc) :=
      isOpen_toExt_iff.2 (show IsOpen unitDisc from isOpen_ball)
    rw [frontier, (isOpen_toExt_iff.2 hW.1).interior_eq,
      frontier, hUD.interior_eq]
    rw [hΦ.2.2.1.image_diff_subset subset_closure, hΦ.2.2.2, hΦopen]
  refine ⟨φ ∘ t, Φ ∘ T, hdiff, hinj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun z hz => hφ.mapsTo (hmaps hz)
  · exact hΦ.2.1.comp T.continuous.continuousOn hTc
  · intro z hz w hw he
    exact T.injective (hΦ.2.2.1 (hTc hz) (hTc hw) he)
  · rw [image_comp, hTclosed, hΦ.2.2.2]
  · rw [image_comp, hTopen, hΦopen]
  · rw [image_comp, hTfrontier, hΦfrontier]
  · intro z hz
    change Φ (T (z : ExtPlane)) = (φ (t z) : ExtPlane)
    rw [hTcoe z hz, hΦ.1 (t z) (hmaps hz)]

/-- A genuine closed-disc coordinate on the spherical closed exterior,
with its analytic formula retained at every finite interior point. This
is the input to local half-disc restriction and sewing; no radial boundary
alignment or topological shrinking is performed. -/
theorem s78ra_exterior_closed_coordinate {J : Set ℂ} (hJ : IsJordanDomain J)
    (hb : Bornology.IsBounded J) :
    ∃ (f : ℂ → ℂ) (e : ↥((toExt J)ᶜ) ≃ₜ closedBall (0 : ℂ) 1),
      DifferentiableOn ℂ f (closure J)ᶜ ∧ InjOn f (closure J)ᶜ ∧
      (∀ z ∈ (closure J)ᶜ, ∀ hz : (z : ExtPlane) ∈ (toExt J)ᶜ,
        (e ⟨(z : ExtPlane), hz⟩).val = f z) ∧
      (∀ x : ↥((toExt J)ᶜ),
        ‖(e x).val‖ < 1 ↔ x.val ∈ (closure (toExt J))ᶜ) ∧
      (∀ x : ↥((toExt J)ᶜ),
        ‖(e x).val‖ = 1 ↔ x.val ∈ frontier (toExt J)) := by
  obtain ⟨f, F, hf, hfi, _, hFc, hFi, hFcl, hFo, hFfr, hFe⟩ :=
    s78ra_exterior_uniformizer hJ hb
  let C : Set ExtPlane := (toExt J)ᶜ
  let B : Set ExtPlane := closure (toExt unitDisc)
  have hCclosed : IsClosed C := (isOpen_toExt_iff.2 hJ.1).isClosed_compl
  letI : CompactSpace ↥C := isCompact_iff_compactSpace.1 hCclosed.isCompact
  let k : ↥C → ↥B := fun x => ⟨F x.val, by
    change F x.val ∈ closure (toExt unitDisc)
    rw [← hFcl]
    exact mem_image_of_mem F x.property⟩
  have hkc : Continuous k := by
    apply Continuous.subtype_mk
    exact hFc.comp_continuous continuous_subtype_val (fun x => x.property)
  have hki : Function.Injective k := by
    intro x y he
    exact Subtype.ext (hFi x.property y.property (congrArg Subtype.val he))
  have hks : Function.Surjective k := by
    intro y
    have hy : y.val ∈ F '' (toExt J)ᶜ := by
      rw [hFcl]
      exact y.property
    obtain ⟨x, hx, he⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  let eC : ↥C ≃ₜ ↥B :=
    (hkc.isClosedEmbedding hki).isEmbedding.toHomeomorphOfSurjective hks
  let eB : closedBall (0 : ℂ) 1 ≃ₜ ↥B :=
    (OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage
      (closedBall (0 : ℂ) 1)).trans
      (Homeomorph.setCongr abN_closure_toExt_unitDisc.symm)
  let e : ↥C ≃ₜ closedBall (0 : ℂ) 1 := eC.trans eB.symm
  have heF : ∀ x : ↥C, ((e x).val : ExtPlane) = F x.val := by
    intro x
    exact congrArg Subtype.val (eB.apply_symm_apply (eC x))
  have hlocus : ∀ x : ↥C, ‖(e x).val‖ < 1 ↔
      x.val ∈ (closure (toExt J))ᶜ := by
    intro x
    have hfmem : F x.val ∈ toExt unitDisc ↔
        x.val ∈ (closure (toExt J))ᶜ := by
      constructor
      · intro hx
        obtain ⟨y, hy, he⟩ := hFo.symm ▸ hx
        have hyC : y ∈ C := compl_subset_compl.2 subset_closure hy
        exact (hFi hyC x.property he) ▸ hy
      · intro hx
        rw [← hFo]
        exact mem_image_of_mem F hx
    rw [← hfmem, ← heF x, coe_mem_toExt_iff]
    exact mem_ball_zero_iff.symm
  refine ⟨f, e, hf, hfi, ?_, hlocus, ?_⟩
  · intro z hz hzC
    apply OnePoint.coe_injective
    exact (heF ⟨(z : ExtPlane), hzC⟩).trans (hFe z hz)
  · intro x
    have hle : ‖(e x).val‖ ≤ 1 := mem_closedBall_zero_iff.1 (e x).property
    have hnot : ‖(e x).val‖ = 1 ↔ ¬ ‖(e x).val‖ < 1 := by
      constructor
      · intro h
        rw [h]
        exact lt_irrefl 1
      · intro h
        exact le_antisymm hle (le_of_not_gt h)
    rw [hnot, hlocus]
    change (¬ x.val ∉ closure (toExt J)) ↔ _
    rw [not_not]
    rw [frontier, (isOpen_toExt_iff.2 hJ.1).interior_eq]
    exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩

/-- The boundary-normalized Cayley coordinate has the expected imaginary
part. This identity also holds at the totalized pole; the analytic and
injectivity lemmas below explicitly exclude that pole. -/
theorem s78ra_cayley_im (a w : ℂ) :
    (I * (a - w) / (a + w)).im =
      (normSq a - normSq w) / normSq (a + w) := by
  simp only [Complex.div_im, Complex.mul_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, normSq_apply]
  ring

/-- A unit-circle boundary point is sent to zero and its antipode is the
only pole. -/
theorem s78ra_cayley_center (a : ℂ) : I * (a - a) / (a + a) = 0 := by
  simp

/-- The normalized Cayley map sends the open unit disc into the upper
half-plane. In particular its denominator is nonzero there. -/
theorem s78ra_cayley_upper {a w : ℂ} (ha : ‖a‖ = 1) (hw : ‖w‖ < 1) :
    a + w ≠ 0 ∧ 0 < (I * (a - w) / (a + w)).im := by
  have hd : a + w ≠ 0 := by
    intro h
    have he : w = -a := by linear_combination h
    rw [he, norm_neg, ha] at hw
    exact (lt_irrefl 1) hw
  refine ⟨hd, ?_⟩
  rw [s78ra_cayley_im]
  have han : normSq a = 1 := by rw [normSq_eq_norm_sq, ha]; norm_num
  have hwn : normSq w < 1 := normSq_lt_one_iff.2 hw
  exact div_pos (by rw [han]; linarith) (normSq_pos.2 hd)

/-- Boundary values lie on the real line. The pole is excluded by the
local chart domain, rather than treated as a finite coordinate. -/
theorem s78ra_cayley_real {a w : ℂ} (ha : ‖a‖ = 1) (hw : ‖w‖ = 1) :
    (I * (a - w) / (a + w)).im = 0 := by
  rw [s78ra_cayley_im, normSq_eq_norm_sq, normSq_eq_norm_sq, ha, hw]
  simp

/-- The normalized Cayley map is holomorphic away from its pole. -/
theorem s78ra_cayley_differentiableAt {a w : ℂ} (hw : a + w ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => I * (a - z) / (a + z)) w := by
  have hn : DifferentiableAt ℂ (fun z : ℂ => I * (a - z)) w := by fun_prop
  have hd : DifferentiableAt ℂ (fun z : ℂ => a + z) w := by fun_prop
  exact hn.div hd hw

/-- The normalized Cayley coordinate is injective on its actual finite
domain. This supplies injectivity of each restricted boundary coordinate. -/
theorem s78ra_cayley_injective {a : ℂ} (ha : a ≠ 0) :
    InjOn (fun z : ℂ => I * (a - z) / (a + z)) {z | a + z ≠ 0} := by
  intro z hz w hw he
  have he' : (a - z) * (a + w) = (a - w) * (a + z) := by
    have h := (div_eq_div_iff hz hw).1 he
    apply mul_left_cancel₀ Complex.I_ne_zero
    calc
      I * ((a - z) * (a + w)) = (I * (a - z)) * (a + w) := by ring
      _ = (I * (a - w)) * (a + z) := h
      _ = I * ((a - w) * (a + z)) := by ring
  have hprod : a * (z - w) = 0 := by
    linear_combination (-1 / 2 : ℂ) * he'
  exact sub_eq_zero.1 ((mul_eq_zero.1 hprod).resolve_left ha)

end LiZhongQC
end -- close original anonymous noncomputable section
end SchottkyExteriorUniformizerBlock

section SchottkyCayleyHalfChartBlock

/-! The actual topological half-plane coordinate, with both rational formulas.
The temporary import refers to the preceding archive module; its installed
path is intended to be LiZhongQC.Lemmas.SchottkyExteriorUniformizer. -/

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace LiZhongQC

/-- The inverse normalized Cayley formula maps the closed upper half-plane
into the closed disc and avoids the antipodal pole. -/
theorem s78ra_cayley_inverse_mem {a z : ℂ} (ha : ‖a‖ = 1) (hz : 0 ≤ z.im) :
    ‖a * (I - z) / (I + z)‖ ≤ 1 ∧ a + a * (I - z) / (I + z) ≠ 0 := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hd : I + z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
    linarith
  have han : normSq a = 1 := by rw [normSq_eq_norm_sq, ha]; norm_num
  have hsq : normSq (a * (I - z) / (I + z)) ≤ 1 := by
    rw [normSq_div, normSq_mul, han, one_mul, div_le_one (normSq_pos.2 hd)]
    simp only [normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im]
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg (a * (I - z) / (I + z))]
  · have he : a + a * (I - z) / (I + z) = (2 * a * I) / (I + z) := by
      field_simp [hd]
      <;> ring
    rw [he]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha0) I_ne_zero) hd

/-- A genuine homeomorphism from the closed unit disc with one boundary
point removed to the closed upper half-plane. Both maps are explicit. -/
theorem s78ra_closed_disc_halfplane_homeomorph {a : ℂ} (ha : ‖a‖ = 1) :
    ∃ e : {w : ℂ | ‖w‖ ≤ 1 ∧ a + w ≠ 0} ≃ₜ {z : ℂ | 0 ≤ z.im},
      (∀ w, (e w).val = I * (a - w.val) / (a + w.val)) ∧
      (∀ z, (e.symm z).val = a * (I - z.val) / (I + z.val)) := by
  have hden : ∀ z : {z : ℂ | 0 ≤ z.im}, I + z.val ≠ 0 := by
    intro z h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
    have hz : 0 ≤ z.val.im := z.property
    linarith
  have hforward : ∀ w : {w : ℂ | ‖w‖ ≤ 1 ∧ a + w ≠ 0},
      0 ≤ (I * (a - w.val) / (a + w.val)).im := by
    intro w
    rw [s78ra_cayley_im]
    apply div_nonneg _ (normSq_nonneg _)
    rw [normSq_eq_norm_sq, normSq_eq_norm_sq, ha]
    nlinarith [w.property.1, norm_nonneg w.val]
  let f : {w : ℂ | ‖w‖ ≤ 1 ∧ a + w ≠ 0} → {z : ℂ | 0 ≤ z.im} :=
    fun w => ⟨I * (a - w.val) / (a + w.val), hforward w⟩
  let g : {z : ℂ | 0 ≤ z.im} → {w : ℂ | ‖w‖ ≤ 1 ∧ a + w ≠ 0} :=
    fun z => ⟨a * (I - z.val) / (I + z.val), s78ra_cayley_inverse_mem ha z.property⟩
  have hleft : Function.LeftInverse g f := by
    intro w
    apply Subtype.ext
    change a * (I - (I * (a - w.val) / (a + w.val))) /
      (I + (I * (a - w.val) / (a + w.val))) = w.val
    have hd := hden (f w)
    change I + (I * (a - w.val) / (a + w.val)) ≠ 0 at hd
    apply (div_eq_iff hd).2
    field_simp [w.property.2]
    <;> ring
  have hright : Function.RightInverse g f := by
    intro z
    apply Subtype.ext
    change I * (a - (a * (I - z.val) / (I + z.val))) /
      (a + (a * (I - z.val) / (I + z.val))) = z.val
    have hd := (s78ra_cayley_inverse_mem ha z.property).2
    apply (div_eq_iff hd).2
    field_simp [hden z]
    <;> ring
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul (continuous_const.sub continuous_subtype_val)).div
      (continuous_const.add continuous_subtype_val) (fun w => w.property.2)
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul (continuous_const.sub continuous_subtype_val)).div
      (continuous_const.add continuous_subtype_val) hden
  exact ⟨{
    toFun := f
    invFun := g
    left_inv := hleft
    right_inv := hright
    continuous_toFun := hf
    continuous_invFun := hg }, fun _ => rfl, fun _ => rfl⟩

/-- Under the explicit half-plane homeomorphism, disc interior is exactly
the strictly upper side. Thus the real axis is precisely the seam. -/
theorem s78ra_cayley_side_iff {a w : ℂ} (ha : ‖a‖ = 1)
    (hw : ‖w‖ ≤ 1) (hd : a + w ≠ 0) :
    0 < (I * (a - w) / (a + w)).im ↔ ‖w‖ < 1 := by
  have _hfinite := hd
  constructor
  · intro hi
    by_contra hn
    have he : ‖w‖ = 1 := le_antisymm hw (le_of_not_gt hn)
    rw [s78ra_cayley_real ha he] at hi
    exact (lt_irrefl 0) hi
  · intro hi
    exact (s78ra_cayley_upper ha hi).2

/-- An actual closed-disc coordinate yields a relatively open boundary
chart to the closed upper half-plane, centered at the specified boundary
point. This theorem constructs the homeomorphism, rather than assuming a
collar. Restriction to a small half-disc is then a restriction of this map. -/
theorem s78ra_closed_coordinate_halfchart {A : Type*} [TopologicalSpace A]
    (e : A ≃ₜ closedBall (0 : ℂ) 1) (p : A) (hp : ‖(e p).val‖ = 1) :
    ∃ V : Set A, IsOpen V ∧ p ∈ V ∧
      ∃ h : ↥V ≃ₜ {z : ℂ | 0 ≤ z.im},
        (∀ x : ↥V, (h x).val =
          I * ((e p).val - (e x.val).val) / ((e p).val + (e x.val).val)) ∧
        (∀ hpV : p ∈ V, (h ⟨p, hpV⟩).val = 0) ∧
        (∀ x : ↥V, 0 < (h x).val.im ↔ ‖(e x.val).val‖ < 1) := by
  let a : ℂ := (e p).val
  let V : Set A := {x | a + (e x).val ≠ 0}
  have hVo : IsOpen V :=
    isOpen_ne_fun (continuous_const.add (continuous_subtype_val.comp e.continuous))
      continuous_const
  have ha0 : a ≠ 0 := by
    intro he
    have hp' : ‖a‖ = 1 := hp
    simp [he] at hp'
  have hpV : p ∈ V := by
    change a + a ≠ 0
    intro he
    apply ha0
    linear_combination (1 / 2 : ℂ) * he
  let E : ↥V ≃ₜ {w : ℂ | ‖w‖ ≤ 1 ∧ a + w ≠ 0} := {
    toFun := fun x => ⟨(e x.val).val,
      ⟨mem_closedBall_zero_iff.1 (e x.val).property, x.property⟩⟩
    invFun := fun w => ⟨e.symm ⟨w.val, mem_closedBall_zero_iff.2 w.property.1⟩, by
      change a + (e (e.symm ⟨w.val, _⟩)).val ≠ 0
      rw [e.apply_symm_apply]
      exact w.property.2⟩
    left_inv := by
      intro x
      apply Subtype.ext
      change e.symm (e x.val) = x.val
      exact e.symm_apply_apply x.val
    right_inv := by
      intro w
      apply Subtype.ext
      change (e (e.symm ⟨w.val, _⟩)).val = w.val
      rw [e.apply_symm_apply]
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (e.continuous.comp continuous_subtype_val)
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact e.symm.continuous.comp (continuous_subtype_val.subtype_mk _) }
  obtain ⟨k, hk, _⟩ := s78ra_closed_disc_halfplane_homeomorph hp
  refine ⟨V, hVo, hpV, E.trans k, ?_, ?_, ?_⟩
  · intro x
    exact hk (E x)
  · intro hpV'
    rw [show ((E.trans k) ⟨p, hpV'⟩).val =
      I * (a - a) / (a + a) from hk (E ⟨p, hpV'⟩)]
    exact s78ra_cayley_center a
  · intro x
    rw [show ((E.trans k) x).val =
      I * (a - (e x.val).val) / (a + (e x.val).val) from hk (E x)]
    exact s78ra_cayley_side_iff hp
      (mem_closedBall_zero_iff.1 (e x.val).property) x.property

/-- A genuine relative conformal boundary coordinate for the closed
exterior of a bounded Jordan domain. Its domain is open in that closed
exterior; its target is the closed upper half-plane. The finite interior
formula is holomorphic on the entire finite exterior. -/
theorem s78ra_exterior_boundary_halfchart {J : Set ℂ} (hJ : IsJordanDomain J)
    (hb : Bornology.IsBounded J) (p : ↥((toExt J)ᶜ))
    (hp : p.val ∈ frontier (toExt J)) :
    ∃ (g : ℂ → ℂ) (V : Set ↥((toExt J)ᶜ)), IsOpen V ∧ p ∈ V ∧
      ∃ h : ↥V ≃ₜ {z : ℂ | 0 ≤ z.im},
        DifferentiableOn ℂ g (closure J)ᶜ ∧
        (∀ hpV : p ∈ V, (h ⟨p, hpV⟩).val = 0) ∧
        (∀ x : ↥V, 0 < (h x).val.im ↔
          x.val.val ∈ (closure (toExt J))ᶜ) ∧
        (∀ z ∈ (closure J)ᶜ, ∀ hzC : (z : ExtPlane) ∈ (toExt J)ᶜ,
          ∀ hzV : (⟨(z : ExtPlane), hzC⟩ : ↥((toExt J)ᶜ)) ∈ V,
            (h ⟨⟨(z : ExtPlane), hzC⟩, hzV⟩).val = g z) := by
  obtain ⟨f, e, hf, _, hef, hei, heb⟩ := s78ra_exterior_closed_coordinate hJ hb
  have hpe : ‖(e p).val‖ = 1 := (heb p).2 hp
  obtain ⟨V, hVo, hpV, h, hh, hhp, hhi⟩ :=
    s78ra_closed_coordinate_halfchart e p hpe
  let a : ℂ := (e p).val
  let g : ℂ → ℂ := fun z => I * (a - f z) / (a + f z)
  have hzC : ∀ z ∈ (closure J)ᶜ, (z : ExtPlane) ∈ (toExt J)ᶜ := by
    intro z hz hh
    exact hz (subset_closure (coe_mem_toExt_iff.1 hh))
  have hfd : ∀ z ∈ (closure J)ᶜ, ‖f z‖ < 1 := by
    intro z hz
    have hzE : (z : ExtPlane) ∈ (closure (toExt J))ᶜ := by
      rw [closure_toExt_of_isBounded' hb]
      exact fun hh => hz (coe_mem_toExt_iff.1 hh)
    have hn := (hei ⟨(z : ExtPlane), hzC z hz⟩).2 hzE
    rwa [hef z hz (hzC z hz)] at hn
  refine ⟨g, V, hVo, hpV, h, ?_, hhp, ?_, ?_⟩
  · intro z hz
    have hfa : DifferentiableAt ℂ f z :=
      hf.differentiableAt (isClosed_closure.isOpen_compl.mem_nhds hz)
    have hka : DifferentiableAt ℂ (fun w => I * (a - w) / (a + w)) (f z) :=
      s78ra_cayley_differentiableAt (s78ra_cayley_upper hpe (hfd z hz)).1
    exact (hka.comp z hfa).differentiableWithinAt
  · intro x
    exact (hhi x).trans (hei x.val)
  · intro z hz hzC' hzV
    rw [hh]
    change I * (a - (e ⟨(z : ExtPlane), hzC'⟩).val) /
      (a + (e ⟨(z : ExtPlane), hzC'⟩).val) = g z
    rw [hef z hz hzC']

end LiZhongQC
end -- close original anonymous noncomputable section
end SchottkyCayleyHalfChartBlock

section SchottkyInvolutionCoordinateBlock

/-! Local reflection coordinates for any supplied antiholomorphic involution.
These are independent of the newly constructed Schottky quotient. -/

open Complex Set Filter Topology
open scoped ComplexConjugate Manifold

noncomputable section
namespace LiZhongQC

/-- An antiholomorphic involution germ fixing p has a genuine invertible
analytic coordinate in which it is conjugation. One of the two averages
with coefficients 1 and I always has a nonzero derivative. -/
theorem s78ra_antiholomorphic_involution_germ_coordinate
    {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ (conj ∘ f) p)
    (hfix : f p = p) (hperiod : ∀ᶠ z in 𝓝 p, f (f z) = z) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      p ∈ e.source ∧ e p = 0 ∧ AnalyticAt ℂ e p ∧
      AnalyticAt ℂ e.symm 0 ∧
      ∀ᶠ z in 𝓝 p, e (f z) = conj (e z) := by
  let d : ℂ := deriv (conj ∘ f) p
  have hb : ∃ b : ℂ, b + conj b * d ≠ 0 := by
    by_cases hd : 1 + d = 0
    · have hd' : d = -1 := by linear_combination hd
      refine ⟨I, ?_⟩
      norm_num [hd', Complex.ext_iff]
    · exact ⟨1, by simpa using hd⟩
  obtain ⟨b, hb⟩ := hb
  let A : ℂ → ℂ := fun z => b * (z - p) + conj b * (conj (f z) - conj p)
  have hA : AnalyticAt ℂ A p :=
    (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).add
      (analyticAt_const.mul (hf.sub analyticAt_const))
  have hD : HasDerivAt A (b + conj b * d) p := by
    have h := (((hasDerivAt_id p).sub_const p).const_mul b).add
      ((hf.differentiableAt.hasDerivAt.sub_const (conj p)).const_mul (conj b))
    convert! h using 1 <;>
      simp only [A, d, Pi.add_apply, Function.comp_apply, id_eq, mul_one]
  have hne : deriv A p ≠ 0 := by rw [hD.deriv]; exact hb
  have hzero : A p = 0 := by simp only [A, hfix, sub_self, mul_zero, add_zero]
  let hfd := hA.hasStrictDerivAt.hasStrictFDerivAt_equiv hne
  let e : OpenPartialHomeomorph ℂ ℂ := hfd.toOpenPartialHomeomorph A
  have hp : p ∈ e.source := hfd.mem_toOpenPartialHomeomorph_source
  have hi : AnalyticAt ℂ e.symm 0 := by
    have h := hA.analyticAt_localInverse hne
    change AnalyticAt ℂ e.symm (A p) at h
    rw [hzero] at h
    exact h
  refine ⟨e, hp, hzero, hA, hi, ?_⟩
  filter_upwards [hperiod] with z hz
  change A (f z) = conj (A z)
  simp only [A, hz, map_add, map_mul, map_sub, Complex.conj_conj]
  ring

/-- Any supplied IsAnticonformalInvolution, including that of an arbitrary
hd, has local reflection coordinates at each fixed point. No relationship
to the concrete quotient and no boundary regularity assumption is required.
The output is a genuine local coordinate change in the preferred chart. -/
theorem s78ra_given_involution_fixed_coordinate
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (J : X ≃ₜ X) (hJ : IsAnticonformalInvolution J)
    (p : X) (hp : J p = p) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (chartAt ℂ p) p ∈ e.source ∧ e ((chartAt ℂ p) p) = 0 ∧
      AnalyticAt ℂ e ((chartAt ℂ p) p) ∧ AnalyticAt ℂ e.symm 0 ∧
      ∀ᶠ z in 𝓝 ((chartAt ℂ p) p),
        e (localMapExpr J p z) = conj (e z) := by
  let c := chartAt ℂ p
  have hps : p ∈ c.source := mem_chart_source ℂ p
  have hpt : c p ∈ c.target := c.mapsTo hps
  have hmem : c p ∈ localMapDomain J p := by
    change c p ∈ c.target ∧ J (c.symm (c p)) ∈ (chartAt ℂ (J p)).source
    simp only [c.left_inv hps, hp]
    exact ⟨hpt, hps⟩
  have ha : AnalyticAt ℂ (conj ∘ localMapExpr J p) (c p) :=
    (hJ.2 p).analyticAt ((s23_localMapDomain_isOpen J.continuous p).mem_nhds hmem)
  have hfix : localMapExpr J p (c p) = c p := by
    change (chartAt ℂ (J p)) (J (c.symm (c p))) = c p
    simp only [c.left_inv hps, hp]
    rfl
  have hperiod : ∀ᶠ z in 𝓝 (c p),
      localMapExpr J p (localMapExpr J p z) = z := by
    filter_upwards [(s23_localMapDomain_isOpen J.continuous p).mem_nhds hmem] with z hz
    change z ∈ c.target ∧ J (c.symm z) ∈ (chartAt ℂ (J p)).source at hz
    rw [hp] at hz
    change (chartAt ℂ (J p))
      (J (c.symm ((chartAt ℂ (J p)) (J (c.symm z))))) = z
    simp only [hp]
    change c (J (c.symm (c (J (c.symm z))))) = z
    rw [c.left_inv hz.2, hJ.1, c.right_inv hz.1]
  exact s78ra_antiholomorphic_involution_germ_coordinate ha hfix hperiod

end LiZhongQC
end -- close original anonymous noncomputable section
end SchottkyInvolutionCoordinateBlock
