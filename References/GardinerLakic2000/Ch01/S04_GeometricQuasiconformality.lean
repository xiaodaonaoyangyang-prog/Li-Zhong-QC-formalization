import References.GardinerLakic2000.Ch01.S03_AnalyticQuasiconformality

/-!
# Gardiner–Lakic 2000, Ch. 1 §1.4 Geometric quasiconformality

Source `teichmuller.txt`, lines 677–790 (Chapter 1, §1.4).

* Definition (generalized quadrilateral and its module `m(Q)`, l. 678) — exists: `LiZhongQC.TopQuad`
  `LiZhongQC.TopQuad.modulus` (a Jordan domain with four boundary points, module of the conformal rectangle)
* Unlabelled (`m(Q*) = m(Q)⁻¹`, l. 678; used in the proof of Proposition 3 and in §2.3) — exists:
  `LiZhongQC.thm1_2_modulus_rotate` (the conjugate quadrilateral is the rotated one)
* Proposition 3 (l. 694) — `prop1_3`
* Proposition 4 (l. 744) — `prop1_4`
* Definition 4 (geometric definition, l. 782) — exists: `LiZhongQC.IsKQC` (an orientation preserving homeomorphism
  with m(f(Q)) at most K m(Q) for every quadrilateral with closure in the domain)
* Unlabelled (the geometric definition implies the analytic one, l. 788; cited at l. 780, 1291) —
  `para1_4_geometric_imp_analytic`

Not items: the existence of the conformal map onto a rectangle (l. 680, U−; part of `LiZhongQC.TopQuad.modulus`); the
Remark (Grötzsch's argument, l. 742); "no side-preserving conformal map if `a/b ≠ a′/b′`" (l. 778, U−).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (TopQuad IsKQC toExt)

/-- **Proposition 3** (§1.4, l. 694). If `f` is `K`-quasiconformal on `Ω` (analytic definition) and takes the
quadrilateral `Q` in `Ω` to the quadrilateral `f(Q)`, then `(1/K) m(f(Q)) ≤ m(Q) ≤ K m(f(Q))`. "Contained in `Ω`"
is read as `Q̄ ⊆ Ω`, so that `f(Q)` is again a quadrilateral with the image vertices. -/
theorem prop1_3 {f : ℂ → ℂ} {Ω : Set ℂ} {K : ℝ} (hf : IsKQCAnalytic f Ω K) (Q Q' : TopQuad)
    (hQ : closure (toExt Q.dom) ⊆ toExt Ω) (himg : Q.IsImageUnder Q' f) :
    Q'.modulus / K ≤ Q.modulus ∧ Q.modulus ≤ K * Q'.modulus := by
  -- the bridge `gl1_acl_isKQC` and the two-sided bound of the geometric definition (`LiZhongQC.IsKQC.modulus_ge`)
  obtain ⟨h1, h2⟩ := (gl1_acl_isKQC hf).modulus_ge Q Q' hQ himg
  have hK0 : 0 < K := zero_lt_one.trans_le hf.2.2.1
  constructor
  · rw [div_le_iff₀ hK0]
    linarith
  · rw [div_le_iff₀ hK0] at h1
    linarith

open LiZhongQC in
/-- Helper for `prop1_4` (§1.4), P1: the side correspondence. A `K`-quasiconformal map of `R = (0, a) × (0, b)` onto
`R′ = (0, a′) × (0, b′)`, continuous on `R̄` and fixing the vertices, maps the left side `{Re = 0}` into the left side
and the right side `{Re = a}` into `{Re = a′}` (homeomorphic boundary extension `thm13_3_boundary_correspondence`,
equal to `f` on `R̄`; images of sides `aqc_image_side_homeo`). -/
theorem gl1_gz_sides {a b a' b' K : ℝ} (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b') {f : ℂ → ℂ}
    (hf : IsKQC f {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b} K)
    (himg : f '' {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b} =
      {z : ℂ | 0 < z.re ∧ z.re < a' ∧ 0 < z.im ∧ z.im < b'})
    (hcont : ContinuousOn f {z : ℂ | 0 ≤ z.re ∧ z.re ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b})
    (h0 : f 0 = 0) (h1 : f a = a') (h2 : f (a + b * I) = a' + b' * I) (h3 : f (b * I) = b' * I) :
    ∀ y : ℝ, y ∈ Icc 0 b → (f ((y : ℂ) * I)).re = 0 ∧ (f ((a : ℂ) + (y : ℂ) * I)).re = a' := by
  have hR : {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b} = rectangle a b := rfl
  have hR' : {z : ℂ | 0 < z.re ∧ z.re < a' ∧ 0 < z.im ∧ z.im < b'} = rectangle a' b' := rfl
  rw [hR] at hf himg
  rw [hR'] at himg
  obtain ⟨F, hF⟩ := thm13_3_boundary_correspondence (isJordanDomain_rectangle ha hb)
    (isJordanDomain_rectangle ha' hb') ⟨K, hf⟩ himg
  -- `F = f` on the closed rectangle
  have hcl : closure (toExt (rectangle a b)) = toExt (Icc 0 a ×ℂ Icc 0 b) := closure_toExt_rectangle ha hb
  have hbar : Icc 0 a ×ℂ Icc 0 b ⊆ {z : ℂ | 0 ≤ z.re ∧ z.re ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b} := by
    intro z hz
    exact ⟨hz.1.1, hz.1.2, hz.2.1, hz.2.2⟩
  have hFf : ∀ z ∈ Icc 0 a ×ℂ Icc 0 b, F (z : ExtPlane) = ((f z : ℂ) : ExtPlane) := by
    have hsub : Icc 0 a ×ℂ Icc 0 b ⊆ closure (rectangle a b) := by
      rw [rectangle_eq_reProdIm, closure_reProdIm, closure_Ioo ha.ne, closure_Ioo hb.ne]
    have hc1 : ContinuousOn (fun z : ℂ => F (z : ExtPlane)) (Icc 0 a ×ℂ Icc 0 b) :=
      hF.2.1.comp OnePoint.continuous_coe.continuousOn fun z hz => by
        rw [hcl]
        exact mem_image_of_mem _ hz
    have hc2 : ContinuousOn (fun z : ℂ => ((f z : ℂ) : ExtPlane)) (Icc 0 a ×ℂ Icc 0 b) :=
      OnePoint.continuous_coe.comp_continuousOn (hcont.mono hbar)
    have hRsub : rectangle a b ⊆ Icc 0 a ×ℂ Icc 0 b := by
      intro z hz
      exact ⟨⟨hz.1.le, hz.2.1.le⟩, ⟨hz.2.2.1.le, hz.2.2.2.le⟩⟩
    exact Set.EqOn.of_subset_closure (fun z hz => hF.1 z hz) hc1 hc2 hRsub hsub
  have hv : ∀ i, F (rectVert a b i) = rectVert a' b' i := by
    intro i
    fin_cases i
    · show F ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane)
      rw [hFf 0 (by simp [mem_reProdIm, ha.le, hb.le]), h0]
    · show F (((a : ℝ) : ℂ) : ExtPlane) = (((a' : ℝ) : ℂ) : ExtPlane)
      rw [hFf _ (by simp [mem_reProdIm, ha.le, hb.le]), h1]
    · show F (((a : ℂ) + (b : ℂ) * I : ℂ) : ExtPlane) = (((a' : ℂ) + (b' : ℂ) * I : ℂ) : ExtPlane)
      rw [hFf _ (by simp [mem_reProdIm, ha.le, hb.le]), h2]
    · show F (((b : ℂ) * I : ℂ) : ExtPlane) = (((b' : ℂ) * I : ℂ) : ExtPlane)
      rw [hFf _ (by simp [mem_reProdIm, ha.le, hb.le]), h3]
  -- conjugate by `z ↦ i z̄` to exchange the vertical and the horizontal sides
  set e := rectSwapHomeomorph.onePointCongr with he
  have hmaps : MapsTo rectSwap (rectangle b a) (rectangle a b) := fun z hz => rectSwap_mem_rectangle hz
  have himg' : (rectSwap ∘ f ∘ rectSwap) '' rectangle b a = rectangle b' a' := by
    rw [image_comp, image_comp, rectSwap_image_rectangle, himg, rectSwap_image_rectangle]
  have htoExt : ∀ S : Set ℂ, e '' toExt S = toExt (rectSwap '' S) := fun S => by
    show e '' (((↑) : ℂ → ExtPlane) '' S) = ((↑) : ℂ → ExtPlane) '' (rectSwap '' S)
    rw [image_image, image_image]
    rfl
  have hcl1 : e '' closure (toExt (rectangle b a)) = closure (toExt (rectangle a b)) := by
    rw [Homeomorph.image_closure, htoExt, rectSwap_image_rectangle]
  have hcl2 : e '' closure (toExt (rectangle a' b')) = closure (toExt (rectangle b' a')) := by
    rw [Homeomorph.image_closure, htoExt, rectSwap_image_rectangle]
  have hemaps : MapsTo e (closure (toExt (rectangle b a))) (closure (toExt (rectangle a b))) :=
    fun p hp => by
      rw [← hcl1]
      exact mem_image_of_mem e hp
  have hH' : IsHomeoExtension (rectSwap ∘ f ∘ rectSwap) (rectangle b a) (rectangle b' a') (e ∘ F ∘ e) := by
    refine ⟨fun z hz => ?_, e.continuous.comp_continuousOn (hF.2.1.comp e.continuous.continuousOn hemaps),
      e.injective.injOn.comp (hF.2.2.1.comp e.injective.injOn hemaps) (mapsTo_univ _ _), ?_⟩
    · show e (F (OnePoint.map rectSwap (z : ExtPlane))) = _
      rw [OnePoint.map_some, hF.1 _ (hmaps hz)]
      rfl
    · rw [image_comp, image_comp, hcl1, hF.2.2.2, hcl2]
  have hvert : ∀ i, (e ∘ F ∘ e) (rectVert b a i) = rectVert b' a' i := fun i => by
    show OnePoint.map rectSwap (F (OnePoint.map rectSwap (rectVert b a i))) = _
    rw [rectSwap_rectVert a b i, hv, rectSwap_rectVert b' a', neg_neg]
  obtain ⟨hs0, hs1⟩ := rect_homeoExtension_sides hb ha hb' ha' himg' hH' hvert
  -- read off the real parts
  have hG : ∀ z ∈ Icc 0 a ×ℂ Icc 0 b,
      (e ∘ F ∘ e) ((rectSwap z : ℂ) : ExtPlane) = ((rectSwap (f z) : ℂ) : ExtPlane) := by
    intro z hz
    show OnePoint.map rectSwap (F (OnePoint.map rectSwap ((rectSwap z : ℂ) : ExtPlane))) = _
    rw [OnePoint.map_some, rectSwap_rectSwap, hFf z hz, OnePoint.map_some]
  have hre : ∀ w : ℂ, (rectSwap w).im = w.re := fun w => by
    show (I * conj w).im = w.re
    simp
  have hsw1 : ∀ y : ℝ, rectSwap ((y : ℂ) * I) = (y : ℂ) := fun y => by
    show I * conj ((y : ℂ) * I) = (y : ℂ)
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    linear_combination (-(y : ℂ)) * I_mul_I
  have hsw2 : ∀ y : ℝ, rectSwap ((a : ℂ) + (y : ℂ) * I) = (y : ℂ) + (a : ℂ) * I := fun y => by
    show I * conj ((a : ℂ) + (y : ℂ) * I) = (y : ℂ) + (a : ℂ) * I
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    linear_combination (-(y : ℂ)) * I_mul_I
  intro y hy
  constructor
  · have hz : ((y : ℂ) * I) ∈ Icc 0 a ×ℂ Icc 0 b := by
      simp [mem_reProdIm, ha.le, hy.1, hy.2]
    have hp : (((y : ℂ) : ℂ) : ExtPlane) ∈ toExt (Icc 0 b ×ℂ {0}) :=
      ⟨(y : ℂ), by simp [mem_reProdIm, hy.1, hy.2], rfl⟩
    have hq := hs0 ▸ mem_image_of_mem (e ∘ F ∘ e) hp
    rw [← hsw1 y, hG _ hz] at hq
    obtain ⟨w, hw, hwe⟩ := hq
    have hw' : w = rectSwap (f ((y : ℂ) * I)) := OnePoint.coe_injective hwe
    rw [← hre, ← hw']
    exact hw.2
  · have hz : ((a : ℂ) + (y : ℂ) * I) ∈ Icc 0 a ×ℂ Icc 0 b := by
      simp [mem_reProdIm, ha.le, hy.1, hy.2]
    have hp : (((y : ℂ) + (a : ℂ) * I : ℂ) : ExtPlane) ∈ toExt (Icc 0 b ×ℂ {a}) :=
      ⟨(y : ℂ) + (a : ℂ) * I, by simp [mem_reProdIm, hy.1, hy.2], rfl⟩
    have hq := hs1 ▸ mem_image_of_mem (e ∘ F ∘ e) hp
    rw [← hsw2 y, hG _ hz] at hq
    obtain ⟨w, hw, hwe⟩ := hq
    have hw' : w = rectSwap (f ((a : ℂ) + (y : ℂ) * I)) := OnePoint.coe_injective hwe
    rw [← hre, ← hw']
    exact hw.2

open LiZhongQC in
/-- Helper for `prop1_4` (§1.4), P3 data: at almost every point of `D` a `K`-quasiconformal map is differentiable
with `f_x = f_z + f_z̄`, `(|f_z| + |f_z̄|)² ≤ K J_f` and `J_f ≥ 0` (Theorems 9.3, 9.4), and `∬_D J_f ≤ m(f(D))`
(`lintegral_jacobian_le_volume_image`). -/
theorem gl1_gz_energy {D : Set ℂ} {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f D K) :
    (∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ f z ∧ partialX f z = dz f z + dzbar f z ∧
      partialY f z = I * (dz f z - dzbar f z) ∧
      (‖dz f z‖ + ‖dzbar f z‖) ^ 2 ≤ K * jacobian f z ∧ 0 ≤ jacobian f z) ∧
      ∫⁻ z in D, ENNReal.ofReal (jacobian f z) ≤ volume (f '' D) := by
  refine ⟨?_, lintegral_jacobian_le_volume_image hf hf.1.measurableSet subset_rfl⟩
  have hK : 1 ≤ K := hf.2.1
  filter_upwards [thm9_3_differentiable_ae hf, thm9_4_dilatation_ae hf] with z hd hk
  have hx : partialX f z = dz f z + dzbar f z := by
    rw [partialX_eq_of_differentiableAt hd]
    show fderiv ℝ f z 1 =
      (fderiv ℝ f z 1 - I * fderiv ℝ f z I) / 2 + (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2
    ring
  have hy : partialY f z = I * (dz f z - dzbar f z) := by
    rw [partialY_eq_of_differentiableAt hd]
    show fderiv ℝ f z I =
      I * ((fderiv ℝ f z 1 - I * fderiv ℝ f z I) / 2 - (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2)
    linear_combination (fderiv ℝ f z I) * I_mul_I
  have h0 : 0 ≤ ‖dz f z‖ + ‖dzbar f z‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hpq : 0 ≤ ‖dz f z‖ - ‖dzbar f z‖ := by
    by_contra hneg
    have : K * (‖dz f z‖ - ‖dzbar f z‖) < 0 := mul_neg_of_pos_of_neg (by linarith) (lt_of_not_ge hneg)
    linarith
  refine ⟨hd, hx, hy, ?_, ?_⟩
  · show (‖dz f z‖ + ‖dzbar f z‖) ^ 2 ≤ K * (‖dz f z‖ ^ 2 - ‖dzbar f z‖ ^ 2)
    nlinarith [mul_le_mul_of_nonneg_left hk h0]
  · show 0 ≤ ‖dz f z‖ ^ 2 - ‖dzbar f z‖ ^ 2
    nlinarith [mul_nonneg hpq h0]

/-- Helper for `prop1_4` (§1.4): Fubini on the rectangle, `∬_R h = ∫_0^b ∫_0^a h(t + iy) dt dy` for `h` integrable on
`R = (0, a) × (0, b)`; and `m(R) = ab`. -/
theorem gl1_gz_fubini {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    volume {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b} = ENNReal.ofReal (a * b) ∧
      ∀ h : ℂ → ℝ, IntegrableOn h {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b} →
        (∀ᵐ y : ℝ ∂(volume.restrict (Ioo 0 b)),
          IntegrableOn (fun t : ℝ => h ((t : ℂ) + (y : ℂ) * I)) (Ioo 0 a)) ∧
        ∫ z in {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b}, h z =
          ∫ y in Ioo (0 : ℝ) b, ∫ t in Ioo (0 : ℝ) a, h ((t : ℂ) + (y : ℂ) * I) := by
  have _hb := hb  -- not needed: `m(R) = ab` and Fubini only use `0 < a`
  have he := Complex.measurableEquivRealProd.symm.measurableEmbedding
  refine ⟨?_, fun h hh => ⟨?_, ?_⟩⟩
  · rw [show {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b} = LiZhongQC.rectangle a b from rfl,
      LiZhongQC.volume_rectangle, ENNReal.ofReal_mul ha.le]
  · have hi : Integrable (fun p => h (Complex.measurableEquivRealProd.symm p))
        ((volume.restrict (Ioo (0 : ℝ) a)).prod (volume.restrict (Ioo (0 : ℝ) b))) := by
      have h1 : Integrable h (Measure.map Complex.measurableEquivRealProd.symm
          ((volume.restrict (Ioo (0 : ℝ) a)).prod (volume.restrict (Ioo (0 : ℝ) b)))) := by
        rw [← LiZhongQC.volume_restrict_openRect_eq_map]
        exact hh
      exact he.integrable_map_iff.1 h1
    filter_upwards [hi.prod_left_ae] with y hy
    have e : (fun x => h (Complex.measurableEquivRealProd.symm (x, y))) =
        fun t : ℝ => h ((t : ℂ) + (y : ℂ) * I) := by
      funext t
      rw [LiZhongQC.measurableEquivRealProd_symm_apply']
    rw [e] at hy
    exact hy
  · exact LiZhongQC.fx_setIntegral_openRect_symm hh

open LiZhongQC in
/-- Helper for `prop1_4` (§1.4), P2: on almost every horizontal line the real part of the `x`-derivative integrates to
the width of the image, `∫_0^a Re f_x(t + iy) dt = Re f(a + iy) − Re f(iy) = a′`. The `y` used are those (a full-measure
set) for which `t ↦ f(t + iy)` is absolutely continuous on every `[1/n, a − 1/n]` with `1/n < y < b − 1/n` (ACL on the
countably many closed sub-rectangles `[1/n, a − 1/n] × [1/n, b − 1/n]`) and `t ↦ f_x(t + iy)` is integrable on `(0, a)`
(Fubini); for each such `y` the endpoint passage `n → ∞` uses only continuity of `f` on `R̄` and dominated
convergence. -/
theorem gl1_gz_line {a b a' K : ℝ} (ha : 0 < a) (hb : 0 < b) {f : ℂ → ℂ}
    (hf : IsKQC f {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b} K)
    (hcont : ContinuousOn f {z : ℂ | 0 ≤ z.re ∧ z.re ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b})
    (hpx : IntegrableOn (partialX f) {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b})
    (hsides : ∀ y : ℝ, y ∈ Icc 0 b → (f ((y : ℂ) * I)).re = 0 ∧ (f ((a : ℂ) + (y : ℂ) * I)).re = a') :
    ∀ᵐ y : ℝ ∂(volume.restrict (Ioo 0 b)), ∫ t in Ioo (0 : ℝ) a, (partialX f ((t : ℂ) + (y : ℂ) * I)).re = a' := by
  have hacl := (thm9_1_isACL hf).2
  set δ : ℕ → ℝ := fun n => min a b / ((n : ℝ) + 3) with hδdef
  have hm0 : 0 < min a b := lt_min ha hb
  have hδpos : ∀ n, 0 < δ n := fun n => div_pos hm0 (by positivity)
  have hδle : ∀ n, 3 * δ n ≤ min a b := by
    intro n
    show 3 * (min a b / ((n : ℝ) + 3)) ≤ min a b
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hm0.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hδa : ∀ n, 2 * δ n < a := fun n => by linarith [hδle n, min_le_left a b, hδpos n]
  have hδb : ∀ n, 2 * δ n < b := fun n => by linarith [hδle n, min_le_right a b, hδpos n]
  have hδt : Tendsto δ atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact tendsto_const_nhds.div_atTop h
  -- absolute continuity on almost every horizontal line of each closed sub-rectangle
  have hY : ∀ n, ∀ᵐ y : ℝ ∂(volume.restrict (Ioo 0 b)), y ∈ Ioo (δ n) (b - δ n) →
      AbsolutelyContinuousOnInterval (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (δ n) (a - δ n) := by
    intro n
    have hsub : closedRect (δ n) (a - δ n) (δ n) (b - δ n) ⊆
        {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b} := by
      intro z hz
      obtain ⟨h1, h2, h3, h4⟩ := hz
      have := hδpos n
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    have h := (hacl (δ n) (a - δ n) (δ n) (b - δ n) (by linarith [hδa n]) (by linarith [hδb n]) hsub).2
    exact ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).1 h)
  -- integrability on almost every horizontal line
  have hint := ((gl1_gz_fubini ha hb).2 (fun z => ‖partialX f z‖) (Integrable.norm hpx)).1
  filter_upwards [ae_all_iff.2 hY, hint, ae_restrict_mem measurableSet_Ioo] with y hyY hyint hy
  set φ : ℝ → ℂ := fun x => f ((x : ℂ) + (y : ℂ) * I) with hφ
  have hg : ∀ t : ℝ, deriv φ t = partialX f ((t : ℂ) + (y : ℂ) * I) := by
    intro t
    show deriv φ t = deriv (fun s : ℝ => f ((t : ℂ) + (y : ℂ) * I + (s : ℂ))) 0
    have e : (fun s : ℝ => f ((t : ℂ) + (y : ℂ) * I + (s : ℂ))) = fun s => φ (t + s) := by
      funext s
      show f ((t : ℂ) + (y : ℂ) * I + (s : ℂ)) = f (((t + s : ℝ) : ℂ) + (y : ℂ) * I)
      congr 1
      push_cast
      ring
    rw [e, deriv_comp_const_add φ t 0, add_zero]
  have hgi : IntegrableOn (deriv φ) (Ioo 0 a) := by
    refine Integrable.mono' hyint (measurable_deriv φ).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    show ‖deriv φ t‖ ≤ ‖partialX f ((t : ℂ) + (y : ℂ) * I)‖
    rw [hg t]
  -- the extension by zero of `Re f_x` on the line
  set G : ℝ → ℝ := (Ioo (0 : ℝ) a).indicator (fun t => (deriv φ t).re) with hGdef
  have hGi : Integrable G := (integrable_indicator_iff measurableSet_Ioo).2 hgi.re
  have hprim : Continuous fun t => ∫ x in (0 : ℝ)..t, G x :=
    intervalIntegral.continuous_primitive (fun _ _ => hGi.intervalIntegrable) 0
  have hGint : ∫ t in Ioo (0 : ℝ) a, (deriv φ t).re = ∫ x in (0 : ℝ)..a, G x := by
    rw [intervalIntegral.integral_of_le ha.le, integral_Ioc_eq_integral_Ioo, hGdef,
      setIntegral_indicator measurableSet_Ioo, inter_self]
  -- the fundamental theorem of calculus on the sub-segments
  have hftc : ∀ᶠ n in atTop, ∫ x in (δ n)..(a - δ n), G x = (φ (a - δ n)).re - (φ (δ n)).re := by
    have e1 := hδt.eventually (gt_mem_nhds hy.1)
    have e2 := hδt.eventually (gt_mem_nhds (sub_pos.2 hy.2))
    filter_upwards [e1, e2] with n hn1 hn2
    have hac := hyY n ⟨hn1, by linarith⟩
    have hsub : uIcc (δ n) (a - δ n) ⊆ Ioo 0 a := by
      rw [uIcc_of_le (by linarith [hδa n])]
      intro x hx
      exact ⟨by linarith [hx.1, hδpos n], by linarith [hx.2, hδpos n]⟩
    have hgi' : IntervalIntegrable (deriv φ) volume (δ n) (a - δ n) :=
      (hgi.mono_set hsub).intervalIntegrable
    calc ∫ x in (δ n)..(a - δ n), G x = ∫ x in (δ n)..(a - δ n), Complex.reCLM (deriv φ x) := by
          refine intervalIntegral.integral_congr fun x hx => ?_
          rw [Complex.reCLM_apply]
          exact indicator_of_mem (hsub hx) _
      _ = Complex.reCLM (∫ x in (δ n)..(a - δ n), deriv φ x) := Complex.reCLM.intervalIntegral_comp_comm hgi'
      _ = (φ (a - δ n)).re - (φ (δ n)).re := by
          rw [integral_deriv_eq_sub_of_absolutelyContinuous hac, Complex.reCLM_apply, sub_re]
  -- the two limits
  have hL : Tendsto (fun n => ∫ x in (δ n)..(a - δ n), G x) atTop (𝓝 (∫ x in (0 : ℝ)..a, G x)) := by
    have h1 : Tendsto (fun n => (∫ x in (0 : ℝ)..(a - δ n), G x) - ∫ x in (0 : ℝ)..(δ n), G x) atTop
        (𝓝 ((∫ x in (0 : ℝ)..(a - 0), G x) - ∫ x in (0 : ℝ)..0, G x)) :=
      ((hprim.tendsto _).comp ((tendsto_const_nhds (x := a)).sub hδt)).sub ((hprim.tendsto _).comp hδt)
    rw [sub_zero, intervalIntegral.integral_same, sub_zero] at h1
    refine h1.congr fun n => ?_
    exact intervalIntegral.integral_interval_sub_left hGi.intervalIntegrable hGi.intervalIntegrable
  have hyb : y ∈ Icc 0 b := ⟨hy.1.le, hy.2.le⟩
  have hR : Tendsto (fun n => (φ (a - δ n)).re - (φ (δ n)).re) atTop (𝓝 (a' - 0)) := by
    have hbar1 : (a : ℂ) + (y : ℂ) * I ∈ {z : ℂ | 0 ≤ z.re ∧ z.re ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b} := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith [hy.1, hy.2]
    have hbar0 : (y : ℂ) * I ∈ {z : ℂ | 0 ≤ z.re ∧ z.re ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b} := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith [hy.1, hy.2]
    have hmem1 : ∀ n, ((a - δ n : ℝ) : ℂ) + (y : ℂ) * I ∈
        {z : ℂ | 0 ≤ z.re ∧ z.re ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b} := fun n => by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith [hy.1, hy.2, hδpos n, hδa n]
    have hmem0 : ∀ n, ((δ n : ℝ) : ℂ) + (y : ℂ) * I ∈
        {z : ℂ | 0 ≤ z.re ∧ z.re ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b} := fun n => by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith [hy.1, hy.2, hδpos n, hδa n]
    have hz1 : Tendsto (fun n => ((a - δ n : ℝ) : ℂ) + (y : ℂ) * I) atTop (𝓝 ((a : ℂ) + (y : ℂ) * I)) := by
      have h := ((Complex.continuous_ofReal.tendsto _).comp ((tendsto_const_nhds (x := a)).sub hδt)).add_const
        ((y : ℂ) * I)
      simpa using h
    have hz0 : Tendsto (fun n => ((δ n : ℝ) : ℂ) + (y : ℂ) * I) atTop (𝓝 ((y : ℂ) * I)) := by
      have h := ((Complex.continuous_ofReal.tendsto _).comp hδt).add_const ((y : ℂ) * I)
      simpa using h
    have hf1 : Tendsto (fun n => f (((a - δ n : ℝ) : ℂ) + (y : ℂ) * I)) atTop
        (𝓝 (f ((a : ℂ) + (y : ℂ) * I))) :=
      (hcont _ hbar1).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hz1, Eventually.of_forall hmem1⟩)
    have hf0 : Tendsto (fun n => f (((δ n : ℝ) : ℂ) + (y : ℂ) * I)) atTop (𝓝 (f ((y : ℂ) * I))) :=
      (hcont _ hbar0).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hz0, Eventually.of_forall hmem0⟩)
    have h := ((Complex.continuous_re.tendsto _).comp hf1).sub ((Complex.continuous_re.tendsto _).comp hf0)
    rw [(hsides y hyb).1, (hsides y hyb).2] at h
    exact h
  have hfin := tendsto_nhds_unique (hL.congr' hftc) hR
  have e : ∫ t in Ioo (0 : ℝ) a, (partialX f ((t : ℂ) + (y : ℂ) * I)).re =
      ∫ t in Ioo (0 : ℝ) a, (deriv φ t).re := by
    simp_rw [hg]
  rw [e, hGint, hfin, sub_zero]

/-- Helper for `prop1_4` (§1.4), P4: the equality case of the length–area chain, as an abstract statement. On a set `S`
of measure `A`, if `v ≤ u ≤ w` and `w² ≤ K J` a.e., `∬_S v = B`, `∬_S J ≤ C` and `B² = K A C`, then all the
inequalities are equalities a.e. and `w = B/A` a.e. (`∬_S (w − B/A)² = ∬ w² − 2(B/A) ∬ w + B²/A ≤ K C − B²/A = 0`, then
`∬ (w − u) = ∬ (u − v) = ∬ (K J − w²) = 0` with nonnegative integrands). -/
theorem gl1_gz_equality {S : Set ℂ} {u v w J : ℂ → ℝ} {A B C K : ℝ} (hA : 0 < A) (hB : 0 < B) (hK : 0 < K)
    (hS : volume S = ENNReal.ofReal A) (hv : IntegrableOn v S) (hu : IntegrableOn u S) (hw : IntegrableOn w S)
    (hw2 : IntegrableOn (fun z => w z ^ 2) S) (hJ : IntegrableOn J S)
    (hle : ∀ᵐ z ∂(volume.restrict S), v z ≤ u z ∧ u z ≤ w z ∧ w z ^ 2 ≤ K * J z)
    (hvB : ∫ z in S, v z = B) (hJC : ∫ z in S, J z ≤ C) (hratio : B ^ 2 = K * A * C) :
    ∀ᵐ z ∂(volume.restrict S), v z = u z ∧ u z = w z ∧ w z = B / A ∧ w z ^ 2 = K * J z := by
  have hv' : Integrable v (volume.restrict S) := hv
  have hu' : Integrable u (volume.restrict S) := hu
  have hw' : Integrable w (volume.restrict S) := hw
  have hw2' : Integrable (fun z => w z ^ 2) (volume.restrict S) := hw2
  have hJ' : Integrable J (volume.restrict S) := hJ
  have hfin : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ, hS]; exact ENNReal.ofReal_lt_top⟩
  have hconst : ∀ c : ℝ, ∫ _ in S, c = A * c := by
    intro c
    rw [setIntegral_const, measureReal_def, hS, ENNReal.toReal_ofReal hA.le, smul_eq_mul]
  have hmA : B / A * A = B := div_mul_cancel₀ B hA.ne'
  have hm : 0 < B / A := div_pos hB hA
  have hKC : K * C = B / A * B := by
    rw [div_mul_eq_mul_div, eq_div_iff hA.ne']
    linear_combination -hratio
  have hvu : ∫ z in S, v z ≤ ∫ z in S, u z := integral_mono_ae hv' hu' (hle.mono fun z h => h.1)
  have huw : ∫ z in S, u z ≤ ∫ z in S, w z := integral_mono_ae hu' hw' (hle.mono fun z h => h.2.1)
  have hw2J : ∫ z in S, w z ^ 2 ≤ ∫ z in S, K * J z :=
    integral_mono_ae hw2' (hJ'.const_mul K) (hle.mono fun z h => h.2.2)
  rw [integral_const_mul] at hw2J
  have hKJC : K * ∫ z in S, J z ≤ K * C := mul_le_mul_of_nonneg_left hJC hK.le
  -- the variance identity
  have hvari : Integrable (fun z => (w z - B / A) ^ 2) (volume.restrict S) := by
    have e1 : (fun z => (w z - B / A) ^ 2) = fun z => (w z ^ 2 - 2 * (B / A) * w z) + (B / A) ^ 2 := by
      funext z
      ring
    rw [e1]
    exact (hw2'.sub (hw'.const_mul _)).add (integrable_const _)
  have hvar : ∫ z in S, (w z - B / A) ^ 2 =
      (∫ z in S, w z ^ 2) - 2 * (B / A) * (∫ z in S, w z) + A * (B / A) ^ 2 := by
    have e1 : (fun z => (w z - B / A) ^ 2) = fun z => (w z ^ 2 - 2 * (B / A) * w z) + (B / A) ^ 2 := by
      funext z
      ring
    have hi1 : Integrable (fun z => w z ^ 2 - 2 * (B / A) * w z) (volume.restrict S) :=
      hw2'.sub (hw'.const_mul _)
    have hi2 : Integrable (fun z => 2 * (B / A) * w z) (volume.restrict S) := hw'.const_mul _
    rw [e1, integral_add hi1 (integrable_const _), integral_sub hw2' hi2, integral_const_mul, hconst]
  have hBw : B ≤ ∫ z in S, w z := hvB ▸ hvu.trans huw
  have hmw : B / A * B ≤ B / A * ∫ z in S, w z := mul_le_mul_of_nonneg_left hBw hm.le
  have hsq : A * (B / A) ^ 2 = B / A * B := by
    calc A * (B / A) ^ 2 = B / A * A * (B / A) := by ring
      _ = B / A * B := by rw [hmA]; ring
  have hvar0 : ∫ z in S, (w z - B / A) ^ 2 = 0 := by
    refine le_antisymm ?_ (integral_nonneg fun z => sq_nonneg _)
    rw [hvar]
    nlinarith
  have hwm : ∀ᵐ z ∂(volume.restrict S), w z = B / A := by
    have h := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun z => sq_nonneg _) hvari).mp hvar0
    filter_upwards [h] with z hz
    have hz' : (w z - B / A) ^ 2 = 0 := hz
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hz')
  have hwB : ∫ z in S, w z = B := by
    rw [integral_congr_ae hwm, hconst]
    rw [mul_comm]
    exact hmA
  -- `u = w`
  have huw' : ∀ᵐ z ∂(volume.restrict S), u z = w z := by
    have h0 : ∫ z in S, (w z - u z) = 0 := by
      refine le_antisymm ?_ (integral_nonneg_of_ae (hle.mono fun z h => sub_nonneg.mpr h.2.1))
      rw [integral_sub hw' hu']
      linarith
    have h := (integral_eq_zero_iff_of_nonneg_ae (hle.mono fun z h => sub_nonneg.mpr h.2.1)
      (hw'.sub hu')).mp h0
    filter_upwards [h] with z hz
    have hz' : w z - u z = 0 := hz
    linarith
  -- `v = u`
  have hvu' : ∀ᵐ z ∂(volume.restrict S), v z = u z := by
    have h0 : ∫ z in S, (u z - v z) = 0 := by
      refine le_antisymm ?_ (integral_nonneg_of_ae (hle.mono fun z h => sub_nonneg.mpr h.1))
      rw [integral_sub hu' hv']
      linarith
    have h := (integral_eq_zero_iff_of_nonneg_ae (hle.mono fun z h => sub_nonneg.mpr h.1)
      (hu'.sub hv')).mp h0
    filter_upwards [h] with z hz
    have hz' : u z - v z = 0 := hz
    linarith
  -- `w² = K J`
  have hwJ : ∀ᵐ z ∂(volume.restrict S), w z ^ 2 = K * J z := by
    have hw2B : ∫ z in S, w z ^ 2 = B / A * B := by
      rw [integral_congr_ae (hwm.mono fun z hz => show w z ^ 2 = (B / A) ^ 2 by rw [hz]), hconst]
      exact hsq
    have h0 : ∫ z in S, (K * J z - w z ^ 2) = 0 := by
      refine le_antisymm ?_ (integral_nonneg_of_ae (hle.mono fun z h => sub_nonneg.mpr h.2.2))
      rw [integral_sub (hJ'.const_mul K) hw2', integral_const_mul]
      linarith
    have h := (integral_eq_zero_iff_of_nonneg_ae (hle.mono fun z h => sub_nonneg.mpr h.2.2)
      ((hJ'.const_mul K).sub hw2')).mp h0
    filter_upwards [h] with z hz
    have hz' : K * J z - w z ^ 2 = 0 := hz
    linarith
  filter_upwards [hwm, huw', hvu', hwJ] with z h1 h2 h3 h4
  exact ⟨h3, h2, h1, h4⟩

/-- Helper for `prop1_4` (§1.4), P4 at a point: if `α + β` is real and nonnegative, `|α + β| = |α| + |β| = m > 0` and
`(|α| + |β|)² = K (|α|² − |β|²)`, then `α = m/(1 + k)` and `β = k m/(1 + k)`, `k = (K − 1)/(K + 1)`. -/
theorem gl1_gz_pointwise {α β : ℂ} {m K : ℝ} (hm : 0 < m) (hK : 1 ≤ K) (h1 : (α + β).re = ‖α + β‖)
    (h2 : ‖α + β‖ = ‖α‖ + ‖β‖) (h3 : ‖α‖ + ‖β‖ = m) (h4 : (‖α‖ + ‖β‖) ^ 2 = K * (‖α‖ ^ 2 - ‖β‖ ^ 2)) :
    α = ((m / (1 + (K - 1) / (K + 1)) : ℝ) : ℂ) ∧
      β = (((K - 1) / (K + 1) * (m / (1 + (K - 1) / (K + 1))) : ℝ) : ℂ) := by
  have hK0 : 0 < K := by linarith
  have hK1 : K + 1 ≠ 0 := by linarith
  have hKne : K ≠ 0 := hK0.ne'
  have hpq : K * (‖α‖ - ‖β‖) = m := by
    have e : m * m = K * (‖α‖ - ‖β‖) * m := by
      calc m * m = (‖α‖ + ‖β‖) ^ 2 := by rw [h3]; ring
        _ = K * (‖α‖ ^ 2 - ‖β‖ ^ 2) := h4
        _ = K * (‖α‖ - ‖β‖) * (‖α‖ + ‖β‖) := by ring
        _ = K * (‖α‖ - ‖β‖) * m := by rw [h3]
    exact (mul_right_cancel₀ hm.ne' e).symm
  have hα0 : α ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpq
    nlinarith [norm_nonneg β]
  obtain ⟨r, hr0, hr⟩ := (sameRay_iff_norm_add.mpr h2).exists_nonneg_left hα0
  have hsim : (α + β).im = 0 :=
    Complex.abs_re_eq_norm.mp (by rw [h1, abs_of_nonneg (norm_nonneg _)])
  have hs : α + β = (m : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re, h1, h2, h3]
    · rw [Complex.ofReal_im]
      exact hsim
  have hβr : β = (r : ℂ) * α := by rw [← hr, Complex.real_smul]
  have h1r : (1 + r : ℝ) ≠ 0 := by linarith
  have hαv : α = ((m / (1 + r) : ℝ) : ℂ) := by
    have e : ((1 + r : ℝ) : ℂ) * α = m := by
      rw [← hs, hβr]
      push_cast
      ring
    rw [Complex.ofReal_div, eq_div_iff (Complex.ofReal_ne_zero.mpr h1r), mul_comm, e]
  have hnn : 0 ≤ m / (1 + r) := div_nonneg hm.le (by linarith)
  have hβv : β = ((r * (m / (1 + r)) : ℝ) : ℂ) := by
    rw [hβr, hαv]
    push_cast
    ring
  have hα : α = (‖α‖ : ℂ) := by
    conv_rhs => rw [hαv]
    rw [Complex.norm_real, Real.norm_of_nonneg hnn]
    exact hαv
  have hβ : β = (‖β‖ : ℂ) := by
    conv_rhs => rw [hβv]
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hr0 hnn)]
    exact hβv
  have hpv : ‖α‖ = m / (1 + (K - 1) / (K + 1)) := by
    have e : 1 + (K - 1) / (K + 1) = 2 * K / (K + 1) := by
      rw [eq_div_iff hK1]
      field_simp
      ring
    rw [e, div_div_eq_mul_div, eq_div_iff (mul_ne_zero two_ne_zero hKne)]
    linear_combination K * h3 + hpq
  have hqv : ‖β‖ = (K - 1) / (K + 1) * (m / (1 + (K - 1) / (K + 1))) := by
    rw [← hpv, div_mul_eq_mul_div, eq_div_iff hK1]
    linear_combination h3 - hpq
  constructor
  · rw [hα, hpv]
  · rw [hβ, hqv]

open LiZhongQC in
/-- Helper for `prop1_4` (§1.4), P5: an ACL map of `R` whose partials are a.e. those of the affine map
`z ↦ c z + d z̄` (`f_x = c + d`, `f_y = i(c − d)`) differs from it by a constant on `R` (on almost every horizontal and
vertical segment the difference is absolutely continuous with zero derivative, hence constant; continuity fills in the
remaining segments). -/
theorem gl1_gz_rigid {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {f : ℂ → ℂ} {c d : ℂ}
    (hacl : IsACL f {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b})
    (hx : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b}), partialX f z = c + d)
    (hy : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b}),
      partialY f z = I * (c - d)) :
    ∃ e : ℂ, ∀ z ∈ {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b}, f z = c * z + d * conj z + e := by
  set h : ℂ → ℂ := fun z => f z - (c * z + d * conj z) with hh
  have hlin : Continuous fun z : ℂ => c * z + d * conj z :=
    (continuous_const.mul continuous_id).add (continuous_const.mul Complex.continuous_conj)
  have hhc : ContinuousOn h {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b} :=
    hacl.1.sub hlin.continuousOn
  have hconj : ∀ x y : ℝ, conj ((x : ℂ) + (y : ℂ) * I) = (x : ℂ) - (y : ℂ) * I := fun x y => by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  -- Fubini for the null sets of the two a.e. statements
  obtain ⟨sx, hsx, hsxm, hsxP⟩ := hx.exists_measurable_mem
  obtain ⟨sy, hsy, hsym, hsyP⟩ := hy.exists_measurable_mem
  have hxl : ∀ᵐ y : ℝ ∂(volume.restrict (Ioo 0 b)), ∀ᵐ x : ℝ ∂(volume.restrict (Ioo 0 a)),
      (x : ℂ) + (y : ℂ) * I ∈ sx :=
    s13x_rm2_ae_ae_of_ae_rect_symm (P := fun z => z ∈ sx) (a := 0) (b := a) (c := 0) (d := b) hsxm hsx
  have hyl : ∀ᵐ x : ℝ ∂(volume.restrict (Ioo 0 a)), ∀ᵐ y : ℝ ∂(volume.restrict (Ioo 0 b)),
      (x : ℂ) + (y : ℂ) * I ∈ sy :=
    s13x_rm2_ae_ae_of_ae_rect (P := fun z => z ∈ sy) (a := 0) (b := a) (c := 0) (d := b) hsym hsy
  -- the closed sub-rectangles
  set δ : ℕ → ℝ := fun n => min a b / ((n : ℝ) + 3) with hδdef
  have hm0 : 0 < min a b := lt_min ha hb
  have hδpos : ∀ n, 0 < δ n := fun n => div_pos hm0 (by positivity)
  have hδle : ∀ n, 3 * δ n ≤ min a b := by
    intro n
    show 3 * (min a b / ((n : ℝ) + 3)) ≤ min a b
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hm0.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hδa : ∀ n, 2 * δ n < a := fun n => by linarith [hδle n, min_le_left a b, hδpos n]
  have hδb : ∀ n, 2 * δ n < b := fun n => by linarith [hδle n, min_le_right a b, hδpos n]
  have hδt : Tendsto δ atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact tendsto_const_nhds.div_atTop h
  have hsub : ∀ n, closedRect (δ n) (a - δ n) (δ n) (b - δ n) ⊆
      {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b} := by
    intro n z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    have := hδpos n
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hmemR : ∀ x y : ℝ, 0 < x → x < a → 0 < y → y < b →
      (x : ℂ) + (y : ℂ) * I ∈ {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b} := by
    intro x y h1 h2 h3 h4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
  have hlineH : ∀ x : ℝ, Continuous fun y : ℝ => (x : ℂ) + (y : ℂ) * I := fun x =>
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hlineV : ∀ y : ℝ, Continuous fun x : ℝ => (x : ℂ) + (y : ℂ) * I := fun y =>
    Complex.continuous_ofReal.add continuous_const
  -- horizontal segments: `h(x + iy) = h(a/2 + iy)`
  have hhor : ∀ n, ∀ y ∈ Ioo (δ n) (b - δ n), ∀ x ∈ Icc (δ n) (a - δ n),
      h ((x : ℂ) + (y : ℂ) * I) = h (((a / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
    intro n
    have hae : ∀ᵐ y : ℝ ∂(volume.restrict (Ioo (δ n) (b - δ n))), ∀ x ∈ Icc (δ n) (a - δ n),
        h ((x : ℂ) + (y : ℂ) * I) = h (((a / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
      have hAC := (hacl.2 (δ n) (a - δ n) (δ n) (b - δ n) (by linarith [hδa n]) (by linarith [hδb n])
        (hsub n)).2
      have hxl' : ∀ᵐ y : ℝ ∂(volume.restrict (Ioo (δ n) (b - δ n))),
          ∀ᵐ x : ℝ ∂(volume.restrict (Ioo 0 a)), (x : ℂ) + (y : ℂ) * I ∈ sx :=
        ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo (hδpos n).le (by linarith [hδpos n])) hxl
      filter_upwards [hAC, hxl'] with y hyAC hyx
      intro x hx
      set φ : ℝ → ℂ := fun t => f ((t : ℂ) + (y : ℂ) * I) with hφ
      have hderiv : ∀ t : ℝ, deriv φ t = partialX f ((t : ℂ) + (y : ℂ) * I) := by
        intro t
        show deriv φ t = deriv (fun s : ℝ => f ((t : ℂ) + (y : ℂ) * I + (s : ℂ))) 0
        have e : (fun s : ℝ => f ((t : ℂ) + (y : ℂ) * I + (s : ℂ))) = fun s => φ (t + s) := by
          funext s
          show f ((t : ℂ) + (y : ℂ) * I + (s : ℂ)) = f (((t + s : ℝ) : ℂ) + (y : ℂ) * I)
          congr 1
          push_cast
          ring
        rw [e, deriv_comp_const_add φ t 0, add_zero]
      have hsubI : uIcc (a / 2) x ⊆ Icc (δ n) (a - δ n) := by
        exact uIcc_subset_Icc ⟨by linarith [hδa n], by linarith [hδa n]⟩ hx
      have hac' : AbsolutelyContinuousOnInterval φ (a / 2) x :=
        hyAC.mono (hsubI.trans (by rw [uIcc_of_le (by linarith [hδa n])]))
      have hint : ∫ t in (a / 2)..x, deriv φ t = ∫ t in (a / 2)..x, (c + d) := by
        refine intervalIntegral.integral_congr_ae ?_
        have h1 := (ae_restrict_iff' measurableSet_Ioo).1 hyx
        filter_upwards [h1] with t ht htI
        rw [hderiv]
        apply hsxP
        apply ht
        have := hsubI (uIoc_subset_uIcc htI)
        exact ⟨by linarith [this.1, hδpos n], by linarith [this.2, hδpos n]⟩
      rw [integral_deriv_eq_sub_of_absolutelyContinuous hac', intervalIntegral.integral_const,
        Complex.real_smul] at hint
      show f ((x : ℂ) + (y : ℂ) * I) - (c * ((x : ℂ) + (y : ℂ) * I) + d * conj ((x : ℂ) + (y : ℂ) * I)) =
        f (((a / 2 : ℝ) : ℂ) + (y : ℂ) * I) -
          (c * (((a / 2 : ℝ) : ℂ) + (y : ℂ) * I) + d * conj (((a / 2 : ℝ) : ℂ) + (y : ℂ) * I))
      rw [hconj, hconj]
      have hint' : f ((x : ℂ) + (y : ℂ) * I) - f (((a / 2 : ℝ) : ℂ) + (y : ℂ) * I) =
          ((x - a / 2 : ℝ) : ℂ) * (c + d) := hint
      push_cast at hint' ⊢
      linear_combination hint'
    intro y hy x hx
    have hc1 : ContinuousOn (fun y : ℝ => h ((x : ℂ) + (y : ℂ) * I)) (Ioo (δ n) (b - δ n)) :=
      hhc.comp (hlineH x).continuousOn fun y hy' =>
        hmemR x y (by linarith [hx.1, hδpos n]) (by linarith [hx.2, hδpos n]) (by linarith [hy'.1, hδpos n])
          (by linarith [hy'.2, hδpos n])
    have hc2 : ContinuousOn (fun y : ℝ => h (((a / 2 : ℝ) : ℂ) + (y : ℂ) * I)) (Ioo (δ n) (b - δ n)) :=
      hhc.comp (hlineH (a / 2)).continuousOn fun y hy' =>
        hmemR (a / 2) y (by linarith) (by linarith) (by linarith [hy'.1, hδpos n]) (by linarith [hy'.2, hδpos n])
    exact MeasureTheory.Measure.eqOn_open_of_ae_eq (hae.mono fun y hy' => hy' x hx) isOpen_Ioo hc1 hc2 hy
  -- vertical segments: `h(x + iy) = h(x + i b/2)`
  have hver : ∀ n, ∀ x ∈ Ioo (δ n) (a - δ n), ∀ y ∈ Icc (δ n) (b - δ n),
      h ((x : ℂ) + (y : ℂ) * I) = h ((x : ℂ) + ((b / 2 : ℝ) : ℂ) * I) := by
    intro n
    have hae : ∀ᵐ x : ℝ ∂(volume.restrict (Ioo (δ n) (a - δ n))), ∀ y ∈ Icc (δ n) (b - δ n),
        h ((x : ℂ) + (y : ℂ) * I) = h ((x : ℂ) + ((b / 2 : ℝ) : ℂ) * I) := by
      have hAC := (hacl.2 (δ n) (a - δ n) (δ n) (b - δ n) (by linarith [hδa n]) (by linarith [hδb n])
        (hsub n)).1
      have hyl' : ∀ᵐ x : ℝ ∂(volume.restrict (Ioo (δ n) (a - δ n))),
          ∀ᵐ y : ℝ ∂(volume.restrict (Ioo 0 b)), (x : ℂ) + (y : ℂ) * I ∈ sy :=
        ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo (hδpos n).le (by linarith [hδpos n])) hyl
      filter_upwards [hAC, hyl'] with x hxAC hxy
      intro y hy
      set ψ : ℝ → ℂ := fun t => f ((x : ℂ) + (t : ℂ) * I) with hψ
      have hderiv : ∀ t : ℝ, deriv ψ t = partialY f ((x : ℂ) + (t : ℂ) * I) := by
        intro t
        show deriv ψ t = deriv (fun s : ℝ => f ((x : ℂ) + (t : ℂ) * I + (s : ℂ) * I)) 0
        have e : (fun s : ℝ => f ((x : ℂ) + (t : ℂ) * I + (s : ℂ) * I)) = fun s => ψ (t + s) := by
          funext s
          show f ((x : ℂ) + (t : ℂ) * I + (s : ℂ) * I) = f ((x : ℂ) + ((t + s : ℝ) : ℂ) * I)
          congr 1
          push_cast
          ring
        rw [e, deriv_comp_const_add ψ t 0, add_zero]
      have hsubI : uIcc (b / 2) y ⊆ Icc (δ n) (b - δ n) := by
        exact uIcc_subset_Icc ⟨by linarith [hδb n], by linarith [hδb n]⟩ hy
      have hac' : AbsolutelyContinuousOnInterval ψ (b / 2) y :=
        hxAC.mono (hsubI.trans (by rw [uIcc_of_le (by linarith [hδb n])]))
      have hint : ∫ t in (b / 2)..y, deriv ψ t = ∫ t in (b / 2)..y, I * (c - d) := by
        refine intervalIntegral.integral_congr_ae ?_
        have h1 := (ae_restrict_iff' measurableSet_Ioo).1 hxy
        filter_upwards [h1] with t ht htI
        rw [hderiv]
        apply hsyP
        apply ht
        have := hsubI (uIoc_subset_uIcc htI)
        exact ⟨by linarith [this.1, hδpos n], by linarith [this.2, hδpos n]⟩
      rw [integral_deriv_eq_sub_of_absolutelyContinuous hac', intervalIntegral.integral_const,
        Complex.real_smul] at hint
      show f ((x : ℂ) + (y : ℂ) * I) - (c * ((x : ℂ) + (y : ℂ) * I) + d * conj ((x : ℂ) + (y : ℂ) * I)) =
        f ((x : ℂ) + ((b / 2 : ℝ) : ℂ) * I) -
          (c * ((x : ℂ) + ((b / 2 : ℝ) : ℂ) * I) + d * conj ((x : ℂ) + ((b / 2 : ℝ) : ℂ) * I))
      rw [hconj, hconj]
      have hint' : f ((x : ℂ) + (y : ℂ) * I) - f ((x : ℂ) + ((b / 2 : ℝ) : ℂ) * I) =
          ((y - b / 2 : ℝ) : ℂ) * (I * (c - d)) := hint
      push_cast at hint' ⊢
      linear_combination hint'
    intro x hx y hy
    have hc1 : ContinuousOn (fun x : ℝ => h ((x : ℂ) + (y : ℂ) * I)) (Ioo (δ n) (a - δ n)) :=
      hhc.comp (hlineV y).continuousOn fun x hx' =>
        hmemR x y (by linarith [hx'.1, hδpos n]) (by linarith [hx'.2, hδpos n]) (by linarith [hy.1, hδpos n])
          (by linarith [hy.2, hδpos n])
    have hc2 : ContinuousOn (fun x : ℝ => h ((x : ℂ) + ((b / 2 : ℝ) : ℂ) * I)) (Ioo (δ n) (a - δ n)) :=
      hhc.comp (hlineV (b / 2)).continuousOn fun x hx' =>
        hmemR x (b / 2) (by linarith [hx'.1, hδpos n]) (by linarith [hx'.2, hδpos n]) (by linarith) (by linarith)
    exact MeasureTheory.Measure.eqOn_open_of_ae_eq (hae.mono fun x hx' => hx' y hy) isOpen_Ioo hc1 hc2 hx
  -- every point of `R` lies in some sub-rectangle
  refine ⟨h (((a / 2 : ℝ) : ℂ) + ((b / 2 : ℝ) : ℂ) * I), fun z hz => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hpos : 0 < min (min z.re (a - z.re)) (min z.im (b - z.im)) :=
    lt_min (lt_min h1 (by linarith)) (lt_min h3 (by linarith))
  obtain ⟨n, hn⟩ := (hδt.eventually (gt_mem_nhds hpos)).exists
  have hn1 : δ n < z.re := lt_of_lt_of_le hn ((min_le_left _ _).trans (min_le_left _ _))
  have hn2 : δ n < a - z.re := lt_of_lt_of_le hn ((min_le_left _ _).trans (min_le_right _ _))
  have hn3 : δ n < z.im := lt_of_lt_of_le hn ((min_le_right _ _).trans (min_le_left _ _))
  have hn4 : δ n < b - z.im := lt_of_lt_of_le hn ((min_le_right _ _).trans (min_le_right _ _))
  have e1 := hhor n z.im ⟨hn3, by linarith⟩ z.re ⟨hn1.le, by linarith⟩
  have e2 := hver n (a / 2) ⟨by linarith [hδa n], by linarith [hδa n]⟩ z.im ⟨hn3.le, by linarith⟩
  have e3 := e1.trans e2
  rw [Complex.re_add_im] at e3
  have e4 : f z - (c * z + d * conj z) = h (((a / 2 : ℝ) : ℂ) + ((b / 2 : ℝ) : ℂ) * I) := e3
  linear_combination e4

/-- **Proposition 4** (§1.4, l. 744). Let `R = (0, a) × (0, b)` and `R′ = (0, a′) × (0, b′)` with `a′/b′ = K a/b`, and
let `f` be a side-preserving `K`-quasiconformal map of `R` onto `R′` (continuous on `R̄`, mapping the vertices
`0, a, a + ib, ib` to `0, a′, a′ + ib′, ib′`). Then `f(z) = (b′/b)(z + k z̄)/(1 − k)`, `k = (K − 1)/(K + 1)`. -/
theorem prop1_4 {a b a' b' K : ℝ} (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b') (hK : 1 ≤ K)
    (hratio : a' / b' = K * (a / b)) {f : ℂ → ℂ}
    (hf : IsKQC f {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b} K)
    (himg : f '' {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b} =
      {z : ℂ | 0 < z.re ∧ z.re < a' ∧ 0 < z.im ∧ z.im < b'})
    (hcont : ContinuousOn f {z : ℂ | 0 ≤ z.re ∧ z.re ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b})
    (h0 : f 0 = 0) (h1 : f a = a') (h2 : f (a + b * I) = a' + b' * I) (h3 : f (b * I) = b' * I) :
    ∀ z ∈ {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b},
      f z = (b' / b : ℝ) * (z + ((K - 1) / (K + 1) : ℝ) * conj z) / (1 - ((K - 1) / (K + 1) : ℝ)) := by
  -- the length–area chain `a′b ≤ ∬ Re f_x ≤ ∬ |f_x| ≤ ∬ (|f_z| + |f_z̄|)`, `∬ (|f_z| + |f_z̄|)² ≤ K ∬ J ≤ K a′b′`
  -- is forced to be a chain of equalities by `a′/b′ = K a/b`; then `f_z`, `f_z̄` are constant and `f` is affine
  set R := {z : ℂ | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b} with hRdef
  have hRm : MeasurableSet R := hf.1.measurableSet
  have hK0 : 0 < K := by linarith
  have hsides := gl1_gz_sides ha hb ha' hb' hf himg hcont h0 h1 h2 h3
  obtain ⟨hae, hJle⟩ := gl1_gz_energy hf
  obtain ⟨hvolR, hfub⟩ := gl1_gz_fubini ha hb
  obtain ⟨hvolR', -⟩ := gl1_gz_fubini ha' hb'
  rw [himg, hvolR'] at hJle
  -- measurability of the Wirtinger derivatives
  have hdzm : Measurable fun z => LiZhongQC.dz f z := by
    have e : (fun z => LiZhongQC.dz f z) = fun z => (fderiv ℝ f z 1 - I * fderiv ℝ f z I) / 2 := rfl
    rw [e]
    exact ((measurable_fderiv_apply_const ℝ f 1).sub (measurable_const.mul
      (measurable_fderiv_apply_const ℝ f I))).div_const 2
  have hdzbm : Measurable fun z => LiZhongQC.dzbar f z := by
    have e : (fun z => LiZhongQC.dzbar f z) = fun z => (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2 := rfl
    rw [e]
    exact ((measurable_fderiv_apply_const ℝ f 1).add (measurable_const.mul
      (measurable_fderiv_apply_const ℝ f I))).div_const 2
  set w : ℂ → ℝ := fun z => ‖LiZhongQC.dz f z‖ + ‖LiZhongQC.dzbar f z‖ with hwdef
  set J : ℂ → ℝ := fun z => LiZhongQC.jacobian f z with hJdef
  set u : ℂ → ℝ := fun z => ‖LiZhongQC.partialX f z‖ with hudef
  set v : ℂ → ℝ := fun z => (LiZhongQC.partialX f z).re with hvdef
  have hwm : Measurable w := hdzm.norm.add hdzbm.norm
  have hJm : Measurable J := by
    have e : J = fun z => ‖LiZhongQC.dz f z‖ ^ 2 - ‖LiZhongQC.dzbar f z‖ ^ 2 := rfl
    rw [e]
    exact (hdzm.norm.pow_const 2).sub (hdzbm.norm.pow_const 2)
  have hfin : volume R < ⊤ := by rw [hvolR]; exact ENNReal.ofReal_lt_top
  have : IsFiniteMeasure (volume.restrict R) := isFiniteMeasure_restrict.2 hfin.ne
  -- `∬ J ≤ a′b′` and `∬ w² ≤ K a′b′`
  have hJi : IntegrableOn J R := by
    refine ⟨hJm.aestronglyMeasurable, ?_⟩
    show ∫⁻ z in R, ‖J z‖ₑ < ⊤
    calc ∫⁻ z in R, ‖J z‖ₑ = ∫⁻ z in R, ENNReal.ofReal (LiZhongQC.jacobian f z) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with z hz
          rw [← ofReal_norm, Real.norm_of_nonneg hz.2.2.2.2]
      _ < ⊤ := lt_of_le_of_lt hJle ENNReal.ofReal_lt_top
  have hJC : ∫ z in R, J z ≤ a' * b' := by
    have h := (integral_eq_lintegral_of_nonneg_ae (by filter_upwards [hae] with z hz using hz.2.2.2.2)
      hJm.aestronglyMeasurable)
    rw [h]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hJle
  have hw2i : IntegrableOn (fun z => w z ^ 2) R := by
    refine Integrable.mono' (hJi.const_mul K) (hwm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hae] with z hz
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hz.2.2.2.1
  have hwi : IntegrableOn w R := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hw2i) hwm.aestronglyMeasurable ?_
    refine ae_of_all _ fun z => ?_
    have h0w : 0 ≤ w z := add_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [Real.norm_of_nonneg h0w]
    show w z ≤ 1 + w z ^ 2
    nlinarith [sq_nonneg (w z - 1)]
  -- `f_x = f_z + f_z̄` a.e., so `|f_x| ≤ w` and `f_x` is integrable
  have hpxm : AEStronglyMeasurable (LiZhongQC.partialX f) (volume.restrict R) :=
    (hdzm.add hdzbm).aestronglyMeasurable.congr (by
      filter_upwards [hae] with z hz
      exact hz.2.1.symm)
  have hpxi : IntegrableOn (LiZhongQC.partialX f) R := by
    refine Integrable.mono' hwi hpxm ?_
    filter_upwards [hae] with z hz
    rw [hz.2.1]
    exact norm_add_le _ _
  have hui : IntegrableOn u R := hpxi.norm
  have hvi : IntegrableOn v R := hpxi.re
  -- `∬ Re f_x = a′ b` (P2 and Fubini)
  have hline := gl1_gz_line ha hb hf hcont hpxi hsides
  have hvB : ∫ z in R, v z = a' * b := by
    rw [(hfub v hvi).2]
    have e : ∫ y in Ioo 0 b, ∫ t in Ioo 0 a, v (t + y * I) = ∫ y in Ioo 0 b, a' :=
      integral_congr_ae (by filter_upwards [hline] with y hy using hy)
    rw [e, setIntegral_const, measureReal_def, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal hb.le, smul_eq_mul,
      mul_comm]
  have hratio' : (a' * b) ^ 2 = K * (a * b) * (a' * b') := by
    have e : a' = K * a * b' / b := by
      field_simp at hratio
      field_simp
      linarith
    rw [e]
    field_simp
  -- P4: all the inequalities are equalities a.e.
  have heq := gl1_gz_equality (S := R) (u := u) (v := v) (w := w) (J := J) (mul_pos ha hb) (mul_pos ha' hb) hK0
    hvolR hvi hui hwi hw2i hJi (by
      filter_upwards [hae] with z hz
      refine ⟨Complex.re_le_norm _, ?_, hz.2.2.2.1⟩
      show ‖LiZhongQC.partialX f z‖ ≤ ‖LiZhongQC.dz f z‖ + ‖LiZhongQC.dzbar f z‖
      rw [hz.2.1]
      exact norm_add_le _ _) hvB hJC hratio'
  set m : ℝ := a' * b / (a * b) with hmdef
  have hm : 0 < m := by positivity
  set k : ℝ := (K - 1) / (K + 1) with hkdef
  set c : ℝ := m / (1 + k) with hcdef
  -- the Wirtinger derivatives are `c` and `k c` a.e.
  have hpt : ∀ᵐ z ∂(volume.restrict R), LiZhongQC.dz f z = (c : ℂ) ∧ LiZhongQC.dzbar f z = ((k * c : ℝ) : ℂ) := by
    filter_upwards [hae, heq] with z hz he
    obtain ⟨-, hx, -, -, -⟩ := hz
    obtain ⟨e1, e2, e3, e4⟩ := he
    have h1 : (LiZhongQC.dz f z + LiZhongQC.dzbar f z).re = ‖LiZhongQC.dz f z + LiZhongQC.dzbar f z‖ := by
      rw [← hx]
      exact e1
    have h2 : ‖LiZhongQC.dz f z + LiZhongQC.dzbar f z‖ = ‖LiZhongQC.dz f z‖ + ‖LiZhongQC.dzbar f z‖ := by
      rw [← hx]
      exact e2
    exact gl1_gz_pointwise hm hK h1 h2 e3 e4
  -- P5: `f − (c z + k c z̄)` is constant, and the constant vanishes at the vertex `0`
  obtain ⟨e, he⟩ := gl1_gz_rigid ha hb (c := (c : ℂ)) (d := ((k * c : ℝ) : ℂ)) (LiZhongQC.thm9_1_isACL hf)
    (by
      filter_upwards [hae, hpt] with z hz hp
      rw [hz.2.1, hp.1, hp.2])
    (by
      filter_upwards [hae, hpt] with z hz hp
      rw [hz.2.2.1, hp.1, hp.2])
  have he0 : e = 0 := by
    -- `zₙ = (a + b i)/(n + 2) → 0` inside `R`
    set zs : ℕ → ℂ := fun n => ((a / (n + 2) : ℝ) : ℂ) + ((b / (n + 2) : ℝ) : ℂ) * I with hzs
    have hzR : ∀ n, zs n ∈ R := fun n => by
      simp only [hzs, hRdef, mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_zero, add_im, mul_im, zero_add, add_zero]
      have hn : (0 : ℝ) < n + 2 := by positivity
      refine ⟨by positivity, ?_, by positivity, ?_⟩
      · rw [div_lt_iff₀ hn]
        nlinarith
      · rw [div_lt_iff₀ hn]
        nlinarith
    have hzt : Tendsto zs atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => a / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
      have h2 : Tendsto (fun n : ℕ => b / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
      have h3 := (Complex.continuous_ofReal.tendsto 0).comp h1
      have h4 := (Complex.continuous_ofReal.tendsto 0).comp h2
      simpa [hzs] using h3.add (h4.mul_const I)
    have hclos : ∀ n, zs n ∈ {z : ℂ | 0 ≤ z.re ∧ z.re ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b} := fun n => by
      obtain ⟨p1, p2, p3, p4⟩ := hzR n
      exact ⟨p1.le, p2.le, p3.le, p4.le⟩
    have h0mem : (0 : ℂ) ∈ {z : ℂ | 0 ≤ z.re ∧ z.re ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b} := by
      simp only [mem_ofPred_eq, zero_re, zero_im]
      exact ⟨le_rfl, ha.le, le_rfl, hb.le⟩
    have hf0 : Tendsto (fun n => f (zs n)) atTop (𝓝 0) := by
      have := (hcont 0 h0mem).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hzt, Eventually.of_forall hclos⟩)
      rwa [h0] at this
    have hA : Tendsto (fun n => (c : ℂ) * zs n + ((k * c : ℝ) : ℂ) * conj (zs n) + e) atTop (𝓝 e) := by
      have h1 : Tendsto (fun n => (c : ℂ) * zs n) atTop (𝓝 ((c : ℂ) * 0)) := tendsto_const_nhds.mul hzt
      have h2 : Tendsto (fun n => ((k * c : ℝ) : ℂ) * conj (zs n)) atTop (𝓝 (((k * c : ℝ) : ℂ) * conj 0)) :=
        tendsto_const_nhds.mul ((Complex.continuous_conj.tendsto 0).comp hzt)
      have h3 := (h1.add h2).add_const e
      simpa using h3
    exact tendsto_nhds_unique (hA.congr fun n => (he (zs n) (hzR n)).symm) hf0
  -- the affine map in the book's normal form
  intro z hz
  rw [he z hz, he0, add_zero]
  have hK1 : (K + 1) ≠ 0 := by linarith
  have hb0 : b ≠ 0 := hb.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have hKne : K ≠ 0 := hK0.ne'
  have hcval : c = b' / b / (1 - k) := by
    rw [hcdef, hmdef, hkdef]
    have e : a' = K * a * b' / b := by
      field_simp at hratio
      field_simp
      linarith
    have h1k : 1 + (K - 1) / (K + 1) = 2 * K / (K + 1) := by field_simp; ring
    have h1k' : 1 - (K - 1) / (K + 1) = 2 / (K + 1) := by field_simp; ring
    rw [e, h1k, h1k']
    field_simp
  rw [hcval]
  push_cast
  have hk1 : (1 : ℂ) - ((K - 1) / (K + 1) : ℝ) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_ne_zero]
    rw [show (1 : ℝ) - (K - 1) / (K + 1) = 2 / (K + 1) by field_simp; ring]
    positivity
  push_cast at hk1
  field_simp

open LiZhongQC in
/-- From `L²` generalized partials (with the continuous representative) to GL distributional
partials: the integration-by-parts equations for `C∞` test functions. -/
theorem p14_distrib_of_genPartials {f gx gy : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hcont : ContinuousOn f Ω)
    (hgen : HasGenPartials f gx gy Ω 2) :
    HasDistribPartials f gx gy Ω := by
  constructor
  · intro C hCΩ hC
    haveI : IsFiniteMeasure (volume.restrict C) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
    have h12 : (1 : ℝ≥0∞) ≤ 2 := by simp
    exact ⟨(hcont.mono hCΩ).integrableOn_compact hC,
      memLp_one_iff_integrable.1 ((hgen.1 C hCΩ hC).1.mono_exponent h12),
      memLp_one_iff_integrable.1 ((hgen.1 C hCΩ hC).2.mono_exponent h12)⟩
  · intro φ hφ hcφ hsφ
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    obtain ⟨E1, E2⟩ := sp_ibp hΩ hgen hφ1 hcφ hsφ
    have hφ0 : ∀ z ∉ tsupport φ, φ z = 0 := fun z hz =>
      Function.notMem_support.1 (fun hs => hz (subset_closure hs))
    have hconv : ∀ e : ℂ, ∀ w : ℂ → ℂ,
        (∫ z, f z * fderiv ℝ φ z e) = ∫ z in Ω, f z * fderiv ℝ φ z e ∧
        (∫ z, w z * φ z) = ∫ z in Ω, w z * φ z := fun e w => by
      constructor
      · rw [sp_setIntegral_eq_integral hΩ.measurableSet hsφ (fun z hz => by
          rw [sp_fderiv_eq_zero_of_notMem_tsupport hz e, mul_zero])]
      · rw [sp_setIntegral_eq_integral hΩ.measurableSet hsφ (fun z hz => by
          rw [hφ0 z hz, mul_zero])]
    constructor
    · have c1 : (∫ z in Ω, f z * fderiv ℝ φ z 1) = ∫ z in Ω, fderiv ℝ φ z 1 * f z :=
        integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
      have c2 : (∫ z in Ω, φ z * gx z) = ∫ z in Ω, gx z * φ z :=
        integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
      rw [(hconv 1 gx).1, (hconv 1 gx).2, c1, E1, c2]
    · have c1 : (∫ z in Ω, f z * fderiv ℝ φ z I) = ∫ z in Ω, fderiv ℝ φ z I * f z :=
        integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
      have c2 : (∫ z in Ω, φ z * gy z) = ∫ z in Ω, gy z * φ z :=
        integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
      rw [(hconv I gy).1, (hconv I gy).2, c1, E2, c2]

open LiZhongQC in
/-- The pointwise dilatation bound of the analytic definition, from Theorem 10.1 and the a.e.
differentiability (Theorem 9.3). -/
theorem p14_ae_bound {f : ℂ → ℂ} {Ω : Set ℂ} {K : ℝ} (hΩ : IsOpen Ω) (hK : 1 ≤ K)
    (hhomeo : IsHomeomorphOnto f Ω (f '' Ω)) (hf : IsKQC f Ω K) :
    ∀ᵐ z ∂(volume.restrict Ω),
      ‖(partialX f z + I * partialY f z) / 2‖ ≤ (K - 1) / (K + 1) * ‖(partialX f z - I * partialY f z) / 2‖ := by
  obtain ⟨-, hineq⟩ := (thm10_1_isKQC_iff hΩ hK hhomeo).1 hf
  filter_upwards [hineq, thm9_3_differentiable_ae hf] with z hz hdiff
  rw [partialX_eq_of_differentiableAt hdiff, partialY_eq_of_differentiableAt hdiff]
  show ‖dzbar f z‖ ≤ (K - 1) / (K + 1) * ‖dz f z‖
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hK1]
  linarith [hz]

/-- **Unlabelled** (§1.4, l. 788; cited at l. 780, 1291). The geometric definition of quasiconformality implies the
analytic one ("the converse result … is also true. We omit the proof"). -/
theorem para1_4_geometric_imp_analytic {f : ℂ → ℂ} {Ω : Set ℂ} {K : ℝ} (hf : IsKQC f Ω K) (hc : IsConnected Ω) :
    IsKQCAnalytic f Ω K := by
  have hgen := (LiZhongQC.thm9_5_L2_derivatives hf).1
  have himgopen : IsOpen (f '' Ω) :=
    LiZhongQC.isOpen_image_of_continuousOn_injOn hf.1 hf.2.2.1.1 hf.2.2.1.2.1
  exact ⟨hf.1, hc, hf.2.1, hf.2.2.1, himgopen, _, _,
    p14_distrib_of_genPartials hf.1 hf.2.2.1.1 hgen, p14_ae_bound hf.1 hf.2.1 hf.2.2.1 hf⟩

end GardinerLakic2000
