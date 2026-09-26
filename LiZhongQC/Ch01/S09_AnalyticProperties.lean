import LiZhongQC.Ch01.S07_GeometricDefinition
import LiZhongQC.Ch01.S04_ModulusExtremalLength
import LiZhongQC.Lemmas.RectangleQuad
import LiZhongQC.Lemmas.InvarianceOfDomain
import LiZhongQC.Ch01.S08_Compactness

/-!
# §9 拟共形映射的分析性质 — Analytic properties of quasiconformal mappings

* Definition 9.1 (absolute continuity on lines, A.C.L.)   — `IsACL`
* Theorem 9.1 (q.c. maps are A.C.L.)                      — `thm9_1_isACL`
* Theorem 9.2 (partial derivatives exist a.e.)            — `thm9_2_partials_ae`
* Lemma 9.1 (Menchoff: a homeomorphism with partials a.e. is differentiable a.e.)
                                                           — `lemma9_1_menchoff`
* Theorem 9.3 (q.c. maps are differentiable a.e.)         — `thm9_3_differentiable_ae`
* Definition 9.2 (`L_p` generalized derivatives)          — `HasGenPartials`
* Green's formula for A.C.L. functions (9.9), (9.10)      — `eq9_9_green`, `eq9_10_green`
* Lemma 9.2 (A.C.L. + locally `L_p` partials ⇔ `L_p` generalized derivatives)
* Theorem 9.4 (the dilatation inequality a.e.)            — `thm9_4_dilatation_ae`
* (9.17) and Theorem 9.5 (`L₂` generalized derivatives)    — `eq9_17`, `thm9_5_L2_derivatives`
* Theorem 9.6 (absolute continuity), Corollaries 1 and 2
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- The closed rectangle `[a, b] × [c, d]` with sides parallel to the axes. -/
def closedRect (a b c d : ℝ) : Set ℂ := {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d}

/-- The open rectangle `(a, b) × (c, d)`. -/
def openRect (a b c d : ℝ) : Set ℂ := {z : ℂ | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d}

/-- **Definition 9.1** (线段上绝对连续, A.C.L.).  `f` is continuous in `D` and, for every closed
rectangle `R̄ = [a,b] × [c,d] ⊆ D`, `y ↦ f(x + iy)` is absolutely continuous on `[c, d]` for
almost every `x ∈ (a, b)`, and `x ↦ f(x + iy)` is absolutely continuous on `[a, b]` for almost
every `y ∈ (c, d)`. -/
def IsACL (f : ℂ → ℂ) (D : Set ℂ) : Prop :=
  ContinuousOn f D ∧ ∀ a b c d : ℝ, a < b → c < d → closedRect a b c d ⊆ D →
    (∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)),
        AbsolutelyContinuousOnInterval (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) c d) ∧
      ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)),
        AbsolutelyContinuousOnInterval (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) a b

/-- The fundamental theorem of calculus for a complex-valued absolutely continuous function
(reduced to its real and imaginary parts). -/
theorem integral_deriv_eq_sub_of_absolutelyContinuous {φ : ℝ → ℂ} {a b : ℝ}
    (hφ : AbsolutelyContinuousOnInterval φ a b) :
    ∫ x in a..b, deriv φ x = φ b - φ a := by
  have hre : AbsolutelyContinuousOnInterval (fun x => (φ x).re) a b := by
    apply squeeze_zero (fun t ↦ ?_) (fun t ↦ ?_) hφ
    · exact Finset.sum_nonneg fun i _ => dist_nonneg
    · gcongr with i _
      rw [Real.dist_eq, dist_eq_norm, ← sub_re]
      exact Complex.abs_re_le_norm _
  have him : AbsolutelyContinuousOnInterval (fun x => (φ x).im) a b := by
    apply squeeze_zero (fun t ↦ ?_) (fun t ↦ ?_) hφ
    · exact Finset.sum_nonneg fun i _ => dist_nonneg
    · gcongr with i _
      rw [Real.dist_eq, dist_eq_norm, ← sub_im]
      exact Complex.abs_im_le_norm _
  have hdiff : ∀ᵐ x, x ∈ uIcc a b → deriv φ x =
      ((deriv (fun x => (φ x).re) x : ℝ) : ℂ) + ((deriv (fun x => (φ x).im) x : ℝ) : ℂ) * I := by
    filter_upwards [hre.ae_differentiableAt, him.ae_differentiableAt] with x h1 h2 hx
    have hd : HasDerivAt (fun x => ((φ x).re : ℂ) + ((φ x).im : ℂ) * I)
        (((deriv (fun x => (φ x).re) x : ℝ) : ℂ) + ((deriv (fun x => (φ x).im) x : ℝ) : ℂ) * I) x :=
      ((h1 hx).hasDerivAt.ofReal_comp).add (((h2 hx).hasDerivAt.ofReal_comp).mul_const I)
    have e : (fun x => ((φ x).re : ℂ) + ((φ x).im : ℂ) * I) = φ :=
      funext fun x => Complex.re_add_im _
    rw [e] at hd
    exact hd.deriv
  have hint_re := hre.intervalIntegrable_deriv
  have hint_im := him.intervalIntegrable_deriv
  have hint_re' : IntervalIntegrable (fun x => ((deriv (fun x => (φ x).re) x : ℝ) : ℂ)) volume a b :=
    ⟨hint_re.1.ofReal, hint_re.2.ofReal⟩
  have hint_im' : IntervalIntegrable (fun x => ((deriv (fun x => (φ x).im) x : ℝ) : ℂ)) volume a b :=
    ⟨hint_im.1.ofReal, hint_im.2.ofReal⟩
  calc ∫ x in a..b, deriv φ x
      = ∫ x in a..b, (((deriv (fun x => (φ x).re) x : ℝ) : ℂ) +
          ((deriv (fun x => (φ x).im) x : ℝ) : ℂ) * I) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [hdiff] with x hx hx'
        exact hx (uIoc_subset_uIcc hx')
    _ = ((∫ x in a..b, deriv (fun x => (φ x).re) x : ℝ) : ℂ) +
          ((∫ x in a..b, deriv (fun x => (φ x).im) x : ℝ) : ℂ) * I := by
        rw [intervalIntegral.integral_add hint_re' (hint_im'.mul_const I),
          intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
          intervalIntegral.integral_ofReal]
    _ = φ b - φ a := by
        rw [hre.integral_deriv_eq_sub, him.integral_deriv_eq_sub]
        apply Complex.ext <;> simp

/-! ### Helpers for Theorem 9.1 (`acl_`)

The proof follows the book: for a rectangle `R̄ ⊂ D` the increasing function `t ↦ m(f(R_t))` has
a finite derivative a.e.; at such a `t₀`, the thin rectangles `(x', x'') × (t₀, t₀ + h)`, with the
vertical sides taken as the first pair of sides, have modulus `h/(x'' - x')`, so Definition 7.1 and
Rengel's inequality bound the distance between the images of their vertical sides by the image
area, and Schwarz's inequality gives absolute continuity on the line `Im z = t₀`.  The vertical
half is the horizontal half for `f ∘ (i ·)`. -/

/-- The rigid map `z ↦ i z + c`. -/
def aclRigid (c : ℂ) (z : ℂ) : ℂ := I * z + c

theorem acl_isConformalOnto_rigid (c : ℂ) : IsConformalOnto (aclRigid c) univ univ := by
  refine ⟨(by unfold aclRigid; fun_prop : Differentiable ℂ (aclRigid c)).differentiableOn,
    fun z _ w _ h => mul_left_cancel₀ I_ne_zero (add_right_cancel h), ?_⟩
  ext w
  refine ⟨fun _ => mem_univ w, fun _ => ⟨-I * (w - c), mem_univ _, ?_⟩⟩
  show I * (-I * (w - c)) + c = w
  rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul, sub_add_cancel]

theorem acl_rigid_det (c : ℂ) : I * 1 - c * 0 ≠ 0 := by simp

theorem acl_mobiusExt_rigid (c z : ℂ) :
    mobiusExt I c 0 1 (z : ExtPlane) = ((aclRigid c z : ℂ) : ExtPlane) := by
  rw [mobiusExt_coe (by simp : (0 : ℂ) * z + 1 ≠ 0)]
  simp [mobiusFn, aclRigid]

/-- `z ↦ i z + c` restricted to any set extends homeomorphically to `ℂ̄` by `mobiusExt I c 0 1`. -/
theorem acl_isHomeoExtension_rigid (c : ℂ) (S : Set ℂ) :
    IsHomeoExtension (aclRigid c) S (aclRigid c '' S) (mobiusExt I c 0 1) := by
  have h := (scExt_isHomeoExtension_id S).comp_homeomorph (mapsTo_id S)
    (mobiusHomeomorph I c 0 1 (acl_rigid_det c)) (g := aclRigid c) (W := aclRigid c '' S)
    (fun w _ => by rw [mobiusHomeomorph_apply]; exact acl_mobiusExt_rigid c w) ?_
  · have e1 : aclRigid c ∘ id = aclRigid c := Function.comp_id _
    have e2 : (⇑(mobiusHomeomorph I c 0 1 (acl_rigid_det c)) ∘ id) = mobiusExt I c 0 1 := by
      funext p
      rw [Function.comp_apply, id, mobiusHomeomorph_apply]
    rwa [e1, e2] at h
  · unfold toExt
    rw [image_image, image_image]
    exact image_congr fun w _ => by rw [mobiusHomeomorph_apply]; exact acl_mobiusExt_rigid c w

/-- `z ↦ i z + (x'' + t i)` maps `R(0, h, h + ℓ i, ℓ i)` onto `(x'' - ℓ, x'') × (t, t + h)`. -/
theorem acl_image_rigid_rectangle (x'' t h ℓ : ℝ) :
    aclRigid ((x'' : ℂ) + (t : ℂ) * I) '' rectangle h ℓ = openRect (x'' - ℓ) x'' t (t + h) := by
  ext w
  simp only [mem_image, rectangle, openRect, mem_setOf_eq, aclRigid]
  constructor
  · rintro ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
    have hre : (I * z + ((x'' : ℂ) + (t : ℂ) * I)).re = x'' - z.im := by
      simp
      ring
    have him : (I * z + ((x'' : ℂ) + (t : ℂ) * I)).im = z.re + t := by simp
    rw [hre, him]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨-I * (w - ((x'' : ℂ) + (t : ℂ) * I)), ?_, ?_⟩
    · have hre : (-I * (w - ((x'' : ℂ) + (t : ℂ) * I))).re = w.im - t := by simp
      have him : (-I * (w - ((x'' : ℂ) + (t : ℂ) * I))).im = x'' - w.re := by simp
      rw [hre, him]
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul, sub_add_cancel]

/-- The image of the bottom edge `[0, h] × {0}` under `z ↦ i z + (x'' + t i)`: the vertical
segment `x'' + [t, t + h] i`. -/
theorem acl_image_rigid_bottom (x'' t h : ℝ) :
    aclRigid ((x'' : ℂ) + (t : ℂ) * I) '' (Icc 0 h ×ℂ {0}) =
      (fun τ : ℝ => (x'' : ℂ) + ((t + τ : ℝ) : ℂ) * I) '' Icc 0 h := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_reProdIm, mem_singleton_iff] at hz
    refine ⟨z.re, hz.1, ?_⟩
    apply Complex.ext
    · simp [aclRigid, hz.2]
    · simp [aclRigid, hz.2]
      ring
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨(τ : ℂ), ?_, ?_⟩
    · rw [mem_reProdIm, mem_singleton_iff]
      exact ⟨by simpa using hτ, by simp⟩
    · apply Complex.ext
      · simp [aclRigid]
      · simp [aclRigid]
        ring

/-- The image of the top edge `[0, h] × {ℓ}` under `z ↦ i z + (x'' + t i)`: the vertical segment
`(x'' - ℓ) + [t, t + h] i`. -/
theorem acl_image_rigid_top (x'' t h ℓ : ℝ) :
    aclRigid ((x'' : ℂ) + (t : ℂ) * I) '' (Icc 0 h ×ℂ {ℓ}) =
      (fun τ : ℝ => ((x'' - ℓ : ℝ) : ℂ) + ((t + τ : ℝ) : ℂ) * I) '' Icc 0 h := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_reProdIm, mem_singleton_iff] at hz
    refine ⟨z.re, hz.1, ?_⟩
    apply Complex.ext
    · simp [aclRigid, hz.2]
      ring
    · simp [aclRigid, hz.2]
      ring
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨(τ : ℂ) + (ℓ : ℂ) * I, ?_, ?_⟩
    · rw [mem_reProdIm, mem_singleton_iff]
      exact ⟨by simpa using hτ, by simp⟩
    · apply Complex.ext
      · simp [aclRigid]
        ring
      · simp [aclRigid]
        ring

/-- The rectangle `(x', x'') × (t, t + h)` as a quadrilateral whose first pair of sides are the two
vertical sides: the image of `R(0, h, h + ℓ i, ℓ i)`, `ℓ = x'' - x'`, under `z ↦ i z + (x'' + t i)`.
Its modulus is `h/ℓ`, and its first and third sides are the right and the left vertical side. -/
theorem acl_exists_rectQuad {x' x'' t h : ℝ} (hx : x' < x'') (hh : 0 < h) :
    ∃ Q : TopQuad, Q.dom = openRect x' x'' t (t + h) ∧ Q.modulus = h / (x'' - x') ∧
      Q.side 0 = toExt ((fun τ : ℝ => (x'' : ℂ) + ((t + τ : ℝ) : ℂ) * I) '' Icc 0 h) ∧
      Q.side 2 = toExt ((fun τ : ℝ => (x' : ℂ) + ((t + τ : ℝ) : ℂ) * I) '' Icc 0 h) := by
  set c : ℂ := (x'' : ℂ) + (t : ℂ) * I with hc
  have hℓ : 0 < x'' - x' := sub_pos.2 hx
  have hdom : aclRigid c '' rectangle h (x'' - x') = openRect x' x'' t (t + h) := by
    rw [hc, acl_image_rigid_rectangle, sub_sub_cancel]
  have hcl : closure (toExt (rectQuad hh hℓ).dom) ⊆ toExt univ := by
    show closure (toExt (rectangle h (x'' - x'))) ⊆ toExt univ
    rw [scExt_closure_toExt_of_isBounded (scExt_isBounded_rectangle _ _)]
    exact image_mono (subset_univ _)
  obtain ⟨Q, hQimg, hQce⟩ :=
    TopQuad.exists_image_conformal isOpen_univ (acl_isConformalOnto_rigid c) hcl
  have hQdom : Q.dom = openRect x' x'' t (t + h) := by
    rw [hQimg.1]
    exact hdom
  have hQo : IsOpen Q.dom := Q.isTopQuad.1.1
  have hconf : IsConformalOnto (aclRigid c) (rectQuad hh hℓ).dom Q.dom :=
    ⟨(acl_isConformalOnto_rigid c).1.mono (subset_univ _),
      (acl_isConformalOnto_rigid c).2.1.mono (subset_univ _), hQimg.1.symm⟩
  have hext : IsHomeoExtension (aclRigid c) (rectQuad hh hℓ).dom Q.dom (mobiusExt I c 0 1) := by
    rw [hQimg.1]
    exact acl_isHomeoExtension_rigid c _
  have hvert : ∀ j, Q.vert j = mobiusExt I c 0 1 ((rectQuad hh hℓ).vert j) := fun j => by
    rw [hQimg.2 j]
    fin_cases j <;> simp [rectQuad, rectVert, acl_mobiusExt_rigid]
  refine ⟨Q, hQdom, ?_, ?_, ?_⟩
  · rw [← thm1_3_modulus_conformal_invariant hQce]
    exact modulus_rectQuad hh hℓ
  · rw [Q.side_eq_boundaryArc, hvert 0, hvert (0 + 1), hvert (0 + 2),
      ← TopQuad.image_side hQo hconf hext 0, (rectQuad hh hℓ).side_eq_boundaryArc]
    show mobiusExt I c 0 1 '' boundaryArc (frontier (toExt (rectangle h (x'' - x'))))
      (rectVert h (x'' - x') 0) (rectVert h (x'' - x') 1) (rectVert h (x'' - x') 2) = _
    rw [boundaryArc_frontier_toExt_rectangle_bottom hh hℓ]
    unfold toExt
    rw [image_image, image_congr fun z _ => acl_mobiusExt_rigid c z, ← image_image, hc,
      acl_image_rigid_bottom]
  · rw [Q.side_eq_boundaryArc, hvert 2, hvert (2 + 1), hvert (2 + 2),
      ← TopQuad.image_side hQo hconf hext 2, (rectQuad hh hℓ).side_eq_boundaryArc]
    show mobiusExt I c 0 1 '' boundaryArc (frontier (toExt (rectangle h (x'' - x'))))
      (rectVert h (x'' - x') 2) (rectVert h (x'' - x') 3) (rectVert h (x'' - x') 0) = _
    rw [boundaryArc_frontier_toExt_rectangle_top hh hℓ]
    unfold toExt
    rw [image_image, image_congr fun z _ => acl_mobiusExt_rigid c z, ← image_image, hc,
      acl_image_rigid_top, sub_sub_cancel]

/-- The sides of the image quadrilateral of a homeomorphism (the variant of `TopQuad.image_side`
that only needs `f '' Q.dom = V`). -/
theorem acl_image_side {Q : TopQuad} {V : Set ℂ} (hV : IsOpen V) {f : ℂ → ℂ}
    {F : ExtPlane → ExtPlane} (hfQ : f '' Q.dom = V) (hF : IsHomeoExtension f Q.dom V F)
    (i : Fin 4) :
    F '' Q.side i = boundaryArc (frontier (toExt V)) (F (Q.vert i)) (F (Q.vert (i + 1)))
      (F (Q.vert (i + 2))) := by
  have hQ := Q.isTopQuad
  have hfr : frontier (toExt Q.dom) ⊆ closure (toExt Q.dom) := frontier_subset_closure
  rw [Q.side_eq_boundaryArc, image_boundaryArc_of_injOn isClosed_closure hF.2.1 hF.2.2.1 hfr
    (hfr (hQ.2.1 i)) (hfr (hQ.2.1 _)) (hfr (hQ.2.1 _)), hF.image_frontier hQ.1.1 hV hfQ]

/-- A map continuous and injective on the closure of a bounded open set `U`, with `f '' U` open,
extends to the closures in `ℂ̄` by `OnePoint.map f`. -/
theorem acl_isHomeoExtension_map {f : ℂ → ℂ} {U : Set ℂ} (hUb : Bornology.IsBounded U)
    (hc : ContinuousOn f (closure U)) (hi : InjOn f (closure U)) :
    IsHomeoExtension f U (f '' U) (OnePoint.map f) := by
  have hcl : closure (toExt U) = toExt (closure U) := scExt_closure_toExt_of_isBounded hUb
  have hK : IsCompact (f '' closure U) := hUb.isCompact_closure.image_of_continuousOn hc
  have hfcl : f '' closure U = closure (f '' U) :=
    subset_antisymm hc.image_closure (closure_minimal (image_mono subset_closure) hK.isClosed)
  have hVb : Bornology.IsBounded (f '' U) := hK.isBounded.subset (image_mono subset_closure)
  refine ⟨fun z _ => rfl, ?_, ?_, ?_⟩
  · rw [hcl]
    rintro _ ⟨z, hz, rfl⟩
    show Tendsto (OnePoint.map f) (𝓝[toExt (closure U)] (z : ExtPlane)) (𝓝 (OnePoint.map f z))
    rw [OnePoint.nhdsWithin_coe, scExt_preimage_coe_toExt, tendsto_map'_iff]
    exact (OnePoint.continuous_coe.tendsto _).comp (hc z hz)
  · rw [hcl]
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩ h
    rw [hi hz hw (OnePoint.coe_injective h)]
  · rw [hcl, scExt_closure_toExt_of_isBounded hVb, ← hfcl]
    unfold toExt
    rw [image_image, image_image]
    rfl

/-- Definition 7.1 applied to a rectangle `Q` with `Q̄ ⊆ D`: the image quadrilateral `Q'` has
domain `f '' Q.dom`, modulus at least `M(Q)/K`, and sides the images of the sides of `Q`. -/
theorem acl_exists_image_quad {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {Q : TopQuad}
    (hQb : Bornology.IsBounded Q.dom) (hQD : closure Q.dom ⊆ D) :
    ∃ Q' : TopQuad, Q'.dom = f '' Q.dom ∧ Q.modulus / K ≤ Q'.modulus ∧
      ∀ i, Q'.side i = OnePoint.map f '' Q.side i := by
  have hQcl : closure (toExt Q.dom) ⊆ toExt D := by
    rw [scExt_closure_toExt_of_isBounded hQb]
    exact image_mono hQD
  obtain ⟨Q', hQ', -⟩ := hf.2.2.2 Q hQcl
  have hmod := (hf.modulus_ge Q Q' hQcl hQ').1
  have hV : IsOpen Q'.dom := Q'.isTopQuad.1.1
  have hfQ : f '' Q.dom = Q'.dom := hQ'.1.symm
  have hext : IsHomeoExtension f Q.dom Q'.dom (OnePoint.map f) := by
    rw [← hfQ]
    exact acl_isHomeoExtension_map hQb (hf.2.2.1.1.mono hQD) (hf.2.2.1.2.1.mono hQD)
  refine ⟨Q', hQ'.1, hmod, fun i => ?_⟩
  rw [acl_image_side hV hfQ hext i, Q'.side_eq_boundaryArc, hQ'.2 i, hQ'.2 (i + 1), hQ'.2 (i + 2)]

theorem acl_length_eq (γ : LRCurve) : γ.length = ∫⁻ t in Ioo (0 : ℝ) 1, ‖deriv γ.toFun t‖ₑ := by
  simp [LRCurve.length, LRCurve.rhoLength]

/-- The Euclidean length of a locally rectifiable curve is at least the distance between its
endpoint limits (fundamental theorem of calculus on `[s, s'] ⊂ (0, 1)`, then `s → 0`, `s' → 1`). -/
theorem acl_edist_le_length (γ : LRCurve) {p q : ℂ} (hp : Tendsto γ.toFun (𝓝[>] 0) (𝓝 p))
    (hq : Tendsto γ.toFun (𝓝[<] 1) (𝓝 q)) : edist p q ≤ γ.length := by
  rcases eq_or_ne γ.length ⊤ with htop | htop
  · rw [htop]
    exact le_top
  have key : ∀ s s' : ℝ, 0 < s → s < s' → s' < 1 →
      edist (γ.toFun s) (γ.toFun s') ≤ γ.length := by
    intro s s' hs hss' hs'
    have hsub : Icc s s' ⊆ Ioo 0 1 := Icc_subset_Ioo hs hs'
    obtain ⟨L, hL⟩ :=
      (γ.locallyLipschitzOn.mono hsub).exists_lipschitzOnWith_of_compact isCompact_Icc
    have hAC : AbsolutelyContinuousOnInterval γ.toFun s s' := by
      rw [← uIcc_of_le hss'.le] at hL
      exact hL.absolutelyContinuousOnInterval
    have hFTC := integral_deriv_eq_sub_of_absolutelyContinuous hAC
    have hmeas : AEStronglyMeasurable (fun t => ‖deriv γ.toFun t‖) (volume.restrict (Ioc s s')) :=
      (measurable_deriv γ.toFun).norm.aestronglyMeasurable
    calc edist (γ.toFun s) (γ.toFun s') = ENNReal.ofReal ‖γ.toFun s' - γ.toFun s‖ := by
          rw [edist_dist, dist_eq_norm, norm_sub_rev]
      _ ≤ ENNReal.ofReal (∫ t in s..s', ‖deriv γ.toFun t‖) := by
          rw [← hFTC]
          exact ENNReal.ofReal_le_ofReal (intervalIntegral.norm_integral_le_integral_norm hss'.le)
      _ = ENNReal.ofReal (∫⁻ t in Ioc s s', ‖deriv γ.toFun t‖ₑ).toReal := by
          rw [intervalIntegral.integral_of_le hss'.le,
            integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t => norm_nonneg _) hmeas]
          simp_rw [ofReal_norm]
      _ ≤ ENNReal.ofReal γ.length.toReal := by
          refine ENNReal.ofReal_le_ofReal (ENNReal.toReal_mono htop ?_)
          rw [acl_length_eq]
          exact lintegral_mono_set (Ioc_subset_Icc_self.trans hsub)
      _ = γ.length := ENNReal.ofReal_toReal htop
  have h1 : ∀ s, 0 < s → s < 1 → edist (γ.toFun s) q ≤ γ.length := by
    intro s hs hs1
    refine le_of_tendsto (tendsto_const_nhds.edist hq) ?_
    filter_upwards [Ioo_mem_nhdsLT hs1] with s' hs'
    exact key s s' hs hs'.1 hs'.2
  refine le_of_tendsto (hp.edist tendsto_const_nhds) ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with s hs
  exact h1 s hs.1 hs.2

/-! Rectangles: compactness, closures, measurability of images. -/

theorem acl_closedRect_eq (a b c d : ℝ) : closedRect a b c d = Icc a b ×ℂ Icc c d := by
  ext z
  simp only [closedRect, mem_setOf_eq, mem_reProdIm, mem_Icc]
  tauto

theorem acl_isCompact_closedRect (a b c d : ℝ) : IsCompact (closedRect a b c d) := by
  rw [acl_closedRect_eq]
  exact isCompact_Icc.reProdIm isCompact_Icc

theorem acl_closedRect_subset {a b c d a' b' c' d' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) (hc : c ≤ c')
    (hd : d' ≤ d) : closedRect a' b' c' d' ⊆ closedRect a b c d := fun z hz =>
  ⟨by linarith [hz.1], by linarith [hz.2.1], by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩

theorem acl_openRect_subset_closedRect {a b c d a' b' c' d' : ℝ} (ha : a ≤ a') (hb : b' ≤ b)
    (hc : c ≤ c') (hd : d' ≤ d) : openRect a' b' c' d' ⊆ closedRect a b c d := fun z hz =>
  ⟨by linarith [hz.1], by linarith [hz.2.1], by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩

theorem acl_isBounded_openRect (a b c d : ℝ) : Bornology.IsBounded (openRect a b c d) :=
  (acl_isCompact_closedRect a b c d).isBounded.subset
    (acl_openRect_subset_closedRect le_rfl le_rfl le_rfl le_rfl)

theorem acl_closure_openRect_subset (a b c d : ℝ) :
    closure (openRect a b c d) ⊆ closedRect a b c d :=
  closure_minimal (acl_openRect_subset_closedRect le_rfl le_rfl le_rfl le_rfl)
    (acl_isCompact_closedRect a b c d).isClosed

/-- An open rectangle is a countable union of closed rectangles. -/
theorem acl_openRect_eq_iUnion (a b c d : ℝ) :
    openRect a b c d = ⋃ n : ℕ, closedRect (a + 1 / (n + 1)) (b - 1 / (n + 1)) (c + 1 / (n + 1))
      (d - 1 / (n + 1)) := by
  ext z
  simp only [mem_iUnion, openRect, closedRect, mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min (lt_min (sub_pos.2 h1) (sub_pos.2 h2))
      (lt_min (sub_pos.2 h3) (sub_pos.2 h4)))
    obtain ⟨hn1, hn2⟩ := lt_min_iff.1 hn
    obtain ⟨hn11, hn12⟩ := lt_min_iff.1 hn1
    obtain ⟨hn21, hn22⟩ := lt_min_iff.1 hn2
    exact ⟨n, by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨n, h1, h2, h3, h4⟩
    have hn : (0 : ℝ) < 1 / (n + 1) := Nat.one_div_pos_of_nat
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem acl_measurableSet_image_openRect {f : ℂ → ℂ} {D : Set ℂ} (hc : ContinuousOn f D)
    {a b c d : ℝ} (hR : closedRect a b c d ⊆ D) : MeasurableSet (f '' openRect a b c d) := by
  rw [acl_openRect_eq_iUnion, image_iUnion]
  refine MeasurableSet.iUnion fun n => ?_
  have hn : (0 : ℝ) < 1 / (n + 1) := Nat.one_div_pos_of_nat
  have hsub : closedRect (a + 1 / (n + 1)) (b - 1 / (n + 1)) (c + 1 / (n + 1)) (d - 1 / (n + 1)) ⊆
      closedRect a b c d :=
    acl_closedRect_subset (by linarith) (by linarith) (by linarith) (by linarith)
  exact ((acl_isCompact_closedRect _ _ _ _).image_of_continuousOn
    (hc.mono (hsub.trans hR))).isClosed.measurableSet

theorem acl_volume_image_lt_top {f : ℂ → ℂ} {D : Set ℂ} (hc : ContinuousOn f D) {a b c d : ℝ}
    (hR : closedRect a b c d ⊆ D) {S : Set ℂ} (hS : S ⊆ closedRect a b c d) :
    volume (f '' S) < ⊤ :=
  lt_of_le_of_lt (measure_mono (image_mono hS))
    ((acl_isCompact_closedRect a b c d).image_of_continuousOn (hc.mono hR)).measure_lt_top

/-- The increasing set function `g(t) = m(f(R_t))` of the book, `R_t = (a, b) × (c, t)`, clamped
at `t = d`. -/
def aclArea (f : ℂ → ℂ) (a b c d : ℝ) (t : ℝ) : ℝ :=
  (volume (f '' openRect a b c (min t d))).toReal

theorem acl_monotone_aclArea {f : ℂ → ℂ} {D : Set ℂ} (hc : ContinuousOn f D) {a b c d : ℝ}
    (hR : closedRect a b c d ⊆ D) : Monotone (aclArea f a b c d) := by
  intro s t hst
  unfold aclArea
  refine ENNReal.toReal_mono (acl_volume_image_lt_top hc hR
    (acl_openRect_subset_closedRect le_rfl le_rfl le_rfl (min_le_right t d))).ne ?_
  refine measure_mono (image_mono fun z hz => ?_)
  exact ⟨hz.1, hz.2.1, hz.2.2.1, lt_of_lt_of_le hz.2.2.2 (min_le_min_right d hst)⟩

/-- The images of the thin rectangles over a disjoint family of intervals on the line `Im z = t`
are disjoint and lie in `f(R_{t+h}) ∖ f(R_t)`, so their total area is at most
`g(t + h) - g(t)`. -/
theorem acl_sum_volume_le {f : ℂ → ℂ} {D : Set ℂ} (hc : ContinuousOn f D) (hi : InjOn f D)
    {a b c d : ℝ} (hab : a ≤ b) (hR : closedRect a b c d ⊆ D) {t h : ℝ} (hh : 0 < h)
    (hct : c ≤ t) (htd : t + h ≤ d) {n : ℕ} {E : ℕ → ℝ × ℝ} (hE : (n, E) ∈ AbsolutelyContinuousOnInterval.disjWithin a b) :
    ∑ i ∈ Finset.range n,
        (volume (f '' openRect (min (E i).1 (E i).2) (max (E i).1 (E i).2) t (t + h))).toReal ≤
      aclArea f a b c d (t + h) - aclArea f a b c d t := by
  obtain ⟨hmem, hdisj⟩ := hE
  have hmem' : ∀ i ∈ Finset.range n, (E i).1 ∈ Icc a b ∧ (E i).2 ∈ Icc a b := by
    intro i hi'
    have := hmem i hi'
    rwa [uIcc_of_le hab] at this
  set R : ℕ → Set ℂ := fun i => openRect (min (E i).1 (E i).2) (max (E i).1 (E i).2) t (t + h)
    with hRdef
  have hRsub : ∀ i ∈ Finset.range n, closedRect (min (E i).1 (E i).2) (max (E i).1 (E i).2) t
      (t + h) ⊆ closedRect a b c d := fun i hi' =>
    acl_closedRect_subset (le_min (hmem' i hi').1.1 (hmem' i hi').2.1)
      (max_le (hmem' i hi').1.2 (hmem' i hi').2.2) hct htd
  have hmeas : ∀ i ∈ Finset.range n, MeasurableSet (f '' R i) := fun i hi' =>
    acl_measurableSet_image_openRect hc ((hRsub i hi').trans hR)
  have hRD : ∀ i ∈ Finset.range n, R i ⊆ D := fun i hi' =>
    (acl_openRect_subset_closedRect le_rfl le_rfl le_rfl le_rfl).trans ((hRsub i hi').trans hR)
  -- disjointness of the images
  have hdisj' : ((Finset.range n : Finset ℕ) : Set ℕ).PairwiseDisjoint fun i => f '' R i := by
    intro i hi' j hj' hij
    have hd := hdisj hi' hj' hij
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    have hzw : w = z := hi (hRD j hj' hw) (hRD i hi' hz) hwz
    rw [hzw] at hw
    have h1 : z.re ∈ uIoc (E i).1 (E i).2 := ⟨hz.1, hz.2.1.le⟩
    have h2 : z.re ∈ uIoc (E j).1 (E j).2 := ⟨hw.1, hw.2.1.le⟩
    exact Set.disjoint_left.1 hd h1 h2
  -- the union lies in `f(R_{t+h}) ∖ f(R_t)`
  set A := f '' openRect a b c (t + h) with hA
  set B := f '' openRect a b c t with hB
  have hBA : B ⊆ A := image_mono fun z hz => ⟨hz.1, hz.2.1, hz.2.2.1, by linarith [hz.2.2.2]⟩
  have hBm : MeasurableSet B :=
    acl_measurableSet_image_openRect hc ((acl_closedRect_subset le_rfl le_rfl le_rfl
      (by linarith)).trans hR)
  have hBfin : volume B ≠ ⊤ :=
    (acl_volume_image_lt_top hc hR (acl_openRect_subset_closedRect le_rfl le_rfl le_rfl
      (by linarith))).ne
  have hAfin : volume A ≠ ⊤ :=
    (acl_volume_image_lt_top hc hR (acl_openRect_subset_closedRect le_rfl le_rfl le_rfl htd)).ne
  have hunion : (⋃ i ∈ Finset.range n, f '' R i) ⊆ A \ B := by
    intro w hw
    simp only [mem_iUnion, exists_prop] at hw
    obtain ⟨i, hi', z, hz, rfl⟩ := hw
    have hz1 := (hmem' i hi').1
    have hz2 := (hmem' i hi').2
    have hmin : a ≤ min (E i).1 (E i).2 := le_min hz1.1 hz2.1
    have hmax : max (E i).1 (E i).2 ≤ b := max_le hz1.2 hz2.2
    have hzR : min (E i).1 (E i).2 < z.re ∧ z.re < max (E i).1 (E i).2 ∧ t < z.im ∧
        z.im < t + h := hz
    refine ⟨⟨z, ⟨by linarith, by linarith, by linarith, hzR.2.2.2⟩, rfl⟩, ?_⟩
    rintro ⟨z', hz', hz'z⟩
    have hzD : z ∈ D := hRD i hi' hz
    have hz'D : z' ∈ D :=
      hR (acl_openRect_subset_closedRect le_rfl le_rfl le_rfl (by linarith) hz')
    have hzz : z' = z := hi hz'D hzD hz'z
    rw [hzz] at hz'
    linarith [hzR.2.2.1, hz'.2.2.2]
  have hsum : ∑ i ∈ Finset.range n, volume (f '' R i) ≤ volume A - volume B := by
    rw [← measure_biUnion_finset hdisj' hmeas, ← measure_diff hBA hBm.nullMeasurableSet hBfin]
    exact measure_mono hunion
  have hfin : ∀ i ∈ Finset.range n, volume (f '' R i) ≠ ⊤ := fun i hi' =>
    (acl_volume_image_lt_top hc hR ((acl_openRect_subset_closedRect le_rfl le_rfl le_rfl
      le_rfl).trans (hRsub i hi'))).ne
  rw [← ENNReal.toReal_sum hfin]
  unfold aclArea
  have htd' : t ≤ d := by linarith
  rw [min_eq_left htd, min_eq_left htd', ← hA, ← hB,
    ← ENNReal.toReal_sub_of_le (measure_mono hBA) hAfin]
  exact ENNReal.toReal_mono (ENNReal.sub_ne_top hAfin) hsum

theorem acl_dist_vert (x t τ : ℝ) :
    dist ((x : ℂ) + (t : ℂ) * I) ((x : ℂ) + ((t + τ : ℝ) : ℂ) * I) = |τ| := by
  have e : (x : ℂ) + (t : ℂ) * I - ((x : ℂ) + ((t + τ : ℝ) : ℂ) * I) = -(τ : ℂ) * I := by
    push_cast
    ring
  rw [Complex.dist_eq, e, norm_mul, norm_neg, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs]

theorem acl_mem_closedRect {a b c d x t : ℝ} (hax : a ≤ x) (hxb : x ≤ b) (hct : c ≤ t)
    (htd : t ≤ d) : (x : ℂ) + (t : ℂ) * I ∈ closedRect a b c d :=
  ⟨by simp [hax], by simp [hxb], by simp [hct], by simp [htd]⟩

/-- The per-rectangle estimate of the book: for the thin rectangle `R = (x', x'') × (t, t + h)` and
`u = max (|f(x''+it) - f(x'+it)| - 2η) 0` (the distance between the images of the vertical sides
is at least `u` when `f` moves points of the closed rectangle by less than `η` along vertical
segments of length `≤ h`), Definition 7.1 and Rengel's inequality give
`u² · h/((x'' - x') K) ≤ m(f(R))`. -/
theorem acl_rect_estimate {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {a b c d : ℝ}
    (hR : closedRect a b c d ⊆ D) {x' x'' t h η : ℝ} (hx : x' < x'') (hh : 0 < h)
    (hax : a ≤ x') (hxb : x'' ≤ b) (hct : c ≤ t) (htd : t + h ≤ d)
    (hρ : ∀ x, a ≤ x → x ≤ b → ∀ τ ∈ Icc (0 : ℝ) h,
      dist (f ((x : ℂ) + (t : ℂ) * I)) (f ((x : ℂ) + ((t + τ : ℝ) : ℂ) * I)) < η) :
    (max (dist (f ((x' : ℂ) + (t : ℂ) * I)) (f ((x'' : ℂ) + (t : ℂ) * I)) - 2 * η) 0) ^ 2 *
        (h / ((x'' - x') * K)) ≤
      (volume (f '' openRect x' x'' t (t + h))).toReal := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hf.2.1
  have hℓ : 0 < x'' - x' := sub_pos.2 hx
  obtain ⟨Q, hQdom, hQmod, hQs0, hQs2⟩ := acl_exists_rectQuad (t := t) hx hh
  have hQb : Bornology.IsBounded Q.dom := by
    rw [hQdom]
    exact acl_isBounded_openRect _ _ _ _
  have hQD : closure Q.dom ⊆ D := by
    rw [hQdom]
    exact (acl_closure_openRect_subset _ _ _ _).trans
      ((acl_closedRect_subset hax hxb hct htd).trans hR)
  obtain ⟨Q', hQ'dom, hQ'mod, hQ'side⟩ := acl_exists_image_quad hf hQb hQD
  have hQ'area : Q'.area = volume (f '' openRect x' x'' t (t + h)) := by
    show volume Q'.dom = _
    rw [hQ'dom, hQdom]
  have hfin : Q'.area < ⊤ := by
    rw [hQ'area]
    exact acl_volume_image_lt_top hf.2.2.1.1 hR (acl_openRect_subset_closedRect hax hxb hct htd)
  have hren := rengel_right Q' hfin
  -- the distance between the images of the vertical sides
  set m := dist (f ((x' : ℂ) + (t : ℂ) * I)) (f ((x'' : ℂ) + (t : ℂ) * I)) with hm
  set u := max (m - 2 * η) 0 with hu
  have hsd : ENNReal.ofReal u ≤ Q'.sideDistance 0 := by
    refine le_iInf₂ fun γ hγ => ?_
    obtain ⟨-, ⟨p, hp, hlp⟩, ⟨q, hq, hlq⟩⟩ := hγ
    rw [hQ'side 0, hQs0] at hp
    have hq' : q ∈ OnePoint.map f '' Q.side 2 := by
      rw [hQ'side (0 + 2)] at hq
      exact hq
    rw [hQs2] at hq'
    clear hq
    obtain ⟨_, ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩, rfl⟩ := hp
    obtain ⟨_, ⟨_, ⟨τ', hτ', rfl⟩, rfl⟩, rfl⟩ := hq'
    simp only [OnePoint.map_some] at hlp hlq
    have hlp' : Tendsto γ.toFun (𝓝[>] 0) (𝓝 (f ((x'' : ℂ) + ((t + τ : ℝ) : ℂ) * I))) :=
      OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.2 hlp
    have hlq' : Tendsto γ.toFun (𝓝[<] 1) (𝓝 (f ((x' : ℂ) + ((t + τ' : ℝ) : ℂ) * I))) :=
      OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.2 hlq
    have hlen := acl_edist_le_length γ hlp' hlq'
    have h1 := hρ x'' (hax.trans hx.le) hxb τ hτ
    have h2 := hρ x' hax (hx.le.trans hxb) τ' hτ'
    have htri : m ≤ 2 * η + dist (f ((x'' : ℂ) + ((t + τ : ℝ) : ℂ) * I))
        (f ((x' : ℂ) + ((t + τ' : ℝ) : ℂ) * I)) := by
      have h3 := dist_triangle4 (f ((x' : ℂ) + (t : ℂ) * I)) (f ((x' : ℂ) + ((t + τ' : ℝ) : ℂ) * I))
        (f ((x'' : ℂ) + ((t + τ : ℝ) : ℂ) * I)) (f ((x'' : ℂ) + (t : ℂ) * I))
      rw [dist_comm (f ((x' : ℂ) + ((t + τ' : ℝ) : ℂ) * I)),
        dist_comm (f ((x'' : ℂ) + ((t + τ : ℝ) : ℂ) * I)) (f ((x'' : ℂ) + (t : ℂ) * I))] at h3
      linarith
    have hu' : u ≤ dist (f ((x'' : ℂ) + ((t + τ : ℝ) : ℂ) * I))
        (f ((x' : ℂ) + ((t + τ' : ℝ) : ℂ) * I)) :=
      max_le (by linarith) dist_nonneg
    calc ENNReal.ofReal u ≤ ENNReal.ofReal (dist (f ((x'' : ℂ) + ((t + τ : ℝ) : ℂ) * I))
          (f ((x' : ℂ) + ((t + τ' : ℝ) : ℂ) * I))) := ENNReal.ofReal_le_ofReal hu'
      _ = edist (f ((x'' : ℂ) + ((t + τ : ℝ) : ℂ) * I))
          (f ((x' : ℂ) + ((t + τ' : ℝ) : ℂ) * I)) := (edist_dist _ _).symm
      _ ≤ γ.length := hlen
  -- combine Definition 7.1 and Rengel's inequality
  have hQ'mod' : ENNReal.ofReal (h / ((x'' - x') * K)) ≤ ENNReal.ofReal Q'.modulus := by
    apply ENNReal.ofReal_le_ofReal
    rw [hQmod, div_div] at hQ'mod
    exact hQ'mod
  have h1 : ENNReal.ofReal (h / ((x'' - x') * K)) * Q'.sideDistance 0 ^ 2 ≤ Q'.area :=
    ENNReal.mul_le_of_le_div (hQ'mod'.trans hren)
  have h2 : ENNReal.ofReal (h / ((x'' - x') * K)) * ENNReal.ofReal u ^ 2 ≤ Q'.area :=
    le_trans (by gcongr) h1
  have h3 : ENNReal.ofReal (u ^ 2 * (h / ((x'' - x') * K))) ≤ Q'.area := by
    rw [ENNReal.ofReal_mul (sq_nonneg u), ENNReal.ofReal_pow (le_max_right _ _), mul_comm]
    exact h2
  rw [ENNReal.ofReal_le_iff_le_toReal hfin.ne, hQ'area] at h3
  exact h3

/-- The key estimate of the book: at `t₀ ∈ (c, d)` where `g = m(f(R_t))` is differentiable, for
every disjoint family of intervals on the line `Im z = t₀` of total length `s`,
`∑ |f(x_k'' + i t₀) - f(x_k' + i t₀)| ≤ √(K (|g'(t₀)| + 1) s)`. -/
theorem acl_sum_dist_le {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {a b c d : ℝ}
    (hab : a < b) (hR : closedRect a b c d ⊆ D) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo c d)
    (hg : DifferentiableAt ℝ (aclArea f a b c d) t₀) {n : ℕ} {E : ℕ → ℝ × ℝ}
    (hE : (n, E) ∈ AbsolutelyContinuousOnInterval.disjWithin a b) :
    ∑ i ∈ Finset.range n,
        dist (f (((E i).1 : ℂ) + (t₀ : ℂ) * I)) (f (((E i).2 : ℂ) + (t₀ : ℂ) * I)) ≤
      Real.sqrt (K * (|deriv (aclArea f a b c d) t₀| + 1) *
        ∑ i ∈ Finset.range n, dist (E i).1 (E i).2) := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hf.2.1
  have hc := hf.2.2.1.1
  have hinj := hf.2.2.1.2.1
  set g := aclArea f a b c d with hgdef
  set L := K * (|deriv g t₀| + 1) with hL
  set s := ∑ i ∈ Finset.range n, dist (E i).1 (E i).2 with hs
  have hL0 : 0 < L := by positivity
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => dist_nonneg
  have hmem' : ∀ i ∈ Finset.range n, (E i).1 ∈ Icc a b ∧ (E i).2 ∈ Icc a b := by
    intro i hi
    have := hE.1 i hi
    rwa [uIcc_of_le hab.le] at this
  -- the derivative bound: for small `h > 0`, `g (t₀ + h) - g t₀ ≤ (|g'(t₀)| + 1) h`
  have hT := hasDerivAt_iff_tendsto_slope_zero.1 hg.hasDerivAt
  obtain ⟨h₀, hh₀, hslope⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 (Metric.tendsto_nhds.1 hT 1 one_pos))
  have hgbound : ∀ h : ℝ, 0 < h → h < h₀ → g (t₀ + h) - g t₀ ≤ (|deriv g t₀| + 1) * h := by
    intro h hh hhh₀
    have hd : dist h 0 < h₀ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hh]
      exact hhh₀
    have h1 := hslope hd hh.ne'
    rw [Real.dist_eq, smul_eq_mul] at h1
    have h2 : h⁻¹ * (g (t₀ + h) - g t₀) ≤ |deriv g t₀| + 1 := by
      have := (abs_sub_lt_iff.1 h1).1
      linarith [le_abs_self (deriv g t₀)]
    calc g (t₀ + h) - g t₀ = h * (h⁻¹ * (g (t₀ + h) - g t₀)) := by field_simp
      _ ≤ h * (|deriv g t₀| + 1) := mul_le_mul_of_nonneg_left h2 hh.le
      _ = (|deriv g t₀| + 1) * h := mul_comm _ _
  -- it suffices to prove the bound up to `2 n η` for every `η > 0`
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set η := ε / (2 * n + 1) with hη
  have hη0 : 0 < η := by positivity
  have hηε : 2 * (n : ℝ) * η ≤ ε := by
    rw [hη, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  -- uniform continuity of `f` on the closed rectangle
  obtain ⟨ρ, hρ0, hρ⟩ := Metric.uniformContinuousOn_iff.1
    ((acl_isCompact_closedRect a b c d).uniformContinuousOn_of_continuous (hc.mono hR)) η hη0
  -- the height of the thin rectangles
  set h := min (min (ρ / 2) (h₀ / 2)) ((d - t₀) / 2) with hh
  have hh0 : 0 < h := lt_min (lt_min (half_pos hρ0) (half_pos hh₀)) (half_pos (sub_pos.2 ht₀.2))
  have hhρ : h < ρ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (half_lt_self hρ0)
  have hhh₀ : h < h₀ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (half_lt_self hh₀)
  have htd : t₀ + h ≤ d := by
    have := min_le_right (min (ρ / 2) (h₀ / 2)) ((d - t₀) / 2)
    linarith
  have hρ' : ∀ x, a ≤ x → x ≤ b → ∀ τ ∈ Icc (0 : ℝ) h,
      dist (f ((x : ℂ) + (t₀ : ℂ) * I)) (f ((x : ℂ) + ((t₀ + τ : ℝ) : ℂ) * I)) < η := by
    intro x hax hxb τ hτ
    apply hρ
    · exact acl_mem_closedRect hax hxb ht₀.1.le ht₀.2.le
    · exact acl_mem_closedRect hax hxb (by linarith [ht₀.1, hτ.1]) (by linarith [hτ.2])
    · rw [acl_dist_vert, abs_of_nonneg hτ.1]
      linarith [hτ.2]
  -- the per-rectangle estimates
  set u : ℕ → ℝ := fun i => max (dist (f (((E i).1 : ℂ) + (t₀ : ℂ) * I))
    (f (((E i).2 : ℂ) + (t₀ : ℂ) * I)) - 2 * η) 0 with hu
  set v : ℕ → ℝ := fun i =>
    (volume (f '' openRect (min (E i).1 (E i).2) (max (E i).1 (E i).2) t₀ (t₀ + h))).toReal with hv
  have hu0 : ∀ i, 0 ≤ u i := fun i => le_max_right _ _
  have hv0 : ∀ i, 0 ≤ v i := fun i => ENNReal.toReal_nonneg
  have hper : ∀ i ∈ Finset.range n, u i ^ 2 / dist (E i).1 (E i).2 ≤ K / h * v i := by
    intro i hi
    obtain ⟨h1, h2⟩ := hmem' i hi
    rcases eq_or_ne (E i).1 (E i).2 with heq | hne
    · have hu' : u i = 0 := by
        simp only [hu, heq, dist_self]
        exact max_eq_right (by linarith)
      rw [hu', heq, dist_self]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
      positivity
    · have hlt : min (E i).1 (E i).2 < max (E i).1 (E i).2 := min_lt_max.2 hne
      have hest := acl_rect_estimate hf hR hlt hh0 (le_min h1.1 h2.1) (max_le h1.2 h2.2)
        ht₀.1.le htd hρ'
      have hm : dist (f (((min (E i).1 (E i).2 : ℝ) : ℂ) + (t₀ : ℂ) * I))
          (f (((max (E i).1 (E i).2 : ℝ) : ℂ) + (t₀ : ℂ) * I)) =
          dist (f (((E i).1 : ℂ) + (t₀ : ℂ) * I)) (f (((E i).2 : ℂ) + (t₀ : ℂ) * I)) := by
        rcases le_total (E i).1 (E i).2 with hle | hle
        · rw [min_eq_left hle, max_eq_right hle]
        · rw [min_eq_right hle, max_eq_left hle, dist_comm]
      have hℓ : dist (E i).1 (E i).2 = max (E i).1 (E i).2 - min (E i).1 (E i).2 := by
        rw [Real.dist_eq, max_sub_min_eq_abs']
      rw [hm] at hest
      have hℓ0 : 0 < max (E i).1 (E i).2 - min (E i).1 (E i).2 := sub_pos.2 hlt
      rw [hℓ, div_le_iff₀ hℓ0]
      calc u i ^ 2 = (u i ^ 2 * (h / ((max (E i).1 (E i).2 - min (E i).1 (E i).2) * K))) *
            ((max (E i).1 (E i).2 - min (E i).1 (E i).2) * K / h) := by
            field_simp
        _ ≤ v i * ((max (E i).1 (E i).2 - min (E i).1 (E i).2) * K / h) :=
            mul_le_mul_of_nonneg_right hest (by positivity)
        _ = K / h * v i * (max (E i).1 (E i).2 - min (E i).1 (E i).2) := by ring
  -- summing up
  have hsumv : ∑ i ∈ Finset.range n, v i ≤ g (t₀ + h) - g t₀ :=
    acl_sum_volume_le hc hinj hab.le hR hh0 ht₀.1.le htd hE
  have hsum1 : ∑ i ∈ Finset.range n, u i ^ 2 / dist (E i).1 (E i).2 ≤ L := by
    calc ∑ i ∈ Finset.range n, u i ^ 2 / dist (E i).1 (E i).2
        ≤ ∑ i ∈ Finset.range n, K / h * v i := Finset.sum_le_sum hper
      _ = K / h * ∑ i ∈ Finset.range n, v i := by rw [Finset.mul_sum]
      _ ≤ K / h * ((|deriv g t₀| + 1) * h) :=
          mul_le_mul_of_nonneg_left (hsumv.trans (hgbound h hh0 hhh₀)) (by positivity)
      _ = L := by
          rw [hL]
          field_simp
  -- Schwarz's inequality
  have hCS : (∑ i ∈ Finset.range n, u i) ^ 2 ≤ s * L := by
    have h1 : ∀ i ∈ Finset.range n,
        u i = Real.sqrt (dist (E i).1 (E i).2) * (u i / Real.sqrt (dist (E i).1 (E i).2)) := by
      intro i _
      rcases eq_or_ne (dist (E i).1 (E i).2) 0 with h0 | h0
      · have heq : (E i).1 = (E i).2 := dist_eq_zero.1 h0
        have hu' : u i = 0 := by
          simp only [hu, heq, dist_self]
          exact max_eq_right (by linarith)
        rw [hu', h0]
        simp
      · rw [mul_div_cancel₀ _ (Real.sqrt_ne_zero'.2 (lt_of_le_of_ne dist_nonneg (Ne.symm h0)))]
    calc (∑ i ∈ Finset.range n, u i) ^ 2
        = (∑ i ∈ Finset.range n, Real.sqrt (dist (E i).1 (E i).2) *
            (u i / Real.sqrt (dist (E i).1 (E i).2))) ^ 2 := by rw [Finset.sum_congr rfl h1]
      _ ≤ (∑ i ∈ Finset.range n, Real.sqrt (dist (E i).1 (E i).2) ^ 2) *
            ∑ i ∈ Finset.range n, (u i / Real.sqrt (dist (E i).1 (E i).2)) ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = s * ∑ i ∈ Finset.range n, u i ^ 2 / dist (E i).1 (E i).2 := by
          congr 1
          · exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt dist_nonneg
          · exact Finset.sum_congr rfl fun i _ => by rw [div_pow, Real.sq_sqrt dist_nonneg]
      _ ≤ s * L := mul_le_mul_of_nonneg_left hsum1 hs0
  have hsumu : ∑ i ∈ Finset.range n, u i ≤ Real.sqrt (L * s) := by
    rw [mul_comm]
    exact (le_abs_self _).trans (Real.abs_le_sqrt hCS)
  calc ∑ i ∈ Finset.range n,
        dist (f (((E i).1 : ℂ) + (t₀ : ℂ) * I)) (f (((E i).2 : ℂ) + (t₀ : ℂ) * I))
      ≤ ∑ i ∈ Finset.range n, (u i + 2 * η) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := le_max_left (dist (f (((E i).1 : ℂ) + (t₀ : ℂ) * I))
          (f (((E i).2 : ℂ) + (t₀ : ℂ) * I)) - 2 * η) 0
        simp only [hu]
        linarith
    _ = ∑ i ∈ Finset.range n, u i + 2 * n * η := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ Real.sqrt (L * s) + ε := add_le_add hsumu hηε

/-- The horizontal half of Theorem 9.1: `f` is absolutely continuous on almost every horizontal
line of a closed rectangle `R̄ ⊂ D`. -/
theorem acl_horizontal {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hR : closedRect a b c d ⊆ D) :
    ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)),
      AbsolutelyContinuousOnInterval (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) a b := by
  have _hcd := hcd
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hf.2.1
  have hmono := acl_monotone_aclArea hf.2.2.1.1 hR
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hmono.ae_differentiableAt] with t₀ hg ht₀
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  set L := K * (|deriv (aclArea f a b c d) t₀| + 1) with hL
  have hL0 : 0 < L := by positivity
  refine ⟨ε ^ 2 / (2 * L), by positivity, ?_⟩
  rintro ⟨n, E⟩ hE hlen
  have h := acl_sum_dist_le hf hab hR ht₀ hg hE
  refine lt_of_le_of_lt h ?_
  rw [Real.sqrt_lt' hε]
  calc L * ∑ i ∈ Finset.range n, dist (E i).1 (E i).2 < L * (ε ^ 2 / (2 * L)) :=
        mul_lt_mul_of_pos_left hlen hL0
    _ = ε ^ 2 / 2 := by field_simp
    _ < ε ^ 2 := by linarith [pow_pos hε 2]

/-- The vertical half of Theorem 9.1, obtained from the horizontal half for `f ∘ (i ·)`. -/
theorem acl_vertical {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hR : closedRect a b c d ⊆ D) :
    ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)),
      AbsolutelyContinuousOnInterval (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) c d := by
  set r : ℂ → ℂ := fun z => I * z with hr
  have hrsurj : Function.Surjective r := fun w =>
    ⟨-I * w, by
      show I * (-I * w) = w
      rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]⟩
  have hrconf : IsConformalOnto r (r ⁻¹' D) D :=
    ⟨(by rw [hr]; fun_prop : Differentiable ℂ r).differentiableOn,
      fun z _ w _ h => mul_left_cancel₀ I_ne_zero h, image_preimage_eq D hrsurj⟩
  have hD' : IsOpen (r ⁻¹' D) := hf.1.preimage (by rw [hr]; fun_prop)
  have hg : IsKQC (f ∘ r) (r ⁻¹' D) K := by
    have h := thm7_1_comp (isKQC_one_of_conformal hD' hrconf) hf (by rw [hrconf.2.2])
    simpa using h
  have hR' : closedRect c d (-b) (-a) ⊆ r ⁻¹' D := by
    intro w hw
    show I * w ∈ D
    apply hR
    have hre : (I * w).re = -w.im := by simp
    have him : (I * w).im = w.re := by simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hre]; linarith [hw.2.2.2]
    · rw [hre]; linarith [hw.2.2.1]
    · rw [him]; exact hw.1
    · rw [him]; exact hw.2.1
  have h := acl_horizontal hg hcd (by linarith : -b < -a) hR'
  have hpre : (fun x : ℝ => -x) ⁻¹' Ioo (-b) (-a) = Ioo a b := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  have hneg : MeasurePreserving (fun x : ℝ => -x) (volume.restrict (Ioo a b))
      (volume.restrict (Ioo (-b) (-a))) := by
    have := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
      (measurableSet_Ioo (a := -b) (b := -a))
    rwa [show (Neg.neg : ℝ → ℝ) ⁻¹' Ioo (-b) (-a) = Ioo a b from hpre] at this
  have h' := hneg.quasiMeasurePreserving.ae h
  filter_upwards [h'] with x hx
  have e : (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) =
      fun u : ℝ => (f ∘ r) ((u : ℂ) + ((-x : ℝ) : ℂ) * I) := by
    funext y
    simp only [Function.comp_apply, hr]
    congr 1
    push_cast
    linear_combination (x : ℂ) * I_sq
  rw [e]
  exact hx

/-! ### Helpers for Theorem 9.2 (`acl_`): from A.C.L. to partial derivatives a.e.

Absolutely continuous functions are differentiable a.e. (Mathlib, real-valued; apply it to the
real and imaginary parts).  To pass from "for a.e. `y`, for a.e. `x`" to "for a.e. `z`" on an open
rectangle one needs the differentiability set to be measurable; on a closed rectangle `f` is
extended by Tietze to a continuous `g : ℂ → ℂ`, whose line-differentiability set is measurable
(`measurableSet_lineDifferentiableAt`), and `f`, `g` agree near every point of the open rectangle.
`D` is then covered by countably many rational rectangles. -/

theorem acl_AC_re {φ : ℝ → ℂ} {a b : ℝ} (hφ : AbsolutelyContinuousOnInterval φ a b) :
    AbsolutelyContinuousOnInterval (fun x => (φ x).re) a b := by
  apply squeeze_zero (fun t ↦ ?_) (fun t ↦ ?_) hφ
  · exact Finset.sum_nonneg fun i _ => dist_nonneg
  · gcongr with i _
    rw [Real.dist_eq, dist_eq_norm, ← sub_re]
    exact Complex.abs_re_le_norm _

theorem acl_AC_im {φ : ℝ → ℂ} {a b : ℝ} (hφ : AbsolutelyContinuousOnInterval φ a b) :
    AbsolutelyContinuousOnInterval (fun x => (φ x).im) a b := by
  apply squeeze_zero (fun t ↦ ?_) (fun t ↦ ?_) hφ
  · exact Finset.sum_nonneg fun i _ => dist_nonneg
  · gcongr with i _
    rw [Real.dist_eq, dist_eq_norm, ← sub_im]
    exact Complex.abs_im_le_norm _

theorem acl_differentiableAt_of_re_im {φ : ℝ → ℂ} {x : ℝ}
    (h1 : DifferentiableAt ℝ (fun t => (φ t).re) x)
    (h2 : DifferentiableAt ℝ (fun t => (φ t).im) x) : DifferentiableAt ℝ φ x := by
  have hd : HasDerivAt (fun t => (((φ t).re : ℝ) : ℂ) + (((φ t).im : ℝ) : ℂ) * I)
      (((deriv (fun t => (φ t).re) x : ℝ) : ℂ) + ((deriv (fun t => (φ t).im) x : ℝ) : ℂ) * I) x :=
    (h1.hasDerivAt.ofReal_comp).add (h2.hasDerivAt.ofReal_comp.mul_const I)
  have e : (fun t => (((φ t).re : ℝ) : ℂ) + (((φ t).im : ℝ) : ℂ) * I) = φ :=
    funext fun t => Complex.re_add_im _
  rw [e] at hd
  exact hd.differentiableAt

/-- An absolutely continuous `ℂ`-valued function is differentiable a.e. on the interval. -/
theorem acl_AC_ae_differentiableAt {φ : ℝ → ℂ} {a b : ℝ}
    (hφ : AbsolutelyContinuousOnInterval φ a b) :
    ∀ᵐ x, x ∈ uIcc a b → DifferentiableAt ℝ φ x := by
  filter_upwards [(acl_AC_re hφ).ae_differentiableAt, (acl_AC_im hφ).ae_differentiableAt]
    with x h1 h2 hx
  exact acl_differentiableAt_of_re_im (h1 hx) (h2 hx)

/-- Tietze: a function continuous on a closed set extends to a continuous function on `ℂ`. -/
theorem acl_exists_continuous_ext {f : ℂ → ℂ} {s : Set ℂ} (hs : IsClosed s)
    (hc : ContinuousOn f s) : ∃ g : ℂ → ℂ, Continuous g ∧ EqOn g f s := by
  have hres : Continuous (s.restrict f) := continuousOn_iff_continuous_restrict.1 hc
  obtain ⟨g₁, -, hg₁⟩ := ContinuousMap.exists_restrict_eq_forall_mem_of_closed
    (⟨fun z : s => (f z).re, Complex.continuous_re.comp hres⟩ : C(s, ℝ)) (t := univ)
    (fun _ => mem_univ _) univ_nonempty hs
  obtain ⟨g₂, -, hg₂⟩ := ContinuousMap.exists_restrict_eq_forall_mem_of_closed
    (⟨fun z : s => (f z).im, Complex.continuous_im.comp hres⟩ : C(s, ℝ)) (t := univ)
    (fun _ => mem_univ _) univ_nonempty hs
  refine ⟨fun z => (g₁ z : ℂ) + (g₂ z : ℂ) * I,
    (Complex.continuous_ofReal.comp g₁.continuous).add
      ((Complex.continuous_ofReal.comp g₂.continuous).mul continuous_const), fun z hz => ?_⟩
  have e1 : g₁ z = (f z).re := by
    have := ContinuousMap.congr_fun hg₁ ⟨z, hz⟩
    simpa using this
  have e2 : g₂ z = (f z).im := by
    have := ContinuousMap.congr_fun hg₂ ⟨z, hz⟩
    simpa using this
  simp only [e1, e2]
  exact Complex.re_add_im _

theorem acl_measurableSet_horizontal {g : ℂ → ℂ} (hg : Continuous g) :
    MeasurableSet {z : ℂ | DifferentiableAt ℝ (fun t : ℝ => g (z + t)) 0} := by
  have e : {z : ℂ | DifferentiableAt ℝ (fun t : ℝ => g (z + t)) 0} =
      {z : ℂ | LineDifferentiableAt ℝ g z 1} := by
    ext z
    simp only [LineDifferentiableAt, mem_setOf_eq, Complex.real_smul, mul_one]
  rw [e]
  exact measurableSet_lineDifferentiableAt hg

theorem acl_measurableSet_vertical {g : ℂ → ℂ} (hg : Continuous g) :
    MeasurableSet {z : ℂ | DifferentiableAt ℝ (fun t : ℝ => g (z + t * I)) 0} := by
  have e : {z : ℂ | DifferentiableAt ℝ (fun t : ℝ => g (z + t * I)) 0} =
      {z : ℂ | LineDifferentiableAt ℝ g z I} := by
    ext z
    simp only [LineDifferentiableAt, mem_setOf_eq, Complex.real_smul]
  rw [e]
  exact measurableSet_lineDifferentiableAt hg

theorem acl_differentiableAt_congr_horiz {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hfg : EqOn g f U) {z : ℂ} (hz : z ∈ U) :
    DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ↔
      DifferentiableAt ℝ (fun t : ℝ => g (z + t)) 0 := by
  have hev : (fun t : ℝ => f (z + t)) =ᶠ[𝓝 0] fun t => g (z + t) := by
    have hcont : Continuous fun t : ℝ => z + (t : ℂ) := by fun_prop
    have h0 : z + ((0 : ℝ) : ℂ) ∈ U := by simpa using hz
    filter_upwards [hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)] with t ht
    exact (hfg ht).symm
  exact hev.differentiableAt_iff

theorem acl_differentiableAt_congr_vert {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hfg : EqOn g f U) {z : ℂ} (hz : z ∈ U) :
    DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0 ↔
      DifferentiableAt ℝ (fun t : ℝ => g (z + t * I)) 0 := by
  have hev : (fun t : ℝ => f (z + t * I)) =ᶠ[𝓝 0] fun t => g (z + t * I) := by
    have hcont : Continuous fun t : ℝ => z + (t : ℂ) * I := by fun_prop
    have h0 : z + ((0 : ℝ) : ℂ) * I ∈ U := by simpa using hz
    filter_upwards [hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)] with t ht
    exact (hfg ht).symm
  exact hev.differentiableAt_iff

theorem acl_ae_prod_of_ae_ae_swap {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] {T : Set (ℝ × ℝ)}
    (hT : MeasurableSet T) (h : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, (x, y) ∈ T) : ∀ᵐ p ∂(μ.prod ν), p ∈ T := by
  have h' : ∀ᵐ q ∂(ν.prod μ), q ∈ Prod.swap ⁻¹' T :=
    (Measure.ae_prod_mem_iff_ae_ae_mem (measurable_swap hT)).2 h
  filter_upwards [(Measure.measurePreserving_swap (μ := μ) (ν := ν)).quasiMeasurePreserving.ae h']
    with p hp
  simpa using hp

/-- Transfer of an a.e. statement from the product `(a,b) × (c,d)` to the open rectangle. -/
theorem acl_ae_openRect_of_ae_prod {a b c d : ℝ} {S : Set ℂ}
    (h : ∀ᵐ p ∂((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))),
      (p.1 : ℂ) + (p.2 : ℂ) * I ∈ S) :
    ∀ᵐ z ∂(volume.restrict (openRect a b c d)), z ∈ S := by
  have hmp := Complex.volume_preserving_equiv_real_prod
  have hpre : Complex.measurableEquivRealProd ⁻¹' (Ioo a b ×ˢ Ioo c d) = openRect a b c d := by
    ext z
    simp only [mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod, mem_Ioo, openRect,
      mem_setOf_eq]
    tauto
  rw [Measure.prod_restrict] at h
  have hq := (hmp.restrict_preimage (s := Ioo a b ×ˢ Ioo c d)
    (measurableSet_Ioo.prod measurableSet_Ioo)).quasiMeasurePreserving
  rw [hpre] at hq
  filter_upwards [hq.ae h] with z hz
  simpa using hz

theorem acl_openRect_eq (a b c d : ℝ) : openRect a b c d = Ioo a b ×ℂ Ioo c d := by
  ext z
  simp only [openRect, mem_setOf_eq, mem_reProdIm, mem_Ioo]
  tauto

theorem acl_isOpen_openRect (a b c d : ℝ) : IsOpen (openRect a b c d) := by
  rw [acl_openRect_eq]
  exact isOpen_Ioo.reProdIm isOpen_Ioo

theorem acl_mem_openRect {a b c d x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo c d) :
    (x : ℂ) + (y : ℂ) * I ∈ openRect a b c d :=
  ⟨by simpa using hx.1, by simpa using hx.2, by simpa using hy.1, by simpa using hy.2⟩

/-- On an open rectangle `R̄ ⊂ D`, the A.C.L. data give both partial derivatives a.e. -/
theorem acl_ae_rect {f : ℂ → ℂ} {D : Set ℂ} (hc : ContinuousOn f D) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hR : closedRect a b c d ⊆ D)
    (hH : ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)),
      AbsolutelyContinuousOnInterval (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) a b)
    (hV : ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)),
      AbsolutelyContinuousOnInterval (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) c d) :
    ∀ᵐ z ∂(volume.restrict (openRect a b c d)),
      DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
        DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0 := by
  obtain ⟨g, hgc, hgf⟩ :=
    acl_exists_continuous_ext (acl_isCompact_closedRect a b c d).isClosed (hc.mono hR)
  have hgf' : EqOn g f (openRect a b c d) :=
    hgf.mono (acl_openRect_subset_closedRect le_rfl le_rfl le_rfl le_rfl)
  have hUo := acl_isOpen_openRect a b c d
  have hmeas : Measurable fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I).measurable
  -- horizontal derivatives
  have hH' : ∀ᵐ z ∂(volume.restrict (openRect a b c d)),
      z ∈ {z : ℂ | DifferentiableAt ℝ (fun t : ℝ => g (z + t)) 0} := by
    apply acl_ae_openRect_of_ae_prod
    apply acl_ae_prod_of_ae_ae_swap (hmeas (acl_measurableSet_horizontal hgc))
    filter_upwards [hH, self_mem_ae_restrict measurableSet_Ioo] with y hy hyI
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [acl_AC_ae_differentiableAt hy] with x hx hxI
    have hd : DifferentiableAt ℝ (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) x :=
      hx (by rw [uIcc_of_le hab.le]; exact Ioo_subset_Icc_self hxI)
    show DifferentiableAt ℝ (fun t : ℝ => g (((x : ℂ) + (y : ℂ) * I) + t)) 0
    rw [← acl_differentiableAt_congr_horiz hUo hgf' (acl_mem_openRect hxI hyI)]
    have e : (fun t : ℝ => f (((x : ℂ) + (y : ℂ) * I) + t)) =
        (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) ∘ fun t : ℝ => x + t := by
      funext t
      simp only [Function.comp_apply]
      congr 1
      push_cast
      ring
    rw [e]
    have hd' : DifferentiableAt ℝ (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (x + 0) := by
      simpa using hd
    exact hd'.comp 0 (differentiableAt_id.const_add x)
  -- vertical derivatives
  have hV' : ∀ᵐ z ∂(volume.restrict (openRect a b c d)),
      z ∈ {z : ℂ | DifferentiableAt ℝ (fun t : ℝ => g (z + t * I)) 0} := by
    apply acl_ae_openRect_of_ae_prod
    apply (Measure.ae_prod_mem_iff_ae_ae_mem (hmeas (acl_measurableSet_vertical hgc))).2
    filter_upwards [hV, self_mem_ae_restrict measurableSet_Ioo] with x hx hxI
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [acl_AC_ae_differentiableAt hx] with y hy hyI
    have hd : DifferentiableAt ℝ (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) y :=
      hy (by rw [uIcc_of_le hcd.le]; exact Ioo_subset_Icc_self hyI)
    show DifferentiableAt ℝ (fun t : ℝ => g (((x : ℂ) + (y : ℂ) * I) + t * I)) 0
    rw [← acl_differentiableAt_congr_vert hUo hgf' (acl_mem_openRect hxI hyI)]
    have e : (fun t : ℝ => f (((x : ℂ) + (y : ℂ) * I) + t * I)) =
        (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) ∘ fun t : ℝ => y + t := by
      funext t
      simp only [Function.comp_apply]
      congr 1
      push_cast
      ring
    rw [e]
    have hd' : DifferentiableAt ℝ (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (y + 0) := by
      simpa using hd
    exact hd'.comp 0 (differentiableAt_id.const_add y)
  filter_upwards [hH', hV', self_mem_ae_restrict hUo.measurableSet] with z hzH hzV hz
  exact ⟨(acl_differentiableAt_congr_horiz hUo hgf' hz).2 hzH,
    (acl_differentiableAt_congr_vert hUo hgf' hz).2 hzV⟩

/-- Every point of an open set lies in a rational open rectangle whose closure is in the set. -/
theorem acl_exists_rat_rect {D : Set ℂ} (hD : IsOpen D) {z : ℂ} (hz : z ∈ D) :
    ∃ q : ℚ × ℚ × ℚ × ℚ, (q.1 : ℝ) < q.2.1 ∧ (q.2.2.1 : ℝ) < q.2.2.2 ∧
      closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ D ∧ z ∈ openRect q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD z hz
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - ε / 2 < z.re by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.re < z.re + ε / 2 by linarith)
  obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (show z.im - ε / 2 < z.im by linarith)
  obtain ⟨d, hd1, hd2⟩ := exists_rat_btwn (show z.im < z.im + ε / 2 by linarith)
  refine ⟨(a, b, c, d), by linarith, by linarith, fun w hw => ?_, ⟨ha2, hb1, hc2, hd1⟩⟩
  apply hball
  rw [mem_ball, Complex.dist_eq]
  have h1 : |(w - z).re| < ε / 2 := by
    rw [sub_re]
    exact abs_sub_lt_iff.2 ⟨by linarith [hw.2.1], by linarith [hw.1]⟩
  have h2 : |(w - z).im| < ε / 2 := by
    rw [sub_im]
    exact abs_sub_lt_iff.2 ⟨by linarith [hw.2.2.2], by linarith [hw.2.2.1]⟩
  linarith [Complex.norm_le_abs_re_add_abs_im (w - z)]

/-- **Theorem 9.1**: a quasiconformal map is A.C.L.

Proof as in the book: for a closed rectangle `R̄ ⊂ D` the area function `t ↦ m(f(R_t))` is
monotone, hence differentiable a.e.; at a point `t₀` of differentiability the thin rectangles
`(x_k', x_k'') × (t₀, t₀ + δ)` are quadrilaterals of modulus `δ / (x_k'' - x_k')` (`rectQuad`),
Rengel's inequality for their images together with `K`-quasiconformality bounds the distances
`|f(x_k' + i t₀) - f(x_k'' + i t₀)|`, and Cauchy–Schwarz gives the absolute continuity of
`x ↦ f(x + i t₀)`; the vertical statement follows by applying this to `f ∘ (i ·)`. -/
theorem thm9_1_isACL {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) : IsACL f D := by
  refine ⟨hf.2.2.1.1, fun a b c d hab hcd hR => ⟨?_, ?_⟩⟩
  · exact acl_vertical hf hab hcd hR
  · exact acl_horizontal hf hab hcd hR

/-- **Theorem 9.2**: a quasiconformal map has partial derivatives almost everywhere.

By Theorem 9.1 and the a.e. differentiability of absolutely continuous functions (applied to the
real and imaginary parts), on a.e. horizontal (resp. vertical) line through a closed rectangle
`R̄ ⊂ D` the partial derivative `f'_x` (resp. `f'_y`) exists a.e.; Fubini turns this into an a.e.
statement on the open rectangle, the measurability of the exceptional set being obtained by
extending `f` continuously to `ℂ` (Tietze) and using `measurableSet_lineDifferentiableAt`.
Finally `D` is the union of countably many rational rectangles. -/
theorem thm9_2_partials_ae {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) :
    ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
      DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0 := by
  obtain ⟨hc, hrect⟩ := thm9_1_isACL hf
  have hD : IsOpen D := hf.1
  -- the countable cover of `D` by rational open rectangles with closure in `D`
  have hcover : D = ⋃ q : {q : ℚ × ℚ × ℚ × ℚ // (q.1 : ℝ) < q.2.1 ∧ (q.2.2.1 : ℝ) < q.2.2.2 ∧
      closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ D}, openRect q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 := by
    ext z
    constructor
    · intro hz
      obtain ⟨q, h1, h2, h3, h4⟩ := acl_exists_rat_rect hD hz
      exact mem_iUnion.2 ⟨⟨q, h1, h2, h3⟩, h4⟩
    · intro hz
      obtain ⟨q, hq⟩ := mem_iUnion.1 hz
      exact q.2.2.2 (acl_openRect_subset_closedRect le_rfl le_rfl le_rfl le_rfl hq)
  rw [hcover, ae_restrict_iUnion_iff]
  intro q
  exact acl_ae_rect hc q.2.1 q.2.2.1 q.2.2.2 (hrect _ _ _ _ q.2.1 q.2.2.1 q.2.2.2).2
    (hrect _ _ _ _ q.2.1 q.2.2.1 q.2.2.2).1


/-! ## M1: the maximum-modulus principle for open maps on a closed rectangle. -/

theorem menchoff_interior_closedRect (a b c d : ℝ) :
    interior (closedRect a b c d) = openRect a b c d := by
  rw [acl_closedRect_eq, acl_openRect_eq, interior_reProdIm, interior_Icc, interior_Icc]

/-- For any `v : ℂ` and `t ≥ 0` there is a unit vector `dir` with `‖v + t • dir‖ = ‖v‖ + t`
(move away from the origin along `v`'s own direction, or along an arbitrary direction if `v = 0`). -/
theorem menchoff_exists_dir_add_norm (v : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ dir : ℂ, ‖dir‖ = 1 ∧ ‖v + (t : ℂ) * dir‖ = ‖v‖ + t := by
  by_cases hv : v = 0
  · refine ⟨1, by simp, ?_⟩
    simp only [hv, zero_add, mul_one, norm_zero, norm_real]
    exact abs_of_nonneg ht
  · have hvnn : (0:ℝ) < ‖v‖ := norm_pos_iff.2 hv
    have hvne : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast hvnn.ne'
    refine ⟨v / (‖v‖ : ℂ), ?_, ?_⟩
    · rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hvnn, div_self hvnn.ne']
    · have heq : v + (t : ℂ) * (v / (‖v‖ : ℂ)) = ((‖v‖ + t : ℝ) : ℂ) * (v / (‖v‖ : ℂ)) := by
        push_cast
        field_simp
      rw [heq, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith),
        norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hvnn, div_self hvnn.ne', mul_one]

/-- If `f` is continuous on a closed rectangle `R̄ ⊆ D` and maps open subsets of `D` to open sets,
then for any `w`, `‖f z - w‖` (for `z ∈ R̄`) attains its max at a frontier point of `R̄`. -/
theorem menchoff_max_principle {f : ℂ → ℂ} {D : Set ℂ} (hc : ContinuousOn f D)
    (hopen : ∀ U ⊆ D, IsOpen U → IsOpen (f '' U)) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hQ : closedRect a b c d ⊆ D) (w : ℂ) {z : ℂ} (hz : z ∈ closedRect a b c d) :
    ∃ ζ ∈ frontier (closedRect a b c d), ‖f z - w‖ ≤ ‖f ζ - w‖ := by
  set Q := closedRect a b c d with hQ_def
  have hQcpt : IsCompact Q := acl_isCompact_closedRect a b c d
  have hQne : Q.Nonempty := ⟨z, hz⟩
  have hcont : ContinuousOn (fun ζ => ‖f ζ - w‖) Q :=
    ((hc.mono hQ).sub continuousOn_const).norm
  obtain ⟨z₀, hz₀Q, hz₀max0⟩ := hQcpt.exists_isMaxOn hQne hcont
  rw [isMaxOn_iff] at hz₀max0
  have hz₀max : ∀ ζ ∈ Q, ‖f ζ - w‖ ≤ ‖f z₀ - w‖ := hz₀max0
  refine ⟨z₀, ?_, hz₀max z hz⟩
  by_contra hz₀nf
  have hfr : frontier Q = Q \ interior Q := by
    rw [frontier, hQcpt.isClosed.closure_eq]
  have hz₀int : z₀ ∈ interior Q := by
    by_contra hnotin
    exact hz₀nf (hfr ▸ (⟨hz₀Q, hnotin⟩ : z₀ ∈ Q \ interior Q))
  rw [hQ_def, menchoff_interior_closedRect] at hz₀int
  set U := openRect a b c d with hU_def
  have hUD : U ⊆ D := (acl_openRect_subset_closedRect le_rfl le_rfl le_rfl le_rfl).trans hQ
  have hUo : IsOpen U := acl_isOpen_openRect a b c d
  have hUQ : U ⊆ Q := acl_openRect_subset_closedRect le_rfl le_rfl le_rfl le_rfl
  have hfU_open : IsOpen (f '' U) := hopen U hUD hUo
  have hfz₀mem : f z₀ ∈ f '' U := mem_image_of_mem f hz₀int
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hfU_open (f z₀) hfz₀mem
  obtain ⟨dir, hdir1, hdireq⟩ := menchoff_exists_dir_add_norm (f z₀ - w) (t := ε / 2) (by linarith)
  set p : ℂ := f z₀ + (ε / 2 : ℝ) * dir with hp_def
  have hpball : p ∈ Metric.ball (f z₀) ε := by
    rw [mem_ball, dist_eq_norm, hp_def]
    have heq0 : (f z₀ + (ε/2:ℝ) * dir) - f z₀ = (ε/2:ℝ) * dir := by ring
    rw [heq0, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < ε/2),
      hdir1, mul_one]
    linarith
  obtain ⟨ζ, hζU, hζp⟩ := hball hpball
  have hζQ : ζ ∈ Q := hUQ hζU
  have hcontra : ‖f ζ - w‖ ≤ ‖f z₀ - w‖ := hz₀max ζ hζQ
  rw [hζp] at hcontra
  have heq2 : p - w = (f z₀ - w) + (ε/2 : ℝ) * dir := by rw [hp_def]; ring
  rw [heq2, hdireq] at hcontra
  linarith

/-! ## M2: Egorov on the difference quotients. -/

/-- If `h : ℝ → ℝ≥0∞` is continuous on `S` and `c : ι → ℝ` has range in `S` and dense in `S`
(every point of `S` is approximated arbitrarily well by values of `c`), then the supremum of `h`
along `c` equals the supremum of `h` over `S`. -/
theorem menchoff_iSup_dense_eq {h : ℝ → ℝ≥0∞} {S : Set ℝ} {ι : Type*} {c : ι → ℝ}
    (hcS : ∀ i, c i ∈ S) (hd : ∀ x ∈ S, ∀ ε > 0, ∃ i, |c i - x| < ε)
    (hh : ContinuousOn h S) :
    (⨆ i, h (c i)) = ⨆ x ∈ S, h x := by
  apply le_antisymm
  · exact iSup_le fun i => le_iSup₂ (f := fun x (_ : x ∈ S) => h x) (c i) (hcS i)
  · refine iSup₂_le fun x hx => ?_
    have hseq : ∀ n : ℕ, ∃ i, |c i - x| < 1 / (n + 1) := fun n => hd x hx _ (by positivity)
    choose v hvx using hseq
    have hvtend : Tendsto (fun n => c (v n)) atTop (𝓝 x) := by
      rw [tendsto_iff_dist_tendsto_zero]
      apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      rw [Real.dist_eq]
      exact (hvx n).le
    have hcont : ContinuousWithinAt h S x := hh x hx
    have hlim : Tendsto (fun n => h (c (v n))) atTop (𝓝 (h x)) :=
      hcont.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hvtend
        (Eventually.of_forall fun n => hcS (v n)))
    exact le_of_tendsto' hlim fun n => le_iSup (fun i => h (c i)) (v n)

/-- The horizontal directional derivative of `g` at `z`, as a real-parameter derivative. -/
def menchoffFx (g : ℂ → ℂ) (z : ℂ) : ℂ := deriv (fun t : ℝ => g (z + t)) 0

/-- The vertical directional derivative of `g` at `z`. -/
def menchoffFy (g : ℂ → ℂ) (z : ℂ) : ℂ := deriv (fun t : ℝ => g (z + t * I)) 0

theorem menchoff_measurable_fx {g : ℂ → ℂ} (hg : Continuous g) : Measurable (menchoffFx g) := by
  have hcu : Continuous (Function.uncurry fun (z : ℂ) (t : ℝ) => g (z + t)) := by fun_prop
  have hm := measurable_deriv_with_param (𝕜 := ℝ) hcu
  have : menchoffFx g = (fun p : ℂ × ℝ => deriv (fun t : ℝ => g (p.1 + t)) p.2) ∘
      (fun z => (z, (0:ℝ))) := rfl
  rw [this]
  exact hm.comp (by fun_prop)

theorem menchoff_measurable_fy {g : ℂ → ℂ} (hg : Continuous g) : Measurable (menchoffFy g) := by
  have hcu : Continuous (Function.uncurry fun (z : ℂ) (t : ℝ) => g (z + t * I)) := by fun_prop
  have hm := measurable_deriv_with_param (𝕜 := ℝ) hcu
  have : menchoffFy g = (fun p : ℂ × ℝ => deriv (fun t : ℝ => g (p.1 + t * I)) p.2) ∘
      (fun z => (z, (0:ℝ))) := rfl
  rw [this]
  exact hm.comp (by fun_prop)

/-- The rational-step index set for scale `n`: rationals `q` with `0 < |q| < 1/(n+1)`. -/
abbrev menchoffQIdx (n : ℕ) := {q : ℚ // 0 < |(q:ℝ)| ∧ |(q:ℝ)| < 1 / (n + 1)}

/-- The `n`-th horizontal difference-quotient defect at `z`, as a sup over rational steps. -/
def menchoffGn (g : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℝ≥0∞ :=
  ⨆ q : menchoffQIdx n, ‖slope (fun t : ℝ => g (z + t)) 0 (q : ℝ) - menchoffFx g z‖ₑ

/-- The `n`-th vertical difference-quotient defect at `z`. -/
def menchoffHn (g : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℝ≥0∞ :=
  ⨆ q : menchoffQIdx n, ‖slope (fun t : ℝ => g (z + t * I)) 0 (q : ℝ) - menchoffFy g z‖ₑ

theorem menchoff_measurable_gn {g : ℂ → ℂ} (hg : Continuous g) (n : ℕ) :
    Measurable (menchoffGn g n) := by
  apply Measurable.iSup
  intro q
  have hslope : Continuous (fun z : ℂ => slope (fun t : ℝ => g (z + t)) 0 (q : ℝ)) := by
    have : (fun z : ℂ => slope (fun t : ℝ => g (z + t)) 0 (q : ℝ)) =
        fun z : ℂ => ((q : ℝ))⁻¹ • (g (z + (q:ℝ)) - g z) := by
      funext z
      simp [slope, vsub_eq_sub]
    rw [this]
    fun_prop
  exact (hslope.measurable.sub (menchoff_measurable_fx hg)).enorm

theorem menchoff_measurable_hn {g : ℂ → ℂ} (hg : Continuous g) (n : ℕ) :
    Measurable (menchoffHn g n) := by
  apply Measurable.iSup
  intro q
  have hslope : Continuous (fun z : ℂ => slope (fun t : ℝ => g (z + t * I)) 0 (q : ℝ)) := by
    have : (fun z : ℂ => slope (fun t : ℝ => g (z + t * I)) 0 (q : ℝ)) =
        fun z : ℂ => ((q : ℝ))⁻¹ • (g (z + (q:ℝ) * I) - g z) := by
      funext z
      simp [slope, vsub_eq_sub]
    rw [this]
    fun_prop
  exact (hslope.measurable.sub (menchoff_measurable_fy hg)).enorm

theorem menchoff_gn_tendsto_zero {g : ℂ → ℂ} {z : ℂ}
    (hz : DifferentiableAt ℝ (fun t : ℝ => g (z + t)) 0) :
    Tendsto (fun n => menchoffGn g n z) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact Eventually.of_forall fun _ => le_top
  · have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    have hderiv : HasDerivAt (fun t : ℝ => g (z + t)) (menchoffFx g z) 0 := hz.hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds] at hderiv
    obtain ⟨δ, hδ, hδprop⟩ := hderiv ε.toReal hε'
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    filter_upwards [eventually_ge_atTop N] with n hn
    unfold menchoffGn
    refine iSup_le fun q => ?_
    have hqne0 : (q.1 : ℝ) ≠ 0 := abs_pos.mp q.2.1
    have hqlt : |(q.1 : ℝ)| < 1 / (n + 1 : ℝ) := q.2.2
    have hnle : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact_mod_cast Nat.add_le_add_right hn 1
    have hdist : dist (q.1 : ℝ) 0 < δ := by
      rw [Real.dist_eq, sub_zero]
      linarith
    have hbound := hδprop (x := (q.1 : ℝ)) hqne0 hdist
    rw [dist_eq_norm] at hbound
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal hbound.le).trans_eq (ENNReal.ofReal_toReal hεtop)

theorem menchoff_hn_tendsto_zero {g : ℂ → ℂ} {z : ℂ}
    (hz : DifferentiableAt ℝ (fun t : ℝ => g (z + t * I)) 0) :
    Tendsto (fun n => menchoffHn g n z) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact Eventually.of_forall fun _ => le_top
  · have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    have hderiv : HasDerivAt (fun t : ℝ => g (z + t * I)) (menchoffFy g z) 0 := hz.hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds] at hderiv
    obtain ⟨δ, hδ, hδprop⟩ := hderiv ε.toReal hε'
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    filter_upwards [eventually_ge_atTop N] with n hn
    unfold menchoffHn
    refine iSup_le fun q => ?_
    have hqne0 : (q.1 : ℝ) ≠ 0 := abs_pos.mp q.2.1
    have hqlt : |(q.1 : ℝ)| < 1 / (n + 1 : ℝ) := q.2.2
    have hnle : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact_mod_cast Nat.add_le_add_right hn 1
    have hdist : dist (q.1 : ℝ) 0 < δ := by
      rw [Real.dist_eq, sub_zero]
      linarith
    have hbound := hδprop (x := (q.1 : ℝ)) hqne0 hdist
    rw [dist_eq_norm] at hbound
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal hbound.le).trans_eq (ENNReal.ofReal_toReal hεtop)

/-- Density of the rationals in a punctured interval `{x | 0 < |x| < r}`: every real point there
is approximated arbitrarily well by rationals staying in the same punctured interval. -/
theorem menchoff_dense_punctured (r : ℝ) :
    ∀ x ∈ {x : ℝ | 0 < |x| ∧ |x| < r}, ∀ ε > 0,
      ∃ q : ℚ, 0 < |(q:ℝ)| ∧ |(q:ℝ)| < r ∧ |(q:ℝ) - x| < ε := by
  intro x hx ε hε
  set ε' : ℝ := min ε (min |x| (r - |x|)) with hε'_def
  have hε'pos : 0 < ε' := lt_min hε (lt_min hx.1 (by linarith [hx.2]))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x - ε' < x + ε' by linarith)
  have hqx : |(q:ℝ) - x| < ε' := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  refine ⟨q, ?_, ?_, hqx.trans_le (min_le_left _ _)⟩
  · have h1 : |x| - |(q:ℝ) - x| ≤ |(q:ℝ)| := by
      have := abs_sub_abs_le_abs_sub x (q:ℝ)
      linarith [abs_sub_comm x (q:ℝ)]
    have h2 : |(q:ℝ) - x| < |x| := hqx.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  · have h1 : |(q:ℝ)| ≤ |x| + |(q:ℝ) - x| := by
      calc |(q:ℝ)| = |x + ((q:ℝ) - x)| := by ring_nf
        _ ≤ |x| + |(q:ℝ) - x| := abs_add_le x _
    have h2 : |(q:ℝ) - x| < r - |x| := hqx.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith

/-- If the rational-step sup `menchoffGn g n z` is `< ε`, then so is the difference-quotient
defect at every real step `s` in the same range. -/
theorem menchoff_gn_real_bound {g : ℂ → ℂ} (hg : Continuous g) {n : ℕ} {z : ℂ} {ε : ℝ≥0∞}
    (hb : menchoffGn g n z < ε) {s : ℝ} (hs0 : 0 < |s|) (hs1 : |s| < 1 / (n + 1)) :
    ‖slope (fun t : ℝ => g (z + t)) 0 s - menchoffFx g z‖ₑ < ε := by
  have hcont : ContinuousOn (fun x : ℝ => ‖slope (fun t : ℝ => g (z + t)) 0 x - menchoffFx g z‖ₑ)
      {x : ℝ | 0 < |x| ∧ |x| < 1 / (n + 1)} := by
    have heq : ∀ x : ℝ, x ≠ 0 → slope (fun t : ℝ => g (z + t)) 0 x =
        (x : ℝ)⁻¹ • (g (z + x) - g z) := by
      intro x _
      simp [slope, vsub_eq_sub]
    apply ContinuousOn.enorm
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.congr (f := fun x : ℝ => (x:ℝ)⁻¹ • (g (z+x) - g z))
    · have hinv : ContinuousOn (fun x : ℝ => (x : ℝ)⁻¹) {x : ℝ | 0 < |x| ∧ |x| < 1 / (n + 1)} :=
        continuousOn_id.inv₀ (fun x hx => abs_pos.mp hx.1)
      have hgz : Continuous (fun x : ℝ => g (z + x) - g z) := by fun_prop
      exact hinv.smul hgz.continuousOn
    · intro x hx
      exact heq x (abs_pos.mp hx.1)
  have heq2 : (⨆ q : menchoffQIdx n,
        ‖slope (fun t : ℝ => g (z + t)) 0 (q : ℝ) - menchoffFx g z‖ₑ) =
      ⨆ x ∈ {x : ℝ | 0 < |x| ∧ |x| < 1 / (n + 1)},
        ‖slope (fun t : ℝ => g (z + t)) 0 x - menchoffFx g z‖ₑ :=
    menchoff_iSup_dense_eq (c := fun q : menchoffQIdx n => (q.1 : ℝ)) (fun q => q.2)
      (fun x hx ε' hε' => by
        obtain ⟨q, hq1, hq2, hq3⟩ := menchoff_dense_punctured (1 / (n + 1)) x hx ε' hε'
        exact ⟨⟨q, hq1, hq2⟩, hq3⟩) hcont
  have hb2 : (⨆ x ∈ {x : ℝ | 0 < |x| ∧ |x| < 1 / (n + 1)},
      ‖slope (fun t : ℝ => g (z + t)) 0 x - menchoffFx g z‖ₑ) < ε := heq2 ▸ hb
  exact lt_of_le_of_lt (le_iSup₂ (f := fun x
    (_ : x ∈ {x : ℝ | 0 < |x| ∧ |x| < 1 / (n + 1)}) =>
      ‖slope (fun t : ℝ => g (z + t)) 0 x - menchoffFx g z‖ₑ) s ⟨hs0, hs1⟩) hb2

/-- Vertical analogue of `menchoff_gn_real_bound`. -/
theorem menchoff_hn_real_bound {g : ℂ → ℂ} (hg : Continuous g) {n : ℕ} {z : ℂ} {ε : ℝ≥0∞}
    (hb : menchoffHn g n z < ε) {s : ℝ} (hs0 : 0 < |s|) (hs1 : |s| < 1 / (n + 1)) :
    ‖slope (fun t : ℝ => g (z + t * I)) 0 s - menchoffFy g z‖ₑ < ε := by
  have hcont : ContinuousOn
      (fun x : ℝ => ‖slope (fun t : ℝ => g (z + t * I)) 0 x - menchoffFy g z‖ₑ)
      {x : ℝ | 0 < |x| ∧ |x| < 1 / (n + 1)} := by
    have heq : ∀ x : ℝ, x ≠ 0 → slope (fun t : ℝ => g (z + t * I)) 0 x =
        (x : ℝ)⁻¹ • (g (z + x * I) - g z) := by
      intro x _
      simp [slope, vsub_eq_sub]
    apply ContinuousOn.enorm
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.congr (f := fun x : ℝ => (x:ℝ)⁻¹ • (g (z + x * I) - g z))
    · have hinv : ContinuousOn (fun x : ℝ => (x : ℝ)⁻¹) {x : ℝ | 0 < |x| ∧ |x| < 1 / (n + 1)} :=
        continuousOn_id.inv₀ (fun x hx => abs_pos.mp hx.1)
      have hgz : Continuous (fun x : ℝ => g (z + x * I) - g z) := by fun_prop
      exact hinv.smul hgz.continuousOn
    · intro x hx
      exact heq x (abs_pos.mp hx.1)
  have heq2 : (⨆ q : menchoffQIdx n,
        ‖slope (fun t : ℝ => g (z + t * I)) 0 (q : ℝ) - menchoffFy g z‖ₑ) =
      ⨆ x ∈ {x : ℝ | 0 < |x| ∧ |x| < 1 / (n + 1)},
        ‖slope (fun t : ℝ => g (z + t * I)) 0 x - menchoffFy g z‖ₑ :=
    menchoff_iSup_dense_eq (c := fun q : menchoffQIdx n => (q.1 : ℝ)) (fun q => q.2)
      (fun x hx ε' hε' => by
        obtain ⟨q, hq1, hq2, hq3⟩ := menchoff_dense_punctured (1 / (n + 1)) x hx ε' hε'
        exact ⟨⟨q, hq1, hq2⟩, hq3⟩) hcont
  have hb2 : (⨆ x ∈ {x : ℝ | 0 < |x| ∧ |x| < 1 / (n + 1)},
      ‖slope (fun t : ℝ => g (z + t * I)) 0 x - menchoffFy g z‖ₑ) < ε := heq2 ▸ hb
  exact lt_of_le_of_lt (le_iSup₂ (f := fun x
    (_ : x ∈ {x : ℝ | 0 < |x| ∧ |x| < 1 / (n + 1)}) =>
      ‖slope (fun t : ℝ => g (z + t * I)) 0 x - menchoffFy g z‖ₑ) s ⟨hs0, hs1⟩) hb2

/-- `menchoffGn g · z` is antitone: the index set of allowed rational steps shrinks with `n`. -/
theorem menchoff_gn_antitone (g : ℂ → ℂ) (z : ℂ) : Antitone (fun n => menchoffGn g n z) := by
  intro n m hnm
  unfold menchoffGn
  apply iSup_le
  intro q
  have hle : (1 : ℝ) / (m + 1) ≤ 1 / (n + 1) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hmem : 0 < |(q.1 : ℝ)| ∧ |(q.1 : ℝ)| < 1 / (n + 1) := ⟨q.2.1, q.2.2.trans_le hle⟩
  exact le_iSup (fun q' : menchoffQIdx n =>
    ‖slope (fun t : ℝ => g (z + t)) 0 (q' : ℝ) - menchoffFx g z‖ₑ) ⟨q.1, hmem⟩

/-- `menchoffHn g · z` is antitone. -/
theorem menchoff_hn_antitone (g : ℂ → ℂ) (z : ℂ) : Antitone (fun n => menchoffHn g n z) := by
  intro n m hnm
  unfold menchoffHn
  apply iSup_le
  intro q
  have hle : (1 : ℝ) / (m + 1) ≤ 1 / (n + 1) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hmem : 0 < |(q.1 : ℝ)| ∧ |(q.1 : ℝ)| < 1 / (n + 1) := ⟨q.2.1, q.2.2.trans_le hle⟩
  exact le_iSup (fun q' : menchoffQIdx n =>
    ‖slope (fun t : ℝ => g (z + t * I)) 0 (q' : ℝ) - menchoffFy g z‖ₑ) ⟨q.1, hmem⟩

/-- A "poor man's Egorov" for a pointwise-ANTITONE sequence `G n` of `ℝ≥0∞`-valued measurable
functions tending a.e. to `0` on a finite-measure set `Q`: for any threshold `ε > 0` and any
tolerance `δ > 0`, some single index `N` already has `{z ∈ Q | ε ≤ G N z}` of measure `≤ δ`.
No uniform-space machinery is needed since the sequence is monotone: this is continuity of
measure from above applied to the (automatically antitone) super-level sets. -/
theorem menchoff_antitone_null_of_ae_tendsto {G : ℕ → ℂ → ℝ≥0∞}
    (hGmeas : ∀ n, Measurable (G n)) {Q : Set ℂ} (hQm : MeasurableSet Q) (hQfin : volume Q ≠ ∞)
    (hanti : ∀ z, Antitone (fun n => G n z))
    (hae : ∀ᵐ z ∂volume, z ∈ Q → Tendsto (fun n => G n z) atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N : ℕ, volume (Q ∩ {z | ε ≤ G N z}) ≤ δ := by
  set A : ℕ → Set ℂ := fun n => Q ∩ {z | ε ≤ G n z} with hA_def
  have hAanti : Antitone A := by
    intro n m hnm z hz
    exact ⟨hz.1, hz.2.trans (hanti z hnm)⟩
  have hAmeas : ∀ n, MeasurableSet (A n) := fun n =>
    hQm.inter (measurableSet_le measurable_const (hGmeas n))
  have hAfin : volume (A 0) ≠ ∞ := ne_top_of_le_ne_top hQfin (measure_mono Set.inter_subset_left)
  have hAinter_sub : (⋂ n, A n) ⊆ {z | z ∈ Q ∧ ¬ Tendsto (fun n => G n z) atTop (𝓝 0)} := by
    intro z hz
    simp only [Set.mem_iInter, hA_def, Set.mem_inter_iff, Set.mem_setOf_eq] at hz
    refine ⟨(hz 0).1, ?_⟩
    intro hconv
    obtain ⟨n, hn⟩ := ((tendsto_order.mp hconv).2 ε hε).exists
    exact absurd (hz n).2 (not_le.mpr hn)
  have hAinter : volume (⋂ n, A n) = 0 := by
    apply measure_mono_null hAinter_sub
    have heq : {z : ℂ | z ∈ Q ∧ ¬ Tendsto (fun n => G n z) atTop (𝓝 0)} =
        {z : ℂ | ¬ (z ∈ Q → Tendsto (fun n => G n z) atTop (𝓝 0))} :=
      Set.ext fun z => Classical.not_imp.symm
    rw [heq, ← ae_iff]
    exact hae
  have htend := tendsto_measure_iInter_atTop (μ := volume)
    (fun n => (hAmeas n).nullMeasurableSet) hAanti ⟨0, hAfin⟩
  rw [hAinter] at htend
  obtain ⟨N, hN⟩ := ((ENNReal.tendsto_nhds_zero.mp htend) δ hδ).exists
  exact ⟨N, hN⟩

/-- Genuine uniform convergence on a single set `E` (of controllable measure-deficit `δ`), built
by summing a geometric series of exceptional-set measures over all target accuracies at once.
Unlike `menchoff_antitone_null_of_ae_tendsto` (single accuracy, single index), this gives a set
`E` that works simultaneously for every `ε > 0`. -/
theorem menchoff_uniform_null_seq {G : ℕ → ℂ → ℝ≥0∞}
    (hGmeas : ∀ n, Measurable (G n)) {Q : Set ℂ} (hQm : MeasurableSet Q) (hQfin : volume Q ≠ ∞)
    (hanti : ∀ z, Antitone (fun n => G n z))
    (hae : ∀ᵐ z ∂volume, z ∈ Q → Tendsto (fun n => G n z) atTop (𝓝 0))
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ E ⊆ Q, MeasurableSet E ∧ volume (Q \ E) ≤ δ ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ E, G n z < ENNReal.ofReal ε := by
  have hδk : ∀ k : ℕ, 0 < δ * (2⁻¹ : ℝ≥0∞) ^ (k + 1) :=
    fun k => ENNReal.mul_pos hδ.ne' (pow_ne_zero _ (by norm_num))
  choose Nfun hNfun using fun k : ℕ =>
    menchoff_antitone_null_of_ae_tendsto hGmeas hQm hQfin hanti hae
      (ε := ENNReal.ofReal (1 / (k + 1 : ℝ))) (by positivity) (hδk k)
  set Bad : ℕ → Set ℂ := fun k => Q ∩ {z | ENNReal.ofReal (1 / (k + 1 : ℝ)) ≤ G (Nfun k) z}
    with hBad_def
  set E : Set ℂ := Q \ ⋃ k, Bad k with hE_def
  have hEQ : E ⊆ Q := Set.diff_subset
  have hBadmeas : ∀ k, MeasurableSet (Bad k) := fun k =>
    hQm.inter (measurableSet_le measurable_const (hGmeas (Nfun k)))
  have hEmeas : MeasurableSet E := hQm.diff (MeasurableSet.iUnion hBadmeas)
  have hEdiff : volume (Q \ E) ≤ δ := by
    have heq : Q \ E = Q ∩ ⋃ k, Bad k := by
      rw [hE_def]; ext z; simp only [Set.mem_diff, Set.mem_inter_iff, not_and, not_not]
      tauto
    rw [heq]
    calc volume (Q ∩ ⋃ k, Bad k) ≤ volume (⋃ k, Bad k) := measure_mono Set.inter_subset_right
      _ ≤ ∑' k, volume (Bad k) := measure_iUnion_le _
      _ ≤ ∑' k, δ * (2⁻¹ : ℝ≥0∞) ^ (k + 1) := ENNReal.tsum_le_tsum (fun k => hNfun k)
      _ = δ := by
          have hgeo : ∑' k:ℕ, (2⁻¹:ℝ≥0∞)^(k+1) = 1 := by
            simp_rw [pow_succ]
            rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric_two]
            rw [ENNReal.mul_inv_cancel] <;> norm_num
          rw [ENNReal.tsum_mul_left, hgeo, mul_one]
  refine ⟨E, hEQ, hEmeas, hEdiff, ?_⟩
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  refine ⟨Nfun k, fun n hn z hz => ?_⟩
  have hzNotBad : z ∉ Bad k := fun hzBad => hz.2 (Set.mem_iUnion.2 ⟨k, hzBad⟩)
  have hzlt : G (Nfun k) z < ENNReal.ofReal (1 / (k + 1 : ℝ)) := by
    by_contra hcon
    push Not at hcon
    exact hzNotBad ⟨hz.1, hcon⟩
  calc G n z ≤ G (Nfun k) z := hanti z hn
    _ < ENNReal.ofReal (1 / (k + 1 : ℝ)) := hzlt
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hk.le

theorem menchoff_fx_continuousOn_of_uniform {g : ℂ → ℂ} (hg : Continuous g) {E : Set ℂ}
    (hU : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ E, menchoffGn g n z < ENNReal.ofReal ε) :
    ContinuousOn (menchoffFx g) E := by
  set qseq : ℕ → ℝ := fun n => 1 / (n + 2) with hqseq_def
  have hqseq_mem : ∀ n : ℕ, (0:ℝ) < |qseq n| ∧ |qseq n| < 1 / (n + 1) := by
    intro n
    have h1 : (0:ℝ) < qseq n := by rw [hqseq_def]; positivity
    rw [abs_of_pos h1]
    refine ⟨h1, ?_⟩
    rw [hqseq_def]
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    linarith
  set F : ℕ → ℂ → ℂ := fun n z => slope (fun t : ℝ => g (z + t)) 0 (qseq n) with hF_def
  have hFcont : ∀ n, Continuous (F n) := by
    intro n
    have heq : F n = fun z => (qseq n : ℝ)⁻¹ • (g (z + qseq n) - g z) := by
      funext z
      simp [hF_def, slope, vsub_eq_sub]
    rw [heq]
    fun_prop
  have hTU : TendstoUniformlyOn F (menchoffFx g) atTop E := by
    rw [tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hU ε hε
    filter_upwards [eventually_ge_atTop N] with n hn
    intro z hz
    have hb : menchoffGn g n z < ENNReal.ofReal ε := hN n hn z hz
    have hbnd := menchoff_gn_real_bound hg hb (hqseq_mem n).1 (hqseq_mem n).2
    rw [← ofReal_norm] at hbnd
    rw [dist_eq_norm, norm_sub_rev]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hbnd
  exact hTU.continuousOn ((Eventually.of_forall fun n => (hFcont n).continuousOn).frequently)

theorem menchoff_fy_continuousOn_of_uniform {g : ℂ → ℂ} (hg : Continuous g) {E : Set ℂ}
    (hU : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ E, menchoffHn g n z < ENNReal.ofReal ε) :
    ContinuousOn (menchoffFy g) E := by
  set qseq : ℕ → ℝ := fun n => 1 / (n + 2) with hqseq_def
  have hqseq_mem : ∀ n : ℕ, (0:ℝ) < |qseq n| ∧ |qseq n| < 1 / (n + 1) := by
    intro n
    have h1 : (0:ℝ) < qseq n := by rw [hqseq_def]; positivity
    rw [abs_of_pos h1]
    refine ⟨h1, ?_⟩
    rw [hqseq_def]
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    linarith
  set F : ℕ → ℂ → ℂ := fun n z => slope (fun t : ℝ => g (z + t * I)) 0 (qseq n) with hF_def
  have hFcont : ∀ n, Continuous (F n) := by
    intro n
    have heq : F n = fun z => (qseq n : ℝ)⁻¹ • (g (z + qseq n * I) - g z) := by
      funext z
      simp [hF_def, slope, vsub_eq_sub]
    rw [heq]
    fun_prop
  have hTU : TendstoUniformlyOn F (menchoffFy g) atTop E := by
    rw [tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hU ε hε
    filter_upwards [eventually_ge_atTop N] with n hn
    intro z hz
    have hb : menchoffHn g n z < ENNReal.ofReal ε := hN n hn z hz
    have hbnd := menchoff_hn_real_bound hg hb (hqseq_mem n).1 (hqseq_mem n).2
    rw [← ofReal_norm] at hbnd
    rw [dist_eq_norm, norm_sub_rev]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hbnd
  exact hTU.continuousOn ((Eventually.of_forall fun n => (hFcont n).continuousOn).frequently)

/-- **M2 assembly.** For `g` continuous and a.e. horizontally/vertically differentiable on a
closed rectangle `Q`, and any target accuracy `m`, there is a subset `E ⊆ Q` missing only
`≤ 1/(m+1)` of `Q`'s measure, on which `menchoffFx g`/`menchoffFy g` are continuous, and a single
scale `N` beyond which every real step gives a difference-quotient defect `< 1/(m+1)` at every
point of `E`, in both the horizontal and vertical directions. -/
theorem menchoff_M2 {g : ℂ → ℂ} (hg : Continuous g) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hae : ∀ᵐ z ∂volume, z ∈ closedRect a b c d →
      DifferentiableAt ℝ (fun t : ℝ => g (z + t)) 0 ∧
      DifferentiableAt ℝ (fun t : ℝ => g (z + t * I)) 0)
    (m : ℕ) :
    ∃ E : Set ℂ, E ⊆ closedRect a b c d ∧ MeasurableSet E ∧
      volume (closedRect a b c d \ E) ≤ ENNReal.ofReal (1 / (m + 1)) ∧
      ContinuousOn (menchoffFx g) E ∧ ContinuousOn (menchoffFy g) E ∧
      ∃ N : ℕ, ∀ z ∈ E, ∀ s : ℝ, 0 < |s| → |s| < 1 / (N + 1) →
        ‖slope (fun t : ℝ => g (z + t)) 0 s - menchoffFx g z‖ₑ < ENNReal.ofReal (1 / (m + 1)) ∧
        ‖slope (fun t : ℝ => g (z + t * I)) 0 s - menchoffFy g z‖ₑ < ENNReal.ofReal (1 / (m + 1)) := by
  set Q := closedRect a b c d with hQ_def
  have hQcpt : IsCompact Q := acl_isCompact_closedRect a b c d
  have hQm : MeasurableSet Q := hQcpt.isClosed.measurableSet
  have hQfin : volume Q ≠ ∞ := hQcpt.measure_lt_top.ne
  have haeG : ∀ᵐ z ∂volume, z ∈ Q → Tendsto (fun n => menchoffGn g n z) atTop (𝓝 0) := by
    filter_upwards [hae] with z hz hzQ
    exact menchoff_gn_tendsto_zero (hz hzQ).1
  have haeH : ∀ᵐ z ∂volume, z ∈ Q → Tendsto (fun n => menchoffHn g n z) atTop (𝓝 0) := by
    filter_upwards [hae] with z hz hzQ
    exact menchoff_hn_tendsto_zero (hz hzQ).2
  obtain ⟨Eg, hEgQ, hEgmeas, hEgdiff, hEgU⟩ := menchoff_uniform_null_seq
    (menchoff_measurable_gn hg) hQm hQfin (fun z => menchoff_gn_antitone g z) haeG
    (δ := ENNReal.ofReal (1 / (2 * (m + 1)))) (by positivity)
  obtain ⟨Eh, hEhQ, hEhmeas, hEhdiff, hEhU⟩ := menchoff_uniform_null_seq
    (menchoff_measurable_hn hg) hQm hQfin (fun z => menchoff_hn_antitone g z) haeH
    (δ := ENNReal.ofReal (1 / (2 * (m + 1)))) (by positivity)
  set E := Eg ∩ Eh with hE_def
  have hEQ : E ⊆ Q := fun z hz => hEgQ hz.1
  have hEmeas : MeasurableSet E := hEgmeas.inter hEhmeas
  have hEdiff : volume (Q \ E) ≤ ENNReal.ofReal (1 / (m + 1)) := by
    have hsub : Q \ E ⊆ (Q \ Eg) ∪ (Q \ Eh) := by
      intro z hz
      simp only [hE_def, Set.mem_diff, Set.mem_inter_iff, Set.mem_union] at hz ⊢
      tauto
    calc volume (Q \ E) ≤ volume ((Q \ Eg) ∪ (Q \ Eh)) := measure_mono hsub
      _ ≤ volume (Q \ Eg) + volume (Q \ Eh) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (1 / (2 * (m + 1))) + ENNReal.ofReal (1 / (2 * (m + 1))) :=
          add_le_add hEgdiff hEhdiff
      _ = ENNReal.ofReal (1 / (m + 1)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          field_simp
          ring
  have hCfx : ContinuousOn (menchoffFx g) E :=
    (menchoff_fx_continuousOn_of_uniform hg hEgU).mono Set.inter_subset_left
  have hCfy : ContinuousOn (menchoffFy g) E :=
    (menchoff_fy_continuousOn_of_uniform hg hEhU).mono Set.inter_subset_right
  refine ⟨E, hEQ, hEmeas, hEdiff, hCfx, hCfy, ?_⟩
  obtain ⟨Ng, hNg⟩ := hEgU (1 / (m + 1)) (by positivity)
  obtain ⟨Nh, hNh⟩ := hEhU (1 / (m + 1)) (by positivity)
  refine ⟨max Ng Nh, fun z hz s hs0 hs1 => ?_⟩
  have hb1 : menchoffGn g (max Ng Nh) z < ENNReal.ofReal (1 / (m + 1)) :=
    hNg (max Ng Nh) (le_max_left _ _) z hz.1
  have hb2 : menchoffHn g (max Ng Nh) z < ENNReal.ofReal (1 / (m + 1)) :=
    hNh (max Ng Nh) (le_max_right _ _) z hz.2
  exact ⟨menchoff_gn_real_bound hg hb1 hs0 hs1, menchoff_hn_real_bound hg hb2 hs0 hs1⟩

/-! ## M3: density along horizontal and vertical lines. -/

def menchoffHSlice (E : Set ℂ) (y : ℝ) : Set ℝ := {x : ℝ | (x:ℂ) + y*I ∈ E}
def menchoffVSlice (E : Set ℂ) (x : ℝ) : Set ℝ := {y : ℝ | (x:ℂ) + y*I ∈ E}

theorem menchoff_measurableSet_hslice {E : Set ℂ} (hE : MeasurableSet E) (y : ℝ) :
    MeasurableSet (menchoffHSlice E y) := by
  have hm : Measurable (fun x:ℝ => (x:ℂ) + y*I) := by fun_prop
  exact hE.preimage hm

theorem menchoff_measurableSet_vslice {E : Set ℂ} (hE : MeasurableSet E) (x : ℝ) :
    MeasurableSet (menchoffVSlice E x) := by
  have hm : Measurable (fun y:ℝ => (x:ℂ) + y*I) := by fun_prop
  exact hE.preimage hm

/-- Sequential 1-D density (at scale `1/(n+1)`), matching `measurableSet_tendsto`'s countable-index
requirement so the set of density points of a fixed slice is measurable. -/
def menchoffIsDensityAt (S : Set ℝ) (x : ℝ) : Prop :=
  Tendsto (fun n : ℕ => volume (S ∩ closedBall x (1/(n+1))) / volume (closedBall x (1/(n+1))))
    atTop (𝓝 1)

theorem menchoff_ae_density_hslice {E : Set ℂ} (hE : MeasurableSet E) (y : ℝ) :
    ∀ᵐ x ∂volume, x ∈ menchoffHSlice E y → menchoffIsDensityAt (menchoffHSlice E y) x := by
  rw [← ae_restrict_iff' (menchoff_measurableSet_hslice hE y)]
  have h := IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div
    (volume : Measure ℝ) (menchoffHSlice E y) 1
  filter_upwards [h] with x hx
  exact hx (w := fun _ : ℕ => x) (δ := fun n => 1/(n+1))
    (by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact tendsto_one_div_add_atTop_nhds_zero_nat
      · exact Eventually.of_forall fun n => by rw [Set.mem_Ioi]; positivity)
    (by filter_upwards with n
        simp only [Metric.mem_closedBall, one_mul]
        rw [dist_self]
        positivity)

theorem menchoff_ae_density_vslice {E : Set ℂ} (hE : MeasurableSet E) (x : ℝ) :
    ∀ᵐ y ∂volume, y ∈ menchoffVSlice E x → menchoffIsDensityAt (menchoffVSlice E x) y := by
  rw [← ae_restrict_iff' (menchoff_measurableSet_vslice hE x)]
  have h := IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div
    (volume : Measure ℝ) (menchoffVSlice E x) 1
  filter_upwards [h] with y hy
  exact hy (w := fun _ : ℕ => y) (δ := fun n => 1/(n+1))
    (by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact tendsto_one_div_add_atTop_nhds_zero_nat
      · exact Eventually.of_forall fun n => by rw [Set.mem_Ioi]; positivity)
    (by filter_upwards with n
        simp only [Metric.mem_closedBall, one_mul]
        rw [dist_self]
        positivity)


def menchoffE2 (E : Set ℂ) : Set (ℝ × ℝ) := {p : ℝ × ℝ | (p.1:ℂ) + p.2*I ∈ E}

theorem menchoff_measurableSet_E2 {E : Set ℂ} (hE : MeasurableSet E) :
    MeasurableSet (menchoffE2 E) := by
  have hm : Measurable (fun p : ℝ×ℝ => (p.1:ℂ) + p.2*I) := by fun_prop
  exact hE.preimage hm

theorem menchoff_hslice_eq_E2 (E : Set ℂ) (y : ℝ) :
    menchoffHSlice E y = {x : ℝ | (x, y) ∈ menchoffE2 E} := rfl

theorem menchoff_vslice_eq_E2 (E : Set ℂ) (x : ℝ) :
    menchoffVSlice E x = {y : ℝ | (x, y) ∈ menchoffE2 E} := rfl

theorem menchoff_measurable_ball_inter_hslice {E : Set ℂ} (hE : MeasurableSet E) (r : ℝ) :
    Measurable (fun p : ℝ × ℝ => volume (closedBall p.1 r ∩ menchoffHSlice E p.2)) := by
  set T : Set ((ℝ×ℝ)×ℝ) := {q : (ℝ×ℝ)×ℝ | |q.1.1 - q.2| ≤ r ∧ (q.2, q.1.2) ∈ menchoffE2 E}
    with hT_def
  have hT1 : MeasurableSet {q : (ℝ×ℝ)×ℝ | |q.1.1 - q.2| ≤ r} := by
    have : Measurable (fun q : (ℝ×ℝ)×ℝ => |q.1.1 - q.2|) := by fun_prop
    exact measurableSet_le this measurable_const
  have hT2 : MeasurableSet {q : (ℝ×ℝ)×ℝ | (q.2, q.1.2) ∈ menchoffE2 E} := by
    have hm : Measurable (fun q : (ℝ×ℝ)×ℝ => (q.2, q.1.2)) := by fun_prop
    exact (menchoff_measurableSet_E2 hE).preimage hm
  have hTmeas : MeasurableSet T := hT1.inter hT2
  have hmeas := measurable_measure_prodMk_left (ν := volume) hTmeas
  have heq : (fun p : ℝ×ℝ => volume (closedBall p.1 r ∩ menchoffHSlice E p.2)) =
      (fun p : ℝ×ℝ => volume (Prod.mk p ⁻¹' T)) := by
    funext p
    congr 1
    ext x'
    simp only [Set.mem_preimage, hT_def, Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_closedBall,
      menchoffHSlice, Real.dist_eq, menchoffE2, abs_sub_comm x' p.1]
  rw [heq]
  exact hmeas

theorem menchoff_measurable_ball_inter_vslice {E : Set ℂ} (hE : MeasurableSet E) (r : ℝ) :
    Measurable (fun p : ℝ × ℝ => volume (closedBall p.2 r ∩ menchoffVSlice E p.1)) := by
  set T : Set ((ℝ×ℝ)×ℝ) := {q : (ℝ×ℝ)×ℝ | |q.1.2 - q.2| ≤ r ∧ (q.1.1, q.2) ∈ menchoffE2 E}
    with hT_def
  have hT1 : MeasurableSet {q : (ℝ×ℝ)×ℝ | |q.1.2 - q.2| ≤ r} := by
    have : Measurable (fun q : (ℝ×ℝ)×ℝ => |q.1.2 - q.2|) := by fun_prop
    exact measurableSet_le this measurable_const
  have hT2 : MeasurableSet {q : (ℝ×ℝ)×ℝ | (q.1.1, q.2) ∈ menchoffE2 E} := by
    have hm : Measurable (fun q : (ℝ×ℝ)×ℝ => (q.1.1, q.2)) := by fun_prop
    exact (menchoff_measurableSet_E2 hE).preimage hm
  have hTmeas : MeasurableSet T := hT1.inter hT2
  have hmeas := measurable_measure_prodMk_left (ν := volume) hTmeas
  have heq : (fun p : ℝ×ℝ => volume (closedBall p.2 r ∩ menchoffVSlice E p.1)) =
      (fun p : ℝ×ℝ => volume (Prod.mk p ⁻¹' T)) := by
    funext p
    congr 1
    ext y'
    simp only [Set.mem_preimage, hT_def, Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_closedBall,
      menchoffVSlice, Real.dist_eq, menchoffE2, abs_sub_comm y' p.2]
  rw [heq]
  exact hmeas

def menchoffΦh (E : Set ℂ) (r : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  volume (closedBall p.1 r ∩ menchoffHSlice E p.2) / volume (closedBall p.1 r)

def menchoffΦv (E : Set ℂ) (r : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  volume (closedBall p.2 r ∩ menchoffVSlice E p.1) / volume (closedBall p.2 r)

theorem menchoff_measurable_ball1 (r : ℝ) : Measurable (fun x : ℝ => volume (closedBall x r)) := by
  have heq : (fun x : ℝ => volume (closedBall x r)) = fun _ => volume (closedBall (0:ℝ) r) := by
    funext x
    rw [Real.volume_closedBall, Real.volume_closedBall]
  rw [heq]
  exact measurable_const

theorem menchoff_measurable_Φh {E : Set ℂ} (hE : MeasurableSet E) (r : ℝ) :
    Measurable (menchoffΦh E r) :=
  (menchoff_measurable_ball_inter_hslice hE r).div
    ((menchoff_measurable_ball1 r).comp measurable_fst)

theorem menchoff_measurable_Φv {E : Set ℂ} (hE : MeasurableSet E) (r : ℝ) :
    Measurable (menchoffΦv E r) :=
  (menchoff_measurable_ball_inter_vslice hE r).div
    ((menchoff_measurable_ball1 r).comp measurable_snd)

/-- The set of `(x,y)` where the horizontal slice through `(x,y)` is 1-D density-dense at `x`. -/
def menchoffGoodH (E : Set ℂ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | Tendsto (fun n : ℕ => menchoffΦh E (1/(n+1)) p) atTop (𝓝 1)}

def menchoffGoodV (E : Set ℂ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | Tendsto (fun n : ℕ => menchoffΦv E (1/(n+1)) p) atTop (𝓝 1)}

theorem menchoff_measurableSet_goodH {E : Set ℂ} (hE : MeasurableSet E) :
    MeasurableSet (menchoffGoodH E) :=
  measurableSet_tendsto (𝓝 1) (fun n => menchoff_measurable_Φh hE (1/(n+1)))

theorem menchoff_measurableSet_goodV {E : Set ℂ} (hE : MeasurableSet E) :
    MeasurableSet (menchoffGoodV E) :=
  measurableSet_tendsto (𝓝 1) (fun n => menchoff_measurable_Φv hE (1/(n+1)))

theorem menchoff_ae_ae_dens_h {E : Set ℂ} (hE : MeasurableSet E) (y : ℝ) :
    ∀ᵐ x ∂volume, x ∈ menchoffHSlice E y → (x, y) ∈ menchoffGoodH E := by
  filter_upwards [menchoff_ae_density_hslice hE y] with x hx hxy
  have hd : menchoffIsDensityAt (menchoffHSlice E y) x := hx hxy
  unfold menchoffIsDensityAt at hd
  show Tendsto (fun n : ℕ => menchoffΦh E (1/(n+1)) (x,y)) atTop (𝓝 1)
  have heq : (fun n : ℕ => menchoffΦh E (1/(n+1)) (x,y)) =
      (fun n : ℕ => volume (menchoffHSlice E y ∩ closedBall x (1/(n+1))) / volume (closedBall x (1/(n+1)))) := by
    funext n
    unfold menchoffΦh
    rw [Set.inter_comm]
  rw [heq]
  exact hd

theorem menchoff_ae_goodH {E : Set ℂ} (hE : MeasurableSet E) :
    ∀ᵐ z ∂volume, z ∈ E → (z.re, z.im) ∈ menchoffGoodH E := by
  set T : Set (ℝ×ℝ) := (menchoffE2 E)ᶜ ∪ menchoffGoodH E with hT_def
  have hTmeas : MeasurableSet T :=
    (menchoff_measurableSet_E2 hE).compl.union (menchoff_measurableSet_goodH hE)
  have hae : ∀ᵐ p ∂ (volume.prod volume), p ∈ T := by
    apply acl_ae_prod_of_ae_ae_swap hTmeas
    apply Filter.Eventually.of_forall
    intro y
    filter_upwards [menchoff_ae_ae_dens_h hE y] with x hx
    simp only [hT_def, Set.mem_union, Set.mem_compl_iff]
    by_cases hxy : x ∈ menchoffHSlice E y
    · exact Or.inr (hx hxy)
    · exact Or.inl hxy
  have hq := Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving
  filter_upwards [hq.ae hae] with z hz hzE
  simp only [Complex.measurableEquivRealProd_apply] at hz
  rcases hz with hz | hz
  · exact absurd hzE (by simpa [menchoffE2] using hz)
  · exact hz

theorem menchoff_ae_ae_dens_v {E : Set ℂ} (hE : MeasurableSet E) (x : ℝ) :
    ∀ᵐ y ∂volume, y ∈ menchoffVSlice E x → (x, y) ∈ menchoffGoodV E := by
  filter_upwards [menchoff_ae_density_vslice hE x] with y hy hxy
  have hd : menchoffIsDensityAt (menchoffVSlice E x) y := hy hxy
  unfold menchoffIsDensityAt at hd
  show Tendsto (fun n : ℕ => menchoffΦv E (1/(n+1)) (x,y)) atTop (𝓝 1)
  have heq : (fun n : ℕ => menchoffΦv E (1/(n+1)) (x,y)) =
      (fun n : ℕ => volume (menchoffVSlice E x ∩ closedBall y (1/(n+1))) / volume (closedBall y (1/(n+1)))) := by
    funext n
    unfold menchoffΦv
    rw [Set.inter_comm]
  rw [heq]
  exact hd

theorem menchoff_ae_goodV {E : Set ℂ} (hE : MeasurableSet E) :
    ∀ᵐ z ∂volume, z ∈ E → (z.re, z.im) ∈ menchoffGoodV E := by
  set T : Set (ℝ×ℝ) := (menchoffE2 E)ᶜ ∪ menchoffGoodV E with hT_def
  have hTmeas : MeasurableSet T :=
    (menchoff_measurableSet_E2 hE).compl.union (menchoff_measurableSet_goodV hE)
  have hae : ∀ᵐ p ∂ (volume.prod volume), p ∈ T := by
    rw [Measure.ae_prod_mem_iff_ae_ae_mem hTmeas]
    apply Filter.Eventually.of_forall
    intro x
    filter_upwards [menchoff_ae_ae_dens_v hE x] with y hy
    simp only [hT_def, Set.mem_union, Set.mem_compl_iff]
    by_cases hxy : y ∈ menchoffVSlice E x
    · exact Or.inr (hy hxy)
    · exact Or.inl hxy
  have hq := Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving
  filter_upwards [hq.ae hae] with z hz hzE
  simp only [Complex.measurableEquivRealProd_apply] at hz
  rcases hz with hz | hz
  · exact absurd hzE (by simpa [menchoffE2] using hz)
  · exact hz

/-- **M3.** For a.e. `z` in a measurable set `E ⊆ ℂ`, `z` is a 1-D Lebesgue density point of `E`
along both its horizontal and vertical line through `z`. -/
theorem menchoff_M3 {E : Set ℂ} (hE : MeasurableSet E) :
    ∀ᵐ z ∂volume, z ∈ E →
      Tendsto (fun n : ℕ => volume (menchoffHSlice E z.im ∩ closedBall z.re (1/(n+1))) /
        volume (closedBall z.re (1/(n+1)))) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => volume (menchoffVSlice E z.re ∩ closedBall z.im (1/(n+1))) /
        volume (closedBall z.im (1/(n+1)))) atTop (𝓝 1) := by
  filter_upwards [menchoff_ae_goodH hE, menchoff_ae_goodV hE] with z hzH hzV hzE
  have h1 : (z.re, z.im) ∈ menchoffGoodH E := hzH hzE
  have h2 : (z.re, z.im) ∈ menchoffGoodV E := hzV hzE
  unfold menchoffGoodH menchoffΦh at h1
  unfold menchoffGoodV menchoffΦv at h2
  simp only [Set.mem_setOf_eq, Set.inter_comm] at h1 h2
  exact ⟨h1, h2⟩

/-! ## M4 support: continuum density, existence lemmas, two-step path. -/

theorem menchoff_alg_helper (ε η r A : ℝ) (hε1 : ε < 1) (hηle : η ≤ ε/4) (hηnn : 0 ≤ η)
    (hApos : 0 < A) (hrleA : r * A ≤ 1) (hsmallB : 1 < (3*ε/4) * (A+1)) :
    (1-ε) * (2*r) ≤ (1-η) * (2/(A+1)) := by
  have hkey : (1-ε) * r * (A+1) ≤ 1 - η := by
    have hε1' : (0:ℝ) ≤ 1 - ε := by linarith
    have h1 : (1-ε) * r * A ≤ (1-ε) := by nlinarith [hrleA, hε1']
    have h2 : (1-ε) * (A+1) ≤ (1-η) * A := by
      have hp : (3*ε/4) * (A+1) ≤ (ε - η) * (A+1) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        linarith [hηle]
      have hp2 : 1 < (ε - η) * (A+1) := lt_of_lt_of_le hsmallB hp
      nlinarith [hp2, hηnn]
    have h3 : (1-ε)*r ≤ (1-ε)/A := by
      rw [le_div_iff₀ hApos]; nlinarith [hrleA, hε1']
    have h4 : (1-ε) * (A+1) / A ≤ 1 - η := by
      rw [div_le_iff₀ hApos]; nlinarith [h2]
    calc (1-ε) * r * (A+1) = (1-ε) * r * A + (1-ε)*r := by ring
      _ ≤ (1-ε) + (1-ε)*r := by linarith
      _ ≤ (1-ε) + (1-ε)/A := by linarith
      _ = (1-ε) * (A+1) / A := by field_simp
      _ ≤ 1 - η := h4
  rw [show (1-η)*(2/(A+1)) = 2*(1-η)/(A+1) by ring]
  rw [le_div_iff₀ (by linarith : (0:ℝ) < A+1)]
  nlinarith [hkey]

theorem menchoff_sandwich_real {g : ℝ → ℝ} (hmono : Monotone g) (hnonneg : ∀ r, 0 ≤ g r)
    (hbdd : ∀ r, 0 ≤ r → g r ≤ 2*r)
    (hseq : Tendsto (fun n : ℕ => g (1/(n+1)) / (2/(n+1))) atTop (𝓝 1)) :
    Tendsto (fun r : ℝ => g r / (2*r)) (𝓝[>] 0) (𝓝 1) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set η : ℝ := min (ε/4) (1/4) with hη_def
  have hηpos : 0 < η := by positivity
  have hηle : η ≤ ε/4 := min_le_left _ _
  have hηlt1 : η ≤ 1/4 := min_le_right _ _
  -- N1 from the sequential convergence
  rw [Metric.tendsto_atTop] at hseq
  obtain ⟨N1, hN1⟩ := hseq η hηpos
  -- N2 large enough that 1/(N2+2) ≤ 3ε/4
  obtain ⟨N2, hN2⟩ := exists_nat_gt (4/(3*ε))
  set N : ℕ := max N1 N2 with hN_def
  refine ⟨1/(N+1), by positivity, fun {r} hr hdist => ?_⟩
  simp only [Set.mem_Ioi] at hr
  rw [Real.dist_eq, sub_zero, abs_of_pos hr] at hdist
  -- find n ≥ N with 1/(n+2) < r ≤ 1/(n+1)
  set m : ℕ := ⌊1/r⌋₊ with hm_def
  have hNR : (0:ℝ) < (N:ℝ) + 1 := by positivity
  have hr1 : r ≤ 1 := by
    have h1 : (1:ℝ)/((N:ℝ)+1) ≤ 1 := by
      rw [div_le_one₀ hNR]; linarith [Nat.cast_nonneg (α := ℝ) N]
    linarith
  have hm1 : 1 ≤ m := by
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hr]
    linarith
  have hmN : N + 1 ≤ m := by
    apply Nat.le_floor
    push_cast
    rw [le_div_iff₀ hr]
    have : ((N:ℝ)+1) * r < ((N:ℝ)+1) * (1/((N:ℝ)+1)) := by
      apply mul_lt_mul_of_pos_left hdist hNR
    rw [mul_one_div, div_self hNR.ne'] at this
    linarith
  have hmfloor_le : (m:ℝ) ≤ 1/r := Nat.floor_le (by positivity)
  have hmfloor_lt : (1:ℝ)/r < (m:ℝ)+1 := Nat.lt_floor_add_one _
  set n : ℕ := m - 1 with hn_def
  have hnm : n + 1 = m := by omega
  have hn_ge_N : N ≤ n := by omega
  have hrle : r ≤ 1/((n:ℝ)+1) := by
    have hcast : ((n:ℝ)+1) = (m:ℝ) := by
      exact_mod_cast hnm
    rw [hcast, le_div_iff₀ (by positivity : (0:ℝ) < (m:ℝ))]
    calc r * (m:ℝ) ≤ r * (1/r) := by
          apply mul_le_mul_of_nonneg_left hmfloor_le hr.le
      _ = 1 := by field_simp
  have hrgt : 1/((n:ℝ)+2) < r := by
    have hcast : ((n:ℝ)+2) = (m:ℝ)+1 := by
      have h := hnm
      have : ((n:ℝ)+1)+1 = (m:ℝ)+1 := by exact_mod_cast congrArg (·+1) h
      linarith
    rw [hcast, div_lt_iff₀ (by positivity : (0:ℝ) < (m:ℝ)+1)]
    have h2 : (1:ℝ) < ((m:ℝ)+1) * r := by
      rw [← div_lt_iff₀ hr]
      linarith
    linarith
  -- combine with hN1 at index n+1 (giving info at scale 1/(n+2))
  have hN1_le : N1 ≤ N := hN_def ▸ le_max_left N1 N2
  have hN2_le : N2 ≤ N := hN_def ▸ le_max_right N1 N2
  have hn1n : N1 ≤ n + 1 := by omega
  have hd := hN1 (n+1) hn1n
  have hcast2 : ((n:ℝ)+1)+1 = (n:ℝ)+2 := by ring
  rw [Nat.cast_add, Nat.cast_one, hcast2] at hd
  rw [Real.dist_eq] at hd
  have hgn2bdd : g (1/((n:ℝ)+2)) ≤ 2*(1/((n:ℝ)+2)) := hbdd (1/((n:ℝ)+2)) (by positivity)
  have hgn2bdd' : g (1/((n:ℝ)+2)) ≤ 2/((n:ℝ)+2) := by rw [mul_one_div] at hgn2bdd; exact hgn2bdd
  have hgn2nn : 0 ≤ g (1/((n:ℝ)+2)) := hnonneg (1/((n:ℝ)+2))
  have hratio_le1 : g (1/((n:ℝ)+2)) / (2/((n:ℝ)+2)) ≤ 1 := by
    rw [div_le_one₀ (by positivity)]; exact hgn2bdd'
  have hgn2_lb : (1 - η) * (2/((n:ℝ)+2)) < g (1/((n:ℝ)+2)) := by
    have habs := abs_lt.mp hd
    have h2 : 1 - g (1/((n:ℝ)+2)) / (2/((n:ℝ)+2)) < η := by linarith [habs.1, habs.2]
    have h3 : (1 - η) < g (1/((n:ℝ)+2)) / (2/((n:ℝ)+2)) := by linarith
    calc (1-η) * (2/((n:ℝ)+2)) < (g (1/((n:ℝ)+2)) / (2/((n:ℝ)+2))) * (2/((n:ℝ)+2)) := by
          apply mul_lt_mul_of_pos_right h3 (by positivity)
      _ = g (1/((n:ℝ)+2)) := by field_simp
  have hmono' : g (1/((n:ℝ)+2)) ≤ g r := hmono hrgt.le
  have hgr_lb : (1 - η) * (2/((n:ℝ)+2)) < g r := lt_of_lt_of_le hgn2_lb hmono'
  have hgr_ub : g r ≤ 2 * r := hbdd r hr.le
  have hgr_nn : 0 ≤ g r := hnonneg r
  have hratio_le1' : g r / (2*r) ≤ 1 := by
    rw [div_le_one₀ (by positivity)]; exact hgr_ub
  -- numeric bound: N2 > 4/(3ε) and n ≥ N2 gives 1/(n+2) < 3ε/4
  have hn2n : N2 ≤ n := by omega
  have hNlarge : (4:ℝ)/(3*ε) < (n:ℝ) + 2 := by
    have : (N2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2n
    linarith
  have hsmall : 1/((n:ℝ)+2) < 3*ε/4 := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hNlarge
    nlinarith
  -- final chain: g r / (2r) > 1 - ε
  have hApos : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hrleA : r * ((n:ℝ)+1) ≤ 1 := by
    rw [← le_div_iff₀ hApos]; exact hrle
  have hsmallB : (1:ℝ) < (3*ε/4) * (((n:ℝ)+1)+1) := by
    rw [div_lt_iff₀ (by positivity)] at hsmall
    have hcast2 : ((n:ℝ)+1)+1 = (n:ℝ)+2 := by ring
    rw [hcast2]; linarith [hsmall]
  rcases lt_or_ge ε 1 with hε1 | hε1
  · -- ε < 1: the real algebra, via the standalone helper
    have hkey2 : (1-ε)*(2*r) ≤ (1-η)*(2/((n:ℝ)+2)) := by
      have := menchoff_alg_helper ε η r ((n:ℝ)+1) hε1 hηle hηpos.le hApos hrleA hsmallB
      have hcast2 : ((n:ℝ)+1)+1 = (n:ℝ)+2 := by ring
      rwa [hcast2] at this
    have hgoal : (1-ε) * (2*r) < g r := lt_of_le_of_lt hkey2 hgr_lb
    rw [Real.dist_eq, abs_of_nonpos (by linarith [hratio_le1'])]
    have : 1 - ε < g r / (2*r) := by
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2*r)]
      linarith [hgoal]
    linarith
  · -- ε ≥ 1: trivial since g r/(2r) > 0
    have hgrpos : 0 < g r := by nlinarith [hgr_lb, hηlt1]
    have hpos : (0:ℝ) < g r / (2*r) := by positivity
    rw [Real.dist_eq, abs_of_nonpos (by linarith [hratio_le1'])]
    linarith

open MeasureTheory in
/-- Converts an ENNReal-valued sequential bidirectional-density fact (as produced by the M3
Fubini/1-D-density route) into a genuine real-valued CONTINUUM density statement, via
`menchoff_sandwich_real`. -/
theorem menchoff_density_continuum {S : Set ℝ} {x0 : ℝ}
    (hseq : Tendsto (fun n : ℕ => volume (S ∩ closedBall x0 (1/(n+1))) /
      volume (closedBall x0 (1/(n+1)))) atTop (𝓝 1)) :
    Tendsto (fun r : ℝ => (volume (S ∩ closedBall x0 r)).toReal / (2*r)) (𝓝[>] 0) (𝓝 1) := by
  apply menchoff_sandwich_real
  · intro r1 r2 hr12
    apply ENNReal.toReal_mono
    · exact (measure_mono (Set.inter_subset_right)).trans_lt
        (by rw [Real.volume_closedBall]; exact ENNReal.ofReal_lt_top) |>.ne
    · exact measure_mono (Set.inter_subset_inter_right S (Metric.closedBall_subset_closedBall hr12))
  · intro r; exact ENNReal.toReal_nonneg
  · intro r hr
    have hle : volume (S ∩ closedBall x0 r) ≤ volume (closedBall x0 r) :=
      measure_mono Set.inter_subset_right
    have := ENNReal.toReal_mono (b := volume (closedBall x0 r))
      (by rw [Real.volume_closedBall]; exact ENNReal.ofReal_ne_top) hle
    rwa [Real.volume_closedBall, ENNReal.toReal_ofReal (by linarith)] at this
  · have hcomp := (ENNReal.tendsto_toReal (a := (1:ℝ≥0∞)) (by norm_num)).comp hseq
    simp only [ENNReal.toReal_one, Function.comp_def] at hcomp
    have heq : ∀ n : ℕ, (volume (S ∩ closedBall x0 (1/((n:ℝ)+1))) /
        volume (closedBall x0 (1/((n:ℝ)+1)))).toReal =
        (volume (S ∩ closedBall x0 (1/((n:ℝ)+1)))).toReal / (2/((n:ℝ)+1)) := by
      intro n
      rw [ENNReal.toReal_div, Real.volume_closedBall, ENNReal.toReal_ofReal (by positivity),
        mul_one_div]
    simpa only [heq] using hcomp

open MeasureTheory in
/-- From continuum bidirectional density at `x0`, every sufficiently small `s > 0` has a point
of `S` in the "almost-`s`" window `(s/(1+ε), s]` to the right of `x0`. -/
theorem menchoff_exists_right {S : Set ℝ} {x0 : ℝ}
    (hdens : Tendsto (fun r : ℝ => (volume (S ∩ closedBall x0 r)).toReal / (2*r)) (𝓝[>] 0) (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ →
      ∃ ξ ∈ Set.Ioc (s/(1+ε)) s, x0 + ξ ∈ S := by
  intro ε hε
  rw [Metric.tendsto_nhdsWithin_nhds] at hdens
  obtain ⟨δ, hδ, hprop⟩ := hdens (ε/(4*(1+ε))) (by positivity)
  refine ⟨δ, hδ, fun s hs0 hsδ => ?_⟩
  by_contra hcon
  push Not at hcon
  set bad : Set ℝ := Set.Ioc (x0 + s/(1+ε)) (x0 + s) with hbad_def
  have hbad_sub_ball : bad ⊆ closedBall x0 s := by
    intro y hy
    simp only [hbad_def, Set.mem_Ioc] at hy
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    have hpos : (0:ℝ) ≤ s/(1+ε) := by positivity
    exact ⟨by linarith [hy.1, hpos], by linarith [hy.2]⟩
  have hSbad : S ∩ bad = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hyS, hyBad⟩
    simp only [hbad_def, Set.mem_Ioc] at hyBad
    refine hcon (y - x0) (Set.mem_Ioc.mpr ⟨by linarith [hyBad.1], by linarith [hyBad.2]⟩) ?_
    simpa using hyS
  have hsub : S ∩ closedBall x0 s ⊆ closedBall x0 s \ bad := by
    intro y hy
    refine ⟨hy.2, ?_⟩
    intro hyBad
    have : y ∈ S ∩ bad := ⟨hy.1, hyBad⟩
    rw [hSbad] at this
    exact this
  have hballmeas : volume (closedBall x0 s) = ENNReal.ofReal (2*s) := Real.volume_closedBall x0 s
  have hbadnn : (0:ℝ) ≤ s - s/(1+ε) := by
    have : s/(1+ε) ≤ s := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [hε]
    linarith
  have hbadmeas : volume bad = ENNReal.ofReal (s - s/(1+ε)) := by
    rw [hbad_def, Real.volume_Ioc]; congr 1; ring
  have hdiffmeas : volume (closedBall x0 s \ bad) =
      volume (closedBall x0 s) - volume bad := by
    apply measure_diff hbad_sub_ball measurableSet_Ioc.nullMeasurableSet
    rw [hbadmeas]; exact ENNReal.ofReal_ne_top
  have hle : volume (S ∩ closedBall x0 s) ≤ volume (closedBall x0 s) - volume bad :=
    hdiffmeas ▸ measure_mono hsub
  have hle' : (volume (S ∩ closedBall x0 s)).toReal ≤ 2*s - (s - s/(1+ε)) := by
    have hval : (volume (closedBall x0 s) - volume bad).toReal = 2*s - (s - s/(1+ε)) := by
      have hspos : (0:ℝ) ≤ s/(1+ε) := by positivity
      rw [hballmeas, hbadmeas, ← ENNReal.ofReal_sub _ hbadnn,
        ENNReal.toReal_ofReal (by linarith [hbadnn, hs0, hspos])]
    have hfin : volume (closedBall x0 s) - volume bad ≠ ⊤ :=
      ne_top_of_le_ne_top (hballmeas ▸ ENNReal.ofReal_ne_top) tsub_le_self
    calc (volume (S ∩ closedBall x0 s)).toReal ≤ (volume (closedBall x0 s) - volume bad).toReal :=
          ENNReal.toReal_mono hfin hle
      _ = 2*s - (s - s/(1+ε)) := hval
  have hratio_le : (volume (S ∩ closedBall x0 s)).toReal / (2*s) ≤ 1 - ε/(2*(1+ε)) := by
    rw [div_le_iff₀ (by positivity)]
    have heq : (1 - ε/(2*(1+ε))) * (2*s) = 2*s - (s - s/(1+ε)) := by field_simp; ring
    rw [heq]; exact hle'
  have hdist := hprop (Set.mem_Ioi.mpr hs0) (by rw [Real.dist_eq, sub_zero, abs_of_pos hs0]; exact hsδ)
  rw [Real.dist_eq, abs_lt] at hdist
  have hcompare : ε/(4*(1+ε)) < ε/(2*(1+ε)) := by
    apply div_lt_div_of_pos_left hε (by positivity)
    linarith
  linarith [hdist.1, hratio_le, hcompare]

open MeasureTheory in
/-- Mirror of `menchoff_exists_right`: every sufficiently small `s > 0` has a point of `S` in the
"almost-`s`" window `[-s, -s/(1+ε))` to the left of `x0`. -/
theorem menchoff_exists_left {S : Set ℝ} {x0 : ℝ}
    (hdens : Tendsto (fun r : ℝ => (volume (S ∩ closedBall x0 r)).toReal / (2*r)) (𝓝[>] 0) (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ →
      ∃ ξ ∈ Set.Ico (-s) (-(s/(1+ε))), x0 + ξ ∈ S := by
  intro ε hε
  rw [Metric.tendsto_nhdsWithin_nhds] at hdens
  obtain ⟨δ, hδ, hprop⟩ := hdens (ε/(4*(1+ε))) (by positivity)
  refine ⟨δ, hδ, fun s hs0 hsδ => ?_⟩
  by_contra hcon
  push Not at hcon
  set bad : Set ℝ := Set.Ico (x0 - s) (x0 - s/(1+ε)) with hbad_def
  have hbad_sub_ball : bad ⊆ closedBall x0 s := by
    intro y hy
    simp only [hbad_def, Set.mem_Ico] at hy
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    have hpos : (0:ℝ) ≤ s/(1+ε) := by positivity
    exact ⟨by linarith [hy.1], by linarith [hy.2, hpos]⟩
  have hSbad : S ∩ bad = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hyS, hyBad⟩
    simp only [hbad_def, Set.mem_Ico] at hyBad
    refine hcon (y - x0) (Set.mem_Ico.mpr ⟨by linarith [hyBad.1], by linarith [hyBad.2]⟩) ?_
    simpa using hyS
  have hsub : S ∩ closedBall x0 s ⊆ closedBall x0 s \ bad := by
    intro y hy
    refine ⟨hy.2, ?_⟩
    intro hyBad
    have : y ∈ S ∩ bad := ⟨hy.1, hyBad⟩
    rw [hSbad] at this
    exact this
  have hballmeas : volume (closedBall x0 s) = ENNReal.ofReal (2*s) := Real.volume_closedBall x0 s
  have hbadnn : (0:ℝ) ≤ (x0 - s/(1+ε)) - (x0 - s) := by
    have : s/(1+ε) ≤ s := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [hε]
    linarith
  have hbadmeas : volume bad = ENNReal.ofReal ((x0 - s/(1+ε)) - (x0 - s)) := by
    rw [hbad_def]; exact Real.volume_Ico
  have hdiffmeas : volume (closedBall x0 s \ bad) =
      volume (closedBall x0 s) - volume bad := by
    apply measure_diff hbad_sub_ball measurableSet_Ico.nullMeasurableSet
    rw [hbadmeas]; exact ENNReal.ofReal_ne_top
  have hle : volume (S ∩ closedBall x0 s) ≤ volume (closedBall x0 s) - volume bad :=
    hdiffmeas ▸ measure_mono hsub
  have hle' : (volume (S ∩ closedBall x0 s)).toReal ≤ 2*s - (s - s/(1+ε)) := by
    have hval : (volume (closedBall x0 s) - volume bad).toReal = 2*s - (s - s/(1+ε)) := by
      have hspos : (0:ℝ) ≤ s/(1+ε) := by positivity
      rw [hballmeas, hbadmeas, ← ENNReal.ofReal_sub _ hbadnn,
        ENNReal.toReal_ofReal (by nlinarith [hbadnn, hs0, hspos])]
      ring
    have hfin : volume (closedBall x0 s) - volume bad ≠ ⊤ :=
      ne_top_of_le_ne_top (hballmeas ▸ ENNReal.ofReal_ne_top) tsub_le_self
    calc (volume (S ∩ closedBall x0 s)).toReal ≤ (volume (closedBall x0 s) - volume bad).toReal :=
          ENNReal.toReal_mono hfin hle
      _ = 2*s - (s - s/(1+ε)) := hval
  have hratio_le : (volume (S ∩ closedBall x0 s)).toReal / (2*s) ≤ 1 - ε/(2*(1+ε)) := by
    rw [div_le_iff₀ (by positivity)]
    have heq : (1 - ε/(2*(1+ε))) * (2*s) = 2*s - (s - s/(1+ε)) := by field_simp; ring
    rw [heq]; exact hle'
  have hdist := hprop (Set.mem_Ioi.mpr hs0) (by rw [Real.dist_eq, sub_zero, abs_of_pos hs0]; exact hsδ)
  rw [Real.dist_eq, abs_lt] at hdist
  have hcompare : ε/(4*(1+ε)) < ε/(2*(1+ε)) := by
    apply div_lt_div_of_pos_left hε (by positivity)
    linarith
  linarith [hdist.1, hratio_le, hcompare]

/-- Converts a `slope`-based difference-quotient bound into a plain difference bound
(horizontal direction). -/
theorem menchoff_slope_to_diff {g : ℂ → ℂ} {z0 : ℂ} {ξ : ℝ} (hξ : ξ ≠ 0) {A : ℂ} {μ : ℝ}
    (h : ‖slope (fun t : ℝ => g (z0 + t)) 0 ξ - A‖ < μ) :
    ‖g (z0 + ξ) - g z0 - A * ξ‖ < |ξ| * μ := by
  have heq : g (z0 + ξ) - g z0 - A * ξ = (ξ:ℂ) * (slope (fun t : ℝ => g (z0 + t)) 0 ξ - A) := by
    have hξC : (ξ:ℂ) ≠ 0 := by exact_mod_cast hξ
    simp only [slope, vsub_eq_sub, Complex.real_smul, add_zero, Complex.ofReal_zero, sub_zero,
      Complex.ofReal_inv]
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hξC, one_mul]
    ring
  rw [heq, norm_mul, norm_real, Real.norm_eq_abs]
  exact mul_lt_mul_of_pos_left h (abs_pos.mpr hξ)

/-- Vertical analogue of `menchoff_slope_to_diff`. -/
theorem menchoff_slope_to_diff_vert {g : ℂ → ℂ} {z0 : ℂ} {η : ℝ} (hη : η ≠ 0) {A : ℂ} {μ : ℝ}
    (h : ‖slope (fun t : ℝ => g (z0 + t * I)) 0 η - A‖ < μ) :
    ‖g (z0 + η * I) - g z0 - A * η‖ < |η| * μ := by
  have heq : g (z0 + η * I) - g z0 - A * η =
      (η:ℂ) * (slope (fun t : ℝ => g (z0 + t * I)) 0 η - A) := by
    have hηC : (η:ℂ) ≠ 0 := by exact_mod_cast hη
    simp only [slope, vsub_eq_sub, Complex.real_smul, Complex.ofReal_zero, zero_mul, add_zero,
      sub_zero, Complex.ofReal_inv]
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hηC, one_mul]
    ring
  rw [heq, norm_mul, norm_real, Real.norm_eq_abs]
  exact mul_lt_mul_of_pos_left h (abs_pos.mpr hη)

/-- Two-step path estimate (book's (9.3)): from `z0` horizontally to `z0+ξ` (control via
`z0`'s own horizontal defect), then vertically to `z0+ξ+ηI` (control via `z0+ξ`'s vertical
defect), with an `fy`-continuity correction at the join. -/
theorem menchoff_two_step {g : ℂ → ℂ} {z0 : ℂ} {ξ η : ℝ} (hξ : ξ ≠ 0) (hη : η ≠ 0) {μ : ℝ}
    (hbx : ‖slope (fun t : ℝ => g (z0 + t)) 0 ξ - menchoffFx g z0‖ < μ)
    (hby : ‖slope (fun t : ℝ => g ((z0 + ξ) + t * I)) 0 η - menchoffFy g (z0 + ξ)‖ < μ)
    (hfy : ‖menchoffFy g (z0 + ξ) - menchoffFy g z0‖ < μ) :
    ‖g (z0 + ξ + η * I) - g z0 - menchoffFx g z0 * ξ - menchoffFy g z0 * η‖ <
      μ * (|ξ| + 2 * |η|) := by
  have h1 : ‖g (z0 + ξ) - g z0 - menchoffFx g z0 * ξ‖ < |ξ| * μ :=
    menchoff_slope_to_diff hξ hbx
  have h2 : ‖g ((z0 + ξ) + η * I) - g (z0 + ξ) - menchoffFy g (z0 + ξ) * η‖ < |η| * μ :=
    menchoff_slope_to_diff_vert hη hby
  have h3 : ‖menchoffFy g (z0 + ξ) * η - menchoffFy g z0 * η‖ < |η| * μ := by
    rw [← sub_mul, norm_mul, norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_lt_mul_of_pos_left hfy (abs_pos.mpr hη)
  have hdecomp : g (z0 + ξ + η * I) - g z0 - menchoffFx g z0 * ξ - menchoffFy g z0 * η =
      (g (z0 + ξ) - g z0 - menchoffFx g z0 * ξ) +
      (g ((z0 + ξ) + η * I) - g (z0 + ξ) - menchoffFy g (z0 + ξ) * η) +
      (menchoffFy g (z0 + ξ) * η - menchoffFy g z0 * η) := by
    have hz : z0 + ξ + η * I = (z0 + ξ) + η * I := by ring
    rw [hz]; ring
  rw [hdecomp]
  have htri : ‖(g (z0 + ξ) - g z0 - menchoffFx g z0 * ξ) +
        (g ((z0 + ξ) + η * I) - g (z0 + ξ) - menchoffFy g (z0 + ξ) * η) +
        (menchoffFy g (z0 + ξ) * η - menchoffFy g z0 * η)‖
      ≤ ‖g (z0 + ξ) - g z0 - menchoffFx g z0 * ξ‖ +
        ‖g ((z0 + ξ) + η * I) - g (z0 + ξ) - menchoffFy g (z0 + ξ) * η‖ +
        ‖menchoffFy g (z0 + ξ) * η - menchoffFy g z0 * η‖ := by
    have step1 := norm_add_le
      (g (z0 + ξ) - g z0 - menchoffFx g z0 * ξ +
        (g ((z0 + ξ) + η * I) - g (z0 + ξ) - menchoffFy g (z0 + ξ) * η))
      (menchoffFy g (z0 + ξ) * η - menchoffFy g z0 * η)
    have step2 := norm_add_le
      (g (z0 + ξ) - g z0 - menchoffFx g z0 * ξ)
      (g ((z0 + ξ) + η * I) - g (z0 + ξ) - menchoffFy g (z0 + ξ) * η)
    linarith [step1, step2]
  calc ‖(g (z0 + ξ) - g z0 - menchoffFx g z0 * ξ) +
        (g ((z0 + ξ) + η * I) - g (z0 + ξ) - menchoffFy g (z0 + ξ) * η) +
        (menchoffFy g (z0 + ξ) * η - menchoffFy g z0 * η)‖
      ≤ ‖g (z0 + ξ) - g z0 - menchoffFx g z0 * ξ‖ +
        ‖g ((z0 + ξ) + η * I) - g (z0 + ξ) - menchoffFy g (z0 + ξ) * η‖ +
        ‖menchoffFy g (z0 + ξ) * η - menchoffFy g z0 * η‖ := htri
    _ < |ξ| * μ + |η| * μ + |η| * μ := by
        apply add_lt_add (add_lt_add h1 h2) h3
    _ = μ * (|ξ| + 2 * |η|) := by ring

/-- Mirror of `menchoff_two_step`: from `z0` VERTICALLY to `z0+ηI` (control via `z0`'s own
vertical defect), then HORIZONTALLY to `z0+ξ+ηI` (control via `z0+ηI`'s horizontal defect), with
an `fx`-continuity correction at the join. -/
theorem menchoff_two_step_vh {g : ℂ → ℂ} {z0 : ℂ} {ξ η : ℝ} (hξ : ξ ≠ 0) (hη : η ≠ 0) {μ : ℝ}
    (hby : ‖slope (fun t : ℝ => g (z0 + t * I)) 0 η - menchoffFy g z0‖ < μ)
    (hbx : ‖slope (fun t : ℝ => g ((z0 + η * I) + t)) 0 ξ - menchoffFx g (z0 + η * I)‖ < μ)
    (hfx : ‖menchoffFx g (z0 + η * I) - menchoffFx g z0‖ < μ) :
    ‖g (z0 + ξ + η * I) - g z0 - menchoffFx g z0 * ξ - menchoffFy g z0 * η‖ <
      μ * (2 * |ξ| + |η|) := by
  have h1 : ‖g (z0 + η * I) - g z0 - menchoffFy g z0 * η‖ < |η| * μ :=
    menchoff_slope_to_diff_vert hη hby
  have h2 : ‖g ((z0 + η * I) + ξ) - g (z0 + η * I) - menchoffFx g (z0 + η * I) * ξ‖ < |ξ| * μ :=
    menchoff_slope_to_diff hξ hbx
  have h3 : ‖menchoffFx g (z0 + η * I) * ξ - menchoffFx g z0 * ξ‖ < |ξ| * μ := by
    rw [← sub_mul, norm_mul, norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_lt_mul_of_pos_left hfx (abs_pos.mpr hξ)
  have hdecomp : g (z0 + ξ + η * I) - g z0 - menchoffFx g z0 * ξ - menchoffFy g z0 * η =
      (g (z0 + η * I) - g z0 - menchoffFy g z0 * η) +
      (g ((z0 + η * I) + ξ) - g (z0 + η * I) - menchoffFx g (z0 + η * I) * ξ) +
      (menchoffFx g (z0 + η * I) * ξ - menchoffFx g z0 * ξ) := by
    have hz : z0 + ξ + η * I = (z0 + η * I) + ξ := by ring
    rw [hz]; ring
  rw [hdecomp]
  have htri : ‖(g (z0 + η * I) - g z0 - menchoffFy g z0 * η) +
        (g ((z0 + η * I) + ξ) - g (z0 + η * I) - menchoffFx g (z0 + η * I) * ξ) +
        (menchoffFx g (z0 + η * I) * ξ - menchoffFx g z0 * ξ)‖
      ≤ ‖g (z0 + η * I) - g z0 - menchoffFy g z0 * η‖ +
        ‖g ((z0 + η * I) + ξ) - g (z0 + η * I) - menchoffFx g (z0 + η * I) * ξ‖ +
        ‖menchoffFx g (z0 + η * I) * ξ - menchoffFx g z0 * ξ‖ := by
    have step1 := norm_add_le
      (g (z0 + η * I) - g z0 - menchoffFy g z0 * η +
        (g ((z0 + η * I) + ξ) - g (z0 + η * I) - menchoffFx g (z0 + η * I) * ξ))
      (menchoffFx g (z0 + η * I) * ξ - menchoffFx g z0 * ξ)
    have step2 := norm_add_le
      (g (z0 + η * I) - g z0 - menchoffFy g z0 * η)
      (g ((z0 + η * I) + ξ) - g (z0 + η * I) - menchoffFx g (z0 + η * I) * ξ)
    linarith [step1, step2]
  calc ‖(g (z0 + η * I) - g z0 - menchoffFy g z0 * η) +
        (g ((z0 + η * I) + ξ) - g (z0 + η * I) - menchoffFx g (z0 + η * I) * ξ) +
        (menchoffFx g (z0 + η * I) * ξ - menchoffFx g z0 * ξ)‖
      ≤ ‖g (z0 + η * I) - g z0 - menchoffFy g z0 * η‖ +
        ‖g ((z0 + η * I) + ξ) - g (z0 + η * I) - menchoffFx g (z0 + η * I) * ξ‖ +
        ‖menchoffFx g (z0 + η * I) * ξ - menchoffFx g z0 * ξ‖ := htri
    _ < |η| * μ + |ξ| * μ + |ξ| * μ := by
        apply add_lt_add (add_lt_add h1 h2) h3
    _ = μ * (2 * |ξ| + |η|) := by ring

/-- If `ξ` approximates `s` from below within relative error `μ` (i.e. `ξ ∈ (s/(1+μ), s]`), the
absolute gap is `< s*μ`. Kept as a standalone lemma (small signature) to avoid `nlinarith`
timeouts against the large ambient context of the quadrant proof. -/
theorem menchoff_bracket_close_lo {s ξ μ : ℝ} (hs0 : 0 < s) (hμpos : 0 < μ)
    (hξmem : ξ ∈ Set.Ioc (s/(1+μ)) s) : |ξ - s| < s*μ := by
  have h1μpos : (0:ℝ) < 1+μ := by positivity
  rw [abs_of_nonpos (by linarith [hξmem.2])]
  have hstep : s*μ/(1+μ) < s*μ := by
    rw [div_lt_iff₀ h1μpos]
    nlinarith [hs0, hμpos, mul_pos hs0 (mul_pos hμpos hμpos)]
  have heq : s - s/(1+μ) = s*μ/(1+μ) := by field_simp; ring
  have hkey : s - s/(1+μ) < s*μ := heq ▸ hstep
  linarith [hξmem.1, hkey]

/-- Mirror of `menchoff_bracket_close_lo` for approximation from above. -/
theorem menchoff_bracket_close_hi {s ξ μ : ℝ} (hs0 : 0 < s) (hμpos : 0 < μ)
    (hξ1 : s < ξ) (hξ2 : ξ ≤ (1+μ)*s) : |ξ - s| ≤ s*μ := by
  rw [abs_of_pos (by linarith)]
  nlinarith [hξ2]

/-- If `x` and `t` both lie in `[lo,hi]`, and both endpoints are within `M` of `t`, then so is
`x`. Used to bound the "other" coordinate on a rectangle edge (which ranges over `[lo,hi]`, not
just the two endpoints already controlled). -/
theorem menchoff_sandwich_close {x t lo hi M : ℝ} (hx1 : lo ≤ x) (hx2 : x ≤ hi)
    (ht1 : lo ≤ t) (ht2 : t ≤ hi) (hlo : t - lo ≤ M) (hhi : hi - t ≤ M) : |x - t| ≤ M := by
  rcases le_or_gt x t with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- Closing step for a "horizontal-then-vertical" rectangle edge (left/right), packaged as a
single self-contained theorem (no ambient context beyond its own arguments) so that using it from
inside `menchoff_M4_quadrant_pp`'s large proof doesn't retrigger `nlinarith`/`simp` timeouts. -/
theorem menchoff_edge_finish_h {g : ℂ → ℂ} {z0 zeta : ℂ} {xi eta s t μ : ℝ}
    (hs0 : 0 < s) (ht0 : 0 < t) (hμpos : 0 < μ)
    (hxipos : 0 < xi) (hetapos : 0 < eta)
    (hxi_le2s : xi ≤ 2*s) (heta_le2t : eta ≤ 2*t)
    (hxiclose : |xi - s| ≤ s*μ) (hetaclose : |eta - t| ≤ t*μ)
    (hzetaeq : zeta = z0 + xi + eta * I)
    (hstep : ‖g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta‖ < μ*(xi+2*eta))
    (hzetabound : ‖g (z0+(s:ℂ)+(t:ℂ)*I) - (g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ))‖
      ≤ ‖g zeta - (g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ))‖) :
    ‖g (z0+(s:ℂ)+(t:ℂ)*I) - g z0 - menchoffFx g z0 * (s:ℂ) - menchoffFy g z0 * (t:ℂ)‖ ≤
      (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * μ * (|s| + |t|) := by
  set w : ℂ := g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ) with hw_def
  have hgzeta : ‖g zeta - w‖ ≤
      ‖g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta‖ +
      ‖menchoffFx g z0‖ * |xi - s| + ‖menchoffFy g z0‖ * |eta - t| := by
    have hdecomp : g zeta - w =
        (g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta) +
        menchoffFx g z0 * ((xi:ℂ) - s) + menchoffFy g z0 * ((eta:ℂ) - t) := by
      simp only [hw_def]; push_cast; ring
    rw [hdecomp]
    calc ‖(g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta) +
          menchoffFx g z0 * ((xi:ℂ) - s) + menchoffFy g z0 * ((eta:ℂ) - t)‖
        ≤ ‖g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta‖ +
          ‖menchoffFx g z0 * ((xi:ℂ) - s)‖ + ‖menchoffFy g z0 * ((eta:ℂ) - t)‖ := by
          have s1 := norm_add_le (g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta +
            menchoffFx g z0 * ((xi:ℂ) - s)) (menchoffFy g z0 * ((eta:ℂ) - t))
          have s2 := norm_add_le (g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta)
            (menchoffFx g z0 * ((xi:ℂ) - s))
          linarith [s1, s2]
      _ = _ := by
          have e1 : ‖((xi:ℂ) - s)‖ = |xi - s| := by
            rw [show ((xi:ℂ)-s) = ((xi-s:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs]
          have e2 : ‖((eta:ℂ) - t)‖ = |eta - t| := by
            rw [show ((eta:ℂ)-t) = ((eta-t:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs]
          rw [norm_mul, norm_mul, e1, e2]
  have hfinal1 : ‖g zeta - w‖ < μ*(xi+2*eta) + ‖menchoffFx g z0‖*(s*μ) + ‖menchoffFy g z0‖*(t*μ) := by
    have hb1 : ‖menchoffFx g z0‖ * |xi - s| ≤ ‖menchoffFx g z0‖ * (s*μ) :=
      mul_le_mul_of_nonneg_left hxiclose (norm_nonneg _)
    have hb2 : ‖menchoffFy g z0‖ * |eta - t| ≤ ‖menchoffFy g z0‖ * (t*μ) :=
      mul_le_mul_of_nonneg_left hetaclose (norm_nonneg _)
    linarith [hgzeta, hstep, hb1, hb2]
  have hfinal2 : μ*(xi+2*eta) + ‖menchoffFx g z0‖*(s*μ) + ‖menchoffFy g z0‖*(t*μ) ≤
      (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * μ * (s+t) := by
    have h1 : μ * xi ≤ μ * (2*s) := mul_le_mul_of_nonneg_left hxi_le2s hμpos.le
    have h2 : μ * eta ≤ μ * (2*t) := mul_le_mul_of_nonneg_left heta_le2t hμpos.le
    have h3 : 0 ≤ ‖menchoffFx g z0‖ * (μ*t) := mul_nonneg (norm_nonneg _) (by positivity)
    have h4 : 0 ≤ ‖menchoffFy g z0‖ * (μ*s) := mul_nonneg (norm_nonneg _) (by positivity)
    have h5 : 0 ≤ μ * s := by positivity
    have h6 : 0 ≤ μ * t := by positivity
    nlinarith [h1, h2, h3, h4, h5, h6]
  have hbnd : ‖g (z0+(s:ℂ)+(t:ℂ)*I) - w‖ ≤ (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * μ * (s+t) :=
    le_trans hzetabound (le_trans hfinal1.le hfinal2)
  have heq : g (z0+(s:ℂ)+(t:ℂ)*I) - g z0 - menchoffFx g z0 * (s:ℂ) - menchoffFy g z0 * (t:ℂ) =
      g (z0+(s:ℂ)+(t:ℂ)*I) - w := by rw [hw_def]; ring
  rw [abs_of_pos hs0, abs_of_pos ht0, heq]
  exact hbnd

/-- Mirror of `menchoff_edge_finish_h` for the top/bottom edges (via `menchoff_two_step_vh`,
whose bound is `2*|ξ|+|η|` instead of `|ξ|+2*|η|`). -/
theorem menchoff_edge_finish_v {g : ℂ → ℂ} {z0 zeta : ℂ} {xi eta s t μ : ℝ}
    (hs0 : 0 < s) (ht0 : 0 < t) (hμpos : 0 < μ)
    (hxipos : 0 < xi) (hetapos : 0 < eta)
    (hxi_le2s : xi ≤ 2*s) (heta_le2t : eta ≤ 2*t)
    (hxiclose : |xi - s| ≤ s*μ) (hetaclose : |eta - t| ≤ t*μ)
    (hzetaeq : zeta = z0 + xi + eta * I)
    (hstep : ‖g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta‖ < μ*(2*xi+eta))
    (hzetabound : ‖g (z0+(s:ℂ)+(t:ℂ)*I) - (g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ))‖
      ≤ ‖g zeta - (g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ))‖) :
    ‖g (z0+(s:ℂ)+(t:ℂ)*I) - g z0 - menchoffFx g z0 * (s:ℂ) - menchoffFy g z0 * (t:ℂ)‖ ≤
      (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * μ * (|s| + |t|) := by
  set w : ℂ := g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ) with hw_def
  have hgzeta : ‖g zeta - w‖ ≤
      ‖g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta‖ +
      ‖menchoffFx g z0‖ * |xi - s| + ‖menchoffFy g z0‖ * |eta - t| := by
    have hdecomp : g zeta - w =
        (g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta) +
        menchoffFx g z0 * ((xi:ℂ) - s) + menchoffFy g z0 * ((eta:ℂ) - t) := by
      simp only [hw_def]; push_cast; ring
    rw [hdecomp]
    calc ‖(g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta) +
          menchoffFx g z0 * ((xi:ℂ) - s) + menchoffFy g z0 * ((eta:ℂ) - t)‖
        ≤ ‖g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta‖ +
          ‖menchoffFx g z0 * ((xi:ℂ) - s)‖ + ‖menchoffFy g z0 * ((eta:ℂ) - t)‖ := by
          have s1 := norm_add_le (g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta +
            menchoffFx g z0 * ((xi:ℂ) - s)) (menchoffFy g z0 * ((eta:ℂ) - t))
          have s2 := norm_add_le (g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta)
            (menchoffFx g z0 * ((xi:ℂ) - s))
          linarith [s1, s2]
      _ = _ := by
          have e1 : ‖((xi:ℂ) - s)‖ = |xi - s| := by
            rw [show ((xi:ℂ)-s) = ((xi-s:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs]
          have e2 : ‖((eta:ℂ) - t)‖ = |eta - t| := by
            rw [show ((eta:ℂ)-t) = ((eta-t:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs]
          rw [norm_mul, norm_mul, e1, e2]
  have hfinal1 : ‖g zeta - w‖ < μ*(2*xi+eta) + ‖menchoffFx g z0‖*(s*μ) + ‖menchoffFy g z0‖*(t*μ) := by
    have hb1 : ‖menchoffFx g z0‖ * |xi - s| ≤ ‖menchoffFx g z0‖ * (s*μ) :=
      mul_le_mul_of_nonneg_left hxiclose (norm_nonneg _)
    have hb2 : ‖menchoffFy g z0‖ * |eta - t| ≤ ‖menchoffFy g z0‖ * (t*μ) :=
      mul_le_mul_of_nonneg_left hetaclose (norm_nonneg _)
    linarith [hgzeta, hstep, hb1, hb2]
  have hfinal2 : μ*(2*xi+eta) + ‖menchoffFx g z0‖*(s*μ) + ‖menchoffFy g z0‖*(t*μ) ≤
      (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * μ * (s+t) := by
    have h1 : μ * xi ≤ μ * (2*s) := mul_le_mul_of_nonneg_left hxi_le2s hμpos.le
    have h2 : μ * eta ≤ μ * (2*t) := mul_le_mul_of_nonneg_left heta_le2t hμpos.le
    have h3 : 0 ≤ ‖menchoffFx g z0‖ * (μ*t) := mul_nonneg (norm_nonneg _) (by positivity)
    have h4 : 0 ≤ ‖menchoffFy g z0‖ * (μ*s) := mul_nonneg (norm_nonneg _) (by positivity)
    have h5 : 0 ≤ μ * s := by positivity
    have h6 : 0 ≤ μ * t := by positivity
    nlinarith [h1, h2, h3, h4, h5, h6]
  have hbnd : ‖g (z0+(s:ℂ)+(t:ℂ)*I) - w‖ ≤ (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * μ * (s+t) :=
    le_trans hzetabound (le_trans hfinal1.le hfinal2)
  have heq : g (z0+(s:ℂ)+(t:ℂ)*I) - g z0 - menchoffFx g z0 * (s:ℂ) - menchoffFy g z0 * (t:ℂ) =
      g (z0+(s:ℂ)+(t:ℂ)*I) - w := by rw [hw_def]; ring
  rw [abs_of_pos hs0, abs_of_pos ht0, heq]
  exact hbnd

set_option maxHeartbeats 1000000 in
theorem menchoff_M4_quadrant_pp {g : ℂ → ℂ} (hg : Continuous g) {Q : Set ℂ} (hQ : IsOpen Q)
    (hopen : ∀ U ⊆ Q, IsOpen U → IsOpen (g '' U))
    {E : Set ℂ} (hEQ : E ⊆ Q)
    {z0 : ℂ} (hz0 : z0 ∈ E) {m N : ℕ}
    (hM2 : ∀ z ∈ E, ∀ s : ℝ, s ≠ 0 → |s| < 1/((N:ℝ)+1) →
      ‖slope (fun t : ℝ => g (z + t)) 0 s - menchoffFx g z‖ < 1/((m:ℝ)+1) ∧
      ‖slope (fun t : ℝ => g (z + t * I)) 0 s - menchoffFy g z‖ < 1/((m:ℝ)+1))
    (hCfx : ContinuousWithinAt (menchoffFx g) E z0)
    (hCfy : ContinuousWithinAt (menchoffFy g) E z0)
    (hDensHR : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ →
      ∃ ξ ∈ Set.Ioc (s/(1+ε)) s, z0 + ξ ∈ E)
    (hDensVR : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      ∃ η ∈ Set.Ioc (t/(1+ε)) t, z0 + η * I ∈ E) :
    ∃ δ > 0, ∀ s t : ℝ, 0 < s → s < δ → 0 < t → t < δ →
      ‖g (z0 + s + t * I) - g z0 - menchoffFx g z0 * s - menchoffFy g z0 * t‖ ≤
        (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * (1/((m:ℝ)+1)) * (|s| + |t|) := by
  set μ : ℝ := 1/((m:ℝ)+1) with hμ_def
  have hμpos : 0 < μ := by positivity
  obtain ⟨δC1, hδC1, hCfxProp⟩ := Metric.tendsto_nhdsWithin_nhds.mp hCfx μ hμpos
  obtain ⟨δC2, hδC2, hCfyProp⟩ := Metric.tendsto_nhdsWithin_nhds.mp hCfy μ hμpos
  obtain ⟨δHR, hδHR, hHRProp⟩ := hDensHR μ hμpos
  obtain ⟨δVR, hδVR, hVRProp⟩ := hDensVR μ hμpos
  obtain ⟨ρ, hρpos, hballQ⟩ := Metric.isOpen_iff.mp hQ z0 (hEQ hz0)
  set δ0 : ℝ := min (min δC1 δC2) (min δHR δVR) with hδ0_def
  have hδ0pos : 0 < δ0 := lt_min (lt_min hδC1 hδC2) (lt_min hδHR hδVR)
  set δ1 : ℝ := min δ0 (ρ/3) with hδ1_def
  have hδ1pos : 0 < δ1 := lt_min hδ0pos (by positivity)
  set δ : ℝ := min (δ1 / (1+μ)) (1/((N:ℝ)+2) / (1+μ)) with hδ_def
  have hδpos : 0 < δ := by positivity
  refine ⟨δ, hδpos, fun s t hs0 hsδ ht0 htδ => ?_⟩
  have hδ_le1 : δ ≤ δ1 / (1+μ) := min_le_left _ _
  have hδ_le2 : δ ≤ (1/((N:ℝ)+2)) / (1+μ) := min_le_right _ _
  have h1μpos : (0:ℝ) < 1 + μ := by positivity
  have hs1μ : (1+μ) * s < δ1 := by
    have : s < δ1 / (1+μ) := lt_of_lt_of_le hsδ hδ_le1
    rw [lt_div_iff₀' h1μpos] at this
    linarith
  have ht1μ : (1+μ) * t < δ1 := by
    have : t < δ1 / (1+μ) := lt_of_lt_of_le htδ hδ_le1
    rw [lt_div_iff₀' h1μpos] at this
    linarith
  have hsN : (1+μ) * s < 1/((N:ℝ)+2) := by
    have : s < (1/((N:ℝ)+2)) / (1+μ) := lt_of_lt_of_le hsδ hδ_le2
    rw [lt_div_iff₀' h1μpos] at this
    linarith
  have htN : (1+μ) * t < 1/((N:ℝ)+2) := by
    have : t < (1/((N:ℝ)+2)) / (1+μ) := lt_of_lt_of_le htδ hδ_le2
    rw [lt_div_iff₀' h1μpos] at this
    linarith
  have hδ0ledC1 : δ0 ≤ δC1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ0ledC2 : δ0 ≤ δC2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ0ledHR : δ0 ≤ δHR := (min_le_right _ _).trans (min_le_left _ _)
  have hδ0ledVR : δ0 ≤ δVR := (min_le_right _ _).trans (min_le_right _ _)
  have hδ1leδ0 : δ1 ≤ δ0 := min_le_left _ _
  have hδ1leρ3 : δ1 ≤ ρ/3 := min_le_right _ _
  have hsleμs : s ≤ (1+μ)*s := by nlinarith [hμpos, hs0]
  have htleμt : t ≤ (1+μ)*t := by nlinarith [hμpos, ht0]
  have hsHR : s < δHR := lt_of_le_of_lt hsleμs (hs1μ.trans_le (hδ1leδ0.trans hδ0ledHR))
  have htVR : t < δVR := lt_of_le_of_lt htleμt (ht1μ.trans_le (hδ1leδ0.trans hδ0ledVR))
  have hμsHR : (1+μ)*s < δHR := hs1μ.trans_le (hδ1leδ0.trans hδ0ledHR)
  have hμtVR : (1+μ)*t < δVR := ht1μ.trans_le (hδ1leδ0.trans hδ0ledVR)
  obtain ⟨ξ1, hξ1mem, hξ1E⟩ := hHRProp s hs0 hsHR
  obtain ⟨ξ2, hξ2mem, hξ2E⟩ := hHRProp ((1+μ)*s) (by positivity) hμsHR
  obtain ⟨η1, hη1mem, hη1E⟩ := hVRProp t ht0 htVR
  obtain ⟨η2, hη2mem, hη2E⟩ := hVRProp ((1+μ)*t) (by positivity) hμtVR
  rw [Set.mem_Ioc] at hξ1mem hξ2mem hη1mem hη2mem
  have hcancels : (1+μ)*s/(1+μ) = s := by field_simp
  have hcancelt : (1+μ)*t/(1+μ) = t := by field_simp
  have hξ2mem' : s < ξ2 ∧ ξ2 ≤ (1+μ)*s := by
    refine ⟨?_, hξ2mem.2⟩
    have := hξ2mem.1; rwa [hcancels] at this
  have hη2mem' : t < η2 ∧ η2 ≤ (1+μ)*t := by
    refine ⟨?_, hη2mem.2⟩
    have := hη2mem.1; rwa [hcancelt] at this
  -- basic order facts
  have hξ1pos : 0 < ξ1 := lt_trans (by positivity) hξ1mem.1
  have hη1pos : 0 < η1 := lt_trans (by positivity) hη1mem.1
  have hξ1lts : ξ1 ≤ s := hξ1mem.2
  have hη1let : η1 ≤ t := hη1mem.2
  have hslt2 : s < ξ2 := hξ2mem'.1
  have htlt2 : t < η2 := hη2mem'.1
  have hξ1ltξ2 : ξ1 < ξ2 := lt_of_le_of_lt hξ1lts hslt2
  have hη1ltη2 : η1 < η2 := lt_of_le_of_lt hη1let htlt2
  have hξ1ubd : ξ1 ≤ (1+μ)*s := hξ1lts.trans hsleμs
  have hη1ubd : η1 ≤ (1+μ)*t := hη1let.trans htleμt
  have hξ2ubd : ξ2 ≤ (1+μ)*s := hξ2mem'.2
  have hη2ubd : η2 ≤ (1+μ)*t := hη2mem'.2
  set R : Set ℂ := closedRect (z0.re+ξ1) (z0.re+ξ2) (z0.im+η1) (z0.im+η2) with hR_def
  have hRsub : R ⊆ Q := by
    intro w hw
    simp only [hR_def, closedRect, Set.mem_setOf_eq] at hw
    apply hballQ
    rw [Metric.mem_ball, dist_eq_norm]
    have hre : |w.re - z0.re| ≤ (1+μ)*s := by
      rw [abs_le]; constructor <;> [linarith [hw.1, hξ1pos]; linarith [hw.2.1]]
    have him : |w.im - z0.im| ≤ (1+μ)*t := by
      rw [abs_le]; constructor <;> [linarith [hw.2.2.1, hη1pos]; linarith [hw.2.2.2]]
    have hbound : ‖w - z0‖ ≤ |w.re - z0.re| + |w.im - z0.im| := by
      have heq : (w - z0).re = w.re - z0.re := by simp
      have heq2 : (w - z0).im = w.im - z0.im := by simp
      calc ‖w - z0‖ ≤ |(w-z0).re| + |(w-z0).im| := Complex.norm_le_abs_re_add_abs_im _
        _ = |w.re - z0.re| + |w.im - z0.im| := by rw [heq, heq2]
    have h1 : (1+μ)*s < ρ/3 := lt_of_lt_of_le hs1μ hδ1leρ3
    have h2 : (1+μ)*t < ρ/3 := lt_of_lt_of_le ht1μ hδ1leρ3
    linarith [hbound, hre, him, h1, h2]
  set w : ℂ := g z0 + menchoffFx g z0 * s + menchoffFy g z0 * t with hw_def
  have hzst_mem : z0 + s + t * I ∈ R := by
    simp only [hR_def, closedRect, Set.mem_setOf_eq]
    have hre : (z0 + (s:ℂ) + (t:ℂ) * I).re = z0.re + s := by simp
    have him : (z0 + (s:ℂ) + (t:ℂ) * I).im = z0.im + t := by simp
    rw [hre, him]
    refine ⟨by linarith [hξ1lts], by linarith [hslt2], by linarith [hη1let], by linarith [htlt2]⟩
  have hab' : z0.re + ξ1 < z0.re + ξ2 := by linarith
  have hcd' : z0.im + η1 < z0.im + η2 := by linarith
  obtain ⟨ζ, hζfr, hζbound⟩ := menchoff_max_principle (a := z0.re+ξ1) (b := z0.re+ξ2)
    (c := z0.im+η1) (d := z0.im+η2) hg.continuousOn hopen hab' hcd' hRsub w hzst_mem
  have hζbound' : ‖g (z0+(s:ℂ)+(t:ℂ)*I) - (g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ))‖
      ≤ ‖g ζ - (g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ))‖ := by
    rw [← hw_def]; exact hζbound
  have hRclosed : IsClosed R := (acl_isCompact_closedRect _ _ _ _).isClosed
  have hζR : ζ ∈ R := by
    have := hζfr.1
    rwa [hRclosed.closure_eq] at this
  have hζRmem : z0.re+ξ1 ≤ ζ.re ∧ ζ.re ≤ z0.re+ξ2 ∧ z0.im+η1 ≤ ζ.im ∧ ζ.im ≤ z0.im+η2 := by
    simpa only [hR_def, closedRect, Set.mem_setOf_eq] using hζR
  have hζcase : ζ.re = z0.re+ξ1 ∨ ζ.re = z0.re+ξ2 ∨ ζ.im = z0.im+η1 ∨ ζ.im = z0.im+η2 := by
    by_contra hcon
    push Not at hcon
    have hζint : ζ ∈ interior R := by
      rw [hR_def, menchoff_interior_closedRect]
      simp only [openRect, Set.mem_setOf_eq]
      exact ⟨lt_of_le_of_ne hζRmem.1 (Ne.symm hcon.1),
        lt_of_le_of_ne hζRmem.2.1 hcon.2.1,
        lt_of_le_of_ne hζRmem.2.2.1 (Ne.symm hcon.2.2.1),
        lt_of_le_of_ne hζRmem.2.2.2 hcon.2.2.2⟩
    exact hζfr.2 hζint
  -- shared numeric facts for all four edges
  have hN2 : (1:ℝ)/((N:ℝ)+2) < 1/((N:ℝ)+1) := by
    apply div_lt_div_of_pos_left (by norm_num) (by positivity); linarith
  have hξ1small : |ξ1| < 1/((N:ℝ)+1) := by
    rw [abs_of_pos hξ1pos]; exact lt_of_le_of_lt hξ1ubd (hsN.trans hN2)
  have hξ2small : |ξ2| < 1/((N:ℝ)+1) := by
    rw [abs_of_pos (lt_trans hξ1pos hξ1ltξ2)]; exact lt_of_le_of_lt hξ2ubd (hsN.trans hN2)
  have hη1small : |η1| < 1/((N:ℝ)+1) := by
    rw [abs_of_pos hη1pos]; exact lt_of_le_of_lt hη1ubd (htN.trans hN2)
  have hη2small : |η2| < 1/((N:ℝ)+1) := by
    rw [abs_of_pos (lt_trans hη1pos hη1ltη2)]; exact lt_of_le_of_lt hη2ubd (htN.trans hN2)
  have hξ1D : |ξ1| < δC1 ∧ |ξ1| < δC2 := by
    rw [abs_of_pos hξ1pos]
    exact ⟨lt_of_le_of_lt hξ1ubd (hs1μ.trans_le (hδ1leδ0.trans hδ0ledC1)),
      lt_of_le_of_lt hξ1ubd (hs1μ.trans_le (hδ1leδ0.trans hδ0ledC2))⟩
  have hη1D : |η1| < δC1 ∧ |η1| < δC2 := by
    rw [abs_of_pos hη1pos]
    exact ⟨lt_of_le_of_lt hη1ubd (ht1μ.trans_le (hδ1leδ0.trans hδ0ledC1)),
      lt_of_le_of_lt hη1ubd (ht1μ.trans_le (hδ1leδ0.trans hδ0ledC2))⟩
  have hξ2pos : 0 < ξ2 := lt_trans hξ1pos hξ1ltξ2
  have hη2pos : 0 < η2 := lt_trans hη1pos hη1ltη2
  have hξ2D : |ξ2| < δC1 ∧ |ξ2| < δC2 := by
    rw [abs_of_pos hξ2pos]
    exact ⟨lt_of_le_of_lt hξ2ubd (hs1μ.trans_le (hδ1leδ0.trans hδ0ledC1)),
      lt_of_le_of_lt hξ2ubd (hs1μ.trans_le (hδ1leδ0.trans hδ0ledC2))⟩
  have hη2D : |η2| < δC1 ∧ |η2| < δC2 := by
    rw [abs_of_pos hη2pos]
    exact ⟨lt_of_le_of_lt hη2ubd (ht1μ.trans_le (hδ1leδ0.trans hδ0ledC1)),
      lt_of_le_of_lt hη2ubd (ht1μ.trans_le (hδ1leδ0.trans hδ0ledC2))⟩
  have hξ1close : |ξ1 - s| < s*μ := menchoff_bracket_close_lo hs0 hμpos hξ1mem
  have hη1close : |η1 - t| < t*μ := menchoff_bracket_close_lo ht0 hμpos hη1mem
  have hξ2close : |ξ2 - s| ≤ s*μ := menchoff_bracket_close_hi hs0 hμpos hslt2 hξ2mem'.2
  have hη2close : |η2 - t| ≤ t*μ := menchoff_bracket_close_hi ht0 hμpos htlt2 hη2mem'.2
  have hμle1 : μ ≤ 1 := by
    rw [hμ_def, div_le_one₀ (by positivity)]
    have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hξ2le2s : ξ2 ≤ 2*s := by
    have hstep1 : μ*s ≤ 1*s := mul_le_mul_of_nonneg_right hμle1 hs0.le
    have hstep2 : (1+μ)*s = s + μ*s := by ring
    have hstep3 : (1+μ)*s ≤ 2*s := by rw [hstep2]; linarith [hstep1]
    linarith [hξ2ubd, hstep3]
  have hη2le2t : η2 ≤ 2*t := by
    have hstep1 : μ*t ≤ 1*t := mul_le_mul_of_nonneg_right hμle1 ht0.le
    have hstep2 : (1+μ)*t = t + μ*t := by ring
    have hstep3 : (1+μ)*t ≤ 2*t := by rw [hstep2]; linarith [hstep1]
    linarith [hη2ubd, hstep3]
  have hξ1close' : s - ξ1 ≤ s*μ := by
    have := abs_le.mp hξ1close.le; linarith [this.1]
  have hξ2close' : ξ2 - s ≤ s*μ := by
    have := abs_le.mp hξ2close; linarith [this.1]
  have hη1close' : t - η1 ≤ t*μ := by
    have := abs_le.mp hη1close.le; linarith [this.1]
  have hη2close' : η2 - t ≤ t*μ := by
    have := abs_le.mp hη2close; linarith [this.1]
  rcases hζcase with hcase | hcase | hcase | hcase
  · -- LEFT edge: ζ.re = z0.re + ξ1
    set etaT : ℝ := ζ.im - z0.im with hetaT_def
    have hetaTmem1 : η1 ≤ etaT := by simp only [hetaT_def]; linarith [hζRmem.2.2.1]
    have hetaTmem2 : etaT ≤ η2 := by simp only [hetaT_def]; linarith [hζRmem.2.2.2]
    have hζeq : ζ = z0 + ξ1 + etaT * I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hcase]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, hetaT_def]
        ring
    have hetaTne : etaT ≠ 0 := by linarith [hetaTmem1, hη1pos]
    have hetaTclose : |etaT - t| ≤ t*μ :=
      menchoff_sandwich_close hetaTmem1 hetaTmem2 hη1let htlt2.le hη1close' hη2close'
    have hetaTsmall : |etaT| < 1/((N:ℝ)+1) := by
      rw [abs_of_pos (by linarith)]
      exact lt_of_le_of_lt hetaTmem2 (by rw [abs_of_pos hη2pos] at hη2small; exact hη2small)
    have hbx : ‖slope (fun u:ℝ => g (z0+u)) 0 ξ1 - menchoffFx g z0‖ < μ :=
      (hM2 z0 hz0 ξ1 hξ1pos.ne' hξ1small).1
    have hby : ‖slope (fun u:ℝ => g ((z0+ξ1)+u*I)) 0 etaT - menchoffFy g (z0+ξ1)‖ < μ :=
      (hM2 (z0+ξ1) hξ1E etaT hetaTne hetaTsmall).2
    have hfy : ‖menchoffFy g (z0+ξ1) - menchoffFy g z0‖ < μ := by
      have hd : dist (z0+(ξ1:ℂ)) z0 < δC2 := by
        rw [dist_eq_norm]
        have : z0 + (ξ1:ℂ) - z0 = (ξ1:ℂ) := by ring
        rw [this, norm_real, Real.norm_eq_abs]
        exact hξ1D.2
      have := hCfyProp hξ1E hd
      rwa [dist_eq_norm] at this
    have hstep := menchoff_two_step hξ1pos.ne' hetaTne hbx hby hfy
    rw [← hζeq, abs_of_pos hξ1pos, abs_of_pos (show (0:ℝ) < etaT by linarith)] at hstep
    have hetaTubd : etaT ≤ 2*t := le_trans hetaTmem2 hη2le2t
    exact menchoff_edge_finish_h hs0 ht0 hμpos hξ1pos (by linarith)
      (by linarith [hξ1lts]) hetaTubd hξ1close.le hetaTclose hζeq hstep hζbound'
  · -- RIGHT edge: ζ.re = z0.re + ξ2
    set etaT : ℝ := ζ.im - z0.im with hetaT_def
    have hetaTmem1 : η1 ≤ etaT := by simp only [hetaT_def]; linarith [hζRmem.2.2.1]
    have hetaTmem2 : etaT ≤ η2 := by simp only [hetaT_def]; linarith [hζRmem.2.2.2]
    have hζeq : ζ = z0 + ξ2 + etaT * I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hcase]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, hetaT_def]
        ring
    have hetaTne : etaT ≠ 0 := by linarith [hetaTmem1, hη1pos]
    have hetaTclose : |etaT - t| ≤ t*μ :=
      menchoff_sandwich_close hetaTmem1 hetaTmem2 hη1let htlt2.le hη1close' hη2close'
    have hetaTsmall : |etaT| < 1/((N:ℝ)+1) := by
      rw [abs_of_pos (by linarith)]
      exact lt_of_le_of_lt hetaTmem2 (by rw [abs_of_pos hη2pos] at hη2small; exact hη2small)
    have hbx : ‖slope (fun u:ℝ => g (z0+u)) 0 ξ2 - menchoffFx g z0‖ < μ :=
      (hM2 z0 hz0 ξ2 hξ2pos.ne' hξ2small).1
    have hby : ‖slope (fun u:ℝ => g ((z0+ξ2)+u*I)) 0 etaT - menchoffFy g (z0+ξ2)‖ < μ :=
      (hM2 (z0+ξ2) hξ2E etaT hetaTne hetaTsmall).2
    have hfy : ‖menchoffFy g (z0+ξ2) - menchoffFy g z0‖ < μ := by
      have hd : dist (z0+(ξ2:ℂ)) z0 < δC2 := by
        rw [dist_eq_norm]
        have heq0 : z0 + (ξ2:ℂ) - z0 = (ξ2:ℂ) := by ring
        rw [heq0, norm_real, Real.norm_eq_abs]
        exact hξ2D.2
      have := hCfyProp hξ2E hd
      rwa [dist_eq_norm] at this
    have hstep := menchoff_two_step hξ2pos.ne' hetaTne hbx hby hfy
    rw [← hζeq, abs_of_pos hξ2pos, abs_of_pos (show (0:ℝ) < etaT by linarith)] at hstep
    have hetaTubd : etaT ≤ 2*t := le_trans hetaTmem2 hη2le2t
    exact menchoff_edge_finish_h hs0 ht0 hμpos hξ2pos (by linarith)
      hξ2le2s hetaTubd hξ2close hetaTclose hζeq hstep hζbound'
  · -- BOTTOM edge: ζ.im = z0.im + η1
    set xiT : ℝ := ζ.re - z0.re with hxiT_def
    have hxiTmem1 : ξ1 ≤ xiT := by simp only [hxiT_def]; linarith [hζRmem.1]
    have hxiTmem2 : xiT ≤ ξ2 := by simp only [hxiT_def]; linarith [hζRmem.2.1]
    have hζeq : ζ = z0 + xiT + η1 * I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hxiT_def]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, hcase]
        ring
    have hxiTne : xiT ≠ 0 := by linarith [hxiTmem1, hξ1pos]
    have hxiTclose : |xiT - s| ≤ s*μ :=
      menchoff_sandwich_close hxiTmem1 hxiTmem2 hξ1lts hslt2.le hξ1close' hξ2close'
    have hxiTsmall : |xiT| < 1/((N:ℝ)+1) := by
      rw [abs_of_pos (by linarith)]
      exact lt_of_le_of_lt hxiTmem2 (by rw [abs_of_pos hξ2pos] at hξ2small; exact hξ2small)
    have hby : ‖slope (fun u:ℝ => g (z0+u*I)) 0 η1 - menchoffFy g z0‖ < μ :=
      (hM2 z0 hz0 η1 hη1pos.ne' hη1small).2
    have hbx : ‖slope (fun u:ℝ => g ((z0+η1*I)+u)) 0 xiT - menchoffFx g (z0+η1*I)‖ < μ :=
      (hM2 (z0+η1*I) hη1E xiT hxiTne hxiTsmall).1
    have hfx : ‖menchoffFx g (z0+η1*I) - menchoffFx g z0‖ < μ := by
      have hd : dist (z0+(η1:ℂ)*I) z0 < δC1 := by
        rw [dist_eq_norm]
        have heq0 : z0 + (η1:ℂ)*I - z0 = (η1:ℂ)*I := by ring
        rw [heq0, norm_mul, norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
        exact hη1D.1
      have := hCfxProp hη1E hd
      rwa [dist_eq_norm] at this
    have hstep := menchoff_two_step_vh hxiTne hη1pos.ne' hby hbx hfx
    rw [← hζeq, abs_of_pos (show (0:ℝ) < xiT by linarith), abs_of_pos hη1pos] at hstep
    have hxiTubd : xiT ≤ 2*s := le_trans hxiTmem2 hξ2le2s
    exact menchoff_edge_finish_v hs0 ht0 hμpos (by linarith) hη1pos
      hxiTubd (by linarith [hη1let]) hxiTclose hη1close.le hζeq hstep hζbound'
  · -- TOP edge: ζ.im = z0.im + η2
    set xiT : ℝ := ζ.re - z0.re with hxiT_def
    have hxiTmem1 : ξ1 ≤ xiT := by simp only [hxiT_def]; linarith [hζRmem.1]
    have hxiTmem2 : xiT ≤ ξ2 := by simp only [hxiT_def]; linarith [hζRmem.2.1]
    have hζeq : ζ = z0 + xiT + η2 * I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hxiT_def]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, hcase]
        ring
    have hxiTne : xiT ≠ 0 := by linarith [hxiTmem1, hξ1pos]
    have hxiTclose : |xiT - s| ≤ s*μ :=
      menchoff_sandwich_close hxiTmem1 hxiTmem2 hξ1lts hslt2.le hξ1close' hξ2close'
    have hxiTsmall : |xiT| < 1/((N:ℝ)+1) := by
      rw [abs_of_pos (by linarith)]
      exact lt_of_le_of_lt hxiTmem2 (by rw [abs_of_pos hξ2pos] at hξ2small; exact hξ2small)
    have hby : ‖slope (fun u:ℝ => g (z0+u*I)) 0 η2 - menchoffFy g z0‖ < μ :=
      (hM2 z0 hz0 η2 hη2pos.ne' hη2small).2
    have hbx : ‖slope (fun u:ℝ => g ((z0+η2*I)+u)) 0 xiT - menchoffFx g (z0+η2*I)‖ < μ :=
      (hM2 (z0+η2*I) hη2E xiT hxiTne hxiTsmall).1
    have hfx : ‖menchoffFx g (z0+η2*I) - menchoffFx g z0‖ < μ := by
      have hd : dist (z0+(η2:ℂ)*I) z0 < δC1 := by
        rw [dist_eq_norm]
        have heq0 : z0 + (η2:ℂ)*I - z0 = (η2:ℂ)*I := by ring
        rw [heq0, norm_mul, norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
        exact hη2D.1
      have := hCfxProp hη2E hd
      rwa [dist_eq_norm] at this
    have hstep := menchoff_two_step_vh hxiTne hη2pos.ne' hby hbx hfx
    rw [← hζeq, abs_of_pos (show (0:ℝ) < xiT by linarith), abs_of_pos hη2pos] at hstep
    have hxiTubd : xiT ≤ 2*s := le_trans hxiTmem2 hξ2le2s
    exact menchoff_edge_finish_v hs0 ht0 hμpos (by linarith) hη2pos
      hxiTubd hη2le2t hxiTclose hη2close hζeq hstep hζbound'



/-- Tiny isolated fact (kept out of the main proof's huge context so `nlinarith` stays fast):
for `x < 0` and `μ ≤ 1`, `(1+μ)*x ≥ 2*x`. -/
theorem menchoff_mul_le_two_of_le_one {x μ : ℝ} (hx : x < 0) (hμ : μ ≤ 1) :
    (1+μ)*x ≥ 2*x := by nlinarith

/-- Companion for `x > 0`: `(1+μ)*x ≤ 2*x`. -/
theorem menchoff_mul_le_two_of_le_one_pos {x μ : ℝ} (hx : 0 < x) (hμ : μ ≤ 1) :
    (1+μ)*x ≤ 2*x := by nlinarith

/-- Sign-general form of -0f's `menchoff_edge_finish_h` (no positivity assumption on `s, t`),
for the horizontal-two-step branches (left/right rectangle edges) in the non-`pp` quadrants. -/
theorem menchoff_edge_finish_h_gen {g : ℂ → ℂ} {z0 zeta : ℂ} {xi eta s t μ : ℝ}
    (hμpos : 0 < μ)
    (hxi_le2s : |xi| ≤ 2* |s|) (heta_le2t : |eta| ≤ 2* |t|)
    (hxiclose : |xi - s| ≤ |s| *μ) (hetaclose : |eta - t| ≤ |t| *μ)
    (hzetaeq : zeta = z0 + xi + eta * I)
    (hstep : ‖g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta‖ < μ*(|xi|+2* |eta|))
    (hzetabound : ‖g (z0+(s:ℂ)+(t:ℂ)*I) - (g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ))‖
      ≤ ‖g zeta - (g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ))‖) :
    ‖g (z0+(s:ℂ)+(t:ℂ)*I) - g z0 - menchoffFx g z0 * (s:ℂ) - menchoffFy g z0 * (t:ℂ)‖ ≤
      (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * μ * (|s| + |t|) := by
  set w : ℂ := g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ) with hw_def
  have hgzeta : ‖g zeta - w‖ ≤
      ‖g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta‖ +
      ‖menchoffFx g z0‖ * |xi - s| + ‖menchoffFy g z0‖ * |eta - t| := by
    have hdecomp : g zeta - w =
        (g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta) +
        menchoffFx g z0 * ((xi:ℂ) - s) + menchoffFy g z0 * ((eta:ℂ) - t) := by
      simp only [hw_def]; push_cast; ring
    rw [hdecomp]
    calc ‖(g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta) +
          menchoffFx g z0 * ((xi:ℂ) - s) + menchoffFy g z0 * ((eta:ℂ) - t)‖
        ≤ ‖g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta‖ +
          ‖menchoffFx g z0 * ((xi:ℂ) - s)‖ + ‖menchoffFy g z0 * ((eta:ℂ) - t)‖ := by
          have s1 := norm_add_le (g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta +
            menchoffFx g z0 * ((xi:ℂ) - s)) (menchoffFy g z0 * ((eta:ℂ) - t))
          have s2 := norm_add_le (g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta)
            (menchoffFx g z0 * ((xi:ℂ) - s))
          linarith [s1, s2]
      _ = _ := by
          have e1 : ‖((xi:ℂ) - s)‖ = |xi - s| := by
            rw [show ((xi:ℂ)-s) = ((xi-s:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs]
          have e2 : ‖((eta:ℂ) - t)‖ = |eta - t| := by
            rw [show ((eta:ℂ)-t) = ((eta-t:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs]
          rw [norm_mul, norm_mul, e1, e2]
  have hfinal1 : ‖g zeta - w‖ < μ*(|xi|+2* |eta|) + ‖menchoffFx g z0‖*(|s| *μ) + ‖menchoffFy g z0‖*(|t| *μ) := by
    have hb1 : ‖menchoffFx g z0‖ * |xi - s| ≤ ‖menchoffFx g z0‖ * (|s| *μ) :=
      mul_le_mul_of_nonneg_left hxiclose (norm_nonneg _)
    have hb2 : ‖menchoffFy g z0‖ * |eta - t| ≤ ‖menchoffFy g z0‖ * (|t| *μ) :=
      mul_le_mul_of_nonneg_left hetaclose (norm_nonneg _)
    linarith [hgzeta, hstep, hb1, hb2]
  have hfinal2 : μ*(|xi|+2* |eta|) + ‖menchoffFx g z0‖*(|s| *μ) + ‖menchoffFy g z0‖*(|t| *μ) ≤
      (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * μ * (|s|+|t|) := by
    have h1 : μ * |xi| ≤ μ * (2* |s|) := mul_le_mul_of_nonneg_left hxi_le2s hμpos.le
    have h2 : μ * |eta| ≤ μ * (2* |t|) := mul_le_mul_of_nonneg_left heta_le2t hμpos.le
    have h3 : 0 ≤ ‖menchoffFx g z0‖ * (μ* |t|) := mul_nonneg (norm_nonneg _) (by positivity)
    have h4 : 0 ≤ ‖menchoffFy g z0‖ * (μ* |s|) := mul_nonneg (norm_nonneg _) (by positivity)
    have h5 : 0 ≤ μ * |s| := by positivity
    have h6 : 0 ≤ μ * |t| := by positivity
    nlinarith [h1, h2, h3, h4, h5, h6]
  have hbnd : ‖g (z0+(s:ℂ)+(t:ℂ)*I) - w‖ ≤ (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * μ * (|s|+|t|) :=
    le_trans hzetabound (le_trans hfinal1.le hfinal2)
  have heq : g (z0+(s:ℂ)+(t:ℂ)*I) - g z0 - menchoffFx g z0 * (s:ℂ) - menchoffFy g z0 * (t:ℂ) =
      g (z0+(s:ℂ)+(t:ℂ)*I) - w := by rw [hw_def]; ring
  rw [heq]
  exact hbnd

/-- Sign-general form of -0f's `menchoff_edge_finish_v` (no positivity assumption on `s, t`),
for the vertical-two-step branches (bottom/top rectangle edges) in the non-`pp` quadrants. -/
theorem menchoff_edge_finish_v_gen {g : ℂ → ℂ} {z0 zeta : ℂ} {xi eta s t μ : ℝ}
    (hμpos : 0 < μ)
    (hxi_le2s : |xi| ≤ 2* |s|) (heta_le2t : |eta| ≤ 2* |t|)
    (hxiclose : |xi - s| ≤ |s| *μ) (hetaclose : |eta - t| ≤ |t| *μ)
    (hzetaeq : zeta = z0 + xi + eta * I)
    (hstep : ‖g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta‖ < μ*(2* |xi|+|eta|))
    (hzetabound : ‖g (z0+(s:ℂ)+(t:ℂ)*I) - (g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ))‖
      ≤ ‖g zeta - (g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ))‖) :
    ‖g (z0+(s:ℂ)+(t:ℂ)*I) - g z0 - menchoffFx g z0 * (s:ℂ) - menchoffFy g z0 * (t:ℂ)‖ ≤
      (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * μ * (|s| + |t|) := by
  set w : ℂ := g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ) with hw_def
  have hgzeta : ‖g zeta - w‖ ≤
      ‖g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta‖ +
      ‖menchoffFx g z0‖ * |xi - s| + ‖menchoffFy g z0‖ * |eta - t| := by
    have hdecomp : g zeta - w =
        (g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta) +
        menchoffFx g z0 * ((xi:ℂ) - s) + menchoffFy g z0 * ((eta:ℂ) - t) := by
      simp only [hw_def]; push_cast; ring
    rw [hdecomp]
    calc ‖(g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta) +
          menchoffFx g z0 * ((xi:ℂ) - s) + menchoffFy g z0 * ((eta:ℂ) - t)‖
        ≤ ‖g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta‖ +
          ‖menchoffFx g z0 * ((xi:ℂ) - s)‖ + ‖menchoffFy g z0 * ((eta:ℂ) - t)‖ := by
          have s1 := norm_add_le (g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta +
            menchoffFx g z0 * ((xi:ℂ) - s)) (menchoffFy g z0 * ((eta:ℂ) - t))
          have s2 := norm_add_le (g zeta - g z0 - menchoffFx g z0 * xi - menchoffFy g z0 * eta)
            (menchoffFx g z0 * ((xi:ℂ) - s))
          linarith [s1, s2]
      _ = _ := by
          have e1 : ‖((xi:ℂ) - s)‖ = |xi - s| := by
            rw [show ((xi:ℂ)-s) = ((xi-s:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs]
          have e2 : ‖((eta:ℂ) - t)‖ = |eta - t| := by
            rw [show ((eta:ℂ)-t) = ((eta-t:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs]
          rw [norm_mul, norm_mul, e1, e2]
  have hfinal1 : ‖g zeta - w‖ < μ*(2* |xi|+|eta|) + ‖menchoffFx g z0‖*(|s| *μ) + ‖menchoffFy g z0‖*(|t| *μ) := by
    have hb1 : ‖menchoffFx g z0‖ * |xi - s| ≤ ‖menchoffFx g z0‖ * (|s| *μ) :=
      mul_le_mul_of_nonneg_left hxiclose (norm_nonneg _)
    have hb2 : ‖menchoffFy g z0‖ * |eta - t| ≤ ‖menchoffFy g z0‖ * (|t| *μ) :=
      mul_le_mul_of_nonneg_left hetaclose (norm_nonneg _)
    linarith [hgzeta, hstep, hb1, hb2]
  have hfinal2 : μ*(2* |xi|+|eta|) + ‖menchoffFx g z0‖*(|s| *μ) + ‖menchoffFy g z0‖*(|t| *μ) ≤
      (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * μ * (|s|+|t|) := by
    have h1 : μ * |xi| ≤ μ * (2* |s|) := mul_le_mul_of_nonneg_left hxi_le2s hμpos.le
    have h2 : μ * |eta| ≤ μ * (2* |t|) := mul_le_mul_of_nonneg_left heta_le2t hμpos.le
    have h3 : 0 ≤ ‖menchoffFx g z0‖ * (μ* |t|) := mul_nonneg (norm_nonneg _) (by positivity)
    have h4 : 0 ≤ ‖menchoffFy g z0‖ * (μ* |s|) := mul_nonneg (norm_nonneg _) (by positivity)
    have h5 : 0 ≤ μ * |s| := by positivity
    have h6 : 0 ≤ μ * |t| := by positivity
    nlinarith [h1, h2, h3, h4, h5, h6]
  have hbnd : ‖g (z0+(s:ℂ)+(t:ℂ)*I) - w‖ ≤ (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * μ * (|s|+|t|) :=
    le_trans hzetabound (le_trans hfinal1.le hfinal2)
  have heq : g (z0+(s:ℂ)+(t:ℂ)*I) - g z0 - menchoffFx g z0 * (s:ℂ) - menchoffFy g z0 * (t:ℂ) =
      g (z0+(s:ℂ)+(t:ℂ)*I) - w := by rw [hw_def]; ring
  rw [heq]
  exact hbnd

set_option maxHeartbeats 1000000 in
theorem menchoff_M4_quadrant_pm {g : ℂ → ℂ} (hg : Continuous g) {Q : Set ℂ} (hQ : IsOpen Q)
    (hopen : ∀ U ⊆ Q, IsOpen U → IsOpen (g '' U)) {E : Set ℂ} (hEQ : E ⊆ Q)
    {z0 : ℂ} (hz0 : z0 ∈ E) {m N : ℕ}
    (hM2 : ∀ z ∈ E, ∀ s : ℝ, s ≠ 0 → |s| < 1/((N:ℝ)+1) →
      ‖slope (fun t : ℝ => g (z + t)) 0 s - menchoffFx g z‖ < 1/((m:ℝ)+1) ∧
      ‖slope (fun t : ℝ => g (z + t * I)) 0 s - menchoffFy g z‖ < 1/((m:ℝ)+1))
    (hCfx : ContinuousWithinAt (menchoffFx g) E z0)
    (hCfy : ContinuousWithinAt (menchoffFy g) E z0)
    (hDensHR : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ →
      ∃ ξ ∈ Set.Ioc (s/(1+ε)) s, z0 + ξ ∈ E)
    (hDensVL : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      ∃ η ∈ Set.Ico (-t) (-(t/(1+ε))), z0 + η * I ∈ E) :
    ∃ δ > 0, ∀ s t : ℝ, 0 < s → s < δ → t < 0 → -δ < t →
      ‖g (z0 + s + t * I) - g z0 - menchoffFx g z0 * s - menchoffFy g z0 * t‖ ≤
        (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * (1/((m:ℝ)+1)) * (|s| + |t|) := by
  set μ : ℝ := 1/((m:ℝ)+1) with hμ_def
  have hμpos : 0 < μ := by positivity
  obtain ⟨δC1, hδC1, hCfxProp⟩ := Metric.tendsto_nhdsWithin_nhds.mp hCfx μ hμpos
  obtain ⟨δC2, hδC2, hCfyProp⟩ := Metric.tendsto_nhdsWithin_nhds.mp hCfy μ hμpos
  obtain ⟨δHR, hδHR, hHRProp⟩ := hDensHR μ hμpos
  obtain ⟨δVL, hδVL, hVLProp⟩ := hDensVL μ hμpos
  obtain ⟨ρ, hρpos, hballQ⟩ := Metric.isOpen_iff.mp hQ z0 (hEQ hz0)
  set δ0 : ℝ := min (min δC1 δC2) (min δHR δVL) with hδ0_def
  have hδ0pos : 0 < δ0 := lt_min (lt_min hδC1 hδC2) (lt_min hδHR hδVL)
  set δ1 : ℝ := min δ0 (ρ/3) with hδ1_def
  have hδ1pos : 0 < δ1 := lt_min hδ0pos (by positivity)
  set δ : ℝ := min (δ1 / (1+μ)) (1/((N:ℝ)+2) / (1+μ)) with hδ_def
  have hδpos : 0 < δ := by positivity
  refine ⟨δ, hδpos, fun s t hspos hsδ htneg htδ => ?_⟩
  have ht'0 : 0 < -t := by linarith
  have ht'δ : -t < δ := by linarith
  have h1μpos : (0:ℝ) < 1 + μ := by positivity
  have hδ_le1 : δ ≤ δ1 / (1+μ) := min_le_left _ _
  have hδ_le2 : δ ≤ (1/((N:ℝ)+2)) / (1+μ) := min_le_right _ _
  have hs1μ : (1+μ) * s < δ1 := by
    have hlt : s < δ1 / (1+μ) := lt_of_lt_of_le hsδ hδ_le1
    rw [lt_div_iff₀' h1μpos] at hlt; linarith
  have ht1μ : (1+μ) * (-t) < δ1 := by
    have hlt : -t < δ1 / (1+μ) := lt_of_lt_of_le ht'δ hδ_le1
    rw [lt_div_iff₀' h1μpos] at hlt; linarith
  have hsN : (1+μ) * s < 1/((N:ℝ)+2) := by
    have hlt : s < (1/((N:ℝ)+2)) / (1+μ) := lt_of_lt_of_le hsδ hδ_le2
    rw [lt_div_iff₀' h1μpos] at hlt; linarith
  have htN : (1+μ) * (-t) < 1/((N:ℝ)+2) := by
    have hlt : -t < (1/((N:ℝ)+2)) / (1+μ) := lt_of_lt_of_le ht'δ hδ_le2
    rw [lt_div_iff₀' h1μpos] at hlt; linarith
  have hδ0ledC1 : δ0 ≤ δC1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ0ledC2 : δ0 ≤ δC2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ0ledHR : δ0 ≤ δHR := (min_le_right _ _).trans (min_le_left _ _)
  have hδ0ledVL : δ0 ≤ δVL := (min_le_right _ _).trans (min_le_right _ _)
  have hδ1leδ0 : δ1 ≤ δ0 := min_le_left _ _
  have hδ1leρ3 : δ1 ≤ ρ/3 := min_le_right _ _
  have hsleμs : s ≤ (1+μ)*s := by nlinarith [hμpos, hspos]
  have htleμt : (-t) ≤ (1+μ)*(-t) := by nlinarith [hμpos, ht'0]
  have hsHR : s < δHR := lt_of_le_of_lt hsleμs (hs1μ.trans_le (hδ1leδ0.trans hδ0ledHR))
  have htVL : (-t) < δVL := lt_of_le_of_lt htleμt (ht1μ.trans_le (hδ1leδ0.trans hδ0ledVL))
  have hμsHR : (1+μ)*s < δHR := hs1μ.trans_le (hδ1leδ0.trans hδ0ledHR)
  have hμtVL : (1+μ)*(-t) < δVL := ht1μ.trans_le (hδ1leδ0.trans hδ0ledVL)
  obtain ⟨xiLo, hxiLomem, hxiLoE⟩ := hHRProp s hspos hsHR
  obtain ⟨xiHi, hxiHimem, hxiHiE⟩ := hHRProp ((1+μ)*s) (by positivity) hμsHR
  obtain ⟨etaHi, hetaHimem, hetaHiE⟩ := hVLProp (-t) ht'0 htVL
  obtain ⟨etaLo, hetaLomem, hetaLoE⟩ := hVLProp ((1+μ)*(-t)) (by positivity) hμtVL
  rw [Set.mem_Ioc] at hxiLomem hxiHimem
  rw [Set.mem_Ico] at hetaHimem hetaLomem
  have hcancels : (1+μ)*s/(1+μ) = s := by field_simp
  have hxiHimem' : s < xiHi ∧ xiHi ≤ (1+μ)*s := by
    refine ⟨?_, hxiHimem.2⟩
    have := hxiHimem.1; rwa [hcancels] at this
  have hxiLo_lo : s/(1+μ) < xiLo := hxiLomem.1
  have hxiLo_hi : xiLo ≤ s := hxiLomem.2
  have hxiHi_lo : s < xiHi := hxiHimem'.1
  have hxiHi_hi : xiHi ≤ (1+μ)*s := hxiHimem'.2
  have hetaHi_lo : t ≤ etaHi := by linarith [hetaHimem.1]
  have hetaHi_hi : etaHi < t/(1+μ) := by
    have heq : -((-t)/(1+μ)) = t/(1+μ) := by ring
    rw [← heq]; exact hetaHimem.2
  have hetaLo_lo : (1+μ)*t ≤ etaLo := by
    have heq : -((1+μ)*(-t)) = (1+μ)*t := by ring
    linarith [hetaLomem.1, heq]
  have hetaLo_hi : etaLo < t := by
    have heq : -((1+μ)*(-t)/(1+μ)) = t := by field_simp
    rw [← heq]; exact hetaLomem.2
  have hxiLo_lt_xiHi : xiLo < xiHi := lt_of_le_of_lt hxiLo_hi hxiHi_lo
  have hetaLo_lt_etaHi : etaLo < etaHi := lt_of_lt_of_le hetaLo_hi hetaHi_lo
  have hxiLo_ne0 : xiLo ≠ 0 := by
    intro h; rw [h] at hxiLo_lo
    have : (0:ℝ) < s/(1+μ) := div_pos hspos h1μpos
    linarith
  have hxiHi_ne0 : xiHi ≠ 0 := by intro h; rw [h] at hxiHi_lo; linarith
  have hetaLo_ne0 : etaLo ≠ 0 := by intro h; rw [h] at hetaLo_hi; linarith
  have hetaHi_ne0 : etaHi ≠ 0 := by
    intro h; rw [h] at hetaHi_hi
    have : t/(1+μ) < 0 := div_neg_of_neg_of_pos htneg h1μpos
    linarith
  set R : Set ℂ := closedRect (z0.re+xiLo) (z0.re+xiHi) (z0.im+etaLo) (z0.im+etaHi) with hR_def
  have hRsub : R ⊆ Q := by
    intro w hw
    simp only [hR_def, closedRect, Set.mem_setOf_eq] at hw
    apply hballQ
    rw [Metric.mem_ball, dist_eq_norm]
    have hre : |w.re - z0.re| ≤ (1+μ)*s := by
      rw [abs_le]
      constructor
      · have hpos1 : (0:ℝ) < s/(1+μ) := div_pos hspos h1μpos
        have hpos2 : (0:ℝ) < (1+μ)*s := by positivity
        linarith [hw.1, hxiLo_lo, hpos1, hpos2]
      · linarith [hw.2.1, hxiHi_hi]
    have him : |w.im - z0.im| ≤ (1+μ)*(-t) := by
      rw [abs_le]
      constructor
      · linarith [hw.2.2.1, hetaLo_lo]
      · have h2 : t/(1+μ) < 0 := div_neg_of_neg_of_pos htneg h1μpos
        linarith [hw.2.2.2, hetaHi_hi, h2]
    have hbound : ‖w - z0‖ ≤ |w.re - z0.re| + |w.im - z0.im| := by
      have heq : (w - z0).re = w.re - z0.re := by simp
      have heq2 : (w - z0).im = w.im - z0.im := by simp
      calc ‖w - z0‖ ≤ |(w-z0).re| + |(w-z0).im| := Complex.norm_le_abs_re_add_abs_im _
        _ = |w.re - z0.re| + |w.im - z0.im| := by rw [heq, heq2]
    have h1 : (1+μ)*s < ρ/3 := lt_of_lt_of_le hs1μ hδ1leρ3
    have h2 : (1+μ)*(-t) < ρ/3 := lt_of_lt_of_le ht1μ hδ1leρ3
    linarith [hbound, hre, him, h1, h2]
  set w : ℂ := g z0 + menchoffFx g z0 * s + menchoffFy g z0 * t with hw_def
  have hzst_mem : z0 + s + t * I ∈ R := by
    simp only [hR_def, closedRect, Set.mem_setOf_eq]
    have hre : (z0 + (s:ℂ) + (t:ℂ) * I).re = z0.re + s := by simp
    have him : (z0 + (s:ℂ) + (t:ℂ) * I).im = z0.im + t := by simp
    rw [hre, him]
    exact ⟨by linarith [hxiLo_hi], by linarith [hxiHi_lo], by linarith [hetaLo_hi], by linarith [hetaHi_lo]⟩
  have hab' : z0.re + xiLo < z0.re + xiHi := by linarith
  have hcd' : z0.im + etaLo < z0.im + etaHi := by linarith
  obtain ⟨ζ, hζfr, hζbound⟩ := menchoff_max_principle (a := z0.re+xiLo) (b := z0.re+xiHi)
    (c := z0.im+etaLo) (d := z0.im+etaHi) hg.continuousOn hopen hab' hcd' hRsub w hzst_mem
  have hζbound' : ‖g (z0+(s:ℂ)+(t:ℂ)*I) - (g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ))‖
      ≤ ‖g ζ - (g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ))‖ := by
    rw [← hw_def]; exact hζbound
  have hRclosed : IsClosed R := (acl_isCompact_closedRect _ _ _ _).isClosed
  have hζR : ζ ∈ R := by
    have := hζfr.1
    rwa [hRclosed.closure_eq] at this
  have hζRmem : z0.re+xiLo ≤ ζ.re ∧ ζ.re ≤ z0.re+xiHi ∧ z0.im+etaLo ≤ ζ.im ∧ ζ.im ≤ z0.im+etaHi := by
    simpa only [hR_def, closedRect, Set.mem_setOf_eq] using hζR
  have hζcase : ζ.re = z0.re+xiLo ∨ ζ.re = z0.re+xiHi ∨ ζ.im = z0.im+etaLo ∨ ζ.im = z0.im+etaHi := by
    by_contra hcon
    push Not at hcon
    have hζint : ζ ∈ interior R := by
      rw [hR_def, menchoff_interior_closedRect]
      simp only [openRect, Set.mem_setOf_eq]
      exact ⟨lt_of_le_of_ne hζRmem.1 (Ne.symm hcon.1),
        lt_of_le_of_ne hζRmem.2.1 hcon.2.1,
        lt_of_le_of_ne hζRmem.2.2.1 (Ne.symm hcon.2.2.1),
        lt_of_le_of_ne hζRmem.2.2.2 hcon.2.2.2⟩
    exact hζfr.2 hζint
  have hN2 : (1:ℝ)/((N:ℝ)+2) < 1/((N:ℝ)+1) := by
    apply div_lt_div_of_pos_left (by norm_num) (by positivity); linarith
  have hμle1 : μ ≤ 1 := by
    rw [hμ_def, div_le_one₀ (by positivity)]
    have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hxiLosmall : |xiLo| < 1/((N:ℝ)+1) := by
    rw [abs_of_pos (by linarith [hxiLo_lo, div_pos hspos h1μpos] : (0:ℝ) < xiLo)]
    linarith [hxiLo_hi, hsleμs, hsN, hN2]
  have hxiHismall : |xiHi| < 1/((N:ℝ)+1) := by
    rw [abs_of_pos (by linarith [hxiHi_lo, hspos] : (0:ℝ) < xiHi)]
    exact lt_of_le_of_lt hxiHi_hi (hsN.trans hN2)
  have hetaLosmall : |etaLo| < 1/((N:ℝ)+1) := by
    rw [abs_of_neg (by linarith [hetaLo_hi] : etaLo < 0)]
    have : -etaLo ≤ (1+μ)*(-t) := by linarith [hetaLo_lo]
    linarith [this, htN, hN2]
  have hetaHismall : |etaHi| < 1/((N:ℝ)+1) := by
    rw [abs_of_neg (by linarith [hetaHi_hi, div_neg_of_neg_of_pos htneg h1μpos] : etaHi < 0)]
    have : -etaHi ≤ -t := by linarith [hetaHi_lo]
    have h2 : -t ≤ (1+μ)*(-t) := htleμt
    linarith [this, h2, htN, hN2]
  have hxiLoD : |xiLo| < δC1 ∧ |xiLo| < δC2 := by
    rw [abs_of_pos (by linarith [hxiLo_lo, div_pos hspos h1μpos] : (0:ℝ) < xiLo)]
    constructor
    · have := hs1μ.trans_le (hδ1leδ0.trans hδ0ledC1); linarith [hxiLo_hi, hsleμs, this]
    · have := hs1μ.trans_le (hδ1leδ0.trans hδ0ledC2); linarith [hxiLo_hi, hsleμs, this]
  have hxiHiD : |xiHi| < δC1 ∧ |xiHi| < δC2 := by
    rw [abs_of_pos (by linarith [hxiHi_lo, hspos] : (0:ℝ) < xiHi)]
    exact ⟨lt_of_le_of_lt hxiHi_hi (hs1μ.trans_le (hδ1leδ0.trans hδ0ledC1)),
      lt_of_le_of_lt hxiHi_hi (hs1μ.trans_le (hδ1leδ0.trans hδ0ledC2))⟩
  have hetaLoD : |etaLo| < δC1 ∧ |etaLo| < δC2 := by
    rw [abs_of_neg (by linarith [hetaLo_hi] : etaLo < 0)]
    have h1 : -etaLo ≤ (1+μ)*(-t) := by linarith [hetaLo_lo]
    exact ⟨lt_of_le_of_lt h1 (ht1μ.trans_le (hδ1leδ0.trans hδ0ledC1)),
      lt_of_le_of_lt h1 (ht1μ.trans_le (hδ1leδ0.trans hδ0ledC2))⟩
  have hetaHiD : |etaHi| < δC1 ∧ |etaHi| < δC2 := by
    rw [abs_of_neg (by linarith [hetaHi_hi, div_neg_of_neg_of_pos htneg h1μpos] : etaHi < 0)]
    have h1 : -etaHi ≤ (1+μ)*(-t) := by linarith [hetaHi_lo, htleμt]
    exact ⟨lt_of_le_of_lt h1 (ht1μ.trans_le (hδ1leδ0.trans hδ0ledC1)),
      lt_of_le_of_lt h1 (ht1μ.trans_le (hδ1leδ0.trans hδ0ledC2))⟩
  have hxiLoclose : |xiLo - s| ≤ |s| *μ := by
    have h := menchoff_bracket_close_lo hspos hμpos ⟨hxiLo_lo, hxiLo_hi⟩
    rw [abs_of_pos hspos]; exact h.le
  have hxiHiclose : |xiHi - s| ≤ |s| *μ := by
    have := menchoff_bracket_close_hi hspos hμpos hxiHi_lo hxiHi_hi
    rwa [abs_of_pos hspos]
  have hetaLoclose : |etaLo - t| ≤ |t| *μ := by
    have := menchoff_bracket_close_hi ht'0 hμpos
      (show -t < -etaLo by linarith [hetaLo_hi]) (show -etaLo ≤ (1+μ)*(-t) by linarith [hetaLo_lo])
    rw [abs_of_neg htneg]
    have heq : |(-etaLo) - (-t)| = |etaLo - t| := by rw [← abs_neg]; ring_nf
    linarith [this, heq.symm.le, heq.le]
  have hetaHiclose : |etaHi - t| ≤ |t| *μ := by
    have hmem : (-etaHi) ∈ Set.Ioc ((-t)/(1+μ)) (-t) := by
      constructor
      · linarith [hetaHi_hi, div_neg_of_neg_of_pos htneg h1μpos]
      · linarith [hetaHi_lo]
    have := menchoff_bracket_close_lo ht'0 hμpos hmem
    rw [abs_of_neg htneg]
    have heq : |(-etaHi) - (-t)| = |etaHi - t| := by rw [← abs_neg]; ring_nf
    linarith [this.le, heq.symm.le, heq.le]
  have hkeyt : (1+μ)*t ≥ 2*t := menchoff_mul_le_two_of_le_one htneg hμle1
  have hxiLole2s : |xiLo| ≤ 2* |s| := by
    rw [abs_of_pos (by linarith [hxiLo_lo, div_pos hspos h1μpos] : (0:ℝ) < xiLo), abs_of_pos hspos]
    linarith [hxiLo_hi]
  have hkeys : (1+μ)*s ≤ 2*s := menchoff_mul_le_two_of_le_one_pos hspos hμle1
  have hxiHile2s : |xiHi| ≤ 2* |s| := by
    rw [abs_of_pos (by linarith [hxiHi_lo, hspos] : (0:ℝ) < xiHi), abs_of_pos hspos]
    linarith [hxiHi_hi, hkeys]
  have hetaLole2t : |etaLo| ≤ 2* |t| := by
    rw [abs_of_neg (by linarith [hetaLo_hi] : etaLo < 0), abs_of_neg htneg]
    linarith [hetaLo_lo, hkeyt]
  have hetaHile2t : |etaHi| ≤ 2* |t| := by
    rw [abs_of_neg (by linarith [hetaHi_hi, div_neg_of_neg_of_pos htneg h1μpos] : etaHi < 0),
      abs_of_neg htneg]
    linarith [hetaHi_lo, htneg]
  rcases hζcase with hcase | hcase | hcase | hcase
  · -- LEFT edge: ζ.re = z0.re + xiLo
    set etaT : ℝ := ζ.im - z0.im with hetaT_def
    have hetaTmem1 : etaLo ≤ etaT := by simp only [hetaT_def]; linarith [hζRmem.2.2.1]
    have hetaTmem2 : etaT ≤ etaHi := by simp only [hetaT_def]; linarith [hζRmem.2.2.2]
    have hζeq : ζ = z0 + xiLo + etaT * I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hcase]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, hetaT_def]
        ring
    have hetaTne : etaT ≠ 0 := by
      have hetaHineg0 : etaHi < 0 := by
        have h2 : t/(1+μ) < 0 := div_neg_of_neg_of_pos htneg h1μpos
        linarith [hetaHi_hi, h2]
      intro h
      rw [h] at hetaTmem2
      linarith [hetaTmem2, hetaHineg0]
    have hetaTclose : |etaT - t| ≤ |t| *μ := by
      have hlo' : t - etaLo ≤ |t| *μ := by linarith [(abs_le.mp hetaLoclose).1]
      have hhi' : etaHi - t ≤ |t| *μ := (abs_le.mp hetaHiclose).2
      exact menchoff_sandwich_close hetaTmem1 hetaTmem2 hetaLo_hi.le hetaHi_lo hlo' hhi'
    have hetaHineg : etaHi < 0 := by
      have h2 : t/(1+μ) < 0 := div_neg_of_neg_of_pos htneg h1μpos
      linarith [hetaHi_hi, h2]
    have hetaLoneg' : etaLo < 0 := by linarith [hetaLo_hi]
    have hetaTsmall : |etaT| < 1/((N:ℝ)+1) := by
      rcases le_total 0 etaT with h | h
      · rw [abs_of_nonneg h]
        have := abs_of_neg hetaHineg
        linarith [hetaTmem2, hetaHismall, this]
      · rw [abs_of_nonpos h]
        have := abs_of_neg hetaLoneg'
        linarith [hetaTmem1, hetaLosmall, this]
    have hbx : ‖slope (fun u:ℝ => g (z0+u)) 0 xiLo - menchoffFx g z0‖ < μ :=
      (hM2 z0 hz0 xiLo hxiLo_ne0 hxiLosmall).1
    have hby : ‖slope (fun u:ℝ => g ((z0+xiLo)+u*I)) 0 etaT - menchoffFy g (z0+xiLo)‖ < μ :=
      (hM2 (z0+xiLo) hxiLoE etaT hetaTne hetaTsmall).2
    have hfy : ‖menchoffFy g (z0+xiLo) - menchoffFy g z0‖ < μ := by
      have hd : dist (z0+(xiLo:ℂ)) z0 < δC2 := by
        rw [dist_eq_norm]
        have heq0 : z0 + (xiLo:ℂ) - z0 = (xiLo:ℂ) := by ring
        rw [heq0, norm_real, Real.norm_eq_abs]
        exact hxiLoD.2
      have := hCfyProp hxiLoE hd
      rwa [dist_eq_norm] at this
    have hstep := menchoff_two_step hxiLo_ne0 hetaTne hbx hby hfy
    rw [← hζeq] at hstep
    have hetaTle2t : |etaT| ≤ 2* |t| := by
      have hetaHile0 : etaHi ≤ 0 := by
        have h2 : t/(1+μ) < 0 := div_neg_of_neg_of_pos htneg h1μpos
        linarith [hetaHi_hi, h2]
      have hetaTneg : etaT ≤ 0 := le_trans hetaTmem2 hetaHile0
      rw [abs_of_nonpos hetaTneg]
      have : -etaT ≤ -etaLo := by linarith [hetaTmem1]
      have hetaLoneg : etaLo ≤ 0 := by linarith [hetaLo_hi]
      rw [abs_of_nonpos hetaLoneg] at hetaLole2t
      linarith [this, hetaLole2t]
    exact menchoff_edge_finish_h_gen hμpos hxiLole2s hetaTle2t hxiLoclose hetaTclose hζeq hstep hζbound'
  · -- RIGHT edge: ζ.re = z0.re + xiHi
    set etaT : ℝ := ζ.im - z0.im with hetaT_def
    have hetaTmem1 : etaLo ≤ etaT := by simp only [hetaT_def]; linarith [hζRmem.2.2.1]
    have hetaTmem2 : etaT ≤ etaHi := by simp only [hetaT_def]; linarith [hζRmem.2.2.2]
    have hζeq : ζ = z0 + xiHi + etaT * I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hcase]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, hetaT_def]
        ring
    have hetaTne : etaT ≠ 0 := by
      have hetaHineg0 : etaHi < 0 := by
        have h2 : t/(1+μ) < 0 := div_neg_of_neg_of_pos htneg h1μpos
        linarith [hetaHi_hi, h2]
      intro h
      rw [h] at hetaTmem2
      linarith [hetaTmem2, hetaHineg0]
    have hetaTclose : |etaT - t| ≤ |t| *μ := by
      have hlo' : t - etaLo ≤ |t| *μ := by linarith [(abs_le.mp hetaLoclose).1]
      have hhi' : etaHi - t ≤ |t| *μ := (abs_le.mp hetaHiclose).2
      exact menchoff_sandwich_close hetaTmem1 hetaTmem2 hetaLo_hi.le hetaHi_lo hlo' hhi'
    have hetaHineg : etaHi < 0 := by
      have h2 : t/(1+μ) < 0 := div_neg_of_neg_of_pos htneg h1μpos
      linarith [hetaHi_hi, h2]
    have hetaLoneg' : etaLo < 0 := by linarith [hetaLo_hi]
    have hetaTsmall : |etaT| < 1/((N:ℝ)+1) := by
      rcases le_total 0 etaT with h | h
      · rw [abs_of_nonneg h]
        have := abs_of_neg hetaHineg
        linarith [hetaTmem2, hetaHismall, this]
      · rw [abs_of_nonpos h]
        have := abs_of_neg hetaLoneg'
        linarith [hetaTmem1, hetaLosmall, this]
    have hbx : ‖slope (fun u:ℝ => g (z0+u)) 0 xiHi - menchoffFx g z0‖ < μ :=
      (hM2 z0 hz0 xiHi hxiHi_ne0 hxiHismall).1
    have hby : ‖slope (fun u:ℝ => g ((z0+xiHi)+u*I)) 0 etaT - menchoffFy g (z0+xiHi)‖ < μ :=
      (hM2 (z0+xiHi) hxiHiE etaT hetaTne hetaTsmall).2
    have hfy : ‖menchoffFy g (z0+xiHi) - menchoffFy g z0‖ < μ := by
      have hd : dist (z0+(xiHi:ℂ)) z0 < δC2 := by
        rw [dist_eq_norm]
        have heq0 : z0 + (xiHi:ℂ) - z0 = (xiHi:ℂ) := by ring
        rw [heq0, norm_real, Real.norm_eq_abs]
        exact hxiHiD.2
      have := hCfyProp hxiHiE hd
      rwa [dist_eq_norm] at this
    have hstep := menchoff_two_step hxiHi_ne0 hetaTne hbx hby hfy
    rw [← hζeq] at hstep
    have hetaTle2t : |etaT| ≤ 2* |t| := by
      have hetaHile0 : etaHi ≤ 0 := by
        have h2 : t/(1+μ) < 0 := div_neg_of_neg_of_pos htneg h1μpos
        linarith [hetaHi_hi, h2]
      have hetaTneg : etaT ≤ 0 := le_trans hetaTmem2 hetaHile0
      rw [abs_of_nonpos hetaTneg]
      have : -etaT ≤ -etaLo := by linarith [hetaTmem1]
      have hetaLoneg : etaLo ≤ 0 := by linarith [hetaLo_hi]
      rw [abs_of_nonpos hetaLoneg] at hetaLole2t
      linarith [this, hetaLole2t]
    exact menchoff_edge_finish_h_gen hμpos hxiHile2s hetaTle2t hxiHiclose hetaTclose hζeq hstep hζbound'
  · -- BOTTOM edge: ζ.im = z0.im + etaLo
    set xiT : ℝ := ζ.re - z0.re with hxiT_def
    have hxiTmem1 : xiLo ≤ xiT := by simp only [hxiT_def]; linarith [hζRmem.1]
    have hxiTmem2 : xiT ≤ xiHi := by simp only [hxiT_def]; linarith [hζRmem.2.1]
    have hζeq : ζ = z0 + xiT + etaLo * I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hxiT_def]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, hcase]
        ring
    have hxiTne : xiT ≠ 0 := by
      intro h
      have h1 : xiLo ≤ 0 := h ▸ hxiTmem1
      have h2 : 0 ≤ xiHi := h ▸ hxiTmem2
      have hxiLopos : 0 < xiLo := by linarith [hxiLo_lo, div_pos hspos h1μpos]
      linarith [hxiLopos]
    have hxiTclose : |xiT - s| ≤ |s| *μ := by
      have hlo' : s - xiLo ≤ s*μ := by
        have h1 := (abs_le.mp hxiLoclose).1
        rw [abs_of_pos hspos] at h1; linarith
      have hhi' : xiHi - s ≤ s*μ := by
        have h2 := (abs_le.mp hxiHiclose).2
        rwa [abs_of_pos hspos] at h2
      have hkey := menchoff_sandwich_close hxiTmem1 hxiTmem2 hxiLo_hi hxiHi_lo.le hlo' hhi'
      rw [abs_of_pos hspos]; linarith [hkey]
    have hxiTsmall : |xiT| < 1/((N:ℝ)+1) := by
      rcases le_total 0 xiT with h | h
      · rw [abs_of_nonneg h]
        linarith [hxiTmem2, hxiHismall, abs_of_pos (by linarith [hxiHi_lo, hspos] : (0:ℝ) < xiHi)]
      · rw [abs_of_nonpos h]
        have hxiLopos : 0 < xiLo := by linarith [hxiLo_lo, div_pos hspos h1μpos]
        linarith [hxiTmem1, hxiLosmall, abs_of_pos hxiLopos]
    have hby : ‖slope (fun u:ℝ => g (z0+u*I)) 0 etaLo - menchoffFy g z0‖ < μ :=
      (hM2 z0 hz0 etaLo hetaLo_ne0 hetaLosmall).2
    have hbx : ‖slope (fun u:ℝ => g ((z0+etaLo*I)+u)) 0 xiT - menchoffFx g (z0+etaLo*I)‖ < μ :=
      (hM2 (z0+etaLo*I) hetaLoE xiT hxiTne hxiTsmall).1
    have hfx : ‖menchoffFx g (z0+etaLo*I) - menchoffFx g z0‖ < μ := by
      have hd : dist (z0+(etaLo:ℂ)*I) z0 < δC1 := by
        rw [dist_eq_norm]
        have heq0 : z0 + (etaLo:ℂ)*I - z0 = (etaLo:ℂ)*I := by ring
        rw [heq0, norm_mul, norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
        exact hetaLoD.1
      have := hCfxProp hetaLoE hd
      rwa [dist_eq_norm] at this
    have hstep := menchoff_two_step_vh hxiTne hetaLo_ne0 hby hbx hfx
    rw [← hζeq] at hstep
    have hxiTle2s : |xiT| ≤ 2* |s| := by
      have hxiHile0' : xiHi ≤ 2*s := by linarith [hxiHi_hi, hsleμs, hμle1]
      rw [abs_of_pos hspos]
      rcases le_total 0 xiT with h | h
      · rw [abs_of_nonneg h]; linarith [hxiTmem2, hxiHile0']
      · rw [abs_of_nonpos h]
        have hxiLopos : 0 < xiLo := by linarith [hxiLo_lo, div_pos hspos h1μpos]
        linarith [hxiTmem1, hxiLopos]
    exact menchoff_edge_finish_v_gen hμpos hxiTle2s hetaLole2t hxiTclose hetaLoclose hζeq hstep hζbound'
  · -- TOP edge: ζ.im = z0.im + etaHi
    set xiT : ℝ := ζ.re - z0.re with hxiT_def
    have hxiTmem1 : xiLo ≤ xiT := by simp only [hxiT_def]; linarith [hζRmem.1]
    have hxiTmem2 : xiT ≤ xiHi := by simp only [hxiT_def]; linarith [hζRmem.2.1]
    have hζeq : ζ = z0 + xiT + etaHi * I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hxiT_def]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, hcase]
        ring
    have hxiTne : xiT ≠ 0 := by
      intro h
      have h1 : xiLo ≤ 0 := h ▸ hxiTmem1
      have hxiLopos : 0 < xiLo := by linarith [hxiLo_lo, div_pos hspos h1μpos]
      linarith [hxiLopos]
    have hxiTclose : |xiT - s| ≤ |s| *μ := by
      have hlo' : s - xiLo ≤ s*μ := by
        have h1 := (abs_le.mp hxiLoclose).1
        rw [abs_of_pos hspos] at h1; linarith
      have hhi' : xiHi - s ≤ s*μ := by
        have h2 := (abs_le.mp hxiHiclose).2
        rwa [abs_of_pos hspos] at h2
      have hkey := menchoff_sandwich_close hxiTmem1 hxiTmem2 hxiLo_hi hxiHi_lo.le hlo' hhi'
      rw [abs_of_pos hspos]; linarith [hkey]
    have hxiTsmall : |xiT| < 1/((N:ℝ)+1) := by
      rcases le_total 0 xiT with h | h
      · rw [abs_of_nonneg h]
        linarith [hxiTmem2, hxiHismall, abs_of_pos (by linarith [hxiHi_lo, hspos] : (0:ℝ) < xiHi)]
      · rw [abs_of_nonpos h]
        have hxiLopos : 0 < xiLo := by linarith [hxiLo_lo, div_pos hspos h1μpos]
        linarith [hxiTmem1, hxiLosmall, abs_of_pos hxiLopos]
    have hby : ‖slope (fun u:ℝ => g (z0+u*I)) 0 etaHi - menchoffFy g z0‖ < μ :=
      (hM2 z0 hz0 etaHi hetaHi_ne0 hetaHismall).2
    have hbx : ‖slope (fun u:ℝ => g ((z0+etaHi*I)+u)) 0 xiT - menchoffFx g (z0+etaHi*I)‖ < μ :=
      (hM2 (z0+etaHi*I) hetaHiE xiT hxiTne hxiTsmall).1
    have hfx : ‖menchoffFx g (z0+etaHi*I) - menchoffFx g z0‖ < μ := by
      have hd : dist (z0+(etaHi:ℂ)*I) z0 < δC1 := by
        rw [dist_eq_norm]
        have heq0 : z0 + (etaHi:ℂ)*I - z0 = (etaHi:ℂ)*I := by ring
        rw [heq0, norm_mul, norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
        exact hetaHiD.1
      have := hCfxProp hetaHiE hd
      rwa [dist_eq_norm] at this
    have hstep := menchoff_two_step_vh hxiTne hetaHi_ne0 hby hbx hfx
    rw [← hζeq] at hstep
    have hxiTle2s : |xiT| ≤ 2* |s| := by
      have hxiHile0' : xiHi ≤ 2*s := by linarith [hxiHi_hi, hsleμs, hμle1]
      rw [abs_of_pos hspos]
      rcases le_total 0 xiT with h | h
      · rw [abs_of_nonneg h]; linarith [hxiTmem2, hxiHile0']
      · rw [abs_of_nonpos h]
        have hxiLopos : 0 < xiLo := by linarith [hxiLo_lo, div_pos hspos h1μpos]
        linarith [hxiTmem1, hxiLopos]
    exact menchoff_edge_finish_v_gen hμpos hxiTle2s hetaHile2t hxiTclose hetaHiclose hζeq hstep hζbound'

set_option maxHeartbeats 1000000 in
theorem menchoff_M4_quadrant_mp {g : ℂ → ℂ} (hg : Continuous g) {Q : Set ℂ} (hQ : IsOpen Q)
    (hopen : ∀ U ⊆ Q, IsOpen U → IsOpen (g '' U)) {E : Set ℂ} (hEQ : E ⊆ Q)
    {z0 : ℂ} (hz0 : z0 ∈ E) {m N : ℕ}
    (hM2 : ∀ z ∈ E, ∀ s : ℝ, s ≠ 0 → |s| < 1/((N:ℝ)+1) →
      ‖slope (fun t : ℝ => g (z + t)) 0 s - menchoffFx g z‖ < 1/((m:ℝ)+1) ∧
      ‖slope (fun t : ℝ => g (z + t * I)) 0 s - menchoffFy g z‖ < 1/((m:ℝ)+1))
    (hCfx : ContinuousWithinAt (menchoffFx g) E z0)
    (hCfy : ContinuousWithinAt (menchoffFy g) E z0)
    (hDensHL : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ →
      ∃ ξ ∈ Set.Ico (-s) (-(s/(1+ε))), z0 + ξ ∈ E)
    (hDensVR : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      ∃ η ∈ Set.Ioc (t/(1+ε)) t, z0 + η * I ∈ E) :
    ∃ δ > 0, ∀ s t : ℝ, s < 0 → -δ < s → 0 < t → t < δ →
      ‖g (z0 + s + t * I) - g z0 - menchoffFx g z0 * s - menchoffFy g z0 * t‖ ≤
        (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * (1/((m:ℝ)+1)) * (|s| + |t|) := by
  set μ : ℝ := 1/((m:ℝ)+1) with hμ_def
  have hμpos : 0 < μ := by positivity
  obtain ⟨δC1, hδC1, hCfxProp⟩ := Metric.tendsto_nhdsWithin_nhds.mp hCfx μ hμpos
  obtain ⟨δC2, hδC2, hCfyProp⟩ := Metric.tendsto_nhdsWithin_nhds.mp hCfy μ hμpos
  obtain ⟨δHL, hδHL, hHLProp⟩ := hDensHL μ hμpos
  obtain ⟨δVR, hδVR, hVRProp⟩ := hDensVR μ hμpos
  obtain ⟨ρ, hρpos, hballQ⟩ := Metric.isOpen_iff.mp hQ z0 (hEQ hz0)
  set δ0 : ℝ := min (min δC1 δC2) (min δHL δVR) with hδ0_def
  have hδ0pos : 0 < δ0 := lt_min (lt_min hδC1 hδC2) (lt_min hδHL hδVR)
  set δ1 : ℝ := min δ0 (ρ/3) with hδ1_def
  have hδ1pos : 0 < δ1 := lt_min hδ0pos (by positivity)
  set δ : ℝ := min (δ1 / (1+μ)) (1/((N:ℝ)+2) / (1+μ)) with hδ_def
  have hδpos : 0 < δ := by positivity
  refine ⟨δ, hδpos, fun s t hsneg hsδ htpos htδ => ?_⟩
  have hs'0 : 0 < -s := by linarith
  have hs'δ : -s < δ := by linarith
  have h1μpos : (0:ℝ) < 1 + μ := by positivity
  have hδ_le1 : δ ≤ δ1 / (1+μ) := min_le_left _ _
  have hδ_le2 : δ ≤ (1/((N:ℝ)+2)) / (1+μ) := min_le_right _ _
  have hs1μ : (1+μ) * (-s) < δ1 := by
    have hlt : -s < δ1 / (1+μ) := lt_of_lt_of_le hs'δ hδ_le1
    rw [lt_div_iff₀' h1μpos] at hlt; linarith
  have ht1μ : (1+μ) * t < δ1 := by
    have hlt : t < δ1 / (1+μ) := lt_of_lt_of_le htδ hδ_le1
    rw [lt_div_iff₀' h1μpos] at hlt; linarith
  have hsN : (1+μ) * (-s) < 1/((N:ℝ)+2) := by
    have hlt : -s < (1/((N:ℝ)+2)) / (1+μ) := lt_of_lt_of_le hs'δ hδ_le2
    rw [lt_div_iff₀' h1μpos] at hlt; linarith
  have htN : (1+μ) * t < 1/((N:ℝ)+2) := by
    have hlt : t < (1/((N:ℝ)+2)) / (1+μ) := lt_of_lt_of_le htδ hδ_le2
    rw [lt_div_iff₀' h1μpos] at hlt; linarith
  have hδ0ledC1 : δ0 ≤ δC1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ0ledC2 : δ0 ≤ δC2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ0ledHL : δ0 ≤ δHL := (min_le_right _ _).trans (min_le_left _ _)
  have hδ0ledVR : δ0 ≤ δVR := (min_le_right _ _).trans (min_le_right _ _)
  have hδ1leδ0 : δ1 ≤ δ0 := min_le_left _ _
  have hδ1leρ3 : δ1 ≤ ρ/3 := min_le_right _ _
  have hsleμs : (-s) ≤ (1+μ)*(-s) := by nlinarith [hμpos, hs'0]
  have htleμt : t ≤ (1+μ)*t := by nlinarith [hμpos, htpos]
  have hsHL : (-s) < δHL := lt_of_le_of_lt hsleμs (hs1μ.trans_le (hδ1leδ0.trans hδ0ledHL))
  have htVR : t < δVR := lt_of_le_of_lt htleμt (ht1μ.trans_le (hδ1leδ0.trans hδ0ledVR))
  have hμsHL : (1+μ)*(-s) < δHL := hs1μ.trans_le (hδ1leδ0.trans hδ0ledHL)
  have hμtVR : (1+μ)*t < δVR := ht1μ.trans_le (hδ1leδ0.trans hδ0ledVR)
  obtain ⟨xiHi, hxiHimem, hxiHiE⟩ := hHLProp (-s) hs'0 hsHL
  obtain ⟨xiLo, hxiLomem, hxiLoE⟩ := hHLProp ((1+μ)*(-s)) (by positivity) hμsHL
  obtain ⟨etaLo, hetaLomem, hetaLoE⟩ := hVRProp t htpos htVR
  obtain ⟨etaHi, hetaHimem, hetaHiE⟩ := hVRProp ((1+μ)*t) (by positivity) hμtVR
  rw [Set.mem_Ico] at hxiHimem hxiLomem
  rw [Set.mem_Ioc] at hetaLomem hetaHimem
  have hxiHi_lo : s ≤ xiHi := by linarith [hxiHimem.1]
  have hxiHi_hi : xiHi < s/(1+μ) := by
    have heq : -((-s)/(1+μ)) = s/(1+μ) := by ring
    rw [← heq]; exact hxiHimem.2
  have hxiLo_lo : (1+μ)*s ≤ xiLo := by
    have heq : -((1+μ)*(-s)) = (1+μ)*s := by ring
    linarith [hxiLomem.1, heq]
  have hxiLo_hi : xiLo < s := by
    have heq : -((1+μ)*(-s)/(1+μ)) = s := by field_simp
    rw [← heq]; exact hxiLomem.2
  have hcancelt : (1+μ)*t/(1+μ) = t := by field_simp
  have hetaHimem' : t < etaHi ∧ etaHi ≤ (1+μ)*t := by
    refine ⟨?_, hetaHimem.2⟩
    have := hetaHimem.1; rwa [hcancelt] at this
  have hetaLo_lo : t/(1+μ) < etaLo := hetaLomem.1
  have hetaLo_hi : etaLo ≤ t := hetaLomem.2
  have hetaHi_lo : t < etaHi := hetaHimem'.1
  have hetaHi_hi : etaHi ≤ (1+μ)*t := hetaHimem'.2
  have hxiLo_lt_xiHi : xiLo < xiHi := lt_of_lt_of_le hxiLo_hi hxiHi_lo
  have hetaLo_lt_etaHi : etaLo < etaHi := lt_of_le_of_lt hetaLo_hi hetaHi_lo
  have hxiLo_ne0 : xiLo ≠ 0 := by intro h; rw [h] at hxiLo_hi; linarith
  have hxiHi_ne0 : xiHi ≠ 0 := by
    intro h; rw [h] at hxiHi_hi
    have : s/(1+μ) < 0 := div_neg_of_neg_of_pos hsneg h1μpos
    linarith
  have hetaLo_ne0 : etaLo ≠ 0 := by
    intro h; rw [h] at hetaLo_lo
    have : (0:ℝ) < t/(1+μ) := div_pos htpos h1μpos
    linarith
  have hetaHi_ne0 : etaHi ≠ 0 := by intro h; rw [h] at hetaHi_lo; linarith
  set R : Set ℂ := closedRect (z0.re+xiLo) (z0.re+xiHi) (z0.im+etaLo) (z0.im+etaHi) with hR_def
  have hRsub : R ⊆ Q := by
    intro w hw
    simp only [hR_def, closedRect, Set.mem_setOf_eq] at hw
    apply hballQ
    rw [Metric.mem_ball, dist_eq_norm]
    have hre : |w.re - z0.re| ≤ (1+μ)*(-s) := by
      rw [abs_le]
      constructor
      · linarith [hw.1, hxiLo_lo]
      · have h2 : s/(1+μ) < 0 := div_neg_of_neg_of_pos hsneg h1μpos
        linarith [hw.2.1, hxiHi_hi, h2]
    have him : |w.im - z0.im| ≤ (1+μ)*t := by
      rw [abs_le]
      constructor
      · have hpos1 : (0:ℝ) < t/(1+μ) := div_pos htpos h1μpos
        have hpos2 : (0:ℝ) < (1+μ)*t := by positivity
        linarith [hw.2.2.1, hetaLo_lo, hpos1, hpos2]
      · linarith [hw.2.2.2, hetaHi_hi]
    have hbound : ‖w - z0‖ ≤ |w.re - z0.re| + |w.im - z0.im| := by
      have heq : (w - z0).re = w.re - z0.re := by simp
      have heq2 : (w - z0).im = w.im - z0.im := by simp
      calc ‖w - z0‖ ≤ |(w-z0).re| + |(w-z0).im| := Complex.norm_le_abs_re_add_abs_im _
        _ = |w.re - z0.re| + |w.im - z0.im| := by rw [heq, heq2]
    have h1 : (1+μ)*(-s) < ρ/3 := lt_of_lt_of_le hs1μ hδ1leρ3
    have h2 : (1+μ)*t < ρ/3 := lt_of_lt_of_le ht1μ hδ1leρ3
    linarith [hbound, hre, him, h1, h2]
  set w : ℂ := g z0 + menchoffFx g z0 * s + menchoffFy g z0 * t with hw_def
  have hzst_mem : z0 + s + t * I ∈ R := by
    simp only [hR_def, closedRect, Set.mem_setOf_eq]
    have hre : (z0 + (s:ℂ) + (t:ℂ) * I).re = z0.re + s := by simp
    have him : (z0 + (s:ℂ) + (t:ℂ) * I).im = z0.im + t := by simp
    rw [hre, him]
    exact ⟨by linarith [hxiLo_hi], by linarith [hxiHi_lo], by linarith [hetaLo_hi], by linarith [hetaHi_lo]⟩
  have hab' : z0.re + xiLo < z0.re + xiHi := by linarith
  have hcd' : z0.im + etaLo < z0.im + etaHi := by linarith
  obtain ⟨ζ, hζfr, hζbound⟩ := menchoff_max_principle (a := z0.re+xiLo) (b := z0.re+xiHi)
    (c := z0.im+etaLo) (d := z0.im+etaHi) hg.continuousOn hopen hab' hcd' hRsub w hzst_mem
  have hζbound' : ‖g (z0+(s:ℂ)+(t:ℂ)*I) - (g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ))‖
      ≤ ‖g ζ - (g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ))‖ := by
    rw [← hw_def]; exact hζbound
  have hRclosed : IsClosed R := (acl_isCompact_closedRect _ _ _ _).isClosed
  have hζR : ζ ∈ R := by
    have := hζfr.1
    rwa [hRclosed.closure_eq] at this
  have hζRmem : z0.re+xiLo ≤ ζ.re ∧ ζ.re ≤ z0.re+xiHi ∧ z0.im+etaLo ≤ ζ.im ∧ ζ.im ≤ z0.im+etaHi := by
    simpa only [hR_def, closedRect, Set.mem_setOf_eq] using hζR
  have hζcase : ζ.re = z0.re+xiLo ∨ ζ.re = z0.re+xiHi ∨ ζ.im = z0.im+etaLo ∨ ζ.im = z0.im+etaHi := by
    by_contra hcon
    push Not at hcon
    have hζint : ζ ∈ interior R := by
      rw [hR_def, menchoff_interior_closedRect]
      simp only [openRect, Set.mem_setOf_eq]
      exact ⟨lt_of_le_of_ne hζRmem.1 (Ne.symm hcon.1),
        lt_of_le_of_ne hζRmem.2.1 hcon.2.1,
        lt_of_le_of_ne hζRmem.2.2.1 (Ne.symm hcon.2.2.1),
        lt_of_le_of_ne hζRmem.2.2.2 hcon.2.2.2⟩
    exact hζfr.2 hζint
  have hN2 : (1:ℝ)/((N:ℝ)+2) < 1/((N:ℝ)+1) := by
    apply div_lt_div_of_pos_left (by norm_num) (by positivity); linarith
  have hμle1 : μ ≤ 1 := by
    rw [hμ_def, div_le_one₀ (by positivity)]
    have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hxiHismall : |xiHi| < 1/((N:ℝ)+1) := by
    rw [abs_of_neg (by linarith [hxiHi_hi, div_neg_of_neg_of_pos hsneg h1μpos] : xiHi < 0)]
    have : -xiHi ≤ -s := by linarith [hxiHi_lo]
    have h2 : -s ≤ (1+μ)*(-s) := hsleμs
    linarith [this, h2, hsN, hN2]
  have hxiLosmall : |xiLo| < 1/((N:ℝ)+1) := by
    rw [abs_of_neg (by linarith [hxiLo_hi] : xiLo < 0)]
    have : -xiLo ≤ (1+μ)*(-s) := by linarith [hxiLo_lo]
    linarith [this, hsN, hN2]
  have hetaLosmall : |etaLo| < 1/((N:ℝ)+1) := by
    rw [abs_of_pos (by linarith [hetaLo_lo, div_pos htpos h1μpos] : (0:ℝ) < etaLo)]
    linarith [hetaLo_hi, htleμt, htN, hN2]
  have hetaHismall : |etaHi| < 1/((N:ℝ)+1) := by
    rw [abs_of_pos (by linarith [hetaHi_lo, htpos] : (0:ℝ) < etaHi)]
    exact lt_of_le_of_lt hetaHi_hi (htN.trans hN2)
  have hxiHiD : |xiHi| < δC1 ∧ |xiHi| < δC2 := by
    rw [abs_of_neg (by linarith [hxiHi_hi, div_neg_of_neg_of_pos hsneg h1μpos] : xiHi < 0)]
    have h1 : -xiHi ≤ (1+μ)*(-s) := by linarith [hxiHi_lo, hsleμs]
    exact ⟨lt_of_le_of_lt h1 (hs1μ.trans_le (hδ1leδ0.trans hδ0ledC1)),
      lt_of_le_of_lt h1 (hs1μ.trans_le (hδ1leδ0.trans hδ0ledC2))⟩
  have hxiLoD : |xiLo| < δC1 ∧ |xiLo| < δC2 := by
    rw [abs_of_neg (by linarith [hxiLo_hi] : xiLo < 0)]
    have h1 : -xiLo ≤ (1+μ)*(-s) := by linarith [hxiLo_lo]
    exact ⟨lt_of_le_of_lt h1 (hs1μ.trans_le (hδ1leδ0.trans hδ0ledC1)),
      lt_of_le_of_lt h1 (hs1μ.trans_le (hδ1leδ0.trans hδ0ledC2))⟩
  have hetaLoD : |etaLo| < δC1 ∧ |etaLo| < δC2 := by
    rw [abs_of_pos (by linarith [hetaLo_lo, div_pos htpos h1μpos] : (0:ℝ) < etaLo)]
    constructor
    · have := ht1μ.trans_le (hδ1leδ0.trans hδ0ledC1); linarith [hetaLo_hi, htleμt, this]
    · have := ht1μ.trans_le (hδ1leδ0.trans hδ0ledC2); linarith [hetaLo_hi, htleμt, this]
  have hetaHiD : |etaHi| < δC1 ∧ |etaHi| < δC2 := by
    rw [abs_of_pos (by linarith [hetaHi_lo, htpos] : (0:ℝ) < etaHi)]
    exact ⟨lt_of_le_of_lt hetaHi_hi (ht1μ.trans_le (hδ1leδ0.trans hδ0ledC1)),
      lt_of_le_of_lt hetaHi_hi (ht1μ.trans_le (hδ1leδ0.trans hδ0ledC2))⟩
  have hxiHiclose : |xiHi - s| ≤ |s| *μ := by
    have hmem : (-xiHi) ∈ Set.Ioc ((-s)/(1+μ)) (-s) := by
      constructor
      · linarith [hxiHi_hi, div_neg_of_neg_of_pos hsneg h1μpos]
      · linarith [hxiHi_lo]
    have := menchoff_bracket_close_lo hs'0 hμpos hmem
    rw [abs_of_neg hsneg]
    have heq : |(-xiHi) - (-s)| = |xiHi - s| := by rw [← abs_neg]; ring_nf
    linarith [this.le, heq.symm.le, heq.le]
  have hxiLoclose : |xiLo - s| ≤ |s| *μ := by
    have := menchoff_bracket_close_hi hs'0 hμpos
      (show -s < -xiLo by linarith [hxiLo_hi]) (show -xiLo ≤ (1+μ)*(-s) by linarith [hxiLo_lo])
    rw [abs_of_neg hsneg]
    have heq : |(-xiLo) - (-s)| = |xiLo - s| := by rw [← abs_neg]; ring_nf
    linarith [this, heq.symm.le, heq.le]
  have hetaLoclose : |etaLo - t| < t*μ := menchoff_bracket_close_lo htpos hμpos ⟨hetaLo_lo, hetaLo_hi⟩
  have hetaHiclose : |etaHi - t| ≤ |t| *μ := by
    have h := menchoff_bracket_close_hi htpos hμpos hetaHi_lo hetaHi_hi
    rw [abs_of_pos htpos]; exact h
  have hkeys : (1+μ)*s ≥ 2*s := menchoff_mul_le_two_of_le_one hsneg hμle1
  have hxiLole2s : |xiLo| ≤ 2* |s| := by
    rw [abs_of_neg (by linarith [hxiLo_hi] : xiLo < 0), abs_of_neg hsneg]
    linarith [hxiLo_lo, hkeys]
  have hxiHile2s : |xiHi| ≤ 2* |s| := by
    rw [abs_of_neg (by linarith [hxiHi_hi, div_neg_of_neg_of_pos hsneg h1μpos] : xiHi < 0),
      abs_of_neg hsneg]
    linarith [hxiHi_lo, hsneg]
  have hetaLole2t : |etaLo| ≤ 2* |t| := by
    rw [abs_of_pos (by linarith [hetaLo_lo, div_pos htpos h1μpos] : (0:ℝ) < etaLo), abs_of_pos htpos]
    linarith [hetaLo_hi]
  have hkeyt2 : (1+μ)*t ≤ 2*t := menchoff_mul_le_two_of_le_one_pos htpos hμle1
  have hetaHile2t : |etaHi| ≤ 2* |t| := by
    rw [abs_of_pos (by linarith [hetaHi_lo, htpos] : (0:ℝ) < etaHi), abs_of_pos htpos]
    linarith [hetaHi_hi, hkeyt2]
  rcases hζcase with hcase | hcase | hcase | hcase
  · -- LEFT edge: ζ.re = z0.re + xiLo
    set etaT : ℝ := ζ.im - z0.im with hetaT_def
    have hetaTmem1 : etaLo ≤ etaT := by simp only [hetaT_def]; linarith [hζRmem.2.2.1]
    have hetaTmem2 : etaT ≤ etaHi := by simp only [hetaT_def]; linarith [hζRmem.2.2.2]
    have hζeq : ζ = z0 + xiLo + etaT * I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hcase]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, hetaT_def]
        ring
    have hetaTne : etaT ≠ 0 := by
      intro h
      have hetaLopos : 0 < etaLo := by linarith [hetaLo_lo, div_pos htpos h1μpos]
      have h1 : etaLo ≤ 0 := h ▸ hetaTmem1
      linarith [hetaLopos]
    have hetaTclose : |etaT - t| ≤ |t| *μ := by
      have hlo' : t - etaLo ≤ |t| *μ := by
        rw [abs_of_pos htpos]
        linarith [(abs_lt.mp hetaLoclose).1]
      have hhi' : etaHi - t ≤ |t| *μ := (abs_le.mp hetaHiclose).2
      exact menchoff_sandwich_close hetaTmem1 hetaTmem2 hetaLo_hi hetaHi_lo.le hlo' hhi'
    have hetaTsmall : |etaT| < 1/((N:ℝ)+1) := by
      rcases le_total 0 etaT with h | h
      · rw [abs_of_nonneg h]
        linarith [hetaTmem2, hetaHismall, abs_of_pos (by linarith [hetaHi_lo, htpos] : (0:ℝ) < etaHi)]
      · rw [abs_of_nonpos h]
        have hetaLopos : 0 < etaLo := by linarith [hetaLo_lo, div_pos htpos h1μpos]
        linarith [hetaTmem1, hetaLosmall, abs_of_pos hetaLopos]
    have hbx : ‖slope (fun u:ℝ => g (z0+u)) 0 xiLo - menchoffFx g z0‖ < μ :=
      (hM2 z0 hz0 xiLo hxiLo_ne0 hxiLosmall).1
    have hby : ‖slope (fun u:ℝ => g ((z0+xiLo)+u*I)) 0 etaT - menchoffFy g (z0+xiLo)‖ < μ :=
      (hM2 (z0+xiLo) hxiLoE etaT hetaTne hetaTsmall).2
    have hfy : ‖menchoffFy g (z0+xiLo) - menchoffFy g z0‖ < μ := by
      have hd : dist (z0+(xiLo:ℂ)) z0 < δC2 := by
        rw [dist_eq_norm]
        have heq0 : z0 + (xiLo:ℂ) - z0 = (xiLo:ℂ) := by ring
        rw [heq0, norm_real, Real.norm_eq_abs]
        exact hxiLoD.2
      have := hCfyProp hxiLoE hd
      rwa [dist_eq_norm] at this
    have hstep := menchoff_two_step hxiLo_ne0 hetaTne hbx hby hfy
    rw [← hζeq] at hstep
    have hetaTle2t : |etaT| ≤ 2* |t| := by
      have hetaHile0' : etaHi ≤ 2*t := by linarith [hetaHi_hi, hkeyt2]
      rw [abs_of_pos htpos]
      rcases le_total 0 etaT with h | h
      · rw [abs_of_nonneg h]; linarith [hetaTmem2, hetaHile0']
      · rw [abs_of_nonpos h]
        have hetaLopos : 0 < etaLo := by linarith [hetaLo_lo, div_pos htpos h1μpos]
        linarith [hetaTmem1, hetaLopos]
    exact menchoff_edge_finish_h_gen hμpos hxiLole2s hetaTle2t hxiLoclose hetaTclose hζeq hstep hζbound'
  · -- RIGHT edge: ζ.re = z0.re + xiHi
    set etaT : ℝ := ζ.im - z0.im with hetaT_def
    have hetaTmem1 : etaLo ≤ etaT := by simp only [hetaT_def]; linarith [hζRmem.2.2.1]
    have hetaTmem2 : etaT ≤ etaHi := by simp only [hetaT_def]; linarith [hζRmem.2.2.2]
    have hζeq : ζ = z0 + xiHi + etaT * I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hcase]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, hetaT_def]
        ring
    have hetaTne : etaT ≠ 0 := by
      intro h
      have hetaLopos : 0 < etaLo := by linarith [hetaLo_lo, div_pos htpos h1μpos]
      have h1 : etaLo ≤ 0 := h ▸ hetaTmem1
      linarith [hetaLopos]
    have hetaTclose : |etaT - t| ≤ |t| *μ := by
      have hlo' : t - etaLo ≤ |t| *μ := by
        rw [abs_of_pos htpos]
        linarith [(abs_lt.mp hetaLoclose).1]
      have hhi' : etaHi - t ≤ |t| *μ := (abs_le.mp hetaHiclose).2
      exact menchoff_sandwich_close hetaTmem1 hetaTmem2 hetaLo_hi hetaHi_lo.le hlo' hhi'
    have hetaTsmall : |etaT| < 1/((N:ℝ)+1) := by
      rcases le_total 0 etaT with h | h
      · rw [abs_of_nonneg h]
        linarith [hetaTmem2, hetaHismall, abs_of_pos (by linarith [hetaHi_lo, htpos] : (0:ℝ) < etaHi)]
      · rw [abs_of_nonpos h]
        have hetaLopos : 0 < etaLo := by linarith [hetaLo_lo, div_pos htpos h1μpos]
        linarith [hetaTmem1, hetaLosmall, abs_of_pos hetaLopos]
    have hbx : ‖slope (fun u:ℝ => g (z0+u)) 0 xiHi - menchoffFx g z0‖ < μ :=
      (hM2 z0 hz0 xiHi hxiHi_ne0 hxiHismall).1
    have hby : ‖slope (fun u:ℝ => g ((z0+xiHi)+u*I)) 0 etaT - menchoffFy g (z0+xiHi)‖ < μ :=
      (hM2 (z0+xiHi) hxiHiE etaT hetaTne hetaTsmall).2
    have hfy : ‖menchoffFy g (z0+xiHi) - menchoffFy g z0‖ < μ := by
      have hd : dist (z0+(xiHi:ℂ)) z0 < δC2 := by
        rw [dist_eq_norm]
        have heq0 : z0 + (xiHi:ℂ) - z0 = (xiHi:ℂ) := by ring
        rw [heq0, norm_real, Real.norm_eq_abs]
        exact hxiHiD.2
      have := hCfyProp hxiHiE hd
      rwa [dist_eq_norm] at this
    have hstep := menchoff_two_step hxiHi_ne0 hetaTne hbx hby hfy
    rw [← hζeq] at hstep
    have hetaTle2t : |etaT| ≤ 2* |t| := by
      have hetaHile0' : etaHi ≤ 2*t := by linarith [hetaHi_hi, hkeyt2]
      rw [abs_of_pos htpos]
      rcases le_total 0 etaT with h | h
      · rw [abs_of_nonneg h]; linarith [hetaTmem2, hetaHile0']
      · rw [abs_of_nonpos h]
        have hetaLopos : 0 < etaLo := by linarith [hetaLo_lo, div_pos htpos h1μpos]
        linarith [hetaTmem1, hetaLopos]
    exact menchoff_edge_finish_h_gen hμpos hxiHile2s hetaTle2t hxiHiclose hetaTclose hζeq hstep hζbound'
  · -- BOTTOM edge: ζ.im = z0.im + etaLo
    set xiT : ℝ := ζ.re - z0.re with hxiT_def
    have hxiTmem1 : xiLo ≤ xiT := by simp only [hxiT_def]; linarith [hζRmem.1]
    have hxiTmem2 : xiT ≤ xiHi := by simp only [hxiT_def]; linarith [hζRmem.2.1]
    have hζeq : ζ = z0 + xiT + etaLo * I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hxiT_def]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, hcase]
        ring
    have hxiTne : xiT ≠ 0 := by
      intro h
      have h2 : 0 ≤ xiHi := h ▸ hxiTmem2
      have h3 : s/(1+μ) < 0 := div_neg_of_neg_of_pos hsneg h1μpos
      linarith [hxiHi_hi, h3]
    have hxiTclose : |xiT - s| ≤ |s| *μ := by
      have hlo' : s - xiLo ≤ |s| *μ := by
        have h1 := (abs_le.mp hxiLoclose).1
        rw [abs_of_neg hsneg] at h1 ⊢; linarith
      have hhi' : xiHi - s ≤ |s| *μ := (abs_le.mp hxiHiclose).2
      exact menchoff_sandwich_close hxiTmem1 hxiTmem2 hxiLo_hi.le hxiHi_lo hlo' hhi'
    have hxiHineg2 : xiHi < 0 := by
      have h2 : s/(1+μ) < 0 := div_neg_of_neg_of_pos hsneg h1μpos
      linarith [hxiHi_hi, h2]
    have hxiLoneg2 : xiLo < 0 := by linarith [hxiLo_hi]
    have hxiTsmall : |xiT| < 1/((N:ℝ)+1) := by
      rcases le_total 0 xiT with h | h
      · rw [abs_of_nonneg h]
        linarith [hxiTmem2, hxiHismall, abs_of_neg hxiHineg2]
      · rw [abs_of_nonpos h]
        linarith [hxiTmem1, hxiLosmall, abs_of_neg hxiLoneg2]
    have hby : ‖slope (fun u:ℝ => g (z0+u*I)) 0 etaLo - menchoffFy g z0‖ < μ :=
      (hM2 z0 hz0 etaLo hetaLo_ne0 hetaLosmall).2
    have hbx : ‖slope (fun u:ℝ => g ((z0+etaLo*I)+u)) 0 xiT - menchoffFx g (z0+etaLo*I)‖ < μ :=
      (hM2 (z0+etaLo*I) hetaLoE xiT hxiTne hxiTsmall).1
    have hfx : ‖menchoffFx g (z0+etaLo*I) - menchoffFx g z0‖ < μ := by
      have hd : dist (z0+(etaLo:ℂ)*I) z0 < δC1 := by
        rw [dist_eq_norm]
        have heq0 : z0 + (etaLo:ℂ)*I - z0 = (etaLo:ℂ)*I := by ring
        rw [heq0, norm_mul, norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
        exact hetaLoD.1
      have := hCfxProp hetaLoE hd
      rwa [dist_eq_norm] at this
    have hstep := menchoff_two_step_vh hxiTne hetaLo_ne0 hby hbx hfx
    rw [← hζeq] at hstep
    have hxiTle2s : |xiT| ≤ 2* |s| := by
      have hxiHineg : xiHi < 0 := by
        have h2 : s/(1+μ) < 0 := div_neg_of_neg_of_pos hsneg h1μpos
        linarith [hxiHi_hi, h2]
      have hxiTneg : xiT ≤ 0 := le_trans hxiTmem2 hxiHineg.le
      rw [abs_of_nonpos hxiTneg, abs_of_neg hsneg]
      have : -xiT ≤ -xiLo := by linarith [hxiTmem1]
      have hxiLoneg : xiLo ≤ 0 := by linarith [hxiLo_hi]
      have hxiLole2s' := hxiLole2s
      rw [abs_of_neg hsneg] at hxiLole2s'
      linarith [this, hxiLole2s']
    have hetaLoclose' : |etaLo - t| ≤ |t| * μ := by rw [abs_of_pos htpos]; exact hetaLoclose.le
    exact menchoff_edge_finish_v_gen hμpos hxiTle2s hetaLole2t hxiTclose hetaLoclose' hζeq hstep hζbound'
  · -- TOP edge: ζ.im = z0.im + etaHi
    set xiT : ℝ := ζ.re - z0.re with hxiT_def
    have hxiTmem1 : xiLo ≤ xiT := by simp only [hxiT_def]; linarith [hζRmem.1]
    have hxiTmem2 : xiT ≤ xiHi := by simp only [hxiT_def]; linarith [hζRmem.2.1]
    have hζeq : ζ = z0 + xiT + etaHi * I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hxiT_def]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, hcase]
        ring
    have hxiTne : xiT ≠ 0 := by
      intro h
      have h2 : 0 ≤ xiHi := h ▸ hxiTmem2
      have h3 : s/(1+μ) < 0 := div_neg_of_neg_of_pos hsneg h1μpos
      linarith [hxiHi_hi, h3]
    have hxiTclose : |xiT - s| ≤ |s| *μ := by
      have hlo' : s - xiLo ≤ |s| *μ := by
        have h1 := (abs_le.mp hxiLoclose).1
        rw [abs_of_neg hsneg] at h1 ⊢; linarith
      have hhi' : xiHi - s ≤ |s| *μ := (abs_le.mp hxiHiclose).2
      exact menchoff_sandwich_close hxiTmem1 hxiTmem2 hxiLo_hi.le hxiHi_lo hlo' hhi'
    have hxiHineg2 : xiHi < 0 := by
      have h2 : s/(1+μ) < 0 := div_neg_of_neg_of_pos hsneg h1μpos
      linarith [hxiHi_hi, h2]
    have hxiLoneg2 : xiLo < 0 := by linarith [hxiLo_hi]
    have hxiTsmall : |xiT| < 1/((N:ℝ)+1) := by
      rcases le_total 0 xiT with h | h
      · rw [abs_of_nonneg h]
        linarith [hxiTmem2, hxiHismall, abs_of_neg hxiHineg2]
      · rw [abs_of_nonpos h]
        linarith [hxiTmem1, hxiLosmall, abs_of_neg hxiLoneg2]
    have hby : ‖slope (fun u:ℝ => g (z0+u*I)) 0 etaHi - menchoffFy g z0‖ < μ :=
      (hM2 z0 hz0 etaHi hetaHi_ne0 hetaHismall).2
    have hbx : ‖slope (fun u:ℝ => g ((z0+etaHi*I)+u)) 0 xiT - menchoffFx g (z0+etaHi*I)‖ < μ :=
      (hM2 (z0+etaHi*I) hetaHiE xiT hxiTne hxiTsmall).1
    have hfx : ‖menchoffFx g (z0+etaHi*I) - menchoffFx g z0‖ < μ := by
      have hd : dist (z0+(etaHi:ℂ)*I) z0 < δC1 := by
        rw [dist_eq_norm]
        have heq0 : z0 + (etaHi:ℂ)*I - z0 = (etaHi:ℂ)*I := by ring
        rw [heq0, norm_mul, norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
        exact hetaHiD.1
      have := hCfxProp hetaHiE hd
      rwa [dist_eq_norm] at this
    have hstep := menchoff_two_step_vh hxiTne hetaHi_ne0 hby hbx hfx
    rw [← hζeq] at hstep
    have hxiTle2s : |xiT| ≤ 2* |s| := by
      have hxiHineg : xiHi < 0 := by
        have h2 : s/(1+μ) < 0 := div_neg_of_neg_of_pos hsneg h1μpos
        linarith [hxiHi_hi, h2]
      have hxiTneg : xiT ≤ 0 := le_trans hxiTmem2 hxiHineg.le
      rw [abs_of_nonpos hxiTneg, abs_of_neg hsneg]
      have : -xiT ≤ -xiLo := by linarith [hxiTmem1]
      have hxiLoneg : xiLo ≤ 0 := by linarith [hxiLo_hi]
      have hxiLole2s' := hxiLole2s
      rw [abs_of_neg hsneg] at hxiLole2s'
      linarith [this, hxiLole2s']
    exact menchoff_edge_finish_v_gen hμpos hxiTle2s hetaHile2t hxiTclose hetaHiclose hζeq hstep hζbound'

set_option maxHeartbeats 1000000 in
theorem menchoff_M4_quadrant_mm {g : ℂ → ℂ} (hg : Continuous g) {Q : Set ℂ} (hQ : IsOpen Q)
    (hopen : ∀ U ⊆ Q, IsOpen U → IsOpen (g '' U)) {E : Set ℂ} (hEQ : E ⊆ Q)
    {z0 : ℂ} (hz0 : z0 ∈ E) {m N : ℕ}
    (hM2 : ∀ z ∈ E, ∀ s : ℝ, s ≠ 0 → |s| < 1/((N:ℝ)+1) →
      ‖slope (fun t : ℝ => g (z + t)) 0 s - menchoffFx g z‖ < 1/((m:ℝ)+1) ∧
      ‖slope (fun t : ℝ => g (z + t * I)) 0 s - menchoffFy g z‖ < 1/((m:ℝ)+1))
    (hCfx : ContinuousWithinAt (menchoffFx g) E z0)
    (hCfy : ContinuousWithinAt (menchoffFy g) E z0)
    (hDensHL : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ →
      ∃ ξ ∈ Set.Ico (-s) (-(s/(1+ε))), z0 + ξ ∈ E)
    (hDensVL : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      ∃ η ∈ Set.Ico (-t) (-(t/(1+ε))), z0 + η * I ∈ E) :
    ∃ δ > 0, ∀ s t : ℝ, s < 0 → -δ < s → t < 0 → -δ < t →
      ‖g (z0 + s + t * I) - g z0 - menchoffFx g z0 * s - menchoffFy g z0 * t‖ ≤
        (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * (1/((m:ℝ)+1)) * (|s| + |t|) := by
  set μ : ℝ := 1/((m:ℝ)+1) with hμ_def
  have hμpos : 0 < μ := by positivity
  obtain ⟨δC1, hδC1, hCfxProp⟩ := Metric.tendsto_nhdsWithin_nhds.mp hCfx μ hμpos
  obtain ⟨δC2, hδC2, hCfyProp⟩ := Metric.tendsto_nhdsWithin_nhds.mp hCfy μ hμpos
  obtain ⟨δHL, hδHL, hHLProp⟩ := hDensHL μ hμpos
  obtain ⟨δVL, hδVL, hVLProp⟩ := hDensVL μ hμpos
  obtain ⟨ρ, hρpos, hballQ⟩ := Metric.isOpen_iff.mp hQ z0 (hEQ hz0)
  set δ0 : ℝ := min (min δC1 δC2) (min δHL δVL) with hδ0_def
  have hδ0pos : 0 < δ0 := lt_min (lt_min hδC1 hδC2) (lt_min hδHL hδVL)
  set δ1 : ℝ := min δ0 (ρ/3) with hδ1_def
  have hδ1pos : 0 < δ1 := lt_min hδ0pos (by positivity)
  set δ : ℝ := min (δ1 / (1+μ)) (1/((N:ℝ)+2) / (1+μ)) with hδ_def
  have hδpos : 0 < δ := by positivity
  refine ⟨δ, hδpos, fun s t hsneg hsδ htneg htδ => ?_⟩
  have hs'0 : 0 < -s := by linarith
  have ht'0 : 0 < -t := by linarith
  have hs'δ : -s < δ := by linarith
  have ht'δ : -t < δ := by linarith
  have h1μpos : (0:ℝ) < 1 + μ := by positivity
  have hδ_le1 : δ ≤ δ1 / (1+μ) := min_le_left _ _
  have hδ_le2 : δ ≤ (1/((N:ℝ)+2)) / (1+μ) := min_le_right _ _
  have hs1μ : (1+μ) * (-s) < δ1 := by
    have hlt : -s < δ1 / (1+μ) := lt_of_lt_of_le hs'δ hδ_le1
    rw [lt_div_iff₀' h1μpos] at hlt; linarith
  have ht1μ : (1+μ) * (-t) < δ1 := by
    have hlt : -t < δ1 / (1+μ) := lt_of_lt_of_le ht'δ hδ_le1
    rw [lt_div_iff₀' h1μpos] at hlt; linarith
  have hsN : (1+μ) * (-s) < 1/((N:ℝ)+2) := by
    have hlt : -s < (1/((N:ℝ)+2)) / (1+μ) := lt_of_lt_of_le hs'δ hδ_le2
    rw [lt_div_iff₀' h1μpos] at hlt; linarith
  have htN : (1+μ) * (-t) < 1/((N:ℝ)+2) := by
    have hlt : -t < (1/((N:ℝ)+2)) / (1+μ) := lt_of_lt_of_le ht'δ hδ_le2
    rw [lt_div_iff₀' h1μpos] at hlt; linarith
  have hδ0ledC1 : δ0 ≤ δC1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ0ledC2 : δ0 ≤ δC2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ0ledHL : δ0 ≤ δHL := (min_le_right _ _).trans (min_le_left _ _)
  have hδ0ledVL : δ0 ≤ δVL := (min_le_right _ _).trans (min_le_right _ _)
  have hδ1leδ0 : δ1 ≤ δ0 := min_le_left _ _
  have hδ1leρ3 : δ1 ≤ ρ/3 := min_le_right _ _
  have hsleμs : (-s) ≤ (1+μ)*(-s) := by nlinarith [hμpos, hs'0]
  have htleμt : (-t) ≤ (1+μ)*(-t) := by nlinarith [hμpos, ht'0]
  have hsHL : (-s) < δHL := lt_of_le_of_lt hsleμs (hs1μ.trans_le (hδ1leδ0.trans hδ0ledHL))
  have htVL : (-t) < δVL := lt_of_le_of_lt htleμt (ht1μ.trans_le (hδ1leδ0.trans hδ0ledVL))
  have hμsHL : (1+μ)*(-s) < δHL := hs1μ.trans_le (hδ1leδ0.trans hδ0ledHL)
  have hμtVL : (1+μ)*(-t) < δVL := ht1μ.trans_le (hδ1leδ0.trans hδ0ledVL)
  obtain ⟨xiHi, hxiHimem, hxiHiE⟩ := hHLProp (-s) hs'0 hsHL
  obtain ⟨xiLo, hxiLomem, hxiLoE⟩ := hHLProp ((1+μ)*(-s)) (by positivity) hμsHL
  obtain ⟨etaHi, hetaHimem, hetaHiE⟩ := hVLProp (-t) ht'0 htVL
  obtain ⟨etaLo, hetaLomem, hetaLoE⟩ := hVLProp ((1+μ)*(-t)) (by positivity) hμtVL
  rw [Set.mem_Ico] at hxiHimem hxiLomem hetaHimem hetaLomem
  have hxiHi_lo : s ≤ xiHi := by linarith [hxiHimem.1]
  have hxiHi_hi : xiHi < s/(1+μ) := by
    have heq : -((-s)/(1+μ)) = s/(1+μ) := by ring
    rw [← heq]; exact hxiHimem.2
  have hxiLo_lo : (1+μ)*s ≤ xiLo := by
    have heq : -((1+μ)*(-s)) = (1+μ)*s := by ring
    linarith [hxiLomem.1, heq]
  have hxiLo_hi : xiLo < s := by
    have heq : -((1+μ)*(-s)/(1+μ)) = s := by field_simp
    rw [← heq]; exact hxiLomem.2
  have hetaHi_lo : t ≤ etaHi := by linarith [hetaHimem.1]
  have hetaHi_hi : etaHi < t/(1+μ) := by
    have heq : -((-t)/(1+μ)) = t/(1+μ) := by ring
    rw [← heq]; exact hetaHimem.2
  have hetaLo_lo : (1+μ)*t ≤ etaLo := by
    have heq : -((1+μ)*(-t)) = (1+μ)*t := by ring
    linarith [hetaLomem.1, heq]
  have hetaLo_hi : etaLo < t := by
    have heq : -((1+μ)*(-t)/(1+μ)) = t := by field_simp
    rw [← heq]; exact hetaLomem.2
  have hxiLo_lt_xiHi : xiLo < xiHi := lt_of_lt_of_le hxiLo_hi hxiHi_lo
  have hetaLo_lt_etaHi : etaLo < etaHi := lt_of_lt_of_le hetaLo_hi hetaHi_lo
  have hxiLo_ne0 : xiLo ≠ 0 := by intro h; rw [h] at hxiLo_hi; linarith
  have hxiHi_ne0 : xiHi ≠ 0 := by
    intro h; rw [h] at hxiHi_hi
    have : s/(1+μ) < 0 := div_neg_of_neg_of_pos hsneg h1μpos
    linarith
  have hetaLo_ne0 : etaLo ≠ 0 := by intro h; rw [h] at hetaLo_hi; linarith
  have hetaHi_ne0 : etaHi ≠ 0 := by
    intro h; rw [h] at hetaHi_hi
    have : t/(1+μ) < 0 := div_neg_of_neg_of_pos htneg h1μpos
    linarith
  set R : Set ℂ := closedRect (z0.re+xiLo) (z0.re+xiHi) (z0.im+etaLo) (z0.im+etaHi) with hR_def
  have hRsub : R ⊆ Q := by
    intro w hw
    simp only [hR_def, closedRect, Set.mem_setOf_eq] at hw
    apply hballQ
    rw [Metric.mem_ball, dist_eq_norm]
    have hre : |w.re - z0.re| ≤ (1+μ)*(-s) := by
      rw [abs_le]
      constructor
      · linarith [hw.1, hxiLo_lo]
      · have h2 : s/(1+μ) < 0 := div_neg_of_neg_of_pos hsneg (by positivity)
        linarith [hw.2.1, hxiHi_hi, h2]
    have him : |w.im - z0.im| ≤ (1+μ)*(-t) := by
      rw [abs_le]
      constructor
      · linarith [hw.2.2.1, hetaLo_lo]
      · have h2 : t/(1+μ) < 0 := div_neg_of_neg_of_pos htneg (by positivity)
        linarith [hw.2.2.2, hetaHi_hi, h2]
    have hbound : ‖w - z0‖ ≤ |w.re - z0.re| + |w.im - z0.im| := by
      have heq : (w - z0).re = w.re - z0.re := by simp
      have heq2 : (w - z0).im = w.im - z0.im := by simp
      calc ‖w - z0‖ ≤ |(w-z0).re| + |(w-z0).im| := Complex.norm_le_abs_re_add_abs_im _
        _ = |w.re - z0.re| + |w.im - z0.im| := by rw [heq, heq2]
    have h1 : (1+μ)*(-s) < ρ/3 := lt_of_lt_of_le hs1μ hδ1leρ3
    have h2 : (1+μ)*(-t) < ρ/3 := lt_of_lt_of_le ht1μ hδ1leρ3
    linarith [hbound, hre, him, h1, h2]
  set w : ℂ := g z0 + menchoffFx g z0 * s + menchoffFy g z0 * t with hw_def
  have hzst_mem : z0 + s + t * I ∈ R := by
    simp only [hR_def, closedRect, Set.mem_setOf_eq]
    have hre : (z0 + (s:ℂ) + (t:ℂ) * I).re = z0.re + s := by simp
    have him : (z0 + (s:ℂ) + (t:ℂ) * I).im = z0.im + t := by simp
    rw [hre, him]
    exact ⟨by linarith [hxiLo_hi], by linarith [hxiHi_lo], by linarith [hetaLo_hi], by linarith [hetaHi_lo]⟩
  have hab' : z0.re + xiLo < z0.re + xiHi := by linarith
  have hcd' : z0.im + etaLo < z0.im + etaHi := by linarith
  obtain ⟨ζ, hζfr, hζbound⟩ := menchoff_max_principle (a := z0.re+xiLo) (b := z0.re+xiHi)
    (c := z0.im+etaLo) (d := z0.im+etaHi) hg.continuousOn hopen hab' hcd' hRsub w hzst_mem
  have hζbound' : ‖g (z0+(s:ℂ)+(t:ℂ)*I) - (g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ))‖
      ≤ ‖g ζ - (g z0 + menchoffFx g z0 * (s:ℂ) + menchoffFy g z0 * (t:ℂ))‖ := by
    rw [← hw_def]; exact hζbound
  have hRclosed : IsClosed R := (acl_isCompact_closedRect _ _ _ _).isClosed
  have hζR : ζ ∈ R := by
    have := hζfr.1
    rwa [hRclosed.closure_eq] at this
  have hζRmem : z0.re+xiLo ≤ ζ.re ∧ ζ.re ≤ z0.re+xiHi ∧ z0.im+etaLo ≤ ζ.im ∧ ζ.im ≤ z0.im+etaHi := by
    simpa only [hR_def, closedRect, Set.mem_setOf_eq] using hζR
  have hζcase : ζ.re = z0.re+xiLo ∨ ζ.re = z0.re+xiHi ∨ ζ.im = z0.im+etaLo ∨ ζ.im = z0.im+etaHi := by
    by_contra hcon
    push Not at hcon
    have hζint : ζ ∈ interior R := by
      rw [hR_def, menchoff_interior_closedRect]
      simp only [openRect, Set.mem_setOf_eq]
      exact ⟨lt_of_le_of_ne hζRmem.1 (Ne.symm hcon.1),
        lt_of_le_of_ne hζRmem.2.1 hcon.2.1,
        lt_of_le_of_ne hζRmem.2.2.1 (Ne.symm hcon.2.2.1),
        lt_of_le_of_ne hζRmem.2.2.2 hcon.2.2.2⟩
    exact hζfr.2 hζint
  have hN2 : (1:ℝ)/((N:ℝ)+2) < 1/((N:ℝ)+1) := by
    apply div_lt_div_of_pos_left (by norm_num) (by positivity); linarith
  have hμle1 : μ ≤ 1 := by
    rw [hμ_def, div_le_one₀ (by positivity)]
    have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hxiLosmall : |xiLo| < 1/((N:ℝ)+1) := by
    rw [abs_of_neg (by linarith [hxiLo_hi] : xiLo < 0)]
    have : -xiLo ≤ (1+μ)*(-s) := by linarith [hxiLo_lo]
    linarith [this, hsN, hN2]
  have hxiHismall : |xiHi| < 1/((N:ℝ)+1) := by
    rw [abs_of_neg (by linarith [hxiHi_hi, div_neg_of_neg_of_pos hsneg h1μpos] : xiHi < 0)]
    have : -xiHi ≤ -s := by linarith [hxiHi_lo]
    have h2 : -s ≤ (1+μ)*(-s) := hsleμs
    linarith [this, h2, hsN, hN2]
  have hetaLosmall : |etaLo| < 1/((N:ℝ)+1) := by
    rw [abs_of_neg (by linarith [hetaLo_hi] : etaLo < 0)]
    have : -etaLo ≤ (1+μ)*(-t) := by linarith [hetaLo_lo]
    linarith [this, htN, hN2]
  have hetaHismall : |etaHi| < 1/((N:ℝ)+1) := by
    rw [abs_of_neg (by linarith [hetaHi_hi, div_neg_of_neg_of_pos htneg h1μpos] : etaHi < 0)]
    have : -etaHi ≤ -t := by linarith [hetaHi_lo]
    have h2 : -t ≤ (1+μ)*(-t) := htleμt
    linarith [this, h2, htN, hN2]
  have hxiLoD : |xiLo| < δC1 ∧ |xiLo| < δC2 := by
    rw [abs_of_neg (by linarith [hxiLo_hi] : xiLo < 0)]
    have h1 : -xiLo ≤ (1+μ)*(-s) := by linarith [hxiLo_lo]
    exact ⟨lt_of_le_of_lt h1 (hs1μ.trans_le (hδ1leδ0.trans hδ0ledC1)),
      lt_of_le_of_lt h1 (hs1μ.trans_le (hδ1leδ0.trans hδ0ledC2))⟩
  have hxiHiD : |xiHi| < δC1 ∧ |xiHi| < δC2 := by
    rw [abs_of_neg (by linarith [hxiHi_hi, div_neg_of_neg_of_pos hsneg h1μpos] : xiHi < 0)]
    have h1 : -xiHi ≤ (1+μ)*(-s) := by linarith [hxiHi_lo, hsleμs]
    exact ⟨lt_of_le_of_lt h1 (hs1μ.trans_le (hδ1leδ0.trans hδ0ledC1)),
      lt_of_le_of_lt h1 (hs1μ.trans_le (hδ1leδ0.trans hδ0ledC2))⟩
  have hetaLoD : |etaLo| < δC1 ∧ |etaLo| < δC2 := by
    rw [abs_of_neg (by linarith [hetaLo_hi] : etaLo < 0)]
    have h1 : -etaLo ≤ (1+μ)*(-t) := by linarith [hetaLo_lo]
    exact ⟨lt_of_le_of_lt h1 (ht1μ.trans_le (hδ1leδ0.trans hδ0ledC1)),
      lt_of_le_of_lt h1 (ht1μ.trans_le (hδ1leδ0.trans hδ0ledC2))⟩
  have hetaHiD : |etaHi| < δC1 ∧ |etaHi| < δC2 := by
    rw [abs_of_neg (by linarith [hetaHi_hi, div_neg_of_neg_of_pos htneg h1μpos] : etaHi < 0)]
    have h1 : -etaHi ≤ (1+μ)*(-t) := by linarith [hetaHi_lo, htleμt]
    exact ⟨lt_of_le_of_lt h1 (ht1μ.trans_le (hδ1leδ0.trans hδ0ledC1)),
      lt_of_le_of_lt h1 (ht1μ.trans_le (hδ1leδ0.trans hδ0ledC2))⟩
  have hxiLoclose : |xiLo - s| ≤ |s| *μ := by
    have := menchoff_bracket_close_hi hs'0 hμpos
      (show -s < -xiLo by linarith [hxiLo_hi]) (show -xiLo ≤ (1+μ)*(-s) by linarith [hxiLo_lo])
    rw [abs_of_neg hsneg]
    have heq : |(-xiLo) - (-s)| = |xiLo - s| := by rw [← abs_neg]; ring_nf
    linarith [this, heq.symm.le, heq.le]
  have hxiHiclose : |xiHi - s| ≤ |s| *μ := by
    have hmem : (-xiHi) ∈ Set.Ioc ((-s)/(1+μ)) (-s) := by
      constructor
      · linarith [hxiHi_hi, div_neg_of_neg_of_pos hsneg h1μpos]
      · linarith [hxiHi_lo]
    have := menchoff_bracket_close_lo hs'0 hμpos hmem
    rw [abs_of_neg hsneg]
    have heq : |(-xiHi) - (-s)| = |xiHi - s| := by rw [← abs_neg]; ring_nf
    linarith [this.le, heq.symm.le, heq.le]
  have hetaLoclose : |etaLo - t| ≤ |t| *μ := by
    have := menchoff_bracket_close_hi ht'0 hμpos
      (show -t < -etaLo by linarith [hetaLo_hi]) (show -etaLo ≤ (1+μ)*(-t) by linarith [hetaLo_lo])
    rw [abs_of_neg htneg]
    have heq : |(-etaLo) - (-t)| = |etaLo - t| := by rw [← abs_neg]; ring_nf
    linarith [this, heq.symm.le, heq.le]
  have hetaHiclose : |etaHi - t| ≤ |t| *μ := by
    have hmem : (-etaHi) ∈ Set.Ioc ((-t)/(1+μ)) (-t) := by
      constructor
      · linarith [hetaHi_hi, div_neg_of_neg_of_pos htneg h1μpos]
      · linarith [hetaHi_lo]
    have := menchoff_bracket_close_lo ht'0 hμpos hmem
    rw [abs_of_neg htneg]
    have heq : |(-etaHi) - (-t)| = |etaHi - t| := by rw [← abs_neg]; ring_nf
    linarith [this.le, heq.symm.le, heq.le]
  have hkeys : (1+μ)*s ≥ 2*s := menchoff_mul_le_two_of_le_one hsneg hμle1
  have hkeyt : (1+μ)*t ≥ 2*t := menchoff_mul_le_two_of_le_one htneg hμle1
  have hxiLole2s : |xiLo| ≤ 2* |s| := by
    rw [abs_of_neg (by linarith [hxiLo_hi] : xiLo < 0), abs_of_neg hsneg]
    linarith [hxiLo_lo, hkeys]
  have hxiHile2s : |xiHi| ≤ 2* |s| := by
    rw [abs_of_neg (by linarith [hxiHi_hi, div_neg_of_neg_of_pos hsneg h1μpos] : xiHi < 0),
      abs_of_neg hsneg]
    linarith [hxiHi_lo, hsneg]
  have hetaLole2t : |etaLo| ≤ 2* |t| := by
    rw [abs_of_neg (by linarith [hetaLo_hi] : etaLo < 0), abs_of_neg htneg]
    linarith [hetaLo_lo, hkeyt]
  have hetaHile2t : |etaHi| ≤ 2* |t| := by
    rw [abs_of_neg (by linarith [hetaHi_hi, div_neg_of_neg_of_pos htneg h1μpos] : etaHi < 0),
      abs_of_neg htneg]
    linarith [hetaHi_lo, htneg]
  rcases hζcase with hcase | hcase | hcase | hcase
  · -- LEFT edge: ζ.re = z0.re + xiLo
    set etaT : ℝ := ζ.im - z0.im with hetaT_def
    have hetaTmem1 : etaLo ≤ etaT := by simp only [hetaT_def]; linarith [hζRmem.2.2.1]
    have hetaTmem2 : etaT ≤ etaHi := by simp only [hetaT_def]; linarith [hζRmem.2.2.2]
    have hζeq : ζ = z0 + xiLo + etaT * I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hcase]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, hetaT_def]
        ring
    have hetaTne : etaT ≠ 0 := by
      have hetaHineg0 : etaHi < 0 := by
        have h2 : t/(1+μ) < 0 := div_neg_of_neg_of_pos htneg h1μpos
        linarith [hetaHi_hi, h2]
      intro h
      rw [h] at hetaTmem2
      linarith [hetaTmem2, hetaHineg0]
    have hetaTclose : |etaT - t| ≤ |t| *μ := by
      have hlo' : t - etaLo ≤ |t| *μ := by linarith [(abs_le.mp hetaLoclose).1]
      have hhi' : etaHi - t ≤ |t| *μ := (abs_le.mp hetaHiclose).2
      exact menchoff_sandwich_close hetaTmem1 hetaTmem2 hetaLo_hi.le hetaHi_lo hlo' hhi'
    have hetaHineg : etaHi < 0 := by
      have h2 : t/(1+μ) < 0 := div_neg_of_neg_of_pos htneg h1μpos
      linarith [hetaHi_hi, h2]
    have hetaLoneg' : etaLo < 0 := by linarith [hetaLo_hi]
    have hetaTsmall : |etaT| < 1/((N:ℝ)+1) := by
      rcases le_total 0 etaT with h | h
      · rw [abs_of_nonneg h]
        have := abs_of_neg hetaHineg
        linarith [hetaTmem2, hetaHismall, this]
      · rw [abs_of_nonpos h]
        have := abs_of_neg hetaLoneg'
        linarith [hetaTmem1, hetaLosmall, this]
    have hbx : ‖slope (fun u:ℝ => g (z0+u)) 0 xiLo - menchoffFx g z0‖ < μ :=
      (hM2 z0 hz0 xiLo hxiLo_ne0 hxiLosmall).1
    have hby : ‖slope (fun u:ℝ => g ((z0+xiLo)+u*I)) 0 etaT - menchoffFy g (z0+xiLo)‖ < μ :=
      (hM2 (z0+xiLo) hxiLoE etaT hetaTne hetaTsmall).2
    have hfy : ‖menchoffFy g (z0+xiLo) - menchoffFy g z0‖ < μ := by
      have hd : dist (z0+(xiLo:ℂ)) z0 < δC2 := by
        rw [dist_eq_norm]
        have heq0 : z0 + (xiLo:ℂ) - z0 = (xiLo:ℂ) := by ring
        rw [heq0, norm_real, Real.norm_eq_abs]
        exact hxiLoD.2
      have := hCfyProp hxiLoE hd
      rwa [dist_eq_norm] at this
    have hstep := menchoff_two_step hxiLo_ne0 hetaTne hbx hby hfy
    rw [← hζeq] at hstep
    have hetaTle2t : |etaT| ≤ 2* |t| := by
      have hetaHile0 : etaHi ≤ 0 := by
        have h2 : t/(1+μ) < 0 := div_neg_of_neg_of_pos htneg h1μpos
        linarith [hetaHi_hi, h2]
      have hetaTneg : etaT ≤ 0 := le_trans hetaTmem2 hetaHile0
      rw [abs_of_nonpos hetaTneg]
      have : -etaT ≤ -etaLo := by linarith [hetaTmem1]
      have hetaLoneg : etaLo ≤ 0 := by linarith [hetaLo_hi]
      rw [abs_of_nonpos hetaLoneg] at hetaLole2t
      linarith [this, hetaLole2t]
    exact menchoff_edge_finish_h_gen hμpos hxiLole2s hetaTle2t hxiLoclose hetaTclose hζeq hstep hζbound'
  · -- RIGHT edge: ζ.re = z0.re + xiHi
    set etaT : ℝ := ζ.im - z0.im with hetaT_def
    have hetaTmem1 : etaLo ≤ etaT := by simp only [hetaT_def]; linarith [hζRmem.2.2.1]
    have hetaTmem2 : etaT ≤ etaHi := by simp only [hetaT_def]; linarith [hζRmem.2.2.2]
    have hζeq : ζ = z0 + xiHi + etaT * I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hcase]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, hetaT_def]
        ring
    have hetaTne : etaT ≠ 0 := by
      have hetaHineg0 : etaHi < 0 := by
        have h2 : t/(1+μ) < 0 := div_neg_of_neg_of_pos htneg h1μpos
        linarith [hetaHi_hi, h2]
      intro h
      rw [h] at hetaTmem2
      linarith [hetaTmem2, hetaHineg0]
    have hetaTclose : |etaT - t| ≤ |t| *μ := by
      have hlo' : t - etaLo ≤ |t| *μ := by linarith [(abs_le.mp hetaLoclose).1]
      have hhi' : etaHi - t ≤ |t| *μ := (abs_le.mp hetaHiclose).2
      exact menchoff_sandwich_close hetaTmem1 hetaTmem2 hetaLo_hi.le hetaHi_lo hlo' hhi'
    have hetaHineg : etaHi < 0 := by
      have h2 : t/(1+μ) < 0 := div_neg_of_neg_of_pos htneg h1μpos
      linarith [hetaHi_hi, h2]
    have hetaLoneg' : etaLo < 0 := by linarith [hetaLo_hi]
    have hetaTsmall : |etaT| < 1/((N:ℝ)+1) := by
      rcases le_total 0 etaT with h | h
      · rw [abs_of_nonneg h]
        have := abs_of_neg hetaHineg
        linarith [hetaTmem2, hetaHismall, this]
      · rw [abs_of_nonpos h]
        have := abs_of_neg hetaLoneg'
        linarith [hetaTmem1, hetaLosmall, this]
    have hbx : ‖slope (fun u:ℝ => g (z0+u)) 0 xiHi - menchoffFx g z0‖ < μ :=
      (hM2 z0 hz0 xiHi hxiHi_ne0 hxiHismall).1
    have hby : ‖slope (fun u:ℝ => g ((z0+xiHi)+u*I)) 0 etaT - menchoffFy g (z0+xiHi)‖ < μ :=
      (hM2 (z0+xiHi) hxiHiE etaT hetaTne hetaTsmall).2
    have hfy : ‖menchoffFy g (z0+xiHi) - menchoffFy g z0‖ < μ := by
      have hd : dist (z0+(xiHi:ℂ)) z0 < δC2 := by
        rw [dist_eq_norm]
        have heq0 : z0 + (xiHi:ℂ) - z0 = (xiHi:ℂ) := by ring
        rw [heq0, norm_real, Real.norm_eq_abs]
        exact hxiHiD.2
      have := hCfyProp hxiHiE hd
      rwa [dist_eq_norm] at this
    have hstep := menchoff_two_step hxiHi_ne0 hetaTne hbx hby hfy
    rw [← hζeq] at hstep
    have hetaTle2t : |etaT| ≤ 2* |t| := by
      have hetaHile0 : etaHi ≤ 0 := by
        have h2 : t/(1+μ) < 0 := div_neg_of_neg_of_pos htneg h1μpos
        linarith [hetaHi_hi, h2]
      have hetaTneg : etaT ≤ 0 := le_trans hetaTmem2 hetaHile0
      rw [abs_of_nonpos hetaTneg]
      have : -etaT ≤ -etaLo := by linarith [hetaTmem1]
      have hetaLoneg : etaLo ≤ 0 := by linarith [hetaLo_hi]
      rw [abs_of_nonpos hetaLoneg] at hetaLole2t
      linarith [this, hetaLole2t]
    exact menchoff_edge_finish_h_gen hμpos hxiHile2s hetaTle2t hxiHiclose hetaTclose hζeq hstep hζbound'
  · -- BOTTOM edge: ζ.im = z0.im + etaLo
    set xiT : ℝ := ζ.re - z0.re with hxiT_def
    have hxiTmem1 : xiLo ≤ xiT := by simp only [hxiT_def]; linarith [hζRmem.1]
    have hxiTmem2 : xiT ≤ xiHi := by simp only [hxiT_def]; linarith [hζRmem.2.1]
    have hζeq : ζ = z0 + xiT + etaLo * I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hxiT_def]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, hcase]
        ring
    have hxiTne : xiT ≠ 0 := by
      have hxiHineg0 : xiHi < 0 := by
        have h2 : s/(1+μ) < 0 := div_neg_of_neg_of_pos hsneg h1μpos
        linarith [hxiHi_hi, h2]
      intro h
      rw [h] at hxiTmem2
      linarith [hxiTmem2, hxiHineg0]
    have hxiTclose : |xiT - s| ≤ |s| *μ := by
      have hlo' : s - xiLo ≤ |s| *μ := by linarith [(abs_le.mp hxiLoclose).1]
      have hhi' : xiHi - s ≤ |s| *μ := (abs_le.mp hxiHiclose).2
      exact menchoff_sandwich_close hxiTmem1 hxiTmem2 hxiLo_hi.le hxiHi_lo hlo' hhi'
    have hxiHineg : xiHi < 0 := by
      have h2 : s/(1+μ) < 0 := div_neg_of_neg_of_pos hsneg h1μpos
      linarith [hxiHi_hi, h2]
    have hxiLoneg' : xiLo < 0 := by linarith [hxiLo_hi]
    have hxiTsmall : |xiT| < 1/((N:ℝ)+1) := by
      rcases le_total 0 xiT with h | h
      · rw [abs_of_nonneg h]
        have := abs_of_neg hxiHineg
        linarith [hxiTmem2, hxiHismall, this]
      · rw [abs_of_nonpos h]
        have := abs_of_neg hxiLoneg'
        linarith [hxiTmem1, hxiLosmall, this]
    have hby : ‖slope (fun u:ℝ => g (z0+u*I)) 0 etaLo - menchoffFy g z0‖ < μ :=
      (hM2 z0 hz0 etaLo hetaLo_ne0 hetaLosmall).2
    have hbx : ‖slope (fun u:ℝ => g ((z0+etaLo*I)+u)) 0 xiT - menchoffFx g (z0+etaLo*I)‖ < μ :=
      (hM2 (z0+etaLo*I) hetaLoE xiT hxiTne hxiTsmall).1
    have hfx : ‖menchoffFx g (z0+etaLo*I) - menchoffFx g z0‖ < μ := by
      have hd : dist (z0+(etaLo:ℂ)*I) z0 < δC1 := by
        rw [dist_eq_norm]
        have heq0 : z0 + (etaLo:ℂ)*I - z0 = (etaLo:ℂ)*I := by ring
        rw [heq0, norm_mul, norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
        exact hetaLoD.1
      have := hCfxProp hetaLoE hd
      rwa [dist_eq_norm] at this
    have hstep := menchoff_two_step_vh hxiTne hetaLo_ne0 hby hbx hfx
    rw [← hζeq] at hstep
    have hxiTle2s : |xiT| ≤ 2* |s| := by
      have hxiHile0 : xiHi ≤ 0 := by
        have h2 : s/(1+μ) < 0 := div_neg_of_neg_of_pos hsneg h1μpos
        linarith [hxiHi_hi, h2]
      have hxiTneg : xiT ≤ 0 := le_trans hxiTmem2 hxiHile0
      rw [abs_of_nonpos hxiTneg]
      have : -xiT ≤ -xiLo := by linarith [hxiTmem1]
      have hxiLoneg : xiLo ≤ 0 := by linarith [hxiLo_hi]
      rw [abs_of_nonpos hxiLoneg] at hxiLole2s
      linarith [this, hxiLole2s]
    exact menchoff_edge_finish_v_gen hμpos hxiTle2s hetaLole2t hxiTclose hetaLoclose hζeq hstep hζbound'
  · -- TOP edge: ζ.im = z0.im + etaHi
    set xiT : ℝ := ζ.re - z0.re with hxiT_def
    have hxiTmem1 : xiLo ≤ xiT := by simp only [hxiT_def]; linarith [hζRmem.1]
    have hxiTmem2 : xiT ≤ xiHi := by simp only [hxiT_def]; linarith [hζRmem.2.1]
    have hζeq : ζ = z0 + xiT + etaHi * I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hxiT_def]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, hcase]
        ring
    have hxiTne : xiT ≠ 0 := by
      have hxiHineg0 : xiHi < 0 := by
        have h2 : s/(1+μ) < 0 := div_neg_of_neg_of_pos hsneg h1μpos
        linarith [hxiHi_hi, h2]
      intro h
      rw [h] at hxiTmem2
      linarith [hxiTmem2, hxiHineg0]
    have hxiTclose : |xiT - s| ≤ |s| *μ := by
      have hlo' : s - xiLo ≤ |s| *μ := by linarith [(abs_le.mp hxiLoclose).1]
      have hhi' : xiHi - s ≤ |s| *μ := (abs_le.mp hxiHiclose).2
      exact menchoff_sandwich_close hxiTmem1 hxiTmem2 hxiLo_hi.le hxiHi_lo hlo' hhi'
    have hxiHineg : xiHi < 0 := by
      have h2 : s/(1+μ) < 0 := div_neg_of_neg_of_pos hsneg h1μpos
      linarith [hxiHi_hi, h2]
    have hxiLoneg' : xiLo < 0 := by linarith [hxiLo_hi]
    have hxiTsmall : |xiT| < 1/((N:ℝ)+1) := by
      rcases le_total 0 xiT with h | h
      · rw [abs_of_nonneg h]
        have := abs_of_neg hxiHineg
        linarith [hxiTmem2, hxiHismall, this]
      · rw [abs_of_nonpos h]
        have := abs_of_neg hxiLoneg'
        linarith [hxiTmem1, hxiLosmall, this]
    have hby : ‖slope (fun u:ℝ => g (z0+u*I)) 0 etaHi - menchoffFy g z0‖ < μ :=
      (hM2 z0 hz0 etaHi hetaHi_ne0 hetaHismall).2
    have hbx : ‖slope (fun u:ℝ => g ((z0+etaHi*I)+u)) 0 xiT - menchoffFx g (z0+etaHi*I)‖ < μ :=
      (hM2 (z0+etaHi*I) hetaHiE xiT hxiTne hxiTsmall).1
    have hfx : ‖menchoffFx g (z0+etaHi*I) - menchoffFx g z0‖ < μ := by
      have hd : dist (z0+(etaHi:ℂ)*I) z0 < δC1 := by
        rw [dist_eq_norm]
        have heq0 : z0 + (etaHi:ℂ)*I - z0 = (etaHi:ℂ)*I := by ring
        rw [heq0, norm_mul, norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
        exact hetaHiD.1
      have := hCfxProp hetaHiE hd
      rwa [dist_eq_norm] at this
    have hstep := menchoff_two_step_vh hxiTne hetaHi_ne0 hby hbx hfx
    rw [← hζeq] at hstep
    have hxiTle2s : |xiT| ≤ 2* |s| := by
      have hxiHile0 : xiHi ≤ 0 := by
        have h2 : s/(1+μ) < 0 := div_neg_of_neg_of_pos hsneg h1μpos
        linarith [hxiHi_hi, h2]
      have hxiTneg : xiT ≤ 0 := le_trans hxiTmem2 hxiHile0
      rw [abs_of_nonpos hxiTneg]
      have : -xiT ≤ -xiLo := by linarith [hxiTmem1]
      have hxiLoneg : xiLo ≤ 0 := by linarith [hxiLo_hi]
      rw [abs_of_nonpos hxiLoneg] at hxiLole2s
      linarith [this, hxiLole2s]
    exact menchoff_edge_finish_v_gen hμpos hxiTle2s hetaHile2t hxiTclose hetaHiclose hζeq hstep hζbound'

theorem menchoff_M4_bound {g : ℂ → ℂ} (hg : Continuous g) {Q : Set ℂ} (hQ : IsOpen Q)
    (hopen : ∀ U ⊆ Q, IsOpen U → IsOpen (g '' U)) {E : Set ℂ} (hEQ : E ⊆ Q)
    {z0 : ℂ} (hz0 : z0 ∈ E) {m N : ℕ}
    (hM2 : ∀ z ∈ E, ∀ s : ℝ, s ≠ 0 → |s| < 1/(N+1) →
      ‖slope (fun t : ℝ => g (z + t)) 0 s - menchoffFx g z‖ < 1/(m+1) ∧
      ‖slope (fun t : ℝ => g (z + t * I)) 0 s - menchoffFy g z‖ < 1/(m+1))
    (hCfx : ContinuousWithinAt (menchoffFx g) E z0)
    (hCfy : ContinuousWithinAt (menchoffFy g) E z0)
    (hDensHR : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ →
      ∃ ξ ∈ Set.Ioc (s/(1+ε)) s, z0 + ξ ∈ E)
    (hDensHL : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ →
      ∃ ξ ∈ Set.Ico (-s) (-(s/(1+ε))), z0 + ξ ∈ E)
    (hDensVR : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      ∃ η ∈ Set.Ioc (t/(1+ε)) t, z0 + η * I ∈ E)
    (hDensVL : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      ∃ η ∈ Set.Ico (-t) (-(t/(1+ε))), z0 + η * I ∈ E) :
    ∃ δ > 0, ∀ s t : ℝ, |s| < δ → |t| < δ →
      ‖g (z0 + s + t * I) - g z0 - menchoffFx g z0 * s - menchoffFy g z0 * t‖ ≤
        (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * (1/(m+1)) * (|s| + |t|) := by
  obtain ⟨δ1, hδ1pos, h1⟩ := menchoff_M4_quadrant_pp hg hQ hopen hEQ hz0 hM2 hCfx hCfy hDensHR hDensVR
  obtain ⟨δ2, hδ2pos, h2⟩ := menchoff_M4_quadrant_pm hg hQ hopen hEQ hz0 hM2 hCfx hCfy hDensHR hDensVL
  obtain ⟨δ3, hδ3pos, h3⟩ := menchoff_M4_quadrant_mp hg hQ hopen hEQ hz0 hM2 hCfx hCfy hDensHL hDensVR
  obtain ⟨δ4, hδ4pos, h4⟩ := menchoff_M4_quadrant_mm hg hQ hopen hEQ hz0 hM2 hCfx hCfy hDensHL hDensVL
  have hcoeff : (1 : ℝ) ≤ 6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖ := by
    have h1 := norm_nonneg (menchoffFx g z0)
    have h2 := norm_nonneg (menchoffFy g z0)
    linarith
  refine ⟨min δ1 (min δ2 (min δ3 (min δ4 (1 / ((N : ℝ) + 1))))), by positivity, ?_⟩
  intro s t hs ht
  have hδ1s : |s| < δ1 := hs.trans_le (min_le_left _ _)
  have hδ2s : |s| < δ2 := hs.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ3s : |s| < δ3 := hs.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδ4s : |s| < δ4 :=
    hs.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδNs : |s| < 1 / ((N : ℝ) + 1) := hs.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hδ1t : |t| < δ1 := ht.trans_le (min_le_left _ _)
  have hδ2t : |t| < δ2 := ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ3t : |t| < δ3 := ht.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδ4t : |t| < δ4 :=
    ht.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδNt : |t| < 1 / ((N : ℝ) + 1) := ht.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  rcases lt_trichotomy s 0 with hsneg | hszero | hspos
  · rcases lt_trichotomy t 0 with htneg | htzero | htpos
    · exact h4 s t hsneg (by rw [abs_of_neg hsneg] at hδ4s; linarith) htneg
        (by rw [abs_of_neg htneg] at hδ4t; linarith)
    · subst htzero
      have hsne : s ≠ 0 := hsneg.ne
      have hb := menchoff_slope_to_diff hsne (hM2 z0 hz0 s hsne hδNs).1
      simp only [Complex.ofReal_zero, zero_mul, mul_zero, add_zero, sub_zero, abs_zero]
      have hkey : |s| * (1 / ((m:ℝ) + 1)) ≤
          (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * (1 / ((m:ℝ) + 1)) * |s| := by
        have hμnn : (0:ℝ) ≤ 1 / ((m:ℝ)+1) := by positivity
        calc |s| * (1/((m:ℝ)+1)) = 1 * ((1/((m:ℝ)+1)) * |s|) := by ring
          _ ≤ (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * ((1/((m:ℝ)+1)) * |s|) :=
              mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hμnn (abs_nonneg s))
          _ = (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * (1/((m:ℝ)+1)) * |s| := by ring
      linarith [hb.le]
    · exact h3 s t hsneg (by rw [abs_of_neg hsneg] at hδ3s; linarith) htpos
        (by rwa [abs_of_pos htpos] at hδ3t)
  · subst hszero
    rcases lt_trichotomy t 0 with htneg | htzero | htpos
    · have htne : t ≠ 0 := htneg.ne
      have hb := menchoff_slope_to_diff_vert htne (hM2 z0 hz0 t htne hδNt).2
      simp only [Complex.ofReal_zero, zero_mul, mul_zero, add_zero, sub_zero, abs_zero]
      have hkey : |t| * (1 / ((m:ℝ) + 1)) ≤
          (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * (1 / ((m:ℝ) + 1)) * |t| := by
        have hμnn : (0:ℝ) ≤ 1 / ((m:ℝ)+1) := by positivity
        calc |t| * (1/((m:ℝ)+1)) = 1 * ((1/((m:ℝ)+1)) * |t|) := by ring
          _ ≤ (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * ((1/((m:ℝ)+1)) * |t|) :=
              mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hμnn (abs_nonneg t))
          _ = (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * (1/((m:ℝ)+1)) * |t| := by ring
      linarith [hb.le]
    · subst htzero; simp
    · have hb := menchoff_slope_to_diff_vert htpos.ne' (hM2 z0 hz0 t htpos.ne' hδNt).2
      simp only [Complex.ofReal_zero, zero_mul, mul_zero, add_zero, sub_zero, abs_zero]
      have hkey : |t| * (1 / ((m:ℝ) + 1)) ≤
          (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * (1 / ((m:ℝ) + 1)) * |t| := by
        have hμnn : (0:ℝ) ≤ 1 / ((m:ℝ)+1) := by positivity
        calc |t| * (1/((m:ℝ)+1)) = 1 * ((1/((m:ℝ)+1)) * |t|) := by ring
          _ ≤ (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * ((1/((m:ℝ)+1)) * |t|) :=
              mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hμnn (abs_nonneg t))
          _ = (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * (1/((m:ℝ)+1)) * |t| := by ring
      linarith [hb.le]
  · rcases lt_trichotomy t 0 with htneg | htzero | htpos
    · exact h2 s t hspos (by rwa [abs_of_pos hspos] at hδ2s)
        htneg (by rw [abs_of_neg htneg] at hδ2t; linarith)
    · subst htzero
      have hsne : s ≠ 0 := hspos.ne'
      have hb := menchoff_slope_to_diff hsne (hM2 z0 hz0 s hsne hδNs).1
      simp only [Complex.ofReal_zero, zero_mul, mul_zero, add_zero, sub_zero, abs_zero]
      have hkey : |s| * (1 / ((m:ℝ) + 1)) ≤
          (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * (1 / ((m:ℝ) + 1)) * |s| := by
        have hμnn : (0:ℝ) ≤ 1 / ((m:ℝ)+1) := by positivity
        calc |s| * (1/((m:ℝ)+1)) = 1 * ((1/((m:ℝ)+1)) * |s|) := by ring
          _ ≤ (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * ((1/((m:ℝ)+1)) * |s|) :=
              mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hμnn (abs_nonneg s))
          _ = (6 + ‖menchoffFx g z0‖ + ‖menchoffFy g z0‖) * (1/((m:ℝ)+1)) * |s| := by ring
      linarith [hb.le]
    · exact h1 s t hspos (by rwa [abs_of_pos hspos] at hδ1s) htpos (by rwa [abs_of_pos htpos] at hδ1t)



theorem menchoff_volume_closedRect_eq_openRect (a b c d : ℝ) :
    volume (Set.Icc a b ×ℂ Set.Icc c d) = volume (Set.Ioo a b ×ℂ Set.Ioo c d) := by
  have hpre1 : Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc c d) =
      Set.Icc a b ×ℂ Set.Icc c d := by
    ext z; simp [Complex.measurableEquivRealProd_apply, mem_reProdIm]; tauto
  have hpre2 : Complex.measurableEquivRealProd ⁻¹' (Set.Ioo a b ×ˢ Set.Ioo c d) =
      Set.Ioo a b ×ℂ Set.Ioo c d := by
    ext z; simp [Complex.measurableEquivRealProd_apply, mem_reProdIm]
  rw [← hpre1, ← hpre2, (Complex.volume_preserving_equiv_real_prod).measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet,
    (Complex.volume_preserving_equiv_real_prod).measure_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet,
    Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Measure.prod_prod]
  simp [Real.volume_Icc, Real.volume_Ioo]

/-- The boundary of a rectangle is Lebesgue-null. -/
theorem menchoff_volume_closedRect_diff_openRect (a b c d : ℝ) :
    volume (closedRect a b c d \ openRect a b c d) = 0 := by
  have hsub : openRect a b c d ⊆ closedRect a b c d :=
    acl_openRect_subset_closedRect le_rfl le_rfl le_rfl le_rfl
  have hmeas : MeasurableSet (openRect a b c d) := (acl_isOpen_openRect a b c d).measurableSet
  have hlt : volume (openRect a b c d) < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) (acl_isCompact_closedRect a b c d).measure_lt_top
  have heqv : volume (closedRect a b c d) = volume (openRect a b c d) := by
    rw [acl_closedRect_eq, acl_openRect_eq]
    exact menchoff_volume_closedRect_eq_openRect a b c d
  rw [measure_diff hsub hmeas.nullMeasurableSet hlt.ne, heqv, tsub_self]

/-- Derivatives are local: if `g = f` on an open set `U`, the horizontal difference-quotient
derivative of `g` and of `f` agree at every point of `U`. -/
theorem menchoff_fx_eq_of_eqOn {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hfg : EqOn g f U)
    {z : ℂ} (hz : z ∈ U) : menchoffFx g z = menchoffFx f z := by
  have hev : (fun t : ℝ => g (z + t)) =ᶠ[𝓝 0] fun t : ℝ => f (z + t) := by
    have hcont : Continuous fun t : ℝ => z + (t : ℂ) := by fun_prop
    have h0 : z + ((0 : ℝ) : ℂ) ∈ U := by simpa using hz
    filter_upwards [hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)] with t ht
    exact hfg ht
  unfold menchoffFx
  exact hev.deriv_eq

theorem menchoff_fy_eq_of_eqOn {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hfg : EqOn g f U)
    {z : ℂ} (hz : z ∈ U) : menchoffFy g z = menchoffFy f z := by
  have hev : (fun t : ℝ => g (z + t * I)) =ᶠ[𝓝 0] fun t : ℝ => f (z + t * I) := by
    have hcont : Continuous fun t : ℝ => z + (t : ℂ) * I := by fun_prop
    have h0 : z + ((0 : ℝ) : ℂ) * I ∈ U := by simpa using hz
    filter_upwards [hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)] with t ht
    exact hfg ht
  unfold menchoffFy
  exact hev.deriv_eq

/-- Openness of images transfers from `f` to any extension `g` that agrees with `f` on `U`. -/
theorem menchoff_hopen_of_eqOn {f g : ℂ → ℂ} {D U : Set ℂ} (hD : IsOpen D)
    (hfc : ContinuousOn f D) (hfi : InjOn f D) (hUD : U ⊆ D) (hfgU : EqOn g f U) :
    ∀ V ⊆ U, IsOpen V → IsOpen (g '' V) := by
  intro V hVU hVo
  rw [Set.image_congr (hfgU.mono hVU)]
  exact isOpen_image_of_continuousOn_injOn_of_subset hD hfc hfi (hVU.trans hUD) hVo

theorem menchoff_mem_of_hSlice {E : Set ℂ} {z0 : ℂ} {ξ : ℝ}
    (h : z0.re + ξ ∈ menchoffHSlice E z0.im) : z0 + (ξ : ℂ) ∈ E := by
  simp only [menchoffHSlice, mem_setOf_eq] at h
  have heq : ((z0.re + ξ : ℝ) : ℂ) + (z0.im : ℝ) * I = z0 + (ξ : ℂ) := by
    have hri := Complex.re_add_im z0; push_cast; linear_combination hri
  rwa [heq] at h

theorem menchoff_mem_of_vSlice {E : Set ℂ} {z0 : ℂ} {η : ℝ}
    (h : z0.im + η ∈ menchoffVSlice E z0.re) : z0 + (η : ℂ) * I ∈ E := by
  simp only [menchoffVSlice, mem_setOf_eq] at h
  have heq : ((z0.re : ℝ) : ℂ) + ((z0.im + η : ℝ) : ℂ) * I = z0 + (η : ℂ) * I := by
    have hri := Complex.re_add_im z0; push_cast; linear_combination hri
  rwa [heq] at h

/-- The four density hypotheses of `menchoff_M4_bound`, from `menchoff_M3`'s output at `z0`. -/
theorem menchoff_hDensHR {E : Set ℂ} {z0 : ℂ}
    (hseq : Tendsto (fun n : ℕ => volume (menchoffHSlice E z0.im ∩ closedBall z0.re (1/(n+1))) /
      volume (closedBall z0.re (1/(n+1)))) atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ →
      ∃ ξ ∈ Set.Ioc (s/(1+ε)) s, z0 + ξ ∈ E := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := menchoff_exists_right (menchoff_density_continuum hseq) ε hε
  refine ⟨δ, hδ, fun s hs0 hsδ => ?_⟩
  obtain ⟨ξ, hξ, hmem⟩ := hb s hs0 hsδ
  exact ⟨ξ, hξ, menchoff_mem_of_hSlice hmem⟩

theorem menchoff_hDensHL {E : Set ℂ} {z0 : ℂ}
    (hseq : Tendsto (fun n : ℕ => volume (menchoffHSlice E z0.im ∩ closedBall z0.re (1/(n+1))) /
      volume (closedBall z0.re (1/(n+1)))) atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ →
      ∃ ξ ∈ Set.Ico (-s) (-(s/(1+ε))), z0 + ξ ∈ E := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := menchoff_exists_left (menchoff_density_continuum hseq) ε hε
  refine ⟨δ, hδ, fun s hs0 hsδ => ?_⟩
  obtain ⟨ξ, hξ, hmem⟩ := hb s hs0 hsδ
  exact ⟨ξ, hξ, menchoff_mem_of_hSlice hmem⟩

theorem menchoff_hDensVR {E : Set ℂ} {z0 : ℂ}
    (hseq : Tendsto (fun n : ℕ => volume (menchoffVSlice E z0.re ∩ closedBall z0.im (1/(n+1))) /
      volume (closedBall z0.im (1/(n+1)))) atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      ∃ η ∈ Set.Ioc (t/(1+ε)) t, z0 + η * I ∈ E := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := menchoff_exists_right (menchoff_density_continuum hseq) ε hε
  refine ⟨δ, hδ, fun t ht0 htδ => ?_⟩
  obtain ⟨η, hη, hmem⟩ := hb t ht0 htδ
  exact ⟨η, hη, menchoff_mem_of_vSlice hmem⟩

theorem menchoff_hDensVL {E : Set ℂ} {z0 : ℂ}
    (hseq : Tendsto (fun n : ℕ => volume (menchoffVSlice E z0.re ∩ closedBall z0.im (1/(n+1))) /
      volume (closedBall z0.im (1/(n+1)))) atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      ∃ η ∈ Set.Ico (-t) (-(t/(1+ε))), z0 + η * I ∈ E := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := menchoff_exists_left (menchoff_density_continuum hseq) ε hε
  refine ⟨δ, hδ, fun t ht0 htδ => ?_⟩
  obtain ⟨η, hη, hmem⟩ := hb t ht0 htδ
  exact ⟨η, hη, menchoff_mem_of_vSlice hmem⟩

theorem menchoff_tendsto_ofReal_one_div_add :
    Tendsto (fun m : ℕ => ENNReal.ofReal (1/((m:ℝ)+1))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => (1/((m:ℝ)+1))) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 := (ENNReal.continuous_ofReal.continuousAt (x := (0:ℝ))).tendsto.comp h1
  simpa [Function.comp_def] using h2

/-- A quantity bounded above by a null sequence for every index is zero. -/
theorem menchoff_eq_zero_of_forall_le {c : ENNReal} {f : ℕ → ENNReal}
    (htend : Tendsto f atTop (𝓝 0)) (h : ∀ m, c ≤ f m) : c = 0 :=
  le_antisymm (ge_of_tendsto htend (Filter.Eventually.of_forall h)) bot_le

theorem menchoff_tendsto_ofReal_one_div_add_shift (M : ℕ) :
    Tendsto (fun k : ℕ => ENNReal.ofReal (1/(((k+M:ℕ):ℝ)+1))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => (1/((m:ℝ)+1))) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 := h1.comp (tendsto_add_atTop_nat M)
  have h3 := (ENNReal.continuous_ofReal.continuousAt (x := (0:ℝ))).tendsto.comp h2
  simp only [Function.comp_def] at h3
  simpa using h3

/-- If `volume (R \ G m) ≤ 1/(m+1)` for every `m`, then a.e. `z ∈ R` lies in `G m` for
infinitely many `m` — no summability needed, since `1/(m+1) → 0` already forces the tail
intersections to be null. -/
theorem menchoff_null_compl_of_le (R : Set ℂ) (G : ℕ → Set ℂ)
    (hbound : ∀ m, volume (R \ G m) ≤ ENNReal.ofReal (1/((m:ℝ)+1))) :
    volume (R \ {z | ∃ᶠ m in atTop, z ∈ G m}) = 0 := by
  have hcover : R \ {z | ∃ᶠ m in atTop, z ∈ G m} = ⋃ M : ℕ, (R ∩ ⋂ m ∈ Ici M, (R \ G m)) := by
    ext z
    simp only [mem_diff, mem_setOf_eq, Filter.not_frequently, Filter.eventually_atTop,
      mem_iUnion, mem_inter_iff, mem_iInter, mem_Ici]
    constructor
    · rintro ⟨hzR, N, hN⟩
      exact ⟨N, hzR, fun m hm => ⟨hzR, hN m hm⟩⟩
    · rintro ⟨N, hzR, hN⟩
      exact ⟨hzR, N, fun m hm => (hN m hm).2⟩
  rw [hcover]
  refine measure_iUnion_null fun M => ?_
  apply menchoff_eq_zero_of_forall_le (menchoff_tendsto_ofReal_one_div_add_shift M)
  intro k
  calc volume (R ∩ ⋂ m ∈ Ici M, (R \ G m)) ≤ volume (R \ G (k + M)) :=
        measure_mono (fun z hz => (mem_iInter₂.mp hz.2) (k + M) (Nat.le_add_left M k))
    _ ≤ ENNReal.ofReal (1/(((k+M:ℕ):ℝ)+1)) := hbound (k + M)

/-- The `ℝ`-linear map `s + tI ↦ Fx·s + Fy·t`. -/
def menchoffL (Fx Fy : ℂ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.smulRight Complex.reCLM Fx + ContinuousLinearMap.smulRight Complex.imCLM Fy

theorem menchoffL_apply (Fx Fy h : ℂ) : menchoffL Fx Fy h = (h.re : ℂ) * Fx + (h.im : ℂ) * Fy := by
  simp [menchoffL, Complex.real_smul, Complex.reCLM_apply, Complex.imCLM_apply]

/-- If the difference-quotient bound at `z0` holds, with error constant `C/(m+1)`, for
infinitely many `m`, then `f` is differentiable at `z0` with derivative `menchoffL Fx Fy`. -/
theorem menchoff_hasFDerivAt_of_bound {f : ℂ → ℂ} {z0 Fx Fy : ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∃ᶠ m : ℕ in atTop, ∃ δ > 0, ∀ s t : ℝ, |s| < δ → |t| < δ →
      ‖f (z0 + s + t * I) - f z0 - Fx * s - Fy * t‖ ≤ C * (1/((m:ℝ)+1)) * (|s| + |t|)) :
    HasFDerivAt f (menchoffL Fx Fy) z0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hev : ∀ᶠ m : ℕ in atTop, C * (1/((m:ℝ)+1)) ≤ c/2 := by
    have htend : Tendsto (fun m : ℕ => C * (1/((m:ℝ)+1))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ => (1/((m:ℝ)+1))) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using h1.const_mul C
    exact htend.eventually_le_const (by positivity)
  obtain ⟨m, ⟨δ, hδ, hb⟩, hCm⟩ := (hbd.and_eventually hev).exists
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ] with h hh
  rw [Metric.mem_ball, dist_zero_right] at hh
  have hs : |h.re| < δ := lt_of_le_of_lt (Complex.abs_re_le_norm h) hh
  have ht : |h.im| < δ := lt_of_le_of_lt (Complex.abs_im_le_norm h) hh
  have key := hb h.re h.im hs ht
  have hzh : z0 + h.re + h.im * I = z0 + h := by
    have hri := Complex.re_add_im h; linear_combination hri
  rw [hzh] at key
  show ‖f (z0 + h) - f z0 - menchoffL Fx Fy h‖ ≤ c * ‖h‖
  rw [menchoffL_apply]
  have heq : f (z0+h) - f z0 - ((h.re:ℂ)*Fx + (h.im:ℂ)*Fy) =
      f (z0+h) - f z0 - Fx*(h.re:ℝ) - Fy*(h.im:ℝ) := by ring
  rw [heq]
  have hsum : |h.re| + |h.im| ≤ 2 * ‖h‖ := by
    linarith [Complex.abs_re_le_norm h, Complex.abs_im_le_norm h]
  have hnn : (0:ℝ) ≤ |h.re| + |h.im| := by positivity
  calc ‖f (z0+h) - f z0 - Fx*(h.re:ℝ) - Fy*(h.im:ℝ)‖
      ≤ C * (1/((m:ℝ)+1)) * (|h.re| + |h.im|) := key
    _ ≤ c/2 * (2*‖h‖) := mul_le_mul hCm hsum hnn (by linarith)
    _ = c * ‖h‖ := by ring

theorem menchoff_enorm_lt_ofReal_iff (x : ℂ) (c : ℝ) : ‖x‖ₑ < ENNReal.ofReal c ↔ ‖x‖ < c := by
  rw [← ofReal_norm]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg x)

/-- Transports an a.e. statement from an open subset `U` to the ambient closed set `R`, when
`R \ U` is null: the restricted measures agree, so "a.e. on `U`" and "a.e. on `R`" coincide. -/
theorem menchoff_ae_of_ae_restrict_open {R U : Set ℂ} (hRmeas : MeasurableSet R) (hUR : U ⊆ R)
    (hnull : volume (R \ U) = 0) {P : ℂ → Prop} (h : ∀ᵐ z ∂ volume.restrict U, P z) :
    ∀ᵐ z ∂ volume, z ∈ R → P z := by
  have heq : volume.restrict R = volume.restrict U := by
    apply Measure.restrict_congr_set
    rw [ae_eq_set]
    exact ⟨hnull, by rw [Set.diff_eq_empty.mpr hUR]; exact measure_empty⟩
  rw [← ae_restrict_iff' hRmeas, heq]
  exact h

/-- The countable-assembly step: `f` is differentiable a.e. on any open rectangle whose closure
lies in `D`, given `hpart` on `D`. Combines a Tietze extension `g`, the openness of `g`'s images
(threaded from `f`'s via `menchoff_hopen_of_eqOn`), `menchoff_M2`'s scale-`m` good sets intersected
with the open rectangle, `menchoff_M3`'s density at a.e. point of each, `menchoff_M4_bound`'s
ε–δ estimate transported from `g` back to `f`, and `menchoff_hasFDerivAt_of_bound` assembling the
derivative from infinitely many scales. -/
theorem menchoff_ae_diff_openRect {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hfc : ContinuousOn f D) (hfi : InjOn f D) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hRD : closedRect a b c d ⊆ D)
    (hpart : ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
      DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0) :
    ∀ᵐ z ∂(volume.restrict (openRect a b c d)), DifferentiableAt ℝ f z := by
  have hUR : openRect a b c d ⊆ closedRect a b c d :=
    acl_openRect_subset_closedRect le_rfl le_rfl le_rfl le_rfl
  have hUD : openRect a b c d ⊆ D := hUR.trans hRD
  have hUo : IsOpen (openRect a b c d) := acl_isOpen_openRect a b c d
  have hUmeas : MeasurableSet (openRect a b c d) := hUo.measurableSet
  have hRmeas : MeasurableSet (closedRect a b c d) :=
    (acl_isCompact_closedRect a b c d).isClosed.measurableSet
  obtain ⟨g, hgc, hgf⟩ := acl_exists_continuous_ext (acl_isCompact_closedRect a b c d).isClosed
    (hfc.mono hRD)
  have hgfU : EqOn g f (openRect a b c d) := hgf.mono hUR
  have hopen_g : ∀ V ⊆ openRect a b c d, IsOpen V → IsOpen (g '' V) :=
    menchoff_hopen_of_eqOn hD hfc hfi hUD hgfU
  have hFxeq : ∀ z ∈ openRect a b c d, menchoffFx g z = menchoffFx f z :=
    fun z hz => menchoff_fx_eq_of_eqOn hUo hgfU hz
  have hFyeq : ∀ z ∈ openRect a b c d, menchoffFy g z = menchoffFy f z :=
    fun z hz => menchoff_fy_eq_of_eqOn hUo hgfU hz
  have hpartU : ∀ᵐ z ∂ (volume.restrict (openRect a b c d)),
      DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
        DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0 :=
    ae_mono (Measure.restrict_mono hUD (le_refl _)) hpart
  have hpartU' : ∀ᵐ z ∂ (volume.restrict (openRect a b c d)),
      DifferentiableAt ℝ (fun t : ℝ => g (z + t)) 0 ∧
        DifferentiableAt ℝ (fun t : ℝ => g (z + t * I)) 0 := by
    filter_upwards [hpartU, ae_restrict_mem hUmeas] with z hz hzU
    exact ⟨(acl_differentiableAt_congr_horiz hUo hgfU hzU).mp hz.1,
           (acl_differentiableAt_congr_vert hUo hgfU hzU).mp hz.2⟩
  have hae_g : ∀ᵐ z ∂ volume, z ∈ closedRect a b c d →
      DifferentiableAt ℝ (fun t : ℝ => g (z + t)) 0 ∧
        DifferentiableAt ℝ (fun t : ℝ => g (z + t * I)) 0 :=
    menchoff_ae_of_ae_restrict_open hRmeas hUR
      (menchoff_volume_closedRect_diff_openRect a b c d) hpartU'
  have hGgood : ∀ m : ℕ, ∃ G : Set ℂ, G ⊆ openRect a b c d ∧
      volume (closedRect a b c d \ G) ≤ ENNReal.ofReal (1/((m:ℝ)+1)) ∧
      ∀ z0 ∈ G, ∃ δ > 0, ∀ s t : ℝ, |s| < δ → |t| < δ →
        ‖f (z0+s+t*I) - f z0 - menchoffFx f z0 * s - menchoffFy f z0 * t‖ ≤
          (6+‖menchoffFx f z0‖+‖menchoffFy f z0‖) * (1/((m:ℝ)+1)) * (|s|+|t|) := by
    intro m
    obtain ⟨E, hER, hEmeas, hEvol, hCfxE, hCfyE, N, hM2E⟩ := menchoff_M2 hgc hab hcd hae_g m
    set E' := E ∩ openRect a b c d with hE'def
    have hE'meas : MeasurableSet E' := hEmeas.inter hUmeas
    have hE'U : E' ⊆ openRect a b c d := inter_subset_right
    have hE'R : E' ⊆ closedRect a b c d := hE'U.trans hUR
    have hE'vol : volume (closedRect a b c d \ E') ≤ ENNReal.ofReal (1/((m:ℝ)+1)) := by
      have heqdiff : closedRect a b c d \ E' =
          (closedRect a b c d \ E) ∪ (closedRect a b c d \ openRect a b c d) := by
        ext z; simp only [mem_diff, hE'def, mem_inter_iff, mem_union]; tauto
      rw [heqdiff]
      calc volume _ ≤ volume (closedRect a b c d \ E) +
            volume (closedRect a b c d \ openRect a b c d) := measure_union_le _ _
        _ ≤ ENNReal.ofReal (1/((m:ℝ)+1)) + 0 := by
            rw [menchoff_volume_closedRect_diff_openRect]; exact add_le_add hEvol le_rfl
        _ = ENNReal.ofReal (1/((m:ℝ)+1)) := by rw [add_zero]
    have hdens := menchoff_M3 hE'meas
    set Gm := E' ∩ {z0 | Tendsto (fun n : ℕ => volume (menchoffHSlice E' z0.im ∩
        closedBall z0.re (1/(n+1))) / volume (closedBall z0.re (1/(n+1)))) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => volume (menchoffVSlice E' z0.re ∩
        closedBall z0.im (1/(n+1))) / volume (closedBall z0.im (1/(n+1)))) atTop (𝓝 1)}
      with hGmdef
    have hGmE' : Gm ⊆ E' := inter_subset_left
    have hGmU : Gm ⊆ openRect a b c d := hGmE'.trans hE'U
    have hGmnull : volume (E' \ Gm) = 0 := by
      rw [ae_iff] at hdens
      simp only [Classical.not_imp] at hdens
      convert hdens using 2
      ext z
      simp only [mem_diff, hGmdef, mem_inter_iff, mem_setOf_eq]
      tauto
    have hGmvol : volume (closedRect a b c d \ Gm) ≤ ENNReal.ofReal (1/((m:ℝ)+1)) := by
      have heqdiff2 : closedRect a b c d \ Gm =
          (closedRect a b c d \ E') ∪ (E' \ Gm) := by
        ext z
        simp only [mem_diff, mem_union]
        constructor
        · rintro ⟨hzR, hzGm⟩
          by_cases hzE' : z ∈ E'
          · exact Or.inr ⟨hzE', hzGm⟩
          · exact Or.inl ⟨hzR, hzE'⟩
        · rintro (⟨hzR, hzE'⟩ | ⟨hzE', hzGm⟩)
          · exact ⟨hzR, fun h => hzE' (hGmE' h)⟩
          · exact ⟨hE'R hzE', hzGm⟩
      rw [heqdiff2]
      calc volume _ ≤ volume (closedRect a b c d \ E') + volume (E' \ Gm) := measure_union_le _ _
        _ ≤ ENNReal.ofReal (1/((m:ℝ)+1)) + 0 := add_le_add hE'vol hGmnull.le
        _ = ENNReal.ofReal (1/((m:ℝ)+1)) := by rw [add_zero]
    refine ⟨Gm, hGmU, hGmvol, ?_⟩
    intro z0 hz0
    have hz0E' : z0 ∈ E' := hGmE' hz0
    have hz0E : z0 ∈ E := hz0E'.1
    have hz0U : z0 ∈ openRect a b c d := hz0E'.2
    have hz0densH : Tendsto (fun n : ℕ => volume (menchoffHSlice E' z0.im ∩
        closedBall z0.re (1/(n+1))) / volume (closedBall z0.re (1/(n+1)))) atTop (𝓝 1) := hz0.2.1
    have hz0densV : Tendsto (fun n : ℕ => volume (menchoffVSlice E' z0.re ∩
        closedBall z0.im (1/(n+1))) / volume (closedBall z0.im (1/(n+1)))) atTop (𝓝 1) := hz0.2.2
    have hM2' : ∀ z ∈ E', ∀ s : ℝ, s ≠ 0 → |s| < 1/((N:ℝ)+1) →
        ‖slope (fun t : ℝ => g (z+t)) 0 s - menchoffFx g z‖ < 1/((m:ℝ)+1) ∧
        ‖slope (fun t : ℝ => g (z+t*I)) 0 s - menchoffFy g z‖ < 1/((m:ℝ)+1) := by
      intro z hz s hs hsN
      have hbound := hM2E z hz.1 s (abs_pos.mpr hs) hsN
      exact ⟨(menchoff_enorm_lt_ofReal_iff _ _).mp hbound.1,
             (menchoff_enorm_lt_ofReal_iff _ _).mp hbound.2⟩
    have hE'E : E' ⊆ E := inter_subset_left
    obtain ⟨δ, hδ, hbnd⟩ := menchoff_M4_bound hgc hUo hopen_g hE'U hz0E' hM2'
      ((hCfxE.mono hE'E).continuousWithinAt hz0E')
      ((hCfyE.mono hE'E).continuousWithinAt hz0E')
      (menchoff_hDensHR hz0densH) (menchoff_hDensHL hz0densH)
      (menchoff_hDensVR hz0densV) (menchoff_hDensVL hz0densV)
    obtain ⟨ρ, hρ, hballU⟩ := Metric.isOpen_iff.mp hUo z0 hz0U
    refine ⟨min δ (ρ/2), lt_min hδ (by linarith), fun s t hs ht => ?_⟩
    have hs' : |s| < δ := lt_of_lt_of_le hs (min_le_left _ _)
    have ht' : |t| < δ := lt_of_lt_of_le ht (min_le_left _ _)
    have hzst : z0 + (s:ℂ) + (t:ℂ)*I ∈ openRect a b c d := by
      apply hballU
      rw [mem_ball, dist_eq_norm]
      have hb : ‖z0 + s + t*I - z0‖ ≤ |s| + |t| := by
        have heq : z0 + (s:ℂ) + (t:ℂ)*I - z0 = (s:ℂ) + (t:ℂ)*I := by ring
        rw [heq]
        calc ‖(s:ℂ)+(t:ℂ)*I‖ ≤ ‖(s:ℂ)‖ + ‖(t:ℂ)*I‖ := norm_add_le _ _
          _ = |s| + |t| := by simp
      have hst : |s| + |t| < ρ := by
        have hs2 : |s| < ρ/2 := lt_of_lt_of_le hs (min_le_right _ _)
        have ht2 : |t| < ρ/2 := lt_of_lt_of_le ht (min_le_right _ _)
        linarith
      linarith
    have heq1 : g (z0 + s + t*I) = f (z0 + s + t*I) := hgfU hzst
    have heq2 : g z0 = f z0 := hgfU hz0U
    have heq3 : menchoffFx g z0 = menchoffFx f z0 := hFxeq z0 hz0U
    have heq4 : menchoffFy g z0 = menchoffFy f z0 := hFyeq z0 hz0U
    have hfinal := hbnd s t hs' ht'
    rwa [heq1, heq2, heq3, heq4] at hfinal
  choose G hGU hGvol hGbound using hGgood
  set GOOD := {z | ∃ᶠ m in atTop, z ∈ G m} with hGOODdef
  have hnullGOOD : volume (closedRect a b c d \ GOOD) = 0 :=
    menchoff_null_compl_of_le (closedRect a b c d) G hGvol
  have hGOODdiff : ∀ z0 ∈ GOOD, DifferentiableAt ℝ f z0 := by
    intro z0 hz0
    have hz0U : z0 ∈ openRect a b c d := by
      obtain ⟨m, hm⟩ := hz0.exists
      exact hGU m hm
    have hbd : ∃ᶠ m : ℕ in atTop, ∃ δ > 0, ∀ s t : ℝ, |s| < δ → |t| < δ →
        ‖f (z0+s+t*I) - f z0 - menchoffFx f z0 * s - menchoffFy f z0 * t‖ ≤
          (6+‖menchoffFx f z0‖+‖menchoffFy f z0‖) * (1/((m:ℝ)+1)) * (|s|+|t|) :=
      hz0.mono (fun m hm => hGbound m z0 hm)
    exact (menchoff_hasFDerivAt_of_bound (f := f) (z0 := z0) (Fx := menchoffFx f z0)
      (Fy := menchoffFy f z0) (by positivity) hbd).differentiableAt
  have hglobal : ∀ᵐ z ∂ volume, z ∈ closedRect a b c d → DifferentiableAt ℝ f z := by
    rw [ae_iff]
    simp only [Classical.not_imp]
    have hsub : {z | z ∈ closedRect a b c d ∧ ¬ DifferentiableAt ℝ f z} ⊆
        closedRect a b c d \ GOOD := by
      rintro z ⟨hzR, hzD⟩
      exact ⟨hzR, fun hzGOOD => hzD (hGOODdiff z hzGOOD)⟩
    exact measure_mono_null hsub hnullGOOD
  have hUonly : ∀ᵐ z ∂ volume, z ∈ openRect a b c d → DifferentiableAt ℝ f z :=
    hglobal.mono (fun z hz hzU => hz (hUR hzU))
  exact (ae_restrict_iff' hUmeas).mpr hUonly

/-- The countable-cover assembly: glue `menchoff_ae_diff_openRect` over the rational open
rectangles covering `D` (same cover as `thm9_2_partials_ae` in S09). Relocated here (after
`menchoff_ae_diff_openRect`, which it calls) from the position of its stub in the pasted
interface above, to avoid a forward reference; its statement is unchanged. -/
theorem menchoff_M5 {f : ℂ → ℂ} {D D' : Set ℂ} (hD : IsOpen D) (hf : IsHomeomorphOnto f D D')
    (hpart : ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
      DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0) :
    ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ f z := by
  have hcover : D = ⋃ q : {q : ℚ × ℚ × ℚ × ℚ // (q.1 : ℝ) < q.2.1 ∧ (q.2.2.1 : ℝ) < q.2.2.2 ∧
      closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ D}, openRect q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 := by
    ext z
    constructor
    · intro hz
      obtain ⟨q, h1, h2, h3, h4⟩ := acl_exists_rat_rect hD hz
      exact mem_iUnion.2 ⟨⟨q, h1, h2, h3⟩, h4⟩
    · intro hz
      obtain ⟨q, hq⟩ := mem_iUnion.1 hz
      exact q.2.2.2 (acl_openRect_subset_closedRect le_rfl le_rfl le_rfl le_rfl hq)
  rw [hcover, ae_restrict_iUnion_iff]
  intro q
  exact menchoff_ae_diff_openRect hD hf.1 hf.2.1 q.2.1 q.2.2.1 q.2.2.2 hpart

/-- **Lemma 9.1** (Menchoff), verbatim from S09:1118. -/
theorem lemma9_1_menchoff {f : ℂ → ℂ} {D D' : Set ℂ} (hD : IsOpen D)
    (hf : IsHomeomorphOnto f D D')
    (hpart : ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
      DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0) :
    ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ f z :=
  menchoff_M5 hD hf hpart


/-- **Theorem 9.3**: a quasiconformal map is differentiable (as a function of `(x, y)`) almost
everywhere. -/
theorem thm9_3_differentiable_ae {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) :
    ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ f z :=
  lemma9_1_menchoff hf.1 hf.2.2.1 (thm9_2_partials_ae hf)

/-- **Definition 9.2** (`L_p` 广义导数).  `g` and `h` are the `L_p` generalized partial
derivatives of `f` with respect to `x` and `y` in `D`: they are locally `p`-integrable in `D`
and there are `C¹` functions `fₙ` converging to `f` locally uniformly in `D` whose partial
derivatives `(fₙ)'_x`, `(fₙ)'_y` converge to `g`, `h` in `L_p` on compact subsets of `D`. -/
def HasGenPartials (f g h : ℂ → ℂ) (D : Set ℂ) (p : ℝ≥0∞) : Prop :=
  (∀ C ⊆ D, IsCompact C → MemLp g p (volume.restrict C) ∧ MemLp h p (volume.restrict C)) ∧
    ∃ fn : ℕ → ℂ → ℂ, (∀ n, ContDiffOn ℝ 1 (fn n) D) ∧
      TendstoLocallyUniformlyOn fn f atTop D ∧
      ∀ C ⊆ D, IsCompact C →
        Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fn n) z 1 - g z) p (volume.restrict C))
            atTop (𝓝 0) ∧
          Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fn n) z I - h z) p (volume.restrict C))
            atTop (𝓝 0)

/-- `f` has `L_p` generalized derivatives in `D`. -/
def HasLpGenDeriv (f : ℂ → ℂ) (D : Set ℂ) (p : ℝ≥0∞) : Prop :=
  ∃ g h : ℂ → ℂ, HasGenPartials f g h D p

/-- The generalized formal derivatives `∂_z f = (g - i h)/2`, `∂_{z̄} f = (g + i h)/2` built from
generalized partial derivatives `g = f'_x`, `h = f'_y`. -/
def genDz (g h : ℂ → ℂ) (z : ℂ) : ℂ := (g z - I * h z) / 2

/-- See `genDz`. -/
def genDzbar (g h : ℂ → ℂ) (z : ℂ) : ℂ := (g z + I * h z) / 2

/-- Fubini's theorem on the open rectangle `(a, b) × (c, d)` (Bochner integral). -/
theorem setIntegral_openRect {g : ℂ → ℂ} {a b c d : ℝ} (hg : IntegrableOn g (openRect a b c d)) :
    ∫ z in openRect a b c d, g z =
      ∫ x in Ioo a b, ∫ y in Ioo c d, g ((x : ℂ) + (y : ℂ) * I) := by
  have he := Complex.measurableEquivRealProd.symm.measurableEmbedding
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' openRect a b c d = Ioo a b ×ˢ Ioo c d := by
    ext p
    simp [openRect, Complex.measurableEquivRealProd, and_assoc]
  have himg : Complex.measurableEquivRealProd.symm '' (Ioo a b ×ˢ Ioo c d) = openRect a b c d := by
    rw [← hpre, image_preimage_eq_of_subset]
    intro z _
    exact ⟨Complex.measurableEquivRealProd z, by simp⟩
  have hint : IntegrableOn (fun p => g (Complex.measurableEquivRealProd.symm p))
      (Ioo a b ×ˢ Ioo c d) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod, ← hpre]
    exact (he.integrableOn_map_iff).1 (by rw [hmp.map_eq]; exact hg)
  rw [← himg, hmp.setIntegral_image_emb he, Measure.volume_eq_prod, setIntegral_prod _ hint]
  refine setIntegral_congr_fun measurableSet_Ioo fun x _ =>
    setIntegral_congr_fun measurableSet_Ioo fun y _ => ?_
  congr 1
  apply Complex.ext <;> simp [Complex.measurableEquivRealProd]

/-- Fubini's theorem on `(a, b) × (c, d)`, integrating first in `x`. -/
theorem setIntegral_openRect_symm {g : ℂ → ℂ} {a b c d : ℝ}
    (hg : IntegrableOn g (openRect a b c d)) :
    ∫ z in openRect a b c d, g z =
      ∫ y in Ioo c d, ∫ x in Ioo a b, g ((x : ℂ) + (y : ℂ) * I) := by
  have he := Complex.measurableEquivRealProd.symm.measurableEmbedding
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' openRect a b c d = Ioo a b ×ˢ Ioo c d := by
    ext p
    simp [openRect, Complex.measurableEquivRealProd, and_assoc]
  have himg : Complex.measurableEquivRealProd.symm '' (Ioo a b ×ˢ Ioo c d) = openRect a b c d := by
    rw [← hpre, image_preimage_eq_of_subset]
    intro z _
    exact ⟨Complex.measurableEquivRealProd z, by simp⟩
  have hint : IntegrableOn (fun p => g (Complex.measurableEquivRealProd.symm p))
      (Ioo a b ×ˢ Ioo c d) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod, ← hpre]
    exact (he.integrableOn_map_iff).1 (by rw [hmp.map_eq]; exact hg)
  rw [← himg, hmp.setIntegral_image_emb he, Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_prod_symm _ (by rw [Measure.prod_restrict]; exact hint)]
  refine setIntegral_congr_fun measurableSet_Ioo fun y _ =>
    setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
  congr 1
  apply Complex.ext <;> simp [Complex.measurableEquivRealProd]

theorem isCompact_closedRect (a b c d : ℝ) : IsCompact (closedRect a b c d) := by
  have e : closedRect a b c d = Icc a b ×ℂ Icc c d := by
    ext z
    simp [closedRect, mem_reProdIm, and_assoc]
  rw [e]
  exact Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
    ((Metric.isBounded_Icc a b).reProdIm (Metric.isBounded_Icc c d))

/-- Green's formula (9.9) for an A.C.L. function with locally integrable partial derivatives:
`∫_{∂R} f dx = -∬_R f'_y dx dy`. -/
theorem eq9_9_green {f : ℂ → ℂ} {D : Set ℂ} (hf : IsACL f D)
    (hloc : ∀ C ⊆ D, IsCompact C → IntegrableOn (partialY f) C) {a b c d : ℝ} (hab : a < b)
    (hcd : c < d) (hR : closedRect a b c d ⊆ D) :
    (∫ x in a..b, f ((x : ℂ) + (c : ℂ) * I)) - (∫ x in a..b, f ((x : ℂ) + (d : ℂ) * I)) =
      -∫ z in openRect a b c d, partialY f z := by
  obtain ⟨hfc, hacl⟩ := hf
  obtain ⟨hvert, -⟩ := hacl a b c d hab hcd hR
  have hint : IntegrableOn (partialY f) (openRect a b c d) :=
    (hloc _ hR (isCompact_closedRect a b c d)).mono_set
      fun _ hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  -- the partial derivative is the derivative along the vertical line
  have hpY : ∀ x y : ℝ, partialY f ((x : ℂ) + (y : ℂ) * I) =
      deriv (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) y := by
    intro x y
    have e : (fun t : ℝ => f ((x : ℂ) + (y : ℂ) * I + (t : ℂ) * I)) =
        fun t : ℝ => (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (y + t) := by
      funext t
      congr 1
      push_cast
      ring
    show deriv (fun t : ℝ => f ((x : ℂ) + (y : ℂ) * I + (t : ℂ) * I)) 0 = _
    rw [e]
    exact (deriv_comp_const_add (f := fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (a := y)
      (x := 0)).trans (by rw [add_zero])
  -- (A.C.L.) the fundamental theorem of calculus on almost every vertical line
  have hline : ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)),
      ∫ y in Ioo c d, partialY f ((x : ℂ) + (y : ℂ) * I) =
        f ((x : ℂ) + (d : ℂ) * I) - f ((x : ℂ) + (c : ℂ) * I) := by
    filter_upwards [hvert] with x hx
    rw [← integral_deriv_eq_sub_of_absolutelyContinuous hx, intervalIntegral.integral_of_le hcd.le,
      integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun y _ => hpY x y
  have hcont : ∀ t ∈ Icc c d, ContinuousOn (fun x : ℝ => f ((x : ℂ) + (t : ℂ) * I)) (Icc a b) :=
    fun t ht => hfc.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (t : ℂ) * I).continuousOn
      fun x hx => hR ⟨by simpa using hx.1, by simpa using hx.2, by simpa using ht.1,
        by simpa using ht.2⟩
  rw [← intervalIntegral.integral_sub
      (ContinuousOn.intervalIntegrable_of_Icc hab.le (hcont c ⟨le_rfl, hcd.le⟩))
      (ContinuousOn.intervalIntegrable_of_Icc hab.le (hcont d ⟨hcd.le, le_rfl⟩)),
    setIntegral_openRect hint, intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo,
    ← integral_neg]
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  rw [ae_restrict_iff' measurableSet_Ioo] at hline
  filter_upwards [hline] with x hx hxI
  rw [hx hxI]
  ring

/-- Green's formula (9.10): `∫_{∂R} f dy = ∬_R f'_x dx dy`. -/
theorem eq9_10_green {f : ℂ → ℂ} {D : Set ℂ} (hf : IsACL f D)
    (hloc : ∀ C ⊆ D, IsCompact C → IntegrableOn (partialX f) C) {a b c d : ℝ} (hab : a < b)
    (hcd : c < d) (hR : closedRect a b c d ⊆ D) :
    (∫ y in c..d, f ((b : ℂ) + (y : ℂ) * I)) - (∫ y in c..d, f ((a : ℂ) + (y : ℂ) * I)) =
      ∫ z in openRect a b c d, partialX f z := by
  obtain ⟨hfc, hacl⟩ := hf
  obtain ⟨-, hhor⟩ := hacl a b c d hab hcd hR
  have hint : IntegrableOn (partialX f) (openRect a b c d) :=
    (hloc _ hR (isCompact_closedRect a b c d)).mono_set
      fun _ hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  -- the partial derivative is the derivative along the horizontal line
  have hpX : ∀ x y : ℝ, partialX f ((x : ℂ) + (y : ℂ) * I) =
      deriv (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) x := by
    intro x y
    have e : (fun t : ℝ => f ((x : ℂ) + (y : ℂ) * I + (t : ℂ))) =
        fun t : ℝ => (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (x + t) := by
      funext t
      congr 1
      push_cast
      ring
    show deriv (fun t : ℝ => f ((x : ℂ) + (y : ℂ) * I + (t : ℂ))) 0 = _
    rw [e]
    exact (deriv_comp_const_add (f := fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (a := x)
      (x := 0)).trans (by rw [add_zero])
  -- (A.C.L.) the fundamental theorem of calculus on almost every horizontal line
  have hline : ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)),
      ∫ x in Ioo a b, partialX f ((x : ℂ) + (y : ℂ) * I) =
        f ((b : ℂ) + (y : ℂ) * I) - f ((a : ℂ) + (y : ℂ) * I) := by
    filter_upwards [hhor] with y hy
    rw [← integral_deriv_eq_sub_of_absolutelyContinuous hy, intervalIntegral.integral_of_le hab.le,
      integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun x _ => hpX x y
  have hcont : ∀ s ∈ Icc a b, ContinuousOn (fun y : ℝ => f ((s : ℂ) + (y : ℂ) * I)) (Icc c d) :=
    fun s hs => hfc.comp (by fun_prop : Continuous fun y : ℝ => (s : ℂ) + (y : ℂ) * I).continuousOn
      fun y hy => hR ⟨by simpa using hs.1, by simpa using hs.2, by simpa using hy.1,
        by simpa using hy.2⟩
  rw [← intervalIntegral.integral_sub
      (ContinuousOn.intervalIntegrable_of_Icc hcd.le (hcont b ⟨hab.le, le_rfl⟩))
      (ContinuousOn.intervalIntegrable_of_Icc hcd.le (hcont a ⟨le_rfl, hab.le⟩)),
    setIntegral_openRect_symm hint, intervalIntegral.integral_of_le hcd.le,
    integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  rw [ae_restrict_iff' measurableSet_Ioo] at hline
  filter_upwards [hline] with y hy hyI
  rw [hy hyI]

/-- Absolute continuity on `uIcc a b` only depends on the values there. -/
theorem absolutelyContinuousOnInterval_congr {f g : ℝ → ℂ} {a b : ℝ} (hfg : EqOn f g (uIcc a b))
    (hf : AbsolutelyContinuousOnInterval f a b) : AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hf ε hε
  refine ⟨δ, hδ, fun E hE hsum => ?_⟩
  have h1 := h E hE hsum
  rwa [Finset.sum_congr rfl fun i hi => by rw [hfg (hE.1 i hi).1, hfg (hE.1 i hi).2]] at h1

theorem absolutelyContinuousOnInterval_const (C : ℂ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => C) a b := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  exact ⟨1, one_pos, fun E _ _ => by simpa using hε⟩

theorem absolutelyContinuousOnInterval_ofReal {u : ℝ → ℝ} {a b : ℝ}
    (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun x => (u x : ℂ)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hu ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hu ε hε
  refine ⟨δ, hδ, fun E hE hsum => ?_⟩
  have h1 := h E hE hsum
  have e : ∀ i ∈ Finset.range E.1, dist ((u (E.2 i).1 : ℂ)) ((u (E.2 i).2 : ℂ)) =
      dist (u (E.2 i).1) (u (E.2 i).2) := fun i _ => by
    rw [dist_eq_norm, ← ofReal_sub, norm_real, ← dist_eq_norm]
  rwa [Finset.sum_congr rfl e]

/-- The primitive of an integrable complex function is absolutely continuous. -/
theorem absolutelyContinuousOnInterval_intervalIntegral_complex {u : ℝ → ℂ} {a b c : ℝ}
    (hu : IntervalIntegrable u volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ v in c..x, u v) a b := by
  have hre : IntervalIntegrable (fun t => (u t).re) volume a b := ⟨hu.1.re, hu.2.re⟩
  have him : IntervalIntegrable (fun t => (u t).im) volume a b := ⟨hu.1.im, hu.2.im⟩
  have h := (absolutelyContinuousOnInterval_ofReal
    (hre.absolutelyContinuousOnInterval_intervalIntegral hc)).add
    ((absolutelyContinuousOnInterval_ofReal
      (him.absolutelyContinuousOnInterval_intervalIntegral hc)).const_smul I)
  refine absolutelyContinuousOnInterval_congr (fun x hx => ?_) h
  have hsub : IntervalIntegrable u volume c x := hu.mono_set (uIcc_subset_uIcc hc hx)
  have hr : (∫ v in c..x, u v).re = ∫ v in c..x, (u v).re := by
    simpa using (Complex.reCLM.intervalIntegral_comp_comm hsub).symm
  have hi : (∫ v in c..x, u v).im = ∫ v in c..x, (u v).im := by
    simpa using (Complex.imCLM.intervalIntegral_comp_comm hsub).symm
  apply Complex.ext <;> simp [hr, hi]

/-- Lebesgue's differentiation theorem for the primitive of an integrable complex function. -/
theorem ae_hasDerivAt_integral_complex {u : ℝ → ℂ} {c d : ℝ} (hcd : c ≤ d)
    (hu : IntervalIntegrable u volume c d) :
    ∀ᵐ y, y ∈ Ioo c d → HasDerivAt (fun y => ∫ t in c..y, u t) (u y) y := by
  have hre : IntervalIntegrable (fun t => (u t).re) volume c d := ⟨hu.1.re, hu.2.re⟩
  have him : IntervalIntegrable (fun t => (u t).im) volume c d := ⟨hu.1.im, hu.2.im⟩
  filter_upwards [hre.ae_hasDerivAt_integral, him.ae_hasDerivAt_integral] with y h1 h2 hy
  have hyI : y ∈ uIcc c d := by rw [uIcc_of_le hcd]; exact Ioo_subset_Icc_self hy
  have hcI : c ∈ uIcc c d := by rw [uIcc_of_le hcd]; exact ⟨le_rfl, hcd⟩
  have hd := ((h1 hyI c hcI).ofReal_comp).add (((h2 hyI c hcI).ofReal_comp).mul_const I)
  have hval : ((u y).re : ℂ) + ((u y).im : ℂ) * I = u y := Complex.re_add_im _
  rw [hval] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hy.1 hy.2] with t ht
  have htI : t ∈ uIcc c d := by rw [uIcc_of_le hcd]; exact Ioo_subset_Icc_self ht
  have hsub : IntervalIntegrable u volume c t := hu.mono_set (uIcc_subset_uIcc hcI htI)
  have hr : (∫ v in c..t, u v).re = ∫ v in c..t, (u v).re := by
    simpa using (Complex.reCLM.intervalIntegral_comp_comm hsub).symm
  have hi : (∫ v in c..t, u v).im = ∫ v in c..t, (u v).im := by
    simpa using (Complex.imCLM.intervalIntegral_comp_comm hsub).symm
  apply Complex.ext <;> simp [hr, hi]

theorem continuous_rectCoords : Continuous fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * I :=
  (Complex.continuous_ofReal.comp continuous_fst).add
    ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

theorem measurableEquivRealProd_symm_apply' (x y : ℝ) :
    Complex.measurableEquivRealProd.symm (x, y) = (x : ℂ) + (y : ℂ) * I := by
  apply Complex.ext <;> simp [Complex.measurableEquivRealProd]

theorem volume_restrict_openRect_eq_map (a b c d : ℝ) :
    volume.restrict (openRect a b c d) = Measure.map Complex.measurableEquivRealProd.symm
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))) := by
  have he := Complex.measurableEquivRealProd.symm.measurableEmbedding
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' openRect a b c d = Ioo a b ×ˢ Ioo c d := by
    ext p
    simp [openRect, Complex.measurableEquivRealProd, and_assoc]
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← hpre,
    (hmp.restrict_preimage_emb he (openRect a b c d)).map_eq]

/-- Tonelli's theorem on the open rectangle `(a, b) × (c, d)`. -/
theorem lintegral_openRect {a b c d : ℝ} {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z in openRect a b c d, F z =
      ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d, F ((x : ℂ) + (y : ℂ) * I) := by
  have he := Complex.measurableEquivRealProd.symm.measurableEmbedding
  rw [volume_restrict_openRect_eq_map, lintegral_map hF he.measurable,
    lintegral_prod (fun q => F (Complex.measurableEquivRealProd.symm q))
      (hF.comp he.measurable).aemeasurable]
  simp only [measurableEquivRealProd_symm_apply']

/-- Tonelli's theorem on `(a, b) × (c, d)`, integrating first in `x`. -/
theorem lintegral_openRect_symm {a b c d : ℝ} {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z in openRect a b c d, F z =
      ∫⁻ y in Ioo c d, ∫⁻ x in Ioo a b, F ((x : ℂ) + (y : ℂ) * I) := by
  rw [lintegral_openRect hF]
  exact lintegral_lintegral_swap (hF.comp continuous_rectCoords.measurable).aemeasurable

theorem ae_openRect_of_ae_ae {a b c d : ℝ} {P : ℂ → Prop} (hP : MeasurableSet {z | P z})
    (h : ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)), ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)),
      P ((x : ℂ) + (y : ℂ) * I)) :
    ∀ᵐ z ∂(volume.restrict (openRect a b c d)), P z := by
  have he := Complex.measurableEquivRealProd.symm.measurableEmbedding
  rw [volume_restrict_openRect_eq_map, ae_map_iff he.measurable.aemeasurable hP,
    Measure.ae_prod_iff_ae_ae (p := fun q => P (Complex.measurableEquivRealProd.symm q))
      (show MeasurableSet {q | P (Complex.measurableEquivRealProd.symm q)} from he.measurable hP)]
  simpa only [measurableEquivRealProd_symm_apply'] using h

theorem ae_openRect_of_ae_ae_symm {a b c d : ℝ} {P : ℂ → Prop} (hP : MeasurableSet {z | P z})
    (h : ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)), ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)),
      P ((x : ℂ) + (y : ℂ) * I)) :
    ∀ᵐ z ∂(volume.restrict (openRect a b c d)), P z :=
  ae_openRect_of_ae_ae hP ((Measure.ae_ae_comm (p := fun (x y : ℝ) => P ((x : ℂ) + (y : ℂ) * I))
    (continuous_rectCoords.measurable hP)).2 h)

/-- A property holding a.e. on every open rectangle whose closure lies in `D` holds a.e. on `D`. -/
theorem ae_restrict_of_forall_openRect {D : Set ℂ} (hD : IsOpen D) {P : ℂ → Prop}
    (h : ∀ a b c d : ℝ, a < b → c < d → closedRect a b c d ⊆ D →
      ∀ᵐ z ∂(volume.restrict (openRect a b c d)), P z) :
    ∀ᵐ z ∂(volume.restrict D), P z := by
  let S := {q : ℚ × ℚ × ℚ × ℚ // (q.1 : ℝ) < q.2.1 ∧ (q.2.2.1 : ℝ) < q.2.2.2 ∧
    closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ D}
  have hsub : D ⊆ ⋃ q : S, openRect q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 := by
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD z hz
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - ε / 2 < z.re by linarith)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.re < z.re + ε / 2 by linarith)
    obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (show z.im - ε / 2 < z.im by linarith)
    obtain ⟨d, hd1, hd2⟩ := exists_rat_btwn (show z.im < z.im + ε / 2 by linarith)
    have hR : closedRect a b c d ⊆ D := by
      intro w hw
      obtain ⟨h1, h2, h3, h4⟩ := hw
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖w - z‖ ≤ |(w - z).re| + |(w - z).im| := Complex.norm_le_abs_re_add_abs_im _
        _ < ε / 2 + ε / 2 := by
            rw [sub_re, sub_im]
            exact add_lt_add (abs_lt.2 ⟨by linarith, by linarith⟩)
              (abs_lt.2 ⟨by linarith, by linarith⟩)
        _ = ε := by ring
    exact mem_iUnion.2 ⟨⟨(a, b, c, d), ha2.trans hb1, hc2.trans hd1, hR⟩, ha2, hb1, hc2, hd1⟩
  refine ae_restrict_of_ae_restrict_of_subset hsub ?_
  rw [ae_restrict_iUnion_iff]
  exact fun q => h _ _ _ _ q.2.1 q.2.2.1 q.2.2.2

theorem partialX_ofReal_add (f : ℂ → ℂ) (x y : ℝ) :
    partialX f ((x : ℂ) + (y : ℂ) * I) = deriv (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) x := by
  have e : (fun t : ℝ => f ((x : ℂ) + (y : ℂ) * I + (t : ℂ))) =
      fun t : ℝ => (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (x + t) := by
    funext t
    congr 1
    push_cast
    ring
  show deriv (fun t : ℝ => f ((x : ℂ) + (y : ℂ) * I + (t : ℂ))) 0 = _
  rw [e]
  exact (deriv_comp_const_add (f := fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (a := x)
    (x := 0)).trans (by rw [add_zero])

theorem partialY_ofReal_add (f : ℂ → ℂ) (x y : ℝ) :
    partialY f ((x : ℂ) + (y : ℂ) * I) = deriv (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) y := by
  have e : (fun t : ℝ => f ((x : ℂ) + (y : ℂ) * I + (t : ℂ) * I)) =
      fun t : ℝ => (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (y + t) := by
    funext t
    congr 1
    push_cast
    ring
  show deriv (fun t : ℝ => f ((x : ℂ) + (y : ℂ) * I + (t : ℂ) * I)) 0 = _
  rw [e]
  exact (deriv_comp_const_add (f := fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (a := y)
    (x := 0)).trans (by rw [add_zero])

/-- The nearest point of `[a, b] × [c, d]` (coordinatewise clamp). -/
def rectClamp (a b c d : ℝ) (z : ℂ) : ℂ :=
  ((max a (min b z.re) : ℝ) : ℂ) + ((max c (min d z.im) : ℝ) : ℂ) * I

theorem continuous_rectClamp (a b c d : ℝ) : Continuous (rectClamp a b c d) := by
  unfold rectClamp
  exact (Complex.continuous_ofReal.comp (continuous_const.max (continuous_const.min
    Complex.continuous_re))).add ((Complex.continuous_ofReal.comp (continuous_const.max
      (continuous_const.min Complex.continuous_im))).mul continuous_const)

theorem rectClamp_mem {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (z : ℂ) :
    rectClamp a b c d z ∈ closedRect a b c d := by
  simp only [closedRect, rectClamp, mem_setOf_eq, add_re, ofReal_re, mul_re, I_re, mul_zero,
    ofReal_im, I_im, mul_one, sub_zero, add_zero, add_im, mul_im, zero_add]
  refine ⟨le_max_left _ _, max_le hab (min_le_left _ _), le_max_left _ _,
    max_le hcd (min_le_left _ _)⟩

theorem rectClamp_of_mem {a b c d : ℝ} {z : ℂ} (hz : z ∈ closedRect a b c d) :
    rectClamp a b c d z = z := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  unfold rectClamp
  rw [min_eq_right h2, max_eq_right h1, min_eq_right h4, max_eq_right h3]
  exact Complex.re_add_im z

theorem measurable_partialX_comp_rectClamp {f : ℂ → ℂ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f (closedRect a b c d)) :
    Measurable (partialX (f ∘ rectClamp a b c d)) := by
  have hc : Continuous (f ∘ rectClamp a b c d) :=
    hf.comp_continuous (continuous_rectClamp a b c d) (rectClamp_mem hab hcd)
  have hu : Continuous (fun p : ℂ × ℝ => (f ∘ rectClamp a b c d) (p.1 + (p.2 : ℂ))) :=
    hc.comp (continuous_fst.add (Complex.continuous_ofReal.comp continuous_snd))
  have hm := measurable_deriv_with_param (f := fun (z : ℂ) (t : ℝ) =>
    (f ∘ rectClamp a b c d) (z + (t : ℂ))) hu
  exact hm.comp (measurable_id.prodMk measurable_const)

theorem measurable_partialY_comp_rectClamp {f : ℂ → ℂ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f (closedRect a b c d)) :
    Measurable (partialY (f ∘ rectClamp a b c d)) := by
  have hc : Continuous (f ∘ rectClamp a b c d) :=
    hf.comp_continuous (continuous_rectClamp a b c d) (rectClamp_mem hab hcd)
  have hu : Continuous (fun p : ℂ × ℝ => (f ∘ rectClamp a b c d) (p.1 + (p.2 : ℂ) * I)) :=
    hc.comp (continuous_fst.add ((Complex.continuous_ofReal.comp continuous_snd).mul
      continuous_const))
  have hm := measurable_deriv_with_param (f := fun (z : ℂ) (t : ℝ) =>
    (f ∘ rectClamp a b c d) (z + (t : ℂ) * I)) hu
  exact hm.comp (measurable_id.prodMk measurable_const)

/-- The limiting step of Lemma 9.2 (⇐) along the parallel segments `t ↦ φ s t`, `t ∈ [c, d]`,
of direction `v`, lying in a compact `R ⊆ D`.  By Fatou's lemma, the `L¹` errors
`∫_c^d |∂_v f_n - k'|` along the segments have `liminf = 0` for almost every `s`, and on such a
segment the fundamental theorem of calculus for `f_n` passes to the limit. -/
theorem hasGenPartials_line_aux {f k k' : ℂ → ℂ} {D R : Set ℂ} (hD : IsOpen D) {p : ℝ≥0∞}
    (hp : 1 ≤ p) {fn : ℕ → ℂ → ℂ} (hfn : ∀ n, ContDiffOn ℝ 1 (fn n) D)
    (hconv : TendstoLocallyUniformlyOn fn f atTop D) (hRc : IsCompact R) (hR : R ⊆ D) {v : ℂ}
    (hk : MemLp k p (volume.restrict R))
    (hLp : Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fn n) z v - k z) p (volume.restrict R))
      atTop (𝓝 0))
    (hk'm : Measurable k') (hk' : k =ᵐ[volume.restrict R] k') {a b c d : ℝ} (hcd : c < d)
    {φ : ℝ → ℝ → ℂ} (hφc : Continuous (Function.uncurry φ))
    (hφR : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d, φ s t ∈ R) (hφd : ∀ s t, HasDerivAt (φ s) v t)
    (hφint : ∀ F : ℂ → ℝ≥0∞, Measurable F →
      ∫⁻ s in Ioo a b, ∫⁻ t in Ioo c d, F (φ s t) ≤ ∫⁻ z in R, F z) :
    ∀ᵐ (s : ℝ) ∂(volume.restrict (Ioo a b)),
      IntervalIntegrable (fun t => k' (φ s t)) volume c d ∧
      ∀ η ∈ Icc c d, f (φ s η) = f (φ s c) + ∫ t in c..η, k' (φ s t) := by
  have hφs : ∀ s, Continuous (φ s) := fun s => hφc.comp (Continuous.prodMk_right s)
  haveI : IsFiniteMeasure (volume.restrict R) := isFiniteMeasure_restrict.2 hRc.measure_lt_top.ne
  -- the errors along the segments
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ → ℝ≥0∞, e = fun n (s : ℝ) => ∫⁻ t in Ioo c d,
      ‖fderiv ℝ (fn n) (φ s t) v - k' (φ s t)‖ₑ := ⟨_, rfl⟩
  have hFm : ∀ n, Measurable fun z : ℂ => ‖fderiv ℝ (fn n) z v - k' z‖ₑ := fun n =>
    ((measurable_fderiv_apply_const ℝ (fn n) v).sub hk'm).enorm
  have hemeas : ∀ n, Measurable (e n) := fun n => by
    rw [he]
    exact ((hFm n).comp hφc.measurable).lintegral_prod_right'
  have hint_e : ∀ n, ∫⁻ s in Ioo a b, e n s ≤
      eLpNorm (fun z => fderiv ℝ (fn n) z v - k z) 1 (volume.restrict R) := by
    intro n
    have hmn : AEStronglyMeasurable (fun z => fderiv ℝ (fn n) z v - k z) (volume.restrict R) :=
      (measurable_fderiv_apply_const ℝ (fn n) v).aestronglyMeasurable.sub hk.aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm hmn]
    calc ∫⁻ s in Ioo a b, e n s ≤ ∫⁻ z in R, ‖fderiv ℝ (fn n) z v - k' z‖ₑ := by
          rw [he]
          exact hφint _ (hFm n)
      _ = ∫⁻ z in R, ‖fderiv ℝ (fn n) z v - k z‖ₑ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hk'] with z hz
          rw [hz]
  have hL1 : Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fn n) z v - k z) 1
      (volume.restrict R)) atTop (𝓝 0) := by
    have hmeas : ∀ n, AEStronglyMeasurable (fun z => fderiv ℝ (fn n) z v - k z)
        (volume.restrict R) := fun n =>
      (measurable_fderiv_apply_const ℝ (fn n) v).aestronglyMeasurable.sub hk.aestronglyMeasurable
    have hexp : 0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal := by
      rw [ENNReal.toReal_one, div_one, sub_nonneg]
      rcases eq_or_ne p ⊤ with rfl | hpt
      · simp
      · have h1 : 1 ≤ p.toReal := by
          rw [← ENNReal.toReal_one]
          exact ENNReal.toReal_mono hpt hp
        exact (div_le_one (by linarith)).2 h1
    have hC : (volume.restrict R) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top _ _)
    have h0 := ENNReal.Tendsto.mul_const hLp (Or.inr hC)
    rw [zero_mul] at h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun n => zero_le)
      fun n => eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (hmeas n)
  have hlim_e : Tendsto (fun n => ∫⁻ s in Ioo a b, e n s) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1 (fun n => zero_le) hint_e
  -- Fatou: `liminf e_n = 0` almost everywhere
  have hfatou := lintegral_liminf_le' (μ := volume.restrict (Ioo a b)) (u := atTop)
    fun n => (hemeas n).aemeasurable
  rw [hlim_e.liminf_eq] at hfatou
  have hzero : ∀ᵐ (s : ℝ) ∂(volume.restrict (Ioo a b)), liminf (fun n => e n s) atTop = 0 :=
    (lintegral_eq_zero_iff' (Measurable.liminf fun n => hemeas n).aemeasurable).1
      (le_antisymm hfatou zero_le)
  -- `k'` is integrable on almost every segment
  have hk'int : IntegrableOn k' R := (hk.integrable hp).congr hk'
  have hlineInt : ∀ᵐ (s : ℝ) ∂(volume.restrict (Ioo a b)),
      ∫⁻ t in Ioo c d, ‖k' (φ s t)‖ₑ < ⊤ := by
    have hfin : ∫⁻ s in Ioo a b, ∫⁻ t in Ioo c d, ‖k' (φ s t)‖ₑ < ⊤ :=
      lt_of_le_of_lt (hφint _ hk'm.enorm) hk'int.2
    exact ae_lt_top ((hk'm.enorm.comp hφc.measurable).lintegral_prod_right') hfin.ne
  -- the fundamental theorem of calculus for the approximations
  have hFTC : ∀ n, ∀ s ∈ Icc a b, ∀ η ∈ Icc c d,
      ContinuousOn (fun t => fderiv ℝ (fn n) (φ s t) v) (uIcc c η) ∧
      fn n (φ s η) - fn n (φ s c) = ∫ t in c..η, fderiv ℝ (fn n) (φ s t) v := by
    intro n s hs η hη
    have hcontD := (hfn n).continuousOn_fderiv_of_isOpen hD le_rfl
    have hmaps : ∀ t ∈ uIcc c η, φ s t ∈ D := fun t ht => by
      rw [uIcc_of_le hη.1] at ht
      exact hR (hφR s hs t ⟨ht.1, ht.2.trans hη.2⟩)
    have hderiv : ∀ t ∈ uIcc c η, HasDerivAt (fun t => fn n (φ s t))
        (fderiv ℝ (fn n) (φ s t) v) t := by
      intro t ht
      have hdiff : DifferentiableAt ℝ (fn n) (φ s t) :=
        ((hfn n).differentiableOn one_ne_zero _ (hmaps t ht)).differentiableAt
          (hD.mem_nhds (hmaps t ht))
      exact hdiff.hasFDerivAt.comp_hasDerivAt t (hφd s t)
    have hcont : ContinuousOn (fun t => fderiv ℝ (fn n) (φ s t) v) (uIcc c η) :=
      (hcontD.comp (hφs s).continuousOn hmaps).clm_apply continuousOn_const
    exact ⟨hcont,
      (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable).symm⟩
  filter_upwards [hzero, hlineInt, ae_restrict_mem measurableSet_Ioo] with s hs0 hsint hsab
  have hsI : IntervalIntegrable (fun t => k' (φ s t)) volume c d :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hcd.le).2
      ⟨(hk'm.comp (hφs s).measurable).aestronglyMeasurable, hsint⟩
  refine ⟨hsI, fun η hη => ?_⟩
  have hsIcc : s ∈ Icc a b := Ioo_subset_Icc_self hsab
  have hbound : ∀ n, ‖(fn n (φ s η) - fn n (φ s c)) - ∫ t in c..η, k' (φ s t)‖ₑ ≤ e n s := by
    intro n
    obtain ⟨hcont, hftc⟩ := hFTC n s hsIcc η hη
    have hsubI : IntervalIntegrable (fun t => k' (φ s t)) volume c η :=
      hsI.mono_set (by
        rw [uIcc_of_le hη.1, uIcc_of_le hcd.le]
        exact Icc_subset_Icc le_rfl hη.2)
    rw [hftc, ← intervalIntegral.integral_sub hcont.intervalIntegrable hsubI,
      intervalIntegral.integral_of_le hη.1, he]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ t in Ioc c η, ‖fderiv ℝ (fn n) (φ s t) v - k' (φ s t)‖ₑ
        ≤ ∫⁻ t in Ioc c d, ‖fderiv ℝ (fn n) (φ s t) v - k' (φ s t)‖ₑ :=
          lintegral_mono_set (Ioc_subset_Ioc le_rfl hη.2)
      _ = ∫⁻ t in Ioo c d, ‖fderiv ℝ (fn n) (φ s t) v - k' (φ s t)‖ₑ :=
          setLIntegral_congr Ioo_ae_eq_Ioc.symm
  have hηD : φ s η ∈ D := hR (hφR s hsIcc η hη)
  have hcD : φ s c ∈ D := hR (hφR s hsIcc c ⟨le_rfl, hcd.le⟩)
  have hlimF : Tendsto (fun n => ‖(fn n (φ s η) - fn n (φ s c)) - ∫ t in c..η, k' (φ s t)‖ₑ)
      atTop (𝓝 ‖(f (φ s η) - f (φ s c)) - ∫ t in c..η, k' (φ s t)‖ₑ) :=
    (((hconv.tendsto_at hηD).sub (hconv.tendsto_at hcD)).sub_const _).enorm
  have hle := liminf_le_liminf (f := atTop) (Filter.Eventually.of_forall hbound)
  rw [hlimF.liminf_eq, hs0] at hle
  have h0 := enorm_eq_zero.1 (le_antisymm hle zero_le)
  linear_combination h0

/-- Lemma 9.2 (⇐) along parallel segments: absolute continuity on almost every segment, and the
derivative along almost every segment is `k'` almost everywhere. -/
theorem hasGenPartials_line {f k k' : ℂ → ℂ} {D R : Set ℂ} (hD : IsOpen D) {p : ℝ≥0∞}
    (hp : 1 ≤ p) {fn : ℕ → ℂ → ℂ} (hfn : ∀ n, ContDiffOn ℝ 1 (fn n) D)
    (hconv : TendstoLocallyUniformlyOn fn f atTop D) (hRc : IsCompact R) (hR : R ⊆ D) {v : ℂ}
    (hk : MemLp k p (volume.restrict R))
    (hLp : Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fn n) z v - k z) p (volume.restrict R))
      atTop (𝓝 0))
    (hk'm : Measurable k') (hk' : k =ᵐ[volume.restrict R] k') {a b c d : ℝ} (hcd : c < d)
    {φ : ℝ → ℝ → ℂ} (hφc : Continuous (Function.uncurry φ))
    (hφR : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d, φ s t ∈ R) (hφd : ∀ s t, HasDerivAt (φ s) v t)
    (hφint : ∀ F : ℂ → ℝ≥0∞, Measurable F →
      ∫⁻ s in Ioo a b, ∫⁻ t in Ioo c d, F (φ s t) ≤ ∫⁻ z in R, F z) :
    (∀ᵐ (s : ℝ) ∂(volume.restrict (Ioo a b)),
      AbsolutelyContinuousOnInterval (fun t => f (φ s t)) c d) ∧
    ∀ᵐ (s : ℝ) ∂(volume.restrict (Ioo a b)), ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioo c d)),
      deriv (fun t => f (φ s t)) t = k' (φ s t) := by
  have hlines := hasGenPartials_line_aux hD hp hfn hconv hRc hR hk hLp hk'm hk' hcd hφc hφR hφd
    hφint
  refine ⟨?_, ?_⟩
  · filter_upwards [hlines] with s hs
    obtain ⟨hsI, hseq⟩ := hs
    have hcI : c ∈ uIcc c d := by rw [uIcc_of_le hcd.le]; exact ⟨le_rfl, hcd.le⟩
    refine absolutelyContinuousOnInterval_congr (fun t ht => ?_)
      ((absolutelyContinuousOnInterval_const (f (φ s c)) c d).add
        (absolutelyContinuousOnInterval_intervalIntegral_complex hsI hcI))
    rw [uIcc_of_le hcd.le] at ht
    exact (hseq t ht).symm
  · filter_upwards [hlines] with s hs
    obtain ⟨hsI, hseq⟩ := hs
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [ae_hasDerivAt_integral_complex hcd.le hsI] with t ht htI
    rw [← ((ht htI).const_add (f (φ s c))).deriv]
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioo_mem_nhds htI.1 htI.2] with u hu
    exact hseq u (Ioo_subset_Icc_self hu)

theorem mem_closedRect_of_mem_Icc {a b c d x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    (x : ℂ) + (y : ℂ) * I ∈ closedRect a b c d :=
  ⟨by simpa using hx.1, by simpa using hx.2, by simpa using hy.1, by simpa using hy.2⟩

/-- Lemma 9.2 (⇐) on vertical segments of a rectangle. -/
theorem hasGenPartials_vertical {f g h : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hf : HasGenPartials f g h D p) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hR : closedRect a b c d ⊆ D) :
    (∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)),
      AbsolutelyContinuousOnInterval (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) c d) ∧
    ∀ᵐ z ∂(volume.restrict (openRect a b c d)), partialY f z = h z := by
  obtain ⟨hloc, fn, hfn, hconv, hLp⟩ := hf
  have hRc := isCompact_closedRect a b c d
  have hfc : ContinuousOn f D :=
    hconv.continuousOn (Filter.Frequently.of_forall fun n => (hfn n).continuousOn)
  have hopenR : openRect a b c d ⊆ closedRect a b c d :=
    fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  have hRm : MeasurableSet (openRect a b c d) := by
    have e : openRect a b c d = Complex.re ⁻¹' Ioo a b ∩ Complex.im ⁻¹' Ioo c d := by
      ext z
      simp [openRect, and_assoc]
    rw [e]
    exact (measurableSet_Ioo.preimage Complex.measurable_re).inter
      (measurableSet_Ioo.preimage Complex.measurable_im)
  obtain ⟨h', hh'm, hh'⟩ : ∃ h' : ℂ → ℂ, Measurable h' ∧
      h =ᵐ[volume.restrict (closedRect a b c d)] h' :=
    ⟨_, (hloc _ hR hRc).2.aestronglyMeasurable.aemeasurable.measurable_mk, (hloc _ hR hRc).2.aestronglyMeasurable.aemeasurable.ae_eq_mk⟩
  have hl := hasGenPartials_line (φ := fun x y : ℝ => (x : ℂ) + (y : ℂ) * I) hD hp hfn hconv hRc
    hR (hloc _ hR hRc).2 (hLp _ hR hRc).2 hh'm hh' hcd continuous_rectCoords
    (fun x hx y hy => mem_closedRect_of_mem_Icc hx hy)
    (fun x y => by simpa using (((hasDerivAt_id (y : ℂ)).mul_const I).const_add (x : ℂ)).comp_ofReal)
    (fun F hF => by rw [← lintegral_openRect hF]; exact lintegral_mono_set hopenR)
  obtain ⟨hAC, hder⟩ := hl
  refine ⟨hAC, ?_⟩
  have hFm := measurable_partialY_comp_rectClamp hab.le hcd.le (hfc.mono hR)
  have hlocal : ∀ x ∈ Icc a b, ∀ y ∈ Ioo c d, partialY (f ∘ rectClamp a b c d)
      ((x : ℂ) + (y : ℂ) * I) = partialY f ((x : ℂ) + (y : ℂ) * I) := by
    intro x hx y hy
    rw [partialY_ofReal_add, partialY_ofReal_add]
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with t ht
    simp only [Function.comp_apply]
    rw [rectClamp_of_mem (mem_closedRect_of_mem_Icc hx (Ioo_subset_Icc_self ht))]
  have hae : ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)), ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)),
      partialY (f ∘ rectClamp a b c d) ((x : ℂ) + (y : ℂ) * I) = h' ((x : ℂ) + (y : ℂ) * I) := by
    filter_upwards [hder, ae_restrict_mem measurableSet_Ioo] with x hx hxab
    rw [ae_restrict_iff' measurableSet_Ioo] at hx ⊢
    filter_upwards [hx] with y hy hyI
    rw [hlocal x (Ioo_subset_Icc_self hxab) y hyI, partialY_ofReal_add]
    exact hy hyI
  have h2 := ae_openRect_of_ae_ae (measurableSet_eq_fun hFm hh'm) hae
  filter_upwards [h2, ae_restrict_of_ae_restrict_of_subset hopenR hh',
    ae_restrict_mem hRm] with z hz hz' hzR
  have hloc := hlocal z.re (Ioo_subset_Icc_self ⟨hzR.1, hzR.2.1⟩) z.im ⟨hzR.2.2.1, hzR.2.2.2⟩
  rw [Complex.re_add_im] at hloc
  rw [← hloc, hz, hz']

/-- Lemma 9.2 (⇐) on horizontal segments of a rectangle. -/
theorem hasGenPartials_horizontal {f g h : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hf : HasGenPartials f g h D p) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hR : closedRect a b c d ⊆ D) :
    (∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)),
      AbsolutelyContinuousOnInterval (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) a b) ∧
    ∀ᵐ z ∂(volume.restrict (openRect a b c d)), partialX f z = g z := by
  obtain ⟨hloc, fn, hfn, hconv, hLp⟩ := hf
  have hRc := isCompact_closedRect a b c d
  have hfc : ContinuousOn f D :=
    hconv.continuousOn (Filter.Frequently.of_forall fun n => (hfn n).continuousOn)
  have hopenR : openRect a b c d ⊆ closedRect a b c d :=
    fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  have hRm : MeasurableSet (openRect a b c d) := by
    have e : openRect a b c d = Complex.re ⁻¹' Ioo a b ∩ Complex.im ⁻¹' Ioo c d := by
      ext z
      simp [openRect, and_assoc]
    rw [e]
    exact (measurableSet_Ioo.preimage Complex.measurable_re).inter
      (measurableSet_Ioo.preimage Complex.measurable_im)
  obtain ⟨g', hg'm, hg'⟩ : ∃ g' : ℂ → ℂ, Measurable g' ∧
      g =ᵐ[volume.restrict (closedRect a b c d)] g' :=
    ⟨_, (hloc _ hR hRc).1.aestronglyMeasurable.aemeasurable.measurable_mk, (hloc _ hR hRc).1.aestronglyMeasurable.aemeasurable.ae_eq_mk⟩
  have hφc : Continuous (Function.uncurry fun y x : ℝ => (x : ℂ) + (y : ℂ) * I) :=
    (Complex.continuous_ofReal.comp continuous_snd).add
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)
  have hl := hasGenPartials_line (φ := fun y x : ℝ => (x : ℂ) + (y : ℂ) * I) hD hp hfn hconv hRc
    hR (hloc _ hR hRc).1 (hLp _ hR hRc).1 hg'm hg' hab hφc
    (fun y hy x hx => mem_closedRect_of_mem_Icc hx hy)
    (fun y x => by simpa using ((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * I)).comp_ofReal)
    (fun F hF => by rw [← lintegral_openRect_symm hF]; exact lintegral_mono_set hopenR)
  obtain ⟨hAC, hder⟩ := hl
  refine ⟨hAC, ?_⟩
  have hFm := measurable_partialX_comp_rectClamp hab.le hcd.le (hfc.mono hR)
  have hlocal : ∀ y ∈ Icc c d, ∀ x ∈ Ioo a b, partialX (f ∘ rectClamp a b c d)
      ((x : ℂ) + (y : ℂ) * I) = partialX f ((x : ℂ) + (y : ℂ) * I) := by
    intro y hy x hx
    rw [partialX_ofReal_add, partialX_ofReal_add]
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
    simp only [Function.comp_apply]
    rw [rectClamp_of_mem (mem_closedRect_of_mem_Icc (Ioo_subset_Icc_self ht) hy)]
  have hae : ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)), ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)),
      partialX (f ∘ rectClamp a b c d) ((x : ℂ) + (y : ℂ) * I) = g' ((x : ℂ) + (y : ℂ) * I) := by
    filter_upwards [hder, ae_restrict_mem measurableSet_Ioo] with y hy hycd
    rw [ae_restrict_iff' measurableSet_Ioo] at hy ⊢
    filter_upwards [hy] with x hx hxI
    rw [hlocal y (Ioo_subset_Icc_self hycd) x hxI, partialX_ofReal_add]
    exact hx hxI
  have h2 := ae_openRect_of_ae_ae_symm (measurableSet_eq_fun hFm hg'm) hae
  filter_upwards [h2, ae_restrict_of_ae_restrict_of_subset hopenR hg',
    ae_restrict_mem hRm] with z hz hz' hzR
  have hloc := hlocal z.im ⟨hzR.2.2.1.le, hzR.2.2.2.le⟩ z.re ⟨hzR.1, hzR.2.1⟩
  rw [Complex.re_add_im] at hloc
  rw [← hloc, hz, hz']

/-- Convolving with a probability density does not increase the `L_p` norm (`1 ≤ p < ∞`); the
pointwise estimate is Jensen's inequality for the measure `φ dt`. -/
theorem eLpNorm_convolution_le_of_lintegral_eq_one {φ : ℂ → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∫⁻ x, ENNReal.ofReal (φ x) = 1) {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F volume) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    eLpNorm (convolution φ F (ContinuousLinearMap.lsmul ℝ ℝ) volume) p volume ≤
      eLpNorm F p volume := by
  have hq : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp' hp
  have hq0 : 0 < p.toReal := by linarith
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  set ρ : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (φ x) with hρ
  have hρm : Measurable ρ := ENNReal.measurable_ofReal.comp hφm
  haveI : IsProbabilityMeasure (volume.withDensity ρ) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hφ1⟩
  have hpt : ∀ x, ‖convolution φ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ p.toReal ≤
      ∫⁻ t, ρ t * ‖F (x - t)‖ₑ ^ p.toReal := by
    intro x
    have hFx : AEStronglyMeasurable (fun t => F (x - t)) volume :=
      hF.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume x)
    have h1 : ‖convolution φ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ≤
        ∫⁻ t, ρ t * ‖F (x - t)‖ₑ := by
      rw [convolution_def]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun t => ?_))
      rw [ContinuousLinearMap.lsmul_apply, enorm_smul, Real.enorm_eq_ofReal (hφ0 t)]
    have hFxρ : AEStronglyMeasurable (fun t => F (x - t)) (volume.withDensity ρ) :=
      hFx.mono_ac (withDensity_absolutelyContinuous _ _)
    have h2 : eLpNorm (fun t => F (x - t)) 1 (volume.withDensity ρ) ≤
        eLpNorm (fun t => F (x - t)) p (volume.withDensity ρ) :=
      eLpNorm_le_eLpNorm_of_exponent_le hp
    rw [eLpNorm_one_eq_lintegral_enorm hFxρ, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hFxρ,
      lintegral_withDensity_eq_lintegral_mul₀ hρm.aemeasurable hFx.enorm,
      lintegral_withDensity_eq_lintegral_mul₀ hρm.aemeasurable (hFx.enorm.pow_const _)] at h2
    calc ‖convolution φ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ p.toReal
        ≤ (∫⁻ t, ρ t * ‖F (x - t)‖ₑ) ^ p.toReal := ENNReal.rpow_le_rpow h1 hq0.le
      _ ≤ ((∫⁻ t, ρ t * ‖F (x - t)‖ₑ ^ p.toReal) ^ (1 / p.toReal)) ^ p.toReal :=
          ENNReal.rpow_le_rpow h2 hq0.le
      _ = ∫⁻ t, ρ t * ‖F (x - t)‖ₑ ^ p.toReal := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
  have hmeas2 : AEMeasurable (Function.uncurry fun x t : ℂ => ρ t * ‖F (x - t)‖ₑ ^ p.toReal)
      (volume.prod volume) := by
    have h : AEStronglyMeasurable (fun q : ℂ × ℂ => F (q.1 - q.2)) (volume.prod volume) :=
      hF.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)
    exact (hρm.comp measurable_snd).aemeasurable.mul (h.enorm.pow_const _)
  have hint : ∫⁻ x, ‖convolution φ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ p.toReal ≤
      ∫⁻ x, ‖F x‖ₑ ^ p.toReal :=
    calc ∫⁻ x, ‖convolution φ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ p.toReal
        ≤ ∫⁻ x, ∫⁻ t, ρ t * ‖F (x - t)‖ₑ ^ p.toReal := lintegral_mono hpt
      _ = ∫⁻ t, ∫⁻ x, ρ t * ‖F (x - t)‖ₑ ^ p.toReal := lintegral_lintegral_swap hmeas2
      _ = ∫⁻ t, ρ t * ∫⁻ x, ‖F x‖ₑ ^ p.toReal := by
          refine lintegral_congr fun t => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_sub_right_eq_self (fun x => ‖F x‖ₑ ^ p.toReal) t]
      _ = ∫⁻ x, ‖F x‖ₑ ^ p.toReal := by rw [lintegral_mul_const _ hρm, hφ1, one_mul]
  have hconvm : AEStronglyMeasurable (convolution φ F (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      volume :=
    (hφm.aestronglyMeasurable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ)
      hF).integral_prod_right'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hconvm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hF]
  exact ENNReal.rpow_le_rpow hint (by positivity)

/-- Mollifiers form an approximate identity in `L_p` (`1 ≤ p < ∞`), measured on a set of finite
measure. -/
theorem tendsto_eLpNorm_convolution_normed_sub {b : ℕ → ContDiffBump (0 : ℂ)}
    (hb : Tendsto (fun n => (b n).rOut) atTop (𝓝 0)) {F : ℂ → ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp' : p ≠ ⊤) (hF : MemLp F p volume) {C : Set ℂ} (hC : volume C ≠ ⊤) :
    Tendsto (fun n => eLpNorm (fun z => convolution ((b n).normed volume) F
      (ContinuousLinearMap.lsmul ℝ ℝ) volume z - F z) p (volume.restrict C)) atTop (𝓝 0) := by
  haveI : IsFiniteMeasure (volume.restrict C) := isFiniteMeasure_restrict.2 hC
  have hyoung : ∀ n (G : ℂ → ℂ), AEStronglyMeasurable G volume →
      eLpNorm (convolution ((b n).normed volume) G (ContinuousLinearMap.lsmul ℝ ℝ) volume) p
        volume ≤ eLpNorm G p volume := fun n G hG =>
    eLpNorm_convolution_le_of_lintegral_eq_one (b n).continuous_normed.measurable
      (fun x => (b n).nonneg_normed x)
      (by rw [← ofReal_integral_eq_lintegral_ofReal (b n).integrable_normed
          (Eventually.of_forall fun x => (b n).nonneg_normed x), (b n).integral_normed,
          ENNReal.ofReal_one]) hG hp hp'
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' (by norm_num)).ne'
  obtain ⟨H, hHc, hFH, hHcont, -⟩ := hF.exists_hasCompactSupport_eLpNorm_sub_le hp' hε3
  have hunif : ∀ᶠ n in atTop, eLpNorm (fun z => convolution ((b n).normed volume) H
      (ContinuousLinearMap.lsmul ℝ ℝ) volume z - H z) p (volume.restrict C) ≤ ε / 3 := by
    obtain ⟨κ, hκε, hκ⟩ : ∃ κ : ℝ,
        (volume.restrict C) univ ^ p.toReal⁻¹ * ENNReal.ofReal κ ≤ ε / 3 ∧ 0 < κ := by
      have hM : (volume.restrict C) univ ^ p.toReal⁻¹ ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)
      have ht : Tendsto (fun κ : ℝ => (volume.restrict C) univ ^ p.toReal⁻¹ * ENNReal.ofReal κ)
          (𝓝[>] 0) (𝓝 0) := by
        have h := ENNReal.Tendsto.const_mul
          (ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ)))) (Or.inr hM)
        rw [ENNReal.ofReal_zero, mul_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      exact ((ht.eventually (ge_mem_nhds (pos_iff_ne_zero.2 hε3))).and
        self_mem_nhdsWithin).exists
    obtain ⟨ρ, hρ, hρH⟩ :=
      Metric.uniformContinuous_iff.1 (hHc.uniformContinuous_of_continuous hHcont) κ hκ
    filter_upwards [hb.eventually (gt_mem_nhds hρ)] with n hn
    have hHm : AEStronglyMeasurable (fun z => convolution ((b n).normed volume) H
        (ContinuousLinearMap.lsmul ℝ ℝ) volume z - H z) (volume.restrict C) :=
      (((b n).hasCompactSupport_normed.continuous_convolution_left _
        (b n).continuous_normed hHcont.locallyIntegrable).sub hHcont).aestronglyMeasurable
    refine (eLpNorm_le_of_ae_bound (C := κ) hHm (Eventually.of_forall fun z => ?_)).trans hκε
    rw [← dist_eq_norm]
    exact dist_convolution_le hκ.le (b n).support_normed_eq.subset (b n).nonneg_normed
      (b n).integral_normed hHcont.aestronglyMeasurable
      fun x hx => (hρH (lt_trans (mem_ball.1 hx) hn)).le
  filter_upwards [hunif] with n hn
  have hFloc : LocallyIntegrable F volume := hF.locallyIntegrable hp
  have hHloc : LocallyIntegrable H volume := hHcont.locallyIntegrable
  have hex : ∀ G : ℂ → ℂ, LocallyIntegrable G volume →
      ConvolutionExists ((b n).normed volume) G (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    fun G hG => (b n).hasCompactSupport_normed.convolutionExists_left _
      (b n).continuous_normed hG
  have hdist : convolution ((b n).normed volume) F (ContinuousLinearMap.lsmul ℝ ℝ) volume =
      convolution ((b n).normed volume) (F - H) (ContinuousLinearMap.lsmul ℝ ℝ) volume +
        convolution ((b n).normed volume) H (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    rw [← (hex _ (hFloc.sub hHloc)).distrib_add (hex _ hHloc), sub_add_cancel]
  set A := convolution ((b n).normed volume) (F - H) (ContinuousLinearMap.lsmul ℝ ℝ) volume
    with hA
  set B : ℂ → ℂ := fun z => convolution ((b n).normed volume) H
    (ContinuousLinearMap.lsmul ℝ ℝ) volume z - H z with hB
  have heq : (fun z => convolution ((b n).normed volume) F (ContinuousLinearMap.lsmul ℝ ℝ) volume z
      - F z) = A + B + (H - F) := by
    funext z
    have h := congrFun hdist z
    simp only [Pi.add_apply, Pi.sub_apply, hB] at h ⊢
    rw [h]
    ring
  have h1 : eLpNorm A p (volume.restrict C) ≤ ε / 3 :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      ((hyoung n _ (hF.aestronglyMeasurable.sub hHcont.aestronglyMeasurable)).trans hFH)
  have h3 : eLpNorm (H - F) p (volume.restrict C) ≤ ε / 3 := by
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    rw [eLpNorm_sub_comm]
    exact hFH
  rw [heq]
  calc eLpNorm (A + B + (H - F)) p (volume.restrict C)
      ≤ eLpNorm (A + B) p (volume.restrict C) + eLpNorm (H - F) p (volume.restrict C) :=
        eLpNorm_add_le hp
    _ ≤ eLpNorm A p (volume.restrict C) + eLpNorm B p (volume.restrict C) +
          eLpNorm (H - F) p (volume.restrict C) :=
        add_le_add (eLpNorm_add_le (f := A) (g := B) hp) le_rfl
    _ ≤ ε / 3 + ε / 3 + ε / 3 := add_le_add (add_le_add h1 hn) h3
    _ = ε := ENNReal.add_thirds ε

/-- The mollifier of radius `1 / (n + 1)` used in Lemma 9.2 (⇒). -/
def lemma92Bump (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) h]
    linarith

/-- The compact exhaustion `Kₙ = {|z| ≤ n, dist(z, ∁D) ≥ 1/(n+1)}` of `D`. -/
def lemma92Exhaust (D : Set ℂ) (n : ℕ) : Set ℂ :=
  closedBall 0 n ∩ (thickening (1 / ((n : ℝ) + 1)) Dᶜ)ᶜ

theorem isCompact_lemma92Exhaust (D : Set ℂ) (n : ℕ) : IsCompact (lemma92Exhaust D n) :=
  (isCompact_closedBall 0 (n : ℝ)).inter_right isOpen_thickening.isClosed_compl

theorem lemma92Exhaust_subset (D : Set ℂ) (n : ℕ) : lemma92Exhaust D n ⊆ D := by
  intro z hz
  by_contra h
  exact hz.2 (self_subset_thickening (by positivity) _ h)

/-- The approximations `fₙ = φₙ ⋆ (1_{Kₙ} f)` of Lemma 9.2 (⇒). -/
def lemma92Approx (D : Set ℂ) (f : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  convolution ((lemma92Bump n).normed volume) ((lemma92Exhaust D n).indicator f)
    (ContinuousLinearMap.lsmul ℝ ℝ) volume

theorem lemma92_eventually {D C : Set ℂ} (hD : IsOpen D) (hC : IsCompact C) (hCD : C ⊆ D) :
    ∃ δ > 0, cthickening (2 * δ) C ⊆ D ∧ ∀ᶠ n : ℕ in atTop,
      1 / ((n : ℝ) + 1) < δ ∧ cthickening δ C ⊆ lemma92Exhaust D n := by
  obtain ⟨δ₀, hδ₀, hsub⟩ := hC.exists_thickening_subset_open hD hCD
  refine ⟨δ₀ / 4, by positivity,
    (cthickening_subset_thickening' hδ₀ (by linarith) C).trans hsub, ?_⟩
  obtain ⟨N, hN⟩ := (hC.cthickening (r := δ₀ / 4)).isBounded.subset_closedBall 0
  have hr := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  filter_upwards [hr.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ₀ / 4)),
    eventually_ge_atTop ⌈N⌉₊] with n hn hnN
  refine ⟨hn, fun w hw => ⟨?_, fun hw' => ?_⟩⟩
  · rw [mem_closedBall]
    exact (mem_closedBall.1 (hN hw)).trans ((Nat.le_ceil N).trans (by exact_mod_cast hnN))
  · obtain ⟨y, hy, hwy⟩ := mem_thickening_iff.1 hw'
    apply hy
    apply hsub
    have h1 : y ∈ thickening (1 / ((n : ℝ) + 1)) (cthickening (δ₀ / 4) C) :=
      mem_thickening_iff.2 ⟨w, hw, by rw [dist_comm]; exact hwy⟩
    have h2 := thickening_cthickening_subset (1 / ((n : ℝ) + 1))
      (by positivity : (0 : ℝ) ≤ δ₀ / 4) C h1
    exact thickening_mono (by linarith) C h2

theorem integrable_indicator_lemma92Exhaust {D : Set ℂ} {f : ℂ → ℂ} (hf : ContinuousOn f D)
    (n : ℕ) : Integrable ((lemma92Exhaust D n).indicator f) volume :=
  (integrable_indicator_iff (isCompact_lemma92Exhaust D n).measurableSet).2
    ((hf.mono (lemma92Exhaust_subset D n)).integrableOn_compact (isCompact_lemma92Exhaust D n))

theorem contDiff_lemma92Approx {D : Set ℂ} {f : ℂ → ℂ} (hf : ContinuousOn f D) (n : ℕ) :
    ContDiff ℝ 1 (lemma92Approx D f n) :=
  (lemma92Bump n).hasCompactSupport_normed.contDiff_convolution_left _
    (lemma92Bump n).contDiff_normed (integrable_indicator_lemma92Exhaust hf n).locallyIntegrable

theorem tendstoLocallyUniformlyOn_lemma92Approx {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : ContinuousOn f D) : TendstoLocallyUniformlyOn (lemma92Approx D f) f atTop D := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hD]
  intro C hCD hC
  obtain ⟨δ, hδ, hδD, hev⟩ := lemma92_eventually hD hC hCD
  have hKc : IsCompact (cthickening δ C) := hC.cthickening
  have hKD : cthickening δ C ⊆ D := (cthickening_mono (by linarith) C).trans hδD
  have huc := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous (hf.mono hKD))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨η, hη, hηf⟩ := huc (ε / 2) (by positivity)
  have hr := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  filter_upwards [hev, hr.eventually (gt_mem_nhds hη)] with n hn hnη z hz
  obtain ⟨hnδ, hnK⟩ := hn
  rw [dist_comm]
  refine lt_of_le_of_lt (dist_convolution_le (by positivity : (0 : ℝ) ≤ ε / 2)
    (lemma92Bump n).support_normed_eq.subset (lemma92Bump n).nonneg_normed
    (lemma92Bump n).integral_normed
    (integrable_indicator_lemma92Exhaust hf n).aestronglyMeasurable fun x hx => ?_) (by linarith)
  have hxz : dist x z < 1 / ((n : ℝ) + 1) := mem_ball.1 hx
  have hzK : z ∈ cthickening δ C := self_subset_cthickening C hz
  have hxK : x ∈ cthickening δ C := mem_cthickening_of_dist_le x z δ C hz (hxz.le.trans hnδ.le)
  rw [indicator_of_mem (hnK hxK)]
  exact (hηf x hxK z hzK (hxz.trans hnη)).le

theorem absolutelyContinuousOnInterval_re {G : ℝ → ℂ} {a b : ℝ}
    (hG : AbsolutelyContinuousOnInterval G a b) :
    AbsolutelyContinuousOnInterval (fun x => (G x).re) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hG ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hG ε hε
  refine ⟨δ, hδ, fun E hE hsum => lt_of_le_of_lt (Finset.sum_le_sum fun i _ => ?_) (h E hE hsum)⟩
  rw [Real.dist_eq, dist_eq_norm, ← Complex.sub_re]
  exact Complex.abs_re_le_norm _

theorem absolutelyContinuousOnInterval_im {G : ℝ → ℂ} {a b : ℝ}
    (hG : AbsolutelyContinuousOnInterval G a b) :
    AbsolutelyContinuousOnInterval (fun x => (G x).im) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hG ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hG ε hε
  refine ⟨δ, hδ, fun E hE hsum => lt_of_le_of_lt (Finset.sum_le_sum fun i _ => ?_) (h E hE hsum)⟩
  rw [Real.dist_eq, dist_eq_norm, ← Complex.sub_im]
  exact Complex.abs_im_le_norm _

theorem ae_hasDerivAt_of_absolutelyContinuousOnInterval_complex {G : ℝ → ℂ} {a b : ℝ}
    (hG : AbsolutelyContinuousOnInterval G a b) :
    ∀ᵐ x, x ∈ uIcc a b → HasDerivAt G (((deriv (fun x => (G x).re) x : ℝ) : ℂ) +
      ((deriv (fun x => (G x).im) x : ℝ) : ℂ) * I) x := by
  filter_upwards [(absolutelyContinuousOnInterval_re hG).ae_differentiableAt,
    (absolutelyContinuousOnInterval_im hG).ae_differentiableAt] with x h1 h2 hx
  have hd := ((h1 hx).hasDerivAt.ofReal_comp).add (((h2 hx).hasDerivAt.ofReal_comp).mul_const I)
  convert hd using 1
  funext t
  exact (Complex.re_add_im (G t)).symm

theorem intervalIntegrable_deriv_of_absolutelyContinuousOnInterval_complex {G : ℝ → ℂ}
    {a b : ℝ} (hG : AbsolutelyContinuousOnInterval G a b) :
    IntervalIntegrable (deriv G) volume a b := by
  have h1 := (absolutelyContinuousOnInterval_re hG).intervalIntegrable_deriv
  have h2 := (absolutelyContinuousOnInterval_im hG).intervalIntegrable_deriv
  have hi : IntervalIntegrable (fun x => ((deriv (fun x => (G x).re) x : ℝ) : ℂ) +
      ((deriv (fun x => (G x).im) x : ℝ) : ℂ) * I) volume a b :=
    (IntervalIntegrable.add (⟨h1.1.ofReal, h1.2.ofReal⟩ : IntervalIntegrable
      (fun x => ((deriv (fun x => (G x).re) x : ℝ) : ℂ)) volume a b)
      (IntervalIntegrable.mul_const (⟨h2.1.ofReal, h2.2.ofReal⟩ : IntervalIntegrable
        (fun x => ((deriv (fun x => (G x).im) x : ℝ) : ℂ)) volume a b) I))
  rw [intervalIntegrable_iff] at hi ⊢
  refine hi.congr_fun_ae ((ae_restrict_iff' measurableSet_uIoc).2 ?_)
  filter_upwards [ae_hasDerivAt_of_absolutelyContinuousOnInterval_complex hG] with x hx hxI
  exact (hx (uIoc_subset_uIcc hxI)).deriv.symm

/-- Integration by parts against a `C¹` real function vanishing at both ends, for an absolutely
continuous complex function. -/
theorem intervalIntegral_smul_eq_neg_smul_deriv {u u' : ℝ → ℝ} {G : ℝ → ℂ} {a b : ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u')
    (hG : AbsolutelyContinuousOnInterval G a b) (ha : u a = 0) (hb : u b = 0) :
    ∫ x in a..b, u' x • G x = -∫ x in a..b, u x • deriv G x := by
  have hre := absolutelyContinuousOnInterval_re hG
  have him := absolutelyContinuousOnInterval_im hG
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn (hu'.continuousOn (s := uIcc a b))
  have hLip : LipschitzOnWith (Real.toNNReal C) u (uIcc a b) :=
    (convex_uIcc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (hu x).hasDerivWithinAt) fun x hx => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
        exact le_max_of_le_left (hC x hx)
  have huac := hLip.absolutelyContinuousOnInterval
  have hderu : deriv u = u' := funext fun x => (hu x).deriv
  have hr := huac.integral_mul_deriv_eq_deriv_mul hre
  have hi := huac.integral_mul_deriv_eq_deriv_mul him
  rw [hderu, ha, hb, zero_mul, zero_mul, sub_zero, zero_sub] at hr hi
  have hucont : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  have hI1 : IntervalIntegrable (fun x => u' x • G x) volume a b :=
    (hu'.continuousOn.smul hG.continuousOn).intervalIntegrable
  have hI2 : IntervalIntegrable (fun x => u x • deriv G x) volume a b := by
    have h := (intervalIntegrable_deriv_of_absolutelyContinuousOnInterval_complex hG).continuousOn_mul
      (Complex.continuous_ofReal.comp hucont).continuousOn
    simpa only [Function.comp_apply, Complex.real_smul] using h
  have hreI : ∀ {F : ℝ → ℂ}, IntervalIntegrable F volume a b →
      (∫ x in a..b, F x).re = ∫ x in a..b, (F x).re := fun hF => by
    simpa using (Complex.reCLM.intervalIntegral_comp_comm hF).symm
  have himI : ∀ {F : ℝ → ℂ}, IntervalIntegrable F volume a b →
      (∫ x in a..b, F x).im = ∫ x in a..b, (F x).im := fun hF => by
    simpa using (Complex.imCLM.intervalIntegral_comp_comm hF).symm
  have hae := ae_hasDerivAt_of_absolutelyContinuousOnInterval_complex hG
  have hre2 : ∫ x in a..b, u x * deriv (fun x => (G x).re) x =
      ∫ x in a..b, (u x • deriv G x).re := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with x hx hxI
    rw [(hx (uIoc_subset_uIcc hxI)).deriv]
    simp
  have him2 : ∫ x in a..b, u x * deriv (fun x => (G x).im) x =
      ∫ x in a..b, (u x • deriv G x).im := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with x hx hxI
    rw [(hx (uIoc_subset_uIcc hxI)).deriv]
    simp
  apply Complex.ext
  · rw [hreI hI1, Complex.neg_re, hreI hI2, ← hre2, hr, neg_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp
  · rw [himI hI1, Complex.neg_im, himI hI2, ← him2, hi, neg_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp

theorem lemma92Bump_normed_eq_zero {n : ℕ} {x : ℂ} (hx : 1 / ((n : ℝ) + 1) ≤ ‖x‖) :
    (lemma92Bump n).normed volume x = 0 := by
  by_contra h
  have h' : x ∈ ball (0 : ℂ) (lemma92Bump n).rOut := by
    rw [← (lemma92Bump n).support_normed_eq (μ := volume)]
    exact h
  rw [mem_ball, dist_zero_right] at h'
  exact absurd hx (not_le.2 h')

theorem fderiv_lemma92Approx_apply {D : Set ℂ} {f : ℂ → ℂ} (hf : ContinuousOn f D) (n : ℕ)
    (z v : ℂ) : fderiv ℝ (lemma92Approx D f n) z v =
      ∫ t, fderiv ℝ ((lemma92Bump n).normed volume) t v •
        (lemma92Exhaust D n).indicator f (z - t) := by
  have hg := (integrable_indicator_lemma92Exhaust hf n).locallyIntegrable
  have hd := (lemma92Bump n).hasCompactSupport_normed.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) ((lemma92Bump n).contDiff_normed (μ := volume) (n := 1)) hg z
  have hex := ((lemma92Bump n).hasCompactSupport_normed.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ)
    (((lemma92Bump n).contDiff_normed (μ := volume) (n := 1)).continuous_fderiv one_ne_zero) hg z
  unfold lemma92Approx
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex]
  simp

/-- Integration by parts on vertical segments of a rectangle, for an A.C.L. function and a `C¹`
function vanishing on the horizontal sides. -/
theorem lemma92_ibp_vertical {f : ℂ → ℂ} {D : Set ℂ} (hf : IsACL f D) {a b c d : ℝ} (hab : a < b)
    (hcd : c < d) (hR : closedRect a b c d ⊆ D)
    (hint : IntegrableOn (partialY f) (closedRect a b c d)) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : ∀ x : ℝ, ψ ((x : ℂ) + (c : ℂ) * I) = 0)
    (hψd : ∀ x : ℝ, ψ ((x : ℂ) + (d : ℂ) * I) = 0) :
    ∫ w in openRect a b c d, fderiv ℝ ψ w I • f w =
      -∫ w in openRect a b c d, ψ w • partialY f w := by
  have hopenR : openRect a b c d ⊆ closedRect a b c d :=
    fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  have hRc := isCompact_closedRect a b c d
  have hcontd : Continuous fun w => fderiv ℝ ψ w I :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint1 : IntegrableOn (fun w => fderiv ℝ ψ w I • f w) (openRect a b c d) :=
    ((hcontd.continuousOn.smul (hf.1.mono hR)).integrableOn_compact hRc).mono_set hopenR
  have hint2 : IntegrableOn (fun w => ψ w • partialY f w) (openRect a b c d) :=
    (hint.continuousOn_smul hψ.continuous.continuousOn hRc).mono_set hopenR
  rw [setIntegral_openRect hint1, setIntegral_openRect hint2, ← integral_neg]
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 (hf.2 a b c d hab hcd hR).1]
    with x hx hxI
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) I t := fun t => by
    simpa using (((hasDerivAt_id (t : ℂ)).mul_const I).const_add (x : ℂ)).comp_ofReal
  have hu : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ψ ((x : ℂ) + (t : ℂ) * I))
      (fderiv ℝ ψ ((x : ℂ) + (t : ℂ) * I) I) t := fun t =>
    ((hψ.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t (hline t)
  have h := intervalIntegral_smul_eq_neg_smul_deriv (u' := fun t => fderiv ℝ ψ ((x : ℂ) + (t : ℂ) * I) I)
    hu (hcontd.comp (by fun_prop : Continuous fun t : ℝ => (x : ℂ) + (t : ℂ) * I)) (hx hxI)
    (hψc x) (hψd x)
  simp only [← partialY_ofReal_add] at h
  rwa [intervalIntegral.integral_of_le hcd.le, intervalIntegral.integral_of_le hcd.le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at h

/-- Integration by parts on horizontal segments of a rectangle, for an A.C.L. function and a `C¹`
function vanishing on the vertical sides. -/
theorem lemma92_ibp_horizontal {f : ℂ → ℂ} {D : Set ℂ} (hf : IsACL f D) {a b c d : ℝ} (hab : a < b)
    (hcd : c < d) (hR : closedRect a b c d ⊆ D)
    (hint : IntegrableOn (partialX f) (closedRect a b c d)) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψa : ∀ y : ℝ, ψ ((a : ℂ) + (y : ℂ) * I) = 0)
    (hψb : ∀ y : ℝ, ψ ((b : ℂ) + (y : ℂ) * I) = 0) :
    ∫ w in openRect a b c d, fderiv ℝ ψ w 1 • f w =
      -∫ w in openRect a b c d, ψ w • partialX f w := by
  have hopenR : openRect a b c d ⊆ closedRect a b c d :=
    fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  have hRc := isCompact_closedRect a b c d
  have hcontd : Continuous fun w => fderiv ℝ ψ w 1 :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint1 : IntegrableOn (fun w => fderiv ℝ ψ w 1 • f w) (openRect a b c d) :=
    ((hcontd.continuousOn.smul (hf.1.mono hR)).integrableOn_compact hRc).mono_set hopenR
  have hint2 : IntegrableOn (fun w => ψ w • partialX f w) (openRect a b c d) :=
    (hint.continuousOn_smul hψ.continuous.continuousOn hRc).mono_set hopenR
  rw [setIntegral_openRect_symm hint1, setIntegral_openRect_symm hint2, ← integral_neg]
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 (hf.2 a b c d hab hcd hR).2]
    with y hy hyI
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) + (y : ℂ) * I) 1 t := fun t => by
    simpa using ((hasDerivAt_id (t : ℂ)).add_const ((y : ℂ) * I)).comp_ofReal
  have hu : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ψ ((t : ℂ) + (y : ℂ) * I))
      (fderiv ℝ ψ ((t : ℂ) + (y : ℂ) * I) 1) t := fun t =>
    ((hψ.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t (hline t)
  have h := intervalIntegral_smul_eq_neg_smul_deriv (u' := fun t => fderiv ℝ ψ ((t : ℂ) + (y : ℂ) * I) 1)
    hu (hcontd.comp (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + (y : ℂ) * I)) (hy hyI)
    (hψa y) (hψb y)
  simp only [← partialX_ofReal_add] at h
  rwa [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at h

theorem fderiv_lemma92Approx_eq {f dF : ℂ → ℂ} {D C : Set ℂ} (hf : ContinuousOn f D) {δ : ℝ}
    {n : ℕ} (hn : 1 / ((n : ℝ) + 1) < δ) (hK : cthickening δ C ⊆ lemma92Exhaust D n) {z : ℂ}
    (hz : z ∈ C) (v : ℂ)
    (hibp : ∫ w in openRect (z.re - δ) (z.re + δ) (z.im - δ) (z.im + δ),
        fderiv ℝ (fun w => (lemma92Bump n).normed volume (z - w)) w v • f w =
      -∫ w in openRect (z.re - δ) (z.re + δ) (z.im - δ) (z.im + δ),
        (lemma92Bump n).normed volume (z - w) • dF w) :
    fderiv ℝ (lemma92Approx D f n) z v =
      convolution ((lemma92Bump n).normed volume) ((cthickening δ C).indicator dF)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
  set φ := (lemma92Bump n).normed volume with hφ
  set S := openRect (z.re - δ) (z.re + δ) (z.im - δ) (z.im + δ) with hS
  have hSm : MeasurableSet S := by
    have e : S = Complex.re ⁻¹' Ioo (z.re - δ) (z.re + δ) ∩
        Complex.im ⁻¹' Ioo (z.im - δ) (z.im + δ) := by
      ext w
      simp [hS, openRect, and_assoc]
    rw [e]
    exact (measurableSet_Ioo.preimage Complex.measurable_re).inter
      (measurableSet_Ioo.preimage Complex.measurable_im)
  have hdiffφ : Differentiable ℝ φ :=
    ((lemma92Bump n).contDiff_normed (μ := volume) (n := 1)).differentiable one_ne_zero
  have hψ : ∀ w, fderiv ℝ (fun w => φ (z - w)) w v = -(fderiv ℝ φ (z - w) v) := by
    intro w
    have h : HasFDerivAt (fun w => φ (z - w))
        ((fderiv ℝ φ (z - w)).comp (-ContinuousLinearMap.id ℝ ℂ)) w :=
      (hdiffφ (z - w)).hasFDerivAt.comp w ((hasFDerivAt_id w).const_sub z)
    rw [h.fderiv]
    simp
  have hK2 : ∀ w, φ (z - w) ≠ 0 → dist w z < 1 / ((n : ℝ) + 1) := by
    intro w hw
    by_contra h
    rw [not_lt, dist_eq_norm, ← norm_neg, neg_sub] at h
    exact hw (lemma92Bump_normed_eq_zero h)
  have hK1 : ∀ w, fderiv ℝ φ (z - w) ≠ 0 → dist w z ≤ 1 / ((n : ℝ) + 1) := by
    intro w hw
    have h : z - w ∈ closedBall (0 : ℂ) (lemma92Bump n).rOut := by
      rw [← (lemma92Bump n).tsupport_normed_eq (μ := volume)]
      exact support_fderiv_subset (𝕜 := ℝ) hw
    rw [mem_closedBall, dist_zero_right, ← norm_neg, neg_sub, ← dist_eq_norm] at h
    exact h
  have hS1 : ∀ w, dist w z < δ → w ∈ S := by
    intro w hw
    rw [dist_eq_norm] at hw
    have h1 : |w.re - z.re| < δ := by
      rw [← sub_re]
      exact lt_of_le_of_lt (Complex.abs_re_le_norm _) hw
    have h2 : |w.im - z.im| < δ := by
      rw [← sub_im]
      exact lt_of_le_of_lt (Complex.abs_im_le_norm _) hw
    rw [abs_lt] at h1 h2
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hC1 : ∀ w, dist w z ≤ 1 / ((n : ℝ) + 1) → w ∈ lemma92Exhaust D n := fun w hw =>
    hK (mem_cthickening_of_dist_le w z δ C hz (hw.trans hn.le))
  rw [fderiv_lemma92Approx_apply hf n z v]
  calc ∫ t, fderiv ℝ φ t v • (lemma92Exhaust D n).indicator f (z - t)
      = ∫ w, fderiv ℝ φ (z - w) v • (lemma92Exhaust D n).indicator f w := by
        rw [← integral_sub_left_eq_self
          (fun w => fderiv ℝ φ (z - w) v • (lemma92Exhaust D n).indicator f w) volume z]
        simp only [sub_sub_cancel]
    _ = ∫ w in S, fderiv ℝ φ (z - w) v • f w := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S)
          (f := fun w => fderiv ℝ φ (z - w) v • (lemma92Exhaust D n).indicator f w) fun w hw => ?_]
        · refine setIntegral_congr_fun hSm fun w _ => ?_
          by_cases h : fderiv ℝ φ (z - w) = 0
          · simp [h]
          · rw [indicator_of_mem (hC1 w (hK1 w h))]
        · by_contra h
          have h' : fderiv ℝ φ (z - w) ≠ 0 := fun h0 => h (by simp [h0])
          exact hw (hS1 w ((hK1 w h').trans_lt hn))
    _ = -∫ w in S, fderiv ℝ (fun w => φ (z - w)) w v • f w := by
        rw [← integral_neg]
        refine setIntegral_congr_fun hSm fun w _ => ?_
        rw [hψ, neg_smul, neg_neg]
    _ = ∫ w in S, φ (z - w) • dF w := by rw [hibp, neg_neg]
    _ = ∫ w, φ (z - w) • (cthickening δ C).indicator dF w := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S)
          (f := fun w => φ (z - w) • (cthickening δ C).indicator dF w) fun w hw => ?_]
        · refine setIntegral_congr_fun hSm fun w _ => ?_
          by_cases h : φ (z - w) = 0
          · simp [h]
          · rw [indicator_of_mem (mem_cthickening_of_dist_le w z δ C hz
              ((hK2 w h).le.trans hn.le))]
        · by_contra h
          have h' : φ (z - w) ≠ 0 := fun h0 => h (by simp [h0])
          exact hw (hS1 w ((hK2 w h').trans hn))
    _ = ∫ t, φ t • (cthickening δ C).indicator dF (z - t) := by
        rw [← integral_sub_left_eq_self
          (fun t => φ t • (cthickening δ C).indicator dF (z - t)) volume z]
        simp only [sub_sub_cancel]
    _ = convolution φ ((cthickening δ C).indicator dF) (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
        rw [convolution_def]
        simp only [ContinuousLinearMap.lsmul_apply]

/-- **Lemma 9.2** (⇒).  An A.C.L. function whose partial derivatives are locally
`p`-integrable (`p ≥ 1`) has `L_p` generalized partial derivatives, equal to the classical
ones.

The proof follows the book's mollifier argument.  Take `fₙ = φₙ ⋆ (1_{Kₙ} f)`, with bumps `φₙ` of
radius `1/(n+1)` and a compact exhaustion `Kₙ` of `D` (`lemma92Approx`).  These maps are `C¹` and
converge locally uniformly to `f`.  Near each compact set, `∂fₙ = φₙ ⋆ ∂f`
(`fderiv_lemma92Approx_eq`), by integration by parts on almost every segment, where `f` is
absolutely continuous; this segment-wise integration by parts replaces the Green formula used in
the book.  Finally, mollifiers are an approximate identity in `L_p`
(`tendsto_eLpNorm_convolution_normed_sub`, via Jensen's inequality and density of `C_c`). -/
theorem lemma9_2_genPartials_of_isACL {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hf : IsACL f D)
    (hloc : ∀ C ⊆ D, IsCompact C →
      MemLp (partialX f) p (volume.restrict C) ∧ MemLp (partialY f) p (volume.restrict C)) :
    HasGenPartials f (partialX f) (partialY f) D p := by
  refine ⟨hloc, lemma92Approx D f, fun n => (contDiff_lemma92Approx hf.1 n).contDiffOn,
    tendstoLocallyUniformlyOn_lemma92Approx hD hf.1, fun C hCD hC => ?_⟩
  obtain ⟨δ, hδ, hδD, hev⟩ := lemma92_eventually hD hC hCD
  have hKc : IsCompact (cthickening δ C) := hC.cthickening
  have hKD : cthickening δ C ⊆ D := (cthickening_mono (by linarith) C).trans hδD
  have hb : Tendsto (fun n => (lemma92Bump n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsq : ∀ z ∈ C, closedRect (z.re - δ) (z.re + δ) (z.im - δ) (z.im + δ) ⊆ D := by
    intro z hz w hw
    apply hδD
    refine mem_cthickening_of_dist_le w z (2 * δ) C hz ?_
    rw [dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    obtain ⟨h1, h2, h3, h4⟩ := hw
    rw [sub_re, sub_im]
    have e1 : |w.re - z.re| ≤ δ := abs_le.2 ⟨by linarith, by linarith⟩
    have e2 : |w.im - z.im| ≤ δ := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hsqint : ∀ z ∈ C,
      IntegrableOn (partialX f) (closedRect (z.re - δ) (z.re + δ) (z.im - δ) (z.im + δ)) ∧
      IntegrableOn (partialY f) (closedRect (z.re - δ) (z.re + δ) (z.im - δ) (z.im + δ)) := by
    intro z hz
    have hRc := isCompact_closedRect (z.re - δ) (z.re + δ) (z.im - δ) (z.im + δ)
    haveI : IsFiniteMeasure
        (volume.restrict (closedRect (z.re - δ) (z.re + δ) (z.im - δ) (z.im + δ))) :=
      isFiniteMeasure_restrict.2 hRc.measure_lt_top.ne
    exact ⟨(hloc _ (hsq z hz) hRc).1.integrable hp, (hloc _ (hsq z hz) hRc).2.integrable hp⟩
  have hψ : ∀ (n : ℕ) (z : ℂ), ContDiff ℝ 1 fun w => (lemma92Bump n).normed volume (z - w) :=
    fun n z => ((lemma92Bump n).contDiff_normed (μ := volume) (n := 1)).comp
      (contDiff_const.sub contDiff_id)
  refine ⟨?_, ?_⟩
  · have hG : MemLp ((cthickening δ C).indicator (partialX f)) p volume :=
      (memLp_indicator_iff_restrict hKc.measurableSet).2 (hloc _ hKD hKc).1
    refine (tendsto_eLpNorm_convolution_normed_sub hb hp hp' hG hC.measure_lt_top.ne).congr' ?_
    filter_upwards [hev] with n hn
    obtain ⟨hnδ, hnK⟩ := hn
    refine eLpNorm_congr_ae ((ae_restrict_iff' hC.measurableSet).2
      (Eventually.of_forall fun z hz => ?_))
    have hibp := lemma92_ibp_horizontal hf (a := z.re - δ) (b := z.re + δ) (c := z.im - δ)
      (d := z.im + δ) (by linarith) (by linarith) (hsq z hz) (hsqint z hz).1 (hψ n z)
      (fun y => lemma92Bump_normed_eq_zero (hnδ.le.trans (by
        calc δ = |(z - (((z.re - δ : ℝ) : ℂ) + (y : ℂ) * I)).re| := by simp [abs_of_pos hδ]
          _ ≤ _ := Complex.abs_re_le_norm _)))
      (fun y => lemma92Bump_normed_eq_zero (hnδ.le.trans (by
        calc δ = |(z - (((z.re + δ : ℝ) : ℂ) + (y : ℂ) * I)).re| := by simp [abs_of_pos hδ]
          _ ≤ _ := Complex.abs_re_le_norm _)))
    beta_reduce
    rw [indicator_of_mem (self_subset_cthickening C hz),
      ← fderiv_lemma92Approx_eq hf.1 hnδ hnK hz 1 hibp]
  · have hG : MemLp ((cthickening δ C).indicator (partialY f)) p volume :=
      (memLp_indicator_iff_restrict hKc.measurableSet).2 (hloc _ hKD hKc).2
    refine (tendsto_eLpNorm_convolution_normed_sub hb hp hp' hG hC.measure_lt_top.ne).congr' ?_
    filter_upwards [hev] with n hn
    obtain ⟨hnδ, hnK⟩ := hn
    refine eLpNorm_congr_ae ((ae_restrict_iff' hC.measurableSet).2
      (Eventually.of_forall fun z hz => ?_))
    have hibp := lemma92_ibp_vertical hf (a := z.re - δ) (b := z.re + δ) (c := z.im - δ)
      (d := z.im + δ) (by linarith) (by linarith) (hsq z hz) (hsqint z hz).2 (hψ n z)
      (fun x => lemma92Bump_normed_eq_zero (hnδ.le.trans (by
        calc δ = |(z - ((x : ℂ) + ((z.im - δ : ℝ) : ℂ) * I)).im| := by simp [abs_of_pos hδ]
          _ ≤ _ := Complex.abs_im_le_norm _)))
      (fun x => lemma92Bump_normed_eq_zero (hnδ.le.trans (by
        calc δ = |(z - ((x : ℂ) + ((z.im + δ : ℝ) : ℂ) * I)).im| := by simp [abs_of_pos hδ]
          _ ≤ _ := Complex.abs_im_le_norm _)))
    beta_reduce
    rw [indicator_of_mem (self_subset_cthickening C hz),
      ← fderiv_lemma92Approx_eq hf.1 hnδ hnK hz I hibp]

/-- **Lemma 9.2** (⇐).  A function with `L_p` generalized partial derivatives (`p ≥ 1`) is
A.C.L., and its classical partial derivatives agree a.e. with the generalized ones.

The book passes to the limit in the classical Green formula for the approximating `C¹` maps and
then uses a dense set of lines and Lebesgue's differentiation theorem for indefinite integrals.
Here the limit is taken segment by segment: by Fatou's lemma the `L¹` errors of `∂f_n` along
almost every segment have `liminf = 0`, so on that segment `f` is the indefinite integral of (a
measurable version of) the generalized derivative (`hasGenPartials_line_aux`).  Absolute
continuity and Lebesgue's differentiation theorem then give both claims on every rectangle, and
a countable cover by rational rectangles gives them on `D`. -/
theorem lemma9_2_isACL_of_genPartials {f g h : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hf : HasGenPartials f g h D p) :
    IsACL f D ∧ (∀ᵐ z ∂(volume.restrict D), partialX f z = g z) ∧
      ∀ᵐ z ∂(volume.restrict D), partialY f z = h z := by
  have hfc : ContinuousOn f D := by
    obtain ⟨-, fn, hfn, hconv, -⟩ := hf
    exact hconv.continuousOn (Filter.Frequently.of_forall fun n => (hfn n).continuousOn)
  exact ⟨⟨hfc, fun a b c d hab hcd hR => ⟨(hasGenPartials_vertical hD hp hf hab hcd hR).1,
      (hasGenPartials_horizontal hD hp hf hab hcd hR).1⟩⟩,
    ae_restrict_of_forall_openRect hD fun a b c d hab hcd hR =>
      (hasGenPartials_horizontal hD hp hf hab hcd hR).2,
    ae_restrict_of_forall_openRect hD fun a b c d hab hcd hR =>
      (hasGenPartials_vertical hD hp hf hab hcd hR).2⟩

/-! ### Theorem 9.6 track — helpers of piece T -/


/-- **T2.** A `K`-q.c. real-linear map `ζ ↦ a ζ + b ζ̄` of the unit disc satisfies
`|a| + |b| ≤ K (|a| − |b|)`. -/
theorem ac_t_dilatation_of_isKQC_linear {a b : ℂ} {K : ℝ}
    (hA : IsKQC (fun ζ => a * ζ + b * (starRingEnd ℂ) ζ) (ball (0 : ℂ) 1) K) :
    ‖a‖ + ‖b‖ ≤ K * (‖a‖ - ‖b‖) := by
  set A : ℂ → ℂ := fun ζ => a * ζ + b * (starRingEnd ℂ) ζ with hAdef
  have hAinj : InjOn A (ball (0:ℂ) 1) := hA.2.2.1.2.1
  have hA0 : A 0 = 0 := by rw [hAdef]; simp
  -- Orientation: `‖b‖ < ‖a‖`.
  have horient : ‖b‖ < ‖a‖ := by
    by_contra hcon
    push Not at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt
    · -- ‖a‖ = ‖b‖: `A` is not injective.
      exfalso
      by_cases hb0 : b = 0
      · have ha0 : a = 0 := by
          have h1 : ‖a‖ = 0 := by rw [heq, hb0]; simp
          exact norm_eq_zero.mp h1
        have hA14 : A ((1:ℂ)/4) = 0 := by rw [hAdef]; simp [ha0, hb0]
        have h14 : ((1:ℂ)/4 : ℂ) ∈ ball (0:ℂ) 1 := by
          rw [mem_ball, dist_eq_norm]; norm_num
        have hcontra := hAinj (mem_ball_self one_pos) h14 (hA0.trans hA14.symm)
        norm_num at hcontra
      · have ha0 : a ≠ 0 := by
          intro ha0
          apply hb0
          have h1 : ‖b‖ = 0 := by rw [← heq, ha0]; simp
          exact norm_eq_zero.mp h1
        obtain ⟨ζ₀, hζ₀sq⟩ := IsAlgClosed.exists_pow_nat_eq (-b / a) (n := 2) (by norm_num)
        have hbnorm : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb0
        have hζ₀norm : ‖ζ₀‖ = 1 := by
          have h1 : ‖ζ₀‖ ^ 2 = ‖(-b / a : ℂ)‖ := by
            rw [← hζ₀sq, norm_pow]
          rw [norm_div, norm_neg, heq, div_self hbnorm] at h1
          nlinarith [h1, norm_nonneg ζ₀]
        have hζ₀ne0 : ζ₀ ≠ 0 := by
          intro h; rw [h] at hζ₀norm; simp at hζ₀norm
        have hζ₀barinv : (starRingEnd ℂ) ζ₀ = 1 / ζ₀ := by
          have h1 : ζ₀ * (starRingEnd ℂ) ζ₀ = ((‖ζ₀‖ : ℝ) : ℂ) ^ 2 :=
            Complex.mul_conj' ζ₀
          rw [hζ₀norm] at h1
          simp only [Complex.ofReal_one, one_pow] at h1
          field_simp
          linear_combination h1
        have hAζ₀ : a * ζ₀ + b * (starRingEnd ℂ) ζ₀ = 0 := by
          rw [hζ₀barinv]
          have hsq : a * ζ₀ ^ 2 = -b := by
            have h2 : a * (-b / a) = -b := by field_simp
            rw [hζ₀sq]; exact h2
          field_simp
          linear_combination hsq
        set ζ : ℂ := ζ₀ / 2 with hζdef
        have hζne0 : ζ ≠ 0 := by
          rw [hζdef]; simp [hζ₀ne0]
        have hζmem : ζ ∈ ball (0:ℂ) 1 := by
          rw [mem_ball, dist_eq_norm, hζdef, sub_zero, norm_div, hζ₀norm]
          norm_num
        have hζbar : (starRingEnd ℂ) ζ = (starRingEnd ℂ) ζ₀ / 2 := by
          rw [hζdef, map_div₀, show (starRingEnd ℂ) (2 : ℂ) = 2 from map_ofNat _ 2]
        have hAζ : A ζ = 0 := by
          rw [hAdef]
          show a * ζ + b * (starRingEnd ℂ) ζ = 0
          rw [hζdef, hζbar]
          linear_combination hAζ₀ / 2
        have hcontra := hAinj (mem_ball_self one_pos) hζmem (hA0.trans hAζ.symm)
        exact hζne0 hcontra.symm
    · -- ‖a‖ < ‖b‖: the loop `A(e^{2πit})` winds `-1`, contradicting `qcl_r_hloc_of_isKQC`'s `+1`.
      exfalso
      have hbne0 : b ≠ 0 := by
        intro hb0; rw [hb0] at hlt; simp at hlt; linarith [norm_nonneg a]
      obtain ⟨ρ₁, hρ₁pos, hloc⟩ := qcl_r_hloc_of_isKQC hA (mem_ball_self one_pos)
      set ρ : ℝ := ρ₁ / 2 with hρdef
      have hρpos : 0 < ρ := by rw [hρdef]; positivity
      have hρlt : ρ < ρ₁ := by rw [hρdef]; linarith
      set w : ℝ → ℂ := fun t => a * Complex.exp (4 * π * I * (t:ℂ)) + b with hwdef
      have hexp1 : ∀ t : ℝ, ‖Complex.exp (4 * π * I * (t:ℂ))‖ = 1 := by
        intro t
        rw [Complex.norm_exp]
        have h0 : (4 * π * I * (t:ℂ)).re = 0 := by simp
        rw [h0, Real.exp_zero]
      have hwslit : ∀ t : ℝ, w t / b ∈ Complex.slitPlane := by
        intro t
        have hlt1 : ‖w t / b - 1‖ < 1 := by
          have heq1 : w t / b - 1 = a * Complex.exp (4 * π * I * (t:ℂ)) / b := by
            rw [hwdef]; field_simp; ring
          rw [heq1, norm_div, norm_mul, hexp1, mul_one, div_lt_one (norm_pos_iff.2 hbne0)]
          exact hlt
        have h2 := Complex.mem_slitPlane_of_norm_lt_one hlt1
        rwa [show (1:ℂ) + (w t / b - 1) = w t / b from by ring] at h2
      have hwne0 : ∀ t : ℝ, w t / b ≠ 0 := fun t => Complex.slitPlane_ne_zero (hwslit t)
      set L₂ : ℝ → ℂ := fun t => Complex.log (w t / b) with hL₂def
      have hwcont : ContinuousOn (fun t : ℝ => w t / b) (Icc (0:ℝ) 1) := by
        have h1 : Continuous (fun t : ℝ => w t / b) := by
          rw [hwdef]; fun_prop
        exact h1.continuousOn
      have hL₂cont : ContinuousOn L₂ (Icc (0:ℝ) 1) := by
        rw [hL₂def]
        exact ContinuousOn.clog hwcont (fun t _ => hwslit t)
      have hL₂exp : ∀ t : ℝ, Complex.exp (L₂ t) = w t / b := by
        intro t
        rw [hL₂def]
        exact Complex.exp_log (hwne0 t)
      have hw1w0 : w 1 = w 0 := by
        rw [hwdef]
        show a * Complex.exp (4 * π * I * (1:ℂ)) + b = a * Complex.exp (4 * π * I * (0:ℂ)) + b
        congr 2
        rw [show (4 * π * I * (1:ℂ)) = 2 * π * I + 2 * π * I by ring, Complex.exp_add,
          Complex.exp_two_pi_mul_I, show (4 * π * I * (0:ℂ)) = 0 by ring, Complex.exp_zero]
        ring
      have hL₂10 : L₂ 1 = L₂ 0 := by rw [hL₂def]; simp only; rw [hw1w0]
      set L : ℝ → ℂ := fun t => ((Real.log ρ : ℝ) : ℂ) + (-(2 * π * I * (t:ℂ))) +
        Complex.log b + L₂ t with hLdef
      have hLcont : ContinuousOn L (Icc (0:ℝ) 1) := by
        have hcontpart : Continuous (fun t : ℝ => ((Real.log ρ : ℝ) : ℂ) +
            (-(2 * π * I * (t:ℂ))) + Complex.log b) := by fun_prop
        rw [hLdef]
        exact hcontpart.continuousOn.add hL₂cont
      have hLexp : ∀ t ∈ Icc (0:ℝ) 1,
          Complex.exp (L t) = A (0 + ρ * Complex.exp (2 * π * I * t)) - A 0 := by
        intro t _
        rw [hLdef, hA0, sub_zero, zero_add]
        show Complex.exp (((Real.log ρ:ℝ):ℂ) + (-(2*π*I*(t:ℂ))) + Complex.log b + L₂ t) =
          A (ρ * Complex.exp (2*π*I*(t:ℂ)))
        rw [hAdef]
        show Complex.exp (((Real.log ρ:ℝ):ℂ) + (-(2*π*I*(t:ℂ))) + Complex.log b + L₂ t) =
          a * (ρ * Complex.exp (2*π*I*(t:ℂ))) +
            b * (starRingEnd ℂ) (ρ * Complex.exp (2*π*I*(t:ℂ)))
        have hexpsplit3 : Complex.exp (((Real.log ρ:ℝ):ℂ) + (-(2*π*I*(t:ℂ))) + Complex.log b +
            L₂ t) = Complex.exp ((Real.log ρ:ℝ):ℂ) * Complex.exp (-(2*π*I*(t:ℂ))) *
              Complex.exp (Complex.log b) * Complex.exp (L₂ t) := by
          rw [Complex.exp_add, Complex.exp_add, Complex.exp_add]
        rw [hexpsplit3]
        have hρexp : Complex.exp ((Real.log ρ:ℝ):ℂ) = (ρ:ℂ) := by
          rw [← Complex.ofReal_exp, Real.exp_log hρpos]
        rw [hρexp, Complex.exp_log hbne0, hL₂exp t]
        have hconjeq : (starRingEnd ℂ) (ρ * Complex.exp (2*π*I*(t:ℂ))) =
            (ρ:ℂ) * Complex.exp (-(2*π*I*(t:ℂ))) := by
          rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
          congr 2
          simp only [map_mul, Complex.conj_I, Complex.conj_ofReal,
            show (starRingEnd ℂ) (2:ℂ) = 2 from map_ofNat _ 2]
          ring
        rw [hconjeq]
        have hwval : w t = a * Complex.exp (4*π*I*(t:ℂ)) + b := rfl
        have hexpsplit2 : Complex.exp (-(2*π*I*(t:ℂ))) * Complex.exp (4*π*I*(t:ℂ)) =
            Complex.exp (2*π*I*(t:ℂ)) := by
          rw [← Complex.exp_add]; congr 1; ring
        have hbcancel : b * (w t / b) = w t := by field_simp
        have hstep : (ρ:ℂ) * Complex.exp (-(2*π*I*(t:ℂ))) * b * (w t / b) =
            (ρ:ℂ) * Complex.exp (-(2*π*I*(t:ℂ))) * w t := by
          rw [show (ρ:ℂ) * Complex.exp (-(2*π*I*(t:ℂ))) * b * (w t / b) =
            (ρ:ℂ) * Complex.exp (-(2*π*I*(t:ℂ))) * (b * (w t / b)) from by ring, hbcancel]
        rw [hstep, hwval]
        linear_combination (ρ * a) * hexpsplit2
      have hkey := hloc ρ hρpos hρlt L hLcont hLexp
      rw [hLdef] at hkey
      simp only at hkey
      rw [hL₂10] at hkey
      have hfin : (-(2 * π * I) : ℂ) = 2 * π * I := by
        push_cast at hkey
        linear_combination hkey
      have hπne0 : (π:ℂ) ≠ 0 := by
        exact_mod_cast Real.pi_ne_zero
      have hIne0 : (I:ℂ) ≠ 0 := Complex.I_ne_zero
      apply (mul_ne_zero (mul_ne_zero (by norm_num : (4:ℂ) ≠ 0) hπne0) hIne0)
      linear_combination -hfin
  -- Now derive the numeric bound from `horient : ‖b‖ < ‖a‖`.
  by_cases hb0 : b = 0
  · have hK1 : 1 ≤ K := hA.2.1
    rw [hb0]
    simp only [norm_zero, sub_zero, add_zero]
    calc ‖a‖ = 1 * ‖a‖ := (one_mul _).symm
      _ ≤ K * ‖a‖ := mul_le_mul_of_nonneg_right hK1 (norm_nonneg a)
  · set α : ℝ := ‖a‖ + ‖b‖ with hαdef
    set β : ℝ := ‖a‖ - ‖b‖ with hβdef
    have hβpos : 0 < β := by rw [hβdef]; linarith [horient]
    have hαpos : 0 < α := by rw [hαdef]; linarith [norm_nonneg b, horient]
    set ε : ℝ := 1 / 4 with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; norm_num
    set C : ℂ := Complex.exp ((Complex.arg a : ℝ) * I) with hCdef
    set Cb : ℂ := Complex.exp ((Complex.arg b : ℝ) * I) with hCbdef
    set θ : ℝ := (Complex.arg b - Complex.arg a) / 2 with hθdef
    set u : ℂ := Complex.exp ((θ : ℝ) * I) with hudef
    set k : ℂ := (ε : ℂ) * u with hkdef
    set E : ℂ := (ε : ℂ) * C * u with hEdef
    have h1 : (0:ℝ) < 1 := one_pos
    have haC : (‖a‖ : ℂ) * C = a := by rw [hCdef]; exact Complex.norm_mul_exp_arg_mul_I a
    have hbCb : (‖b‖ : ℂ) * Cb = b := by rw [hCbdef]; exact Complex.norm_mul_exp_arg_mul_I b
    have hconjU : (starRingEnd ℂ) u = Complex.exp (-(θ:ℂ) * I) := by
      rw [hudef, ← Complex.exp_conj]
      congr 1
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    have hCU : C * u = Cb * (starRingEnd ℂ) u := by
      rw [hCdef, hudef, hCbdef, hconjU, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      have hargeq' : (Complex.arg a : ℂ) + (θ:ℂ) = (Complex.arg b:ℂ) + (-(θ:ℂ)) := by
        have hargeq : Complex.arg a + θ = Complex.arg b - θ := by rw [hθdef]; ring
        exact_mod_cast hargeq
      linear_combination I * hargeq'
    have haU : (‖a‖:ℂ) * (C * u) = a * u := by
      rw [show (‖a‖:ℂ) * (C * u) = (‖a‖:ℂ) * C * u from by ring, haC]
    have hbU : (‖b‖:ℂ) * (C * u) = b * (starRingEnd ℂ) u := by
      rw [hCU, show (‖b‖:ℂ) * (Cb * (starRingEnd ℂ) u) =
        (‖b‖:ℂ) * Cb * (starRingEnd ℂ) u from by ring, hbCb]
    have hAusum : a * u + b * (starRingEnd ℂ) u = (α:ℂ) * (C * u) := by
      rw [← haU, ← hbU, hαdef]; push_cast; ring
    have hAudiff : a * u - b * (starRingEnd ℂ) u = (β:ℂ) * (C * u) := by
      rw [← haU, ← hbU, hβdef]; push_cast; ring
    set φ : ℂ → ℂ := fun z => (α:ℂ) * (z.re:ℂ) + I * (β:ℂ) * (z.im:ℂ) with hφdef
    have hφre : ∀ z : ℂ, (φ z).re = α * z.re := by intro z; rw [hφdef]; simp
    have hφim : ∀ z : ℂ, (φ z).im = β * z.im := by intro z; rw [hφdef]; simp
    have hzconj : ∀ z : ℂ, (starRingEnd ℂ) z = (z.re:ℂ) - (z.im:ℂ) * I := by
      intro z
      have hz : z = (z.re:ℂ) + (z.im:ℂ) * I := (Complex.re_add_im z).symm
      conv_lhs => rw [hz]
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    have hkey : ∀ z : ℂ, A (k * z) = E * φ z := by
      intro z
      have hAkz : A (k * z) = a * (k * z) + b * (starRingEnd ℂ) (k * z) := by rw [hAdef]
      rw [hAkz, hkdef]
      have hconjkz : (starRingEnd ℂ) ((ε:ℂ) * u * z) =
          (ε:ℂ) * (starRingEnd ℂ) u * (starRingEnd ℂ) z := by
        rw [map_mul, map_mul, Complex.conj_ofReal]
      rw [hconjkz, hzconj z]
      have hzval : (z.re:ℂ) + (z.im:ℂ) * I = z := Complex.re_add_im z
      have hexpand : a * ((ε:ℂ) * u * z) + b * ((ε:ℂ) * (starRingEnd ℂ) u *
          ((z.re:ℂ) - (z.im:ℂ) * I)) =
          (ε:ℂ) * ((z.re:ℂ) * (a * u + b * (starRingEnd ℂ) u) +
            (z.im:ℂ) * I * (a * u - b * (starRingEnd ℂ) u)) := by
        linear_combination (-(a * (ε:ℂ) * u)) * hzval
      rw [hexpand, hAusum, hAudiff, hEdef, hφdef]
      ring
    have hvert : ∀ i : Fin 4, rectVert α β i = OnePoint.map φ (rectVert (1:ℝ) 1 i) := by
      have hφ0 : φ (0:ℂ) = (0:ℂ) := by rw [hφdef]; simp
      have hφ1 : φ (1:ℂ) = (α:ℂ) := by rw [hφdef]; simp
      have hφ2 : φ ((1:ℂ) + (1:ℂ) * I) = (α:ℂ) + (β:ℂ) * I := by
        rw [hφdef]; simp; ring
      have hφ3 : φ ((1:ℂ) * I) = (β:ℂ) * I := by rw [hφdef]; simp; ring
      intro i
      fin_cases i
      · show rectVert α β 0 = OnePoint.map φ (rectVert (1:ℝ) 1 0)
        rw [show rectVert α β 0 = ((0:ℂ):OnePoint ℂ) from rfl,
          show rectVert (1:ℝ) 1 0 = ((0:ℂ):OnePoint ℂ) from rfl, OnePoint.map_some, hφ0]
      · show rectVert α β 1 = OnePoint.map φ (rectVert (1:ℝ) 1 1)
        rw [show rectVert α β 1 = ((α:ℂ):OnePoint ℂ) from rfl,
          show rectVert (1:ℝ) 1 1 = ((1:ℂ):OnePoint ℂ) from rfl, OnePoint.map_some, hφ1]
      · show rectVert α β 2 = OnePoint.map φ (rectVert (1:ℝ) 1 2)
        rw [show rectVert α β 2 = (((α:ℂ) + (β:ℂ) * I):OnePoint ℂ) from rfl,
          show rectVert (1:ℝ) 1 2 = (((1:ℂ) + (1:ℂ) * I):OnePoint ℂ) from rfl,
          OnePoint.map_some, hφ2]
      · show rectVert α β 3 = OnePoint.map φ (rectVert (1:ℝ) 1 3)
        rw [show rectVert α β 3 = (((β:ℂ) * I):OnePoint ℂ) from rfl,
          show rectVert (1:ℝ) 1 3 = (((1:ℂ) * I):OnePoint ℂ) from rfl, OnePoint.map_some, hφ3]
    have hφimage : φ '' rectangle (1:ℝ) 1 = rectangle α β := by
      ext w
      simp only [rectangle, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨z, ⟨hz1, hz2, hz3, hz4⟩, rfl⟩
        rw [hφre, hφim]
        exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
      · rintro ⟨hw1, hw2, hw3, hw4⟩
        refine ⟨(⟨w.re / α, w.im / β⟩ : ℂ), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · exact div_pos hw1 hαpos
        · rw [div_lt_one hαpos]; exact hw2
        · exact div_pos hw3 hβpos
        · rw [div_lt_one hβpos]; exact hw4
        · apply Complex.ext
          · rw [hφre]; show α * (w.re / α) = w.re; field_simp
          · rw [hφim]; show β * (w.im / β) = w.im; field_simp
    have hmulconf : ∀ m : ℂ, m ≠ 0 →
        IsConformalOnto (fun z => m * z) univ ((fun z => m * z) '' univ) :=
      fun m hm =>
        ⟨(differentiable_id.const_mul m).differentiableOn,
          fun x _ y _ hxy => mul_left_cancel₀ hm hxy, rfl⟩
    have hk0 : k ≠ 0 := by
      rw [hkdef]
      exact mul_ne_zero (by rw [hεdef]; exact_mod_cast (by norm_num : (1:ℝ)/4 ≠ 0))
        (Complex.exp_ne_zero _)
    have hE0 : E ≠ 0 := by
      rw [hEdef]
      exact mul_ne_zero (mul_ne_zero
        (by rw [hεdef]; exact_mod_cast (by norm_num : (1:ℝ)/4 ≠ 0))
        (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)
    set Q : TopQuad := rectQuad h1 h1 with hQdef
    set Q0 : TopQuad := rectQuad hαpos hβpos with hQ0def
    have hQsub : closure (toExt Q.dom) ⊆ toExt (univ : Set ℂ) := by
      have hQdom : Q.dom = rectangle (1:ℝ) 1 := rfl
      rw [hQdom, closure_toExt_of_isBounded (isBounded_rectangle 1 1)]
      exact image_mono (subset_univ _)
    have hQ0sub : closure (toExt Q0.dom) ⊆ toExt (univ : Set ℂ) := by
      have hQ0dom : Q0.dom = rectangle α β := rfl
      rw [hQ0dom, closure_toExt_of_isBounded (isBounded_rectangle α β)]
      exact image_mono (subset_univ _)
    obtain ⟨Qε, hQε_img, hQε_conf⟩ :=
      TopQuad.exists_image_conformal isOpen_univ (hmulconf k hk0) hQsub
    obtain ⟨Q'', hQ0_img, hQ0_conf⟩ :=
      TopQuad.exists_image_conformal isOpen_univ (hmulconf E hE0) hQ0sub
    have hQmod : Q.modulus = 1 / 1 := modulus_rectQuad h1 h1
    have hQ0mod : Q0.modulus = α / β := modulus_rectQuad hαpos hβpos
    have hQεmod : Q.modulus = Qε.modulus := thm1_3_modulus_conformal_invariant hQε_conf
    have hQ''mod : Q0.modulus = Q''.modulus := thm1_3_modulus_conformal_invariant hQ0_conf
    have hmapkey : ∀ w : OnePoint ℂ,
        OnePoint.map (fun z => E * z) (OnePoint.map φ w) =
          OnePoint.map A (OnePoint.map (fun z => k * z) w) := by
      intro w
      cases w with
      | infty => simp
      | coe z => simp [hkey z]
    have hQvert : Q.vert = rectVert (1:ℝ) 1 := rfl
    have hQ0vert : Q0.vert = rectVert α β := rfl
    have hQdom : Q.dom = rectangle (1:ℝ) 1 := rfl
    have hQ0dom : Q0.dom = rectangle α β := rfl
    have hvertmatch : ∀ i : Fin 4, Q''.vert i = OnePoint.map A (Qε.vert i) := by
      intro i
      rw [hQ0_img.2 i, hQε_img.2 i, hQ0vert, hQvert, hvert i]
      exact hmapkey (rectVert (1:ℝ) 1 i)
    have hdommatch : Q''.dom = A '' Qε.dom := by
      rw [hQ0_img.1, hQε_img.1, hQ0dom, hQdom, ← hφimage]
      simp only [Set.image_image]
      congr 1
      funext z
      show E * φ z = A (k * z)
      exact (hkey z).symm
    have hQεQ''img : Qε.IsImageUnder Q'' A := ⟨hdommatch, hvertmatch⟩
    have hQεball : closure ((fun z : ℂ => k * z) '' rectangle (1:ℝ) 1) ⊆ ball (0:ℂ) 1 := by
      have hcpt : IsCompact (closure (rectangle (1:ℝ) 1)) := by
        rw [closure_rectangle_eq_reProdIm h1 h1]
        exact isCompact_Icc.reProdIm isCompact_Icc
      have hcont_k : Continuous (fun z : ℂ => k * z) := continuous_const.mul continuous_id
      have hclosed_image : IsClosed ((fun z : ℂ => k * z) '' closure (rectangle (1:ℝ) 1)) :=
        (hcpt.image hcont_k).isClosed
      have hclosure_sub : closure ((fun z : ℂ => k * z) '' rectangle (1:ℝ) 1) ⊆
          (fun z : ℂ => k * z) '' closure (rectangle (1:ℝ) 1) := by
        rw [← hclosed_image.closure_eq]
        exact closure_mono (image_mono subset_closure)
      have hballsub : (fun z : ℂ => k * z) '' closure (rectangle (1:ℝ) 1) ⊆ ball (0:ℂ) 1 := by
        rintro w ⟨z, hz, rfl⟩
        rw [closure_rectangle_eq_reProdIm h1 h1, mem_reProdIm] at hz
        obtain ⟨⟨hz1, hz2⟩, ⟨hz3, hz4⟩⟩ := hz
        have hzn : ‖z‖ ≤ 2 := by
          have hb := Complex.norm_le_abs_re_add_abs_im z
          have h1' : |z.re| ≤ 1 := abs_le.2 ⟨by linarith, hz2⟩
          have h2' : |z.im| ≤ 1 := abs_le.2 ⟨by linarith, hz4⟩
          linarith
        have hunorm : ‖u‖ = 1 := by rw [hudef]; exact Complex.norm_exp_ofReal_mul_I θ
        have hknorm : ‖k‖ = ε := by
          rw [hkdef, norm_mul, hunorm, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hεpos]
        rw [mem_ball, dist_eq_norm, sub_zero, norm_mul, hknorm]
        rw [hεdef]
        nlinarith [hzn]
      exact hclosure_sub.trans hballsub
    have hQεsub : closure (toExt Qε.dom) ⊆ toExt (ball (0:ℂ) 1) := by
      have hQεdom : Qε.dom = (fun z : ℂ => k * z) '' rectangle (1:ℝ) 1 := hQε_img.1
      have hQεclosure : closure Qε.dom ⊆ ball (0:ℂ) 1 := by rw [hQεdom]; exact hQεball
      have hQεbdd : Bornology.IsBounded Qε.dom :=
        isBounded_ball.subset (subset_closure.trans hQεclosure)
      rw [closure_toExt_of_isBounded hQεbdd]
      exact image_mono hQεclosure
    obtain ⟨Q', hQ'_img, hQ'_mod⟩ := hA.2.2.2 Qε hQεsub
    have hQ'eq : Q' = Q'' := hQ'_img.unique hQεQ''img
    rw [hQ'eq, ← hQ''mod, hQ0mod, ← hQεmod, hQmod] at hQ'_mod
    have hfinal : α / β ≤ K * (1/1) := hQ'_mod
    rw [div_le_iff₀ hβpos] at hfinal
    have : α ≤ K * β := by nlinarith [hfinal]
    rw [hαdef, hβdef] at this
    linarith [this]



/-- Copied verbatim from `S12_Existence.lean` (not imported, to avoid pulling in unrelated heavy
machinery): a `K`-q.c. map restricted to a smaller open subset of its domain is still `K`-q.c. -/
theorem ac_t_isKQC_restrict {f : ℂ → ℂ} {D U : Set ℂ} {K : ℝ} (hf : IsKQC f D K)
    (hUo : IsOpen U) (hUD : U ⊆ D) : IsKQC f U K := by
  obtain ⟨hDo, hK1, hhom, hquad⟩ := hf
  obtain ⟨hc, hi, -, hinv⟩ := hhom
  refine ⟨hUo, hK1, ⟨hc.mono hUD, hi.mono hUD, rfl, ?_⟩, fun Q hQ => hquad Q (hQ.trans (image_mono hUD))⟩
  have heq : Set.EqOn (Function.invFunOn f U) (Function.invFunOn f D) (f '' U) := by
    intro w hw
    obtain ⟨z, hzU, rfl⟩ := hw
    have h1 : Function.invFunOn f U (f z) = z := (hi.mono hUD).leftInvOn_invFunOn hzU
    have h2 : Function.invFunOn f D (f z) = z := hi.leftInvOn_invFunOn (hUD hzU)
    rw [h1, h2]
  exact (hinv.mono (image_mono hUD)).congr heq

/-- **T1.** Blow-up at a point of differentiability: the derivative `ζ ↦ dz f z₀ · ζ + dzbar f z₀ · ζ̄`
is either zero or a `K`-q.c. map of the unit disc. -/
theorem ac_t_isKQC_blowup_or_zero {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {z₀ : ℂ}
    (hz₀ : z₀ ∈ D) (hd : DifferentiableAt ℝ f z₀) :
    (dz f z₀ = 0 ∧ dzbar f z₀ = 0) ∨
      IsKQC (fun ζ => dz f z₀ * ζ + dzbar f z₀ * (starRingEnd ℂ) ζ) (ball (0 : ℂ) 1) K := by
  set A : ℂ → ℂ := fun ζ => dz f z₀ * ζ + dzbar f z₀ * (starRingEnd ℂ) ζ with hAdef
  obtain ⟨r₀, hr₀pos, hr₀sub⟩ := Metric.isOpen_iff.mp hf.1 z₀ hz₀
  -- Step 1: for every `0 < r ≤ r₀`, the blow-up quotient is `K`-q.c. on `ball 0 1`.
  have hgKQC : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      IsKQC (fun ζ : ℂ => (f (z₀ + (r : ℂ) * ζ) - f z₀) / (r : ℂ)) (ball (0 : ℂ) 1) K := by
    intro r hrpos hrle
    have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
    have hψconf : IsConformalOnto (fun ζ : ℂ => z₀ + (r : ℂ) * ζ) univ univ := by
      refine ⟨(by fun_prop : Differentiable ℂ (fun ζ : ℂ => z₀ + (r : ℂ) * ζ)).differentiableOn,
        ?_, ?_⟩
      · intro a _ b _ hab
        have hab' : z₀ + (r : ℂ) * a = z₀ + (r : ℂ) * b := hab
        exact mul_left_cancel₀ hrne (add_left_cancel hab')
      · rw [image_univ, Set.range_eq_univ]
        intro w
        exact ⟨(w - z₀) / (r : ℂ), by field_simp; ring⟩
    have hφconf : IsConformalOnto (fun w : ℂ => (w - f z₀) / (r : ℂ)) univ univ := by
      refine ⟨(by fun_prop : Differentiable ℂ (fun w : ℂ => (w - f z₀) / (r : ℂ))).differentiableOn,
        ?_, ?_⟩
      · intro a _ b _ hab
        have hab' : (a - f z₀) / (r : ℂ) = (b - f z₀) / (r : ℂ) := hab
        have h2 : a - f z₀ = b - f z₀ := by
          field_simp at hab'
          linear_combination hab'
        linear_combination h2
      · rw [image_univ, Set.range_eq_univ]
        intro w
        exact ⟨(r : ℂ) * w + f z₀, by field_simp; ring⟩
    have hψKQC1 : IsKQC (fun ζ : ℂ => z₀ + (r : ℂ) * ζ) univ 1 :=
      isKQC_one_of_conformal isOpen_univ hψconf
    have hψKQCball : IsKQC (fun ζ : ℂ => z₀ + (r : ℂ) * ζ) (ball (0 : ℂ) 1) 1 :=
      ac_t_isKQC_restrict hψKQC1 Metric.isOpen_ball (subset_univ _)
    have himg : (fun ζ : ℂ => z₀ + (r : ℂ) * ζ) '' ball (0 : ℂ) 1 ⊆ D := by
      rintro w ⟨ζ, hζ, rfl⟩
      apply hr₀sub
      have hζ1 : ‖ζ‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hζ
      have hrnorm : ‖(r : ℂ)‖ = r := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
      have hdx : dist (z₀ + (r : ℂ) * ζ) z₀ = r * ‖ζ‖ := by
        rw [dist_eq_norm]
        have heq : z₀ + (r : ℂ) * ζ - z₀ = (r : ℂ) * ζ := by ring
        rw [heq, norm_mul, hrnorm]
      rw [Metric.mem_ball, hdx]
      calc r * ‖ζ‖ < r * 1 := mul_lt_mul_of_pos_left hζ1 hrpos
        _ = r := mul_one r
        _ ≤ r₀ := hrle
    have hcomp1 : IsKQC (f ∘ (fun ζ : ℂ => z₀ + (r : ℂ) * ζ)) (ball (0 : ℂ) 1) (1 * K) :=
      thm7_1_comp hψKQCball hf himg
    have hφKQC1 : IsKQC (fun w : ℂ => (w - f z₀) / (r : ℂ)) univ 1 :=
      isKQC_one_of_conformal isOpen_univ hφconf
    have hcomp2 : IsKQC
        ((fun w : ℂ => (w - f z₀) / (r : ℂ)) ∘ (f ∘ (fun ζ : ℂ => z₀ + (r : ℂ) * ζ)))
        (ball (0 : ℂ) 1) ((1 * K) * 1) :=
      thm7_1_comp hcomp1 hφKQC1 (subset_univ _)
    have heq : (fun w : ℂ => (w - f z₀) / (r : ℂ)) ∘ (f ∘ (fun ζ : ℂ => z₀ + (r : ℂ) * ζ))
        = (fun ζ : ℂ => (f (z₀ + (r : ℂ) * ζ) - f z₀) / (r : ℂ)) := by
      funext ζ
      simp [Function.comp]
    rw [heq, one_mul, mul_one] at hcomp2
    exact hcomp2
  -- Step 2: a sequence `rₙ → 0⁺` with `rₙ ≤ r₀`, giving uniform convergence of the blow-ups to `A`.
  set r_seq : ℕ → ℝ := fun n => r₀ * (1 / ((n : ℝ) + 1)) with hr_seq_def
  have hr_pos : ∀ n, 0 < r_seq n := fun n => mul_pos hr₀pos (by positivity)
  have hr_le : ∀ n, r_seq n ≤ r₀ := by
    intro n
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    calc r_seq n = r₀ * (1 / ((n : ℝ) + 1)) := rfl
      _ ≤ r₀ * 1 := mul_le_mul_of_nonneg_left h1 hr₀pos.le
      _ = r₀ := mul_one r₀
  have hr_tendsto : Tendsto r_seq atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul r₀
    simpa [hr_seq_def, mul_zero] using h
  have hlimU : TendstoUniformlyOn
      (fun n : ℕ => fun ζ : ℂ => (f (z₀ + (r_seq n : ℂ) * ζ) - f z₀) / (r_seq n : ℂ)) A atTop
      (ball (0 : ℂ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlO := hd.hasFDerivAt.isLittleO
    have hbound := Asymptotics.isLittleO_iff.mp hlO (show (0 : ℝ) < ε / 2 by linarith)
    rw [Metric.eventually_nhds_iff] at hbound
    obtain ⟨δ, hδpos, hδ⟩ := hbound
    have htend : ∀ᶠ n in atTop, r_seq n < δ :=
      hr_tendsto.eventually (Iio_mem_nhds hδpos)
    filter_upwards [htend] with n hn ζ hζ
    have hrnpos : 0 < r_seq n := hr_pos n
    have hrnne : (r_seq n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrnpos.ne'
    have hrnnorm : ‖(r_seq n : ℂ)‖ = r_seq n := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrnpos]
    have hζ1 : ‖ζ‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hζ
    have hdx : dist (z₀ + (r_seq n : ℂ) * ζ) z₀ = r_seq n * ‖ζ‖ := by
      rw [dist_eq_norm]
      have heq : z₀ + (r_seq n : ℂ) * ζ - z₀ = (r_seq n : ℂ) * ζ := by ring
      rw [heq, norm_mul, hrnnorm]
    have hdxlt : dist (z₀ + (r_seq n : ℂ) * ζ) z₀ < δ := by
      rw [hdx]
      calc r_seq n * ‖ζ‖ < r_seq n * 1 := mul_lt_mul_of_pos_left hζ1 hrnpos
        _ = r_seq n := mul_one _
        _ < δ := hn
    have hkey := hδ hdxlt
    have hsub_eq : (z₀ + (r_seq n : ℂ) * ζ) - z₀ = (r_seq n : ℂ) * ζ := by ring
    rw [hsub_eq, fderiv_eq_dz_dzbar hd] at hkey
    have hconjeq : (starRingEnd ℂ) ((r_seq n : ℂ) * ζ) = (r_seq n : ℂ) * (starRingEnd ℂ) ζ := by
      rw [map_mul, Complex.conj_ofReal]
    rw [hconjeq] at hkey
    have hfactor : dz f z₀ * ((r_seq n : ℂ) * ζ) + dzbar f z₀ * ((r_seq n : ℂ) * (starRingEnd ℂ) ζ)
        = (r_seq n : ℂ) * A ζ := by
      simp only [hAdef]
      ring
    rw [hfactor] at hkey
    have hnormrhs : ‖(r_seq n : ℂ) * ζ‖ = r_seq n * ‖ζ‖ := by rw [norm_mul, hrnnorm]
    rw [hnormrhs] at hkey
    -- hkey : ‖f (z₀ + rn*ζ) - f z₀ - rn * A ζ‖ ≤ ε/2 * (rn * ‖ζ‖)
    have hdiv : f (z₀ + (r_seq n : ℂ) * ζ) - f z₀ - (r_seq n : ℂ) * A ζ
        = (r_seq n : ℂ) * ((f (z₀ + (r_seq n : ℂ) * ζ) - f z₀) / (r_seq n : ℂ) - A ζ) := by
      field_simp
    rw [hdiv, norm_mul, hrnnorm] at hkey
    have hζle : ‖ζ‖ ≤ 1 := hζ1.le
    have hbound2 : r_seq n * ‖(f (z₀ + (r_seq n : ℂ) * ζ) - f z₀) / (r_seq n : ℂ) - A ζ‖
        ≤ (ε / 2) * r_seq n := by
      refine hkey.trans ?_
      calc ε / 2 * (r_seq n * ‖ζ‖) ≤ ε / 2 * (r_seq n * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hζle hrnpos.le) (by linarith)
        _ = ε / 2 * r_seq n := by ring
    have hfinal : ‖(f (z₀ + (r_seq n : ℂ) * ζ) - f z₀) / (r_seq n : ℂ) - A ζ‖ ≤ ε / 2 :=
      le_of_mul_le_mul_left
        (by linarith [hbound2] : r_seq n * ‖(f (z₀ + (r_seq n : ℂ) * ζ) - f z₀) / (r_seq n : ℂ) - A ζ‖ ≤ r_seq n * (ε / 2))
        hrnpos
    rw [dist_eq_norm]
    calc ‖A ζ - (f (z₀ + (r_seq n : ℂ) * ζ) - f z₀) / (r_seq n : ℂ)‖
        = ‖(f (z₀ + (r_seq n : ℂ) * ζ) - f z₀) / (r_seq n : ℂ) - A ζ‖ := norm_sub_rev _ _
      _ ≤ ε / 2 := hfinal
      _ < ε := by linarith
  have hlim : TendstoLocallyUniformlyOn
      (fun n : ℕ => fun ζ : ℂ => (f (z₀ + (r_seq n : ℂ) * ζ) - f z₀) / (r_seq n : ℂ)) A atTop
      (ball (0 : ℂ) 1) := hlimU.tendstoLocallyUniformlyOn
  -- Step 3: apply Theorem 8.2.
  have hqc : ∀ n, IsKQC (fun ζ : ℂ => (f (z₀ + (r_seq n : ℂ) * ζ) - f z₀) / (r_seq n : ℂ))
      (ball (0 : ℂ) 1) K := fun n => hgKQC (r_seq n) (hr_pos n) (hr_le n)
  have hmain := thm8_2_limit (D := ball (0 : ℂ) 1) Metric.isBounded_ball (isConnected_ball one_pos)
      hqc hlim
  -- Step 4: rule out the constant case (forcing `A ≡ 0`).
  rcases hmain with ⟨c, hc⟩ | hAKQC
  · left
    have hA0 : A 0 = c := hc 0 (Metric.mem_ball_self one_pos)
    have hA0eq0 : A (0 : ℂ) = 0 := by simp [hAdef]
    have hc0 : c = 0 := by rw [← hA0, hA0eq0]
    have hmem1 : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
      simp [Metric.mem_ball, dist_eq_norm]
      norm_num
    have hmem2 : (Complex.I / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
      simp [Metric.mem_ball, dist_eq_norm]
      norm_num
    have h1 : A (1 / 2 : ℂ) = 0 := by rw [hc (1 / 2 : ℂ) hmem1, hc0]
    have h2 : A (Complex.I / 2 : ℂ) = 0 := by rw [hc (Complex.I / 2 : ℂ) hmem2, hc0]
    simp only [hAdef] at h1 h2
    have hc1 : (starRingEnd ℂ) (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
    have hc2 : (starRingEnd ℂ) (Complex.I / 2 : ℂ) = -(Complex.I / 2 : ℂ) := by
      have h2real : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
      rw [map_div₀, Complex.conj_I, h2real]
      ring
    rw [hc1] at h1
    rw [hc2] at h2
    constructor
    · linear_combination h1 - Complex.I * h2 + ((dz f z₀ - dzbar f z₀) / 2) * Complex.I_sq
    · linear_combination h1 + Complex.I * h2 + ((dzbar f z₀ - dz f z₀) / 2) * Complex.I_sq
  · right
    exact hAKQC

/-- **T3.** The dilatation inequality at every point of differentiability (T1 + T2; the zero case is
`0 ≤ K · 0`). -/
theorem ac_t_dilatation_of_differentiableAt {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K)
    {z₀ : ℂ} (hz₀ : z₀ ∈ D) (hd : DifferentiableAt ℝ f z₀) :
    ‖dz f z₀‖ + ‖dzbar f z₀‖ ≤ K * (‖dz f z₀‖ - ‖dzbar f z₀‖) := by
  rcases ac_t_isKQC_blowup_or_zero hf hz₀ hd with ⟨h1, h2⟩ | hA
  · rw [h1, h2]
    simp
  · exact ac_t_dilatation_of_isKQC_linear hA

/-- **Theorem 9.4**: the partial derivatives of a `K`-q.c. map satisfy
`|∂_z f| + |∂_{z̄} f| ≤ K (|∂_z f| - |∂_{z̄} f|)` almost everywhere (9.12).

Proved (2026-09-21): at every point of differentiability the blow-ups converge to the derivative, which
is `K`-q.c. by Theorem 8.2 (`ac_t_isKQC_blowup_or_zero`), and a `K`-q.c. real-linear map has dilatation
`≤ K` (`ac_t_dilatation_of_isKQC_linear`); then `thm9_3_differentiable_ae`. -/
theorem thm9_4_dilatation_ae {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) :
    ∀ᵐ z ∂(volume.restrict D), ‖dz f z‖ + ‖dzbar f z‖ ≤ K * (‖dz f z‖ - ‖dzbar f z‖) := by
  filter_upwards [thm9_3_differentiable_ae hf, ae_restrict_mem hf.1.measurableSet] with z hz hzD
  exact ac_t_dilatation_of_differentiableAt hf hzD hz

/-! ### Area track interface (coordinator 553e2d) -/

/-- At a point of differentiability of a `K`-q.c. map the Jacobian is the absolute value of the determinant of the
real derivative: `J_f = |∂f|² - |∂̄f|² ≥ 0` by the dilatation inequality `ac_t_dilatation_of_differentiableAt`. -/
theorem ar_jacobian_eq_abs_det {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {z₀ : ℂ}
    (hz₀ : z₀ ∈ D) (hdiff : DifferentiableAt ℝ f z₀) :
    jacobian f z₀ = |LinearMap.det (fderiv ℝ f z₀ : ℂ →ₗ[ℝ] ℂ)| := by
  have hK : 1 ≤ K := hf.2.1
  have h := ac_t_dilatation_of_differentiableAt hf hz₀ hdiff
  have ha := norm_nonneg (dz f z₀)
  have hb := norm_nonneg (dzbar f z₀)
  have h1 : 0 ≤ ‖dz f z₀‖ - ‖dzbar f z₀‖ := by
    by_contra hneg
    have : K * (‖dz f z₀‖ - ‖dzbar f z₀‖) < 0 := mul_neg_of_pos_of_neg (by linarith) (lt_of_not_ge hneg)
    linarith
  have hJ : 0 ≤ jacobian f z₀ := by
    rw [jacobian, show ‖dz f z₀‖ ^ 2 - ‖dzbar f z₀‖ ^ 2 =
      (‖dz f z₀‖ - ‖dzbar f z₀‖) * (‖dz f z₀‖ + ‖dzbar f z₀‖) by ring]
    exact mul_nonneg h1 (add_nonneg ha hb)
  rw [det_fderiv_eq_jacobian hdiff, abs_of_nonneg hJ]

/-- The closed square `[-r, r]²` has area `4r²` for `r ≥ 0`. -/
theorem ar_vol_volume_closedRect_square {r : ℝ} (hr : 0 ≤ r) :
    volume (closedRect (-r) r (-r) r) = ENNReal.ofReal (4 * r ^ 2) := by
  have hpre : Complex.measurableEquivRealProd ⁻¹' (Set.Icc (-r) r ×ˢ Set.Icc (-r) r) =
      closedRect (-r) r (-r) r := by
    rw [acl_closedRect_eq]
    ext z
    simp [Complex.measurableEquivRealProd_apply, mem_reProdIm]
    tauto
  rw [← hpre, (Complex.volume_preserving_equiv_real_prod).measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet,
    Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by linarith)]
  congr 1
  ring

/-- The image of the square `[-r, r]²` under the affine map `h ↦ c + A h` has area `4r² |det A|`. -/
theorem ar_volume_affine_image_square (A : ℂ →L[ℝ] ℂ) (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume ((fun h => c + A h) '' closedRect (-r) r (-r) r) =
      ENNReal.ofReal (|LinearMap.det (A : ℂ →ₗ[ℝ] ℂ)| * (4 * r ^ 2)) := by
  have himg : (fun h => c + A h) '' closedRect (-r) r (-r) r =
      (fun x => c + x) '' (⇑A '' closedRect (-r) r (-r) r) := by
    rw [Set.image_image]
  rw [himg, Set.image_add_left, measure_preimage_add, Measure.addHaar_image_continuousLinearMap,
    ar_vol_volume_closedRect_square hr, ← ENNReal.ofReal_mul (abs_nonneg _)]

/-- A closed rectangle is convex: it is an intersection of four half-planes. -/
theorem ar_cov_convex_closedRect (a b c d : ℝ) : Convex ℝ (closedRect a b c d) :=
  (convex_halfSpace_re_ge a).inter ((convex_halfSpace_re_le b).inter
    ((convex_halfSpace_im_ge c).inter (convex_halfSpace_im_le d)))

/-- A continuous nonvanishing function on a convex nonempty subset of `ℂ` has a continuous logarithm there: the
subset is contractible, hence simply connected, and locally path connected, so the map lifts through the covering
`exp : ℂ → ℂ \ {0}` (the proof of `iod_exists_log_on_closedBall`, for a general convex set). -/
theorem ar_cov_exists_log_on_convex {s : Set ℂ} (hconv : Convex ℝ s) (hne : s.Nonempty) {g : ℂ → ℂ}
    (hgc : ContinuousOn g s) (hgne : ∀ x ∈ s, g x ≠ 0) :
    ∃ L : ℂ → ℂ, ContinuousOn L s ∧ ∀ x ∈ s, Complex.exp (L x) = g x := by
  classical
  have := hconv.contractibleSpace hne
  have : SimplyConnectedSpace ↥s := SimplyConnectedSpace.ofContractible _
  have : LocallyPathConnectedSpace ↥s := hconv.locallyPathConnectedSpace
  obtain ⟨c, hc⟩ := hne
  have he : Complex.exp (Complex.log (g c)) = g (⟨c, hc⟩ : ↥s).1 := Complex.exp_log (hgne c hc)
  obtain ⟨F, ⟨-, hFexp⟩, -⟩ :=
    IsCoveringMapOn.existsUnique_continuousMap_lifts isCoveringMapOn_exp
      (⟨fun x : ↥s => g x.1, hgc.domRestrict⟩ : C(↥s, ℂ)) he (fun x => hgne x.1 x.2)
  refine ⟨fun z => if h : z ∈ s then F ⟨z, h⟩ else 0, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hL : s.domRestrict (fun z => if h : z ∈ s then F ⟨z, h⟩ else 0) = fun x : ↥s => F x := by
      funext x
      exact dite_eq_left x.2
    rw [hL]
    exact F.continuous
  · intro x hx
    have hLx : (fun z => if h : z ∈ s then F ⟨z, h⟩ else 0) x = F ⟨x, hx⟩ := dite_eq_left hx
    rw [hLx]
    exact congrFun hFexp ⟨x, hx⟩

/-- Covering lemma for squares: a continuous map `g` of the closed square `[-r, r]²` with `|g(h) - h| < δ` covers the
concentric square `[-(r - δ), r - δ]²`.  A missed point `w` would give `h - w` a continuous logarithm on the boundary
of the square (a logarithm of `g - w` on the convex square, minus the principal logarithm of `(g - w)/(h - w)`, which
lies in the disc `|ζ - 1| < 1`), although `w` lies in a bounded complementary component of the boundary. -/
theorem ar_covering_square {g : ℂ → ℂ} {r δ : ℝ} (hδ : 0 < δ)
    (hg : ContinuousOn g (closedRect (-r) r (-r) r))
    (hclose : ∀ h ∈ closedRect (-r) r (-r) r, ‖g h - h‖ < δ) :
    closedRect (-(r - δ)) (r - δ) (-(r - δ)) (r - δ) ⊆ g '' closedRect (-r) r (-r) r := by
  intro w hw
  by_contra hwg
  have hw1 : -(r - δ) ≤ w.re := hw.1
  have hw2 : w.re ≤ r - δ := hw.2.1
  have hw3 : -(r - δ) ≤ w.im := hw.2.2.1
  have hw4 : w.im ≤ r - δ := hw.2.2.2
  have hr : 0 ≤ r := by linarith
  -- Step 1: a continuous logarithm `L` of `g - w` on the convex square
  have hS0 : (0 : ℂ) ∈ closedRect (-r) r (-r) r := by
    show -r ≤ (0 : ℂ).re ∧ (0 : ℂ).re ≤ r ∧ -r ≤ (0 : ℂ).im ∧ (0 : ℂ).im ≤ r
    simp only [Complex.zero_re, Complex.zero_im]
    exact ⟨by linarith, hr, by linarith, hr⟩
  have hgw : ∀ x ∈ closedRect (-r) r (-r) r, g x - w ≠ 0 := by
    intro x hx hx0
    exact hwg ⟨x, hx, sub_eq_zero.mp hx0⟩
  obtain ⟨L, hLc, hLexp⟩ := ar_cov_exists_log_on_convex (g := fun x => g x - w)
    (ar_cov_convex_closedRect (-r) r (-r) r) ⟨0, hS0⟩ (hg.sub continuousOn_const) hgw
  -- Step 2: the boundary `B` of the square; the component of `Bᶜ` containing `w` is bounded
  set B : Set ℂ := closedRect (-r) r (-r) r \ openRect (-r) r (-r) r
  have hBc : IsCompact B := (acl_isCompact_closedRect _ _ _ _).diff (acl_isOpen_openRect _ _ _ _)
  have hwO : w ∈ openRect (-r) r (-r) r := ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hwB : w ∉ B := fun h => h.2 hwO
  have hOS : openRect (-r) r (-r) r ⊆ closedRect (-r) r (-r) r :=
    acl_openRect_subset_closedRect le_rfl le_rfl le_rfl le_rfl
  have hsub : connectedComponentIn Bᶜ w ⊆ openRect (-r) r (-r) r ∪ (closedRect (-r) r (-r) r)ᶜ := by
    intro z hz
    have hzB : z ∉ B := connectedComponentIn_subset _ _ hz
    by_cases hzS : z ∈ closedRect (-r) r (-r) r
    · left
      by_contra hzO
      exact hzB ⟨hzS, hzO⟩
    · right
      exact hzS
  have hcomp : connectedComponentIn Bᶜ w ⊆ openRect (-r) r (-r) r :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union
      (acl_isOpen_openRect _ _ _ _) (acl_isCompact_closedRect _ _ _ _).isClosed.isOpen_compl
      (Set.disjoint_compl_right_iff_subset.mpr hOS) hsub ⟨w, mem_connectedComponentIn hwB, hwO⟩
  have hbdd : Bornology.IsBounded (connectedComponentIn Bᶜ w) :=
    (acl_isBounded_openRect _ _ _ _).subset hcomp
  -- Step 3: a continuous logarithm of `z - w` on `B`, namely `L z - log ((g z - w) / (z - w))`
  have hBS : B ⊆ closedRect (-r) r (-r) r := Set.sdiff_subset
  have hBnorm : ∀ z ∈ B, δ ≤ ‖z - w‖ := by
    intro z hz
    by_contra hle
    have hlt : ‖z - w‖ < δ := not_le.mp hle
    have hre := abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm (z - w)) hlt)
    have him := abs_lt.mp (lt_of_le_of_lt (Complex.abs_im_le_norm (z - w)) hlt)
    rw [Complex.sub_re] at hre
    rw [Complex.sub_im] at him
    exact hz.2 ⟨by linarith [hre.1], by linarith [hre.2], by linarith [him.1], by linarith [him.2]⟩
  have hBne : ∀ z ∈ B, z - w ≠ 0 := by
    intro z hz h0
    rw [sub_eq_zero.mp h0] at hz
    exact hwB hz
  have hslit : ∀ z ∈ B, (g z - w) / (z - w) ∈ Complex.slitPlane := by
    intro z hz
    have hzw : 0 < ‖z - w‖ := norm_pos_iff.mpr (hBne z hz)
    have hkey : ‖(g z - w) / (z - w) - 1‖ < 1 := by
      rw [div_sub_one (hBne z hz), norm_div, div_lt_one hzw,
        show g z - w - (z - w) = g z - z by ring]
      exact lt_of_lt_of_le (hclose z (hBS hz)) (hBnorm z hz)
    have hre := abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm _) hkey)
    rw [Complex.sub_re, Complex.one_re] at hre
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [hre.1]))
  -- Step 4: contradiction with `not_exists_continuousOn_log_of_isBounded_connectedComponentIn` (Borsuk)
  refine not_exists_continuousOn_log_of_isBounded_connectedComponentIn hBc hwB hbdd
    ⟨fun z => L z - Complex.log ((g z - w) / (z - w)), ?_, ?_⟩
  · exact (hLc.mono hBS).sub ((((hg.mono hBS).sub continuousOn_const).div₀
      (continuousOn_id.sub continuousOn_const) hBne).clog hslit)
  · intro z hz
    show Complex.exp (L z - Complex.log ((g z - w) / (z - w))) = z - w
    have hu0 : (g z - w) / (z - w) ≠ 0 := div_ne_zero (hgw z (hBS hz)) (hBne z hz)
    rw [Complex.exp_sub, Complex.exp_log hu0, hLexp z (hBS hz), div_div_cancel₀ (hgw z (hBS hz))]

/-- Area of a homothetic image in the plane: `m(c + r · T) = r² m(T)`. -/
theorem ar_up_volume_image_homothety (c : ℂ) (r : ℝ) (T : Set ℂ) :
    volume ((fun y => c + r • y) '' T) = ENNReal.ofReal (r ^ 2) * volume T := by
  have h1 : (fun y => c + r • y) '' T = (fun b => c + b) '' ((fun y => r • y) '' T) := by
    rw [Set.image_image]
  have h2 : volume ((fun y : ℂ => r • y) '' T) = ENNReal.ofReal |r ^ Module.finrank ℝ ℂ| * volume T :=
    Measure.addHaar_smul volume r T
  rw [h1, Set.image_add_left, measure_preimage_add, h2, Complex.finrank_real_complex,
    abs_of_nonneg (sq_nonneg r)]

/-- If the first-order remainder `f z - f z₀ - A (z - z₀)` has norm at most `ρ r` on the square `Q_r` of half-side
`r > 0` centred at `z₀`, then `f(Q_r)` lies in `f(z₀) + r · T`, where `T` is the closed `ρ`-thickening of
`A([-1, 1]²)`. -/
theorem ar_up_image_subset {f : ℂ → ℂ} {z₀ : ℂ} (A : ℂ →L[ℝ] ℂ) {r ρ : ℝ} (hr : 0 < r)
    (hbound : ∀ z ∈ closedRect (z₀.re - r) (z₀.re + r) (z₀.im - r) (z₀.im + r),
      ‖f z - f z₀ - A (z - z₀)‖ ≤ ρ * r) :
    f '' closedRect (z₀.re - r) (z₀.re + r) (z₀.im - r) (z₀.im + r) ⊆
      (fun y => f z₀ + r • y) '' cthickening ρ (A '' closedRect (-1) 1 (-1) 1) := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨r⁻¹ • (f z - f z₀), ?_, ?_⟩
  · have hz' : z₀.re - r ≤ z.re ∧ z.re ≤ z₀.re + r ∧ z₀.im - r ≤ z.im ∧ z.im ≤ z₀.im + r := hz
    have hmem : r⁻¹ • (z - z₀) ∈ closedRect (-1) 1 (-1) 1 := by
      show -1 ≤ (r⁻¹ • (z - z₀)).re ∧ (r⁻¹ • (z - z₀)).re ≤ 1 ∧
        -1 ≤ (r⁻¹ • (z - z₀)).im ∧ (r⁻¹ • (z - z₀)).im ≤ 1
      simp only [Complex.smul_re, Complex.smul_im, Complex.sub_re, Complex.sub_im, smul_eq_mul]
      refine ⟨(le_inv_mul_iff₀ hr).2 ?_, (inv_mul_le_iff₀ hr).2 ?_, (le_inv_mul_iff₀ hr).2 ?_,
        (inv_mul_le_iff₀ hr).2 ?_⟩ <;> linarith
    refine Metric.mem_cthickening_of_dist_le _ (A (r⁻¹ • (z - z₀))) ρ _ ⟨_, hmem, rfl⟩ ?_
    rw [dist_eq_norm, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
      inv_mul_le_iff₀ hr, mul_comm r ρ]
    exact hbound z hz
  · simp only [smul_inv_smul₀ hr.ne', add_sub_cancel]

/-- Upper bound for the area of the image of a small square at a point of differentiability:
`m(f(Q_r)) ≤ (|det Df(z₀)| + η) · 4r²` for small `r > 0`, because `f(Q_r)` lies in `f(z₀) + r · T` with `T` a thin
closed thickening of the compact set `Df(z₀)([-1, 1]²)`, whose measure tends to `4 |det Df(z₀)|`. -/
theorem ar_upper {f : ℂ → ℂ} {z₀ : ℂ} (hdiff : DifferentiableAt ℝ f z₀) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (volume (f '' closedRect (z₀.re - r) (z₀.re + r) (z₀.im - r) (z₀.im + r))).toReal / (4 * r ^ 2) ≤
        |LinearMap.det (fderiv ℝ f z₀ : ℂ →ₗ[ℝ] ℂ)| + η := by
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ f z₀
  set d : ℝ := |LinearMap.det (A : ℂ →ₗ[ℝ] ℂ)|
  have hK : IsCompact (A '' closedRect (-1) 1 (-1) 1) :=
    (acl_isCompact_closedRect _ _ _ _).image A.continuous
  have hvolK : volume (A '' closedRect (-1) 1 (-1) 1) = ENNReal.ofReal (d * 4) := by
    have h := ar_volume_affine_image_square A 0 zero_le_one
    simpa only [zero_add, one_pow, mul_one] using h
  have hlt : volume (A '' closedRect (-1) 1 (-1) 1) < ENNReal.ofReal (4 * (d + η)) := by
    rw [hvolK, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    linarith
  obtain ⟨ρ, hρT, hρ⟩ :=
    ((((tendsto_measure_cthickening_of_isCompact hK).eventually (eventually_lt_nhds hlt)).filter_mono
      nhdsWithin_le_nhds).and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists
  have hρ0 : (0 : ℝ) < ρ := hρ
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.1 hdiff.hasFDerivAt
  obtain ⟨κ, hκ, hball⟩ := Metric.eventually_nhds_iff.1 (hlo.def (half_pos hρ0))
  filter_upwards [Ioo_mem_nhdsGT (half_pos hκ)] with r hr
  obtain ⟨hr0, hrκ⟩ := hr
  have hsub := ar_up_image_subset (f := f) (z₀ := z₀) A (ρ := ρ) hr0 (fun z hz => by
    have hz' : z₀.re - r ≤ z.re ∧ z.re ≤ z₀.re + r ∧ z₀.im - r ≤ z.im ∧ z.im ≤ z₀.im + r := hz
    have h1 : |z.re - z₀.re| ≤ r := abs_le.2 ⟨by linarith, by linarith⟩
    have h2 : |z.im - z₀.im| ≤ r := abs_le.2 ⟨by linarith, by linarith⟩
    have hnorm : ‖z - z₀‖ ≤ 2 * r := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [Complex.sub_re, Complex.sub_im]
      linarith
    have hdist : dist (z - z₀) 0 < κ := by
      rw [dist_zero_right]
      linarith
    have hb := hball hdist
    rw [add_sub_cancel] at hb
    calc ‖f z - f z₀ - A (z - z₀)‖ ≤ ρ / 2 * ‖z - z₀‖ := hb
      _ ≤ ρ / 2 * (2 * r) := by gcongr
      _ = ρ * r := by ring)
  have hvol : volume (f '' closedRect (z₀.re - r) (z₀.re + r) (z₀.im - r) (z₀.im + r)) ≤
      ENNReal.ofReal (r ^ 2 * (4 * (d + η))) := by
    calc volume (f '' closedRect (z₀.re - r) (z₀.re + r) (z₀.im - r) (z₀.im + r))
        ≤ volume ((fun y => f z₀ + r • y) '' cthickening ρ (A '' closedRect (-1) 1 (-1) 1)) :=
          measure_mono hsub
      _ = ENNReal.ofReal (r ^ 2) * volume (cthickening ρ (A '' closedRect (-1) 1 (-1) 1)) :=
          ar_up_volume_image_homothety _ _ _
      _ ≤ ENNReal.ofReal (r ^ 2) * ENNReal.ofReal (4 * (d + η)) := by gcongr
      _ = ENNReal.ofReal (r ^ 2 * (4 * (d + η))) := (ENNReal.ofReal_mul (sq_nonneg r)).symm
  have hreal := ENNReal.toReal_le_of_le_ofReal (by positivity) hvol
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- Lower bound for the area of the image of a small square, for `f` continuous near `z₀` and differentiable at `z₀`:
`m(f(Q_r)) ≥ (|det Df(z₀)| - η) · 4r²` for small `r > 0`.  Trivial if the determinant vanishes; otherwise the
covering lemma `ar_covering_square` applied to `h ↦ Df(z₀)⁻¹ (f(z₀ + h) - f(z₀))` shows that `f(Q_r)` contains
`f(z₀) + Df(z₀)([-(1-t)r, (1-t)r]²)`. -/
theorem ar_lower {f : ℂ → ℂ} {z₀ : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 z₀) (hcont : ContinuousOn f U)
    (hdiff : DifferentiableAt ℝ f z₀) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), |LinearMap.det (fderiv ℝ f z₀ : ℂ →ₗ[ℝ] ℂ)| - η ≤
      (volume (f '' closedRect (z₀.re - r) (z₀.re + r) (z₀.im - r) (z₀.im + r))).toReal / (4 * r ^ 2) := by
  obtain ⟨A, hA⟩ : ∃ A : ℂ →L[ℝ] ℂ, fderiv ℝ f z₀ = A := ⟨_, rfl⟩
  have hderiv : HasFDerivAt f A z₀ := hA ▸ hdiff.hasFDerivAt
  rw [hA]
  obtain ⟨d, hd_def⟩ : ∃ d : ℝ, LinearMap.det (A : ℂ →ₗ[ℝ] ℂ) = d := ⟨_, rfl⟩
  rw [hd_def]
  by_cases hd : d = 0
  · refine Filter.Eventually.of_forall fun r => ?_
    rw [hd, abs_zero, zero_sub]
    exact (neg_nonpos.2 hη.le).trans (div_nonneg ENNReal.toReal_nonneg (by positivity))
  -- the inverse `B` of `A`
  have hdet : A.det ≠ 0 := by
    show LinearMap.det (A : ℂ →ₗ[ℝ] ℂ) ≠ 0
    rw [hd_def]
    exact hd
  obtain ⟨B, hAB, hBA⟩ : ∃ B : ℂ →L[ℝ] ℂ, (∀ y, A (B y) = y) ∧ ∀ x, B (A x) = x :=
    ⟨((A.toContinuousLinearEquivOfDetNeZero hdet).symm : ℂ →L[ℝ] ℂ),
      fun y => (A.toContinuousLinearEquivOfDetNeZero hdet).apply_symm_apply y,
      fun x => (A.toContinuousLinearEquivOfDetNeZero hdet).symm_apply_apply x⟩
  have hd_pos : 0 < |d| := abs_pos.2 hd
  -- the shrinking factor `1 - t`
  obtain ⟨t, ht_pos, ht_half, ht_eta⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧ t * (2 * |d|) ≤ η :=
    ⟨min (1 / 2) (η / (2 * |d|)), lt_min (by norm_num) (by positivity), min_le_left _ _,
      (le_div_iff₀ (by positivity)).1 (min_le_right _ _)⟩
  have hmain : |d| - η ≤ |d| * (1 - t) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg t) hd_pos.le]
  -- the approximation parameter `ε`
  obtain ⟨ε, hε, hBε⟩ := exists_pos_mul_lt (half_pos ht_pos) (2 * ‖B‖)
  have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hderiv).def hε
  obtain ⟨κ₁, hκ₁, hκ₁'⟩ := Metric.eventually_nhds_iff.1 hlo
  obtain ⟨κ₂, hκ₂, hκ₂U⟩ := Metric.mem_nhds_iff.1 hU
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min κ₁ κ₂ / 2 by positivity)] with r hr
  obtain ⟨hr0, hrκ⟩ := hr
  have hrκ₁ : 2 * r < κ₁ := by linarith [min_le_left κ₁ κ₂]
  have hrκ₂ : 2 * r < κ₂ := by linarith [min_le_right κ₁ κ₂]
  have hSnorm : ∀ h ∈ closedRect (-r) r (-r) r, ‖h‖ ≤ 2 * r := by
    intro h hh
    obtain ⟨h1, h2, h3, h4⟩ := hh
    have := Complex.norm_le_abs_re_add_abs_im h
    have : |h.re| ≤ r := abs_le.2 ⟨h1, h2⟩
    have : |h.im| ≤ r := abs_le.2 ⟨h3, h4⟩
    linarith
  have hSQ : ∀ h ∈ closedRect (-r) r (-r) r,
      z₀ + h ∈ closedRect (z₀.re - r) (z₀.re + r) (z₀.im - r) (z₀.im + r) := by
    intro h hh
    obtain ⟨h1, h2, h3, h4⟩ := hh
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Complex.add_re, Complex.add_im] <;> linarith
  have hQU : closedRect (z₀.re - r) (z₀.re + r) (z₀.im - r) (z₀.im + r) ⊆ U := by
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    apply hκ₂U
    rw [Metric.mem_ball, dist_eq_norm]
    have := Complex.norm_le_abs_re_add_abs_im (z - z₀)
    have : |(z - z₀).re| ≤ r :=
      abs_le.2 ⟨by simp only [Complex.sub_re]; linarith, by simp only [Complex.sub_re]; linarith⟩
    have : |(z - z₀).im| ≤ r :=
      abs_le.2 ⟨by simp only [Complex.sub_im]; linarith, by simp only [Complex.sub_im]; linarith⟩
    linarith
  -- the normalized map `g`
  have hgcont : ContinuousOn (fun h => B (f (z₀ + h) - f z₀)) (closedRect (-r) r (-r) r) := by
    have hadd : ContinuousOn (fun h : ℂ => z₀ + h) (closedRect (-r) r (-r) r) := by fun_prop
    have h1 : ContinuousOn (fun h => f (z₀ + h)) (closedRect (-r) r (-r) r) :=
      hcont.comp hadd fun h hh => hQU (hSQ h hh)
    exact B.continuous.comp_continuousOn (h1.sub continuousOn_const)
  have hclose : ∀ h ∈ closedRect (-r) r (-r) r, ‖B (f (z₀ + h) - f z₀) - h‖ < t * r := by
    intro h hh
    have hh2 := hSnorm h hh
    have hest : ‖f (z₀ + h) - f z₀ - A h‖ ≤ ε * ‖h‖ :=
      hκ₁' (by rw [dist_zero_right]; linarith)
    have hgh : B (f (z₀ + h) - f z₀) - h = B (f (z₀ + h) - f z₀ - A h) := by
      rw [map_sub B _ (A h), hBA]
    rw [hgh]
    calc ‖B (f (z₀ + h) - f z₀ - A h)‖ ≤ ‖B‖ * ‖f (z₀ + h) - f z₀ - A h‖ := B.le_opNorm _
      _ ≤ ‖B‖ * (ε * (2 * r)) :=
        mul_le_mul_of_nonneg_left (hest.trans (mul_le_mul_of_nonneg_left hh2 hε.le)) (norm_nonneg B)
      _ = 2 * ‖B‖ * ε * r := by ring
      _ ≤ t / 2 * r := mul_le_mul_of_nonneg_right hBε.le hr0.le
      _ < t * r := by nlinarith
  -- covering
  have hcov := ar_covering_square (mul_pos ht_pos hr0) hgcont hclose
  have hsub : (fun h' => f z₀ + A h') ''
      closedRect (-(r - t * r)) (r - t * r) (-(r - t * r)) (r - t * r) ⊆
        f '' closedRect (z₀.re - r) (z₀.re + r) (z₀.im - r) (z₀.im + r) := by
    rintro _ ⟨h', hh', rfl⟩
    obtain ⟨h, hh, rfl⟩ := hcov hh'
    refine ⟨z₀ + h, hSQ h hh, ?_⟩
    simp only [hAB]
    abel
  have hrt : 0 ≤ r - t * r := by nlinarith
  have hvol := ar_volume_affine_image_square A (f z₀) hrt
  rw [hd_def] at hvol
  have hfin : volume (f '' closedRect (z₀.re - r) (z₀.re + r) (z₀.im - r) (z₀.im + r)) ≠ ⊤ :=
    ((acl_isCompact_closedRect _ _ _ _).image_of_continuousOn (hcont.mono hQU)).measure_lt_top.ne
  have hle : ENNReal.ofReal (|d| * (4 * (r - t * r) ^ 2)) ≤
      volume (f '' closedRect (z₀.re - r) (z₀.re + r) (z₀.im - r) (z₀.im + r)) := by
    rw [← hvol]
    exact measure_mono hsub
  have hle' := (ENNReal.ofReal_le_iff_le_toReal hfin).1 hle
  rw [le_div_iff₀ (by positivity)]
  calc (|d| - η) * (4 * r ^ 2) ≤ |d| * (1 - t) ^ 2 * (4 * r ^ 2) :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
    _ = |d| * (4 * (r - t * r) ^ 2) := by ring
    _ ≤ _ := hle'

/-- At a point of differentiability, the area of the image of the square of side `2r`
centred at `z₀` is `4r² J_f(z₀) + o(r²)`: the set function `σ ↦ m(f(σ))` has derivative
`J_f(z₀)`.

Proved (2026-09-25): the upper bound by closed thickenings of `Df(z₀)([-1,1]²)` (`ar_upper`), the lower bound by
the square covering lemma `ar_covering_square` (a degree argument via continuous logarithms) applied to
`Df(z₀)⁻¹(f(z₀ + ·) - f(z₀))` (`ar_lower`); `J_f(z₀) = |det Df(z₀)|` since `J_f ≥ 0` for q.c. maps. -/
theorem area_image_square_deriv {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {z₀ : ℂ}
    (hz₀ : z₀ ∈ D) (hdiff : DifferentiableAt ℝ f z₀) :
    Tendsto (fun r : ℝ => (volume (f '' closedRect (z₀.re - r) (z₀.re + r) (z₀.im - r) (z₀.im + r))).toReal /
      (4 * r ^ 2)) (𝓝[>] 0) (𝓝 (jacobian f z₀)) := by
  have hU : D ∈ 𝓝 z₀ := hf.1.mem_nhds hz₀
  have hcont : ContinuousOn f D := hf.2.2.1.1
  rw [ar_jacobian_eq_abs_det hf hz₀ hdiff]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [ar_lower hU hcont hdiff (half_pos (sub_pos.2 ha))] with r hr
    linarith
  · filter_upwards [ar_upper hdiff (half_pos (sub_pos.2 hb))] with r hr
    linarith

theorem measurableSet_openRect (a b c d : ℝ) : MeasurableSet (openRect a b c d) := by
  have e : openRect a b c d = Complex.re ⁻¹' Ioo a b ∩ Complex.im ⁻¹' Ioo c d := by
    ext z
    simp [openRect, and_assoc]
  rw [e]
  exact (measurableSet_Ioo.preimage Complex.measurable_re).inter
    (measurableSet_Ioo.preimage Complex.measurable_im)

theorem openRect_subset_closedRect (a b c d : ℝ) : openRect a b c d ⊆ closedRect a b c d :=
  fun _ hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩

/-- At a point of differentiability the classical partial derivative `f'_x` is `f'(z)(1)`. -/
theorem partialX_eq_of_differentiableAt {f : ℂ → ℂ} {z : ℂ} (hz : DifferentiableAt ℝ f z) :
    partialX f z = fderiv ℝ f z 1 := by
  have h1 : HasDerivAt (fun t : ℝ => z + (t : ℂ)) 1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_add z
  exact (hz.hasFDerivAt.comp_hasDerivAt_of_eq 0 h1 (by simp)).deriv

/-- At a point of differentiability the classical partial derivative `f'_y` is `f'(z)(i)`. -/
theorem partialY_eq_of_differentiableAt {f : ℂ → ℂ} {z : ℂ} (hz : DifferentiableAt ℝ f z) :
    partialY f z = fderiv ℝ f z I := by
  have h1 : HasDerivAt (fun t : ℝ => z + (t : ℂ) * I) I 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const I).const_add z
  exact (hz.hasFDerivAt.comp_hasDerivAt_of_eq 0 h1 (by simp)).deriv

/-- For a quasiconformal map and a measurable `σ ⊆ D`, `∬_σ J_f ≤ m(f(σ))`.  Instead of the theory
of set functions used in the book, apply the change of variables formula on the set of points of
differentiability, which has full measure by Theorem 9.3. -/
theorem lintegral_jacobian_le_volume_image {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K)
    {σ : Set ℂ} (hσ : MeasurableSet σ) (hσD : σ ⊆ D) :
    ∫⁻ z in σ, ENNReal.ofReal (jacobian f z) ≤ volume (f '' σ) := by
  have hSm : MeasurableSet (σ ∩ {z | DifferentiableAt ℝ f z}) :=
    hσ.inter (measurableSet_of_differentiableAt ℝ f)
  have hnull : volume (σ \ (σ ∩ {z | DifferentiableAt ℝ f z})) = 0 := by
    have h := thm9_3_differentiable_ae hf
    rw [ae_restrict_iff' hf.1.measurableSet, ae_iff] at h
    exact measure_mono_null (fun z hz => fun h' => hz.2 ⟨hz.1, h' (hσD hz.1)⟩) h
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm
    (fun z hz => hz.2.hasFDerivAt.hasFDerivWithinAt)
    (hf.2.2.1.2.1.mono fun z hz => hσD hz.1) (fun _ => 1)
  simp only [mul_one, setLIntegral_const, one_mul] at hcv
  calc ∫⁻ z in σ, ENNReal.ofReal (jacobian f z)
      = ∫⁻ z in σ ∩ {z | DifferentiableAt ℝ f z}, ENNReal.ofReal (jacobian f z) :=
        setLIntegral_congr (ae_eq_set.2 ⟨hnull, by
          rw [diff_eq_empty.2 inter_subset_left, measure_empty]⟩)
    _ ≤ ∫⁻ z in σ ∩ {z | DifferentiableAt ℝ f z}, ENNReal.ofReal |(fderiv ℝ f z).det| := by
        refine setLIntegral_mono' hSm fun z hz => ENNReal.ofReal_le_ofReal ?_
        have e : (fderiv ℝ f z).det = jacobian f z := det_fderiv_eq_jacobian hz.2
        rw [e]
        exact le_abs_self _
    _ = volume (f '' (σ ∩ {z | DifferentiableAt ℝ f z})) := hcv.symm
    _ ≤ volume (f '' σ) := measure_mono (image_mono inter_subset_left)

/-- (9.17): for a quasiconformal map and a rectangle `R̄ ⊆ D`, `∬_R J_f ≤ m(f(R))`. -/
theorem eq9_17 {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {a b c d : ℝ} (_hab : a < b)
    (_hcd : c < d) (hR : closedRect a b c d ⊆ D) :
    ∫⁻ z in openRect a b c d, ENNReal.ofReal (jacobian f z) ≤ volume (f '' openRect a b c d) :=
  lintegral_jacobian_le_volume_image hf (measurableSet_openRect a b c d)
    ((openRect_subset_closedRect a b c d).trans hR)

/-- **Theorem 9.5**: a quasiconformal map has `L₂` generalized partial derivatives; moreover
`∬_R (|∂_z f| + |∂_{z̄} f|)² ≤ K m(f(R))` for rectangles `R̄ ⊆ D`. -/
theorem thm9_5_L2_derivatives {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) :
    HasGenPartials f (partialX f) (partialY f) D 2 ∧
      ∀ a b c d : ℝ, a < b → c < d → closedRect a b c d ⊆ D →
        ∫⁻ z in openRect a b c d, ENNReal.ofReal ((‖dz f z‖ + ‖dzbar f z‖) ^ 2) ≤
          ENNReal.ofReal K * volume (f '' openRect a b c d) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hf.2.1
  -- `(|∂_z f| + |∂_{z̄} f|)² ≤ K J_f` almost everywhere, by (9.12)
  have hsq : ∀ᵐ z ∂(volume.restrict D), (‖dz f z‖ + ‖dzbar f z‖) ^ 2 ≤ K * jacobian f z := by
    filter_upwards [thm9_4_dilatation_ae hf] with z hz
    have h0 : 0 ≤ ‖dz f z‖ + ‖dzbar f z‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    unfold jacobian
    nlinarith
  have hkey : ∀ σ : Set ℂ, MeasurableSet σ → σ ⊆ D →
      ∫⁻ z in σ, ENNReal.ofReal ((‖dz f z‖ + ‖dzbar f z‖) ^ 2) ≤
        ENNReal.ofReal K * volume (f '' σ) := by
    intro σ hσ hσD
    calc ∫⁻ z in σ, ENNReal.ofReal ((‖dz f z‖ + ‖dzbar f z‖) ^ 2)
        ≤ ∫⁻ z in σ, ENNReal.ofReal K * ENNReal.ofReal (jacobian f z) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hσD hsq] with z hz
          rw [← ENNReal.ofReal_mul hK0]
          exact ENNReal.ofReal_le_ofReal hz
      _ = ENNReal.ofReal K * ∫⁻ z in σ, ENNReal.ofReal (jacobian f z) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K * volume (f '' σ) := by
          gcongr
          exact lintegral_jacobian_le_volume_image hf hσ hσD
  refine ⟨lemma9_2_genPartials_of_isACL hf.1 one_le_two (by simp) (thm9_1_isACL hf)
    fun C hCD hC => ?_, fun a b c d _ _ hR =>
      hkey _ (measurableSet_openRect a b c d) ((openRect_subset_closedRect a b c d).trans hR)⟩
  -- the partial derivatives are locally square integrable
  have hdiffC : ∀ᵐ z ∂(volume.restrict C), DifferentiableAt ℝ f z :=
    ae_restrict_of_ae_restrict_of_subset hCD (thm9_3_differentiable_ae hf)
  have hgm : Measurable fun z => ‖dz f z‖ + ‖dzbar f z‖ :=
    (measurable_dz f).norm.add (measurable_dzbar f).norm
  have hfin : volume (f '' C) < ⊤ :=
    (hC.image_of_continuousOn (hf.2.2.1.1.mono hCD)).measure_lt_top
  have hg : MemLp (fun z => ‖dz f z‖ + ‖dzbar f z‖) 2 (volume.restrict C) := by
    rw [memLp_two_iff_integrable_sq hgm.aestronglyMeasurable]
    refine ⟨(hgm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => sq_nonneg _)]
    exact (hkey C hC.isClosed.measurableSet hCD).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  have hbound : ∀ w z, DifferentiableAt ℝ f z → ‖w‖ = 1 →
      ‖fderiv ℝ f z w‖ ≤ ‖‖dz f z‖ + ‖dzbar f z‖‖ := fun w z hz hw => by
    rw [fderiv_eq_dz_dzbar hz, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc ‖dz f z * w + dzbar f z * conj w‖ ≤ ‖dz f z * w‖ + ‖dzbar f z * conj w‖ := norm_add_le _ _
      _ = ‖dz f z‖ + ‖dzbar f z‖ := by rw [norm_mul, norm_mul, norm_conj, hw, mul_one, mul_one]
  refine ⟨hg.of_le ?_ ?_, hg.of_le ?_ ?_⟩
  · exact (measurable_fderiv_apply_const ℝ f (1 : ℂ)).aestronglyMeasurable.congr
      (hdiffC.mono fun z hz => (partialX_eq_of_differentiableAt hz).symm)
  · filter_upwards [hdiffC] with z hz
    rw [partialX_eq_of_differentiableAt hz]
    exact hbound 1 z hz (by simp)
  · exact (measurable_fderiv_apply_const ℝ f I).aestronglyMeasurable.congr
      (hdiffC.mono fun z hz => (partialY_eq_of_differentiableAt hz).symm)
  · filter_upwards [hdiffC] with z hz
    rw [partialY_eq_of_differentiableAt hz]
    exact hbound I z hz (by simp)

/-! ### Theorem 9.6 track — helpers of piece N -/


theorem ac_n_c_min_reflect (a b x y : ℝ) : min (a + b - y) (a + b - x) = a + b - max x y := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, min_eq_left (by linarith : a + b - y ≤ a + b - x)]
  · rw [max_eq_left h, min_eq_right (by linarith : a + b - x ≤ a + b - y)]

theorem ac_n_c_max_reflect (a b x y : ℝ) : max (a + b - y) (a + b - x) = a + b - min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_right (by linarith : a + b - y ≤ a + b - x)]
  · rw [min_eq_right h, max_eq_left (by linarith : a + b - x ≤ a + b - y)]

theorem ac_n_c_reflect_mem_uIcc {a b x : ℝ} (hx : x ∈ uIcc a b) : a + b - x ∈ uIcc a b := by
  rw [mem_uIcc] at hx ⊢
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨by linarith, by linarith⟩
  · right; exact ⟨by linarith, by linarith⟩

/-- `AbsolutelyContinuousOnInterval` transfers under the reflection `t ↦ a + b - t` of `[a,b]`. -/
theorem ac_n_c_reflect {φ : ℝ → ℂ} {a b : ℝ} (hφ : AbsolutelyContinuousOnInterval φ a b) :
    AbsolutelyContinuousOnInterval (fun t => φ (a + b - t)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hφ ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hφ ε hε
  refine ⟨δ, hδ, ?_⟩
  rintro ⟨n, I⟩ hE hlt
  set I' : ℕ → ℝ × ℝ := fun i => (a + b - (I i).2, a + b - (I i).1) with hI'def
  have hlen : ∀ i, dist (I' i).1 (I' i).2 = dist (I i).1 (I i).2 := by
    intro i
    simp only [hI'def, Real.dist_eq]
    rw [show a + b - (I i).2 - (a + b - (I i).1) = -((I i).2 - (I i).1) by ring, abs_neg,
      abs_sub_comm]
  have hE' : ((n, I') : ℕ × (ℕ → ℝ × ℝ)) ∈ AbsolutelyContinuousOnInterval.disjWithin a b := by
    refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
    · obtain ⟨h1, h2⟩ := hE.1 i hi
      exact ⟨ac_n_c_reflect_mem_uIcc h2, ac_n_c_reflect_mem_uIcc h1⟩
    · have hd := hE.2 hi hj hij
      show Disjoint (uIoc (I' i).1 (I' i).2) (uIoc (I' j).1 (I' j).2)
      have hdd : Disjoint (uIoc (I i).1 (I i).2) (uIoc (I j).1 (I j).2) := hd
      simp only [uIoc] at hdd ⊢
      simp only [hI'def]
      rw [ac_n_c_min_reflect, ac_n_c_max_reflect, ac_n_c_min_reflect, ac_n_c_max_reflect]
      rw [Set.Ioc_disjoint_Ioc] at hdd ⊢
      rw [ac_n_c_min_reflect, ac_n_c_max_reflect]
      have hc1 : max (min (I j).1 (I j).2) (min (I i).1 (I i).2) =
          max (min (I i).1 (I i).2) (min (I j).1 (I j).2) := max_comm _ _
      have hc2 : min (max (I j).1 (I j).2) (max (I i).1 (I i).2) =
          min (max (I i).1 (I i).2) (max (I j).1 (I j).2) := min_comm _ _
      linarith [hdd, hc1, hc2]
  have heq : ∑ i ∈ Finset.range n, dist (I' i).1 (I' i).2 =
      ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 :=
    Finset.sum_congr rfl (fun i _ => hlen i)
  have hlt' : ∑ i ∈ Finset.range n, dist (I' i).1 (I' i).2 < δ := heq ▸ hlt
  have hkey := hbound (n, I') hE' hlt'
  calc ∑ i ∈ Finset.range n,
        dist ((fun t => φ (a + b - t)) (I i).1) ((fun t => φ (a + b - t)) (I i).2)
      = ∑ i ∈ Finset.range n, dist (φ (I' i).1) (φ (I' i).2) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hI'def]; rw [dist_comm]
    _ < ε := hkey

/-- `‖deriv φ‖` is interval-integrable on `[a,b]` for `φ : ℝ → ℂ` absolutely continuous on
`[a,b]`, via the real/imaginary decomposition. -/
theorem ac_n_c_intervalIntegrable_norm_deriv {φ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hφ : AbsolutelyContinuousOnInterval φ a b) :
    IntervalIntegrable (fun x => ‖deriv φ x‖) volume a b := by
  have hre : AbsolutelyContinuousOnInterval (fun x => (φ x).re) a b := acl_AC_re hφ
  have him : AbsolutelyContinuousOnInterval (fun x => (φ x).im) a b := acl_AC_im hφ
  have hdiff : ∀ᵐ x, x ∈ uIcc a b → deriv φ x =
      ((deriv (fun x => (φ x).re) x : ℝ) : ℂ) + ((deriv (fun x => (φ x).im) x : ℝ) : ℂ) * I := by
    filter_upwards [hre.ae_differentiableAt, him.ae_differentiableAt] with x h1 h2 hx
    have hd : HasDerivAt (fun x => ((φ x).re : ℂ) + ((φ x).im : ℂ) * I)
        (((deriv (fun x => (φ x).re) x : ℝ) : ℂ) + ((deriv (fun x => (φ x).im) x : ℝ) : ℂ) * I) x :=
      ((h1 hx).hasDerivAt.ofReal_comp).add (((h2 hx).hasDerivAt.ofReal_comp).mul_const I)
    have e : (fun x => ((φ x).re : ℂ) + ((φ x).im : ℂ) * I) = φ :=
      funext fun x => Complex.re_add_im _
    rw [e] at hd
    exact hd.deriv
  have hbound : ∀ᵐ x, x ∈ uIcc a b →
      ‖deriv φ x‖ ≤ |deriv (fun x => (φ x).re) x| + |deriv (fun x => (φ x).im) x| := by
    filter_upwards [hdiff] with x hx hx'
    rw [hx hx']
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Complex.norm_real, Real.norm_eq_abs]
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  have hintre0 : IntervalIntegrable (fun x => deriv (fun x => (φ x).re) x) volume a b :=
    hre.intervalIntegrable_deriv
  have hintim0 : IntervalIntegrable (fun x => deriv (fun x => (φ x).im) x) volume a b :=
    him.intervalIntegrable_deriv
  have hintre : IntervalIntegrable (fun x => |deriv (fun x => (φ x).re) x|) volume a b :=
    hintre0.abs
  have hintim : IntervalIntegrable (fun x => |deriv (fun x => (φ x).im) x|) volume a b :=
    hintim0.abs
  have hcombo : AEStronglyMeasurable
      (fun x => ((deriv (fun x => (φ x).re) x : ℝ) : ℂ) +
        ((deriv (fun x => (φ x).im) x : ℝ) : ℂ) * I) (volume.restrict (Ioc a b)) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hintre0.aestronglyMeasurable).add
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable
        hintim0.aestronglyMeasurable).mul_const I)
  have hdiff' : (deriv φ) =ᵐ[volume.restrict (Ioc a b)]
      (fun x => ((deriv (fun x => (φ x).re) x : ℝ) : ℂ) +
        ((deriv (fun x => (φ x).im) x : ℝ) : ℂ) * I) := by
    show ∀ᵐ x ∂(volume.restrict (Ioc a b)), deriv φ x = _
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hdiff] with x hx hmem
    exact hx (Ioc_subset_Icc_self.trans Icc_subset_uIcc hmem)
  have hmeas0 : AEStronglyMeasurable (fun x => ‖deriv φ x‖) (volume.restrict (Ioc a b)) :=
    (hcombo.congr hdiff'.symm).norm
  have hmeas : AEStronglyMeasurable (fun x => ‖deriv φ x‖) (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab]; exact hmeas0
  refine (hintre.add hintim).mono_fun' hmeas ?_
  rw [Set.uIoc_of_le hab]
  filter_upwards [ae_restrict_of_ae hbound, self_mem_ae_restrict measurableSet_Ioc]
    with x hx hxmem
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact hx (Ioc_subset_Icc_self.trans Icc_subset_uIcc hxmem)

/-- Generic per-side helper: for `φ` absolutely continuous on `[p, p+a]`, the norm of the
difference between `φ` at any two points of `[p,p+a]` is bounded by the sub-integral of
`‖deriv φ‖` between them. -/
theorem ac_n_c_norm_diff_le {φ : ℝ → ℂ} {p a : ℝ}
    (hφ : AbsolutelyContinuousOnInterval φ p (p + a)) {u1 u2 : ℝ}
    (hu1 : u1 ∈ Icc p (p + a)) (hu2 : u2 ∈ Icc p (p + a)) (hu12 : u1 ≤ u2) :
    ‖φ u2 - φ u1‖ ≤ ∫ x in u1..u2, ‖deriv φ x‖ := by
  have hpa : p ≤ p + a := hu1.1.trans hu1.2
  have hsub : uIcc u1 u2 ⊆ uIcc p (p + a) := by
    rw [uIcc_of_le hu12, uIcc_of_le hpa]
    exact Icc_subset_Icc hu1.1 hu2.2
  have hφ' : AbsolutelyContinuousOnInterval φ u1 u2 := hφ.mono hsub
  rw [← integral_deriv_eq_sub_of_absolutelyContinuous hφ']
  exact intervalIntegral.norm_integral_le_integral_norm hu12

/-- Generic per-side additivity: the sub-integral of `‖deriv φ‖` from `p` to `u` plus from `u` to
`p+a` equals the full-side integral, for `φ` absolutely continuous on `[p,p+a]`. -/
theorem ac_n_c_side_additive {φ : ℝ → ℂ} {p a : ℝ}
    (hφ : AbsolutelyContinuousOnInterval φ p (p + a)) {u : ℝ} (hu : u ∈ Icc p (p + a)) :
    (∫ x in p..u, ‖deriv φ x‖) + (∫ x in u..(p + a), ‖deriv φ x‖) =
      ∫ x in p..(p + a), ‖deriv φ x‖ := by
  have hpa : p ≤ p + a := hu.1.trans hu.2
  have hp_u : uIcc p u ⊆ uIcc p (p + a) := by
    rw [uIcc_of_le hu.1, uIcc_of_le hpa]
    exact Icc_subset_Icc le_rfl hu.2
  have hu_pa : uIcc u (p + a) ⊆ uIcc p (p + a) := by
    rw [uIcc_of_le hu.2, uIcc_of_le hpa]
    exact Icc_subset_Icc hu.1 le_rfl
  have h1 : IntervalIntegrable (fun x => ‖deriv φ x‖) volume p u :=
    ac_n_c_intervalIntegrable_norm_deriv hu.1 (hφ.mono hp_u)
  have h2 : IntervalIntegrable (fun x => ‖deriv φ x‖) volume u (p + a) :=
    ac_n_c_intervalIntegrable_norm_deriv hu.2 (hφ.mono hu_pa)
  exact intervalIntegral.integral_add_adjacent_intervals h1 h2

/-- The frontier of a closed rectangle, as the union of its four sides. -/
theorem ac_n_c_frontier_closedRect {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    frontier (closedRect a b c d) =
      {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ (z.im = c ∨ z.im = d)} ∪
      {z : ℂ | (z.re = a ∨ z.re = b) ∧ c ≤ z.im ∧ z.im ≤ d} := by
  rw [acl_closedRect_eq, frontier_reProdIm, closure_Icc, closure_Icc, frontier_Icc hab,
    frontier_Icc hcd]
  ext z
  simp only [mem_union, mem_reProdIm, mem_Icc, mem_insert_iff, mem_singleton_iff, mem_setOf_eq]
  tauto

/-- Given `f` continuous+injective on an open `D` containing the closed square `Q̄`, there are
two points `ζ, ζ'` on the frontier of `Q̄` whose images are as far apart as any two images of
points of `Q̄` — i.e. `f''Q̄` is contained in `closedBall (f ζ') (dist (f ζ) (f ζ'))`. -/
theorem ac_n_c_exists_diam_frontier {f : ℂ → ℂ} {D : Set ℂ}
    (hfc : ContinuousOn f D) (hfi : InjOn f D) {x₀ y₀ a : ℝ} (ha : 0 < a)
    (hQ : closedRect x₀ (x₀ + a) y₀ (y₀ + a) ⊆ D) :
    ∃ ζ ∈ frontier (closedRect x₀ (x₀ + a) y₀ (y₀ + a)),
      ∃ ζ' ∈ frontier (closedRect x₀ (x₀ + a) y₀ (y₀ + a)),
        ∀ z ∈ closedRect x₀ (x₀ + a) y₀ (y₀ + a), dist (f z) (f ζ') ≤ dist (f ζ) (f ζ') := by
  set Q := closedRect x₀ (x₀ + a) y₀ (y₀ + a) with hQdef
  have hQcpt : IsCompact Q := acl_isCompact_closedRect _ _ _ _
  have hQne : Q.Nonempty := ⟨(x₀ : ℂ) + (y₀ : ℂ) * I, by
    simp [hQdef, closedRect, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    linarith⟩
  have hfQcont : ContinuousOn f Q := hfc.mono hQ
  have hf1 : ContinuousOn (fun p : ℂ × ℂ => f p.1) (Q ×ˢ Q) :=
    hfQcont.comp' continuousOn_fst (fun p hp => hp.1)
  have hf2 : ContinuousOn (fun p : ℂ × ℂ => f p.2) (Q ×ˢ Q) :=
    hfQcont.comp' continuousOn_snd (fun p hp => hp.2)
  have hcont : ContinuousOn (fun p : ℂ × ℂ => dist (f p.1) (f p.2)) (Q ×ˢ Q) :=
    continuous_dist.comp_continuousOn (hf1.prodMk hf2)
  obtain ⟨⟨P, R⟩, hPRmem, hPRmax0⟩ :=
    (hQcpt.prod hQcpt).exists_isMaxOn (hQne.prod hQne) hcont
  rw [isMaxOn_iff] at hPRmax0
  have hPRmax : ∀ p ∈ Q ×ˢ Q, dist (f p.1) (f p.2) ≤ dist (f P) (f R) := hPRmax0
  have hPmem : P ∈ Q := hPRmem.1
  have hRmem : R ∈ Q := hPRmem.2
  have hglobal : ∀ z ∈ Q, ∀ z' ∈ Q, dist (f z) (f z') ≤ dist (f P) (f R) :=
    fun z hz z' hz' => hPRmax (z, z') (mem_prod.2 ⟨hz, hz'⟩)
  have hopen : ∀ U ⊆ D, IsOpen U → IsOpen (f '' U) := fun U hUD hUo =>
    isOpen_image_of_continuousOn_injOn hUo (hfc.mono hUD) (hfi.mono hUD)
  have hxlt : x₀ < x₀ + a := by linarith
  have hylt : y₀ < y₀ + a := by linarith
  have hQclosed : IsClosed Q := hQcpt.isClosed
  obtain ⟨ζ, hζfr, hζmax⟩ :=
    menchoff_max_principle hfc hopen hxlt hylt hQ (f R) hPmem
  have hζmem : ζ ∈ Q := by
    have := frontier_subset_closure hζfr; rwa [hQclosed.closure_eq] at this
  have hζmax' : dist (f P) (f R) ≤ dist (f ζ) (f R) := by
    rw [dist_eq_norm, dist_eq_norm]; exact hζmax
  have heq1 : dist (f ζ) (f R) = dist (f P) (f R) :=
    le_antisymm (hglobal ζ hζmem R hRmem) hζmax'
  obtain ⟨ζ', hζ'fr, hζ'max⟩ :=
    menchoff_max_principle hfc hopen hxlt hylt hQ (f ζ) hRmem
  have hζ'mem : ζ' ∈ Q := by
    have := frontier_subset_closure hζ'fr; rwa [hQclosed.closure_eq] at this
  have hζ'max' : dist (f R) (f ζ) ≤ dist (f ζ') (f ζ) := by
    rw [dist_eq_norm, dist_eq_norm]; exact hζ'max
  have heq2 : dist (f ζ) (f ζ') = dist (f P) (f R) := by
    have hge : dist (f P) (f R) ≤ dist (f ζ) (f ζ') := by
      rw [dist_comm (f ζ) (f ζ')]
      calc dist (f P) (f R) = dist (f R) (f ζ) := heq1.symm.trans (dist_comm (f ζ) (f R))
        _ ≤ dist (f ζ') (f ζ) := hζ'max'
    exact le_antisymm (hglobal ζ hζmem ζ' hζ'mem) hge
  refine ⟨ζ, hζfr, ζ', hζ'fr, fun z hz => ?_⟩
  rw [heq2]
  exact hglobal z hz ζ' hζ'mem

/-- `‖φ (p+a) - φ p‖` is bounded by the full-side integral, for `φ` AC on `[p,p+a]`. -/
theorem ac_n_c_norm_diff_full {φ : ℝ → ℂ} {p a : ℝ} (ha : 0 ≤ a)
    (hφ : AbsolutelyContinuousOnInterval φ p (p + a)) :
    ‖φ (p + a) - φ p‖ ≤ ∫ x in p..(p + a), ‖deriv φ x‖ :=
  ac_n_c_norm_diff_le hφ ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)

/-- **Same-side generic arc bound.** `φ0,φ1,φ2,φ3` are `f` restricted to 4 consecutive sides
of a quadrilateral loop (each AC on its own `[pᵢ,pᵢ+a]`), joined end-to-start cyclically. For
`ζ = φ0 u`, `ζ' = φ0 v` both on the FIRST side, `2 * dist ζ ζ'` is bounded by the sum of all
four full-side integrals. -/
theorem ac_n_c_arc_same_side {φ0 φ1 φ2 φ3 : ℝ → ℂ} {p0 p1 p2 p3 a : ℝ} (ha : 0 ≤ a)
    (h0 : AbsolutelyContinuousOnInterval φ0 p0 (p0 + a))
    (h1 : AbsolutelyContinuousOnInterval φ1 p1 (p1 + a))
    (h2 : AbsolutelyContinuousOnInterval φ2 p2 (p2 + a))
    (h3 : AbsolutelyContinuousOnInterval φ3 p3 (p3 + a))
    (hjoin01 : φ0 (p0 + a) = φ1 p1) (hjoin12 : φ1 (p1 + a) = φ2 p2)
    (hjoin23 : φ2 (p2 + a) = φ3 p3) (hjoin30 : φ3 (p3 + a) = φ0 p0)
    {u v : ℝ} (hu : u ∈ Icc p0 (p0 + a)) (hv : v ∈ Icc p0 (p0 + a)) (huv : u ≤ v) :
    2 * dist (φ0 u) (φ0 v) ≤
      (∫ x in p0..(p0 + a), ‖deriv φ0 x‖) + (∫ x in p1..(p1 + a), ‖deriv φ1 x‖) +
        (∫ x in p2..(p2 + a), ‖deriv φ2 x‖) + (∫ x in p3..(p3 + a), ‖deriv φ3 x‖) := by
  have hpa0 : p0 ≤ p0 + a := hu.1.trans hu.2
  have hdirect : dist (φ0 u) (φ0 v) ≤ ∫ x in u..v, ‖deriv φ0 x‖ := by
    rw [dist_eq_norm, norm_sub_rev]; exact ac_n_c_norm_diff_le h0 hu hv huv
  have hop1 : dist (φ0 u) (φ0 p0) ≤ ∫ x in p0..u, ‖deriv φ0 x‖ := by
    rw [dist_comm, dist_eq_norm, norm_sub_rev]
    exact ac_n_c_norm_diff_le h0 ⟨le_rfl, hpa0⟩ hu hu.1
  have hop2 : dist (φ0 p0) (φ3 p3) ≤ ∫ x in p3..(p3 + a), ‖deriv φ3 x‖ := by
    rw [← hjoin30, dist_comm, dist_eq_norm, norm_sub_rev]; exact ac_n_c_norm_diff_full ha h3
  have hop3 : dist (φ3 p3) (φ2 p2) ≤ ∫ x in p2..(p2 + a), ‖deriv φ2 x‖ := by
    rw [← hjoin23, dist_comm, dist_eq_norm, norm_sub_rev]; exact ac_n_c_norm_diff_full ha h2
  have hop4 : dist (φ2 p2) (φ1 p1) ≤ ∫ x in p1..(p1 + a), ‖deriv φ1 x‖ := by
    rw [← hjoin12, dist_comm, dist_eq_norm, norm_sub_rev]; exact ac_n_c_norm_diff_full ha h1
  have hop5 : dist (φ1 p1) (φ0 v) ≤ ∫ x in v..(p0 + a), ‖deriv φ0 x‖ := by
    rw [← hjoin01, dist_eq_norm]; exact ac_n_c_norm_diff_le h0 hv ⟨hpa0, le_rfl⟩ hv.2
  have hother : dist (φ0 u) (φ0 v) ≤
      (∫ x in p0..u, ‖deriv φ0 x‖) + (∫ x in p3..(p3 + a), ‖deriv φ3 x‖) +
        (∫ x in p2..(p2 + a), ‖deriv φ2 x‖) + (∫ x in p1..(p1 + a), ‖deriv φ1 x‖) +
        (∫ x in v..(p0 + a), ‖deriv φ0 x‖) := by
    calc dist (φ0 u) (φ0 v)
        ≤ dist (φ0 u) (φ0 p0) + dist (φ0 p0) (φ0 v) := dist_triangle _ _ _
      _ ≤ dist (φ0 u) (φ0 p0) + (dist (φ0 p0) (φ3 p3) + dist (φ3 p3) (φ0 v)) := by
          gcongr; exact dist_triangle _ _ _
      _ ≤ dist (φ0 u) (φ0 p0) + (dist (φ0 p0) (φ3 p3) +
          (dist (φ3 p3) (φ2 p2) + dist (φ2 p2) (φ0 v))) := by
          gcongr; exact dist_triangle _ _ _
      _ ≤ dist (φ0 u) (φ0 p0) + (dist (φ0 p0) (φ3 p3) + (dist (φ3 p3) (φ2 p2) +
          (dist (φ2 p2) (φ1 p1) + dist (φ1 p1) (φ0 v)))) := by
          gcongr; exact dist_triangle _ _ _
      _ ≤ (∫ x in p0..u, ‖deriv φ0 x‖) + ((∫ x in p3..(p3 + a), ‖deriv φ3 x‖) +
          ((∫ x in p2..(p2 + a), ‖deriv φ2 x‖) +
            ((∫ x in p1..(p1 + a), ‖deriv φ1 x‖) + (∫ x in v..(p0 + a), ‖deriv φ0 x‖)))) := by
          gcongr
      _ = _ := by ring
  have hsplitu : (∫ x in p0..u, ‖deriv φ0 x‖) + (∫ x in u..(p0 + a), ‖deriv φ0 x‖) =
      ∫ x in p0..(p0 + a), ‖deriv φ0 x‖ := ac_n_c_side_additive h0 hu
  have hsplituv : (∫ x in u..v, ‖deriv φ0 x‖) + (∫ x in v..(p0 + a), ‖deriv φ0 x‖) =
      ∫ x in u..(p0 + a), ‖deriv φ0 x‖ := by
    have hi1 : IntervalIntegrable (fun x => ‖deriv φ0 x‖) volume u v :=
      ac_n_c_intervalIntegrable_norm_deriv huv (h0.mono (by
        rw [uIcc_of_le huv, uIcc_of_le hpa0]; exact Icc_subset_Icc hu.1 hv.2))
    have hi2 : IntervalIntegrable (fun x => ‖deriv φ0 x‖) volume v (p0 + a) :=
      ac_n_c_intervalIntegrable_norm_deriv hv.2 (h0.mono (by
        rw [uIcc_of_le hv.2, uIcc_of_le hpa0]; exact Icc_subset_Icc hv.1 le_rfl))
    exact intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  linarith [hdirect, hother, hsplitu, hsplituv]

/-- **Adjacent-side generic arc bound.** As `ac_n_c_arc_same_side`, but `ζ = φ0 u` is on the
FIRST side and `ζ' = φ1 w` is on the SECOND (consecutive) side. -/
theorem ac_n_c_arc_adjacent_side {φ0 φ1 φ2 φ3 : ℝ → ℂ} {p0 p1 p2 p3 a : ℝ} (ha : 0 ≤ a)
    (h0 : AbsolutelyContinuousOnInterval φ0 p0 (p0 + a))
    (h1 : AbsolutelyContinuousOnInterval φ1 p1 (p1 + a))
    (h2 : AbsolutelyContinuousOnInterval φ2 p2 (p2 + a))
    (h3 : AbsolutelyContinuousOnInterval φ3 p3 (p3 + a))
    (hjoin01 : φ0 (p0 + a) = φ1 p1) (hjoin12 : φ1 (p1 + a) = φ2 p2)
    (hjoin23 : φ2 (p2 + a) = φ3 p3) (hjoin30 : φ3 (p3 + a) = φ0 p0)
    {u w : ℝ} (hu : u ∈ Icc p0 (p0 + a)) (hw : w ∈ Icc p1 (p1 + a)) :
    2 * dist (φ0 u) (φ1 w) ≤
      (∫ x in p0..(p0 + a), ‖deriv φ0 x‖) + (∫ x in p1..(p1 + a), ‖deriv φ1 x‖) +
        (∫ x in p2..(p2 + a), ‖deriv φ2 x‖) + (∫ x in p3..(p3 + a), ‖deriv φ3 x‖) := by
  have hpa0 : p0 ≤ p0 + a := hu.1.trans hu.2
  have hpa1 : p1 ≤ p1 + a := hw.1.trans hw.2
  have hdirect : dist (φ0 u) (φ1 w) ≤
      (∫ x in u..(p0 + a), ‖deriv φ0 x‖) + (∫ x in p1..w, ‖deriv φ1 x‖) := by
    calc dist (φ0 u) (φ1 w)
        ≤ dist (φ0 u) (φ0 (p0 + a)) + dist (φ0 (p0 + a)) (φ1 w) := dist_triangle _ _ _
      _ = dist (φ0 u) (φ0 (p0 + a)) + dist (φ1 p1) (φ1 w) := by rw [hjoin01]
      _ ≤ (∫ x in u..(p0 + a), ‖deriv φ0 x‖) + (∫ x in p1..w, ‖deriv φ1 x‖) := by
          gcongr
          · rw [dist_eq_norm, norm_sub_rev]
            exact ac_n_c_norm_diff_le h0 hu ⟨hpa0, le_rfl⟩ hu.2
          · rw [dist_eq_norm, norm_sub_rev]
            exact ac_n_c_norm_diff_le h1 ⟨le_rfl, hpa1⟩ hw hw.1
  have hother : dist (φ0 u) (φ1 w) ≤
      (∫ x in p0..u, ‖deriv φ0 x‖) + (∫ x in p3..(p3 + a), ‖deriv φ3 x‖) +
        (∫ x in p2..(p2 + a), ‖deriv φ2 x‖) + (∫ x in w..(p1 + a), ‖deriv φ1 x‖) := by
    calc dist (φ0 u) (φ1 w)
        ≤ dist (φ0 u) (φ0 p0) + dist (φ0 p0) (φ1 w) := dist_triangle _ _ _
      _ = dist (φ0 u) (φ0 p0) + dist (φ3 (p3 + a)) (φ1 w) := by rw [hjoin30]
      _ ≤ dist (φ0 u) (φ0 p0) + (dist (φ3 (p3 + a)) (φ3 p3) + dist (φ3 p3) (φ1 w)) := by
          gcongr; exact dist_triangle _ _ _
      _ = dist (φ0 u) (φ0 p0) + (dist (φ3 (p3 + a)) (φ3 p3) + dist (φ2 (p2 + a)) (φ1 w)) := by
          rw [hjoin23]
      _ ≤ dist (φ0 u) (φ0 p0) + (dist (φ3 (p3 + a)) (φ3 p3) +
          (dist (φ2 (p2 + a)) (φ2 p2) + dist (φ2 p2) (φ1 w))) := by
          gcongr; exact dist_triangle _ _ _
      _ = dist (φ0 u) (φ0 p0) + (dist (φ3 (p3 + a)) (φ3 p3) +
          (dist (φ2 (p2 + a)) (φ2 p2) + dist (φ1 (p1 + a)) (φ1 w))) := by rw [hjoin12]
      _ ≤ (∫ x in p0..u, ‖deriv φ0 x‖) + ((∫ x in p3..(p3 + a), ‖deriv φ3 x‖) +
          ((∫ x in p2..(p2 + a), ‖deriv φ2 x‖) + (∫ x in w..(p1 + a), ‖deriv φ1 x‖))) := by
          gcongr
          · rw [dist_comm, dist_eq_norm, norm_sub_rev]
            exact ac_n_c_norm_diff_le h0 ⟨le_rfl, hpa0⟩ hu hu.1
          · rw [dist_eq_norm]; exact ac_n_c_norm_diff_full ha h3
          · rw [dist_eq_norm]; exact ac_n_c_norm_diff_full ha h2
          · rw [dist_eq_norm]; exact ac_n_c_norm_diff_le h1 hw ⟨hpa1, le_rfl⟩ hw.2
      _ = _ := by ring
  have hsplit0 : (∫ x in p0..u, ‖deriv φ0 x‖) + (∫ x in u..(p0 + a), ‖deriv φ0 x‖) =
      ∫ x in p0..(p0 + a), ‖deriv φ0 x‖ := ac_n_c_side_additive h0 hu
  have hsplit1 : (∫ x in p1..w, ‖deriv φ1 x‖) + (∫ x in w..(p1 + a), ‖deriv φ1 x‖) =
      ∫ x in p1..(p1 + a), ‖deriv φ1 x‖ := ac_n_c_side_additive h1 hw
  linarith [hdirect, hother, hsplit0, hsplit1]

/-- **Opposite-side generic arc bound.** As above, but `ζ = φ0 u` is on the FIRST side and
`ζ' = φ2 v` is on the OPPOSITE (third) side. -/
theorem ac_n_c_arc_opposite_side {φ0 φ1 φ2 φ3 : ℝ → ℂ} {p0 p1 p2 p3 a : ℝ} (ha : 0 ≤ a)
    (h0 : AbsolutelyContinuousOnInterval φ0 p0 (p0 + a))
    (h1 : AbsolutelyContinuousOnInterval φ1 p1 (p1 + a))
    (h2 : AbsolutelyContinuousOnInterval φ2 p2 (p2 + a))
    (h3 : AbsolutelyContinuousOnInterval φ3 p3 (p3 + a))
    (hjoin01 : φ0 (p0 + a) = φ1 p1) (hjoin12 : φ1 (p1 + a) = φ2 p2)
    (hjoin23 : φ2 (p2 + a) = φ3 p3) (hjoin30 : φ3 (p3 + a) = φ0 p0)
    {u v : ℝ} (hu : u ∈ Icc p0 (p0 + a)) (hv : v ∈ Icc p2 (p2 + a)) :
    2 * dist (φ0 u) (φ2 v) ≤
      (∫ x in p0..(p0 + a), ‖deriv φ0 x‖) + (∫ x in p1..(p1 + a), ‖deriv φ1 x‖) +
        (∫ x in p2..(p2 + a), ‖deriv φ2 x‖) + (∫ x in p3..(p3 + a), ‖deriv φ3 x‖) := by
  have hpa0 : p0 ≤ p0 + a := hu.1.trans hu.2
  have hpa2 : p2 ≤ p2 + a := hv.1.trans hv.2
  have hdirect : dist (φ0 u) (φ2 v) ≤
      (∫ x in u..(p0 + a), ‖deriv φ0 x‖) + (∫ x in p1..(p1 + a), ‖deriv φ1 x‖) +
        (∫ x in p2..v, ‖deriv φ2 x‖) := by
    calc dist (φ0 u) (φ2 v)
        ≤ dist (φ0 u) (φ0 (p0 + a)) + dist (φ0 (p0 + a)) (φ2 v) := dist_triangle _ _ _
      _ = dist (φ0 u) (φ0 (p0 + a)) + dist (φ1 p1) (φ2 v) := by rw [hjoin01]
      _ ≤ dist (φ0 u) (φ0 (p0 + a)) + (dist (φ1 p1) (φ1 (p1 + a)) + dist (φ1 (p1 + a)) (φ2 v)) := by
          gcongr; exact dist_triangle _ _ _
      _ = dist (φ0 u) (φ0 (p0 + a)) + (dist (φ1 p1) (φ1 (p1 + a)) + dist (φ2 p2) (φ2 v)) := by
          rw [hjoin12]
      _ ≤ (∫ x in u..(p0 + a), ‖deriv φ0 x‖) + ((∫ x in p1..(p1 + a), ‖deriv φ1 x‖) +
          (∫ x in p2..v, ‖deriv φ2 x‖)) := by
          gcongr
          · rw [dist_eq_norm, norm_sub_rev]
            exact ac_n_c_norm_diff_le h0 hu ⟨hpa0, le_rfl⟩ hu.2
          · rw [dist_eq_norm, norm_sub_rev]; exact ac_n_c_norm_diff_full ha h1
          · rw [dist_eq_norm, norm_sub_rev]
            exact ac_n_c_norm_diff_le h2 ⟨le_rfl, hpa2⟩ hv hv.1
      _ = _ := by ring
  have hother : dist (φ0 u) (φ2 v) ≤
      (∫ x in p0..u, ‖deriv φ0 x‖) + (∫ x in p3..(p3 + a), ‖deriv φ3 x‖) +
        (∫ x in v..(p2 + a), ‖deriv φ2 x‖) := by
    calc dist (φ0 u) (φ2 v)
        ≤ dist (φ0 u) (φ0 p0) + dist (φ0 p0) (φ2 v) := dist_triangle _ _ _
      _ = dist (φ0 u) (φ0 p0) + dist (φ3 (p3 + a)) (φ2 v) := by rw [hjoin30]
      _ ≤ dist (φ0 u) (φ0 p0) + (dist (φ3 (p3 + a)) (φ3 p3) + dist (φ3 p3) (φ2 v)) := by
          gcongr; exact dist_triangle _ _ _
      _ = dist (φ0 u) (φ0 p0) + (dist (φ3 (p3 + a)) (φ3 p3) + dist (φ2 (p2 + a)) (φ2 v)) := by
          rw [hjoin23]
      _ ≤ (∫ x in p0..u, ‖deriv φ0 x‖) + ((∫ x in p3..(p3 + a), ‖deriv φ3 x‖) +
          (∫ x in v..(p2 + a), ‖deriv φ2 x‖)) := by
          gcongr
          · rw [dist_comm, dist_eq_norm, norm_sub_rev]
            exact ac_n_c_norm_diff_le h0 ⟨le_rfl, hpa0⟩ hu hu.1
          · rw [dist_eq_norm]; exact ac_n_c_norm_diff_full ha h3
          · rw [dist_eq_norm]; exact ac_n_c_norm_diff_le h2 hv ⟨hpa2, le_rfl⟩ hv.2
      _ = _ := by ring
  have hsplit0 : (∫ x in p0..u, ‖deriv φ0 x‖) + (∫ x in u..(p0 + a), ‖deriv φ0 x‖) =
      ∫ x in p0..(p0 + a), ‖deriv φ0 x‖ := ac_n_c_side_additive h0 hu
  have hsplit2 : (∫ x in p2..v, ‖deriv φ2 x‖) + (∫ x in v..(p2 + a), ‖deriv φ2 x‖) =
      ∫ x in p2..(p2 + a), ‖deriv φ2 x‖ := ac_n_c_side_additive h2 hv
  linarith [hdirect, hother, hsplit0, hsplit2]

/-- The integral of `‖deriv‖` of a reflected function equals the integral for the original
function: reflection reverses the derivative's sign but not its norm, and the substitution
`t ↦ p + (p+a) - t` maps `[p,p+a]` back to itself. -/
theorem ac_n_c_reflect_integral_eq (ψ : ℝ → ℂ) (p a : ℝ) :
    (∫ x in p..(p + a), ‖deriv (fun t => ψ (p + (p + a) - t)) x‖) =
      ∫ x in p..(p + a), ‖deriv ψ x‖ := by
  have step1 : (∫ x in p..(p + a), ‖deriv (fun t => ψ (p + (p + a) - t)) x‖) =
      ∫ x in p..(p + a), ‖deriv ψ (p + (p + a) - x)‖ := by
    apply intervalIntegral.integral_congr
    intro x _
    show ‖deriv (fun t => ψ (p + (p + a) - t)) x‖ = ‖deriv ψ (p + (p + a) - x)‖
    rw [deriv_comp_const_sub, norm_neg]
  rw [step1, intervalIntegral.integral_comp_sub_left (fun x => ‖deriv ψ x‖) (p + (p + a))]
  congr 1 <;> ring

-- Case-dispatcher: `2 * dist (f ζ) (f ζ')` bounded by the sum of the four full-side
-- integrals, for `ζ, ζ'` on the frontier of the closed square.
theorem ac_n_c_two_arc_bound {f : ℂ → ℂ} {x₀ y₀ a : ℝ} (ha : 0 < a)
    (hbot : AbsolutelyContinuousOnInterval (fun x : ℝ => f ((x : ℂ) + (y₀ : ℂ) * I)) x₀ (x₀ + a))
    (htop : AbsolutelyContinuousOnInterval
      (fun x : ℝ => f ((x : ℂ) + ((y₀ + a : ℝ) : ℂ) * I)) x₀ (x₀ + a))
    (hleft : AbsolutelyContinuousOnInterval (fun y : ℝ => f ((x₀ : ℂ) + (y : ℂ) * I)) y₀ (y₀ + a))
    (hright : AbsolutelyContinuousOnInterval
      (fun y : ℝ => f (((x₀ + a : ℝ) : ℂ) + (y : ℂ) * I)) y₀ (y₀ + a))
    {ζ ζ' : ℂ} (hζ : ζ ∈ frontier (closedRect x₀ (x₀ + a) y₀ (y₀ + a)))
    (hζ' : ζ' ∈ frontier (closedRect x₀ (x₀ + a) y₀ (y₀ + a))) :
    2 * dist (f ζ) (f ζ') ≤
      (∫ x in x₀..(x₀ + a), ‖deriv (fun x : ℝ => f ((x : ℂ) + (y₀ : ℂ) * I)) x‖) +
        (∫ y in y₀..(y₀ + a), ‖deriv (fun y : ℝ => f (((x₀ + a : ℝ) : ℂ) + (y : ℂ) * I)) y‖) +
        (∫ x in x₀..(x₀ + a), ‖deriv (fun x : ℝ => f ((x : ℂ) + ((y₀ + a : ℝ) : ℂ) * I)) x‖) +
        (∫ y in y₀..(y₀ + a), ‖deriv (fun y : ℝ => f ((x₀ : ℂ) + (y : ℂ) * I)) y‖) := by
  have h0 := hbot
  have h1 := hright
  have h2 := ac_n_c_reflect htop
  have h3 := ac_n_c_reflect hleft
  have hj01 : (fun x : ℝ => f ((x : ℂ) + (y₀ : ℂ) * I)) (x₀ + a) =
      (fun y : ℝ => f (((x₀ + a : ℝ) : ℂ) + (y : ℂ) * I)) y₀ := by norm_num
  have hj12 : (fun y : ℝ => f (((x₀ + a : ℝ) : ℂ) + (y : ℂ) * I)) (y₀ + a) =
      (fun t => (fun x : ℝ => f ((x : ℂ) + ((y₀ + a : ℝ) : ℂ) * I)) (x₀ + (x₀ + a) - t)) x₀ := by
    norm_num
  have hj23 : (fun t => (fun x : ℝ => f ((x : ℂ) + ((y₀ + a : ℝ) : ℂ) * I)) (x₀ + (x₀ + a) - t))
      (x₀ + a) =
      (fun t => (fun y : ℝ => f ((x₀ : ℂ) + (y : ℂ) * I)) (y₀ + (y₀ + a) - t)) y₀ := by norm_num
  have hj30 : (fun t => (fun y : ℝ => f ((x₀ : ℂ) + (y : ℂ) * I)) (y₀ + (y₀ + a) - t)) (y₀ + a) =
      (fun x : ℝ => f ((x : ℂ) + (y₀ : ℂ) * I)) x₀ := by norm_num
  have hab : x₀ ≤ x₀ + a := by linarith
  have hcd : y₀ ≤ y₀ + a := by linarith
  have hbridge2 := ac_n_c_reflect_integral_eq (fun x : ℝ => f ((x : ℂ) + ((y₀ + a : ℝ) : ℂ) * I))
    x₀ a
  have hbridge3 := ac_n_c_reflect_integral_eq (fun y : ℝ => f ((x₀ : ℂ) + (y : ℂ) * I)) y₀ a
  have hval_bot : ∀ z : ℂ, z.im = y₀ → f z = (fun x : ℝ => f ((x : ℂ) + (y₀ : ℂ) * I)) z.re := by
    intro z hz
    show f z = f ((z.re : ℂ) + (y₀ : ℂ) * I)
    rw [← hz]; congr 1; exact (Complex.re_add_im z).symm
  have hval_right : ∀ z : ℂ, z.re = x₀ + a →
      f z = (fun y : ℝ => f (((x₀ + a : ℝ) : ℂ) + (y : ℂ) * I)) z.im := by
    intro z hz
    show f z = f (((x₀ + a : ℝ) : ℂ) + (z.im : ℂ) * I)
    rw [← hz]; congr 1; exact (Complex.re_add_im z).symm
  have hval_top : ∀ z : ℂ, z.im = y₀ + a → f z =
      (fun t => (fun x : ℝ => f ((x : ℂ) + ((y₀ + a : ℝ) : ℂ) * I)) (x₀ + (x₀ + a) - t))
        (x₀ + (x₀ + a) - z.re) := by
    intro z hz
    show f z = f (((x₀ + (x₀ + a) - (x₀ + (x₀ + a) - z.re) : ℝ) : ℂ) + ((y₀ + a : ℝ) : ℂ) * I)
    rw [show x₀ + (x₀ + a) - (x₀ + (x₀ + a) - z.re) = z.re by ring, ← hz]
    congr 1; exact (Complex.re_add_im z).symm
  have hval_left : ∀ z : ℂ, z.re = x₀ → f z =
      (fun t => (fun y : ℝ => f ((x₀ : ℂ) + (y : ℂ) * I)) (y₀ + (y₀ + a) - t))
        (y₀ + (y₀ + a) - z.im) := by
    intro z hz
    show f z = f ((x₀ : ℂ) + ((y₀ + (y₀ + a) - (y₀ + (y₀ + a) - z.im) : ℝ) : ℂ) * I)
    rw [show y₀ + (y₀ + a) - (y₀ + (y₀ + a) - z.im) = z.im by ring, ← hz]
    congr 1; exact (Complex.re_add_im z).symm
  have hmem_reflect : ∀ {p q t : ℝ}, p ≤ q → t ∈ Icc p q → p + q - t ∈ Icc p q := by
    intro p q t _ ht; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [ac_n_c_frontier_closedRect hab hcd] at hζ hζ'
  rcases hζ with ⟨hζx1, hζx2, hζim⟩ | ⟨hζre, hζy1, hζy2⟩
  · rcases hζim with hζb | hζt
    · rw [hval_bot ζ hζb]
      rcases hζ' with ⟨hζ'x1, hζ'x2, hζ'im⟩ | ⟨hζ're, hζ'y1, hζ'y2⟩
      · rcases hζ'im with hζ'b | hζ't
        · rw [hval_bot ζ' hζ'b]
          rcases le_total ζ.re ζ'.re with hle | hle
          · linarith [ac_n_c_arc_same_side ha.le h0 h1 h2 h3 hj01 hj12 hj23 hj30
              (u := ζ.re) (v := ζ'.re) ⟨hζx1, hζx2⟩ ⟨hζ'x1, hζ'x2⟩ hle, hbridge2, hbridge3]
          · rw [dist_comm]
            linarith [ac_n_c_arc_same_side ha.le h0 h1 h2 h3 hj01 hj12 hj23 hj30
              (u := ζ'.re) (v := ζ.re) ⟨hζ'x1, hζ'x2⟩ ⟨hζx1, hζx2⟩ hle, hbridge2, hbridge3]
        · rw [hval_top ζ' hζ't]
          linarith [ac_n_c_arc_opposite_side ha.le h0 h1 h2 h3 hj01 hj12 hj23 hj30
            (u := ζ.re) (v := x₀ + (x₀ + a) - ζ'.re) ⟨hζx1, hζx2⟩
            (hmem_reflect hab ⟨hζ'x1, hζ'x2⟩), hbridge2, hbridge3]
      · rcases hζ're with hζ'l | hζ'r
        · rw [hval_left ζ' hζ'l, dist_comm]
          linarith [ac_n_c_arc_adjacent_side ha.le h3 h0 h1 h2 hj30 hj01 hj12 hj23
            (u := y₀ + (y₀ + a) - ζ'.im) (w := ζ.re) (hmem_reflect hcd ⟨hζ'y1, hζ'y2⟩)
            ⟨hζx1, hζx2⟩, hbridge2, hbridge3]
        · rw [hval_right ζ' hζ'r]
          linarith [ac_n_c_arc_adjacent_side ha.le h0 h1 h2 h3 hj01 hj12 hj23 hj30
            (u := ζ.re) (w := ζ'.im) ⟨hζx1, hζx2⟩ ⟨hζ'y1, hζ'y2⟩, hbridge2, hbridge3]
    · rw [hval_top ζ hζt]
      rcases hζ' with ⟨hζ'x1, hζ'x2, hζ'im⟩ | ⟨hζ're, hζ'y1, hζ'y2⟩
      · rcases hζ'im with hζ'b | hζ't
        · rw [hval_bot ζ' hζ'b, dist_comm]
          linarith [ac_n_c_arc_opposite_side ha.le h0 h1 h2 h3 hj01 hj12 hj23 hj30
            (u := ζ'.re) (v := x₀ + (x₀ + a) - ζ.re) ⟨hζ'x1, hζ'x2⟩
            (hmem_reflect hab ⟨hζx1, hζx2⟩), hbridge2, hbridge3]
        · rw [hval_top ζ' hζ't]
          rcases le_total (x₀ + (x₀ + a) - ζ.re) (x₀ + (x₀ + a) - ζ'.re) with hle | hle
          · linarith [ac_n_c_arc_same_side ha.le h2 h3 h0 h1 hj23 hj30 hj01 hj12
              (u := x₀ + (x₀ + a) - ζ.re) (v := x₀ + (x₀ + a) - ζ'.re)
              (hmem_reflect hab ⟨hζx1, hζx2⟩) (hmem_reflect hab ⟨hζ'x1, hζ'x2⟩) hle,
              hbridge2, hbridge3]
          · rw [dist_comm]
            linarith [ac_n_c_arc_same_side ha.le h2 h3 h0 h1 hj23 hj30 hj01 hj12
              (u := x₀ + (x₀ + a) - ζ'.re) (v := x₀ + (x₀ + a) - ζ.re)
              (hmem_reflect hab ⟨hζ'x1, hζ'x2⟩) (hmem_reflect hab ⟨hζx1, hζx2⟩) hle, hbridge2, hbridge3]
      · rcases hζ're with hζ'l | hζ'r
        · rw [hval_left ζ' hζ'l]
          linarith [ac_n_c_arc_adjacent_side ha.le h2 h3 h0 h1 hj23 hj30 hj01 hj12
            (u := x₀ + (x₀ + a) - ζ.re) (w := y₀ + (y₀ + a) - ζ'.im)
            (hmem_reflect hab ⟨hζx1, hζx2⟩) (hmem_reflect hcd ⟨hζ'y1, hζ'y2⟩), hbridge2, hbridge3]
        · rw [hval_right ζ' hζ'r, dist_comm]
          linarith [ac_n_c_arc_adjacent_side ha.le h1 h2 h3 h0 hj12 hj23 hj30 hj01
            (u := ζ'.im) (w := x₀ + (x₀ + a) - ζ.re) ⟨hζ'y1, hζ'y2⟩
            (hmem_reflect hab ⟨hζx1, hζx2⟩), hbridge2, hbridge3]
  · rcases hζre with hζl | hζr
    · rw [hval_left ζ hζl]
      rcases hζ' with ⟨hζ'x1, hζ'x2, hζ'im⟩ | ⟨hζ're, hζ'y1, hζ'y2⟩
      · rcases hζ'im with hζ'b | hζ't
        · rw [hval_bot ζ' hζ'b]
          linarith [ac_n_c_arc_adjacent_side ha.le h3 h0 h1 h2 hj30 hj01 hj12 hj23
            (u := y₀ + (y₀ + a) - ζ.im) (w := ζ'.re) (hmem_reflect hcd ⟨hζy1, hζy2⟩)
            ⟨hζ'x1, hζ'x2⟩, hbridge2, hbridge3]
        · rw [hval_top ζ' hζ't, dist_comm]
          linarith [ac_n_c_arc_adjacent_side ha.le h2 h3 h0 h1 hj23 hj30 hj01 hj12
            (u := x₀ + (x₀ + a) - ζ'.re) (w := y₀ + (y₀ + a) - ζ.im)
            (hmem_reflect hab ⟨hζ'x1, hζ'x2⟩) (hmem_reflect hcd ⟨hζy1, hζy2⟩), hbridge2, hbridge3]
      · rcases hζ're with hζ'l | hζ'r
        · rw [hval_left ζ' hζ'l]
          rcases le_total (y₀ + (y₀ + a) - ζ.im) (y₀ + (y₀ + a) - ζ'.im) with hle | hle
          · linarith [ac_n_c_arc_same_side ha.le h3 h0 h1 h2 hj30 hj01 hj12 hj23
              (u := y₀ + (y₀ + a) - ζ.im) (v := y₀ + (y₀ + a) - ζ'.im)
              (hmem_reflect hcd ⟨hζy1, hζy2⟩) (hmem_reflect hcd ⟨hζ'y1, hζ'y2⟩) hle,
              hbridge2, hbridge3]
          · rw [dist_comm]
            linarith [ac_n_c_arc_same_side ha.le h3 h0 h1 h2 hj30 hj01 hj12 hj23
              (u := y₀ + (y₀ + a) - ζ'.im) (v := y₀ + (y₀ + a) - ζ.im)
              (hmem_reflect hcd ⟨hζ'y1, hζ'y2⟩) (hmem_reflect hcd ⟨hζy1, hζy2⟩) hle, hbridge2, hbridge3]
        · rw [hval_right ζ' hζ'r]
          linarith [ac_n_c_arc_opposite_side ha.le h3 h0 h1 h2 hj30 hj01 hj12 hj23
            (u := y₀ + (y₀ + a) - ζ.im) (v := ζ'.im) (hmem_reflect hcd ⟨hζy1, hζy2⟩)
            ⟨hζ'y1, hζ'y2⟩, hbridge2, hbridge3]
    · rw [hval_right ζ hζr]
      rcases hζ' with ⟨hζ'x1, hζ'x2, hζ'im⟩ | ⟨hζ're, hζ'y1, hζ'y2⟩
      · rcases hζ'im with hζ'b | hζ't
        · rw [hval_bot ζ' hζ'b, dist_comm]
          linarith [ac_n_c_arc_adjacent_side ha.le h0 h1 h2 h3 hj01 hj12 hj23 hj30
            (u := ζ'.re) (w := ζ.im) ⟨hζ'x1, hζ'x2⟩ ⟨hζy1, hζy2⟩, hbridge2, hbridge3]
        · rw [hval_top ζ' hζ't]
          linarith [ac_n_c_arc_adjacent_side ha.le h1 h2 h3 h0 hj12 hj23 hj30 hj01
            (u := ζ.im) (w := x₀ + (x₀ + a) - ζ'.re) ⟨hζy1, hζy2⟩
            (hmem_reflect hab ⟨hζ'x1, hζ'x2⟩), hbridge2, hbridge3]
      · rcases hζ're with hζ'l | hζ'r
        · rw [hval_left ζ' hζ'l, dist_comm]
          linarith [ac_n_c_arc_opposite_side ha.le h3 h0 h1 h2 hj30 hj01 hj12 hj23
            (u := y₀ + (y₀ + a) - ζ'.im) (v := ζ.im) (hmem_reflect hcd ⟨hζ'y1, hζ'y2⟩)
            ⟨hζy1, hζy2⟩, hbridge2, hbridge3]
        · rw [hval_right ζ' hζ'r]
          rcases le_total ζ.im ζ'.im with hle | hle
          · linarith [ac_n_c_arc_same_side ha.le h1 h2 h3 h0 hj12 hj23 hj30 hj01
              (u := ζ.im) (v := ζ'.im) ⟨hζy1, hζy2⟩ ⟨hζ'y1, hζ'y2⟩ hle]
          · rw [dist_comm]
            linarith [ac_n_c_arc_same_side ha.le h1 h2 h3 h0 hj12 hj23 hj30 hj01
              (u := ζ'.im) (v := ζ.im) ⟨hζ'y1, hζ'y2⟩ ⟨hζy1, hζy2⟩ hle, hbridge2, hbridge3]

/-- `(∫⁻ g)² ≤ μ(univ) · ∫⁻ g²` — Cauchy–Schwarz with `1` as the other factor. -/
theorem ac_n_c_sq_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {g : α → ℝ≥0∞}
    (hg : AEMeasurable g μ) : (∫⁻ a, g a ∂μ) ^ 2 ≤ μ Set.univ * ∫⁻ a, g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (aemeasurable_const (b := (1 : ℝ≥0∞))) hg
  simp only [Pi.mul_apply, one_mul, one_pow, lintegral_one, ENNReal.rpow_two] at h
  have e : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc (∫⁻ a, g a ∂μ) ^ 2
      ≤ (μ Set.univ ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left' h 2
    _ = μ Set.univ * ∫⁻ a, g a ^ 2 ∂μ := by rw [mul_pow, e, e]

/-- Cauchy–Schwarz for one side: the square of the (unsquared) full-side integral is bounded by
`a` times the (squared) lintegral of the same derivative. -/
theorem ac_n_c_side_cauchy_schwarz {φ : ℝ → ℂ} {p a : ℝ} (ha : 0 < a)
    (hφ : AbsolutelyContinuousOnInterval φ p (p + a)) :
    (ENNReal.ofReal (∫ x in p..(p + a), ‖deriv φ x‖)) ^ 2 ≤
      ENNReal.ofReal a * ∫⁻ x in Ioo p (p + a), ‖deriv φ x‖ₑ ^ 2 := by
  have hpa : p ≤ p + a := by linarith
  have hint : IntervalIntegrable (fun x => ‖deriv φ x‖) volume p (p + a) :=
    ac_n_c_intervalIntegrable_norm_deriv hpa hφ
  have heq1 : ENNReal.ofReal (∫ x in p..(p + a), ‖deriv φ x‖) =
      ∫⁻ x in Ioc p (p + a), ENNReal.ofReal ‖deriv φ x‖ := by
    rw [intervalIntegral.integral_of_le hpa]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint.1
      (Filter.Eventually.of_forall (fun x => norm_nonneg _))
  have heqset : (volume.restrict (Ioc p (p + a))) = volume.restrict (Ioo p (p + a)) :=
    (restrict_Ioo_eq_restrict_Ioc).symm
  rw [heq1, heqset]
  have hmeasOo : AEStronglyMeasurable (fun x => ‖deriv φ x‖) (volume.restrict (Ioo p (p + a))) :=
    heqset ▸ hint.1.aestronglyMeasurable
  have heq2 : ∀ x, ENNReal.ofReal ‖deriv φ x‖ = ‖deriv φ x‖ₑ := fun x => ofReal_norm _
  simp_rw [heq2]
  have hgmeasO : AEMeasurable (fun x => ‖deriv φ x‖ₑ) (volume.restrict (Ioo p (p + a))) := by
    have hbase : AEMeasurable (fun x => ENNReal.ofReal ‖deriv φ x‖)
        (volume.restrict (Ioo p (p + a))) :=
      ENNReal.continuous_ofReal.measurable.comp_aemeasurable hmeasOo.aemeasurable
    simpa only [ofReal_norm] using hbase
  have hstep := ac_n_c_sq_lintegral_le (volume.restrict (Ioo p (p + a))) hgmeasO
  have huniv : (volume.restrict (Ioo p (p + a))) Set.univ = ENNReal.ofReal a := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    congr 1; ring
  rwa [huniv] at hstep

theorem ac_n_c_four_sq_nnreal (a b c d : ℝ≥0) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  have h1 := two_mul_le_add_sq a b
  have h2 := two_mul_le_add_sq a c
  have h3 := two_mul_le_add_sq a d
  have h4 := two_mul_le_add_sq b c
  have h5 := two_mul_le_add_sq b d
  have h6 := two_mul_le_add_sq c d
  have hexpand : (a + b + c + d) ^ 2 =
      a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + (2 * a * b + 2 * a * c + 2 * a * d + 2 * b * c + 2 * b * d +
        2 * c * d) := by ring
  rw [hexpand]
  calc a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 +
      (2 * a * b + 2 * a * c + 2 * a * d + 2 * b * c + 2 * b * d + 2 * c * d)
      ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 +
        ((a ^ 2 + b ^ 2) + (a ^ 2 + c ^ 2) + (a ^ 2 + d ^ 2) + (b ^ 2 + c ^ 2) + (b ^ 2 + d ^ 2) +
          (c ^ 2 + d ^ 2)) := by gcongr
    _ = 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by ring

theorem ac_n_c_four_sum_sq_le (a b c d : ℝ≥0∞) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  rcases eq_top_or_lt_top a with ha | ha
  · simp [ha]
  rcases eq_top_or_lt_top b with hb | hb
  · simp [hb]
  rcases eq_top_or_lt_top c with hc | hc
  · simp [hc]
  rcases eq_top_or_lt_top d with hd | hd
  · simp [hd]
  lift a to ℝ≥0 using ha.ne
  lift b to ℝ≥0 using hb.ne
  lift c to ℝ≥0 using hc.ne
  lift d to ℝ≥0 using hd.ne
  exact_mod_cast ac_n_c_four_sq_nnreal a b c d

theorem ac_n_c_deriv_eq_partialX (f : ℂ → ℂ) (y₀ x₁ : ℝ) :
    deriv (fun x : ℝ => f ((x : ℂ) + (y₀ : ℂ) * I)) x₁ = partialX f ((x₁ : ℂ) + (y₀ : ℂ) * I) := by
  have hstep : deriv (fun t : ℝ => (fun x : ℝ => f ((x : ℂ) + (y₀ : ℂ) * I)) (x₁ + t)) 0 =
      deriv (fun x : ℝ => f ((x : ℂ) + (y₀ : ℂ) * I)) (x₁ + 0) := by
    convert deriv_comp_const_add (fun x : ℝ => f ((x : ℂ) + (y₀ : ℂ) * I)) x₁ 0
  rw [add_zero] at hstep
  rw [← hstep]
  show deriv (fun t : ℝ => f (((x₁ + t : ℝ) : ℂ) + (y₀ : ℂ) * I)) 0 =
    deriv (fun t : ℝ => f (((x₁ : ℂ) + (y₀ : ℂ) * I) + t)) 0
  congr 1
  funext t
  push_cast
  ring_nf

theorem ac_n_c_deriv_eq_partialY (f : ℂ → ℂ) (x₀ y₁ : ℝ) :
    deriv (fun y : ℝ => f ((x₀ : ℂ) + (y : ℂ) * I)) y₁ = partialY f ((x₀ : ℂ) + (y₁ : ℂ) * I) := by
  have hstep : deriv (fun t : ℝ => (fun y : ℝ => f ((x₀ : ℂ) + (y : ℂ) * I)) (y₁ + t)) 0 =
      deriv (fun y : ℝ => f ((x₀ : ℂ) + (y : ℂ) * I)) (y₁ + 0) := by
    convert deriv_comp_const_add (fun y : ℝ => f ((x₀ : ℂ) + (y : ℂ) * I)) y₁ 0
  rw [add_zero] at hstep
  rw [← hstep]
  show deriv (fun t : ℝ => f ((x₀ : ℂ) + ((y₁ + t : ℝ) : ℂ) * I)) 0 =
    deriv (fun t : ℝ => f (((x₀ : ℂ) + (y₁ : ℂ) * I) + t * I)) 0
  congr 1
  funext t
  push_cast
  ring_nf

theorem ac_n_c_NNReal_pi_eq : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal π := by
  rw [ENNReal.ofReal, ← NNReal.coe_real_pi, Real.toNNReal_coe]

theorem ac_n_volume_image_le_boundary {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hfc : ContinuousOn f D) (hfi : InjOn f D) {x₀ y₀ a : ℝ} (ha : 0 < a)
    (hQ : closedRect x₀ (x₀ + a) y₀ (y₀ + a) ⊆ D)
    (hbot : AbsolutelyContinuousOnInterval (fun x : ℝ => f ((x : ℂ) + (y₀ : ℂ) * I)) x₀ (x₀ + a))
    (htop : AbsolutelyContinuousOnInterval
      (fun x : ℝ => f ((x : ℂ) + ((y₀ + a : ℝ) : ℂ) * I)) x₀ (x₀ + a))
    (hleft : AbsolutelyContinuousOnInterval (fun y : ℝ => f ((x₀ : ℂ) + (y : ℂ) * I)) y₀ (y₀ + a))
    (hright : AbsolutelyContinuousOnInterval
      (fun y : ℝ => f (((x₀ + a : ℝ) : ℂ) + (y : ℂ) * I)) y₀ (y₀ + a)) :
    volume (f '' closedRect x₀ (x₀ + a) y₀ (y₀ + a)) ≤ ENNReal.ofReal (π * a) *
      ((∫⁻ x in Ioo x₀ (x₀ + a), ‖partialX f ((x : ℂ) + (y₀ : ℂ) * I)‖ₑ ^ 2) +
        (∫⁻ x in Ioo x₀ (x₀ + a), ‖partialX f ((x : ℂ) + ((y₀ + a : ℝ) : ℂ) * I)‖ₑ ^ 2) +
        (∫⁻ y in Ioo y₀ (y₀ + a), ‖partialY f ((x₀ : ℂ) + (y : ℂ) * I)‖ₑ ^ 2) +
        (∫⁻ y in Ioo y₀ (y₀ + a), ‖partialY f (((x₀ + a : ℝ) : ℂ) + (y : ℂ) * I)‖ₑ ^ 2)) := by
  set s1 := ∫ x in x₀..(x₀ + a), ‖deriv (fun x : ℝ => f ((x : ℂ) + (y₀ : ℂ) * I)) x‖ with hs1def
  set s2 := ∫ y in y₀..(y₀ + a), ‖deriv (fun y : ℝ => f (((x₀ + a : ℝ) : ℂ) + (y : ℂ) * I)) y‖
    with hs2def
  set s3 := ∫ x in x₀..(x₀ + a), ‖deriv (fun x : ℝ => f ((x : ℂ) + ((y₀ + a : ℝ) : ℂ) * I)) x‖
    with hs3def
  set s4 := ∫ y in y₀..(y₀ + a), ‖deriv (fun y : ℝ => f ((x₀ : ℂ) + (y : ℂ) * I)) y‖ with hs4def
  set S1 := ∫⁻ x in Ioo x₀ (x₀ + a), ‖partialX f ((x : ℂ) + (y₀ : ℂ) * I)‖ₑ ^ 2 with hS1def
  set S3 := ∫⁻ x in Ioo x₀ (x₀ + a), ‖partialX f ((x : ℂ) + ((y₀ + a : ℝ) : ℂ) * I)‖ₑ ^ 2
    with hS3def
  set S4 := ∫⁻ y in Ioo y₀ (y₀ + a), ‖partialY f ((x₀ : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 with hS4def
  set S2 := ∫⁻ y in Ioo y₀ (y₀ + a), ‖partialY f (((x₀ + a : ℝ) : ℂ) + (y : ℂ) * I)‖ₑ ^ 2
    with hS2def
  obtain ⟨ζ, hζfr, ζ', hζ'fr, hballfact⟩ := ac_n_c_exists_diam_frontier hfc hfi ha hQ
  set diam := dist (f ζ) (f ζ') with hdiamdef
  have hsub : f '' closedRect x₀ (x₀ + a) y₀ (y₀ + a) ⊆ closedBall (f ζ') diam := by
    rintro w ⟨z, hz, rfl⟩; exact hballfact z hz
  have hvol1 : volume (f '' closedRect x₀ (x₀ + a) y₀ (y₀ + a)) ≤
      (ENNReal.ofReal diam) ^ 2 * NNReal.pi := by
    have hmono : volume (f '' closedRect x₀ (x₀ + a) y₀ (y₀ + a)) ≤ volume (closedBall (f ζ') diam) :=
      measure_mono hsub
    rwa [Complex.volume_closedBall] at hmono
  have harc : 2 * diam ≤ s1 + s2 + s3 + s4 :=
    ac_n_c_two_arc_bound ha hbot htop hleft hright hζfr hζ'fr
  have hs1nn : 0 ≤ s1 := intervalIntegral.integral_nonneg (by linarith) (fun x _ => norm_nonneg _)
  have hs2nn : 0 ≤ s2 := intervalIntegral.integral_nonneg (by linarith) (fun x _ => norm_nonneg _)
  have hs3nn : 0 ≤ s3 := intervalIntegral.integral_nonneg (by linarith) (fun x _ => norm_nonneg _)
  have hs4nn : 0 ≤ s4 := intervalIntegral.integral_nonneg (by linarith) (fun x _ => norm_nonneg _)
  have hcs1 : (ENNReal.ofReal s1) ^ 2 ≤ ENNReal.ofReal a * S1 := by
    have hraw := ac_n_c_side_cauchy_schwarz ha hbot
    rw [hS1def]
    have heq : (∫⁻ x in Ioo x₀ (x₀ + a), ‖deriv (fun x : ℝ => f ((x : ℂ) + (y₀ : ℂ) * I)) x‖ₑ ^ 2)
        = ∫⁻ x in Ioo x₀ (x₀ + a), ‖partialX f ((x : ℂ) + (y₀ : ℂ) * I)‖ₑ ^ 2 := by
      apply lintegral_congr; intro x; rw [ac_n_c_deriv_eq_partialX]
    rwa [heq] at hraw
  have hcs2 : (ENNReal.ofReal s2) ^ 2 ≤ ENNReal.ofReal a * S2 := by
    have hraw := ac_n_c_side_cauchy_schwarz ha hright
    rw [hS2def]
    have heq : (∫⁻ y in Ioo y₀ (y₀ + a),
        ‖deriv (fun y : ℝ => f (((x₀ + a : ℝ) : ℂ) + (y : ℂ) * I)) y‖ₑ ^ 2)
        = ∫⁻ y in Ioo y₀ (y₀ + a), ‖partialY f (((x₀ + a : ℝ) : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 := by
      apply lintegral_congr; intro y; rw [ac_n_c_deriv_eq_partialY]
    rwa [heq] at hraw
  have hcs3 : (ENNReal.ofReal s3) ^ 2 ≤ ENNReal.ofReal a * S3 := by
    have hraw := ac_n_c_side_cauchy_schwarz ha htop
    rw [hS3def]
    have heq : (∫⁻ x in Ioo x₀ (x₀ + a),
        ‖deriv (fun x : ℝ => f ((x : ℂ) + ((y₀ + a : ℝ) : ℂ) * I)) x‖ₑ ^ 2)
        = ∫⁻ x in Ioo x₀ (x₀ + a), ‖partialX f ((x : ℂ) + ((y₀ + a : ℝ) : ℂ) * I)‖ₑ ^ 2 := by
      apply lintegral_congr; intro x; rw [ac_n_c_deriv_eq_partialX]
    rwa [heq] at hraw
  have hcs4 : (ENNReal.ofReal s4) ^ 2 ≤ ENNReal.ofReal a * S4 := by
    have hraw := ac_n_c_side_cauchy_schwarz ha hleft
    rw [hS4def]
    have heq : (∫⁻ y in Ioo y₀ (y₀ + a), ‖deriv (fun y : ℝ => f ((x₀ : ℂ) + (y : ℂ) * I)) y‖ₑ ^ 2)
        = ∫⁻ y in Ioo y₀ (y₀ + a), ‖partialY f ((x₀ : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 := by
      apply lintegral_congr; intro y; rw [ac_n_c_deriv_eq_partialY]
    rwa [heq] at hraw
  have hfour := ac_n_c_four_sum_sq_le (ENNReal.ofReal s1) (ENNReal.ofReal s2) (ENNReal.ofReal s3)
    (ENNReal.ofReal s4)
  have hstep1 : ENNReal.ofReal (2 * diam) ≤
      ENNReal.ofReal s1 + (ENNReal.ofReal s2 + (ENNReal.ofReal s3 + ENNReal.ofReal s4)) := by
    have hraw : ENNReal.ofReal (2 * diam) ≤ ENNReal.ofReal (s1 + (s2 + (s3 + s4))) := by
      rw [show s1 + (s2 + (s3 + s4)) = s1 + s2 + s3 + s4 by ring]
      exact ENNReal.ofReal_le_ofReal harc
    rwa [ENNReal.ofReal_add hs1nn (by linarith : (0:ℝ) ≤ s2 + (s3 + s4)),
      ENNReal.ofReal_add hs2nn (by linarith : (0:ℝ) ≤ s3 + s4),
      ENNReal.ofReal_add hs3nn hs4nn] at hraw
  rw [show (2 : ℝ) * diam = diam + diam by ring,
    ENNReal.ofReal_add dist_nonneg dist_nonneg] at hstep1
  have hsq : (ENNReal.ofReal diam + ENNReal.ofReal diam) ^ 2 ≤
      (ENNReal.ofReal s1 + (ENNReal.ofReal s2 + (ENNReal.ofReal s3 + ENNReal.ofReal s4))) ^ 2 :=
    ENNReal.pow_le_pow_left hstep1
  have hfoursum : (ENNReal.ofReal s1 + (ENNReal.ofReal s2 + (ENNReal.ofReal s3 +
      ENNReal.ofReal s4))) ^ 2 ≤ 4 * ((ENNReal.ofReal s1) ^ 2 + ((ENNReal.ofReal s2) ^ 2 +
        ((ENNReal.ofReal s3) ^ 2 + (ENNReal.ofReal s4) ^ 2))) := by
    have heq : (ENNReal.ofReal s1 + (ENNReal.ofReal s2 + (ENNReal.ofReal s3 + ENNReal.ofReal s4)))
        = ENNReal.ofReal s1 + ENNReal.ofReal s2 + ENNReal.ofReal s3 + ENNReal.ofReal s4 := by ring
    rw [heq]
    calc (ENNReal.ofReal s1 + ENNReal.ofReal s2 + ENNReal.ofReal s3 + ENNReal.ofReal s4) ^ 2
        ≤ 4 * ((ENNReal.ofReal s1) ^ 2 + (ENNReal.ofReal s2) ^ 2 + (ENNReal.ofReal s3) ^ 2 +
            (ENNReal.ofReal s4) ^ 2) := hfour
      _ = 4 * ((ENNReal.ofReal s1) ^ 2 + ((ENNReal.ofReal s2) ^ 2 + ((ENNReal.ofReal s3) ^ 2 +
            (ENNReal.ofReal s4) ^ 2))) := by ring
  have h4D2le : 4 * (ENNReal.ofReal diam) ^ 2 ≤ 4 * ((ENNReal.ofReal s1) ^ 2 +
      ((ENNReal.ofReal s2) ^ 2 + ((ENNReal.ofReal s3) ^ 2 + (ENNReal.ofReal s4) ^ 2))) := by
    calc 4 * (ENNReal.ofReal diam) ^ 2 = (ENNReal.ofReal diam + ENNReal.ofReal diam) ^ 2 := by ring
      _ ≤ _ := hsq.trans hfoursum
  have h4ne0 : (4 : ℝ≥0∞) ≠ 0 := by norm_num
  have h4netop : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hD2le : (ENNReal.ofReal diam) ^ 2 ≤ (ENNReal.ofReal s1) ^ 2 + ((ENNReal.ofReal s2) ^ 2 +
      ((ENNReal.ofReal s3) ^ 2 + (ENNReal.ofReal s4) ^ 2)) :=
    (ENNReal.mul_le_mul_iff_right h4ne0 h4netop).mp h4D2le
  have hSle : (ENNReal.ofReal s1) ^ 2 + ((ENNReal.ofReal s2) ^ 2 + ((ENNReal.ofReal s3) ^ 2 +
      (ENNReal.ofReal s4) ^ 2)) ≤
      ENNReal.ofReal a * S1 + (ENNReal.ofReal a * S2 + (ENNReal.ofReal a * S3 +
        ENNReal.ofReal a * S4)) := by gcongr
  have hDfinal : (ENNReal.ofReal diam) ^ 2 ≤
      ENNReal.ofReal a * S1 + (ENNReal.ofReal a * S2 + (ENNReal.ofReal a * S3 +
        ENNReal.ofReal a * S4)) := hD2le.trans hSle
  calc volume (f '' closedRect x₀ (x₀ + a) y₀ (y₀ + a)) ≤ (ENNReal.ofReal diam) ^ 2 * NNReal.pi :=
        hvol1
    _ ≤ (ENNReal.ofReal a * S1 + (ENNReal.ofReal a * S2 + (ENNReal.ofReal a * S3 +
        ENNReal.ofReal a * S4))) * NNReal.pi := by gcongr
    _ = ENNReal.ofReal (π * a) * (S1 + S3 + S4 + S2) := by
        rw [ac_n_c_NNReal_pi_eq,
          show (ENNReal.ofReal a * S1 + (ENNReal.ofReal a * S2 + (ENNReal.ofReal a * S3 +
              ENNReal.ofReal a * S4))) * ENNReal.ofReal π =
            ENNReal.ofReal a * ENNReal.ofReal π * (S1 + S2 + S3 + S4) by ring,
          ← ENNReal.ofReal_mul ha.le, show a * π = π * a by ring]
        congr 1
        ring



/-- Fubini for the closed rectangle (via the null boundary + the project's `lintegral_openRect`). -/
theorem ac_n_c_lintegral_closedRect {a b c d : ℝ} {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z in closedRect a b c d, F z =
      ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d, F ((x : ℂ) + (y : ℂ) * I) := by
  rw [← lintegral_openRect hF]
  apply setLIntegral_congr
  rw [ae_eq_set]
  refine ⟨menchoff_volume_closedRect_diff_openRect a b c d, ?_⟩
  rw [Set.diff_eq_empty.mpr (acl_openRect_subset_closedRect le_rfl le_rfl le_rfl le_rfl)]
  exact measure_empty

/-- The clamped `partialX` agrees with `partialX f` at any point whose x-coordinate is in the
open interval `(a,b)` and whose y-coordinate is in the closed interval `[c,d]`. -/
theorem ac_n_c_partialX_clamp_eq {f : ℂ → ℂ} {a b c d : ℝ} :
    ∀ y ∈ Icc c d, ∀ x ∈ Ioo a b,
      partialX (f ∘ rectClamp a b c d) ((x : ℂ) + (y : ℂ) * I) =
        partialX f ((x : ℂ) + (y : ℂ) * I) := by
  intro y hy x hx
  rw [partialX_ofReal_add, partialX_ofReal_add]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
  simp only [Function.comp_apply]
  rw [rectClamp_of_mem (mem_closedRect_of_mem_Icc (Ioo_subset_Icc_self ht) hy)]

/-- The clamped `partialY` agrees with `partialY f` at any point whose y-coordinate is in the
open interval `(c,d)` and whose x-coordinate is in the closed interval `[a,b]`. -/
theorem ac_n_c_partialY_clamp_eq {f : ℂ → ℂ} {a b c d : ℝ} :
    ∀ x ∈ Icc a b, ∀ y ∈ Ioo c d,
      partialY (f ∘ rectClamp a b c d) ((x : ℂ) + (y : ℂ) * I) =
        partialY f ((x : ℂ) + (y : ℂ) * I) := by
  intro x hx y hy
  rw [partialY_ofReal_add, partialY_ofReal_add]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [Ioo_mem_nhds hy.1 hy.2] with t ht
  simp only [Function.comp_apply]
  rw [rectClamp_of_mem (mem_closedRect_of_mem_Icc hx (Ioo_subset_Icc_self ht))]

/-- Fubini for `‖partialX f‖ₑ^2` over a closed rectangle, with the TRUE (unclamped) `partialX f`
on both sides. -/
theorem ac_n_c_lintegral_partialX {f : ℂ → ℂ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f (closedRect a b c d)) :
    ∫⁻ z in closedRect a b c d, ‖partialX f z‖ₑ ^ 2 =
      ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d, ‖partialX f ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 := by
  have hFm : Measurable (fun z => ‖partialX (f ∘ rectClamp a b c d) z‖ₑ ^ 2) :=
    ((measurable_partialX_comp_rectClamp hab hcd hf).enorm).pow_const 2
  have hzeq : ∀ z : ℂ, z.re ∈ Ioo a b → z ∈ closedRect a b c d →
      ‖partialX (f ∘ rectClamp a b c d) z‖ₑ ^ 2 = ‖partialX f z‖ₑ ^ 2 := by
    intro z hzre hz
    have e1 : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
    rw [e1, ac_n_c_partialX_clamp_eq z.im ⟨hz.2.2.1, hz.2.2.2⟩ z.re hzre]
  have hmeasR : MeasurableSet (closedRect a b c d) :=
    (acl_isCompact_closedRect a b c d).isClosed.measurableSet
  have hnull : volume {z : ℂ | z ∈ closedRect a b c d ∧ z.re ∉ Ioo a b} = 0 := by
    refine measure_mono_null (t := closedRect a b c d \ openRect a b c d) ?_
      (menchoff_volume_closedRect_diff_openRect a b c d)
    rintro z ⟨hz1, hz2⟩
    refine ⟨hz1, fun hz3 => hz2 ⟨hz3.1, hz3.2.1⟩⟩
  have hae0 : ∀ᵐ z ∂volume, z ∈ closedRect a b c d → z.re ∈ Ioo a b := by
    rw [ae_iff]
    have hset : {z : ℂ | ¬(z ∈ closedRect a b c d → z.re ∈ Ioo a b)} =
        {z : ℂ | z ∈ closedRect a b c d ∧ z.re ∉ Ioo a b} := by
      ext z; exact Classical.not_imp
    rw [hset]
    exact hnull
  have hcong : ∀ᵐ z ∂volume, z ∈ closedRect a b c d →
      ‖partialX (f ∘ rectClamp a b c d) z‖ₑ ^ 2 = ‖partialX f z‖ₑ ^ 2 := by
    filter_upwards [hae0] with z hz0 hz1
    exact hzeq z (hz0 hz1) hz1
  rw [← setLIntegral_congr_fun_ae hmeasR hcong,
    ac_n_c_lintegral_closedRect hFm]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
  refine setLIntegral_congr_fun measurableSet_Ioo (fun y hy => ?_)
  refine hzeq ((x : ℂ) + (y : ℂ) * I) ?_ (mem_closedRect_of_mem_Icc (Ioo_subset_Icc_self hx)
    (Ioo_subset_Icc_self hy))
  simpa using hx

/-- Fubini for `‖partialY f‖ₑ^2` over a closed rectangle, with the TRUE (unclamped) `partialY f`
on both sides. -/
theorem ac_n_c_lintegral_partialY {f : ℂ → ℂ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f (closedRect a b c d)) :
    ∫⁻ z in closedRect a b c d, ‖partialY f z‖ₑ ^ 2 =
      ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d, ‖partialY f ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 := by
  have hFm : Measurable (fun z => ‖partialY (f ∘ rectClamp a b c d) z‖ₑ ^ 2) :=
    ((measurable_partialY_comp_rectClamp hab hcd hf).enorm).pow_const 2
  have hzeq : ∀ z : ℂ, z.im ∈ Ioo c d → z ∈ closedRect a b c d →
      ‖partialY (f ∘ rectClamp a b c d) z‖ₑ ^ 2 = ‖partialY f z‖ₑ ^ 2 := by
    intro z hzim hz
    have e1 : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
    rw [e1, ac_n_c_partialY_clamp_eq z.re ⟨hz.1, hz.2.1⟩ z.im hzim]
  have hmeasR : MeasurableSet (closedRect a b c d) :=
    (acl_isCompact_closedRect a b c d).isClosed.measurableSet
  have hnull : volume {z : ℂ | z ∈ closedRect a b c d ∧ z.im ∉ Ioo c d} = 0 := by
    refine measure_mono_null (t := closedRect a b c d \ openRect a b c d) ?_
      (menchoff_volume_closedRect_diff_openRect a b c d)
    rintro z ⟨hz1, hz2⟩
    refine ⟨hz1, fun hz3 => hz2 ⟨hz3.2.2.1, hz3.2.2.2⟩⟩
  have hae0 : ∀ᵐ z ∂volume, z ∈ closedRect a b c d → z.im ∈ Ioo c d := by
    rw [ae_iff]
    have hset : {z : ℂ | ¬(z ∈ closedRect a b c d → z.im ∈ Ioo c d)} =
        {z : ℂ | z ∈ closedRect a b c d ∧ z.im ∉ Ioo c d} := by
      ext z; exact Classical.not_imp
    rw [hset]
    exact hnull
  have hcong : ∀ᵐ z ∂volume, z ∈ closedRect a b c d →
      ‖partialY (f ∘ rectClamp a b c d) z‖ₑ ^ 2 = ‖partialY f z‖ₑ ^ 2 := by
    filter_upwards [hae0] with z hz0 hz1
    exact hzeq z (hz0 hz1) hz1
  rw [← setLIntegral_congr_fun_ae hmeasR hcong,
    ac_n_c_lintegral_closedRect hFm]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
  refine setLIntegral_congr_fun measurableSet_Ioo (fun y hy => ?_)
  refine hzeq ((x : ℂ) + (y : ℂ) * I) ?_ (mem_closedRect_of_mem_Icc (Ioo_subset_Icc_self hx)
    (Ioo_subset_Icc_self hy))
  simpa using hy

/-- For `z.re ∈ [x₀, x₀+n*a]` and `s ∈ (0,a)`, there is `j : ℤ` with `-1 ≤ j ≤ n-1` and
`x₀+s+j*a ≤ z.re ≤ x₀+s+(j+1)*a`. -/
theorem ac_n_c_exists_j {x₀ a : ℝ} (ha : 0 < a) {n : ℕ} {s x : ℝ} (hs : s ∈ Ioo (0:ℝ) a)
    (hx : x ∈ Icc x₀ (x₀ + n * a)) :
    ∃ j : ℤ, -1 ≤ j ∧ j ≤ (n:ℤ) - 1 ∧ x₀ + s + j * a ≤ x ∧ x ≤ x₀ + s + (j+1) * a := by
  set j := ⌊(x - x₀ - s) / a⌋ with hjdef
  refine ⟨j, ?_, ?_, ?_, ?_⟩
  · rw [hjdef, Int.le_floor]
    push_cast
    rw [le_div_iff₀ ha]
    linarith [hx.1, hs.2]
  · have hlt : j < (n:ℤ) := by
      rw [hjdef, Int.floor_lt]
      push_cast
      rw [div_lt_iff₀ ha]
      linarith [hx.2, hs.1]
    omega
  · rw [hjdef]
    have := Int.floor_le ((x - x₀ - s) / a)
    rw [le_div_iff₀ ha] at this
    linarith [this]
  · rw [hjdef]
    have := Int.lt_floor_add_one ((x - x₀ - s) / a)
    rw [div_lt_iff₀ ha] at this
    linarith [this]

/-- There is a `t ∈ Ioo 0 a` avoiding a given null set `N`, with `F t ≤ (1/a) * ∫⁻ t in Ioo 0 a, F t`. -/
theorem ac_n_c_exists_good_offset {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ≥0∞} (hF : AEMeasurable F (volume.restrict (Ioo 0 a)))
    {N : Set ℝ} (hN : volume (N ∩ Ioo 0 a) = 0) :
    ∃ t ∈ Ioo (0:ℝ) a, t ∉ N ∧
      F t * ENNReal.ofReal a ≤ ∫⁻ t in Ioo 0 a, F t := by
  have hμ0 : volume.restrict (Ioo (0:ℝ) a) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    rw [Real.volume_Ioo]
    simp only [ENNReal.ofReal_eq_zero, not_le]
    linarith
  haveI : IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) a)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  have hN'' : (volume.restrict (Ioo (0:ℝ) a)) (N ∪ (Ioo (0:ℝ) a)ᶜ) = 0 := by
    rw [Measure.restrict_apply' measurableSet_Ioo, union_inter_distrib_right]
    rw [show (Ioo (0:ℝ) a)ᶜ ∩ Ioo (0:ℝ) a = ∅ from by rw [inter_comm]; exact Set.inter_compl_self _]
    rwa [union_empty]
  obtain ⟨t, htN, htavg⟩ := exists_notMem_null_le_laverage hμ0 hF hN''
  have htN1 : t ∉ N := fun h => htN (Or.inl h)
  have htN2 : t ∈ Ioo (0:ℝ) a := by
    by_contra hcon; exact htN (Or.inr hcon)
  refine ⟨t, htN2, htN1, ?_⟩
  rw [MeasureTheory.laverage, MeasureTheory.lintegral_smul_measure, smul_eq_mul,
    Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero] at htavg
  have hstep : F t * ENNReal.ofReal a ≤
      (ENNReal.ofReal a)⁻¹ * (∫⁻ t in Ioo (0:ℝ) a, F t) * ENNReal.ofReal a :=
    mul_le_mul_left htavg _
  rwa [mul_right_comm, ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top,
    one_mul] at hstep

/-- A pointwise a.e. property, translated by `e`, transfers to `Ioo 0 a` (Lebesgue translation
invariance). -/
theorem ac_n_c_ae_shift {P : ℝ → Prop} {c d : ℝ} (h : ∀ᵐ y ∂(volume.restrict (Ioo c d)), P y)
    {e a : ℝ} (he1 : c ≤ e) (he2 : e + a ≤ d) :
    ∀ᵐ t ∂(volume.restrict (Ioo (0:ℝ) a)), P (t + e) := by
  have h' : ∀ᵐ y ∂volume, y ∈ Ioo c d → P y := (ae_restrict_iff' measurableSet_Ioo).mp h
  have hpm : MeasurePreserving (fun t : ℝ => t + e) volume volume := measurePreserving_add_right volume e
  have h'' : ∀ᵐ t ∂volume, t + e ∈ Ioo c d → P (t + e) := hpm.quasiMeasurePreserving.ae h'
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [h''] with t ht htmem
  exact ht ⟨by linarith [htmem.1], by linarith [htmem.2]⟩

/-- The finite-conjunction version: a.e. `t`, the shifted property holds simultaneously for
every `m` in the finite range `[-1, n]`. -/
theorem ac_n_c_ae_shift_all {P : ℝ → Prop} {c d : ℝ} (h : ∀ᵐ y ∂(volume.restrict (Ioo c d)), P y)
    {e₀ a : ℝ} {n : ℕ} (he1 : ∀ m : ℤ, -1 ≤ m → m ≤ (n:ℤ) → c ≤ e₀ + m * a)
    (he2 : ∀ m : ℤ, -1 ≤ m → m ≤ (n:ℤ) → e₀ + m * a + a ≤ d) :
    ∀ᵐ t ∂(volume.restrict (Ioo (0:ℝ) a)), ∀ m : ℤ, -1 ≤ m → m ≤ (n:ℤ) → P (t + (e₀ + m * a)) := by
  rw [ae_all_iff]
  intro m
  by_cases hm : -1 ≤ m ∧ m ≤ (n:ℤ)
  · have := ac_n_c_ae_shift h (he1 m hm.1 hm.2) (he2 m hm.1 hm.2)
    filter_upwards [this] with t ht _ _
    exact ht
  · filter_upwards with t hm1 hm2
    exact absurd ⟨hm1, hm2⟩ hm

/-- Translation invariance of the `lintegral` over an interval of length `a`. -/
theorem ac_n_c_lintegral_shift {F : ℝ → ℝ≥0∞} (hF : Measurable F) (e a : ℝ) :
    ∫⁻ t in Ioo (0:ℝ) a, F (t + e) = ∫⁻ y in Ioo e (e + a), F y := by
  have hpm : MeasurePreserving (fun t : ℝ => t + e) volume volume := measurePreserving_add_right volume e
  have he := (measurableEmbedding_addRight e)
  have hpre : (fun t : ℝ => t + e) ⁻¹' Ioo e (e + a) = Ioo (0:ℝ) a := by
    ext t; simp only [mem_preimage, mem_Ioo]; constructor <;> (intro h; constructor <;> linarith [h.1, h.2])
  have hres := hpm.restrict_preimage_emb he (Ioo e (e + a))
  rw [hpre] at hres
  exact hres.lintegral_comp hF

/-- The `(n+2)`-piece partition of `Ioo (e₀-a) (e₀+(n+1)*a)` into unit-`a` translates of
`Ioo 0 a`, as a `lintegral` sum identity. -/
theorem ac_n_c_lintegral_partition {F : ℝ → ℝ≥0∞} (hF : Measurable F) {e₀ a : ℝ} (ha : 0 < a)
    (n : ℕ) :
    ∫⁻ y in Ioo (e₀ - a) (e₀ + ((n : ℝ) + 1) * a), F y =
      ∑ m ∈ Finset.Icc (-1 : ℤ) (n : ℤ), ∫⁻ t in Ioo (0 : ℝ) a, F (t + (e₀ + m * a)) := by
  have hshift : ∀ m : ℤ, ∫⁻ t in Ioo (0:ℝ) a, F (t + (e₀ + m * a)) =
      ∫⁻ y in Ioo (e₀ + m * a) (e₀ + m * a + a), F y := fun m =>
    ac_n_c_lintegral_shift hF (e₀ + m * a) a
  simp_rw [hshift]
  have hdisj : (↑(Finset.Icc (-1:ℤ) (n:ℤ)) : Set ℤ).PairwiseDisjoint
      (fun m => Ioo (e₀ + m * a) (e₀ + m * a + a)) := by
    intro m1 _ m2 _ hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hle : m1 + 1 ≤ m2 := hlt
      refine Set.disjoint_left.mpr (fun y hy1 hy2 => ?_)
      have h1 : y < e₀ + m1 * a + a := hy1.2
      have h2 : e₀ + m2 * a < y := hy2.1
      have : (m1:ℝ) + 1 ≤ (m2:ℝ) := by exact_mod_cast hle
      nlinarith
    · have hle : m2 + 1 ≤ m1 := hlt
      refine Set.disjoint_left.mpr (fun y hy1 hy2 => ?_)
      have h1 : e₀ + m1 * a < y := hy1.1
      have h2 : y < e₀ + m2 * a + a := hy2.2
      have : (m2:ℝ) + 1 ≤ (m1:ℝ) := by exact_mod_cast hle
      nlinarith
  have hmeas : ∀ m ∈ Finset.Icc (-1:ℤ) (n:ℤ), MeasurableSet (Ioo (e₀ + m * a) (e₀ + m * a + a)) :=
    fun m _ => measurableSet_Ioo
  rw [← lintegral_biUnion_finset hdisj hmeas]
  apply setLIntegral_congr
  rw [ae_eq_set]
  constructor
  · have hfin : Ioo (e₀ - a) (e₀ + ((n:ℝ) + 1) * a) \
        (⋃ m ∈ Finset.Icc (-1:ℤ) (n:ℤ), Ioo (e₀ + m * a) (e₀ + m * a + a)) ⊆
        (fun k : ℤ => e₀ + k * a) '' (↑(Finset.Icc (0:ℤ) (n:ℤ)) : Set ℤ) := by
      rintro y ⟨hy1, hy2⟩
      simp only [mem_iUnion, mem_Ioo, Finset.mem_Icc, not_exists] at hy2
      set m : ℤ := ⌊(y - e₀) / a⌋ with hmdef
      have hmlo : (-1:ℤ) ≤ m := by
        rw [hmdef, Int.le_floor]; push_cast; rw [le_div_iff₀ ha]
        have := hy1.1; linarith
      have hmhi : m ≤ (n:ℤ) := by
        have hlt : m < (n:ℤ) + 1 := by
          rw [hmdef, Int.floor_lt]; push_cast; rw [div_lt_iff₀ ha]
          have := hy1.2; linarith
        omega
      have hle1 : e₀ + m * a ≤ y := by
        rw [hmdef]; have := Int.floor_le ((y - e₀) / a); rw [le_div_iff₀ ha] at this; linarith
      have hle2 : y < e₀ + m * a + a := by
        rw [hmdef]; have := Int.lt_floor_add_one ((y - e₀) / a); rw [div_lt_iff₀ ha] at this
        linarith
      have heq : e₀ + m * a = y := by
        rcases eq_or_lt_of_le hle1 with h | h
        · exact h
        · exact absurd ⟨h, hle2⟩ (hy2 m ⟨hmlo, hmhi⟩)
      have hmne : m ≠ -1 := by
        intro hm1
        rw [hm1, show ((-1:ℤ):ℝ) = -1 by norm_num] at heq
        have := hy1.1
        nlinarith
      refine ⟨m, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_Icc]; omega
      · exact heq
    refine measure_mono_null hfin ?_
    exact (Set.Finite.image _ (Finset.finite_toSet _)).measure_zero volume
  · rw [Set.diff_eq_empty.mpr]
    · exact measure_empty
    · refine Set.iUnion₂_subset (fun m hm => ?_)
      rw [Finset.mem_Icc] at hm
      intro y hy
      have hm1 : (-1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm.1
      have hm2 : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hm.2
      refine ⟨?_, ?_⟩
      · nlinarith [hy.1]
      · nlinarith [hy.2]

/-- Combine the averaging existence with an a.e. side property `P` (here, "all grid lines
through this offset are A.C."): get a single offset satisfying both. -/
theorem ac_n_c_exists_good_offset_ac {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ≥0∞}
    (hF : AEMeasurable F (volume.restrict (Ioo 0 a))) {P : ℝ → Prop}
    (hP : ∀ᵐ t ∂(volume.restrict (Ioo (0:ℝ) a)), P t) :
    ∃ t ∈ Ioo (0:ℝ) a, P t ∧ F t * ENNReal.ofReal a ≤ ∫⁻ t in Ioo 0 a, F t := by
  have hN : volume ({t : ℝ | ¬ P t} ∩ Ioo (0:ℝ) a) = 0 := by
    rw [← Measure.restrict_apply' measurableSet_Ioo]
    exact ae_iff.mp hP
  obtain ⟨t, ht1, ht2, ht3⟩ := ac_n_c_exists_good_offset ha hF hN
  refine ⟨t, ht1, ?_, ht3⟩
  by_contra hPt
  exact ht2 hPt

/-- Measurability of a `y`-slice `lintegral` of a globally measurable `ℂ`-valued function. -/
theorem ac_n_c_measurable_lintegral_slice {G : ℂ → ℝ≥0∞} (hG : Measurable G) (p q : ℝ) :
    Measurable (fun y : ℝ => ∫⁻ x in Ioo p q, G ((x:ℂ) + (y:ℂ) * I)) := by
  have h1 : Measurable (fun z : ℝ × ℝ =>
      ({w : ℝ × ℝ | w.2 ∈ Ioo p q}).indicator (fun w => G ((w.2:ℂ) + (w.1:ℂ) * I)) z) := by
    apply Measurable.indicator _ (measurable_snd measurableSet_Ioo)
    exact hG.comp (by fun_prop)
  have h2 : Measurable (fun y : ℝ => ∫⁻ x, ({w : ℝ × ℝ | w.2 ∈ Ioo p q}).indicator
      (fun w => G ((w.2:ℂ) + (w.1:ℂ) * I)) (y, x) ∂volume) := h1.lintegral_prod_right'
  have h3 : ∀ y x : ℝ, ({w : ℝ × ℝ | w.2 ∈ Ioo p q}).indicator
      (fun w => G ((w.2:ℂ) + (w.1:ℂ) * I)) (y, x) =
      (Ioo p q).indicator (fun x => G ((x:ℂ) + (y:ℂ) * I)) x := by
    intro y x
    by_cases hx : x ∈ Ioo p q
    · rw [Set.indicator_of_mem (show (y, x) ∈ {w : ℝ × ℝ | w.2 ∈ Ioo p q} from hx),
        Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (show (y, x) ∉ {w : ℝ × ℝ | w.2 ∈ Ioo p q} from hx),
        Set.indicator_of_notMem hx]
  simp_rw [h3, lintegral_indicator measurableSet_Ioo] at h2
  exact h2

/-- Measurability of an `x`-slice `lintegral` of a globally measurable `ℂ`-valued function
(mirror of `ac_n_c_measurable_lintegral_slice`, integrating over `y` instead of `x`). -/
theorem ac_n_c_measurable_lintegral_slice_y {G : ℂ → ℝ≥0∞} (hG : Measurable G) (p q : ℝ) :
    Measurable (fun x : ℝ => ∫⁻ y in Ioo p q, G ((x:ℂ) + (y:ℂ) * I)) := by
  have h1 : Measurable (fun z : ℝ × ℝ =>
      ({w : ℝ × ℝ | w.2 ∈ Ioo p q}).indicator (fun w => G ((w.1:ℂ) + (w.2:ℂ) * I)) z) := by
    apply Measurable.indicator _ (measurable_snd measurableSet_Ioo)
    exact hG.comp (by fun_prop)
  have h2 : Measurable (fun x : ℝ => ∫⁻ y, ({w : ℝ × ℝ | w.2 ∈ Ioo p q}).indicator
      (fun w => G ((w.1:ℂ) + (w.2:ℂ) * I)) (x, y) ∂volume) := h1.lintegral_prod_right'
  have h3 : ∀ x y : ℝ, ({w : ℝ × ℝ | w.2 ∈ Ioo p q}).indicator
      (fun w => G ((w.1:ℂ) + (w.2:ℂ) * I)) (x, y) =
      (Ioo p q).indicator (fun y => G ((x:ℂ) + (y:ℂ) * I)) y := by
    intro x y
    by_cases hy : y ∈ Ioo p q
    · rw [Set.indicator_of_mem (show (x, y) ∈ {w : ℝ × ℝ | w.2 ∈ Ioo p q} from hy),
        Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem (show (x, y) ∉ {w : ℝ × ℝ | w.2 ∈ Ioo p q} from hy),
        Set.indicator_of_notMem hy]
  simp_rw [h3, lintegral_indicator measurableSet_Ioo] at h2
  exact h2

/-- The good horizontal offset `t`: for a.e. `t`, all `n+2` horizontal grid lines through it are
A.C. on the full `x`-range, and the total `∂ₓf` energy along them (summed) is bounded by the
average, i.e. by `1/a` times the total energy on the big rectangle. -/
theorem ac_n_c_good_t {f : ℂ → ℂ} {D : Set ℂ} (hacl : IsACL f D)
    {x₀ y₀ L a : ℝ} (hL : 0 < L) (ha : 0 < a) {n : ℕ} (hn : L = n * a)
    (hQ : closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a) ⊆ D) :
    ∃ t ∈ Ioo (0:ℝ) a,
      (∀ m : ℤ, -1 ≤ m → m ≤ (n:ℤ) →
        AbsolutelyContinuousOnInterval
          (fun x : ℝ => f ((x:ℂ) + ((t + (y₀ + m * a) : ℝ):ℂ) * I)) (x₀ - a) (x₀ + L + a)) ∧
      (∑ m ∈ Finset.Icc (-1:ℤ) (n:ℤ),
          ∫⁻ x in Ioo (x₀ - a) (x₀ + L + a),
            ‖partialX f ((x:ℂ) + ((t + (y₀ + m * a) : ℝ):ℂ) * I)‖ₑ ^ 2) * ENNReal.ofReal a ≤
        ∫⁻ z in closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a), ‖partialX f z‖ₑ ^ 2 := by
  have hxlt : x₀ - a < x₀ + L + a := by linarith
  have hylt : y₀ - a < y₀ + L + a := by linarith
  have hcont : ContinuousOn f (closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a)) :=
    hacl.1.mono hQ
  have hACLrect := hacl.2
  have hACLhoriz := (hACLrect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a) hxlt hylt hQ).2
  have he1 : ∀ m : ℤ, -1 ≤ m → m ≤ (n:ℤ) → y₀ - a ≤ y₀ + m * a := by
    intro m hm1 _
    have hm1' : (-1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
    nlinarith
  have he2 : ∀ m : ℤ, -1 ≤ m → m ≤ (n:ℤ) → y₀ + m * a + a ≤ y₀ + L + a := by
    intro m _ hm2
    have hm2' : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hm2
    nlinarith [hn]
  have hACLshift := ac_n_c_ae_shift_all hACLhoriz he1 he2
  -- The globally-measurable clamped version of `Fx`.
  have hFmX : Measurable (fun z => ‖partialX (f ∘ rectClamp (x₀ - a) (x₀ + L + a) (y₀ - a)
      (y₀ + L + a)) z‖ₑ ^ 2) :=
    ((measurable_partialX_comp_rectClamp hxlt.le hylt.le hcont).enorm).pow_const 2
  set Fxc : ℝ → ℝ≥0∞ := fun y => ∫⁻ x in Ioo (x₀ - a) (x₀ + L + a),
    ‖partialX (f ∘ rectClamp (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a))
      ((x:ℂ) + (y:ℂ) * I)‖ₑ ^ 2 with hFxc_def
  have hFxc_meas : Measurable Fxc := ac_n_c_measurable_lintegral_slice hFmX (x₀ - a) (x₀ + L + a)
  set Hc : ℝ → ℝ≥0∞ := fun t => ∑ m ∈ Finset.Icc (-1:ℤ) (n:ℤ), Fxc (t + (y₀ + m * a)) with hHc_def
  have hHc_meas : Measurable Hc := by
    apply Finset.measurable_sum
    intro m _
    exact hFxc_meas.comp (by fun_prop)
  -- Pointwise bridge: the clamped and true `partialX` agree for `x` in the open `x`-range and
  -- `y` in the closed `y`-range.
  have hbridge_pt : ∀ x y : ℝ, x ∈ Ioo (x₀ - a) (x₀ + L + a) → y ∈ Icc (y₀ - a) (y₀ + L + a) →
      ‖partialX (f ∘ rectClamp (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a))
        ((x:ℂ) + (y:ℂ) * I)‖ₑ ^ 2 = ‖partialX f ((x:ℂ) + (y:ℂ) * I)‖ₑ ^ 2 := by
    intro x y hx hy
    rw [ac_n_c_partialX_clamp_eq y hy x hx]
  have hbridge : ∀ y : ℝ, y ∈ Icc (y₀ - a) (y₀ + L + a) →
      Fxc y = ∫⁻ x in Ioo (x₀ - a) (x₀ + L + a), ‖partialX f ((x:ℂ) + (y:ℂ) * I)‖ₑ ^ 2 := by
    intro y hy
    rw [hFxc_def]
    exact setLIntegral_congr_fun measurableSet_Ioo (fun x hx => hbridge_pt x y hx hy)
  have hbridge_shift : ∀ t : ℝ, t ∈ Ioo (0:ℝ) a → ∀ m : ℤ, -1 ≤ m → m ≤ (n:ℤ) →
      Fxc (t + (y₀ + m * a)) =
        ∫⁻ x in Ioo (x₀ - a) (x₀ + L + a),
          ‖partialX f ((x:ℂ) + ((t + (y₀ + m * a) : ℝ):ℂ) * I)‖ₑ ^ 2 := by
    intro t ht m hm1 hm2
    apply hbridge
    exact ⟨he1 m hm1 hm2 |>.trans (by linarith [ht.1]),
      (by linarith [ht.2] : t + (y₀ + m * a) ≤ y₀ + m * a + a).trans (he2 m hm1 hm2)⟩
  have hHeq : ∀ t : ℝ, t ∈ Ioo (0:ℝ) a → Hc t =
      ∑ m ∈ Finset.Icc (-1:ℤ) (n:ℤ),
        ∫⁻ x in Ioo (x₀ - a) (x₀ + L + a),
          ‖partialX f ((x:ℂ) + ((t + (y₀ + m * a) : ℝ):ℂ) * I)‖ₑ ^ 2 := by
    intro t ht
    rw [hHc_def]
    exact Finset.sum_congr rfl (fun m hm => by
      rw [Finset.mem_Icc] at hm
      exact hbridge_shift t ht m hm.1 hm.2)
  obtain ⟨t, ht, htAC, htbound⟩ := ac_n_c_exists_good_offset_ac ha hHc_meas.aemeasurable hACLshift
  refine ⟨t, ht, htAC, ?_⟩
  rw [← hHeq t ht]
  calc Hc t * ENNReal.ofReal a ≤ ∫⁻ t in Ioo 0 a, Hc t := htbound
    _ = ∑ m ∈ Finset.Icc (-1:ℤ) (n:ℤ), ∫⁻ t in Ioo (0:ℝ) a, Fxc (t + (y₀ + m * a)) := by
        rw [hHc_def]; exact lintegral_finsetSum _ (fun m _ => hFxc_meas.comp (by fun_prop))
    _ = ∫⁻ y in Ioo (y₀ - a) (y₀ + ((n:ℝ) + 1) * a), Fxc y := (ac_n_c_lintegral_partition hFxc_meas ha n).symm
    _ = ∫⁻ y in Ioo (y₀ - a) (y₀ + L + a), Fxc y := by rw [hn]; ring_nf
    _ = ∫⁻ y in Ioo (y₀ - a) (y₀ + L + a),
          ∫⁻ x in Ioo (x₀ - a) (x₀ + L + a), ‖partialX f ((x:ℂ) + (y:ℂ) * I)‖ₑ ^ 2 := by
        refine setLIntegral_congr_fun measurableSet_Ioo (fun y hy => ?_)
        exact hbridge y (Ioo_subset_Icc_self hy)
    _ = ∫⁻ x in Ioo (x₀ - a) (x₀ + L + a), ∫⁻ y in Ioo (y₀ - a) (y₀ + L + a),
          ‖partialX (f ∘ rectClamp (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a))
            ((x:ℂ) + (y:ℂ) * I)‖ₑ ^ 2 := by
        have hjm : AEMeasurable
            (Function.uncurry (fun x y : ℝ => ‖partialX (f ∘ rectClamp (x₀ - a) (x₀ + L + a)
              (y₀ - a) (y₀ + L + a)) ((x:ℂ) + (y:ℂ) * I)‖ₑ ^ 2))
            ((volume.restrict (Ioo (x₀ - a) (x₀ + L + a))).prod
              (volume.restrict (Ioo (y₀ - a) (y₀ + L + a)))) :=
          (hFmX.comp continuous_rectCoords.measurable).aemeasurable
        refine Eq.trans ?_ (lintegral_lintegral_swap hjm).symm
        exact setLIntegral_congr_fun measurableSet_Ioo (fun y hy => (hbridge y (Ioo_subset_Icc_self hy)).symm)
    _ = ∫⁻ x in Ioo (x₀ - a) (x₀ + L + a), ∫⁻ y in Ioo (y₀ - a) (y₀ + L + a),
          ‖partialX f ((x:ℂ) + (y:ℂ) * I)‖ₑ ^ 2 := by
        refine setLIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
        exact setLIntegral_congr_fun measurableSet_Ioo (fun y hy => hbridge_pt x y hx (Ioo_subset_Icc_self hy))
    _ = ∫⁻ z in closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a), ‖partialX f z‖ₑ ^ 2 :=
        (ac_n_c_lintegral_partialX hxlt.le hylt.le hcont).symm

/-- The good vertical offset `s`: mirror of `ac_n_c_good_t` for `∂_y f` and the vertical grid
lines. -/
theorem ac_n_c_good_s {f : ℂ → ℂ} {D : Set ℂ} (hacl : IsACL f D)
    {x₀ y₀ L a : ℝ} (hL : 0 < L) (ha : 0 < a) {n : ℕ} (hn : L = n * a)
    (hQ : closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a) ⊆ D) :
    ∃ s ∈ Ioo (0:ℝ) a,
      (∀ m : ℤ, -1 ≤ m → m ≤ (n:ℤ) →
        AbsolutelyContinuousOnInterval
          (fun y : ℝ => f (((s + (x₀ + m * a) : ℝ):ℂ) + (y:ℂ) * I)) (y₀ - a) (y₀ + L + a)) ∧
      (∑ m ∈ Finset.Icc (-1:ℤ) (n:ℤ),
          ∫⁻ y in Ioo (y₀ - a) (y₀ + L + a),
            ‖partialY f (((s + (x₀ + m * a) : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2) * ENNReal.ofReal a ≤
        ∫⁻ z in closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a), ‖partialY f z‖ₑ ^ 2 := by
  have hxlt : x₀ - a < x₀ + L + a := by linarith
  have hylt : y₀ - a < y₀ + L + a := by linarith
  have hcont : ContinuousOn f (closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a)) :=
    hacl.1.mono hQ
  have hACLrect := hacl.2
  have hACLvert := (hACLrect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a) hxlt hylt hQ).1
  have he1 : ∀ m : ℤ, -1 ≤ m → m ≤ (n:ℤ) → x₀ - a ≤ x₀ + m * a := by
    intro m hm1 _
    have hm1' : (-1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
    nlinarith
  have he2 : ∀ m : ℤ, -1 ≤ m → m ≤ (n:ℤ) → x₀ + m * a + a ≤ x₀ + L + a := by
    intro m _ hm2
    have hm2' : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hm2
    nlinarith [hn]
  have hACLshift := ac_n_c_ae_shift_all hACLvert he1 he2
  have hFmY : Measurable (fun z => ‖partialY (f ∘ rectClamp (x₀ - a) (x₀ + L + a) (y₀ - a)
      (y₀ + L + a)) z‖ₑ ^ 2) :=
    ((measurable_partialY_comp_rectClamp hxlt.le hylt.le hcont).enorm).pow_const 2
  set Gyc : ℝ → ℝ≥0∞ := fun x => ∫⁻ y in Ioo (y₀ - a) (y₀ + L + a),
    ‖partialY (f ∘ rectClamp (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a))
      ((x:ℂ) + (y:ℂ) * I)‖ₑ ^ 2 with hGyc_def
  have hGyc_meas : Measurable Gyc := ac_n_c_measurable_lintegral_slice_y hFmY (y₀ - a) (y₀ + L + a)
  set Kc : ℝ → ℝ≥0∞ := fun s => ∑ m ∈ Finset.Icc (-1:ℤ) (n:ℤ), Gyc (s + (x₀ + m * a)) with hKc_def
  have hKc_meas : Measurable Kc := by
    apply Finset.measurable_sum
    intro m _
    exact hGyc_meas.comp (by fun_prop)
  have hbridge_pt : ∀ x y : ℝ, x ∈ Icc (x₀ - a) (x₀ + L + a) → y ∈ Ioo (y₀ - a) (y₀ + L + a) →
      ‖partialY (f ∘ rectClamp (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a))
        ((x:ℂ) + (y:ℂ) * I)‖ₑ ^ 2 = ‖partialY f ((x:ℂ) + (y:ℂ) * I)‖ₑ ^ 2 := by
    intro x y hx hy
    rw [ac_n_c_partialY_clamp_eq x hx y hy]
  have hbridge : ∀ x : ℝ, x ∈ Icc (x₀ - a) (x₀ + L + a) →
      Gyc x = ∫⁻ y in Ioo (y₀ - a) (y₀ + L + a), ‖partialY f ((x:ℂ) + (y:ℂ) * I)‖ₑ ^ 2 := by
    intro x hx
    rw [hGyc_def]
    exact setLIntegral_congr_fun measurableSet_Ioo (fun y hy => hbridge_pt x y hx hy)
  have hbridge_shift : ∀ s : ℝ, s ∈ Ioo (0:ℝ) a → ∀ m : ℤ, -1 ≤ m → m ≤ (n:ℤ) →
      Gyc (s + (x₀ + m * a)) =
        ∫⁻ y in Ioo (y₀ - a) (y₀ + L + a),
          ‖partialY f (((s + (x₀ + m * a) : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2 := by
    intro s hs m hm1 hm2
    apply hbridge
    exact ⟨he1 m hm1 hm2 |>.trans (by linarith [hs.1]),
      (by linarith [hs.2] : s + (x₀ + m * a) ≤ x₀ + m * a + a).trans (he2 m hm1 hm2)⟩
  have hKeq : ∀ s : ℝ, s ∈ Ioo (0:ℝ) a → Kc s =
      ∑ m ∈ Finset.Icc (-1:ℤ) (n:ℤ),
        ∫⁻ y in Ioo (y₀ - a) (y₀ + L + a),
          ‖partialY f (((s + (x₀ + m * a) : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2 := by
    intro s hs
    rw [hKc_def]
    exact Finset.sum_congr rfl (fun m hm => by
      rw [Finset.mem_Icc] at hm
      exact hbridge_shift s hs m hm.1 hm.2)
  obtain ⟨s, hs, hsAC, hsbound⟩ := ac_n_c_exists_good_offset_ac ha hKc_meas.aemeasurable hACLshift
  refine ⟨s, hs, hsAC, ?_⟩
  rw [← hKeq s hs]
  calc Kc s * ENNReal.ofReal a ≤ ∫⁻ s in Ioo 0 a, Kc s := hsbound
    _ = ∑ m ∈ Finset.Icc (-1:ℤ) (n:ℤ), ∫⁻ s in Ioo (0:ℝ) a, Gyc (s + (x₀ + m * a)) := by
        rw [hKc_def]; exact lintegral_finsetSum _ (fun m _ => hGyc_meas.comp (by fun_prop))
    _ = ∫⁻ x in Ioo (x₀ - a) (x₀ + ((n:ℝ) + 1) * a), Gyc x := (ac_n_c_lintegral_partition hGyc_meas ha n).symm
    _ = ∫⁻ x in Ioo (x₀ - a) (x₀ + L + a), Gyc x := by rw [hn]; ring_nf
    _ = ∫⁻ x in Ioo (x₀ - a) (x₀ + L + a),
          ∫⁻ y in Ioo (y₀ - a) (y₀ + L + a), ‖partialY f ((x:ℂ) + (y:ℂ) * I)‖ₑ ^ 2 := by
        refine setLIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
        exact hbridge x (Ioo_subset_Icc_self hx)
    _ = ∫⁻ z in closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a), ‖partialY f z‖ₑ ^ 2 :=
        (ac_n_c_lintegral_partialY hxlt.le hylt.le hcont).symm

/-- The pieces `Ioo (e₀+j*a) (e₀+j*a+a)` for `j` ranging over a `Finset`, all lying inside
`Ioo p q`, are pairwise disjoint, so their `lintegral`s sum to at most `∫⁻ x in Ioo p q, G x`. -/
theorem ac_n_c_sum_lintegral_subset_le {G : ℝ → ℝ≥0∞} {e₀ a p q : ℝ}
    (ha : 0 < a) (idx : Finset ℤ) (hsub : ∀ j ∈ idx, p ≤ e₀ + j * a ∧ e₀ + j * a + a ≤ q) :
    ∑ j ∈ idx, ∫⁻ x in Ioo (e₀ + j * a) (e₀ + j * a + a), G x ≤ ∫⁻ x in Ioo p q, G x := by
  have hdisj : (↑idx : Set ℤ).PairwiseDisjoint (fun j => Ioo (e₀ + j * a) (e₀ + j * a + a)) := by
    intro j1 _ j2 _ hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hle : j1 + 1 ≤ j2 := hlt
      refine Set.disjoint_left.mpr (fun y hy1 hy2 => ?_)
      have h1 : y < e₀ + j1 * a + a := hy1.2
      have h2 : e₀ + j2 * a < y := hy2.1
      have : (j1:ℝ) + 1 ≤ (j2:ℝ) := by exact_mod_cast hle
      nlinarith
    · have hle : j2 + 1 ≤ j1 := hlt
      refine Set.disjoint_left.mpr (fun y hy1 hy2 => ?_)
      have h1 : e₀ + j1 * a < y := hy1.1
      have h2 : y < e₀ + j2 * a + a := hy2.2
      have : (j2:ℝ) + 1 ≤ (j1:ℝ) := by exact_mod_cast hle
      nlinarith
  have hmeas : ∀ j ∈ idx, MeasurableSet (Ioo (e₀ + j * a) (e₀ + j * a + a)) := fun j _ => measurableSet_Ioo
  rw [← lintegral_biUnion_finset hdisj hmeas]
  apply lintegral_mono_set
  intro x hx
  simp only [mem_iUnion] at hx
  obtain ⟨j, hj, hjx⟩ := hx
  obtain ⟨h1, h2⟩ := hsub j hj
  exact ⟨by linarith [hjx.1], by linarith [hjx.2]⟩

/-- `idx = Icc (-1) (n-1)` shifted by `0` or `1` stays inside the full range `Icc (-1) n`, so a
sum over `idx` of a shifted function is bounded by the sum over the full range. -/
theorem ac_n_c_grid_sum_le_full {G : ℤ → ℝ≥0∞} {n : ℕ} {idx : Finset ℤ}
    (hidx : idx = Finset.Icc (-1:ℤ) ((n:ℤ) - 1)) {shift : ℤ} (hshift : shift = 0 ∨ shift = 1) :
    ∑ k ∈ idx, G (k + shift) ≤ ∑ m ∈ Finset.Icc (-1:ℤ) (n:ℤ), G m := by
  have hinj : Set.InjOn (· + shift) (↑idx : Set ℤ) := fun a _ b _ h => by
    simp only at h; omega
  rw [← Finset.sum_image (f := G) hinj]
  apply Finset.sum_le_sum_of_subset
  intro m hm
  rw [Finset.mem_image] at hm
  obtain ⟨k, hk, rfl⟩ := hm
  rw [hidx, Finset.mem_Icc] at hk
  rw [Finset.mem_Icc]
  omega

/-- `‖partialX f ·‖ₑ^2` is a.e.-measurable w.r.t. the restriction to a closed rectangle on which
`f` is continuous (via the clamp bridge). -/
theorem ac_n_c_aemeasurable_partialX_sq {f : ℂ → ℂ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f (closedRect a b c d)) :
    AEMeasurable (fun z => ‖partialX f z‖ₑ ^ 2) (volume.restrict (closedRect a b c d)) := by
  have hFmX : Measurable (fun z => ‖partialX (f ∘ rectClamp a b c d) z‖ₑ ^ 2) :=
    ((measurable_partialX_comp_rectClamp hab hcd hf).enorm).pow_const 2
  refine hFmX.aemeasurable.congr ?_
  have hnull : volume {z : ℂ | z ∈ closedRect a b c d ∧ z.re ∉ Ioo a b} = 0 := by
    refine measure_mono_null (t := closedRect a b c d \ openRect a b c d) ?_
      (menchoff_volume_closedRect_diff_openRect a b c d)
    rintro z ⟨hz1, hz2⟩
    refine ⟨hz1, fun hz3 => hz2 ⟨hz3.1, hz3.2.1⟩⟩
  have hae0 : ∀ᵐ z ∂volume, z ∈ closedRect a b c d → z.re ∈ Ioo a b := by
    rw [ae_iff]
    have hset : {z : ℂ | ¬(z ∈ closedRect a b c d → z.re ∈ Ioo a b)} =
        {z : ℂ | z ∈ closedRect a b c d ∧ z.re ∉ Ioo a b} := by
      ext z; exact Classical.not_imp
    rw [hset]; exact hnull
  filter_upwards [ae_restrict_of_ae hae0,
    ae_restrict_mem (acl_isCompact_closedRect a b c d).isClosed.measurableSet] with z hz0 hz1
  have hzre := hz0 hz1
  have e1 : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
  rw [e1, ac_n_c_partialX_clamp_eq z.im ⟨hz1.2.2.1, hz1.2.2.2⟩ z.re hzre]

/-- `‖partialY f ·‖ₑ^2` is a.e.-measurable w.r.t. the restriction to a closed rectangle on which
`f` is continuous (via the clamp bridge). -/
theorem ac_n_c_aemeasurable_partialY_sq {f : ℂ → ℂ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f (closedRect a b c d)) :
    AEMeasurable (fun z => ‖partialY f z‖ₑ ^ 2) (volume.restrict (closedRect a b c d)) := by
  have hFmY : Measurable (fun z => ‖partialY (f ∘ rectClamp a b c d) z‖ₑ ^ 2) :=
    ((measurable_partialY_comp_rectClamp hab hcd hf).enorm).pow_const 2
  refine hFmY.aemeasurable.congr ?_
  have hnull : volume {z : ℂ | z ∈ closedRect a b c d ∧ z.im ∉ Ioo c d} = 0 := by
    refine measure_mono_null (t := closedRect a b c d \ openRect a b c d) ?_
      (menchoff_volume_closedRect_diff_openRect a b c d)
    rintro z ⟨hz1, hz2⟩
    refine ⟨hz1, fun hz3 => hz2 ⟨hz3.2.2.1, hz3.2.2.2⟩⟩
  have hae0 : ∀ᵐ z ∂volume, z ∈ closedRect a b c d → z.im ∈ Ioo c d := by
    rw [ae_iff]
    have hset : {z : ℂ | ¬(z ∈ closedRect a b c d → z.im ∈ Ioo c d)} =
        {z : ℂ | z ∈ closedRect a b c d ∧ z.im ∉ Ioo c d} := by
      ext z; exact Classical.not_imp
    rw [hset]; exact hnull
  filter_upwards [ae_restrict_of_ae hae0,
    ae_restrict_mem (acl_isCompact_closedRect a b c d).isClosed.measurableSet] with z hz0 hz1
  have hzim := hz0 hz1
  have e1 : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
  rw [e1, ac_n_c_partialY_clamp_eq z.re ⟨hz1.1, hz1.2.1⟩ z.im hzim]

/-- **N2.** The offset-averaged grid estimate.  Stated for a continuous injective A.C.L. map on an
open set (generalized from `K`-q.c. maps on 2026-09-22 for Lemma 13.1; the q.c. hypothesis entered
only through Theorem 9.1). -/
theorem ac_n_volume_image_le_lintegral {f : ℂ → ℂ} {D : Set ℂ} (hDopen : IsOpen D)
    (hacl : IsACL f D) (hinj : InjOn f D)
    {x₀ y₀ L a : ℝ} (hL : 0 < L) (ha : 0 < a) {n : ℕ} (hn : L = n * a)
    (hQ : closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a) ⊆ D) :
    volume (f '' closedRect x₀ (x₀ + L) y₀ (y₀ + L)) ≤ ENNReal.ofReal (4 * π) *
      ∫⁻ z in closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a),
        (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := by
  obtain ⟨t, ht, htAC, htbound⟩ := ac_n_c_good_t hacl hL ha hn hQ
  obtain ⟨s, hs, hsAC, hsbound⟩ := ac_n_c_good_s hacl hL ha hn hQ
  have hxlt : x₀ - a < x₀ + L + a := by linarith
  have hylt : y₀ - a < y₀ + L + a := by linarith
  have hcont : ContinuousOn f D := hacl.1
  set idx : Finset ℤ := Finset.Icc (-1:ℤ) ((n:ℤ) - 1) with hidx_def
  have hmemIdx : ∀ j : ℤ, j ∈ idx ↔ -1 ≤ j ∧ j ≤ (n:ℤ) - 1 := fun j => by
    rw [hidx_def, Finset.mem_Icc]
  -- coordinatewise bounds putting each grid square inside the big rectangle
  have hxb : ∀ j : ℤ, -1 ≤ j → j ≤ (n:ℤ) - 1 →
      x₀ - a ≤ x₀ + s + j * a ∧ x₀ + s + j * a + a ≤ x₀ + L + a := by
    intro j hj1 hj2
    have hj1' : (-1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj1
    have hj2' : (j:ℝ) ≤ (n:ℝ) - 1 := by exact_mod_cast hj2
    have hm1 : (-1:ℝ) * a ≤ (j:ℝ) * a := mul_le_mul_of_nonneg_right hj1' ha.le
    have hm2 : (j:ℝ) * a ≤ ((n:ℝ) - 1) * a := mul_le_mul_of_nonneg_right hj2' ha.le
    constructor
    · nlinarith [hs.1, hm1]
    · nlinarith [hs.2, hm2, hn]
  have hyb : ∀ k : ℤ, -1 ≤ k → k ≤ (n:ℤ) - 1 →
      y₀ - a ≤ y₀ + t + k * a ∧ y₀ + t + k * a + a ≤ y₀ + L + a := by
    intro k hk1 hk2
    have hk1' : (-1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
    have hk2' : (k:ℝ) ≤ (n:ℝ) - 1 := by exact_mod_cast hk2
    have hm1 : (-1:ℝ) * a ≤ (k:ℝ) * a := mul_le_mul_of_nonneg_right hk1' ha.le
    have hm2 : (k:ℝ) * a ≤ ((n:ℝ) - 1) * a := mul_le_mul_of_nonneg_right hk2' ha.le
    constructor
    · nlinarith [ht.1, hm1]
    · nlinarith [ht.2, hm2, hn]
  have hQjkR : ∀ j : ℤ, -1 ≤ j → j ≤ (n:ℤ) - 1 → ∀ k : ℤ, -1 ≤ k → k ≤ (n:ℤ) - 1 →
      closedRect (x₀ + s + j * a) (x₀ + s + j * a + a) (y₀ + t + k * a) (y₀ + t + k * a + a) ⊆
        closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a) := by
    intro j hj1 hj2 k hk1 hk2 z hz
    obtain ⟨hxb1, hxb2⟩ := hxb j hj1 hj2
    obtain ⟨hyb1, hyb2⟩ := hyb k hk1 hk2
    exact ⟨by linarith [hz.1], by linarith [hz.2.1], by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩
  have hQjk : ∀ j : ℤ, -1 ≤ j → j ≤ (n:ℤ) - 1 → ∀ k : ℤ, -1 ≤ k → k ≤ (n:ℤ) - 1 →
      closedRect (x₀ + s + j * a) (x₀ + s + j * a + a) (y₀ + t + k * a) (y₀ + t + k * a + a) ⊆ D :=
    fun j hj1 hj2 k hk1 hk2 => (hQjkR j hj1 hj2 k hk1 hk2).trans hQ
  -- N1 applied to each grid square
  have hN1sq : ∀ j : ℤ, -1 ≤ j → j ≤ (n:ℤ) - 1 → ∀ k : ℤ, -1 ≤ k → k ≤ (n:ℤ) - 1 →
      volume (f '' closedRect (x₀ + s + j * a) (x₀ + s + j * a + a) (y₀ + t + k * a)
          (y₀ + t + k * a + a)) ≤
        ENNReal.ofReal (π * a) *
          ((∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
              ‖partialX f ((x:ℂ) + ((y₀ + t + k * a : ℝ):ℂ) * I)‖ₑ ^ 2) +
           (∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
              ‖partialX f ((x:ℂ) + ((y₀ + t + k * a + a : ℝ):ℂ) * I)‖ₑ ^ 2) +
           (∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
              ‖partialY f (((x₀ + s + j * a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2) +
           (∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
              ‖partialY f (((x₀ + s + j * a + a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2)) := by
    intro j hj1 hj2 k hk1 hk2
    obtain ⟨hxb1, hxb2⟩ := hxb j hj1 hj2
    obtain ⟨hyb1, hyb2⟩ := hyb k hk1 hk2
    have huIccX : uIcc (x₀ + s + j * a) (x₀ + s + j * a + a) ⊆ uIcc (x₀ - a) (x₀ + L + a) := by
      rw [uIcc_of_le (by linarith : x₀ + s + j * a ≤ x₀ + s + j * a + a), uIcc_of_le hxlt.le]
      exact Icc_subset_Icc hxb1 hxb2
    have huIccY : uIcc (y₀ + t + k * a) (y₀ + t + k * a + a) ⊆ uIcc (y₀ - a) (y₀ + L + a) := by
      rw [uIcc_of_le (by linarith : y₀ + t + k * a ≤ y₀ + t + k * a + a), uIcc_of_le hylt.le]
      exact Icc_subset_Icc hyb1 hyb2
    have hbot : AbsolutelyContinuousOnInterval
        (fun x : ℝ => f ((x:ℂ) + ((y₀ + t + k * a : ℝ):ℂ) * I))
        (x₀ + s + j * a) (x₀ + s + j * a + a) := by
      have heq : y₀ + t + k * a = t + (y₀ + (k:ℝ) * a) := by ring
      rw [heq]
      exact (htAC k hk1 (by omega)).mono huIccX
    have htop : AbsolutelyContinuousOnInterval
        (fun x : ℝ => f ((x:ℂ) + ((y₀ + t + k * a + a : ℝ):ℂ) * I))
        (x₀ + s + j * a) (x₀ + s + j * a + a) := by
      have heq : y₀ + t + k * a + a = t + (y₀ + ((k + 1 : ℤ):ℝ) * a) := by push_cast; ring
      rw [heq]
      exact (htAC (k + 1) (by omega) (by omega)).mono huIccX
    have hleft : AbsolutelyContinuousOnInterval
        (fun y : ℝ => f (((x₀ + s + j * a : ℝ):ℂ) + (y:ℂ) * I))
        (y₀ + t + k * a) (y₀ + t + k * a + a) := by
      have heq : x₀ + s + j * a = s + (x₀ + (j:ℝ) * a) := by ring
      rw [heq]
      exact (hsAC j hj1 (by omega)).mono huIccY
    have hright : AbsolutelyContinuousOnInterval
        (fun y : ℝ => f (((x₀ + s + j * a + a : ℝ):ℂ) + (y:ℂ) * I))
        (y₀ + t + k * a) (y₀ + t + k * a + a) := by
      have heq : x₀ + s + j * a + a = s + (x₀ + ((j + 1 : ℤ):ℝ) * a) := by push_cast; ring
      rw [heq]
      exact (hsAC (j + 1) (by omega) (by omega)).mono huIccY
    exact ac_n_volume_image_le_boundary hDopen hcont hinj ha (hQjk j hj1 hj2 k hk1 hk2)
      hbot htop hleft hright
  -- Coverage: the target square is covered by the grid squares.
  have hcover : closedRect x₀ (x₀ + L) y₀ (y₀ + L) ⊆
      ⋃ j ∈ idx, ⋃ k ∈ idx,
        closedRect (x₀ + s + j * a) (x₀ + s + j * a + a) (y₀ + t + k * a) (y₀ + t + k * a + a) := by
    intro z hz
    obtain ⟨j, hj1, hj2, hjx1, hjx2⟩ := ac_n_c_exists_j ha hs
      (show z.re ∈ Icc x₀ (x₀ + n * a) from ⟨hz.1, hn ▸ hz.2.1⟩)
    obtain ⟨k, hk1, hk2, hky1, hky2⟩ := ac_n_c_exists_j ha ht
      (show z.im ∈ Icc y₀ (y₀ + n * a) from ⟨hz.2.2.1, hn ▸ hz.2.2.2⟩)
    simp only [mem_iUnion]
    have hjx2' : z.re ≤ x₀ + s + j * a + a := by
      have hcast : ((j + 1 : ℤ):ℝ) * a = (j:ℝ) * a + a := by push_cast; ring
      linarith [hjx2, hcast]
    have hky2' : z.im ≤ y₀ + t + k * a + a := by
      have hcast : ((k + 1 : ℤ):ℝ) * a = (k:ℝ) * a + a := by push_cast; ring
      linarith [hky2, hcast]
    exact ⟨j, (hmemIdx j).mpr ⟨hj1, hj2⟩, k, (hmemIdx k).mpr ⟨hk1, hk2⟩,
      hjx1, hjx2', hky1, hky2'⟩
  have himg_cover : f '' closedRect x₀ (x₀ + L) y₀ (y₀ + L) ⊆
      ⋃ j ∈ idx, ⋃ k ∈ idx,
        f '' closedRect (x₀ + s + j * a) (x₀ + s + j * a + a) (y₀ + t + k * a)
          (y₀ + t + k * a + a) := by
    have h := image_mono (f := f) hcover
    simpa [image_iUnion] using h
  have hvol_cover : volume (f '' closedRect x₀ (x₀ + L) y₀ (y₀ + L)) ≤
      ∑ j ∈ idx, ∑ k ∈ idx,
        volume (f '' closedRect (x₀ + s + j * a) (x₀ + s + j * a + a) (y₀ + t + k * a)
          (y₀ + t + k * a + a)) :=
    (measure_mono himg_cover).trans <| (measure_biUnion_finset_le idx _).trans <|
      Finset.sum_le_sum (fun j _ => measure_biUnion_finset_le idx _)
  have hvol_cover2 : volume (f '' closedRect x₀ (x₀ + L) y₀ (y₀ + L)) ≤
      ∑ j ∈ idx, ∑ k ∈ idx, ENNReal.ofReal (π * a) *
        ((∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
            ‖partialX f ((x:ℂ) + ((y₀ + t + k * a : ℝ):ℂ) * I)‖ₑ ^ 2) +
         (∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
            ‖partialX f ((x:ℂ) + ((y₀ + t + k * a + a : ℝ):ℂ) * I)‖ₑ ^ 2) +
         (∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
            ‖partialY f (((x₀ + s + j * a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2) +
         (∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
            ‖partialY f (((x₀ + s + j * a + a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2)) :=
    hvol_cover.trans (Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun k hk =>
      hN1sq j ((hmemIdx j).mp hj).1 ((hmemIdx j).mp hj).2
        k ((hmemIdx k).mp hk).1 ((hmemIdx k).mp hk).2)))
  set fullIdx : Finset ℤ := Finset.Icc (-1:ℤ) (n:ℤ) with hfullIdx_def
  have hidx_sub_full : idx ⊆ fullIdx := by
    rw [hidx_def, hfullIdx_def]; intro m hm; rw [Finset.mem_Icc] at hm ⊢; omega
  set Ffull : ℤ → ℝ≥0∞ := fun m =>
    ∫⁻ x in Ioo (x₀ - a) (x₀ + L + a), ‖partialX f ((x:ℂ) + ((t + (y₀ + m * a) : ℝ):ℂ) * I)‖ₑ ^ 2
    with hFfull_def
  set Gfull : ℤ → ℝ≥0∞ := fun m =>
    ∫⁻ y in Ioo (y₀ - a) (y₀ + L + a), ‖partialY f (((s + (x₀ + m * a) : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2
    with hGfull_def
  have hXsum1 : ∀ k : ℤ, ∑ j ∈ idx, ∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
      ‖partialX f ((x:ℂ) + ((y₀ + t + k * a : ℝ):ℂ) * I)‖ₑ ^ 2 ≤ Ffull k := by
    intro k
    have heq : ∀ x : ℝ, ‖partialX f ((x:ℂ) + ((y₀ + t + k * a : ℝ):ℂ) * I)‖ₑ ^ 2 =
        ‖partialX f ((x:ℂ) + ((t + (y₀ + (k:ℝ) * a) : ℝ):ℂ) * I)‖ₑ ^ 2 := by
      intro x; congr 2; ring
    simp_rw [heq]
    exact ac_n_c_sum_lintegral_subset_le ha idx
      (fun j hj => hxb j ((hmemIdx j).mp hj).1 ((hmemIdx j).mp hj).2)
  have hXsum2 : ∀ k : ℤ, ∑ j ∈ idx, ∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
      ‖partialX f ((x:ℂ) + ((y₀ + t + k * a + a : ℝ):ℂ) * I)‖ₑ ^ 2 ≤ Ffull (k + 1) := by
    intro k
    have heq : ∀ x : ℝ, ‖partialX f ((x:ℂ) + ((y₀ + t + k * a + a : ℝ):ℂ) * I)‖ₑ ^ 2 =
        ‖partialX f ((x:ℂ) + ((t + (y₀ + ((k + 1 : ℤ):ℝ) * a) : ℝ):ℂ) * I)‖ₑ ^ 2 := by
      intro x; congr 2; push_cast; ring
    simp_rw [heq]
    exact ac_n_c_sum_lintegral_subset_le ha idx
      (fun j hj => hxb j ((hmemIdx j).mp hj).1 ((hmemIdx j).mp hj).2)
  have hYsum1 : ∀ j : ℤ, ∑ k ∈ idx, ∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
      ‖partialY f (((x₀ + s + j * a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2 ≤ Gfull j := by
    intro j
    have heq : ∀ y : ℝ, ‖partialY f (((x₀ + s + j * a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2 =
        ‖partialY f (((s + (x₀ + (j:ℝ) * a) : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2 := by
      intro y; congr 2; ring
    simp_rw [heq]
    exact ac_n_c_sum_lintegral_subset_le ha idx
      (fun k hk => hyb k ((hmemIdx k).mp hk).1 ((hmemIdx k).mp hk).2)
  have hYsum2 : ∀ j : ℤ, ∑ k ∈ idx, ∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
      ‖partialY f (((x₀ + s + j * a + a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2 ≤ Gfull (j + 1) := by
    intro j
    have heq : ∀ y : ℝ, ‖partialY f (((x₀ + s + j * a + a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2 =
        ‖partialY f (((s + (x₀ + ((j + 1 : ℤ):ℝ) * a) : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2 := by
      intro y; congr 2; push_cast; ring
    simp_rw [heq]
    exact ac_n_c_sum_lintegral_subset_le ha idx
      (fun k hk => hyb k ((hmemIdx k).mp hk).1 ((hmemIdx k).mp hk).2)
  have hXbound1 : ∑ k ∈ idx, Ffull k ≤ ∑ m ∈ fullIdx, Ffull m :=
    Finset.sum_le_sum_of_subset hidx_sub_full
  have hXbound2 : ∑ k ∈ idx, Ffull (k + 1) ≤ ∑ m ∈ fullIdx, Ffull m :=
    ac_n_c_grid_sum_le_full hidx_def (Or.inr rfl)
  have hYbound1 : ∑ j ∈ idx, Gfull j ≤ ∑ m ∈ fullIdx, Gfull m :=
    Finset.sum_le_sum_of_subset hidx_sub_full
  have hYbound2 : ∑ j ∈ idx, Gfull (j + 1) ≤ ∑ m ∈ fullIdx, Gfull m :=
    ac_n_c_grid_sum_le_full hidx_def (Or.inr rfl)
  have hHfull : (∑ m ∈ fullIdx, Ffull m) * ENNReal.ofReal a ≤
      ∫⁻ z in closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a), ‖partialX f z‖ₑ ^ 2 := htbound
  have hGfull : (∑ m ∈ fullIdx, Gfull m) * ENNReal.ofReal a ≤
      ∫⁻ z in closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a), ‖partialY f z‖ₑ ^ 2 := hsbound
  have hquad : ∑ j ∈ idx, ∑ k ∈ idx,
      ((∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
          ‖partialX f ((x:ℂ) + ((y₀ + t + k * a : ℝ):ℂ) * I)‖ₑ ^ 2) +
       (∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
          ‖partialX f ((x:ℂ) + ((y₀ + t + k * a + a : ℝ):ℂ) * I)‖ₑ ^ 2) +
       (∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
          ‖partialY f (((x₀ + s + j * a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2) +
       (∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
          ‖partialY f (((x₀ + s + j * a + a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2)) ≤
      2 * (∑ m ∈ fullIdx, Ffull m) + 2 * (∑ m ∈ fullIdx, Gfull m) := by
    simp_rw [Finset.sum_add_distrib]
    have e1 : ∑ j ∈ idx, ∑ k ∈ idx, ∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
        ‖partialX f ((x:ℂ) + ((y₀ + t + k * a : ℝ):ℂ) * I)‖ₑ ^ 2 ≤ ∑ m ∈ fullIdx, Ffull m := by
      calc ∑ j ∈ idx, ∑ k ∈ idx, ∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
              ‖partialX f ((x:ℂ) + ((y₀ + t + k * a : ℝ):ℂ) * I)‖ₑ ^ 2
          = ∑ k ∈ idx, ∑ j ∈ idx, ∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
              ‖partialX f ((x:ℂ) + ((y₀ + t + k * a : ℝ):ℂ) * I)‖ₑ ^ 2 := Finset.sum_comm
        _ ≤ ∑ k ∈ idx, Ffull k := Finset.sum_le_sum (fun k _ => hXsum1 k)
        _ ≤ ∑ m ∈ fullIdx, Ffull m := hXbound1
    have e2 : ∑ j ∈ idx, ∑ k ∈ idx, ∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
        ‖partialX f ((x:ℂ) + ((y₀ + t + k * a + a : ℝ):ℂ) * I)‖ₑ ^ 2 ≤ ∑ m ∈ fullIdx, Ffull m := by
      calc ∑ j ∈ idx, ∑ k ∈ idx, ∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
              ‖partialX f ((x:ℂ) + ((y₀ + t + k * a + a : ℝ):ℂ) * I)‖ₑ ^ 2
          = ∑ k ∈ idx, ∑ j ∈ idx, ∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
              ‖partialX f ((x:ℂ) + ((y₀ + t + k * a + a : ℝ):ℂ) * I)‖ₑ ^ 2 := Finset.sum_comm
        _ ≤ ∑ k ∈ idx, Ffull (k + 1) := Finset.sum_le_sum (fun k _ => hXsum2 k)
        _ ≤ ∑ m ∈ fullIdx, Ffull m := hXbound2
    have e3 : ∑ j ∈ idx, ∑ k ∈ idx, ∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
        ‖partialY f (((x₀ + s + j * a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2 ≤ ∑ m ∈ fullIdx, Gfull m :=
      (Finset.sum_le_sum (fun j _ => hYsum1 j)).trans hYbound1
    have e4 : ∑ j ∈ idx, ∑ k ∈ idx, ∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
        ‖partialY f (((x₀ + s + j * a + a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2 ≤ ∑ m ∈ fullIdx, Gfull m :=
      (Finset.sum_le_sum (fun j _ => hYsum2 j)).trans hYbound2
    calc (∑ j ∈ idx, ∑ k ∈ idx, ∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
            ‖partialX f ((x:ℂ) + ((y₀ + t + k * a : ℝ):ℂ) * I)‖ₑ ^ 2) +
        (∑ j ∈ idx, ∑ k ∈ idx, ∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
            ‖partialX f ((x:ℂ) + ((y₀ + t + k * a + a : ℝ):ℂ) * I)‖ₑ ^ 2) +
        (∑ j ∈ idx, ∑ k ∈ idx, ∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
            ‖partialY f (((x₀ + s + j * a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2) +
        (∑ j ∈ idx, ∑ k ∈ idx, ∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
            ‖partialY f (((x₀ + s + j * a + a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2)
        ≤ (∑ m ∈ fullIdx, Ffull m) + (∑ m ∈ fullIdx, Ffull m) + (∑ m ∈ fullIdx, Gfull m) +
            (∑ m ∈ fullIdx, Gfull m) := by gcongr
      _ = 2 * (∑ m ∈ fullIdx, Ffull m) + 2 * (∑ m ∈ fullIdx, Gfull m) := by ring
  set RX : ℝ≥0∞ := ∫⁻ z in closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a),
    ‖partialX f z‖ₑ ^ 2 with hRX_def
  set RY : ℝ≥0∞ := ∫⁻ z in closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a),
    ‖partialY f z‖ₑ ^ 2 with hRY_def
  set SF : ℝ≥0∞ := ∑ m ∈ fullIdx, Ffull m with hSF_def
  set SG : ℝ≥0∞ := ∑ m ∈ fullIdx, Gfull m with hSG_def
  have hpull : ∑ j ∈ idx, ∑ k ∈ idx, ENNReal.ofReal (π * a) *
      ((∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
          ‖partialX f ((x:ℂ) + ((y₀ + t + k * a : ℝ):ℂ) * I)‖ₑ ^ 2) +
       (∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
          ‖partialX f ((x:ℂ) + ((y₀ + t + k * a + a : ℝ):ℂ) * I)‖ₑ ^ 2) +
       (∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
          ‖partialY f (((x₀ + s + j * a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2) +
       (∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
          ‖partialY f (((x₀ + s + j * a + a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2)) =
    ENNReal.ofReal (π * a) * (∑ j ∈ idx, ∑ k ∈ idx,
      ((∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
          ‖partialX f ((x:ℂ) + ((y₀ + t + k * a : ℝ):ℂ) * I)‖ₑ ^ 2) +
       (∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
          ‖partialX f ((x:ℂ) + ((y₀ + t + k * a + a : ℝ):ℂ) * I)‖ₑ ^ 2) +
       (∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
          ‖partialY f (((x₀ + s + j * a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2) +
       (∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
          ‖partialY f (((x₀ + s + j * a + a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2))) := by
    simp_rw [← Finset.mul_sum]
  have hAEmX : AEMeasurable (fun z => ‖partialX f z‖ₑ ^ 2)
      (volume.restrict (closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a))) :=
    ac_n_c_aemeasurable_partialX_sq hxlt.le hylt.le (hcont.mono hQ)
  have hsplitInt : RX + RY = ∫⁻ z in closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a),
      (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := by
    rw [hRX_def, hRY_def]
    exact (lintegral_add_left' hAEmX _).symm
  calc volume (f '' closedRect x₀ (x₀ + L) y₀ (y₀ + L))
      ≤ ∑ j ∈ idx, ∑ k ∈ idx, ENNReal.ofReal (π * a) *
          ((∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
              ‖partialX f ((x:ℂ) + ((y₀ + t + k * a : ℝ):ℂ) * I)‖ₑ ^ 2) +
           (∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
              ‖partialX f ((x:ℂ) + ((y₀ + t + k * a + a : ℝ):ℂ) * I)‖ₑ ^ 2) +
           (∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
              ‖partialY f (((x₀ + s + j * a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2) +
           (∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
              ‖partialY f (((x₀ + s + j * a + a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2)) := hvol_cover2
    _ = ENNReal.ofReal (π * a) * (∑ j ∈ idx, ∑ k ∈ idx,
          ((∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
              ‖partialX f ((x:ℂ) + ((y₀ + t + k * a : ℝ):ℂ) * I)‖ₑ ^ 2) +
           (∫⁻ x in Ioo (x₀ + s + j * a) (x₀ + s + j * a + a),
              ‖partialX f ((x:ℂ) + ((y₀ + t + k * a + a : ℝ):ℂ) * I)‖ₑ ^ 2) +
           (∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
              ‖partialY f (((x₀ + s + j * a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2) +
           (∫⁻ y in Ioo (y₀ + t + k * a) (y₀ + t + k * a + a),
              ‖partialY f (((x₀ + s + j * a + a : ℝ):ℂ) + (y:ℂ) * I)‖ₑ ^ 2))) := hpull
    _ ≤ ENNReal.ofReal (π * a) * (2 * SF + 2 * SG) := by gcongr
    _ = 2 * ENNReal.ofReal π * (SF * ENNReal.ofReal a + SG * ENNReal.ofReal a) := by
        rw [ENNReal.ofReal_mul Real.pi_pos.le]; ring
    _ ≤ 2 * ENNReal.ofReal π * (RX + RY) := by
        gcongr
    _ = ENNReal.ofReal (2 * π) * ∫⁻ z in closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a),
          (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := by
        have h2 : ENNReal.ofReal (2 * π) = 2 * ENNReal.ofReal π := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num
        rw [h2, hsplitInt]
    _ ≤ ENNReal.ofReal (4 * π) * ∫⁻ z in closedRect (x₀ - a) (x₀ + L + a) (y₀ - a) (y₀ + L + a),
          (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := by
        gcongr
        norm_num




/-- A rational-cornered closed square `R₀` around `z` with a margin-`s` enlargement `R₁ ⊆ D`. -/
theorem ac_n_b_exists_rat_square {D : Set ℂ} (hD : IsOpen D) {z : ℂ} (hz : z ∈ D) :
    ∃ p q s : ℚ, 0 < s ∧ z ∈ openRect ((p : ℝ) - s) ((p : ℝ) + s) ((q : ℝ) - s) ((q : ℝ) + s) ∧
      closedRect ((p : ℝ) - 2 * s) ((p : ℝ) + 2 * s) ((q : ℝ) - 2 * s) ((q : ℝ) + 2 * s) ⊆ D := by
  obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.1 hD z hz
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 10 by linarith)
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show z.re - (s : ℝ) / 2 < z.re + (s : ℝ) / 2 by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show z.im - (s : ℝ) / 2 < z.im + (s : ℝ) / 2 by linarith)
  refine ⟨p, q, s, by exact_mod_cast hs1, ⟨by linarith, by linarith, by linarith, by linarith⟩,
    fun w hw => ?_⟩
  apply hball
  rw [mem_ball, Complex.dist_eq]
  have h1 : |(w - z).re| < 5 * (s : ℝ) / 2 := by
    rw [Complex.sub_re, abs_lt]
    exact ⟨by linarith [hw.1], by linarith [hw.2.1]⟩
  have h2 : |(w - z).im| < 5 * (s : ℝ) / 2 := by
    rw [Complex.sub_im, abs_lt]
    exact ⟨by linarith [hw.2.2.1], by linarith [hw.2.2.2]⟩
  have h3 := Complex.norm_le_abs_re_add_abs_im (w - z)
  linarith

/-- **N3 (Lusin's property (N))**, for a homeomorphism of an open set that is A.C.L. with locally
`L²` partial derivatives (generalized from `K`-q.c. maps on 2026-09-22 for Lemma 13.1: the q.c.
hypothesis entered only through Theorems 9.1 and 9.5).  See `ac_n_volume_image_null_of_isKQC`. -/
theorem ac_n_volume_image_null {f : ℂ → ℂ} {D : Set ℂ} (hDopen : IsOpen D) (hacl : IsACL f D)
    (hfi : InjOn f D) (hcontinv : ContinuousOn (Function.invFunOn f D) (f '' D))
    (hL2 : ∀ C ⊆ D, IsCompact C →
      MemLp (partialX f) 2 (volume.restrict C) ∧ MemLp (partialY f) 2 (volume.restrict C))
    {E : Set ℂ} (hED : E ⊆ D) (hE : volume E = 0) : volume (f '' E) = 0 := by
  have hfc : ContinuousOn f D := hacl.1
  -- (Level 2, per (p,q,s)): volume (f '' (E ∩ R₀)) = 0 for a fixed rational square R₀ with
  -- margin-`s` enlargement `R₁ ⊆ D`.
  have hlocal : ∀ p q s : ℚ, 0 < s →
      closedRect ((p : ℝ) - 2 * s) ((p : ℝ) + 2 * s) ((q : ℝ) - 2 * s) ((q : ℝ) + 2 * s) ⊆ D →
      volume (f '' (E ∩ closedRect ((p : ℝ) - s) ((p : ℝ) + s) ((q : ℝ) - s) ((q : ℝ) + s))) = 0 := by
    intro p q s hspos hsub
    set R0 : Set ℂ := closedRect ((p : ℝ) - s) ((p : ℝ) + s) ((q : ℝ) - s) ((q : ℝ) + s) with hR0def
    set R1 : Set ℂ := closedRect ((p : ℝ) - 2 * s) ((p : ℝ) + 2 * s) ((q : ℝ) - 2 * s)
      ((q : ℝ) + 2 * s) with hR1def
    have hsposR : (0:ℝ) < (s:ℝ) := by exact_mod_cast hspos
    have hR0R1sub : R0 ⊆ R1 := by
      intro w hw
      exact ⟨by linarith [hw.1], by linarith [hw.2.1], by linarith [hw.2.2.1],
        by linarith [hw.2.2.2]⟩
    have hR0D : R0 ⊆ D := hR0R1sub.trans hsub
    have hR1compact : IsCompact R1 := acl_isCompact_closedRect _ _ _ _
    have hR0compact : IsCompact R0 := acl_isCompact_closedRect _ _ _ _
    -- Step A: `g := |∂x f|² + |∂y f|²` is integrable on `R1`.
    obtain ⟨hgx, hgy⟩ := hL2 R1 hsub hR1compact
    have hg2 : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ (2 : ℕ) := fun x => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
    have hgxfin : (∫⁻ z in R1, ‖partialX f z‖ₑ ^ 2) < ⊤ := by
      have h1 := hgx.eLpNorm_lt_top
      rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
        hgx.aestronglyMeasurable] at h1
      simpa [hg2] using h1
    have hgyfin : (∫⁻ z in R1, ‖partialY f z‖ₑ ^ 2) < ⊤ := by
      have h1 := hgy.eLpNorm_lt_top
      rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
        hgy.aestronglyMeasurable] at h1
      simpa [hg2] using h1
    have hgxmeas : AEMeasurable (fun z => ‖partialX f z‖ₑ ^ 2) (volume.restrict R1) :=
      hgx.aestronglyMeasurable.aemeasurable.enorm.pow_const 2
    have hgtot : (∫⁻ z in R1, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2)) < ⊤ := by
      rw [lintegral_add_left' hgxmeas]
      exact ENNReal.add_lt_top.2 ⟨hgxfin, hgyfin⟩
    -- Step B: `f` restricted to `D` is an open embedding, so it sends Borel sets to Borel sets.
    have hVopenmap : ∀ V : Set ℂ, IsOpen V → V ⊆ D → IsOpen (f '' V) := fun V hV hVD =>
      isOpen_image_of_continuousOn_injOn hV (hfc.mono hVD) (hfi.mono hVD)
    have hvalOpenMap : IsOpenMap (Subtype.val : D → ℂ) := hDopen.isOpenMap_subtype_val
    have hrestrictOpenMap : IsOpenMap (D.domRestrict f) := by
      intro u hu
      have h1 : IsOpen (Subtype.val '' u) := hvalOpenMap u hu
      have h2 : Subtype.val '' u ⊆ D := by rintro w ⟨x, -, rfl⟩; exact x.2
      have h3 : IsOpen (f '' (Subtype.val '' u)) := hVopenmap _ h1 h2
      rwa [Set.domRestrict_eq, Set.image_comp]
    have hOpenEmb : IsOpenEmbedding (D.domRestrict f) :=
      IsOpenEmbedding.of_continuous_injective_isOpenMap hfc.domRestrict hfi.injective
        hrestrictOpenMap
    have hMeasEmb : MeasurableEmbedding (D.domRestrict f) := hOpenEmb.measurableEmbedding
    have hfimg_meas : ∀ u : Set D, MeasurableSet u → MeasurableSet (f '' (Subtype.val '' u)) := by
      intro u hu
      rw [← Set.image_comp]
      exact hMeasEmb.measurableSet_image.2 hu
    -- `G ⊇ E ∩ R0` a Borel null superset; `f '' (G ∩ R0)` is Borel and has finite volume.
    have hS0 : volume (E ∩ R0) = 0 := measure_mono_null Set.inter_subset_left hE
    obtain ⟨G, hSG, hGmeas, hG0⟩ := exists_measurable_superset_of_null hS0
    have hGR0meas : MeasurableSet (G ∩ R0) := hGmeas.inter hR0compact.measurableSet
    have hGR0subD : G ∩ R0 ⊆ D := fun w hw => hR0D hw.2
    set u0 : Set D := Subtype.val ⁻¹' (G ∩ R0) with hu0def
    have hu0meas : MeasurableSet u0 := hGR0meas.preimage measurable_subtype_coe
    have hu0img : Subtype.val '' u0 = G ∩ R0 := by
      rw [hu0def, Set.image_preimage_eq_iff, Subtype.range_val]
      exact hGR0subD
    have hfGR0meas : MeasurableSet (f '' (G ∩ R0)) := by
      rw [← hu0img]; exact hfimg_meas u0 hu0meas
    have hfR0compact : IsCompact (f '' R0) := hR0compact.image_of_continuousOn (hfc.mono hR0D)
    have hfR0finite : volume (f '' R0) < ⊤ := hfR0compact.measure_lt_top
    have hfGR0sub : f '' (G ∩ R0) ⊆ f '' R0 := Set.image_mono Set.inter_subset_right
    have hfGR0ne_top : volume (f '' (G ∩ R0)) ≠ ⊤ :=
      (lt_of_le_of_lt (measure_mono hfGR0sub) hfR0finite).ne
    -- It suffices to bound `volume (f '' (G ∩ R0))` by `36 π ε` for every `ε > 0`.
    have hmain : ∀ ε : ℝ, 0 < ε → volume (f '' (G ∩ R0)) ≤ ENNReal.ofReal (36 * π * ε) := by
      intro ε hε
      rw [hfGR0meas.measure_eq_iSup_isCompact_of_ne_top hfGR0ne_top]
      refine iSup_le fun C => iSup_le fun hCsub => iSup_le fun hCcompact => ?_
      rcases C.eq_empty_or_nonempty with hCempty | hCnonempty
      · simp [hCempty]
      have hCsubfD : C ⊆ f '' D := hCsub.trans (hfGR0sub.trans (Set.image_mono hR0D))
      set C' : Set ℂ := Function.invFunOn f D '' C with hC'def
      have hC'compact : IsCompact C' := hCcompact.image_of_continuousOn (hcontinv.mono hCsubfD)
      have hfinvFun : ∀ x ∈ C, f (Function.invFunOn f D x) = x := by
        intro x hx
        obtain ⟨a', ha', rfl⟩ := hCsubfD hx
        rw [hfi.leftInvOn_invFunOn ha']
      have hfC'eqC : f '' C' = C := by
        rw [hC'def, ← Set.image_comp]
        apply Set.eq_of_subset_of_subset
        · rintro x ⟨x', hx', rfl⟩
          show f (Function.invFunOn f D x') ∈ C
          rw [hfinvFun x' hx']; exact hx'
        · intro x hx
          exact ⟨x, hx, hfinvFun x hx⟩
      have hC'sub : C' ⊆ G ∩ R0 := by
        rintro x' ⟨x, hx, rfl⟩
        obtain ⟨w, hw, hwx⟩ := hCsub hx
        have hwD : w ∈ D := hGR0subD hw
        have heq : Function.invFunOn f D (f w) = w := hfi.leftInvOn_invFunOn hwD
        rw [hwx] at heq
        rwa [heq]
      have hC'null : volume C' = 0 := measure_mono_null (hC'sub.trans Set.inter_subset_left) hG0
      have hR0subintR1 : R0 ⊆ interior R1 := by
        rw [hR1def, menchoff_interior_closedRect]
        intro w hw
        exact ⟨by linarith [hw.1], by linarith [hw.2.1], by linarith [hw.2.2.1],
          by linarith [hw.2.2.2]⟩
      have hC'subintR1 : C' ⊆ interior R1 :=
        (hC'sub.trans Set.inter_subset_right).trans hR0subintR1
      obtain ⟨δ, hδpos, hδspec⟩ := exists_pos_setLIntegral_lt_of_measure_lt
        (μ := volume.restrict R1) hgtot.ne (ENNReal.ofReal_pos.2 hε).ne'
      have hC'ltδ : volume C' < δ := hC'null ▸ hδpos
      obtain ⟨U, hC'U, hUopen, hUltδ⟩ := Set.exists_isOpen_lt_of_lt C' δ hC'ltδ
      set U' : Set ℂ := U ∩ interior R1 with hU'def
      have hC'U' : C' ⊆ U' := Set.subset_inter hC'U hC'subintR1
      have hU'open : IsOpen U' := hUopen.inter isOpen_interior
      have hU'ltδ : volume U' < δ := lt_of_le_of_lt (measure_mono Set.inter_subset_left) hUltδ
      have hU'subR1 : U' ⊆ R1 := Set.inter_subset_right.trans interior_subset
      have hU'intg : (∫⁻ z in U', (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2)) <
          ENNReal.ofReal ε := by
        have hmeasU'R1 : (volume.restrict R1) U' < δ := by
          rw [Measure.restrict_apply' hR1compact.measurableSet,
            Set.inter_eq_self_of_subset_left hU'subR1]
          exact hU'ltδ
        have h1 := hδspec U' hmeasU'R1
        rwa [Measure.restrict_restrict hU'open.measurableSet,
          Set.inter_eq_self_of_subset_left hU'subR1] at h1
      obtain ⟨η, hηpos, hthick⟩ := hC'compact.exists_thickening_subset_open hU'open hC'U'
      set a : ℝ := η / 8 with hadef
      have hapos : 0 < a := by rw [hadef]; linarith
      -- grid cells anchored at the origin, mesh `a`.
      set closedCell : ℤ → ℤ → Set ℂ := fun j k =>
        closedRect ((j:ℝ) * a) (((j:ℝ) + 1) * a) ((k:ℝ) * a) (((k:ℝ) + 1) * a) with hclosedCelldef
      set openCell : ℤ → ℤ → Set ℂ := fun j k =>
        openRect ((j:ℝ) * a) (((j:ℝ) + 1) * a) ((k:ℝ) * a) (((k:ℝ) + 1) * a) with hopenCelldef
      set enlarged : ℤ → ℤ → Set ℂ := fun j k =>
        closedRect (((j:ℝ) - 1) * a) (((j:ℝ) + 2) * a) (((k:ℝ) - 1) * a) (((k:ℝ) + 2) * a)
        with henlargeddef
      -- integer index bounds from boundedness of `C'`.
      have hC'ne : C'.Nonempty := hCnonempty.image _
      obtain ⟨c0, hc0, hc0max⟩ :=
        hC'compact.exists_isMaxOn hC'ne (continuous_norm.continuousOn (s := C'))
      set M : ℝ := ‖c0‖ with hMdef
      have hMbound : ∀ z ∈ C', ‖z‖ ≤ M := hc0max
      obtain ⟨N, hN⟩ := exists_nat_gt (M / a)
      have hNa : M < (N : ℝ) * a := by
        rw [div_lt_iff₀ hapos] at hN; linarith
      have h1dbound : ∀ x : ℝ, |x| ≤ M → -(N : ℤ) ≤ ⌊x / a⌋ ∧ ⌊x / a⌋ ≤ (N : ℤ) := by
        intro x hx
        rw [abs_le] at hx
        have hfl1 : (⌊x / a⌋ : ℝ) * a ≤ x := by
          have h := Int.floor_le (x / a)
          calc (⌊x / a⌋ : ℝ) * a ≤ (x / a) * a := mul_le_mul_of_nonneg_right h hapos.le
            _ = x := by field_simp
        have hfl2 : x < ((⌊x / a⌋ : ℝ) + 1) * a := by
          have h := Int.lt_floor_add_one (x / a)
          calc x = (x / a) * a := by field_simp
            _ < ((⌊x / a⌋ : ℝ) + 1) * a := mul_lt_mul_of_pos_right h hapos
        constructor
        · have hstep : (-(N : ℝ)) * a < ((⌊x / a⌋ : ℝ) + 1) * a := by
            linarith [hx.1, hfl2, hNa]
          have hstep2 : -(N : ℝ) < (⌊x / a⌋ : ℝ) + 1 := lt_of_mul_lt_mul_right hstep hapos.le
          have hstep3 : ((-(N : ℤ) : ℤ) : ℝ) < (⌊x / a⌋ : ℝ) + 1 := by push_cast; linarith
          have hstep4 : -(N : ℤ) < ⌊x / a⌋ + 1 := by exact_mod_cast hstep3
          omega
        · have hstep : (⌊x / a⌋ : ℝ) * a < (N : ℝ) * a := by linarith [hx.2, hfl1, hNa]
          have hstep2 : (⌊x / a⌋ : ℝ) < (N : ℝ) := lt_of_mul_lt_mul_right hstep hapos.le
          have hstep3 : (⌊x / a⌋ : ℤ) < (N : ℤ) := by exact_mod_cast hstep2
          omega
      have h2dcell : ∀ z ∈ C', ∃ j k : ℤ, j ∈ Finset.Icc (-(N : ℤ)) N ∧
          k ∈ Finset.Icc (-(N : ℤ)) N ∧ z ∈ closedCell j k := by
        intro z hz
        have hzM := hMbound z hz
        have hre : |z.re| ≤ M := (Complex.abs_re_le_norm z).trans hzM
        have him : |z.im| ≤ M := (Complex.abs_im_le_norm z).trans hzM
        obtain ⟨hj1, hj2⟩ := h1dbound z.re hre
        obtain ⟨hk1, hk2⟩ := h1dbound z.im him
        refine ⟨⌊z.re / a⌋, ⌊z.im / a⌋, Finset.mem_Icc.2 ⟨hj1, hj2⟩,
          Finset.mem_Icc.2 ⟨hk1, hk2⟩, ?_, ?_, ?_, ?_⟩
        · have := Int.floor_le (z.re / a)
          calc (⌊z.re / a⌋ : ℝ) * a ≤ (z.re / a) * a := mul_le_mul_of_nonneg_right this hapos.le
            _ = z.re := by field_simp
        · have := Int.lt_floor_add_one (z.re / a)
          calc z.re = (z.re / a) * a := by field_simp
            _ ≤ ((⌊z.re / a⌋ : ℝ) + 1) * a :=
              (mul_lt_mul_of_pos_right this hapos).le
        · have := Int.floor_le (z.im / a)
          calc (⌊z.im / a⌋ : ℝ) * a ≤ (z.im / a) * a := mul_le_mul_of_nonneg_right this hapos.le
            _ = z.im := by field_simp
        · have := Int.lt_floor_add_one (z.im / a)
          calc z.im = (z.im / a) * a := by field_simp
            _ ≤ ((⌊z.im / a⌋ : ℝ) + 1) * a :=
              (mul_lt_mul_of_pos_right this hapos).le
      classical
      set gridFin : Finset (ℤ × ℤ) := Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N
        with hgridFindef
      set hitting : Finset (ℤ × ℤ) := gridFin.filter (fun jk => (closedCell jk.1 jk.2 ∩ C').Nonempty)
        with hhittingdef
      have hcover : C' ⊆ ⋃ jk ∈ hitting, closedCell jk.1 jk.2 := by
        intro z hz
        obtain ⟨j, k, hj, hk, hmem⟩ := h2dcell z hz
        have hjk : (j, k) ∈ hitting := by
          rw [hhittingdef, Finset.mem_filter]
          exact ⟨Finset.mem_product.2 ⟨hj, hk⟩, z, hmem, hz⟩
        exact Set.mem_biUnion hjk hmem
      -- distinct grid cells: pairwise disjoint (via their open interiors), null boundary.
      have hcellij : ∀ j k : ℤ, closedCell j k = closedRect ((j:ℝ)*a) (((j:ℝ)+1)*a) ((k:ℝ)*a)
          (((k:ℝ)+1)*a) := fun j k => by rw [hclosedCelldef]
      have hcellopenij : ∀ j k : ℤ, openCell j k = openRect ((j:ℝ)*a) (((j:ℝ)+1)*a) ((k:ℝ)*a)
          (((k:ℝ)+1)*a) := fun j k => by rw [hopenCelldef]
      have hopensub : ∀ j k : ℤ, openCell j k ⊆ closedCell j k := by
        intro j k
        rw [hcellij, hcellopenij]
        exact acl_openRect_subset_closedRect le_rfl le_rfl le_rfl le_rfl
      have hcelldiffnull : ∀ j k : ℤ, volume (closedCell j k \ openCell j k) = 0 := by
        intro j k
        rw [hcellij, hcellopenij]
        exact menchoff_volume_closedRect_diff_openRect _ _ _ _
      have hcell_int_eq : ∀ j k : ℤ,
          (∫⁻ z in closedCell j k, (‖partialX f z‖ₑ^2 + ‖partialY f z‖ₑ^2)) =
            ∫⁻ z in openCell j k, (‖partialX f z‖ₑ^2 + ‖partialY f z‖ₑ^2) := by
        intro j k
        apply setLIntegral_congr
        rw [ae_eq_set]
        exact ⟨hcelldiffnull j k,
          by rw [Set.diff_eq_empty.2 (hopensub j k), measure_empty]⟩
      have hopendisj : ∀ j k j' k' : ℤ, (j, k) ≠ (j', k') →
          Disjoint (openCell j k) (openCell j' k') := by
        intro j k j' k' hne
        rw [hcellopenij, hcellopenij, Set.disjoint_left]
        intro w hw hw'
        unfold openRect at hw hw'
        rw [Set.mem_setOf_eq] at hw hw'
        have hor : j ≠ j' ∨ k ≠ k' := by
          by_contra hcon
          push Not at hcon
          exact hne (Prod.ext hcon.1 hcon.2)
        rcases hor with hj | hk
        · rcases lt_or_gt_of_ne hj with h | h
          · have hcast : ((j:ℝ)+1) ≤ (j':ℝ) := by exact_mod_cast h
            have hmul : ((j:ℝ)+1)*a ≤ (j':ℝ)*a := mul_le_mul_of_nonneg_right hcast hapos.le
            linarith [hw.2.1, hw'.1]
          · have hcast : ((j':ℝ)+1) ≤ (j:ℝ) := by exact_mod_cast h
            have hmul : ((j':ℝ)+1)*a ≤ (j:ℝ)*a := mul_le_mul_of_nonneg_right hcast hapos.le
            linarith [hw'.2.1, hw.1]
        · rcases lt_or_gt_of_ne hk with h | h
          · have hcast : ((k:ℝ)+1) ≤ (k':ℝ) := by exact_mod_cast h
            have hmul : ((k:ℝ)+1)*a ≤ (k':ℝ)*a := mul_le_mul_of_nonneg_right hcast hapos.le
            linarith [hw.2.2.2, hw'.2.2.1]
          · have hcast : ((k':ℝ)+1) ≤ (k:ℝ) := by exact_mod_cast h
            have hmul : ((k':ℝ)+1)*a ≤ (k:ℝ)*a := mul_le_mul_of_nonneg_right hcast hapos.le
            linarith [hw'.2.2.2, hw.2.2.1]
      have hunion_null : ∀ S : Finset (ℤ × ℤ),
          volume (⋃ jk ∈ S, (closedCell jk.1 jk.2 \ openCell jk.1 jk.2)) = 0 := by
        intro S
        have hle : volume (⋃ jk ∈ S, (closedCell jk.1 jk.2 \ openCell jk.1 jk.2)) ≤
            ∑ jk ∈ S, volume (closedCell jk.1 jk.2 \ openCell jk.1 jk.2) :=
          measure_biUnion_finset_le _ _
        have hz : ∑ jk ∈ S, volume (closedCell jk.1 jk.2 \ openCell jk.1 jk.2) = 0 :=
          Finset.sum_eq_zero (fun jk _ => hcelldiffnull jk.1 jk.2)
        rw [hz] at hle
        exact le_antisymm hle bot_le
      have hunion_ae_eq : ∀ S : Finset (ℤ × ℤ), (⋃ jk ∈ S, closedCell jk.1 jk.2) =ᵐ[volume]
          (⋃ jk ∈ S, openCell jk.1 jk.2) := by
        intro S
        rw [ae_eq_set]
        refine ⟨?_, ?_⟩
        · have hle : volume ((⋃ jk ∈ S, closedCell jk.1 jk.2) \ (⋃ jk ∈ S, openCell jk.1 jk.2)) ≤
              volume (⋃ jk ∈ S, (closedCell jk.1 jk.2 \ openCell jk.1 jk.2)) := by
            apply measure_mono
            rintro w ⟨hw1, hw2⟩
            rw [Set.mem_iUnion₂] at hw1 ⊢
            obtain ⟨jk, hjk, hwjk⟩ := hw1
            exact ⟨jk, hjk, hwjk, fun hcon => hw2 (Set.mem_biUnion hjk hcon)⟩
          rw [hunion_null S] at hle
          exact le_antisymm hle bot_le
        · have hsubset : (⋃ jk ∈ S, openCell jk.1 jk.2) ⊆ ⋃ jk ∈ S, closedCell jk.1 jk.2 := by
            intro w hw
            rw [Set.mem_iUnion₂] at hw ⊢
            obtain ⟨jk, hjk, hwjk⟩ := hw
            exact ⟨jk, hjk, hopensub jk.1 jk.2 hwjk⟩
          rw [Set.diff_eq_empty.2 hsubset, measure_empty]
      have hdisjoint_sum_eq : ∀ S : Finset (ℤ × ℤ),
          ∑ jk ∈ S, ∫⁻ z in closedCell jk.1 jk.2, (‖partialX f z‖ₑ^2 + ‖partialY f z‖ₑ^2) =
            ∫⁻ z in ⋃ jk ∈ S, closedCell jk.1 jk.2, (‖partialX f z‖ₑ^2 + ‖partialY f z‖ₑ^2) := by
        intro S
        rw [setLIntegral_congr (μ := volume)
          (f := fun z => ‖partialX f z‖ₑ^2 + ‖partialY f z‖ₑ^2) (hunion_ae_eq S)]
        have hpd : Set.PairwiseDisjoint (S : Set (ℤ × ℤ)) (fun jk => openCell jk.1 jk.2) := by
          intro jk _ jk' _ hne
          exact hopendisj jk.1 jk.2 jk'.1 jk'.2 (fun h => hne (Prod.ext (congrArg Prod.fst h)
            (congrArg Prod.snd h)))
        have hmeasO : ∀ jk ∈ S, MeasurableSet (openCell jk.1 jk.2) := fun jk _ => by
          rw [hcellopenij]; exact (acl_isOpen_openRect _ _ _ _).measurableSet
        rw [Finset.sum_congr rfl (fun jk _ => hcell_int_eq jk.1 jk.2),
          ← lintegral_biUnion_finset hpd hmeasO]
      -- the enlargement of a hitting cell lies in the thickening of `C'`, hence in `D`.
      have hrect_eq : ∀ a1 b1 c1 d1 a2 b2 c2 d2 : ℝ, a1 = a2 → b1 = b2 → c1 = c2 → d1 = d2 →
          closedRect a1 b1 c1 d1 = closedRect a2 b2 c2 d2 := by
        intro a1 b1 c1 d1 a2 b2 c2 d2 h1 h2 h3 h4; rw [h1, h2, h3, h4]
      have henlarged_thick : ∀ jk ∈ hitting, enlarged jk.1 jk.2 ⊆ thickening η C' := by
        rintro ⟨j, k⟩ hjk
        have hne : (closedCell j k ∩ C').Nonempty := by
          have hmem := hjk
          rw [hhittingdef, Finset.mem_filter] at hmem
          exact hmem.2
        obtain ⟨c, hcCell, hcC'⟩ := hne
        have hstep : enlarged j k ⊆ ball c η := by
          intro w hw
          rw [henlargeddef] at hw
          rw [hclosedCelldef] at hcCell
          rw [mem_ball, Complex.dist_eq]
          have h1 : |w.re - c.re| ≤ 2 * a := by
            rw [abs_le]
            exact ⟨by linarith [hw.1, hcCell.2.1], by linarith [hw.2.1, hcCell.1]⟩
          have h2 : |w.im - c.im| ≤ 2 * a := by
            rw [abs_le]
            exact ⟨by linarith [hw.2.2.1, hcCell.2.2.2], by linarith [hw.2.2.2, hcCell.2.2.1]⟩
          have h3 := Complex.norm_le_abs_re_add_abs_im (w - c)
          rw [Complex.sub_re, Complex.sub_im] at h3
          have h4 : (4 : ℝ) * a < η := by rw [hadef]; linarith
          linarith
        exact hstep.trans (Metric.ball_subset_thickening hcC' η)
      have henlarged_D : ∀ jk ∈ hitting, enlarged jk.1 jk.2 ⊆ D := fun jk hjk =>
        ((henlarged_thick jk hjk).trans hthick).trans (hU'subR1.trans hsub)
      -- N2 applied to each hitting cell.
      have hN2 : ∀ jk ∈ hitting, volume (f '' closedCell jk.1 jk.2) ≤ ENNReal.ofReal (4 * π) *
          ∫⁻ z in enlarged jk.1 jk.2, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := by
        rintro ⟨j, k⟩ hjk
        have heq2 : closedRect ((j : ℝ) * a - a) ((j : ℝ) * a + a + a) ((k : ℝ) * a - a)
            ((k : ℝ) * a + a + a) = enlarged j k := by
          rw [henlargeddef]
          exact hrect_eq _ _ _ _ _ _ _ _ (by ring) (by ring) (by ring) (by ring)
        have hQarg : closedRect ((j : ℝ) * a - a) ((j : ℝ) * a + a + a) ((k : ℝ) * a - a)
            ((k : ℝ) * a + a + a) ⊆ D := heq2 ▸ henlarged_D ⟨j, k⟩ hjk
        have hkey := ac_n_volume_image_le_lintegral hDopen hacl hfi (x₀ := (j : ℝ) * a)
          (y₀ := (k : ℝ) * a)
          (L := a) (a := a) hapos hapos (n := 1) (by push_cast; ring) hQarg
        have heq1 : closedRect ((j : ℝ) * a) ((j : ℝ) * a + a) ((k : ℝ) * a)
            ((k : ℝ) * a + a) = closedCell j k := by
          rw [hclosedCelldef]
          exact hrect_eq _ _ _ _ _ _ _ _ (by ring) (by ring) (by ring) (by ring)
        rwa [heq1, heq2] at hkey
      -- cover-based bound on `volume C`.
      have hCvolbound : volume C ≤ ∑ jk ∈ hitting, volume (f '' closedCell jk.1 jk.2) := by
        calc volume C = volume (f '' C') := by rw [hfC'eqC]
          _ ≤ volume (f '' ⋃ jk ∈ hitting, closedCell jk.1 jk.2) :=
                measure_mono (Set.image_mono hcover)
          _ = volume (⋃ jk ∈ hitting, f '' closedCell jk.1 jk.2) := by rw [Set.image_iUnion₂]
          _ ≤ ∑ jk ∈ hitting, volume (f '' closedCell jk.1 jk.2) := measure_biUnion_finset_le _ _
      have hCbound2 : volume C ≤ ENNReal.ofReal (4 * π) * ∑ jk ∈ hitting,
          ∫⁻ z in enlarged jk.1 jk.2, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := by
        calc volume C ≤ ∑ jk ∈ hitting, volume (f '' closedCell jk.1 jk.2) := hCvolbound
          _ ≤ ∑ jk ∈ hitting, ENNReal.ofReal (4 * π) *
                ∫⁻ z in enlarged jk.1 jk.2, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) :=
              Finset.sum_le_sum hN2
          _ = ENNReal.ofReal (4 * π) * ∑ jk ∈ hitting,
                ∫⁻ z in enlarged jk.1 jk.2, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := by
              rw [Finset.mul_sum]
      -- the "9×" overcounting bound: enlarged cells are unions of 9 grid neighbours.
      set shifts : Finset (ℤ × ℤ) := Finset.Icc (-1 : ℤ) 1 ×ˢ Finset.Icc (-1 : ℤ) 1
        with hshiftsdef
      have hshiftscard : shifts.card = 9 := by rw [hshiftsdef]; decide
      have hshift_inj : ∀ j k : ℤ, Set.InjOn (fun d : ℤ × ℤ => (j + d.1, k + d.2)) shifts := by
        intro j k d1 _ d2 _ heq
        simp only [Prod.mk.injEq] at heq
        exact Prod.ext (by omega) (by omega)
      have henlarged_sub_union : ∀ j k : ℤ,
          enlarged j k ⊆ ⋃ d ∈ shifts, closedCell (j + d.1) (k + d.2) := by
        intro j k w hw
        rw [henlargeddef] at hw
        obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
        have hd1 : ∃ d1 : ℤ, d1 ∈ Finset.Icc (-1 : ℤ) 1 ∧
            ((j + d1 : ℤ) : ℝ) * a ≤ w.re ∧ w.re ≤ ((j + d1 : ℤ) : ℝ) * a + a := by
          rcases lt_or_ge w.re ((j : ℝ) * a) with h | h
          · exact ⟨-1, Finset.mem_Icc.2 (by omega), by push_cast; linarith,
              by push_cast; linarith⟩
          rcases lt_or_ge w.re (((j : ℝ) + 1) * a) with h2 | h2
          · exact ⟨0, Finset.mem_Icc.2 (by omega), by push_cast; linarith,
              by push_cast; linarith⟩
          · exact ⟨1, Finset.mem_Icc.2 (by omega), by push_cast; linarith,
              by push_cast; linarith⟩
        have hd2 : ∃ d2 : ℤ, d2 ∈ Finset.Icc (-1 : ℤ) 1 ∧
            ((k + d2 : ℤ) : ℝ) * a ≤ w.im ∧ w.im ≤ ((k + d2 : ℤ) : ℝ) * a + a := by
          rcases lt_or_ge w.im ((k : ℝ) * a) with h | h
          · exact ⟨-1, Finset.mem_Icc.2 (by omega), by push_cast; linarith,
              by push_cast; linarith⟩
          rcases lt_or_ge w.im (((k : ℝ) + 1) * a) with h2 | h2
          · exact ⟨0, Finset.mem_Icc.2 (by omega), by push_cast; linarith,
              by push_cast; linarith⟩
          · exact ⟨1, Finset.mem_Icc.2 (by omega), by push_cast; linarith,
              by push_cast; linarith⟩
        obtain ⟨d1, hd1mem, hd1a, hd1b⟩ := hd1
        obtain ⟨d2, hd2mem, hd2a, hd2b⟩ := hd2
        rw [Set.mem_iUnion₂]
        refine ⟨(d1, d2), Finset.mem_product.2 ⟨hd1mem, hd2mem⟩, ?_⟩
        rw [hclosedCelldef]
        exact ⟨hd1a, by push_cast; push_cast at hd1b; linarith, hd2a,
          by push_cast; push_cast at hd2b; linarith⟩
      have h9x_step1 : ∀ jk ∈ hitting,
          (∫⁻ z in enlarged jk.1 jk.2, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2)) ≤
            ∑ d ∈ shifts, ∫⁻ z in closedCell (jk.1 + d.1) (jk.2 + d.2),
              (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := by
        rintro ⟨j, k⟩ hjk
        have himgeq : (⋃ d ∈ shifts, closedCell (j + d.1) (k + d.2)) =
            ⋃ jk' ∈ shifts.image (fun d => (j + d.1, k + d.2)), closedCell jk'.1 jk'.2 := by
          rw [Finset.set_biUnion_finset_image]
        have hreindex : ∑ jk' ∈ shifts.image (fun d => (j + d.1, k + d.2)),
            (∫⁻ z in closedCell jk'.1 jk'.2, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2)) =
              ∑ d ∈ shifts, ∫⁻ z in closedCell (j + d.1) (k + d.2),
                (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) :=
          Finset.sum_image (fun d1 hd1 d2 hd2 h => hshift_inj j k hd1 hd2 h)
        calc (∫⁻ z in enlarged j k, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2)) ≤
              ∫⁻ z in ⋃ d ∈ shifts, closedCell (j + d.1) (k + d.2),
                (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) :=
              lintegral_mono_set (henlarged_sub_union j k)
          _ = ∫⁻ z in ⋃ jk' ∈ shifts.image (fun d => (j + d.1, k + d.2)), closedCell jk'.1 jk'.2,
                (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := by rw [himgeq]
          _ = ∑ jk' ∈ shifts.image (fun d => (j + d.1, k + d.2)),
                ∫⁻ z in closedCell jk'.1 jk'.2, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) :=
              (hdisjoint_sum_eq _).symm
          _ = ∑ d ∈ shifts, ∫⁻ z in closedCell (j + d.1) (k + d.2),
                (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := hreindex
      have hcell_shift_sub_U' : ∀ jk ∈ hitting, ∀ d ∈ shifts,
          closedCell (jk.1 + d.1) (jk.2 + d.2) ⊆ U' := by
        rintro ⟨j, k⟩ hjk d hd
        rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hd
        have hsub1 : closedCell (j + d.1) (k + d.2) ⊆ enlarged j k := by
          intro w hw
          rw [hclosedCelldef] at hw
          rw [henlargeddef]
          refine ⟨?_, ?_, ?_, ?_⟩
          · have hd11 : (-1 : ℝ) ≤ (d.1 : ℝ) := by exact_mod_cast hd.1.1
            have hb : ((j : ℝ) - 1) ≤ ((j + d.1 : ℤ) : ℝ) := by push_cast; linarith [hd11]
            calc ((j : ℝ) - 1) * a ≤ ((j + d.1 : ℤ) : ℝ) * a :=
                  mul_le_mul_of_nonneg_right hb hapos.le
              _ ≤ w.re := hw.1
          · have hd12 : (d.1 : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hd.1.2
            have hb : (((j + d.1 : ℤ) : ℝ) + 1) ≤ ((j : ℝ) + 2) := by push_cast; linarith [hd12]
            calc w.re ≤ (((j + d.1 : ℤ) : ℝ) + 1) * a := hw.2.1
              _ ≤ ((j : ℝ) + 2) * a := mul_le_mul_of_nonneg_right hb hapos.le
          · have hd21 : (-1 : ℝ) ≤ (d.2 : ℝ) := by exact_mod_cast hd.2.1
            have hb : ((k : ℝ) - 1) ≤ ((k + d.2 : ℤ) : ℝ) := by push_cast; linarith [hd21]
            calc ((k : ℝ) - 1) * a ≤ ((k + d.2 : ℤ) : ℝ) * a :=
                  mul_le_mul_of_nonneg_right hb hapos.le
              _ ≤ w.im := hw.2.2.1
          · have hd22 : (d.2 : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hd.2.2
            have hb : (((k + d.2 : ℤ) : ℝ) + 1) ≤ ((k : ℝ) + 2) := by push_cast; linarith [hd22]
            calc w.im ≤ (((k + d.2 : ℤ) : ℝ) + 1) * a := hw.2.2.2
              _ ≤ ((k : ℝ) + 2) * a := mul_le_mul_of_nonneg_right hb hapos.le
        exact hsub1.trans ((henlarged_thick ⟨j, k⟩ hjk).trans hthick)
      have h9x : ∑ jk ∈ hitting, ∫⁻ z in enlarged jk.1 jk.2, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2)
          ≤ 9 * ∫⁻ z in U', (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := by
        calc ∑ jk ∈ hitting, ∫⁻ z in enlarged jk.1 jk.2, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2)
            ≤ ∑ jk ∈ hitting, ∑ d ∈ shifts, ∫⁻ z in closedCell (jk.1 + d.1) (jk.2 + d.2),
                (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := Finset.sum_le_sum h9x_step1
          _ = ∑ d ∈ shifts, ∑ jk ∈ hitting, ∫⁻ z in closedCell (jk.1 + d.1) (jk.2 + d.2),
                (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := Finset.sum_comm
          _ ≤ ∑ _d ∈ shifts, ∫⁻ z in U', (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := by
              apply Finset.sum_le_sum
              intro d hd
              calc ∑ jk ∈ hitting, ∫⁻ z in closedCell (jk.1 + d.1) (jk.2 + d.2),
                    (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2)
                  = ∫⁻ z in ⋃ jk ∈ hitting, closedCell (jk.1 + d.1) (jk.2 + d.2),
                      (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := by
                    have := hdisjoint_sum_eq (hitting.image (fun jk => (jk.1 + d.1, jk.2 + d.2)))
                    rw [Finset.sum_image (fun jk1 _ jk2 _ h => by
                      simp only [Prod.mk.injEq] at h; exact Prod.ext (by omega) (by omega))] at this
                    rw [this, Finset.set_biUnion_finset_image]
                _ ≤ ∫⁻ z in U', (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := by
                    apply lintegral_mono_set
                    intro w hw
                    rw [Set.mem_iUnion₂] at hw
                    obtain ⟨jk, hjk, hwjk⟩ := hw
                    exact hcell_shift_sub_U' jk hjk d hd hwjk
          _ = 9 * ∫⁻ z in U', (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := by
              rw [Finset.sum_const, hshiftscard, nsmul_eq_mul]
              norm_num
      calc volume C ≤ ENNReal.ofReal (4 * π) * ∑ jk ∈ hitting,
            ∫⁻ z in enlarged jk.1 jk.2, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := hCbound2
        _ ≤ ENNReal.ofReal (4 * π) * (9 * ∫⁻ z in U', (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2)) := by
              gcongr
        _ ≤ ENNReal.ofReal (4 * π) * (9 * ENNReal.ofReal ε) := by
              gcongr
        _ = ENNReal.ofReal (36 * π * ε) := by
              rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by positivity),
                ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              ring
    have hzero : volume (f '' (G ∩ R0)) = 0 := by
      by_contra hcon
      have hVpos : 0 < volume (f '' (G ∩ R0)) := pos_iff_ne_zero.2 hcon
      set V : ℝ≥0∞ := volume (f '' (G ∩ R0)) with hVdef
      have hVfin : V ≠ ⊤ := hfGR0ne_top
      have htr : (0:ℝ) < V.toReal := ENNReal.toReal_pos hVpos.ne' hVfin
      set ε0 : ℝ := V.toReal / (72 * π) with hε0def
      have hε0pos : 0 < ε0 := by rw [hε0def]; positivity
      have hb := hmain ε0 hε0pos
      have hcalc : ENNReal.ofReal (36 * π * ε0) = V / 2 := by
        have heq2 : 36 * π * ε0 = V.toReal / 2 := by rw [hε0def]; field_simp; ring
        rw [heq2, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2),
          ENNReal.ofReal_toReal hVfin, show ENNReal.ofReal (2:ℝ) = (2:ℝ≥0∞) from by norm_num]
      rw [hcalc] at hb
      exact absurd hb (not_le.2 (ENNReal.half_lt_self hVpos.ne' hVfin))
    have hEfinal : f '' (E ∩ R0) ⊆ f '' (G ∩ R0) :=
      Set.image_mono (Set.subset_inter hSG Set.inter_subset_right)
    exact measure_mono_null hEfinal hzero
  -- Countable cover of `D` by rational squares `R₀` (with a valid margin enlargement `R₁ ⊆ D`).
  have hcover : D = ⋃ t : {t : ℚ × ℚ × ℚ // 0 < t.2.2 ∧
      closedRect ((t.1 : ℝ) - 2 * t.2.2) ((t.1 : ℝ) + 2 * t.2.2)
        ((t.2.1 : ℝ) - 2 * t.2.2) ((t.2.1 : ℝ) + 2 * t.2.2) ⊆ D},
      openRect ((t.1.1 : ℝ) - t.1.2.2) ((t.1.1 : ℝ) + t.1.2.2)
        ((t.1.2.1 : ℝ) - t.1.2.2) ((t.1.2.1 : ℝ) + t.1.2.2) := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, q, s, hspos, hmem, hsub⟩ := ac_n_b_exists_rat_square hDopen hz
      exact mem_iUnion.2 ⟨⟨(p, q, s), hspos, hsub⟩, hmem⟩
    · intro hz
      obtain ⟨t, ht⟩ := mem_iUnion.1 hz
      apply t.2.2
      have hspos : (0:ℝ) < (t.1.2.2 : ℝ) := by exact_mod_cast t.2.1
      refine ⟨by linarith [ht.1], by linarith [ht.2.1],
        by linarith [ht.2.2.1], by linarith [ht.2.2.2]⟩
  have hopensubclosed : ∀ t : {t : ℚ × ℚ × ℚ // 0 < t.2.2 ∧
      closedRect ((t.1 : ℝ) - 2 * t.2.2) ((t.1 : ℝ) + 2 * t.2.2)
        ((t.2.1 : ℝ) - 2 * t.2.2) ((t.2.1 : ℝ) + 2 * t.2.2) ⊆ D},
      openRect ((t.1.1 : ℝ) - t.1.2.2) ((t.1.1 : ℝ) + t.1.2.2)
        ((t.1.2.1 : ℝ) - t.1.2.2) ((t.1.2.1 : ℝ) + t.1.2.2) ⊆
      closedRect ((t.1.1 : ℝ) - t.1.2.2) ((t.1.1 : ℝ) + t.1.2.2)
        ((t.1.2.1 : ℝ) - t.1.2.2) ((t.1.2.1 : ℝ) + t.1.2.2) := by
    intro t w hw
    exact ⟨hw.1.le, hw.2.1.le, hw.2.2.1.le, hw.2.2.2.le⟩
  have hEsub : E ⊆ ⋃ t : {t : ℚ × ℚ × ℚ // 0 < t.2.2 ∧
      closedRect ((t.1 : ℝ) - 2 * t.2.2) ((t.1 : ℝ) + 2 * t.2.2)
        ((t.2.1 : ℝ) - 2 * t.2.2) ((t.2.1 : ℝ) + 2 * t.2.2) ⊆ D},
      closedRect ((t.1.1 : ℝ) - t.1.2.2) ((t.1.1 : ℝ) + t.1.2.2)
        ((t.1.2.1 : ℝ) - t.1.2.2) ((t.1.2.1 : ℝ) + t.1.2.2) := by
    intro w hw
    obtain ⟨t, ht⟩ := mem_iUnion.1 (hcover ▸ hED hw : w ∈ ⋃ t : {t : ℚ × ℚ × ℚ // 0 < t.2.2 ∧
      closedRect ((t.1 : ℝ) - 2 * t.2.2) ((t.1 : ℝ) + 2 * t.2.2)
        ((t.2.1 : ℝ) - 2 * t.2.2) ((t.2.1 : ℝ) + 2 * t.2.2) ⊆ D},
      openRect ((t.1.1 : ℝ) - t.1.2.2) ((t.1.1 : ℝ) + t.1.2.2)
        ((t.1.2.1 : ℝ) - t.1.2.2) ((t.1.2.1 : ℝ) + t.1.2.2))
    exact mem_iUnion.2 ⟨t, hopensubclosed t ht⟩
  have hEeq : E = ⋃ t : {t : ℚ × ℚ × ℚ // 0 < t.2.2 ∧
      closedRect ((t.1 : ℝ) - 2 * t.2.2) ((t.1 : ℝ) + 2 * t.2.2)
        ((t.2.1 : ℝ) - 2 * t.2.2) ((t.2.1 : ℝ) + 2 * t.2.2) ⊆ D},
      E ∩ closedRect ((t.1.1 : ℝ) - t.1.2.2) ((t.1.1 : ℝ) + t.1.2.2)
        ((t.1.2.1 : ℝ) - t.1.2.2) ((t.1.2.1 : ℝ) + t.1.2.2) := by
    rw [← Set.inter_iUnion, Set.inter_eq_self_of_subset_left hEsub]
  have hfEeq : f '' E = ⋃ t : {t : ℚ × ℚ × ℚ // 0 < t.2.2 ∧
      closedRect ((t.1 : ℝ) - 2 * t.2.2) ((t.1 : ℝ) + 2 * t.2.2)
        ((t.2.1 : ℝ) - 2 * t.2.2) ((t.2.1 : ℝ) + 2 * t.2.2) ⊆ D},
      f '' (E ∩ closedRect ((t.1.1 : ℝ) - t.1.2.2) ((t.1.1 : ℝ) + t.1.2.2)
        ((t.1.2.1 : ℝ) - t.1.2.2) ((t.1.2.1 : ℝ) + t.1.2.2)) := by
    conv_lhs => rw [hEeq]
    exact Set.image_iUnion
  rw [hfEeq]
  apply measure_iUnion_null
  intro t
  exact hlocal t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2



/-- **N3** in its original `K`-q.c. form (Theorems 9.1 and 9.5 supply the hypotheses). -/
theorem ac_n_volume_image_null_of_isKQC {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K)
    {E : Set ℂ} (hED : E ⊆ D) (hE : volume E = 0) : volume (f '' E) = 0 :=
  ac_n_volume_image_null hf.1 (thm9_1_isACL hf) hf.2.2.1.2.1 hf.2.2.1.2.2.2
    (thm9_5_L2_derivatives hf).1.1 hED hE

/-! ### Theorem 9.6 track — helpers of piece J -/

/-- The Jacobian of a `K`-q.c. map is nonnegative at every point of differentiability
(`ac_t_dilatation_of_differentiableAt` forces `|∂_{z̄} f| ≤ |∂_z f|`). -/
theorem ac_j_jacobian_nonneg {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {z : ℂ}
    (hz : z ∈ D) (hd : DifferentiableAt ℝ f z) : 0 ≤ jacobian f z := by
  have h := ac_t_dilatation_of_differentiableAt hf hz hd
  have hK : (1 : ℝ) ≤ K := hf.2.1
  have h0 : 0 ≤ ‖dz f z‖ := norm_nonneg _
  have h1 : 0 ≤ ‖dzbar f z‖ := norm_nonneg _
  have hle : ‖dzbar f z‖ ≤ ‖dz f z‖ := by
    by_contra hlt
    push Not at hlt
    have : K * (‖dz f z‖ - ‖dzbar f z‖) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  unfold jacobian
  nlinarith

/-- **Theorem 9.6** (9.18): a quasiconformal map is absolutely continuous with respect to
two-dimensional Lebesgue measure: `m(f(σ)) = ∬_σ J_f dx dy` for Borel sets `σ ⊆ D`.

Proved (2026-09-21): Mathlib's change of variables on the set of differentiability, Lusin's property (N)
for `K`-q.c. maps (`ac_n_volume_image_null`, via the offset-averaged grid estimate
`ac_n_volume_image_le_lintegral` and the `L²` partials) on the null remainder, and `jacobian = det ≥ 0`
at differentiable points (`ac_t_dilatation_of_differentiableAt`). -/
theorem thm9_6_absolutelyContinuous {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K)
    {σ : Set ℂ} (hσ : MeasurableSet σ) (hσD : σ ⊆ D) :
    volume (f '' σ) = ∫⁻ z in σ, ENNReal.ofReal (jacobian f z) := by
  refine le_antisymm ?_ (lintegral_jacobian_le_volume_image hf hσ hσD)
  set A : Set ℂ := σ ∩ {z | DifferentiableAt ℝ f z} with hAdef
  have hSm : MeasurableSet A := hσ.inter (measurableSet_of_differentiableAt ℝ f)
  have hAσ : A ⊆ σ := inter_subset_left
  have hnull : volume (σ \ A) = 0 := by
    have h := thm9_3_differentiable_ae hf
    rw [ae_restrict_iff' hf.1.measurableSet, ae_iff] at h
    exact measure_mono_null (fun z hz => fun h' => hz.2 ⟨hz.1, h' (hσD hz.1)⟩) h
  have himg_null : volume (f '' (σ \ A)) = 0 :=
    ac_n_volume_image_null_of_isKQC hf (fun z hz => hσD hz.1) hnull
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm
    (fun z hz => hz.2.hasFDerivAt.hasFDerivWithinAt)
    (hf.2.2.1.2.1.mono fun z hz => hσD hz.1) (fun _ => 1)
  simp only [mul_one, setLIntegral_const, one_mul] at hcv
  have hcover : f '' σ ⊆ f '' A ∪ f '' (σ \ A) := by
    rw [← image_union, union_diff_cancel hAσ]
  calc volume (f '' σ)
      ≤ volume (f '' A ∪ f '' (σ \ A)) := measure_mono hcover
    _ ≤ volume (f '' A) + volume (f '' (σ \ A)) := measure_union_le _ _
    _ = volume (f '' A) := by rw [himg_null, add_zero]
    _ = ∫⁻ z in A, ENNReal.ofReal |(fderiv ℝ f z).det| := hcv
    _ = ∫⁻ z in A, ENNReal.ofReal (jacobian f z) := by
        refine setLIntegral_congr_fun hSm ?_
        intro z hz
        dsimp only
        have e : (fderiv ℝ f z).det = jacobian f z := det_fderiv_eq_jacobian hz.2
        rw [e, abs_of_nonneg (ac_j_jacobian_nonneg hf (hσD hz.1) hz.2)]
    _ = ∫⁻ z in σ, ENNReal.ofReal (jacobian f z) :=
        (setLIntegral_congr (ae_eq_set.2 ⟨hnull, by
          rw [diff_eq_empty.2 hAσ, measure_empty]⟩)).symm

/-- **Theorem 9.6, Corollary 1**: a quasiconformal map sends null sets to null sets. -/
theorem thm9_6_cor1_null {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {e : Set ℂ}
    (heD : e ⊆ D) (he : volume e = 0) : volume (f '' e) = 0 := by
  obtain ⟨σ, heσ, hσm, hσ0⟩ := exists_measurable_superset_of_null he
  have h1 := thm9_6_absolutelyContinuous hf (hσm.inter hf.1.measurableSet) inter_subset_right
  have h2 : ∫⁻ z in σ ∩ D, ENNReal.ofReal (jacobian f z) = 0 :=
    setLIntegral_measure_zero _ _ (measure_mono_null inter_subset_left hσ0)
  exact measure_mono_null (image_mono (subset_inter heσ heD)) (h1.trans h2)

/-- **Theorem 9.6, Corollary 2**: the Jacobian of a quasiconformal map is positive almost
everywhere. -/
theorem thm9_6_cor2_jacobian_pos {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) :
    ∀ᵐ z ∂(volume.restrict D), 0 < jacobian f z := by
  have hDm : MeasurableSet D := hf.1.measurableSet
  have hJm : Measurable (jacobian f) :=
    ((measurable_dz f).norm.pow_const 2).sub ((measurable_dzbar f).norm.pow_const 2)
  obtain ⟨E, hE⟩ : ∃ E : Set ℂ, E = {z | jacobian f z ≤ 0} ∩ D := ⟨_, rfl⟩
  have hEm : MeasurableSet E := by
    rw [hE]
    exact (measurableSet_le hJm measurable_const).inter hDm
  have hED : E ⊆ D := by
    rw [hE]
    exact inter_subset_right
  -- `m(f(E)) = ∬_E J_f = 0`
  have hfE : volume (f '' E) = 0 := by
    rw [thm9_6_absolutelyContinuous hf hEm hED,
      setLIntegral_congr_fun hEm (fun z hz => ENNReal.ofReal_of_nonpos (by rw [hE] at hz; exact hz.1))]
    simp
  -- `f⁻¹` is quasiconformal and maps `f(E)` back onto `E`
  have hE0 : volume E = 0 := by
    have h1 := thm9_6_cor1_null (thm7_2_inv hf) (image_mono hED) hfE
    rwa [(hf.2.2.1.2.1.leftInvOn_invFunOn.mono hED).image_image] at h1
  rw [ae_restrict_iff' hDm, ae_iff]
  refine measure_mono_null (fun z hz => ?_) hE0
  simp only [mem_setOf_eq, Classical.not_imp, not_lt] at hz
  rw [hE]
  exact ⟨hz.2, hz.1⟩

end LiZhongQC
