import LiZhongQC.Ch01.S04_ModulusExtremalLength
import LiZhongQC.Lemmas.RectangleQuad
import LiZhongQC.Lemmas.ImageQuad
import LiZhongQC.Lemmas.InvarianceOfDomain
import LiZhongQC.Lemmas.CanonicalForm

/-!
# Quasi-invariance of the modulus of round annuli (leaf for Theorem 7.4)

The core of Theorem 7.4 (`thm7_4_dcModulus_quasi_invariance`, S07) without cutting the image domain and
without any boundary extension: a homeomorphism `g` of `{1<|z|<R}` onto `{1<|w|<R'}` satisfying the
quadrilateral bound of Definition 7.1 with constant `K` has `ln R' ≤ K ln R`.  Ingredients: the sector
quadrilateral (A), the radial length estimate (B), the collar lemma (C, pure point-set topology), the
weighted inequality (4.6) on the image quadrilateral (D); and the topology needed to reduce Theorem 7.4 to
this: images of doubly connected domains are doubly connected (E1), `M(B) = ∞` iff a complementary
component is a point (E2), one-point components transport (E3).  Helpers carry the prefix `aqc_`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace LiZhongQC

/-! ### Piece A -/

/-! ## Stage 1: right/left edges of a rectangle -/

theorem aqc_boundaryArc_congr_w {K : Set ℂ} {u v w₁ w₂ : ℂ}
    (h : connectedComponentIn (K \ {u, v}) w₁ = connectedComponentIn (K \ {u, v}) w₂) :
    boundaryArc K u v w₁ = boundaryArc K u v w₂ := by
  unfold boundaryArc
  rw [h]

theorem aqc_left_edge_component {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    connectedComponentIn (frontier (rectangle a b) \ {(a : ℂ), (a : ℂ) + (b : ℂ) * I}) 0 =
      connectedComponentIn (frontier (rectangle a b) \ {(a : ℂ), (a : ℂ) + (b : ℂ) * I})
        ((b : ℂ) * I) := by
  set K := frontier (rectangle a b) \ {(a : ℂ), (a : ℂ) + (b : ℂ) * I} with hK_def
  have hconn : IsPreconnected (({0} : Set ℝ) ×ℂ Icc (0 : ℝ) b) :=
    isPreconnected_reProdIm isPreconnected_singleton isPreconnected_Icc
  have hcre : ((a : ℂ) + (b : ℂ) * I).re = a := by simp
  have hsub : (({0} : Set ℝ) ×ℂ Icc (0 : ℝ) b) ⊆ K := by
    intro z hz
    rw [mem_reProdIm, mem_singleton_iff] at hz
    obtain ⟨hzre, hzim⟩ := hz
    rw [hK_def, mem_diff]
    constructor
    · rw [frontier_rectangle ha hb]
      exact Or.inr ⟨Or.inl hzre, hzim⟩
    · rw [mem_insert_iff, mem_singleton_iff]
      push_neg
      constructor
      · intro h
        rw [h] at hzre
        simp only [Complex.ofReal_re] at hzre
        exact ha.ne' hzre
      · intro h
        rw [h, hcre] at hzre
        exact ha.ne' hzre
  have hmem0 : (0 : ℂ) ∈ (({0} : Set ℝ) ×ℂ Icc (0 : ℝ) b) := by
    rw [mem_reProdIm]
    simp [hb.le]
  have hmem3 : ((b : ℂ) * I) ∈ (({0} : Set ℝ) ×ℂ Icc (0 : ℝ) b) := by
    rw [mem_reProdIm]
    simp [hb.le]
  have hstep := (hconn.subset_connectedComponentIn hmem0 hsub) hmem3
  exact connectedComponentIn_eq hstep

/-- `boundaryArc` is symmetric in its first two (endpoint) arguments. -/
theorem aqc_boundaryArc_swap_uv {K : Set ℂ} {u v w : ℂ} :
    boundaryArc K u v w = boundaryArc K v u w := by
  unfold boundaryArc
  ext p
  simp only [mem_setOf_eq]
  rw [Set.pair_comm u v]
  tauto

/-- The right edge `{a} ×ℂ [0,b]` of `R(0,a,a+bi,bi)` is its side `1`. -/
theorem aqc_boundaryArc_rectangle_right {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    boundaryArc (frontier (rectangle a b)) (a : ℂ) ((a : ℂ) + (b : ℂ) * I) ((b : ℂ) * I) =
      ({a} : Set ℝ) ×ℂ Icc (0 : ℝ) b := by
  have hw : boundaryArc (frontier (rectangle a b)) (a : ℂ) ((a : ℂ) + (b : ℂ) * I) ((b : ℂ) * I) =
      boundaryArc (frontier (rectangle a b)) (a : ℂ) ((a : ℂ) + (b : ℂ) * I) (0 : ℂ) := by
    refine (aqc_boundaryArc_congr_w ?_).symm
    exact aqc_left_edge_component ha hb
  rw [hw]
  set ρ : ℂ → ℂ := fun z => I * (starRingEnd ℂ) z with hρ_def
  have hρinv : ∀ z : ℂ, ρ (ρ z) = z := by
    intro z
    simp only [hρ_def, map_mul, Complex.conj_I, Complex.conj_conj]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hρiso : Isometry ρ := by
    apply Isometry.of_dist_eq
    intro z w
    rw [Complex.dist_eq, Complex.dist_eq]
    have hlin : ρ z - ρ w = ρ (z - w) := by
      simp only [hρ_def, map_sub]
      ring
    rw [hlin, hρ_def]
    simp only [norm_mul, Complex.norm_I, Complex.norm_conj, one_mul]
  have hρemb : IsEmbedding ρ := hρiso.isEmbedding
  have hρre : ∀ z : ℂ, (ρ z).re = z.im := fun z => by
    simp [hρ_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have hρim : ∀ z : ℂ, (ρ z).im = z.re := fun z => by
    simp [hρ_def, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  have hρrect : ρ '' rectangle b a = rectangle a b := by
    ext z
    simp only [rectangle, mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨w, ⟨hw1, hw2, hw3, hw4⟩, rfl⟩
      exact ⟨by rw [hρre]; exact hw3, by rw [hρre]; exact hw4, by rw [hρim]; exact hw1,
        by rw [hρim]; exact hw2⟩
    · rintro ⟨hz1, hz2, hz3, hz4⟩
      exact ⟨ρ z, ⟨by rw [hρre]; exact hz3, by rw [hρre]; exact hz4, by rw [hρim]; exact hz1,
        by rw [hρim]; exact hz2⟩, hρinv z⟩
  have hρfrontier : ρ '' frontier (rectangle b a) = frontier (rectangle a b) := by
    ext z
    simp only [mem_image, frontier_rectangle hb ha, frontier_rectangle ha hb, mem_union,
      mem_reProdIm, mem_Icc, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨w, (⟨⟨h1, h2⟩, h3 | h3⟩ | ⟨h1 | h1, h2, h3⟩), rfl⟩
      · exact Or.inr ⟨Or.inl (by rw [hρre]; exact h3), by rw [hρim]; exact ⟨h1, h2⟩⟩
      · exact Or.inr ⟨Or.inr (by rw [hρre]; exact h3), by rw [hρim]; exact ⟨h1, h2⟩⟩
      · exact Or.inl ⟨by rw [hρre]; exact ⟨h2, h3⟩, Or.inl (by rw [hρim]; exact h1)⟩
      · exact Or.inl ⟨by rw [hρre]; exact ⟨h2, h3⟩, Or.inr (by rw [hρim]; exact h1)⟩
    · rintro (⟨⟨h1, h2⟩, h3 | h3⟩ | ⟨h1 | h1, h2, h3⟩)
      · exact ⟨ρ z, Or.inr ⟨Or.inl (by rw [hρre]; exact h3), by rw [hρim]; exact ⟨h1, h2⟩⟩,
          hρinv z⟩
      · exact ⟨ρ z, Or.inr ⟨Or.inr (by rw [hρre]; exact h3), by rw [hρim]; exact ⟨h1, h2⟩⟩,
          hρinv z⟩
      · exact ⟨ρ z, Or.inl ⟨by rw [hρre]; exact ⟨h2, h3⟩, Or.inl (by rw [hρim]; exact h1)⟩,
          hρinv z⟩
      · exact ⟨ρ z, Or.inl ⟨by rw [hρre]; exact ⟨h2, h3⟩, Or.inr (by rw [hρim]; exact h1)⟩,
          hρinv z⟩
  have hlem := image_boundaryArc_of_isEmbedding hρemb (frontier (rectangle b a))
    ((b : ℂ) + (a : ℂ) * I) ((a : ℂ) * I) (0 : ℂ)
  rw [hρfrontier] at hlem
  have htop := boundaryArc_rectangle_top (a := b) (b := a) hb ha
  rw [htop] at hlem
  have hρ1 : ρ ((b : ℂ) + (a : ℂ) * I) = (a : ℂ) + (b : ℂ) * I := by
    apply Complex.ext
    · rw [hρre]; simp
    · rw [hρim]; simp
  have hρ2 : ρ ((a : ℂ) * I) = (a : ℂ) := by
    apply Complex.ext
    · rw [hρre]; simp
    · rw [hρim]; simp
  have hρ3 : ρ (0 : ℂ) = 0 := by simp [hρ_def]
  rw [hρ1, hρ2, hρ3] at hlem
  have hLHS : ρ '' (Icc (0 : ℝ) b ×ℂ ({a} : Set ℝ)) = ({a} : Set ℝ) ×ℂ Icc (0 : ℝ) b := by
    ext z
    simp only [mem_image, mem_reProdIm, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
      exact ⟨by rw [hρre]; exact hw2, by rw [hρim]; exact hw1⟩
    · rintro ⟨hz1, hz2⟩
      exact ⟨ρ z, ⟨by rw [hρre]; exact hz2, by rw [hρim]; exact hz1⟩, hρinv z⟩
  rw [hLHS] at hlem
  rw [aqc_boundaryArc_swap_uv]
  exact hlem.symm

/-- The left edge `{0} ×ℂ [0,b]` of `R(0,a,a+bi,bi)` is its side `3`. -/
theorem aqc_boundaryArc_rectangle_left {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    boundaryArc (frontier (rectangle a b)) ((b : ℂ) * I) (0 : ℂ) (a : ℂ) =
      ({0} : Set ℝ) ×ℂ Icc (0 : ℝ) b := by
  have hσ : IsEmbedding (fun z : ℂ => (a : ℂ) + (b : ℂ) * I - z) :=
    (Homeomorph.subLeft ((a : ℂ) + (b : ℂ) * I)).isEmbedding
  have hinv : ∀ A : Set ℂ, (fun z : ℂ => (a : ℂ) + (b : ℂ) * I - z) '' A =
      (fun z : ℂ => (a : ℂ) + (b : ℂ) * I - z) ⁻¹' A := fun A =>
    congrFun (image_eq_preimage_of_inverse (f := fun z : ℂ => (a : ℂ) + (b : ℂ) * I - z)
      (g := fun z : ℂ => (a : ℂ) + (b : ℂ) * I - z) (fun z => sub_sub_cancel _ z)
      (fun z => sub_sub_cancel _ z)) A
  have hre : ∀ z : ℂ, ((a : ℂ) + (b : ℂ) * I - z).re = a - z.re := fun z => by simp
  have him : ∀ z : ℂ, ((a : ℂ) + (b : ℂ) * I - z).im = b - z.im := fun z => by simp
  have hK : (fun z : ℂ => (a : ℂ) + (b : ℂ) * I - z) '' frontier (rectangle a b) =
      frontier (rectangle a b) := by
    rw [hinv, frontier_rectangle ha hb]
    ext z
    simp only [mem_preimage, mem_union, mem_reProdIm, mem_Icc, mem_insert_iff, mem_singleton_iff,
      hre, him]
    constructor
    · rintro (⟨⟨h1, h2⟩, h3 | h3⟩ | ⟨h1 | h1, h2, h3⟩)
      · exact Or.inl ⟨⟨by linarith, by linarith⟩, Or.inr (by linarith)⟩
      · exact Or.inl ⟨⟨by linarith, by linarith⟩, Or.inl (by linarith)⟩
      · exact Or.inr ⟨Or.inr (by linarith), by linarith, by linarith⟩
      · exact Or.inr ⟨Or.inl (by linarith), by linarith, by linarith⟩
    · rintro (⟨⟨h1, h2⟩, h3 | h3⟩ | ⟨h1 | h1, h2, h3⟩)
      · exact Or.inl ⟨⟨by linarith, by linarith⟩, Or.inr (by linarith)⟩
      · exact Or.inl ⟨⟨by linarith, by linarith⟩, Or.inl (by linarith)⟩
      · exact Or.inr ⟨Or.inr (by linarith), by linarith, by linarith⟩
      · exact Or.inr ⟨Or.inl (by linarith), by linarith, by linarith⟩
  have hright := aqc_boundaryArc_rectangle_right ha hb
  have h := image_boundaryArc_of_isEmbedding hσ (frontier (rectangle a b))
    (a : ℂ) ((a : ℂ) + (b : ℂ) * I) ((b : ℂ) * I)
  rw [hright, hK] at h
  have hcre : ((a : ℂ) + (b : ℂ) * I).re = a := by simp
  have hcim : ((a : ℂ) + (b : ℂ) * I).im = b := by simp
  have hσa : (a : ℂ) + (b : ℂ) * I - (a : ℂ) = (b : ℂ) * I := by ring
  have hσab : (a : ℂ) + (b : ℂ) * I - ((a : ℂ) + (b : ℂ) * I) = 0 := by ring
  have hσb : (a : ℂ) + (b : ℂ) * I - (b : ℂ) * I = (a : ℂ) := by ring
  simp only [hσa, hσab, hσb] at h
  have hLHS : (fun z : ℂ => (a : ℂ) + (b : ℂ) * I - z) '' (({a} : Set ℝ) ×ℂ Icc (0 : ℝ) b) =
      ({0} : Set ℝ) ×ℂ Icc (0 : ℝ) b := by
    ext z
    simp only [mem_image, mem_reProdIm, mem_singleton_iff, mem_Icc]
    constructor
    · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
      refine ⟨by rw [Complex.sub_re, hcre, hw1]; ring, ?_, ?_⟩ <;>
        · rw [Complex.sub_im, hcim]; linarith [hw2.1, hw2.2]
    · rintro ⟨hz1, hz2, hz3⟩
      refine ⟨(a : ℂ) + (b : ℂ) * I - z, ⟨?_, ?_, ?_⟩, by ring⟩
      · rw [Complex.sub_re, hcre, hz1]; ring
      · rw [Complex.sub_im, hcim]; linarith
      · rw [Complex.sub_im, hcim]; linarith
  rw [hLHS] at h
  exact h.symm

/-- The second side of `R(0, a, a+bi, bi)`, in `ℂ̄`, is the right edge. -/
theorem aqc_boundaryArc_frontier_toExt_rectangle_right {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    boundaryArc (frontier (toExt (rectangle a b))) (rectVert a b 1) (rectVert a b 2)
      (rectVert a b 3) = toExt (({a} : Set ℝ) ×ℂ Icc (0 : ℝ) b) := by
  rw [frontier_toExt_of_isBounded (isBounded_rectangle a b) (isOpen_rectangle a b)]
  have h := image_boundaryArc_of_isEmbedding OnePoint.isOpenEmbedding_coe.isEmbedding
    (frontier (rectangle a b)) (a : ℂ) ((a : ℂ) + (b : ℂ) * I) ((b : ℂ) * I)
  rw [aqc_boundaryArc_rectangle_right ha hb] at h
  unfold toExt
  rw [h]
  rfl

/-- The fourth side of `R(0, a, a+bi, bi)`, in `ℂ̄`, is the left edge. -/
theorem aqc_boundaryArc_frontier_toExt_rectangle_left {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    boundaryArc (frontier (toExt (rectangle a b))) (rectVert a b 3) (rectVert a b 0)
      (rectVert a b 1) = toExt (({0} : Set ℝ) ×ℂ Icc (0 : ℝ) b) := by
  rw [frontier_toExt_of_isBounded (isBounded_rectangle a b) (isOpen_rectangle a b)]
  have h := image_boundaryArc_of_isEmbedding OnePoint.isOpenEmbedding_coe.isEmbedding
    (frontier (rectangle a b)) ((b : ℂ) * I) (0 : ℂ) (a : ℂ)
  rw [aqc_boundaryArc_rectangle_left ha hb] at h
  unfold toExt
  rw [h]
  rfl

/-! ## Stage 2: local copy of `TopQuad.exists_image_conformal` (S07:98-167) -/

theorem aqc_isConformalOnto_of_leftInverse {D D' : Set ℂ} {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) (hfmaps : MapsTo f D D') (hgmaps : MapsTo g D' D)
    (hfg : ∀ w ∈ D', f (g w) = w) (hgf : ∀ z ∈ D, g (f z) = z) : IsConformalOnto f D D' := by
  refine ⟨hf, fun z₁ h₁ z₂ h₂ heq => ?_, ?_⟩
  · rw [← hgf z₁ h₁, ← hgf z₂ h₂, heq]
  · exact subset_antisymm (image_subset_iff.2 hfmaps) fun w hw => ⟨g w, hgmaps hw, hfg w hw⟩

theorem aqc_exists_image_conformal {f : ℂ → ℂ} {D D' : Set ℂ} (hD : IsOpen D)
    (hf : IsConformalOnto f D D') {Q : TopQuad} (hQ : closure (toExt Q.dom) ⊆ toExt D) :
    ∃ Q' : TopQuad, Q.IsImageUnder Q' f ∧ Q.ConfEquiv Q' := by
  obtain ⟨hJ, hQv, φ, Φ, x, hφ, hΦ, hx, hΦv⟩ := Q.isTopQuad
  set C := closure (toExt Q.dom) with hC
  set F : ExtPlane → ExtPlane := OnePoint.map f with hF
  have hQo : IsOpen Q.dom := hJ.1
  have hsubD : Q.dom ⊆ D := fun z hz => by
    obtain ⟨w, hw, hwz⟩ := hQ (subset_closure (mem_image_of_mem _ hz))
    rw [← OnePoint.coe_injective hwz]
    exact hw
  have hfQ : IsConformalOnto f Q.dom (f '' Q.dom) := ⟨hf.1.mono hsubD, hf.2.1.mono hsubD, rfl⟩
  have htoExt : ∀ S : Set ℂ, F '' toExt S = toExt (f '' S) := fun S => by
    simp only [toExt, image_image]
    rfl
  have hFC : ContinuousOn F C := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := hQ hp
    refine ContinuousAt.continuousWithinAt (OnePoint.continuousAt_coe.2 ?_)
    exact OnePoint.continuous_coe.continuousAt.comp
      (hf.1.continuousOn.continuousAt (hD.mem_nhds hz))
  have hFinj : InjOn F C := by
    intro p hp q hq hpq
    obtain ⟨z, hz, rfl⟩ := hQ hp
    obtain ⟨w, hw, rfl⟩ := hQ hq
    rw [hf.2.1 hz hw (OnePoint.coe_injective hpq)]
  have hFimg : F '' C = closure (toExt (f '' Q.dom)) := by
    refine subset_antisymm ?_ ?_
    · rw [← htoExt]
      exact hFC.image_closure
    · refine closure_minimal ?_ (isClosed_closure.isCompact.image_of_continuousOn hFC).isClosed
      rw [← htoExt]
      exact image_mono subset_closure
  have hext : IsHomeoExtension f Q.dom (f '' Q.dom) F := ⟨fun z _ => rfl, hFC, hFinj, hFimg⟩
  have hfo : IsOpen (f '' Q.dom) := hfQ.isOpen hQo
  have hfr : F '' frontier (toExt Q.dom) = frontier (toExt (f '' Q.dom)) :=
    hext.image_frontier hQo hfo rfl
  have hfrC : frontier (toExt Q.dom) ⊆ C := frontier_subset_closure
  have hinv : IsHomeoExtension (Function.invFunOn f Q.dom) (f '' Q.dom) Q.dom
      (Function.invFunOn F C) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      have hzC : ((z : ℂ) : ExtPlane) ∈ C := subset_closure (mem_image_of_mem _ hz)
      rw [hfQ.2.1.leftInvOn_invFunOn hz]
      exact hFinj.leftInvOn_invFunOn hzC
    · rw [← hFimg]
      exact continuousOn_invFunOn_of_isClosed isClosed_closure hFC hFinj
    · rw [← hFimg]
      intro p hp q hq hpq
      calc p = F (Function.invFunOn F C p) := (Function.invFunOn_eq hp).symm
        _ = F (Function.invFunOn F C q) := by rw [hpq]
        _ = q := Function.invFunOn_eq hq
    · rw [← hFimg]
      exact hFinj.leftInvOn_invFunOn.image_image
  have hTQ : IsTopQuad (f '' Q.dom) (fun i => F (Q.vert i)) := by
    refine ⟨⟨hfo, hJ.2.1.image f (hf.1.continuousOn.mono hsubD), ?_⟩, fun i => ?_,
      φ ∘ Function.invFunOn f Q.dom, Φ ∘ Function.invFunOn F C, x, hφ.comp (hfQ.symm hQo),
      hΦ.comp hinv (hfQ.symm hQo).mapsTo, hx, fun i => ?_⟩
    · obtain ⟨γ, hγc, hγi, hγr⟩ := hJ.2.2
      have hγC : ∀ t, γ t ∈ C := fun t => hfrC (hγr ▸ mem_range_self t)
      refine ⟨F ∘ γ, hFC.comp_continuous hγc hγC,
        fun s t hst => hγi (hFinj (hγC s) (hγC t) hst), ?_⟩
      rw [range_comp, hγr, hfr]
    · rw [← hfr]
      exact mem_image_of_mem F (hQv i)
    · show Φ (Function.invFunOn F C (F (Q.vert i))) = _
      rw [hFinj.leftInvOn_invFunOn (hfrC (hQv i))]
      exact hΦv i
  exact ⟨⟨f '' Q.dom, fun i => F (Q.vert i), hTQ⟩, ⟨rfl, fun i => rfl⟩, f, F, hfQ, hext,
    fun i => rfl⟩

/-! ## Stage 3: the sector quadrilateral -/

/-- **A.** The sector-annulus `{1+ε < |z| < R−ε, θ < arg z < 2π−θ}` is a quadrilateral
whose first pair of opposite sides are the two radial segments (sides `0`, `2`) and whose second
pair are the arcs of the circles `|z| = R−ε` (side `1`) and `|z| = 1+ε` (side `3`); its modulus is
`(ln(R−ε) − ln(1+ε)) / (2π − 2θ)`.  (Image of a rectangle under `ζ ↦ exp (ζ + ln(1+ε) + iθ)`.) -/
theorem aqc_exists_sectorQuad {R ε θ : ℝ} (hR : 1 < R) (hε : 0 < ε) (hεR : 1 + ε < R - ε)
    (hθ : 0 < θ) (hθπ : θ < π) :
    ∃ Q : TopQuad, closure (toExt Q.dom) ⊆ toExt (annulus 1 R) ∧
      Q.modulus = (Real.log (R - ε) - Real.log (1 + ε)) / (2 * π - 2 * θ) ∧
      Q.side 1 ⊆ toExt (sphere (0 : ℂ) (R - ε)) ∧ Q.side 3 ⊆ toExt (sphere (0 : ℂ) (1 + ε)) := by
  have h1ε : (0 : ℝ) < 1 + ε := by linarith
  have hRε : (0 : ℝ) < R - ε := by linarith
  set a := Real.log (R - ε) - Real.log (1 + ε) with ha_def
  set b := 2 * π - 2 * θ with hb_def
  have ha : 0 < a := by
    rw [ha_def, sub_pos]
    exact Real.log_lt_log h1ε hεR
  have hb : 0 < b := by rw [hb_def]; linarith
  set Q := rectQuad ha hb with hQ_def
  set c : ℂ := (Real.log (1 + ε) : ℂ) + ((θ : ℂ) - (π : ℂ)) * I with hc_def
  set f : ℂ → ℂ := fun ζ => Complex.exp (ζ + c) with hf_def
  set g : ℂ → ℂ := fun w => Complex.log w - c with hg_def
  set D : Set ℂ := {ζ : ℂ | -θ < ζ.im ∧ ζ.im < 2 * π - θ} with hD_def
  have hDo : IsOpen D := by
    rw [hD_def]
    exact (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hcim : c.im = θ - π := by rw [hc_def]; simp
  have hcre : c.re = Real.log (1 + ε) := by rw [hc_def]; simp
  have hgf : ∀ z ∈ D, g (f z) = z := by
    intro z hz
    have hb1 : -π < (z + c).im := by
      rw [Complex.add_im, hcim]
      linarith [hz.1]
    have hb2 : (z + c).im ≤ π := by
      rw [Complex.add_im, hcim]
      linarith [hz.2]
    rw [hg_def, hf_def]
    simp only
    rw [Complex.log_exp hb1 hb2]
    ring
  have hfdiff : DifferentiableOn ℂ f D := by
    rw [hf_def]
    exact (Complex.differentiable_exp.comp (differentiable_id.add_const c)).differentiableOn
  have hfconf : IsConformalOnto f D (f '' D) := by
    refine aqc_isConformalOnto_of_leftInverse hfdiff (mapsTo_image f D) ?_ ?_ hgf
    · rintro w ⟨z, hz, rfl⟩
      rw [hgf z hz]
      exact hz
    · rintro w ⟨z, hz, rfl⟩
      rw [hgf z hz]
  have hrectD : closure (rectangle a b) ⊆ D := by
    rw [rectangle_eq_reProdIm, closure_reProdIm, closure_Ioo ha.ne, closure_Ioo hb.ne]
    intro z hz
    rw [mem_reProdIm, mem_Icc, mem_Icc] at hz
    exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hQdomclosure : closure (toExt Q.dom) ⊆ toExt D := by
    show closure (toExt (rectangle a b)) ⊆ toExt D
    rw [closure_toExt_of_isBounded (isBounded_rectangle a b)]
    exact image_mono hrectD
  have hQsubD : Q.dom ⊆ D := (subset_closure : rectangle a b ⊆ closure (rectangle a b)).trans
    hrectD
  obtain ⟨Q', hQ'img, hQ'ce⟩ := aqc_exists_image_conformal hDo hfconf hQdomclosure
  have hfQdom : IsConformalOnto f Q.dom (f '' Q.dom) :=
    ⟨hfconf.1.mono hQsubD, hfconf.2.1.mono hQsubD, rfl⟩
  have hfo : IsOpen (f '' Q.dom) := hfQdom.isOpen (isOpen_rectangle a b)
  have hFQdom : IsHomeoExtension f Q.dom (f '' Q.dom) (OnePoint.map f) :=
    (image_isJordanDomain_of_open hDo hfconf.1.continuousOn hfconf.2.1 hQdomclosure hfo).2.1
  have htoExt' : ∀ S : Set ℂ, OnePoint.map f '' toExt S = toExt (f '' S) := fun S => by
    simp only [toExt, image_image]
    rfl
  have hnormeq : ∀ z : ℂ, ‖f z‖ = Real.exp (z.re + Real.log (1 + ε)) := fun z => by
    rw [hf_def]
    simp only
    rw [Complex.norm_exp, Complex.add_re, hcre]
  have hexpa : Real.exp (a + Real.log (1 + ε)) = R - ε := by
    have he : a + Real.log (1 + ε) = Real.log (R - ε) := by rw [ha_def]; ring
    rw [he, Real.exp_log hRε]
  have hexp0 : Real.exp ((0 : ℝ) + Real.log (1 + ε)) = 1 + ε := by
    rw [zero_add, Real.exp_log h1ε]
  refine ⟨Q', ?_, ?_, ?_, ?_⟩
  · -- closure (toExt Q'.dom) ⊆ toExt (annulus 1 R)
    have hbound : f '' rectangle a b ⊆ {z : ℂ | 1 + ε ≤ ‖z‖ ∧ ‖z‖ ≤ R - ε} := by
      rintro _ ⟨ζ, hζ, rfl⟩
      have h1 : 1 + ε ≤ ‖f ζ‖ := by
        rw [hnormeq]
        calc (1 : ℝ) + ε = Real.exp (Real.log (1 + ε)) := (Real.exp_log h1ε).symm
          _ ≤ Real.exp (ζ.re + Real.log (1 + ε)) := Real.exp_le_exp.2 (by linarith [hζ.1])
      have h2 : ‖f ζ‖ ≤ R - ε := by
        rw [hnormeq]
        calc Real.exp (ζ.re + Real.log (1 + ε)) ≤ Real.exp (a + Real.log (1 + ε)) :=
              Real.exp_le_exp.2 (by linarith [hζ.2.1])
          _ = R - ε := hexpa
      exact ⟨h1, h2⟩
    have hclosed : IsClosed {z : ℂ | 1 + ε ≤ ‖z‖ ∧ ‖z‖ ≤ R - ε} :=
      (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    have hbdd : Bornology.IsBounded (f '' rectangle a b) :=
      Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R - ε))
        (fun z hz => by rw [mem_closedBall_zero_iff]; exact (hbound hz).2)
    have hQ'dom : Q'.dom = f '' rectangle a b := hQ'img.1
    rw [hQ'dom, closure_toExt_of_isBounded hbdd]
    rintro _ ⟨z, hz, rfl⟩
    have hzb := closure_minimal hbound hclosed hz
    refine ⟨z, ⟨?_, ?_⟩, rfl⟩
    · have h1 : (1 : ℝ) < 1 + ε := by linarith
      calc (1 : ℝ) < 1 + ε := h1
        _ ≤ ‖z‖ := hzb.1
    · calc ‖z‖ ≤ R - ε := hzb.2
        _ < R := by linarith
  · -- modulus
    rw [← thm1_3_modulus_conformal_invariant hQ'ce]
    exact modulus_rectQuad ha hb
  · -- side 1
    have hside1 : Q'.side 1 = OnePoint.map f '' Q.side 1 := by
      rw [Q'.side_eq_boundaryArc, hQ'img.1]
      simp only [hQ'img.2]
      exact (TopQuad.image_side hfo hfQdom hFQdom 1).symm
    have hQside1 : Q.side 1 = toExt (({a} : Set ℝ) ×ℂ Icc (0 : ℝ) b) :=
      aqc_boundaryArc_frontier_toExt_rectangle_right ha hb
    rw [hside1, hQside1, htoExt']
    rintro _ ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    rw [mem_reProdIm, mem_singleton_iff] at hv
    refine ⟨f v, ?_, rfl⟩
    rw [Metric.mem_sphere, Complex.dist_eq, sub_zero, hnormeq, hv.1]
    exact hexpa
  · -- side 3
    have hside3 : Q'.side 3 = OnePoint.map f '' Q.side 3 := by
      rw [Q'.side_eq_boundaryArc, hQ'img.1]
      simp only [hQ'img.2]
      exact (TopQuad.image_side hfo hfQdom hFQdom 3).symm
    have hQside3 : Q.side 3 = toExt (({0} : Set ℝ) ×ℂ Icc (0 : ℝ) b) :=
      aqc_boundaryArc_frontier_toExt_rectangle_left ha hb
    rw [hside3, hQside3, htoExt']
    rintro _ ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    rw [mem_reProdIm, mem_singleton_iff] at hv
    refine ⟨f v, ?_, rfl⟩
    rw [Metric.mem_sphere, Complex.dist_eq, sub_zero, hnormeq, hv.1]
    exact hexp0

/-! ### Piece B -/

/-- `d/dt log‖γ(t)‖ = Re(γ'(t)/γ(t))` wherever `γ` is differentiable and nonzero. -/
theorem aqc_hasDerivAt_log_norm {γ : ℝ → ℂ} {t : ℝ} {γ' : ℂ} (hγ0 : γ t ≠ 0)
    (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => Real.log ‖γ s‖) (γ' / γ t).re t := by
  have hd : HasDerivAt (fun s => γ s / γ t) (γ' / γ t) t := hγ.div_const _
  have hlog := hd.clog_real (by rw [div_self hγ0]; exact one_mem_slitPlane)
  rw [div_self hγ0, div_one] at hlog
  have hre : HasDerivAt (fun s => (Complex.log (γ s / γ t)).re) (γ' / γ t).re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hlog
  have hev : (fun s => (Complex.log (γ s / γ t)).re) =ᶠ[𝓝 t]
      fun s => Real.log ‖γ s‖ - Real.log ‖γ t‖ := by
    filter_upwards [(hγ.continuousAt.eventually_ne hγ0)] with s hs
    rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hs) (norm_ne_zero_iff.2 hγ0)]
  have := hre.congr_of_eventuallyEq hev.symm
  simpa using this.add_const (Real.log ‖γ t‖)

/-- `Real.log` is Lipschitz on `[m, ∞)` for `m > 0`, with constant `1/m`. -/
theorem aqc_log_lipschitzOnWith (m : ℝ) (hm : 0 < m) :
    LipschitzOnWith (1/m).toNNReal Real.log (Set.Ici m) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le (f := Real.log) (s := Set.Ici m)
  · intro x hx
    simp only [mem_Ici] at hx
    exact (Real.hasDerivAt_log (by linarith)).differentiableAt
  · intro x hx
    simp only [mem_Ici] at hx
    have hx0 : (0:ℝ) < x := by linarith
    rw [Real.deriv_log, ← Real.toNNReal_eq_nnnorm_of_nonneg (by positivity : (0:ℝ) ≤ x⁻¹),
      inv_eq_one_div]
    exact Real.toNNReal_mono (one_div_le_one_div_of_le hm hx)
  · exact convex_Ici m

/-- A continuous nonvanishing curve on a compact interval has a positive lower bound on its
norm. -/
theorem aqc_exists_min_norm {γ : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t) (hcont : ContinuousOn γ (Icc s t))
    (hne : ∀ u ∈ Icc s t, γ u ≠ 0) : ∃ m : ℝ, 0 < m ∧ ∀ u ∈ Icc s t, m ≤ ‖γ u‖ := by
  obtain ⟨a, ha, hamin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hst) hcont.norm
  exact ⟨‖γ a‖, norm_pos_iff.2 (hne a ha), fun u hu => isMinOn_iff.1 hamin u hu⟩

/-- Interior form of the radial estimate: for `s ≤ t` strictly inside `(0,1)`. -/
theorem aqc_enorm_log_norm_sub_le_rhoLength_interior (γ : LRCurve)
    (hne : ∀ t ∈ Ioo (0:ℝ) 1, γ.toFun t ≠ 0) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht1 : t < 1) :
    ‖Real.log ‖γ.toFun t‖ - Real.log ‖γ.toFun s‖‖ₑ ≤
      γ.rhoLength (fun z => ENNReal.ofReal (1 / ‖z‖)) := by
  have hA := LocallyLipschitzOn.ae_differentiableAt_Ioo γ.locallyLipschitzOn
  have hrho : γ.rhoLength (fun z => ENNReal.ofReal (1 / ‖z‖)) =
      ∫⁻ u in Ioo 0 1, ENNReal.ofReal (1 / ‖γ.toFun u‖) * ‖deriv γ.toFun u‖ₑ := by
    simp [LRCurve.rhoLength]
  have hsub : Icc s t ⊆ Ioo 0 1 := Icc_subset_Ioo hs ht1
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
    (LocallyLipschitzOn.mono γ.locallyLipschitzOn hsub)
  have hneIcc : ∀ u ∈ Icc s t, γ.toFun u ≠ 0 := fun u hu => hne u (hsub hu)
  obtain ⟨m, hm0, hmb⟩ := aqc_exists_min_norm hst hK.continuousOn hneIcc
  have hnormLip : LipschitzOnWith K (fun u => ‖γ.toFun u‖) (Icc s t) := by
    rw [lipschitzOnWith_iff_dist_le_mul] at hK ⊢
    intro x hx y hy
    calc dist ‖γ.toFun x‖ ‖γ.toFun y‖ ≤ dist (γ.toFun x) (γ.toFun y) := by
          rw [Real.dist_eq, Complex.dist_eq]; exact abs_norm_sub_norm_le _ _
      _ ≤ K * dist x y := hK x hx y hy
  have hmaps : Set.MapsTo (fun u => ‖γ.toFun u‖) (Icc s t) (Set.Ici m) := fun u hu => hmb u hu
  have hKL : LipschitzOnWith ((1/m).toNNReal * K) (fun u => Real.log ‖γ.toFun u‖) (uIcc s t) := by
    rw [uIcc_of_le hst]
    exact (aqc_log_lipschitzOnWith m hm0).comp hnormLip hmaps
  have hftc : ∫ u in s..t, deriv (fun u => Real.log ‖γ.toFun u‖) u =
      Real.log ‖γ.toFun t‖ - Real.log ‖γ.toFun s‖ :=
    hKL.absolutelyContinuousOnInterval.integral_deriv_eq_sub
  rw [← hftc, intervalIntegral.integral_of_le hst, hrho]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ u in Ioc s t, ‖deriv (fun u => Real.log ‖γ.toFun u‖) u‖ₑ
      ≤ ∫⁻ u in Ioc s t, ENNReal.ofReal (1 / ‖γ.toFun u‖) * ‖deriv γ.toFun u‖ₑ := by
        refine setLIntegral_mono_ae' measurableSet_Ioc ?_
        filter_upwards [hA] with u hu huI
        have hu01 : u ∈ Ioo (0:ℝ) 1 := ⟨hs.trans huI.1, huI.2.trans_lt ht1⟩
        have hune : γ.toFun u ≠ 0 := hne u hu01
        have hd : HasDerivAt (fun u => Real.log ‖γ.toFun u‖) (deriv γ.toFun u / γ.toFun u).re u :=
          aqc_hasDerivAt_log_norm hune (hu hu01).hasDerivAt
        rw [hd.deriv, ← ofReal_norm]
        have hbound : |(deriv γ.toFun u / γ.toFun u).re| ≤ ‖deriv γ.toFun u‖ / ‖γ.toFun u‖ := by
          rw [← norm_div]; exact Complex.abs_re_le_norm _
        calc ENNReal.ofReal |(deriv γ.toFun u / γ.toFun u).re|
            ≤ ENNReal.ofReal (‖deriv γ.toFun u‖ / ‖γ.toFun u‖) := ENNReal.ofReal_le_ofReal hbound
          _ = ENNReal.ofReal (1 / ‖γ.toFun u‖) * ‖deriv γ.toFun u‖ₑ := by
              rw [← ofReal_norm (deriv γ.toFun u), div_eq_mul_one_div, mul_comm,
                ENNReal.ofReal_mul (by positivity)]
    _ ≤ ∫⁻ u in Ioo 0 1, ENNReal.ofReal (1 / ‖γ.toFun u‖) * ‖deriv γ.toFun u‖ₑ :=
        lintegral_mono_set fun u hu => ⟨hs.trans hu.1, hu.2.trans_lt ht1⟩

/-- **B (owner -46).** Radial estimate: a locally rectifiable curve avoiding `0`, with limits `p`
at `0⁺` and `q` at `1⁻`, has `1/|z|`-length at least `|ln|q| − ln|p||`. -/
theorem aqc_abs_log_norm_sub_le_rhoLength {γ : LRCurve} {p q : ℂ} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hne : ∀ t ∈ Ioo (0 : ℝ) 1, γ.toFun t ≠ 0)
    (hp : Tendsto γ.toFun (𝓝[>] 0) (𝓝 p)) (hq : Tendsto γ.toFun (𝓝[<] 1) (𝓝 q)) :
    ENNReal.ofReal |Real.log ‖q‖ - Real.log ‖p‖| ≤
      γ.rhoLength (fun z => ENNReal.ofReal (1 / ‖z‖)) := by
  have hlim0 : Tendsto (fun s => Real.log ‖γ.toFun s‖) (𝓝[>] 0) (𝓝 (Real.log ‖p‖)) :=
    ((Real.continuousAt_log (norm_ne_zero_iff.2 hp0)).comp
      continuous_norm.continuousAt).tendsto.comp hp
  have hlim1 : Tendsto (fun s => Real.log ‖γ.toFun s‖) (𝓝[<] 1) (𝓝 (Real.log ‖q‖)) :=
    ((Real.continuousAt_log (norm_ne_zero_iff.2 hq0)).comp
      continuous_norm.continuousAt).tendsto.comp hq
  have step : ∀ s : ℝ, 0 < s → s < 1 →
      ‖Real.log ‖q‖ - Real.log ‖γ.toFun s‖‖ₑ ≤ γ.rhoLength (fun z => ENNReal.ofReal (1 / ‖z‖)) := by
    intro s hs hs1
    have ht : Tendsto (fun t => ‖Real.log ‖γ.toFun t‖ - Real.log ‖γ.toFun s‖‖ₑ) (𝓝[<] 1)
        (𝓝 ‖Real.log ‖q‖ - Real.log ‖γ.toFun s‖‖ₑ) :=
      (continuous_enorm.tendsto _).comp (hlim1.sub_const _)
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hs1] with t ht'
    exact aqc_enorm_log_norm_sub_le_rhoLength_interior γ hne hs ht'.1.le ht'.2
  have hstep0 : Tendsto (fun s => ‖Real.log ‖q‖ - Real.log ‖γ.toFun s‖‖ₑ) (𝓝[>] 0)
      (𝓝 ‖Real.log ‖q‖ - Real.log ‖p‖‖ₑ) :=
    (continuous_enorm.tendsto _).comp (tendsto_const_nhds.sub hlim0)
  have hfinal : ‖Real.log ‖q‖ - Real.log ‖p‖‖ₑ ≤
      γ.rhoLength (fun z => ENNReal.ofReal (1 / ‖z‖)) := by
    refine le_of_tendsto hstep0 ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with s hs'
    exact step s hs'.1 hs'.2
  rwa [← ofReal_norm, Real.norm_eq_abs] at hfinal

/-! ### Piece C -/

/-- Polar-coordinate preconnectedness, generalizing `isPreconnected_annulus`: any radially
described region `{z | ‖z‖ ∈ s}` for `s ⊆ ℝ` preconnected is preconnected. -/
theorem aqc_isPreconnected_polar {s : Set ℝ} (hs : IsPreconnected s) (hs0 : ∀ r ∈ s, 0 ≤ r) :
    IsPreconnected {z : ℂ | ‖z‖ ∈ s} := by
  have hmap : (fun p : ℝ × ℝ => (p.1 : ℂ) * exp ((p.2 : ℂ) * I)) '' (s ×ˢ (univ : Set ℝ))
      = {z : ℂ | ‖z‖ ∈ s} := by
    apply Subset.antisymm
    · rintro _ ⟨⟨ρ, θ⟩, ⟨hρ, -⟩, rfl⟩
      show ‖(ρ : ℂ) * exp ((θ : ℂ) * I)‖ ∈ s
      rwa [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hs0 ρ hρ)]
    · intro z hz
      exact ⟨(‖z‖, arg z), ⟨hz, mem_univ _⟩, Complex.norm_mul_exp_arg_mul_I z⟩
  have hu : IsPreconnected (univ : Set ℝ) := isPreconnected_univ
  rw [← hmap]
  exact (hs.prod hu).image (fun p : ℝ × ℝ => (p.1 : ℂ) * exp ((p.2 : ℂ) * I))
    (by fun_prop)

/-- Extract a margin `ε₀` witnessing that a nonempty compact subset of an open annulus stays
strictly inside a slightly smaller closed annulus. -/
theorem aqc_exists_eps_of_compact_subset_annulus {R : ℝ} (hR : 1 < R) {C : Set ℂ}
    (hC : IsCompact C) (hCA : C ⊆ annulus 1 R) (hCne : C.Nonempty) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ 2 * ε₀ < R - 1 ∧
      C ⊆ {z : ℂ | 1 + ε₀ ≤ ‖z‖ ∧ ‖z‖ ≤ R - ε₀} := by
  obtain ⟨zmin, hzminC, hzmin⟩ := hC.exists_isMinOn hCne continuous_norm.continuousOn
  obtain ⟨zmax, hzmaxC, hzmax⟩ := hC.exists_isMaxOn hCne continuous_norm.continuousOn
  have h1 : 1 < ‖zmin‖ := (hCA hzminC).1
  have h2 : ‖zmax‖ < R := (hCA hzmaxC).2
  set ε₀ : ℝ := min (min ((‖zmin‖ - 1) / 2) ((R - ‖zmax‖) / 2)) ((R - 1) / 4) with hε₀def
  have hε₀pos : 0 < ε₀ := by
    refine lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hε₀R : 2 * ε₀ < R - 1 := by
    have : ε₀ ≤ (R - 1) / 4 := min_le_right _ _
    linarith
  refine ⟨ε₀, hε₀pos, hε₀R, fun z hz => ?_⟩
  have hzmin' : ε₀ ≤ (‖zmin‖ - 1) / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hzmax' : ε₀ ≤ (R - ‖zmax‖) / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hle1 : ‖zmin‖ ≤ ‖z‖ := hzmin hz
  have hle2 : ‖z‖ ≤ ‖zmax‖ := hzmax hz
  exact ⟨by linarith, by linarith⟩

/-- **C.** Collars: for a homeomorphism `g` of `{1<|z|<R}` onto `{1<|w|<R'}` and every `0 < δ`
with `2δ < R'−1`, the images of the circles `|z| = 1+ε`, `|z| = R−ε` lie in *different* collars
`{1<|w|<1+δ}`, `{R'−δ<|w|<R'}` for all sufficiently small `ε`. -/
theorem aqc_exists_collar {R R' : ℝ} (hR : 1 < R) (hR' : 1 < R') {g : ℂ → ℂ}
    (hg : IsHomeomorphOnto g (annulus 1 R) (annulus 1 R')) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : 2 * δ < R' - 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ 2 * ε₀ < R - 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (g '' sphere (0 : ℂ) (1 + ε) ⊆ annulus 1 (1 + δ) ∧
        g '' sphere (0 : ℂ) (R - ε) ⊆ annulus (R' - δ) R') ∨
      (g '' sphere (0 : ℂ) (1 + ε) ⊆ annulus (R' - δ) R' ∧
        g '' sphere (0 : ℂ) (R - ε) ⊆ annulus 1 (1 + δ)) := by
  obtain ⟨hgc, hginj, hgimg, hginv⟩ := hg
  have hsurj : SurjOn g (annulus 1 R) (annulus 1 R') := hgimg.symm ▸ Set.surjOn_image g _
  set Kδ : Set ℂ := {w : ℂ | 1 + δ ≤ ‖w‖ ∧ ‖w‖ ≤ R' - δ} with hKδdef
  have hKδA' : Kδ ⊆ annulus 1 R' := fun w hw => ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hKδcompact : IsCompact Kδ := by
    have h1 : IsClosed {w : ℂ | 1 + δ ≤ ‖w‖} := isClosed_le continuous_const continuous_norm
    have heq : Kδ = {w : ℂ | 1 + δ ≤ ‖w‖} ∩ closedBall (0 : ℂ) (R' - δ) := by
      ext w
      simp only [hKδdef, mem_setOf_eq, mem_inter_iff, mem_closedBall, dist_zero_right]
    rw [heq]
    exact (isCompact_closedBall (0 : ℂ) (R' - δ)).inter_left h1
  have hKδne : Kδ.Nonempty := ⟨((1 + δ : ℝ) : ℂ), by
    simp only [hKδdef, mem_setOf_eq, Complex.norm_real, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1+δ)]
    exact ⟨le_refl _, by linarith⟩⟩
  set C : Set ℂ := (Function.invFunOn g (annulus 1 R)) '' Kδ with hCdef
  have hCcompact : IsCompact C :=
    hKδcompact.image_of_continuousOn (hginv.mono hKδA')
  have hCA : C ⊆ annulus 1 R := by
    rintro z ⟨w, hwKδ, rfl⟩
    exact Function.invFunOn_mem (hsurj (hKδA' hwKδ))
  have hCne : C.Nonempty := hKδne.image _
  obtain ⟨ε₀, hε₀pos, hε₀R, hCε₀⟩ := aqc_exists_eps_of_compact_subset_annulus hR hCcompact hCA hCne
  refine ⟨ε₀, hε₀pos, hε₀R, fun ε hε0 hεε₀ => ?_⟩
  -- both circles, and the two source collars, avoid the preimage-margin, hence avoid `Kδ`
  have hRε₀ : ε₀ < R - 1 := by linarith
  have hεR1 : ε < R - 1 := hεε₀.trans hRε₀
  have hnotC : ∀ z : ℂ, ‖z‖ < 1 + ε₀ ∨ R - ε₀ < ‖z‖ → z ∉ C := by
    intro z hz hzC
    have := hCε₀ hzC
    rcases hz with hz | hz <;> linarith [this.1, this.2]
  have hgAvoid : ∀ z ∈ annulus 1 R, ‖z‖ < 1 + ε₀ ∨ R - ε₀ < ‖z‖ → g z ∉ Kδ := by
    intro z hzA hz hgzKδ
    have hzC : z ∈ C := by
      refine ⟨g z, hgzKδ, ?_⟩
      exact hginj.leftInvOn_invFunOn hzA
    exact hnotC z hz hzC
  -- (i) the two circles individually avoid `Kδ`
  have hcirc1 : g '' sphere (0 : ℂ) (1 + ε) ∩ Kδ = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro w ⟨⟨z, hzsph, rfl⟩, hwKδ⟩
    have hzA : z ∈ annulus 1 R := by
      simp only [mem_sphere_iff_norm, sub_zero] at hzsph
      exact ⟨by rw [hzsph]; linarith, by rw [hzsph]; linarith⟩
    have hznorm : ‖z‖ < 1 + ε₀ := by
      simp only [mem_sphere_iff_norm, sub_zero] at hzsph
      rw [hzsph]; linarith
    exact hgAvoid z hzA (Or.inl hznorm) hwKδ
  have hcirc2 : g '' sphere (0 : ℂ) (R - ε) ∩ Kδ = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro w ⟨⟨z, hzsph, rfl⟩, hwKδ⟩
    have hzA : z ∈ annulus 1 R := by
      simp only [mem_sphere_iff_norm, sub_zero] at hzsph
      exact ⟨by rw [hzsph]; linarith, by rw [hzsph]; linarith⟩
    have hznorm : R - ε₀ < ‖z‖ := by
      simp only [mem_sphere_iff_norm, sub_zero] at hzsph
      rw [hzsph]; linarith
    exact hgAvoid z hzA (Or.inr hznorm) hwKδ
  -- (ii) the two source collars individually avoid `Kδ`
  have hcol1 : g '' annulus 1 (1 + ε) ∩ Kδ = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro w ⟨⟨z, hzann, rfl⟩, hwKδ⟩
    have hzA : z ∈ annulus 1 R := ⟨hzann.1, by linarith [hzann.2]⟩
    exact hgAvoid z hzA (Or.inl (by linarith [hzann.2])) hwKδ
  have hcol2 : g '' annulus (R - ε) R ∩ Kδ = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro w ⟨⟨z, hzann, rfl⟩, hwKδ⟩
    have hzA : z ∈ annulus 1 R := ⟨by linarith [hzann.1], hzann.2⟩
    exact hgAvoid z hzA (Or.inr (by linarith [hzann.1])) hwKδ
  -- (iii) the two "half-open collars" (annulus + its outer circle) avoid `Kδ` too
  have hhalf1 : g '' {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ ≤ 1 + ε} ∩ Kδ = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro w ⟨⟨z, hzann, rfl⟩, hwKδ⟩
    have hzA : z ∈ annulus 1 R := ⟨hzann.1, by linarith [hzann.2]⟩
    exact hgAvoid z hzA (Or.inl (by linarith [hzann.2])) hwKδ
  have hhalf2 : g '' {z : ℂ | R - ε ≤ ‖z‖ ∧ ‖z‖ < R} ∩ Kδ = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro w ⟨⟨z, hzann, rfl⟩, hwKδ⟩
    have hzA : z ∈ annulus 1 R := ⟨by linarith [hzann.1], hzann.2⟩
    exact hgAvoid z hzA (Or.inr (by linarith [hzann.1])) hwKδ
  -- connectivity of source pieces
  have hIconn : IsPreconnected {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ ≤ 1 + ε} := by
    have heq : {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ ≤ 1 + ε} = {z : ℂ | ‖z‖ ∈ Ioc (1:ℝ) (1 + ε)} := by
      ext z; simp only [mem_setOf_eq, mem_Ioc]
    rw [heq]
    exact aqc_isPreconnected_polar isPreconnected_Ioc (fun r hr => by linarith [hr.1])
  have hOconn : IsPreconnected {z : ℂ | R - ε ≤ ‖z‖ ∧ ‖z‖ < R} := by
    have heq : {z : ℂ | R - ε ≤ ‖z‖ ∧ ‖z‖ < R} = {z : ℂ | ‖z‖ ∈ Ico (R - ε) R} := by
      ext z; simp only [mem_setOf_eq, mem_Ico]
    rw [heq]
    exact aqc_isPreconnected_polar isPreconnected_Ico (fun r hr => by linarith [hr.1])
  have hsphereconn : ∀ r : ℝ, 0 ≤ r → IsPreconnected (sphere (0 : ℂ) r) := by
    intro r hr
    have heq : sphere (0 : ℂ) r = {z : ℂ | ‖z‖ ∈ ({r} : Set ℝ)} := by
      ext z; simp [mem_sphere_iff_norm]
    rw [heq]
    exact aqc_isPreconnected_polar isPreconnected_singleton (by simpa using hr)
  -- images and their disjointness from `Kδ`
  have hIsub : {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ ≤ 1 + ε} ⊆ annulus 1 R := fun z hz => ⟨hz.1, by linarith [hz.2]⟩
  have hOsub : {z : ℂ | R - ε ≤ ‖z‖ ∧ ‖z‖ < R} ⊆ annulus 1 R := fun z hz => ⟨by linarith [hz.1], hz.2⟩
  have hsph1sub : sphere (0 : ℂ) (1 + ε) ⊆ annulus 1 R := by
    intro z hz
    simp only [mem_sphere_iff_norm, sub_zero] at hz
    exact ⟨by rw [hz]; linarith, by rw [hz]; linarith⟩
  have hsph2sub : sphere (0 : ℂ) (R - ε) ⊆ annulus 1 R := by
    intro z hz
    simp only [mem_sphere_iff_norm, sub_zero] at hz
    exact ⟨by rw [hz]; linarith, by rw [hz]; linarith⟩
  -- `I'`, `O'` collars are open and disjoint
  have hI'open : IsOpen (annulus 1 (1 + δ)) := isOpen_annulus _ _
  have hO'open : IsOpen (annulus (R' - δ) R') := isOpen_annulus _ _
  have hIOdisj : Disjoint (annulus 1 (1 + δ)) (annulus (R' - δ) R') := by
    rw [Set.disjoint_left]
    rintro z ⟨-, hz1⟩ ⟨hz2, -⟩
    linarith
  have hAminusKδ : ∀ w : ℂ, w ∈ annulus 1 R' → w ∉ Kδ →
      w ∈ annulus 1 (1 + δ) ∨ w ∈ annulus (R' - δ) R' := by
    intro w hwA' hwKδ
    simp only [hKδdef, mem_setOf_eq, not_and_or, not_le] at hwKδ
    rcases hwKδ with hw | hw
    · exact Or.inl ⟨hwA'.1, hw⟩
    · exact Or.inr ⟨hw, hwA'.2⟩
  have hsubIO : ∀ s : Set ℂ, s ⊆ annulus 1 R → g '' s ∩ Kδ = ∅ →
      g '' s ⊆ annulus 1 (1 + δ) ∪ annulus (R' - δ) R' := by
    intro s hsA hsK w hw
    obtain ⟨z, hzs, rfl⟩ := hw
    have hzA : z ∈ annulus 1 R := hsA hzs
    have hgzA' : g z ∈ annulus 1 R' := hgimg ▸ mem_image_of_mem g hzA
    have hgzK : g z ∉ Kδ := by
      intro hmem
      exact absurd (mem_inter (mem_image_of_mem g hzs) hmem) (by rw [hsK]; exact notMem_empty _)
    exact hAminusKδ (g z) hgzA' hgzK
  have hIorO : ∀ s : Set ℂ, IsPreconnected s → s ⊆ annulus 1 R → g '' s ∩ Kδ = ∅ →
      g '' s ⊆ annulus 1 (1 + δ) ∨ g '' s ⊆ annulus (R' - δ) R' :=
    fun s hsc hsA hsK => (hsc.image g (hgc.mono hsA)).subset_or_subset hI'open hO'open
      hIOdisj (hsubIO s hsA hsK)
  -- sync: the circle and the half-open collar containing it fall in the same piece
  have hunion1 : g '' {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ ≤ 1 + ε} =
      g '' annulus 1 (1 + ε) ∪ g '' sphere (0 : ℂ) (1 + ε) := by
    rw [← image_union]
    congr 1
    ext z
    simp only [mem_setOf_eq, mem_union, annulus, mem_sphere_iff_norm, sub_zero]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h2 with h2 | h2
      · exact Or.inr h2
      · exact Or.inl ⟨h1, h2⟩
    · rintro (⟨h1, h2⟩ | h2)
      · exact ⟨h1, h2.le⟩
      · exact ⟨by rw [h2]; linarith, h2.le⟩
  have hunion2 : g '' {z : ℂ | R - ε ≤ ‖z‖ ∧ ‖z‖ < R} =
      g '' annulus (R - ε) R ∪ g '' sphere (0 : ℂ) (R - ε) := by
    rw [← image_union]
    congr 1
    ext z
    simp only [mem_setOf_eq, mem_union, annulus, mem_sphere_iff_norm, sub_zero]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h1 with h1 | h1
      · exact Or.inr h1.symm
      · exact Or.inl ⟨h1, h2⟩
    · rintro (⟨h1, h2⟩ | h1)
      · exact ⟨h1.le, h2⟩
      · exact ⟨h1.ge, by rw [h1]; linarith⟩
  have hsync1 : (g '' annulus 1 (1 + ε) ⊆ annulus 1 (1 + δ) ∧
        g '' sphere (0 : ℂ) (1 + ε) ⊆ annulus 1 (1 + δ)) ∨
      (g '' annulus 1 (1 + ε) ⊆ annulus (R' - δ) R' ∧
        g '' sphere (0 : ℂ) (1 + ε) ⊆ annulus (R' - δ) R') := by
    have h := hIorO _ hIconn hIsub hhalf1
    rw [hunion1] at h
    rcases h with h | h
    · exact Or.inl (union_subset_iff.mp h)
    · exact Or.inr (union_subset_iff.mp h)
  have hsync2 : (g '' annulus (R - ε) R ⊆ annulus 1 (1 + δ) ∧
        g '' sphere (0 : ℂ) (R - ε) ⊆ annulus 1 (1 + δ)) ∨
      (g '' annulus (R - ε) R ⊆ annulus (R' - δ) R' ∧
        g '' sphere (0 : ℂ) (R - ε) ⊆ annulus (R' - δ) R') := by
    have h := hIorO _ hOconn hOsub hhalf2
    rw [hunion2] at h
    rcases h with h | h
    · exact Or.inl (union_subset_iff.mp h)
    · exact Or.inr (union_subset_iff.mp h)
  -- the partition `A' = U₁ ⊔ Mε ⊔ U₂`
  have hABCeq : annulus 1 (1 + ε) ∪ {z : ℂ | 1 + ε ≤ ‖z‖ ∧ ‖z‖ ≤ R - ε} ∪ annulus (R - ε) R =
      annulus 1 R := by
    ext z
    simp only [annulus, mem_setOf_eq, mem_union]
    constructor
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨by linarith, by linarith⟩
      · exact ⟨by linarith, h2⟩
    · rintro ⟨h1, h2⟩
      rcases lt_or_ge (‖z‖) (1 + ε) with h | h
      · exact Or.inl (Or.inl ⟨h1, h⟩)
      · rcases lt_or_ge (R - ε) (‖z‖) with h' | h'
        · exact Or.inr ⟨h', h2⟩
        · exact Or.inl (Or.inr ⟨h, h'⟩)
  have hpartition : annulus 1 R' = g '' annulus 1 (1 + ε) ∪
      g '' {z : ℂ | 1 + ε ≤ ‖z‖ ∧ ‖z‖ ≤ R - ε} ∪ g '' annulus (R - ε) R := by
    rw [← image_union, ← image_union, hABCeq, hgimg]
  have hMεsub : {z : ℂ | 1 + ε ≤ ‖z‖ ∧ ‖z‖ ≤ R - ε} ⊆ annulus 1 R := fun z hz =>
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  set Mε : Set ℂ := g '' {z : ℂ | 1 + ε ≤ ‖z‖ ∧ ‖z‖ ≤ R - ε} with hMεdef
  have hMεcompact : IsCompact Mε := by
    have hcpt : IsCompact {z : ℂ | 1 + ε ≤ ‖z‖ ∧ ‖z‖ ≤ R - ε} := by
      have h1 : IsClosed {z : ℂ | 1 + ε ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
      have heq : {z : ℂ | 1 + ε ≤ ‖z‖ ∧ ‖z‖ ≤ R - ε} =
          {z : ℂ | 1 + ε ≤ ‖z‖} ∩ closedBall (0 : ℂ) (R - ε) := by
        ext z; simp only [mem_setOf_eq, mem_inter_iff, mem_closedBall, dist_zero_right]
      rw [heq]
      exact (isCompact_closedBall (0 : ℂ) (R - ε)).inter_left h1
    exact hcpt.image_of_continuousOn (hgc.mono hMεsub)
  have hMεA' : Mε ⊆ annulus 1 R' := by
    rw [hMεdef, ← hgimg]; exact image_mono hMεsub
  -- key closure fact: neither `I'` nor `O'` can be a subset of `Mε` (compact, hence closed,
  -- and `⊆ annulus 1 R'`, an OPEN set whose boundary circles it cannot reach)
  have hOnotSub : ¬ (annulus (R' - δ) R' ⊆ Mε) := by
    intro hsub
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hseq : Tendsto (fun n : ℕ => ((R' - 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((R' : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto R').comp (by simpa using tendsto_const_nhds.sub h0)
    have hevent : ∀ᶠ n : ℕ in atTop, ((R' - 1 / ((n : ℝ) + 1) : ℝ) : ℂ) ∈ Mε := by
      filter_upwards [h0.eventually (gt_mem_nhds hδ)] with n hn
      apply hsub
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hnorm : ‖((R' - 1 / ((n : ℝ) + 1) : ℝ) : ℂ)‖ = R' - 1 / ((n : ℝ) + 1) := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      refine ⟨by rw [hnorm]; linarith, by rw [hnorm]; linarith⟩
    have hlim : ((R' : ℝ) : ℂ) ∈ Mε := hMεcompact.isClosed.mem_of_tendsto hseq hevent
    have hmem := hMεA' hlim
    simp only [annulus, mem_setOf_eq] at hmem
    have hnormR' : ‖((R' : ℝ) : ℂ)‖ = R' := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [hnormR'] at hmem
    exact absurd hmem.2 (lt_irrefl R')
  have hInotSub : ¬ (annulus 1 (1 + δ) ⊆ Mε) := by
    intro hsub
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hseq : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).comp (by simpa using tendsto_const_nhds.add h0)
    have hevent : ∀ᶠ n : ℕ in atTop, ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) ∈ Mε := by
      filter_upwards [h0.eventually (gt_mem_nhds hδ)] with n hn
      apply hsub
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hnorm : ‖((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)‖ = 1 + 1 / ((n : ℝ) + 1) := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      refine ⟨by rw [hnorm]; linarith, by rw [hnorm]; linarith⟩
    have hlim : ((1 : ℝ) : ℂ) ∈ Mε := hMεcompact.isClosed.mem_of_tendsto hseq hevent
    have hmem := hMεA' hlim
    simp only [annulus, mem_setOf_eq] at hmem
    have hnorm1 : ‖((1 : ℝ) : ℂ)‖ = 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
    rw [hnorm1] at hmem
    exact absurd hmem.1 (lt_irrefl 1)
  -- assemble: rule out "both circles in the same collar"
  -- generic extraction: given the circle's collar, the disjunction pins down the matching collar
  -- for the source-side piece it was synced with
  have hextract : ∀ (U S1 S2 T : Set ℂ), T.Nonempty → Disjoint S1 S2 →
      ((U ⊆ S1 ∧ T ⊆ S1) ∨ (U ⊆ S2 ∧ T ⊆ S2)) → T ⊆ S1 → U ⊆ S1 := by
    rintro U S1 S2 T ⟨x, hx⟩ hdisj (⟨hu, -⟩ | ⟨hu, ht⟩) hT
    · exact hu
    · exact absurd (ht hx) (Set.disjoint_left.mp hdisj (hT hx))
  have hne1 : (sphere (0 : ℂ) (1 + ε)).Nonempty := NormedSpace.sphere_nonempty.mpr (by linarith)
  have hne2 : (sphere (0 : ℂ) (R - ε)).Nonempty := NormedSpace.sphere_nonempty.mpr (by linarith)
  have hR'δ1 : 1 < R' - δ := by linarith
  have hOsubA' : annulus (R' - δ) R' ⊆ annulus 1 R' := fun w hw => ⟨by linarith [hw.1], hw.2⟩
  have hIsubA' : annulus 1 (1 + δ) ⊆ annulus 1 R' := fun w hw => ⟨hw.1, by linarith [hw.2]⟩
  have hnotBothI : ¬ (g '' sphere (0 : ℂ) (1 + ε) ⊆ annulus 1 (1 + δ) ∧
      g '' sphere (0 : ℂ) (R - ε) ⊆ annulus 1 (1 + δ)) := by
    rintro ⟨h1, h2⟩
    apply hOnotSub
    have hU1 : g '' annulus 1 (1 + ε) ⊆ annulus 1 (1 + δ) :=
      hextract _ _ _ _ (hne1.image g) hIOdisj hsync1 h1
    have hU2 : g '' annulus (R - ε) R ⊆ annulus 1 (1 + δ) :=
      hextract _ _ _ _ (hne2.image g) hIOdisj hsync2 h2
    have hsplit : annulus (R' - δ) R' ⊆
        g '' annulus 1 (1 + ε) ∪ Mε ∪ g '' annulus (R - ε) R := hpartition ▸ hOsubA'
    intro w hw
    rcases hsplit hw with (h | h) | h
    · exact absurd (hU1 h) (fun hc => hIOdisj.ne_of_mem hc hw rfl)
    · exact h
    · exact absurd (hU2 h) (fun hc => hIOdisj.ne_of_mem hc hw rfl)
  have hnotBothO : ¬ (g '' sphere (0 : ℂ) (1 + ε) ⊆ annulus (R' - δ) R' ∧
      g '' sphere (0 : ℂ) (R - ε) ⊆ annulus (R' - δ) R') := by
    rintro ⟨h1, h2⟩
    apply hInotSub
    have hU1 : g '' annulus 1 (1 + ε) ⊆ annulus (R' - δ) R' :=
      hextract _ _ _ _ (hne1.image g) hIOdisj.symm hsync1.symm h1
    have hU2 : g '' annulus (R - ε) R ⊆ annulus (R' - δ) R' :=
      hextract _ _ _ _ (hne2.image g) hIOdisj.symm hsync2.symm h2
    have hsplit : annulus 1 (1 + δ) ⊆
        g '' annulus 1 (1 + ε) ∪ Mε ∪ g '' annulus (R - ε) R := hpartition ▸ hIsubA'
    intro w hw
    rcases hsplit hw with (h | h) | h
    · exact absurd (hU1 h) (fun hc => hIOdisj.ne_of_mem hw hc rfl)
    · exact h
    · exact absurd (hU2 h) (fun hc => hIOdisj.ne_of_mem hw hc rfl)
  -- final assembly: the two circles land in each of `I'`, `O'`, in either order
  rcases hIorO _ (hsphereconn (1 + ε) (by linarith)) hsph1sub hcirc1 with hc1I | hc1O
  · rcases hIorO _ (hsphereconn (R - ε) (by linarith)) hsph2sub hcirc2 with hc2I | hc2O
    · exact absurd ⟨hc1I, hc2I⟩ hnotBothI
    · exact Or.inl ⟨hc1I, hc2O⟩
  · rcases hIorO _ (hsphereconn (R - ε) (by linarith)) hsph2sub hcirc2 with hc2I | hc2O
    · exact Or.inr ⟨hc1O, hc2I⟩
    · exact absurd ⟨hc1O, hc2O⟩ hnotBothO

/-! ### Piece D -/

/-! ## Stage 1: side transport under a plain homeomorphism, and rotate/joiningCurves -/

/-- Local copy of `TopQuad.image_side`, needing only the image equation `f '' Q.dom = V`
(not full `IsConformalOnto`) since the original proof only ever uses that component. -/
theorem aqc_image_side_homeo {Q : TopQuad} {V : Set ℂ} (hV : IsOpen V) {f : ℂ → ℂ}
    {F : ExtPlane → ExtPlane} (himg : f '' Q.dom = V) (hF : IsHomeoExtension f Q.dom V F)
    (i : Fin 4) :
    F '' Q.side i = boundaryArc (frontier (toExt V)) (F (Q.vert i)) (F (Q.vert (i + 1)))
      (F (Q.vert (i + 2))) := by
  have hQ := Q.isTopQuad
  have hfr : frontier (toExt Q.dom) ⊆ closure (toExt Q.dom) := frontier_subset_closure
  rw [Q.side_eq_boundaryArc, image_boundaryArc_of_injOn isClosed_closure hF.2.1 hF.2.2.1 hfr
    (hfr (hQ.2.1 i)) (hfr (hQ.2.1 _)) (hfr (hQ.2.1 _)), hF.image_frontier hQ.1.1 hV himg]

/-- Rotating shifts the joining-curve family the same way it shifts sides:
`Q.rotate.joiningCurves i = Q.joiningCurves (i + 1)`. -/
theorem aqc_rotate_joiningCurves (Q : TopQuad) (i : Fin 4) :
    Q.rotate.joiningCurves i = Q.joiningCurves (i + 1) := by
  have hidx : i + 2 + 1 = i + 1 + 2 := add_right_comm i 2 1
  ext γ
  simp only [TopQuad.joiningCurves, mem_setOf_eq, TopQuad.IsJoiningCurve]
  rw [show Q.rotate.dom = Q.dom from rfl, Q.rotate_side i, Q.rotate_side (i + 2), hidx]

/-! ## Stage 2: the norm-gap and admissibility lemmas -/

/-- The two collar-dichotomy cases both give the same norm gap between a point of the
`R−ε`-image and a point of the `1+ε`-image. -/
theorem aqc_norm_gap {R' δ : ℝ} (hδ : 0 < δ) (hδ' : 2 * δ < R' - 1) {S₁ S₃ : Set ℂ}
    (hcollar : (S₃ ⊆ annulus 1 (1 + δ) ∧ S₁ ⊆ annulus (R' - δ) R') ∨
      (S₃ ⊆ annulus (R' - δ) R' ∧ S₁ ⊆ annulus 1 (1 + δ))) :
    ∀ p ∈ S₁, ∀ q ∈ S₃, Real.log ((R' - δ) / (1 + δ)) ≤ |Real.log ‖q‖ - Real.log ‖p‖| ∧
      p ≠ 0 ∧ q ≠ 0 := by
  have h1δpos : (0 : ℝ) < 1 + δ := by linarith
  have hRδpos : (0 : ℝ) < R' - δ := by linarith
  have hlt : (1 : ℝ) + δ < R' - δ := by linarith
  have hlogdiv : Real.log ((R' - δ) / (1 + δ)) = Real.log (R' - δ) - Real.log (1 + δ) :=
    Real.log_div hRδpos.ne' h1δpos.ne'
  have hlogmono : Real.log (1 + δ) < Real.log (R' - δ) := Real.log_lt_log h1δpos hlt
  rcases hcollar with ⟨h3, h1⟩ | ⟨h3, h1⟩
  · intro p hp q hq
    have hp' := h1 hp
    have hq' := h3 hq
    have hpne : p ≠ 0 := norm_pos_iff.mp (by linarith [hp'.1])
    have hqne : q ≠ 0 := norm_pos_iff.mp (by linarith [hq'.1])
    have hlog1 : Real.log (R' - δ) < Real.log ‖p‖ := Real.log_lt_log hRδpos hp'.1
    have hlog2 : Real.log ‖q‖ < Real.log (1 + δ) := Real.log_lt_log (by linarith [hq'.1]) hq'.2
    refine ⟨?_, hpne, hqne⟩
    rw [abs_of_nonpos (by linarith [hlog1, hlog2, hlogmono]), hlogdiv]
    linarith
  · intro p hp q hq
    have hp' := h1 hp
    have hq' := h3 hq
    have hpne : p ≠ 0 := norm_pos_iff.mp (by linarith [hp'.1])
    have hqne : q ≠ 0 := norm_pos_iff.mp (by linarith [hq'.1])
    have hlog1 : Real.log ‖p‖ < Real.log (1 + δ) := Real.log_lt_log (by linarith [hp'.1]) hp'.2
    have hlog2 : Real.log (R' - δ) < Real.log ‖q‖ := Real.log_lt_log hRδpos hq'.1
    refine ⟨?_, hpne, hqne⟩
    rw [abs_of_nonneg (by linarith [hlog1, hlog2, hlogmono]), hlogdiv]
    linarith

/-- Every curve joining side `1` to side `3` of `Q'` has `1 ≤ ρ`-length, for the density
`ρ = 1/(L·|z|)` (with `L` the collar log-gap). Combines the collar dichotomy (`hcollar`), the
side transport (`hQ'side1`/`hQ'side3`), and the radial length estimate `B`. -/
theorem aqc_admissible {R R' ε δ : ℝ} (hδ : 0 < δ) (hδ' : 2 * δ < R' - 1)
    {g : ℂ → ℂ} {Q' : TopQuad} (h0 : (0 : ℂ) ∉ Q'.dom)
    (hQ'side1 : Q'.side 1 ⊆ toExt (g '' sphere (0 : ℂ) (R - ε)))
    (hQ'side3 : Q'.side 3 ⊆ toExt (g '' sphere (0 : ℂ) (1 + ε)))
    (hcollar : (g '' sphere (0 : ℂ) (1 + ε) ⊆ annulus 1 (1 + δ) ∧
        g '' sphere (0 : ℂ) (R - ε) ⊆ annulus (R' - δ) R') ∨
      (g '' sphere (0 : ℂ) (1 + ε) ⊆ annulus (R' - δ) R' ∧
        g '' sphere (0 : ℂ) (R - ε) ⊆ annulus 1 (1 + δ))) :
    ∀ γ ∈ Q'.joiningCurves 1,
      (1 : ℝ≥0∞) ≤ γ.rhoLength
        (fun z => ENNReal.ofReal (1 / (Real.log ((R' - δ) / (1 + δ)) * ‖z‖))) := by
  set L := Real.log ((R' - δ) / (1 + δ)) with hL_def
  have h1δpos : (0 : ℝ) < 1 + δ := by linarith
  have hRδpos : (0 : ℝ) < R' - δ := by linarith
  have hlt : (1 : ℝ) + δ < R' - δ := by linarith
  have hLpos : 0 < L := by
    rw [hL_def]
    exact Real.log_pos ((one_lt_div h1δpos).mpr hlt)
  rintro γ ⟨hγtr, ⟨p, hp, hptend⟩, ⟨q, hq, hqtend⟩⟩
  have h12 : (1 + 2 : Fin 4) = 3 := by decide
  rw [h12] at hq
  obtain ⟨p', hp', rfl⟩ := hQ'side1 hp
  obtain ⟨q', hq', rfl⟩ := hQ'side3 hq
  obtain ⟨hgap, hp'ne, hq'ne⟩ := aqc_norm_gap hδ hδ' hcollar p' hp' q' hq'
  have hptend' : Tendsto γ.toFun (𝓝[>] 0) (𝓝 p') :=
    OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.2 hptend
  have hqtend' : Tendsto γ.toFun (𝓝[<] 1) (𝓝 q') :=
    OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.2 hqtend
  have hne : ∀ t ∈ Ioo (0 : ℝ) 1, γ.toFun t ≠ 0 := by
    intro t ht hzero
    apply h0
    rw [← hzero]
    exact hγtr ⟨t, ht, rfl⟩
  have hB := aqc_abs_log_norm_sub_le_rhoLength hp'ne hq'ne hne hptend' hqtend'
  have hstep : ENNReal.ofReal L ≤ γ.rhoLength (fun z => ENNReal.ofReal (1 / ‖z‖)) :=
    (ENNReal.ofReal_le_ofReal hgap).trans hB
  have hρeq : (fun z : ℂ => ENNReal.ofReal (1 / (L * ‖z‖))) =
      fun z => ENNReal.ofReal (1 / L) * ENNReal.ofReal (1 / ‖z‖) := by
    funext z
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [one_div, one_div, one_div, mul_inv]
  rw [hρeq]
  have hpull : γ.rhoLength (fun z => ENNReal.ofReal (1 / L) * ENNReal.ofReal (1 / ‖z‖)) =
      ENNReal.ofReal (1 / L) * γ.rhoLength (fun z => ENNReal.ofReal (1 / ‖z‖)) := by
    simp only [LRCurve.rhoLength]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext t
    ring
  rw [hpull]
  have h1 : (1 : ℝ≥0∞) = ENNReal.ofReal (1 / L) * ENNReal.ofReal L := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [show (1 / L) * L = 1 from by field_simp]
    simp
  rw [h1]
  exact mul_le_mul_right hstep _

/-- (4.6) applied to `Q'.rotate` with `ρ = 1/(L|w|)`, plus the annulus area integral and
`thm1_2_modulus_rotate`, give the modulus lower bound `L²/(2π log R') ≤ M(Q')`. -/
theorem aqc_modulus_lower_bound {R' δ : ℝ} (hR' : 1 < R') (hδ : 0 < δ) (hδ' : 2 * δ < R' - 1)
    {Q' : TopQuad} (hQ'dom : Q'.dom ⊆ annulus 1 R')
    (hadm : ∀ γ ∈ Q'.joiningCurves 1,
      (1 : ℝ≥0∞) ≤
        γ.rhoLength (fun z => ENNReal.ofReal (1 / (Real.log ((R' - δ) / (1 + δ)) * ‖z‖)))) :
    (Real.log ((R' - δ) / (1 + δ))) ^ 2 / (2 * π * Real.log R') ≤ Q'.modulus := by
  set L := Real.log ((R' - δ) / (1 + δ)) with hL_def
  have h1δpos : (0 : ℝ) < 1 + δ := by linarith
  have hRδpos : (0 : ℝ) < R' - δ := by linarith
  have hlt : (1 : ℝ) + δ < R' - δ := by linarith
  have hLpos : 0 < L := Real.log_pos ((one_lt_div h1δpos).mpr hlt)
  have hlogR'pos : 0 < Real.log R' := Real.log_pos hR'
  set ρ : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (1 / (L * ‖z‖)) with hρ_def
  have hρmeas : Measurable ρ := by
    rw [hρ_def]
    fun_prop
  have hadm' : ∀ γ ∈ Q'.rotate.joiningCurves 0, (1 : ℝ≥0∞) ≤ γ.rhoLength ρ := by
    rw [aqc_rotate_joiningCurves Q' 0]
    exact hadm
  have h46 := eq4_6_modulus_le_rhoArea Q'.rotate hρmeas hadm'
  rw [show Q'.rotate.dom = Q'.dom from rfl] at h46
  have hmono : rhoArea ρ Q'.dom ≤ rhoArea ρ (annulus 1 R') :=
    MeasureTheory.lintegral_mono_set hQ'dom
  have harea : rhoArea ρ (annulus 1 R') =
      ENNReal.ofReal (1 / L ^ 2) * (ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log R')) := by
    rw [rhoArea]
    have hρsq : ∀ z : ℂ, ρ z ^ 2 = ENNReal.ofReal (1 / L ^ 2) * ENNReal.ofReal (1 / ‖z‖ ^ 2) := by
      intro z
      rw [hρ_def]
      rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    simp_rw [hρsq]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    have hlog := lintegral_annulus_inv_normSq (r₁ := 1) (r₂ := R') zero_lt_one hR'
    rwa [div_one] at hlog
  have h46 := h46.trans (hmono.trans_eq harea)
  have hRHS_eq :
      ENNReal.ofReal (1 / L ^ 2) * (ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log R')) =
        ENNReal.ofReal (2 * π * Real.log R' / L ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [hRHS_eq] at h46
  have hrot_pos : 0 < Q'.rotate.modulus := modulus_pos Q'.rotate
  have hRHSreal_pos : (0 : ℝ) ≤ 2 * π * Real.log R' / L ^ 2 := by positivity
  have hbound : Q'.rotate.modulus ≤ 2 * π * Real.log R' / L ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff hRHSreal_pos).mp h46
  rw [thm1_2_modulus_rotate Q']
  have hinv := one_div_le_one_div_of_le hrot_pos hbound
  rwa [one_div_div] at hinv

/-! ## Stage 4: assembly -/

theorem aqc_log_le_of_quad_bound {R R' K : ℝ} (hR : 1 < R) (hR' : 1 < R') (hK : 0 ≤ K)
    {g : ℂ → ℂ} (hg : IsHomeomorphOnto g (annulus 1 R) (annulus 1 R'))
    (hmod : ∀ Q : TopQuad, closure (toExt Q.dom) ⊆ toExt (annulus 1 R) →
      ∃ Q' : TopQuad, Q.IsImageUnder Q' g ∧ Q'.modulus ≤ K * Q.modulus) :
    Real.log R' ≤ K * Real.log R := by
  have hRo : IsOpen (annulus 1 R) := isOpen_annulus 1 R
  have hcore : ∀ δ : ℝ, 0 < δ → 2 * δ < R' - 1 →
      (Real.log ((R' - δ) / (1 + δ))) ^ 2 / Real.log R' ≤ K * Real.log R := by
    intro δ hδ hδ'
    obtain ⟨ε₀, hε₀, hε₀R, hcollar⟩ := aqc_exists_collar hR hR' hg hδ hδ'
    have hcore2 : ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ θ : ℝ, 0 < θ → θ < π →
        (Real.log ((R' - δ) / (1 + δ))) ^ 2 / (2 * π * Real.log R') ≤
          K * (Real.log (R - ε) - Real.log (1 + ε)) / (2 * π - 2 * θ) := by
      intro ε hε hεε₀ θ hθ hθπ
      have hεR : 1 + ε < R - ε := by linarith
      obtain ⟨Q, hQclos, hQmod, hQside1, hQside3⟩ := aqc_exists_sectorQuad hR hε hεR hθ hθπ
      obtain ⟨Q', hQ'img, hQ'le⟩ := hmod Q hQclos
      have hQdomopen : IsOpen Q.dom := Q.isTopQuad.1.1
      have hQdomsub : Q.dom ⊆ annulus 1 R := by
        intro z hz
        have hz' : ((z : ℂ) : ExtPlane) ∈ closure (toExt Q.dom) :=
          subset_closure (mem_image_of_mem _ hz)
        obtain ⟨w, hw, hwz⟩ := hQclos hz'
        rwa [← OnePoint.coe_injective hwz]
      have hgo : IsOpen (g '' Q.dom) :=
        isOpen_image_of_continuousOn_injOn_of_subset hRo hg.1 hg.2.1 hQdomsub hQdomopen
      obtain ⟨-, hFext, -⟩ := image_isJordanDomain_of_open hRo hg.1 hg.2.1 hQclos hgo
      have hQ'dom : Q'.dom = g '' Q.dom := hQ'img.1
      have hQ'domopen : IsOpen Q'.dom := by rw [hQ'dom]; exact hgo
      have hFext' : IsHomeoExtension g Q.dom Q'.dom (OnePoint.map g) := by
        rw [hQ'dom]; exact hFext
      have hside : ∀ i : Fin 4, OnePoint.map g '' Q.side i =
          boundaryArc (frontier (toExt Q'.dom)) (Q'.vert i) (Q'.vert (i + 1))
            (Q'.vert (i + 2)) := by
        intro i
        rw [aqc_image_side_homeo hQ'domopen hQ'dom.symm hFext' i, ← hQ'img.2, ← hQ'img.2,
          ← hQ'img.2]
      have hside1 : Q'.side 1 = OnePoint.map g '' Q.side 1 := by
        rw [Q'.side_eq_boundaryArc]; exact (hside 1).symm
      have hside3 : Q'.side 3 = OnePoint.map g '' Q.side 3 := by
        rw [Q'.side_eq_boundaryArc]; exact (hside 3).symm
      have hQ'side1 : Q'.side 1 ⊆ toExt (g '' sphere (0 : ℂ) (R - ε)) := by
        rw [hside1]
        rintro _ ⟨v, hv, rfl⟩
        obtain ⟨w, hw, rfl⟩ := hQside1 hv
        exact ⟨g w, ⟨w, hw, rfl⟩, rfl⟩
      have hQ'side3 : Q'.side 3 ⊆ toExt (g '' sphere (0 : ℂ) (1 + ε)) := by
        rw [hside3]
        rintro _ ⟨v, hv, rfl⟩
        obtain ⟨w, hw, rfl⟩ := hQside3 hv
        exact ⟨g w, ⟨w, hw, rfl⟩, rfl⟩
      have hQ'domR' : Q'.dom ⊆ annulus 1 R' := by
        rw [hQ'dom]
        rintro _ ⟨z, hz, rfl⟩
        rw [← hg.2.2.1]
        exact ⟨z, hQdomsub hz, rfl⟩
      have h0 : (0 : ℂ) ∉ Q'.dom := by
        intro h0mem
        have hcontra := hQ'domR' h0mem
        simp only [annulus, mem_setOf_eq, norm_zero] at hcontra
        linarith [hcontra.1]
      have hcollarε := hcollar ε hε hεε₀
      have hadm := aqc_admissible hδ hδ' h0 hQ'side1 hQ'side3 hcollarε
      have hlb := aqc_modulus_lower_bound hR' hδ hδ' hQ'domR' hadm
      have hle : (Real.log ((R' - δ) / (1 + δ))) ^ 2 / (2 * π * Real.log R') ≤ K * Q.modulus :=
        hlb.trans hQ'le
      rw [hQmod, ← mul_div_assoc] at hle
      exact hle
    -- ε → 0, θ fixed
    have hstep1 : ∀ θ : ℝ, 0 < θ → θ < π →
        (Real.log ((R' - δ) / (1 + δ))) ^ 2 / (2 * π * Real.log R') ≤
          K * Real.log R / (2 * π - 2 * θ) := by
      intro θ hθ hθπ
      have h1 : Tendsto (fun ε : ℝ => Real.log (R - ε)) (𝓝[>] 0) (𝓝 (Real.log R)) := by
        refine Tendsto.comp (Real.continuousAt_log (by linarith)).tendsto ?_
        have : Tendsto (fun ε : ℝ => R - ε) (𝓝 0) (𝓝 R) :=
          (continuous_const.sub continuous_id).tendsto' 0 R (by simp)
        exact this.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (fun ε : ℝ => Real.log (1 + ε)) (𝓝[>] 0) (𝓝 (Real.log 1)) := by
        refine Tendsto.comp (Real.continuousAt_log (by norm_num)).tendsto ?_
        have : Tendsto (fun ε : ℝ => 1 + ε) (𝓝 0) (𝓝 (1 : ℝ)) :=
          (continuous_const.add continuous_id).tendsto' 0 1 (by simp)
        exact this.mono_left nhdsWithin_le_nhds
      rw [Real.log_one] at h2
      have htendsto :
          Tendsto (fun ε : ℝ => K * (Real.log (R - ε) - Real.log (1 + ε)) / (2 * π - 2 * θ))
            (𝓝[>] 0) (𝓝 (K * Real.log R / (2 * π - 2 * θ))) := by
        have h3 := (h1.sub h2).const_mul K
        have h4 := h3.div_const (2 * π - 2 * θ)
        simpa using h4
      refine ge_of_tendsto htendsto ?_
      filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε'
      exact hcore2 ε hε'.1 hε'.2 θ hθ hθπ
    -- θ → 0
    have hstep2 : Tendsto (fun θ : ℝ => K * Real.log R / (2 * π - 2 * θ)) (𝓝[>] 0)
        (𝓝 (K * Real.log R / (2 * π))) := by
      have h5 : Tendsto (fun θ : ℝ => 2 * π - 2 * θ) (𝓝 0) (𝓝 (2 * π)) :=
        (continuous_const.sub (continuous_const.mul continuous_id)).tendsto' 0 (2 * π) (by simp)
      exact tendsto_const_nhds.div (h5.mono_left nhdsWithin_le_nhds) (by positivity)
    have hfinal : (Real.log ((R' - δ) / (1 + δ))) ^ 2 / (2 * π * Real.log R') ≤
        K * Real.log R / (2 * π) := by
      refine ge_of_tendsto hstep2 ?_
      filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with θ hθ'
      exact hstep1 θ hθ'.1 hθ'.2
    have h2πpos : (0 : ℝ) < 2 * π := by positivity
    have hrw1 : Real.log ((R' - δ) / (1 + δ)) ^ 2 / (2 * π * Real.log R') =
        Real.log ((R' - δ) / (1 + δ)) ^ 2 / Real.log R' / (2 * π) := by
      rw [div_div, mul_comm (2 * π) (Real.log R')]
    rw [hrw1] at hfinal
    have hstep3 := mul_le_mul_of_nonneg_right hfinal h2πpos.le
    rwa [div_mul_cancel₀ _ h2πpos.ne', div_mul_cancel₀ _ h2πpos.ne'] at hstep3
  -- δ → 0
  have hlogR'pos : 0 < Real.log R' := Real.log_pos hR'
  have hcont : Tendsto (fun δ : ℝ => (R' - δ) / (1 + δ)) (𝓝 0) (𝓝 R') := by
    have hfc : ContinuousAt (fun δ : ℝ => (R' - δ) / (1 + δ)) 0 :=
      ((continuous_const.sub continuous_id).continuousAt).div
        ((continuous_const.add continuous_id).continuousAt) (by norm_num)
    simpa using hfc.tendsto
  have hLtendsto : Tendsto (fun δ : ℝ => Real.log ((R' - δ) / (1 + δ))) (𝓝[>] 0)
      (𝓝 (Real.log R')) :=
    Tendsto.comp (Real.continuousAt_log (show (0 : ℝ) < R' by linarith).ne').tendsto
      (hcont.mono_left nhdsWithin_le_nhds)
  have hL2tendsto : Tendsto
      (fun δ : ℝ => (Real.log ((R' - δ) / (1 + δ))) ^ 2 / Real.log R') (𝓝[>] 0)
        (𝓝 (Real.log R')) := by
    have h6 := (hLtendsto.pow 2).div_const (Real.log R')
    have heq : (Real.log R') ^ 2 / Real.log R' = Real.log R' := by
      field_simp
    rwa [heq] at h6
  refine le_of_tendsto hL2tendsto ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < (R' - 1) / 2 by linarith)] with δ hδ'
  exact hcore δ hδ'.1 (by linarith [hδ'.2])

/-! ### Piece E1 -/

/-- A decreasing sequence of nonempty compact connected sets has connected intersection. -/
theorem aqc_isConnected_iInter_antitone {K : ℕ → Set ℂ} (hanti : ∀ n, K (n+1) ⊆ K n)
    (hne : ∀ n, (K n).Nonempty) (hcompact : ∀ n, IsCompact (K n)) (hconn : ∀ n, IsConnected (K n)) :
    IsConnected (⋂ n, K n) := by
  have hcl : ∀ n, IsClosed (K n) := fun n => (hcompact n).isClosed
  have hnonempty : (⋂ n, K n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hanti hne (hcompact 0) hcl
  have hKcompact : IsCompact (⋂ n, K n) :=
    IsCompact.of_isClosed_subset (hcompact 0) (isClosed_iInter hcl) (iInter_subset _ 0)
  refine ⟨hnonempty, ?_⟩
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hsuv hdisj
  set s := ⋂ n, K n with hsdef
  by_contra hcon
  push Not at hcon
  obtain ⟨hnu, hnv⟩ := hcon
  have hcov : ∀ z ∈ s, z ∈ u ∨ z ∈ v := fun z hz => hsuv hz
  have hexcl : ∀ z ∈ s, z ∈ u → z ∈ v → False := fun z hz hzu hzv =>
    absurd (mem_of_eq_of_mem rfl (mem_inter hz (mem_inter hzu hzv))) (by rw [hdisj]; exact id)
  have hAeq : s ∩ u = s \ v := by
    ext z
    simp only [mem_inter_iff, mem_diff]
    constructor
    · rintro ⟨hzs, hzu⟩
      exact ⟨hzs, fun hzv => hexcl z hzs hzu hzv⟩
    · rintro ⟨hzs, hzv⟩
      exact ⟨hzs, (hcov z hzs).resolve_right hzv⟩
  have hBeq : s ∩ v = s \ u := by
    ext z
    simp only [mem_inter_iff, mem_diff]
    constructor
    · rintro ⟨hzs, hzv⟩
      exact ⟨hzs, fun hzu => hexcl z hzs hzu hzv⟩
    · rintro ⟨hzs, hzu⟩
      exact ⟨hzs, (hcov z hzs).resolve_left hzu⟩
  have hAcompact : IsCompact (s ∩ u) := by rw [hAeq]; exact hKcompact.diff hv
  have hBcompact : IsCompact (s ∩ v) := by rw [hBeq]; exact hKcompact.diff hu
  have hAne : (s ∩ u).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hem
    apply hnv
    intro z hz
    exact (hcov z hz).resolve_left (fun hzu => (hem ▸ (⟨hz, hzu⟩ : z ∈ s ∩ u) : (∅ : Set ℂ) z).elim)
  have hBne : (s ∩ v).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hem
    apply hnu
    intro z hz
    exact (hcov z hz).resolve_right (fun hzv => (hem ▸ (⟨hz, hzv⟩ : z ∈ s ∩ v) : (∅ : Set ℂ) z).elim)
  have hABdisj : Disjoint (s ∩ u) (s ∩ v) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
    rintro ⟨⟨hzs, hzu⟩, _, hzv⟩
    exact hexcl z hzs hzu hzv
  obtain ⟨U', V', hU'o, hV'o, hAU', hBV', hUV'd⟩ :=
    SeparatedNhds.of_isCompact_isCompact hAcompact hBcompact hABdisj
  have hsUV' : s ⊆ U' ∪ V' := by
    intro z hz
    rcases hcov z hz with h | h
    · exact Or.inl (hAU' ⟨hz, h⟩)
    · exact Or.inr (hBV' ⟨hz, h⟩)
  have hCompl : ∀ n, IsCompact (K n ∩ (U' ∪ V')ᶜ) :=
    fun n => (hcompact n).inter_right (hU'o.union hV'o).isClosed_compl
  have hAntiC : ∀ n, K (n+1) ∩ (U' ∪ V')ᶜ ⊆ K n ∩ (U' ∪ V')ᶜ :=
    fun n => inter_subset_inter_left _ (hanti n)
  have hEmptyEventually : ¬ ∀ n, (K n ∩ (U' ∪ V')ᶜ).Nonempty := by
    intro hall
    have hne' := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => K n ∩ (U' ∪ V')ᶜ) hAntiC hall (hCompl 0) (fun n => (hCompl n).isClosed)
    have heq : (⋂ n, K n ∩ (U' ∪ V')ᶜ) = s ∩ (U' ∪ V')ᶜ := by
      ext z
      simp only [mem_iInter, mem_inter_iff, hsdef]
      constructor
      · intro h
        exact ⟨fun i => (h i).1, (h 0).2⟩
      · rintro ⟨h1, h2⟩ i
        exact ⟨h1 i, h2⟩
    rw [heq] at hne'
    obtain ⟨z, hz1, hz2⟩ := hne'
    exact hz2 (hsUV' hz1)
  push Not at hEmptyEventually
  obtain ⟨N, hN⟩ := hEmptyEventually
  have hKN : K N ⊆ U' ∪ V' := by
    intro z hz
    by_contra hzc
    exact (hN ▸ (⟨hz, hzc⟩ : z ∈ K N ∩ (U' ∪ V')ᶜ) : (∅ : Set ℂ) z).elim
  rcases IsPreconnected.subset_or_subset hU'o hV'o hUV'd hKN (hconn N).isPreconnected with h | h
  · have hsU' : s ⊆ U' := (iInter_subset K N).trans h
    have hsub : s ∩ v ⊆ U' ∩ V' := fun z hz => ⟨hsU' hz.1, hBV' hz⟩
    exact absurd (hBne.mono hsub) (by rw [Set.disjoint_iff_inter_eq_empty.mp hUV'd]; exact not_nonempty_empty)
  · have hsV' : s ⊆ V' := (iInter_subset K N).trans h
    have hsub : s ∩ u ⊆ U' ∩ V' := fun z hz => ⟨hAU' hz, hsV' hz.1⟩
    exact absurd (hAne.mono hsub) (by rw [Set.disjoint_iff_inter_eq_empty.mp hUV'd]; exact not_nonempty_empty)

/-- A conformal map is a homeomorphism onto its (open) image. -/
theorem aqc_isHomeomorphOnto_of_isConformalOnto {φ : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U)
    (hφ : IsConformalOnto φ U V) : IsHomeomorphOnto φ U V := by
  obtain ⟨hφd, hφinj, hφimg⟩ := hφ
  refine ⟨hφd.continuousOn, hφinj, hφimg, ?_⟩
  have := (RMT.differentiableOn_invFunOn_of_injOn hU hφd hφinj).2
  rw [hφimg] at this
  exact this.continuousOn

/-- A bounded doubly connected domain is conformally equivalent to an annulus (possibly a
punctured disc, `r₁ = 0`). -/
theorem aqc_exists_annulus_model {B : Set ℂ} (hB : IsDoublyConnected B)
    (hbdd : Bornology.IsBounded B) :
    ∃ r₁ r₂ : ℝ, 0 ≤ r₁ ∧ r₁ < r₂ ∧ ConformallyEquivalent B (annulus r₁ r₂) := by
  rcases thm2_1_canonical_form hB with h | h | h
  · exfalso
    obtain ⟨φ, hφd, hφinj, hφimg⟩ := h
    have hinvd : DifferentiableOn ℂ (Function.invFunOn φ B) puncturedPlane := by
      have := (RMT.differentiableOn_invFunOn_of_injOn hB.1 hφd hφinj).2
      rwa [hφimg] at this
    have hinvinj : InjOn (Function.invFunOn φ B) puncturedPlane := by
      rw [← hφimg]
      intro x hx y hy hxy
      have := congrArg φ hxy
      rwa [Function.invFunOn_eq hx, Function.invFunOn_eq hy] at this
    obtain ⟨M, hM⟩ := hbdd.subset_closedBall (0:ℂ)
    refine not_injOn_punctured_of_bounded hinvd hinvinj (M := M) fun z hz => ?_
    have hmem : Function.invFunOn φ B z ∈ B := by
      rw [← hφimg] at hz
      exact Function.invFunOn_mem hz
    have := hM hmem
    rwa [mem_closedBall_zero_iff] at this
  · exact ⟨0, 1, le_refl 0, one_pos, h⟩
  · obtain ⟨r₁, r₂, hr1, hr12, heq⟩ := h
    exact ⟨r₁, r₂, hr1.le, hr12, heq⟩

/-- The inverse of a homeomorphism is a homeomorphism. -/
theorem aqc_isHomeomorphOnto_invFunOn {f : ℂ → ℂ} {U V : Set ℂ} (hf : IsHomeomorphOnto f U V) :
    IsHomeomorphOnto (Function.invFunOn f U) V U := by
  obtain ⟨hfc, hfinj, hfimg, hinvc⟩ := hf
  have hginj : InjOn (Function.invFunOn f U) V := by
    rw [← hfimg]
    intro x hx y hy hxy
    have := congrArg f hxy
    rwa [Function.invFunOn_eq hx, Function.invFunOn_eq hy] at this
  have hgimg : Function.invFunOn f U '' V = U := by
    ext x
    simp only [mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← hfimg] at hy
      exact Function.invFunOn_mem hy
    · intro hx
      refine ⟨f x, hfimg ▸ mem_image_of_mem f hx, ?_⟩
      exact hfinj.leftInvOn_invFunOn hx
  refine ⟨hinvc, hginj, hgimg, ?_⟩
  have heqOn : EqOn (Function.invFunOn (Function.invFunOn f U) V) f U := by
    intro x hx
    have hxmem : x ∈ Function.invFunOn f U '' V := by rw [hgimg]; exact hx
    have hgx : Function.invFunOn f U (Function.invFunOn (Function.invFunOn f U) V x) = x := Function.invFunOn_eq hxmem
    have hgfx : Function.invFunOn f U (f x) = x := hfinj.leftInvOn_invFunOn hx
    have hmem1 : Function.invFunOn (Function.invFunOn f U) V x ∈ V := Function.invFunOn_mem hxmem
    have hmem2 : f x ∈ V := hfimg ▸ mem_image_of_mem f hx
    exact hginj hmem1 hmem2 (hgx.trans hgfx.symm)
  exact hfc.congr heqOn

/-- The composition of two homeomorphisms is a homeomorphism. -/
theorem aqc_isHomeomorphOnto_comp {f g : ℂ → ℂ} {U V W : Set ℂ}
    (hf : IsHomeomorphOnto f U V) (hg : IsHomeomorphOnto g V W) :
    IsHomeomorphOnto (g ∘ f) U W := by
  obtain ⟨hfc, hfinj, hfimg, hfinvc⟩ := hf
  obtain ⟨hgc, hginj, hgimg, hginvc⟩ := hg
  have hmapsto : MapsTo f U V := fun x hx => hfimg ▸ mem_image_of_mem f hx
  have hcompinj : InjOn (g ∘ f) U := hginj.comp hfinj hmapsto
  refine ⟨hgc.comp hfc hmapsto, hcompinj, ?_, ?_⟩
  · rw [image_comp, hfimg, hgimg]
  · have hmapstoInv : MapsTo (Function.invFunOn g V) W V := by
      intro x hx
      apply Function.invFunOn_mem
      have hx2 := hx
      rw [← hgimg] at hx2
      exact hx2
    have heqOn : EqOn (Function.invFunOn (g ∘ f) U) (Function.invFunOn f U ∘ Function.invFunOn g V) W := by
      intro x hx
      set z := Function.invFunOn g V x with hzdef
      set y := Function.invFunOn f U z with hydef
      have hxgV : x ∈ g '' V := by
        have hx2 := hx
        rw [← hgimg] at hx2
        exact hx2
      have hzV : z ∈ V := Function.invFunOn_mem hxgV
      have hgz : g z = x := Function.invFunOn_eq hxgV
      have hzfU : z ∈ f '' U := by
        have hzV2 := hzV
        rw [← hfimg] at hzV2
        exact hzV2
      have hyU : y ∈ U := Function.invFunOn_mem hzfU
      have hfy : f y = z := Function.invFunOn_eq hzfU
      have hcomp : (g ∘ f) y = x := by show g (f y) = x; rw [hfy, hgz]
      have hxcompU : x ∈ (g ∘ f) '' U := ⟨y, hyU, hcomp⟩
      have hinvU : Function.invFunOn (g ∘ f) U x ∈ U := Function.invFunOn_mem hxcompU
      have hinveq : (g ∘ f) (Function.invFunOn (g ∘ f) U x) = x := Function.invFunOn_eq hxcompU
      show Function.invFunOn (g ∘ f) U x = y
      exact hcompinj hinvU hyU (hinveq.trans hcomp.symm)
    exact (hfinvc.comp hginvc hmapstoInv).congr heqOn

/-- The image of an open subset of the domain of a homeomorphism-onto-an-open-set is open. -/
theorem aqc_isOpen_image_of_isHomeomorphOnto {f : ℂ → ℂ} {D V W : Set ℂ}
    (hf : IsHomeomorphOnto f D V) (hVo : IsOpen V) (hWD : W ⊆ D) (hWo : IsOpen W) :
    IsOpen (f '' W) := by
  obtain ⟨hfc, hfinj, hfimg, hinvc⟩ := hf
  have heq : f '' W = V ∩ (Function.invFunOn f D) ⁻¹' W := by
    ext y
    simp only [mem_image, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨hfimg ▸ mem_image_of_mem f (hWD hx), ?_⟩
      rwa [hfinj.leftInvOn_invFunOn (hWD hx)]
    · rintro ⟨hy, hgy⟩
      have hy' : y ∈ f '' D := hfimg ▸ hy
      refine ⟨Function.invFunOn f D y, hgy, Function.invFunOn_eq hy'⟩
  rw [heq]
  exact hinvc.isOpen_inter_preimage hVo hWo

/-- Restricting a homeomorphism `f : D → V` to an open `B ⊆ D` gives a homeomorphism
`B → f '' B`. -/
theorem aqc_isHomeomorphOnto_restrict {f : ℂ → ℂ} {D V B : Set ℂ}
    (hf : IsHomeomorphOnto f D V) (hVo : IsOpen V) (hBD : B ⊆ D) (hBo : IsOpen B) :
    IsHomeomorphOnto f B (f '' B) := by
  obtain ⟨hfc, hfinj, hfimg, hinvc⟩ := hf
  have hBVo : IsOpen (f '' B) := aqc_isOpen_image_of_isHomeomorphOnto ⟨hfc, hfinj, hfimg, hinvc⟩
    hVo hBD hBo
  have hsub : f '' B ⊆ V := hfimg ▸ image_mono hBD
  refine ⟨hfc.mono hBD, hfinj.mono hBD, rfl, ?_⟩
  have heqOn : EqOn (Function.invFunOn f B) (Function.invFunOn f D) (f '' B) := by
    intro y hy
    have hyD : y ∈ f '' D := hfimg ▸ hsub hy
    have hyB : y ∈ f '' B := hy
    have h1 : f (Function.invFunOn f B y) = y := Function.invFunOn_eq hyB
    have h2 : f (Function.invFunOn f D y) = y := Function.invFunOn_eq hyD
    have hmem1 : Function.invFunOn f B y ∈ B := Function.invFunOn_mem hyB
    have hmem2 : Function.invFunOn f D y ∈ D := Function.invFunOn_mem hyD
    exact hfinj (hBD hmem1) hmem2 (h1.trans h2.symm)
  exact (hinvc.mono hsub).congr heqOn

/-- If a sequence lies eventually in `S` and tends to `p`, then `p ∈ closure S`. -/
theorem aqc_mem_closure_of_eventually_tendsto {S : Set ℂ} {x : ℕ → ℂ} {p : ℂ}
    (hev : ∀ᶠ n in atTop, x n ∈ S) (htend : Tendsto x atTop (𝓝 p)) : p ∈ closure S := by
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun n => x (n+N), fun n => hN (n+N) (Nat.le_add_left N n), ?_⟩
  exact htend.comp (tendsto_add_atTop_nat N)

theorem aqc_not_isBounded_normGT (r₂ : ℝ) : ¬ Bornology.IsBounded {z : ℂ | r₂ < ‖z‖} := by
  intro hb
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0:ℂ)).mp hb
  set M : ℝ := max (max r₂ R + 1) 0 with hMdef
  have hM0 : (0:ℝ) ≤ M := le_max_right _ 0
  have hMge : max r₂ R + 1 ≤ M := le_max_left _ 0
  set z : ℂ := (M : ℂ) with hzdef
  have hznorm : ‖z‖ = M := by
    rw [hzdef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM0]
  have hzmem : z ∈ {z : ℂ | r₂ < ‖z‖} := by
    rw [mem_setOf_eq, hznorm]
    linarith [le_max_left r₂ R]
  have hin := hR hzmem
  rw [mem_closedBall_zero_iff, hznorm] at hin
  linarith [le_max_right r₂ R]

/-- The strict exterior of a disc, together with `extInf`, is preconnected. -/
theorem aqc_isPreconnected_toExt_normGT_insert {r₂ : ℝ} (h₂ : 0 ≤ r₂) :
    IsPreconnected (toExt {z : ℂ | r₂ < ‖z‖} ∪ {extInf}) := by
  have hK : IsPreconnected (toExt {z : ℂ | r₂ < ‖z‖}) :=
    (isPreconnected_setOf_lt_norm h₂).image _ OnePoint.continuous_coe.continuousOn
  refine hK.subset_closure subset_union_left ?_
  exact union_subset subset_closure
    (singleton_subset_iff.2 (extInf_mem_closure_toExt_of_not_isBounded (aqc_not_isBounded_normGT r₂)))

/-- `ExtPlane` is locally connected. Neither Mathlib nor the tree had this for `OnePoint _`. -/
instance aqc_locallyConnectedSpace_extPlane : LocallyConnectedSpace ExtPlane := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U hU
  cases x with
  | some z =>
    have hUz : ((↑) : ℂ → ExtPlane) ⁻¹' U ∈ 𝓝 z := OnePoint.continuous_coe.continuousAt hU
    obtain ⟨V', hV'mem, hV'pre, hV'sub⟩ :=
      (locallyConnectedSpace_iff_connected_subsets.mp inferInstance) z _ hUz
    refine ⟨(↑) '' V', ?_, hV'pre.image _ OnePoint.continuous_coe.continuousOn, ?_⟩
    · obtain ⟨W, hWU, hWo, hzW⟩ := _root_.mem_nhds_iff.mp hV'mem
      exact _root_.mem_nhds_iff.mpr ⟨(↑) '' W, image_mono hWU, OnePoint.isOpen_image_coe.mpr hWo,
        mem_image_of_mem _ hzW⟩
    · exact (image_mono hV'sub).trans (image_preimage_subset _ _)
  | none =>
    show ∃ V ∈ 𝓝 (extInf : ExtPlane), IsPreconnected V ∧ V ⊆ U
    obtain ⟨s, ⟨hsc, hsK⟩, hsub⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hU
    obtain ⟨M₀, hM₀⟩ := hsK.isBounded.subset_closedBall (0 : ℂ)
    set M : ℝ := max M₀ 0 with hMdef
    have hM0 : (0:ℝ) ≤ M := le_max_right M₀ 0
    have hM : s ⊆ closedBall (0 : ℂ) M :=
      hM₀.trans (closedBall_subset_closedBall (le_max_left M₀ 0))
    set V : Set ExtPlane := (↑) '' {z : ℂ | M < ‖z‖} ∪ {extInf} with hVdef
    refine ⟨V, ?_, aqc_isPreconnected_toExt_normGT_insert hM0, ?_⟩
    · rw [OnePoint.hasBasis_nhds_infty.mem_iff]
      refine ⟨closedBall (0 : ℂ) M, ⟨isClosed_closedBall, isCompact_closedBall _ _⟩, ?_⟩
      have hcompl : (closedBall (0:ℂ) M)ᶜ = {z : ℂ | M < ‖z‖} := by
        ext z; simp [not_le]
      rw [hVdef, hcompl]
    · rintro y (⟨z, hz, rfl⟩ | hy)
      · apply hsub
        refine Or.inl ⟨z, ?_, rfl⟩
        intro hzs
        exact absurd (mem_closedBall_zero_iff.1 (hM hzs)) (not_le.2 hz)
      · rw [mem_singleton_iff] at hy
        exact hy ▸ hsub (Or.inr rfl)

/-- A connected component of a closed set (in the ambient space) is closed. -/
theorem aqc_isClosed_connectedComponentIn {s : Set ExtPlane} (hs : IsClosed s) (x : ExtPlane) :
    IsClosed (connectedComponentIn s x) := by
  by_cases hx : x ∈ s
  · rw [connectedComponentIn_eq_image hx]
    exact (isClosed_connectedComponent (α := s)).trans hs
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

/-- A connected component of the complement of an open set, if disjoint from that set's
frontier, is open. -/
theorem aqc_isOpen_connectedComponentIn_compl_of_disjoint_frontier {U : Set ExtPlane}
    (hU : IsOpen U) {x : ExtPlane} (hx : x ∈ Uᶜ)
    (hdisj : connectedComponentIn Uᶜ x ∩ frontier U = ∅) :
    IsOpen (connectedComponentIn Uᶜ x) := by
  set C := connectedComponentIn Uᶜ x with hCdef
  have hCsub : C ⊆ Uᶜ := connectedComponentIn_subset Uᶜ x
  have hCclosed : IsClosed Uᶜ := isClosed_compl_iff.mpr hU
  have hdecomp : Uᶜ = interior Uᶜ ∪ frontier Uᶜ := by
    conv_lhs => rw [← hCclosed.closure_eq]
    exact closure_eq_interior_union_frontier Uᶜ
  have hfeq : frontier Uᶜ = frontier U := frontier_compl U
  have hCsubInt : C ⊆ interior Uᶜ := by
    intro z hz
    rcases hdecomp ▸ (hCsub hz) with h | h
    · exact h
    · exact absurd (mem_inter hz (hfeq ▸ h)) (by rw [hdisj]; exact fun h => h)
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hCeq : C = connectedComponentIn (interior Uᶜ) x := by
    apply Subset.antisymm
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hxC hCsubInt
    · exact connectedComponentIn_mono x interior_subset
  rw [hCeq]
  exact isOpen_interior.connectedComponentIn

/-- Every connected component of the complement of a nonempty open set meets its frontier. -/
theorem aqc_connectedComponentIn_compl_meets_frontier {U : Set ExtPlane}
    (hU : IsOpen U) (hUne : U.Nonempty) {x : ExtPlane} (hx : x ∈ Uᶜ) :
    (connectedComponentIn Uᶜ x ∩ frontier U).Nonempty := by
  by_contra hdisj
  rw [Set.not_nonempty_iff_eq_empty] at hdisj
  have hCo : IsOpen (connectedComponentIn Uᶜ x) :=
    aqc_isOpen_connectedComponentIn_compl_of_disjoint_frontier hU hx hdisj
  have hCc : IsClosed (connectedComponentIn Uᶜ x) :=
    aqc_isClosed_connectedComponentIn (isClosed_compl_iff.mpr hU) x
  have hCne : (connectedComponentIn Uᶜ x).Nonempty := ⟨x, mem_connectedComponentIn hx⟩
  rcases (isClopen_iff.mp ⟨hCc, hCo⟩) with h | h
  · exact absurd h hCne.ne_empty
  · obtain ⟨u, hu⟩ := hUne
    have hCsubU : connectedComponentIn Uᶜ x ⊆ Uᶜ := connectedComponentIn_subset Uᶜ x
    rw [h] at hCsubU
    exact hCsubU (mem_univ u) hu

/-- **E1 (owner -46, after B).** The image of a doubly connected domain `B` with `B̄ ⊆ D` under a
homeomorphism of `D` onto an open set is doubly connected. -/
theorem aqc_isDoublyConnected_image {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hf : IsHomeomorphOnto f D (f '' D)) (hfo : IsOpen (f '' D)) {B : Set ℂ}
    (hB : IsDoublyConnected B) (hBD : closure (toExt B) ⊆ toExt D) :
    IsDoublyConnected (f '' B) := by
  have hBopen : IsOpen B := hB.1
  have hextInf_notin_toExtD : extInf ∉ toExt D := by
    rintro ⟨w, -, hw⟩
    exact (OnePoint.infty_ne_coe w) hw.symm
  have hextInf_notin : extInf ∉ closure (toExt B) := fun h => hextInf_notin_toExtD (hBD h)
  have hBbdd : Bornology.IsBounded B := isBounded_of_extInf_notMem_closure_toExt hextInf_notin
  have hclBsubD : closure B ⊆ D := by
    have heq := closure_toExt_eq_toExt_closure_of_isBounded hBbdd
    have hsub : toExt (closure B) ⊆ toExt D := heq ▸ hBD
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hsub (mem_image_of_mem _ hx)
    rwa [OnePoint.coe_injective hyx] at hy
  have hBsubD : B ⊆ D := subset_closure.trans hclBsubD
  -- Step 1: annulus model
  obtain ⟨r₁, r₂, hr1, hr12, φ, hφd, hφinj, hφimg⟩ := aqc_exists_annulus_model hB hBbdd
  have hφhomeo : IsHomeomorphOnto φ B (annulus r₁ r₂) :=
    aqc_isHomeomorphOnto_of_isConformalOnto hBopen ⟨hφd, hφinj, hφimg⟩
  have hψhomeo : IsHomeomorphOnto (Function.invFunOn φ B) (annulus r₁ r₂) B :=
    aqc_isHomeomorphOnto_invFunOn hφhomeo
  have hfBhomeo : IsHomeomorphOnto f B (f '' B) :=
    aqc_isHomeomorphOnto_restrict hf hfo hBsubD hBopen
  set V := f '' B with hVdef
  set h := f ∘ Function.invFunOn φ B with hhdef
  have hhomeo : IsHomeomorphOnto h (annulus r₁ r₂) V :=
    aqc_isHomeomorphOnto_comp hψhomeo hfBhomeo
  have hVopen : IsOpen V :=
    aqc_isOpen_image_of_isHomeomorphOnto hf hfo hBsubD hBopen
  -- compactness fact
  have hclBcompact : IsCompact (closure B) := hBbdd.isCompact_closure
  have hfclB : IsCompact (f '' closure B) := hclBcompact.image_of_continuousOn (hf.1.mono hclBsubD)
  have hVsubfclB : V ⊆ f '' closure B := image_mono subset_closure
  have hKcompact : ∀ S : Set ℂ, S ⊆ annulus r₁ r₂ → IsCompact (closure (h '' S)) := by
    intro S hS
    have hsub1 : h '' S ⊆ f '' closure B := by
      have : h '' S ⊆ V := hhomeo.2.2.1 ▸ image_mono hS
      exact this.trans hVsubfclB
    exact hfclB.of_isClosed_subset isClosed_closure (closure_minimal hsub1 hfclB.isClosed)
  -- shrinking collars
  set δ : ℕ → ℝ := fun n => (r₂ - r₁) / (2 * (n + 2)) with hδdef
  have hr12' : 0 < r₂ - r₁ := sub_pos.mpr hr12
  have hδpos : ∀ n, 0 < δ n := fun n => by rw [hδdef]; positivity
  have hδanti : ∀ n, δ (n+1) ≤ δ n := by
    intro n
    simp only [hδdef]
    apply div_le_div_of_nonneg_left hr12'.le (by positivity)
    push_cast; linarith
  have hδsmall : ∀ n, δ n < (r₂ - r₁)/2 := by
    intro n
    simp only [hδdef]
    apply div_lt_div_of_pos_left hr12' (by positivity)
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  set K1 : ℕ → Set ℂ := fun n => closure (h '' annulus r₁ (r₁ + δ n)) with hK1def
  set K2 : ℕ → Set ℂ := fun n => closure (h '' annulus (r₂ - δ n) r₂) with hK2def
  have hK1sub : ∀ n, annulus r₁ (r₁ + δ n) ⊆ annulus r₁ r₂ := by
    intro n z hz
    exact ⟨hz.1, hz.2.trans (by linarith [hδsmall n])⟩
  have hK2sub : ∀ n, annulus (r₂ - δ n) r₂ ⊆ annulus r₁ r₂ := by
    intro n z hz
    exact ⟨by linarith [hδsmall n, hz.1], hz.2⟩
  have hK1anti : ∀ n, K1 (n+1) ⊆ K1 n := by
    intro n
    apply closure_mono
    apply image_mono
    intro z hz
    exact ⟨hz.1, hz.2.trans_le (by linarith [hδanti n])⟩
  have hK2anti : ∀ n, K2 (n+1) ⊆ K2 n := by
    intro n
    apply closure_mono
    apply image_mono
    intro z hz
    exact ⟨(by linarith [hδanti n] : r₂ - δ n ≤ r₂ - δ (n+1)).trans_lt hz.1, hz.2⟩
  have hnorm1 : ∀ n, ‖((r₁ + δ n / 2 : ℝ) : ℂ)‖ = r₁ + δ n / 2 := fun n => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hδpos n])]
  have hpt1 : ∀ n, ((r₁ + δ n / 2 : ℝ) : ℂ) ∈ annulus r₁ (r₁ + δ n) := fun n =>
    ⟨by rw [hnorm1]; linarith [hδpos n], by rw [hnorm1]; linarith [hδpos n]⟩
  have hnorm2 : ∀ n, ‖((r₂ - δ n / 2 : ℝ) : ℂ)‖ = r₂ - δ n / 2 := fun n => by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hδsmall n, hr1, hr12] : (0:ℝ) ≤ r₂ - δ n / 2)]
  have hpt2 : ∀ n, ((r₂ - δ n / 2 : ℝ) : ℂ) ∈ annulus (r₂ - δ n) r₂ := fun n =>
    ⟨by rw [hnorm2]; linarith [hδpos n], by rw [hnorm2]; linarith [hδpos n]⟩
  have hK1ne : ∀ n, (K1 n).Nonempty := fun n =>
    ⟨h _, subset_closure (mem_image_of_mem h (hpt1 n))⟩
  have hK2ne : ∀ n, (K2 n).Nonempty := fun n =>
    ⟨h _, subset_closure (mem_image_of_mem h (hpt2 n))⟩
  have hK1compact : ∀ n, IsCompact (K1 n) := fun n => hKcompact _ (hK1sub n)
  have hK2compact : ∀ n, IsCompact (K2 n) := fun n => hKcompact _ (hK2sub n)
  have hK1conn : ∀ n, IsConnected (K1 n) := by
    intro n
    have himgne : (h '' annulus r₁ (r₁ + δ n)).Nonempty := ⟨h _, mem_image_of_mem h (hpt1 n)⟩
    have himgpre : IsPreconnected (h '' annulus r₁ (r₁ + δ n)) :=
      (isPreconnected_annulus hr1).image h (hhomeo.1.mono (hK1sub n))
    exact ⟨himgne.mono subset_closure, himgpre.closure⟩
  have hK2conn : ∀ n, IsConnected (K2 n) := by
    intro n
    have himgne : (h '' annulus (r₂ - δ n) r₂).Nonempty := ⟨h _, mem_image_of_mem h (hpt2 n)⟩
    have himgpre : IsPreconnected (h '' annulus (r₂ - δ n) r₂) :=
      (isPreconnected_annulus
        (by linarith [hδsmall n, hr1, hr12] : (0:ℝ) ≤ r₂ - δ n)).image h (hhomeo.1.mono (hK2sub n))
    exact ⟨himgne.mono subset_closure, himgpre.closure⟩
  set E1 : Set ℂ := ⋂ n, K1 n with hE1def
  set E2 : Set ℂ := ⋂ n, K2 n with hE2def
  have hE1conn : IsConnected E1 :=
    aqc_isConnected_iInter_antitone hK1anti hK1ne hK1compact hK1conn
  have hE2conn : IsConnected E2 :=
    aqc_isConnected_iInter_antitone hK2anti hK2ne hK2compact hK2conn
  -- boundary coverage: frontier V ⊆ E1 ∪ E2
  have hVeq : V = h '' annulus r₁ r₂ := hhomeo.2.2.1.symm
  have hfrontier : frontier V ⊆ E1 ∪ E2 := by
    intro p hp
    have hpcl : p ∈ closure V := hp.1
    have hpnV : p ∉ V := by rw [← hVopen.interior_eq]; exact hp.2
    obtain ⟨z, hzV, hztend⟩ := mem_closure_iff_seq_limit.mp hpcl
    have hzV' : ∀ n, z n ∈ h '' annulus r₁ r₂ := fun n => by
      have h2 := hzV n; rw [hVeq] at h2; exact h2
    set w : ℕ → ℂ := fun n => Function.invFunOn h (annulus r₁ r₂) (z n) with hwdef
    have hwmem : ∀ n, w n ∈ annulus r₁ r₂ := fun n => Function.invFunOn_mem (hzV' n)
    have hwh : ∀ n, h (w n) = z n := fun n => Function.invFunOn_eq (hzV' n)
    have hwball : ∀ n, w n ∈ closedBall (0:ℂ) r₂ :=
      fun n => mem_closedBall_zero_iff.mpr (hwmem n).2.le
    obtain ⟨w', hw'mem, φ, hφmono, hφtend⟩ :=
      (isCompact_closedBall (0:ℂ) r₂).tendsto_subseq hwball
    have hnormtend : Tendsto (fun n => ‖(w ∘ φ) n‖) atTop (𝓝 ‖w'‖) :=
      (continuous_norm.tendsto w').comp hφtend
    have hw'lb : r₁ ≤ ‖w'‖ :=
      ge_of_tendsto hnormtend (Filter.Eventually.of_forall fun n => (hwmem (φ n)).1.le)
    have hw'ub : ‖w'‖ ≤ r₂ := mem_closedBall_zero_iff.mp hw'mem
    have hzφtend : Tendsto (z ∘ φ) atTop (𝓝 p) := hztend.comp hφmono.tendsto_atTop
    rcases hw'lb.eq_or_lt with hcase1 | hcase1
    · -- ‖w'‖ = r₁ : p ∈ E1
      left
      refine mem_iInter.mpr fun n => ?_
      apply aqc_mem_closure_of_eventually_tendsto _ hzφtend
      have hlt : ∀ᶠ j in atTop, ‖(w ∘ φ) j‖ < r₁ + δ n :=
        hnormtend.eventually_lt_const (by rw [← hcase1]; linarith [hδpos n])
      filter_upwards [hlt] with j hj
      have hmem : (w ∘ φ) j ∈ annulus r₁ (r₁ + δ n) := ⟨(hwmem (φ j)).1, hj⟩
      show (z ∘ φ) j ∈ h '' annulus r₁ (r₁ + δ n)
      rw [show (z ∘ φ) j = h ((w ∘ φ) j) from (hwh (φ j)).symm]
      exact mem_image_of_mem h hmem
    · rcases hw'ub.eq_or_lt with hcase2 | hcase2
      · -- ‖w'‖ = r₂ : p ∈ E2
        right
        refine mem_iInter.mpr fun n => ?_
        apply aqc_mem_closure_of_eventually_tendsto _ hzφtend
        have hgt : ∀ᶠ j in atTop, r₂ - δ n < ‖(w ∘ φ) j‖ :=
          hnormtend.eventually_const_lt (by rw [hcase2]; linarith [hδpos n])
        filter_upwards [hgt] with j hj
        have hmem : (w ∘ φ) j ∈ annulus (r₂ - δ n) r₂ := ⟨hj, (hwmem (φ j)).2⟩
        show (z ∘ φ) j ∈ h '' annulus (r₂ - δ n) r₂
        rw [show (z ∘ φ) j = h ((w ∘ φ) j) from (hwh (φ j)).symm]
        exact mem_image_of_mem h hmem
      · -- interior case: contradiction
        exfalso
        have hw'ann : w' ∈ annulus r₁ r₂ := ⟨hcase1, hcase2⟩
        have hzφtend2 : Tendsto (z ∘ φ) atTop (𝓝 (h w')) := by
          have heq : z ∘ φ = h ∘ (w ∘ φ) := by
            funext j; exact (hwh (φ j)).symm
          rw [heq]
          exact (hhomeo.1.continuousAt
            ((isOpen_annulus r₁ r₂).mem_nhds hw'ann)).tendsto.comp hφtend
        have hpeq : p = h w' := tendsto_nhds_unique hzφtend hzφtend2
        rw [hpeq] at hpnV
        exact hpnV (hVeq ▸ mem_image_of_mem h hw'ann)
  -- ---------------------------------------------------------------------------------------------
  -- Last step (leader -68): `E1`, `E2` avoid `V`, lie on opposite sides of the Jordan curve
  -- `J = h(|z| = ρ)`, and every complementary component contains one of them.
  -- ---------------------------------------------------------------------------------------------
  have hVmem : ∀ w ∈ annulus r₁ r₂, h w ∈ V := fun w hw => hVeq ▸ mem_image_of_mem h hw
  -- a point of `V` whose preimage lies outside a closed set `T ⊇ S` is not in `closure (h '' S)`
  have hnotin : ∀ (S T : Set ℂ), S ⊆ annulus r₁ r₂ → IsClosed T → S ⊆ T →
      ∀ w ∈ annulus r₁ r₂, w ∉ T → h w ∉ closure (h '' S) := by
    intro S T hS hT hST w hw hwT hcl
    have hg : ContinuousAt (Function.invFunOn h (annulus r₁ r₂)) (h w) :=
      (hhomeo.2.2.2 (h w) (hVmem w hw)).continuousAt (hVopen.mem_nhds (hVmem w hw))
    have h1 := mem_closure_image hg hcl
    rw [hhomeo.2.1.leftInvOn_invFunOn hw] at h1
    have h2 : Function.invFunOn h (annulus r₁ r₂) '' (h '' S) ⊆ T := by
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      rw [hhomeo.2.1.leftInvOn_invFunOn (hS ha)]
      exact hST ha
    exact hwT (closure_minimal h2 hT h1)
  have hδtend : ∀ ε > 0, ∃ n : ℕ, δ n < ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt ((r₂ - r₁) / (2 * ε))
    refine ⟨n, ?_⟩
    simp only [hδdef]
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith [hn, hε]
  have hE1V : ∀ p ∈ E1, p ∉ V := by
    intro p hp hpV
    rw [hVeq] at hpV
    obtain ⟨w, hw, rfl⟩ := hpV
    obtain ⟨n, hn⟩ := hδtend (‖w‖ - r₁) (sub_pos.2 hw.1)
    exact hnotin _ {z : ℂ | ‖z‖ ≤ r₁ + δ n} (hK1sub n)
      (isClosed_le continuous_norm continuous_const) (fun z hz => hz.2.le) w hw
      (by show ¬ (‖w‖ ≤ r₁ + δ n); exact not_le.2 (by linarith)) (mem_iInter.1 hp n)
  have hE2V : ∀ p ∈ E2, p ∉ V := by
    intro p hp hpV
    rw [hVeq] at hpV
    obtain ⟨w, hw, rfl⟩ := hpV
    obtain ⟨n, hn⟩ := hδtend (r₂ - ‖w‖) (sub_pos.2 hw.2)
    exact hnotin _ {z : ℂ | r₂ - δ n ≤ ‖z‖} (hK2sub n)
      (isClosed_le continuous_const continuous_norm) (fun z hz => hz.1.le) w hw
      (by show ¬ (r₂ - δ n ≤ ‖w‖); exact not_le.2 (by linarith)) (mem_iInter.1 hp n)
  -- the middle circle and the two half-annuli
  set ρ : ℝ := (r₁ + r₂) / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hr1ρ : r₁ < ρ := by rw [hρdef]; linarith
  have hρr2 : ρ < r₂ := by rw [hρdef]; linarith
  have hnormρ : ‖(ρ : ℂ)‖ = ρ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
  have hρmem : (ρ : ℂ) ∈ annulus r₁ r₂ := ⟨by rw [hnormρ]; exact hr1ρ, by rw [hnormρ]; exact hρr2⟩
  have hsph : sphere (0 : ℂ) ρ ⊆ annulus r₁ r₂ := fun z hz => by
    rw [mem_sphere_zero_iff_norm] at hz
    exact ⟨by rw [hz]; exact hr1ρ, by rw [hz]; exact hρr2⟩
  set J : Set ℂ := h '' sphere 0 ρ with hJdef
  have hJ : IsJordanCurve (toExt J) :=
    iod_isJordanCurve_image_sphere hρpos (hhomeo.1.mono hsph) (hhomeo.2.1.mono hsph)
  obtain ⟨I, O, hIo, hOo, hIc, hOc, hIO, hIJ, hOJ, huniv, hIbdd, -⟩ :=
    jordan_curve_theorem_complex_bounded hJ
  have hJV : J ⊆ V := fun p hp => by
    obtain ⟨z, hz, rfl⟩ := hp
    exact hVmem z (hsph hz)
  have hJcpt : IsCompact J := isCompact_of_isJordanCurve_toExt hJ
  set A₁ : Set ℂ := annulus r₁ ρ with hA₁def
  set A₂ : Set ℂ := annulus ρ r₂ with hA₂def
  have hA₁sub : A₁ ⊆ annulus r₁ r₂ := fun z hz => ⟨hz.1, hz.2.trans hρr2⟩
  have hA₂sub : A₂ ⊆ annulus r₁ r₂ := fun z hz => ⟨hr1ρ.trans hz.1, hz.2⟩
  have hnormρ1 : ‖(((r₁ + ρ) / 2 : ℝ) : ℂ)‖ = (r₁ + ρ) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hnormρ2 : ‖(((ρ + r₂) / 2 : ℝ) : ℂ)‖ = (ρ + r₂) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hA₁ne : (h '' A₁).Nonempty :=
    ⟨_, mem_image_of_mem h (⟨by rw [hnormρ1]; linarith, by rw [hnormρ1]; linarith⟩ :
      (((r₁ + ρ) / 2 : ℝ) : ℂ) ∈ A₁)⟩
  have hA₂ne : (h '' A₂).Nonempty :=
    ⟨_, mem_image_of_mem h (⟨by rw [hnormρ2]; linarith, by rw [hnormρ2]; linarith⟩ :
      (((ρ + r₂) / 2 : ℝ) : ℂ) ∈ A₂)⟩
  have hA₁pre : IsPreconnected (h '' A₁) :=
    (isPreconnected_annulus hr1).image h (hhomeo.1.mono hA₁sub)
  have hA₂pre : IsPreconnected (h '' A₂) :=
    (isPreconnected_annulus hρpos.le).image h (hhomeo.1.mono hA₂sub)
  have hdisjJ : ∀ A : Set ℂ, A ⊆ annulus r₁ r₂ → (∀ z ∈ A, ‖z‖ ≠ ρ) → Disjoint (h '' A) J := by
    intro A hA hAρ
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨s, hs, hsa⟩
    have hsa' : s = a := hhomeo.2.1 (hsph hs) (hA ha) hsa
    rw [mem_sphere_zero_iff_norm] at hs
    exact hAρ a ha (hsa' ▸ hs)
  have hsubIO : ∀ A : Set ℂ, Disjoint (h '' A) J → h '' A ⊆ I ∪ O := by
    intro A hd x hx
    have hxu : x ∈ I ∪ O ∪ J := by rw [huniv]; exact mem_univ x
    rcases hxu with hIO' | hJ'
    · exact hIO'
    · exact absurd hJ' (Set.disjoint_left.1 hd hx)
  have hside : ∀ A : Set ℂ, (h '' A).Nonempty → IsPreconnected (h '' A) → Disjoint (h '' A) J →
      h '' A ⊆ I ∨ h '' A ⊆ O := by
    intro A _ hpre hd
    by_cases hc : (h '' A ∩ I).Nonempty
    · exact Or.inl (hpre.subset_left_of_subset_union hIo hOo hIO (hsubIO A hd) hc)
    · right
      intro x hx
      rcases hsubIO A hd hx with hxI | hxO
      · exact absurd ⟨x, hx, hxI⟩ hc
      · exact hxO
  have hA₁ρ : ∀ z ∈ A₁, ‖z‖ ≠ ρ := fun z hz => hz.2.ne
  have hA₂ρ : ∀ z ∈ A₂, ‖z‖ ≠ ρ := fun z hz => hz.1.ne'
  have hcover : V ⊆ h '' A₁ ∪ J ∪ h '' A₂ := by
    intro x hx
    rw [hVeq] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rcases lt_trichotomy ‖z‖ ρ with hlt | heq | hgt
    · exact Or.inl (Or.inl (mem_image_of_mem h ⟨hz.1, hlt⟩))
    · exact Or.inl (Or.inr (mem_image_of_mem h (mem_sphere_zero_iff_norm.2 heq)))
    · exact Or.inr (mem_image_of_mem h ⟨hgt, hz.2⟩)
  -- the closure of a side lies in the side together with `J`
  have hclside : ∀ W W' : Set ℂ, IsOpen W' → Disjoint W W' → W ∪ W' ∪ J = univ →
      closure W ⊆ W ∪ J := by
    intro W W' hW' hWW' hu x hx
    have hxu : x ∈ W ∪ W' ∪ J := by rw [hu]; exact mem_univ x
    rcases hxu with (hxW | hxW') | hxJ
    · exact Or.inl hxW
    · exfalso
      have h1 : x ∈ closure (W' ∩ W) := hW'.inter_closure ⟨hxW', hx⟩
      rw [hWW'.symm.inter_eq, closure_empty] at h1
      exact h1
    · exact Or.inr hxJ
  have hOIJ : O ∪ I ∪ J = univ := by rw [union_comm O I]; exact huniv
  have hclI : closure I ⊆ I ∪ J := hclside I O hOo hIO huniv
  have hclO : closure O ⊆ O ∪ J := hclside O I hIo hIO.symm hOIJ
  -- both sides meet `V`
  have hmeets : ∀ W W' : Set ℂ, IsOpen W → IsOpen W' → W.Nonempty → W'.Nonempty →
      Disjoint W W' → W ∪ W' ∪ J = univ → (W ∩ V).Nonempty := by
    intro W W' hW hW' hWne hW'ne hWW' hu
    have hclW : closure W ⊆ W ∪ J := hclside W W' hW' hWW' hu
    have hnotclosed : ¬ IsClosed W := by
      intro hWc
      rcases isClopen_iff.1 ⟨hWc, hW⟩ with h0 | hu'
      · exact hWne.ne_empty h0
      · obtain ⟨y, hy⟩ := hW'ne
        exact Set.disjoint_left.1 hWW' (by rw [hu']; exact mem_univ y) hy
    obtain ⟨x, hxcl, hxW⟩ : ∃ x, x ∈ closure W ∧ x ∉ W := by
      by_contra hcon
      exact hnotclosed (closure_subset_iff_isClosed.1 fun x hx =>
        by_contra fun hxW => hcon ⟨x, hx, hxW⟩)
    have hxJ : x ∈ J := by
      rcases hclW hxcl with hxW' | hxJ
      · exact absurd hxW' hxW
      · exact hxJ
    obtain ⟨y, hyV, hyW⟩ := mem_closure_iff.1 hxcl V hVopen (hJV hxJ)
    exact ⟨y, hyW, hyV⟩
  have hIV : (I ∩ V).Nonempty := hmeets I O hIo hOo hIc.1 hOc.1 hIO huniv
  have hOV : (O ∩ V).Nonempty := hmeets O I hOo hIo hOc.1 hIc.1 hIO.symm hOIJ
  have hnotboth : ¬ (h '' A₁ ⊆ I ∧ h '' A₂ ⊆ I) := by
    rintro ⟨h1, h2⟩
    obtain ⟨y, hyO, hyV⟩ := hOV
    rcases hcover hyV with (hy1 | hyJ) | hy2
    · exact Set.disjoint_left.1 hIO (h1 hy1) hyO
    · exact Set.disjoint_left.1 hOJ hyO hyJ
    · exact Set.disjoint_left.1 hIO (h2 hy2) hyO
  have hnotboth' : ¬ (h '' A₁ ⊆ O ∧ h '' A₂ ⊆ O) := by
    rintro ⟨h1, h2⟩
    obtain ⟨y, hyI, hyV⟩ := hIV
    rcases hcover hyV with (hy1 | hyJ) | hy2
    · exact Set.disjoint_left.1 hIO hyI (h1 hy1)
    · exact Set.disjoint_left.1 hIJ hyI hyJ
    · exact Set.disjoint_left.1 hIO hyI (h2 hy2)
  -- `E1`, `E2` sit in the closures of the two half-annulus images
  have hE1cl : E1 ⊆ closure (h '' A₁) := by
    refine (iInter_subset K1 0).trans (closure_mono (image_mono fun z hz => ?_))
    exact ⟨hz.1, hz.2.trans_le (by linarith [hδsmall 0, hρdef])⟩
  have hE2cl : E2 ⊆ closure (h '' A₂) := by
    refine (iInter_subset K2 0).trans (closure_mono (image_mono fun z hz => ?_))
    exact ⟨(by linarith [hδsmall 0, hρdef] : ρ ≤ r₂ - δ 0).trans_lt hz.1, hz.2⟩
  have hEJ : ∀ E W : Set ℂ, (∀ p ∈ E, p ∉ V) → E ⊆ closure W → closure W ⊆ W ∪ J → E ⊆ W := by
    intro E W hEV hEW hclW p hp
    rcases hclW (hEW hp) with hpW | hpJ
    · exact hpW
    · exact absurd (hJV hpJ) (hEV p hp)
  have hsides : (E1 ⊆ I ∧ E2 ⊆ O) ∨ (E1 ⊆ O ∧ E2 ⊆ I) := by
    rcases hside A₁ hA₁ne hA₁pre (hdisjJ A₁ hA₁sub hA₁ρ) with h1I | h1O
    · rcases hside A₂ hA₂ne hA₂pre (hdisjJ A₂ hA₂sub hA₂ρ) with h2I | h2O
      · exact absurd ⟨h1I, h2I⟩ hnotboth
      · exact Or.inl ⟨hEJ E1 I hE1V (hE1cl.trans (closure_mono h1I)) hclI,
          hEJ E2 O hE2V (hE2cl.trans (closure_mono h2O)) hclO⟩
    · rcases hside A₂ hA₂ne hA₂pre (hdisjJ A₂ hA₂sub hA₂ρ) with h2I | h2O
      · exact Or.inr ⟨hEJ E1 O hE1V (hE1cl.trans (closure_mono h1O)) hclO,
          hEJ E2 I hE2V (hE2cl.trans (closure_mono h2I)) hclI⟩
      · exact absurd ⟨h1O, h2O⟩ hnotboth'
  -- the two open sets of `ℂ̄` separated by `J`
  have hIJc : I ∪ J = Oᶜ := by
    ext x
    constructor
    · rintro (hxI | hxJ) hxO
      · exact Set.disjoint_left.1 hIO hxI hxO
      · exact Set.disjoint_left.1 hOJ hxO hxJ
    · intro hxO
      have hxu : x ∈ I ∪ O ∪ J := by rw [huniv]; exact mem_univ x
      rcases hxu with (hxI | hxO') | hxJ
      · exact Or.inl hxI
      · exact absurd hxO' hxO
      · exact Or.inr hxJ
  have hUIo : IsOpen (toExt I) := OnePoint.isOpen_image_coe.2 hIo
  have hUOcompl : (toExt O ∪ {extInf})ᶜ = toExt (I ∪ J) := by
    ext x
    induction x using OnePoint.rec with
    | infty =>
      simp only [mem_compl_iff, mem_union, mem_singleton_iff, or_true, not_true_eq_false,
        false_iff]
      exact extInf_mem_compl_toExt (I ∪ J)
    | coe z =>
      constructor
      · intro hx
        have hzO : z ∉ O := fun hzO => hx (Or.inl ⟨z, hzO, rfl⟩)
        exact ⟨z, by rw [hIJc]; exact hzO, rfl⟩
      · rintro ⟨y, hy, hyz⟩ hcon
        rw [OnePoint.coe_injective hyz, hIJc] at hy
        rcases hcon with ⟨y', hy', hy'z⟩ | hinf
        · exact hy (OnePoint.coe_injective hy'z ▸ hy')
        · exact OnePoint.coe_ne_infty z hinf
  have hUOo : IsOpen (toExt O ∪ {extInf}) := by
    have hcl : IsClosed (toExt (I ∪ J)) := by
      refine OnePoint.isClosed_image_coe.2 ⟨by rw [hIJc]; exact hOo.isClosed_compl, ?_⟩
      exact Metric.isCompact_of_isClosed_isBounded (by rw [hIJc]; exact hOo.isClosed_compl)
        (hIbdd.union hJcpt.isBounded)
    rw [← compl_compl (toExt O ∪ {extInf}), hUOcompl]
    exact hcl.isOpen_compl
  have hUdisj : Disjoint (toExt I) (toExt O ∪ {extInf}) := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, hzI, rfl⟩ (⟨y, hyO, hyz⟩ | hinf)
    · exact Set.disjoint_left.1 hIO hzI (OnePoint.coe_injective hyz ▸ hyO)
    · exact OnePoint.coe_ne_infty z hinf
  have hXsub : (toExt V)ᶜ ⊆ toExt I ∪ (toExt O ∪ {extInf}) := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact Or.inr (Or.inr rfl)
    | coe z =>
      have hzV : z ∉ V := fun hzV => hx ⟨z, hzV, rfl⟩
      have hzu : z ∈ I ∪ O ∪ J := by rw [huniv]; exact mem_univ z
      rcases hzu with (hzI | hzO) | hzJ
      · exact Or.inl ⟨z, hzI, rfl⟩
      · exact Or.inr (Or.inl ⟨z, hzO, rfl⟩)
      · exact absurd (hJV hzJ) hzV
  -- components of `ℂ̄ ∖ V`
  have hE1X : toExt E1 ⊆ (toExt V)ᶜ := by
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hqp⟩
    exact hE1V p hp (OnePoint.coe_injective hqp ▸ hq)
  have hE2X : toExt E2 ⊆ (toExt V)ᶜ := by
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hqp⟩
    exact hE2V p hp (OnePoint.coe_injective hqp ▸ hq)
  have hE1Xpre : IsPreconnected (toExt E1) :=
    hE1conn.isPreconnected.image _ OnePoint.continuous_coe.continuousOn
  have hE2Xpre : IsPreconnected (toExt E2) :=
    hE2conn.isPreconnected.image _ OnePoint.continuous_coe.continuousOn
  obtain ⟨p₀, hp₀⟩ := hE1conn.1
  obtain ⟨q₀, hq₀⟩ := hE2conn.1
  have hp₀X : (p₀ : ExtPlane) ∈ (toExt V)ᶜ := hE1X ⟨p₀, hp₀, rfl⟩
  have hq₀X : (q₀ : ExtPlane) ∈ (toExt V)ᶜ := hE2X ⟨q₀, hq₀, rfl⟩
  have hVbdd : Bornology.IsBounded V := hfclB.isBounded.subset hVsubfclB
  have hVne : (toExt V).Nonempty := ⟨_, ⟨_, hVmem _ hρmem, rfl⟩⟩
  have hfrX : frontier (toExt V) ⊆ toExt E1 ∪ toExt E2 := by
    rw [frontier_toExt_of_isBounded hVbdd hVopen]
    rintro _ ⟨p, hp, rfl⟩
    rcases hfrontier hp with h1 | h2
    · exact Or.inl ⟨p, h1, rfl⟩
    · exact Or.inr ⟨p, h2, rfl⟩
  have hcomp : ∀ x ∈ (toExt V)ᶜ,
      connectedComponentIn (toExt V)ᶜ x = connectedComponentIn (toExt V)ᶜ (p₀ : ExtPlane) ∨
      connectedComponentIn (toExt V)ᶜ x = connectedComponentIn (toExt V)ᶜ (q₀ : ExtPlane) := by
    intro x hx
    obtain ⟨y, hyW, hyfr⟩ :=
      aqc_connectedComponentIn_compl_meets_frontier (OnePoint.isOpen_image_coe.2 hVopen) hVne hx
    rcases hfrX hyfr with hy1 | hy2
    · left
      have hsub : toExt E1 ⊆ connectedComponentIn (toExt V)ᶜ y :=
        hE1Xpre.subset_connectedComponentIn hy1 hE1X
      exact (connectedComponentIn_eq hyW).trans (connectedComponentIn_eq (hsub ⟨p₀, hp₀, rfl⟩))
    · right
      have hsub : toExt E2 ⊆ connectedComponentIn (toExt V)ᶜ y :=
        hE2Xpre.subset_connectedComponentIn hy2 hE2X
      exact (connectedComponentIn_eq hyW).trans (connectedComponentIn_eq (hsub ⟨q₀, hq₀, rfl⟩))
  have hsep : ∀ U₁ U₂ : Set ExtPlane, IsOpen U₁ → IsOpen U₂ → Disjoint U₁ U₂ →
      (toExt V)ᶜ ⊆ U₁ ∪ U₂ → ∀ a b : ExtPlane, a ∈ (toExt V)ᶜ → b ∈ (toExt V)ᶜ → a ∈ U₁ → b ∈ U₂ →
      connectedComponentIn (toExt V)ᶜ a ≠ connectedComponentIn (toExt V)ᶜ b := by
    intro U₁ U₂ hU₁ hU₂ hd hsub a b ha hb haU hbU heq
    have hca : connectedComponentIn (toExt V)ᶜ a ⊆ U₁ :=
      isPreconnected_connectedComponentIn.subset_left_of_subset_union hU₁ hU₂ hd
        ((connectedComponentIn_subset _ _).trans hsub) ⟨a, mem_connectedComponentIn ha, haU⟩
    have hbmem : b ∈ connectedComponentIn (toExt V)ᶜ a := by
      rw [heq]; exact mem_connectedComponentIn hb
    exact Set.disjoint_left.1 hd (hca hbmem) hbU
  have hne : connectedComponentIn (toExt V)ᶜ (p₀ : ExtPlane) ≠
      connectedComponentIn (toExt V)ᶜ (q₀ : ExtPlane) := by
    rcases hsides with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hsep (toExt I) (toExt O ∪ {extInf}) hUIo hUOo hUdisj hXsub _ _ hp₀X hq₀X
        ⟨p₀, h1 hp₀, rfl⟩ (Or.inl ⟨q₀, h2 hq₀, rfl⟩)
    · exact hsep (toExt O ∪ {extInf}) (toExt I) hUOo hUIo hUdisj.symm
        (by rw [union_comm]; exact hXsub) _ _ hp₀X hq₀X (Or.inl ⟨p₀, h1 hp₀, rfl⟩)
        ⟨q₀, h2 hq₀, rfl⟩
  -- assembly
  have hVconn : IsConnected V := by
    rw [hVeq]
    exact ⟨⟨_, mem_image_of_mem h hρmem⟩, (isPreconnected_annulus hr1).image h hhomeo.1⟩
  show IsOpen V ∧ IsConnected V ∧ Nat.card (ConnectedComponents ↥((toExt V)ᶜ)) = 2
  refine ⟨hVopen, hVconn, ?_⟩
  rw [Nat.card_eq_two_iff]
  refine ⟨ConnectedComponents.mk ⟨(p₀ : ExtPlane), hp₀X⟩,
    ConnectedComponents.mk ⟨(q₀ : ExtPlane), hq₀X⟩, ?_, ?_⟩
  · intro hmk
    rw [ConnectedComponents.coe_eq_coe] at hmk
    apply hne
    rw [connectedComponentIn_eq_image hp₀X, connectedComponentIn_eq_image hq₀X, hmk]
  · ext c
    simp only [mem_insert_iff, mem_singleton_iff, mem_univ, iff_true]
    obtain ⟨⟨x, hx⟩, rfl⟩ := ConnectedComponents.surjective_coe c
    rcases hcomp x hx with h | h
    · left
      rw [ConnectedComponents.coe_eq_coe]
      apply Set.image_injective.2 Subtype.val_injective
      rw [← connectedComponentIn_eq_image hx, ← connectedComponentIn_eq_image hp₀X]
      exact h
    · right
      rw [ConnectedComponents.coe_eq_coe]
      apply Set.image_injective.2 Subtype.val_injective
      rw [← connectedComponentIn_eq_image hx, ← connectedComponentIn_eq_image hq₀X]
      exact h

/-! ### Piece E2 -/

/-- **E2 (owner -0f, after C).** `M(B) = ∞` iff some component of `ℂ̄ ∖ B` is a single point
(Theorem 2.1 with its uniqueness lemmas `thm2_1_canonical_unique_plane_annulus`,
`thm2_1_canonical_unique_disc_annulus`, `canonical_form_of_degenerate_component`). -/
theorem aqc_dcModulus_eq_top_iff {B : Set ℂ} (hB : IsDoublyConnected B) :
    dcModulus B = ⊤ ↔ ∃ x ∈ (toExt B)ᶜ, connectedComponentIn (toExt B)ᶜ x = {x} := by
  constructor
  · intro htop
    by_contra hnd
    push Not at hnd
    obtain ⟨r₁, r₂, hr₁, hr₂, hequiv⟩ := thm2_1_canonical_form_annulus hB hnd
    have hval := dcModulus_eq_of_equiv hB.1 hr₁ hr₂ hequiv
    rw [htop] at hval
    exact ENNReal.ofReal_ne_top hval.symm
  · rintro ⟨x, hx, hxpt⟩
    rcases canonical_form_of_degenerate_component hB hx hxpt with hequiv | hequiv
    · by_contra hne
      by_cases hex : ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ ConformallyEquivalent B (annulus r₁ r₂)
      · obtain ⟨r₁, r₂, hr₁, hr₂, hBann⟩ := hex
        exact thm2_1_canonical_unique_plane_annulus hr₁ hr₂
          ((hequiv.symm hB.1).trans hBann)
      · exact hne (by rw [dcModulus, if_neg hex])
    · by_contra hne
      by_cases hex : ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ ConformallyEquivalent B (annulus r₁ r₂)
      · obtain ⟨r₁, r₂, hr₁, hr₂, hBann⟩ := hex
        exact thm2_1_canonical_unique_disc_annulus hr₁ hr₂
          ((hequiv.symm hB.1).trans hBann)
      · exact hne (by rw [dcModulus, if_neg hex])

/-! ### Piece E3 -/

theorem aqc_normReal (t : ℝ) (ht : 0 ≤ t) : ‖(t : ℂ)‖ = t := by
  rw [Complex.norm_real, Real.norm_of_nonneg ht]

/-- A singleton connected component of `(toExt S)ᶜ` must be a closure point of `toExt S`
(otherwise it would have a connected neighbourhood, inside `(toExt S)ᶜ`, with more than one
point). -/
theorem aqc_mem_closure_of_singleton_component {S : Set ℂ} {x : ExtPlane}
    (hx : x ∈ (toExt S)ᶜ) (hxpt : connectedComponentIn (toExt S)ᶜ x = {x}) :
    x ∈ closure (toExt S) := by
  by_contra hxnc
  induction x using OnePoint.rec with
  | infty =>
    obtain ⟨R, hR⟩ := (isBounded_of_extInf_notMem_closure_toExt hxnc).subset_closedBall (0 : ℂ)
    set R' : ℝ := max R 0 with hR'def
    have hR'0 : 0 ≤ R' := le_max_right _ _
    have hSub : {z : ℂ | R' < ‖z‖} ⊆ Sᶜ := by
      intro z hz hzS
      have hzc : z ∈ closedBall (0 : ℂ) R := hR hzS
      rw [mem_closedBall, dist_zero_right] at hzc
      have hzR' : ‖z‖ ≤ R' := hzc.trans (le_max_left _ _)
      have hzgt : R' < ‖z‖ := hz
      linarith
    have hpre : IsPreconnected {z : ℂ | R' < ‖z‖} := isPreconnected_setOf_lt_norm hR'0
    have hunb : ¬ Bornology.IsBounded {z : ℂ | R' < ‖z‖} := by
      intro hbdd
      obtain ⟨r, hr⟩ := hbdd.subset_closedBall (0 : ℂ)
      have hpos : (0 : ℝ) ≤ max r R' + 1 := by positivity
      have h1 : ((max r R' + 1 : ℝ) : ℂ) ∈ {z : ℂ | R' < ‖z‖} := by
        show R' < ‖((max r R' + 1 : ℝ) : ℂ)‖
        rw [aqc_normReal _ hpos]
        linarith [le_max_right r R']
      have h2 : ((max r R' + 1 : ℝ) : ℂ) ∈ closedBall (0 : ℂ) r := hr h1
      rw [mem_closedBall, dist_zero_right, aqc_normReal _ hpos] at h2
      linarith [le_max_left r R']
    have hconn : IsPreconnected (toExt {z : ℂ | R' < ‖z‖} ∪ {extInf}) :=
      isPreconnected_toExt_union_extInf_of_unbounded hpre hunb
    have hsubcompl : toExt {z : ℂ | R' < ‖z‖} ∪ {extInf} ⊆ (toExt S)ᶜ := by
      rw [union_subset_iff]
      refine ⟨?_, singleton_subset_iff.2 hx⟩
      rintro _ ⟨z, hz, rfl⟩ ⟨z', hz'S, hz'eq⟩
      rw [OnePoint.coe_eq_coe] at hz'eq
      exact hSub hz (hz'eq ▸ hz'S)
    have hextInfmem : extInf ∈ toExt {z : ℂ | R' < ‖z‖} ∪ {extInf} := Or.inr rfl
    have hsubcomp := hconn.subset_connectedComponentIn hextInfmem hsubcompl
    rw [hxpt] at hsubcomp
    have hR'1 : (0 : ℝ) ≤ R' + 1 := by linarith
    have hz0 : R' < ‖((R' + 1 : ℝ) : ℂ)‖ := by rw [aqc_normReal _ hR'1]; linarith
    have hz0mem : (((R' + 1 : ℝ) : ℂ) : ExtPlane) ∈ toExt {z : ℂ | R' < ‖z‖} ∪ {extInf} :=
      Or.inl ⟨_, hz0, rfl⟩
    exact OnePoint.coe_ne_infty _ (mem_singleton_iff.1 (hsubcomp hz0mem))
  | coe x₀ =>
    have hnc' : x₀ ∉ closure S := by
      intro hmem
      apply hxnc
      have heq := OnePoint.isOpenEmbedding_coe.isInducing.closure_eq_preimage_closure_image S
      rw [heq, mem_preimage] at hmem
      exact hmem
    have hnc'' : x₀ ∈ (closure S)ᶜ := hnc'
    obtain ⟨r, hr0, hrsub⟩ :=
      Metric.isOpen_iff.mp (isClosed_closure (s := S)).isOpen_compl x₀ hnc''
    have hSub : ball x₀ r ⊆ Sᶜ := hrsub.trans (fun z hz hzS => hz (subset_closure hzS))
    have hpre : IsPreconnected (ball x₀ r) := (convex_ball x₀ r).isPreconnected
    have hsubcompl : toExt (ball x₀ r) ⊆ (toExt S)ᶜ := by
      rintro _ ⟨z, hz, rfl⟩ ⟨z', hz'S, hz'eq⟩
      rw [OnePoint.coe_eq_coe] at hz'eq
      exact hSub hz (hz'eq ▸ hz'S)
    have hconn : IsPreconnected (toExt (ball x₀ r)) :=
      hpre.image _ OnePoint.continuous_coe.continuousOn
    have hx₀mem : (x₀ : ExtPlane) ∈ toExt (ball x₀ r) := ⟨x₀, mem_ball_self hr0, rfl⟩
    have hsubcomp := hconn.subset_connectedComponentIn hx₀mem hsubcompl
    rw [hxpt] at hsubcomp
    have hr2 : (0 : ℝ) ≤ r / 2 := by linarith
    set z1 : ℂ := x₀ + ((r / 2 : ℝ) : ℂ) with hz1def
    have hz1ball : z1 ∈ ball x₀ r := by
      rw [mem_ball, hz1def, dist_eq_norm, add_sub_cancel_left, aqc_normReal _ hr2]
      linarith
    have hz1ne : z1 ≠ x₀ := by
      rw [hz1def]
      intro heq
      have hzero : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination heq
      rw [Complex.ofReal_eq_zero] at hzero
      linarith
    have hz1mem : (z1 : ExtPlane) ∈ toExt (ball x₀ r) := ⟨z1, hz1ball, rfl⟩
    have hzeq := mem_singleton_iff.1 (hsubcomp hz1mem)
    rw [OnePoint.coe_eq_coe] at hzeq
    exact hz1ne hzeq

/-- A singleton-open set (in a subspace) equals its own connected component in that subspace. -/
theorem aqc_connectedComponentIn_eq_singleton_of_isOpen {F : Set ExtPlane} {y : ExtPlane}
    (hy : y ∈ F) {U : Set ExtPlane} (hUo : IsOpen U) (hUF : U ∩ F = {y}) :
    connectedComponentIn F y = {y} := by
  rw [connectedComponentIn_eq_image hy]
  have hpre : (Subtype.val : F → ExtPlane) ⁻¹' U = {(⟨y, hy⟩ : F)} := by
    ext p
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro hp
      have : (p : ExtPlane) ∈ U ∩ F := ⟨hp, p.2⟩
      rw [hUF, mem_singleton_iff] at this
      exact Subtype.ext this
    · rintro rfl
      have : y ∈ U ∩ F := hUF ▸ rfl
      exact this.1
  have hUopen' : IsOpen ({(⟨y, hy⟩ : F)} : Set F) := hpre ▸ hUo.preimage continuous_subtype_val
  have hclopen : IsClopen ({(⟨y, hy⟩ : F)} : Set F) := ⟨isClosed_singleton, hUopen'⟩
  have hsub := hclopen.connectedComponent_subset (mem_singleton _)
  have hsup : {(⟨y, hy⟩ : F)} ⊆ connectedComponent (⟨y, hy⟩ : F) :=
    singleton_subset_iff.2 mem_connectedComponent
  rw [Subset.antisymm_iff.mpr ⟨hsub, hsup⟩, image_singleton]

/-- **E3 (owner -0f, after E2).** A one-point complementary component `{x}` of `B` is carried by a
homeomorphism defined near `B̄` to a one-point complementary component `{f x}` of `f(B)`. -/
theorem aqc_exists_singleton_component_image {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hf : IsHomeomorphOnto f D (f '' D)) (hfo : IsOpen (f '' D)) {B : Set ℂ}
    (hB : IsDoublyConnected B) (hBD : closure (toExt B) ⊆ toExt D)
    {x : ExtPlane} (hx : x ∈ (toExt B)ᶜ) (hxpt : connectedComponentIn (toExt B)ᶜ x = {x}) :
    ∃ y ∈ (toExt (f '' B))ᶜ, connectedComponentIn (toExt (f '' B))ᶜ y = {y} := by
  obtain ⟨hfc, hfi, hfimg, hfinv⟩ := hf
  have hxcl : x ∈ closure (toExt B) := aqc_mem_closure_of_singleton_component hx hxpt
  have hxD : x ∈ toExt D := hBD hxcl
  obtain ⟨x₀, hx₀D, hx₀eq⟩ := hxD
  subst hx₀eq
  have hx₀B : x₀ ∉ B := coe_mem_compl_toExt_iff.mp hx
  have hne : connectedComponentIn (toExt B)ᶜ (x₀ : ExtPlane) ≠
      connectedComponentIn (toExt B)ᶜ extInf := by
    intro heq
    have : extInf ∈ connectedComponentIn (toExt B)ᶜ (x₀ : ExtPlane) :=
      heq ▸ mem_connectedComponentIn (extInf_mem_compl_toExt B)
    rw [hxpt, mem_singleton_iff] at this
    exact OnePoint.coe_ne_infty x₀ this.symm
  obtain ⟨hopen, -, -⟩ := fill_component hB hx hne
  have hset_eq : {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ (x₀ : ExtPlane)} =
      {x₀} := by
    rw [hxpt]
    ext z
    simp only [mem_setOf_eq, mem_singleton_iff, OnePoint.coe_eq_coe]
  rw [hset_eq] at hopen
  have hBD' : B ⊆ D := by
    intro z hz
    exact coe_mem_toExt_iff.mp (hBD (subset_closure (mem_image_of_mem _ hz)))
  have hsub : B ∪ {x₀} ⊆ D := union_subset hBD' (singleton_subset_iff.2 hx₀D)
  have hopenimg : IsOpen (f '' (B ∪ {x₀})) :=
    isOpen_image_of_continuousOn_injOn_of_subset hD hfc hfi hsub hopen
  have himg_eq : f '' (B ∪ {x₀}) = f '' B ∪ {f x₀} := by
    rw [image_union, image_singleton]
  rw [himg_eq] at hopenimg
  have hfx₀notin : f x₀ ∉ f '' B := by
    rintro ⟨z, hzB, hzeq⟩
    exact hx₀B (hfi (hBD' hzB) hx₀D hzeq ▸ hzB)
  set y : ExtPlane := (f x₀ : ExtPlane) with hydef
  have hyF : y ∈ (toExt (f '' B))ᶜ := coe_mem_compl_toExt_iff.mpr hfx₀notin
  refine ⟨y, hyF, ?_⟩
  have htoExt_eq : toExt (f '' B ∪ {f x₀}) = toExt (f '' B) ∪ {y} := by
    rw [toExt_union, hydef]
    congr 1
    exact image_singleton
  have hUopen : IsOpen (toExt (f '' B) ∪ {y}) := by
    rw [← htoExt_eq]
    exact isOpen_toExt_iff.mpr hopenimg
  have hUF : (toExt (f '' B) ∪ {y}) ∩ (toExt (f '' B))ᶜ = {y} := by
    ext w
    simp only [mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hw | hw, hwc⟩
      · exact absurd hw hwc
      · exact hw
    · rintro rfl
      exact ⟨Or.inr rfl, hyF⟩
  exact aqc_connectedComponentIn_eq_singleton_of_isOpen hyF hUopen hUF

end LiZhongQC
