import LiZhongQC.Lemmas.S22gbStokes

open Complex Set Filter Topology MeasureTheory
open scoped Real

noncomputable section
namespace LiZhongQC

/-- Vertical lines are Lebesgue null in the plane. -/
theorem s22gb_vert_null (x : ℝ) : volume {z : ℂ | z.re = x} = 0 := by
  have h : {z : ℂ | z.re = x} = Complex.measurableEquivRealProd ⁻¹' (({x} : Set ℝ) ×ˢ (univ : Set ℝ)) := by
    ext z
    simp [Complex.measurableEquivRealProd]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- Horizontal lines are Lebesgue null in the plane. -/
theorem s22gb_horiz_null (y : ℝ) : volume {z : ℂ | z.im = y} = 0 := by
  have h : {z : ℂ | z.im = y} = Complex.measurableEquivRealProd ⁻¹' ((univ : Set ℝ) ×ˢ ({y} : Set ℝ)) := by
    ext z
    simp [Complex.measurableEquivRealProd]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- The frame of a rectangle is Lebesgue null. -/
theorem s22gb_frame_null (a b : ℂ) (hre : a.re ≤ b.re) (him : a.im ≤ b.im) :
    volume (wv_rectF a b) = 0 := by
  have hsub : wv_rectF a b ⊆ {z : ℂ | z.re = a.re} ∪ {z : ℂ | z.re = b.re} ∪
      ({z : ℂ | z.im = a.im} ∪ {z : ℂ | z.im = b.im}) := by
    intro z hz
    obtain ⟨hK, hO⟩ := hz
    rw [wv_rectK, Complex.mem_reProdIm, uIcc_of_le hre, uIcc_of_le him] at hK
    rw [wv_rectO, Complex.mem_reProdIm] at hO
    simp only [mem_union, mem_setOf_eq]
    by_contra hcon
    push_neg at hcon
    apply hO
    exact ⟨⟨lt_of_le_of_ne hK.1.1 (Ne.symm hcon.1.1), lt_of_le_of_ne hK.1.2 hcon.1.2⟩,
      lt_of_le_of_ne hK.2.1 (Ne.symm hcon.2.1), lt_of_le_of_ne hK.2.2 hcon.2.2⟩
  refine measure_mono_null hsub ?_
  refine measure_union_null (measure_union_null (s22gb_vert_null _) (s22gb_vert_null _))
    (measure_union_null (s22gb_horiz_null _) (s22gb_horiz_null _))

theorem s22gb_mem_rectK {p q z : ℂ} (hre : p.re ≤ q.re) (him : p.im ≤ q.im) :
    z ∈ wv_rectK p q ↔ (p.re ≤ z.re ∧ z.re ≤ q.re) ∧ (p.im ≤ z.im ∧ z.im ≤ q.im) := by
  rw [wv_rectK, Complex.mem_reProdIm, uIcc_of_le hre, uIcc_of_le him]
  simp only [mem_Icc]

theorem s22gb_mem_rectO {p q z : ℂ} :
    z ∈ wv_rectO p q ↔ (p.re < z.re ∧ z.re < q.re) ∧ (p.im < z.im ∧ z.im < q.im) := by
  rw [wv_rectO, Complex.mem_reProdIm]
  simp only [mem_Ioo]

/-- Sub-rectangles of the annulus. -/
theorem s22gb_strip_subset {a b c d p q : ℂ} (hp1 : a.re ≤ p.re) (hq1 : q.re ≤ b.re)
    (hp2 : a.im ≤ p.im) (hq2 : q.im ≤ b.im) (hpq1 : p.re ≤ q.re) (hpq2 : p.im ≤ q.im)
    (hout : q.re ≤ c.re ∨ d.re ≤ p.re ∨ q.im ≤ c.im ∨ d.im ≤ p.im) :
    wv_rectK p q ⊆ wv_rectK a b \ wv_rectO c d := by
  intro z hz
  rw [s22gb_mem_rectK hpq1 hpq2] at hz
  refine ⟨?_, ?_⟩
  · rw [s22gb_mem_rectK (hp1.trans (hpq1.trans hq1)) (hp2.trans (hpq2.trans hq2))]
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  · rw [s22gb_mem_rectO]
    rintro ⟨⟨h1, h2⟩, h3, h4⟩
    rcases hout with h | h | h | h <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]

/-- The annulus is the union of four closed strips. -/
theorem s22gb_annulus_eq {a b c d : ℂ} (h1 : a.re < c.re) (h2 : c.re < d.re) (h3 : d.re < b.re)
    (h4 : a.im < c.im) (h5 : c.im < d.im) (h6 : d.im < b.im) :
    wv_rectK a b \ wv_rectO c d =
      ((wv_rectK a ⟨c.re, b.im⟩ ∪ wv_rectK ⟨d.re, a.im⟩ b) ∪ wv_rectK ⟨c.re, a.im⟩ ⟨d.re, c.im⟩) ∪
        wv_rectK ⟨c.re, d.im⟩ ⟨d.re, b.im⟩ := by
  ext z
  simp only [mem_diff, mem_union]
  rw [s22gb_mem_rectK (by linarith) (by linarith), s22gb_mem_rectO,
    s22gb_mem_rectK (by simp <;> linarith) (by simp <;> linarith),
    s22gb_mem_rectK (by simp <;> linarith) (by simp <;> linarith),
    s22gb_mem_rectK (by simp <;> linarith) (by simp <;> linarith),
    s22gb_mem_rectK (by simp <;> linarith) (by simp <;> linarith)]
  simp only []
  constructor
  · rintro ⟨⟨⟨hz1, hz2⟩, hz3, hz4⟩, hO⟩
    by_cases hl : z.re ≤ c.re
    · left; left; left
      exact ⟨⟨hz1, hl⟩, hz3, hz4⟩
    by_cases hr : d.re ≤ z.re
    · left; left; right
      exact ⟨⟨hr, hz2⟩, hz3, hz4⟩
    push_neg at hl hr
    by_cases hb : z.im ≤ c.im
    · left; right
      exact ⟨⟨hl.le, hr.le⟩, hz3, hb⟩
    by_cases ht : d.im ≤ z.im
    · right
      exact ⟨⟨hl.le, hr.le⟩, ht, hz4⟩
    push_neg at hb ht
    exact absurd ⟨⟨hl, hr⟩, hb, ht⟩ hO
  · rintro (((⟨⟨hz1, hz2⟩, hz3, hz4⟩ | ⟨⟨hz1, hz2⟩, hz3, hz4⟩) |
      ⟨⟨hz1, hz2⟩, hz3, hz4⟩) | ⟨⟨hz1, hz2⟩, hz3, hz4⟩)
    · refine ⟨⟨⟨hz1, by linarith⟩, hz3, hz4⟩, ?_⟩
      rintro ⟨⟨h7, h8⟩, h9, h10⟩
      linarith
    · refine ⟨⟨⟨by linarith, hz2⟩, hz3, hz4⟩, ?_⟩
      rintro ⟨⟨h7, h8⟩, h9, h10⟩
      linarith
    · refine ⟨⟨⟨by linarith, by linarith⟩, hz3, by linarith⟩, ?_⟩
      rintro ⟨⟨h7, h8⟩, h9, h10⟩
      linarith
    · refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, hz4⟩, ?_⟩
      rintro ⟨⟨h7, h8⟩, h9, h10⟩
      linarith

theorem s22gb_split3 (f : ℝ → ℝ) {p q r s : ℝ} (hf : ContinuousOn f (Icc p s))
    (h1 : p ≤ q) (h2 : q ≤ r) (h3 : r ≤ s) :
    (∫ x in p..q, f x) + (∫ x in q..r, f x) + (∫ x in r..s, f x) = ∫ x in p..s, f x := by
  have hii : ∀ {x y : ℝ}, x ∈ Icc p s → y ∈ Icc p s → IntervalIntegrable f volume x y :=
    fun hx hy => (hf.mono (uIcc_subset_Icc hx hy)).intervalIntegrable
  have hp : p ∈ Icc p s := ⟨le_rfl, h1.trans (h2.trans h3)⟩
  have hq : q ∈ Icc p s := ⟨h1, h2.trans h3⟩
  have hr : r ∈ Icc p s := ⟨h1.trans h2, h3⟩
  have hs : s ∈ Icc p s := ⟨h1.trans (h2.trans h3), le_rfl⟩
  rw [intervalIntegral.integral_add_adjacent_intervals (hii hp hq) (hii hq hr),
    intervalIntegral.integral_add_adjacent_intervals ((hii hp hq).trans (hii hq hr)) (hii hr hs)]

/-- Stokes on a rectangular annulus, by four strips. The form is `C¹` on the closed annulus,
vanishes on the outer frame, and equals `1` on the inner frame. -/
theorem s22gb_annulus_stokes (u : ℂ → ℝ) (α : ℂ → ℂ → ℝ) {a b c d : ℂ}
    (h1 : a.re < c.re) (h2 : c.re < d.re) (h3 : d.re < b.re)
    (h4 : a.im < c.im) (h5 : c.im < d.im) (h6 : d.im < b.im)
    (hu : ∀ z ∈ wv_rectK a b \ wv_rectO c d, ContDiffAt ℝ 1 u z)
    (hα1 : ∀ z ∈ wv_rectK a b \ wv_rectO c d, ContDiffAt ℝ 1 (fun w => α w 1) z)
    (hαI : ∀ z ∈ wv_rectK a b \ wv_rectO c d, ContDiffAt ℝ 1 (fun w => α w I) z)
    (hu0 : ∀ z ∈ wv_rectF a b, u z = 0) (hu1 : ∀ z ∈ wv_rectF c d, u z = 1) :
    (∫ z in wv_rectK a b \ wv_rectO c d,
      (u z * (fderiv ℝ (fun w => α w I) z 1 - fderiv ℝ (fun w => α w 1) z I) +
        (fderiv ℝ u z 1 * α z I - fderiv ℝ u z I * α z 1))) =
      -s22cd_rectBoundary α c d := by
  classical
  set E := wv_rectK a b \ wv_rectO c d with hE
  set F : ℂ → ℝ := fun z =>
    (u z * (fderiv ℝ (fun w => α w I) z 1 - fderiv ℝ (fun w => α w 1) z I) +
      (fderiv ℝ u z 1 * α z I - fderiv ℝ u z I * α z 1)) with hF
  have hFc : ∀ z ∈ E, ContinuousAt F z := by
    intro z hz
    have hcu := hu z hz
    have hc1 := hα1 z hz
    have hcI := hαI z hz
    have d1 : ContinuousAt (fderiv ℝ u) z := (hcu.fderiv_right (m := 0) (by simp)).continuousAt
    have d2 : ContinuousAt (fderiv ℝ (fun w => α w 1)) z :=
      (hc1.fderiv_right (m := 0) (by simp)).continuousAt
    have d3 : ContinuousAt (fderiv ℝ (fun w => α w I)) z :=
      (hcI.fderiv_right (m := 0) (by simp)).continuousAt
    exact (hcu.continuousAt.mul ((d3.clm_apply continuousAt_const).sub
      (d2.clm_apply continuousAt_const))).add
      (((d1.clm_apply continuousAt_const).mul hcI.continuousAt).sub
        ((d1.clm_apply continuousAt_const).mul hc1.continuousAt))
  -- the four strips
  have hS1 : wv_rectK a ⟨c.re, b.im⟩ ⊆ E :=
    s22gb_strip_subset (le_refl _) (by simp <;> linarith) (le_refl _) (le_refl _)
      (by simp <;> linarith) (by simp <;> linarith) (Or.inl (by simp))
  have hS2 : wv_rectK ⟨d.re, a.im⟩ b ⊆ E :=
    s22gb_strip_subset (by simp <;> linarith) (le_refl _) (le_refl _) (by simp <;> linarith)
      (by simp <;> linarith) (by simp <;> linarith) (Or.inr (Or.inl (by simp)))
  have hS3 : wv_rectK ⟨c.re, a.im⟩ ⟨d.re, c.im⟩ ⊆ E :=
    s22gb_strip_subset (by simp <;> linarith) (by simp <;> linarith) (le_refl _)
      (by simp <;> linarith) (by simp <;> linarith) (by simp <;> linarith)
      (Or.inr (Or.inr (Or.inl (by simp))))
  have hS4 : wv_rectK ⟨c.re, d.im⟩ ⟨d.re, b.im⟩ ⊆ E :=
    s22gb_strip_subset (by simp <;> linarith) (by simp <;> linarith) (by simp <;> linarith) (le_refl _)
      (by simp <;> linarith) (by simp <;> linarith) (Or.inr (Or.inr (Or.inr (by simp))))
  have stokes : ∀ p q : ℂ, p.re ≤ q.re → p.im ≤ q.im → wv_rectK p q ⊆ E →
      (∫ z in wv_rectK p q, F z) = s22cd_rectBoundary (fun ζ v => u ζ * α ζ v) p q :=
    fun p q hre him hsub => s22gb_rect_stokes u α p q hre him
      (fun z hz => hu z (hsub hz)) (fun z hz => hα1 z (hsub hz)) (fun z hz => hαI z (hsub hz))
  have st1 := stokes a ⟨c.re, b.im⟩ (by simp <;> linarith) (by simp <;> linarith) hS1
  have st2 := stokes ⟨d.re, a.im⟩ b (by simp <;> linarith) (by simp <;> linarith) hS2
  have st3 := stokes ⟨c.re, a.im⟩ ⟨d.re, c.im⟩ (by simp <;> linarith) (by simp <;> linarith) hS3
  have st4 := stokes ⟨c.re, d.im⟩ ⟨d.re, b.im⟩ (by simp <;> linarith) (by simp <;> linarith) hS4
  -- integrability on the strips
  have hint : ∀ p q : ℂ, wv_rectK p q ⊆ E → IntegrableOn F (wv_rectK p q) := by
    intro p q hsub
    exact ContinuousOn.integrableOn_compact (wv_isCompact_rectK p q)
      (fun z hz => (hFc z (hsub hz)).continuousWithinAt)
  -- almost-disjointness
  have hadj : ∀ (s t line : Set ℂ), s ∩ t ⊆ line → volume line = 0 → AEDisjoint volume s t :=
    fun s t line h hn => measure_mono_null h hn
  have hmeas : ∀ p q : ℂ, NullMeasurableSet (wv_rectK p q) volume :=
    fun p q => (wv_isCompact_rectK p q).isClosed.measurableSet.nullMeasurableSet
  have d12 : AEDisjoint volume (wv_rectK a ⟨c.re, b.im⟩) (wv_rectK ⟨d.re, a.im⟩ b) := by
    refine hadj _ _ ∅ ?_ measure_empty
    intro z ⟨hz1, hz2⟩
    rw [s22gb_mem_rectK (by simp <;> linarith) (by simp <;> linarith)] at hz1 hz2
    simp at hz1 hz2
    exfalso
    linarith [hz1.1.2, hz2.1.1]
  have d13 : AEDisjoint volume (wv_rectK a ⟨c.re, b.im⟩) (wv_rectK ⟨c.re, a.im⟩ ⟨d.re, c.im⟩) := by
    refine hadj _ _ {z : ℂ | z.re = c.re} ?_ (s22gb_vert_null _)
    intro z ⟨hz1, hz2⟩
    rw [s22gb_mem_rectK (by simp <;> linarith) (by simp <;> linarith)] at hz1 hz2
    simp at hz1 hz2
    exact le_antisymm hz1.1.2 hz2.1.1
  have d23 : AEDisjoint volume (wv_rectK ⟨d.re, a.im⟩ b) (wv_rectK ⟨c.re, a.im⟩ ⟨d.re, c.im⟩) := by
    refine hadj _ _ {z : ℂ | z.re = d.re} ?_ (s22gb_vert_null _)
    intro z ⟨hz1, hz2⟩
    rw [s22gb_mem_rectK (by simp <;> linarith) (by simp <;> linarith)] at hz1 hz2
    simp at hz1 hz2
    exact le_antisymm hz2.1.2 hz1.1.1
  have d14 : AEDisjoint volume (wv_rectK a ⟨c.re, b.im⟩) (wv_rectK ⟨c.re, d.im⟩ ⟨d.re, b.im⟩) := by
    refine hadj _ _ {z : ℂ | z.re = c.re} ?_ (s22gb_vert_null _)
    intro z ⟨hz1, hz2⟩
    rw [s22gb_mem_rectK (by simp <;> linarith) (by simp <;> linarith)] at hz1 hz2
    simp at hz1 hz2
    exact le_antisymm hz1.1.2 hz2.1.1
  have d24 : AEDisjoint volume (wv_rectK ⟨d.re, a.im⟩ b) (wv_rectK ⟨c.re, d.im⟩ ⟨d.re, b.im⟩) := by
    refine hadj _ _ {z : ℂ | z.re = d.re} ?_ (s22gb_vert_null _)
    intro z ⟨hz1, hz2⟩
    rw [s22gb_mem_rectK (by simp <;> linarith) (by simp <;> linarith)] at hz1 hz2
    simp at hz1 hz2
    exact le_antisymm hz2.1.2 hz1.1.1
  have d34 : AEDisjoint volume (wv_rectK ⟨c.re, a.im⟩ ⟨d.re, c.im⟩) (wv_rectK ⟨c.re, d.im⟩ ⟨d.re, b.im⟩) := by
    refine hadj _ _ ∅ ?_ measure_empty
    intro z ⟨hz1, hz2⟩
    rw [s22gb_mem_rectK (by simp <;> linarith) (by simp <;> linarith)] at hz1 hz2
    simp at hz1 hz2
    linarith [hz1.2.2, hz2.2.1]
  have hunion : (∫ z in E, F z) =
      (∫ z in wv_rectK a ⟨c.re, b.im⟩, F z) + (∫ z in wv_rectK ⟨d.re, a.im⟩ b, F z) +
        (∫ z in wv_rectK ⟨c.re, a.im⟩ ⟨d.re, c.im⟩, F z) +
        (∫ z in wv_rectK ⟨c.re, d.im⟩ ⟨d.re, b.im⟩, F z) := by
    rw [hE, s22gb_annulus_eq h1 h2 h3 h4 h5 h6]
    rw [setIntegral_union₀ ((d14.union_left d24).union_left d34) (hmeas _ _)
      (((hint _ _ hS1).union (hint _ _ hS2)).union (hint _ _ hS3)) (hint _ _ hS4),
      setIntegral_union₀ (d13.union_left d23) (hmeas _ _)
        ((hint _ _ hS1).union (hint _ _ hS2)) (hint _ _ hS3),
      setIntegral_union₀ d12 (hmeas _ _) (hint _ _ hS1) (hint _ _ hS2)]
  -- boundary algebra
  have hlineP : ∀ y0 : ℝ, a.im ≤ y0 → y0 ≤ b.im → (y0 ≤ c.im ∨ d.im ≤ y0) →
      ContinuousOn (fun x : ℝ => u ((x : ℂ) + (y0 : ℂ) * I) * α ((x : ℂ) + (y0 : ℂ) * I) 1)
        (Icc a.re b.re) := by
    intro y0 hy1 hy2 hy3 x hx
    have hz : ((x : ℂ) + (y0 : ℂ) * I) ∈ E := by
      refine ⟨(s22gb_mem_rectK (by linarith) (by linarith)).2 ?_, ?_⟩
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
        exact ⟨⟨by simpa using hx.1, by simpa using hx.2⟩, by simpa using hy1, by simpa using hy2⟩
      · rw [s22gb_mem_rectO]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
        rintro ⟨_, h7, h8⟩
        rcases hy3 with h | h <;> simp at h7 h8 <;> linarith
    have hcont : ContinuousAt (fun x : ℝ => (x : ℂ) + (y0 : ℂ) * I) x := by fun_prop
    exact ((ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + (y0 : ℂ) * I) (g := u)
      (hu _ hz).continuousAt hcont).mul
      (ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + (y0 : ℂ) * I) (g := fun w => α w 1)
        (hα1 _ hz).continuousAt hcont)).continuousWithinAt
  have hlineQ : ∀ x0 : ℝ, a.re ≤ x0 → x0 ≤ b.re → (x0 ≤ c.re ∨ d.re ≤ x0) →
      ContinuousOn (fun y : ℝ => u ((x0 : ℂ) + (y : ℂ) * I) * α ((x0 : ℂ) + (y : ℂ) * I) I)
        (Icc a.im b.im) := by
    intro x0 hx1 hx2 hx3 y hy
    have hz : ((x0 : ℂ) + (y : ℂ) * I) ∈ E := by
      refine ⟨(s22gb_mem_rectK (by linarith) (by linarith)).2 ?_, ?_⟩
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
        exact ⟨⟨by simpa using hx1, by simpa using hx2⟩, by simpa using hy.1, by simpa using hy.2⟩
      · rw [s22gb_mem_rectO]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
        rintro ⟨⟨h7, h8⟩, _⟩
        rcases hx3 with h | h <;> simp at h7 h8 <;> linarith
    have hcont : ContinuousAt (fun y : ℝ => (x0 : ℂ) + (y : ℂ) * I) y := by fun_prop
    exact ((ContinuousAt.comp (f := fun y : ℝ => (x0 : ℂ) + (y : ℂ) * I) (g := u)
      (hu _ hz).continuousAt hcont).mul
      (ContinuousAt.comp (f := fun y : ℝ => (x0 : ℂ) + (y : ℂ) * I) (g := fun w => α w I)
        (hαI _ hz).continuousAt hcont)).continuousWithinAt
  have e1 := s22gb_split3 (fun x : ℝ => u ((x : ℂ) + (a.im : ℂ) * I) * α ((x : ℂ) + (a.im : ℂ) * I) 1)
    (hlineP a.im le_rfl (by linarith) (Or.inl h4.le)) h1.le h2.le h3.le
  have e2 := s22gb_split3 (fun x : ℝ => u ((x : ℂ) + (b.im : ℂ) * I) * α ((x : ℂ) + (b.im : ℂ) * I) 1)
    (hlineP b.im (by linarith) le_rfl (Or.inr h6.le)) h1.le h2.le h3.le
  have e3 := s22gb_split3 (fun y : ℝ => u ((c.re : ℂ) + (y : ℂ) * I) * α ((c.re : ℂ) + (y : ℂ) * I) I)
    (hlineQ c.re (by linarith) (by linarith) (Or.inl le_rfl)) h4.le h5.le h6.le
  have e4 := s22gb_split3 (fun y : ℝ => u ((d.re : ℂ) + (y : ℂ) * I) * α ((d.re : ℂ) + (y : ℂ) * I) I)
    (hlineQ d.re (by linarith) (by linarith) (Or.inr le_rfl)) h4.le h5.le h6.le
  have hbig : s22cd_rectBoundary (fun ζ v => u ζ * α ζ v) a b = 0 :=
    s22cd_rectBoundary_zero (fun ζ hζ v => by simp [hu0 ζ hζ])
  have hsmall : s22cd_rectBoundary (fun ζ v => u ζ * α ζ v) c d = s22cd_rectBoundary α c d :=
    s22cd_rectBoundary_congr (fun ζ hζ v => by rw [hu1 ζ hζ, one_mul])
  have hsum : s22cd_rectBoundary (fun ζ v => u ζ * α ζ v) a ⟨c.re, b.im⟩ +
      s22cd_rectBoundary (fun ζ v => u ζ * α ζ v) ⟨d.re, a.im⟩ b +
      s22cd_rectBoundary (fun ζ v => u ζ * α ζ v) ⟨c.re, a.im⟩ ⟨d.re, c.im⟩ +
      s22cd_rectBoundary (fun ζ v => u ζ * α ζ v) ⟨c.re, d.im⟩ ⟨d.re, b.im⟩ =
      s22cd_rectBoundary (fun ζ v => u ζ * α ζ v) a b -
        s22cd_rectBoundary (fun ζ v => u ζ * α ζ v) c d := by
    simp only [s22cd_rectBoundary]
    linarith [e1, e2, e3, e4]
  rw [hunion, st1, st2, st3, st4, hsum, hbig, hsmall]
  ring

end LiZhongQC
