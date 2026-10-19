import LiZhongQC.Ch02.S13_Representation
import LiZhongQC.Lemmas.RectangleQuad
import LiZhongQC.Lemmas.Mobius

open Complex Set Metric Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section
namespace LiZhongQC

theorem s32w_reflect_rect_mem {a b : ℝ} (z : ℂ) :
    z ∈ conj ⁻¹' rectangle a b ↔ 0 < z.re ∧ z.re < a ∧ -b < z.im ∧ z.im < 0 := by
  simp only [rectangle, mem_preimage, mem_setOf_eq, Complex.conj_re, Complex.conj_im]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, by linarith, by linarith⟩

theorem s32w_seg_mem {a : ℝ} (ha : 0 < a) (z : ℂ) :
    z ∈ openSegment ℝ (0 : ℂ) (a : ℂ) ↔ z.im = 0 ∧ 0 < z.re ∧ z.re < a := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    simp only [smul_zero, zero_add, Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero, zero_mul]
    refine ⟨trivial, by positivity, ?_⟩
    nlinarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨1 - z.re / a, z.re / a, ?_, ?_, by ring, ?_⟩
    · have : z.re / a < 1 := (div_lt_one ha).2 h3
      linarith
    · positivity
    · apply Complex.ext
      · simp [Complex.real_smul]
        field_simp
      · simp [Complex.real_smul, h1]

theorem s32w_union_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    rectangle a b ∪ conj ⁻¹' rectangle a b ∪ openSegment ℝ (0 : ℂ) (a : ℂ) =
      {z : ℂ | 0 < z.re ∧ z.re < a ∧ -b < z.im ∧ z.im < b} := by
  ext z
  simp only [mem_union, s32w_reflect_rect_mem, s32w_seg_mem ha]
  simp only [rectangle, mem_setOf_eq]
  constructor
  · rintro ((⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩) | ⟨h1, h2, h3⟩)
    · exact ⟨h1, h2, by linarith, h4⟩
    · exact ⟨h1, h2, h3, by linarith⟩
    · exact ⟨h2, h3, by rw [h1]; linarith, by rw [h1]; exact hb⟩
  · rintro ⟨h1, h2, h3, h4⟩
    rcases lt_trichotomy z.im 0 with h | h | h
    · exact Or.inl (Or.inr ⟨h1, h2, h3, h⟩)
    · exact Or.inr ⟨h, h1, h2⟩
    · exact Or.inl (Or.inl ⟨h1, h2, h, h4⟩)

theorem s32w_isOpen_union {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsOpen (rectangle a b ∪ conj ⁻¹' rectangle a b ∪ openSegment ℝ (0 : ℂ) (a : ℂ)) := by
  rw [s32w_union_eq ha hb]
  have hre := Complex.continuous_re
  have him := Complex.continuous_im
  simp only [setOf_and]
  exact (isOpen_lt continuous_const hre).inter ((isOpen_lt hre continuous_const).inter
    ((isOpen_lt continuous_const him).inter (isOpen_lt him continuous_const)))

theorem s32w_mobius_translate (c : ℂ) (z : ℂ) :
    mobiusHomeomorph 1 c 0 1 (by simp) (z : ExtPlane) = ((z + c : ℂ) : ExtPlane) := by
  rw [mobiusHomeomorph_apply, mobiusExt_coe (by simp)]
  simp [mobiusFn]

theorem s32w_jordan_reflect {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsJordanDomain (conj ⁻¹' rectangle a b) := by
  refine uq_isJordanDomain_image (mobiusHomeomorph 1 (-(b : ℂ) * I) 0 1 (by simp))
    (isJordanDomain_rectangle ha hb) ?_
  ext w
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨z + (-(b : ℂ) * I), ?_, ?_⟩
    · rw [s32w_reflect_rect_mem]
      simp only [rectangle, mem_setOf_eq] at hz
      simp only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      refine ⟨by linarith [hz.1], by linarith [hz.2.1], by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩
    · exact (s32w_mobius_translate _ z).symm
  · rintro ⟨y, hy, rfl⟩
    refine ⟨((y + (b : ℂ) * I : ℂ) : ExtPlane), ⟨y + (b : ℂ) * I, ?_, rfl⟩, ?_⟩
    · rw [s32w_reflect_rect_mem] at hy
      simp only [rectangle, mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      refine ⟨by linarith [hy.1], by linarith [hy.2.1], by linarith [hy.2.2.1], by linarith [hy.2.2.2]⟩
    · rw [s32w_mobius_translate]
      congr 1
      ring

theorem s32w_dz_congr {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (heq : EqOn f g U) {z : ℂ}
    (hz : z ∈ U) : dz f z = dz g z ∧ dzbar f z = dzbar g z := by
  have h : f =ᶠ[𝓝 z] g := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) heq
  have h2 : fderiv ℝ f z = fderiv ℝ g z := h.fderiv_eq
  refine ⟨?_, ?_⟩ <;> simp [dz, dzbar, h2]

theorem s32w_seg_closure {a b : ℝ} (hb : 0 < b) {z : ℂ} (hz0 : z.im = 0) (hz1 : 0 < z.re)
    (hz2 : z.re < a) :
    z ∈ closure (rectangle a b) ∧ z ∈ closure (conj ⁻¹' rectangle a b) := by
  constructor
  · rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨z + ((min (ε / 2) (b / 2) : ℝ) : ℂ) * I, ?_, ?_⟩
    · have h1 : 0 < min (ε / 2) (b / 2) := lt_min (by linarith) (by linarith)
      have h2 : min (ε / 2) (b / 2) ≤ b / 2 := min_le_right _ _
      simp only [rectangle, mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      refine ⟨by linarith, by linarith, by nlinarith, by nlinarith⟩
    · have h2 : min (ε / 2) (b / 2) ≤ ε / 2 := min_le_left _ _
      have h1 : 0 < min (ε / 2) (b / 2) := lt_min (by linarith) (by linarith)
      rw [dist_eq_norm]
      have : z - (z + ((min (ε / 2) (b / 2) : ℝ) : ℂ) * I) =
          -(((min (ε / 2) (b / 2) : ℝ) : ℂ) * I) := by ring
      rw [this, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_of_nonneg h1.le]
      linarith
  · rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨z - ((min (ε / 2) (b / 2) : ℝ) : ℂ) * I, ?_, ?_⟩
    · have h1 : 0 < min (ε / 2) (b / 2) := lt_min (by linarith) (by linarith)
      have h2 : min (ε / 2) (b / 2) ≤ b / 2 := min_le_right _ _
      rw [s32w_reflect_rect_mem]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      refine ⟨by linarith, by linarith, by nlinarith, by nlinarith⟩
    · have h2 : min (ε / 2) (b / 2) ≤ ε / 2 := min_le_left _ _
      have h1 : 0 < min (ε / 2) (b / 2) := lt_min (by linarith) (by linarith)
      rw [dist_eq_norm]
      have : z - (z - ((min (ε / 2) (b / 2) : ℝ) : ℂ) * I) =
          ((min (ε / 2) (b / 2) : ℝ) : ℂ) * I := by ring
      rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_of_nonneg h1.le]
      linarith

theorem s32w_qc_reflect_rectangle {a b K : ℝ} (ha : 0 < a) (hb : 0 < b) {h : ℂ → ℂ}
    (hK : IsKQC h (rectangle a b) K)
    (hc : ContinuousOn h (rectangle a b ∪ openSegment ℝ (0 : ℂ) a))
    (hi : InjOn h (rectangle a b ∪ openSegment ℝ (0 : ℂ) a))
    (hup : MapsTo h (rectangle a b) upperHalf)
    (hre : ∀ z ∈ openSegment ℝ (0 : ℂ) a, (h z).im = 0) :
    ∃ g : ℂ → ℂ, IsKQC g (rectangle a b ∪ conj '' rectangle a b ∪ openSegment ℝ (0 : ℂ) a) K ∧
      EqOn g h (rectangle a b ∪ openSegment ℝ (0 : ℂ) a) ∧
      ∀ z ∈ conj '' rectangle a b, g z = conj (h (conj z)) := by
  have hP : conj '' rectangle a b = conj ⁻¹' rectangle a b := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hz
      exact ⟨conj z, hz, Complex.conj_conj z⟩
  rw [hP]
  set R := rectangle a b with hR
  set P := conj ⁻¹' R with hPdef
  set γ := openSegment ℝ (0 : ℂ) (a : ℂ) with hγ
  set f₂ : ℂ → ℂ := fun z => conj (h (conj z)) with hf₂def
  have hRo : IsOpen R := isOpen_rectangle a b
  have hPo : IsOpen P := hRo.preimage Complex.continuous_conj
  have hK₂ : IsKQC f₂ P K := abR_x_isKQC_conj hK
  have hγim : ∀ z ∈ γ, z.im = 0 := fun z hz => ((s32w_seg_mem ha z).1 hz).1
  have hγconj : ∀ z ∈ γ, conj z = z := fun z hz => Complex.conj_eq_iff_im.2 (hγim z hz)
  have hRim : ∀ z ∈ R, 0 < z.im := fun z hz => hz.2.2.1
  have hPim : ∀ z ∈ P, z.im < 0 := fun z hz => ((s32w_reflect_rect_mem z).1 hz).2.2.2
  let g : ℂ → ℂ := fun z => if 0 ≤ z.im then h z else f₂ z
  have hg1 : EqOn g h (R ∪ γ) := by
    intro z hz
    have : 0 ≤ z.im := by
      rcases hz with hz | hz
      · exact (hRim z hz).le
      · exact (hγim z hz).ge
    simp only [g, if_pos this]
  have hg2 : EqOn g f₂ P := by
    intro z hz
    have : ¬ 0 ≤ z.im := not_le.2 (hPim z hz)
    simp only [g, if_neg this]
  have hmap : MapsTo conj (P ∪ γ) (R ∪ γ) := by
    intro z hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (by rw [hγconj z hz]; exact hz)
  have hqc : IsQuasiconformal g (R ∪ P ∪ γ) := by
    refine qc_extension_across_arc (f₁ := h) (f₂ := f₂) (D₁ := R) (D₂ := P) (γ := γ)
      (isJordanDomain_rectangle ha hb) (s32w_jordan_reflect ha hb) ?_ ?_ ⟨K, hK⟩ ⟨K, hK₂⟩
      ⟨0, a, by exact_mod_cast ha.ne, rfl⟩ ?_ (s32w_isOpen_union ha hb) hc ?_ hi ?_ ?_ hg1 hg2
    · rw [Set.disjoint_left]
      intro z hz hz'
      exact absurd (hRim z hz) (not_lt.2 (hPim z hz').le)
    · rw [Set.disjoint_left]
      rintro w ⟨z, hz, rfl⟩ ⟨z', hz', hzz⟩
      have h1 : 0 < (h z).im := hup hz
      have h2 : (f₂ z').im < 0 := by
        simp only [hf₂def, Complex.conj_im]
        have : 0 < (h (conj z')).im := hup hz'
        linarith
      rw [hzz] at h2
      linarith
    · intro z hz
      obtain ⟨h0, h1, h2⟩ := (s32w_seg_mem ha z).1 hz
      refine ⟨?_, ?_⟩
      · rw [hRo.frontier_eq]
        exact ⟨(s32w_seg_closure hb h0 h1 h2).1, fun hzR => by
          have := hRim z hzR
          linarith⟩
      · rw [hPo.frontier_eq]
        exact ⟨(s32w_seg_closure hb h0 h1 h2).2, fun hzP => by
          have := hPim z hzP
          linarith⟩
    · have h1 : ContinuousOn (fun z => conj (h z)) (R ∪ γ) :=
        Complex.continuous_conj.comp_continuousOn hc
      exact h1.comp Complex.continuous_conj.continuousOn hmap
    · intro x hx y hy hxy
      have hxy' : h (conj x) = h (conj y) := by
        have := congrArg conj hxy
        simpa [hf₂def] using this
      have := hi (hmap hx) (hmap hy) hxy'
      simpa using congrArg conj this
    · intro z hz
      have h1 : (h z).im = 0 := hre z hz
      simp only [hf₂def, hγconj z hz]
      exact (Complex.conj_eq_iff_im.2 h1).symm
  obtain ⟨K', hK'⟩ := hqc
  have hD : IsOpen (R ∪ P ∪ γ) := s32w_isOpen_union ha hb
  have hnull : volume γ = 0 := by
    have hne : LinearMap.ker Complex.imLm ≠ (⊤ : Submodule ℝ ℂ) := by
      intro htop
      have : (Complex.I) ∈ LinearMap.ker Complex.imLm := by rw [htop]; trivial
      simp [Complex.imLm] at this
    refine measure_mono_null ?_ (Measure.addHaar_submodule volume _ hne)
    intro z hz
    simpa [Complex.imLm] using hγim z hz
  refine ⟨g, ?_, hg1, fun z hz => hg2 hz⟩
  refine (thm10_1_isKQC_iff hD hK.2.1 hK'.2.2.1).2 ⟨thm9_1_isACL hK', ?_⟩
  rw [ae_restrict_union_iff, ae_restrict_union_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · filter_upwards [thm9_4_dilatation_ae hK, ae_restrict_mem hRo.measurableSet] with z hz hzR
    obtain ⟨e1, e2⟩ := s32w_dz_congr hRo (fun x hx => hg1 (Or.inl hx)) hzR
    rw [e1, e2]
    exact hz
  · filter_upwards [thm9_4_dilatation_ae hK₂, ae_restrict_mem hPo.measurableSet] with z hz hzP
    obtain ⟨e1, e2⟩ := s32w_dz_congr hPo hg2 hzP
    rw [e1, e2]
    exact hz
  · rw [Measure.restrict_eq_zero.2 hnull]
    simp

end LiZhongQC
