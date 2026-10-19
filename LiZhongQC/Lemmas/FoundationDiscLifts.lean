import LiZhongQC.Lemmas.FoundationJordanGeometry

/-! Source-only outer-disc connectivity and the approved two-lift endpoint. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- Radial truncation preserves a connected set containing the entire exterior of
a smaller circle. The image is exactly its intersection with the truncating disc. -/
theorem ft1gc_outer_closedDisc_connected (B : Set ℂ) (hB : IsConnected B)
    (R r : ℝ) (hr : 0 < r) (hRr : R < r)
    (hext : {z : ℂ | R < ‖z‖} ⊆ B) :
    IsConnected (B ∩ closedBall (0 : ℂ) r) := by
  let T : ℂ → ℂ := fun z => ((r / max r ‖z‖ : ℝ) : ℂ) * z
  have hden : ∀ z : ℂ, 0 < max r ‖z‖ := fun z => hr.trans_le (le_max_left _ _)
  have hTc : Continuous T :=
    (Complex.continuous_ofReal.comp
      (continuous_const.div (continuous_const.max continuous_norm) (fun z => (hden z).ne'))).mul
      continuous_id
  have hfix : ∀ z : ℂ, ‖z‖ ≤ r → T z = z := by
    intro z hz
    change ((r / max r ‖z‖ : ℝ) : ℂ) * z = z
    rw [max_eq_left hz, div_self hr.ne', Complex.ofReal_one, one_mul]
  have hnorm : ∀ z : ℂ, r < ‖z‖ → ‖T z‖ = r := by
    intro z hz
    change ‖((r / max r ‖z‖ : ℝ) : ℂ) * z‖ = r
    rw [max_eq_right hz.le, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (div_nonneg hr.le (norm_nonneg _)),
      div_mul_cancel₀ _ (hr.trans hz).ne']
  have heq : T '' B = B ∩ closedBall (0 : ℂ) r := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      by_cases hwr : ‖w‖ ≤ r
      · rw [hfix w hwr]
        exact ⟨hw, mem_closedBall_zero_iff.2 hwr⟩
      · have hwr' : r < ‖w‖ := lt_of_not_ge hwr
        refine ⟨hext ?_, mem_closedBall_zero_iff.2 (hnorm w hwr').le⟩
        change R < ‖T w‖
        rw [hnorm w hwr']
        exact hRr
    · intro hz
      exact ⟨z, hz.1, hfix z (mem_closedBall_zero_iff.1 hz.2)⟩
  rw [← heq]
  exact hB.image T hTc.continuousOn

/-- Connectedness survives intersection with the unit disc when the set contains
the full exterior of a strictly smaller positive circle. -/
theorem ft1gc_outer_unitDisc_connected (B : Set ℂ) (hB : IsConnected B)
    (R : ℝ) (hR0 : 0 < R) (hR1 : R < 1)
    (hext : {z : ℂ | R < ‖z‖} ⊆ B) :
    IsConnected (B ∩ ball (0 : ℂ) 1) := by
  have hmid0 : 0 < (R + 1) / 2 := by linarith
  have hmidnorm : ‖(((R + 1) / 2 : ℝ) : ℂ)‖ = (R + 1) / 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hmid0.le]
  refine ⟨⟨(((R + 1) / 2 : ℝ) : ℂ), hext ?_, mem_ball_zero_iff.2 ?_⟩, ?_⟩
  · change R < ‖(((R + 1) / 2 : ℝ) : ℂ)‖
    rw [hmidnorm]
    linarith
  · rw [hmidnorm]
    linarith
  · apply isPreconnected_of_forall_pair
    intro x hx y hy
    let m : ℝ := max R (max ‖x‖ ‖y‖)
    let r : ℝ := (m + 1) / 2
    have hm1 : m < 1 := max_lt hR1
      (max_lt (mem_ball_zero_iff.1 hx.2) (mem_ball_zero_iff.1 hy.2))
    have hRm : R ≤ m := le_max_left _ _
    have hxm : ‖x‖ ≤ m := (le_max_left _ _).trans (le_max_right _ _)
    have hym : ‖y‖ ≤ m := (le_max_right _ _).trans (le_max_right _ _)
    have hRr : R < r := by dsimp only [r]; linarith
    have hr0 : 0 < r := hR0.trans hRr
    have hr1 : r < 1 := by dsimp only [r]; linarith
    refine ⟨B ∩ closedBall (0 : ℂ) r, ?_, ?_, ?_,
      (ft1gc_outer_closedDisc_connected B hB R r hr0 hRr hext).isPreconnected⟩
    · intro z hz
      exact ⟨hz.1, mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 hz.2).trans_lt hr1)⟩
    · exact ⟨hx.1, mem_closedBall_zero_iff.2 (by dsimp only [r]; linarith)⟩
    · exact ⟨hy.1, mem_closedBall_zero_iff.2 (by dsimp only [r]; linarith)⟩

/-- An enclosing circle puts its whole exterior in the unbounded labelled piece,
and bounds the inner piece by that same circle. -/
theorem ft1gc_jordan_enclosing_circle (C A B : Set ℂ)
    (hAo : IsOpen A) (hBo : IsOpen B) (hAB : Disjoint A B)
    (hcover : A ∪ B ∪ C = univ) (hAb : Bornology.IsBounded A)
    (R : ℝ) (hR : 0 ≤ R) (hCR : ∀ z ∈ C, ‖z‖ ≤ R) :
    {z : ℂ | R < ‖z‖} ⊆ B ∧ A ⊆ closedBall (0 : ℂ) R := by
  have hsub : {z : ℂ | R < ‖z‖} ⊆ A ∪ B := by
    intro z hz
    have hmem : z ∈ A ∪ B ∪ C := hcover ▸ mem_univ z
    rcases hmem with h | h
    · exact h
    · exact (not_lt_of_ge (hCR z h) hz).elim
  have houter : {z : ℂ | R < ‖z‖} ⊆ B := by
    rcases (isPreconnected_setOf_lt_norm hR).subset_or_subset hAo hBo hAB hsub with h | h
    · obtain ⟨M, hM⟩ := isBounded_iff_subset_closedBall (0 : ℂ) |>.1 hAb
      let x : ℂ := ((max R M + 1 : ℝ) : ℂ)
      have hxnorm : ‖x‖ = max R M + 1 := by
        change ‖((max R M + 1 : ℝ) : ℂ)‖ = max R M + 1
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [le_max_left R M])]
      have hxA : x ∈ A := h (by change R < ‖x‖; rw [hxnorm]; linarith [le_max_left R M])
      have hb := mem_closedBall_zero_iff.1 (hM hxA)
      rw [hxnorm] at hb
      exact (by linarith [le_max_right R M] : False).elim
    · exact h
  refine ⟨houter, ?_⟩
  intro z hz
  apply mem_closedBall_zero_iff.2
  by_contra hzr
  have hzb : z ∈ B := houter (lt_of_not_ge hzr)
  exact Set.disjoint_left.1 hAB hz hzb

/-- A Jordan curve strictly inside the punctured unit disc, with zero on its inner
side, has connected lifts of both sides to the upper half-plane under exp(2 pi i z).
The outer lift is restricted to the unit disc by the domain of this covering; it is
not justified merely by connectedness of the full planar outer component. -/
theorem ft1gc_jordan_disc_lifts_connected (C A B : Set ℂ)
    (hC : IsJordanCurve (toExt C))
    (hCd : C ⊆ {z : ℂ | z ≠ 0 ∧ ‖z‖ < 1})
    (hAo : IsOpen A) (hBo : IsOpen B) (hAc : IsConnected A) (hBc : IsConnected B)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcover : A ∪ B ∪ C = univ) (hAb : Bornology.IsBounded A) (hzero : (0 : ℂ) ∈ A) :
    IsConnected {τ : UpperHalfPlane | Complex.exp (2 * Real.pi * I * (τ : ℂ)) ∈ A} ∧
      IsConnected {τ : UpperHalfPlane | Complex.exp (2 * Real.pi * I * (τ : ℂ)) ∈ B} := by
  have hCJc : IsCompact C := isCompact_of_isJordanCurve_toExt hC
  obtain ⟨d, hd, hgap⟩ := hCJc.exists_forall_le'
    (continuous_const.sub continuous_norm).continuousOn (a := (0 : ℝ))
    (fun z hz => sub_pos.2 (hCd hz).2)
  let R : ℝ := max (1 - d / 2) (1 / 2)
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hR1 : R < 1 := max_lt (by linarith) (by norm_num)
  have hCR : ∀ z ∈ C, ‖z‖ ≤ R := by
    intro z hz
    have h : d ≤ 1 - ‖z‖ := hgap z hz
    have hm : 1 - d / 2 ≤ R := le_max_left _ _
    linarith
  obtain ⟨houter, hinner⟩ := ft1gc_jordan_enclosing_circle C A B
    hAo hBo hAB hcover hAb R hR0.le hCR
  have hfront : frontier A = C :=
    (frontier_pieces_eq_of_jordan_curve_theorem_complex hC
      hAo hBo hAc hBc hAB hAC hBC hcover).1
  have hAJ : IsJordanDomain A := by
    refine ⟨hAo, hAc, ?_⟩
    rw [frontier_toExt_of_isBounded' hAb hAo, hfront]
    exact hC
  have hApc : IsPathConnected (A \ ({0} : Set ℂ)) :=
    ft1gc_punctured_jordan_pathConnected hAJ hzero
  have hBpc : IsPathConnected (B ∩ ball (0 : ℂ) 1) :=
    (hBo.inter isOpen_ball).isConnected_iff_isPathConnected.1
      (ft1gc_outer_unitDisc_connected B hBc R hR0 hR1 houter)
  have hnormcircle : ∀ a : ℝ, 0 < a → ∀ t : ℝ,
      ‖(a : ℂ) * Complex.exp ((t * (2 * Real.pi) : ℝ) * I)‖ = a := by
    intro a ha t
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le, norm_exp_ofReal_mul_I, mul_one]
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hAo.mem_nhds hzero)
  have hleft := ft1gc_upper_exp_preimage_connected (A \ ({0} : Set ℂ)) hApc
    (fun h => h.2 (mem_singleton 0))
    (fun z hz => (mem_closedBall_zero_iff.1 (hinner hz.1)).trans_lt hR1)
    (ε / 2) (by linarith) (fun t => by
      have hn := hnormcircle (ε / 2) (by linarith) t
      refine ⟨hball (mem_ball_zero_iff.2 (by rw [hn]; linarith)), ?_⟩
      intro hz
      have he := mem_singleton_iff.1 hz
      rw [he, norm_zero] at hn
      linarith)
  have hright := ft1gc_upper_exp_preimage_connected (B ∩ ball (0 : ℂ) 1) hBpc
    (fun h => Set.disjoint_left.1 hAB hzero h.1)
    (fun z hz => mem_ball_zero_iff.1 hz.2)
    ((R + 1) / 2) (by linarith) (fun t => by
      have hn := hnormcircle ((R + 1) / 2) (by linarith) t
      refine ⟨houter ?_, mem_ball_zero_iff.2 ?_⟩
      · change R < ‖((R + 1) / 2 : ℝ) * Complex.exp ((t * (2 * Real.pi) : ℝ) * I)‖
        rw [hn]
        linarith
      · rw [hn]
        linarith)
  have hexpnorm : ∀ τ : UpperHalfPlane,
      ‖Complex.exp (2 * Real.pi * I * (τ : ℂ))‖ < 1 := by
    intro τ
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    have hre : (2 * Real.pi * I * (τ : ℂ)).re = -(2 * Real.pi) * τ.im := by
      simp <;> ring
    rw [hre]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos (by norm_num) Real.pi_pos)) τ.im_pos
  have heqA : {τ : UpperHalfPlane | Complex.exp (2 * Real.pi * I * (τ : ℂ)) ∈ A \ ({0} : Set ℂ)} =
      {τ : UpperHalfPlane | Complex.exp (2 * Real.pi * I * (τ : ℂ)) ∈ A} := by
    ext τ
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, fun hz => Complex.exp_ne_zero _ (mem_singleton_iff.1 hz)⟩
  have heqB : {τ : UpperHalfPlane | Complex.exp (2 * Real.pi * I * (τ : ℂ)) ∈ B ∩ ball (0 : ℂ) 1} =
      {τ : UpperHalfPlane | Complex.exp (2 * Real.pi * I * (τ : ℂ)) ∈ B} := by
    ext τ
    exact ⟨fun h => h.1, fun h => ⟨h, mem_ball_zero_iff.2 (hexpnorm τ)⟩⟩
  rw [heqA] at hleft
  rw [heqB] at hright
  exact ⟨hleft, hright⟩

end LiZhongQC
