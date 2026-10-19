import LiZhongQC.Lemmas.FoundationDiscLifts
import LiZhongQC.Lemmas.FoundationLocalEnds

/-! Source-only complete parabolic side-collar proof. The two compact-residual
helpers below are retained verbatim from the earlier unregistered residual source. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- A finite horizontal period strip bounded away from the real axis is compact in H. -/
theorem ft1gc_horizontal_box_compact (δ Y : ℝ) (hδ : 0 < δ) :
    IsCompact {τ : UpperHalfPlane | 0 ≤ τ.re ∧ τ.re ≤ 1 ∧ δ ≤ τ.im ∧ τ.im ≤ Y} := by
  have hC : IsCompact {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ δ ≤ z.im ∧ z.im ≤ Y} := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_const Complex.continuous_re).inter
        ((isClosed_le Complex.continuous_re continuous_const).inter
          ((isClosed_le continuous_const Complex.continuous_im).inter
            (isClosed_le Complex.continuous_im continuous_const)))
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + |Y|)).subset ?_
      intro z hz
      rw [mem_closedBall, dist_zero_right]
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 1 + |Y| := by
          rw [abs_of_nonneg hz.1, abs_of_nonneg (hδ.le.trans hz.2.2.1)]
          linarith [le_abs_self Y, hz.2.1, hz.2.2.2]
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff]
  have heq : ((↑) : UpperHalfPlane → ℂ) ''
      {τ : UpperHalfPlane | 0 ≤ τ.re ∧ τ.re ≤ 1 ∧ δ ≤ τ.im ∧ τ.im ≤ Y} =
      {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ δ ≤ z.im ∧ z.im ≤ Y} := by
    ext z
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact hτ
    · intro hz
      exact ⟨⟨z, hδ.trans_le hz.2.2.1⟩, hz, rfl⟩
  rwa [heq]

/-- The upper parabolic side has compact residue in one translation period once its
uniform positive lower height has been established by side identification. -/
theorem ft1gc_parabolic_residual_compact (W : Set UpperHalfPlane) (δ Y : ℝ)
    (hδ : 0 < δ) (hW : W ⊆ {τ : UpperHalfPlane | δ ≤ τ.im}) :
    IsCompact (closure W ∩ {τ : UpperHalfPlane | 0 ≤ τ.re ∧ τ.re ≤ 1 ∧ τ.im ≤ Y}) := by
  have hcl : closure W ⊆ {τ : UpperHalfPlane | δ ≤ τ.im} :=
    closure_minimal hW (isClosed_le continuous_const UpperHalfPlane.continuous_im)
  refine (ft1gc_horizontal_box_compact δ Y hδ).of_isClosed_subset
    (isClosed_closure.inter ((isClosed_le continuous_const UpperHalfPlane.continuous_re).inter
      ((isClosed_le UpperHalfPlane.continuous_re continuous_const).inter
        (isClosed_le UpperHalfPlane.continuous_im continuous_const)))) ?_
  intro τ hτ
  exact ⟨hτ.2.1, hτ.2.2.1, hcl hτ.1, hτ.2.2.2⟩

/-- A proper embedded translation-periodic boundary has an upper cusp side and a
lower real-boundary side. The upper side has a compact period-strip residual; the lower
side is kept explicit so its group-theoretic elementary case can be proved separately. -/
theorem ft1gc_parabolic_side_collar (ρ : ℝ → UpperHalfPlane)
    (hρ : Topology.IsEmbedding ρ)
    (hproper : ∀ L : Set UpperHalfPlane, IsCompact L → IsCompact (ρ ⁻¹' L))
    (hperiod : ∀ t : ℝ, ρ (t + 1) = (1 : ℝ) +ᵥ ρ t)
    (W : Set UpperHalfPlane) (hWo : IsOpen W) (hWc : IsConnected W)
    (hfront : frontier W = Set.range ρ) :
    ∃ δ Y : ℝ, 0 < δ ∧ δ < Y ∧ 1 < Y ∧
      (({τ : UpperHalfPlane | Y < τ.im} ⊆ W ∧
          W ⊆ {τ : UpperHalfPlane | δ < τ.im} ∧
          IsCompact (closure W ∩ {τ : UpperHalfPlane | 0 ≤ τ.re ∧ τ.re ≤ 1 ∧ τ.im ≤ Y})) ∨
        ({τ : UpperHalfPlane | τ.im < δ} ⊆ W ∧
          W ⊆ {τ : UpperHalfPlane | τ.im < Y})) := by
  classical
  -- Unit translation periodicity already supplies the bounds and full lift identity.
  -- The approved properness assumption is retained but is not needed separately.
  have _hproper := hproper
  let E : UpperHalfPlane → ℂ := fun τ => Complex.exp (2 * Real.pi * I * (τ : ℂ))
  let C : Set ℂ := (fun t : ℝ => E (ρ t)) '' Icc 0 1
  have hk : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hEnorm : ∀ τ : UpperHalfPlane, ‖E τ‖ = Real.exp (-(2 * Real.pi) * τ.im) := by
    intro τ
    change ‖Complex.exp (2 * Real.pi * I * (τ : ℂ))‖ = _
    rw [Complex.norm_exp]
    congr 1
    simp <;> ring
  have hEc : Continuous E := Complex.continuous_exp.comp
    (continuous_const.mul UpperHalfPlane.continuous_coe)
  have hCJ : IsJordanCurve (toExt C) := ft1gc_parabolic_exp_jordan ρ hρ hperiod
  have hCd : C ⊆ {z : ℂ | z ≠ 0 ∧ ‖z‖ < 1} := by
    rintro z ⟨t, ht, rfl⟩
    refine ⟨Complex.exp_ne_zero _, ?_⟩
    rw [hEnorm, Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hk) (ρ t).im_pos
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hAB, hAC, hBC, hcover, hAb, hBub⟩ :=
    jordan_curve_theorem_complex_bounded hCJ
  have hshift : ∀ t : ℝ, (ρ (t + 1) : ℂ) = (ρ t : ℂ) + 1 := by
    intro t
    rw [hperiod, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  have hzero : (0 : ℂ) ∈ A := ft1gc_periodic_jordan_zero_inside (fun t => (ρ t : ℂ))
    (UpperHalfPlane.continuous_coe.comp hρ.continuous)
    (fun s t h => hρ.injective (UpperHalfPlane.ext h)) hshift
    A B hAo hBo hAc hBc hAB hAC hBC hcover hAb hBub
  have hlifts := ft1gc_jordan_disc_lifts_connected C A B hCJ hCd
    hAo hBo hAc hBc hAB hAC hBC hcover hAb hzero
  obtain ⟨δ, Y, hδ, hδY, hY, hband⟩ :=
    ft1gc_parabolic_boundary_band ρ hρ.continuous hperiod
  let r : ℝ := Real.exp (-(2 * Real.pi) * δ)
  let l : ℝ := Real.exp (-(2 * Real.pi) * Y)
  have hr0 : 0 < r := Real.exp_pos _
  have hl0 : 0 < l := Real.exp_pos _
  have hCR : ∀ z ∈ C, ‖z‖ ≤ r := by
    rintro z ⟨t, ht, rfl⟩
    change ‖E (ρ t)‖ ≤ Real.exp (-(2 * Real.pi) * δ)
    rw [hEnorm, Real.exp_le_exp]
    have hh := (hband t).1
    nlinarith
  have hCl : ∀ z ∈ C, l < ‖z‖ := by
    rintro z ⟨t, ht, rfl⟩
    change Real.exp (-(2 * Real.pi) * Y) < ‖E (ρ t)‖
    rw [hEnorm, Real.exp_lt_exp]
    have hh := (hband t).2
    nlinarith
  obtain ⟨houter, hinner⟩ := ft1gc_jordan_enclosing_circle C A B
    hAo hBo hAB hcover hAb r hr0.le hCR
  have hballsub : ball (0 : ℂ) l ⊆ A := by
    have hsub : ball (0 : ℂ) l ⊆ A ∪ B := by
      intro z hz
      have hmem : z ∈ A ∪ B ∪ C := hcover ▸ mem_univ z
      rcases hmem with h | h
      · exact h
      · exact (not_lt_of_ge (hCl z h).le (mem_ball_zero_iff.1 hz)).elim
    exact (convex_ball (0 : ℂ) l).isPreconnected.subset_left_of_subset_union
      hAo hBo hAB hsub ⟨0, mem_ball_self hl0, hzero⟩
  let U : Set UpperHalfPlane := E ⁻¹' A
  let V : Set UpperHalfPlane := E ⁻¹' B
  have hUo : IsOpen U := hAo.preimage hEc
  have hVo : IsOpen V := hBo.preimage hEc
  have hUc : IsConnected U := hlifts.1
  have hVc : IsConnected V := hlifts.2
  have hUV : Disjoint U V := by
    apply Set.disjoint_left.2
    intro τ hτU hτV
    exact Set.disjoint_left.1 hAB hτU hτV
  have hpre := ft1gc_parabolic_exp_full_preimage ρ hperiod
  have hcurve : ∀ τ : UpperHalfPlane, E τ ∈ C ↔ τ ∈ range ρ := by
    intro τ
    change τ ∈ {τ : UpperHalfPlane | Complex.exp (2 * Real.pi * I * (τ : ℂ)) ∈
      (fun t : ℝ => Complex.exp (2 * Real.pi * I * (ρ t : ℂ))) '' Icc 0 1} ↔ _
    rw [hpre]
  have hUVcover : U ∪ V = (frontier W)ᶜ := by
    ext τ
    constructor
    · intro hτ
      change τ ∉ frontier W
      rw [hfront]
      intro hτC
      have heC := (hcurve τ).2 hτC
      rcases hτ with h | h
      · exact Set.disjoint_left.1 hAC h heC
      · exact Set.disjoint_left.1 hBC h heC
    · intro hτ
      change E τ ∈ A ∨ E τ ∈ B
      have hmem : E τ ∈ A ∪ B ∪ C := hcover ▸ mem_univ (E τ)
      rcases hmem with h | h
      · exact h
      · have hτC : τ ∈ frontier W := hfront.symm ▸ (hcurve τ).1 h
        exact (hτ hτC).elim
  have hhigh : {τ : UpperHalfPlane | Y + 1 < τ.im} ⊆ U := by
    intro τ hτ
    have hτ' : Y + 1 < τ.im := hτ
    apply hballsub
    apply mem_ball_zero_iff.2
    change ‖E τ‖ < Real.exp (-(2 * Real.pi) * Y)
    rw [hEnorm, Real.exp_lt_exp]
    nlinarith
  have hUlow : U ⊆ {τ : UpperHalfPlane | δ / 2 < τ.im} := by
    intro τ hτ
    have hn : ‖E τ‖ ≤ r := mem_closedBall_zero_iff.1 (hinner hτ)
    change ‖E τ‖ ≤ Real.exp (-(2 * Real.pi) * δ) at hn
    rw [hEnorm, Real.exp_le_exp] at hn
    change δ / 2 < τ.im
    nlinarith
  have hlow : {τ : UpperHalfPlane | τ.im < δ / 2} ⊆ V := by
    intro τ hτ
    have hτ' : τ.im < δ / 2 := hτ
    apply houter
    change Real.exp (-(2 * Real.pi) * δ) < ‖E τ‖
    rw [hEnorm, Real.exp_lt_exp]
    nlinarith
  have hVhigh : V ⊆ {τ : UpperHalfPlane | τ.im < Y + 1} := by
    intro τ hτ
    change τ.im < Y + 1
    by_contra hle
    have hτY : Y < τ.im := by linarith [le_of_not_gt hle]
    have hEA : E τ ∈ A := hballsub (mem_ball_zero_iff.2 (by
      change ‖E τ‖ < Real.exp (-(2 * Real.pi) * Y)
      rw [hEnorm, Real.exp_lt_exp]
      nlinarith))
    exact Set.disjoint_left.1 hAB hEA hτ
  refine ⟨δ / 2, Y + 1, by linarith, by linarith, by linarith, ?_⟩
  rcases ft1gc_open_eq_one_of_two_sides W U V hWo hWc hUo hVo hUc hVc hUV hUVcover with h | h
  · left
    rw [h]
    exact ⟨hhigh, hUlow, ft1gc_parabolic_residual_compact U (δ / 2) (Y + 1)
      (by linarith) (fun τ hτ => show δ / 2 ≤ τ.im from (hUlow hτ).le)⟩
  · right
    rw [h]
    exact ⟨hlow, hVhigh⟩

end LiZhongQC
