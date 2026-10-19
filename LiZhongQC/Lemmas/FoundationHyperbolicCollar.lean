import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.F1LocalGeometry
import LiZhongQC.Lemmas.FoundationDiscLifts

/- Source: FoundationStripTruncation.lean (md5 594e802740779e790a9944f7a910f3ad) -/
/-! Source-only vertical truncation in H. This is the missing upper-boundary
argument when a full-H periodic side is restricted to a finite horizontal strip. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- Truncating heights at r preserves a connected region containing the full
horoball above b<r, and its image is exactly the closed-height intersection. -/
theorem ft1gc_upper_closed_height_connected (U : Set UpperHalfPlane)
    (hUc : IsConnected U) (b r : ℝ) (hr : 0 < r) (hbr : b < r)
    (htop : {τ : UpperHalfPlane | b < τ.im} ⊆ U) :
    IsConnected (U ∩ {τ : UpperHalfPlane | τ.im ≤ r}) := by
  let T : UpperHalfPlane → UpperHalfPlane := fun τ =>
    ⟨⟨τ.re, min τ.im r⟩, lt_min τ.im_pos hr⟩
  have hTc : Continuous T := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun τ : UpperHalfPlane => (⟨τ.re, min τ.im r⟩ : ℂ))
    have he : (fun τ : UpperHalfPlane => (⟨τ.re, min τ.im r⟩ : ℂ)) =
        fun τ : UpperHalfPlane => ((τ.re : ℝ) : ℂ) + ((min τ.im r : ℝ) : ℂ) * I := by
      funext τ
      apply Complex.ext <;> simp
    rw [he]
    exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_re).add
      ((Complex.continuous_ofReal.comp
        (UpperHalfPlane.continuous_im.min continuous_const)).mul continuous_const)
  have hTim : ∀ τ : UpperHalfPlane, (T τ).im = min τ.im r := fun τ => rfl
  have hfix : ∀ τ : UpperHalfPlane, τ.im ≤ r → T τ = τ := by
    intro τ hτ
    apply UpperHalfPlane.ext
    exact Complex.ext rfl (min_eq_left hτ)
  have himage : T '' U = U ∩ {τ : UpperHalfPlane | τ.im ≤ r} := by
    ext τ
    constructor
    · rintro ⟨κ, hκ, rfl⟩
      by_cases hκr : κ.im ≤ r
      · rw [hfix κ hκr]
        exact ⟨hκ, hκr⟩
      · have hrκ : r < κ.im := lt_of_not_ge hκr
        refine ⟨htop ?_, ?_⟩
        · change b < (T κ).im
          rw [hTim, min_eq_right hrκ.le]
          exact hbr
        · change (T κ).im ≤ r
          rw [hTim]
          exact min_le_right _ _
    · intro hτ
      exact ⟨τ, hτ.1, hfix τ hτ.2⟩
  rw [← himage]
  exact hUc.image T hTc.continuousOn

/-- The upper periodic side remains connected after restriction to a finite strip
whose upper boundary lies above the known horoball threshold. -/
theorem ft1gc_upper_open_height_connected (U : Set UpperHalfPlane)
    (hUc : IsConnected U) (b H : ℝ) (hb : 0 < b) (hbH : b < H)
    (htop : {τ : UpperHalfPlane | b < τ.im} ⊆ U) :
    IsConnected (U ∩ {τ : UpperHalfPlane | τ.im < H}) := by
  have hm0 : 0 < (b + H) / 2 := by linarith
  let τ₀ : UpperHalfPlane := ⟨⟨0, (b + H) / 2⟩, hm0⟩
  have hτ₀im : τ₀.im = (b + H) / 2 := rfl
  refine ⟨⟨τ₀, htop ?_, ?_⟩, ?_⟩
  · change b < τ₀.im
    rw [hτ₀im]
    linarith
  · change τ₀.im < H
    rw [hτ₀im]
    linarith
  · apply isPreconnected_of_forall_pair
    intro x hx y hy
    let m : ℝ := max b (max x.im y.im)
    let r : ℝ := (m + H) / 2
    have hmH : m < H := max_lt hbH (max_lt hx.2 hy.2)
    have hbm : b ≤ m := le_max_left _ _
    have hxm : x.im ≤ m := (le_max_left _ _).trans (le_max_right _ _)
    have hym : y.im ≤ m := (le_max_right _ _).trans (le_max_right _ _)
    have hbr : b < r := by dsimp only [r]; linarith
    have hr : 0 < r := hb.trans hbr
    have hrH : r < H := by dsimp only [r]; linarith
    refine ⟨U ∩ {τ : UpperHalfPlane | τ.im ≤ r}, ?_, ?_, ?_,
      (ft1gc_upper_closed_height_connected U hUc b r hr hbr htop).isPreconnected⟩
    · intro z hz
      exact ⟨hz.1, hz.2.trans_lt hrH⟩
    · exact ⟨hx.1, by change x.im ≤ r; dsimp only [r]; linarith⟩
    · exact ⟨hy.1, by change y.im ≤ r; dsimp only [r]; linarith⟩

end LiZhongQC
end -- source noncomputable section

/- Source: FoundationLogStrip.lean (md5 f3a3b116a55eadd5eec5bf67396f6f56) -/
/-! Source-only principal-log coordinate on H, with its exact finite-strip image. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- Principal log divided by a positive real is an open embedding of H onto the
finite strip 0<im<pi/s. The range equality retains the upper boundary explicitly. -/
theorem ft1gc_log_strip_coordinate (s : ℝ) (hs : 0 < s) :
    ∃ F : UpperHalfPlane → UpperHalfPlane,
      Topology.IsOpenEmbedding F ∧
      range F = {τ : UpperHalfPlane | τ.im < Real.pi / s} ∧
      (∀ τ : UpperHalfPlane, (F τ : ℂ) = Complex.log (τ : ℂ) / (s : ℂ)) ∧
      (∀ τ : UpperHalfPlane, (F τ).im = Complex.arg (τ : ℂ) / s) := by
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have hpos : ∀ τ : UpperHalfPlane, 0 < (Complex.log (τ : ℂ) / (s : ℂ)).im := by
    intro τ
    rw [Complex.div_ofReal_im, Complex.log_im]
    exact div_pos (ft1g_arg_bounds τ).1 hs
  let F : UpperHalfPlane → UpperHalfPlane := fun τ =>
    ⟨Complex.log (τ : ℂ) / (s : ℂ), hpos τ⟩
  have hFcoe : ∀ τ : UpperHalfPlane, (F τ : ℂ) = Complex.log (τ : ℂ) / (s : ℂ) := fun τ => rfl
  have hFim : ∀ τ : UpperHalfPlane, (F τ).im = Complex.arg (τ : ℂ) / s := by
    intro τ
    change (Complex.log (τ : ℂ) / (s : ℂ)).im = _
    rw [Complex.div_ofReal_im, Complex.log_im]
  have hlogc : Continuous (fun τ : UpperHalfPlane => Complex.log (τ : ℂ)) := by
    apply continuous_iff_continuousAt.2
    intro τ
    exact (continuousAt_clog (Complex.mem_slitPlane_iff.2 (Or.inr τ.im_ne_zero))).comp
      UpperHalfPlane.continuous_coe.continuousAt
  have hFc : Continuous F :=
    UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr (hlogc.div_const (s : ℂ))
  let g : UpperHalfPlane → ℂ := fun τ => Complex.exp ((s : ℂ) * (τ : ℂ))
  have hgc : Continuous g := Complex.continuous_exp.comp
    (continuous_const.mul UpperHalfPlane.continuous_coe)
  have hcomp : g ∘ F = ((↑) : UpperHalfPlane → ℂ) := by
    funext τ
    change Complex.exp ((s : ℂ) * (Complex.log (τ : ℂ) / (s : ℂ))) = (τ : ℂ)
    rw [mul_div_cancel₀ _ hsC, Complex.exp_log τ.ne_zero]
  have hFi : Function.Injective F := by
    intro τ κ h
    apply UpperHalfPlane.ext
    calc (τ : ℂ) = g (F τ) := (congrFun hcomp τ).symm
      _ = g (F κ) := congrArg g h
      _ = (κ : ℂ) := congrFun hcomp κ
  have hFind : Topology.IsInducing F := Topology.IsInducing.of_comp hFc hgc (by
    rw [hcomp]
    exact UpperHalfPlane.isEmbedding_coe.isInducing)
  have hrange : range F = {τ : UpperHalfPlane | τ.im < Real.pi / s} := by
    ext κ
    constructor
    · rintro ⟨τ, rfl⟩
      change (F τ).im < Real.pi / s
      rw [hFim]
      exact (div_lt_div_iff_of_pos_right hs).2 (ft1g_arg_bounds τ).2
    · intro hκ
      have hsim : ((s : ℂ) * (κ : ℂ)).im = s * κ.im := by simp
      have hlo : 0 < ((s : ℂ) * (κ : ℂ)).im := by
        rw [hsim]
        exact mul_pos hs κ.im_pos
      have hhi : ((s : ℂ) * (κ : ℂ)).im < Real.pi := by
        rw [hsim]
        have h := (lt_div_iff₀ hs).1 hκ
        nlinarith
      have hexppos : 0 < (Complex.exp ((s : ℂ) * (κ : ℂ))).im := by
        rw [Complex.exp_im]
        exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hlo hhi)
      let τ : UpperHalfPlane := ⟨Complex.exp ((s : ℂ) * (κ : ℂ)), hexppos⟩
      refine ⟨τ, UpperHalfPlane.ext ?_⟩
      change Complex.log (Complex.exp ((s : ℂ) * (κ : ℂ))) / (s : ℂ) = (κ : ℂ)
      rw [Complex.log_exp (by linarith [Real.pi_pos]) hhi.le,
        mul_div_cancel_left₀ _ hsC]
  have hopen : IsOpen (range F) := by
    rw [hrange]
    exact isOpen_lt UpperHalfPlane.continuous_im continuous_const
  exact ⟨F, ⟨⟨hFind, hFi⟩, hopen⟩, hrange, hFcoe, hFim⟩

end LiZhongQC
end -- source noncomputable section

/- Source: FoundationStripSides.lean (md5 8b5343910f2ecb51cd0df99c87197570) -/
/-! Source-only genuine separation in a finite horizontal strip. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- A unit-translation-periodic embedded line in a finite horizontal strip has two
connected sides within that strip. The complement identity is relative to im < H;
it makes no claim that the strip's upper boundary disappears in the ambient H. -/
theorem ft1gc_periodic_strip_sides (σ : ℝ → UpperHalfPlane)
    (hσ : Topology.IsEmbedding σ)
    (hperiod : ∀ t : ℝ, σ (t + 1) = (1 : ℝ) +ᵥ σ t)
    (a b H : ℝ) (ha : 0 < a) (hab : a < b) (hbH : b < H)
    (hband : ∀ t : ℝ, a ≤ (σ t).im ∧ (σ t).im ≤ b) :
    ∃ U V : Set UpperHalfPlane,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = {τ : UpperHalfPlane | τ.im < H} \ Set.range σ ∧
      {τ : UpperHalfPlane | b < τ.im ∧ τ.im < H} ⊆ U ∧
      U ⊆ {τ : UpperHalfPlane | a ≤ τ.im ∧ τ.im < H} ∧
      {τ : UpperHalfPlane | τ.im < a} ⊆ V ∧
      V ⊆ {τ : UpperHalfPlane | τ.im ≤ b} := by
  classical
  let E : UpperHalfPlane → ℂ := fun τ => Complex.exp (2 * Real.pi * I * (τ : ℂ))
  let C : Set ℂ := (fun t : ℝ => E (σ t)) '' Icc 0 1
  have hk : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hEnorm : ∀ τ : UpperHalfPlane, ‖E τ‖ = Real.exp (-(2 * Real.pi) * τ.im) := by
    intro τ
    change ‖Complex.exp (2 * Real.pi * I * (τ : ℂ))‖ = _
    rw [Complex.norm_exp]
    congr 1
    simp <;> ring
  have hEc : Continuous E := Complex.continuous_exp.comp
    (continuous_const.mul UpperHalfPlane.continuous_coe)
  have hCJ : IsJordanCurve (toExt C) := ft1gc_parabolic_exp_jordan σ hσ hperiod
  have hCd : C ⊆ {z : ℂ | z ≠ 0 ∧ ‖z‖ < 1} := by
    rintro z ⟨t, ht, rfl⟩
    refine ⟨Complex.exp_ne_zero _, ?_⟩
    rw [hEnorm, Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hk) (σ t).im_pos
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hAB, hAC, hBC, hcover, hAb, hBub⟩ :=
    jordan_curve_theorem_complex_bounded hCJ
  have hshift : ∀ t : ℝ, (σ (t + 1) : ℂ) = (σ t : ℂ) + 1 := by
    intro t
    rw [hperiod, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  have hzero : (0 : ℂ) ∈ A := ft1gc_periodic_jordan_zero_inside (fun t => (σ t : ℂ))
    (UpperHalfPlane.continuous_coe.comp hσ.continuous)
    (fun s t h => hσ.injective (UpperHalfPlane.ext h)) hshift
    A B hAo hBo hAc hBc hAB hAC hBC hcover hAb hBub
  have hlifts := ft1gc_jordan_disc_lifts_connected C A B hCJ hCd
    hAo hBo hAc hBc hAB hAC hBC hcover hAb hzero
  let r : ℝ := Real.exp (-(2 * Real.pi) * a)
  let l : ℝ := Real.exp (-(2 * Real.pi) * b)
  have hCR : ∀ z ∈ C, ‖z‖ ≤ r := by
    rintro z ⟨t, ht, rfl⟩
    change ‖E (σ t)‖ ≤ Real.exp (-(2 * Real.pi) * a)
    rw [hEnorm, Real.exp_le_exp]
    have hh := (hband t).1
    nlinarith
  have hCl : ∀ z ∈ C, l ≤ ‖z‖ := by
    rintro z ⟨t, ht, rfl⟩
    change Real.exp (-(2 * Real.pi) * b) ≤ ‖E (σ t)‖
    rw [hEnorm, Real.exp_le_exp]
    have hh := (hband t).2
    nlinarith
  obtain ⟨houter, hinner⟩ := ft1gc_jordan_enclosing_circle C A B
    hAo hBo hAB hcover hAb r (Real.exp_pos _).le hCR
  have hballsub : ball (0 : ℂ) l ⊆ A := by
    have hsub : ball (0 : ℂ) l ⊆ A ∪ B := by
      intro z hz
      have hmem : z ∈ A ∪ B ∪ C := hcover ▸ mem_univ z
      rcases hmem with h | h
      · exact h
      · exact (not_lt_of_ge (hCl z h) (mem_ball_zero_iff.1 hz)).elim
    exact (convex_ball (0 : ℂ) l).isPreconnected.subset_left_of_subset_union
      hAo hBo hAB hsub ⟨0, mem_ball_self (Real.exp_pos _), hzero⟩
  let U₀ : Set UpperHalfPlane := E ⁻¹' A
  let V : Set UpperHalfPlane := E ⁻¹' B
  have hU₀o : IsOpen U₀ := hAo.preimage hEc
  have hVo : IsOpen V := hBo.preimage hEc
  have hU₀c : IsConnected U₀ := hlifts.1
  have hVc : IsConnected V := hlifts.2
  have htop : {τ : UpperHalfPlane | b < τ.im} ⊆ U₀ := by
    intro τ hτ
    have hτ' : b < τ.im := hτ
    apply hballsub
    apply mem_ball_zero_iff.2
    change ‖E τ‖ < Real.exp (-(2 * Real.pi) * b)
    rw [hEnorm, Real.exp_lt_exp]
    nlinarith
  have hU₀low : U₀ ⊆ {τ : UpperHalfPlane | a ≤ τ.im} := by
    intro τ hτ
    have hn : ‖E τ‖ ≤ r := mem_closedBall_zero_iff.1 (hinner hτ)
    change ‖E τ‖ ≤ Real.exp (-(2 * Real.pi) * a) at hn
    rw [hEnorm, Real.exp_le_exp] at hn
    change a ≤ τ.im
    nlinarith
  have hlow : {τ : UpperHalfPlane | τ.im < a} ⊆ V := by
    intro τ hτ
    have hτ' : τ.im < a := hτ
    apply houter
    change Real.exp (-(2 * Real.pi) * a) < ‖E τ‖
    rw [hEnorm, Real.exp_lt_exp]
    nlinarith
  have hVhigh : V ⊆ {τ : UpperHalfPlane | τ.im ≤ b} := by
    intro τ hτ
    change τ.im ≤ b
    by_contra h
    have ht : τ ∈ U₀ := htop (lt_of_not_ge h)
    exact Set.disjoint_left.1 hAB ht hτ
  let U : Set UpperHalfPlane := U₀ ∩ {τ : UpperHalfPlane | τ.im < H}
  have hUo : IsOpen U := hU₀o.inter (isOpen_lt UpperHalfPlane.continuous_im continuous_const)
  have hUc : IsConnected U := ft1gc_upper_open_height_connected U₀ hU₀c b H
    (ha.trans hab) hbH htop
  have hUV : Disjoint U V := by
    apply Set.disjoint_left.2
    intro τ hτU hτV
    exact Set.disjoint_left.1 hAB hτU.1 hτV
  have hpre := ft1gc_parabolic_exp_full_preimage σ hperiod
  have hcurve : ∀ τ : UpperHalfPlane, E τ ∈ C ↔ τ ∈ range σ := by
    intro τ
    change τ ∈ {τ : UpperHalfPlane | Complex.exp (2 * Real.pi * I * (τ : ℂ)) ∈
      (fun t : ℝ => Complex.exp (2 * Real.pi * I * (σ t : ℂ))) '' Icc 0 1} ↔ _
    rw [hpre]
  have hUVcover : U ∪ V = {τ : UpperHalfPlane | τ.im < H} \ range σ := by
    ext τ
    constructor
    · intro hτ
      rcases hτ with h | h
      · exact ⟨h.2, fun hc => Set.disjoint_left.1 hAC h.1 ((hcurve τ).2 hc)⟩
      · exact ⟨(hVhigh h).trans_lt hbH,
          fun hc => Set.disjoint_left.1 hBC h ((hcurve τ).2 hc)⟩
    · intro hτ
      have hmem : E τ ∈ A ∪ B ∪ C := hcover ▸ mem_univ (E τ)
      rcases hmem with (h | h) | h
      · exact Or.inl ⟨h, hτ.1⟩
      · exact Or.inr h
      · exact (hτ.2 ((hcurve τ).1 h)).elim
  refine ⟨U, V, hUo, hVo, hUc, hVc, hUV, hUVcover, ?_, ?_, hlow, hVhigh⟩
  · intro τ hτ
    exact ⟨htop hτ.1, hτ.2⟩
  · intro τ hτ
    exact ⟨hU₀low hτ.1, hτ.2⟩

end LiZhongQC
end -- source noncomputable section

/- Source: FoundationHyperbolicCollar.lean (md5 e817471a6febb92ec4487c862673a096) -/
/-! Source-only complete hyperbolic side collar, using genuine finite-strip separation.
The two angular residual helpers are retained verbatim from their earlier source. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- The positive-ray side has compact residue in one radial period. -/
theorem ft1gc_positive_residual_compact (W : Set UpperHalfPlane) (lam θ : ℝ)
    (hlam : 1 < lam) (hθ : 0 < θ) (hθπ : θ < Real.pi / 2)
    (hW : W ⊆ {τ : UpperHalfPlane | Complex.arg (τ : ℂ) ≤ Real.pi - θ}) :
    IsCompact (closure W ∩ {τ : UpperHalfPlane | 1 ≤ ‖(τ : ℂ)‖ ∧
      ‖(τ : ℂ)‖ ≤ lam ∧ θ ≤ Complex.arg (τ : ℂ)}) := by
  have hcl : closure W ⊆ {τ : UpperHalfPlane | Complex.arg (τ : ℂ) ≤ Real.pi - θ} :=
    closure_minimal hW (isClosed_le ft1g_arg_continuous continuous_const)
  have hn : Continuous (fun τ : UpperHalfPlane => ‖(τ : ℂ)‖) :=
    continuous_norm.comp UpperHalfPlane.continuous_coe
  refine (ft1g_annular_band_compact lam θ hlam hθ hθπ).of_isClosed_subset
    (isClosed_closure.inter ((isClosed_le continuous_const hn).inter
      ((isClosed_le hn continuous_const).inter (isClosed_le continuous_const ft1g_arg_continuous)))) ?_
  intro τ hτ
  exact ⟨hτ.2.1, hτ.2.2.1, hτ.2.2.2, hcl hτ.1⟩

/-- The negative-ray side has compact residue in one radial period. -/
theorem ft1gc_negative_residual_compact (W : Set UpperHalfPlane) (lam θ : ℝ)
    (hlam : 1 < lam) (hθ : 0 < θ) (hθπ : θ < Real.pi / 2)
    (hW : W ⊆ {τ : UpperHalfPlane | θ ≤ Complex.arg (τ : ℂ)}) :
    IsCompact (closure W ∩ {τ : UpperHalfPlane | 1 ≤ ‖(τ : ℂ)‖ ∧
      ‖(τ : ℂ)‖ ≤ lam ∧ Complex.arg (τ : ℂ) ≤ Real.pi - θ}) := by
  have hcl : closure W ⊆ {τ : UpperHalfPlane | θ ≤ Complex.arg (τ : ℂ)} :=
    closure_minimal hW (isClosed_le continuous_const ft1g_arg_continuous)
  have hn : Continuous (fun τ : UpperHalfPlane => ‖(τ : ℂ)‖) :=
    continuous_norm.comp UpperHalfPlane.continuous_coe
  refine (ft1g_annular_band_compact lam θ hlam hθ hθπ).of_isClosed_subset
    (isClosed_closure.inter ((isClosed_le continuous_const hn).inter
      ((isClosed_le hn continuous_const).inter (isClosed_le ft1g_arg_continuous continuous_const)))) ?_
  intro τ hτ
  exact ⟨hτ.2.1, hτ.2.2.1, hcl hτ.1, hτ.2.2.2⟩

/-- A proper embedded hyperbolically periodic boundary separates the two real rays.
The alternative records which side is selected. In each case a thin sector lies in W,
and one closed radial-period residual is compact in the upper half-plane. -/
theorem ft1gc_hyperbolic_side_collar (ρ : ℝ → UpperHalfPlane)
    (hρ : Topology.IsEmbedding ρ)
    (hproper : ∀ L : Set UpperHalfPlane, IsCompact L → IsCompact (ρ ⁻¹' L))
    (lam : ℝ) (hlam : 1 < lam)
    (hperiod : ∀ t : ℝ, (ρ (t + 1) : ℂ) = (lam : ℂ) * (ρ t : ℂ))
    (W : Set UpperHalfPlane) (hWo : IsOpen W) (hWc : IsConnected W)
    (hfront : frontier W = Set.range ρ) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi / 2 ∧
      (({τ : UpperHalfPlane | Complex.arg (τ : ℂ) < θ} ⊆ W ∧
          W ⊆ {τ : UpperHalfPlane | Complex.arg (τ : ℂ) < Real.pi - θ} ∧
          IsCompact (closure W ∩ {τ : UpperHalfPlane | 1 ≤ ‖(τ : ℂ)‖ ∧
            ‖(τ : ℂ)‖ ≤ lam ∧ θ ≤ Complex.arg (τ : ℂ)})) ∨
        ({τ : UpperHalfPlane | Real.pi - θ < Complex.arg (τ : ℂ)} ⊆ W ∧
          W ⊆ {τ : UpperHalfPlane | θ < Complex.arg (τ : ℂ)} ∧
          IsCompact (closure W ∩ {τ : UpperHalfPlane | 1 ≤ ‖(τ : ℂ)‖ ∧
            ‖(τ : ℂ)‖ ≤ lam ∧ Complex.arg (τ : ℂ) ≤ Real.pi - θ}))) := by
  classical
  -- The periodic bounds and strip coordinate supply the required separation.
  -- Properness remains in the approved signature but is not used separately.
  have _hproper := hproper
  let s : ℝ := Real.log lam
  have hs : 0 < s := Real.log_pos hlam
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  obtain ⟨F, hF, hFrange, hFcoe, hFim⟩ := ft1gc_log_strip_coordinate s hs
  let σ : ℝ → UpperHalfPlane := F ∘ ρ
  have hσ : Topology.IsEmbedding σ := hF.isEmbedding.comp hρ
  have hσperiod : ∀ t : ℝ, σ (t + 1) = (1 : ℝ) +ᵥ σ t := by
    intro t
    apply UpperHalfPlane.ext
    change (F (ρ (t + 1)) : ℂ) = ((1 : ℝ) +ᵥ F (ρ t) : UpperHalfPlane)
    rw [hFcoe, hperiod, Complex.log_ofReal_mul (by linarith : 0 < lam) (ρ t).ne_zero,
      UpperHalfPlane.coe_vadd, hFcoe]
    change ((s : ℂ) + Complex.log (ρ t : ℂ)) / (s : ℂ) =
      ((1 : ℝ) : ℂ) + Complex.log (ρ t : ℂ) / (s : ℂ)
    rw [add_div, div_self hsC, Complex.ofReal_one]
  obtain ⟨θ₀, hθ₀, hθ₀π, hmargin⟩ :=
    ft1g_periodic_angular_margin ρ hρ.continuous lam hlam hperiod
  let a : ℝ := θ₀ / s
  let b : ℝ := (Real.pi - θ₀) / s
  let H : ℝ := Real.pi / s
  have ha : 0 < a := div_pos hθ₀ hs
  have hab : a < b := (div_lt_div_iff_of_pos_right hs).2 (by linarith)
  have hbH : b < H := (div_lt_div_iff_of_pos_right hs).2 (by linarith)
  have hband : ∀ t : ℝ, a ≤ (σ t).im ∧ (σ t).im ≤ b := by
    intro t
    change θ₀ / s ≤ (F (ρ t)).im ∧ (F (ρ t)).im ≤ (Real.pi - θ₀) / s
    rw [hFim]
    exact ⟨(div_le_div_iff_of_pos_right hs).2 (hmargin t).1,
      (div_le_div_iff_of_pos_right hs).2 (hmargin t).2⟩
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hUV, hcover, htop, hUbound, hbottom, hVbound⟩ :=
    ft1gc_periodic_strip_sides σ hσ hσperiod a b H ha hab hbH hband
  have hUrange : U ⊆ range F := by
    intro κ hκ
    rw [hFrange]
    exact (hUbound hκ).2
  have hVrange : V ⊆ range F := by
    intro κ hκ
    rw [hFrange]
    exact (hVbound hκ).trans_lt hbH
  let P : Set UpperHalfPlane := F ⁻¹' U
  let Q : Set UpperHalfPlane := F ⁻¹' V
  have hPo : IsOpen P := hUo.preimage hF.continuous
  have hQo : IsOpen Q := hVo.preimage hF.continuous
  have hPc : IsConnected P := hUc.preimage_of_isOpenMap hF.isEmbedding.injective hF.isOpenMap hUrange
  have hQc : IsConnected Q := hVc.preimage_of_isOpenMap hF.isEmbedding.injective hF.isOpenMap hVrange
  have hPQ : Disjoint P Q := by
    apply Set.disjoint_left.2
    intro τ hτP hτQ
    exact Set.disjoint_left.1 hUV hτP hτQ
  have hPQcover : P ∪ Q = (frontier W)ᶜ := by
    ext τ
    change F τ ∈ U ∪ V ↔ τ ∉ frontier W
    rw [hcover, hfront]
    constructor
    · intro hτ
      rintro ⟨t, ht⟩
      exact hτ.2 ⟨t, congrArg F ht⟩
    · intro hτ
      refine ⟨?_, ?_⟩
      · change (F τ).im < Real.pi / s
        rw [hFim]
        exact (div_lt_div_iff_of_pos_right hs).2 (ft1g_arg_bounds τ).2
      · rintro ⟨t, ht⟩
        exact hτ ⟨t, hF.isEmbedding.injective ht⟩
  have hpositive : {τ : UpperHalfPlane | Complex.arg (τ : ℂ) < θ₀ / 2} ⊆ Q := by
    intro τ hτ
    apply hbottom
    change (F τ).im < θ₀ / s
    rw [hFim]
    exact (div_lt_div_iff_of_pos_right hs).2 (by change Complex.arg (τ : ℂ) < θ₀ / 2 at hτ; linarith)
  have hQupper : Q ⊆ {τ : UpperHalfPlane | Complex.arg (τ : ℂ) < Real.pi - θ₀ / 2} := by
    intro τ hτ
    have hb := hVbound hτ
    change (F τ).im ≤ (Real.pi - θ₀) / s at hb
    rw [hFim, div_le_div_iff_of_pos_right hs] at hb
    change Complex.arg (τ : ℂ) < Real.pi - θ₀ / 2
    linarith
  have hnegative : {τ : UpperHalfPlane | Real.pi - θ₀ / 2 < Complex.arg (τ : ℂ)} ⊆ P := by
    intro τ hτ
    apply htop
    constructor
    · change (Real.pi - θ₀) / s < (F τ).im
      rw [hFim]
      exact (div_lt_div_iff_of_pos_right hs).2 (by
        change Real.pi - θ₀ / 2 < Complex.arg (τ : ℂ) at hτ
        linarith)
    · change (F τ).im < Real.pi / s
      rw [hFim]
      exact (div_lt_div_iff_of_pos_right hs).2 (ft1g_arg_bounds τ).2
  have hPlower : P ⊆ {τ : UpperHalfPlane | θ₀ / 2 < Complex.arg (τ : ℂ)} := by
    intro τ hτ
    have ha := (hUbound hτ).1
    change θ₀ / s ≤ (F τ).im at ha
    rw [hFim, div_le_div_iff_of_pos_right hs] at ha
    change θ₀ / 2 < Complex.arg (τ : ℂ)
    linarith
  have hθ : 0 < θ₀ / 2 := by linarith
  have hθπ : θ₀ / 2 < Real.pi / 2 := by linarith [Real.pi_pos]
  refine ⟨θ₀ / 2, hθ, hθπ, ?_⟩
  rcases ft1gc_open_eq_one_of_two_sides W P Q hWo hWc hPo hQo hPc hQc hPQ hPQcover with h | h
  · right
    rw [h]
    exact ⟨hnegative, hPlower, ft1gc_negative_residual_compact P lam (θ₀ / 2)
      hlam hθ hθπ (fun τ hτ => show θ₀ / 2 ≤ Complex.arg (τ : ℂ) from (hPlower hτ).le)⟩
  · left
    rw [h]
    exact ⟨hpositive, hQupper, ft1gc_positive_residual_compact Q lam (θ₀ / 2)
      hlam hθ hθπ (fun τ hτ => show Complex.arg (τ : ℂ) ≤ Real.pi - θ₀ / 2 from (hQupper hτ).le)⟩

end LiZhongQC
end -- source noncomputable section
