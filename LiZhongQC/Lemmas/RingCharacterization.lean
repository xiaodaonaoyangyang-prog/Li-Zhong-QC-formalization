import LiZhongQC.Ch02.S13_Representation

/-!
# The ring characterization of quasiconformality (the converse of Theorem 7.4)

`isKQC_of_dcModulus_bound` (the end of §7.3; the book refers to Lehto–Virtanen I, Theorem 7.2): an orientation
preserving homeomorphism that distorts the modulus of every doubly connected `B` with `B̄ ⊆ D` by at most the factor
`K` is `K`-quasiconformal.  Proved (s21r, 2026-09-27).  The statement is moved here unchanged from
`Ch01/S07_GeometricDefinition.lean` (user decision, 2026-09-27) because the proof goes through the analytic
definition: the ring bound gives `IsACL` and the dilatation bound at every point of differentiability, and
Theorem 10.1 (`thm10_1_isKQC_iff`, at the end of `Ch02/S13_Representation.lean`), which §7 cannot import, concludes.
The ring estimates use slit-rectangle rings (`rc_xi`, `rc_xi_ring_bound`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace LiZhongQC

/-! ## The proof of `isKQC_of_dcModulus_bound` (s21r S07, prefix `rc_`)

Route (the analytic definition): ring bound ⇒ `IsACL f D` and, at every point of `D`,
`|∂_z f| + |∂_{z̄} f| ≤ K (|∂_z f| - |∂_{z̄} f|)` ⇒ Theorem 10.1 (`thm10_1_isKQC_iff`), with the same `K`.
Only the first conjunct `M(B) ≤ K M(f(B))` of the hypothesis is used (`rc_RingBound`), always for a
PREIMAGE ring `B` whose modulus is bounded below by the model slit rectangle `Ξ_h` (Stage A1) and whose image
modulus is bounded above by the length–area bound L0 below; `hsense` is used once, for the orientation
`|∂_{z̄} f| ≤ |∂_z f|` (Stage B).
* L0, L0′: the ring upper bound `M(B) ≤ (π/2) m(B)/|q - p|²` (the s21r scout probe `h21r2_proj.lean`) and the
  separation of a compact core from `∞`, also at the image of a homeomorphism.
* Stage A1: `Ξ_h`, its double connectivity and `M(Ξ_h) ≥ πh/(2(1+3h))`; affine invariance.
* Stage A2 (L1b): ring ⇒ `IsACL` (the S09 Theorem 9.1 chain with the per-rectangle estimate from `Ξ`).
* Stage B (L3b): `|∂_{z̄} f| ≤ |∂_z f|` at points of differentiability (local winding `+1`).
* Stage C (L3c): `|∂_z f| + |∂_{z̄} f| ≤ K (|∂_z f| - |∂_{z̄} f|)` at points of differentiability. -/

/-- The one-sided ring condition `M(B) ≤ K M(f(B))` for every doubly connected `B` with `B̄ ⊆ D`
(the first conjunct of the hypothesis of `isKQC_of_dcModulus_bound`). -/
def rc_RingBound (f : ℂ → ℂ) (D : Set ℂ) (K : ℝ) : Prop :=
  ∀ B : Set ℂ, IsDoublyConnected B → closure (toExt B) ⊆ toExt D →
    dcModulus B ≤ ENNReal.ofReal K * dcModulus (f '' B)

/-! ### L0: a closed curve separating `p, q` from `∞` has length `≥ 2|q - p|` -/

/-- The ray `{p + s v : s ≥ 0}` together with `∞` is preconnected (`v ≠ 0`). -/
theorem rc_isPreconnected_ray (p v : ℂ) (hv : v ≠ 0) :
    IsPreconnected (toExt ((fun s : ℝ => p + (s : ℂ) * v) '' Ici 0) ∪ {extInf}) := by
  have hK : IsPreconnected (toExt ((fun s : ℝ => p + (s : ℂ) * v) '' Ici 0)) :=
    (isPreconnected_Ici.image _ (Continuous.continuousOn (by fun_prop))).image _
      OnePoint.continuous_coe.continuousOn
  refine hK.subset_closure subset_union_left ?_
  refine union_subset subset_closure (singleton_subset_iff.2 ?_)
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  refine extInf_mem_closure_toExt_of_unbounded fun R => ?_
  refine ⟨p + (((|R| + ‖p‖ + 1) / ‖v‖ : ℝ) : ℂ) * v,
    ⟨(|R| + ‖p‖ + 1) / ‖v‖, mem_Ici.2 (by positivity), rfl⟩, ?_⟩
  have h1 : ‖(((|R| + ‖p‖ + 1) / ‖v‖ : ℝ) : ℂ) * v‖ = |R| + ‖p‖ + 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
      div_mul_cancel₀ _ hvn.ne']
  have h2 : ‖(((|R| + ‖p‖ + 1) / ‖v‖ : ℝ) : ℂ) * v‖ ≤
      ‖p + (((|R| + ‖p‖ + 1) / ‖v‖ : ℝ) : ℂ) * v‖ + ‖p‖ := by
    have := norm_sub_le (p + (((|R| + ‖p‖ + 1) / ‖v‖ : ℝ) : ℂ) * v) p
    simpa using this
  rw [h1] at h2
  linarith [le_abs_self R]

/-- A closed curve separating `p` from `∞` meets every ray from `p`. -/
theorem rc_exists_ray {γ : LRCurve} {p : ℂ}
    (hne : connectedComponentIn (toExt γ.closedTrace)ᶜ (p : ExtPlane) ≠
      connectedComponentIn (toExt γ.closedTrace)ᶜ extInf) {v : ℂ} (hv : v ≠ 0) :
    ∃ t ∈ Icc (0 : ℝ) 1, ∃ s : ℝ, 0 ≤ s ∧ γ.toFun t = p + (s : ℂ) * v := by
  by_contra hno
  push Not at hno
  have hSC : toExt ((fun s : ℝ => p + (s : ℂ) * v) '' Ici 0) ∪ {extInf}
      ⊆ (toExt γ.closedTrace)ᶜ := by
    rintro z (⟨w, ⟨s, hs, rfl⟩, rfl⟩ | hz) ⟨u, ⟨t, ht, rfl⟩, hwz⟩
    · exact hno t ht s hs (OnePoint.coe_injective hwz)
    · rw [mem_singleton_iff] at hz
      exact OnePoint.coe_ne_infty _ (hwz.trans hz)
  have hpS : (p : ExtPlane) ∈ toExt ((fun s : ℝ => p + (s : ℂ) * v) '' Ici 0) ∪ {extInf} :=
    Or.inl ⟨p, ⟨0, self_mem_Ici, by simp⟩, rfl⟩
  have hinfS : extInf ∈ toExt ((fun s : ℝ => p + (s : ℂ) * v) '' Ici 0) ∪ {extInf} :=
    Or.inr (mem_singleton _)
  exact hne (connectedComponentIn_eq
    ((rc_isPreconnected_ray p v hv).subset_connectedComponentIn hpS hSC hinfS))

/-- The coordinate of `z` along the direction `v` (a unit vector) measured from `p`:
`Re ((z - p) v̄)`. -/
def rc_coord (p v z : ℂ) : ℝ := ((z - p) * (starRingEnd ℂ) v).re

/-- The coordinate changes along a sub-arc by at most the length of the sub-arc. -/
theorem rc_coord_sub_le_lintegral {γ : LRCurve} (hγ : γ.IsClosedCurve) (p v : ℂ)
    (hv : ‖v‖ = 1) {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    ENNReal.ofReal |rc_coord p v (γ.toFun d) - rc_coord p v (γ.toFun c)| ≤
      ∫⁻ t in Ioo c d, ‖deriv γ.toFun t‖ₑ := by
  obtain ⟨K, hKLip, -⟩ := hγ
  have hKcd : LipschitzOnWith K γ.toFun (Icc c d) := hKLip.mono (Icc_subset_Icc hc hd)
  have hcoordLip : LipschitzWith 1 (rc_coord p v) := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    simp only [rc_coord, NNReal.coe_one, one_mul, Real.dist_eq, Complex.dist_eq]
    rw [← sub_re, ← sub_mul, sub_sub_sub_cancel_right]
    calc |((z - w) * (starRingEnd ℂ) v).re| ≤ ‖(z - w) * (starRingEnd ℂ) v‖ :=
          Complex.abs_re_le_norm _
      _ = ‖z - w‖ := by rw [norm_mul, Complex.norm_conj, hv, mul_one]
  have hL : LipschitzOnWith (1 * K) (fun u => rc_coord p v (γ.toFun u)) (uIcc c d) := by
    rw [uIcc_of_le hcd]
    exact hcoordLip.comp_lipschitzOnWith hKcd
  have hftc : ∫ u in c..d, deriv (fun u => rc_coord p v (γ.toFun u)) u =
      rc_coord p v (γ.toFun d) - rc_coord p v (γ.toFun c) :=
    hL.absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have hA := LocallyLipschitzOn.ae_differentiableAt_Ioo γ.locallyLipschitzOn
  rw [← hftc, intervalIntegral.integral_of_le hcd, ← Real.norm_eq_abs, ofReal_norm]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← setLIntegral_congr Ioo_ae_eq_Ioc]
  refine setLIntegral_mono_ae' measurableSet_Ioo ?_
  filter_upwards [hA] with u hu huI
  have hu01 : u ∈ Ioo (0:ℝ) 1 := ⟨hc.trans_lt huI.1, huI.2.trans_le hd⟩
  have hdγ : HasDerivAt γ.toFun (deriv γ.toFun u) u := (hu hu01).hasDerivAt
  have h1 : HasDerivAt (fun s => (γ.toFun s - p) * (starRingEnd ℂ) v)
      (deriv γ.toFun u * (starRingEnd ℂ) v) u :=
    (hdγ.sub_const p).mul_const ((starRingEnd ℂ) v)
  have hderiv : HasDerivAt (fun s => rc_coord p v (γ.toFun s))
      (deriv γ.toFun u * (starRingEnd ℂ) v).re u := by
    have h2 := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt u h1
    simp only [Function.comp_def, Complex.reCLM_apply] at h2
    exact h2
  rw [hderiv.deriv, ← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs]
  calc |(deriv γ.toFun u * (starRingEnd ℂ) v).re| ≤ ‖deriv γ.toFun u * (starRingEnd ℂ) v‖ :=
        Complex.abs_re_le_norm _
    _ = ‖deriv γ.toFun u‖ := by rw [norm_mul, Complex.norm_conj, hv, mul_one]

/-- If the coordinate differs by `≥ δ` at two parameters, the closed curve has length `≥ 2δ`. -/
theorem rc_two_mul_le_of_le {γ : LRCurve} (hγ : γ.IsClosedCurve) (p v : ℂ) (hv : ‖v‖ = 1)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {δ : ℝ}
    (hδ : δ ≤ |rc_coord p v (γ.toFun b) - rc_coord p v (γ.toFun a)|) :
    ENNReal.ofReal (2 * δ) ≤ γ.length := by
  have hγ' := hγ
  obtain ⟨-, -, h01⟩ := hγ'
  have I1 := rc_coord_sub_le_lintegral hγ p v hv le_rfl ha (hab.trans hb)
  have I2 := rc_coord_sub_le_lintegral hγ p v hv ha hab hb
  have I3 := rc_coord_sub_le_lintegral hγ p v hv (ha.trans hab) hb le_rfl
  have hsplit : (∫⁻ t in Ioo 0 a, ‖deriv γ.toFun t‖ₑ) + (∫⁻ t in Ioo a b, ‖deriv γ.toFun t‖ₑ) +
      (∫⁻ t in Ioo b 1, ‖deriv γ.toFun t‖ₑ) ≤ γ.length := by
    have e1 : Disjoint (Ioo (0:ℝ) a) (Ioo a b) :=
      Set.disjoint_left.2 fun t h1 h2 => by linarith [h1.2, h2.1]
    have e2 : Disjoint (Ioo (0:ℝ) a ∪ Ioo a b) (Ioo b 1) := by
      rw [Set.disjoint_union_left]
      exact ⟨Set.disjoint_left.2 fun t h1 h2 => by linarith [h1.2, h2.1],
        Set.disjoint_left.2 fun t h1 h2 => by linarith [h1.2, h2.1]⟩
    rw [← lintegral_union measurableSet_Ioo e1, ← lintegral_union measurableSet_Ioo e2]
    simp only [LRCurve.length, LRCurve.rhoLength, Pi.one_apply, one_mul]
    refine lintegral_mono_set ?_
    rintro t ((ht | ht) | ht)
    · exact ⟨ht.1, ht.2.trans_le (hab.trans hb)⟩
    · exact ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩
    · exact ⟨(ha.trans hab).trans_lt ht.1, ht.2⟩
  set X : ℝ → ℝ := fun t => rc_coord p v (γ.toFun t) with hX
  have hX01 : X 0 = X 1 := by simp only [hX, h01]
  have htri : 2 * δ ≤ |X a - X 0| + |X b - X a| + |X 1 - X b| := by
    have t1 : |X b - X a| ≤ |X b - X 1| + |X 1 - X a| := abs_sub_le _ _ _
    rw [← hX01, abs_sub_comm (X b) (X 0), abs_sub_comm (X 0) (X a)] at t1
    rw [← hX01]
    linarith
  calc ENNReal.ofReal (2 * δ)
      ≤ ENNReal.ofReal (|X a - X 0| + |X b - X a| + |X 1 - X b|) := ENNReal.ofReal_le_ofReal htri
    _ = ENNReal.ofReal |X a - X 0| + ENNReal.ofReal |X b - X a| + ENNReal.ofReal |X 1 - X b| := by
        rw [ENNReal.ofReal_add (by positivity) (abs_nonneg _),
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    _ ≤ (∫⁻ t in Ioo 0 a, ‖deriv γ.toFun t‖ₑ) + (∫⁻ t in Ioo a b, ‖deriv γ.toFun t‖ₑ) +
        (∫⁻ t in Ioo b 1, ‖deriv γ.toFun t‖ₑ) := add_le_add (add_le_add I1 I2) I3
    _ ≤ γ.length := hsplit

/-- **L0 (projection bound).** A closed curve separating two distinct points `p, q` from `∞`
has length `≥ 2|q - p|`. -/
theorem rc_two_mul_le_length {γ : LRCurve} (hγ : γ.IsClosedCurve) {p q : ℂ} (hpq : p ≠ q)
    (hnep : connectedComponentIn (toExt γ.closedTrace)ᶜ (p : ExtPlane) ≠
      connectedComponentIn (toExt γ.closedTrace)ᶜ extInf)
    (hneq : connectedComponentIn (toExt γ.closedTrace)ᶜ (q : ExtPlane) ≠
      connectedComponentIn (toExt γ.closedTrace)ᶜ extInf) :
    ENNReal.ofReal (2 * ‖q - p‖) ≤ γ.length := by
  have hd0 : 0 < ‖q - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hpq.symm)
  set d : ℝ := ‖q - p‖ with hd
  set v : ℂ := (q - p) / (d : ℂ) with hvdef
  have hv : ‖v‖ = 1 := by
    rw [hvdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0, ← hd,
      div_self hd0.ne']
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    exact zero_ne_one hv
  obtain ⟨t₁, ht₁, s₁, hs₁, h₁⟩ := rc_exists_ray hnep (neg_ne_zero.2 hv0)
  obtain ⟨t₂, ht₂, s₂, hs₂, h₂⟩ := rc_exists_ray hneq hv0
  have hvv : v * (starRingEnd ℂ) v = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv]
    simp
  have hqp : q - p = (d : ℂ) * v := by
    rw [hvdef, mul_div_cancel₀]
    exact_mod_cast hd0.ne'
  have hx₁ : rc_coord p v (γ.toFun t₁) = -s₁ := by
    rw [rc_coord, h₁]
    have e : (p + (s₁ : ℂ) * -v - p) * (starRingEnd ℂ) v = -(s₁ : ℂ) * (v * (starRingEnd ℂ) v) := by
      ring
    rw [e, hvv]
    simp
  have hx₂ : rc_coord p v (γ.toFun t₂) = d + s₂ := by
    rw [rc_coord, h₂]
    have e : (q + (s₂ : ℂ) * v - p) * (starRingEnd ℂ) v =
        ((d : ℂ) + s₂) * (v * (starRingEnd ℂ) v) := by
      rw [show q + (s₂ : ℂ) * v - p = (q - p) + (s₂ : ℂ) * v by ring, hqp]
      ring
    rw [e, hvv]
    simp
  have hgap : d ≤ |rc_coord p v (γ.toFun t₂) - rc_coord p v (γ.toFun t₁)| := by
    rw [hx₁, hx₂, abs_of_nonneg (by linarith)]
    linarith
  rcases le_total t₁ t₂ with h | h
  · exact rc_two_mul_le_of_le hγ p v hv ht₁.1 h ht₂.2 hgap
  · rw [abs_sub_comm] at hgap
    exact rc_two_mul_le_of_le hγ p v hv ht₂.1 h ht₁.2 hgap

/-- **L0 (ring upper bound).** If two distinct points `p, q` of `ℂ̄ ∖ B` both lie in a component
of `ℂ̄ ∖ B` other than that of `∞`, then `M(B) ≤ 2π · (1/(2|q-p|))² · m(B)`,
i.e. `M(B) ≤ (π/2) m(B)/|q-p|²`. -/
theorem rc_dcModulus_le_area {B : Set ℂ} (hB : IsDoublyConnected B) {p q : ℂ} (hpq : p ≠ q)
    (hp : (p : ExtPlane) ∈ (toExt B)ᶜ) (hq : (q : ExtPlane) ∈ (toExt B)ᶜ)
    (hsp : connectedComponentIn (toExt B)ᶜ (p : ExtPlane) ≠
      connectedComponentIn (toExt B)ᶜ extInf)
    (hsq : connectedComponentIn (toExt B)ᶜ (q : ExtPlane) ≠
      connectedComponentIn (toExt B)ᶜ extInf) :
    dcModulus B ≤ ENNReal.ofReal (2 * π) *
      (ENNReal.ofReal (1 / (2 * ‖q - p‖)) ^ 2 * volume B) := by
  have hd0 : 0 < ‖q - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hpq.symm)
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * ‖q - p‖)) with hc
  set ρ : ℂ → ℝ≥0∞ := B.indicator (fun _ => c) with hρ
  have hρm : Measurable ρ := measurable_const.indicator hB.1.measurableSet
  have hadm : ∀ γ ∈ separatingCurves B, 1 ≤ γ.rhoLength ρ := by
    intro γ hγ
    obtain ⟨hcl, htr, hsep⟩ := hγ
    have h1 := hsep _ hp _ (extInf_mem_compl_toExt B) hsp
    have h2 := hsep _ hq _ (extInf_mem_compl_toExt B) hsq
    have hL := rc_two_mul_le_length hcl hpq h1 h2
    have heq : γ.rhoLength ρ = c * γ.length := by
      rw [LRCurve.length, ← LRCurve.rhoLength_const_mul γ 1 ENNReal.ofReal_ne_top]
      refine LRCurve.rhoLength_congr fun z hz => ?_
      have hzB : z ∈ B := htr (image_mono Ioo_subset_Icc_self hz)
      rw [hρ, indicator_of_mem hzB, Pi.one_apply, mul_one]
    rw [heq]
    calc (1 : ℝ≥0∞) = c * ENNReal.ofReal (2 * ‖q - p‖) := by
          rw [hc, ← ENNReal.ofReal_mul (by positivity), one_div,
            inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]
      _ ≤ c * γ.length := mul_le_mul_right hL c
  have h := dcModulus_le_rhoArea hB hρm hadm
  have harea : rhoArea ρ B = c ^ 2 * volume B := by
    unfold rhoArea
    calc ∫⁻ z in B, ρ z ^ 2 = ∫⁻ _ in B, c ^ 2 :=
          setLIntegral_congr_fun hB.1.measurableSet fun z hz => by
            simp [hρ, indicator_of_mem hz]
      _ = c ^ 2 * volume B := setLIntegral_const _ _
  rw [harea] at h
  exact h

/-! ### L0′: separation of a compact core from `∞` -/

/-- **L0′.** If `C ⊆ U` with `U` open and `C` compact, every point of `C` lies in a component of
`ℂ̄ ∖ (U ∖ C)` other than that of `∞`: the component is preconnected and covered by the disjoint closed
sets `C` and `ℂ̄ ∖ U`, which contain the point and `∞` respectively. -/
theorem rc_ne_component_extInf {U C : Set ℂ} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    {x : ℂ} (hx : x ∈ C) :
    connectedComponentIn (toExt (U \ C))ᶜ (x : ExtPlane) ≠
      connectedComponentIn (toExt (U \ C))ᶜ extInf := by
  intro heq
  have hxc : (x : ExtPlane) ∈ (toExt (U \ C))ᶜ := by
    rw [coe_mem_compl_toExt_iff]
    exact fun h => h.2 hx
  have hxS : (x : ExtPlane) ∈ connectedComponentIn (toExt (U \ C))ᶜ (x : ExtPlane) :=
    mem_connectedComponentIn hxc
  have hinfS : extInf ∈ connectedComponentIn (toExt (U \ C))ᶜ (x : ExtPlane) := by
    rw [heq]
    exact mem_connectedComponentIn (extInf_mem_compl_toExt _)
  have hSsub : connectedComponentIn (toExt (U \ C))ᶜ (x : ExtPlane) ⊆ toExt C ∪ (toExt U)ᶜ := by
    intro p hp
    have hp' := connectedComponentIn_subset _ _ hp
    by_cases hpinf : p = extInf
    · rw [hpinf]
      exact Or.inr (extInf_notMem_toExt U)
    · obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hpinf
      rw [coe_mem_compl_toExt_iff] at hp'
      by_cases hzC : z ∈ C
      · exact Or.inl (mem_image_of_mem _ hzC)
      · exact Or.inr fun h => hp' ⟨coe_mem_toExt_iff.1 h, hzC⟩
  have hCc : IsClosed (toExt C) := (hC.image OnePoint.continuous_coe).isClosed
  have hUc : IsClosed (toExt U)ᶜ := (OnePoint.isOpenMap_coe U hU).isClosed_compl
  have hdisj : connectedComponentIn (toExt (U \ C))ᶜ (x : ExtPlane) ∩ (toExt C ∩ (toExt U)ᶜ) = ∅ := by
    refine eq_empty_of_forall_notMem fun p hp => ?_
    obtain ⟨z, hz, rfl⟩ := hp.2.1
    exact hp.2.2 (mem_image_of_mem _ (hCU hz))
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 isPreconnected_connectedComponentIn _ _ hCc hUc
    hSsub hdisj with h | h
  · exact extInf_notMem_toExt C (h hinfS)
  · exact h hxS (mem_image_of_mem _ (hCU hx))

/-- **L0′ at the image.** For `f` continuous and injective on `D` and `C ⊆ U ⊆ D` (`U` open, `C`
compact), every `f x` with `x ∈ C` lies in a component of `ℂ̄ ∖ f(U ∖ C)` other than that of `∞`:
`f(U ∖ C) = f(U) ∖ f(C)`, `f(U)` is open (invariance of domain) and `f(C)` is compact. -/
theorem rc_image_ne_component {f : ℂ → ℂ} {D U C : Set ℂ} (hc : ContinuousOn f D) (hi : InjOn f D)
    (hU : IsOpen U) (hUD : U ⊆ D) (hC : IsCompact C) (hCU : C ⊆ U) {x : ℂ} (hx : x ∈ C) :
    connectedComponentIn (toExt (f '' (U \ C)))ᶜ ((f x : ℂ) : ExtPlane) ≠
      connectedComponentIn (toExt (f '' (U \ C)))ᶜ extInf := by
  rw [(hi.mono hUD).image_sdiff_subset hCU]
  exact rc_ne_component_extInf (isOpen_image_of_continuousOn_injOn hU (hc.mono hUD) (hi.mono hUD))
    (hC.image_of_continuousOn (hc.mono (hCU.trans hUD))) (image_mono hCU) (mem_image_of_mem f hx)

/-- A map continuous and injective on an open set `D` sends every doubly connected `B` with
`B̄ ⊆ D` to a doubly connected set (`aqc_isDoublyConnected_image`; the inverse is continuous by
`qcl_f_isHomeomorphOnto_of_injOn`). -/
theorem rc_isDoublyConnected_image {f : ℂ → ℂ} {D B : Set ℂ} (hD : IsOpen D) (hc : ContinuousOn f D)
    (hi : InjOn f D) (hB : IsDoublyConnected B) (hBD : closure (toExt B) ⊆ toExt D) :
    IsDoublyConnected (f '' B) := by
  exact aqc_isDoublyConnected_image hD (qcl_f_isHomeomorphOnto_of_injOn hD hc hi)
    (isOpen_image_of_continuousOn_injOn hD hc hi) hB hBD

/-- **L0 at the image.** For `f` continuous and injective on `D`, `C ⊆ U ⊆ D` (`U` open, `C`
compact) with `f(U ∖ C)` doubly connected, and `p, q ∈ C` with `f p ≠ f q`:
`M(f(U ∖ C)) ≤ 2π (1/(2|f q - f p|))² m(f(U ∖ C))`. -/
theorem rc_dcModulus_image_le {f : ℂ → ℂ} {D U C : Set ℂ} (hc : ContinuousOn f D) (hi : InjOn f D)
    (hU : IsOpen U) (hUD : U ⊆ D) (hC : IsCompact C) (hCU : C ⊆ U)
    (hB : IsDoublyConnected (f '' (U \ C))) {p q : ℂ} (hp : p ∈ C) (hq : q ∈ C) (hpq : f p ≠ f q) :
    dcModulus (f '' (U \ C)) ≤ ENNReal.ofReal (2 * π) *
      (ENNReal.ofReal (1 / (2 * ‖f q - f p‖)) ^ 2 * volume (f '' (U \ C))) := by
  have hnot : ∀ x ∈ C, ((f x : ℂ) : ExtPlane) ∈ (toExt (f '' (U \ C)))ᶜ := by
    intro x hx
    rw [coe_mem_compl_toExt_iff]
    rintro ⟨z, hz, hzx⟩
    have hzx' : z = x := hi (hUD hz.1) (hUD (hCU hx)) hzx
    exact hz.2 (hzx' ▸ hx)
  exact rc_dcModulus_le_area hB hpq (hnot p hp) (hnot q hq)
    (rc_image_ne_component hc hi hU hUD hC hCU hp) (rc_image_ne_component hc hi hU hUD hC hCU hq)

/-! ### Stage A1: the model ring `Ξ_h` (slit rectangle) and its modulus lower bound

`Ξ_h = (-1, 1) × (-h, h) ∖ [-(1-h), 1-h]` for `0 < h < 1`: a horizontal slit whose `ℓ∞`-distance to
the outer boundary is `h` everywhere.  `M(Ξ_h) ≥ πh/(2(1+3h))`: the rectangular loops
`∂((-(1-h+s), 1-h+s) × (-s, s))`, `0 < s < h`, separate the slit from `∞`; averaging their `ρ`-lengths over `s`
gives `h · inf l_ρ ≤ ∫ ρ g` with `g = 1_{Q₊} + 1_{Q₋} + 1_{R_r} + 1_{R_l}`, and Cauchy–Schwarz with
`∫ g² ≤ 4h + 12h²` gives `λ(Γ_sep) ≤ 4/h + 12`, i.e. `M = 2π/λ ≥ πh/(2(1+3h))` (Theorem 4.9).  Affine maps
`w ↦ β + α w` (`α ≠ 0`) keep double connectivity and the modulus. -/

/-- The box `Q_h = (-1, 1) × (-h, h)`. -/
def rc_xiQ (h : ℝ) : Set ℂ := openRect (-1) 1 (-h) h

/-- The closed slit `S_h = [-(1-h), 1-h] × {0}`. -/
def rc_xiS (h : ℝ) : Set ℂ := closedRect (h - 1) (1 - h) 0 0

/-- The model ring `Ξ_h = Q_h ∖ S_h`. -/
def rc_xi (h : ℝ) : Set ℂ := rc_xiQ h \ rc_xiS h

/-- The averaging weight `g = 1_{Q₊} + 1_{Q₋} + 1_{R_r} + 1_{R_l}` with `Q₊ = (-1,1)×(0,h)`,
`Q₋ = (-1,1)×(-h,0)`, `R_r = (1-h,1)×(-h,h)`, `R_l = (-1,h-1)×(-h,h)`. -/
def rc_xiWeight (h : ℝ) : ℂ → ℝ≥0∞ :=
  (openRect (-1) 1 0 h).indicator 1 + (openRect (-1) 1 (-h) 0).indicator 1 +
    (openRect (1 - h) 1 (-h) h).indicator 1 + (openRect (-1) (h - 1) (-h) h).indicator 1

/-- The clamp `x ↦ max 0 (min 1 x)` of `ℝ` onto `[0, 1]`. -/
def rc_clamp (x : ℝ) : ℝ := max 0 (min 1 x)

/-- The boundary of the rectangle `(-A, A) × (-B, B)`, run once counterclockwise from `A + B i` at
constant speed on each quarter of `[0, 1]`: `A + Bi → -A + Bi → -A - Bi → A - Bi → A + Bi`. -/
def rc_rectLoopFun (A B t : ℝ) : ℂ :=
  ((A * (1 - 2 * rc_clamp (4 * t) + 2 * rc_clamp (4 * t - 2)) : ℝ) : ℂ) +
    ((B * (1 - 2 * rc_clamp (4 * t - 1) + 2 * rc_clamp (4 * t - 3)) : ℝ) : ℂ) * I

/-- The rectangle loop is Lipschitz with constant `16 (|A| + |B|)` (the clamp is `1`-Lipschitz). -/
theorem rc_lipschitzWith_rectLoopFun (A B : ℝ) :
    LipschitzWith (Real.toNNReal (16 * (|A| + |B|))) (rc_rectLoopFun A B) := by
  have hcl : LipschitzWith 1 rc_clamp := (LipschitzWith.id.const_min 1).const_max 0
  have hc : ∀ e s t : ℝ, |rc_clamp (4 * s - e) - rc_clamp (4 * t - e)| ≤ 4 * |s - t| := by
    intro e s t
    have h1 := hcl.dist_le_mul (4 * s - e) (4 * t - e)
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul,
      show 4 * s - e - (4 * t - e) = 4 * (s - t) by ring, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 4)] at h1
    exact h1
  have hc0 : ∀ s t : ℝ, |rc_clamp (4 * s) - rc_clamp (4 * t)| ≤ 4 * |s - t| := by
    intro s t
    simpa using hc 0 s t
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [Real.coe_toNNReal _ (by positivity), Complex.dist_eq, Real.dist_eq]
  set X : ℝ := A * (-2 * (rc_clamp (4 * s) - rc_clamp (4 * t)) +
    2 * (rc_clamp (4 * s - 2) - rc_clamp (4 * t - 2))) with hX
  set Y : ℝ := B * (-2 * (rc_clamp (4 * s - 1) - rc_clamp (4 * t - 1)) +
    2 * (rc_clamp (4 * s - 3) - rc_clamp (4 * t - 3))) with hY
  have e : rc_rectLoopFun A B s - rc_rectLoopFun A B t = (X : ℂ) + (Y : ℂ) * I := by
    simp only [rc_rectLoopFun, hX, hY]
    push_cast
    ring
  have hXb : |X| ≤ 16 * |A| * |s - t| := by
    rw [hX, abs_mul]
    have h1 := hc0 s t
    have h2 := hc 2 s t
    have hin : |-2 * (rc_clamp (4 * s) - rc_clamp (4 * t)) +
        2 * (rc_clamp (4 * s - 2) - rc_clamp (4 * t - 2))| ≤ 16 * |s - t| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_neg, abs_two]
      linarith
    calc |A| * _ ≤ |A| * (16 * |s - t|) := mul_le_mul_of_nonneg_left hin (abs_nonneg A)
      _ = 16 * |A| * |s - t| := by ring
  have hYb : |Y| ≤ 16 * |B| * |s - t| := by
    rw [hY, abs_mul]
    have h1 := hc 1 s t
    have h2 := hc 3 s t
    have hin : |-2 * (rc_clamp (4 * s - 1) - rc_clamp (4 * t - 1)) +
        2 * (rc_clamp (4 * s - 3) - rc_clamp (4 * t - 3))| ≤ 16 * |s - t| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_neg, abs_two]
      linarith
    calc |B| * _ ≤ |B| * (16 * |s - t|) := mul_le_mul_of_nonneg_left hin (abs_nonneg B)
      _ = 16 * |B| * |s - t| := by ring
  rw [e]
  calc ‖(X : ℂ) + (Y : ℂ) * I‖ ≤ ‖(X : ℂ)‖ + ‖(Y : ℂ) * I‖ := norm_add_le _ _
    _ = |X| + |Y| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ 16 * |A| * |s - t| + 16 * |B| * |s - t| := add_le_add hXb hYb
    _ = 16 * (|A| + |B|) * |s - t| := by ring

/-- The rectangle loop `rc_rectLoopFun A B` as a locally rectifiable curve. -/
def rc_rectLoop (A B : ℝ) : LRCurve where
  toFun := rc_rectLoopFun A B
  locallyLipschitzOn := fun _ _ =>
    ⟨_, univ, univ_mem, (rc_lipschitzWith_rectLoopFun A B).lipschitzOnWith⟩

/-- The rectangle loop is a closed rectifiable curve. -/
theorem rc_rectLoop_isClosedCurve (A B : ℝ) : (rc_rectLoop A B).IsClosedCurve := by
  refine ⟨_, (rc_lipschitzWith_rectLoopFun A B).lipschitzOnWith, ?_⟩
  show rc_rectLoopFun A B 0 = rc_rectLoopFun A B 1
  norm_num [rc_rectLoopFun, rc_clamp]

/-- Affine maps `w ↦ β + α w` (`α ≠ 0`) are conformal on every set. -/
theorem rc_isConformalOnto_affine {α : ℂ} (hα : α ≠ 0) (β : ℂ) (S : Set ℂ) :
    IsConformalOnto (fun w => β + α * w) S ((fun w => β + α * w) '' S) := by
  refine ⟨(by fun_prop : Differentiable ℂ fun w : ℂ => β + α * w).differentiableOn, ?_, rfl⟩
  intro z _ w _ h
  have h' : β + α * z = β + α * w := h
  exact mul_left_cancel₀ hα (add_left_cancel h')

/-- **Affine invariance of the modulus**: `M(β + α B) = M(B)` (`α ≠ 0`), by Theorem 2.2. -/
theorem rc_dcModulus_affine {B : Set ℂ} (hB : IsDoublyConnected B) {α : ℂ} (hα : α ≠ 0) (β : ℂ) :
    dcModulus ((fun w => β + α * w) '' B) = dcModulus B := by
  exact (thm2_2_dcModulus_conformal_invariant hB ⟨_, rc_isConformalOnto_affine hα β B⟩).symm

/-- Affine images `β + α B` (`α ≠ 0`) of bounded doubly connected sets are doubly connected
(`aqc_isDoublyConnected_image` on `D = ℂ`). -/
theorem rc_isDoublyConnected_affine {B : Set ℂ} (hB : IsDoublyConnected B)
    (hBb : Bornology.IsBounded B) {α : ℂ} (hα : α ≠ 0) (β : ℂ) :
    IsDoublyConnected ((fun w => β + α * w) '' B) := by
  have hc : ContinuousOn (fun w : ℂ => β + α * w) univ :=
    (by fun_prop : Continuous fun w : ℂ => β + α * w).continuousOn
  have hi : InjOn (fun w : ℂ => β + α * w) univ :=
    (rc_isConformalOnto_affine hα β univ).2.1
  refine aqc_isDoublyConnected_image isOpen_univ (qcl_f_isHomeomorphOnto_of_injOn isOpen_univ hc hi)
    (isOpen_image_of_continuousOn_injOn isOpen_univ hc hi) hB ?_
  rw [closure_toExt_eq_toExt_closure_of_isBounded hBb]
  exact image_mono (subset_univ _)

/-- The complement of an open rectangle is preconnected: the closed half-planes `re ≤ a`, `im ≥ d`,
`re ≥ b`, `im ≤ c` are convex and chain through `a + d i`, `b + d i`, `b + c i`. -/
theorem rc_isPreconnected_compl_openRect (a b c d : ℝ) : IsPreconnected (openRect a b c d)ᶜ := by
  have e : (openRect a b c d)ᶜ = ({z : ℂ | z.re ≤ a} ∪ {z : ℂ | d ≤ z.im}) ∪
      ({z : ℂ | b ≤ z.re} ∪ {z : ℂ | z.im ≤ c}) := by
    ext z
    simp only [openRect, mem_compl_iff, mem_ofPred_eq, mem_union, not_and_or, not_lt]
    tauto
  rw [e]
  have h1 : IsPreconnected ({z : ℂ | z.re ≤ a} ∪ {z : ℂ | d ≤ z.im}) :=
    IsPreconnected.union ((a : ℂ) + (d : ℂ) * I) (by simp) (by simp)
      (convex_halfSpace_re_le a).isPreconnected (convex_halfSpace_im_ge d).isPreconnected
  have h2 : IsPreconnected ({z : ℂ | b ≤ z.re} ∪ {z : ℂ | z.im ≤ c}) :=
    IsPreconnected.union ((b : ℂ) + (c : ℂ) * I) (by simp) (by simp)
      (convex_halfSpace_re_ge b).isPreconnected (convex_halfSpace_im_le c).isPreconnected
  exact IsPreconnected.union ((b : ℂ) + (d : ℂ) * I) (Or.inr (by simp)) (Or.inl (by simp)) h1 h2

/-- An open rectangle is convex: it is an intersection of four open half-planes. -/
theorem rc_xi_convex_openRect (a b c d : ℝ) : Convex ℝ (openRect a b c d) := by
  exact (convex_halfSpace_re_gt a).inter ((convex_halfSpace_re_lt b).inter
    ((convex_halfSpace_im_gt c).inter (convex_halfSpace_im_lt d)))

/-- `Ξ_h` is connected (`0 < h < 1`): it is the union of the four convex boxes `Q₊`, `R_r`, `Q₋`, `R_l` of
`rc_xiWeight`, chained through `(1 - h/2) ± (h/2) i` and `-(1 - h/2) - (h/2) i`. -/
theorem rc_xi_isConnected {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) : IsConnected (rc_xi h) := by
  have heq : rc_xi h = ((openRect (-1) 1 0 h ∪ openRect (1 - h) 1 (-h) h) ∪ openRect (-1) 1 (-h) 0) ∪
      openRect (-1) (h - 1) (-h) h := by
    ext z
    simp only [rc_xi, rc_xiQ, rc_xiS, openRect, closedRect, Set.mem_sdiff, mem_union, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨k1, k2, k3, k4⟩, hn⟩
      rcases lt_trichotomy z.im 0 with hi | hi | hi
      · exact Or.inl (Or.inr ⟨k1, k2, k3, hi⟩)
      · by_cases hr : z.re < h - 1
        · exact Or.inr ⟨k1, hr, k3, k4⟩
        · refine Or.inl (Or.inl (Or.inr ⟨?_, k2, k3, k4⟩))
          by_contra hr'
          exact hn ⟨not_lt.1 hr, not_lt.1 hr', hi.ge, hi.le⟩
      · exact Or.inl (Or.inl (Or.inl ⟨k1, k2, hi, k4⟩))
    · rintro (((⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4⟩) | ⟨k1, k2, k3, k4⟩) | ⟨k1, k2, k3, k4⟩)
      · exact ⟨⟨k1, k2, by linarith, k4⟩, fun hs => by linarith [hs.2.2.2]⟩
      · exact ⟨⟨by linarith, k2, k3, k4⟩, fun hs => by linarith [hs.2.1]⟩
      · exact ⟨⟨k1, k2, k3, by linarith⟩, fun hs => by linarith [hs.2.2.1]⟩
      · exact ⟨⟨k1, by linarith, k3, k4⟩, fun hs => by linarith [hs.1]⟩
  have p1 : ((1 - h / 2 : ℝ) : ℂ) + ((h / 2 : ℝ) : ℂ) * I ∈
      openRect (-1) 1 0 h ∩ openRect (1 - h) 1 (-h) h :=
    ⟨acl_mem_openRect ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩,
      acl_mem_openRect ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩⟩
  have p2 : ((1 - h / 2 : ℝ) : ℂ) + ((-(h / 2) : ℝ) : ℂ) * I ∈
      openRect (1 - h) 1 (-h) h ∩ openRect (-1) 1 (-h) 0 :=
    ⟨acl_mem_openRect ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩,
      acl_mem_openRect ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩⟩
  have p3 : ((h / 2 - 1 : ℝ) : ℂ) + ((-(h / 2) : ℝ) : ℂ) * I ∈
      openRect (-1) 1 (-h) 0 ∩ openRect (-1) (h - 1) (-h) h :=
    ⟨acl_mem_openRect ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩,
      acl_mem_openRect ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩⟩
  rw [heq]
  refine ⟨⟨_, Or.inl (Or.inl (Or.inl p1.1))⟩, ?_⟩
  exact IsPreconnected.union _ (Or.inr p3.1) p3.2
    (IsPreconnected.union _ (Or.inr p2.1) p2.2
      (IsPreconnected.union _ p1.1 p1.2 (rc_xi_convex_openRect _ _ _ _).isPreconnected
        (rc_xi_convex_openRect _ _ _ _).isPreconnected)
      (rc_xi_convex_openRect _ _ _ _).isPreconnected)
    (rc_xi_convex_openRect _ _ _ _).isPreconnected

/-- `Ξ_h` is doubly connected (`0 < h < 1`).

Proof: `Ξ_h` is open (the open box minus the closed slit) and connected (the four convex boxes `Q₊`, `R_r`,
`Q₋`, `R_l` of `rc_xiWeight` cover it and chain through `(1-h/2) ± (h/2) i` and `-(1-h/2) - (h/2) i`), and
`ℂ̄ ∖ Ξ_h = S_h ∪ (ℂ̄ ∖ Q_h)` with both pieces compact, connected and disjoint, so exactly two components.
Uses: `t53_image_sep` (S05:4610), first conjunct, with `B = Ξ_h`, `A = S_h`, `W = id`: `S_h` compact
(`acl_isCompact_closedRect`, S09:364) and connected (`ar_cov_convex_closedRect`, S09:6816, nonempty as
`h - 1 < 1 - h`), `Ξ_h ∪ S_h = Q_h` open (`acl_isOpen_openRect`, S09:978; `S_h ⊆ Q_h` as `0 < h < 1`), `hVc`:
`extInf ∈ _` and `isPreconnected_compl_toExt` (CanonicalForm:100) with `acl_isBounded_openRect` (S09:376) and
`rc_isPreconnected_compl_openRect`; `image_id`. -/
theorem rc_isDoublyConnected_xi {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) : IsDoublyConnected (rc_xi h) := by
  have hSQ : rc_xiS h ⊆ rc_xiQ h := fun z hz =>
    ⟨by linarith [hz.1], by linarith [hz.2.1], by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩
  have hunion : rc_xi h ∪ rc_xiS h = rc_xiQ h := Set.sdiff_union_of_subset hSQ
  have hQo : IsOpen (rc_xiQ h) := acl_isOpen_openRect _ _ _ _
  have hSc : IsCompact (rc_xiS h) := acl_isCompact_closedRect _ _ _ _
  have h0S : ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I ∈ rc_xiS h :=
    acl_mem_closedRect (by linarith) (by linarith) le_rfl le_rfl
  have hSconn : IsConnected (rc_xiS h) := ⟨⟨_, h0S⟩, (ar_cov_convex_closedRect _ _ _ _).isPreconnected⟩
  have hWo : IsOpen (id '' (rc_xi h ∪ rc_xiS h)) := by
    rw [Set.image_id, hunion]
    exact hQo
  have hVc : IsConnected (toExt (id '' (rc_xi h ∪ rc_xiS h)))ᶜ := by
    rw [Set.image_id, hunion]
    exact ⟨⟨extInf, extInf_mem_compl_toExt _⟩,
      isPreconnected_compl_toExt (acl_isBounded_openRect _ _ _ _) (rc_isPreconnected_compl_openRect _ _ _ _)⟩
  have hdc := (t53_image_sep (hQo.sdiff hSc.isClosed) (rc_xi_isConnected hh0 hh1) hSc hSconn
    Set.disjoint_sdiff_left continuousOn_id (Set.injOn_id _) hWo hVc).1
  rwa [Set.image_id] at hdc

/-- The clamp vanishes on `(-∞, 0]`. -/
theorem rc_loop_clamp_of_nonpos {x : ℝ} (hx : x ≤ 0) : rc_clamp x = 0 := by
  unfold rc_clamp
  rw [min_eq_right (hx.trans zero_le_one), max_eq_left hx]

/-- The clamp is `1` on `[1, ∞)`. -/
theorem rc_loop_clamp_of_one_le {x : ℝ} (hx : 1 ≤ x) : rc_clamp x = 1 := by
  unfold rc_clamp
  rw [min_eq_left hx, max_eq_right zero_le_one]

/-- The clamp is the identity on `[0, 1]`. -/
theorem rc_loop_clamp_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : rc_clamp x = x := by
  unfold rc_clamp
  rw [min_eq_right h1, max_eq_right h0]

/-- The rectangle loop on the first quarter `[0, 1/4]`: the top side, from `A + Bi` to `-A + Bi`. -/
theorem rc_loop_fun_q1 (A B : ℝ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 4) :
    rc_rectLoopFun A B t = ((A + -8 * A * t : ℝ) : ℂ) + (B : ℂ) * I := by
  rw [rc_rectLoopFun, rc_loop_clamp_of_mem (x := 4 * t) (by linarith) (by linarith),
    rc_loop_clamp_of_nonpos (x := 4 * t - 2) (by linarith),
    rc_loop_clamp_of_nonpos (x := 4 * t - 1) (by linarith),
    rc_loop_clamp_of_nonpos (x := 4 * t - 3) (by linarith)]
  push_cast
  ring

/-- The rectangle loop on the second quarter `[1/4, 1/2]`: the left side, from `-A + Bi` to `-A - Bi`. -/
theorem rc_loop_fun_q2 (A B : ℝ) {t : ℝ} (h0 : 1 / 4 ≤ t) (h1 : t ≤ 1 / 2) :
    rc_rectLoopFun A B t = ((-A : ℝ) : ℂ) + ((3 * B + -8 * B * t : ℝ) : ℂ) * I := by
  rw [rc_rectLoopFun, rc_loop_clamp_of_one_le (x := 4 * t) (by linarith),
    rc_loop_clamp_of_nonpos (x := 4 * t - 2) (by linarith),
    rc_loop_clamp_of_mem (x := 4 * t - 1) (by linarith) (by linarith),
    rc_loop_clamp_of_nonpos (x := 4 * t - 3) (by linarith)]
  push_cast
  ring

/-- The rectangle loop on the third quarter `[1/2, 3/4]`: the bottom side, from `-A - Bi` to `A - Bi`. -/
theorem rc_loop_fun_q3 (A B : ℝ) {t : ℝ} (h0 : 1 / 2 ≤ t) (h1 : t ≤ 3 / 4) :
    rc_rectLoopFun A B t = ((-5 * A + 8 * A * t : ℝ) : ℂ) + ((-B : ℝ) : ℂ) * I := by
  rw [rc_rectLoopFun, rc_loop_clamp_of_one_le (x := 4 * t) (by linarith),
    rc_loop_clamp_of_mem (x := 4 * t - 2) (by linarith) (by linarith),
    rc_loop_clamp_of_one_le (x := 4 * t - 1) (by linarith),
    rc_loop_clamp_of_nonpos (x := 4 * t - 3) (by linarith)]
  push_cast
  ring

/-- The rectangle loop on the last quarter `[3/4, 1]`: the right side, from `A - Bi` to `A + Bi`. -/
theorem rc_loop_fun_q4 (A B : ℝ) {t : ℝ} (h0 : 3 / 4 ≤ t) (h1 : t ≤ 1) :
    rc_rectLoopFun A B t = (A : ℂ) + ((-7 * B + 8 * B * t : ℝ) : ℂ) * I := by
  rw [rc_rectLoopFun, rc_loop_clamp_of_one_le (x := 4 * t) (by linarith),
    rc_loop_clamp_of_one_le (x := 4 * t - 2) (by linarith),
    rc_loop_clamp_of_one_le (x := 4 * t - 1) (by linarith),
    rc_loop_clamp_of_mem (x := 4 * t - 3) (by linarith) (by linarith)]
  push_cast
  ring

/-- A point `x + y i` of the closed rectangle `[-A, A] × [-B, B]` on one of its four side lines lies on the
boundary `closedRect ∖ openRect`. -/
theorem rc_loop_mem_bdry {A B x y : ℝ} (hx : -A ≤ x ∧ x ≤ A) (hy : -B ≤ y ∧ y ≤ B)
    (hs : x = -A ∨ x = A ∨ y = -B ∨ y = B) :
    (x : ℂ) + (y : ℂ) * I ∈ closedRect (-A) A (-B) B \ openRect (-A) A (-B) B := by
  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hre]; exact hx.1
  · rw [hre]; exact hx.2
  · rw [him]; exact hy.1
  · rw [him]; exact hy.2
  · rintro ⟨h1, h2, h3, h4⟩
    rw [hre] at h1 h2
    rw [him] at h3 h4
    rcases hs with hs | hs | hs | hs <;> linarith

/-- For `-c ≤ u ≤ c` (`c > 0`) the parameter offset `(c - u)/(8c)` lies in `[0, 1/4]`, and `8c` times it is
`c - u`. -/
theorem rc_loop_frac_mem {c u : ℝ} (hc : 0 < c) (h1 : -c ≤ u) (h2 : u ≤ c) :
    0 ≤ (c - u) / (8 * c) ∧ (c - u) / (8 * c) ≤ 1 / 4 ∧ 8 * c * ((c - u) / (8 * c)) = c - u := by
  refine ⟨div_nonneg (by linarith) (by positivity), ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    linarith
  · field_simp

/-- The trace of the rectangle loop is the boundary of the rectangle (`A, B > 0`).

Proof: on the quarters of `[0, 1]` the clamps are affine and the loop runs along the top
(`x = A(1 - 8t)`, `y = B`), the left side (`x = -A`, `y = B(3 - 8t)`), the bottom (`x = A(8t - 5)`, `y = -B`) and
the right side (`x = A`, `y = B(8t - 7)`); conversely a boundary point `x + y i` is hit at `t = (A - x)/(8A)`,
`1/4 + (B - y)/(8B)`, `1/2 + (x + A)/(8A)` or `3/4 + (y + B)/(8B)`.
Uses: `ext`; `LRCurve.closedTrace`, `rc_rectLoopFun`, `rc_clamp`; case split on the quarter with
`max_eq_left/right`, `min_eq_left/right`; `Complex.ext_iff`. -/
theorem rc_rectLoop_closedTrace {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (rc_rectLoop A B).closedTrace = closedRect (-A) A (-B) B \ openRect (-A) A (-B) B := by
  ext z
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    show rc_rectLoopFun A B t ∈ closedRect (-A) A (-B) B \ openRect (-A) A (-B) B
    rcases le_total t (1 / 4) with h1 | h1
    · rw [rc_loop_fun_q1 A B ht0 h1]
      exact rc_loop_mem_bdry ⟨by nlinarith, by nlinarith⟩ ⟨by linarith, le_rfl⟩
        (Or.inr (Or.inr (Or.inr rfl)))
    rcases le_total t (1 / 2) with h2 | h2
    · rw [rc_loop_fun_q2 A B h1 h2]
      exact rc_loop_mem_bdry ⟨le_rfl, by linarith⟩ ⟨by nlinarith, by nlinarith⟩ (Or.inl rfl)
    rcases le_total t (3 / 4) with h3 | h3
    · rw [rc_loop_fun_q3 A B h2 h3]
      exact rc_loop_mem_bdry ⟨by nlinarith, by nlinarith⟩ ⟨le_rfl, by linarith⟩
        (Or.inr (Or.inr (Or.inl rfl)))
    · rw [rc_loop_fun_q4 A B h3 ht1]
      exact rc_loop_mem_bdry ⟨by linarith, le_rfl⟩ ⟨by nlinarith, by nlinarith⟩ (Or.inr (Or.inl rfl))
  · rintro ⟨⟨h1, h2, h3, h4⟩, hno⟩
    have hside : z.im = B ∨ z.re = -A ∨ z.im = -B ∨ z.re = A := by
      by_contra hc
      simp only [not_or] at hc
      exact hno ⟨lt_of_le_of_ne h1 (Ne.symm hc.2.1), lt_of_le_of_ne h2 hc.2.2.2,
        lt_of_le_of_ne h3 (Ne.symm hc.2.2.1), lt_of_le_of_ne h4 hc.1⟩
    rcases hside with hs | hs | hs | hs
    · obtain ⟨f0, f1, f2⟩ := rc_loop_frac_mem hA h1 h2
      refine ⟨(A - z.re) / (8 * A), ⟨f0, by linarith⟩, ?_⟩
      show rc_rectLoopFun A B _ = z
      rw [rc_loop_fun_q1 A B f0 f1]
      apply Complex.ext
      · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
        linarith
      · simp only [add_im, ofReal_re, mul_im, ofReal_im, I_re, I_im]
        linarith
    · obtain ⟨f0, f1, f2⟩ := rc_loop_frac_mem hB h3 h4
      refine ⟨1 / 4 + (B - z.im) / (8 * B), ⟨by linarith, by linarith⟩, ?_⟩
      show rc_rectLoopFun A B _ = z
      rw [rc_loop_fun_q2 A B (by linarith) (by linarith)]
      apply Complex.ext
      · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
        linarith
      · simp only [add_im, ofReal_re, mul_im, ofReal_im, I_re, I_im]
        linarith
    · obtain ⟨f0, f1, f2⟩ := rc_loop_frac_mem hA (neg_le_neg h2) (by linarith)
      refine ⟨1 / 2 + (A - -z.re) / (8 * A), ⟨by linarith, by linarith⟩, ?_⟩
      show rc_rectLoopFun A B _ = z
      rw [rc_loop_fun_q3 A B (by linarith) (by linarith)]
      apply Complex.ext
      · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
        linarith
      · simp only [add_im, ofReal_re, mul_im, ofReal_im, I_re, I_im]
        linarith
    · obtain ⟨f0, f1, f2⟩ := rc_loop_frac_mem hB (neg_le_neg h4) (by linarith)
      refine ⟨3 / 4 + (B - -z.im) / (8 * B), ⟨by linarith, by linarith⟩, ?_⟩
      show rc_rectLoopFun A B _ = z
      rw [rc_loop_fun_q4 A B (by linarith) (by linarith)]
      apply Complex.ext
      · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
        linarith
      · simp only [add_im, ofReal_re, mul_im, ofReal_im, I_re, I_im]
        linarith

/-- `(0, 1)` is covered, up to the null set `{1/4, 1/2, 3/4}`, by its four open quarters. -/
theorem rc_loop_lintegral_quarters_le (F : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioo (0 : ℝ) 1, F t ≤ ((∫⁻ t in Ioo 0 (1 / 4), F t) + ∫⁻ t in Ioo (1 / 4) (1 / 2), F t) +
      ((∫⁻ t in Ioo (1 / 2) (3 / 4), F t) + ∫⁻ t in Ioo (3 / 4) 1, F t) := by
  have hae : Ioo (0 : ℝ) 1 ≤ᵐ[volume]
      (Ioo 0 (1 / 4) ∪ Ioo (1 / 4) (1 / 2)) ∪ (Ioo (1 / 2) (3 / 4) ∪ Ioo (3 / 4) 1) := by
    rw [ae_le_set]
    refine measure_mono_null (t := ({1 / 4, 1 / 2, 3 / 4} : Set ℝ)) ?_ ((Set.toFinite _).measure_zero _)
    rintro t ⟨ht, hn⟩
    simp only [mem_union, mem_Ioo, not_or, not_and, not_lt] at hn
    simp only [mem_insert_iff, mem_singleton_iff]
    obtain ⟨⟨k1, k2⟩, k3, k4⟩ := hn
    rcases (k1 ht.1).lt_or_eq with g1 | g1
    · rcases (k2 g1).lt_or_eq with g2 | g2
      · rcases (k3 g2).lt_or_eq with g3 | g3
        · linarith [k4 g3, ht.2]
        · exact Or.inr (Or.inr g3.symm)
      · exact Or.inr (Or.inl g2.symm)
    · exact Or.inl g1.symm
  refine (lintegral_mono_set' hae).trans ?_
  exact (lintegral_union_le _ _ _).trans
    (add_le_add (lintegral_union_le _ _ _) (lintegral_union_le _ _ _))

/-- One side of the rectangle loop: on `(p, q)` the curve is `G ∘ (t ↦ a + b t)` with `G' = w`, `‖w‖ = 1`,
`b ≠ 0`; the affine substitution bounds its `ρ`-length by `∫_S ρ ∘ G` when `a + b t ∈ S`. -/
theorem rc_loop_side_le {γ : ℝ → ℂ} {ρ : ℂ → ℝ≥0∞} (G : ℝ → ℂ) {w : ℂ} {p q a b : ℝ} {S : Set ℝ}
    (hb : b ≠ 0) (hG : ∀ x, HasDerivAt G w x) (hw : ‖w‖ = 1)
    (hγ : ∀ t ∈ Ioo p q, γ t = G (a + b * t)) (hS : ∀ t ∈ Ioo p q, a + b * t ∈ S) :
    ∫⁻ t in Ioo p q, ρ (γ t) * ‖deriv γ t‖ₑ ≤ ∫⁻ x in S, ρ (G x) := by
  have hφ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => a + b * t) b t := fun t => by
    simpa using ((hasDerivAt_id' t).const_mul b).const_add a
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul (measurableSet_Ioo : MeasurableSet (Ioo p q))
    (fun t _ => (hφ t).hasDerivWithinAt)
    (fun x _ y _ hxy => mul_left_cancel₀ hb (add_left_cancel hxy)) (fun x => ρ (G x))
  have hd : ∀ t ∈ Ioo p q, deriv γ t = b • w := fun t ht =>
    (((hG (a + b * t)).scomp t (hφ t)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) hγ)).deriv
  calc ∫⁻ t in Ioo p q, ρ (γ t) * ‖deriv γ t‖ₑ
      = ∫⁻ t in Ioo p q, ENNReal.ofReal |b| * ρ (G (a + b * t)) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
        rw [hd t ht, hγ t ht, ← ofReal_norm, norm_smul, hw, mul_one, Real.norm_eq_abs, mul_comm]
    _ = ∫⁻ x in (fun t => a + b * t) '' Ioo p q, ρ (G x) := hcv.symm
    _ ≤ ∫⁻ x in S, ρ (G x) := lintegral_mono_set (image_subset_iff.2 hS)

/-- The `ρ`-length of the rectangle loop is at most the sum of the four side integrals (any `ρ`).

Proof: `(0, 1)` is the union of the four open quarters and three points (null); on the quarters the
derivative is the constant `-8A`, `-8B i`, `8A`, `8B i`, and the affine substitution onto the side gives
`∫_{-A}^{A} ρ(x + B i) dx` etc. (in fact equality).
Uses: `lintegral_union_le`, `setLIntegral_measure_zero` (points); `Filter.EventuallyEq.deriv_eq` on each open
quarter; `lintegral_image_eq_lintegral_abs_deriv_mul` (Mathlib `JacobianOneDim`), as in `vertSeg_rhoLength`
(Quadrilateral:776).  No measurability of `ρ` is needed. -/
theorem rc_rectLoop_rhoLength_le {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (ρ : ℂ → ℝ≥0∞) :
    (rc_rectLoop A B).rhoLength ρ ≤
      (∫⁻ x in Ioo (-A) A, (ρ ((x : ℂ) + (B : ℂ) * I) + ρ ((x : ℂ) + ((-B : ℝ) : ℂ) * I))) +
        ∫⁻ y in Ioo (-B) B, (ρ ((A : ℂ) + (y : ℂ) * I) + ρ (((-A : ℝ) : ℂ) + (y : ℂ) * I)) := by
  have hH : ∀ c x : ℝ, HasDerivAt (fun x : ℝ => (x : ℂ) + (c : ℂ) * I) ((1 : ℝ) : ℂ) x :=
    fun c x => (hasDerivAt_id' x).ofReal_comp.add_const _
  have hV : ∀ c y : ℝ, HasDerivAt (fun y : ℝ => (c : ℂ) + (y : ℂ) * I) (((1 : ℝ) : ℂ) * I) y :=
    fun c y => ((hasDerivAt_id' y).ofReal_comp.mul_const I).const_add _
  have hw1 : ‖((1 : ℝ) : ℂ)‖ = 1 := by simp
  have hwI : ‖((1 : ℝ) : ℂ) * I‖ = 1 := by simp
  have h1 := rc_loop_side_le (ρ := ρ) (γ := (rc_rectLoop A B).toFun) (fun x : ℝ => (x : ℂ) + (B : ℂ) * I)
    (p := 0) (q := 1 / 4) (a := A) (b := -8 * A) (S := Ioo (-A) A) (by nlinarith) (hH B) hw1
    (fun t ht => rc_loop_fun_q1 A B ht.1.le ht.2.le)
    (fun t ht => ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩)
  have h2 := rc_loop_side_le (ρ := ρ) (γ := (rc_rectLoop A B).toFun)
    (fun y : ℝ => ((-A : ℝ) : ℂ) + (y : ℂ) * I)
    (p := 1 / 4) (q := 1 / 2) (a := 3 * B) (b := -8 * B) (S := Ioo (-B) B) (by nlinarith) (hV (-A)) hwI
    (fun t ht => rc_loop_fun_q2 A B ht.1.le ht.2.le)
    (fun t ht => ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩)
  have h3 := rc_loop_side_le (ρ := ρ) (γ := (rc_rectLoop A B).toFun)
    (fun x : ℝ => (x : ℂ) + ((-B : ℝ) : ℂ) * I)
    (p := 1 / 2) (q := 3 / 4) (a := -5 * A) (b := 8 * A) (S := Ioo (-A) A) (by positivity) (hH (-B)) hw1
    (fun t ht => rc_loop_fun_q3 A B ht.1.le ht.2.le)
    (fun t ht => ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩)
  have h4 := rc_loop_side_le (ρ := ρ) (γ := (rc_rectLoop A B).toFun) (fun y : ℝ => (A : ℂ) + (y : ℂ) * I)
    (p := 3 / 4) (q := 1) (a := -7 * B) (b := 8 * B) (S := Ioo (-B) B) (by positivity) (hV A) hwI
    (fun t ht => rc_loop_fun_q4 A B ht.1.le ht.2.le)
    (fun t ht => ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩)
  calc (rc_rectLoop A B).rhoLength ρ
      ≤ ((∫⁻ x in Ioo (-A) A, ρ ((x : ℂ) + (B : ℂ) * I)) +
            ∫⁻ y in Ioo (-B) B, ρ (((-A : ℝ) : ℂ) + (y : ℂ) * I)) +
          ((∫⁻ x in Ioo (-A) A, ρ ((x : ℂ) + ((-B : ℝ) : ℂ) * I)) +
            ∫⁻ y in Ioo (-B) B, ρ ((A : ℂ) + (y : ℂ) * I)) :=
        (rc_loop_lintegral_quarters_le _).trans (add_le_add (add_le_add h1 h2) (add_le_add h3 h4))
    _ = ((∫⁻ x in Ioo (-A) A, ρ ((x : ℂ) + (B : ℂ) * I)) +
            ∫⁻ x in Ioo (-A) A, ρ ((x : ℂ) + ((-B : ℝ) : ℂ) * I)) +
          ((∫⁻ y in Ioo (-B) B, ρ ((A : ℂ) + (y : ℂ) * I)) +
            ∫⁻ y in Ioo (-B) B, ρ (((-A : ℝ) : ℂ) + (y : ℂ) * I)) := by ring
    _ ≤ _ := add_le_add (le_lintegral_add _ _) (le_lintegral_add _ _)

/-- For `0 < s < h < 1` the loop `∂((-(1-h+s), 1-h+s) × (-s, s))` is a separating curve of `Ξ_h`.

Proof: with `A = 1 - h + s < 1` and `B = s < h` the trace (the rectangle boundary, `rc_rectLoop_closedTrace`)
lies in `Q_h` and meets the real axis only at `±A` with `A > 1 - h`, so it avoids `S_h`.  The complement
`ℂ̄ ∖ Ξ_h = S_h ∪ (ℂ̄ ∖ Q_h)` has the two preconnected pieces `S_h` (inside the open rectangle of the loop) and
`ℂ̄ ∖ Q_h` (outside its closed rectangle); these two disjoint open sets cover `ℂ̄ ∖ trace`, so points of
different components of `ℂ̄ ∖ Ξ_h` are in different components of `ℂ̄ ∖ trace`.
Uses: `rc_rectLoop_isClosedCurve`, `rc_rectLoop_closedTrace`; the same/apart argument of
`circleCurve_mem_separatingCurves` (S04:1880–1938) with `isOpen_toExt_iff`, `isClosed_compl_toExt`
(CanonicalForm:49/51), `IsPreconnected.subset_left_of_subset_union`, `rc_isPreconnected_compl_openRect` and
`isPreconnected_compl_toExt` (CanonicalForm:100); `t53_tc_compl_eq_union` (S05:4595, `W = id`) for the complement. -/
theorem rc_rectLoop_mem_separatingCurves {h s : ℝ} (hh1 : h < 1) (hs0 : 0 < s) (hsh : s < h) :
    rc_rectLoop (1 - h + s) s ∈ separatingCurves (rc_xi h) := by
  set A := 1 - h + s with hA
  have hA0 : 0 < A := by linarith
  have htr := rc_rectLoop_closedTrace hA0 hs0
  have htrace : (rc_rectLoop A s).closedTrace ⊆ rc_xi h := by
    rw [htr]
    rintro z ⟨⟨k1, k2, k3, k4⟩, hno⟩
    refine ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, ?_⟩
    rintro ⟨g1, g2, g3, g4⟩
    exact hno ⟨by linarith, by linarith, by linarith, by linarith⟩
  refine ⟨rc_rectLoop_isClosedCurve _ _, htrace, ?_⟩
  -- `ℂ̄ ∖ Ξ_h = S_h ∪ (ℂ̄ ∖ Q_h)`, two preconnected pieces
  have hcompl : (toExt (rc_xi h))ᶜ = toExt (rc_xiS h) ∪ (toExt (rc_xiQ h))ᶜ := by
    ext y
    induction y using OnePoint.rec with
    | infty => exact iff_of_true (extInf_mem_compl_toExt _) (Or.inr (extInf_mem_compl_toExt _))
    | coe z =>
      rw [coe_mem_compl_toExt_iff, mem_union, coe_mem_toExt_iff, coe_mem_compl_toExt_iff]
      constructor
      · intro hz
        by_cases hzS : z ∈ rc_xiS h
        · exact Or.inl hzS
        · exact Or.inr fun hzQ => hz ⟨hzQ, hzS⟩
      · rintro (hzS | hzQ) hz
        · exact hz.2 hzS
        · exact hzQ hz.1
  have hSpre : IsPreconnected (toExt (rc_xiS h)) :=
    (ar_cov_convex_closedRect _ _ _ _).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
  have hQpre : IsPreconnected (toExt (rc_xiQ h))ᶜ :=
    isPreconnected_compl_toExt (acl_isBounded_openRect _ _ _ _) (rc_isPreconnected_compl_openRect _ _ _ _)
  have hSsub : toExt (rc_xiS h) ⊆ (toExt (rc_xi h))ᶜ := by
    rw [hcompl]
    exact subset_union_left
  have hQsub : (toExt (rc_xiQ h))ᶜ ⊆ (toExt (rc_xi h))ᶜ := by
    rw [hcompl]
    exact subset_union_right
  -- `ℂ̄ ∖ trace` is covered by the open inner rectangle and the complement of the closed one
  have hU1o : IsOpen (toExt (openRect (-A) A (-s) s)) := isOpen_toExt_iff.2 (acl_isOpen_openRect _ _ _ _)
  have hU2o : IsOpen (toExt (closedRect (-A) A (-s) s))ᶜ :=
    ((acl_isCompact_closedRect _ _ _ _).image OnePoint.continuous_coe).isClosed.isOpen_compl
  have hdisj : Disjoint (toExt (openRect (-A) A (-s) s)) (toExt (closedRect (-A) A (-s) s))ᶜ :=
    Set.disjoint_compl_right_iff_subset.2
      (image_mono (acl_openRect_subset_closedRect le_rfl le_rfl le_rfl le_rfl))
  have hcover : (toExt (rc_rectLoop A s).closedTrace)ᶜ ⊆
      toExt (openRect (-A) A (-s) s) ∪ (toExt (closedRect (-A) A (-s) s))ᶜ := by
    rw [htr]
    intro y hy
    induction y using OnePoint.rec with
    | infty => exact Or.inr (extInf_mem_compl_toExt _)
    | coe z =>
      rw [coe_mem_compl_toExt_iff] at hy
      by_cases hz : z ∈ openRect (-A) A (-s) s
      · exact Or.inl (mem_image_of_mem _ hz)
      · refine Or.inr ?_
        rw [coe_mem_compl_toExt_iff]
        exact fun hc => hy ⟨hc, hz⟩
  have hSU : toExt (rc_xiS h) ⊆ toExt (openRect (-A) A (-s) s) := image_mono fun z hz =>
    ⟨by linarith [hz.1], by linarith [hz.2.1], by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩
  have hQU : (toExt (rc_xiQ h))ᶜ ⊆ (toExt (closedRect (-A) A (-s) s))ᶜ :=
    compl_subset_compl.2 (image_mono fun z hz =>
      ⟨by linarith [hz.1], by linarith [hz.2.1], by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩)
  have hAC : (toExt (rc_xi h))ᶜ ⊆ (toExt (rc_rectLoop A s).closedTrace)ᶜ :=
    compl_subset_compl.2 (image_mono htrace)
  have same : ∀ {S : Set ExtPlane}, IsPreconnected S → S ⊆ (toExt (rc_xi h))ᶜ →
      ∀ {a b : ExtPlane}, a ∈ S → b ∈ S →
        connectedComponentIn (toExt (rc_xi h))ᶜ a = connectedComponentIn (toExt (rc_xi h))ᶜ b := by
    intro S hS hSA a b ha hb
    exact connectedComponentIn_eq (hS.subset_connectedComponentIn ha hSA hb)
  have apart : ∀ {a b : ExtPlane}, a ∈ toExt (rc_xiS h) → b ∈ (toExt (rc_xiQ h))ᶜ →
      connectedComponentIn (toExt (rc_rectLoop A s).closedTrace)ᶜ a ≠
        connectedComponentIn (toExt (rc_rectLoop A s).closedTrace)ᶜ b := by
    intro a b ha hb heq
    have haC : a ∈ (toExt (rc_rectLoop A s).closedTrace)ᶜ := hAC (hSsub ha)
    have hsub : connectedComponentIn (toExt (rc_rectLoop A s).closedTrace)ᶜ a ⊆
        toExt (openRect (-A) A (-s) s) :=
      isPreconnected_connectedComponentIn.subset_left_of_subset_union hU1o hU2o hdisj
        ((connectedComponentIn_subset _ _).trans hcover) ⟨a, mem_connectedComponentIn haC, hSU ha⟩
    have hbC : b ∈ (toExt (rc_rectLoop A s).closedTrace)ᶜ := hAC (hQsub hb)
    have hbin : b ∈ connectedComponentIn (toExt (rc_rectLoop A s).closedTrace)ᶜ a := by
      rw [heq]
      exact mem_connectedComponentIn hbC
    exact Set.disjoint_left.1 hdisj (hsub hbin) (hQU hb)
  intro x hx y hy hxy
  rw [hcompl] at hx hy
  rcases hx with hxS | hxQ <;> rcases hy with hyS | hyQ
  · exact absurd (same hSpre hSsub hxS hyS) hxy
  · exact apart hxS hyQ
  · exact fun heq => apart hyS hxQ heq.symm
  · exact absurd (same hQpre hQsub hxQ hyQ) hxy

/-- Affine substitution with unit slope, as an inequality: `∫_{(p,q)} G(φ(s)) ds ≤ ∫_S G` for
`φ(s) = a + b s` with `|b| = 1` and `φ(s) ∈ S` on `(p, q)`. -/
theorem rc_xi_lintegral_comp_le {G : ℝ → ℝ≥0∞} (φ : ℝ → ℝ) {p q a b : ℝ} {S : Set ℝ} (hb : |b| = 1)
    (hφ : ∀ s, φ s = a + b * s) (hS : ∀ s ∈ Ioo p q, φ s ∈ S) :
    ∫⁻ s in Ioo p q, G (φ s) ≤ ∫⁻ x in S, G x := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  have hd : ∀ t : ℝ, HasDerivAt φ b t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => a + b * t) b t := by
      simpa using ((hasDerivAt_id' t).const_mul b).const_add a
    rwa [show (fun t : ℝ => a + b * t) = φ from funext fun s => (hφ s).symm] at h1
  have hinj : InjOn φ (Ioo p q) := fun x _ y _ hxy => by
    rw [hφ, hφ] at hxy
    exact mul_left_cancel₀ hb0 (add_left_cancel hxy)
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul (measurableSet_Ioo : MeasurableSet (Ioo p q))
    (fun t _ => (hd t).hasDerivWithinAt) hinj G
  simp only [hb, ENNReal.ofReal_one, one_mul] at hcv
  rw [← hcv]
  exact lintegral_mono_set (image_subset_iff.2 hS)

/-- `ρ · 1_S = 1_S ρ` pointwise. -/
theorem rc_xi_mul_indicator_one (S : Set ℂ) (ρ : ℂ → ℝ≥0∞) (z : ℂ) :
    ρ z * S.indicator 1 z = S.indicator ρ z := by
  by_cases hz : z ∈ S <;> simp [hz]

/-- **Averaging over the loops**: `(inf_{Γ_sep(Ξ_h)} l_ρ) · h ≤ ∫ ρ g` (`0 < h < 1`, `ρ` measurable).

Proof: for `s ∈ (0, h)` the loop with `A = 1 - h + s`, `B = s` is separating, so the infimum is at most the four
side integrals, which only grow when their ranges are enlarged to `(-1, 1)` and `(-h, h)`.  Integrating over
`s ∈ (0, h)` (substituting `y = ±s` on the horizontal sides and `x = ±(1 - h + s)` on the vertical ones) gives
`∫_{Q₊} ρ + ∫_{Q₋} ρ + ∫_{R_r} ρ + ∫_{R_l} ρ = ∫ ρ g`.
Uses: `rc_rectLoop_mem_separatingCurves`, `rc_rectLoop_rhoLength_le`, `iInf₂_le`, `lintegral_mono_set`;
`setLIntegral_const`, `Real.volume_Ioo`, `setLIntegral_mono'`; Tonelli `lintegral_openRect` /
`lintegral_openRect_symm` (S09:5138/5148); `lintegral_add_left`, `lintegral_indicator`; template
`iInf_rhoLength_mul_log_le` (S04:2102). -/
theorem rc_iInf_rhoLength_mul_le {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) :
    (⨅ γ ∈ separatingCurves (rc_xi h), γ.rhoLength ρ) * ENNReal.ofReal h ≤
      ∫⁻ z, ρ z * rc_xiWeight h z := by
  have _ := hh0
  have hms : ∀ a b c d : ℝ, MeasurableSet (openRect a b c d) :=
    fun a b c d => (acl_isOpen_openRect a b c d).measurableSet
  -- the loops with `0 < s < h`
  have hpt : ∀ s ∈ Ioo 0 h, (⨅ γ ∈ separatingCurves (rc_xi h), γ.rhoLength ρ) ≤
      (∫⁻ x in Ioo (-1 : ℝ) 1, ρ ((x : ℂ) + (s : ℂ) * I)) +
        (∫⁻ x in Ioo (-1 : ℝ) 1, ρ ((x : ℂ) + ((-s : ℝ) : ℂ) * I)) +
        (∫⁻ y in Ioo (-h) h, ρ (((1 - h + s : ℝ) : ℂ) + (y : ℂ) * I)) +
        ∫⁻ y in Ioo (-h) h, ρ (((-(1 - h + s) : ℝ) : ℂ) + (y : ℂ) * I) := by
    intro s hs
    have hA0 : 0 < 1 - h + s := by linarith [hs.1]
    have hsub1 : Ioo (-(1 - h + s)) (1 - h + s) ⊆ Ioo (-1) 1 :=
      Ioo_subset_Ioo (by linarith [hs.2]) (by linarith [hs.2])
    have hsub2 : Ioo (-s) s ⊆ Ioo (-h) h := Ioo_subset_Ioo (by linarith [hs.2]) hs.2.le
    have hmx : Measurable fun x : ℝ => ρ ((x : ℂ) + (s : ℂ) * I) := hρ.comp (by fun_prop)
    have hmy : Measurable fun y : ℝ => ρ (((1 - h + s : ℝ) : ℂ) + (y : ℂ) * I) := hρ.comp (by fun_prop)
    calc (⨅ γ ∈ separatingCurves (rc_xi h), γ.rhoLength ρ)
        ≤ (rc_rectLoop (1 - h + s) s).rhoLength ρ :=
          iInf₂_le _ (rc_rectLoop_mem_separatingCurves hh1 hs.1 hs.2)
      _ ≤ _ := rc_rectLoop_rhoLength_le hA0 hs.1 ρ
      _ ≤ (∫⁻ x in Ioo (-1 : ℝ) 1, (ρ ((x : ℂ) + (s : ℂ) * I) + ρ ((x : ℂ) + ((-s : ℝ) : ℂ) * I))) +
            ∫⁻ y in Ioo (-h) h, (ρ (((1 - h + s : ℝ) : ℂ) + (y : ℂ) * I) +
              ρ (((-(1 - h + s) : ℝ) : ℂ) + (y : ℂ) * I)) :=
          add_le_add (lintegral_mono_set hsub1) (lintegral_mono_set hsub2)
      _ = _ := by rw [lintegral_add_left hmx, lintegral_add_left hmy, ← add_assoc]
  -- measurability in `s` of the four slice integrals
  have mBo : Measurable fun s : ℝ => ∫⁻ x in Ioo (-1 : ℝ) 1, ρ ((x : ℂ) + ((-s : ℝ) : ℂ) * I) :=
    (hρ.comp (by fun_prop : Continuous fun p : ℝ × ℝ => (p.2 : ℂ) + ((-p.1 : ℝ) : ℂ) * I).measurable
      ).lintegral_prod_right'
  have mRr : Measurable fun s : ℝ => ∫⁻ y in Ioo (-h) h, ρ (((1 - h + s : ℝ) : ℂ) + (y : ℂ) * I) :=
    (hρ.comp (by fun_prop : Continuous fun p : ℝ × ℝ => ((1 - h + p.1 : ℝ) : ℂ) + (p.2 : ℂ) * I).measurable
      ).lintegral_prod_right'
  have mRl : Measurable fun s : ℝ => ∫⁻ y in Ioo (-h) h, ρ (((-(1 - h + s) : ℝ) : ℂ) + (y : ℂ) * I) :=
    (hρ.comp (by fun_prop : Continuous fun p : ℝ × ℝ => ((-(1 - h + p.1) : ℝ) : ℂ) + (p.2 : ℂ) * I
      ).measurable).lintegral_prod_right'
  -- each slice family integrates to at most the integral over its box
  have htop : ∫⁻ s in Ioo 0 h, ∫⁻ x in Ioo (-1 : ℝ) 1, ρ ((x : ℂ) + (s : ℂ) * I) ≤
      ∫⁻ z in openRect (-1) 1 0 h, ρ z :=
    le_of_eq (lintegral_openRect_symm hρ).symm
  have hbot : ∫⁻ s in Ioo 0 h, ∫⁻ x in Ioo (-1 : ℝ) 1, ρ ((x : ℂ) + ((-s : ℝ) : ℂ) * I) ≤
      ∫⁻ z in openRect (-1) 1 (-h) 0, ρ z := by
    rw [lintegral_openRect_symm hρ]
    exact rc_xi_lintegral_comp_le (G := fun y : ℝ => ∫⁻ x in Ioo (-1 : ℝ) 1, ρ ((x : ℂ) + (y : ℂ) * I))
      (fun s => -s) (a := 0) (b := -1) (by norm_num) (fun s => show -s = 0 + -1 * s by ring)
      (fun s hs => show -s ∈ Ioo (-h) 0 from ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  have hright : ∫⁻ s in Ioo 0 h, ∫⁻ y in Ioo (-h) h, ρ (((1 - h + s : ℝ) : ℂ) + (y : ℂ) * I) ≤
      ∫⁻ z in openRect (1 - h) 1 (-h) h, ρ z := by
    rw [lintegral_openRect hρ]
    exact rc_xi_lintegral_comp_le (G := fun x : ℝ => ∫⁻ y in Ioo (-h) h, ρ ((x : ℂ) + (y : ℂ) * I))
      (fun s => 1 - h + s) (a := 1 - h) (b := 1) (by norm_num)
      (fun s => show 1 - h + s = 1 - h + 1 * s by ring)
      (fun s hs => show 1 - h + s ∈ Ioo (1 - h) 1 from ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  have hleft : ∫⁻ s in Ioo 0 h, ∫⁻ y in Ioo (-h) h, ρ (((-(1 - h + s) : ℝ) : ℂ) + (y : ℂ) * I) ≤
      ∫⁻ z in openRect (-1) (h - 1) (-h) h, ρ z := by
    rw [lintegral_openRect hρ]
    exact rc_xi_lintegral_comp_le (G := fun x : ℝ => ∫⁻ y in Ioo (-h) h, ρ ((x : ℂ) + (y : ℂ) * I))
      (fun s => -(1 - h + s)) (a := h - 1) (b := -1) (by norm_num)
      (fun s => show -(1 - h + s) = h - 1 + -1 * s by ring)
      (fun s hs => show -(1 - h + s) ∈ Ioo (-1) (h - 1) from ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  -- `∫ ρ g` is the sum of the four box integrals
  have hsplit : ∫⁻ z, ρ z * rc_xiWeight h z =
      (∫⁻ z in openRect (-1) 1 0 h, ρ z) + (∫⁻ z in openRect (-1) 1 (-h) 0, ρ z) +
        (∫⁻ z in openRect (1 - h) 1 (-h) h, ρ z) + ∫⁻ z in openRect (-1) (h - 1) (-h) h, ρ z := by
    have hg : ∀ z, ρ z * rc_xiWeight h z =
        (openRect (-1) 1 0 h).indicator ρ z + (openRect (-1) 1 (-h) 0).indicator ρ z +
          (openRect (1 - h) 1 (-h) h).indicator ρ z + (openRect (-1) (h - 1) (-h) h).indicator ρ z := by
      intro z
      simp only [rc_xiWeight, Pi.add_apply, mul_add, rc_xi_mul_indicator_one]
    rw [lintegral_congr hg, lintegral_add_right _ (hρ.indicator (hms (-1) (h - 1) (-h) h)),
      lintegral_add_right _ (hρ.indicator (hms (1 - h) 1 (-h) h)),
      lintegral_add_right _ (hρ.indicator (hms (-1) 1 (-h) 0)), lintegral_indicator (hms _ _ _ _),
      lintegral_indicator (hms _ _ _ _), lintegral_indicator (hms _ _ _ _), lintegral_indicator (hms _ _ _ _)]
  calc (⨅ γ ∈ separatingCurves (rc_xi h), γ.rhoLength ρ) * ENNReal.ofReal h
      = ∫⁻ _ in Ioo 0 h, (⨅ γ ∈ separatingCurves (rc_xi h), γ.rhoLength ρ) := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
    _ ≤ ∫⁻ s in Ioo 0 h, ((∫⁻ x in Ioo (-1 : ℝ) 1, ρ ((x : ℂ) + (s : ℂ) * I)) +
          (∫⁻ x in Ioo (-1 : ℝ) 1, ρ ((x : ℂ) + ((-s : ℝ) : ℂ) * I)) +
          (∫⁻ y in Ioo (-h) h, ρ (((1 - h + s : ℝ) : ℂ) + (y : ℂ) * I)) +
          ∫⁻ y in Ioo (-h) h, ρ (((-(1 - h + s) : ℝ) : ℂ) + (y : ℂ) * I)) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ = (∫⁻ s in Ioo 0 h, ∫⁻ x in Ioo (-1 : ℝ) 1, ρ ((x : ℂ) + (s : ℂ) * I)) +
          (∫⁻ s in Ioo 0 h, ∫⁻ x in Ioo (-1 : ℝ) 1, ρ ((x : ℂ) + ((-s : ℝ) : ℂ) * I)) +
          (∫⁻ s in Ioo 0 h, ∫⁻ y in Ioo (-h) h, ρ (((1 - h + s : ℝ) : ℂ) + (y : ℂ) * I)) +
          ∫⁻ s in Ioo 0 h, ∫⁻ y in Ioo (-h) h, ρ (((-(1 - h + s) : ℝ) : ℂ) + (y : ℂ) * I) := by
        rw [lintegral_add_right _ mRl, lintegral_add_right _ mRr, lintegral_add_right _ mBo]
    _ ≤ (∫⁻ z in openRect (-1) 1 0 h, ρ z) + (∫⁻ z in openRect (-1) 1 (-h) 0, ρ z) +
          (∫⁻ z in openRect (1 - h) 1 (-h) h, ρ z) + ∫⁻ z in openRect (-1) (h - 1) (-h) h, ρ z :=
        add_le_add (add_le_add (add_le_add htop hbot) hright) hleft
    _ = ∫⁻ z, ρ z * rc_xiWeight h z := hsplit.symm

/-- The area of an open rectangle: `|(a, b) × (c, d)| = (b - a)(d - c)`. -/
theorem rc_xi_volume_openRect (a b c d : ℝ) :
    volume (openRect a b c d) = ENNReal.ofReal (b - a) * ENNReal.ofReal (d - c) := by
  have hpre : Complex.measurableEquivRealProd ⁻¹' (Ioo a b ×ˢ Ioo c d) = openRect a b c d := by
    ext z
    simp [openRect, and_assoc]
  rw [← hpre, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]

/-- The pointwise bound `(q + r)² ≤ q + 3r` for `q = 1_P + 1_M`, `r = 1_R + 1_L` with `P ∩ M = R ∩ L = ∅`. -/
theorem rc_xi_sq_le_aux {P M R L : Set ℂ} (hPM : Disjoint P M) (hRL : Disjoint R L) (z : ℂ) :
    (P.indicator (1 : ℂ → ℝ≥0∞) z + M.indicator 1 z + R.indicator 1 z + L.indicator 1 z) ^ 2 ≤
      P.indicator 1 z + M.indicator 1 z + 3 * R.indicator 1 z + 3 * L.indicator 1 z := by
  by_cases h1 : z ∈ P
  · have h2 : z ∉ M := Set.disjoint_left.1 hPM h1
    by_cases h3 : z ∈ R
    · have h4 : z ∉ L := Set.disjoint_left.1 hRL h3
      simp [h1, h2, h3, h4]
      norm_num
    · by_cases h4 : z ∈ L
      · simp [h1, h2, h3, h4]
        norm_num
      · simp [h1, h2, h3, h4]
  · by_cases h3 : z ∈ R
    · have h4 : z ∉ L := Set.disjoint_left.1 hRL h3
      by_cases h2 : z ∈ M
      · simp [h1, h2, h3, h4]
        norm_num
      · simp [h1, h2, h3, h4]
    · by_cases h2 : z ∈ M <;> by_cases h4 : z ∈ L
      · simp [h1, h2, h3, h4]
        norm_num
      · simp [h1, h2, h3, h4]
      · simp [h1, h2, h3, h4]
      · simp [h1, h2, h3, h4]

/-- `∫ g² ≤ 4h + 12h²` for the averaging weight (`0 < h < 1`).

Proof: `Q₊ ∩ Q₋ = ∅` (sign of `im`) and `R_r ∩ R_l = ∅` (`1 - h > h - 1`), so with
`q = 1_{Q₊} + 1_{Q₋} ∈ {0, 1}` and `r = 1_{R_r} + 1_{R_l} ∈ {0, 1}`: `g² = (q + r)² ≤ q + 3r`; the four boxes have
areas `2h, 2h, 2h², 2h²`.  (A bound `g² ≤ 2(1_Q + 1_R)` would lose the sharp constant.)
Uses: the pointwise bound, `lintegral_mono`, `lintegral_add_left`/`lintegral_add_right`,
`lintegral_indicator`, `setLIntegral_const`; box areas via `Complex.volume_preserving_equiv_real_prod`
(pattern `volume_rectangle`, Quadrilateral:468) or `volume_restrict_openRect_eq_map` (S09:5126). -/
theorem rc_lintegral_xiWeight_sq_le {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ∫⁻ z, rc_xiWeight h z ^ 2 ≤ ENNReal.ofReal (4 * h + 12 * h ^ 2) := by
  have hPM : Disjoint (openRect (-1) 1 0 h) (openRect (-1) 1 (-h) 0) :=
    Set.disjoint_left.2 fun z h1 h2 => by linarith [h1.2.2.1, h2.2.2.2]
  have hRL : Disjoint (openRect (1 - h) 1 (-h) h) (openRect (-1) (h - 1) (-h) h) :=
    Set.disjoint_left.2 fun z h1 h2 => by linarith [h1.1, h2.2.1]
  have hm : ∀ a b c d : ℝ, Measurable ((openRect a b c d).indicator (1 : ℂ → ℝ≥0∞)) :=
    fun a b c d => measurable_one.indicator (acl_isOpen_openRect a b c d).measurableSet
  have hms : ∀ a b c d : ℝ, MeasurableSet (openRect a b c d) :=
    fun a b c d => (acl_isOpen_openRect a b c d).measurableSet
  have e1 : volume (openRect (-1) 1 0 h) = ENNReal.ofReal (2 * h) := by
    rw [rc_xi_volume_openRect, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have e2 : volume (openRect (-1) 1 (-h) 0) = ENNReal.ofReal (2 * h) := by
    rw [rc_xi_volume_openRect, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have e3 : 3 * volume (openRect (1 - h) 1 (-h) h) = ENNReal.ofReal (6 * h ^ 2) := by
    rw [rc_xi_volume_openRect, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_ofNat 3,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have e4 : 3 * volume (openRect (-1) (h - 1) (-h) h) = ENNReal.ofReal (6 * h ^ 2) := by
    rw [rc_xi_volume_openRect, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_ofNat 3,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  calc ∫⁻ z, rc_xiWeight h z ^ 2
      ≤ ∫⁻ z, ((openRect (-1) 1 0 h).indicator 1 z + (openRect (-1) 1 (-h) 0).indicator 1 z +
          3 * (openRect (1 - h) 1 (-h) h).indicator 1 z +
          3 * (openRect (-1) (h - 1) (-h) h).indicator 1 z) :=
        lintegral_mono fun z => rc_xi_sq_le_aux hPM hRL z
    _ = volume (openRect (-1) 1 0 h) + volume (openRect (-1) 1 (-h) 0) +
          3 * volume (openRect (1 - h) 1 (-h) h) + 3 * volume (openRect (-1) (h - 1) (-h) h) := by
        rw [lintegral_add_right _ ((hm (-1) (h - 1) (-h) h).const_mul 3),
          lintegral_add_right _ ((hm (1 - h) 1 (-h) h).const_mul 3),
          lintegral_add_right _ (hm (-1) 1 (-h) 0), lintegral_const_mul _ (hm (-1) (h - 1) (-h) h),
          lintegral_const_mul _ (hm (1 - h) 1 (-h) h), lintegral_indicator_one (hms _ _ _ _),
          lintegral_indicator_one (hms _ _ _ _), lintegral_indicator_one (hms _ _ _ _),
          lintegral_indicator_one (hms _ _ _ _)]
    _ = ENNReal.ofReal (4 * h + 12 * h ^ 2) := by
        rw [e1, e2, e3, e4, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **Extremal length bound** `λ(Γ_sep(Ξ_h)) ≤ 4/h + 12` (`0 < h < 1`): for an admissible `ρ`,
`(h · inf l_ρ)² ≤ (∫ ρ g)² ≤ A(ρ) ∫ g² ≤ A(ρ) (4h + 12h²)` (the template is
`extremalLength_annulusSeparating_le`, S04:2124). -/
theorem rc_extremalLength_xi_le {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    extremalLength (separatingCurves (rc_xi h)) ≤ ENNReal.ofReal (4 / h + 12) := by
  unfold extremalLength extremalLengthIn
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨hρm, hρ0, hρtop⟩ := hρ
  rw [← iInf_rhoLength_sq, ENNReal.div_le_iff hρ0.ne' hρtop.ne]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, (⨅ γ ∈ separatingCurves (rc_xi h), γ.rhoLength ρ) = ℓ := ⟨_, rfl⟩
  rw [hℓ]
  have hgm : Measurable (rc_xiWeight h) := by
    unfold rc_xiWeight
    refine (((measurable_one.indicator ?_).add (measurable_one.indicator ?_)).add
      (measurable_one.indicator ?_)).add (measurable_one.indicator ?_) <;>
      exact (acl_isOpen_openRect _ _ _ _).measurableSet
  have hiv : ℓ * ENNReal.ofReal h ≤ ∫⁻ z, ρ z * rc_xiWeight h z := by
    rw [← hℓ]
    exact rc_iInf_rhoLength_mul_le hh0 hh1 hρm
  have hcs : (∫⁻ z, ρ z * rc_xiWeight h z) ^ 2 ≤
      (∫⁻ z, ρ z ^ 2) * ∫⁻ z, rc_xiWeight h z ^ 2 := by
    have h1 := setLIntegral_mul_sq_le (s := univ) hρm hgm
    simpa only [Measure.restrict_univ] using h1
  have harea : ∫⁻ z, ρ z ^ 2 = rhoArea ρ univ := by
    rw [rhoArea, Measure.restrict_univ]
  have hsplit : ENNReal.ofReal (4 * h + 12 * h ^ 2) =
      ENNReal.ofReal h ^ 2 * ENNReal.ofReal (4 / h + 12) := by
    rw [← ENNReal.ofReal_pow hh0.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hkey : ENNReal.ofReal h ^ 2 * ℓ ^ 2 ≤
      ENNReal.ofReal h ^ 2 * (ENNReal.ofReal (4 / h + 12) * rhoArea ρ univ) := by
    calc ENNReal.ofReal h ^ 2 * ℓ ^ 2 = (ℓ * ENNReal.ofReal h) ^ 2 := by ring
      _ ≤ (∫⁻ z, ρ z * rc_xiWeight h z) ^ 2 := pow_le_pow_left' hiv 2
      _ ≤ (∫⁻ z, ρ z ^ 2) * ∫⁻ z, rc_xiWeight h z ^ 2 := hcs
      _ ≤ rhoArea ρ univ * ENNReal.ofReal (4 * h + 12 * h ^ 2) := by
          rw [harea]
          exact mul_le_mul_right (rc_lintegral_xiWeight_sq_le hh0 hh1) _
      _ = ENNReal.ofReal h ^ 2 * (ENNReal.ofReal (4 / h + 12) * rhoArea ρ univ) := by
          rw [hsplit]
          ring
  have hh2 : ENNReal.ofReal h ^ 2 ≠ 0 := pow_ne_zero 2 (ENNReal.ofReal_pos.2 hh0).ne'
  have hh2t : ENNReal.ofReal h ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_mul_iff_right hh2 hh2t).1 hkey

/-- **The model lower bound** `M(Ξ_h) ≥ πh/(2(1+3h))` (`0 < h < 1`): Theorem 4.9 with
`λ(Γ_sep) ≤ 4/h + 12`, `2π/(4/h + 12) = πh/(2(1+3h))`. -/
theorem rc_dcModulus_xi_ge {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ENNReal.ofReal (π * h / (2 * (1 + 3 * h))) ≤ dcModulus (rc_xi h) := by
  rw [thm4_9_dcModulus_eq (rc_isDoublyConnected_xi hh0 hh1)]
  calc ENNReal.ofReal (π * h / (2 * (1 + 3 * h)))
      = ENNReal.ofReal (2 * π) / ENNReal.ofReal (4 / h + 12) := by
        rw [← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        field_simp
        ring
    _ ≤ ENNReal.ofReal (2 * π) / extremalLength (separatingCurves (rc_xi h)) :=
        ENNReal.div_le_div_left (rc_extremalLength_xi_le hh0 hh1) _

/-- The model lower bound for affine images: `M(β + α Ξ_h) ≥ πh/(2(1+3h))` (`α ≠ 0`, `0 < h < 1`). -/
theorem rc_dcModulus_affine_xi_ge {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) {α : ℂ} (hα : α ≠ 0) (β : ℂ) :
    ENNReal.ofReal (π * h / (2 * (1 + 3 * h))) ≤ dcModulus ((fun w => β + α * w) '' rc_xi h) := by
  rw [rc_dcModulus_affine (rc_isDoublyConnected_xi hh0 hh1) hα β]
  exact rc_dcModulus_xi_ge hh0 hh1

/-! ### Stage A2 (L1b): the ring condition implies `IsACL f D`

The S09 proof of Theorem 9.1 (`acl_rect_estimate` S09:529 → `acl_sum_dist_le` S09:610 → `acl_horizontal` S09:764,
`acl_vertical` S09:788 → `thm9_1_isACL` S09:1081) uses Definition 7.1 only in the per-rectangle estimate.  Here
that estimate comes from the master ring inequality `rc_xi_ring_bound` (a slit ring `Ξ` centred in the thin
rectangle; first conjunct of the hypothesis, for the PREIMAGE ring), with constant `3K` in place of `K`; the
rest of the chain is S09's with `hf : IsKQC f D K` replaced by `(hD) (hK) (hc) (hi) (hring)`.  The S09 helpers
reused unchanged contain no `IsKQC`: `acl_sum_volume_le` (S09:437–511), `acl_monotone_aclArea` (425–433),
`acl_volume_image_lt_top` (414–419), `acl_closure_openRect_subset` (380–384), `acl_closedRect_subset` (368–371),
`acl_openRect_subset_closedRect` (372–375), `acl_isCompact_closedRect` (364–367), `acl_isBounded_openRect`
(376–379), `acl_isOpen_openRect` (978–981), `acl_mem_closedRect` (520–523), `aclArea` (422–424). -/

/-- **LM (master ring inequality).** For the slit ring `B = φ '' Ξ_h`, `φ w = β + α w` (`α ≠ 0`,
`0 < h < 1`), with `closure (φ '' Q_h) ⊆ D`:
`πh/(2(1+3h)) ≤ K · 2π · (1/(2 d))² · m(f(B))`, `d = |f(φ(1-h)) - f(φ(h-1))|` (the images of the slit ends).
Proof: the model bound `M(B) ≥ πh/(2(1+3h))`; the FIRST conjunct `M(B) ≤ K M(f(B))` (`hring B`, where
`closure (toExt B) = toExt (closure B) ⊆ toExt (closure (φ '' Q_h)) ⊆ toExt D` as `B` is bounded); and L0 at the
image (`rc_dcModulus_image_le`, `U = φ '' Q_h`, `C = φ '' S_h`, `U ∖ C = B`). -/
theorem rc_xi_ring_bound {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hD : IsOpen D) (hc : ContinuousOn f D)
    (hi : InjOn f D) (hring : rc_RingBound f D K) {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    {α β : ℂ} (hα : α ≠ 0) (hQD : closure ((fun w => β + α * w) '' rc_xiQ h) ⊆ D) :
    ENNReal.ofReal (π * h / (2 * (1 + 3 * h))) ≤
      ENNReal.ofReal K * (ENNReal.ofReal (2 * π) *
        (ENNReal.ofReal (1 / (2 * ‖f (β + α * ((1 - h : ℝ) : ℂ)) - f (β + α * ((h - 1 : ℝ) : ℂ))‖)) ^ 2 *
          volume (f '' ((fun w => β + α * w) '' rc_xi h)))) := by
  have hφc : Continuous fun w : ℂ => β + α * w := by fun_prop
  have hφi : InjOn (fun w : ℂ => β + α * w) univ := (rc_isConformalOnto_affine hα β univ).2.1
  have hSQ : rc_xiS h ⊆ rc_xiQ h := by
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hQb : Bornology.IsBounded (rc_xiQ h) := acl_isBounded_openRect _ _ _ _
  have hUb : Bornology.IsBounded ((fun w : ℂ => β + α * w) '' rc_xiQ h) :=
    (hQb.isCompact_closure.image hφc).isBounded.subset (image_mono subset_closure)
  have hXi : IsDoublyConnected (rc_xi h) := rc_isDoublyConnected_xi hh0 hh1
  have hB : IsDoublyConnected ((fun w : ℂ => β + α * w) '' rc_xi h) :=
    rc_isDoublyConnected_affine hXi (hQb.subset sdiff_subset) hα β
  have hBU : (fun w : ℂ => β + α * w) '' rc_xi h ⊆ (fun w : ℂ => β + α * w) '' rc_xiQ h :=
    image_mono sdiff_subset
  have hBD : closure (toExt ((fun w : ℂ => β + α * w) '' rc_xi h)) ⊆ toExt D := by
    rw [closure_toExt_eq_toExt_closure_of_isBounded (hUb.subset hBU)]
    exact image_mono ((closure_mono hBU).trans hQD)
  have hU : IsOpen ((fun w : ℂ => β + α * w) '' rc_xiQ h) :=
    isOpen_image_of_continuousOn_injOn (acl_isOpen_openRect _ _ _ _) hφc.continuousOn
      (hφi.mono (subset_univ _))
  have hUD : (fun w : ℂ => β + α * w) '' rc_xiQ h ⊆ D := subset_closure.trans hQD
  have hC : IsCompact ((fun w : ℂ => β + α * w) '' rc_xiS h) :=
    (acl_isCompact_closedRect _ _ _ _).image hφc
  have hCU : (fun w : ℂ => β + α * w) '' rc_xiS h ⊆ (fun w : ℂ => β + α * w) '' rc_xiQ h :=
    image_mono hSQ
  have hdiff : (fun w : ℂ => β + α * w) '' rc_xi h =
      (fun w : ℂ => β + α * w) '' rc_xiQ h \ (fun w : ℂ => β + α * w) '' rc_xiS h :=
    (hφi.mono (subset_univ _)).image_sdiff_subset hSQ
  have hSmem : ∀ x : ℝ, h - 1 ≤ x → x ≤ 1 - h → (x : ℂ) ∈ rc_xiS h := by
    intro x hx1 hx2
    exact ⟨by simpa using hx1, by simpa using hx2, by simp, by simp⟩
  have hp : β + α * ((h - 1 : ℝ) : ℂ) ∈ (fun w : ℂ => β + α * w) '' rc_xiS h :=
    mem_image_of_mem _ (hSmem _ le_rfl (by linarith))
  have hq : β + α * ((1 - h : ℝ) : ℂ) ∈ (fun w : ℂ => β + α * w) '' rc_xiS h :=
    mem_image_of_mem _ (hSmem _ (by linarith) le_rfl)
  have hpq : f (β + α * ((h - 1 : ℝ) : ℂ)) ≠ f (β + α * ((1 - h : ℝ) : ℂ)) := by
    intro heq
    have h1 := hi (hUD (hCU hp)) (hUD (hCU hq)) heq
    have h2 : ((h - 1 : ℝ) : ℂ) = ((1 - h : ℝ) : ℂ) := hφi (mem_univ _) (mem_univ _) h1
    have h3 : h - 1 = 1 - h := Complex.ofReal_injective h2
    linarith
  have hfB : IsDoublyConnected (f '' ((fun w : ℂ => β + α * w) '' rc_xiQ h \
      (fun w : ℂ => β + α * w) '' rc_xiS h)) := by
    rw [← hdiff]
    exact rc_isDoublyConnected_image hD hc hi hB hBD
  have hup := rc_dcModulus_image_le hc hi hU hUD hC hCU hfB hp hq hpq
  rw [← hdiff] at hup
  calc ENNReal.ofReal (π * h / (2 * (1 + 3 * h)))
      ≤ dcModulus ((fun w : ℂ => β + α * w) '' rc_xi h) := rc_dcModulus_affine_xi_ge hh0 hh1 hα β
    _ ≤ ENNReal.ofReal K * dcModulus (f '' ((fun w : ℂ => β + α * w) '' rc_xi h)) := hring _ hB hBD
    _ ≤ _ := mul_le_mul_right hup _

/-- **L1b per-rectangle estimate** (replaces `acl_rect_estimate`, S09:529–605, whose Definition 7.1 + Rengel step
is replaced by LM).  For `R = (x′, x″) × (t, t + h)` inside `R̄₀ = closedRect a b c d ⊆ D`, with `2h ≤ ℓ := x″ - x′`,
`h < ρ` and `f` moving pairs of points of `R̄₀` at distance `< ρ` by `< η`:
`u² · h/(ℓ · 3K) ≤ m(f(R))`, where `u = max (|f(x′ + t i) - f(x″ + t i)| - 2η) 0`.

Proof: put `s = h/ℓ ∈ (0, 1/2]`, `α = ℓ/2`, `β = (x′+x″)/2 + (t + h/2) i`, `φ w = β + α w`, `B = φ '' Ξ_s`.
(1) Closure chain: `Ξ_s ⊆ Q_s` and `φ '' Q_s ⊆ openRect x′ x″ t (t+h)` (`re = (x′+x″)/2 + (ℓ/2)X`,
`im = t + h/2 + (ℓ/2)Y`, `(ℓ/2)s = h/2`), so `closure (φ '' Q_s) ⊆ closedRect x′ x″ t (t+h)`
(`acl_closure_openRect_subset`, S09:380) `⊆ closedRect a b c d` (`acl_closedRect_subset hax hxb hct htd`, S09:368)
`⊆ D` (`hR`); this is LM's `hQD`, and LM turns it into `closure (toExt B) ⊆ toExt D`
(`closure_toExt_eq_toExt_closure_of_isBounded`).  LM (FIRST conjunct, preimage ring `B`) gives
`πs/(2(1+3s)) ≤ K · 2π · (1/(2d))² · m(f(B))` with `d = ‖f q - f p‖`, `q = φ(1-s) = (x″ - h/2) + (t + h/2) i`,
`p = φ(s-1) = (x′ + h/2) + (t + h/2) i`.
(2) `u ≤ d`: `|p - (x′ + t i)| = |q - (x″ + t i)| = h/√2 ≤ |re| + |im| = h < ρ`, and
`p, q, x′ + t i, x″ + t i ∈ closedRect a b c d` (`x′ + h/2 ≤ x″`, `t + h/2 ≤ d`), so `hρ` and the triangle inequality
give `|f(x′+ti) - f(x″+ti)| < η + d + η`.
(3) `m(f(B)) ≤ V := m(f(R)) < ⊤` (`B ⊆ φ '' Q_s ⊆ R`; `acl_volume_image_lt_top`, S09:414).  If `u = 0` the claim is
`0 ≤ V`; else `d ≥ u > 0` and `πs/(2(1+3s)) ≤ KπV/(2d²)` gives `sd² ≤ K(1+3s)V ≤ (5/2)KV ≤ 3KV`, i.e.
`u² h/(ℓ · 3K) ≤ V`. -/
theorem rc_rect_estimate {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hD : IsOpen D) (hK : 0 < K)
    (hc : ContinuousOn f D) (hi : InjOn f D) (hring : rc_RingBound f D K) {a b c d : ℝ}
    (hR : closedRect a b c d ⊆ D) {x' x'' t h η ρ : ℝ} (hh : 0 < h) (hhℓ : 2 * h ≤ x'' - x')
    (hhρ : h < ρ) (hax : a ≤ x') (hxb : x'' ≤ b) (hct : c ≤ t) (htd : t + h ≤ d)
    (hρ : ∀ z ∈ closedRect a b c d, ∀ w ∈ closedRect a b c d, dist z w < ρ → dist (f z) (f w) < η) :
    (max (dist (f ((x' : ℂ) + (t : ℂ) * I)) (f ((x'' : ℂ) + (t : ℂ) * I)) - 2 * η) 0) ^ 2 *
        (h / ((x'' - x') * (3 * K))) ≤
      (volume (f '' openRect x' x'' t (t + h))).toReal := by
  have hℓ0 : 0 < x'' - x' := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = h / (x'' - x') := ⟨_, rfl⟩
  have hs0 : 0 < s := by
    rw [hs]
    positivity
  have hs1 : s ≤ 1 / 2 := by
    rw [hs, div_le_iff₀ hℓ0]
    linarith
  have hsh : (x'' - x') / 2 * s = h / 2 := by
    rw [hs]
    field_simp
  have hα0 : (((x'' - x') / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  -- (1) the ring sits in the rectangle
  have hsub : (fun w => ((((x' + x'') / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I) +
      (((x'' - x') / 2 : ℝ) : ℂ) * w) '' rc_xiQ s ⊆ openRect x' x'' t (t + h) := by
    rintro _ ⟨w, ⟨hw1, hw2, hw3, hw4⟩, rfl⟩
    show (((x' + x'') / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I + (((x'' - x') / 2 : ℝ) : ℂ) * w ∈
      openRect x' x'' t (t + h)
    have hre : ((((x' + x'') / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I +
        (((x'' - x') / 2 : ℝ) : ℂ) * w).re = (x' + x'') / 2 + (x'' - x') / 2 * w.re := by
      simp
    have him : ((((x' + x'') / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I +
        (((x'' - x') / 2 : ℝ) : ℂ) * w).im = t + h / 2 + (x'' - x') / 2 * w.im := by
      simp
    have hl2 : 0 < (x'' - x') / 2 := by positivity
    have e1 := mul_lt_mul_of_pos_left hw1 hl2
    have e2 := mul_lt_mul_of_pos_left hw2 hl2
    have e3 := mul_lt_mul_of_pos_left hw3 hl2
    have e4 := mul_lt_mul_of_pos_left hw4 hl2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hre]
      linarith
    · rw [hre]
      linarith
    · rw [him]
      linarith
    · rw [him]
      linarith
  have hQD : closure ((fun w => ((((x' + x'') / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I) +
      (((x'' - x') / 2 : ℝ) : ℂ) * w) '' rc_xiQ s) ⊆ D :=
    (closure_mono hsub).trans ((acl_closure_openRect_subset _ _ _ _).trans
      ((acl_closedRect_subset hax hxb hct htd).trans hR))
  have hLM := rc_xi_ring_bound hD hc hi hring hs0 (by linarith) hα0 hQD
  -- the slit ends
  have hq : ((((x' + x'') / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I) +
      (((x'' - x') / 2 : ℝ) : ℂ) * ((1 - s : ℝ) : ℂ) = ((x'' - h / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp
      linarith
    · simp
  have hp : ((((x' + x'') / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I) +
      (((x'' - x') / 2 : ℝ) : ℂ) * ((s - 1 : ℝ) : ℂ) = ((x' + h / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp
      linarith
    · simp
  rw [hq, hp] at hLM
  -- (2) the moves are shorter than `ρ`
  have hmove : ∀ x y : ℝ, dist ((x : ℂ) + (t : ℂ) * I) ((y : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I) ≤
      |x - y| + h / 2 := by
    intro x y
    rw [Complex.dist_eq]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, sub_im, add_im, mul_im, zero_add]
    rw [show t - (t + h / 2) = -(h / 2) by ring, abs_neg, abs_of_pos (show (0 : ℝ) < h / 2 by positivity)]
  have hc1 : (x' : ℂ) + (t : ℂ) * I ∈ closedRect a b c d :=
    acl_mem_closedRect hax (by linarith) hct (by linarith)
  have hc2 : (x'' : ℂ) + (t : ℂ) * I ∈ closedRect a b c d :=
    acl_mem_closedRect (by linarith) hxb hct (by linarith)
  have hpR : ((x' + h / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I ∈ closedRect a b c d :=
    acl_mem_closedRect (by linarith) (by linarith) (by linarith) (by linarith)
  have hqR : ((x'' - h / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I ∈ closedRect a b c d :=
    acl_mem_closedRect (by linarith) (by linarith) (by linarith) (by linarith)
  have hd1 : dist (f ((x' : ℂ) + (t : ℂ) * I)) (f (((x' + h / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I)) < η := by
    refine hρ _ hc1 _ hpR (lt_of_le_of_lt (hmove _ _) ?_)
    rw [show x' - (x' + h / 2) = -(h / 2) by ring, abs_neg, abs_of_pos (show (0 : ℝ) < h / 2 by positivity)]
    linarith
  have hd2 : dist (f (((x'' - h / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I)) (f ((x'' : ℂ) + (t : ℂ) * I)) < η := by
    rw [dist_comm]
    refine hρ _ hc2 _ hqR (lt_of_le_of_lt (hmove _ _) ?_)
    rw [show x'' - (x'' - h / 2) = h / 2 by ring, abs_of_pos (show (0 : ℝ) < h / 2 by positivity)]
    linarith
  obtain ⟨dd, hdd⟩ : ∃ dd : ℝ, dd = ‖f (((x'' - h / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I) -
      f (((x' + h / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I)‖ := ⟨_, rfl⟩
  rw [← hdd] at hLM
  have htri : dist (f ((x' : ℂ) + (t : ℂ) * I)) (f ((x'' : ℂ) + (t : ℂ) * I)) < η + dd + η := by
    have h4 := dist_triangle4 (f ((x' : ℂ) + (t : ℂ) * I))
      (f (((x' + h / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I))
      (f (((x'' - h / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I)) (f ((x'' : ℂ) + (t : ℂ) * I))
    rw [dist_comm (f (((x' + h / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I))
      (f (((x'' - h / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I)),
      dist_eq_norm (f (((x'' - h / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I))
        (f (((x' + h / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I)), ← hdd] at h4
    linarith
  -- (3) the area and the algebra
  have hVE : volume (f '' openRect x' x'' t (t + h)) < ⊤ :=
    acl_volume_image_lt_top hc hR (acl_openRect_subset_closedRect hax hxb hct htd)
  set V := (volume (f '' openRect x' x'' t (t + h))).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hBV : volume (f '' ((fun w => ((((x' + x'') / 2 : ℝ) : ℂ) + ((t + h / 2 : ℝ) : ℂ) * I) +
      (((x'' - x') / 2 : ℝ) : ℂ) * w) '' rc_xi s)) ≤ ENNReal.ofReal V := by
    rw [hV, ENNReal.ofReal_toReal hVE.ne]
    exact measure_mono (image_mono ((image_mono sdiff_subset).trans hsub))
  rcases le_or_gt (dist (f ((x' : ℂ) + (t : ℂ) * I)) (f ((x'' : ℂ) + (t : ℂ) * I)) - 2 * η) 0 with hu | hu
  · rw [max_eq_right hu]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    exact hV0
  rw [max_eq_left hu.le]
  have hdpos : 0 < dd := by linarith
  have hstep : ENNReal.ofReal (π * s / (2 * (1 + 3 * s))) ≤
      ENNReal.ofReal (K * (2 * π * ((1 / (2 * dd)) ^ 2 * V))) := by
    refine hLM.trans ?_
    rw [ENNReal.ofReal_mul hK.le, ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * π by positivity),
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ (1 / (2 * dd)) ^ 2 by positivity),
      ENNReal.ofReal_pow (show (0 : ℝ) ≤ 1 / (2 * dd) by positivity)]
    gcongr
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hstep
  have h13 : 2 * (1 + 3 * s) ≠ 0 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hstep (show 0 ≤ 2 * (1 + 3 * s) * (2 * dd) ^ 2 by positivity)
  have h2 : π * s / (2 * (1 + 3 * s)) * (2 * (1 + 3 * s) * (2 * dd) ^ 2) = π * s * (2 * dd) ^ 2 := by
    rw [← mul_assoc, div_mul_cancel₀ _ h13]
  have hinv : (1 / (2 * dd)) ^ 2 * (2 * dd) ^ 2 = 1 := by
    rw [← mul_pow, one_div, inv_mul_cancel₀ (by positivity), one_pow]
  have h3 : K * (2 * π * ((1 / (2 * dd)) ^ 2 * V)) * (2 * (1 + 3 * s) * (2 * dd) ^ 2) =
      K * (2 * π) * V * (2 * (1 + 3 * s)) := by
    calc K * (2 * π * ((1 / (2 * dd)) ^ 2 * V)) * (2 * (1 + 3 * s) * (2 * dd) ^ 2)
        = K * (2 * π) * V * (2 * (1 + 3 * s)) * ((1 / (2 * dd)) ^ 2 * (2 * dd) ^ 2) := by ring
      _ = K * (2 * π) * V * (2 * (1 + 3 * s)) := by rw [hinv, mul_one]
  rw [h2, h3] at h1
  -- h1 : π s (2 dd)² ≤ 4π K V (1 + 3s), i.e. s dd² ≤ K (1 + 3s) V
  have hkey : s * dd ^ 2 ≤ K * (1 + 3 * s) * V := by
    have hpi : 0 < 4 * π := by positivity
    refine le_of_mul_le_mul_left ?_ hpi
    calc 4 * π * (s * dd ^ 2) = π * s * (2 * dd) ^ 2 := by ring
      _ ≤ K * (2 * π) * V * (2 * (1 + 3 * s)) := h1
      _ = 4 * π * (K * (1 + 3 * s) * V) := by ring
  have hkey2 : s * dd ^ 2 ≤ 3 * K * V := by
    have : K * (1 + 3 * s) * V ≤ K * 3 * V := by
      have hKV : 0 ≤ K * V := mul_nonneg hK.le hV0
      nlinarith
    linarith
  have hu2 : (dist (f ((x' : ℂ) + (t : ℂ) * I)) (f ((x'' : ℂ) + (t : ℂ) * I)) - 2 * η) ^ 2 ≤ dd ^ 2 :=
    pow_le_pow_left₀ hu.le (by linarith) 2
  have hfrac : h / ((x'' - x') * (3 * K)) = s / (3 * K) := by
    rw [hs]
    field_simp
  rw [hfrac, ← mul_div_assoc, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hu2 hs0.le]

/-- **L1b key estimate** (the copy of `acl_sum_dist_le`, S09:610–760, with the ring estimate).  At `t₀ ∈ (c, d)`
where `g = aclArea f a b c d` is differentiable, for a disjoint family `E` of `n` intervals of `[a, b]`:
`Σ |f(E_i.1 + i t₀) - f(E_i.2 + i t₀)| ≤ √(3K (|g′(t₀)| + 1) Σ |E_i|)`.

Proof: S09's argument with constant `3K`; the only new choice (`2h ≤ ℓ_i`) concerns finitely many intervals that
are fixed before `h` is chosen.
Uses: the body of `acl_sum_dist_le` (S09:610–760) with the substitutions: 618 `hK0 := hK`; 619 `hc`;
620 `hinj := hi`; 622 `L := 3 * K * (|deriv g t₀| + 1)`; keep the 2-D uniform continuity `hρ` of 655–656
(`Metric.uniformContinuousOn_iff`, compact `closedRect a b c d`) and DROP the vertical `hρ'` (665–672); a new
`h₁ > 0` with `∀ i ∈ Finset.range n, (E i).1 ≠ (E i).2 → 2 * h₁ ≤ dist (E i).1 (E i).2`
(`Filter.eventually_all_finset` on `𝓝[>] 0`, `.exists`) and
`h := min (min (min (ρ / 2) (h₀ / 2)) ((d - t₀) / 2)) h₁` (658); in `hper` (680–709) the bound `3 * K / h * v i` from
`rc_rect_estimate hD hK hc hi hring hR hh0 (2h ≤ max - min, via S09:699–700) hhρ (le_min h1.1 h2.1)
(max_le h1.2 h2.2) ht₀.1.le htd hρ`; `K ↦ 3 * K` in 705–717; the rest verbatim (`acl_sum_volume_le`, S09:437, needs
only `hc`, `hi`; Cauchy–Schwarz 723–760). -/
theorem rc_sum_dist_le {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hD : IsOpen D) (hK : 0 < K)
    (hc : ContinuousOn f D) (hi : InjOn f D) (hring : rc_RingBound f D K) {a b c d : ℝ}
    (hab : a < b) (hR : closedRect a b c d ⊆ D) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo c d)
    (hg : DifferentiableAt ℝ (aclArea f a b c d) t₀) {n : ℕ} {E : ℕ → ℝ × ℝ}
    (hE : (n, E) ∈ AbsolutelyContinuousOnInterval.disjWithin a b) :
    ∑ i ∈ Finset.range n,
        dist (f (((E i).1 : ℂ) + (t₀ : ℂ) * I)) (f (((E i).2 : ℂ) + (t₀ : ℂ) * I)) ≤
      Real.sqrt (3 * K * (|deriv (aclArea f a b c d) t₀| + 1) *
        ∑ i ∈ Finset.range n, dist (E i).1 (E i).2) := by
  have hK0 : 0 < K := hK
  have hinj := hi
  set g := aclArea f a b c d with hgdef
  set L := 3 * K * (|deriv g t₀| + 1) with hL
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
  -- a height `h₁` with `2 h₁ ≤ |E_i|` for the finitely many nondegenerate intervals
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ i ∈ Finset.range n,
      (E i).1 ≠ (E i).2 → 2 * x ≤ dist (E i).1 (E i).2 := by
    rw [Filter.eventually_all_finset]
    intro i _
    by_cases hne : (E i).1 = (E i).2
    · exact Filter.Eventually.of_forall fun x h => absurd hne h
    · have hpos : 0 < dist (E i).1 (E i).2 := dist_pos.2 hne
      filter_upwards [Ioo_mem_nhdsGT (half_pos hpos)] with x hx
      intro _
      linarith [hx.2]
  obtain ⟨h₁, hh₁, hh₁0⟩ := (hev.and self_mem_nhdsWithin).exists
  -- it suffices to prove the bound up to `2 n η` for every `η > 0`
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set η := ε / (2 * n + 1) with hη
  have hη0 : 0 < η := by positivity
  have hηε : 2 * (n : ℝ) * η ≤ ε := by
    rw [hη, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  -- uniform continuity of `f` on the closed rectangle (the 2-D form used by `rc_rect_estimate`)
  obtain ⟨ρ, hρ0, hρ⟩ := Metric.uniformContinuousOn_iff.1
    ((acl_isCompact_closedRect a b c d).uniformContinuousOn_of_continuous (hc.mono hR)) η hη0
  -- the height of the thin rectangles
  set h := min (min (min (ρ / 2) (h₀ / 2)) ((d - t₀) / 2)) h₁ with hh
  have hh0 : 0 < h :=
    lt_min (lt_min (lt_min (half_pos hρ0) (half_pos hh₀)) (half_pos (sub_pos.2 ht₀.2))) hh₁0
  have hhρ : h < ρ := lt_of_le_of_lt ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
    (half_lt_self hρ0)
  have hhh₀ : h < h₀ := lt_of_le_of_lt ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
    (half_lt_self hh₀)
  have hhh₁ : h ≤ h₁ := min_le_right _ _
  have htd : t₀ + h ≤ d := by
    have := (min_le_left (min (min (ρ / 2) (h₀ / 2)) ((d - t₀) / 2)) h₁).trans
      (min_le_right (min (ρ / 2) (h₀ / 2)) ((d - t₀) / 2))
    linarith
  -- the per-rectangle estimates
  set u : ℕ → ℝ := fun i => max (dist (f (((E i).1 : ℂ) + (t₀ : ℂ) * I))
    (f (((E i).2 : ℂ) + (t₀ : ℂ) * I)) - 2 * η) 0 with hu
  set v : ℕ → ℝ := fun i =>
    (volume (f '' openRect (min (E i).1 (E i).2) (max (E i).1 (E i).2) t₀ (t₀ + h))).toReal with hv
  have hu0 : ∀ i, 0 ≤ u i := fun i => le_max_right _ _
  have hv0 : ∀ i, 0 ≤ v i := fun i => ENNReal.toReal_nonneg
  have hper : ∀ i ∈ Finset.range n, u i ^ 2 / dist (E i).1 (E i).2 ≤ 3 * K / h * v i := by
    intro i hir
    obtain ⟨h1, h2⟩ := hmem' i hir
    rcases eq_or_ne (E i).1 (E i).2 with heq | hne
    · have hu' : u i = 0 := by
        simp only [hu, heq, dist_self]
        exact max_eq_right (by linarith)
      rw [hu', heq, dist_self]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
      positivity
    · have hℓ : dist (E i).1 (E i).2 = max (E i).1 (E i).2 - min (E i).1 (E i).2 := by
        rw [Real.dist_eq, max_sub_min_eq_abs']
      have h2ℓ : 2 * h ≤ max (E i).1 (E i).2 - min (E i).1 (E i).2 := by
        rw [← hℓ]
        linarith [hh₁ i hir hne]
      have hest := rc_rect_estimate hD hK hc hi hring hR hh0 h2ℓ hhρ (le_min h1.1 h2.1)
        (max_le h1.2 h2.2) ht₀.1.le htd hρ
      have hm : dist (f (((min (E i).1 (E i).2 : ℝ) : ℂ) + (t₀ : ℂ) * I))
          (f (((max (E i).1 (E i).2 : ℝ) : ℂ) + (t₀ : ℂ) * I)) =
          dist (f (((E i).1 : ℂ) + (t₀ : ℂ) * I)) (f (((E i).2 : ℂ) + (t₀ : ℂ) * I)) := by
        rcases le_total (E i).1 (E i).2 with hle | hle
        · rw [min_eq_left hle, max_eq_right hle]
        · rw [min_eq_right hle, max_eq_left hle, dist_comm]
      rw [hm] at hest
      have hℓ0 : 0 < max (E i).1 (E i).2 - min (E i).1 (E i).2 := by linarith
      rw [hℓ, div_le_iff₀ hℓ0]
      calc u i ^ 2 = (u i ^ 2 * (h / ((max (E i).1 (E i).2 - min (E i).1 (E i).2) * (3 * K)))) *
            ((max (E i).1 (E i).2 - min (E i).1 (E i).2) * (3 * K) / h) := by
            field_simp
        _ ≤ v i * ((max (E i).1 (E i).2 - min (E i).1 (E i).2) * (3 * K) / h) :=
            mul_le_mul_of_nonneg_right hest (by positivity)
        _ = 3 * K / h * v i * (max (E i).1 (E i).2 - min (E i).1 (E i).2) := by ring
  -- summing up
  have hsumv : ∑ i ∈ Finset.range n, v i ≤ g (t₀ + h) - g t₀ :=
    acl_sum_volume_le hc hinj hab.le hR hh0 ht₀.1.le htd hE
  have hsum1 : ∑ i ∈ Finset.range n, u i ^ 2 / dist (E i).1 (E i).2 ≤ L := by
    calc ∑ i ∈ Finset.range n, u i ^ 2 / dist (E i).1 (E i).2
        ≤ ∑ i ∈ Finset.range n, 3 * K / h * v i := Finset.sum_le_sum hper
      _ = 3 * K / h * ∑ i ∈ Finset.range n, v i := by rw [Finset.mul_sum]
      _ ≤ 3 * K / h * ((|deriv g t₀| + 1) * h) :=
          mul_le_mul_of_nonneg_left (hsumv.trans (hgbound h hh0 hhh₀)) (by positivity)
      _ = L := by
          rw [hL, div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_right₀ _ hh0.ne']
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

/-- The horizontal half: `f` is absolutely continuous on almost every horizontal line of `R̄ ⊆ D` (the body of
`acl_horizontal`, S09:764–785, with `L := 3K(|g′(t₀)| + 1)` and `rc_sum_dist_le`). -/
theorem rc_horizontal {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hD : IsOpen D) (hK : 0 < K)
    (hc : ContinuousOn f D) (hi : InjOn f D) (hring : rc_RingBound f D K) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hR : closedRect a b c d ⊆ D) :
    ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)),
      AbsolutelyContinuousOnInterval (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) a b := by
  have _hcd := hcd
  have hmono := acl_monotone_aclArea hc hR
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hmono.ae_differentiableAt] with t₀ hg ht₀
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  set L := 3 * K * (|deriv (aclArea f a b c d) t₀| + 1) with hL
  have hL0 : 0 < L := by positivity
  refine ⟨ε ^ 2 / (2 * L), by positivity, ?_⟩
  rintro ⟨n, E⟩ hE hlen
  have h := rc_sum_dist_le hD hK hc hi hring hab hR ht₀ hg hE
  refine lt_of_le_of_lt h ?_
  rw [Real.sqrt_lt' hε]
  calc L * ∑ i ∈ Finset.range n, dist (E i).1 (E i).2 < L * (ε ^ 2 / (2 * L)) :=
        mul_lt_mul_of_pos_left hlen hL0
    _ = ε ^ 2 / 2 := by field_simp
    _ < ε ^ 2 := by linarith [pow_pos hε 2]

/-- The ring condition is invariant under precomposition with the rotation `z ↦ i z`: for `B` doubly connected
with `B̄ ⊆ (i ·)⁻¹ D`, `i B` is doubly connected with `M(i B) = M(B)` (Theorem 2.2) and `closure (i B) ⊆ D`. -/
theorem rc_ringBound_comp_mul_I {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hring : rc_RingBound f D K) :
    rc_RingBound (f ∘ fun z => I * z) ((fun z => I * z) ⁻¹' D) K := by
  intro B hB hBD
  have hBb : Bornology.IsBounded B :=
    isBounded_of_extInf_notMem_closure_toExt fun h => extInf_notMem_toExt _ (hBD h)
  have hr : (fun z : ℂ => I * z) = fun w => 0 + I * w := funext fun w => (zero_add _).symm
  have hrc : Continuous fun z : ℂ => I * z := by fun_prop
  have hB' : IsDoublyConnected ((fun z : ℂ => I * z) '' B) := by
    rw [hr]
    exact rc_isDoublyConnected_affine hB hBb I_ne_zero 0
  have hM : dcModulus ((fun z : ℂ => I * z) '' B) = dcModulus B := by
    rw [hr]
    exact rc_dcModulus_affine hB I_ne_zero 0
  have hcl : closure B ⊆ (fun z : ℂ => I * z) ⁻¹' D := by
    intro z hz
    have hz' : (z : ExtPlane) ∈ toExt ((fun z : ℂ => I * z) ⁻¹' D) := by
      apply hBD
      rw [closure_toExt_eq_toExt_closure_of_isBounded hBb]
      exact mem_image_of_mem _ hz
    exact coe_mem_toExt_iff.1 hz'
  have hbd' : Bornology.IsBounded ((fun z : ℂ => I * z) '' B) :=
    (hBb.isCompact_closure.image hrc).isBounded.subset (image_mono subset_closure)
  have hBD' : closure (toExt ((fun z : ℂ => I * z) '' B)) ⊆ toExt D := by
    rw [closure_toExt_eq_toExt_closure_of_isBounded hbd']
    refine image_mono ?_
    have h1 : closure ((fun z : ℂ => I * z) '' B) ⊆ (fun z : ℂ => I * z) '' closure B :=
      closure_minimal (image_mono subset_closure) (hBb.isCompact_closure.image hrc).isClosed
    intro w hw
    obtain ⟨z, hz, rfl⟩ := h1 hw
    exact hcl hz
  have h := hring _ hB' hBD'
  rw [hM, ← image_comp] at h
  exact h

/-- The vertical half: the horizontal half for `f ∘ (i ·)` on `(i ·)⁻¹ D` (the body of `acl_vertical`,
S09:788–839, with `thm7_1_comp` replaced by the continuity, injectivity and ring condition of `f ∘ (i ·)`). -/
theorem rc_vertical {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hD : IsOpen D) (hK : 0 < K)
    (hc : ContinuousOn f D) (hi : InjOn f D) (hring : rc_RingBound f D K) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hR : closedRect a b c d ⊆ D) :
    ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)),
      AbsolutelyContinuousOnInterval (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) c d := by
  set r : ℂ → ℂ := fun z => I * z with hr
  have hrc : Continuous r := by
    rw [hr]
    fun_prop
  have hD' : IsOpen (r ⁻¹' D) := hD.preimage hrc
  have hc' : ContinuousOn (f ∘ r) (r ⁻¹' D) := hc.comp hrc.continuousOn fun z hz => hz
  have hi' : InjOn (f ∘ r) (r ⁻¹' D) :=
    hi.comp (fun z _ w _ h => mul_left_cancel₀ I_ne_zero h) fun z hz => hz
  have hring' : rc_RingBound (f ∘ r) (r ⁻¹' D) K := rc_ringBound_comp_mul_I hring
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
  have h := rc_horizontal hD' hK hc' hi' hring' hcd (by linarith : -b < -a) hR'
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

/-- **L1b**: a homeomorphism satisfying the ring condition is A.C.L. (the assembly of `thm9_1_isACL`, S09:1081). -/
theorem rc_isACL {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hD : IsOpen D) (hK : 0 < K) (hc : ContinuousOn f D)
    (hi : InjOn f D) (hring : rc_RingBound f D K) : IsACL f D := by
  exact ⟨hc, fun a b c d hab hcd hR =>
    ⟨rc_vertical hD hK hc hi hring hab hcd hR, rc_horizontal hD hK hc hi hring hab hcd hR⟩⟩

/-! ### Stage B (L3b): orientation, `|∂_{z̄} f| ≤ |∂_z f|` at points of differentiability

The local winding of a sense-preserving homeomorphism is `+1` (the R1 argument of Theorem 8.2, which uses the
`IsKQC` hypothesis only through the image quadrilateral); a point with `|∂_z f| < |∂_{z̄} f|` would give winding
`-1`.  This is the only use of `hsense`. -/

/-- **R1 for sense-preserving homeomorphisms**: local winding `+1` at every point of `U`.  A verbatim copy of
`qcl_r_hloc_of_isKQC` (S08:4075–4395), whose `IsKQC` hypothesis enters only as the openness of `U`, the continuity
and injectivity of `h`, and the existence of the image quadrilateral (`hh.2.2.2 S hSU`, whose modulus bound is
discarded); here these are `hU`, `hc`, `hi` and `hsense`. -/
theorem rc_hloc_of_sensePreserving {h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hc : ContinuousOn h U)
    (hi : InjOn h U) (hsense : IsSensePreserving h U) {p : ℂ} (hp : p ∈ U) :
    ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = h (p + ρ * Complex.exp (2 * π * I * t)) - h p) →
      L 1 - L 0 = 2 * π * I := by
  obtain ⟨S, hpS, hSU⟩ := exists_topQuad_mem_closure_subset hU hp
  obtain ⟨S', hS'⟩ := hsense S hSU
  obtain ⟨hJ, hv, φ, Φ, x, hφ, hΦ, hx, hΦv⟩ := S.isTopQuad
  obtain ⟨hJ', hv', φ', Φ', x', hφ', hΦ', hx', hΦ'v⟩ := S'.isTopQuad
  have hSdomopen : IsOpen S.dom := hJ.1
  have hSdomU : S.dom ⊆ U := fun z hz => by
    have hzt := hSU (subset_closure (mem_image_of_mem _ hz))
    exact coe_mem_toExt_iff.mp hzt
  have hhcont : ContinuousOn h U := hc
  have hhinj : InjOn h U := hi
  have hfo : IsOpen (h '' S.dom) :=
    isOpen_image_of_continuousOn_injOn_of_subset hU hhcont hhinj hSdomU hSdomopen
  obtain ⟨-, hext, -⟩ := image_isJordanDomain_of_open hU hhcont hhinj hSU hfo
  have hext' : IsHomeoExtension h S.dom S'.dom (OnePoint.map h) := by
    rw [hS'.1]; exact hext
  set ψ : ℂ → ℂ := Function.invFunOn φ S.dom with hψdef
  set Ψ : ExtPlane → ExtPlane := Function.invFunOn Φ (closure (toExt S.dom)) with hΨdef
  have hφsymm : IsConformalOnto ψ upperHalf S.dom := hφ.symm hSdomopen
  have hφinvimg : ψ '' upperHalf = S.dom := hφsymm.2.2
  have hφinvext : IsHomeoExtension ψ upperHalf S.dom Ψ := isHomeoExtension_invFunOn hφ hΦ
  have hφinvmaps : MapsTo ψ upperHalf S.dom := by
    intro w hw; rw [← hφinvimg]; exact mem_image_of_mem _ hw
  have hstep1 : IsHomeoExtension (h ∘ ψ) upperHalf S'.dom (OnePoint.map h ∘ Ψ) :=
    IsHomeoExtension.comp hext' hφinvext hφinvmaps
  have hstep1img : (h ∘ ψ) '' upperHalf = S'.dom := by
    rw [Set.image_comp, hφinvimg, ← hS'.1]
  have hstep1maps : MapsTo (h ∘ ψ) upperHalf S'.dom := by
    intro w hw; rw [← hstep1img]; exact mem_image_of_mem _ hw
  have hstep2 : IsHomeoExtension (φ' ∘ (h ∘ ψ)) upperHalf upperHalf (Φ' ∘ (OnePoint.map h ∘ Ψ)) :=
    IsHomeoExtension.comp hΦ' hstep1 hstep1maps
  set κ : ℂ → ℂ := φ' ∘ (h ∘ ψ) with hκdef
  set Kext : ExtPlane → ExtPlane := Φ' ∘ (OnePoint.map h ∘ Ψ) with hKextdef
  have hKextext : IsHomeoExtension κ upperHalf upperHalf Kext := hstep2
  have hκimg : κ '' upperHalf = upperHalf := by
    rw [hκdef, Set.image_comp, hstep1img]
    exact hφ'.2.2
  have hΦinvcancel : ∀ i, Ψ (((x i : ℝ) : ℂ) : ExtPlane) = S.vert i := by
    intro i
    have hmem : S.vert i ∈ closure (toExt S.dom) := frontier_subset_closure (hv i)
    have h1 := hΦ.2.2.1.leftInvOn_invFunOn hmem
    rwa [hΦv i] at h1
  have hKextv : ∀ i, Kext (((x i : ℝ) : ℂ) : ExtPlane) = (((x' i : ℝ) : ℂ) : ExtPlane) := by
    intro i
    show Φ' (OnePoint.map h (Ψ (((x i : ℝ) : ℂ) : ExtPlane))) = _
    rw [hΦinvcancel i, ← hS'.2 i]
    exact hΦ'v i
  have hz₀mem : φ p ∈ upperHalf := hφ.2.2 ▸ mem_image_of_mem φ hpS
  have hlocκ : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = κ (φ p + ρ * Complex.exp (2 * π * I * t)) - κ (φ p)) →
      L 1 - L 0 = 2 * π * I := by
    by_cases hinf : Kext extInf = extInf
    · have hKextfr : Kext '' frontier (toExt upperHalf) = frontier (toExt upperHalf) :=
        IsHomeoExtension.image_frontier scExt_isOpen_upperHalf scExt_isOpen_upperHalf hκimg
          hKextext
      have hKextc : ContinuousOn Kext (frontier (toExt upperHalf)) :=
        hKextext.2.1.mono frontier_subset_closure
      have hKexti : InjOn Kext (frontier (toExt upperHalf)) :=
        hKextext.2.2.1.mono frontier_subset_closure
      obtain ⟨f, hfcont, hfinj, hfmono, hf⟩ :=
        qcl_w_strictMono_of_cyclic hKextc hKexti hKextfr hinf hx hx' hKextv
      exact qcl_w_hloc_of_strictMono_boundary hKextext hκimg hinf hz₀mem f hfcont hfinj hf hfmono
    · have hKextfr : Kext '' frontier (toExt upperHalf) = frontier (toExt upperHalf) :=
        IsHomeoExtension.image_frontier scExt_isOpen_upperHalf scExt_isOpen_upperHalf hκimg
          hKextext
      have hinfmem : extInf ∈ frontier (toExt upperHalf) := by
        rw [scExt_frontier_toExt_upperHalf]; exact Or.inr rfl
      have hKextinfmem : Kext extInf ∈ frontier (toExt upperHalf) :=
        hKextfr ▸ mem_image_of_mem Kext hinfmem
      rw [scExt_frontier_toExt_upperHalf] at hKextinfmem
      obtain ⟨r, hr⟩ : ∃ r : ℝ, Kext extInf = (((r : ℝ) : ℂ) : ExtPlane) := by
        rcases hKextinfmem with hh1 | hh1
        · obtain ⟨z, hz, hzeq⟩ := hh1
          exact ⟨z.re, by rw [← hzeq]; congr 1; exact Complex.ext_iff.2 ⟨rfl, hz⟩⟩
        · exact absurd hh1 hinf
      have hdetM : (0 : ℝ) * (-r) - (-1) * (1 : ℝ) = 1 := by ring
      have hdetMpos : (0 : ℝ) < (0 : ℝ) * (-r) - (-1) * (1 : ℝ) := by rw [hdetM]; norm_num
      have hdetMC : ((0 : ℝ) : ℂ) * ((-r : ℝ) : ℂ) - ((-1 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) ≠ 0 := by
        have h0 : ((0 : ℝ) * (-r) - (-1) * (1 : ℝ) : ℝ) ≠ 0 := hdetMpos.ne'
        exact_mod_cast h0
      set M : ℂ → ℂ := mobiusFn ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((-r : ℝ) : ℂ)
        with hMdef
      set E : ExtPlane ≃ₜ ExtPlane :=
        mobiusHomeomorph ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((-r : ℝ) : ℂ) hdetMC with hEdef
      have hEapp : ∀ w : ExtPlane, E w = mobiusExt ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ)
          ((-r : ℝ) : ℂ) w := fun w => rfl
      have hMconf : IsConformalOnto M upperHalf upperHalf :=
        isConformalOnto_mobius_upperHalf hdetMpos
      have hEmaps : ∀ w ∈ upperHalf, E (w : ExtPlane) = ((M w : ℂ) : ExtPlane) := fun w hw => by
        rw [hEapp]
        exact mobiusExt_coe (mobiusFn_den_ne_zero_real hdetMpos.ne' hw)
      have hEimg : E '' toExt upperHalf = toExt upperHalf := mobiusExt_image_toExt_upperHalf hdetMpos
      have hκmaps : MapsTo κ upperHalf upperHalf := by
        intro w hw; rw [← hκimg]; exact mem_image_of_mem _ hw
      have hMKextext : IsHomeoExtension (M ∘ κ) upperHalf upperHalf (E ∘ Kext) :=
        IsHomeoExtension.comp_homeomorph hKextext hκmaps E hEmaps hEimg
      have hMKexts : (M ∘ κ) '' upperHalf = upperHalf := by
        rw [image_comp, hκimg, hMconf.2.2]
      have hEKextinf : (E ∘ Kext) extInf = extInf := by
        show E (Kext extInf) = extInf
        rw [hr, hEapp]
        have hden0 : (1 : ℂ) * ((r : ℝ) : ℂ) + ((-r : ℝ) : ℂ) = 0 := by push_cast; ring
        exact mobiusExt_coe_of_eq_zero hden0
      have hxi_mem : ∀ i, (((x i : ℝ) : ℂ) : ExtPlane) ∈ closure (toExt upperHalf) := by
        intro i
        apply frontier_subset_closure
        rw [scExt_frontier_toExt_upperHalf]
        exact Or.inl ⟨(x i : ℝ), rfl, rfl⟩
      have hinfclos : extInf ∈ closure (toExt upperHalf) := frontier_subset_closure hinfmem
      have hx'ner : ∀ i, x' i ≠ r := by
        intro i heq
        have h1 : Kext (((x i : ℝ) : ℂ) : ExtPlane) = Kext extInf := by rw [hKextv i, heq, hr]
        have h2 := hKextext.2.2.1 (hxi_mem i) hinfclos h1
        exact OnePoint.coe_ne_infty _ h2
      set y' : Fin 4 → ℝ := fun i => -1 / (x' i - r) with hy'def
      have hMx'eq : ∀ i, mobiusExt ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((-r : ℝ) : ℂ)
          (((x' i : ℝ) : ℂ) : ExtPlane) = (((y' i : ℝ) : ℂ) : ExtPlane) := by
        intro i
        have hden2 : ((1 : ℝ) : ℂ) * ((x' i : ℝ) : ℂ) + ((-r : ℝ) : ℂ) ≠ 0 := by
          have hne : (x' i - r : ℝ) ≠ 0 := sub_ne_zero.2 (hx'ner i)
          intro hh
          apply hne
          have h' : ((x' i - r : ℝ) : ℂ) = 0 := by push_cast at hh ⊢; linear_combination hh
          exact_mod_cast h'
        rw [mobiusExt_coe hden2]
        congr 1
        show mobiusFn ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((-r : ℝ) : ℂ) ((x' i : ℝ) : ℂ) =
          (((y' i : ℝ)) : ℂ)
        rw [mobiusFn, hy'def]
        simp only
        push_cast
        congr 1 <;> ring
      have hEKextv : ∀ i, (E ∘ Kext) (((x i : ℝ) : ℂ) : ExtPlane) = (((y' i : ℝ) : ℂ) : ExtPlane) := by
        intro i
        show E (Kext (((x i : ℝ) : ℂ) : ExtPlane)) = _
        rw [hKextv i, hEapp]
        exact hMx'eq i
      have hy'cyc : CyclicStrictMono y' :=
        automorphism_upperHalf_preserves_cyclicOrder hdetMpos x' hx' y' hMx'eq
      have hEKextfr : (E ∘ Kext) '' frontier (toExt upperHalf) = frontier (toExt upperHalf) :=
        IsHomeoExtension.image_frontier scExt_isOpen_upperHalf scExt_isOpen_upperHalf hMKexts
          hMKextext
      have hEKextc : ContinuousOn (E ∘ Kext) (frontier (toExt upperHalf)) :=
        hMKextext.2.1.mono frontier_subset_closure
      have hEKexti : InjOn (E ∘ Kext) (frontier (toExt upperHalf)) :=
        hMKextext.2.2.1.mono frontier_subset_closure
      obtain ⟨f, hfcont, hfinj, hfmono, hf⟩ :=
        qcl_w_strictMono_of_cyclic hEKextc hEKexti hEKextfr hEKextinf hx hy'cyc hEKextv
      obtain ⟨ρ₁, hρ₁pos, hlocMκ⟩ :=
        qcl_w_hloc_of_strictMono_boundary hMKextext hMKexts hEKextinf hz₀mem f hfcont hfinj hf
          hfmono
      -- Transport `hlocMκ` (local winding of `M ∘ κ`) back to `κ` via the explicit inverse
      -- Möbius map `Minv := mobiusFn r (-1) 1 0`, using `qcl_r_transport_conformal`.
      set Minv : ℂ → ℂ := mobiusFn ((r : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ)
        with hMinvdef
      have hκz0ner : κ (φ p) ≠ ((r : ℝ) : ℂ) := by
        intro heq
        have him : (κ (φ p)).im = 0 := by rw [heq]; simp
        have hpos : 0 < (κ (φ p)).im := hκmaps hz₀mem
        linarith
      have hMw : ∀ w : ℂ, w ≠ ((r : ℝ) : ℂ) → M w = -1 / (w - ((r : ℝ) : ℂ)) := by
        intro w hw
        rw [hMdef, mobiusFn]
        congr 1 <;> push_cast <;> ring
      have hMwne0 : ∀ w : ℂ, w ≠ ((r : ℝ) : ℂ) → M w ≠ 0 := by
        intro w hw
        rw [hMw w hw]
        exact div_ne_zero (by norm_num) (sub_ne_zero.2 hw)
      have hMinvMcancel : ∀ w : ℂ, w ≠ ((r : ℝ) : ℂ) → Minv (M w) = w := by
        intro w hw
        have hwrne : w - ((r : ℝ) : ℂ) ≠ 0 := sub_ne_zero.2 hw
        rw [hMw w hw, hMinvdef, mobiusFn]
        field_simp
        push_cast
        ring
      have hMκcont : ContinuousOn (M ∘ κ) upperHalf := by
        rw [OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff]
        have h1 : ContinuousOn (fun z : ℂ => (E ∘ Kext) (z : ExtPlane)) upperHalf :=
          hMKextext.2.1.comp OnePoint.continuous_coe.continuousOn
            (fun z hz => subset_closure (mem_image_of_mem _ hz))
        exact h1.congr fun z hz => (hMKextext.1 z hz).symm
      have hMκinj : InjOn (M ∘ κ) upperHalf := by
        intro a ha b hb hab
        have ea : (E ∘ Kext) (a : ExtPlane) = ((M ∘ κ) a : ℂ) := hMKextext.1 a ha
        have eb : (E ∘ Kext) (b : ExtPlane) = ((M ∘ κ) b : ℂ) := hMKextext.1 b hb
        have h1 : (E ∘ Kext) (a : ExtPlane) = (E ∘ Kext) (b : ExtPlane) := by rw [ea, eb, hab]
        have h2 := hMKextext.2.2.1 (subset_closure (mem_image_of_mem _ ha))
          (subset_closure (mem_image_of_mem _ hb)) h1
        exact OnePoint.coe_injective h2
      obtain ⟨ε, hεpos, hεball⟩ := Metric.isOpen_iff.1 scExt_isOpen_upperHalf (φ p) hz₀mem
      have hMinvopen : IsOpen {w : ℂ | w ≠ (0 : ℂ)} := isOpen_ne
      have hMinvdiffOn : DifferentiableOn ℂ Minv {w : ℂ | w ≠ (0 : ℂ)} := by
        intro w hw
        have hw' : (1 : ℂ) * w + ((0 : ℝ) : ℂ) ≠ 0 := by simpa using hw
        exact (hasDerivAt_mobiusFn (a := ((r : ℝ) : ℂ)) (b := ((-1 : ℝ) : ℂ))
          hw').differentiableAt.differentiableWithinAt
      have hMκz0memU : (M ∘ κ) (φ p) ∈ {w : ℂ | w ≠ (0 : ℂ)} :=
        hMwne0 (κ (φ p)) hκz0ner
      have hMderivneat : deriv Minv ((M ∘ κ) (φ p)) ≠ 0 := by
        show deriv Minv (M (κ (φ p))) ≠ 0
        have hw' : ((1:ℝ) : ℂ) * (M (κ (φ p))) + ((0 : ℝ) : ℂ) ≠ 0 := by
          have := hMwne0 (κ (φ p)) hκz0ner
          simpa using this
        have hdetMinvC : ((r:ℝ):ℂ) * ((0:ℝ):ℂ) - ((-1:ℝ):ℂ) * ((1:ℝ):ℂ) ≠ 0 := by
          have : ((r:ℝ)*(0:ℝ) - (-1)*(1:ℝ) : ℝ) ≠ 0 := by norm_num
          exact_mod_cast this
        rw [hMinvdef, (hasDerivAt_mobiusFn (a := ((r:ℝ):ℂ)) (b := ((-1:ℝ):ℂ))
          (c := ((1:ℝ):ℂ)) (d := ((0:ℝ):ℂ)) hw').deriv]
        exact div_ne_zero hdetMinvC (pow_ne_zero 2 hw')
      have hlocMinvMκ := qcl_r_transport_conformal hεpos (hMκcont.mono hεball)
        (fun z hz hzne heqv => hzne (hMκinj (hεball hz) hz₀mem heqv)) ⟨ρ₁, hρ₁pos, hlocMκ⟩
        hMinvopen hMκz0memU hMinvdiffOn hMderivneat
      obtain ⟨ρ₁', hρ₁'pos, hlocMinvMκ'⟩ := hlocMinvMκ
      have henorm : ∀ t : ℝ, ‖Complex.exp (2 * π * I * (t : ℂ))‖ = 1 := by
        intro t
        rw [Complex.norm_exp]
        have h0 : (2 * π * I * (t : ℂ)).re = 0 := by simp
        rw [h0, Real.exp_zero]
      refine ⟨min ρ₁' ε, lt_min hρ₁'pos hεpos, ?_⟩
      intro ρ hρpos hρlt L hLcont hLe
      have hρρ1' : ρ < ρ₁' := hρlt.trans_le (min_le_left _ _)
      have hρε : ρ < ε := hρlt.trans_le (min_le_right _ _)
      apply hlocMinvMκ' ρ hρpos hρρ1' L hLcont
      intro t ht
      have hcircUH : φ p + ρ * Complex.exp (2 * π * I * (t : ℂ)) ∈ upperHalf := by
        apply hεball
        rw [Metric.mem_ball, dist_eq_norm]
        have heq : φ p + (ρ : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) - φ p =
            (ρ : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) := by ring
        rw [heq, norm_mul, henorm t, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hρpos]
        exact hρε
      have hκcircNer : κ (φ p + ρ * Complex.exp (2 * π * I * (t : ℂ))) ≠ ((r : ℝ) : ℂ) := by
        intro heq
        have him : (κ (φ p + ρ * Complex.exp (2 * π * I * (t : ℂ)))).im = 0 := by
          rw [heq]; simp
        have hpos : 0 < (κ (φ p + ρ * Complex.exp (2 * π * I * (t : ℂ)))).im :=
          hκmaps hcircUH
        linarith
      rw [hLe t ht]
      simp only [Function.comp_apply]
      rw [hMinvMcancel _ hκcircNer, hMinvMcancel _ hκz0ner]
  -- Transport `hlocκ` (local winding of `κ` at `φ p`) back to `h` (local winding at `p`):
  -- post-compose with `ψ' := invFunOn φ' S'.dom` to get `K := ψ' ∘ κ`'s winding at `φ p`,
  -- then pre-compose with `φ` (via `qcl_r_transport_precompose`) to get `K ∘ φ`'s winding at
  -- `p`; finally `K ∘ φ = h` on `S.dom` (both cancellations of the canonical maps).
  have henorm : ∀ t : ℝ, ‖Complex.exp (2 * π * I * (t : ℂ))‖ = 1 := by
    intro t
    rw [Complex.norm_exp]
    have h0 : (2 * π * I * (t : ℂ)).re = 0 := by simp
    rw [h0, Real.exp_zero]
  have hκmaps : MapsTo κ upperHalf upperHalf := by
    intro w hw; rw [← hκimg]; exact mem_image_of_mem _ hw
  set ψ' : ℂ → ℂ := Function.invFunOn φ' S'.dom with hψ'def
  have hφ'symm : IsConformalOnto ψ' upperHalf S'.dom := hφ'.symm hJ'.1
  have hκcont : ContinuousOn κ upperHalf := by
    rw [OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff]
    exact (hKextext.2.1.comp OnePoint.continuous_coe.continuousOn
      (fun z hz => subset_closure (mem_image_of_mem _ hz))).congr
      (fun z hz => (hKextext.1 z hz).symm)
  have hκinj : InjOn κ upperHalf := by
    intro a ha b hb hab
    have h1 : Kext (a : ExtPlane) = Kext (b : ExtPlane) := by
      rw [hKextext.1 a ha, hKextext.1 b hb, hab]
    have h2 := hKextext.2.2.1 (subset_closure (mem_image_of_mem _ ha))
      (subset_closure (mem_image_of_mem _ hb)) h1
    exact OnePoint.coe_injective h2
  have hκφpmem : κ (φ p) ∈ upperHalf := hκmaps hz₀mem
  have hψ'deriv : deriv ψ' (κ (φ p)) ≠ 0 :=
    deriv_ne_zero_of_injOn scExt_isOpen_upperHalf hφ'symm.1 hφ'symm.2.1 hκφpmem
  obtain ⟨ε₂, hε₂pos, hε₂ball⟩ := Metric.isOpen_iff.1 scExt_isOpen_upperHalf (φ p) hz₀mem
  have hlocK := qcl_r_transport_conformal (k := κ) (A := ψ') (z₀ := φ p) (r₀ := ε₂) hε₂pos
    (hκcont.mono hε₂ball) (fun z hz hzne heq => hzne (hκinj (hε₂ball hz) hz₀mem heq)) hlocκ
    scExt_isOpen_upperHalf hκφpmem hφ'symm.1 hψ'deriv
  set K : ℂ → ℂ := ψ' ∘ κ with hKdef
  have hψφeq : ∀ w ∈ S.dom, ψ (φ w) = w := hφ.2.1.leftInvOn_invFunOn
  have hκφeq : ∀ w ∈ S.dom, κ (φ w) = φ' (h w) := by
    intro w hw
    show φ' (h (ψ (φ w))) = φ' (h w)
    rw [hψφeq w hw]
  have hhw'dom : ∀ w ∈ S.dom, h w ∈ S'.dom := by
    intro w hw
    rw [hS'.1]; exact mem_image_of_mem h hw
  have hψ'φ'eq : ∀ w ∈ S'.dom, ψ' (φ' w) = w := hφ'.2.1.leftInvOn_invFunOn
  have hKeq : ∀ w ∈ S.dom, K (φ w) = h w := by
    intro w hw
    show ψ' (κ (φ w)) = h w
    rw [hκφeq w hw]
    exact hψ'φ'eq (h w) (hhw'dom w hw)
  have hKφp : K (φ p) = h p := hKeq p hpS
  have hKcont : ContinuousOn K upperHalf := hφ'symm.1.continuousOn.comp hκcont hκmaps
  have hKinj : InjOn K upperHalf := by
    intro a ha b hb hab
    have h2 := hφ'symm.2.1 (hκmaps ha) (hκmaps hb) hab
    exact hκinj ha hb h2
  have hderivφp : deriv φ p ≠ 0 := deriv_ne_zero_of_injOn hSdomopen hφ.1 hφ.2.1 hpS
  have hloc_h := qcl_r_transport_precompose (k := K) (f := φ) (w₀ := p) (z₀ := φ p) rfl
    hSdomopen hpS hφ.1 hφ.2.1 hderivφp hε₂pos (hKcont.mono hε₂ball) (hKinj.mono hε₂ball) hlocK
  obtain ⟨ρ_h, hρ_hpos, hloc_h'⟩ := hloc_h
  obtain ⟨ε₃, hε₃pos, hε₃ball⟩ := Metric.isOpen_iff.1 hSdomopen p hpS
  refine ⟨min ρ_h ε₃, lt_min hρ_hpos hε₃pos, ?_⟩
  intro ρ hρpos hρlt L hLcont hLe
  have hρh : ρ < ρ_h := hρlt.trans_le (min_le_left _ _)
  have hρε3 : ρ < ε₃ := hρlt.trans_le (min_le_right _ _)
  apply hloc_h' ρ hρpos hρh L hLcont
  intro t ht
  rw [hLe t ht]
  have hcircS : p + ρ * Complex.exp (2 * π * I * (t : ℂ)) ∈ S.dom := by
    apply hε₃ball
    rw [Metric.mem_ball, dist_eq_norm]
    have heqn : p + (ρ : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) - p =
        (ρ : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) := by ring
    rw [heqn, norm_mul, henorm t, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
    exact hρε3
  rw [hKeq _ hcircS, hKφp]

/-- **L3b (orientation).** At a point of real differentiability of a sense-preserving homeomorphism,
`|∂_{z̄} f| ≤ |∂_z f|` (i.e. `det f′(z₀) = |∂_z f|² - |∂_{z̄} f|² ≥ 0`).

Proof: write `a = dz f z₀`, `b = dzbar f z₀`, `f(z₀ + v) = f z₀ + a v + b v̄ + o(|v|)` (`fderiv_eq_dz_dzbar`,
S06:34).  If `‖a‖ < ‖b‖`, put `ε = (‖b‖ - ‖a‖)/2`; for small `ρ` the loop `γ(t) = f(z₀ + ρ e^{2πit}) - f z₀`
satisfies `‖γ(t) - ρ b e^{-2πit}‖ ≤ ρ‖a‖ + ερ < ρ‖b‖`, so its lift change equals that of `ρ b e^{-2πit}`, i.e.
`-2πi`, while `rc_hloc_of_sensePreserving` gives `+2πi`.  (`hsense` is essential: `conj` satisfies every other
hypothesis and has `‖a‖ = 0 < 1 = ‖b‖`.)
Uses: `rc_hloc_of_sensePreserving hD hc hi hsense hz₀`; the little-o bound from
`hasFDerivAt_iff_isLittleO_nhds_zero` + `fderiv_eq_dz_dzbar` with `Metric.eventually_nhds_iff` (pattern `ar_upper`,
S09:6965); a lift `L` of `γ` by `exists_continuousOn_log_lift` (Winding:43; `γ t ≠ 0` by injectivity); the explicit
lift `M t = Complex.log (ρ b) - 2πi t` of `ρ b e^{-2πit}` (or the T2 lift, S09:6255–6336);
`lift_change_eq_of_norm_sub_lt` (Winding:155); `2πi ≠ -2πi`. -/
theorem rc_norm_dzbar_le {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hc : ContinuousOn f D) (hi : InjOn f D)
    (hsense : IsSensePreserving f D) {z₀ : ℂ} (hz₀ : z₀ ∈ D) (hdiff : DifferentiableAt ℝ f z₀) :
    ‖dzbar f z₀‖ ≤ ‖dz f z₀‖ := by
  by_contra hcon
  have hlt : ‖dz f z₀‖ < ‖dzbar f z₀‖ := not_le.1 hcon
  have hb0 : dzbar f z₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlt
    exact absurd hlt (not_lt.2 (norm_nonneg _))
  -- the expansion `f(z₀ + v) = f z₀ + a v + b v̄ + r(v)`, `‖r(v)‖ ≤ ε ‖v‖`, `ε = (‖b‖ - ‖a‖)/2`
  have hε0 : 0 < (‖dzbar f z₀‖ - ‖dz f z₀‖) / 2 := by linarith
  obtain ⟨κ, hκ, hrem⟩ : ∃ κ > 0, ∀ v : ℂ, ‖v‖ < κ →
      ‖f (z₀ + v) - f z₀ - (dz f z₀ * v + dzbar f z₀ * (starRingEnd ℂ) v)‖ ≤
        (‖dzbar f z₀‖ - ‖dz f z₀‖) / 2 * ‖v‖ := by
    have ho := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hdiff.hasFDerivAt).def hε0
    obtain ⟨κ, hκ, hκv⟩ := Metric.eventually_nhds_iff.1 ho
    refine ⟨κ, hκ, fun v hv => ?_⟩
    have h1 := @hκv v (by rw [dist_zero_right]; exact hv)
    rwa [fderiv_eq_dz_dzbar hdiff] at h1
  -- the local winding `+1` (R1, the only use of `hsense`)
  obtain ⟨ρ₁, hρ₁, hloc⟩ := rc_hloc_of_sensePreserving hD hc hi hsense hz₀
  obtain ⟨δ, hδ, hδD⟩ := Metric.isOpen_iff.1 hD z₀ hz₀
  have hm : 0 < min (min ρ₁ κ) δ := lt_min (lt_min hρ₁ hκ) hδ
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = min (min ρ₁ κ) δ / 2 := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by
    rw [hρ]
    positivity
  have hρm : ρ < min (min ρ₁ κ) δ := by
    rw [hρ]
    linarith
  have hρρ₁ : ρ < ρ₁ := hρm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hρκ : ρ < κ := hρm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hρδ : ρ < δ := hρm.trans_le (min_le_right _ _)
  have hen : ∀ t : ℝ, ‖Complex.exp (2 * π * I * t)‖ = 1 := by
    intro t
    rw [Complex.norm_exp]
    simp
  have hen' : ∀ t : ℝ, ‖Complex.exp (-(2 * π * I * t))‖ = 1 := by
    intro t
    rw [Complex.norm_exp]
    simp
  have hvn : ∀ t : ℝ, ‖(ρ : ℂ) * Complex.exp (2 * π * I * t)‖ = ρ := by
    intro t
    rw [norm_mul, hen, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  have hmem : ∀ t : ℝ, z₀ + ρ * Complex.exp (2 * π * I * t) ∈ D := by
    intro t
    apply hδD
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hvn]
    exact hρδ
  -- a continuous logarithm `L` of `γ(t) = f(z₀ + ρ e^{2πit}) - f z₀`; its change is `2πi`
  have hγc : ContinuousOn (fun t : ℝ => f (z₀ + ρ * Complex.exp (2 * π * I * t))) (Icc 0 1) :=
    hc.comp (Continuous.continuousOn (by fun_prop)) fun t _ => hmem t
  have hγne : ∀ t ∈ Icc (0 : ℝ) 1, f (z₀ + ρ * Complex.exp (2 * π * I * t)) ≠ f z₀ := by
    intro t _ h
    have h1 := hi (hmem t) hz₀ h
    have h2 : (ρ : ℂ) * Complex.exp (2 * π * I * t) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact hρ0.ne' (Complex.ofReal_eq_zero.1 h3)
    · exact Complex.exp_ne_zero _ h3
  obtain ⟨Lf, hLc, hLe⟩ := exists_continuousOn_log_lift hγc hγne
  have hwind : Lf 1 - Lf 0 = 2 * π * I := hloc ρ hρ0 hρρ₁ Lf hLc hLe
  -- the comparison loop `β(t) = ρ b e^{-2πit}` and its lift, of change `-2πi`
  have hρb : (ρ : ℂ) * dzbar f z₀ ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 hρ0.ne') hb0
  have hMe : ∀ t ∈ Icc (0 : ℝ) 1,
      Complex.exp ((fun t : ℝ => Complex.log ((ρ : ℂ) * dzbar f z₀) - 2 * π * I * t) t) =
        (fun t : ℝ => (ρ : ℂ) * dzbar f z₀ * Complex.exp (-(2 * π * I * t))) t := by
    intro t _
    show Complex.exp (Complex.log ((ρ : ℂ) * dzbar f z₀) - 2 * π * I * t) =
      (ρ : ℂ) * dzbar f z₀ * Complex.exp (-(2 * π * I * t))
    rw [sub_eq_add_neg, Complex.exp_add, Complex.exp_log hρb]
  have hMc : ContinuousOn (fun t : ℝ => Complex.log ((ρ : ℂ) * dzbar f z₀) - 2 * π * I * t) (Icc 0 1) :=
    (by fun_prop : Continuous fun t : ℝ => Complex.log ((ρ : ℂ) * dzbar f z₀) - 2 * π * I * t).continuousOn
  have hβc : ContinuousOn (fun t : ℝ => (ρ : ℂ) * dzbar f z₀ * Complex.exp (-(2 * π * I * t))) (Icc 0 1) :=
    (by fun_prop : Continuous fun t : ℝ =>
      (ρ : ℂ) * dzbar f z₀ * Complex.exp (-(2 * π * I * t))).continuousOn
  have hγ1 : (fun t : ℝ => f (z₀ + ρ * Complex.exp (2 * π * I * t)) - f z₀) 1 =
      (fun t : ℝ => f (z₀ + ρ * Complex.exp (2 * π * I * t)) - f z₀) 0 := by
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_two_pi_mul_I,
      Complex.exp_zero]
  have hβ1 : (fun t : ℝ => (ρ : ℂ) * dzbar f z₀ * Complex.exp (-(2 * π * I * t))) 1 =
      (fun t : ℝ => (ρ : ℂ) * dzbar f z₀ * Complex.exp (-(2 * π * I * t))) 0 := by
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, neg_zero, Complex.exp_neg,
      Complex.exp_two_pi_mul_I, Complex.exp_zero, inv_one]
  -- `γ` stays closer to `β` than `β` to `0`
  have hclose : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(fun t : ℝ => f (z₀ + ρ * Complex.exp (2 * π * I * t)) - f z₀) t -
          (fun t : ℝ => (ρ : ℂ) * dzbar f z₀ * Complex.exp (-(2 * π * I * t))) t‖ <
        ‖(fun t : ℝ => (ρ : ℂ) * dzbar f z₀ * Complex.exp (-(2 * π * I * t))) t‖ := by
    intro t _
    show ‖f (z₀ + ρ * Complex.exp (2 * π * I * t)) - f z₀ -
        (ρ : ℂ) * dzbar f z₀ * Complex.exp (-(2 * π * I * t))‖ <
      ‖(ρ : ℂ) * dzbar f z₀ * Complex.exp (-(2 * π * I * t))‖
    have hconj : (starRingEnd ℂ) ((ρ : ℂ) * Complex.exp (2 * π * I * t)) =
        (ρ : ℂ) * Complex.exp (-(2 * π * I * t)) := by
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
      congr 2
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
      ring
    have hr := hrem ((ρ : ℂ) * Complex.exp (2 * π * I * t)) (by rw [hvn]; exact hρκ)
    rw [hconj, hvn] at hr
    have e1 : f (z₀ + ρ * Complex.exp (2 * π * I * t)) - f z₀ -
        (ρ : ℂ) * dzbar f z₀ * Complex.exp (-(2 * π * I * t)) =
        (f (z₀ + ρ * Complex.exp (2 * π * I * t)) - f z₀ -
          (dz f z₀ * ((ρ : ℂ) * Complex.exp (2 * π * I * t)) +
            dzbar f z₀ * ((ρ : ℂ) * Complex.exp (-(2 * π * I * t))))) +
          dz f z₀ * ((ρ : ℂ) * Complex.exp (2 * π * I * t)) := by
      ring
    have hβn : ‖(ρ : ℂ) * dzbar f z₀ * Complex.exp (-(2 * π * I * t))‖ = ρ * ‖dzbar f z₀‖ := by
      rw [norm_mul, norm_mul, hen', mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
    have hav : ‖dz f z₀ * ((ρ : ℂ) * Complex.exp (2 * π * I * t))‖ = ‖dz f z₀‖ * ρ := by
      rw [norm_mul, hvn]
    rw [e1, hβn]
    calc ‖f (z₀ + ρ * Complex.exp (2 * π * I * t)) - f z₀ -
            (dz f z₀ * ((ρ : ℂ) * Complex.exp (2 * π * I * t)) +
              dzbar f z₀ * ((ρ : ℂ) * Complex.exp (-(2 * π * I * t)))) +
            dz f z₀ * ((ρ : ℂ) * Complex.exp (2 * π * I * t))‖
        ≤ ‖f (z₀ + ρ * Complex.exp (2 * π * I * t)) - f z₀ -
            (dz f z₀ * ((ρ : ℂ) * Complex.exp (2 * π * I * t)) +
              dzbar f z₀ * ((ρ : ℂ) * Complex.exp (-(2 * π * I * t))))‖ +
            ‖dz f z₀ * ((ρ : ℂ) * Complex.exp (2 * π * I * t))‖ := norm_add_le _ _
      _ ≤ (‖dzbar f z₀‖ - ‖dz f z₀‖) / 2 * ρ + ‖dz f z₀‖ * ρ := by
          rw [hav]
          exact add_le_add_left hr _
      _ < ρ * ‖dzbar f z₀‖ := by nlinarith
  have hchange := lift_change_eq_of_norm_sub_lt (hγc.sub continuousOn_const) hβc hγ1 hβ1 hclose hLc hMc
    hLe hMe
  have key : Lf 1 - Lf 0 = -(2 * π * I) := by
    rw [hchange]
    simp only [Complex.ofReal_one, Complex.ofReal_zero]
    ring
  rw [hwind] at key
  have h4 : (4 * π : ℂ) * I = 0 := by linear_combination key
  have h4ne : (4 * π : ℂ) ≠ 0 := by
    have h4r : (4 * π : ℝ) ≠ 0 := by positivity
    exact_mod_cast h4r
  exact mul_ne_zero h4ne I_ne_zero h4

/-! ### Stage C (L3c): the sharp bound `|∂_z f| + |∂_{z̄} f| ≤ K (|∂_z f| - |∂_{z̄} f|)`

At `z₀` with `f(z₀ + v) = f z₀ + a v + b v̄ + o(|v|)` and `|b| ≤ |a|`, put `σ₁ = |a| + |b|`, `σ₂ = |a| - |b| ≥ 0`.
The slit ring `z₀ + t e^{iψ} Ξ_h` has its slit along the direction `e^{iψ}` of maximal stretch (`rc_frame`); its
image lies in the rotated box of half-widths `t(σ₁ + 2ε)`, `t(σ₂ h + 2ε)` (`rc_image_subset_box`, where
`σ₂ ≥ 0` — the orientation — is used), and the images of the slit ends are `≥ 2t(1-h)(σ₁ - ε)` apart
(`rc_chord_ge`).  LM gives `h(1-h)²(σ₁-ε)² ≤ K(1+3h)(σ₁+2ε)(σ₂h+2ε)` (`rc_ring_step`; FIRST conjunct), and
`ε → 0`, then `h → 0`, gives `σ₁ ≤ K σ₂` (`rc_limit`).  In the rank-one case `σ₂ = 0` this forces `σ₁ = 0`
(no such points exist), so no separate exclusion is needed. -/

/-- **Frame** (the singular value decomposition of `v ↦ a v + b v̄`): with `θ = (arg a + arg b)/2` and
`ψ = (arg b - arg a)/2`, `a e^{iψ} = |a| e^{iθ}` and `b e^{-iψ} = |b| e^{iθ}` (also for `a = 0` or `b = 0`). -/
theorem rc_frame (a b : ℂ) : ∃ θ ψ : ℝ, a * Complex.exp (ψ * I) = ‖a‖ * Complex.exp (θ * I) ∧
    b * Complex.exp (((-ψ : ℝ) : ℂ) * I) = ‖b‖ * Complex.exp (θ * I) := by
  refine ⟨(Complex.arg a + Complex.arg b) / 2, (Complex.arg b - Complex.arg a) / 2, ?_, ?_⟩
  · have ha := Complex.norm_mul_exp_arg_mul_I a
    calc a * Complex.exp ((((Complex.arg b - Complex.arg a) / 2 : ℝ) : ℂ) * I)
        = ‖a‖ * Complex.exp (Complex.arg a * I) *
            Complex.exp ((((Complex.arg b - Complex.arg a) / 2 : ℝ) : ℂ) * I) := by rw [ha]
      _ = ‖a‖ * Complex.exp ((((Complex.arg a + Complex.arg b) / 2 : ℝ) : ℂ) * I) := by
          rw [mul_assoc, ← Complex.exp_add]
          congr 2
          push_cast
          ring
  · have hb := Complex.norm_mul_exp_arg_mul_I b
    calc b * Complex.exp (((-((Complex.arg b - Complex.arg a) / 2) : ℝ) : ℂ) * I)
        = ‖b‖ * Complex.exp (Complex.arg b * I) *
            Complex.exp (((-((Complex.arg b - Complex.arg a) / 2) : ℝ) : ℂ) * I) := by rw [hb]
      _ = ‖b‖ * Complex.exp ((((Complex.arg a + Complex.arg b) / 2 : ℝ) : ℂ) * I) := by
          rw [mul_assoc, ← Complex.exp_add]
          congr 2
          push_cast
          ring

/-- The frame identity: `a (e^{iψ} w) + b conj (e^{iψ} w) = e^{iθ} ((|a| + |b|) Re w + i (|a| - |b|) Im w)`. -/
theorem rc_frame_apply {a b : ℂ} {θ ψ : ℝ} (ha : a * Complex.exp (ψ * I) = ‖a‖ * Complex.exp (θ * I))
    (hb : b * Complex.exp (((-ψ : ℝ) : ℂ) * I) = ‖b‖ * Complex.exp (θ * I)) (w : ℂ) :
    a * (Complex.exp (ψ * I) * w) + b * (starRingEnd ℂ) (Complex.exp (ψ * I) * w) =
      Complex.exp (θ * I) * ((((‖a‖ + ‖b‖) * w.re : ℝ) : ℂ) + (((‖a‖ - ‖b‖) * w.im : ℝ) : ℂ) * I) := by
  have hconj : (starRingEnd ℂ) (Complex.exp (ψ * I)) = Complex.exp (((-ψ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    push_cast
    ring
  rw [map_mul, hconj, ← mul_assoc, ← mul_assoc, ha, hb]
  conv_lhs => rw [← Complex.re_add_im w]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The area of a rotated and translated box: `m(e^{iθ} ((-A, A) × (-B, B)) + c) = 4AB`. -/
theorem rc_volume_rigid_openRect (θ : ℝ) (c : ℂ) {A : ℝ} (hA : 0 ≤ A) (B : ℝ) :
    volume (rigidHomeomorph θ c '' openRect (-A) A (-B) B) = ENNReal.ofReal (4 * A * B) := by
  rw [volume_image_rigidHomeomorph θ c (acl_isOpen_openRect _ _ _ _)]
  have hpre : Complex.measurableEquivRealProd ⁻¹' (Ioo (-A) A ×ˢ Ioo (-B) B) = openRect (-A) A (-B) B := by
    ext z
    simp [openRect, and_assoc]
  rw [← hpre, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo, ← ENNReal.ofReal_mul (by linarith)]
  congr 1
  ring

/-- **Image box.**  If `f(z₀ + v) = f z₀ + a v + b v̄ + r(v)`, `‖r(v)‖ ≤ ε‖v‖` for `‖v‖ < κ`, and `3t/2 < κ`, then
the image of the slit ring `z₀ + t e^{iψ} Ξ_h` lies in the box `e^{iθ} ((-t(σ₁+2ε), t(σ₁+2ε)) × (-t(σ₂h+2ε),
t(σ₂h+2ε))) + f z₀` (`σ₁ = |a| + |b|`, `σ₂ = |a| - |b|`).

Proof: for `w = X + iY ∈ Ξ_h ⊆ Q_h` (`|X| < 1`, `|Y| < h ≤ 1/2`, so `|w| < 3/2`) put `v = t e^{iψ} w`,
`‖v‖ < 3t/2 < κ`; by `rc_frame_apply`, `f(z₀ + v) = f z₀ + e^{iθ} (tσ₁X + i tσ₂Y) + r` with
`‖r‖ ≤ ε‖v‖ < (3/2)εt`, so the rotated coordinates satisfy `|tσ₁X + Re(e^{-iθ} r)| < tσ₁ + 2εt` and
`|tσ₂Y + Im(e^{-iθ} r)| < tσ₂h + 2εt`; the second uses `σ₂ ≥ 0` (`hab`: this is where the orientation enters). -/
theorem rc_image_subset_box {f : ℂ → ℂ} {z₀ a b : ℂ} {θ ψ ε κ t h : ℝ}
    (ha : a * Complex.exp (ψ * I) = ‖a‖ * Complex.exp (θ * I))
    (hb : b * Complex.exp (((-ψ : ℝ) : ℂ) * I) = ‖b‖ * Complex.exp (θ * I)) (hab : ‖b‖ ≤ ‖a‖)
    (hε : 0 < ε) (ht : 0 < t) (hh1 : h ≤ 1 / 2) (htκ : 3 * t / 2 < κ)
    (hrem : ∀ v : ℂ, ‖v‖ < κ → ‖f (z₀ + v) - f z₀ - (a * v + b * (starRingEnd ℂ) v)‖ ≤ ε * ‖v‖) :
    f '' ((fun w => z₀ + ((t : ℂ) * Complex.exp (ψ * I)) * w) '' rc_xi h) ⊆
      rigidHomeomorph θ (f z₀) '' openRect (-(t * (‖a‖ + ‖b‖ + 2 * ε))) (t * (‖a‖ + ‖b‖ + 2 * ε))
        (-(t * ((‖a‖ - ‖b‖) * h + 2 * ε))) (t * ((‖a‖ - ‖b‖) * h + 2 * ε)) := by
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  show f (z₀ + ((t : ℂ) * Complex.exp (ψ * I)) * w) ∈ _
  obtain ⟨⟨hw1, hw2, hw3, hw4⟩, -⟩ := hw
  have hx1 : |w.re| < 1 := abs_lt.2 ⟨hw1, hw2⟩
  have hx2 : |w.im| < h := abs_lt.2 ⟨hw3, hw4⟩
  have hwn : ‖w‖ < 3 / 2 := by
    have := Complex.norm_le_abs_re_add_abs_im w
    linarith
  set v : ℂ := ((t : ℂ) * Complex.exp (ψ * I)) * w with hv
  have hvn : ‖v‖ < 3 * t / 2 := by
    rw [hv, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    nlinarith
  have hr := hrem v (hvn.trans htκ)
  have hlin : a * v + b * (starRingEnd ℂ) v = Complex.exp (θ * I) *
      ((((‖a‖ + ‖b‖) * (t * w.re) : ℝ) : ℂ) + (((‖a‖ - ‖b‖) * (t * w.im) : ℝ) : ℂ) * I) := by
    have e : v = Complex.exp (ψ * I) * ((t : ℂ) * w) := by
      rw [hv]
      ring
    rw [e, rc_frame_apply ha hb]
    simp
  set r : ℂ := f (z₀ + v) - f z₀ - (a * v + b * (starRingEnd ℂ) v) with hr_def
  set W : ℂ := Complex.exp (((-θ : ℝ) : ℂ) * I) * (f (z₀ + v) - f z₀) with hW
  have hexp : Complex.exp (((-θ : ℝ) : ℂ) * I) * Complex.exp (θ * I) = 1 := by
    rw [← Complex.exp_add, show ((-θ : ℝ) : ℂ) * I + (θ : ℂ) * I = 0 by push_cast; ring,
      Complex.exp_zero]
  have hWr : W = ((((‖a‖ + ‖b‖) * (t * w.re) : ℝ) : ℂ) + (((‖a‖ - ‖b‖) * (t * w.im) : ℝ) : ℂ) * I) +
      Complex.exp (((-θ : ℝ) : ℂ) * I) * r := by
    have hfr : f (z₀ + v) - f z₀ = Complex.exp (θ * I) *
        ((((‖a‖ + ‖b‖) * (t * w.re) : ℝ) : ℂ) + (((‖a‖ - ‖b‖) * (t * w.im) : ℝ) : ℂ) * I) + r := by
      rw [hr_def, hlin]
      ring
    rw [hW, hfr, mul_add, ← mul_assoc, hexp, one_mul]
  have hWeq : rigidHomeomorph θ (f z₀) W = f (z₀ + v) := by
    show Complex.exp ((θ : ℂ) * I) * W + f z₀ = f (z₀ + v)
    rw [hW, ← mul_assoc, mul_comm (Complex.exp ((θ : ℂ) * I)), hexp, one_mul, sub_add_cancel]
  have hrn : ‖Complex.exp (((-θ : ℝ) : ℂ) * I) * r‖ < 2 * ε * t := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have h1 : ε * ‖v‖ ≤ ε * (3 * t / 2) := mul_le_mul_of_nonneg_left hvn.le hε.le
    nlinarith
  have hre : W.re = (‖a‖ + ‖b‖) * (t * w.re) + (Complex.exp (((-θ : ℝ) : ℂ) * I) * r).re := by
    rw [hWr]
    simp
  have him : W.im = (‖a‖ - ‖b‖) * (t * w.im) + (Complex.exp (((-θ : ℝ) : ℂ) * I) * r).im := by
    rw [hWr]
    simp
  have hre1 := (Complex.abs_re_le_norm (Complex.exp (((-θ : ℝ) : ℂ) * I) * r)).trans_lt hrn
  have him1 := (Complex.abs_im_le_norm (Complex.exp (((-θ : ℝ) : ℂ) * I) * r)).trans_lt hrn
  have hσ₁ : 0 ≤ ‖a‖ + ‖b‖ := by positivity
  have hσ₂ : 0 ≤ ‖a‖ - ‖b‖ := sub_nonneg.2 hab
  have hp1 : |(‖a‖ + ‖b‖) * (t * w.re)| ≤ (‖a‖ + ‖b‖) * t := by
    rw [abs_mul, abs_mul, abs_of_nonneg hσ₁, abs_of_pos ht]
    have := mul_le_mul_of_nonneg_left hx1.le ht.le
    nlinarith
  have hp2 : |(‖a‖ - ‖b‖) * (t * w.im)| ≤ (‖a‖ - ‖b‖) * t * h := by
    rw [abs_mul, abs_mul, abs_of_nonneg hσ₂, abs_of_pos ht]
    have := mul_le_mul_of_nonneg_left hx2.le ht.le
    nlinarith
  refine ⟨W, ⟨?_, ?_, ?_, ?_⟩, hWeq⟩
  · rw [hre]
    have := neg_abs_le ((‖a‖ + ‖b‖) * (t * w.re))
    have := neg_abs_le (Complex.exp (((-θ : ℝ) : ℂ) * I) * r).re
    nlinarith
  · rw [hre]
    have := le_abs_self ((‖a‖ + ‖b‖) * (t * w.re))
    have := le_abs_self (Complex.exp (((-θ : ℝ) : ℂ) * I) * r).re
    nlinarith
  · rw [him]
    have := neg_abs_le ((‖a‖ - ‖b‖) * (t * w.im))
    have := neg_abs_le (Complex.exp (((-θ : ℝ) : ℂ) * I) * r).im
    nlinarith
  · rw [him]
    have := le_abs_self ((‖a‖ - ‖b‖) * (t * w.im))
    have := le_abs_self (Complex.exp (((-θ : ℝ) : ℂ) * I) * r).im
    nlinarith

/-- **Chord bound.**  With the same expansion, `|f(z₀ + t e^{iψ} c) - f(z₀ - t e^{iψ} c)| ≥ 2tc(σ₁ - ε)`
(`t, c > 0`, `tc < κ`).

Proof: the difference is `a(2tc e^{iψ}) + b conj(2tc e^{iψ}) + r₊ - r₋ = 2tc σ₁ e^{iθ} + r₊ - r₋`
(`rc_frame_apply`), and `‖r±‖ ≤ ε tc`. -/
theorem rc_chord_ge {f : ℂ → ℂ} {z₀ a b : ℂ} {θ ψ ε κ t c : ℝ}
    (ha : a * Complex.exp (ψ * I) = ‖a‖ * Complex.exp (θ * I))
    (hb : b * Complex.exp (((-ψ : ℝ) : ℂ) * I) = ‖b‖ * Complex.exp (θ * I))
    (ht : 0 < t) (hc : 0 < c) (htκ : t * c < κ)
    (hrem : ∀ v : ℂ, ‖v‖ < κ → ‖f (z₀ + v) - f z₀ - (a * v + b * (starRingEnd ℂ) v)‖ ≤ ε * ‖v‖) :
    2 * t * c * (‖a‖ + ‖b‖ - ε) ≤
      ‖f (z₀ + ((t : ℂ) * Complex.exp (ψ * I)) * (c : ℂ)) -
        f (z₀ + ((t : ℂ) * Complex.exp (ψ * I)) * ((-c : ℝ) : ℂ))‖ := by
  have hv : ∀ s : ℝ, ‖((t : ℂ) * Complex.exp (ψ * I)) * (s : ℂ)‖ = t * |s| := by
    intro s
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht, mul_one]
  have hlin : ∀ s : ℝ, a * (((t : ℂ) * Complex.exp (ψ * I)) * (s : ℂ)) +
      b * (starRingEnd ℂ) (((t : ℂ) * Complex.exp (ψ * I)) * (s : ℂ)) =
      Complex.exp (θ * I) * (((‖a‖ + ‖b‖) * (t * s) : ℝ) : ℂ) := by
    intro s
    have e : ((t : ℂ) * Complex.exp (ψ * I)) * (s : ℂ) = Complex.exp (ψ * I) * ((t * s : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, rc_frame_apply ha hb]
    simp
  have hvc : ‖((t : ℂ) * Complex.exp (ψ * I)) * (c : ℂ)‖ = t * c := by rw [hv, abs_of_pos hc]
  have hvc' : ‖((t : ℂ) * Complex.exp (ψ * I)) * ((-c : ℝ) : ℂ)‖ = t * c := by
    rw [hv, abs_neg, abs_of_pos hc]
  have hrp := hrem _ (by rw [hvc]; exact htκ)
  have hrm := hrem _ (by rw [hvc']; exact htκ)
  rw [hlin, hvc] at hrp
  rw [hlin, hvc'] at hrm
  set Ep : ℂ := Complex.exp (θ * I) * (((‖a‖ + ‖b‖) * (t * c) : ℝ) : ℂ) with hEp
  set Em : ℂ := Complex.exp (θ * I) * (((‖a‖ + ‖b‖) * (t * -c) : ℝ) : ℂ) with hEm
  set Fp := f (z₀ + ((t : ℂ) * Complex.exp (ψ * I)) * (c : ℂ)) with hFp
  set Fm := f (z₀ + ((t : ℂ) * Complex.exp (ψ * I)) * ((-c : ℝ) : ℂ)) with hFm
  have hE : ‖Ep - Em‖ = 2 * t * c * (‖a‖ + ‖b‖) := by
    rw [hEp, hEm, ← mul_sub, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs,
      show (‖a‖ + ‖b‖) * (t * c) - (‖a‖ + ‖b‖) * (t * -c) = 2 * t * c * (‖a‖ + ‖b‖) by ring]
    exact abs_of_nonneg (by positivity)
  have htri : ‖Ep - Em‖ ≤ ‖Fp - Fm‖ + ‖Fp - f z₀ - Ep‖ + ‖Fm - f z₀ - Em‖ := by
    have e : Ep - Em = (Fp - Fm) - (Fp - f z₀ - Ep) + (Fm - f z₀ - Em) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact norm_sub_le _ _
  linarith

/-- **The ring step (★).**  For `0 < h ≤ 1/2` and `0 < ε < σ₁/2`:
`h (1-h)² (σ₁ - ε)² ≤ K (1+3h) (σ₁ + 2ε) (σ₂ h + 2ε)`.

Proof: choose `θ, ψ` by `rc_frame`, `κ` from `hL ε`, `δ > 0` with `ball z₀ δ ⊆ D`, and `t = min κ δ / 4`.
Then `closure (φ '' Q_h) ⊆ closedBall z₀ (3t/2) ⊆ D` for `φ w = z₀ + t e^{iψ} w` (`|w| < 3/2` on `Q_h`), and LM
(`rc_xi_ring_bound`, FIRST conjunct, preimage ring `φ '' Ξ_h`) gives `πh/(2(1+3h)) ≤ K · 2π · (1/(2d))² · m`.  By
`rc_image_subset_box` and `rc_volume_rigid_openRect`, `m ≤ 4t²(σ₁ + 2ε)(σ₂h + 2ε)`; by `rc_chord_ge` (`c = 1 - h`),
`d ≥ D₀ := 2t(1-h)(σ₁ - ε) > 0`.  So `πh/(2(1+3h)) ≤ Kπ(σ₁+2ε)(σ₂h+2ε)/(2(1-h)²(σ₁-ε)²)`, which is (★).
(Sanity: for a linear map with `K = σ₁/σ₂` and `ε → 0`, (★) reads `(1-h)² ≤ 1 + 3h`.) -/
theorem rc_ring_step {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hD : IsOpen D) (hc : ContinuousOn f D)
    (hi : InjOn f D) (hK : 0 ≤ K) (hring : rc_RingBound f D K) {z₀ a b : ℂ} (hz₀ : z₀ ∈ D)
    (hL : ∀ ε > 0, ∃ κ > 0, ∀ v : ℂ, ‖v‖ < κ →
      ‖f (z₀ + v) - f z₀ - (a * v + b * (starRingEnd ℂ) v)‖ ≤ ε * ‖v‖)
    (hab : ‖b‖ ≤ ‖a‖) {h ε : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1 / 2) (hε0 : 0 < ε)
    (hε1 : ε < (‖a‖ + ‖b‖) / 2) :
    h * (1 - h) ^ 2 * (‖a‖ + ‖b‖ - ε) ^ 2 ≤
      K * (1 + 3 * h) * (‖a‖ + ‖b‖ + 2 * ε) * ((‖a‖ - ‖b‖) * h + 2 * ε) := by
  obtain ⟨θ, ψ, ha, hb⟩ := rc_frame a b
  obtain ⟨κ, hκ, hrem⟩ := hL ε hε0
  obtain ⟨δ, hδ, hδD⟩ := Metric.isOpen_iff.1 hD z₀ hz₀
  have hm : 0 < min κ δ := lt_min hκ hδ
  set t : ℝ := min κ δ / 4 with ht_def
  have ht : 0 < t := by positivity
  have htκ : 3 * t / 2 < κ := by
    have := min_le_left κ δ
    rw [ht_def]
    linarith
  have htδ : 3 * t / 2 < δ := by
    have := min_le_right κ δ
    rw [ht_def]
    linarith
  have hσ₂ : 0 ≤ ‖a‖ - ‖b‖ := sub_nonneg.2 hab
  have hσε : 0 < ‖a‖ + ‖b‖ - ε := by linarith
  have hα : (t : ℂ) * Complex.exp (ψ * I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 ht.ne') (Complex.exp_ne_zero _)
  have hQD : closure ((fun w => z₀ + ((t : ℂ) * Complex.exp (ψ * I)) * w) '' rc_xiQ h) ⊆ D := by
    refine (closure_minimal ?_ isClosed_closedBall).trans ((closedBall_subset_ball htδ).trans hδD)
    rintro _ ⟨w, ⟨hw1, hw2, hw3, hw4⟩, rfl⟩
    show z₀ + ((t : ℂ) * Complex.exp (ψ * I)) * w ∈ closedBall z₀ (3 * t / 2)
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht, Complex.norm_exp_ofReal_mul_I, mul_one]
    have h1 := Complex.norm_le_abs_re_add_abs_im w
    have h2 : |w.re| < 1 := abs_lt.2 ⟨hw1, hw2⟩
    have h3 : |w.im| < h := abs_lt.2 ⟨hw3, hw4⟩
    nlinarith
  have hLM := rc_xi_ring_bound hD hc hi hring hh0 (by linarith) hα hQD
  have hB2 : 0 ≤ (‖a‖ - ‖b‖) * h + 2 * ε := add_nonneg (mul_nonneg hσ₂ hh0.le) (by linarith)
  obtain ⟨Vb, hVb⟩ : ∃ Vb : ℝ, Vb = 4 * (t * (‖a‖ + ‖b‖ + 2 * ε)) * (t * ((‖a‖ - ‖b‖) * h + 2 * ε)) :=
    ⟨_, rfl⟩
  have hVb0 : 0 ≤ Vb := by
    rw [hVb]
    positivity
  have hvol : volume (f '' ((fun w => z₀ + ((t : ℂ) * Complex.exp (ψ * I)) * w) '' rc_xi h)) ≤
      ENNReal.ofReal Vb := by
    rw [hVb, ← rc_volume_rigid_openRect θ (f z₀) (A := t * (‖a‖ + ‖b‖ + 2 * ε)) (by positivity)
      (t * ((‖a‖ - ‖b‖) * h + 2 * ε))]
    exact measure_mono (rc_image_subset_box ha hb hab hε0 ht hh1 htκ hrem)
  have hc0 : (0 : ℝ) < 1 - h := by linarith
  have hch := rc_chord_ge ha hb ht hc0 (by nlinarith) hrem
  have e : ((-(1 - h) : ℝ) : ℂ) = ((h - 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e] at hch
  obtain ⟨D0, hD0⟩ : ∃ D0 : ℝ, D0 = 2 * t * (1 - h) * (‖a‖ + ‖b‖ - ε) := ⟨_, rfl⟩
  rw [← hD0] at hch
  have hD0pos : 0 < D0 := by
    rw [hD0]
    positivity
  have hdd : ENNReal.ofReal (1 / (2 * ‖f (z₀ + ((t : ℂ) * Complex.exp (ψ * I)) * ((1 - h : ℝ) : ℂ)) -
      f (z₀ + ((t : ℂ) * Complex.exp (ψ * I)) * ((h - 1 : ℝ) : ℂ))‖)) ≤
      ENNReal.ofReal (1 / (2 * D0)) :=
    ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hstep : ENNReal.ofReal (π * h / (2 * (1 + 3 * h))) ≤
      ENNReal.ofReal (K * (2 * π * ((1 / (2 * D0)) ^ 2 * Vb))) := by
    refine hLM.trans ?_
    rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * π by positivity),
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ (1 / (2 * D0)) ^ 2 by positivity),
      ENNReal.ofReal_pow (show (0 : ℝ) ≤ 1 / (2 * D0) by positivity)]
    gcongr
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hstep
  have h13 : 2 * (1 + 3 * h) ≠ 0 := by positivity
  have hpos : 0 ≤ 2 * (1 + 3 * h) * (2 * D0) ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hstep hpos
  have h2 : π * h / (2 * (1 + 3 * h)) * (2 * (1 + 3 * h) * (2 * D0) ^ 2) = π * h * (2 * D0) ^ 2 := by
    rw [← mul_assoc, div_mul_cancel₀ _ h13]
  have hinv : (1 / (2 * D0)) ^ 2 * (2 * D0) ^ 2 = 1 := by
    rw [← mul_pow, one_div, inv_mul_cancel₀ (by positivity), one_pow]
  have h3 : K * (2 * π * ((1 / (2 * D0)) ^ 2 * Vb)) * (2 * (1 + 3 * h) * (2 * D0) ^ 2) =
      K * (2 * π) * Vb * (2 * (1 + 3 * h)) := by
    calc K * (2 * π * ((1 / (2 * D0)) ^ 2 * Vb)) * (2 * (1 + 3 * h) * (2 * D0) ^ 2)
        = K * (2 * π) * Vb * (2 * (1 + 3 * h)) * ((1 / (2 * D0)) ^ 2 * (2 * D0) ^ 2) := by ring
      _ = K * (2 * π) * Vb * (2 * (1 + 3 * h)) := by rw [hinv, mul_one]
  rw [h2, h3] at h1
  have e1 : π * h * (2 * D0) ^ 2 = π * (16 * t ^ 2) * (h * (1 - h) ^ 2 * (‖a‖ + ‖b‖ - ε) ^ 2) := by
    rw [hD0]
    ring
  have e2 : K * (2 * π) * Vb * (2 * (1 + 3 * h)) =
      π * (16 * t ^ 2) * (K * (1 + 3 * h) * (‖a‖ + ‖b‖ + 2 * ε) * ((‖a‖ - ‖b‖) * h + 2 * ε)) := by
    rw [hVb]
    ring
  rw [e1, e2] at h1
  exact le_of_mul_le_mul_left h1 (by positivity)

/-- **The limit.**  If (★) holds for all `0 < h ≤ 1/2`, `0 < ε < σ₁/2`, then `σ₁ ≤ K σ₂` (no sign conditions on
`K`, `σ₂`).

Proof: fix `h`, let `ε → 0⁺` (both sides are polynomials in `ε`): `h(1-h)²σ₁² ≤ K(1+3h)σ₁σ₂h`; divide by
`hσ₁ > 0`: `(1-h)²σ₁ ≤ K(1+3h)σ₂`; let `h → 0⁺` (`le_of_tendsto_of_tendsto` on `𝓝[>] 0`, twice). -/
theorem rc_limit {σ₁ σ₂ K : ℝ} (hσ₁ : 0 < σ₁)
    (hstar : ∀ h ε : ℝ, 0 < h → h ≤ 1 / 2 → 0 < ε → ε < σ₁ / 2 →
      h * (1 - h) ^ 2 * (σ₁ - ε) ^ 2 ≤ K * (1 + 3 * h) * (σ₁ + 2 * ε) * (σ₂ * h + 2 * ε)) :
    σ₁ ≤ K * σ₂ := by
  have step1 : ∀ h : ℝ, 0 < h → h ≤ 1 / 2 → (1 - h) ^ 2 * σ₁ ≤ K * (1 + 3 * h) * σ₂ := by
    intro h hh0 hh1
    have hlim : h * (1 - h) ^ 2 * (σ₁ - 0) ^ 2 ≤
        K * (1 + 3 * h) * (σ₁ + 2 * 0) * (σ₂ * h + 2 * 0) := by
      refine le_of_tendsto_of_tendsto (b := 𝓝[>] (0 : ℝ))
        (((by fun_prop : Continuous fun ε : ℝ => h * (1 - h) ^ 2 * (σ₁ - ε) ^ 2).tendsto 0).mono_left
          nhdsWithin_le_nhds)
        (((by fun_prop : Continuous fun ε : ℝ =>
          K * (1 + 3 * h) * (σ₁ + 2 * ε) * (σ₂ * h + 2 * ε)).tendsto 0).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < σ₁ / 2 by positivity)] with ε hε
      exact hstar h ε hh0 hh1 hε.1 hε.2
    have hpos : 0 < h * σ₁ := mul_pos hh0 hσ₁
    have hmul : h * σ₁ * ((1 - h) ^ 2 * σ₁) ≤ h * σ₁ * (K * (1 + 3 * h) * σ₂) := by nlinarith [hlim]
    exact le_of_mul_le_mul_left hmul hpos
  have hlim2 : (1 - 0) ^ 2 * σ₁ ≤ K * (1 + 3 * 0) * σ₂ := by
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] (0 : ℝ))
      (((by fun_prop : Continuous fun h : ℝ => (1 - h) ^ 2 * σ₁).tendsto 0).mono_left nhdsWithin_le_nhds)
      (((by fun_prop : Continuous fun h : ℝ => K * (1 + 3 * h) * σ₂).tendsto 0).mono_left
        nhdsWithin_le_nhds) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with h hh
    exact step1 h hh.1 hh.2.le
  simpa using hlim2

/-- **L3c**: at a point of real differentiability with `|∂_{z̄} f| ≤ |∂_z f|` (Stage B), the ring condition gives
`|∂_z f| + |∂_{z̄} f| ≤ K (|∂_z f| - |∂_{z̄} f|)`.  If `∂_z f(z₀) = 0` both sides vanish; otherwise `σ₁ > 0` and
`rc_limit` applies to `rc_ring_step` (the expansion from `fderiv_eq_dz_dzbar`, S06:34). -/
theorem rc_L3c {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hD : IsOpen D) (hc : ContinuousOn f D) (hi : InjOn f D)
    (hK : 0 ≤ K) (hring : rc_RingBound f D K) {z₀ : ℂ} (hz₀ : z₀ ∈ D) (hdiff : DifferentiableAt ℝ f z₀)
    (horient : ‖dzbar f z₀‖ ≤ ‖dz f z₀‖) :
    ‖dz f z₀‖ + ‖dzbar f z₀‖ ≤ K * (‖dz f z₀‖ - ‖dzbar f z₀‖) := by
  rcases (norm_nonneg (dz f z₀)).eq_or_lt with h0 | hpos
  · have h1 : ‖dzbar f z₀‖ = 0 := le_antisymm (horient.trans h0.symm.le) (norm_nonneg _)
    rw [← h0, h1]
    simp
  · have hσ : 0 < ‖dz f z₀‖ + ‖dzbar f z₀‖ := by linarith [norm_nonneg (dzbar f z₀)]
    have hL : ∀ ε > 0, ∃ κ > 0, ∀ v : ℂ, ‖v‖ < κ →
        ‖f (z₀ + v) - f z₀ - (dz f z₀ * v + dzbar f z₀ * (starRingEnd ℂ) v)‖ ≤ ε * ‖v‖ := by
      intro ε hε
      have ho := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hdiff.hasFDerivAt).def hε
      obtain ⟨κ, hκ, hκv⟩ := Metric.eventually_nhds_iff.1 ho
      refine ⟨κ, hκ, fun v hv => ?_⟩
      have h1 := @hκv v (by rw [dist_zero_right]; exact hv)
      rwa [fderiv_eq_dz_dzbar hdiff] at h1
    exact rc_limit hσ fun h ε hh0 hh1 hε0 hε1 =>
      rc_ring_step hD hc hi hK hring hz₀ hL horient hh0 hh1 hε0 hε1

/-- The converse of Theorem 7.4 (Lehto–Virtanen): an orientation preserving homeomorphism
satisfying `M(B)/K ≤ M(f(B)) ≤ K M(B)` for all doubly connected `B` with `B̄ ⊆ D` is
`K`-quasiconformal.

Proved (s21r, 2026-09-27).  The book refers to Lehto–Virtanen I, Theorem 7.2; this proof goes through the analytic
definition instead (Theorem 10.1, `thm10_1_isKQC_iff`, same `K`).  The inequality `M(B) ≤ K M(f(B))`, applied to
slit-rectangle rings `β + α Ξ_h` (`rc_xi_ring_bound`: `M ≥ πh/(2(1+3h))` below, the length–area bound above), gives
`IsACL f D` (`rc_isACL`, the Theorem 9.1 chain) and `|∂_z f| + |∂_{z̄} f| ≤ K (|∂_z f| - |∂_{z̄} f|)` at every point of
differentiability (`rc_L3c`, slit along the direction of maximal stretch), once sense preservation gives
`|∂_{z̄} f| ≤ |∂_z f|` there (`rc_norm_dzbar_le`, local winding `+1`).  Lehto–Virtanen's own proof stays in the
geometric definition; as drawn, its comb ring (their Fig. 2) touches `∂R′`. -/
theorem isKQC_of_dcModulus_bound {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hD : IsOpen D) (hK : 1 ≤ K)
    (hhom : IsHomeomorphOnto f D (f '' D)) (hsense : IsSensePreserving f D)
    (hbound : ∀ B : Set ℂ, IsDoublyConnected B → closure (toExt B) ⊆ toExt D →
      dcModulus B ≤ ENNReal.ofReal K * dcModulus (f '' B) ∧
        dcModulus (f '' B) ≤ ENNReal.ofReal K * dcModulus B) :
    IsKQC f D K := by
  have hring : rc_RingBound f D K := fun B hB hBD => (hbound B hB hBD).1
  refine (thm10_1_isKQC_iff hD hK hhom).2 ⟨rc_isACL hD (by linarith) hhom.1 hhom.2.1 hring,
    ae_restrict_of_forall_mem hD.measurableSet fun z hz => ?_⟩
  by_cases hd : DifferentiableAt ℝ f z
  · exact rc_L3c hD hhom.1 hhom.2.1 (by linarith) hring hz hd
      (rc_norm_dzbar_le hD hhom.1 hhom.2.1 hsense hz hd)
  · simp [dz, dzbar, fderiv_zero_of_not_differentiableAt hd]

end LiZhongQC
