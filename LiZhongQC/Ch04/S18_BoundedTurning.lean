import LiZhongQC.Ch04.S17_BoundaryValues

/-!
# §18 拟圆周的几何特征 — The geometric characterization of quasicircles

* Definition (§18.1): `M`-bounded turning (有界折转)        — `IsBoundedTurning`
* a `K`-quasicircle through `∞` is `λ(K)`-bounded turning  — `quasicircle_through_inf_boundedTurning`
* Theorem 18.1 (Ahlfors: quasicircles are exactly the Jordan curves of bounded turning)
                                                            — `thm18_1_boundedTurning_of_quasicircle`,
                                                              `thm18_1_quasicircle_of_boundedTurning`,
                                                              `thm18_1`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- **Definition** (§18.1, `M` 有界折转).  A Jordan curve `C ⊆ ℂ̄` is of `M`-bounded turning: for any
two distinct finite points `z₁, z₂ ∈ C`, one of the two arcs of `C ∖ {z₁, z₂}` has diameter at most
`M |z₁ - z₂|` (an arc through `∞` has infinite diameter). -/
def IsBoundedTurning (C : Set ExtPlane) (M : ℝ) : Prop :=
  IsJordanCurve C ∧ 1 ≤ M ∧
    ∀ z₁ z₂ : ℂ, (z₁ : ExtPlane) ∈ C → (z₂ : ExtPlane) ∈ C → z₁ ≠ z₂ →
      ∃ p ∈ C \ {(z₁ : ExtPlane), (z₂ : ExtPlane)},
        extInf ∉ connectedComponentIn (C \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) p ∧
        Metric.ediam {z : ℂ | (z : ExtPlane) ∈
          connectedComponentIn (C \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) p} ≤
            ENNReal.ofReal (M * ‖z₁ - z₂‖)

/-! ### Three-point track interface, part 2 (coordinator 553e2d) -/

/-- The boundary of `ℍ` in `ℂ̄` is the extended real line `ℝ ∪ {∞}`: the Cayley map sends `1` to `∞` and the rest
of the unit circle onto `ℝ` (`b4_cayley_image`). -/
theorem tp_c1_frontier_upperHalf : frontier (toExt upperHalf) = toExt realLine ∪ {extInf} := by
  apply Subset.antisymm
  · rw [frontier_toExt_upperHalf]
    rintro _ ⟨_, ⟨ζ, hζ, rfl⟩, rfl⟩
    by_cases h1 : ζ = 1
    · right
      rw [h1, mobiusExt_coe_of_eq_zero (show (-1 : ℂ) * 1 + 1 = 0 by ring)]
      exact mem_singleton _
    · left
      have hden : (-1 : ℂ) * ζ + 1 ≠ 0 := fun h => h1 (by linear_combination -h)
      rw [mobiusExt_coe hden]
      refine ⟨_, ?_, rfl⟩
      rw [← b4_cayley_image]
      refine ⟨ζ, ⟨hζ, h1⟩, ?_⟩
      simp only [mobiusFn]
      ring
  · rintro p (⟨z, hz, rfl⟩ | hp)
    · have hz' : z.im = 0 := hz
      have hzr : ((z.re : ℝ) : ℂ) = z := Complex.ext rfl (by simp [hz'])
      rw [← hzr]
      exact ofReal_mem_frontier_upperHalf z.re
    · rw [mem_singleton_iff.mp hp]
      exact infty_mem_frontier_upperHalf

/-- The extended real line `ℝ ∪ {∞}` is a Jordan curve (it is `∂ℍ`). -/
theorem tp_c1_isJordanCurve_extRealLine : IsJordanCurve (toExt realLine ∪ {extInf}) := by
  rw [← tp_c1_frontier_upperHalf]
  exact isJordanCurve_frontier_upperHalf

/-- **C1.** `f(ℝ) ∪ {∞}` is a Jordan curve for a q.c. map `f` of the plane onto itself: it is the image of the
extended real line `∂ℍ` (a Jordan curve) under the homeomorphism of `ℂ̄` induced by `f`. -/
theorem tp_isJordanCurve_image_realLine {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hs : f '' univ = univ) :
    IsJordanCurve (toExt (f '' realLine) ∪ {extInf}) := by
  obtain ⟨e, he⟩ := t1_homeomorph hf hs
  have himg : e.onePointCongr '' (toExt realLine ∪ {extInf}) = toExt (f '' realLine) ∪ {extInf} := by
    rw [image_union, s13x_de_image_toExt, he, image_singleton]
    rfl
  rw [← himg]
  exact uq_isJordanCurve_image _ tp_c1_isJordanCurve_extRealLine

/-- **C2 helper.** For an injective `f`, a point of `f(ℝ) ∪ {∞}` lying in `f({x₁ < Re z < x₂})` lies on the open
arc `f((x₁, x₂))`. -/
theorem tp_c2_mem_arc_of_mem_strip {f : ℂ → ℂ} (hinj : Function.Injective f) {x₁ x₂ : ℝ} {w : ExtPlane}
    (hw : w ∈ toExt (f '' realLine) ∪ {extInf}) (hU : w ∈ toExt (f '' (Complex.re ⁻¹' Ioo x₁ x₂))) :
    w ∈ toExt ((fun t : ℝ => f t) '' Ioo x₁ x₂) := by
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hU
  rcases hw with ⟨_, ⟨y, hy, rfl⟩, h⟩ | h
  · have hyz : y = z := hinj (OnePoint.coe_injective h)
    have hyim : y.im = 0 := hy
    have hzr : ((z.re : ℝ) : ℂ) = z := Complex.ext rfl (by simp [← hyz, hyim])
    exact ⟨_, ⟨z.re, hz, rfl⟩, congrArg (fun u : ℂ => ((f u : ℂ) : ExtPlane)) hzr⟩
  · exact absurd h (OnePoint.coe_ne_infty _)

/-- **C2 helper.** A point of `ℂ̄` other than `f(x₁), f(x₂)` lies in the open set `f({x₁ < Re z < x₂})` or off the
compact arc `f([x₁, x₂])`. -/
theorem tp_c2_mem_union {f : ℂ → ℂ} {x₁ x₂ : ℝ} {w : ExtPlane}
    (hw : w ∉ ({((f x₁ : ℂ) : ExtPlane), ((f x₂ : ℂ) : ExtPlane)} : Set ExtPlane)) :
    w ∈ toExt (f '' (Complex.re ⁻¹' Ioo x₁ x₂)) ∪ (toExt ((fun t : ℝ => f t) '' Icc x₁ x₂))ᶜ := by
  by_cases hwK : w ∈ toExt ((fun t : ℝ => f t) '' Icc x₁ x₂)
  · left
    obtain ⟨_, ⟨t, ht, rfl⟩, rfl⟩ := hwK
    have h1 : t ≠ x₁ := by
      rintro rfl
      exact hw (Or.inl rfl)
    have h2 : t ≠ x₂ := by
      rintro rfl
      exact hw (Or.inr rfl)
    exact ⟨_, ⟨(t : ℂ), ⟨lt_of_le_of_ne ht.1 h1.symm, lt_of_le_of_ne ht.2 h2⟩, rfl⟩, rfl⟩
  · exact Or.inr hwK

/-- **C2.** For `x₁ < x₂`, the component of `(f(ℝ) ∪ {∞}) ∖ {f(x₁), f(x₂)}` through `f((x₁ + x₂)/2)` is the finite arc
`f((x₁, x₂))`: the arc is connected, and it is cut out of the curve both by the open set `f({x₁ < Re z < x₂})` and by
the complement of the compact arc `f([x₁, x₂])`. -/
theorem tp_arc_component {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hs : f '' univ = univ) {x₁ x₂ : ℝ}
    (h : x₁ < x₂) :
    connectedComponentIn ((toExt (f '' realLine) ∪ {extInf}) \ {((f x₁ : ℂ) : ExtPlane), ((f x₂ : ℂ) : ExtPlane)})
        ((f (((x₁ + x₂) / 2 : ℝ) : ℂ) : ℂ) : ExtPlane) =
      toExt ((fun t : ℝ => f t) '' Ioo x₁ x₂) := by
  have hinj : Function.Injective f := fun a b hab => hf.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
  have hg : Continuous (fun t : ℝ => f t) := (continuousOn_univ.1 hf.2.2.1.1).comp Complex.continuous_ofReal
  have hmid : ((x₁ + x₂) / 2 : ℝ) ∈ Ioo x₁ x₂ := ⟨by linarith, by linarith⟩
  have hpA : ((f (((x₁ + x₂) / 2 : ℝ) : ℂ) : ℂ) : ExtPlane) ∈ toExt ((fun t : ℝ => f t) '' Ioo x₁ x₂) :=
    ⟨_, ⟨_, hmid, rfl⟩, rfl⟩
  have hAS : toExt ((fun t : ℝ => f t) '' Ioo x₁ x₂) ⊆
      (toExt (f '' realLine) ∪ {extInf}) \ {((f x₁ : ℂ) : ExtPlane), ((f x₂ : ℂ) : ExtPlane)} := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨Or.inl ⟨_, ⟨(t : ℂ), Complex.ofReal_im t, rfl⟩, rfl⟩, ?_⟩
    rintro (h' | h')
    · exact ht.1.ne' (Complex.ofReal_injective (hinj (OnePoint.coe_injective h')))
    · exact ht.2.ne (Complex.ofReal_injective (hinj (OnePoint.coe_injective h')))
  refine Subset.antisymm ?_ (((isPreconnected_Ioo.image _ hg.continuousOn).image _
    OnePoint.continuous_coe.continuousOn).subset_connectedComponentIn hpA hAS)
  obtain ⟨e, he⟩ := t1_homeomorph hf hs
  have hUo : IsOpen (toExt (f '' (Complex.re ⁻¹' Ioo x₁ x₂))) := by
    refine OnePoint.isOpen_image_coe.2 ?_
    rw [← he]
    exact e.isOpenMap _ (isOpen_Ioo.preimage Complex.continuous_re)
  have hK : IsCompact ((fun t : ℝ => f t) '' Icc x₁ x₂) := isCompact_Icc.image hg
  have hVo : IsOpen (toExt ((fun t : ℝ => f t) '' Icc x₁ x₂))ᶜ :=
    OnePoint.isOpen_compl_image_coe.2 ⟨hK.isClosed, hK⟩
  have hQS := connectedComponentIn_subset
    ((toExt (f '' realLine) ∪ {extInf}) \ {((f x₁ : ℂ) : ExtPlane), ((f x₂ : ℂ) : ExtPlane)})
    ((f (((x₁ + x₂) / 2 : ℝ) : ℂ) : ℂ) : ExtPlane)
  have hdisj : connectedComponentIn
      ((toExt (f '' realLine) ∪ {extInf}) \ {((f x₁ : ℂ) : ExtPlane), ((f x₂ : ℂ) : ExtPlane)})
      ((f (((x₁ + x₂) / 2 : ℝ) : ℂ) : ℂ) : ExtPlane) ∩
        (toExt (f '' (Complex.re ⁻¹' Ioo x₁ x₂)) ∩ (toExt ((fun t : ℝ => f t) '' Icc x₁ x₂))ᶜ) = ∅ := by
    refine eq_empty_of_forall_notMem fun w ⟨hwQ, hwU, hwV⟩ => hwV ?_
    exact image_mono (image_mono Ioo_subset_Icc_self)
      (tp_c2_mem_arc_of_mem_strip hinj (hQS hwQ).1 hwU)
  rcases isPreconnected_iff_subset_of_disjoint.1 isPreconnected_connectedComponentIn _ _ hUo hVo
    (fun w hw => tp_c2_mem_union (hQS hw).2) hdisj with hQU | hQV
  · exact fun w hw => tp_c2_mem_arc_of_mem_strip hinj (hQS hw).1 (hQU hw)
  · exact absurd (image_mono (image_mono Ioo_subset_Icc_self) hpA)
      (hQV (mem_connectedComponentIn (hAS hpA)))

/-- **C3.** The finite arc `f((x₁, x₂))` has diameter at most `λ(K) |f(x₁) - f(x₂)|`: by (16.1) at `(x₁, t, x₂)` and at
`(x₁, t', x₂)`, `2 |f(t) - f(t')| ≤ 2 λ(K) |f(x₁) - f(x₂)|` (for `x₂ ≤ x₁` the arc is empty). -/
theorem tp_arc_ediam {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hs : f '' univ = univ) {x₁ x₂ : ℝ} :
    Metric.ediam ((fun t : ℝ => f t) '' Ioo x₁ x₂) ≤ ENNReal.ofReal (lambdaInv K * ‖f x₁ - f x₂‖) := by
  refine Metric.ediam_le_of_forall_dist_le ?_
  rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩
  -- (16.1) at `(x₁, t, x₂)` and at `(x₁, t', x₂)`, plus the triangle inequality through `f x₁` and through `f x₂`
  have h₁ := thm16_1_three_point hf hs ht.1 ht.2
  have h₂ := thm16_1_three_point hf hs ht'.1 ht'.2
  have e₁ : ‖f t - f t'‖ ≤ ‖f t - f x₁‖ + ‖f x₁ - f t'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have e₂ : ‖f t - f t'‖ ≤ ‖f t - f x₂‖ + ‖f x₂ - f t'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [norm_sub_rev (f t) (f x₁)] at e₁
  rw [norm_sub_rev (f x₂) (f t')] at e₂
  rw [dist_eq_norm]
  linarith

/-- A finite point of `f(ℝ) ∪ {∞}` is `f(x)` for a real `x`. -/
theorem tp_exists_real_of_mem {f : ℂ → ℂ} {z : ℂ} (hz : (z : ExtPlane) ∈ toExt (f '' realLine) ∪ {extInf}) :
    ∃ x : ℝ, f x = z := by
  rcases hz with ⟨w, ⟨y, hy, rfl⟩, h⟩ | h
  · refine ⟨y.re, ?_⟩
    have hy' : y.im = 0 := hy
    have hyr : ((y.re : ℝ) : ℂ) = y := Complex.ext rfl (by simp [hy'])
    rw [hyr]
    exact OnePoint.coe_injective h
  · exact absurd h (OnePoint.coe_ne_infty z)

/-- The bounded-turning condition at `f(x₁), f(x₂)`, `x₁ < x₂`: the component through `f((x₁ + x₂)/2)` is the finite
arc `f((x₁, x₂))` (C2), of diameter at most `λ(K) |f(x₁) - f(x₂)|` (C3). -/
theorem tp_bt_of_lt {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hs : f '' univ = univ) {x₁ x₂ : ℝ}
    (h : x₁ < x₂) :
    ∃ p ∈ (toExt (f '' realLine) ∪ {extInf}) \ {((f x₁ : ℂ) : ExtPlane), ((f x₂ : ℂ) : ExtPlane)},
      extInf ∉ connectedComponentIn
        ((toExt (f '' realLine) ∪ {extInf}) \ {((f x₁ : ℂ) : ExtPlane), ((f x₂ : ℂ) : ExtPlane)}) p ∧
      Metric.ediam {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn
        ((toExt (f '' realLine) ∪ {extInf}) \ {((f x₁ : ℂ) : ExtPlane), ((f x₂ : ℂ) : ExtPlane)}) p} ≤
          ENNReal.ofReal (lambdaInv K * ‖f x₁ - f x₂‖) := by
  have hinj : Function.Injective f := fun a b hab => hf.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
  have hm1 : ((x₁ + x₂) / 2 : ℝ) ≠ x₁ := by intro h'; linarith
  have hm2 : ((x₁ + x₂) / 2 : ℝ) ≠ x₂ := by intro h'; linarith
  refine ⟨((f (((x₁ + x₂) / 2 : ℝ) : ℂ) : ℂ) : ExtPlane), ⟨Or.inl ⟨_, ⟨_, ?_, rfl⟩, rfl⟩, ?_⟩, ?_⟩
  · show (((x₁ + x₂) / 2 : ℝ) : ℂ).im = 0
    exact Complex.ofReal_im _
  · rintro (h' | h')
    · exact hm1 (Complex.ofReal_injective (hinj (OnePoint.coe_injective h')))
    · exact hm2 (Complex.ofReal_injective (hinj (OnePoint.coe_injective h')))
  rw [tp_arc_component hf hs h]
  refine ⟨fun h' => ?_, ?_⟩
  · obtain ⟨_, -, h''⟩ := h'
    exact OnePoint.coe_ne_infty _ h''
  · have hset : {z : ℂ | (z : ExtPlane) ∈ toExt ((fun t : ℝ => f t) '' Ioo x₁ x₂)} =
        (fun t : ℝ => f t) '' Ioo x₁ x₂ :=
      preimage_image_eq _ OnePoint.coe_injective
    rw [hset]
    exact tp_arc_ediam hf hs

/-- §18.1: a `K`-quasicircle `f(ℝ) ∪ {∞}` through `∞` is of `λ(K)`-bounded turning. -/
theorem quasicircle_through_inf_boundedTurning {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K)
    (hs : f '' univ = univ) :
    IsBoundedTurning (toExt (f '' realLine) ∪ {extInf}) (lambdaInv K) := by
  refine ⟨tp_isJordanCurve_image_realLine hf hs, td_one_le_lambdaInv hf.2.1, ?_⟩
  intro z₁ z₂ hz₁ hz₂ hne
  obtain ⟨x₁, rfl⟩ := tp_exists_real_of_mem hz₁
  obtain ⟨x₂, rfl⟩ := tp_exists_real_of_mem hz₂
  have hx : x₁ ≠ x₂ := fun h => hne (by rw [h])
  rcases lt_or_gt_of_ne hx with h | h
  · exact tp_bt_of_lt hf hs h
  · rw [pair_comm, norm_sub_rev]
    exact tp_bt_of_lt hf hs h

/-! ### s15w track (coordinator 553e2d), part N18: Theorem 18.1 (necessity), Möbius reduction to the case through `∞` -/

/-! ### Theorem 18.1 (necessity) — scout N18 helpers -/

/-- Composing a fractional linear transformation with `w ↦ 1/(w - a)`:
`1/(M(w) - a)` for `M = mobiusExt α β κ δ` is `mobiusExt κ δ (α - aκ) (β - aδ)`. -/
theorem n18_mobius_comp {α β κ δ : ℂ} (a : ℂ) (h : α * δ - β * κ ≠ 0) (w : ExtPlane) :
    mobiusExt 0 1 1 (-a) (mobiusExt α β κ δ w) = mobiusExt κ δ (α - a * κ) (β - a * δ) w := by
  induction w using OnePoint.rec with
  | infty =>
    by_cases hκ : κ = 0
    · have hα : α ≠ 0 := by
        rintro rfl
        apply h
        simp [hκ]
      rw [mobiusExt_infty_of_eq hκ, mobiusExt_infty_of_ne one_ne_zero,
        mobiusExt_infty_of_ne (by rw [hκ, mul_zero, sub_zero]; exact hα)]
      simp [hκ]
    · rw [mobiusExt_infty_of_ne hκ]
      by_cases hp : α - a * κ = 0
      · rw [mobiusExt_infty_of_eq hp, mobiusExt_coe_of_eq_zero]
        field_simp
        linear_combination hp
      · have hq : 1 * (α / κ) + -a ≠ 0 := by
          intro h0
          apply hp
          field_simp at h0
          linear_combination h0
        rw [mobiusExt_infty_of_ne hp, mobiusExt_coe hq]
        congr 1
        simp only [mobiusFn]
        field_simp
        ring
  | coe z =>
    by_cases hz : κ * z + δ = 0
    · have hn : (α - a * κ) * z + (β - a * δ) ≠ 0 := by
        intro h0
        apply h
        linear_combination α * hz - κ * h0 - a * κ * hz
      rw [mobiusExt_coe_of_eq_zero hz, mobiusExt_infty_of_ne one_ne_zero, mobiusExt_coe hn]
      congr 1
      simp [mobiusFn, hz]
    · have hmul := mobiusFn_mul_den (a := α) (b := β) hz
      rw [mobiusExt_coe hz]
      by_cases hp : (α - a * κ) * z + (β - a * δ) = 0
      · rw [mobiusExt_coe_of_eq_zero hp, mobiusExt_coe_of_eq_zero]
        have h0 : (1 * mobiusFn α β κ δ z + -a) * (κ * z + δ) = 0 := by linear_combination hmul + hp
        exact (mul_eq_zero.1 h0).resolve_right hz
      · have hq : 1 * mobiusFn α β κ δ z + -a ≠ 0 := by
          intro h0
          apply hp
          linear_combination (κ * z + δ) * h0 - hmul
        rw [mobiusExt_coe hp, mobiusExt_coe hq]
        congr 1
        show (0 * mobiusFn α β κ δ z + 1) / (1 * mobiusFn α β κ δ z + -a) =
          (κ * z + δ) / ((α - a * κ) * z + (β - a * δ))
        rw [div_eq_div_iff hq hp]
        linear_combination -hmul

/-- The image of a `K`-quasicircle under `w ↦ 1/(w - a)` is a `K`-quasicircle (compose the two
Möbius transformations, `n18_mobius_comp`). -/
theorem n18_isKQuasicircle_inv {C : Set ExtPlane} {K : ℝ} (hC : IsKQuasicircle C K) (a : ℂ) :
    IsKQuasicircle (mobiusExt 0 1 1 (-a) '' C) K := by
  obtain ⟨f, hf, hs, M, ⟨α, β, κ, δ, hdet, rfl⟩, rfl⟩ := hC
  refine ⟨f, hf, hs, mobiusExt κ δ (α - a * κ) (β - a * δ),
    ⟨κ, δ, α - a * κ, β - a * δ, fun h => hdet (by linear_combination -h), rfl⟩, ?_⟩
  rw [image_image]
  exact image_congr fun w _ => n18_mobius_comp a hdet w

/-- A `K`-quasicircle is a Jordan curve: the image of the circle `f(S¹)` (a Jordan curve) under a
Möbius homeomorphism of `ℂ̄`. -/
theorem n18_isJordanCurve {C : Set ExtPlane} {K : ℝ} (hC : IsKQuasicircle C K) : IsJordanCurve C := by
  obtain ⟨f, hf, hs, M, ⟨α, β, κ, δ, hdet, rfl⟩, rfl⟩ := hC
  have hfc : Continuous f := continuousOn_univ.1 hf.2.2.1.1
  have hinj : Function.Injective f := fun x y hxy => hf.2.2.1.2.1 (mem_univ x) (mem_univ y) hxy
  have hmap : OnePoint.map f '' toExt (sphere 0 1) = toExt (f '' sphere 0 1) := by
    unfold toExt
    rw [← image_comp, ← image_comp]
    exact image_congr fun x _ => by simp
  rw [hmap]
  exact uq_isJordanCurve_image (mobiusHomeomorph α β κ δ hdet)
    (iod_isJordanCurve_image_sphere one_pos hfc.continuousOn hinj.injOn)

/-- A `K`-quasicircle has a point other than any two given points (it contains the three distinct
points `M(f(1)), M(f(-1)), M(f(i))`). -/
theorem n18_exists_third {C : Set ExtPlane} {K : ℝ} (hC : IsKQuasicircle C K) (p q : ExtPlane) :
    ∃ r ∈ C, r ≠ p ∧ r ≠ q := by
  obtain ⟨f, hf, hs, M, ⟨α, β, κ, δ, hdet, rfl⟩, rfl⟩ := hC
  have hinj : Function.Injective f := fun x y hxy => hf.2.2.1.2.1 (mem_univ x) (mem_univ y) hxy
  have hFi : ∀ x y : ℂ, mobiusExt α β κ δ (OnePoint.map f (x : ExtPlane)) =
      mobiusExt α β κ δ (OnePoint.map f (y : ExtPlane)) → x = y := by
    intro x y h
    have hMi : Function.Injective (mobiusExt α β κ δ) := (mobiusHomeomorph α β κ δ hdet).injective
    have h' := hMi h
    rw [OnePoint.map_some, OnePoint.map_some] at h'
    exact hinj (OnePoint.coe_injective h')
  have hmem : ∀ ζ : ℂ, ‖ζ‖ = 1 → mobiusExt α β κ δ (OnePoint.map f (ζ : ExtPlane)) ∈
      mobiusExt α β κ δ '' (OnePoint.map f '' toExt (sphere 0 1)) :=
    fun ζ hζ => mem_image_of_mem _ (mem_image_of_mem _ ⟨ζ, mem_sphere_zero_iff_norm.mpr hζ, rfl⟩)
  have n1 : mobiusExt α β κ δ (OnePoint.map f ((1 : ℂ) : ExtPlane)) ≠
      mobiusExt α β κ δ (OnePoint.map f ((-1 : ℂ) : ExtPlane)) := fun h => by
    have := hFi _ _ h
    norm_num at this
  have n2 : mobiusExt α β κ δ (OnePoint.map f ((1 : ℂ) : ExtPlane)) ≠
      mobiusExt α β κ δ (OnePoint.map f ((I : ℂ) : ExtPlane)) := fun h => by
    have := congrArg Complex.im (hFi _ _ h)
    simp at this
  have n3 : mobiusExt α β κ δ (OnePoint.map f ((-1 : ℂ) : ExtPlane)) ≠
      mobiusExt α β κ δ (OnePoint.map f ((I : ℂ) : ExtPlane)) := fun h => by
    have := congrArg Complex.im (hFi _ _ h)
    simp at this
  by_contra hcon
  push Not at hcon
  have e1 := hcon _ (hmem 1 (by simp))
  have e2 := hcon _ (hmem (-1) (by simp))
  have e3 := hcon _ (hmem I (by simp))
  by_cases h1 : mobiusExt α β κ δ (OnePoint.map f ((1 : ℂ) : ExtPlane)) = p
  · have h2 := e2 fun h => n1 (h1.trans h.symm)
    have h3 := e3 fun h => n2 (h1.trans h.symm)
    exact n3 (h2.trans h3.symm)
  · have h1' := e1 h1
    by_cases h2 : mobiusExt α β κ δ (OnePoint.map f ((-1 : ℂ) : ExtPlane)) = p
    · by_cases h3 : mobiusExt α β κ δ (OnePoint.map f ((I : ℂ) : ExtPlane)) = p
      · exact n3 (h2.trans h3.symm)
      · exact n2 (h1'.trans (e3 h3).symm)
    · exact n1 (h1'.trans (e2 h2).symm)

/-- Through `∞`: for `x₁ ≠ x₂`, some point `g(y₀)` (`y₀ ≠ x₁, x₂`) of `g(ℝ) ∪ {∞}` has its component in
`(g(ℝ) ∪ {∞}) ∖ {g(x₁), g(x₂)}` made of finite points `v` with `‖v - g(x₁)‖ ≤ λ(K) ‖g(x₁) - g(x₂)‖`
(`tp_arc_component` + `thm16_1_three_point`). -/
theorem n18_arc_through_inf {g : ℂ → ℂ} {K : ℝ} (hg : IsKQC g univ K) (hgs : g '' univ = univ)
    {x₁ x₂ : ℝ} (hx : x₁ ≠ x₂) :
    ∃ y₀ : ℝ, y₀ ≠ x₁ ∧ y₀ ≠ x₂ ∧
      ∀ q ∈ connectedComponentIn ((toExt (g '' realLine) ∪ {extInf}) \
          {((g x₁ : ℂ) : ExtPlane), ((g x₂ : ℂ) : ExtPlane)}) ((g y₀ : ℂ) : ExtPlane),
        ∃ v : ℂ, q = (v : ExtPlane) ∧ ‖v - g x₁‖ ≤ lambdaInv K * ‖g x₁ - g x₂‖ := by
  rcases lt_or_gt_of_ne hx with h | h
  · refine ⟨(x₁ + x₂) / 2, fun h' => by linarith, fun h' => by linarith, ?_⟩
    rw [tp_arc_component hg hgs h]
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨g t, rfl, ?_⟩
    have h3 := thm16_1_three_point hg hgs ht.1 ht.2
    have e := norm_sub_rev (g t) (g x₁)
    have := norm_nonneg (g t - g x₂)
    linarith
  · refine ⟨(x₂ + x₁) / 2, fun h' => by linarith, fun h' => by linarith, ?_⟩
    rw [pair_comm, tp_arc_component hg hgs h]
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨g t, rfl, ?_⟩
    have h3 := thm16_1_three_point hg hgs ht.1 ht.2
    rw [norm_sub_rev (g x₁) (g x₂)]
    have := norm_nonneg (g x₂ - g t)
    linarith

/-- The algebra of `w ↦ 1/(w - a)`: `‖1/(w-a) - 1/(z₁-a)‖ ≤ L ‖1/(z₁-a) - 1/(z₂-a)‖` gives
`‖w - z₁‖ ‖z₂ - a‖ ≤ L ‖z₁ - z₂‖ ‖w - a‖`. -/
theorem n18_inv_algebra {w z₁ z₂ a : ℂ} {L : ℝ} (hw : w ≠ a) (h1 : z₁ ≠ a) (h2 : z₂ ≠ a)
    (h : ‖(w - a)⁻¹ - (z₁ - a)⁻¹‖ ≤ L * ‖(z₁ - a)⁻¹ - (z₂ - a)⁻¹‖) :
    ‖w - z₁‖ * ‖z₂ - a‖ ≤ L * ‖z₁ - z₂‖ * ‖w - a‖ := by
  have hw' : w - a ≠ 0 := sub_ne_zero.mpr hw
  have h1' : z₁ - a ≠ 0 := sub_ne_zero.mpr h1
  have h2' : z₂ - a ≠ 0 := sub_ne_zero.mpr h2
  have e1 : (w - a)⁻¹ - (z₁ - a)⁻¹ = (z₁ - w) / ((w - a) * (z₁ - a)) := by
    field_simp
    ring
  have e2 : (z₁ - a)⁻¹ - (z₂ - a)⁻¹ = (z₂ - z₁) / ((z₁ - a) * (z₂ - a)) := by
    field_simp
    ring
  rw [e1, e2, norm_div, norm_div, norm_mul, norm_mul, norm_sub_rev z₁ w, norm_sub_rev z₂ z₁] at h
  have hA : 0 < ‖w - a‖ := norm_pos_iff.mpr hw'
  have hB : 0 < ‖z₁ - a‖ := norm_pos_iff.mpr h1'
  have hD : 0 < ‖z₂ - a‖ := norm_pos_iff.mpr h2'
  rw [div_le_iff₀ (mul_pos hA hB)] at h
  have e3 : L * (‖z₁ - z₂‖ / (‖z₁ - a‖ * ‖z₂ - a‖)) * (‖w - a‖ * ‖z₁ - a‖) =
      L * ‖z₁ - z₂‖ * ‖w - a‖ / ‖z₂ - a‖ := by
    field_simp
  rw [e3, le_div_iff₀ hD] at h
  exact h

/-- **Cross-ratio form of the three-point condition.** For a `K`-quasicircle `C` and three distinct finite
points `z₁, z₂, a ∈ C`, some `p ∈ C ∖ {z₁, z₂}` has its component in `C ∖ {z₁, z₂}` (the arc not through `a`)
made of points `w` with `‖w - z₁‖ ‖z₂ - a‖ ≤ λ(K) ‖z₁ - z₂‖ ‖w - a‖`: send `a` to `∞` by `w ↦ 1/(w - a)`
(`n18_isKQuasicircle_inv`, `tp_quasicircle_through_inf`) and use `n18_arc_through_inf`. -/
theorem n18_cross {C : Set ExtPlane} {K : ℝ} (hC : IsKQuasicircle C K) {z₁ z₂ a : ℂ}
    (hz₁ : (z₁ : ExtPlane) ∈ C) (hz₂ : (z₂ : ExtPlane) ∈ C) (ha : (a : ExtPlane) ∈ C)
    (h12 : z₁ ≠ z₂) (h1a : z₁ ≠ a) (h2a : z₂ ≠ a) :
    ∃ p ∈ C \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}, ∀ w : ℂ,
      (w : ExtPlane) ∈ connectedComponentIn (C \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) p →
        ‖w - z₁‖ * ‖z₂ - a‖ ≤ lambdaInv K * ‖z₁ - z₂‖ * ‖w - a‖ := by
  have hdet : (0 : ℂ) * (-a) - 1 * 1 ≠ 0 := by norm_num
  have hTc : Continuous (mobiusExt 0 1 1 (-a)) := continuous_mobiusExt hdet
  have hTi : Function.Injective (mobiusExt 0 1 1 (-a)) := (mobiusHomeomorph 0 1 1 (-a) hdet).injective
  have hTa : mobiusExt 0 1 1 (-a) (a : ExtPlane) = extInf := mobiusExt_coe_of_eq_zero (by ring)
  have hTz : ∀ z : ℂ, z ≠ a → mobiusExt 0 1 1 (-a) (z : ExtPlane) = (((z - a)⁻¹ : ℂ) : ExtPlane) := by
    intro z hz
    have hden : (1 : ℂ) * z + -a ≠ 0 := by
      rw [one_mul, ← sub_eq_add_neg]
      exact sub_ne_zero.mpr hz
    rw [mobiusExt_coe hden]
    congr 1
    simp only [mobiusFn]
    ring
  have hinf : extInf ∈ mobiusExt 0 1 1 (-a) '' C := ⟨_, ha, hTa⟩
  obtain ⟨g, hg, hgs, hCg⟩ := tp_quasicircle_through_inf (n18_isKQuasicircle_inv hC a) hinf
  have hginj : Function.Injective g := fun x y hxy => hg.2.2.1.2.1 (mem_univ x) (mem_univ y) hxy
  have hmem : ∀ z : ℂ, (z : ExtPlane) ∈ C → z ≠ a → ∃ x : ℝ, g x = (z - a)⁻¹ := by
    intro z hz hza
    apply tp_exists_real_of_mem (f := g)
    rw [← hCg, ← hTz z hza]
    exact mem_image_of_mem _ hz
  obtain ⟨x₁, hx₁⟩ := hmem z₁ hz₁ h1a
  obtain ⟨x₂, hx₂⟩ := hmem z₂ hz₂ h2a
  have hx : x₁ ≠ x₂ := by
    rintro rfl
    rw [hx₁] at hx₂
    apply h12
    have := inv_injective hx₂
    linear_combination this
  obtain ⟨y₀, hy₁, hy₂, hcomp⟩ := n18_arc_through_inf hg hgs hx
  have hy₀C : ((g y₀ : ℂ) : ExtPlane) ∈ mobiusExt 0 1 1 (-a) '' C := by
    rw [hCg]
    exact Or.inl ⟨_, ⟨(y₀ : ℂ), Complex.ofReal_im y₀, rfl⟩, rfl⟩
  obtain ⟨p, hpC, hTp⟩ := hy₀C
  have hS : mobiusExt 0 1 1 (-a) '' (C \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) =
      (toExt (g '' realLine) ∪ {extInf}) \ {((g x₁ : ℂ) : ExtPlane), ((g x₂ : ℂ) : ExtPlane)} := by
    rw [image_sdiff hTi, image_pair, hTz z₁ h1a, hTz z₂ h2a, ← hx₁, ← hx₂, hCg]
  have hp : p ∈ C \ {(z₁ : ExtPlane), (z₂ : ExtPlane)} := by
    refine ⟨hpC, ?_⟩
    rintro (h | h)
    · apply hy₁
      apply Complex.ofReal_injective
      apply hginj
      have h' := congrArg (mobiusExt 0 1 1 (-a)) h
      rw [hTp, hTz z₁ h1a, ← hx₁] at h'
      exact OnePoint.coe_injective h'
    · apply hy₂
      apply Complex.ofReal_injective
      apply hginj
      have h' := congrArg (mobiusExt 0 1 1 (-a)) h
      rw [hTp, hTz z₂ h2a, ← hx₂] at h'
      exact OnePoint.coe_injective h'
  refine ⟨p, hp, fun w hw => ?_⟩
  have hTw := hTc.continuousOn.mapsTo_connectedComponentIn hp hw
  rw [hS, hTp] at hTw
  obtain ⟨v, hv, hvle⟩ := hcomp _ hTw
  have hwa : w ≠ a := by
    rintro rfl
    rw [hTa] at hv
    exact OnePoint.coe_ne_infty v hv.symm
  rw [hTz w hwa] at hv
  have hv' : (w - a)⁻¹ = v := OnePoint.coe_injective hv
  rw [← hv', hx₁, hx₂] at hvle
  exact n18_inv_algebra hwa h1a h2a hvle

/-- A set of points within `R` of a centre `c` has diameter at most `M` whenever `2R ≤ M`. -/
theorem n18_ediam_le_of_center {S : Set ℂ} {c : ℂ} {R M : ℝ} (hRM : 2 * R ≤ M)
    (h : ∀ w ∈ S, ‖w - c‖ ≤ R) : Metric.ediam S ≤ ENNReal.ofReal M := by
  refine Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_
  rw [dist_eq_norm]
  have hx' := h x hx
  have hy' := h y hy
  have := norm_sub_le_norm_sub_add_norm_sub x c y
  rw [norm_sub_rev c y] at this
  linarith

/-- **Theorem 18.1** (necessity): a `K`-quasicircle is of `M`-bounded turning with `M` depending
only on `K` (one may take `M = 2e^{Kπ}` for curves in the plane). -/
theorem thm18_1_boundedTurning_of_quasicircle {K : ℝ} (hK : 1 ≤ K) :
    ∃ M : ℝ, ∀ C : Set ExtPlane, IsKQuasicircle C K → extInf ∉ C → IsBoundedTurning C M := by
  have hL := td_one_le_lambdaInv hK
  refine ⟨6 * lambdaInv K, fun C hC hinf => ⟨n18_isJordanCurve hC, by linarith, ?_⟩⟩
  intro z₁ z₂ hz₁ hz₂ hne
  have hd : 0 < ‖z₁ - z₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hnotinf : ∀ p, extInf ∉ connectedComponentIn (C \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) p :=
    fun p h => hinf (connectedComponentIn_subset _ _ h).1
  by_cases hfar : ∃ a : ℂ, (a : ExtPlane) ∈ C ∧ 2 * lambdaInv K * ‖z₁ - z₂‖ ≤ ‖z₂ - a‖
  · obtain ⟨a, ha, had⟩ := hfar
    have h2a : z₂ ≠ a := by
      rintro rfl
      rw [sub_self, norm_zero] at had
      nlinarith
    have h1a : z₁ ≠ a := by
      rintro rfl
      rw [norm_sub_rev z₂ z₁] at had
      nlinarith
    obtain ⟨p, hp, hbound⟩ := n18_cross hC hz₁ hz₂ ha hne h1a h2a
    refine ⟨p, hp, hnotinf p, n18_ediam_le_of_center (c := z₁) (R := 3 * lambdaInv K * ‖z₁ - z₂‖)
      (by linarith) fun w hw => ?_⟩
    have hw' := hbound w hw
    have hDpos : 0 < ‖z₂ - a‖ := by nlinarith
    have htri : ‖w - a‖ ≤ ‖w - z₁‖ + ‖z₁ - z₂‖ + ‖z₂ - a‖ := by
      have t1 := norm_sub_le_norm_sub_add_norm_sub w z₁ a
      have t2 := norm_sub_le_norm_sub_add_norm_sub z₁ z₂ a
      linarith
    have hX := norm_nonneg (w - z₁)
    have hLd : 0 ≤ lambdaInv K * ‖z₁ - z₂‖ := by positivity
    have k1 : ‖w - z₁‖ * ‖z₂ - a‖ ≤
        lambdaInv K * ‖z₁ - z₂‖ * (‖w - z₁‖ + ‖z₁ - z₂‖ + ‖z₂ - a‖) :=
      hw'.trans (mul_le_mul_of_nonneg_left htri hLd)
    have k2 : ‖w - z₁‖ * (2 * lambdaInv K * ‖z₁ - z₂‖) ≤ ‖w - z₁‖ * ‖z₂ - a‖ :=
      mul_le_mul_of_nonneg_left had hX
    have k3 : ‖z₁ - z₂‖ * (2 * lambdaInv K * ‖z₁ - z₂‖) ≤ ‖z₁ - z₂‖ * ‖z₂ - a‖ :=
      mul_le_mul_of_nonneg_left had hd.le
    have key : ‖w - z₁‖ * ‖z₂ - a‖ ≤ (‖z₁ - z₂‖ + 2 * lambdaInv K * ‖z₁ - z₂‖) * ‖z₂ - a‖ := by
      nlinarith
    have hX' : ‖w - z₁‖ ≤ ‖z₁ - z₂‖ + 2 * lambdaInv K * ‖z₁ - z₂‖ :=
      le_of_mul_le_mul_right key hDpos
    nlinarith
  · push Not at hfar
    obtain ⟨p, hpC, hp1, hp2⟩ := n18_exists_third hC (z₁ : ExtPlane) (z₂ : ExtPlane)
    refine ⟨p, ⟨hpC, ?_⟩, hnotinf p, n18_ediam_le_of_center (c := z₂) (R := 2 * lambdaInv K * ‖z₁ - z₂‖)
      (by nlinarith) fun w hw => ?_⟩
    · rintro (h | h)
      exacts [hp1 h, hp2 h]
    rw [norm_sub_rev]
    exact (hfar w (connectedComponentIn_subset _ _ hw).1).le

/-! ### Theorem 18.1 (sufficiency) (s21u stage BT, coordinator 553e2d)

The route is the modulus-only route of the s21u scout U1 (§4.5).  For a Jordan curve `C ∋ ∞` of bounded turning,
uniformize the complementary components by `φ : A₁ → ℍ`, `ψ : A₂ → 𝕃` fixing `∞` (`s18v_Setup`) and show that the
welding `h = ψ ∘ φ⁻¹` is `ρ(M)`-quasisymmetric; the Beurling–Ahlfors extension and the welding construction
(`wd_backward`, `wd_glue`) then make `C` a `K(M)`-quasicircle.  Quasisymmetry compares
`Q₁ = A₁(∞, z(x-t), z(x), z(x+t))` (modulus `Λ(1) = 1`) with `Q₂ = A₂(∞, z(x+t), z(x), z(x-t))` (modulus `Λ(ρ)`,
`ρ` the reciprocal of the ratio (17.2)): the two quadrilaterals have the same four sides (arcs of `C`), an annulus
metric compares the distances between opposite sides, and a disc metric then bounds `M(Q₂)^{±1}`.  A curve not
through `∞` is first moved by `w ↦ 1/(w - a)`, `a ∈ C`, at the cost `M ↦ (M + 1)²` in the three-point constant.

The main pieces are `s18v_components`, `s18v_weld_homeo`, `s18v_or_loop`, `s18v_weld_strictMono` (the welding is
increasing: an orientation fact the moduli cannot see), `s18v_arc_props`, `s18v_quads`, `s18v_annulus_bound`,
`s18v_disc_bound`, `s18v_moduli_bound`, `s18v_threePoint_of_bt` and `s18v_threePoint_mobius`. -/

/-- The uniformization of a Jordan curve `C ∋ ∞` (the hypotheses of Theorem 16.3 and of `wd_backward`): `A₁, A₂ ⊆ ℂ`
are the complementary components, `φ : A₁ → ℍ` and `ψ : A₂ → 𝕃` are conformal with homeomorphic extensions `Φ, Ψ`
fixing `∞`, and `h` is the welding (`Φ z = x`, `Ψ z = h x` at the finite points `z ∈ C`). -/
def s18v_Setup (C : Set ExtPlane) (A₁ A₂ : Set ℂ) (φ ψ : ℂ → ℂ) (Φ Ψ : ExtPlane → ExtPlane) (h : ℝ → ℝ) :
    Prop :=
  extInf ∈ C ∧ AreComplementaryComponents C (toExt A₁) (toExt A₂) ∧ IsConformalOnto φ A₁ upperHalf ∧
    IsConformalOnto ψ A₂ lowerHalf ∧ IsHomeoExtension φ A₁ upperHalf Φ ∧ IsHomeoExtension ψ A₂ lowerHalf Ψ ∧
    Φ extInf = extInf ∧ Ψ extInf = extInf ∧
    ∀ z : ℂ, (z : ExtPlane) ∈ C → ∃ x : ℝ, Φ z = ((x : ℂ) : ExtPlane) ∧ Ψ z = (((h x : ℝ) : ℂ) : ExtPlane)

/-- The three-point condition along `C` in the order of `Φ`: for finite `z₁, w, z₂ ∈ C` whose `Φ`-coordinates are reals
`u < s < v`, `|w - z₁| ≤ M |z₁ - z₂|`. -/
def s18v_ThreePoint (C : Set ExtPlane) (Φ : ExtPlane → ExtPlane) (M : ℝ) : Prop :=
  ∀ z₁ w z₂ : ℂ, (z₁ : ExtPlane) ∈ C → (w : ExtPlane) ∈ C → (z₂ : ExtPlane) ∈ C → ∀ u s v : ℝ,
    Φ z₁ = ((u : ℂ) : ExtPlane) → Φ w = ((s : ℂ) : ExtPlane) → Φ z₂ = ((v : ℂ) : ExtPlane) → u < s → s < v →
      ‖w - z₁‖ ≤ M * ‖z₁ - z₂‖

/-- The finite points of `C` whose `Φ`-coordinate is a real number in `I` (an arc of `C` when `I` is an interval). -/
def s18v_arc (C : Set ExtPlane) (Φ : ExtPlane → ExtPlane) (I : Set ℝ) : Set ℂ :=
  {z : ℂ | (z : ExtPlane) ∈ C ∧ ∃ s ∈ I, Φ z = ((s : ℂ) : ExtPlane)}

/-- The bound `π ((1 + e^{2π}) M² + 1)²` for `M(Q₂)^{±1}` (step (ii) of `s18v_moduli_bound`). -/
def s18v_B (M : ℝ) : ℝ := π * ((1 + Real.exp (2 * π)) * M ^ 2 + 1) ^ 2

/-- The quasisymmetry constant `λ(B(M))` of the welding. -/
def s18v_rho (M : ℝ) : ℝ := lambdaInv (s18v_B M)

/-- The quasicircle constant `8ρ(ρ + 1)` of the Beurling–Ahlfors extension (Theorem 17.2), `ρ = s18v_rho M`. -/
def s18v_K (M : ℝ) : ℝ := 8 * s18v_rho M * (s18v_rho M + 1)

/-! #### The uniformization of a Jordan curve through `∞` -/

/-- A Jordan curve `C ∋ ∞` misses some finite point: otherwise `C = ℂ̄`, its parametrization `γ` is a homeomorphism
from the circle, and `γ⁻¹` would inject `ℂ` continuously into the unit circle, whose interior in `ℂ` is empty,
against invariance of domain (`isOpen_image_of_continuousOn_injOn`). -/
theorem s18v_c_exists_finite_notMem {C : Set ExtPlane} (hC : IsJordanCurve C) (hinf : extInf ∈ C) :
    ∃ b : ℂ, (b : ExtPlane) ∉ C := by
  by_contra hcon
  push Not at hcon
  obtain ⟨γ, hγc, hγi, hγr⟩ := hC
  have hsurj : Function.Surjective γ := by
    intro p
    have hp : p ∈ C := by
      rcases uq_j_eq_infty_or_coe p with rfl | ⟨z, rfl⟩
      · exact hinf
      · exact hcon z
    rw [← hγr] at hp
    exact hp
  set e : Circle ≃ₜ ExtPlane := hγc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective γ ⟨hγi, hsurj⟩)
  set f : ℂ → ℂ := fun z => ((e.symm (z : ExtPlane) : Circle) : ℂ)
  have hfc : Continuous f := continuous_subtype_val.comp (e.symm.continuous.comp OnePoint.continuous_coe)
  have hfi : Function.Injective f := fun a b hab =>
    OnePoint.coe_injective (e.symm.injective (Circle.coe_injective hab))
  have hopen : IsOpen (f '' univ) := isOpen_image_of_continuousOn_injOn isOpen_univ hfc.continuousOn hfi.injOn
  have hsub : f '' univ ⊆ sphere (0 : ℂ) 1 := by
    rintro _ ⟨z, -, rfl⟩
    rw [mem_sphere_zero_iff_norm]
    exact Circle.norm_coe _
  have hint := interior_maximal hsub hopen
  rw [interior_sphere (0 : ℂ) one_ne_zero] at hint
  exact hint ⟨0, mem_univ 0, rfl⟩

/-- The complement of a Jordan curve `C ∋ ∞` has two components, both contained in `ℂ`.

*Truth.*  This is the Jordan curve theorem on the sphere.  Pick a finite `b ∉ C`: such a point exists, because a
Jordan curve is not all of `ℂ̄` (otherwise `γ⁻¹ ∘ (↑)` would inject `ℂ` continuously into the unit circle, whose
interior in `ℂ` is empty, against invariance of domain).  `T = mobiusHomeomorph 0 1 1 (-b)` sends `b` to `∞`, so
`T(C) = toExt C₀` with `C₀ ⊆ ℂ` a Jordan curve.  The Jordan curve theorem gives the bounded piece `A` and the
unbounded piece `B`.  The components of `T(C)ᶜ` in `ℂ̄` are `toExt A` and `toExt B ∪ {∞}`; the latter is connected
because `∞ ∈ closure (toExt B)`.  Their preimages under `T` avoid `∞`, because `T ∞ = 0 ∈ C₀`, so they are `toExt A₁`
and `toExt A₂` for some `A₁, A₂ ⊆ ℂ`.  Both are nonempty and different.

*Route.*
- the Möbius move and the component bookkeeping of `s16p_frontier_eq` (S16:1193): `uq_j_toExt_preimage_coe`,
  `uq_isJordanCurve_image`, `gsep_z_connectedComponentIn_image_homeomorph`;
- `jordan_curve_theorem_complex_bounded` (JordanBridge:185), `extInf_mem_closure_toExt_of_not_isBounded`
  (ExpStripLift:329);
- for `b ∉ C`: `isOpen_image_of_continuousOn_injOn` (InvarianceOfDomain:378). -/
theorem s18v_components {C : Set ExtPlane} (hC : IsJordanCurve C) (hinf : extInf ∈ C) :
    ∃ A₁ A₂ : Set ℂ, AreComplementaryComponents C (toExt A₁) (toExt A₂) := by
  obtain ⟨b, hb⟩ := s18v_c_exists_finite_notMem hC hinf
  set T := mobiusHomeomorph 0 1 1 (-b) (uq_j_inv_det b)
  have hTb : T (b : ExtPlane) = extInf := uq_j_mobiusInv_apply_self b
  have hinfTC : extInf ∉ T '' C := by
    rintro ⟨c, hc, hce⟩
    rw [← hTb] at hce
    rw [T.injective hce] at hc
    exact hb hc
  set C₀ : Set ℂ := ((↑) : ℂ → ExtPlane) ⁻¹' (T '' C)
  have hC₀e : toExt C₀ = T '' C := uq_j_toExt_preimage_coe hinfTC
  have hJ₀ : IsJordanCurve (toExt C₀) := by
    rw [hC₀e]
    exact uq_isJordanCurve_image T hC
  obtain ⟨A, B, hA, hB, hAc, hBc, hAB, hAC, hBC, huniv, hAb, -⟩ := jordan_curve_theorem_complex_bounded hJ₀
  obtain ⟨a, ha⟩ := hAc.nonempty
  obtain ⟨b', hb'⟩ := hBc.nonempty
  -- `(T '' C)ᶜ` is covered by the disjoint open sets `toExt A` and `(toExt (A ∪ C₀))ᶜ`
  have hK : IsCompact (A ∪ C₀) := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ (hAb.union (isCompact_of_isJordanCurve_toExt hJ₀).isBounded)
    have hcompl : (A ∪ C₀)ᶜ = B := by
      ext z
      constructor
      · intro hz
        have hz' : z ∈ A ∪ B ∪ C₀ := huniv ▸ mem_univ z
        rcases hz' with (h' | h') | h'
        · exact absurd (Or.inl h') hz
        · exact h'
        · exact absurd (Or.inr h') hz
      · rintro hz (h' | h')
        · exact disjoint_left.1 hAB h' hz
        · exact disjoint_left.1 hBC hz h'
    rw [← isOpen_compl_iff, hcompl]
    exact hB
  set U : Set ExtPlane := toExt A with hU
  set V : Set ExtPlane := (toExt (A ∪ C₀))ᶜ with hV
  have hUo : IsOpen U := OnePoint.isOpen_image_coe.2 hA
  have hVo : IsOpen V := OnePoint.isOpen_compl_image_coe.2 ⟨hK.isClosed, hK⟩
  have hUV : Disjoint U V := by
    rw [hU, hV, disjoint_compl_right_iff_subset]
    exact image_mono subset_union_left
  have hcov : (T '' C)ᶜ ⊆ U ∪ V := by
    intro p hp
    by_cases hpK : p ∈ toExt (A ∪ C₀)
    · obtain ⟨z, hz, rfl⟩ := hpK
      rcases hz with hz | hz
      · exact Or.inl ⟨z, hz, rfl⟩
      · exact absurd (hC₀e ▸ ⟨z, hz, rfl⟩ : ((z : ℂ) : ExtPlane) ∈ T '' C) hp
    · exact Or.inr hpK
  -- pull back by `T`
  have hU'o : IsOpen (T ⁻¹' U) := hUo.preimage T.continuous
  have hV'o : IsOpen (T ⁻¹' V) := hVo.preimage T.continuous
  have hU'V' : Disjoint (T ⁻¹' U) (T ⁻¹' V) := hUV.preimage T
  have hcov' : Cᶜ ⊆ T ⁻¹' U ∪ T ⁻¹' V := fun q hq =>
    hcov fun ⟨c, hc, hce⟩ => hq (T.injective hce ▸ hc)
  set p₁ := T.symm (a : ExtPlane)
  set p₂ := T.symm (b' : ExtPlane)
  have hTp₁ : T p₁ = (a : ExtPlane) := T.apply_symm_apply _
  have hTp₂ : T p₂ = (b' : ExtPlane) := T.apply_symm_apply _
  have hp₁C : p₁ ∈ Cᶜ := fun h' => by
    have h2 : (a : ExtPlane) ∈ toExt C₀ := hC₀e ▸ hTp₁ ▸ mem_image_of_mem T h'
    exact disjoint_left.1 hAC ha (coe_mem_toExt_iff.1 h2)
  have hp₂C : p₂ ∈ Cᶜ := fun h' => by
    have h2 : (b' : ExtPlane) ∈ toExt C₀ := hC₀e ▸ hTp₂ ▸ mem_image_of_mem T h'
    exact disjoint_left.1 hBC hb' (coe_mem_toExt_iff.1 h2)
  have hcomp : connectedComponentIn Cᶜ p₁ ⊆ T ⁻¹' U :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union hU'o hV'o hU'V'
      ((connectedComponentIn_subset _ _).trans hcov')
      ⟨p₁, mem_connectedComponentIn hp₁C, show T p₁ ∈ U by rw [hTp₁]; exact ⟨a, ha, rfl⟩⟩
  have hp₂U : p₂ ∉ T ⁻¹' U := fun h' => by
    have h2 : T p₂ ∈ toExt A := h'
    rw [hTp₂] at h2
    exact disjoint_left.1 hAB (coe_mem_toExt_iff.1 h2) hb'
  have hne : connectedComponentIn Cᶜ p₁ ≠ connectedComponentIn Cᶜ p₂ := fun h' =>
    hp₂U (hcomp (h' ▸ mem_connectedComponentIn hp₂C))
  have hinf' : ∀ p, extInf ∉ connectedComponentIn Cᶜ p := fun p h' => connectedComponentIn_subset _ _ h' hinf
  refine ⟨((↑) : ℂ → ExtPlane) ⁻¹' connectedComponentIn Cᶜ p₁, ((↑) : ℂ → ExtPlane) ⁻¹' connectedComponentIn Cᶜ p₂,
    hC, p₁, hp₁C, p₂, hp₂C, uq_j_toExt_preimage_coe (hinf' p₁), uq_j_toExt_preimage_coe (hinf' p₂), ?_⟩
  rw [uq_j_toExt_preimage_coe (hinf' p₁), uq_j_toExt_preimage_coe (hinf' p₂)]
  exact hne

/-- A local copy of `s20l_uw_real_point` (S20, downstream): a finite boundary point `z ∉ U` of `U` is sent to a real
point by a homeomorphic extension `F`, fixing `∞`, of a conformal map of `U` onto `ℍ` or `𝕃`. -/
theorem s18v_real_point {f : ℂ → ℂ} {U V : Set ℂ} {F : ExtPlane → ExtPlane} (hF : IsHomeoExtension f U V F)
    (hfUV : f '' U = V) (hV : V = upperHalf ∨ V = lowerHalf) (hFinf : F extInf = extInf)
    (hinfU : extInf ∈ closure (toExt U)) {z : ℂ} (hz : (z : ExtPlane) ∈ closure (toExt U)) (hzU : z ∉ U) :
    ∃ x : ℝ, F z = ((x : ℂ) : ExtPlane) := by
  have hFz : F z ∈ closure (toExt V) := hF.2.2.2 ▸ mem_image_of_mem F hz
  have hni : F z ≠ extInf := fun h => OnePoint.coe_ne_infty z (hF.2.2.1 hz hinfU (h.trans hFinf.symm))
  have hnV : ∀ v ∈ V, F z ≠ (v : ExtPlane) := by
    intro v hv h
    rw [← hfUV] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [← hF.1 u hu] at h
    have hzu : (z : ExtPlane) = (u : ExtPlane) := hF.2.2.1 hz (subset_closure ⟨u, hu, rfl⟩) h
    exact hzU (OnePoint.coe_injective hzu ▸ hu)
  rcases wd_b_cases (F z) with h | ⟨x, h⟩ | ⟨w, hw, h⟩ | ⟨w, hw, h⟩
  · exact absurd h hni
  · exact ⟨x, h⟩
  · rcases hV with rfl | rfl
    · exact absurd h (hnV w hw)
    · exact (disjoint_left.1 wd_b_closure_lower_disjoint hFz ⟨w, hw, h.symm⟩).elim
  · rcases hV with rfl | rfl
    · exact (disjoint_left.1 wd_b_closure_upper_disjoint hFz ⟨w, hw, h.symm⟩).elim
    · exact absurd h (hnV w hw)

/-- A complementary component `A₁` of a Jordan curve `C ∋ ∞` is a Jordan domain with `∞` on its boundary
(`s16p_basic`, `s16p_frontier_eq`). -/
theorem s18v_isJordanDomain {C : Set ExtPlane} {A₁ A₂ : Set ℂ}
    (hC : AreComplementaryComponents C (toExt A₁) (toExt A₂)) (hinf : extInf ∈ C) :
    IsJordanDomain A₁ ∧ extInf ∈ frontier (toExt A₁) := by
  obtain ⟨-, hA₁o, -, hA₁c, -, -, -⟩ := s16p_basic hC
  have hfr : frontier (toExt A₁) = C := s16p_frontier_eq hC hinf
  obtain ⟨p, hp⟩ := hA₁c.nonempty
  obtain ⟨z, hz, -⟩ := hp
  refine ⟨⟨OnePoint.isOpen_image_coe.1 hA₁o, ⟨⟨z, hz⟩, ?_⟩, hfr ▸ hC.1⟩, hfr ▸ hinf⟩
  exact OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image.1 hA₁c.isPreconnected

/-- A Jordan domain with `∞` on its boundary has a conformal map onto `𝕃` whose homeomorphic extension fixes `∞`
(`s16p_uniformizer_inf` followed by `z ↦ -z`; the second half of `s20l_uniformizers`, S20, downstream). -/
theorem s18v_uniformizer_lower {Ω : Set ℂ} (hΩ : IsJordanDomain Ω) (hinf : extInf ∈ frontier (toExt Ω)) :
    ∃ ψ : ℂ → ℂ, IsConformalOnto ψ Ω lowerHalf ∧
      ∃ Ψ : ExtPlane → ExtPlane, IsHomeoExtension ψ Ω lowerHalf Ψ ∧ Ψ extInf = extInf := by
  obtain ⟨ψ₀, hψ₀, Ψ₀, hΨ₀, hΨ₀inf⟩ := s16p_uniformizer_inf hΩ hinf
  have hnU : (Homeomorph.neg ℂ) '' upperHalf = lowerHalf :=
    wd_n_neg_image fun z => by
      show (-z).im < 0 ↔ 0 < z.im
      rw [neg_im, neg_lt_zero]
  have hnc : IsConformalOnto (Homeomorph.neg ℂ) upperHalf lowerHalf :=
    ⟨(differentiable_id.neg : Differentiable ℂ fun z : ℂ => -z).differentiableOn,
      (Homeomorph.neg ℂ).injective.injOn, hnU⟩
  have hne : IsHomeoExtension (Homeomorph.neg ℂ) upperHalf lowerHalf (Homeomorph.neg ℂ).onePointCongr := by
    have h1 := s13x_de_isHomeoExtension_homeomorph (Homeomorph.neg ℂ) upperHalf
    rwa [hnU] at h1
  refine ⟨_, hnc.comp hψ₀, _, hne.comp hΨ₀ hψ₀.mapsTo, ?_⟩
  show (Homeomorph.neg ℂ).onePointCongr (Ψ₀ extInf) = extInf
  rw [hΨ₀inf]
  rfl

/-- The welding exists: for uniformizers `φ : A₁ → ℍ`, `ψ : A₂ → 𝕃` fixing `∞` of the complementary components of
`C ∋ ∞`, every finite `z ∈ C` has real coordinates `Φ z = x`, `Ψ z = h x` with `h x = Re Ψ(Φ⁻¹ x)` (the key step of
`s20l_welding_qs`, S20, downstream). -/
theorem s18v_welding {C : Set ExtPlane} {A₁ A₂ : Set ℂ} (hinf : extInf ∈ C)
    (hC : AreComplementaryComponents C (toExt A₁) (toExt A₂)) {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    (hφ : IsConformalOnto φ A₁ upperHalf) (hψ : IsConformalOnto ψ A₂ lowerHalf)
    (hΦ : IsHomeoExtension φ A₁ upperHalf Φ) (hΨ : IsHomeoExtension ψ A₂ lowerHalf Ψ)
    (hΦinf : Φ extInf = extInf) (hΨinf : Ψ extInf = extInf) :
    ∃ h : ℝ → ℝ, ∀ z : ℂ, (z : ExtPlane) ∈ C →
      ∃ x : ℝ, Φ z = ((x : ℂ) : ExtPlane) ∧ Ψ z = (((h x : ℝ) : ℂ) : ExtPlane) := by
  obtain ⟨hJ, p₁, hp₁, p₂, hp₂, h₁, h₂, -⟩ := hC
  have hfr₁ : frontier (toExt A₁) = C := wd_frontier_eq hJ ⟨p₁, hp₁, h₁⟩ (Or.inl rfl) hφ hΦ
  have hfr₂ : frontier (toExt A₂) = C := wd_frontier_eq hJ ⟨p₂, hp₂, h₂⟩ (Or.inr rfl) hψ hΨ
  have hcl₁ : C ⊆ closure (toExt A₁) := hfr₁ ▸ frontier_subset_closure
  have hcl₂ : C ⊆ closure (toExt A₂) := hfr₂ ▸ frontier_subset_closure
  have hnot : ∀ (A : Set ℂ) (p : ExtPlane), toExt A = connectedComponentIn Cᶜ p →
      ∀ z : ℂ, (z : ExtPlane) ∈ C → z ∉ A := by
    intro A p hA z hz hzA
    have hmem : (z : ExtPlane) ∈ connectedComponentIn Cᶜ p := hA ▸ ⟨z, hzA, rfl⟩
    exact connectedComponentIn_subset _ _ hmem hz
  refine ⟨fun x => (extToC (Ψ (Function.invFunOn Φ (closure (toExt A₁)) ((x : ℂ) : ExtPlane)))).re,
    fun z hz => ?_⟩
  obtain ⟨x, hx⟩ :=
    s18v_real_point hΦ hφ.2.2 (Or.inl rfl) hΦinf (hcl₁ hinf) (hcl₁ hz) (hnot A₁ p₁ h₁ z hz)
  obtain ⟨y, hy⟩ :=
    s18v_real_point hΨ hψ.2.2 (Or.inr rfl) hΨinf (hcl₂ hinf) (hcl₂ hz) (hnot A₂ p₂ h₂ z hz)
  refine ⟨x, hx, ?_⟩
  have hinv : Function.invFunOn Φ (closure (toExt A₁)) ((x : ℂ) : ExtPlane) = (z : ExtPlane) := by
    rw [← hx]
    exact hΦ.2.2.1.leftInvOn_invFunOn (hcl₁ hz)
  have hwx : (extToC (Ψ (Function.invFunOn Φ (closure (toExt A₁)) ((x : ℂ) : ExtPlane)))).re = y := by
    rw [hinv, hy]
    exact Complex.ofReal_re y
  show Ψ z = ((((extToC (Ψ (Function.invFunOn Φ (closure (toExt A₁)) ((x : ℂ) : ExtPlane)))).re : ℝ) : ℂ) :
    ExtPlane)
  rw [hwx, hy]

/-- Every Jordan curve through `∞` carries the data `s18v_Setup` (`s18v_components`, `s16p_uniformizer_inf`,
`s18v_uniformizer_lower`, `s18v_welding`). -/
theorem s18v_setup_exists {C : Set ExtPlane} (hJ : IsJordanCurve C) (hinf : extInf ∈ C) :
    ∃ (A₁ A₂ : Set ℂ) (φ ψ : ℂ → ℂ) (Φ Ψ : ExtPlane → ExtPlane) (h : ℝ → ℝ),
      s18v_Setup C A₁ A₂ φ ψ Φ Ψ h := by
  obtain ⟨A₁, A₂, hC⟩ := s18v_components hJ hinf
  have hC' : AreComplementaryComponents C (toExt A₂) (toExt A₁) := by
    obtain ⟨hJ', p₁, hp₁, p₂, hp₂, h₁, h₂, hne⟩ := hC
    exact ⟨hJ', p₂, hp₂, p₁, hp₁, h₂, h₁, hne.symm⟩
  obtain ⟨hD₁, hi₁⟩ := s18v_isJordanDomain hC hinf
  obtain ⟨hD₂, hi₂⟩ := s18v_isJordanDomain hC' hinf
  obtain ⟨φ, hφ, Φ, hΦ, hΦinf⟩ := s16p_uniformizer_inf hD₁ hi₁
  obtain ⟨ψ, hψ, Ψ, hΨ, hΨinf⟩ := s18v_uniformizer_lower hD₂ hi₂
  obtain ⟨h, hh⟩ := s18v_welding hinf hC hφ hψ hΦ hΨ hΦinf hΨinf
  exact ⟨A₁, A₂, φ, ψ, Φ, Ψ, h, hinf, hC, hφ, hψ, hΦ, hΨ, hΦinf, hΨinf, hh⟩

/-! #### The welding is an increasing homeomorphism of `ℝ` -/

/-- A homeomorphic extension `F`, fixing `∞`, of a conformal map `f` of a complementary component `A` (with
`∂A = C`) onto `ℍ` or `𝕃` pulls every real point `x` back to a finite point `z` of `C` with `F z = x`. -/
theorem s18v_c_preimage_real {C : Set ExtPlane} {A V : Set ℂ} {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hfr : frontier (toExt A) = C) (hAo : IsOpen A) (hV : V = upperHalf ∨ V = lowerHalf)
    (hf : IsConformalOnto f A V) (hF : IsHomeoExtension f A V F) (hFinf : F extInf = extInf) (x : ℝ) :
    ∃ z : ℂ, (z : ExtPlane) ∈ C ∧ Function.invFunOn F (closure (toExt A)) ((x : ℂ) : ExtPlane) = z ∧
      F z = ((x : ℂ) : ExtPlane) := by
  have hxV : (x : ℂ) ∉ V := by
    rcases hV with rfl | rfl
    · exact fun h' => by simp [upperHalf] at h'
    · exact fun h' => by simp [lowerHalf] at h'
  have hxcl : ((x : ℂ) : ExtPlane) ∈ F '' closure (toExt A) := by
    rw [hF.2.2.2]
    rcases hV with rfl | rfl
    · exact wd_b_real_mem_closure_upper x
    · exact wd_b_real_mem_closure_lower x
  have hpmem := Function.invFunOn_mem hxcl
  have hpx := Function.invFunOn_eq hxcl
  obtain ⟨z, hz⟩ : ∃ z : ℂ, Function.invFunOn F (closure (toExt A)) ((x : ℂ) : ExtPlane) = z := by
    rcases uq_j_eq_infty_or_coe (Function.invFunOn F (closure (toExt A)) ((x : ℂ) : ExtPlane)) with h' | h'
    · rw [h', hFinf] at hpx
      exact absurd hpx (OnePoint.infty_ne_coe _)
    · exact h'
  rw [hz] at hpmem hpx
  have hzA : z ∉ A := by
    intro hzA
    rw [hF.1 z hzA] at hpx
    exact hxV (OnePoint.coe_injective hpx ▸ hf.2.2 ▸ mem_image_of_mem f hzA)
  refine ⟨z, ?_, hz, hpx⟩
  rw [← hfr]
  refine ⟨hpmem, ?_⟩
  have hAo' : IsOpen (toExt A) := OnePoint.isOpen_image_coe.2 hAo
  rw [hAo'.interior_eq]
  exact fun h' => hzA (coe_mem_toExt_iff.1 h')

/-- The frontier facts of `s18v_Setup`: both components are open with frontier `C`. -/
theorem s18v_c_frontiers {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    {h : ℝ → ℝ} (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) :
    IsOpen A₁ ∧ IsOpen A₂ ∧ frontier (toExt A₁) = C ∧ frontier (toExt A₂) = C := by
  obtain ⟨-, hC, hφ, hψ, hΦ, hΨ, -, -, -⟩ := hS
  obtain ⟨-, hA₁o, hA₂o, -, -, -, -⟩ := s16p_basic hC
  obtain ⟨hJ, p₁, hp₁, p₂, hp₂, h₁, h₂, -⟩ := hC
  exact ⟨OnePoint.isOpen_image_coe.1 hA₁o, OnePoint.isOpen_image_coe.1 hA₂o,
    wd_frontier_eq hJ ⟨p₁, hp₁, h₁⟩ (Or.inl rfl) hφ hΦ, wd_frontier_eq hJ ⟨p₂, hp₂, h₂⟩ (Or.inr rfl) hψ hΨ⟩

/-- For a real `x`, `Φ⁻¹ x` is a finite point `z` of `C` with `Φ z = x` and `Ψ z = h x`. -/
theorem s18v_c_inv_real {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    {h : ℝ → ℝ} (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) (x : ℝ) :
    ∃ z : ℂ, (z : ExtPlane) ∈ C ∧ Function.invFunOn Φ (closure (toExt A₁)) ((x : ℂ) : ExtPlane) = z ∧
      Φ z = ((x : ℂ) : ExtPlane) ∧ Ψ z = (((h x : ℝ) : ℂ) : ExtPlane) := by
  obtain ⟨hA₁o, -, hfr₁, -⟩ := s18v_c_frontiers hS
  obtain ⟨-, -, hφ, -, hΦ, -, hΦinf, -, hw⟩ := hS
  obtain ⟨z, hzC, hz, hzx⟩ := s18v_c_preimage_real hfr₁ hA₁o (Or.inl rfl) hφ hΦ hΦinf x
  obtain ⟨x', hx'1, hx'2⟩ := hw z hzC
  have hxx : x' = x := Complex.ofReal_injective (OnePoint.coe_injective (hx'1.symm.trans hzx))
  subst hxx
  exact ⟨z, hzC, hz, hzx, hx'2⟩

/-- The welding `h` of `s18v_Setup` is a continuous bijection of `ℝ`.

*Truth.*  Fix a real `x`.  `Φ` maps `closure (toExt A₁)` homeomorphically onto `closure (toExt ℍ)` and `∂A₁ = C` onto
`∂ℍ = ℝ ∪ {∞}` (`IsHomeoExtension.image_frontier`, `wd_frontier_eq`).  With `Φ ∞ = ∞`, `z = Φ⁻¹ x` is therefore a
finite point of `C`, and the last clause of the setup forces `Ψ z = h x`.  So `h = Re ∘ extToC ∘ Ψ ∘ Φ⁻¹` on `ℝ`:
- it is continuous: `Φ⁻¹` is continuous on `closure ℍ` (`isHomeoExtension_invFunOn`), `Ψ` on `closure A₂ ⊇ C`, and
  `extToC` at finite points;
- it is injective, because `Ψ` and `Φ⁻¹` are;
- it is surjective: for real `y`, `Ψ⁻¹ y` is a finite point `z` of `C`, and the setup at `z` gives `h (Φ z) = y`.

*Route.*  `isHomeoExtension_invFunOn` (ImageQuad:63), `IsHomeoExtension.image_frontier` (Quadrilateral),
`wd_frontier_eq` (S16:1887), `s16p_continuousAt_extToC` (S16:1183), `s18v_real_point`. -/
theorem s18v_weld_homeo {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    {h : ℝ → ℝ} (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) :
    Continuous h ∧ Function.Injective h ∧ Function.Surjective h := by
  obtain ⟨-, hA₂o, -, hfr₂⟩ := s18v_c_frontiers hS
  have hinv := s18v_c_inv_real hS
  obtain ⟨-, -, hφ, hψ, hΦ, hΨ, -, hΨinf, hw⟩ := hS
  have hcl₂ : C ⊆ closure (toExt A₂) := hfr₂ ▸ frontier_subset_closure
  refine ⟨?_, ?_, ?_⟩
  · have hform : h = fun x : ℝ =>
        (extToC (Ψ (Function.invFunOn Φ (closure (toExt A₁)) ((x : ℂ) : ExtPlane)))).re := by
      funext x
      obtain ⟨z, -, hz, -, hzΨ⟩ := hinv x
      rw [hz, hzΨ]
      rfl
    rw [hform]
    have hc1 : Continuous fun x : ℝ => Function.invFunOn Φ (closure (toExt A₁)) ((x : ℂ) : ExtPlane) :=
      (isHomeoExtension_invFunOn hφ hΦ).2.1.comp_continuous
        (OnePoint.continuous_coe.comp Complex.continuous_ofReal) fun x => wd_b_real_mem_closure_upper x
    have hc2 : Continuous fun x : ℝ => Ψ (Function.invFunOn Φ (closure (toExt A₁)) ((x : ℂ) : ExtPlane)) := by
      refine hΨ.2.1.comp_continuous hc1 fun x => ?_
      obtain ⟨z, hzC, hz, -⟩ := hinv x
      rw [hz]
      exact hcl₂ hzC
    refine Complex.continuous_re.comp (continuous_iff_continuousAt.2 fun x => ?_)
    obtain ⟨z, -, hz, -, hzΨ⟩ := hinv x
    have hat : ContinuousAt extToC (Ψ (Function.invFunOn Φ (closure (toExt A₁)) ((x : ℂ) : ExtPlane))) := by
      rw [hz, hzΨ]
      exact s16p_continuousAt_extToC _
    exact ContinuousAt.comp (f := fun x : ℝ => Ψ (Function.invFunOn Φ (closure (toExt A₁)) ((x : ℂ) : ExtPlane)))
      (x := x) hat hc2.continuousAt
  · intro x y hxy
    obtain ⟨z, hzC, -, hzΦ, hzΨ⟩ := hinv x
    obtain ⟨w, hwC, -, hwΦ, hwΨ⟩ := hinv y
    have hzw : (z : ExtPlane) = w := hΨ.2.2.1 (hcl₂ hzC) (hcl₂ hwC) (by rw [hzΨ, hwΨ, hxy])
    rw [hzw, hwΦ] at hzΦ
    exact (Complex.ofReal_injective (OnePoint.coe_injective hzΦ)).symm
  · intro y
    obtain ⟨z, hzC, -, hzy⟩ := s18v_c_preimage_real hfr₂ hA₂o (Or.inr rfl) hψ hΨ hΨinf y
    obtain ⟨x, -, hx⟩ := hw z hzC
    exact ⟨x, Complex.ofReal_injective (OnePoint.coe_injective (hx.symm.trans hzy))⟩

/-- The unit-circle parametrization `t ↦ e^{2πit}` has modulus `1`. -/
theorem s18v_c_norm_circ (t : ℝ) : ‖Complex.exp (2 * π * I * t)‖ = 1 := by
  rw [Complex.norm_exp]
  have h0 : (2 * π * I * (t : ℂ)).re = 0 := by simp
  rw [h0, Real.exp_zero]

/-- The unit-circle parametrization is continuous. -/
theorem s18v_c_circ_cont : Continuous fun t : ℝ => Complex.exp (2 * π * I * t) := by
  fun_prop

/-- The unit-circle parametrization is closed: `e^{2πi·1} = e^{2πi·0}`. -/
theorem s18v_c_circ_one :
    Complex.exp (2 * π * I * ((1 : ℝ) : ℂ)) = Complex.exp (2 * π * I * ((0 : ℝ) : ℂ)) := by
  rw [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, Complex.exp_two_pi_mul_I]

/-- Reversing the unit-circle parametrization conjugates it: `e^{2πi(1-t)} = conj e^{2πit}`. -/
theorem s18v_c_circ_rev (t : ℝ) :
    Complex.exp (2 * π * I * ((1 - t : ℝ) : ℂ)) = conj (Complex.exp (2 * π * I * t)) := by
  rw [← Complex.exp_conj]
  have h1 : 2 * π * I * ((1 - t : ℝ) : ℂ) = 2 * π * I + conj (2 * π * I * (t : ℂ)) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  rw [h1, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]

/-- The circle `|z| = 2` has winding `+1` about `E i`, when `E` has local winding `+1` at `i`: shrink it to
`|z - i| = ε` through the circles of centre `s i` and radius `2(1 - s) + sε`, which avoid `i` (W3a). -/
theorem s18v_c_wind_two {E : ℂ → ℂ} (hE : Continuous E) (hEi : Function.Injective E)
    (h₁ : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = E (I + ρ * Complex.exp (2 * π * I * t)) - E I) →
      L 1 - L 0 = 2 * π * I)
    {L : ℝ → ℂ} (hL : ContinuousOn L (Icc 0 1))
    (hLe : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = E (2 * Complex.exp (2 * π * I * t)) - E I) :
    L 1 - L 0 = 2 * π * I := by
  obtain ⟨ρ₁, hρ₁, hl⟩ := h₁
  set ε : ℝ := min (ρ₁ / 2) 1
  have hε0 : 0 < ε := lt_min (by linarith) one_pos
  have hερ : ε < ρ₁ := (min_le_left _ _).trans_lt (by linarith)
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      ((1 - s : ℝ) : ℂ) * (2 * Complex.exp (2 * π * I * t)) +
        (s : ℂ) * (I + (ε : ℂ) * Complex.exp (2 * π * I * t)) ≠ I := by
    intro s hs t h
    have h2 : ((2 * (1 - s) + s * ε : ℝ) : ℂ) * Complex.exp (2 * π * I * t) = ((1 - s : ℝ) : ℂ) * I := by
      push_cast at h ⊢
      linear_combination h
    have h3 := congrArg norm h2
    rw [norm_mul, norm_mul, s18v_c_norm_circ, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by nlinarith [hs.1, hs.2]), Real.norm_of_nonneg (by linarith [hs.2])] at h3
    nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 hε1), hs.1, hs.2]
  have hc1 : ContinuousOn (fun t : ℝ => E (I + (ε : ℂ) * Complex.exp (2 * π * I * t))) (Icc 0 1) :=
    (hE.comp (continuous_const.add (continuous_const.mul s18v_c_circ_cont))).continuousOn
  obtain ⟨L₁, hL₁c, hL₁e⟩ := exists_continuousOn_log_lift (w := E I) hc1 fun t _ h => by
    have h' := hEi h
    have h'' : (ε : ℂ) * Complex.exp (2 * π * I * t) = 0 := by linear_combination h'
    rcases mul_eq_zero.1 h'' with h0 | h0
    · exact hε0.ne' (Complex.ofReal_eq_zero.1 h0)
    · exact Complex.exp_ne_zero _ h0
  have hwind := hl ε hε0 hερ L₁ hL₁c hL₁e
  rw [← hwind]
  refine lift_change_eq_of_homotopy (w := E I)
    (H := fun s t : ℝ => E (((1 - s : ℝ) : ℂ) * (2 * Complex.exp (2 * π * I * t)) +
      (s : ℂ) * (I + (ε : ℂ) * Complex.exp (2 * π * I * t)))) ?_ ?_ ?_ hL hL₁c ?_ ?_
  · refine Continuous.continuousOn (hE.comp ?_)
    fun_prop
  · intro s _
    rw [s18v_c_circ_one]
  · intro s hs t _ h
    exact hne s hs t (hEi h)
  · intro t ht
    rw [hLe t ht]
    congr 2
    push_cast
    ring
  · intro t ht
    rw [hL₁e t ht]
    congr 2
    push_cast
    ring

/-- **The orientation statement.**  A continuous injection `E` of `ℂ` cannot have local winding `+1` at `i` while
`E ∘ conj` also has local winding `+1` at `i`, i.e. while `E` has local winding `-1` at `-i`.

*Truth.*  Let `α t = E (2 e^{2πit})`.
- The points `E (s i)`, `s ∈ [-1, 1]`, avoid `α` (injectivity, `|s i| < 2`).  W3a with
  `H s t = α t - E (p s) + E i` (`p` from `i` to `-i`) therefore shows that `α` has the same winding about `E i` and
  about `E (-i)`.
- Shrinking the circle `|z| = 2` to `|z - i| = ε` through the circles of centre `s i` and radius `2 - s (2 - ε)`
  (these avoid `i`) gives winding `1` about `E i`, by W3a and `h₁`.
- Shrinking to `|z + i| = ε` gives winding `-1` about `E (-i)`.  Indeed `E (-i + ε e^{2πit}) = E (conj
  (i + ε e^{2πi(1-t)}))`, so for a lift `L` of `h₂`'s loop, `t ↦ L (1 - t)` lifts the reversed loop and changes by
  `-2πi`.

So `2πi = -2πi`, a contradiction.  The hypotheses are not vacuous: lifts exist for small radii
(`exists_continuousOn_log_lift`), and `E = id` satisfies `h₁`.

*Route.*  `lift_change_eq_of_homotopy` (W3a, Winding:197), `exists_continuousOn_log_lift` (W1a, Winding:43). -/
theorem s18v_or_loop {E : ℂ → ℂ} (hE : Continuous E) (hEi : Function.Injective E)
    (h₁ : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = E (I + ρ * Complex.exp (2 * π * I * t)) - E I) →
      L 1 - L 0 = 2 * π * I)
    (h₂ : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = E (conj (I + ρ * Complex.exp (2 * π * I * t))) - E (conj I)) →
      L 1 - L 0 = 2 * π * I) :
    False := by
  have hnorm2 : ∀ t : ℝ, ‖2 * Complex.exp (2 * π * I * t)‖ = 2 := fun t => by
    rw [norm_mul, s18v_c_norm_circ, mul_one, Complex.norm_two]
  have hα : ContinuousOn (fun t : ℝ => E (2 * Complex.exp (2 * π * I * t))) (Icc 0 1) :=
    (hE.comp (continuous_const.mul s18v_c_circ_cont)).continuousOn
  -- lifts of `α = E (2 e^{2πit})` about `E i` and about `E (-i)`
  obtain ⟨A, hAc, hAe⟩ := exists_continuousOn_log_lift (w := E I) hα fun t _ h => by
    have h' := congrArg norm (hEi h)
    rw [hnorm2, Complex.norm_I] at h'
    norm_num at h'
  obtain ⟨B, hBc, hBe⟩ := exists_continuousOn_log_lift (w := E (-I)) hα fun t _ h => by
    have h' := congrArg norm (hEi h)
    rw [hnorm2, norm_neg, Complex.norm_I] at h'
    norm_num at h'
  -- winding `+1` about `E i`
  have hA := s18v_c_wind_two hE hEi h₁ hAc hAe
  -- winding `-1` about `E (-i)`: `t ↦ B (1 - t)` lifts the loop of `E ∘ conj`
  have hmaps : MapsTo (fun t : ℝ => 1 - t) (Icc 0 1) (Icc 0 1) := fun t ht => ⟨by linarith [ht.2], by
    linarith [ht.1]⟩
  have hB := s18v_c_wind_two (E := fun z => E (conj z)) (hE.comp Complex.continuous_conj)
    (hEi.comp (RingHom.injective (starRingEnd ℂ))) h₂ (L := fun t => B (1 - t))
    (hBc.comp (continuous_const.sub continuous_id).continuousOn hmaps) fun t ht => by
      show Complex.exp (B (1 - t)) = E (conj (2 * Complex.exp (2 * π * I * t))) - E (conj I)
      rw [hBe (1 - t) (hmaps ht), s18v_c_circ_rev, Complex.conj_I, map_mul, map_ofNat]
  -- the two windings of `α` agree (move the base point from `i` to `-i` along the imaginary axis)
  have hAB : A 1 - A 0 = B 1 - B 0 := by
    refine lift_change_eq_of_homotopy (w := E I)
      (H := fun s t : ℝ => E (2 * Complex.exp (2 * π * I * t)) - E (I * ((1 - 2 * s : ℝ) : ℂ)) + E I)
      ?_ ?_ ?_ hAc hBc ?_ ?_
    · refine Continuous.continuousOn ?_
      have hc : Continuous fun p : ℝ × ℝ => E (I * ((1 - 2 * p.1 : ℝ) : ℂ)) := hE.comp (by fun_prop)
      exact ((hE.comp (continuous_const.mul (s18v_c_circ_cont.comp continuous_snd))).sub hc).add
        continuous_const
    · intro s _
      rw [s18v_c_circ_one]
    · intro s hs t _ h
      have h' : E (2 * Complex.exp (2 * π * I * t)) = E (I * ((1 - 2 * s : ℝ) : ℂ)) := by
        linear_combination h
      have h'' := congrArg norm (hEi h')
      rw [hnorm2, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at h''
      have := abs_le.2 (⟨by linarith [hs.2], by linarith [hs.1]⟩ : -1 ≤ 1 - 2 * s ∧ 1 - 2 * s ≤ 1)
      linarith
    · intro t ht
      rw [hAe t ht]
      have : I * ((1 - 2 * 0 : ℝ) : ℂ) = I := by push_cast; ring
      rw [this]
      ring
    · intro t ht
      rw [hBe t ht]
      have : I * ((1 - 2 * 1 : ℝ) : ℂ) = -I := by push_cast; ring
      rw [this]
      ring
  simp only [sub_self, sub_zero] at hB
  have h0 : (2 * π * I : ℂ) = 0 := by linear_combination -(hA - hAB + hB) / 2
  exact Complex.two_pi_I_ne_zero h0

/-- A strictly increasing surjection `g` of `ℝ` gives the homeomorphism `x + iy ↦ g x + iy` of `ℂ`. -/
theorem s18v_c_homeo {g : ℝ → ℝ} (hg : StrictMono g) (hs : Function.Surjective g) :
    ∃ e : ℂ ≃ₜ ℂ, ∀ z : ℂ, e z = ((g z.re : ℝ) : ℂ) + (z.im : ℂ) * I := by
  let o : ℝ ≃ₜ ℝ := (StrictMono.orderIsoOfSurjective g hg hs).toHomeomorph
  let c : ℂ ≃ₜ ℝ × ℝ := Complex.equivRealProdCLM.toHomeomorph
  refine ⟨c.trans ((o.prodCongr (Homeomorph.refl ℝ)).trans c.symm), fun z => ?_⟩
  apply Complex.ext <;> simp [c, o]

/-- Local winding `+1` at `z₀` passes to a map agreeing with the given one near `z₀`. -/
theorem s18v_c_hloc_congr {k k' : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (heq : ∀ z ∈ ball z₀ r, k' z = k z)
    (hloc : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = k (z₀ + ρ * Complex.exp (2 * π * I * t)) - k z₀) →
      L 1 - L 0 = 2 * π * I) :
    ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = k' (z₀ + ρ * Complex.exp (2 * π * I * t)) - k' z₀) →
      L 1 - L 0 = 2 * π * I := by
  obtain ⟨ρ₁, hρ₁, hl⟩ := hloc
  refine ⟨min ρ₁ r, lt_min hρ₁ hr, fun ρ hρ hρ' L hL hLe => hl ρ hρ (hρ'.trans_le (min_le_left _ _)) L hL
    fun t ht => ?_⟩
  have hmem : z₀ + ρ * Complex.exp (2 * π * I * t) ∈ ball z₀ r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, s18v_c_norm_circ, Complex.norm_real,
      Real.norm_of_nonneg hρ.le, mul_one]
    exact hρ'.trans_le (min_le_right _ _)
  rw [hLe t ht, heq _ hmem, heq _ (mem_ball_self hr)]

/-- A point of the unit ball about `i` lies in `ℍ`. -/
theorem s18v_c_ball_I {z : ℂ} (hz : z ∈ ball I 1) : z ∈ upperHalf := by
  have h1 : |(z - I).im| < 1 := (Complex.abs_im_le_norm _).trans_lt (mem_ball_iff_norm.1 hz)
  rw [sub_im, I_im] at h1
  show 0 < z.im
  linarith [(abs_lt.1 h1).1]

/-- The orientation contradiction behind `s18v_weld_strictMono`: a decreasing welding is impossible.  Glue
`E = Φ⁻¹` on `ℍ̄` and `E = Ψ⁻¹ ∘ Ĥ` on `𝕃̄` (`Ĥ (x + iy) = h x + iy`) into a homeomorphism `E₀` of `ℂ`; near `i`,
`E₀ = φ⁻¹` has winding `+1`, and so has `E₀ ∘ conj = (ψ⁻¹ ∘ neg) ∘ e`, `e (x + iy) = -h x + iy` having increasing
boundary values; `s18v_or_loop` excludes this. -/
theorem s18v_c_false_of_anti {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    {h : ℝ → ℝ} (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) (hanti : StrictAnti h) : False := by
  classical
  obtain ⟨hA₁o, hA₂o, hfr₁, hfr₂⟩ := s18v_c_frontiers hS
  obtain ⟨hc, -, hsurj⟩ := s18v_weld_homeo hS
  have hinv := s18v_c_inv_real hS
  obtain ⟨hinf, hC, hφ, hψ, hΦ, hΨ, hΦinf, hΨinf, -⟩ := hS
  obtain ⟨-, -, -, -, -, hA₂C, hA₁₂⟩ := s16p_basic hC
  have hcl₁ : closure (toExt A₁) = toExt A₁ ∪ C := by
    rw [← hfr₁, closure_eq_self_union_frontier]
  have hcl₂C : C ⊆ closure (toExt A₂) := hfr₂ ▸ frontier_subset_closure
  have hΦi := isHomeoExtension_invFunOn hφ hΦ
  have hΨi := isHomeoExtension_invFunOn hψ hΨ
  set Φi := Function.invFunOn Φ (closure (toExt A₁))
  set Ψi := Function.invFunOn Ψ (closure (toExt A₂))
  set ψi := Function.invFunOn ψ A₂
  have hΦiinf : Φi extInf = extInf := by
    have h0 := hΦ.2.2.1.leftInvOn_invFunOn (show extInf ∈ closure (toExt A₁) from hcl₁ ▸ Or.inr hinf)
    rwa [hΦinf] at h0
  have hΨiinf : Ψi extInf = extInf := by
    have h0 := hΨ.2.2.1.leftInvOn_invFunOn (hcl₂C hinf)
    rwa [hΨinf] at h0
  -- the homeomorphisms `e (x + iy) = -h x + iy` and `Ĥ (x + iy) = h x + iy` of `ℂ`
  have hmono : StrictMono fun x => -h x := fun a b hab => neg_lt_neg (hanti hab)
  have hsurj' : Function.Surjective fun x => -h x := fun y => by
    obtain ⟨x, hx⟩ := hsurj (-y)
    exact ⟨x, show -h x = y by rw [hx, neg_neg]⟩
  obtain ⟨e, he⟩ := s18v_c_homeo hmono hsurj'
  have heim : ∀ z, (e z).im = z.im := fun z => by
    rw [he]
    simp
  have hereal : ∀ x : ℝ, e (x : ℂ) = ((-h x : ℝ) : ℂ) := fun x => by
    rw [he]
    simp
  set Hh : ℂ ≃ₜ ℂ := Complex.conjLIE.toHomeomorph.trans (e.trans (Homeomorph.neg ℂ))
  have hHconj : ∀ z, Hh (conj z) = -(e z) := fun z => by
    show -(e (conj (conj z))) = -(e z)
    rw [conj_conj]
  have hHim : ∀ z, (Hh z).im = z.im := fun z => by
    show (-(e (conj z))).im = z.im
    rw [neg_im, heim, conj_im, neg_neg]
  have hHreal : ∀ x : ℝ, Hh (x : ℂ) = ((h x : ℝ) : ℂ) := fun x => by
    show -(e (conj (x : ℂ))) = _
    rw [Complex.conj_ofReal, hereal]
    push_cast
    ring
  set Hx := Hh.onePointCongr
  have hHL : MapsTo Hx (closure (toExt lowerHalf)) (closure (toExt lowerHalf)) := by
    refine MapsTo.closure ?_ Hx.continuous
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨Hh z, (show (Hh z).im < 0 by rw [hHim]; exact hz), rfl⟩
  -- the glued map `E = Φ⁻¹` on `ℍ̄`, `E = Ψ⁻¹ ∘ Ĥ` on `𝕃̄`
  obtain ⟨E, hE⟩ : ∃ E : ExtPlane → ExtPlane,
      ∀ p, E p = if p ∈ closure (toExt upperHalf) then Φi p else Ψi (Hx p) := ⟨_, fun p => rfl⟩
  have hEU : EqOn E Φi (closure (toExt upperHalf)) := fun p hp => by rw [hE, ite_eq_left hp]
  have hEL : EqOn E (Ψi ∘ Hx) (closure (toExt lowerHalf)) := fun p hp => by
    by_cases hpU : p ∈ closure (toExt upperHalf)
    · rw [hE, ite_eq_left hpU]
      rcases wd_b_closure_inter hpU hp with rfl | ⟨x, rfl⟩
      · show Φi extInf = Ψi extInf
        rw [hΦiinf, hΨiinf]
      · obtain ⟨z, hzC, hz, -, hzΨ⟩ := hinv x
        have hHx : Hx (((x : ℝ) : ℂ) : ExtPlane) = Ψ z := by
          rw [hzΨ]
          show ((Hh x : ℂ) : ExtPlane) = _
          rw [hHreal]
        show Φi _ = Ψi (Hx _)
        rw [hz, hHx]
        exact (hΨ.2.2.1.leftInvOn_invFunOn (hcl₂C hzC)).symm
    · rw [hE, ite_eq_right hpU]
      rfl
  have hEc : Continuous E := wd_b_paste hΦi.2.1 (hΨi.2.1.comp Hx.continuous.continuousOn hHL) hEU hEL
  have hA₂' : ∀ z ∈ lowerHalf, E z ∈ toExt A₂ := by
    intro z hz
    have hzU : (z : ExtPlane) ∉ closure (toExt upperHalf) := fun h' =>
      disjoint_left.1 wd_b_closure_upper_disjoint h' ⟨z, hz, rfl⟩
    have hHz : Hh z ∈ lowerHalf := show (Hh z).im < 0 by rw [hHim]; exact hz
    rw [hE, ite_eq_right hzU]
    exact ⟨_, (wd_b_invFunOn_coe hΨ hψ.2.2 hHz).2, (wd_b_invFunOn_coe hΨ hψ.2.2 hHz).1.symm⟩
  have hEinj : Function.Injective E := by
    have hsep : ∀ p q, p ∈ closure (toExt upperHalf) → q ∉ closure (toExt upperHalf) → E p ≠ E q := by
      intro p q hp hq hpq
      obtain ⟨z, hz, rfl⟩ := wd_b_not_mem_closure_upper hq
      have h1 : E p ∈ toExt A₁ ∪ C := by
        have h2 := mem_image_of_mem Φi hp
        rw [hΦi.2.2.2, hcl₁] at h2
        rwa [hEU hp]
      rw [hpq] at h1
      rcases h1 with h1 | h1
      · exact disjoint_left.1 hA₁₂ h1 (hA₂' z hz)
      · exact disjoint_left.1 hA₂C (hA₂' z hz) h1
    intro p q hpq
    by_cases hp : p ∈ closure (toExt upperHalf) <;> by_cases hq : q ∈ closure (toExt upperHalf)
    · rw [hEU hp, hEU hq] at hpq
      exact hΦi.2.2.1 hp hq hpq
    · exact (hsep p q hp hq hpq).elim
    · exact (hsep q p hq hp hpq.symm).elim
    · obtain ⟨z, hz, rfl⟩ := wd_b_not_mem_closure_upper hp
      obtain ⟨w, hw, rfl⟩ := wd_b_not_mem_closure_upper hq
      have hzL : ((z : ℂ) : ExtPlane) ∈ closure (toExt lowerHalf) := subset_closure ⟨z, hz, rfl⟩
      have hwL : ((w : ℂ) : ExtPlane) ∈ closure (toExt lowerHalf) := subset_closure ⟨w, hw, rfl⟩
      rw [hEL hzL, hEL hwL] at hpq
      exact Hx.injective (hΨi.2.2.1 (hHL hzL) (hHL hwL) hpq)
  have hEinf : E extInf = extInf := by rw [hEU wd_b_infty_mem_closure_upper, hΦiinf]
  obtain ⟨-, hhom⟩ := wd_b_plane_homeo hEc hEinj hEinf
  set E₀ : ℂ → ℂ := fun z => extToC (E z)
  have hE₀c : Continuous E₀ := continuousOn_univ.1 hhom.1
  have hE₀i : Function.Injective E₀ := fun a b hab => hhom.2.1 (mem_univ a) (mem_univ b) hab
  have hI : I ∈ upperHalf := show (0 : ℝ) < I.im by simp
  -- local winding `+1` of `E₀ = φ⁻¹` at `i`
  have hφi1 : IsKQC (Function.invFunOn φ A₁) upperHalf 1 :=
    isKQC_one_of_conformal isOpen_upperHalf (hφ.symm hA₁o)
  have h₁ := s18v_c_hloc_congr (k := Function.invFunOn φ A₁) (k' := E₀) one_pos (fun z hz => by
    show extToC (E z) = _
    rw [hEU (subset_closure ⟨z, s18v_c_ball_I hz, rfl⟩), hΦi.1 z (s18v_c_ball_I hz)]
    rfl) (qcl_r_hloc_of_isKQC hφi1 hI)
  -- local winding `+1` of `E₀ ∘ conj = (ψ⁻¹ ∘ neg) ∘ e` at `i`
  have heU : e '' upperHalf = upperHalf := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      show 0 < (e z).im
      rw [heim]
      exact hz
    · intro hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      show 0 < (e.symm w).im
      rw [← heim, e.apply_symm_apply]
      exact hw
  have hG : IsHomeoExtension e upperHalf upperHalf e.onePointCongr := by
    have h0 := s13x_de_isHomeoExtension_homeomorph e upperHalf
    rwa [heU] at h0
  have hlocm := qcl_w_hloc_of_strictMono_boundary hG heU rfl hI (fun x => -h x) (continuous_neg.comp hc)
    hmono.injective (fun t => by
      show ((e (t : ℂ) : ℂ) : ExtPlane) = _
      rw [hereal]) hmono
  have hψs := hψ.symm hA₂o
  have hnegL : MapsTo (fun w : ℂ => -w) upperHalf lowerHalf := fun w hw =>
    show (-w).im < 0 by rw [neg_im]; exact neg_lt_zero.2 hw
  have hAd : DifferentiableOn ℂ (fun w => ψi (-w)) upperHalf := hψs.1.comp (differentiableOn_neg _) hnegL
  have hAi : InjOn (fun w => ψi (-w)) upperHalf := fun a ha b hb hab =>
    neg_injective (hψs.2.1 (hnegL ha) (hnegL hb) hab)
  have heI : e I ∈ upperHalf := heU ▸ mem_image_of_mem e hI
  have hloc2 := qcl_r_transport_conformal (k := e) (A := fun w => ψi (-w)) one_pos e.continuous.continuousOn
    (fun z _ hz => e.injective.ne hz) hlocm isOpen_upperHalf heI hAd
    (deriv_ne_zero_of_injOn isOpen_upperHalf hAd hAi heI)
  have h₂ := s18v_c_hloc_congr (k := fun z => ψi (-(e z))) (k' := fun z => E₀ (conj z)) one_pos
    (fun z hz => by
      have hzU := s18v_c_ball_I hz
      have hcz : conj z ∈ lowerHalf := show (conj z).im < 0 by rw [conj_im]; exact neg_lt_zero.2 hzU
      have hczU : ((conj z : ℂ) : ExtPlane) ∉ closure (toExt upperHalf) := fun h' =>
        disjoint_left.1 wd_b_closure_upper_disjoint h' ⟨_, hcz, rfl⟩
      have hv : -(e z) ∈ lowerHalf := hnegL (heU ▸ mem_image_of_mem e hzU)
      show extToC (E (conj z : ℂ)) = ψi (-(e z))
      rw [hE, ite_eq_right hczU]
      show extToC (Ψi ((Hh (conj z) : ℂ) : ExtPlane)) = _
      rw [hHconj]
      exact congrArg extToC (wd_b_invFunOn_coe hΨ hψ.2.2 hv).1) hloc2
  exact s18v_or_loop hE₀c hE₀i h₁ h₂

/-- **Orientation of the welding.**  The welding of `s18v_Setup` is increasing.

*Truth.*  By `s18v_weld_homeo`, `h` is continuous and injective, hence `StrictMono` or `StrictAnti`
(`Continuous.strictMono_of_inj`).  Suppose it is `StrictAnti`.
- Glue `E = Φ⁻¹` on `closure ℍ` and `E = Ψ⁻¹ ∘ Ĥ` on `closure 𝕃`, with `Ĥ (x + iy) = h x + iy` and `Ĥ ∞ = ∞`.  The
  two agree on `ℝ ∪ {∞}` by the setup (`Ψ (Φ⁻¹ x) = h x`).  So `E` is a continuous injection of `ℂ̄` fixing `∞`:
  use `wd_b_paste`, and `closure A₁ ∩ closure A₂ = C`.  Then `E₀ = extToC ∘ E ∘ (↑)` is a homeomorphism of `ℂ`
  (`wd_b_plane_homeo`).
- Near `i`, `E₀ = φ⁻¹`, which is `1`-q.c. (`isKQC_one_of_conformal`, `IsConformalOnto.symm`), so it has local winding
  `+1` (`qcl_r_hloc_of_isKQC`).
- Near `i`, `E₀ ∘ conj = (Ψ⁻¹ ∘ neg) ∘ m` with `m (x + iy) = -h x + iy`.  `m` is a self-map of `ℍ` fixing `∞` whose
  boundary values `-h` are `StrictMono`, so it has local winding `+1` (`qcl_w_hloc_of_strictMono_boundary`), and so has
  `E₀ ∘ conj` (`qcl_r_transport_conformal`: `ψ⁻¹ ∘ neg` is conformal on `ℍ`, with nonzero derivative).
- `s18v_or_loop` gives `False`.

*Orientation check.*  For `C = ℝ ∪ {∞}` with `φ = ψ = id` the welding is `id`.  With the components swapped
(`A₁ = 𝕃`, `A₂ = ℍ`, `φ = ψ = -z`) it is again `id`: both maps reverse `ℝ`.  Conformal self-maps of the half-planes
fixing `∞` are `a z + b` with `a > 0`, so `h` is increasing in every case, as the statement says.

*Route.*  `s18v_weld_homeo`, `s18v_or_loop`, `wd_b_paste` (S16:868), `wd_b_plane_homeo` (S16:883),
`qcl_r_hloc_of_isKQC` (S08:4075), `qcl_w_hloc_of_strictMono_boundary` (S08:3063), `qcl_r_transport_conformal`
(S08:3722), `isHomeoExtension_invFunOn` (ImageQuad:63). -/
theorem s18v_weld_strictMono {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    {h : ℝ → ℝ} (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) : StrictMono h := by
  obtain ⟨hc, hi, -⟩ := s18v_weld_homeo hS
  exact (hc.strictMono_of_inj hi).resolve_right (s18v_c_false_of_anti hS)

/-! #### Arcs of `C` in the coordinate `Φ` -/

/-- `Φ` is injective on the finite points of `C` (`C = ∂A₁ ⊆ closure A₁`). -/
theorem s18v_inj {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane} {h : ℝ → ℝ}
    (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) :
    ∀ z w : ℂ, (z : ExtPlane) ∈ C → (w : ExtPlane) ∈ C → Φ z = Φ w → z = w := by
  obtain ⟨-, hC, hφ, -, hΦ, -, -, -, -⟩ := hS
  obtain ⟨hJ, p₁, hp₁, -, -, h₁, -, -⟩ := hC
  have hfr₁ : frontier (toExt A₁) = C := wd_frontier_eq hJ ⟨p₁, hp₁, h₁⟩ (Or.inl rfl) hφ hΦ
  have hcl₁ : C ⊆ closure (toExt A₁) := hfr₁ ▸ frontier_subset_closure
  intro z w hz hw hzw
  exact OnePoint.coe_injective (hΦ.2.2.1 (hcl₁ hz) (hcl₁ hw) hzw)

/-- `s18v_arc` is monotone in the interval. -/
theorem s18v_arc_mono {C : Set ExtPlane} {Φ : ExtPlane → ExtPlane} {I J : Set ℝ} (hIJ : I ⊆ J) :
    s18v_arc C Φ I ⊆ s18v_arc C Φ J := by
  exact fun _ ⟨hz, s, hs, he⟩ => ⟨hz, s, hIJ hs, he⟩

/-- Arcs over disjoint parameter sets are disjoint. -/
theorem s18v_arc_disjoint {C : Set ExtPlane} {Φ : ExtPlane → ExtPlane} {I J : Set ℝ} (hIJ : Disjoint I J) :
    Disjoint (s18v_arc C Φ I) (s18v_arc C Φ J) := by
  rw [Set.disjoint_left]
  rintro z ⟨-, s, hs, he⟩ ⟨-, s', hs', he'⟩
  have hss : s = s' := Complex.ofReal_injective (OnePoint.coe_injective (he.symm.trans he'))
  exact Set.disjoint_left.1 hIJ hs (hss ▸ hs')

/-- For the data `s18v_Setup`, `C ∩ Φ⁻¹(T)` is closed for every closed `T ⊆ ℂ̄` (`Φ` is continuous on
`closure (toExt A₁) ⊇ C`), and `Φ` sends the finite points of `C` to finite points (`Φ` is injective on
`closure (toExt A₁)` and `Φ ∞ = ∞`). -/
theorem s18v_a_setup_closed {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    {h : ℝ → ℝ} (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) :
    (∀ T : Set ExtPlane, IsClosed T → IsClosed (C ∩ Φ ⁻¹' T)) ∧
      ∀ z : ℂ, (z : ExtPlane) ∈ C → Φ z ≠ extInf := by
  obtain ⟨hinf, hC, hφ, -, hΦ, -, hΦinf, -, -⟩ := hS
  obtain ⟨hJ, p₁, hp₁, -, -, h₁, -, -⟩ := hC
  have hfr : frontier (toExt A₁) = C := wd_frontier_eq hJ ⟨p₁, hp₁, h₁⟩ (Or.inl rfl) hφ hΦ
  have hCK : C ⊆ closure (toExt A₁) := hfr ▸ frontier_subset_closure
  refine ⟨fun T hT => ?_, fun z hz h => ?_⟩
  · have e : C ∩ Φ ⁻¹' T = C ∩ (closure (toExt A₁) ∩ Φ ⁻¹' T) := by
      rw [← inter_assoc, inter_eq_left.2 hCK]
    rw [e, ← hfr]
    exact isClosed_frontier.inter (hΦ.2.1.preimage_isClosed_of_isClosed isClosed_closure hT)
  · exact OnePoint.coe_ne_infty z (hΦ.2.2.1 (hCK hz) (hCK hinf) (h.trans hΦinf.symm))

/-- The arc over a closed parameter set `I` is closed: it is the trace on `ℂ` of `C ∩ Φ⁻¹(I ∪ {∞})`, and
`toExt I ∪ {∞}` is closed in `ℂ̄`. -/
theorem s18v_a_arc_isClosed {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    {h : ℝ → ℝ} (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) {I : Set ℝ} (hI : IsClosed I) :
    IsClosed (s18v_arc C Φ I) := by
  obtain ⟨hcl, hfin⟩ := s18v_a_setup_closed hS
  have hT : IsClosed (toExt (((↑) : ℝ → ℂ) '' I) ∪ {extInf}) := by
    have hmemT : extInf ∈ toExt (((↑) : ℝ → ℂ) '' I) ∪ {extInf} := Or.inr rfl
    rw [OnePoint.isClosed_iff_of_mem hmemT]
    have e : ((↑) : ℂ → ExtPlane) ⁻¹' (toExt (((↑) : ℝ → ℂ) '' I) ∪ {extInf}) = ((↑) : ℝ → ℂ) '' I := by
      ext z
      simp only [mem_preimage, mem_union, mem_singleton_iff, OnePoint.coe_ne_infty, or_false]
      exact ⟨fun ⟨w, hw, hwz⟩ => OnePoint.coe_injective hwz ▸ hw, fun hz => ⟨z, hz, rfl⟩⟩
    rw [e]
    exact Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _ hI
  have e : s18v_arc C Φ I =
      ((↑) : ℂ → ExtPlane) ⁻¹' (C ∩ Φ ⁻¹' (toExt (((↑) : ℝ → ℂ) '' I) ∪ {extInf})) := by
    ext z
    constructor
    · rintro ⟨hz, s, hs, he⟩
      exact ⟨hz, Or.inl ⟨_, ⟨s, hs, rfl⟩, he.symm⟩⟩
    · rintro ⟨hz, ⟨_, ⟨s, hs, rfl⟩, he⟩ | hz'⟩
      · exact ⟨hz, s, hs, he.symm⟩
      · exact absurd hz' (hfin z hz)
  rw [e]
  exact (hcl _ hT).preimage OnePoint.continuous_coe

/-- The arc over a compact parameter set `I` is compact: its image in `ℂ̄` is `C ∩ Φ⁻¹(toExt I)`, a closed set
without `∞` (`OnePoint.isOpen_compl_image_coe`). -/
theorem s18v_a_arc_isCompact {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    {h : ℝ → ℝ} (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) {I : Set ℝ} (hI : IsCompact I) :
    IsCompact (s18v_arc C Φ I) := by
  obtain ⟨hcl, -⟩ := s18v_a_setup_closed hS
  have hΦinf : Φ extInf = extInf := hS.2.2.2.2.2.2.1
  have hT : IsClosed (toExt (((↑) : ℝ → ℂ) '' I)) :=
    ((hI.image Complex.continuous_ofReal).image OnePoint.continuous_coe).isClosed
  have heq : toExt (s18v_arc C Φ I) = C ∩ Φ ⁻¹' toExt (((↑) : ℝ → ℂ) '' I) := by
    ext p
    constructor
    · rintro ⟨z, ⟨hz, s, hs, he⟩, rfl⟩
      exact ⟨hz, ⟨_, ⟨s, hs, rfl⟩, he.symm⟩⟩
    · rintro ⟨hp, ⟨_, ⟨s, hs, rfl⟩, he⟩⟩
      rcases uq_j_eq_infty_or_coe p with rfl | ⟨z, rfl⟩
      · exact absurd (he.trans hΦinf) (OnePoint.coe_ne_infty _)
      · exact ⟨z, ⟨hp, s, hs, he.symm⟩, rfl⟩
  have hc : IsClosed (toExt (s18v_arc C Φ I)) := by
    rw [heq]
    exact hcl _ hT
  exact (OnePoint.isOpen_compl_image_coe.1 hc.isOpen_compl).2

/-- Every real coordinate `s` is taken: `s ∈ ∂ℍ = Φ(∂A₁)` has a preimage in `closure A₁`, which is finite
(`Φ ∞ = ∞`) and not in `A₁` (`φ(A₁) = ℍ`), hence lies on `∂A₁ = C`. -/
theorem s18v_a_arc_nonempty {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    {h : ℝ → ℝ} (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) (s : ℝ) : (s18v_arc C Φ {s}).Nonempty := by
  obtain ⟨-, hC, hφ, -, hΦ, -, hΦinf, -, -⟩ := hS
  have hA₁o : IsOpen (toExt A₁) := (s16p_basic hC).2.1
  obtain ⟨hJ, p₁, hp₁, -, -, h₁, -, -⟩ := hC
  have hfr : frontier (toExt A₁) = C := wd_frontier_eq hJ ⟨p₁, hp₁, h₁⟩ (Or.inl rfl) hφ hΦ
  have hmem : (((s : ℂ) : ExtPlane)) ∈ Φ '' closure (toExt A₁) := by
    rw [hΦ.2.2.2]
    exact frontier_subset_closure (ofReal_mem_frontier_upperHalf s)
  obtain ⟨p, hp, hΦp⟩ := hmem
  rcases uq_j_eq_infty_or_coe p with rfl | ⟨z, rfl⟩
  · rw [hΦinf] at hΦp
    exact absurd hΦp.symm (OnePoint.coe_ne_infty _)
  · refine ⟨z, ?_, s, rfl, hΦp⟩
    rw [← hfr, hA₁o.frontier_eq]
    refine ⟨hp, ?_⟩
    rintro ⟨w, hw, hwz⟩
    have h1 : Φ (w : ExtPlane) = ((φ w : ℂ) : ExtPlane) := hΦ.1 w hw
    rw [hwz, hΦp] at h1
    have h2 : (s : ℂ) = φ w := OnePoint.coe_injective h1
    have h3 : φ w ∈ upperHalf := hφ.2.2 ▸ mem_image_of_mem φ hw
    have h4 : (φ w).im = 0 := by
      rw [← h2]
      exact Complex.ofReal_im s
    exact (show 0 < (φ w).im from h3).ne' h4

/-- Topology of the arcs `s18v_arc C Φ I`: compact over `Icc`, closed over `Iic` and `Ici`, and every real
coordinate is taken.

*Truth.*  As in `s18v_weld_homeo`, `γ s = Φ⁻¹ s` is a continuous injection of `ℝ` onto the finite part of `C`.
`γ s → ∞` in `ℂ̄` as `s → ±∞`, because `Φ⁻¹` is continuous at `∞ = Φ⁻¹ ∞`.  `Φ` is injective on `C` (`s18v_inj`),
so `s18v_arc C Φ I = γ '' I`.  Hence:
- the arc over `Icc a b` is a continuous image of a compact set;
- the arcs over `Iic a` and `Ici a` are closed, since `γ` is proper (a sequence `γ sₙ` converging in `ℂ` has `sₙ`
  bounded);
- the arc over `{s}` contains `γ s`.
Edge case: for `a > b` the arc over `Icc a b` is empty, hence compact.

*Route.*  `isHomeoExtension_invFunOn` (ImageQuad:63), `IsHomeoExtension.image_frontier`, `wd_frontier_eq` (S16:1887),
`OnePoint.comap_coe_nhds_infty`, `IsCompact.image`. -/
theorem s18v_arc_props {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    {h : ℝ → ℝ} (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) :
    (∀ a b : ℝ, IsCompact (s18v_arc C Φ (Icc a b))) ∧ (∀ a : ℝ, IsClosed (s18v_arc C Φ (Iic a))) ∧
      (∀ a : ℝ, IsClosed (s18v_arc C Φ (Ici a))) ∧ ∀ s : ℝ, (s18v_arc C Φ {s}).Nonempty := by
  exact ⟨fun _ _ => s18v_a_arc_isCompact hS isCompact_Icc, fun _ => s18v_a_arc_isClosed hS isClosed_Iic,
    fun _ => s18v_a_arc_isClosed hS isClosed_Ici, s18v_a_arc_nonempty hS⟩

/-- The three-point condition with non-strict order: `u ≤ s ≤ v`, `u < v` (the equality cases are `w = z₁`, `w = z₂`,
by `s18v_inj`). -/
theorem s18v_bt_le {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane} {h : ℝ → ℝ}
    (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) {M : ℝ} (hM : 1 ≤ M) (h3 : s18v_ThreePoint C Φ M) {z₁ w z₂ : ℂ}
    {u s v : ℝ} (hz₁ : z₁ ∈ s18v_arc C Φ {u}) (hw : w ∈ s18v_arc C Φ {s}) (hz₂ : z₂ ∈ s18v_arc C Φ {v})
    (hus : u ≤ s) (hsv : s ≤ v) : ‖w - z₁‖ ≤ M * ‖z₁ - z₂‖ := by
  obtain ⟨hz₁C, u', hu', hu⟩ := hz₁
  obtain ⟨hwC, s', hs', hs⟩ := hw
  obtain ⟨hz₂C, v', hv', hv⟩ := hz₂
  rw [mem_singleton_iff] at hu' hs' hv'
  subst hu' hs' hv'
  have hi := s18v_inj hS
  rcases hus.lt_or_eq with hus' | hus'
  · rcases hsv.lt_or_eq with hsv' | hsv'
    · exact h3 z₁ w z₂ hz₁C hwC hz₂C u' s' v' hu hs hv hus' hsv'
    · have hwz : w = z₂ := hi w z₂ hwC hz₂C (by rw [hs, hv, hsv'])
      rw [hwz, norm_sub_rev]
      nlinarith [norm_nonneg (z₁ - z₂)]
  · have hwz : w = z₁ := hi w z₁ hwC hz₁C (by rw [hs, hu, hus'])
    rw [hwz, sub_self, norm_zero]
    positivity

/-! #### The two quadrilaterals and the moduli estimates -/

/-- The extended real line: `s ↦ s` from `ℝ` into `ℂ̄` is continuous. -/
theorem s18v_b_r_continuous : Continuous (fun s : ℝ => ((s : ℂ) : ExtPlane)) := by
  exact OnePoint.continuous_coe.comp Complex.continuous_ofReal

/-- `s ↦ s` from `ℝ` into `ℂ̄` is injective. -/
theorem s18v_b_r_inj {s s' : ℝ} (h : ((s : ℂ) : ExtPlane) = ((s' : ℂ) : ExtPlane)) : s = s' := by
  exact Complex.ofReal_injective (OnePoint.coe_injective h)

/-- A real point lies on the extended real line `ℝ ∪ {∞}`. -/
theorem s18v_b_r_mem (s : ℝ) : ((s : ℂ) : ExtPlane) ∈ toExt realLine ∪ {extInf} := by
  exact Or.inl ⟨(s : ℂ), Complex.ofReal_im s, rfl⟩

/-- A point of the extended real line is `∞` or a real point. -/
theorem s18v_b_E_cases {p : ExtPlane} (hp : p ∈ toExt realLine ∪ {extInf}) :
    p = extInf ∨ ∃ s : ℝ, p = ((s : ℂ) : ExtPlane) := by
  rcases hp with ⟨z, hz, rfl⟩ | hp
  · have hz' : z.im = 0 := hz
    exact Or.inr ⟨z.re, congrArg _ (Complex.ext (by simp) (by simp [hz']))⟩
  · exact Or.inl hp

/-- `∞` is in the closure of the image of a set of reals unbounded below or above. -/
theorem s18v_b_inf_mem_closure {I : Set ℝ} (hI : ¬ BddBelow I ∨ ¬ BddAbove I) :
    extInf ∈ closure ((fun s : ℝ => ((s : ℂ) : ExtPlane)) '' I) := by
  have e : (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' I = toExt (((↑) : ℝ → ℂ) '' I) := by
    unfold toExt
    rw [image_image]
  rw [e]
  refine extInf_mem_closure_toExt_of_not_isBounded fun hb => ?_
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hb
  have hRI : ∀ s ∈ I, |s| ≤ R := fun s hs => by
    have := hR _ (mem_image_of_mem _ hs)
    rwa [Complex.norm_real, Real.norm_eq_abs] at this
  rcases hI with hI | hI
  · exact hI ⟨-R, fun s hs => by linarith [neg_abs_le s, hRI s hs]⟩
  · exact hI ⟨R, fun s hs => le_trans (le_abs_self s) (hRI s hs)⟩

/-- The piece `(-∞, u) ∪ (v, ∞) ∪ {∞}` of the extended real line is preconnected. -/
theorem s18v_b_isPreconnected_out (u v : ℝ) :
    IsPreconnected ((fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Iio u ∪
      (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Ioi v ∪ {extInf}) := by
  have hc := s18v_b_r_continuous
  have h1 : IsPreconnected ((fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Iio u ∪ {extInf}) :=
    (isPreconnected_Iio.image _ hc.continuousOn).subset_closure subset_union_left
      (union_subset subset_closure (singleton_subset_iff.2 (s18v_b_inf_mem_closure (Or.inl (not_bddBelow_Iio u)))))
  have h2 : IsPreconnected ((fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Ioi v ∪ {extInf}) :=
    (isPreconnected_Ioi.image _ hc.continuousOn).subset_closure subset_union_left
      (union_subset subset_closure (singleton_subset_iff.2 (s18v_b_inf_mem_closure (Or.inr (not_bddAbove_Ioi v)))))
  rw [union_union_distrib_right]
  exact h1.union extInf (mem_union_right _ rfl) (mem_union_right _ rfl) h2

/-- A boundary arc `boundaryArc K u v w` avoids every preconnected `U ⊆ K ∖ {u, v}` through `w`, except for its
end points. -/
theorem s18v_b_boundaryArc_subset {K U : Set ExtPlane} {u v w : ExtPlane} (hU : IsPreconnected U)
    (hUK : U ⊆ K \ {u, v}) (hw : w ∈ U) : boundaryArc K u v w ⊆ {u, v} ∪ (K \ U) := by
  rintro p ⟨hpK, hp⟩
  by_cases hpU : p ∈ U
  · rcases hp with rfl | rfl | hne
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)
    · exact absurd (connectedComponentIn_eq (hU.subset_connectedComponentIn hw hUK hpU)).symm hne
  · exact Or.inr ⟨hpK, hpU⟩

/-- `boundaryArc K u v w` is symmetric in its end points. -/
theorem s18v_b_boundaryArc_comm (K : Set ExtPlane) (u v w : ExtPlane) :
    boundaryArc K u v w = boundaryArc K v u w := by
  unfold boundaryArc
  rw [pair_comm u v]
  ext p
  exact and_congr_right fun _ => or_left_comm

/-- On `ℝ ∪ {∞}`, the arc from `a` to `b` (`a < b`) avoiding a point outside `[a, b]` is `[a, b]`. -/
theorem s18v_b_arc_Icc {a b : ℝ} (hab : a < b) {w : ExtPlane}
    (hw : w ∈ (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Iio a ∪ (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Ioi b ∪
      {extInf}) :
    boundaryArc (toExt realLine ∪ {extInf}) ((a : ℂ) : ExtPlane) ((b : ℂ) : ExtPlane) w ⊆
      (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Icc a b := by
  intro p hp
  have hUK : (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Iio a ∪ (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Ioi b ∪
      {extInf} ⊆ (toExt realLine ∪ {extInf}) \ {((a : ℂ) : ExtPlane), ((b : ℂ) : ExtPlane)} := by
    rintro q ((⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | hq)
    · refine ⟨s18v_b_r_mem s, ?_⟩
      rintro (h | h)
      · exact (mem_Iio.1 hs).ne (s18v_b_r_inj h)
      · exact ((mem_Iio.1 hs).trans hab).ne (s18v_b_r_inj h)
    · refine ⟨s18v_b_r_mem s, ?_⟩
      rintro (h | h)
      · exact (hab.trans (mem_Ioi.1 hs)).ne' (s18v_b_r_inj h)
      · exact (mem_Ioi.1 hs).ne' (s18v_b_r_inj h)
    · rw [mem_singleton_iff.1 hq]
      refine ⟨Or.inr rfl, ?_⟩
      rintro (h | h) <;> exact OnePoint.coe_ne_infty _ h.symm
  rcases s18v_b_boundaryArc_subset (s18v_b_isPreconnected_out a b) hUK hw hp with (rfl | rfl) | ⟨hpE, hpU⟩
  · exact ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩
  · exact ⟨b, ⟨hab.le, le_rfl⟩, rfl⟩
  · rcases s18v_b_E_cases hpE with rfl | ⟨s, rfl⟩
    · exact absurd (Or.inr rfl) hpU
    · exact ⟨s, ⟨not_lt.1 fun h => hpU (Or.inl (Or.inl ⟨s, h, rfl⟩)),
        not_lt.1 fun h => hpU (Or.inl (Or.inr ⟨s, h, rfl⟩))⟩, rfl⟩

/-- On `ℝ ∪ {∞}`, the arc from `∞` to `a` avoiding `b > a` is `(-∞, a] ∪ {∞}`. -/
theorem s18v_b_arc_Iic {a b : ℝ} (hab : a < b) :
    boundaryArc (toExt realLine ∪ {extInf}) extInf ((a : ℂ) : ExtPlane) ((b : ℂ) : ExtPlane) ⊆
      (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Iic a ∪ {extInf} := by
  intro p hp
  have hUK : (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Ioi a ⊆
      (toExt realLine ∪ {extInf}) \ {extInf, ((a : ℂ) : ExtPlane)} := by
    rintro q ⟨s, hs, rfl⟩
    refine ⟨s18v_b_r_mem s, ?_⟩
    rintro (h | h)
    · exact OnePoint.coe_ne_infty _ h
    · exact (mem_Ioi.1 hs).ne' (s18v_b_r_inj h)
  rcases s18v_b_boundaryArc_subset (isPreconnected_Ioi.image _ s18v_b_r_continuous.continuousOn) hUK
    ⟨b, hab, rfl⟩ hp with (rfl | rfl) | ⟨hpE, hpU⟩
  · exact Or.inr rfl
  · exact Or.inl ⟨a, mem_Iic.2 le_rfl, rfl⟩
  · rcases s18v_b_E_cases hpE with rfl | ⟨s, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl ⟨s, mem_Iic.2 (not_lt.1 fun h => hpU ⟨s, h, rfl⟩), rfl⟩

/-- On `ℝ ∪ {∞}`, the arc from `∞` to `b` avoiding `a < b` is `[b, ∞) ∪ {∞}`. -/
theorem s18v_b_arc_Ici {a b : ℝ} (hab : a < b) :
    boundaryArc (toExt realLine ∪ {extInf}) extInf ((b : ℂ) : ExtPlane) ((a : ℂ) : ExtPlane) ⊆
      (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Ici b ∪ {extInf} := by
  intro p hp
  have hUK : (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Iio b ⊆
      (toExt realLine ∪ {extInf}) \ {extInf, ((b : ℂ) : ExtPlane)} := by
    rintro q ⟨s, hs, rfl⟩
    refine ⟨s18v_b_r_mem s, ?_⟩
    rintro (h | h)
    · exact OnePoint.coe_ne_infty _ h
    · exact (mem_Iio.1 hs).ne (s18v_b_r_inj h)
  rcases s18v_b_boundaryArc_subset (isPreconnected_Iio.image _ s18v_b_r_continuous.continuousOn) hUK
    ⟨a, hab, rfl⟩ hp with (rfl | rfl) | ⟨hpE, hpU⟩
  · exact Or.inr rfl
  · exact Or.inl ⟨b, mem_Ici.2 le_rfl, rfl⟩
  · rcases s18v_b_E_cases hpE with rfl | ⟨s, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl ⟨s, mem_Ici.2 (not_lt.1 fun h => hpU ⟨s, h, rfl⟩), rfl⟩

/-- For the setup, `C ⊆ closure A₁` and `Φ` maps `C = ∂A₁` onto `∂ℍ = ℝ ∪ {∞}`. -/
theorem s18v_b_basic {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane} {h : ℝ → ℝ}
    (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) :
    C ⊆ closure (toExt A₁) ∧ Φ '' C = toExt realLine ∪ {extInf} := by
  obtain ⟨hinf, hC, hφ, -, hΦ, -, -, -, -⟩ := hS
  obtain ⟨hD₁, -⟩ := s18v_isJordanDomain hC hinf
  have hfr : frontier (toExt A₁) = C := s16p_frontier_eq hC hinf
  refine ⟨hfr ▸ frontier_subset_closure, ?_⟩
  rw [← hfr, hΦ.image_frontier hD₁.1 isOpen_upperHalf hφ.2.2, tp_c1_frontier_upperHalf]

/-- The parametrization `γ = Φ⁻¹` of `C` by `ℝ ∪ {∞}`: continuous, onto `C`, and inverse to `Φ`. -/
theorem s18v_b_param {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane} {h : ℝ → ℝ}
    (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) :
    ContinuousOn (Function.invFunOn Φ (closure (toExt A₁))) (toExt realLine ∪ {extInf}) ∧
      (∀ e ∈ toExt realLine ∪ {extInf}, Function.invFunOn Φ (closure (toExt A₁)) e ∈ C) ∧
      (∀ e ∈ toExt realLine ∪ {extInf}, Φ (Function.invFunOn Φ (closure (toExt A₁)) e) = e) ∧
      (∀ q ∈ C, Function.invFunOn Φ (closure (toExt A₁)) (Φ q) = q) ∧
      (∀ q ∈ C, Φ q ∈ toExt realLine ∪ {extInf}) := by
  obtain ⟨hcl, himC⟩ := s18v_b_basic hS
  obtain ⟨-, -, hφ, -, hΦ, -, -, -, -⟩ := hS
  have hEcl : toExt realLine ∪ {extInf} ⊆ closure (toExt upperHalf) := by
    rw [← tp_c1_frontier_upperHalf]
    exact frontier_subset_closure
  refine ⟨(isHomeoExtension_invFunOn hφ hΦ).2.1.mono hEcl, fun e he => ?_, fun e he => ?_,
    fun q hq => hΦ.2.2.1.leftInvOn_invFunOn (hcl hq), fun q hq => himC ▸ mem_image_of_mem Φ hq⟩
  · rw [← himC] at he
    obtain ⟨q, hq, rfl⟩ := he
    rw [hΦ.2.2.1.leftInvOn_invFunOn (hcl hq)]
    exact hq
  · rw [← himC] at he
    obtain ⟨q, hq, rfl⟩ := he
    exact Function.invFunOn_eq ⟨q, hcl hq, rfl⟩

/-- A point of `C` with real coordinate in `I` is a finite point of the arc over `I`. -/
theorem s18v_b_pull {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane} {h : ℝ → ℝ}
    (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) {q : ExtPlane} (hq : q ∈ C) {I : Set ℝ}
    (hI : Φ q ∈ (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' I) : q ∈ toExt (s18v_arc C Φ I) := by
  obtain ⟨s, hs, hsq⟩ := hI
  rcases uq_j_eq_infty_or_coe q with rfl | ⟨z, rfl⟩
  · exact absurd (hsq.trans hS.2.2.2.2.2.2.1) (OnePoint.coe_ne_infty _)
  · exact ⟨z, ⟨hq, s, hs, hsq.symm⟩, rfl⟩

/-- A point of `C` with coordinate in `I ∪ {∞}` is in the arc over `I` or is `∞`. -/
theorem s18v_b_pull_inf {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    {h : ℝ → ℝ} (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) {q : ExtPlane} (hq : q ∈ C) {I : Set ℝ}
    (hI : Φ q ∈ (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' I ∪ {extInf}) :
    q ∈ toExt (s18v_arc C Φ I) ∪ {extInf} := by
  rcases hI with hI | hI
  · exact Or.inl (s18v_b_pull hS hq hI)
  · obtain ⟨hcl, -⟩ := s18v_b_basic hS
    exact Or.inr (hS.2.2.2.2.1.2.2.1 (hcl hq) (hcl hS.1) (hI.trans hS.2.2.2.2.2.2.1.symm))

/-- `Φ` carries a boundary arc of `C` onto the boundary arc of `ℝ ∪ {∞}` between the images of its points. -/
theorem s18v_b_image_arc {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    {h : ℝ → ℝ} (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) {u v w : ExtPlane} (hu : u ∈ C) (hv : v ∈ C)
    (hw : w ∈ C) : Φ '' boundaryArc C u v w = boundaryArc (toExt realLine ∪ {extInf}) (Φ u) (Φ v) (Φ w) := by
  obtain ⟨hcl, himC⟩ := s18v_b_basic hS
  have hΦ := hS.2.2.2.2.1
  rw [image_boundaryArc_of_injOn isClosed_closure hΦ.2.1 hΦ.2.2.1 hcl (hcl hu) (hcl hv) (hcl hw), himC]

/-- A boundary arc of `C` whose `Φ`-image lies in `I ∪ {∞}` lies in the arc over `I`, plus `∞`. -/
theorem s18v_b_side {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane} {h : ℝ → ℝ}
    (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) {u v w : ExtPlane} (hu : u ∈ C) (hv : v ∈ C) (hw : w ∈ C)
    {I : Set ℝ} (hX : boundaryArc (toExt realLine ∪ {extInf}) (Φ u) (Φ v) (Φ w) ⊆
      (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' I ∪ {extInf}) :
    boundaryArc C u v w ⊆ toExt (s18v_arc C Φ I) ∪ {extInf} := by
  intro q hq
  refine s18v_b_pull_inf hS hq.1 (hX ?_)
  rw [← s18v_b_image_arc hS hu hv hw]
  exact mem_image_of_mem Φ hq

/-- A boundary arc of `C` whose `Φ`-image lies in `I` lies in the arc over `I`. -/
theorem s18v_b_side' {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane} {h : ℝ → ℝ}
    (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) {u v w : ExtPlane} (hu : u ∈ C) (hv : v ∈ C) (hw : w ∈ C)
    {I : Set ℝ} (hX : boundaryArc (toExt realLine ∪ {extInf}) (Φ u) (Φ v) (Φ w) ⊆
      (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' I) :
    boundaryArc C u v w ⊆ toExt (s18v_arc C Φ I) := by
  intro q hq
  refine s18v_b_pull hS hq.1 (hX ?_)
  rw [← s18v_b_image_arc hS hu hv hw]
  exact mem_image_of_mem Φ hq

/-- A Jordan domain `D` with four boundary points sent by a conformal map onto `ℍ` to `∞, -1, 0, ρ` is a
quadrilateral of modulus `Λ(ρ)` (`isTopQuad_upperHalf_lambda`, Theorem 1.3). -/
theorem s18v_b_quad {D : Set ℂ} {p₀ p₁ p₂ p₃ : ExtPlane} {f : ℂ → ℂ} {F : ExtPlane → ExtPlane} {ρ : ℝ}
    (hρ : 0 < ρ) (hD : IsJordanDomain D) (h₀ : p₀ ∈ frontier (toExt D)) (h₁ : p₁ ∈ frontier (toExt D))
    (h₂ : p₂ ∈ frontier (toExt D)) (h₃ : p₃ ∈ frontier (toExt D)) (hf : IsConformalOnto f D upperHalf)
    (hF : IsHomeoExtension f D upperHalf F) (e₀ : F p₀ = extInf) (e₁ : F p₁ = (((-1 : ℝ) : ℂ) : ExtPlane))
    (e₂ : F p₂ = ((0 : ℂ) : ExtPlane)) (e₃ : F p₃ = (((ρ : ℝ) : ℂ) : ExtPlane)) :
    ∃ Q : TopQuad, Q.dom = D ∧ Q.vert = ![p₀, p₁, p₂, p₃] ∧ Q.modulus = quadLambda ρ := by
  have hFv : ∀ i, F (![p₀, p₁, p₂, p₃] i) = ![extInf, (((-1 : ℝ) : ℂ) : ExtPlane), ((0 : ℂ) : ExtPlane),
      (((ρ : ℝ) : ℂ) : ExtPlane)] i := by
    intro i
    fin_cases i
    exacts [e₀, e₁, e₂, e₃]
  obtain ⟨-, -, φ₀, Φ₀, x, hφ₀, hΦ₀, hx, hv₀⟩ := isTopQuad_upperHalf_lambda hρ
  have hQ : IsTopQuad D ![p₀, p₁, p₂, p₃] := by
    refine ⟨hD, fun i => ?_, φ₀ ∘ f, Φ₀ ∘ F, x, hφ₀.comp hf, hΦ₀.comp hF hf.mapsTo, hx, fun i => ?_⟩
    · fin_cases i
      exacts [h₀, h₁, h₂, h₃]
    · show Φ₀ (F _) = _
      rw [hFv i]
      exact hv₀ i
  exact ⟨⟨D, _, hQ⟩, rfl, rfl, thm1_3_modulus_conformal_invariant
    (Q' := ⟨upperHalf, _, isTopQuad_upperHalf_lambda hρ⟩) ⟨f, F, hf, hF, hFv⟩⟩

/-- The extension of `z ↦ -z` to `ℂ̄` sends a real point `y` to `-y`. -/
theorem s18v_b_neg_r (y : ℝ) :
    (Homeomorph.neg ℂ).onePointCongr (((y : ℝ) : ℂ) : ExtPlane) = (((-y : ℝ) : ℂ) : ExtPlane) := by
  rw [Complex.ofReal_neg]
  rfl

/-- The quadrilaterals `Q₁ = A₁(∞, z(x-t), z(x), z(x+t))` and `Q₂ = A₂(∞, z(x+t), z(x), z(x-t))`,
`z(s) = Φ⁻¹ s`: `M(Q₁) = 1`, `M(Q₂) = Λ((h x - h (x-t))/(h (x+t) - h x))`, and their sides lie on the four arcs of `C`
over `(-∞, x-t]`, `[x-t, x]`, `[x, x+t]`, `[x+t, ∞)`.

*Truth.*
- `Q₁`: `a ∘ φ`, with `a w = (w - x)/t` a real affine automorphism of `ℍ`, is conformal `A₁ → ℍ`.  Its extension
  `â ∘ Φ` sends the vertices to `∞, -1, 0, 1`.  So `A₁(∞, z(x-t), z(x), z(x+t))` is conformally equivalent to
  `ℍ(∞, -1, 0, 1)`, a quadrilateral (`isTopQuad_upperHalf_lambda`).  Pulling back its uniformizer gives `IsTopQuad`,
  and `M(Q₁) = Λ(1) = 1` (`thm1_3_modulus_conformal_invariant`, `b4_quadLambda_one`).
- `Q₂`: use `b ∘ neg ∘ ψ` with `b w = (w + h x)/(h (x+t) - h x)`, a positive scaling because `h` is `StrictMono`.
  By the setup, `Ψ z(s) = h s`, so the vertices go to `∞, -1, 0, ρ` with `ρ = (h x - h (x-t))/(h (x+t) - h x) > 0`,
  and `M(Q₂) = Λ(ρ)`.
- Sides.  `frontier (toExt A₂) = frontier (toExt A₁) = C` (`s16p_frontier_eq`).  So both quadrilaterals' sides are
  boundary arcs of `C`, and `Φ` carries them onto boundary arcs of `ℝ ∪ {∞}` (`image_boundaryArc_of_injOn`,
  `IsHomeoExtension.image_frontier`).  On `ℝ ∪ {∞}` the arc from `u` to `v` avoiding `w` lies in the closed interval
  between `u` and `v` that does not contain `w`.  The other piece is connected: it is `toExt (Iio u ∪ Ioi v) ∪ {∞}`,
  or `toExt (Ioi u)` for an arc through `∞`, a union of connected sets whose closures contain `∞`.

*Orientation check (the P2b lesson).*  The vertex orders above are the positive ones.  `Q₁` uniformizes to
`∞, -1, 0, 1` and `Q₂` to `∞, -1, 0, ρ`; `ℍ(∞, -1, 0, ρ)` is a quadrilateral for every `ρ > 0`, and `ρ > 0` holds
exactly because `h` is increasing.  Each side inclusion follows the convention of `TopQuad.side`: side `i` is the arc
from vertex `i` to vertex `i + 1` not containing vertex `i + 2`.
- For `Q₁`, the sides are the arcs `(∞, z(x-t))`, `(z(x-t), z(x))`, `(z(x), z(x+t))`, `(z(x+t), ∞)`.
- For `Q₂` they are `(∞, z(x+t))`, `(z(x+t), z(x))`, `(z(x), z(x-t))`, `(z(x-t), ∞)`.
- In `Φ`-coordinates these are `(-∞, x-t]`, `[x-t, x]`, `[x, x+t]`, `[x+t, ∞)` for `Q₁`, and the reverse list for `Q₂`.

*Route.*  `isTopQuad_upperHalf_lambda` (S05:6323), `uq_k_mobius_auto` (S13:4338), `IsConformalOnto.comp`,
`IsHomeoExtension.comp` (Mobius:356/363), `thm1_3_modulus_conformal_invariant` (S01:657), `acl_image_side` (S09:259),
`image_boundaryArc_of_injOn` (Quadrilateral:92), `s16p_frontier_eq`; `boundaryArc K u v w` is symmetric in `u, v`
(`Set.pair_comm`). -/
theorem s18v_quads {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane} {h : ℝ → ℝ}
    (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) (hmono : StrictMono h) {x t : ℝ} (ht : 0 < t) :
    ∃ Q₁ Q₂ : TopQuad, Q₁.modulus = 1 ∧ Q₂.modulus = quadLambda ((h x - h (x - t)) / (h (x + t) - h x)) ∧
      Q₁.side 0 ⊆ toExt (s18v_arc C Φ (Iic (x - t))) ∪ {extInf} ∧
      Q₁.side 1 ⊆ toExt (s18v_arc C Φ (Icc (x - t) x)) ∧
      Q₁.side 2 ⊆ toExt (s18v_arc C Φ (Icc x (x + t))) ∧
      Q₁.side 3 ⊆ toExt (s18v_arc C Φ (Ici (x + t))) ∪ {extInf} ∧
      Q₂.side 0 ⊆ toExt (s18v_arc C Φ (Ici (x + t))) ∪ {extInf} ∧
      Q₂.side 1 ⊆ toExt (s18v_arc C Φ (Icc x (x + t))) ∧
      Q₂.side 2 ⊆ toExt (s18v_arc C Φ (Icc (x - t) x)) ∧
      Q₂.side 3 ⊆ toExt (s18v_arc C Φ (Iic (x - t))) ∪ {extInf} := by
  have hS' := hS
  obtain ⟨hinf, hC, hφ, hψ, hΦ, hΨ, hΦinf, hΨinf, hh⟩ := hS'
  obtain ⟨-, hGC, hΦG, -, -⟩ := s18v_b_param hS
  have hC' : AreComplementaryComponents C (toExt A₂) (toExt A₁) := by
    obtain ⟨hJ', p₁, hp₁, p₂, hp₂, h₁, h₂, hne⟩ := hC
    exact ⟨hJ', p₂, hp₂, p₁, hp₁, h₂, h₁, hne.symm⟩
  obtain ⟨hD₁, -⟩ := s18v_isJordanDomain hC hinf
  obtain ⟨hD₂, -⟩ := s18v_isJordanDomain hC' hinf
  have hfr₁ : frontier (toExt A₁) = C := s16p_frontier_eq hC hinf
  have hfr₂ : frontier (toExt A₂) = C := s16p_frontier_eq hC' hinf
  -- the points `z(s) = Φ⁻¹ s`
  have hpt : ∀ s : ℝ, ∃ z : ℂ, (z : ExtPlane) ∈ C ∧ Φ z = ((s : ℂ) : ExtPlane) ∧
      Ψ z = (((h s : ℝ) : ℂ) : ExtPlane) := by
    intro s
    have hq := hGC _ (s18v_b_r_mem s)
    have hΦq := hΦG _ (s18v_b_r_mem s)
    rcases uq_j_eq_infty_or_coe (Function.invFunOn Φ (closure (toExt A₁)) ((s : ℂ) : ExtPlane)) with
      h0 | ⟨z, hz⟩
    · rw [h0, hΦinf] at hΦq
      exact absurd hΦq.symm (OnePoint.coe_ne_infty _)
    · rw [hz] at hq hΦq
      obtain ⟨s', hs', hΨs'⟩ := hh z hq
      obtain rfl : s' = s := s18v_b_r_inj (hs'.symm.trans hΦq)
      exact ⟨z, hq, hΦq, hΨs'⟩
  obtain ⟨zm, hzm, hΦzm, hΨzm⟩ := hpt (x - t)
  obtain ⟨z0, hz0, hΦz0, hΨz0⟩ := hpt x
  obtain ⟨zp, hzp, hΦzp, hΨzp⟩ := hpt (x + t)
  -- `Q₁ = A₁(∞, z(x-t), z(x), z(x+t))`, uniformized by `(φ - x)/t`
  have hden₁ : ∀ s : ℝ, (0 : ℝ) * s + t ≠ 0 := fun s => by rw [zero_mul, zero_add]; exact ht.ne'
  obtain ⟨hm₁c, hm₁e⟩ := uq_k_mobius_auto (a := 1) (b := -x) (c := 0) (d := t) (by linarith)
  have hM₁ : ∀ q : ExtPlane, (mobiusExt ((1 : ℝ) : ℂ) ((-x : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((t : ℝ) : ℂ) ∘ Φ) q =
      mobiusExt ((1 : ℝ) : ℂ) ((-x : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((t : ℝ) : ℂ) (Φ q) := fun q => rfl
  have e₁₀ : (mobiusExt ((1 : ℝ) : ℂ) ((-x : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((t : ℝ) : ℂ) ∘ Φ) extInf = extInf := by
    rw [hM₁, hΦinf]
    exact mobiusExt_infty_of_eq Complex.ofReal_zero
  have e₁₁ : (mobiusExt ((1 : ℝ) : ℂ) ((-x : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((t : ℝ) : ℂ) ∘ Φ) (zm : ExtPlane) =
      (((-1 : ℝ) : ℂ) : ExtPlane) := by
    rw [hM₁, hΦzm, mobiusExt_ofReal_coe (hden₁ _)]
    congr 2
    rw [zero_mul, zero_add, div_eq_iff ht.ne']
    ring
  have e₁₂ : (mobiusExt ((1 : ℝ) : ℂ) ((-x : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((t : ℝ) : ℂ) ∘ Φ) (z0 : ExtPlane) =
      ((0 : ℂ) : ExtPlane) := by
    rw [hM₁, hΦz0, mobiusExt_ofReal_coe (hden₁ _)]
    congr 1
    simp
  have e₁₃ : (mobiusExt ((1 : ℝ) : ℂ) ((-x : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((t : ℝ) : ℂ) ∘ Φ) (zp : ExtPlane) =
      (((1 : ℝ) : ℂ) : ExtPlane) := by
    rw [hM₁, hΦzp, mobiusExt_ofReal_coe (hden₁ _)]
    congr 2
    rw [zero_mul, zero_add, div_eq_iff ht.ne']
    ring
  obtain ⟨Q₁, hQ₁d, hQ₁v, hQ₁m⟩ := s18v_b_quad one_pos hD₁ (hfr₁ ▸ hinf) (hfr₁ ▸ hzm) (hfr₁ ▸ hz0)
    (hfr₁ ▸ hzp) (hm₁c.comp hφ) (hm₁e.comp hΦ hφ.mapsTo) e₁₀ e₁₁ e₁₂ e₁₃
  -- `Q₂ = A₂(∞, z(x+t), z(x), z(x-t))`, uniformized by `(h x - ψ)/(h(x+t) - h x)`
  have hD : 0 < h (x + t) - h x := sub_pos.2 (hmono (lt_add_of_pos_right x ht))
  have hρ : 0 < (h x - h (x - t)) / (h (x + t) - h x) :=
    div_pos (sub_pos.2 (hmono (sub_lt_self x ht))) hD
  have hnL : (Homeomorph.neg ℂ) '' lowerHalf = upperHalf :=
    wd_n_neg_image fun z => by
      show 0 < (-z).im ↔ z.im < 0
      rw [neg_im, neg_pos]
  have hnc : IsConformalOnto (Homeomorph.neg ℂ) lowerHalf upperHalf :=
    ⟨(differentiable_id.neg : Differentiable ℂ fun z : ℂ => -z).differentiableOn,
      (Homeomorph.neg ℂ).injective.injOn, hnL⟩
  have hne : IsHomeoExtension (Homeomorph.neg ℂ) lowerHalf upperHalf (Homeomorph.neg ℂ).onePointCongr := by
    have h1 := s13x_de_isHomeoExtension_homeomorph (Homeomorph.neg ℂ) lowerHalf
    rwa [hnL] at h1
  have hden₂ : ∀ s : ℝ, (0 : ℝ) * s + (h (x + t) - h x) ≠ 0 := fun s => by
    rw [zero_mul, zero_add]
    exact hD.ne'
  obtain ⟨hm₂c, hm₂e⟩ := uq_k_mobius_auto (a := 1) (b := h x) (c := 0) (d := h (x + t) - h x) (by linarith)
  have hM₂ : ∀ q : ExtPlane, (mobiusExt ((1 : ℝ) : ℂ) ((h x : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((h (x + t) - h x : ℝ) : ℂ) ∘
      ((Homeomorph.neg ℂ).onePointCongr ∘ Ψ)) q = mobiusExt ((1 : ℝ) : ℂ) ((h x : ℝ) : ℂ) ((0 : ℝ) : ℂ)
        ((h (x + t) - h x : ℝ) : ℂ) ((Homeomorph.neg ℂ).onePointCongr (Ψ q)) := fun q => rfl
  have e₂₀ : (mobiusExt ((1 : ℝ) : ℂ) ((h x : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((h (x + t) - h x : ℝ) : ℂ) ∘
      ((Homeomorph.neg ℂ).onePointCongr ∘ Ψ)) extInf = extInf := by
    rw [hM₂, hΨinf]
    exact mobiusExt_infty_of_eq Complex.ofReal_zero
  have e₂₁ : (mobiusExt ((1 : ℝ) : ℂ) ((h x : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((h (x + t) - h x : ℝ) : ℂ) ∘
      ((Homeomorph.neg ℂ).onePointCongr ∘ Ψ)) (zp : ExtPlane) = (((-1 : ℝ) : ℂ) : ExtPlane) := by
    rw [hM₂, hΨzp, s18v_b_neg_r, mobiusExt_ofReal_coe (hden₂ _)]
    congr 2
    rw [zero_mul, zero_add, div_eq_iff hD.ne']
    ring
  have e₂₂ : (mobiusExt ((1 : ℝ) : ℂ) ((h x : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((h (x + t) - h x : ℝ) : ℂ) ∘
      ((Homeomorph.neg ℂ).onePointCongr ∘ Ψ)) (z0 : ExtPlane) = ((0 : ℂ) : ExtPlane) := by
    rw [hM₂, hΨz0, s18v_b_neg_r, mobiusExt_ofReal_coe (hden₂ _)]
    congr 1
    simp
  have e₂₃ : (mobiusExt ((1 : ℝ) : ℂ) ((h x : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((h (x + t) - h x : ℝ) : ℂ) ∘
      ((Homeomorph.neg ℂ).onePointCongr ∘ Ψ)) (zm : ExtPlane) =
        ((((h x - h (x - t)) / (h (x + t) - h x) : ℝ) : ℂ) : ExtPlane) := by
    rw [hM₂, hΨzm, s18v_b_neg_r, mobiusExt_ofReal_coe (hden₂ _)]
    congr 2
    ring
  obtain ⟨Q₂, hQ₂d, hQ₂v, hQ₂m⟩ := s18v_b_quad hρ hD₂ (hfr₂ ▸ hinf) (hfr₂ ▸ hzp) (hfr₂ ▸ hz0)
    (hfr₂ ▸ hzm) (hm₂c.comp (hnc.comp hψ)) (hm₂e.comp (hne.comp hΨ hψ.mapsTo) (hnc.comp hψ).mapsTo)
    e₂₀ e₂₁ e₂₂ e₂₃
  -- the sides
  have hs₁ : ∀ i, Q₁.side i = boundaryArc C (Q₁.vert i) (Q₁.vert (i + 1)) (Q₁.vert (i + 2)) := fun i => by
    rw [TopQuad.side_eq_boundaryArc, hQ₁d, hfr₁]
  have hs₂ : ∀ i, Q₂.side i = boundaryArc C (Q₂.vert i) (Q₂.vert (i + 1)) (Q₂.vert (i + 2)) := fun i => by
    rw [TopQuad.side_eq_boundaryArc, hQ₂d, hfr₂]
  have hxm : x - t < x := sub_lt_self x ht
  have hxp : x < x + t := lt_add_of_pos_right x ht
  refine ⟨Q₁, Q₂, hQ₁m.trans b4_quadLambda_one, hQ₂m, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs₁, hQ₁v]
    show boundaryArc C extInf (zm : ExtPlane) (z0 : ExtPlane) ⊆ _
    refine s18v_b_side hS hinf hzm hz0 ?_
    rw [hΦinf, hΦzm, hΦz0]
    exact s18v_b_arc_Iic hxm
  · rw [hs₁, hQ₁v]
    show boundaryArc C (zm : ExtPlane) (z0 : ExtPlane) (zp : ExtPlane) ⊆ _
    refine s18v_b_side' hS hzm hz0 hzp ?_
    rw [hΦzm, hΦz0, hΦzp]
    exact s18v_b_arc_Icc hxm (Or.inl (Or.inr ⟨x + t, hxp, rfl⟩))
  · rw [hs₁, hQ₁v]
    show boundaryArc C (z0 : ExtPlane) (zp : ExtPlane) extInf ⊆ _
    refine s18v_b_side' hS hz0 hzp hinf ?_
    rw [hΦz0, hΦzp, hΦinf]
    exact s18v_b_arc_Icc hxp (Or.inr rfl)
  · rw [hs₁, hQ₁v]
    show boundaryArc C (zp : ExtPlane) extInf (zm : ExtPlane) ⊆ _
    refine s18v_b_side hS hzp hinf hzm ?_
    rw [hΦzp, hΦinf, hΦzm, s18v_b_boundaryArc_comm]
    exact s18v_b_arc_Ici (hxm.trans hxp)
  · rw [hs₂, hQ₂v]
    show boundaryArc C extInf (zp : ExtPlane) (z0 : ExtPlane) ⊆ _
    refine s18v_b_side hS hinf hzp hz0 ?_
    rw [hΦinf, hΦzp, hΦz0]
    exact s18v_b_arc_Ici hxp
  · rw [hs₂, hQ₂v]
    show boundaryArc C (zp : ExtPlane) (z0 : ExtPlane) (zm : ExtPlane) ⊆ _
    refine s18v_b_side' hS hzp hz0 hzm ?_
    rw [hΦzp, hΦz0, hΦzm, s18v_b_boundaryArc_comm]
    exact s18v_b_arc_Icc hxp (Or.inl (Or.inl ⟨x - t, hxm, rfl⟩))
  · rw [hs₂, hQ₂v]
    show boundaryArc C (z0 : ExtPlane) (zm : ExtPlane) extInf ⊆ _
    refine s18v_b_side' hS hz0 hzm hinf ?_
    rw [hΦz0, hΦzm, hΦinf, s18v_b_boundaryArc_comm]
    exact s18v_b_arc_Icc hxm (Or.inr rfl)
  · rw [hs₂, hQ₂v]
    show boundaryArc C (zm : ExtPlane) extInf (zp : ExtPlane) ⊆ _
    refine s18v_b_side hS hzm hinf hzp ?_
    rw [hΦzm, hΦinf, hΦzp, s18v_b_boundaryArc_comm]
    exact s18v_b_arc_Iic (hxm.trans hxp)

/-- The fundamental theorem of calculus along a curve: for `F` Lipschitz and a density `ρ` with
`|(F ∘ γ)'| ≤ ρ(γ) |γ'|` wherever `γ` is differentiable, `|F(γ t) - F(γ s)| ≤ l_ρ(γ)` for `0 < s ≤ t < 1`
(as in `aqc_enorm_log_norm_sub_le_rhoLength_interior`). -/
theorem s18v_a_ftc_interior (γ : LRCurve) {F : ℂ → ℝ} {KF : ℝ≥0} (hF : LipschitzWith KF F)
    {ρ : ℂ → ℝ≥0∞}
    (hbd : ∀ u ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ γ.toFun u →
      ‖deriv (fun s => F (γ.toFun s)) u‖ₑ ≤ ρ (γ.toFun u) * ‖deriv γ.toFun u‖ₑ)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht1 : t < 1) :
    ‖F (γ.toFun t) - F (γ.toFun s)‖ₑ ≤ γ.rhoLength ρ := by
  have hA := LocallyLipschitzOn.ae_differentiableAt_Ioo γ.locallyLipschitzOn
  have hsub : Icc s t ⊆ Ioo 0 1 := Icc_subset_Ioo hs ht1
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
    (LocallyLipschitzOn.mono γ.locallyLipschitzOn hsub)
  have hKL : LipschitzOnWith (KF * K) (fun u => F (γ.toFun u)) (uIcc s t) := by
    rw [uIcc_of_le hst]
    exact hF.comp_lipschitzOnWith hK
  have hftc : ∫ u in s..t, deriv (fun u => F (γ.toFun u)) u = F (γ.toFun t) - F (γ.toFun s) :=
    hKL.absolutelyContinuousOnInterval.integral_deriv_eq_sub
  rw [← hftc, intervalIntegral.integral_of_le hst]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ u in Ioc s t, ‖deriv (fun u => F (γ.toFun u)) u‖ₑ
      ≤ ∫⁻ u in Ioc s t, ρ (γ.toFun u) * ‖deriv γ.toFun u‖ₑ := by
        refine setLIntegral_mono_ae' measurableSet_Ioc ?_
        filter_upwards [hA] with u hu huI
        have hu01 : u ∈ Ioo (0 : ℝ) 1 := ⟨hs.trans huI.1, huI.2.trans_lt ht1⟩
        exact hbd u hu01 (hu hu01)
    _ ≤ γ.rhoLength ρ := lintegral_mono_set fun u hu => ⟨hs.trans hu.1, hu.2.trans_lt ht1⟩

/-- The end-point form of `s18v_a_ftc_interior`: if `F ∘ γ` tends to `a` at `0⁺` and to `b` at `1⁻`, then
`|b - a| ≤ l_ρ(γ)` (as in `aqc_abs_log_norm_sub_le_rhoLength`). -/
theorem s18v_a_ftc (γ : LRCurve) {F : ℂ → ℝ} {KF : ℝ≥0} (hF : LipschitzWith KF F)
    {ρ : ℂ → ℝ≥0∞}
    (hbd : ∀ u ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ γ.toFun u →
      ‖deriv (fun s => F (γ.toFun s)) u‖ₑ ≤ ρ (γ.toFun u) * ‖deriv γ.toFun u‖ₑ)
    {a b : ℝ} (ha : Tendsto (fun s => F (γ.toFun s)) (𝓝[>] 0) (𝓝 a))
    (hb : Tendsto (fun s => F (γ.toFun s)) (𝓝[<] 1) (𝓝 b)) :
    ENNReal.ofReal |b - a| ≤ γ.rhoLength ρ := by
  have step : ∀ s : ℝ, 0 < s → s < 1 → ‖b - F (γ.toFun s)‖ₑ ≤ γ.rhoLength ρ := by
    intro s hs hs1
    have ht : Tendsto (fun t => ‖F (γ.toFun t) - F (γ.toFun s)‖ₑ) (𝓝[<] 1)
        (𝓝 ‖b - F (γ.toFun s)‖ₑ) :=
      (continuous_enorm.tendsto _).comp (hb.sub_const _)
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hs1] with t ht'
    exact s18v_a_ftc_interior γ hF hbd hs ht'.1.le ht'.2
  have hstep0 : Tendsto (fun s => ‖b - F (γ.toFun s)‖ₑ) (𝓝[>] 0) (𝓝 ‖b - a‖ₑ) :=
    (continuous_enorm.tendsto _).comp (tendsto_const_nhds.sub ha)
  have hfinal : ‖b - a‖ₑ ≤ γ.rhoLength ρ := by
    refine le_of_tendsto hstep0 ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with s hs'
    exact step s hs'.1 hs'.2
  rwa [← ofReal_norm, Real.norm_eq_abs] at hfinal

/-- A curve tending to `∞` in `ℂ̄` has `‖γ - c‖ → ∞` (`OnePoint.comap_coe_nhds_infty`). -/
theorem s18v_a_tendsto_norm {l : Filter ℝ} {g : ℝ → ℂ} (c : ℂ)
    (hg : Tendsto (fun t => ((g t : ℂ) : ExtPlane)) l (𝓝 extInf)) :
    Tendsto (fun t => ‖g t - c‖) l atTop := by
  have h1 : Tendsto g l (cocompact ℂ) := by
    rw [← coclosedCompact_eq_cocompact, ← OnePoint.comap_coe_nhds_infty]
    exact tendsto_comap_iff.2 hg
  have h2 : Tendsto (fun t => ‖g t‖ - ‖c‖) l atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_norm_cocompact_atTop.comp h1)
  refine tendsto_atTop_mono (fun t => ?_) h2
  have := norm_sub_norm_le (g t) c
  linarith

/-- The distance to `c`, clamped to `[r, R]`, is `1`-Lipschitz. -/
theorem s18v_a_clamp_lipschitz (c : ℂ) (r R : ℝ) :
    LipschitzWith 1 (fun z : ℂ => max r (min R ‖z - c‖)) := by
  have hN : LipschitzWith 1 (fun z : ℂ => ‖z - c‖) := LipschitzWith.of_dist_le_mul fun z w => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
    calc |‖z - c‖ - ‖w - c‖| ≤ ‖(z - c) - (w - c)‖ := abs_norm_sub_norm_le _ _
      _ = ‖z - w‖ := by rw [sub_sub_sub_cancel_right]
  exact (hN.const_min R).const_max r

/-- The clamped logarithm `log (max r (min R ‖z - c‖))` is `1/r`-Lipschitz (`aqc_log_lipschitzOnWith`). -/
theorem s18v_a_logclamp_lipschitz (c : ℂ) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    LipschitzWith (1 / r).toNNReal (fun z : ℂ => Real.log (max r (min R ‖z - c‖))) := by
  have h := (aqc_log_lipschitzOnWith r hr).comp (s18v_a_clamp_lipschitz c r R).lipschitzOnWith
    (s := univ) (fun z _ => mem_Ici.2 (le_max_left _ _))
  rw [mul_one, lipschitzOnWith_univ] at h
  exact h

/-- The derivative of `log (max r (min R |γ - c|))` is at most `1_{annulusAt c r R}(γ) |γ'| / |γ - c|` wherever
`γ` is differentiable: inside the annulus it is `Re (γ' / (γ - c))` (`aqc_hasDerivAt_log_norm`), elsewhere the
clamped function has a local minimum or maximum. -/
theorem s18v_a_annulus_deriv (γ : ℝ → ℂ) (c : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) {u : ℝ}
    (hu : DifferentiableAt ℝ γ u) :
    ‖deriv (fun s => Real.log (max r (min R ‖γ s - c‖))) u‖ₑ ≤
      (annulusAt c r R).indicator (fun z => ENNReal.ofReal (1 / ‖z - c‖)) (γ u) * ‖deriv γ u‖ₑ := by
  by_cases hlo : ‖γ u - c‖ ≤ r
  · have hmin : IsLocalMin (fun s => Real.log (max r (min R ‖γ s - c‖))) u :=
      Eventually.of_forall fun s => by
        show Real.log (max r (min R ‖γ u - c‖)) ≤ Real.log (max r (min R ‖γ s - c‖))
        rw [max_eq_left (min_le_of_right_le hlo)]
        exact Real.log_le_log hr (le_max_left _ _)
    rw [hmin.deriv_eq_zero, enorm_zero]
    exact zero_le
  by_cases hhi : R ≤ ‖γ u - c‖
  · have hmax : IsLocalMax (fun s => Real.log (max r (min R ‖γ s - c‖))) u :=
      Eventually.of_forall fun s => by
        show Real.log (max r (min R ‖γ s - c‖)) ≤ Real.log (max r (min R ‖γ u - c‖))
        rw [min_eq_left hhi, max_eq_right hrR.le]
        exact Real.log_le_log (lt_of_lt_of_le hr (le_max_left _ _)) (max_le hrR.le (min_le_left _ _))
    rw [hmax.deriv_eq_zero, enorm_zero]
    exact zero_le
  push Not at hlo hhi
  have hmem : γ u ∈ annulusAt c r R := ⟨hlo, hhi⟩
  have hne : γ u - c ≠ 0 := norm_pos_iff.1 (hr.trans hlo)
  have hd : HasDerivAt (fun s => γ s - c) (deriv γ u) u := hu.hasDerivAt.sub_const c
  have hlog := aqc_hasDerivAt_log_norm (γ := fun s => γ s - c) hne hd
  have hev : (fun s => Real.log (max r (min R ‖γ s - c‖))) =ᶠ[𝓝 u] fun s => Real.log ‖γ s - c‖ := by
    filter_upwards [hu.continuousAt.preimage_mem_nhds (isOpen_annulusAt.mem_nhds hmem)] with s hs
    rw [min_eq_right hs.2.le, max_eq_right hs.1.le]
  rw [(hlog.congr_of_eventuallyEq hev).deriv, indicator_of_mem hmem, Real.enorm_eq_ofReal_abs]
  have hbound : |(deriv γ u / (γ u - c)).re| ≤ ‖deriv γ u‖ / ‖γ u - c‖ := by
    rw [← norm_div]
    exact Complex.abs_re_le_norm _
  calc ENNReal.ofReal |(deriv γ u / (γ u - c)).re|
      ≤ ENNReal.ofReal (‖deriv γ u‖ / ‖γ u - c‖) := ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (1 / ‖γ u - c‖) * ‖deriv γ u‖ₑ := by
        rw [← ofReal_norm (deriv γ u), div_eq_mul_one_div, mul_comm,
          ENNReal.ofReal_mul (by positivity)]

/-- The area of the annulus density: `∫ 1_{annulusAt c r R} / ‖z - c‖² = 2π log (R/r)` (translate by `c`, then
`lintegral_annulus_inv_normSq`). -/
theorem s18v_a_lintegral_annulusAt (c : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∫⁻ z, (annulusAt c r R).indicator (fun z => ENNReal.ofReal (1 / ‖z - c‖)) z ^ 2 =
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (R / r)) := by
  have hpt : ∀ z : ℂ, (annulusAt c r R).indicator (fun z => ENNReal.ofReal (1 / ‖z - c‖)) z ^ 2 =
      (annulus r R).indicator (fun w => ENNReal.ofReal (1 / ‖w‖ ^ 2)) (z - c) := by
    intro z
    rw [← indicator_comp_right (fun z : ℂ => z - c)]
    by_cases hz : z ∈ annulusAt c r R
    · have hz' : z ∈ (fun z : ℂ => z - c) ⁻¹' annulus r R := hz
      rw [indicator_of_mem hz, indicator_of_mem hz', Function.comp_apply,
        ← ENNReal.ofReal_pow (by positivity), one_div_pow]
    · have hz' : z ∉ (fun z : ℂ => z - c) ⁻¹' annulus r R := hz
      rw [indicator_of_notMem hz, indicator_of_notMem hz']
      simp
  simp_rw [hpt]
  rw [lintegral_sub_right_eq_self (fun w => (annulus r R).indicator
      (fun w => ENNReal.ofReal (1 / ‖w‖ ^ 2)) w) c,
    lintegral_indicator measurableSet_annulus, lintegral_annulus_inv_normSq hr hrR]

/-- **Annulus metric.**  If side `0` of `Q` lies in `closedBall c r` and side `2` lies in `{|z - c| ≥ R} ∪ {∞}`,
`0 < r < R`, then `M(Q) log(R/r) ≤ 2π`.

*Truth.*  Every `γ ∈ Q.joiningCurves 0` starts (`t → 0⁺`, in `ℂ̄`) at a finite `p` with `|p - c| ≤ r`, and ends
(`t → 1⁻`) at `∞` or at a finite `q` with `|q - c| ≥ R`.
- The clamped function `v t = log (max r (min R |γ t - c|))` is locally Lipschitz on `(0, 1)`, with `v (0⁺) = log r`
  and `v (1⁻) = log R`; if the end point is `∞`, then `v = log R` eventually.
- `|v'| ≤ 1_{r < |γ - c| < R} |γ'| / |γ - c|` a.e.
- So the density `ρ = 1_{annulusAt c r R} / (|z - c| log (R/r))` gives every joining curve `ρ`-length at least `1`
  (FTC on `[s, t] ⊂ (0, 1)`, then limits, as in `aqc_abs_log_norm_sub_le_rhoLength`).
- Its area is `2π / log (R/r)` (`rhoArea_annulus_density` after translating by `c` and scaling).
`eq4_6_modulus_le_rhoArea` then gives `M(Q) ≤ 2π / log (R/r)`.
Edge cases: `γ` may pass through `c` (the clamp at `r > 0` avoids `log 0`).  `r < R` makes `log (R/r) > 0`.

*Route.*  `eq4_6_modulus_le_rhoArea` (S04:182), `rhoArea_annulus_density` (S04:1663),
`aqc_enorm_log_norm_sub_le_rhoLength_interior` / `aqc_abs_log_norm_sub_le_rhoLength` (AnnulusQC:508/557),
`LocallyLipschitzOn.ae_differentiableAt_Ioo` (S03:504). -/
theorem s18v_annulus_bound (Q : TopQuad) {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (h0 : ∀ p ∈ Q.side 0, ∃ z : ℂ, p = (z : ExtPlane) ∧ ‖z - c‖ ≤ r)
    (h2 : ∀ p ∈ Q.side 2, p = extInf ∨ ∃ z : ℂ, p = (z : ExtPlane) ∧ R ≤ ‖z - c‖) :
    Q.modulus * Real.log (R / r) ≤ 2 * π := by
  have hR : 0 < R := hr.trans hrR
  have hLpos : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).2 hrR)
  have hFL := s18v_a_logclamp_lipschitz c hr R
  have hadm : ∀ γ ∈ Q.joiningCurves 0, ENNReal.ofReal (Real.log (R / r)) ≤
      γ.rhoLength ((annulusAt c r R).indicator fun z => ENNReal.ofReal (1 / ‖z - c‖)) := by
    rintro γ ⟨-, ⟨p, hp, hpγ⟩, ⟨q, hq, hqγ⟩⟩
    obtain ⟨z, rfl, hz⟩ := h0 p hp
    have hz' : Tendsto γ.toFun (𝓝[>] 0) (𝓝 z) :=
      OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.2 hpγ
    have ha : Tendsto (fun s => Real.log (max r (min R ‖γ.toFun s - c‖))) (𝓝[>] 0)
        (𝓝 (Real.log r)) := by
      have e : Real.log (max r (min R ‖z - c‖)) = Real.log r := by
        rw [max_eq_left (min_le_of_right_le hz)]
      rw [← e]
      exact (hFL.continuous.tendsto z).comp hz'
    have hb : Tendsto (fun s => Real.log (max r (min R ‖γ.toFun s - c‖))) (𝓝[<] 1)
        (𝓝 (Real.log R)) := by
      rcases h2 q hq with rfl | ⟨w, rfl, hw⟩
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [(s18v_a_tendsto_norm c hqγ).eventually_ge_atTop R] with s hs
        rw [min_eq_left hs, max_eq_right hrR.le]
      · have hw' : Tendsto γ.toFun (𝓝[<] 1) (𝓝 w) :=
          OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.2 hqγ
        have e : Real.log (max r (min R ‖w - c‖)) = Real.log R := by
          rw [min_eq_left hw, max_eq_right hrR.le]
        rw [← e]
        exact (hFL.continuous.tendsto w).comp hw'
    have h := s18v_a_ftc γ hFL (fun u _ hu => s18v_a_annulus_deriv γ.toFun c hr hrR hu) ha hb
    rwa [← Real.log_div hR.ne' hr.ne', abs_of_pos hLpos] at h
  have hρm : Measurable fun z => ENNReal.ofReal (1 / Real.log (R / r)) *
      (annulusAt c r R).indicator (fun z => ENNReal.ofReal (1 / ‖z - c‖)) z :=
    measurable_const.mul ((by fun_prop : Measurable fun z : ℂ => ENNReal.ofReal (1 / ‖z - c‖)).indicator
      measurableSet_annulusAt)
  have hadm' : ∀ γ ∈ Q.joiningCurves 0, 1 ≤ γ.rhoLength fun z => ENNReal.ofReal (1 / Real.log (R / r)) *
      (annulusAt c r R).indicator (fun z => ENNReal.ofReal (1 / ‖z - c‖)) z := by
    intro γ hγ
    rw [LRCurve.rhoLength_const_mul _ _ ENNReal.ofReal_ne_top]
    calc (1 : ℝ≥0∞) = ENNReal.ofReal (1 / Real.log (R / r)) * ENNReal.ofReal (Real.log (R / r)) := by
          rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hLpos.ne', ENNReal.ofReal_one]
      _ ≤ _ := mul_le_mul_right (hadm γ hγ) _
  have h46 := eq4_6_modulus_le_rhoArea Q hρm hadm'
  have harea : rhoArea (fun z => ENNReal.ofReal (1 / Real.log (R / r)) *
      (annulusAt c r R).indicator (fun z => ENNReal.ofReal (1 / ‖z - c‖)) z) Q.dom ≤
        ENNReal.ofReal (2 * π / Real.log (R / r)) := by
    refine (setLIntegral_le_lintegral _ _).trans_eq ?_
    simp_rw [mul_pow]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
      s18v_a_lintegral_annulusAt c hr hrR, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hle := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h46.trans harea)
  rwa [le_div_iff₀ hLpos] at hle

/-- A pointwise derivative bound: if `|f a - f u| ≤ K ‖g a - g u‖` for all `a` and `g` is differentiable at `u`,
then `|f'(u)| ≤ K ‖g'(u)‖` (compare the slopes; `f'(u) = 0` when `f` is not differentiable at `u`). -/
theorem s18v_a_deriv_le {f : ℝ → ℝ} {g : ℝ → ℂ} {u K : ℝ} (hK : 0 ≤ K)
    (hfg : ∀ a, |f a - f u| ≤ K * ‖g a - g u‖) (hg : DifferentiableAt ℝ g u) :
    |deriv f u| ≤ K * ‖deriv g u‖ := by
  by_cases hf : DifferentiableAt ℝ f u
  · have h1 := (continuous_abs.tendsto _).comp (hasDerivAt_iff_tendsto_slope.1 hf.hasDerivAt)
    have h2 := ((continuous_norm.tendsto _).comp (hasDerivAt_iff_tendsto_slope.1 hg.hasDerivAt)).const_mul K
    refine le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun a => ?_)
    simp only [Function.comp_apply, slope_def_module, norm_smul, Real.norm_eq_abs, smul_eq_mul, abs_mul]
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hfg a) (abs_nonneg _)
  · rw [deriv_zero_of_not_differentiableAt hf, abs_zero]
    positivity

/-- The distance to `p`, capped at `d`, is `1`-Lipschitz. -/
theorem s18v_a_cap_lipschitz (p : ℂ) (d : ℝ) : LipschitzWith 1 (fun z : ℂ => min d ‖z - p‖) := by
  have hN : LipschitzWith 1 (fun z : ℂ => ‖z - p‖) := LipschitzWith.of_dist_le_mul fun z w => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
    calc |‖z - p‖ - ‖w - p‖| ≤ ‖(z - p) - (w - p)‖ := abs_norm_sub_norm_le _ _
      _ = ‖z - w‖ := by rw [sub_sub_sub_cancel_right]
  exact hN.const_min d

/-- The derivative of `min d |γ - p|`, `|p - c| ≤ r`, is at most `1_{ball c (r + d)}(γ) |γ'|` wherever `γ` is
differentiable: where `|γ - p| < d` by `s18v_a_deriv_le`, elsewhere the capped function has a local maximum. -/
theorem s18v_a_disc_deriv (γ : ℝ → ℂ) {p c : ℂ} {r d : ℝ} (hpc : ‖p - c‖ ≤ r) {u : ℝ}
    (hu : DifferentiableAt ℝ γ u) :
    ‖deriv (fun s => min d ‖γ s - p‖) u‖ₑ ≤
      (ball c (r + d)).indicator (fun _ => (1 : ℝ≥0∞)) (γ u) * ‖deriv γ u‖ₑ := by
  by_cases hhi : d ≤ ‖γ u - p‖
  · have hmax : IsLocalMax (fun s => min d ‖γ s - p‖) u := Eventually.of_forall fun s => by
      show min d ‖γ s - p‖ ≤ min d ‖γ u - p‖
      rw [min_eq_left hhi]
      exact min_le_left _ _
    rw [hmax.deriv_eq_zero, enorm_zero]
    exact zero_le
  push Not at hhi
  have hmem : γ u ∈ ball c (r + d) := by
    rw [mem_ball, dist_eq_norm]
    have := norm_sub_le_norm_sub_add_norm_sub (γ u) p c
    linarith
  rw [indicator_of_mem hmem, one_mul]
  have hL := s18v_a_deriv_le (f := fun s => min d ‖γ s - p‖) (K := 1) zero_le_one (fun a => by
    have h := (s18v_a_cap_lipschitz p d).dist_le_mul (γ a) (γ u)
    rwa [NNReal.coe_one, Real.dist_eq, dist_eq_norm] at h) hu
  rw [one_mul] at hL
  rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hL

/-- **Disc metric.**  If side `0` of `Q` lies in `closedBall c r` and every finite point of side `2` is at
distance at least `d > 0` from every finite point of side `0`, then `M(Q) d² ≤ π (r + d)²`.

*Truth.*  Take a joining curve from `p ∈` side `0` (so `|p - c| ≤ r`) to `q ∈` side `2`.
- `v t = min d |γ t - p|` goes from `0` to `d`: either `q = ∞`, or `q` is finite and `|q - p| ≥ d` by `h2`.
- `|v'| ≤ 1_{|γ - p| < d} |γ'|` a.e., and `|γ - p| < d` forces `|γ - c| < r + d`.
- So `ρ = 1_{ball c (r + d)} / d` gives `ρ`-length at least `1`, and its area is `π (r + d)² / d²`.
`eq4_6_modulus_le_rhoArea` concludes.  Edge case: `r = 0` is allowed.

*Route.*  `eq4_6_modulus_le_rhoArea` (S04:182), the clamp technique of `s18v_annulus_bound`, `Real.volume_ball`. -/
theorem s18v_disc_bound (Q : TopQuad) {c : ℂ} {r d : ℝ} (hr : 0 ≤ r) (hd : 0 < d)
    (h0 : ∀ p ∈ Q.side 0, ∃ z : ℂ, p = (z : ExtPlane) ∧ ‖z - c‖ ≤ r)
    (h2 : ∀ p ∈ Q.side 2, p = extInf ∨ ∃ w : ℂ, p = (w : ExtPlane) ∧
      ∀ z : ℂ, (z : ExtPlane) ∈ Q.side 0 → d ≤ ‖w - z‖) :
    Q.modulus * d ^ 2 ≤ π * (r + d) ^ 2 := by
  have hadm : ∀ γ ∈ Q.joiningCurves 0, ENNReal.ofReal d ≤
      γ.rhoLength ((ball c (r + d)).indicator fun _ => (1 : ℝ≥0∞)) := by
    rintro γ ⟨-, ⟨p, hp, hpγ⟩, ⟨q, hq, hqγ⟩⟩
    obtain ⟨z, rfl, hz⟩ := h0 p hp
    have hFL := s18v_a_cap_lipschitz z d
    have hz' : Tendsto γ.toFun (𝓝[>] 0) (𝓝 z) :=
      OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.2 hpγ
    have ha : Tendsto (fun s => min d ‖γ.toFun s - z‖) (𝓝[>] 0) (𝓝 0) := by
      have e : min d ‖z - z‖ = 0 := by rw [sub_self, norm_zero, min_eq_right hd.le]
      have h := (hFL.continuous.tendsto z).comp hz'
      rwa [e] at h
    have hb : Tendsto (fun s => min d ‖γ.toFun s - z‖) (𝓝[<] 1) (𝓝 d) := by
      rcases h2 q hq with rfl | ⟨w, rfl, hw⟩
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [(s18v_a_tendsto_norm z hqγ).eventually_ge_atTop d] with s hs
        rw [min_eq_left hs]
      · have hw' : Tendsto γ.toFun (𝓝[<] 1) (𝓝 w) :=
          OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.2 hqγ
        have e : min d ‖w - z‖ = d := min_eq_left (hw z hp)
        have h := (hFL.continuous.tendsto w).comp hw'
        rwa [e] at h
    have h := s18v_a_ftc γ hFL (fun u _ hu => s18v_a_disc_deriv γ.toFun hz hu) ha hb
    rwa [sub_zero, abs_of_pos hd] at h
  have hρm : Measurable fun z => ENNReal.ofReal (1 / d) *
      (ball c (r + d)).indicator (fun _ => (1 : ℝ≥0∞)) z :=
    measurable_const.mul (measurable_const.indicator measurableSet_ball)
  have hadm' : ∀ γ ∈ Q.joiningCurves 0, 1 ≤ γ.rhoLength fun z => ENNReal.ofReal (1 / d) *
      (ball c (r + d)).indicator (fun _ => (1 : ℝ≥0∞)) z := by
    intro γ hγ
    rw [LRCurve.rhoLength_const_mul _ _ ENNReal.ofReal_ne_top]
    calc (1 : ℝ≥0∞) = ENNReal.ofReal (1 / d) * ENNReal.ofReal d := by
          rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hd.ne', ENNReal.ofReal_one]
      _ ≤ _ := mul_le_mul_right (hadm γ hγ) _
  have h46 := eq4_6_modulus_le_rhoArea Q hρm hadm'
  have hsq : ∀ z : ℂ, (ENNReal.ofReal (1 / d) * (ball c (r + d)).indicator (fun _ => (1 : ℝ≥0∞)) z) ^ 2 =
      ENNReal.ofReal (1 / d) ^ 2 * (ball c (r + d)).indicator (fun _ => (1 : ℝ≥0∞)) z := by
    intro z
    rw [mul_pow]
    by_cases hz : z ∈ ball c (r + d)
    · rw [indicator_of_mem hz, one_pow]
    · rw [indicator_of_notMem hz, zero_pow two_ne_zero]
  have harea : rhoArea (fun z => ENNReal.ofReal (1 / d) *
      (ball c (r + d)).indicator (fun _ => (1 : ℝ≥0∞)) z) Q.dom ≤
        ENNReal.ofReal (π * (r + d) ^ 2 / d ^ 2) := by
    refine (setLIntegral_le_lintegral _ _).trans_eq ?_
    simp_rw [hsq]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
      lintegral_indicator_const measurableSet_ball, Complex.volume_ball, one_mul,
      ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hle := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h46.trans harea)
  rwa [le_div_iff₀ (by positivity)] at hle

/-- A closest pair between a nonempty closed set `S` and a nonempty compact set `T` of `ℂ`
(`IsCompact.exists_isMinOn`, `IsClosed.exists_infDist_eq_dist`). -/
theorem s18v_a_closest {S T : Set ℂ} (hS : IsClosed S) (hT : IsCompact T) (hSn : S.Nonempty)
    (hTn : T.Nonempty) : ∃ ζ ∈ S, ∃ ζ' ∈ T, ∀ z ∈ S, ∀ w ∈ T, ‖ζ - ζ'‖ ≤ ‖z - w‖ := by
  obtain ⟨ζ', hζ', hmin⟩ := hT.exists_isMinOn hTn (continuous_infDist_pt S).continuousOn
  obtain ⟨ζ, hζ, heq⟩ := hS.exists_infDist_eq_dist hSn ζ'
  refine ⟨ζ, hζ, ζ', hζ', fun z hz w hw => ?_⟩
  have h1 : infDist ζ' S ≤ infDist w S := isMinOn_iff.1 hmin w hw
  have h2 : infDist w S ≤ dist w z := infDist_le_dist_of_mem hz
  rw [← dist_eq_norm, ← dist_eq_norm, dist_comm ζ, dist_comm z, ← heq]
  exact h1.trans h2

/-- Step (i) of `s18v_moduli_bound`: a quadrilateral of modulus `1` whose side `0` lies in `closedBall ζ m` and
whose side `2` lies in `{|z - ζ| ≥ D - m} ∪ {∞}` has `D ≤ (1 + e^{2π}) m` (`s18v_annulus_bound`, and trivially
when `D ≤ 2m`). -/
theorem s18v_a_step_annulus {Q : TopQuad} {A B : Set ℂ} {ζ : ℂ} {m D : ℝ} (hQ : Q.modulus = 1)
    (hm : 0 < m) (h0 : Q.side 0 ⊆ toExt A) (h2 : Q.side 2 ⊆ toExt B ∪ {extInf})
    (hA : ∀ w ∈ A, ‖w - ζ‖ ≤ m) (hB : ∀ w ∈ B, D - m ≤ ‖w - ζ‖) :
    D ≤ (1 + Real.exp (2 * π)) * m := by
  have he : 1 ≤ Real.exp (2 * π) := Real.one_le_exp (by positivity)
  by_cases hD : D ≤ 2 * m
  · nlinarith
  push Not at hD
  have hb := s18v_annulus_bound Q (c := ζ) (r := m) (R := D - m) hm (by linarith)
    (fun p hp => by
      obtain ⟨z, hz, rfl⟩ := h0 hp
      exact ⟨z, rfl, hA z hz⟩)
    (fun p hp => by
      rcases h2 hp with ⟨z, hz, rfl⟩ | hp'
      · exact Or.inr ⟨z, rfl, hB z hz⟩
      · exact Or.inl hp')
  rw [hQ, one_mul, Real.log_le_iff_le_exp (div_pos (by linarith) hm), div_le_iff₀ hm] at hb
  linarith

/-- Step (ii) of `s18v_moduli_bound`: if side `0` of `Q` lies in `closedBall ζ m` and every finite point of side
`2` is at distance at least `D` from side `0`, then `M(Q) D² ≤ π (m + D)²` (`s18v_disc_bound`). -/
theorem s18v_a_step_disc {Q : TopQuad} {A B : Set ℂ} {ζ : ℂ} {m D : ℝ} (hm : 0 ≤ m) (hD : 0 < D)
    (h0 : Q.side 0 ⊆ toExt A) (h2 : Q.side 2 ⊆ toExt B ∪ {extInf})
    (hA : ∀ w ∈ A, ‖w - ζ‖ ≤ m) (hAB : ∀ a ∈ A, ∀ b ∈ B, D ≤ ‖b - a‖) :
    Q.modulus * D ^ 2 ≤ π * (m + D) ^ 2 := by
  refine s18v_disc_bound Q (c := ζ) hm hD (fun p hp => ?_) (fun p hp => ?_)
  · obtain ⟨z, hz, rfl⟩ := h0 hp
    exact ⟨z, rfl, hA z hz⟩
  · rcases h2 hp with ⟨w, hw, rfl⟩ | hp'
    · refine Or.inr ⟨w, rfl, fun z hz => ?_⟩
      obtain ⟨z', hz', hzz⟩ := h0 hz
      rw [← OnePoint.coe_injective hzz]
      exact hAB z' hz' w hw
    · exact Or.inl hp'

/-- The arithmetic closing steps (ii) and (ii′): `X D² ≤ π (m + D)²` and `m ≤ c₀ M² D` give
`X ≤ π (c₀ M² + 1)²`. -/
theorem s18v_a_final {X m D M c₀ : ℝ} (hD : 0 < D) (hm0 : 0 ≤ m) (h : X * D ^ 2 ≤ π * (m + D) ^ 2)
    (hmD : m ≤ c₀ * M ^ 2 * D) : X ≤ π * (c₀ * M ^ 2 + 1) ^ 2 := by
  have h1 : m + D ≤ (c₀ * M ^ 2 + 1) * D := by linarith
  have h2 : (m + D) ^ 2 ≤ ((c₀ * M ^ 2 + 1) * D) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  have h3 : X * D ^ 2 ≤ (π * (c₀ * M ^ 2 + 1) ^ 2) * D ^ 2 := by
    calc X * D ^ 2 ≤ π * (m + D) ^ 2 := h
      _ ≤ π * ((c₀ * M ^ 2 + 1) * D) ^ 2 := mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
      _ = (π * (c₀ * M ^ 2 + 1) ^ 2) * D ^ 2 := by ring
  exact le_of_mul_le_mul_right h3 (by positivity)

/-- **Steps (i)–(ii) of the scout's route.**  Two quadrilaterals `Q₁`, `Q₂` whose sides lie on four sets
`S₁, …, S₄` in the pattern of `s18v_quads`, with `M(Q₁) = 1` and the three-point inclusions `hbt₁`, `hbt₂`, have
`M(Q₂) ≤ B(M)` and `M(Q₂.rotate) ≤ B(M)`.

*Truth.*  Let `Δ₁ = dist (S₁, S₃)`, attained at `ζ₁ ∈ S₁`, `ζ₂ ∈ S₃`, and `Δ₂ = dist (S₂, S₄)`, attained at
`η₁ ∈ S₂`, `η₂ ∈ S₄`.  Both are positive: the sets are closed or compact, nonempty and disjoint.  Put
`c₀ = 1 + e^{2π}`.
- (i) `Q₁.rotate` has sides `S₂`, `S₄` and modulus `1/M(Q₁) = 1`.  `hbt₁` puts `S₂` in `closedBall ζ₁ (MΔ₁)`, and
  then `S₄ ⊆ {|z - ζ₁| ≥ Δ₂ - MΔ₁}`.  `s18v_annulus_bound` gives `Δ₂ ≤ c₀ M Δ₁` (trivially so if
  `Δ₂ ≤ 2MΔ₁`).
- (i′) Symmetrically, `Q₁.rotate.rotate` has sides `S₃`, `S₁` and modulus `1`.  With `hbt₂`: `Δ₁ ≤ c₀ M Δ₂`.
- (ii) `Q₂.rotate.rotate` has sides `S₂ ⊆ closedBall ζ₁ (MΔ₁)` and `S₄` (at distance `≥ Δ₂`), and modulus `M(Q₂)`.
  `s18v_disc_bound` gives `M(Q₂) ≤ π (MΔ₁/Δ₂ + 1)² ≤ π (c₀M² + 1)²`.
- (ii′) `Q₂.rotate` has sides `S₃ ⊆ closedBall η₁ (MΔ₂)` and `S₁` (at distance `≥ Δ₁`).  So `M(Q₂.rotate) ≤ B` too.

*Orientation check.*  Only rotations are used (`TopQuad.rotate_side`: side `i` of `Q.rotate` is side `i + 1` of `Q`,
and `thm1_2_modulus_rotate`), never reversals.  The side hypotheses fix which set each side lies on, and they are
what `s18v_quads` proves.  `hbt₁` needs `ζ₁ ∈ S₁` (the arc before `S₂`) and `ζ₂ ∈ S₃`; `hbt₂` needs `η₁ ∈ S₂` and
`η₂ ∈ S₄`.  These are exactly the orders in which `s18v_bt_le` applies.

*Route.*  `s18v_annulus_bound`, `s18v_disc_bound`, `thm1_2_modulus_rotate` (S01:640), `TopQuad.rotate_side`
(S04:1348), `IsCompact.exists_isMinOn`, `IsClosed.exists_infDist_eq_dist`. -/
theorem s18v_moduli_bound {Q₁ Q₂ : TopQuad} {S₁ S₂ S₃ S₄ : Set ℂ} {M : ℝ} (hM : 1 ≤ M)
    (hS₁ : IsClosed S₁) (hS₂ : IsCompact S₂) (hS₃ : IsCompact S₃) (hS₄ : IsClosed S₄)
    (hn₁ : S₁.Nonempty) (hn₂ : S₂.Nonempty) (hn₃ : S₃.Nonempty) (hn₄ : S₄.Nonempty)
    (hd₁₃ : Disjoint S₁ S₃) (hd₂₄ : Disjoint S₂ S₄) (hQ₁ : Q₁.modulus = 1)
    (h10 : Q₁.side 0 ⊆ toExt S₁ ∪ {extInf}) (h11 : Q₁.side 1 ⊆ toExt S₂)
    (h12 : Q₁.side 2 ⊆ toExt S₃) (h13 : Q₁.side 3 ⊆ toExt S₄ ∪ {extInf})
    (h20 : Q₂.side 0 ⊆ toExt S₄ ∪ {extInf}) (h21 : Q₂.side 1 ⊆ toExt S₃)
    (h22 : Q₂.side 2 ⊆ toExt S₂) (h23 : Q₂.side 3 ⊆ toExt S₁ ∪ {extInf})
    (hbt₁ : ∀ ζ₁ ∈ S₁, ∀ ζ₂ ∈ S₃, ∀ w ∈ S₂, ‖w - ζ₁‖ ≤ M * ‖ζ₁ - ζ₂‖)
    (hbt₂ : ∀ η₁ ∈ S₂, ∀ η₂ ∈ S₄, ∀ w ∈ S₃, ‖w - η₁‖ ≤ M * ‖η₁ - η₂‖) :
    Q₂.modulus ≤ s18v_B M ∧ Q₂.rotate.modulus ≤ s18v_B M := by
  obtain ⟨ζ₁, hζ₁, ζ₂, hζ₂, hcl₁⟩ := s18v_a_closest hS₁ hS₃ hn₁ hn₃
  obtain ⟨η₂, hη₂, η₁, hη₁, hcl₂⟩ := s18v_a_closest hS₄ hS₂ hn₄ hn₂
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hΔ₁ : 0 < ‖ζ₁ - ζ₂‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 fun h => disjoint_left.1 hd₁₃ hζ₁ (by rwa [h]))
  have hΔ₂ : 0 < ‖η₁ - η₂‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 fun h => disjoint_left.1 hd₂₄ hη₁ (by rwa [h]))
  have hball₂ : ∀ w ∈ S₂, ‖w - ζ₁‖ ≤ M * ‖ζ₁ - ζ₂‖ := fun w hw => hbt₁ ζ₁ hζ₁ ζ₂ hζ₂ w hw
  have hball₃ : ∀ w ∈ S₃, ‖w - η₁‖ ≤ M * ‖η₁ - η₂‖ := fun w hw => hbt₂ η₁ hη₁ η₂ hη₂ w hw
  have hsep₂₄ : ∀ a ∈ S₂, ∀ b ∈ S₄, ‖η₁ - η₂‖ ≤ ‖b - a‖ := fun a ha b hb => by
    rw [norm_sub_rev η₁]
    exact hcl₂ b hb a ha
  have hsep₁₃ : ∀ a ∈ S₃, ∀ b ∈ S₁, ‖ζ₁ - ζ₂‖ ≤ ‖b - a‖ := fun a ha b hb => hcl₁ b hb a ha
  have hrr : ∀ Q : TopQuad, Q.rotate.rotate.modulus = Q.modulus := fun Q => by
    rw [thm1_2_modulus_rotate Q, thm1_2_modulus_rotate Q.rotate, one_div_one_div]
  have hrot : Q₁.rotate.modulus = 1 := by
    have h := thm1_2_modulus_rotate Q₁
    rw [hQ₁, eq_comm, one_div, inv_eq_one] at h
    exact h
  have hi : ‖η₁ - η₂‖ ≤ (1 + Real.exp (2 * π)) * (M * ‖ζ₁ - ζ₂‖) := by
    refine s18v_a_step_annulus (Q := Q₁.rotate) (B := S₄) hrot (by positivity) ?_ ?_ hball₂ fun b hb => ?_
    · rw [TopQuad.rotate_side]
      exact h11
    · rw [TopQuad.rotate_side]
      exact h13
    · have t := norm_sub_le_norm_sub_add_norm_sub b ζ₁ η₁
      have t₁ := hsep₂₄ η₁ hη₁ b hb
      have t₂ := hball₂ η₁ hη₁
      rw [norm_sub_rev ζ₁ η₁] at t
      linarith
  have hi' : ‖ζ₁ - ζ₂‖ ≤ (1 + Real.exp (2 * π)) * (M * ‖η₁ - η₂‖) := by
    refine s18v_a_step_annulus (Q := Q₁.rotate.rotate) (B := S₁) ((hrr Q₁).trans hQ₁) (by positivity) ?_ ?_
      hball₃ fun b hb => ?_
    · rw [TopQuad.rotate_side, TopQuad.rotate_side]
      exact h12
    · rw [TopQuad.rotate_side, TopQuad.rotate_side]
      exact h10
    · have t := norm_sub_le_norm_sub_add_norm_sub b η₁ ζ₂
      have t₁ := hsep₁₃ ζ₂ hζ₂ b hb
      have t₂ := hball₃ ζ₂ hζ₂
      rw [norm_sub_rev η₁ ζ₂] at t
      linarith
  have hii : Q₂.rotate.rotate.modulus * ‖η₁ - η₂‖ ^ 2 ≤ π * (M * ‖ζ₁ - ζ₂‖ + ‖η₁ - η₂‖) ^ 2 := by
    refine s18v_a_step_disc (mul_nonneg hM0 hΔ₁.le) hΔ₂ ?_ ?_ hball₂ hsep₂₄
    · rw [TopQuad.rotate_side, TopQuad.rotate_side]
      exact h22
    · rw [TopQuad.rotate_side, TopQuad.rotate_side]
      exact h20
  have hii' : Q₂.rotate.modulus * ‖ζ₁ - ζ₂‖ ^ 2 ≤ π * (M * ‖η₁ - η₂‖ + ‖ζ₁ - ζ₂‖) ^ 2 := by
    refine s18v_a_step_disc (mul_nonneg hM0 hΔ₂.le) hΔ₁ ?_ ?_ hball₃ hsep₁₃
    · rw [TopQuad.rotate_side]
      exact h21
    · rw [TopQuad.rotate_side]
      exact h23
  rw [hrr] at hii
  unfold s18v_B
  constructor
  · refine s18v_a_final hΔ₂ (mul_nonneg hM0 hΔ₁.le) hii ?_
    calc M * ‖ζ₁ - ζ₂‖ ≤ M * ((1 + Real.exp (2 * π)) * (M * ‖η₁ - η₂‖)) :=
          mul_le_mul_of_nonneg_left hi' hM0
      _ = (1 + Real.exp (2 * π)) * M ^ 2 * ‖η₁ - η₂‖ := by ring
  · refine s18v_a_final hΔ₁ (mul_nonneg hM0 hΔ₂.le) hii' ?_
    calc M * ‖η₁ - η₂‖ ≤ M * ((1 + Real.exp (2 * π)) * (M * ‖ζ₁ - ζ₂‖)) :=
          mul_le_mul_of_nonneg_left hi hM0
      _ = (1 + Real.exp (2 * π)) * M ^ 2 * ‖ζ₁ - ζ₂‖ := by ring

/-- The ratio bound: `Λ(ρ) ≤ B(M)` and `Λ(1/ρ) ≤ B(M)` for `ρ = (h x - h (x-t))/(h (x+t) - h x)` (`s18v_quads`,
`s18v_arc_props`, `s18v_bt_le`, `s18v_moduli_bound`, and `Λ(ρ) Λ(1/ρ) = 1`). -/
theorem s18v_ratio {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane} {h : ℝ → ℝ}
    (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) {M : ℝ} (hM : 1 ≤ M) (h3 : s18v_ThreePoint C Φ M)
    (hmono : StrictMono h) {x t : ℝ} (ht : 0 < t) :
    quadLambda ((h x - h (x - t)) / (h (x + t) - h x)) ≤ s18v_B M ∧
      quadLambda (1 / ((h x - h (x - t)) / (h (x + t) - h x))) ≤ s18v_B M := by
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h10, h11, h12, h13, h20, h21, h22, h23⟩ := s18v_quads hS hmono (x := x) ht
  obtain ⟨hK, hC₁, hC₂, hne⟩ := s18v_arc_props hS
  have hn : ∀ (I : Set ℝ) (s : ℝ), s ∈ I → (s18v_arc C Φ I).Nonempty := fun I s hs =>
    (hne s).mono (s18v_arc_mono (singleton_subset_iff.2 hs))
  have hsing : ∀ {I : Set ℝ} {z : ℂ}, z ∈ s18v_arc C Φ I → ∃ s ∈ I, z ∈ s18v_arc C Φ {s} :=
    fun ⟨hz, s, hs, he⟩ => ⟨s, hs, hz, s, rfl, he⟩
  have hbt₁ : ∀ ζ₁ ∈ s18v_arc C Φ (Iic (x - t)), ∀ ζ₂ ∈ s18v_arc C Φ (Icc x (x + t)),
      ∀ w ∈ s18v_arc C Φ (Icc (x - t) x), ‖w - ζ₁‖ ≤ M * ‖ζ₁ - ζ₂‖ := by
    intro ζ₁ hζ₁ ζ₂ hζ₂ w hw
    obtain ⟨u, hu, hζ₁'⟩ := hsing hζ₁
    obtain ⟨v, hv, hζ₂'⟩ := hsing hζ₂
    obtain ⟨s, hs, hw'⟩ := hsing hw
    exact s18v_bt_le hS hM h3 hζ₁' hw' hζ₂' (le_trans (mem_Iic.1 hu) hs.1) (le_trans hs.2 hv.1)
  have hbt₂ : ∀ η₁ ∈ s18v_arc C Φ (Icc (x - t) x), ∀ η₂ ∈ s18v_arc C Φ (Ici (x + t)),
      ∀ w ∈ s18v_arc C Φ (Icc x (x + t)), ‖w - η₁‖ ≤ M * ‖η₁ - η₂‖ := by
    intro η₁ hη₁ η₂ hη₂ w hw
    obtain ⟨u, hu, hη₁'⟩ := hsing hη₁
    obtain ⟨v, hv, hη₂'⟩ := hsing hη₂
    obtain ⟨s, hs, hw'⟩ := hsing hw
    exact s18v_bt_le hS hM h3 hη₁' hw' hη₂' (le_trans hu.2 hs.1) (le_trans hs.2 (mem_Ici.1 hv))
  have hd₁₃ : Disjoint (s18v_arc C Φ (Iic (x - t))) (s18v_arc C Φ (Icc x (x + t))) := by
    refine s18v_arc_disjoint (Set.disjoint_left.2 fun s hs hs' => ?_)
    exact absurd hs'.1 (not_le.2 ((mem_Iic.1 hs).trans_lt (sub_lt_self x ht)))
  have hd₂₄ : Disjoint (s18v_arc C Φ (Icc (x - t) x)) (s18v_arc C Φ (Ici (x + t))) := by
    refine s18v_arc_disjoint (Set.disjoint_left.2 fun s hs hs' => ?_)
    exact absurd (hs.2.trans_lt (lt_add_of_pos_right x ht)) (not_lt.2 (mem_Ici.1 hs'))
  obtain ⟨hb₁, hb₂⟩ := s18v_moduli_bound hM (hC₁ (x - t)) (hK (x - t) x) (hK x (x + t)) (hC₂ (x + t))
    (hn _ (x - t) (mem_Iic.2 le_rfl)) (hn _ x ⟨sub_le_self x ht.le, le_rfl⟩)
    (hn _ x ⟨le_rfl, le_add_of_nonneg_right ht.le⟩) (hn _ (x + t) (mem_Ici.2 le_rfl)) hd₁₃ hd₂₄ hQ₁
    h10 h11 h12 h13 h20 h21 h22 h23 hbt₁ hbt₂
  have hr : 0 < (h x - h (x - t)) / (h (x + t) - h x) :=
    div_pos (sub_pos.2 (hmono (sub_lt_self x ht))) (sub_pos.2 (hmono (lt_add_of_pos_right x ht)))
  refine ⟨hQ₂ ▸ hb₁, ?_⟩
  have e₁ := thm1_2_modulus_rotate Q₂
  have e₂ := eq5_20 hr
  have hpos := modulus_pos Q₂.rotate
  rw [hQ₂] at e₁
  rw [e₁, one_div, inv_mul_eq_iff_eq_mul₀ hpos.ne', mul_one] at e₂
  rw [e₂]
  exact hb₂

/-! #### Assembly for a curve through `∞` -/

/-- A quasisymmetric welding makes `C` a quasicircle with an explicit constant: the Beurling–Ahlfors extension
(`thm17_2_beurling_ahlfors`) glued by `wd_backward` and `wd_glue` (the (⇐) half of `thm16_3_welding`). -/
theorem s18v_of_qs {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane} {h : ℝ → ℝ}
    (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) {ρ : ℝ} (hqs : IsQuasisymmetric h ρ) :
    IsKQuasicircle C (8 * ρ * (ρ + 1)) := by
  obtain ⟨hinf, hC, hφ, hψ, hΦ, hΨ, hΦinf, hΨinf, hh⟩ := hS
  obtain ⟨-, hK, hs, G, hG, -, hGx⟩ := thm17_2_beurling_ahlfors hqs
  obtain ⟨H, hH, hHU, hHL, hCH⟩ := wd_backward hinf hC hφ hψ hΦ hΨ hΦinf hΨinf hh hK hs hG hGx
  have hK1 : 1 ≤ 8 * ρ * (ρ + 1) := hK.2.1
  have hH' : IsHomeomorphOnto H univ (H '' univ) := by
    rw [hH.2.2.1]
    exact hH
  have hHK : IsKQC H univ (8 * ρ * (ρ + 1)) := wd_glue hK1 hH' hHU (hHL.mono hK1)
  rw [hCH]
  exact isKQuasicircle_image_realLine hHK hH.2.2.1

/-- **The core.**  A Jordan curve through `∞` satisfying the three-point condition along `Φ` is an
`s18v_K M`-quasicircle: the welding is increasing (`s18v_weld_strictMono`), a homeomorphism (`s18v_weld_homeo`) and
`s18v_rho M`-quasisymmetric (`s18v_ratio`, `b4_le_lambdaInv`). -/
theorem s18v_core {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane} {h : ℝ → ℝ}
    (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) {M : ℝ} (hM : 1 ≤ M) (h3 : s18v_ThreePoint C Φ M) :
    IsKQuasicircle C (s18v_K M) := by
  have hmono : StrictMono h := s18v_weld_strictMono hS
  obtain ⟨hc, -, hsurj⟩ := s18v_weld_homeo hS
  refine s18v_of_qs hS ⟨hmono, hc, tendsto_atTop_atTop_of_monotone hmono.monotone fun b => ?_,
    tendsto_atBot_atBot_of_monotone hmono.monotone fun b => ?_, fun x t ht => ?_⟩
  · obtain ⟨a, ha⟩ := hsurj b
    exact ⟨a, ha.ge⟩
  · obtain ⟨a, ha⟩ := hsurj b
    exact ⟨a, ha.le⟩
  · obtain ⟨hr₁, hr₂⟩ := s18v_ratio hS hM h3 hmono ht
    have hr : 0 < (h x - h (x - t)) / (h (x + t) - h x) :=
      div_pos (sub_pos.2 (hmono (sub_lt_self x ht))) (sub_pos.2 (hmono (lt_add_of_pos_right x ht)))
    have hle₁ := b4_le_lambdaInv hr hr₁
    have hle₂ := b4_le_lambdaInv (one_div_pos.2 hr) hr₂
    have hq : qsRatio h x t = 1 / ((h x - h (x - t)) / (h (x + t) - h x)) := by
      rw [qsRatio, one_div_div]
    rw [hq]
    refine ⟨?_, hle₂⟩
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hr hle₁

/-! #### Front ends: bounded turning gives the three-point condition -/

/-- The three-point condition is monotone in the constant. -/
theorem s18v_threePoint_mono {C : Set ExtPlane} {Φ : ExtPlane → ExtPlane} {M M' : ℝ} (h3 : s18v_ThreePoint C Φ M)
    (hMM' : M ≤ M') : s18v_ThreePoint C Φ M' := by
  exact fun z₁ w z₂ hz₁ hw hz₂ u s v hu hs hv hus hsv =>
    (h3 z₁ w z₂ hz₁ hw hz₂ u s v hu hs hv hus hsv).trans (mul_le_mul_of_nonneg_right hMM' (norm_nonneg _))

/-- A parametrization `G` of `K` by `ℝ ∪ {∞}` with inverse coordinate `Θ`: the `G`-image of a preconnected set
`U ⊆ ℝ ∪ {∞}` containing the coordinate of `p ∈ K` and avoiding those of `q₁, q₂` lies in the component of `p` in
`K ∖ {q₁, q₂}`. -/
theorem s18v_b_sub {K U : Set ExtPlane} {G Θ : ExtPlane → ExtPlane}
    (hG : ContinuousOn G (toExt realLine ∪ {extInf})) (hGK : ∀ e ∈ toExt realLine ∪ {extInf}, G e ∈ K)
    (hΘG : ∀ e ∈ toExt realLine ∪ {extInf}, Θ (G e) = e) (hGΘ : ∀ q ∈ K, G (Θ q) = q)
    (hU : IsPreconnected U) (hUE : U ⊆ toExt realLine ∪ {extInf}) {q₁ q₂ p : ExtPlane}
    (h₁ : Θ q₁ ∉ U) (h₂ : Θ q₂ ∉ U) (hp : p ∈ K) (hpU : Θ p ∈ U) :
    G '' U ⊆ connectedComponentIn (K \ {q₁, q₂}) p := by
  refine (hU.image G (hG.mono hUE)).subset_connectedComponentIn ⟨Θ p, hpU, hGΘ p hp⟩ ?_
  rintro _ ⟨e, he, rfl⟩
  refine ⟨hGK e (hUE he), ?_⟩
  rintro (h | h)
  · exact h₁ (by rw [← h, hΘG e (hUE he)]; exact he)
  · exact h₂ (by rw [← h, hΘG e (hUE he)]; exact he)

/-- The two components of `K ∖ {q₁, q₂}`, for `q₁, q₂` of coordinates `u < v`: the component of any `p` contains
the arc over `(u, v)` or the arc over `(-∞, u) ∪ (v, ∞) ∪ {∞}`. -/
theorem s18v_b_comp_cases {K : Set ExtPlane} {G Θ : ExtPlane → ExtPlane}
    (hG : ContinuousOn G (toExt realLine ∪ {extInf})) (hGK : ∀ e ∈ toExt realLine ∪ {extInf}, G e ∈ K)
    (hΘG : ∀ e ∈ toExt realLine ∪ {extInf}, Θ (G e) = e) (hGΘ : ∀ q ∈ K, G (Θ q) = q)
    (hΘK : ∀ q ∈ K, Θ q ∈ toExt realLine ∪ {extInf}) {q₁ q₂ p : ExtPlane} {u v : ℝ} (huv : u < v)
    (hq₁ : q₁ ∈ K) (hq₂ : q₂ ∈ K) (h₁ : Θ q₁ = ((u : ℂ) : ExtPlane)) (h₂ : Θ q₂ = ((v : ℂ) : ExtPlane))
    (hp : p ∈ K \ {q₁, q₂}) :
    G '' ((fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Ioo u v) ⊆ connectedComponentIn (K \ {q₁, q₂}) p ∨
      G '' ((fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Iio u ∪ (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Ioi v ∪
        {extInf}) ⊆ connectedComponentIn (K \ {q₁, q₂}) p := by
  obtain ⟨hpK, hpq⟩ := hp
  have hin : Θ p ∈ (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Ioo u v →
      G '' ((fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Ioo u v) ⊆ connectedComponentIn (K \ {q₁, q₂}) p := by
    intro hpU
    refine s18v_b_sub hG hGK hΘG hGΘ (isPreconnected_Ioo.image _ s18v_b_r_continuous.continuousOn)
      (fun e ⟨s, _, hs⟩ => hs ▸ s18v_b_r_mem s) ?_ ?_ hpK hpU
    · rw [h₁]
      rintro ⟨s, hs, hsu⟩
      exact hs.1.ne' (s18v_b_r_inj hsu)
    · rw [h₂]
      rintro ⟨s, hs, hsv⟩
      exact hs.2.ne (s18v_b_r_inj hsv)
  have hout : Θ p ∈ (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Iio u ∪ (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Ioi v ∪
      {extInf} → G '' ((fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Iio u ∪ (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Ioi v ∪
        {extInf}) ⊆ connectedComponentIn (K \ {q₁, q₂}) p := by
    intro hpU
    refine s18v_b_sub hG hGK hΘG hGΘ (s18v_b_isPreconnected_out u v) ?_ ?_ ?_ hpK hpU
    · rintro e ((⟨s, -, rfl⟩ | ⟨s, -, rfl⟩) | he)
      · exact s18v_b_r_mem s
      · exact s18v_b_r_mem s
      · exact Or.inr he
    · rw [h₁]
      rintro ((⟨s, hs, hsu⟩ | ⟨s, hs, hsu⟩) | h)
      · exact (mem_Iio.1 hs).ne (s18v_b_r_inj hsu)
      · exact (huv.trans (mem_Ioi.1 hs)).ne' (s18v_b_r_inj hsu)
      · exact OnePoint.coe_ne_infty _ h
    · rw [h₂]
      rintro ((⟨s, hs, hsv⟩ | ⟨s, hs, hsv⟩) | h)
      · exact ((mem_Iio.1 hs).trans huv).ne (s18v_b_r_inj hsv)
      · exact (mem_Ioi.1 hs).ne' (s18v_b_r_inj hsv)
      · exact OnePoint.coe_ne_infty _ h
  rcases s18v_b_E_cases (hΘK p hpK) with he | ⟨s, hs⟩
  · exact Or.inr (hout (Or.inr he))
  · have hsu : s ≠ u := by
      rintro rfl
      exact hpq (Or.inl (by rw [← hGΘ p hpK, hs, ← h₁, hGΘ q₁ hq₁]))
    have hsv : s ≠ v := by
      rintro rfl
      exact hpq (Or.inr (show p = q₂ by rw [← hGΘ p hpK, hs, ← h₂, hGΘ q₂ hq₂]))
    rcases lt_or_gt_of_ne hsu with h | h
    · exact Or.inr (hout (Or.inl (Or.inl ⟨s, h, hs.symm⟩)))
    · rcases lt_or_gt_of_ne hsv with h' | h'
      · exact Or.inl (hin ⟨s, ⟨h, h'⟩, hs.symm⟩)
      · exact Or.inr (hout (Or.inl (Or.inr ⟨s, h', hs.symm⟩)))

/-- The end points of an arc: `G(s)` lies in the closure of `G(I)` for `s ∈ closure I`. -/
theorem s18v_b_mem_closure {G : ExtPlane → ExtPlane} (hG : ContinuousOn G (toExt realLine ∪ {extInf}))
    {I : Set ℝ} {s : ℝ} (hs : s ∈ closure I) :
    G ((s : ℂ) : ExtPlane) ∈ closure (G '' ((fun s : ℝ => ((s : ℂ) : ExtPlane)) '' I)) := by
  have hc : Continuous (fun s : ℝ => G ((s : ℂ) : ExtPlane)) :=
    hG.comp_continuous s18v_b_r_continuous s18v_b_r_mem
  rw [image_image]
  exact mem_closure_image hc.continuousAt hs

/-- Two finite points in the closure of a set `P ⊆ ℂ̄` whose finite part has diameter at most `D` are at distance
at most `D`. -/
theorem s18v_b_dist_le {P : Set ExtPlane} {x y : ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hdiam : Metric.ediam {z : ℂ | (z : ExtPlane) ∈ P} ≤ ENNReal.ofReal D)
    (hx : (x : ExtPlane) ∈ closure P) (hy : (y : ExtPlane) ∈ closure P) : ‖x - y‖ ≤ D := by
  have key : ∀ z : ℂ, (z : ExtPlane) ∈ closure P → z ∈ closure {z : ℂ | (z : ExtPlane) ∈ P} := by
    intro z hz
    rw [OnePoint.isOpenEmbedding_coe.isInducing.closure_eq_preimage_closure_image]
    have hsplit : P ⊆ ((↑) : ℂ → ExtPlane) '' {z : ℂ | (z : ExtPlane) ∈ P} ∪ {extInf} := by
      intro q hq
      rcases uq_j_eq_infty_or_coe q with rfl | ⟨w, rfl⟩
      · exact Or.inr rfl
      · exact Or.inl ⟨w, hq, rfl⟩
    have h := closure_mono hsplit hz
    rw [closure_union, closure_singleton] at h
    rcases h with h | h
    · exact h
    · exact absurd h (OnePoint.coe_ne_infty z)
  have h := Metric.edist_le_ediam_of_mem (key x hx) (key y hy)
  rw [Metric.ediam_closure] at h
  have h2 := h.trans hdiam
  rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hD, dist_eq_norm] at h2
  exact h2

/-- **Front end through `∞`.**  Bounded turning of `C ∋ ∞` gives the three-point condition along `Φ` with the
same constant.

*Truth.*  Take finite `z₁, w, z₂ ∈ C` with `Φ`-coordinates `u < s < v`.
- Bounded turning at `(z₁, z₂)` gives a component `P` of `C ∖ {z₁, z₂}` with `∞ ∉ P` and `diam P ≤ M |z₁ - z₂|`.
- `Φ` is a homeomorphism of `C` onto `ℝ ∪ {∞}` (`image_connectedComponentIn_of_isEmbedding`).  The component of a
  point whose coordinate lies outside `[u, v]` contains `∞`, since `toExt (Iio u ∪ Ioi v) ∪ {∞}` is connected.  So `P`
  is the arc over `(u, v)`, and it contains `w`.
- `z₁` lies in the closure of that arc (continuity of `Φ⁻¹`), so `|w - z₁| ≤ diam P ≤ M |z₁ - z₂|`
  (`Metric.ediam_closure`).

*Orientation check.*  The statement is symmetric under reversing the order.  The condition `∞ ∉ P` selects the
finite arc, whichever way `Φ` runs.

*Route.*  `image_connectedComponentIn_of_isEmbedding` (Quadrilateral:38), `isHomeoExtension_invFunOn`,
`Metric.ediam_closure`, and the arc lemmas shared with `s18v_quads`. -/
theorem s18v_threePoint_of_bt {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    {h : ℝ → ℝ} (hS : s18v_Setup C A₁ A₂ φ ψ Φ Ψ h) {M : ℝ} (hbt : IsBoundedTurning C M) :
    s18v_ThreePoint C Φ M := by
  intro z₁ w z₂ hz₁ hw hz₂ u s v hu hs hv hus hsv
  obtain ⟨hGc, hGC, hΦG, hGΦ, hΦE⟩ := s18v_b_param hS
  have huv : u < v := hus.trans hsv
  have hne : z₁ ≠ z₂ := by
    rintro rfl
    exact huv.ne (s18v_b_r_inj (hu.symm.trans hv))
  obtain ⟨p, hp, hpinf, hdiam⟩ := hbt.2.2 z₁ z₂ hz₁ hz₂ hne
  have hMd : 0 ≤ M * ‖z₁ - z₂‖ := mul_nonneg (by linarith [hbt.2.1]) (norm_nonneg _)
  rcases s18v_b_comp_cases hGc hGC hΦG hGΦ hΦE huv hz₁ hz₂ hu hv hp with hA | hB
  · -- the component is the finite arc over `(u, v)`: it contains `w`, and `z₁` is in its closure
    have hwP : (w : ExtPlane) ∈ connectedComponentIn (C \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) p :=
      hA ⟨((s : ℂ) : ExtPlane), ⟨s, ⟨hus, hsv⟩, rfl⟩, by rw [← hs]; exact hGΦ _ hw⟩
    have hz₁P : (z₁ : ExtPlane) ∈ closure (connectedComponentIn (C \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) p) := by
      have h1 := s18v_b_mem_closure hGc (I := Ioo u v) (s := u) (by rw [closure_Ioo huv.ne]; exact ⟨le_rfl, huv.le⟩)
      rw [← hu, hGΦ _ hz₁] at h1
      exact closure_mono hA h1
    exact s18v_b_dist_le hMd hdiam (subset_closure hwP) hz₁P
  · -- the other arc contains `∞`, which the bounded-turning component avoids
    refine absurd (hB ⟨extInf, Or.inr rfl, ?_⟩) hpinf
    have h1 := hGΦ _ hS.1
    rwa [hS.2.2.2.2.2.2.1] at h1

/-- The two components of `K ∖ {q₁, q₂}` when `q₂` has coordinate `∞` and `q₁` has coordinate `c`: the component of
any `p` contains the arc over `(-∞, c)` or the arc over `(c, ∞)`. -/
theorem s18v_b_comp_cases_inf {K : Set ExtPlane} {G Θ : ExtPlane → ExtPlane}
    (hG : ContinuousOn G (toExt realLine ∪ {extInf})) (hGK : ∀ e ∈ toExt realLine ∪ {extInf}, G e ∈ K)
    (hΘG : ∀ e ∈ toExt realLine ∪ {extInf}, Θ (G e) = e) (hGΘ : ∀ q ∈ K, G (Θ q) = q)
    (hΘK : ∀ q ∈ K, Θ q ∈ toExt realLine ∪ {extInf}) {q₁ q₂ p : ExtPlane} {c : ℝ} (hq₁ : q₁ ∈ K) (hq₂ : q₂ ∈ K)
    (h₁ : Θ q₁ = ((c : ℂ) : ExtPlane)) (h₂ : Θ q₂ = extInf) (hp : p ∈ K \ {q₁, q₂}) :
    G '' ((fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Iio c) ⊆ connectedComponentIn (K \ {q₁, q₂}) p ∨
      G '' ((fun s : ℝ => ((s : ℂ) : ExtPlane)) '' Ioi c) ⊆ connectedComponentIn (K \ {q₁, q₂}) p := by
  obtain ⟨hpK, hpq⟩ := hp
  have hUE : ∀ I : Set ℝ, (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' I ⊆ toExt realLine ∪ {extInf} :=
    fun I e ⟨s', _, hs'⟩ => hs' ▸ s18v_b_r_mem s'
  have hinf : ∀ I : Set ℝ, Θ q₂ ∉ (fun s : ℝ => ((s : ℂ) : ExtPlane)) '' I := by
    rintro I ⟨s', -, hs'⟩
    rw [h₂] at hs'
    exact OnePoint.coe_ne_infty _ hs'
  rcases s18v_b_E_cases (hΘK p hpK) with he | ⟨s', hs'⟩
  · exact (hpq (Or.inr (show p = q₂ by rw [← hGΘ p hpK, he, ← h₂, hGΘ q₂ hq₂]))).elim
  · have hne : s' ≠ c := by
      rintro rfl
      exact hpq (Or.inl (by rw [← hGΘ p hpK, hs', ← h₁, hGΘ q₁ hq₁]))
    rcases lt_or_gt_of_ne hne with h | h
    · refine Or.inl (s18v_b_sub hG hGK hΘG hGΘ (isPreconnected_Iio.image _ s18v_b_r_continuous.continuousOn)
        (hUE _) ?_ (hinf _) hpK ⟨s', h, hs'.symm⟩)
      rw [h₁]
      rintro ⟨s'', hs'', he⟩
      exact (mem_Iio.1 hs'').ne (s18v_b_r_inj he)
    · refine Or.inr (s18v_b_sub hG hGK hΘG hGΘ (isPreconnected_Ioi.image _ s18v_b_r_continuous.continuousOn)
        (hUE _) ?_ (hinf _) hpK ⟨s', h, hs'.symm⟩)
      rw [h₁]
      rintro ⟨s'', hs'', he⟩
      exact (mem_Ioi.1 hs'').ne' (s18v_b_r_inj he)

/-- `w ↦ a + 1/w` inverts `w ↦ 1/(w - a)` on `ℂ̄` (a local copy of `s18v_mobius_inv_self`, which comes later in
the file). -/
theorem s18v_b_mobius_inv (a : ℂ) (p : ExtPlane) : mobiusExt a 1 1 0 (mobiusExt 0 1 1 (-a) p) = p := by
  rw [s16p_mobiusExt_comp (by norm_num : (0 : ℂ) * (-a) - 1 * 1 ≠ 0)]
  have e₁ : a * 0 + 1 * 1 = (1 : ℂ) := by ring
  have e₂ : a * 1 + 1 * -a = (0 : ℂ) := by ring
  have e₃ : (1 : ℂ) * 0 + 0 * 1 = 0 := by ring
  have e₄ : (1 : ℂ) * 1 + 0 * -a = 1 := by ring
  rw [e₁, e₂, e₃, e₄]
  induction p using OnePoint.rec with
  | infty => exact mobiusExt_infty_of_eq rfl
  | coe z =>
    rw [mobiusExt_coe (by simp : (0 : ℂ) * z + 1 ≠ 0)]
    congr 1
    simp [mobiusFn]

/-- `w ↦ 1/(w - a)` at a finite point `z ≠ a`. -/
theorem s18v_b_T_coe {a z : ℂ} (hz : z ≠ a) :
    mobiusExt 0 1 1 (-a) (z : ExtPlane) = (((z - a)⁻¹ : ℂ) : ExtPlane) := by
  have hden : (1 : ℂ) * z + -a ≠ 0 := by
    rw [one_mul, ← sub_eq_add_neg]
    exact sub_ne_zero.mpr hz
  rw [mobiusExt_coe hden]
  congr 1
  simp only [mobiusFn]
  ring

/-- A finite point `z'` of `T '' C`, `T w = 1/(w - a)`, `∞ ∉ C`, is `1/(z - a)` for a finite `z ∈ C ∖ {a}`. -/
theorem s18v_b_T_pre {C : Set ExtPlane} (hinf : extInf ∉ C) {a z' : ℂ}
    (hz' : (z' : ExtPlane) ∈ mobiusExt 0 1 1 (-a) '' C) :
    ∃ z : ℂ, (z : ExtPlane) ∈ C ∧ z ≠ a ∧ z' = (z - a)⁻¹ ∧
      mobiusExt 0 1 1 (-a) (z : ExtPlane) = (z' : ExtPlane) := by
  have hTa : mobiusExt 0 1 1 (-a) (a : ExtPlane) = extInf := mobiusExt_coe_of_eq_zero (by ring)
  obtain ⟨q, hq, hTq⟩ := hz'
  rcases uq_j_eq_infty_or_coe q with rfl | ⟨z, rfl⟩
  · exact absurd hq hinf
  · have hza : z ≠ a := by
      rintro rfl
      rw [hTa] at hTq
      exact OnePoint.coe_ne_infty _ hTq.symm
    refine ⟨z, hq, hza, ?_, hTq⟩
    rw [s18v_b_T_coe hza] at hTq
    exact (OnePoint.coe_injective hTq).symm

/-- The algebra of `w ↦ 1/(w - a)`: `‖w - z₁‖ ‖z₂ - a‖ ≤ L ‖z₁ - z₂‖ ‖w - a‖` gives
`‖1/(w-a) - 1/(z₁-a)‖ ≤ L ‖1/(z₁-a) - 1/(z₂-a)‖` (the converse direction of `n18_inv_algebra`). -/
theorem s18v_b_inv_algebra {w z₁ z₂ a : ℂ} {L : ℝ} (hw : w ≠ a) (h1 : z₁ ≠ a) (h2 : z₂ ≠ a)
    (h : ‖w - z₁‖ * ‖z₂ - a‖ ≤ L * ‖z₁ - z₂‖ * ‖w - a‖) :
    ‖(w - a)⁻¹ - (z₁ - a)⁻¹‖ ≤ L * ‖(z₁ - a)⁻¹ - (z₂ - a)⁻¹‖ := by
  have hw' : w - a ≠ 0 := sub_ne_zero.mpr hw
  have h1' : z₁ - a ≠ 0 := sub_ne_zero.mpr h1
  have h2' : z₂ - a ≠ 0 := sub_ne_zero.mpr h2
  have e1 : (w - a)⁻¹ - (z₁ - a)⁻¹ = (z₁ - w) / ((w - a) * (z₁ - a)) := by
    field_simp
    ring
  have e2 : (z₁ - a)⁻¹ - (z₂ - a)⁻¹ = (z₂ - z₁) / ((z₁ - a) * (z₂ - a)) := by
    field_simp
    ring
  rw [e1, e2, norm_div, norm_div, norm_mul, norm_mul, norm_sub_rev z₁ w, norm_sub_rev z₂ z₁]
  have hA : 0 < ‖w - a‖ := norm_pos_iff.mpr hw'
  have hB : 0 < ‖z₁ - a‖ := norm_pos_iff.mpr h1'
  have hD : 0 < ‖z₂ - a‖ := norm_pos_iff.mpr h2'
  rw [div_le_iff₀ (mul_pos hA hB)]
  have e3 : L * (‖z₁ - z₂‖ / (‖z₁ - a‖ * ‖z₂ - a‖)) * (‖w - a‖ * ‖z₁ - a‖) =
      L * ‖z₁ - z₂‖ * ‖w - a‖ / ‖z₂ - a‖ := by
    field_simp
  rw [e3, le_div_iff₀ hD]
  exact h

/-- The six cases of the constant `(M + 1)²`, in real numbers: `X = |w - z₁|`, `Y = |w - z₂|`, `P = |a - z₁|`,
`D = |z₂ - a|`, `d = |z₁ - z₂|`, `e = |w - a|`, with the triangle inequalities `t1`–`t3`. -/
theorem s18v_b_six_real {X Y P D d e M : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hd : 0 ≤ d) (he : 0 ≤ e)
    (t1 : D ≤ Y + e) (t2 : X ≤ e + P) (t3 : X ≤ Y + d)
    (hAB : (X ≤ M * d ∧ Y ≤ M * d) ∨ (P ≤ M * d ∧ D ≤ M * d)) (hαβ : X ≤ M * e ∨ Y ≤ M * e) :
    X * D ≤ (M + 1) ^ 2 * d * e := by
  have hde := mul_nonneg hd he
  have hM1 : 0 ≤ M + 1 := by linarith
  rcases hAB with ⟨hXd, hYd⟩ | ⟨hPd, hDd⟩ <;> rcases hαβ with hXe | hYe
  · rcases le_total d e with hle | hle
    · calc X * D ≤ (M * d) * ((M + 1) * e) :=
            mul_le_mul hXd (by nlinarith) hD (mul_nonneg hM hd)
        _ ≤ (M + 1) ^ 2 * d * e := by nlinarith [mul_nonneg hde hM1]
    · calc X * D ≤ (M * e) * ((M + 1) * d) :=
            mul_le_mul hXe (by nlinarith) hD (mul_nonneg hM he)
        _ ≤ (M + 1) ^ 2 * d * e := by nlinarith [mul_nonneg hde hM1]
  · calc X * D ≤ (M * d) * ((M + 1) * e) :=
          mul_le_mul hXd (by nlinarith) hD (mul_nonneg hM hd)
      _ ≤ (M + 1) ^ 2 * d * e := by nlinarith [mul_nonneg hde hM1]
  · calc X * D ≤ (M * e) * (M * d) := mul_le_mul hXe hDd hD (mul_nonneg hM he)
      _ ≤ (M + 1) ^ 2 * d * e := by nlinarith [mul_nonneg hde hM1, mul_nonneg hde hM]
  · rcases le_total d e with hle | hle
    · calc X * D ≤ ((M + 1) * e) * (M * d) :=
            mul_le_mul (by nlinarith) hDd hD (mul_nonneg hM1 he)
        _ ≤ (M + 1) ^ 2 * d * e := by nlinarith [mul_nonneg hde hM1]
    · calc X * D ≤ ((M + 1) * d) * ((M + 1) * e) :=
            mul_le_mul (by nlinarith) (by nlinarith) hD (mul_nonneg hM1 hd)
        _ = (M + 1) ^ 2 * d * e := by ring

/-- The six cases of the constant `(M + 1)²`: bounded turning at `(z₁, z₂)` puts `w` or `a` within `M |z₁ - z₂|` of
both `z₁, z₂`, and bounded turning at `(w, a)` puts `z₁` or `z₂` within `M |w - a|` of `w`; in all cases
`|w - z₁| |z₂ - a| ≤ (M + 1)² |z₁ - z₂| |w - a|`. -/
theorem s18v_b_six {w z₁ z₂ a : ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hAB : (‖w - z₁‖ ≤ M * ‖z₁ - z₂‖ ∧ ‖w - z₂‖ ≤ M * ‖z₁ - z₂‖) ∨
      (‖a - z₁‖ ≤ M * ‖z₁ - z₂‖ ∧ ‖a - z₂‖ ≤ M * ‖z₁ - z₂‖))
    (hαβ : ‖z₁ - w‖ ≤ M * ‖w - a‖ ∨ ‖z₂ - w‖ ≤ M * ‖w - a‖) :
    ‖w - z₁‖ * ‖z₂ - a‖ ≤ (M + 1) ^ 2 * ‖z₁ - z₂‖ * ‖w - a‖ := by
  have t1 : ‖z₂ - a‖ ≤ ‖w - z₂‖ + ‖w - a‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub z₂ w a
    rwa [norm_sub_rev z₂ w] at this
  have t2 : ‖w - z₁‖ ≤ ‖w - a‖ + ‖a - z₁‖ := norm_sub_le_norm_sub_add_norm_sub w a z₁
  have t3 : ‖w - z₁‖ ≤ ‖w - z₂‖ + ‖z₁ - z₂‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub w z₂ z₁
    rwa [norm_sub_rev z₂ z₁] at this
  rw [norm_sub_rev z₁ w, norm_sub_rev z₂ w] at hαβ
  rw [norm_sub_rev a z₂] at hAB
  exact s18v_b_six_real hM (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) t1 t2 t3 hAB hαβ

/-- **Front end off `∞`.**  If `C ∌ ∞` is of `M`-bounded turning and `a ∈ C`, then the curve
`C' = T '' C`, `T w = 1/(w - a)`, satisfies the three-point condition along its own `Φ` with constant `(M + 1)²`.

*Truth.*  `C' ∋ ∞ = T a`.  Its finite points are the `T z` with `z ∈ C ∖ {a}`, and `0 ∉ C'` because `∞ ∉ C`.
Take finite `z₁', w', z₂' ∈ C'` with coordinates `u < s < v`, and put `z_j = T⁻¹ z_j'`, `w = T⁻¹ w'`,
`d = |z₁ - z₂|`.
- Bounded turning at `(z₁, z₂)`.  `T` carries the components of `C ∖ {z₁, z₂}` onto those of `C' ∖ {z₁', z₂'}`
  (`gsep_z_connectedComponentIn_image_homeomorph`).  As in `s18v_threePoint_of_bt`, such a component either
  contains the arc over `(u, v)`, so `|w - z_j| ≤ M d`, or contains `∞` and the arcs over `Iio u ∪ Ioi v`, so
  `a = T⁻¹ ∞` lies in it and `|a - z_j| ≤ M d`.  (`z_j` is in the closure, by continuity.)
- Bounded turning at `(w, a)`.  The components of `C' ∖ {w', ∞}` contain the arc over `Iio s` or the arc over
  `Ioi s`.  So `|z₁ - w| ≤ M |w - a|` or `|z₂ - w| ≤ M |w - a|`.
- In all six cases (split further by `|w - a| ≥ d` or `< d`), `|w - z₁| |z₂ - a| ≤ (M + 1)² d |w - a|`.  For
  example: the finite arc, `|w - a| < d` and `|z₂ - w| ≤ M|w - a|` give `|z₂ - a| ≤ (M + 1)|w - a|` and
  `|w - z₁| ≤ M d`; the arc through `a`, `|w - a| < d` and `|z₂ - w| ≤ M|w - a|` give `|w - z₁| ≤ (M + 1) d` and
  `|z₂ - a| ≤ (M + 1)|w - a|`.
- By `|1/(p - a) - 1/(q - a)| = |p - q| / (|p - a| |q - a|)` (the `n18_inv_algebra` pattern), this is
  `|w' - z₁'| ≤ (M + 1)² |z₁' - z₂'|`.

*Orientation check.*  Only the order `u < s < v` along `Φ` is used, and both bounded-turning applications are
symmetric in their two points.

*Route.*  `gsep_z_connectedComponentIn_image_homeomorph`, `mobiusHomeomorph`, `n18_inv_algebra` (S18:379), and the
arc lemmas of `s18v_threePoint_of_bt`. -/
theorem s18v_threePoint_mobius {C : Set ExtPlane} {M : ℝ} (hbt : IsBoundedTurning C M) (hinf : extInf ∉ C) {a : ℂ}
    (ha : (a : ExtPlane) ∈ C) {A₁ A₂ : Set ℂ} {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane} {h : ℝ → ℝ}
    (hS : s18v_Setup (mobiusExt 0 1 1 (-a) '' C) A₁ A₂ φ ψ Φ Ψ h) :
    s18v_ThreePoint (mobiusExt 0 1 1 (-a) '' C) Φ ((M + 1) ^ 2) := by
  intro z₁' w' z₂' hz₁' hw' hz₂' u s v hu hs hv hus hsv
  obtain ⟨hGc, hGC, hΦG, hGΦ, hΦE⟩ := s18v_b_param hS
  -- the parametrization `G = T⁻¹ ∘ Φ⁻¹` of `C`, with coordinate `Θ = Φ ∘ T`
  have hTi : Continuous (mobiusExt a 1 1 0) := continuous_mobiusExt (by norm_num)
  have hG : ContinuousOn (fun e => mobiusExt a 1 1 0 (Function.invFunOn Φ (closure (toExt A₁)) e))
      (toExt realLine ∪ {extInf}) := hTi.comp_continuousOn hGc
  have hGK : ∀ e ∈ toExt realLine ∪ {extInf},
      mobiusExt a 1 1 0 (Function.invFunOn Φ (closure (toExt A₁)) e) ∈ C := by
    intro e he
    obtain ⟨q, hq, hqe⟩ := hGC e he
    rw [← hqe, s18v_b_mobius_inv]
    exact hq
  have hΘG : ∀ e ∈ toExt realLine ∪ {extInf},
      Φ (mobiusExt 0 1 1 (-a) (mobiusExt a 1 1 0 (Function.invFunOn Φ (closure (toExt A₁)) e))) = e := by
    intro e he
    obtain ⟨q, hq, hqe⟩ := hGC e he
    rw [← hqe, s18v_b_mobius_inv, hqe]
    exact hΦG e he
  have hGΘ : ∀ q ∈ C,
      mobiusExt a 1 1 0 (Function.invFunOn Φ (closure (toExt A₁)) (Φ (mobiusExt 0 1 1 (-a) q))) = q := by
    intro q hq
    rw [hGΦ _ (mem_image_of_mem _ hq), s18v_b_mobius_inv]
  have hΘK : ∀ q ∈ C, Φ (mobiusExt 0 1 1 (-a) q) ∈ toExt realLine ∪ {extInf} :=
    fun q hq => hΦE _ (mem_image_of_mem _ hq)
  -- the three points and `a` in the coordinate `Θ`
  obtain ⟨z₁, hz₁C, hz₁a, rfl, hT₁⟩ := s18v_b_T_pre hinf hz₁'
  obtain ⟨w, hwC, hwa, rfl, hTw⟩ := s18v_b_T_pre hinf hw'
  obtain ⟨z₂, hz₂C, hz₂a, rfl, hT₂⟩ := s18v_b_T_pre hinf hz₂'
  have hΘ₁ : Φ (mobiusExt 0 1 1 (-a) (z₁ : ExtPlane)) = ((u : ℂ) : ExtPlane) := by rw [hT₁]; exact hu
  have hΘw : Φ (mobiusExt 0 1 1 (-a) (w : ExtPlane)) = ((s : ℂ) : ExtPlane) := by rw [hTw]; exact hs
  have hΘ₂ : Φ (mobiusExt 0 1 1 (-a) (z₂ : ExtPlane)) = ((v : ℂ) : ExtPlane) := by rw [hT₂]; exact hv
  have hΘa : Φ (mobiusExt 0 1 1 (-a) (a : ExtPlane)) = extInf := by
    rw [mobiusExt_coe_of_eq_zero (by ring)]
    exact hS.2.2.2.2.2.2.1
  have huv : u < v := hus.trans hsv
  have hne : z₁ ≠ z₂ := by
    rintro rfl
    exact huv.ne (s18v_b_r_inj (hΘ₁.symm.trans hΘ₂))
  have hM0 : 0 ≤ M := by linarith [hbt.2.1]
  -- bounded turning at `(z₁, z₂)`: the finite arc (through `w`) or the arc through `a`
  obtain ⟨p, hp, -, hdiam⟩ := hbt.2.2 z₁ z₂ hz₁C hz₂C hne
  have hMd : 0 ≤ M * ‖z₁ - z₂‖ := mul_nonneg hM0 (norm_nonneg _)
  have hAB : (‖w - z₁‖ ≤ M * ‖z₁ - z₂‖ ∧ ‖w - z₂‖ ≤ M * ‖z₁ - z₂‖) ∨
      (‖a - z₁‖ ≤ M * ‖z₁ - z₂‖ ∧ ‖a - z₂‖ ≤ M * ‖z₁ - z₂‖) := by
    rcases s18v_b_comp_cases hG hGK hΘG hGΘ hΘK huv hz₁C hz₂C hΘ₁ hΘ₂ hp with hA | hB
    · have hwP : (w : ExtPlane) ∈ connectedComponentIn (C \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) p :=
        hA ⟨((s : ℂ) : ExtPlane), ⟨s, ⟨hus, hsv⟩, rfl⟩, by rw [← hΘw]; exact hGΘ _ hwC⟩
      have hc₁ : (z₁ : ExtPlane) ∈ closure (connectedComponentIn (C \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) p) := by
        have h1 := s18v_b_mem_closure hG (I := Ioo u v) (s := u)
          (by rw [closure_Ioo huv.ne]; exact ⟨le_rfl, huv.le⟩)
        rw [← hΘ₁, hGΘ _ hz₁C] at h1
        exact closure_mono hA h1
      have hc₂ : (z₂ : ExtPlane) ∈ closure (connectedComponentIn (C \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) p) := by
        have h1 := s18v_b_mem_closure hG (I := Ioo u v) (s := v)
          (by rw [closure_Ioo huv.ne]; exact ⟨huv.le, le_rfl⟩)
        rw [← hΘ₂, hGΘ _ hz₂C] at h1
        exact closure_mono hA h1
      exact Or.inl ⟨s18v_b_dist_le hMd hdiam (subset_closure hwP) hc₁,
        s18v_b_dist_le hMd hdiam (subset_closure hwP) hc₂⟩
    · have haP : (a : ExtPlane) ∈ connectedComponentIn (C \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) p :=
        hB ⟨extInf, Or.inr rfl, by rw [← hΘa]; exact hGΘ _ ha⟩
      have hc₁ : (z₁ : ExtPlane) ∈ closure (connectedComponentIn (C \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) p) := by
        have h1 := s18v_b_mem_closure hG (I := Iio u) (s := u) (by rw [closure_Iio]; exact mem_Iic.2 le_rfl)
        rw [← hΘ₁, hGΘ _ hz₁C] at h1
        exact closure_mono ((image_mono (subset_union_left.trans subset_union_left)).trans hB) h1
      have hc₂ : (z₂ : ExtPlane) ∈ closure (connectedComponentIn (C \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) p) := by
        have h1 := s18v_b_mem_closure hG (I := Ioi v) (s := v) (by rw [closure_Ioi]; exact mem_Ici.2 le_rfl)
        rw [← hΘ₂, hGΘ _ hz₂C] at h1
        exact closure_mono ((image_mono (subset_union_right.trans subset_union_left)).trans hB) h1
      exact Or.inr ⟨s18v_b_dist_le hMd hdiam (subset_closure haP) hc₁,
        s18v_b_dist_le hMd hdiam (subset_closure haP) hc₂⟩
  -- bounded turning at `(w, a)`: the arc through `z₁` or the arc through `z₂`
  obtain ⟨p', hp', -, hdiam'⟩ := hbt.2.2 w a hwC ha hwa
  have hMe : 0 ≤ M * ‖w - a‖ := mul_nonneg hM0 (norm_nonneg _)
  have hαβ : ‖z₁ - w‖ ≤ M * ‖w - a‖ ∨ ‖z₂ - w‖ ≤ M * ‖w - a‖ := by
    rcases s18v_b_comp_cases_inf hG hGK hΘG hGΘ hΘK hwC ha hΘw hΘa hp' with h1 | h1
    · have hzP : (z₁ : ExtPlane) ∈ connectedComponentIn (C \ {(w : ExtPlane), (a : ExtPlane)}) p' :=
        h1 ⟨((u : ℂ) : ExtPlane), ⟨u, hus, rfl⟩, by rw [← hΘ₁]; exact hGΘ _ hz₁C⟩
      have hc : (w : ExtPlane) ∈ closure (connectedComponentIn (C \ {(w : ExtPlane), (a : ExtPlane)}) p') := by
        have h2 := s18v_b_mem_closure hG (I := Iio s) (s := s) (by rw [closure_Iio]; exact mem_Iic.2 le_rfl)
        rw [← hΘw, hGΘ _ hwC] at h2
        exact closure_mono h1 h2
      exact Or.inl (s18v_b_dist_le hMe hdiam' (subset_closure hzP) hc)
    · have hzP : (z₂ : ExtPlane) ∈ connectedComponentIn (C \ {(w : ExtPlane), (a : ExtPlane)}) p' :=
        h1 ⟨((v : ℂ) : ExtPlane), ⟨v, hsv, rfl⟩, by rw [← hΘ₂]; exact hGΘ _ hz₂C⟩
      have hc : (w : ExtPlane) ∈ closure (connectedComponentIn (C \ {(w : ExtPlane), (a : ExtPlane)}) p') := by
        have h2 := s18v_b_mem_closure hG (I := Ioi s) (s := s) (by rw [closure_Ioi]; exact mem_Ici.2 le_rfl)
        rw [← hΘw, hGΘ _ hwC] at h2
        exact closure_mono h1 h2
      exact Or.inr (s18v_b_dist_le hMe hdiam' (subset_closure hzP) hc)
  exact s18v_b_inv_algebra hwa hz₁a hz₂a (s18v_b_six hM0 hAB hαβ)

/-! #### The Möbius move for a curve not through `∞` -/

/-- The image of a `K`-quasicircle under a fractional linear transformation is a `K`-quasicircle (the `K`-explicit
form of `s16p_isQuasicircle_mobius_image`). -/
theorem s18v_isKQuasicircle_mobius_image {C : Set ExtPlane} {K : ℝ} (hC : IsKQuasicircle C K) {a b c d : ℂ}
    (h : a * d - b * c ≠ 0) : IsKQuasicircle (mobiusExt a b c d '' C) K := by
  obtain ⟨f, hf, hs, M, ⟨α, β, κ, δ, hdet, rfl⟩, rfl⟩ := hC
  refine ⟨f, hf, hs, mobiusExt (a * α + b * κ) (a * β + b * δ) (c * α + d * κ) (c * β + d * δ),
    ⟨_, _, _, _, ?_, rfl⟩, ?_⟩
  · have hmul : (a * α + b * κ) * (c * β + d * δ) - (a * β + b * δ) * (c * α + d * κ) =
        (a * d - b * c) * (α * δ - β * κ) := by ring
    rw [hmul]
    exact mul_ne_zero h hdet
  · rw [image_image]
    exact image_congr fun w _ => s16p_mobiusExt_comp hdet w

/-- `w ↦ a + 1/w` inverts `w ↦ 1/(w - a)` on `ℂ̄`. -/
theorem s18v_mobius_inv_self (a : ℂ) (p : ExtPlane) : mobiusExt a 1 1 0 (mobiusExt 0 1 1 (-a) p) = p := by
  rw [s16p_mobiusExt_comp (by norm_num : (0 : ℂ) * (-a) - 1 * 1 ≠ 0)]
  have e₁ : a * 0 + 1 * 1 = (1 : ℂ) := by ring
  have e₂ : a * 1 + 1 * -a = (0 : ℂ) := by ring
  have e₃ : (1 : ℂ) * 0 + 0 * 1 = 0 := by ring
  have e₄ : (1 : ℂ) * 1 + 0 * -a = 1 := by ring
  rw [e₁, e₂, e₃, e₄]
  induction p using OnePoint.rec with
  | infty => exact mobiusExt_infty_of_eq rfl
  | coe z =>
    rw [mobiusExt_coe (by simp : (0 : ℂ) * z + 1 ≠ 0)]
    congr 1
    simp [mobiusFn]

/-- A Jordan curve not through `∞` has a finite point. -/
theorem s18v_exists_finite {C : Set ExtPlane} (hJ : IsJordanCurve C) (hinf : extInf ∉ C) :
    ∃ a : ℂ, (a : ExtPlane) ∈ C := by
  obtain ⟨γ, -, -, hγr⟩ := hJ
  have hmem : γ 1 ∈ C := hγr ▸ mem_range_self 1
  rcases uq_j_eq_infty_or_coe (γ 1) with h | ⟨z, hz⟩
  · exact absurd (h ▸ hmem) hinf
  · exact ⟨z, hz ▸ hmem⟩

/-- **Theorem 18.1** (sufficiency): a Jordan curve of `M`-bounded turning is a `K`-quasicircle
with `K` depending only on `M`. -/
theorem thm18_1_quasicircle_of_boundedTurning {M : ℝ} (hM : 1 ≤ M) :
    ∃ K : ℝ, ∀ C : Set ExtPlane, IsBoundedTurning C M → IsKQuasicircle C K := by
  refine ⟨s18v_K ((M + 1) ^ 2), fun C hC => ?_⟩
  have hM' : 1 ≤ (M + 1) ^ 2 := by nlinarith [hM]
  by_cases hinf : extInf ∈ C
  · obtain ⟨A₁, A₂, φ, ψ, Φ, Ψ, h, hS⟩ := s18v_setup_exists hC.1 hinf
    exact s18v_core hS hM' (s18v_threePoint_mono (s18v_threePoint_of_bt hS hC) (by nlinarith [hM]))
  · -- move a point `a ∈ C` to `∞` by `w ↦ 1/(w - a)`, then move back by `w ↦ a + 1/w`
    obtain ⟨a, ha⟩ := s18v_exists_finite hC.1 hinf
    have hdet : (0 : ℂ) * (-a) - 1 * 1 ≠ 0 := by norm_num
    have hJ' : IsJordanCurve (mobiusExt 0 1 1 (-a) '' C) :=
      uq_isJordanCurve_image (mobiusHomeomorph 0 1 1 (-a) hdet) hC.1
    have hinf' : extInf ∈ mobiusExt 0 1 1 (-a) '' C := ⟨_, ha, mobiusExt_coe_of_eq_zero (by ring)⟩
    obtain ⟨A₁, A₂, φ, ψ, Φ, Ψ, h, hS⟩ := s18v_setup_exists hJ' hinf'
    have hK := s18v_isKQuasicircle_mobius_image (s18v_core hS hM' (s18v_threePoint_mobius hC hinf ha hS))
      (a := a) (b := 1) (c := 1) (d := 0) (by norm_num)
    have hback : mobiusExt a 1 1 0 '' (mobiusExt 0 1 1 (-a) '' C) = C := by
      rw [image_image]
      exact (image_congr fun p _ => s18v_mobius_inv_self a p).trans (image_id' C)
    rwa [hback] at hK

/-- **Theorem 18.1**: a Jordan curve in the plane is a quasicircle iff it is of bounded turning. -/
theorem thm18_1 {C : Set ExtPlane} (hC : IsJordanCurve C) (hinf : extInf ∉ C) :
    IsQuasicircle C ↔ ∃ M : ℝ, IsBoundedTurning C M := by
  constructor
  · rintro ⟨K, hK⟩
    have hK1 : 1 ≤ K := by
      obtain ⟨f, hf, -⟩ := hK
      exact hf.2.1
    obtain ⟨M, hM⟩ := thm18_1_boundedTurning_of_quasicircle hK1
    exact ⟨M, hM C hK hinf⟩
  · rintro ⟨M, hM⟩
    obtain ⟨K, hK⟩ := thm18_1_quasicircle_of_boundedTurning hM.2.1
    exact ⟨K, hK C ⟨hC, hM.2⟩⟩

end LiZhongQC
