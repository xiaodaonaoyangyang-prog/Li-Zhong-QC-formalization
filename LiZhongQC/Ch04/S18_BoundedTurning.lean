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

/-- **Theorem 18.1** (sufficiency): a Jordan curve of `M`-bounded turning is a `K`-quasicircle
with `K` depending only on `M`. -/
theorem thm18_1_quasicircle_of_boundedTurning {M : ℝ} (hM : 1 ≤ M) :
    ∃ K : ℝ, ∀ C : Set ExtPlane, IsBoundedTurning C M → IsKQuasicircle C K := by
  sorry

/-- **Theorem 18.1**: a Jordan curve in the plane is a quasicircle iff it is of bounded turning. -/
theorem thm18_1 {C : Set ExtPlane} (hC : IsJordanCurve C) (hinf : extInf ∉ C) :
    IsQuasicircle C ↔ ∃ M : ℝ, IsBoundedTurning C M := by
  sorry

end LiZhongQC
