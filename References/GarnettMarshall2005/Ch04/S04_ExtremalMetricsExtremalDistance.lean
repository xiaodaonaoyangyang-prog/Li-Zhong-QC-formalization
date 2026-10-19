import References.GarnettMarshall2005.Ch04.S03_FourRules

/-!
# Garnett–Marshall, Chapter IV §4: Extremal metrics for extremal distance

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. IV §4 (pp. 139–143;
`full.md` P1:6135–6259).

Conventions of Chapter IV as in §1. Jordan domains are domains of `ℂ*` (`References.IsJordanDomainExt`), conformal
maps are LV's (`LehtoVirtanen1973.IsConformalMap`), continuity on `Ω̄` is continuity on the closure in `ℂ*`, and
extremal distances of a Jordan domain are taken on finite parts. "A finite union of closed (sub)arcs of `∂Ω`" is a
union of finitely many, at least one, closed Jordan arcs contained in `∂Ω` (`IsFiniteUnionOf`); it may be a whole
boundary curve (a union of two closed arcs), as in the first case of the proof of Theorem 4.2. A rectangle "with
sides parallel to the axes" is `(x₁, x₂) × (y₁, y₂)`; its "horizontal line segments" (slits) are closed horizontal
segments of the closed rectangle at heights strictly between `y₁` and `y₂` (`IsHorizontalSlit`), which may end on a
vertical side, as the slits `L_k` of the proof of Theorem 4.1 do (P1:6221). Radial slits of an annulus
`{r < |z| < R}` are closed radial segments `{t e^{iθ} : a ≤ t ≤ b}`, `r ≤ a < b ≤ R` (`IsRadialSlit`). "The
extremal metrics are the (positive) constant multiples of `ρ₀`" is stated as two claims: every `c ρ₀` with a positive
real constant `c` is an extremal metric (`c = 0` is not a metric), and every extremal metric agrees with some `c ρ₀`
almost everywhere on `Ω`. It is not an equivalence: `ρ`-lengths see area-null sets, so a metric equal to `c ρ₀` a.e.
that vanishes on one extremal curve has `L(Γ, ρ) = 0` and is not extremal.

* Unlabelled (§4, P1:6139–6157): for a rectangle `R = (0, 1) × (0, h)` with finitely many horizontal slits removed,
  `d_Ω(E, F) = d_R(E, F)`, every extremal metric is constant a.e., and `d*_Ω(E, F) = d*_R(E, F)` —
  `slitRectangle_extremalDist`
* Theorem 4.1 (§4; (4.1)) — `thm4_4_1_a`, `thm4_4_1_b`
* Unlabelled (§4, P1:6231): removing finitely many radial slits from an annulus does not change the extremal
  distance and the conjugate extremal distance between the boundary circles — `annulus_radialSlits`
* Theorem 4.2 (§4) — `thm4_4_2`

Helpers (not book notions): `IsFiniteUnionOf` (a union of finitely many, at least one, sets with a given property),
`IsHorizontalSlit`, `IsRadialSlit`, `IsSlitRectangleMap` (the conformal map of Theorem 4.1).

Not stated (inventory U−): the setting paragraph of §4 (P1:6137, a recall of the definitions); the consequence
P1:6162–6168 of the observation (if `φ` maps `Ω` onto a slit rectangle with `φ(E)`, `φ(F)` the vertical sides,
then `d_Ω(E, F) = 1/h = 1/d*_Ω(E, F)` with extremal metric `|φ'|`: contained in Theorem 4.1(b)); the remark that a
ring domain version of Theorem 4.1 follows (P1:6231, it announces Theorem 4.2). (4.2)–(4.5) are steps of the proofs
(App. H, P3:4622, 4644, re-derives them for its own map).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt IsJordanCurve annulus)
open LehtoVirtanen1973 (IsJordanArc IsClosedJordanArc IsConformalMap derivDensity logDerivDensity)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-- `E` is the union of finitely many, at least one, sets with the property `P` (helper, Ch. IV §4: "a finite union
of closed arcs of `∂Ω`", and in §5–§6 "a finite union of arcs"). The sets need not be disjoint. -/
def IsFiniteUnionOf {X : Type*} (P : Set X → Prop) (E : Set X) : Prop :=
  ∃ (n : ℕ) (s : Fin n → Set X), 0 < n ∧ (∀ i, P (s i)) ∧ E = ⋃ i, s i

/-- A horizontal slit of the rectangle `(x₁, x₂) × (y₁, y₂)` (helper, Ch. IV §4): a closed horizontal segment
`[a, b] × {y}` with `x₁ ≤ a < b ≤ x₂` and `y₁ < y < y₂`. -/
def IsHorizontalSlit (x₁ x₂ y₁ y₂ : ℝ) (L : Set ℂ) : Prop :=
  ∃ a b y : ℝ, x₁ ≤ a ∧ a < b ∧ b ≤ x₂ ∧ y₁ < y ∧ y < y₂ ∧ L = Icc a b ×ℂ {y}

/-! ### GM4-C helpers (-e8): rectangles with horizontal slits -/

/-- Helper: a curve of a joining family that lies in a smaller set `Ω'` is a curve of the joining family of `Ω'`. -/
theorem gm4c_joiningFamily_of_subset {Ω Ω' E F γ : Set ℂ} (hγ : γ ∈ joiningFamily Ω E F) (hs : γ ⊆ Ω') :
    γ ∈ joiningFamily Ω' E F := by
  obtain ⟨hpc, f, hfc, hfi, hf0, hf1, hfγ⟩ := hγ
  obtain ⟨s, hsc, rfl⟩ := hpc
  exact ⟨⟨s, fun n => ⟨(hsc n).1, (subset_iUnion s n).trans hs⟩, rfl⟩, f, hfc, hfi, hf0, hf1, hfγ⟩

/-- Helper: removing a null set does not change the `ρ`-area. -/
theorem gm4c_rhoArea_diff_null {D S : Set ℂ} (hS : volume S = 0) (ρ : ℂ → ℝ≥0∞) :
    LiZhongQC.rhoArea ρ (D \ S) = LiZhongQC.rhoArea ρ D := by
  rw [gm4a_rhoArea_eq, gm4a_rhoArea_eq]
  exact setLIntegral_congr (sdiff_null_ae_eq_self hS)

/-- Helper: the union of finitely many horizontal lines is null. -/
theorem gm4c_volume_im_finite {Y : Set ℝ} (hY : Y.Finite) : volume {z : ℂ | z.im ∈ Y} = 0 := by
  have h : {z : ℂ | z.im ∈ Y} = Complex.measurableEquivRealProd ⁻¹' ((univ : Set ℝ) ×ˢ Y) := by
    ext z
    simp [Complex.measurableEquivRealProd]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod,
    hY.measure_zero volume, mul_zero]

/-- Helper: finitely many horizontal slits form a closed set contained in finitely many horizontal lines. -/
theorem gm4c_slits_horizontal {x₁ x₂ y₁ y₂ : ℝ} {n : ℕ} {L : Fin n → Set ℂ}
    (hL : ∀ j, IsHorizontalSlit x₁ x₂ y₁ y₂ (L j)) :
    ∃ Y : Set ℝ, Y.Finite ∧ IsClosed (⋃ j, L j) ∧ ∀ z ∈ ⋃ j, L j, z.im ∈ Y := by
  choose a b y hxa hab hbx hy1 hy2 hLj using hL
  refine ⟨Set.range y, Set.finite_range y, isClosed_iUnion_of_finite fun j => ?_, ?_⟩
  · rw [hLj j]
    exact isClosed_Icc.reProdIm isClosed_singleton
  · intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.1 hz
    rw [hLj j, mem_reProdIm] at hj
    exact ⟨j, (mem_singleton_iff.1 hj.2).symm⟩

/-- Helper: a horizontal segment at a height `y ∈ (0, h)` that carries no slit joins the vertical sides in
the slit rectangle. -/
theorem gm4c_slit_hseg_mem {ℓ h y : ℝ} (hℓ : 0 < ℓ) (hy : y ∈ Ioo 0 h) {S : Set ℂ} {Y : Set ℝ}
    (hSY : ∀ z ∈ S, z.im ∈ Y) (hyY : y ∉ Y) :
    (fun t : ℝ => (y : ℂ) * I + t * 1) '' Ioo 0 ℓ ∈
      joiningFamily (Ioo 0 ℓ ×ℂ Ioo 0 h \ S) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h) := by
  have h := gm4b_rect_seg_mem (h := h) hℓ hy
  refine gm4c_joiningFamily_of_subset h ?_
  intro z hz
  have hzR := gm4a_isPathCurve_subset (gm4a_joiningFamily_isPathCurve h) hz
  refine ⟨hzR, fun hzS => hyY ?_⟩
  obtain ⟨t, -, rfl⟩ := hz
  simpa using hSY _ hzS

/-- Helper (Cauchy–Schwarz on the segments, up to a finite set of exceptional abscissae): as `gm4b_rect_core`, with
the bound on `L` required off the finite set `Y`. -/
theorem gm4c_rect_core_ae {a b : ℝ} {G : ℝ → ℝ → ℝ≥0∞} (hG : ∀ x, Measurable (G x)) {L : ℝ≥0∞} {Y : Set ℝ}
    (hY : Y.Finite) (hL : ∀ x ∈ Ioo 0 a, x ∉ Y → L ≤ ∫⁻ y in Ioo 0 b, G x y) :
    ENNReal.ofReal a * L ^ 2 ≤ ENNReal.ofReal b * ∫⁻ x in Ioo 0 a, ∫⁻ y in Ioo 0 b, G x y ^ 2 := by
  have h1 : ∀ᵐ x ∂(volume.restrict (Ioo 0 a)), L ^ 2 ≤ ENNReal.ofReal b * ∫⁻ y in Ioo 0 b, G x y ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (hY.measure_zero volume))] with x hx hxY
    calc L ^ 2 ≤ (∫⁻ y in Ioo 0 b, G x y) ^ 2 := pow_le_pow_left' (hL x hx hxY) 2
      _ ≤ (volume.restrict (Ioo 0 b)) univ * ∫⁻ y in Ioo 0 b, G x y ^ 2 :=
          gm4b_lintegral_sq_le _ (hG x).aemeasurable
      _ = ENNReal.ofReal b * ∫⁻ y in Ioo 0 b, G x y ^ 2 := by
          rw [Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]
  calc ENNReal.ofReal a * L ^ 2 = ∫⁻ _ in Ioo 0 a, L ^ 2 := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero, mul_comm]
    _ ≤ ∫⁻ x in Ioo 0 a, ENNReal.ofReal b * ∫⁻ y in Ioo 0 b, G x y ^ 2 := lintegral_mono_ae h1
    _ = ENNReal.ofReal b * ∫⁻ x in Ioo 0 a, ∫⁻ y in Ioo 0 b, G x y ^ 2 := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Helper (rectangle, horizontal segments off a finite set of heights): if `Γ` contains the horizontal segment at
every height `y ∈ (0, h) \ Y`, `Y` finite, then `L²/A ≤ ℓ/h` for every metric. -/
theorem gm4c_rect_hseg_ratio_le_ae {ℓ h : ℝ} (hh : 0 < h) {Y : Set ℝ} (hY : Y.Finite) {Γ : Set (Set ℂ)}
    (hΓ : ∀ y ∈ Ioo 0 h, y ∉ Y → (fun t : ℝ => (y : ℂ) * I + t * 1) '' Ioo 0 ℓ ∈ Γ) {ρ : ℂ → ℝ≥0∞}
    (hρ : ρ ∈ LiZhongQC.densitiesP0 (Ioo 0 ℓ ×ℂ Ioo 0 h)) :
    pathRhoLength Γ ρ ^ 2 / LiZhongQC.rhoArea ρ (Ioo 0 ℓ ×ℂ Ioo 0 h) ≤ ENNReal.ofReal (ℓ / h) := by
  obtain ⟨hm, hA0, hAt⟩ := gm4a_mem_densitiesP0.1 hρ
  have hR : Ioo 0 ℓ ×ℂ Ioo 0 h = LiZhongQC.rectangle ℓ h := (LiZhongQC.rectangle_eq_reProdIm ℓ h).symm
  have hmeas : Measurable fun p : ℝ × ℝ => ρ ((p.1 : ℂ) + (p.2 : ℂ) * I) ^ 2 :=
    (hm.comp (by fun_prop)).pow_const 2
  have hA : LiZhongQC.rhoArea ρ (Ioo 0 ℓ ×ℂ Ioo 0 h) =
      ∫⁻ y in Ioo 0 h, ∫⁻ x in Ioo 0 ℓ, ρ ((x : ℂ) + (y : ℂ) * I) ^ 2 := by
    rw [gm4a_rhoArea_eq, hR, LiZhongQC.setLIntegral_rectangle (hm.pow_const 2)]
    exact lintegral_lintegral_swap hmeas.aemeasurable
  have hcore := gm4c_rect_core_ae (G := fun y x => ρ ((x : ℂ) + (y : ℂ) * I)) (fun y => hm.comp (by fun_prop))
    (L := pathRhoLength Γ ρ) hY fun y hy hyY => by
      refine (iInf₂_le _ (hΓ y hy hyY)).trans_eq ?_
      rw [gm4b_lintegral_line (c := (y : ℂ) * I) (u := 1) norm_one measurableSet_Ioo hm]
      refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
      rw [mul_one, add_comm]
  rw [← hA] at hcore
  exact gm4b_div_le_of_mul_le hh hA0.ne' hAt.ne hcore

/-- Helper (slit rectangle, upper bound): for every metric of `R \ S`, `L²/A ≤ ℓ/h`. -/
theorem gm4c_slit_ratio_le {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) {S : Set ℂ} {Y : Set ℝ} (hY : Y.Finite)
    (hSY : ∀ z ∈ S, z.im ∈ Y) {ρ : ℂ → ℝ≥0∞} (hρ : ρ ∈ LiZhongQC.densitiesP0 (Ioo 0 ℓ ×ℂ Ioo 0 h \ S)) :
    pathRhoLength (joiningFamily (Ioo 0 ℓ ×ℂ Ioo 0 h \ S) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h)) ρ ^ 2 /
      LiZhongQC.rhoArea ρ (Ioo 0 ℓ ×ℂ Ioo 0 h \ S) ≤ ENNReal.ofReal (ℓ / h) := by
  have hS0 : volume S = 0 := measure_mono_null (fun z hz => hSY z hz) (gm4c_volume_im_finite hY)
  have hA := gm4c_rhoArea_diff_null (D := Ioo 0 ℓ ×ℂ Ioo 0 h) hS0 ρ
  have hρ' : ρ ∈ LiZhongQC.densitiesP0 (Ioo 0 ℓ ×ℂ Ioo 0 h) := by
    rw [gm4a_mem_densitiesP0] at hρ ⊢
    rwa [hA] at hρ
  rw [hA]
  have _ := hℓ
  exact gm4c_rect_hseg_ratio_le_ae hh hY (Γ := joiningFamily (Ioo 0 ℓ ×ℂ Ioo 0 h \ S) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h))
    (fun y hy hyY => gm4c_slit_hseg_mem hℓ hy hSY hyY) hρ'

/-- Helper (slit rectangle, the metric `ρ = 1`): a metric of area `ℓh`, and the joining family has `1`-length `ℓ`. -/
theorem gm4c_slit_one {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) {S : Set ℂ} {Y : Set ℝ} (hY : Y.Finite)
    (hSY : ∀ z ∈ S, z.im ∈ Y) :
    (fun _ => (1 : ℝ≥0∞)) ∈ LiZhongQC.densitiesP0 (Ioo 0 ℓ ×ℂ Ioo 0 h \ S) ∧
      LiZhongQC.rhoArea (fun _ => (1 : ℝ≥0∞)) (Ioo 0 ℓ ×ℂ Ioo 0 h \ S) = ENNReal.ofReal (ℓ * h) ∧
      pathRhoLength (joiningFamily (Ioo 0 ℓ ×ℂ Ioo 0 h \ S) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h))
        (fun _ => 1) = ENNReal.ofReal ℓ := by
  have hS0 : volume S = 0 := measure_mono_null (fun z hz => hSY z hz) (gm4c_volume_im_finite hY)
  obtain ⟨hmem, hA, -⟩ := gm4b_rect_one hℓ hh
  have hA' := gm4c_rhoArea_diff_null (D := Ioo 0 ℓ ×ℂ Ioo 0 h) hS0 (fun _ => (1 : ℝ≥0∞))
  have hmem' : (fun _ => (1 : ℝ≥0∞)) ∈ LiZhongQC.densitiesP0 (Ioo 0 ℓ ×ℂ Ioo 0 h \ S) := by
    rw [gm4a_mem_densitiesP0] at hmem ⊢
    rwa [hA']
  have hone : ∀ γ : Set ℂ, ∫⁻ z in γ, (1 : ℝ≥0∞) ∂μH[1] = μH[1] γ := fun γ => by simp
  refine ⟨hmem', hA'.trans hA, ?_⟩
  simp only [pathRhoLength, hone]
  refine le_antisymm ?_ ?_
  · obtain ⟨y, hy⟩ := ((Set.Ioo_infinite hh).sdiff hY).nonempty
    refine (iInf₂_le _ (gm4c_slit_hseg_mem hℓ hy.1 hSY hy.2)).trans_eq ?_
    have hgl := gm4b_lintegral_line (c := (y : ℂ) * I) (u := 1) norm_one
      (A := Ioo (0 : ℝ) ℓ) measurableSet_Ioo (ρ := fun _ : ℂ => (1 : ℝ≥0∞)) measurable_const
    rw [hone] at hgl
    rw [hgl]
    simp [Real.volume_Ioo]
  · refine le_iInf₂ fun γ hγ => ?_
    exact gm4b_rect_joining_ge hℓ (gm4a_joiningFamily_mono sdiff_subset subset_rfl subset_rfl hγ)

/-- Helper (slit rectangle): `λ(Γ) = ℓ/h` for the family joining the vertical sides (assembly of
`gm4c_slit_ratio_le` and `gm4c_slit_one`). -/
theorem gm4c_slit_value {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) {S : Set ℂ} {Y : Set ℝ} (hY : Y.Finite)
    (hSY : ∀ z ∈ S, z.im ∈ Y) :
    extremalLengthGM (Ioo 0 ℓ ×ℂ Ioo 0 h \ S)
        (joiningFamily (Ioo 0 ℓ ×ℂ Ioo 0 h \ S) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h)) = ENNReal.ofReal (ℓ / h) := by
  refine le_antisymm ?_ ?_
  · rw [gm4a_extremalLengthGM_eq]
    exact iSup₂_le fun ρ hρ => gm4c_slit_ratio_le hℓ hh hY hSY hρ
  · obtain ⟨hmem, hA, hL⟩ := gm4c_slit_one hℓ hh hY hSY
    refine le_trans ?_ (gm4a_ratio_le hmem)
    rw [hA, hL]
    exact (gm4b_ofReal_sq_div hℓ hh).ge

/-- Helper: an open interval minus a finite set is a union of finitely many non-empty open intervals. -/
theorem gm4c_Ioo_diff_finite {a b : ℝ} (hab : a < b) {Y : Set ℝ} (hY : Y.Finite) :
    ∃ l : List (ℝ × ℝ), l ≠ [] ∧ (∀ p ∈ l, p.1 < p.2) ∧ Ioo a b \ Y = ⋃ p ∈ l, Ioo p.1 p.2 := by
  classical
  have key : ∀ s : Finset ℝ, ∃ l : List (ℝ × ℝ), Ioo a b \ (↑s : Set ℝ) = ⋃ p ∈ l, Ioo p.1 p.2 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨[(a, b)], by simp⟩
    | insert p s hp ih =>
      obtain ⟨l, hl⟩ := ih
      refine ⟨l.flatMap fun q => [(q.1, min p q.2), (max p q.1, q.2)], ?_⟩
      rw [Finset.coe_insert, Set.insert_eq, Set.union_comm, ← Set.sdiff_sdiff, hl]
      ext z
      simp only [Set.mem_sdiff, mem_iUnion, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, mem_singleton_iff,
        mem_Ioo, exists_prop]
      constructor
      · rintro ⟨⟨q, hq, h1, h2⟩, hzp⟩
        rcases lt_or_gt_of_ne hzp with h | h
        · exact ⟨(q.1, min p q.2), ⟨q, hq, Or.inl rfl⟩, h1, lt_min h h2⟩
        · exact ⟨(max p q.1, q.2), ⟨q, hq, Or.inr rfl⟩, max_lt h h1, h2⟩
      · rintro ⟨r, ⟨q, hq, rfl | rfl⟩, h1, h2⟩
        · exact ⟨⟨q, hq, h1, (lt_min_iff.1 h2).2⟩, (lt_min_iff.1 h2).1.ne⟩
        · exact ⟨⟨q, hq, (max_lt_iff.1 h1).2, h2⟩, (max_lt_iff.1 h1).1.ne'⟩
  obtain ⟨l, hl⟩ := key hY.toFinset
  rw [Set.Finite.coe_toFinset] at hl
  have hne : (Ioo a b \ Y).Nonempty := ((Set.Ioo_infinite hab).sdiff hY).nonempty
  refine ⟨l.filter fun p => decide (p.1 < p.2), ?_, ?_, ?_⟩
  · intro h
    obtain ⟨z, hz⟩ := hne
    rw [hl] at hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hz
    have : p ∈ l.filter fun p => decide (p.1 < p.2) := by
      rw [List.mem_filter]
      exact ⟨hp, by simpa using (nonempty_Ioo.1 ⟨z, hzp⟩)⟩
    rw [h] at this
    simp at this
  · intro p hp
    simpa using (List.mem_filter.1 hp).2
  · rw [hl]
    ext z
    simp only [mem_iUnion, exists_prop, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨p, hp, hz⟩
      exact ⟨p, ⟨hp, nonempty_Ioo.1 ⟨z, hz⟩⟩, hz⟩
    · rintro ⟨p, ⟨hp, -⟩, hz⟩
      exact ⟨p, hp, hz⟩

/-- Helper (slit rectangle, separating curves): for every abscissa `x ∈ (0, ℓ)` the vertical segment broken at the
slits is a curve of the separating family of `R \ S`; it differs from the whole vertical segment by a finite set. -/
theorem gm4c_slit_vseg_mem {ℓ h x : ℝ} (hh : 0 < h) (hx : x ∈ Ioo 0 ℓ) {S : Set ℂ} {Y : Set ℝ} (hY : Y.Finite)
    (hSY : ∀ z ∈ S, z.im ∈ Y) :
    ∃ γ ∈ separatingFamily (Ioo 0 ℓ ×ℂ Ioo 0 h \ S) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h),
      γ =ᵐ[μH[1]] (fun t : ℝ => (x : ℂ) + t * I) '' Ioo 0 h := by
  classical
  set R : Set ℂ := Ioo 0 ℓ ×ℂ Ioo 0 h with hR
  set e : ℝ → ℂ := fun t => (x : ℂ) + t * I with he
  set Y' : Set ℝ := {t | t ∈ Y ∧ e t ∈ S} with hY'
  have hY'fin : Y'.Finite := hY.subset fun t ht => ht.1
  obtain ⟨l, hlne, hlt, hl⟩ := gm4c_Ioo_diff_finite hh hY'fin
  set arc : ℝ × ℝ → Set ℂ := fun p => e '' Ioo p.1 p.2 with harc_def
  have hre : ∀ t : ℝ, (e t).re = x := fun t => by simp [he]
  have him : ∀ t : ℝ, (e t).im = t := fun t => by simp [he]
  have hmem : ∀ t, e t ∈ R ↔ t ∈ Ioo 0 h := fun t => by
    rw [hR, mem_reProdIm, hre, him]
    simp [hx.1, hx.2]
  set γ : Set ℂ := e '' (Ioo 0 h \ Y') with hγ
  have hγeq : γ = ⋃ p ∈ l, arc p := by rw [hγ, hl, image_iUnion₂]
  have hγΩ : γ ⊆ R \ S := by
    rintro _ ⟨t, ⟨ht, htY⟩, rfl⟩
    refine ⟨(hmem t).2 ht, fun hS => htY ⟨?_, hS⟩⟩
    simpa [him] using hSY _ hS
  have hback : ∀ w ∈ R \ S, w.re = x → w ∈ γ := by
    rintro w ⟨hwR, hwS⟩ hwx
    rw [hR, mem_reProdIm] at hwR
    have hwe : w = e w.im := by
      apply Complex.ext <;> simp [he, hwx]
    refine ⟨w.im, ⟨hwR.2, fun hY'm => hwS ?_⟩, hwe.symm⟩
    have h2 : e w.im ∈ S := hY'm.2
    rwa [← hwe] at h2
  have harc : ∀ p ∈ l, LehtoVirtanen1973.IsRectifiableArc (arc p) := fun p hp => by
    have hp1 := hlt p hp
    exact gm4b_isRectifiableArc_affine (c := (x : ℂ)) (v := I) I_ne_zero ordConnected_Ioo
      ⟨p.1 + (p.2 - p.1) / 3, ⟨by linarith, by linarith⟩, p.1 + 2 * (p.2 - p.1) / 3,
        ⟨by linarith, by linarith⟩, by intro h'; linarith⟩ (Metric.isBounded_Ioo _ _)
  have hfin : ({p : ℝ × ℝ | p ∈ l}).Finite := l.finite_toSet
  obtain ⟨f, hf⟩ := hfin.countable.exists_eq_range (by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil l hlne
    exact ⟨p, hp⟩)
  have hmem' := Set.ext_iff.1 hf
  have hγ_union : γ = ⋃ n, arc (f n) := by
    rw [hγeq]
    ext z
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨p, hp, hz⟩
      obtain ⟨n, rfl⟩ := (hmem' p).1 hp
      exact ⟨n, hz⟩
    · rintro ⟨n, hz⟩
      exact ⟨f n, (hmem' (f n)).2 (mem_range_self n), hz⟩
  have hpc : IsPathCurve (R \ S) γ := by
    refine ⟨fun n => arc (f n), fun n => ⟨harc _ ((hmem' _).2 (mem_range_self n)), ?_⟩, hγ_union⟩
    exact (subset_iUnion (fun n => arc (f n)) n).trans (by rw [← hγ_union]; exact hγΩ)
  have hsep : IsSeparatingIn (R \ S) γ ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h) := by
    intro z hz hboth
    obtain ⟨⟨p, hpK, hpE⟩, ⟨q, hqK, hqF⟩⟩ := hboth
    set K := connectedComponentIn ((R \ S) \ γ) z with hK
    have hKsub : K ⊆ (R \ S) \ γ := connectedComponentIn_subset _ _
    have hKconn : IsPreconnected K := isPreconnected_connectedComponentIn
    have hsplit : K ⊆ {w : ℂ | w.re < x} ∪ {w : ℂ | x < w.re} := by
      intro w hw
      obtain ⟨hwΩ, hwγ⟩ := hKsub hw
      rcases lt_trichotomy w.re x with h1 | h1 | h1
      · exact Or.inl h1
      · exact absurd (hback w hwΩ h1) hwγ
      · exact Or.inr h1
    rcases hKconn.subset_or_subset (isOpen_lt Complex.continuous_re continuous_const)
      (isOpen_lt continuous_const Complex.continuous_re)
      (Set.disjoint_left.2 fun w (hw1 : w.re < x) (hw2 : x < w.re) => lt_irrefl _ (hw1.trans hw2)) hsplit with
      h1 | h1
    · have hcl : closure K ⊆ {w : ℂ | w.re ≤ x} :=
        closure_minimal (h1.trans fun w (hw : w.re < x) => (le_of_lt hw : w.re ≤ x))
          (isClosed_le Complex.continuous_re continuous_const)
      have h2 : q.re ≤ x := hcl hqK
      rw [mem_reProdIm] at hqF
      have h3 : q.re = ℓ := by simpa using hqF.1
      linarith [hx.2]
    · have hcl : closure K ⊆ {w : ℂ | x ≤ w.re} :=
        closure_minimal (h1.trans fun w (hw : x < w.re) => (le_of_lt hw : x ≤ w.re))
          (isClosed_le continuous_const Complex.continuous_re)
      have h2 : x ≤ p.re := hcl hpK
      rw [mem_reProdIm] at hpE
      have h3 : p.re = 0 := by simpa using hpE.1
      linarith [hx.1]
  refine ⟨γ, ⟨hpc, ⟨arc '' {p | p ∈ l}, hfin.image arc, ?_, ?_⟩, hsep⟩, ?_⟩
  · rw [sUnion_image]
    exact hγeq
  · rintro _ ⟨p, hp, rfl⟩
    exact Or.inl (harc p hp).1
  · have : NullSingletonClass (μH[1] : Measure ℂ) := Measure.nullSingletonClass_hausdorff ℂ one_pos
    have hdiff : (e '' Ioo 0 h) \ γ ⊆ e '' Y' := by
      rintro _ ⟨⟨t, ht, rfl⟩, hnot⟩
      refine ⟨t, ?_, rfl⟩
      by_contra htY'
      exact hnot ⟨t, ⟨ht, htY'⟩, rfl⟩
    have hsub : γ ⊆ e '' Ioo 0 h := image_mono Set.sdiff_subset
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [sdiff_eq_empty.2 hsub, measure_empty]
    · exact measure_mono_null hdiff ((hY'fin.image e).measure_zero _)

/-- Helper (slit rectangle, separating curves, lower bound): a separating curve of `R \ S` has length `≥ h` (it meets
every horizontal segment at a slit-free height). -/
theorem gm4c_slit_sep_ge {ℓ h : ℝ} (hh : 0 < h) {S : Set ℂ} {Y : Set ℝ} (hY : Y.Finite) (hSY : ∀ z ∈ S, z.im ∈ Y)
    {γ : Set ℂ}
    (hγ : γ ∈ separatingFamily (Ioo 0 ℓ ×ℂ Ioo 0 h \ S) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h)) :
    ENNReal.ofReal h ≤ μH[1] γ := by
  have _ := hh
  obtain ⟨hpc, -, hsep⟩ := hγ
  by_cases hℓ : 0 < ℓ
  swap
  · exfalso
    obtain ⟨s, hs, -⟩ := hpc
    obtain ⟨⟨I', -, hn, g, -, hgC⟩, -⟩ := (hs 0).1
    obtain ⟨t, ht⟩ := hn.nonempty
    have hmem : g t ∈ LiZhongQC.toExt (s 0) := hgC ▸ mem_image_of_mem g ht
    obtain ⟨z, hz, -⟩ := hmem
    have h1 := ((hs 0).2 hz).1
    rw [mem_reProdIm] at h1
    exact hℓ (h1.1.1.trans h1.1.2)
  have hsub : Ioo 0 h \ Y ⊆ Complex.im '' γ := by
    intro y hy
    by_contra hno
    set g : ℝ → ℂ := fun t => (t : ℂ) + (y : ℂ) * I with hg
    have hgc : Continuous g := by fun_prop
    set Hy : Set ℂ := g '' Ioo 0 ℓ with hHy
    have hHy_conn : IsPreconnected Hy := isPreconnected_Ioo.image g hgc.continuousOn
    have hz0H : g (ℓ / 2) ∈ Hy := ⟨ℓ / 2, ⟨half_pos hℓ, half_lt_self hℓ⟩, rfl⟩
    have hHyR : Hy ⊆ (Ioo 0 ℓ ×ℂ Ioo 0 h \ S) \ γ := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨⟨?_, fun hS => hy.2 ?_⟩, fun hmem => hno ⟨_, hmem, by simp [hg]⟩⟩
      · rw [mem_reProdIm]
        simp [hg, ht.1, ht.2, hy.1.1, hy.1.2]
      · simpa [hg] using hSY _ hS
    have hHyK : Hy ⊆ connectedComponentIn ((Ioo 0 ℓ ×ℂ Ioo 0 h \ S) \ γ) (g (ℓ / 2)) :=
      hHy_conn.subset_connectedComponentIn hz0H hHyR
    have hcl : g '' closure (Ioo 0 ℓ) ⊆ closure Hy := image_closure_subset_closure_image hgc
    rw [closure_Ioo hℓ.ne] at hcl
    refine hsep (g (ℓ / 2)) (hHyR hz0H) ⟨⟨g 0, closure_mono hHyK (hcl ⟨0, ⟨le_rfl, hℓ.le⟩, rfl⟩), ?_⟩,
      ⟨g ℓ, closure_mono hHyK (hcl ⟨ℓ, ⟨hℓ.le, le_rfl⟩, rfl⟩), ?_⟩⟩
    · rw [mem_reProdIm]
      simp [hg, hy.1.1.le, hy.1.2.le]
    · rw [mem_reProdIm]
      simp [hg, hy.1.1.le, hy.1.2.le]
  have him : LipschitzWith 1 Complex.im := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simpa [dist_eq_norm, Real.dist_eq] using abs_im_le_norm (a - b)
  calc ENNReal.ofReal h = μH[1] (Ioo 0 h \ Y) := by
        rw [hausdorffMeasure_real, measure_sdiff_null (hY.measure_zero _), Real.volume_Ioo, sub_zero]
    _ ≤ μH[1] (Complex.im '' γ) := measure_mono hsub
    _ ≤ μH[1] γ := by
        simpa using him.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1) γ

/-- Helper (rectangle, vertical segments up to a null set of the curve): if for every abscissa `x ∈ (0, ℓ)` the
family `Γ` has a curve that equals the vertical segment `μH[1]`-almost everywhere, then `L²/A ≤ h/ℓ`. -/
theorem gm4c_rect_vseg_ratio_le_ae {ℓ h : ℝ} (hℓ : 0 < ℓ) {Γ : Set (Set ℂ)}
    (hΓ : ∀ x ∈ Ioo 0 ℓ, ∃ γ ∈ Γ, γ =ᵐ[μH[1]] (fun t : ℝ => (x : ℂ) + t * I) '' Ioo 0 h) {ρ : ℂ → ℝ≥0∞}
    (hρ : ρ ∈ LiZhongQC.densitiesP0 (Ioo 0 ℓ ×ℂ Ioo 0 h)) :
    pathRhoLength Γ ρ ^ 2 / LiZhongQC.rhoArea ρ (Ioo 0 ℓ ×ℂ Ioo 0 h) ≤ ENNReal.ofReal (h / ℓ) := by
  obtain ⟨hm, hA0, hAt⟩ := gm4a_mem_densitiesP0.1 hρ
  have hR : Ioo 0 ℓ ×ℂ Ioo 0 h = LiZhongQC.rectangle ℓ h := (LiZhongQC.rectangle_eq_reProdIm ℓ h).symm
  have hA : LiZhongQC.rhoArea ρ (Ioo 0 ℓ ×ℂ Ioo 0 h) =
      ∫⁻ x in Ioo 0 ℓ, ∫⁻ y in Ioo 0 h, ρ ((x : ℂ) + (y : ℂ) * I) ^ 2 := by
    rw [gm4a_rhoArea_eq, hR]
    exact LiZhongQC.setLIntegral_rectangle (hm.pow_const 2)
  have hcore := gm4b_rect_core (G := fun x y => ρ ((x : ℂ) + (y : ℂ) * I)) (fun x => hm.comp (by fun_prop))
    (L := pathRhoLength Γ ρ) fun x hx => by
      obtain ⟨γ, hγΓ, hae⟩ := hΓ x hx
      refine (iInf₂_le _ hγΓ).trans_eq ?_
      rw [setLIntegral_congr hae, gm4b_lintegral_line (c := (x : ℂ)) (u := I) (by simp) measurableSet_Ioo hm]
  rw [← hA] at hcore
  exact gm4b_div_le_of_mul_le hℓ hA0.ne' hAt.ne hcore

/-- Helper (slit rectangle): `λ(Γ*) = h/ℓ` for the family of curves separating the vertical sides. -/
theorem gm4c_slit_sep_value {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) {S : Set ℂ} {Y : Set ℝ} (hY : Y.Finite)
    (hSY : ∀ z ∈ S, z.im ∈ Y) :
    extremalLengthGM (Ioo 0 ℓ ×ℂ Ioo 0 h \ S)
        (separatingFamily (Ioo 0 ℓ ×ℂ Ioo 0 h \ S) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h)) = ENNReal.ofReal (h / ℓ) := by
  have hS0 : volume S = 0 := measure_mono_null (fun z hz => hSY z hz) (gm4c_volume_im_finite hY)
  obtain ⟨hmem, hA, -⟩ := gm4c_slit_one hℓ hh hY hSY
  have hA' := gm4c_rhoArea_diff_null (D := Ioo 0 ℓ ×ℂ Ioo 0 h) hS0
  refine le_antisymm ?_ ?_
  · rw [gm4a_extremalLengthGM_eq]
    refine iSup₂_le fun ρ hρ => ?_
    have hρ' : ρ ∈ LiZhongQC.densitiesP0 (Ioo 0 ℓ ×ℂ Ioo 0 h) := by
      rw [gm4a_mem_densitiesP0] at hρ ⊢
      rwa [hA' ρ] at hρ
    rw [hA' ρ]
    exact gm4c_rect_vseg_ratio_le_ae hℓ (fun x hx => gm4c_slit_vseg_mem hh hx hY hSY) hρ'
  · refine le_trans ?_ (gm4a_ratio_le hmem)
    have hL : ENNReal.ofReal h ≤ pathRhoLength
        (separatingFamily (Ioo 0 ℓ ×ℂ Ioo 0 h \ S) ({0} ×ℂ Icc 0 h) ({ℓ} ×ℂ Icc 0 h)) (fun _ => (1 : ℝ≥0∞)) := by
      rw [gm4a_pathRhoLength_eq]
      refine le_iInf₂ fun γ hγ => ?_
      simpa using gm4c_slit_sep_ge hh hY hSY hγ
    rw [mul_comm ℓ h] at hA
    rw [hA, ← gm4b_ofReal_sq_div hh hℓ]
    exact ENNReal.div_le_div_right (pow_le_pow_left' hL 2) _

/-- **Unlabelled** (Ch. IV §4, P1:6139–6157; "the observation made at the beginning of this section", cited at
P1:6229 and in the proof of Theorem 4.2, P1:6258; App. H, P3:4622). Let `R = {(x, y) : 0 < x < 1, 0 < y < h}` be a
rectangle with sides parallel to the axes, let `Ω = R \ ⋃ L_j` where `{L_j}` is a finite family of horizontal line
segments in `R`, and let `E` and `F` be the vertical sides of the rectangle `R`. Then `d_Ω(E, F) = d_R(E, F)` by the
argument used in Example 1.1. Moreover, every extremal metric for `d_Ω(E, F)` is constant almost everywhere. The same
holds for the conjugate extremal distance, `d*_Ω(E, F) = d*_R(E, F)`, because by definition the "curves" that
separate `E` from `F` need not be connected.
Modelling: `h > 0`; the slits are `IsHorizontalSlit 0 1 0 h` (closed segments of `R̄` strictly between the
horizontal sides; slits may end on a vertical side, as in Figure IV.7 (`L₁`, `L₃` on `E`, `L₂` on `F`) and in the
proof of Theorem 4.1); the vertical sides are the closed segments `{0} × [0, h]` and `{1} × [0, h]`; "constant almost
everywhere" is for area measure on `Ω`. A slit running from one vertical side to the other disconnects `Ω`; the
statement covers that case too (both extremal distances are then those of the component strips taken together). -/
theorem slitRectangle_extremalDist {h : ℝ} (hh : 0 < h) {n : ℕ} {L : Fin n → Set ℂ}
    (hL : ∀ j, IsHorizontalSlit 0 1 0 h (L j)) {R Ω E F : Set ℂ} (hR : R = Ioo 0 1 ×ℂ Ioo 0 h)
    (hΩ : Ω = R \ ⋃ j, L j) (hE : E = {0} ×ℂ Icc 0 h) (hF : F = {1} ×ℂ Icc 0 h) :
    extremalDistGM Ω E F = extremalDistGM R E F ∧
      (∀ ρ : ℂ → ℝ≥0∞, IsExtremalMetricGM Ω (joiningFamily Ω E F) ρ →
        ∃ c : ℝ≥0∞, ρ =ᵐ[volume.restrict Ω] fun _ => c) ∧
      conjExtremalDistGM Ω E F = conjExtremalDistGM R E F := by
  obtain ⟨Y, hY, -, hSY⟩ := gm4c_slits_horizontal hL
  subst hR hΩ hE hF
  have hval := gm4c_slit_value (ℓ := 1) one_pos hh hY hSY
  have hRval := gm4b_rect_value (ℓ := 1) one_pos hh
  have hone := gm4c_slit_one (ℓ := 1) one_pos hh hY hSY
  refine ⟨?_, ?_, ?_⟩
  · unfold extremalDistGM
    rw [hval, hRval]
  · intro ρ hρ
    have hext : IsExtremalMetricGM (Ioo 0 1 ×ℂ Ioo 0 h \ ⋃ j, L j)
        (joiningFamily (Ioo 0 1 ×ℂ Ioo 0 h \ ⋃ j, L j) ({0} ×ℂ Icc 0 h) ({1} ×ℂ Icc 0 h)) (fun _ => 1) := by
      refine ⟨hone.1, ?_⟩
      rw [hval, hone.2.1, hone.2.2]
      exact gm4b_ofReal_sq_div one_pos hh
    obtain ⟨c, hc0, hct, hρc⟩ := gm4b_extremal_eq_const_mul
      (by rw [hval]; exact ENNReal.ofReal_pos.2 (by positivity)) (by rw [hval]; exact ENNReal.ofReal_lt_top) hext hρ
    exact ⟨c, by simpa using hρc⟩
  · exact (gm4c_slit_sep_value (ℓ := 1) one_pos hh hY hSY).trans (gm4b_rect_sep_value (ℓ := 1) one_pos hh).symm

/-- The conformal map of Theorem 4.1 (helper, Ch. IV §4, P1:6170): `φ` is a conformal map of the Jordan domain `Ω`
onto the rectangle `R = (x₁, x₂) × (y₁, y₂)` with the finitely many horizontal slits `L_j` removed, `φ` is
continuous on `Ω̄`, and `φ(E)` and `φ(F)` are the vertical sides of the rectangle (in either order). -/
def IsSlitRectangleMap (Ω E F : Set ExtPlane) (φ : ExtPlane → ExtPlane) (x₁ x₂ y₁ y₂ : ℝ) {n : ℕ}
    (L : Fin n → Set ℂ) : Prop :=
  x₁ < x₂ ∧ y₁ < y₂ ∧ (∀ j, IsHorizontalSlit x₁ x₂ y₁ y₂ (L j)) ∧ IsConformalMap φ Ω ∧
    φ '' Ω = toExt (Ioo x₁ x₂ ×ℂ Ioo y₁ y₂ \ ⋃ j, L j) ∧ ContinuousOn φ (closure Ω) ∧
    ((φ '' E = toExt ({x₁} ×ℂ Icc y₁ y₂) ∧ φ '' F = toExt ({x₂} ×ℂ Icc y₁ y₂)) ∨
      (φ '' E = toExt ({x₂} ×ℂ Icc y₁ y₂) ∧ φ '' F = toExt ({x₁} ×ℂ Icc y₁ y₂)))

/-- **Theorem 4.1** (Ch. IV §4), the characterization (4.1) (cited at P1:5929, 5944, 6231, 6252, 6258, 6382, in
Chapter V, P1:7031, 7037, and in App. H, P3:4568–4584, 4622, 4750, 4909). Let `Ω` be a Jordan domain and let `E` and
`F` be finite unions of closed subarcs of `∂Ω`. Assume `E ∩ F = ∅`. Then there is a rectangle `R` having sides
parallel to the axes and a conformal map `φ` of `Ω` onto the rectangle `R` with a finite number of horizontal line
segments removed such that `φ ∈ C(Ω̄)` and `φ(E)` and `φ(F)` are the vertical sides of the rectangle if and only if
there is an arc `σ ⊆ ∂Ω` such that (4.1) `E ⊆ σ` and `F ∩ σ = ∅`.
Modelling: the map is `IsSlitRectangleMap` (slits as in the module docstring, possibly none); `σ` is a Jordan arc
of `ℂ*` (LV `IsJordanArc`, any kind of parameter interval) contained in `∂Ω`. -/
theorem thm4_4_1_a {Ω E F : Set ExtPlane} (hΩ : IsJordanDomainExt Ω)
    (hE : IsFiniteUnionOf (fun s => IsClosedJordanArc s ∧ s ⊆ frontier Ω) E)
    (hF : IsFiniteUnionOf (fun s => IsClosedJordanArc s ∧ s ⊆ frontier Ω) F) (hEF : Disjoint E F) :
    (∃ (φ : ExtPlane → ExtPlane) (x₁ x₂ y₁ y₂ : ℝ) (n : ℕ) (L : Fin n → Set ℂ),
        IsSlitRectangleMap Ω E F φ x₁ x₂ y₁ y₂ L) ↔
      ∃ σ : Set ExtPlane, IsJordanArc σ ∧ σ ⊆ frontier Ω ∧ E ⊆ σ ∧ Disjoint F σ := by
  sorry

/-- **Theorem 4.1** (Ch. IV §4), the extremal distance. In the situation of `thm4_4_1_a`, when such a map `φ` onto
the slit rectangle `R` exists ("in this case"): the extremal distance from `E` to `F` is the ratio of the length to
the height of this rectangle, the conjugate extremal distance satisfies `d*_Ω(E, F) = 1/d_Ω(E, F)`, and the extremal
metrics on `Ω` for `d_Ω(E, F)` are the positive constant multiples of `ρ₀(z) = |φ'(z)|`.
Modelling: stated for every map `φ` as in `thm4_4_1_a`; distances on finite parts; `|φ'|` is
`LehtoVirtanen1973.derivDensity φ` on the finite part of `Ω` (`φ` has finite values there); "the extremal metrics
are the positive constant multiples of `ρ₀`" is stated as two claims (module docstring): every `c |φ'|`, `c > 0`, is
an extremal metric, and every extremal metric equals some `c |φ'|` almost everywhere for area measure on `Ω`. -/
theorem thm4_4_1_b {Ω E F : Set ExtPlane} (hΩ : IsJordanDomainExt Ω)
    (hE : IsFiniteUnionOf (fun s => IsClosedJordanArc s ∧ s ⊆ frontier Ω) E)
    (hF : IsFiniteUnionOf (fun s => IsClosedJordanArc s ∧ s ⊆ frontier Ω) F) (hEF : Disjoint E F)
    {φ : ExtPlane → ExtPlane} {x₁ x₂ y₁ y₂ : ℝ} {n : ℕ} {L : Fin n → Set ℂ}
    (hφ : IsSlitRectangleMap Ω E F φ x₁ x₂ y₁ y₂ L) :
    extremalDistGM (finitePart Ω) (finitePart E) (finitePart F) = ENNReal.ofReal ((x₂ - x₁) / (y₂ - y₁)) ∧
      conjExtremalDistGM (finitePart Ω) (finitePart E) (finitePart F) =
        (extremalDistGM (finitePart Ω) (finitePart E) (finitePart F))⁻¹ ∧
      (∀ c : ℝ, 0 < c → IsExtremalMetricGM (finitePart Ω)
          (joiningFamily (finitePart Ω) (finitePart E) (finitePart F))
          (fun z => ENNReal.ofReal c * derivDensity φ (finitePart Ω) z)) ∧
      ∀ ρ : ℂ → ℝ≥0∞, IsExtremalMetricGM (finitePart Ω)
          (joiningFamily (finitePart Ω) (finitePart E) (finitePart F)) ρ →
        ∃ c : ℝ, 0 < c ∧ ρ =ᵐ[volume.restrict (finitePart Ω)]
          fun z => ENNReal.ofReal c * derivDensity φ (finitePart Ω) z := by
  sorry

/-- A radial slit of the annulus `{r < |z| < R}` (helper, Ch. IV §4): a closed radial segment
`{t e^{iθ} : a ≤ t ≤ b}` with `r ≤ a < b ≤ R`. -/
def IsRadialSlit (r R : ℝ) (L : Set ℂ) : Prop :=
  ∃ a b θ : ℝ, r ≤ a ∧ a < b ∧ b ≤ R ∧ L = (fun t : ℝ => circleMap 0 t θ) '' Icc a b

/-! ### GM4-C helpers (-e8): annuli with radial slits -/

/-- Helper: finitely many radial slits form a closed set contained in finitely many rays (the arguments of its
points lie in a finite set, and `0` is not in it). -/
theorem gm4c_slits_radial {r R : ℝ} (hr : 0 < r) {n : ℕ} {L : Fin n → Set ℂ} (hL : ∀ j, IsRadialSlit r R (L j)) :
    ∃ Θ : Set ℝ, Θ.Finite ∧ IsClosed (⋃ j, L j) ∧ ∀ z ∈ ⋃ j, L j, z ≠ 0 ∧ arg z ∈ Θ := by
  choose a b θ hra hab hbR hLj using hL
  refine ⟨Set.range fun j => arg (exp (θ j * I)), Set.finite_range _, isClosed_iUnion_of_finite fun j => ?_, ?_⟩
  · rw [hLj j]
    exact (isCompact_Icc.image (by unfold circleMap; fun_prop)).isClosed
  · intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.1 hz
    rw [hLj j] at hj
    obtain ⟨t, ht, rfl⟩ := hj
    have ht0 : 0 < t := hr.trans_le ((hra j).trans ht.1)
    have hc : circleMap 0 t (θ j) = (t : ℂ) * exp (θ j * I) := by simp [circleMap]
    show circleMap 0 t (θ j) ≠ 0 ∧ arg (circleMap 0 t (θ j)) ∈ _
    rw [hc]
    exact ⟨mul_ne_zero (by exact_mod_cast ht0.ne') (exp_ne_zero _), j, (arg_real_mul _ ht0).symm⟩

/-- Helper: finitely many rays form a null set. -/
theorem gm4c_volume_arg_finite {Θ : Set ℝ} (hΘ : Θ.Finite) {S : Set ℂ} (hS : ∀ z ∈ S, z ≠ 0 ∧ arg z ∈ Θ) :
    volume S = 0 := by
  classical
  set S' : Set ℂ := {z | z ≠ 0 ∧ arg z ∈ Θ} with hS'
  have hS'm : MeasurableSet S' :=
    (measurableSet_singleton (0 : ℂ)).compl.inter (Complex.measurable_arg hΘ.measurableSet)
  have key : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 • S'.indicator (1 : ℂ → ℝ≥0∞) (Complex.polarCoord.symm p) =
      ENNReal.ofReal p.1 * Θ.indicator (1 : ℝ → ℝ≥0∞) p.2 := by
    rintro ⟨s, θ⟩ ⟨hs, hθ⟩
    have hs0 : (0 : ℝ) < s := hs
    have harg : arg (Complex.polarCoord.symm (s, θ)) = θ := by
      rw [gm4b_polarSymm, zero_add, arg_real_mul _ hs0, exp_mul_I]
      exact arg_cos_add_sin_mul_I ⟨hθ.1, hθ.2.le⟩
    have hne : Complex.polarCoord.symm (s, θ) ≠ 0 := by
      rw [gm4b_polarSymm, zero_add]
      exact mul_ne_zero (by exact_mod_cast hs0.ne') (exp_ne_zero _)
    by_cases hmem : θ ∈ Θ
    · have h1 : Complex.polarCoord.symm (s, θ) ∈ S' := ⟨hne, by show arg _ ∈ Θ; rw [harg]; exact hmem⟩
      show ENNReal.ofReal s • S'.indicator (1 : ℂ → ℝ≥0∞) (Complex.polarCoord.symm (s, θ)) =
        ENNReal.ofReal s * Θ.indicator (1 : ℝ → ℝ≥0∞) θ
      rw [indicator_of_mem h1, indicator_of_mem hmem, smul_eq_mul]
      rfl
    · have h1 : Complex.polarCoord.symm (s, θ) ∉ S' := fun h => hmem (by have h2 : arg (Complex.polarCoord.symm (s, θ)) ∈ Θ := h.2; rwa [harg] at h2)
      show ENNReal.ofReal s • S'.indicator (1 : ℂ → ℝ≥0∞) (Complex.polarCoord.symm (s, θ)) =
        ENNReal.ofReal s * Θ.indicator (1 : ℝ → ℝ≥0∞) θ
      rw [indicator_of_notMem h1, indicator_of_notMem hmem, smul_zero, mul_zero]
  have hvol : volume S' = 0 := by
    rw [← lintegral_indicator_one hS'm, ← Complex.lintegral_comp_polarCoord_symm,
      setLIntegral_congr_fun polarCoord.open_target.measurableSet key,
      show (polarCoord.target : Set (ℝ × ℝ)) = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl, Measure.volume_eq_prod,
      ← Measure.prod_restrict, lintegral_prod_mul (f := fun s : ℝ => ENNReal.ofReal s) (g := Θ.indicator (1 : ℝ → ℝ≥0∞))
        (measurable_id.ennreal_ofReal.aemeasurable) ((measurable_one.indicator hΘ.measurableSet).aemeasurable), lintegral_indicator_one hΘ.measurableSet,
      Measure.restrict_apply hΘ.measurableSet, measure_mono_null inter_subset_left (hΘ.measure_zero _), mul_zero]
  exact measure_mono_null (fun z hz => hS z hz) hvol

/-- Helper: a radial segment at an angle `θ ∈ (-π, π) \ Θ` that carries no slit joins the boundary circles of
the slit annulus. -/
theorem gm4c_annulus_radial_slit_mem {r R θ : ℝ} (hr : 0 < r) (hrR : r < R) (hθ : θ ∈ Ioo (-π) π) {S : Set ℂ}
    {Θ : Set ℝ} (hSΘ : ∀ z ∈ S, z ≠ 0 ∧ arg z ∈ Θ) (hθΘ : θ ∉ Θ) :
    (fun t : ℝ => (0 : ℂ) + t * exp (θ * I)) '' Ioo r R ∈
      joiningFamily (annulus r R \ S) (sphere 0 r) (sphere 0 R) := by
  have hu : ‖exp (θ * I)‖ = 1 := norm_exp_ofReal_mul_I θ
  have h := gm4b_annulus_radial_mem hr hrR hu
  refine gm4c_joiningFamily_of_subset h ?_
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨gm4a_isPathCurve_subset (gm4a_joiningFamily_isPathCurve h) ⟨t, ht, rfl⟩, fun hS => hθΘ ?_⟩
  have ht0 : 0 < t := hr.trans ht.1
  have harg : arg ((0 : ℂ) + t * exp (θ * I)) = θ := by
    rw [zero_add, arg_real_mul _ ht0, exp_mul_I]
    exact arg_cos_add_sin_mul_I ⟨hθ.1, hθ.2.le⟩
  have h2 := (hSΘ _ hS).2
  rwa [harg] at h2

/-- Helper (Cauchy–Schwarz along the rays, up to a finite set of exceptional angles): as `gm4b_annulus_core1`, with
the bound on `L` required off the finite set `Θ`. -/
theorem gm4c_annulus_core1_ae {r R : ℝ} (hr : 0 < r) (hrR : r < R) {G : ℝ → ℝ → ℝ≥0∞}
    (hG : ∀ θ, Measurable (G θ)) {L : ℝ≥0∞} {Θ : Set ℝ} (hΘ : Θ.Finite)
    (hL : ∀ θ ∈ Ioo (-π) π, θ ∉ Θ → L ≤ ∫⁻ s in Ioo r R, G θ s) :
    ENNReal.ofReal (2 * π) * L ^ 2 ≤
      ENNReal.ofReal (Real.log (R / r)) * ∫⁻ θ in Ioo (-π) π, ∫⁻ s in Ioo r R, ENNReal.ofReal s * G θ s ^ 2 := by
  have h1 : ∀ᵐ θ ∂(volume.restrict (Ioo (-π) π)), L ^ 2 ≤
      ENNReal.ofReal (Real.log (R / r)) * ∫⁻ s in Ioo r R, ENNReal.ofReal s * G θ s ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (hΘ.measure_zero volume))] with θ hθ hθΘ
    exact (pow_le_pow_left' (hL θ hθ hθΘ) 2).trans (gm4b_lintegral_sq_weight hr hrR (hG θ))
  calc ENNReal.ofReal (2 * π) * L ^ 2 = ∫⁻ _ in Ioo (-π) π, L ^ 2 := by
        rw [setLIntegral_const, Real.volume_Ioo, show π - -π = 2 * π by ring, mul_comm]
    _ ≤ ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (Real.log (R / r)) * ∫⁻ s in Ioo r R, ENNReal.ofReal s * G θ s ^ 2 :=
        lintegral_mono_ae h1
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Helper (slit annulus, upper bound): for every metric of `{r < |z| < R} \ S`,
`L²/A ≤ (1/2π) log(R/r)`. -/
theorem gm4c_annulus_slit_ratio_le {r R : ℝ} (hr : 0 < r) (hrR : r < R) {S : Set ℂ} {Θ : Set ℝ} (hΘ : Θ.Finite)
    (hSΘ : ∀ z ∈ S, z ≠ 0 ∧ arg z ∈ Θ) {ρ : ℂ → ℝ≥0∞} (hρ : ρ ∈ LiZhongQC.densitiesP0 (annulus r R \ S)) :
    pathRhoLength (joiningFamily (annulus r R \ S) (sphere 0 r) (sphere 0 R)) ρ ^ 2 /
        LiZhongQC.rhoArea ρ (annulus r R \ S) ≤ ENNReal.ofReal (1 / (2 * π) * Real.log (R / r)) := by
  have hS0 : volume S = 0 := gm4c_volume_arg_finite hΘ hSΘ
  have hA' := gm4c_rhoArea_diff_null (D := annulus r R) hS0 ρ
  have hρ' : ρ ∈ LiZhongQC.densitiesP0 (annulus r R) := by
    rw [gm4a_mem_densitiesP0] at hρ ⊢
    rwa [hA'] at hρ
  rw [hA']
  obtain ⟨hm, hA0, hAt⟩ := gm4a_mem_densitiesP0.1 hρ'
  have hmeas2 : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * ρ ((0 : ℂ) + p.1 * exp (p.2 * I)) ^ 2 :=
    measurable_fst.ennreal_ofReal.mul ((hm.comp (by fun_prop)).pow_const 2)
  have hA : LiZhongQC.rhoArea ρ (annulus r R) =
      ∫⁻ θ in Ioo (-π) π, ∫⁻ s in Ioo r R, ENNReal.ofReal s * ρ ((0 : ℂ) + s * exp (θ * I)) ^ 2 := by
    rw [gm4a_rhoArea_eq, gm4b_lintegral_annulus_polar hr (hm.pow_const 2)]
    exact lintegral_lintegral_swap hmeas2.aemeasurable
  have hcore := gm4c_annulus_core1_ae hr hrR (G := fun θ s => ρ ((0 : ℂ) + s * exp (θ * I)))
    (fun θ => hm.comp (by fun_prop))
    (L := pathRhoLength (joiningFamily (annulus r R \ S) (sphere 0 r) (sphere 0 R)) ρ) hΘ
    fun θ hθ hθΘ => by
      refine (iInf₂_le _ (gm4c_annulus_radial_slit_mem hr hrR hθ hSΘ hθΘ)).trans_eq ?_
      rw [gm4b_lintegral_line (c := 0) (u := exp (θ * I)) (norm_exp_ofReal_mul_I θ) measurableSet_Ioo hm]
  rw [← hA] at hcore
  have h := gm4b_div_le_of_mul_le (a := 2 * π) (b := Real.log (R / r)) (by positivity) hA0.ne' hAt.ne hcore
  rwa [show Real.log (R / r) / (2 * π) = 1 / (2 * π) * Real.log (R / r) by ring] at h

/-- Helper (slit annulus, the metric `c/|z|`): a metric of area `2πc² log(R/r)`, and the joining family has
`c/|z|`-length `c log(R/r)`. -/
theorem gm4c_annulus_slit_metric {r R : ℝ} (hr : 0 < r) (hrR : r < R) {S : Set ℂ} {Θ : Set ℝ} (hΘ : Θ.Finite)
    (hSΘ : ∀ z ∈ S, z ≠ 0 ∧ arg z ∈ Θ) {c : ℝ} (hc : 0 < c) :
    (fun z : ℂ => ENNReal.ofReal (c / ‖z‖)) ∈ LiZhongQC.densitiesP0 (annulus r R \ S) ∧
      LiZhongQC.rhoArea (fun z : ℂ => ENNReal.ofReal (c / ‖z‖)) (annulus r R \ S) =
        ENNReal.ofReal (2 * π * c ^ 2 * Real.log (R / r)) ∧
      pathRhoLength (joiningFamily (annulus r R \ S) (sphere 0 r) (sphere 0 R))
          (fun z => ENNReal.ofReal (c / ‖z‖)) = ENNReal.ofReal (c * Real.log (R / r)) := by
  have hS0 : volume S = 0 := gm4c_volume_arg_finite hΘ hSΘ
  obtain ⟨hmem, harea, hlen⟩ := gm4b_annulus_metric hr hrR hc
  have hA' := gm4c_rhoArea_diff_null (D := annulus r R) hS0 (fun z : ℂ => ENNReal.ofReal (c / ‖z‖))
  have hmem' : (fun z : ℂ => ENNReal.ofReal (c / ‖z‖)) ∈ LiZhongQC.densitiesP0 (annulus r R \ S) := by
    rw [gm4a_mem_densitiesP0] at hmem ⊢
    rwa [hA']
  refine ⟨hmem', hA'.trans harea, ?_⟩
  refine le_antisymm ?_ ?_
  · obtain ⟨θ, hθ⟩ := ((Set.Ioo_infinite (neg_lt_self Real.pi_pos)).sdiff hΘ).nonempty
    refine (iInf₂_le _ (gm4c_annulus_radial_slit_mem hr hrR hθ.1 hSΘ hθ.2)).trans_eq ?_
    have hmeas : Measurable fun z : ℂ => ENNReal.ofReal (c / ‖z‖) :=
      Measurable.ennreal_ofReal (measurable_const.div measurable_norm)
    rw [gm4b_lintegral_line (c := 0) (u := exp (θ * I)) (norm_exp_ofReal_mul_I θ) measurableSet_Ioo hmeas]
    have hcongr : ∀ t ∈ Ioo r R, ENNReal.ofReal (c / ‖(0 : ℂ) + (t : ℂ) * exp (θ * I)‖) =
        ENNReal.ofReal c * ENNReal.ofReal (1 / t) := by
      intro t ht
      have ht0 : 0 < t := hr.trans ht.1
      rw [zero_add, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0.le,
        ← ENNReal.ofReal_mul hc.le]
      congr 1
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioo hcongr, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      gm4b_lintegral_inv hr hrR, ← ENNReal.ofReal_mul hc.le]
  · rw [gm4a_pathRhoLength_eq] at hlen ⊢
    refine le_trans (le_of_eq hlen.symm) ?_
    exact gm4a_pathRhoLength_le_of_contains _ fun γ hγ =>
      ⟨γ, gm4a_joiningFamily_mono sdiff_subset subset_rfl subset_rfl hγ, subset_rfl⟩

/-- Helper (slit annulus): `d(C_r, C_R) = (1/2π) log(R/r)` (assembly of `gm4c_annulus_slit_ratio_le` and
`gm4c_annulus_slit_metric`). -/
theorem gm4c_annulus_slit_value {r R : ℝ} (hr : 0 < r) (hrR : r < R) {S : Set ℂ} {Θ : Set ℝ} (hΘ : Θ.Finite)
    (hSΘ : ∀ z ∈ S, z ≠ 0 ∧ arg z ∈ Θ) :
    extremalDistGM (annulus r R \ S) (sphere 0 r) (sphere 0 R) =
      ENNReal.ofReal (1 / (2 * π) * Real.log (R / r)) := by
  refine le_antisymm ?_ ?_
  · rw [extremalDistGM, gm4a_extremalLengthGM_eq]
    exact iSup₂_le fun ρ hρ => gm4c_annulus_slit_ratio_le hr hrR hΘ hSΘ hρ
  · obtain ⟨hmem, hA, hL⟩ := gm4c_annulus_slit_metric hr hrR hΘ hSΘ (c := 1) one_pos
    have hlog : 0 < Real.log (R / r) := Real.log_pos (by rw [one_lt_div hr]; exact hrR)
    have hπ : 0 < 2 * π := by positivity
    rw [extremalDistGM]
    refine le_trans ?_ (gm4a_ratio_le hmem)
    rw [hA, hL, show (1 : ℝ) * Real.log (R / r) = Real.log (R / r) by ring,
      show 2 * π * (1 : ℝ) ^ 2 * Real.log (R / r) = Real.log (R / r) * (2 * π) by ring,
      gm4b_ofReal_sq_div hlog hπ]
    exact le_of_eq (by congr 1; ring)

/-- Helper: an embedded open arc with finite linear measure, minus finitely many parameters, is a union of finitely
many rectifiable arcs. -/
theorem gm4c_embedded_arcs {k : ℝ → ℂ} (hk : IsEmbedding ((Ioo (-π) π).domRestrict k))
    (hfin : μH[1] (k '' Ioo (-π) π) < ⊤) {P : Set ℝ} (hP : P.Finite) :
    ∃ l : List (Set ℂ), l ≠ [] ∧ (∀ a ∈ l, LehtoVirtanen1973.IsRectifiableArc a) ∧
      k '' (Ioo (-π) π \ P) = ⋃ a ∈ l, a := by
  obtain ⟨l0, hne, hlt, hl⟩ := gm4c_Ioo_diff_finite (neg_lt_self Real.pi_pos) hP
  have hsub : ∀ p ∈ l0, Ioo p.1 p.2 ⊆ Ioo (-π) π := fun p hp z hz => by
    have : z ∈ Ioo (-π) π \ P := by
      rw [hl]
      exact mem_iUnion₂.2 ⟨p, hp, hz⟩
    exact this.1
  refine ⟨l0.map fun p => k '' Ioo p.1 p.2, by simpa using hne, ?_, ?_⟩
  · intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
    have hp1 := hlt p hp
    exact gm4b_isRectifiableArc_of_embedding ordConnected_Ioo
      ⟨p.1 + (p.2 - p.1) / 3, ⟨by linarith, by linarith⟩, p.1 + 2 * (p.2 - p.1) / 3,
        ⟨by linarith, by linarith⟩, by intro h'; linarith⟩
      (hk.comp (IsEmbedding.inclusion (hsub p hp))) ((measure_mono (image_mono (hsub p hp))).trans_lt hfin)
  · rw [hl, image_iUnion₂]
    ext z
    simp only [mem_iUnion, List.mem_map, exists_prop]
    constructor
    · rintro ⟨p, hp, hz⟩
      exact ⟨_, ⟨p, hp, rfl⟩, hz⟩
    · rintro ⟨a, ⟨p, hp, rfl⟩, hz⟩
      exact ⟨p, hp, hz⟩

/-- Helper (slit annulus, separating curves): for every radius `s ∈ (r, R)` the circle broken at the slits is a
curve of the separating family of `{r < |z| < R} \ S`; it differs from the circle `|z| = s` by a finite set. -/
theorem gm4c_circle_slit_mem {r R s : ℝ} (hr : 0 < r) (hrs : r < s) (hsR : s < R) {S : Set ℂ} {Θ : Set ℝ}
    (hΘ : Θ.Finite) (hSΘ : ∀ z ∈ S, z ≠ 0 ∧ arg z ∈ Θ) :
    ∃ γ ∈ separatingFamily (annulus r R \ S) (sphere 0 r) (sphere 0 R), γ =ᵐ[μH[1]] sphere 0 s := by
  classical
  have hs : 0 < s := hr.trans hrs
  have hk₁ := gm4b_circle_arc_emb hs
  have hk₂ : IsEmbedding ((Ioo (-π) π).domRestrict fun θ : ℝ => -((s : ℂ) * exp (θ * I))) :=
    (Homeomorph.neg ℂ).isEmbedding.comp hk₁
  set k₁ : ℝ → ℂ := fun θ => (s : ℂ) * exp (θ * I) with hk₁def
  set k₂ : ℝ → ℂ := fun θ => -((s : ℂ) * exp (θ * I)) with hk₂def
  have hnorm : ∀ θ : ℝ, ‖k₁ θ‖ = s := fun θ => by
    simp only [hk₁def]
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hs.le]
  have hnorm₂ : ∀ θ : ℝ, ‖k₂ θ‖ = s := fun θ => by
    simp only [hk₂def]
    rw [norm_neg]
    exact hnorm θ
  have hfin := gm4b_hausdorff_sphere_lt_top hs
  have hsub₁ : k₁ '' Ioo (-π) π ⊆ sphere 0 s := by
    rintro _ ⟨θ, -, rfl⟩
    rw [mem_sphere_zero_iff_norm]
    exact hnorm θ
  have hsub₂ : k₂ '' Ioo (-π) π ⊆ sphere 0 s := by
    rintro _ ⟨θ, -, rfl⟩
    rw [mem_sphere_zero_iff_norm]
    exact hnorm₂ θ
  have hinj₁ : InjOn k₁ (Ioo (-π) π) := fun a ha b hb h =>
    congrArg Subtype.val (hk₁.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) h)
  have hinj₂ : InjOn k₂ (Ioo (-π) π) := fun a ha b hb h =>
    congrArg Subtype.val (hk₂.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) h)
  -- the finite set of points of the circle lying on slits
  set Q : Set ℂ := k₁ '' Θ with hQ
  have hSQ : ∀ z ∈ S, ‖z‖ = s → z ∈ Q := by
    intro z hz hzs
    refine ⟨arg z, (hSΘ z hz).2, ?_⟩
    have h := norm_mul_exp_arg_mul_I z
    rw [hzs] at h
    exact h
  have hQfin : Q.Finite := hΘ.image _
  set P₁ : Set ℝ := {θ | θ ∈ Ioo (-π) π ∧ k₁ θ ∈ S} with hP₁
  set P₂ : Set ℝ := {θ | θ ∈ Ioo (-π) π ∧ k₂ θ ∈ S} with hP₂
  have hP₁fin : P₁.Finite :=
    Set.Finite.of_injOn (f := k₁) (t := Q) (fun θ hθ => hSQ _ hθ.2 (hnorm θ)) (hinj₁.mono fun θ hθ => hθ.1) hQfin
  have hQ₂ : (k₂ '' P₂ ⊆ Q) := by
    rintro _ ⟨θ, hθ, rfl⟩
    exact hSQ _ hθ.2 (hnorm₂ θ)
  have hP₂fin : P₂.Finite :=
    Set.Finite.of_injOn (f := k₂) (t := Q) (fun θ hθ => hQ₂ ⟨θ, hθ, rfl⟩) (hinj₂.mono fun θ hθ => hθ.1) hQfin
  obtain ⟨l₁, hne₁, har₁, hu₁⟩ := gm4c_embedded_arcs hk₁ ((measure_mono hsub₁).trans_lt hfin) hP₁fin
  obtain ⟨l₂, hne₂, har₂, hu₂⟩ := gm4c_embedded_arcs hk₂ ((measure_mono hsub₂).trans_lt hfin) hP₂fin
  set L : List (Set ℂ) := l₁ ++ l₂ with hL
  have hLne : L ≠ [] := by simp [hL, hne₁]
  have har : ∀ a ∈ L, LehtoVirtanen1973.IsRectifiableArc a := fun a ha => by
    rcases List.mem_append.1 ha with h | h
    · exact har₁ a h
    · exact har₂ a h
  set A₁ : Set ℂ := k₁ '' (Ioo (-π) π \ P₁) with hA₁
  set A₂ : Set ℂ := k₂ '' (Ioo (-π) π \ P₂) with hA₂
  set γ : Set ℂ := A₁ ∪ A₂ with hγ
  have hγL : γ = ⋃ a ∈ L, a := by
    rw [hγ, hu₁, hu₂]
    ext z
    simp only [mem_union, mem_iUnion, List.mem_append, exists_prop, hL]
    constructor
    · rintro (⟨a, ha, hz⟩ | ⟨a, ha, hz⟩)
      · exact ⟨a, Or.inl ha, hz⟩
      · exact ⟨a, Or.inr ha, hz⟩
    · rintro ⟨a, ha | ha, hz⟩
      · exact Or.inl ⟨a, ha, hz⟩
      · exact Or.inr ⟨a, ha, hz⟩
  have hγsph : γ ⊆ sphere 0 s :=
    union_subset ((image_mono Set.sdiff_subset).trans hsub₁) ((image_mono Set.sdiff_subset).trans hsub₂)
  have hγS : ∀ z ∈ γ, z ∉ S := by
    rintro z (⟨θ, ⟨hθ, hθP⟩, rfl⟩ | ⟨θ, ⟨hθ, hθP⟩, rfl⟩) hzS
    · exact hθP ⟨hθ, hzS⟩
    · exact hθP ⟨hθ, hzS⟩
  have hsphA : sphere (0 : ℂ) s ⊆ annulus r R := fun z hz => by
    rw [mem_sphere_zero_iff_norm] at hz
    exact ⟨hz ▸ hrs, hz ▸ hsR⟩
  have hγΩ : γ ⊆ annulus r R \ S := fun z hz => ⟨hsphA (hγsph hz), hγS z hz⟩
  have hback : ∀ w ∈ annulus r R \ S, ‖w‖ = s → w ∈ γ := by
    rintro w ⟨hwA, hwS⟩ hws
    by_cases hw : arg w = π
    · have h := norm_mul_exp_arg_mul_I w
      rw [hw, hws, exp_pi_mul_I] at h
      have hwk : w = k₂ 0 := by
        simp only [hk₂def, ofReal_zero, zero_mul, exp_zero, mul_one]
        rw [← h]
        ring
      refine Or.inr ⟨0, ⟨⟨by linarith [Real.pi_pos], Real.pi_pos⟩, fun hP => hwS (by rw [hwk]; exact hP.2)⟩, hwk.symm⟩
    · have hθ : arg w ∈ Ioo (-π) π := ⟨neg_pi_lt_arg w, lt_of_le_of_ne (arg_le_pi w) hw⟩
      have hwk : w = k₁ (arg w) := by
        have h := norm_mul_exp_arg_mul_I w
        rw [hws] at h
        exact h.symm
      exact Or.inl ⟨arg w, ⟨hθ, fun hP => hwS (by rw [hwk]; exact hP.2)⟩, hwk.symm⟩
  have hpc : IsPathCurve (annulus r R \ S) γ := by
    have hfinL : ({a : Set ℂ | a ∈ L}).Finite := L.finite_toSet
    obtain ⟨f, hf⟩ := hfinL.countable.exists_eq_range (by
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L hLne
      exact ⟨a, ha⟩)
    have hmem' := Set.ext_iff.1 hf
    have hγ_union : γ = ⋃ n, f n := by
      rw [hγL]
      ext z
      simp only [mem_iUnion, exists_prop]
      constructor
      · rintro ⟨a, ha, hz⟩
        obtain ⟨n, rfl⟩ := (hmem' a).1 ha
        exact ⟨n, hz⟩
      · rintro ⟨n, hz⟩
        exact ⟨f n, (hmem' (f n)).2 (mem_range_self n), hz⟩
    refine ⟨f, fun n => ⟨har _ ((hmem' _).2 (mem_range_self n)), ?_⟩, hγ_union⟩
    exact (subset_iUnion f n).trans (by rw [← hγ_union]; exact hγΩ)
  have hsepIn : IsSeparatingIn (annulus r R \ S) γ (sphere 0 r) (sphere 0 R) := by
    intro z hz hboth
    obtain ⟨⟨p, hpK, hpE⟩, ⟨q, hqK, hqF⟩⟩ := hboth
    set K := connectedComponentIn ((annulus r R \ S) \ γ) z with hK
    have hKsub : K ⊆ (annulus r R \ S) \ γ := connectedComponentIn_subset _ _
    have hKconn : IsPreconnected K := isPreconnected_connectedComponentIn
    have hsplit : K ⊆ {w : ℂ | ‖w‖ < s} ∪ {w : ℂ | s < ‖w‖} := by
      intro w hw
      obtain ⟨hwΩ, hwγ⟩ := hKsub hw
      rcases lt_trichotomy ‖w‖ s with h1 | h1 | h1
      · exact Or.inl h1
      · exact absurd (hback w hwΩ h1) hwγ
      · exact Or.inr h1
    rcases hKconn.subset_or_subset (isOpen_lt continuous_norm continuous_const)
      (isOpen_lt continuous_const continuous_norm)
      (Set.disjoint_left.2 fun w (hw1 : ‖w‖ < s) (hw2 : s < ‖w‖) => lt_irrefl _ (hw1.trans hw2)) hsplit with
      h1 | h1
    · have hcl : closure K ⊆ {w : ℂ | ‖w‖ ≤ s} :=
        closure_minimal (h1.trans fun w (hw : ‖w‖ < s) => (le_of_lt hw : ‖w‖ ≤ s))
          (isClosed_le continuous_norm continuous_const)
      have h2 : ‖q‖ ≤ s := hcl hqK
      rw [mem_sphere_zero_iff_norm] at hqF
      linarith
    · have hcl : closure K ⊆ {w : ℂ | s ≤ ‖w‖} :=
        closure_minimal (h1.trans fun w (hw : s < ‖w‖) => (le_of_lt hw : s ≤ ‖w‖))
          (isClosed_le continuous_const continuous_norm)
      have h2 : s ≤ ‖p‖ := hcl hpK
      rw [mem_sphere_zero_iff_norm] at hpE
      linarith
  have hfinL : ({a : Set ℂ | a ∈ L}).Finite := L.finite_toSet
  refine ⟨γ, ⟨hpc, ⟨{a | a ∈ L}, hfinL, ?_, ?_⟩, hsepIn⟩, ?_⟩
  · rw [hγL]
    ext z
    simp
  · intro a ha
    exact Or.inl (har a ha).1
  · have : NullSingletonClass (μH[1] : Measure ℂ) := Measure.nullSingletonClass_hausdorff ℂ one_pos
    have hdiff : sphere (0 : ℂ) s \ γ ⊆ k₁ '' P₁ ∪ k₂ '' P₂ := by
      rintro z ⟨hz, hzγ⟩
      have hzs : ‖z‖ = s := mem_sphere_zero_iff_norm.1 hz
      by_cases hw : arg z = π
      · have h := norm_mul_exp_arg_mul_I z
        rw [hw, hzs, exp_pi_mul_I] at h
        have hwk : z = k₂ 0 := by
          simp only [hk₂def, ofReal_zero, zero_mul, exp_zero, mul_one]
          rw [← h]
          ring
        refine Or.inr ⟨0, ⟨⟨by linarith [Real.pi_pos], Real.pi_pos⟩, ?_⟩, hwk.symm⟩
        by_contra hS0
        exact hzγ (Or.inr ⟨0, ⟨⟨by linarith [Real.pi_pos], Real.pi_pos⟩, fun hP => hS0 hP.2⟩, hwk.symm⟩)
      · have hθ : arg z ∈ Ioo (-π) π := ⟨neg_pi_lt_arg z, lt_of_le_of_ne (arg_le_pi z) hw⟩
        have hwk : z = k₁ (arg z) := by
          have h := norm_mul_exp_arg_mul_I z
          rw [hzs] at h
          exact h.symm
        refine Or.inl ⟨arg z, ⟨hθ, ?_⟩, hwk.symm⟩
        by_contra hS0
        exact hzγ (Or.inl ⟨arg z, ⟨hθ, fun hP => hS0 hP.2⟩, hwk.symm⟩)
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [sdiff_eq_empty.2 hγsph, measure_empty]
    · exact measure_mono_null hdiff (((hP₁fin.image k₁).union (hP₂fin.image k₂)).measure_zero _)

/-- Helper (slit annulus, separating curves, lower bound): a separating curve of the slit annulus has
`∫_γ |z|⁻¹ dμH[1] ≥ 2π` (it meets every ray at a slit-free angle). -/
theorem gm4c_annulus_slit_sep_ge {r R : ℝ} (hr : 0 < r) (hrR : r < R) {S : Set ℂ} {Θ : Set ℝ} (hΘ : Θ.Finite)
    (hSΘ : ∀ z ∈ S, z ≠ 0 ∧ arg z ∈ Θ) {γ : Set ℂ}
    (hγ : γ ∈ separatingFamily (annulus r R \ S) (sphere 0 r) (sphere 0 R)) :
    ENNReal.ofReal (2 * π) ≤ ∫⁻ z in γ, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] := by
  obtain ⟨hpc, -, hsep⟩ := hγ
  have hR : 0 < R := hr.trans hrR
  have hmeas : MeasurableSet γ := gm4b_isPathCurve_measurableSet hpc
  have hhit : ∀ θ ∈ Ioo (-π) π, θ ∉ Θ → ∃ w ∈ γ, w ∈ slitPlane ∧ arg w = θ := by
    intro θ hθ hθΘ
    set u : ℂ := exp (θ * I) with hu
    have hun : ‖u‖ = 1 := norm_exp_ofReal_mul_I θ
    have harg : arg u = θ := by
      rw [hu, exp_mul_I]
      exact arg_cos_add_sin_mul_I ⟨hθ.1, hθ.2.le⟩
    set g : ℝ → ℂ := fun t => (0 : ℂ) + t * u with hg
    have hgc : Continuous g := by fun_prop
    have hgn : ∀ t : ℝ, 0 ≤ t → ‖g t‖ = t := by
      intro t ht
      simp only [hg, zero_add, norm_mul, hun, mul_one, Complex.norm_real, Real.norm_of_nonneg ht]
    have hgargs : ∀ t : ℝ, 0 < t → g t ∈ slitPlane ∧ arg (g t) = θ := by
      intro t ht
      have h1 : arg (g t) = θ := by
        simp only [hg, zero_add]
        rw [arg_real_mul u ht, harg]
      refine ⟨mem_slitPlane_iff_arg.2 ⟨by rw [h1]; exact hθ.2.ne, ?_⟩, h1⟩
      intro h
      have := hgn t ht.le
      rw [h, norm_zero] at this
      exact ht.ne this
    by_contra hno
    have hno' : ∀ t ∈ Ioo r R, g t ∉ γ := fun t ht hmem =>
      hno ⟨g t, hmem, (hgargs t (hr.trans ht.1)).1, (hgargs t (hr.trans ht.1)).2⟩
    set Sθ : Set ℂ := g '' Ioo r R with hS
    have hSA : Sθ ⊆ (annulus r R \ S) \ γ := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨⟨⟨by rw [hgn t (hr.trans ht.1).le]; exact ht.1, by rw [hgn t (hr.trans ht.1).le]; exact ht.2⟩,
        fun hS' => hθΘ ?_⟩, hno' t ht⟩
      have h2 := (hSΘ _ hS').2
      rwa [(hgargs t (hr.trans ht.1)).2] at h2
    have hconn : IsPreconnected Sθ := isPreconnected_Ioo.image g hgc.continuousOn
    have hm : g ((r + R) / 2) ∈ Sθ := ⟨(r + R) / 2, ⟨by linarith, by linarith⟩, rfl⟩
    have hK : Sθ ⊆ connectedComponentIn ((annulus r R \ S) \ γ) (g ((r + R) / 2)) :=
      hconn.subset_connectedComponentIn hm hSA
    have hcl : g '' closure (Ioo r R) ⊆ closure Sθ := image_closure_subset_closure_image hgc
    rw [closure_Ioo hrR.ne] at hcl
    refine hsep (g ((r + R) / 2)) (hSA hm) ⟨⟨g r, closure_mono hK (hcl ⟨r, ⟨le_rfl, hrR.le⟩, rfl⟩), ?_⟩,
      ⟨g R, closure_mono hK (hcl ⟨R, ⟨hrR.le, le_rfl⟩, rfl⟩), ?_⟩⟩
    · rw [mem_sphere_zero_iff_norm, hgn r hr.le]
    · rw [mem_sphere_zero_iff_norm, hgn R hR.le]
  have hsub : Ioo (-π) π \ Θ ⊆ arg '' (γ ∩ slitPlane) := fun θ hθ => by
    obtain ⟨w, hw, hws, hwa⟩ := hhit θ hθ.1 hθ.2
    exact ⟨w, ⟨hw, hws⟩, hwa⟩
  calc ENNReal.ofReal (2 * π) = μH[1] (Ioo (-π) π \ Θ) := by
        rw [hausdorffMeasure_real, measure_sdiff_null (hΘ.measure_zero _), Real.volume_Ioo]
        congr 1
        ring
    _ ≤ μH[1] (arg '' (γ ∩ slitPlane)) := measure_mono hsub
    _ ≤ ∫⁻ z in γ ∩ slitPlane, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] :=
        gm4b_hausdorff_arg_le (hmeas.inter isOpen_slitPlane.measurableSet) inter_subset_right
    _ ≤ ∫⁻ z in γ, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] := lintegral_mono_set inter_subset_left

/-- Helper (annulus, circles up to a null set of the curve): if for every radius `s ∈ (r, R)` the family `Γ` has a
curve that equals the circle `|z| = s` `μH[1]`-almost everywhere, then `L²/A ≤ 2π/log(R/r)`. -/
theorem gm4c_annulus_circles_ratio_le_ae {r R : ℝ} (hr : 0 < r) (hrR : r < R) {Γ : Set (Set ℂ)}
    (hΓ : ∀ s ∈ Ioo r R, ∃ γ ∈ Γ, γ =ᵐ[μH[1]] sphere 0 s) {ρ : ℂ → ℝ≥0∞}
    (hρ : ρ ∈ LiZhongQC.densitiesP0 (annulus r R)) :
    pathRhoLength Γ ρ ^ 2 / LiZhongQC.rhoArea ρ (annulus r R) ≤ ENNReal.ofReal (2 * π / Real.log (R / r)) := by
  obtain ⟨hm, hA0, hAt⟩ := gm4a_mem_densitiesP0.1 hρ
  have hA : LiZhongQC.rhoArea ρ (annulus r R) =
      ∫⁻ s in Ioo r R, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s * ρ ((0 : ℂ) + s * exp (θ * I)) ^ 2 := by
    rw [gm4a_rhoArea_eq, gm4b_lintegral_annulus_polar hr (hm.pow_const 2)]
  have hcore := gm4b_annulus_core2 hr hrR (G := fun s θ => ρ ((0 : ℂ) + s * exp (θ * I)))
    (fun s => hm.comp (by fun_prop)) (L := pathRhoLength Γ ρ) fun s hs => by
      obtain ⟨γ, hγΓ, hae⟩ := hΓ s hs
      refine (iInf₂_le _ hγΓ).trans_eq ?_
      rw [setLIntegral_congr hae, gm4b_lintegral_sphere_sym (hr.trans hs.1) hm]
      simp only [zero_add]
  rw [← hA] at hcore
  have hlog : 0 < Real.log (R / r) := Real.log_pos (by rw [one_lt_div hr]; exact hrR)
  exact gm4b_div_le_of_mul_le hlog hA0.ne' hAt.ne hcore

/-- Helper (slit annulus): `λ(Γ*) = 2π/log(R/r)` for the family of curves separating the boundary circles. -/
theorem gm4c_annulus_slit_sep_value {r R : ℝ} (hr : 0 < r) (hrR : r < R) {S : Set ℂ} {Θ : Set ℝ} (hΘ : Θ.Finite)
    (hSΘ : ∀ z ∈ S, z ≠ 0 ∧ arg z ∈ Θ) :
    conjExtremalDistGM (annulus r R \ S) (sphere 0 r) (sphere 0 R) = ENNReal.ofReal (2 * π / Real.log (R / r)) := by
  have hS0 : volume S = 0 := gm4c_volume_arg_finite hΘ hSΘ
  have hlog : 0 < Real.log (R / r) := Real.log_pos (by rw [one_lt_div hr]; exact hrR)
  have hA' := gm4c_rhoArea_diff_null (D := annulus r R) hS0
  obtain ⟨hmem, hA, -⟩ := gm4c_annulus_slit_metric hr hrR hΘ hSΘ (c := 1) one_pos
  refine le_antisymm ?_ ?_
  · rw [conjExtremalDistGM, gm4a_extremalLengthGM_eq]
    refine iSup₂_le fun ρ hρ => ?_
    have hρ' : ρ ∈ LiZhongQC.densitiesP0 (annulus r R) := by
      rw [gm4a_mem_densitiesP0] at hρ ⊢
      rwa [hA' ρ] at hρ
    rw [hA' ρ]
    exact gm4c_annulus_circles_ratio_le_ae hr hrR (fun s hs => gm4c_circle_slit_mem hr hs.1 hs.2 hΘ hSΘ) hρ'
  · rw [conjExtremalDistGM]
    set ρ : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖⁻¹) with hρ
    have hmem' : ρ ∈ LiZhongQC.densitiesP0 (annulus r R \ S) := by simpa [hρ, one_div] using hmem
    have hA'' : LiZhongQC.rhoArea ρ (annulus r R \ S) = ENNReal.ofReal (2 * π * 1 ^ 2 * Real.log (R / r)) := by
      simpa [hρ, one_div] using hA
    have hL : ENNReal.ofReal (2 * π) ≤ pathRhoLength
        (separatingFamily (annulus r R \ S) (sphere 0 r) (sphere 0 R)) ρ := by
      rw [gm4a_pathRhoLength_eq]
      refine le_iInf₂ fun γ hγ => ?_
      simpa [hρ] using gm4c_annulus_slit_sep_ge hr hrR hΘ hSΘ hγ
    have harith : ENNReal.ofReal (2 * π / Real.log (R / r)) =
        ENNReal.ofReal (2 * π) ^ 2 / ENNReal.ofReal (2 * π * 1 ^ 2 * Real.log (R / r)) := by
      rw [← ENNReal.ofReal_pow (by positivity), one_pow, mul_one,
        ← ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 * π * Real.log (R / r))]
      congr 1
      field_simp
    refine le_trans ?_ (gm4a_ratio_le hmem')
    rw [hA'', harith]
    exact ENNReal.div_le_div_right (pow_le_pow_left' hL 2) _

/-- **Unlabelled** (Ch. IV §4, P1:6231; used in the proof of Theorem 4.2, and cited in Chapter VIII, P2:4940
"Removing a radial slit from an annulus does not affect the extremal distance between its bounding circles", and in
App. H, P3:4895). By the proof of Example 1.2, the extremal distance and the conjugate extremal distance between the
boundary circles of an annulus will not change if (finitely many) radial slits are removed from the annulus.
Modelling: `0 < r < R < ∞` (as in Example 1.2); the slits are `IsRadialSlit r R`; the boundary circles are
`|z| = r` and `|z| = R`. -/
theorem annulus_radialSlits {r R : ℝ} (hr : 0 < r) (hrR : r < R) {n : ℕ} {L : Fin n → Set ℂ}
    (hL : ∀ j, IsRadialSlit r R (L j)) :
    extremalDistGM (annulus r R \ ⋃ j, L j) (sphere 0 r) (sphere 0 R) =
        extremalDistGM (annulus r R) (sphere 0 r) (sphere 0 R) ∧
      conjExtremalDistGM (annulus r R \ ⋃ j, L j) (sphere 0 r) (sphere 0 R) =
        conjExtremalDistGM (annulus r R) (sphere 0 r) (sphere 0 R) := by
  obtain ⟨Θ, hΘ, -, hSΘ⟩ := gm4c_slits_radial hr hL
  exact ⟨(gm4c_annulus_slit_value hr hrR hΘ hSΘ).trans (gm4b_annulus_value hr hrR).symm,
    (gm4c_annulus_slit_sep_value hr hrR hΘ hSΘ).trans (gm4b_annulus_sep_value hr hrR).1.symm⟩

/-- **Theorem 4.2** (Ch. IV §4; cited in Chapter V, P1:7151, and in App. H, P3:4582, 4750, 4911). Suppose `Ω` is
bounded by two disjoint Jordan curves `Γ₁`, `Γ₂` and suppose `E` and `F` are finite unions of closed arcs with
`E ⊆ Γ₁` and `F ⊆ Γ₂`. Then there is a conformal map `ψ` of `Ω` onto an annulus with finitely many radial slits
removed such that `ψ` is continuous on `Ω̄` and the images of `E` and `F` are the two boundary circles. The extremal
metrics for the extremal distance between `E` and `F` are constant multiples of `|ψ'(z)|/|ψ(z)|` and
`d_Ω(E, F) = 1/d*_Ω(E, F) = (1/2π) log R`, where `R > 1` is the ratio of the radii of the boundary circles.
Modelling: `Ω` is a domain of `ℂ*` with `∂Ω = Γ₁ ∪ Γ₂`, `Γ_j` disjoint Jordan curves of `ℂ*`; the annulus is
`{r₁ < |z| < r₂}`, `0 < r₁ < r₂`, so `R = r₂/r₁`; "the images of `E` and `F` are the two boundary circles" is read in
either order; the metric statements are for this `ψ`, on finite parts; `|ψ'|/|ψ|` is
`LehtoVirtanen1973.logDerivDensity ψ` on the finite part of `Ω`; the constants are positive; "the extremal metrics
are constant multiples of `|ψ'|/|ψ|`" is stated as two claims (module docstring): every `c |ψ'|/|ψ|`, `c > 0`, is an
extremal metric, and every extremal metric equals some `c |ψ'|/|ψ|` almost everywhere for area measure on `Ω`. -/
theorem thm4_4_2 {Ω Γ₁ Γ₂ E F : Set ExtPlane} (hΩ : IsDomainExt Ω) (hΓ₁ : IsJordanCurve Γ₁)
    (hΓ₂ : IsJordanCurve Γ₂) (hΓ₁₂ : Disjoint Γ₁ Γ₂) (hΩΓ : frontier Ω = Γ₁ ∪ Γ₂)
    (hE : IsFiniteUnionOf (fun s => IsClosedJordanArc s ∧ s ⊆ Γ₁) E)
    (hF : IsFiniteUnionOf (fun s => IsClosedJordanArc s ∧ s ⊆ Γ₂) F) :
    ∃ (ψ : ExtPlane → ExtPlane) (r₁ r₂ : ℝ) (n : ℕ) (L : Fin n → Set ℂ), 0 < r₁ ∧ r₁ < r₂ ∧
      (∀ j, IsRadialSlit r₁ r₂ (L j)) ∧ IsConformalMap ψ Ω ∧ ψ '' Ω = toExt (annulus r₁ r₂ \ ⋃ j, L j) ∧
      ContinuousOn ψ (closure Ω) ∧
      ((ψ '' E = toExt (sphere 0 r₁) ∧ ψ '' F = toExt (sphere 0 r₂)) ∨
        (ψ '' E = toExt (sphere 0 r₂) ∧ ψ '' F = toExt (sphere 0 r₁))) ∧
      (∀ c : ℝ, 0 < c → IsExtremalMetricGM (finitePart Ω)
          (joiningFamily (finitePart Ω) (finitePart E) (finitePart F))
          (fun z => ENNReal.ofReal c * logDerivDensity ψ (finitePart Ω) z)) ∧
      (∀ ρ : ℂ → ℝ≥0∞, IsExtremalMetricGM (finitePart Ω)
          (joiningFamily (finitePart Ω) (finitePart E) (finitePart F)) ρ →
        ∃ c : ℝ, 0 < c ∧ ρ =ᵐ[volume.restrict (finitePart Ω)]
          fun z => ENNReal.ofReal c * logDerivDensity ψ (finitePart Ω) z) ∧
      extremalDistGM (finitePart Ω) (finitePart E) (finitePart F) =
        (conjExtremalDistGM (finitePart Ω) (finitePart E) (finitePart F))⁻¹ ∧
      extremalDistGM (finitePart Ω) (finitePart E) (finitePart F) =
        ENNReal.ofReal (1 / (2 * π) * Real.log (r₂ / r₁)) := by
  sorry

end GarnettMarshall2005
