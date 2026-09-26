import LiZhongQC.Ch01.S01_Quadrilateral
import LiZhongQC.Ch01.S02_DoublyConnected
import LiZhongQC.Ch01.S03_ExtremalLength
import LiZhongQC.Lemmas.Quadrilateral

/-!
# §4 极值长度与共形模的关系 — Extremal length and conformal modulus

* curves joining opposite sides of a quadrilateral     — `TopQuad.joiningCurves`
* Theorem 4.1 (`M(Q) = 1/λ(Γ)`)                        — `thm4_1_modulus_eq_inv_extremalLength`
* estimate (4.6)                                       — `eq4_6_modulus_le_rhoArea`
* Theorem 4.2 (Rengel's inequality)                    — `thm4_2_rengel`
* Theorem 4.3 (the extremal metric `|f'|`)             — `thm4_3_extremal_metric`,
                                                          `thm4_3_extremal_metric_unique`
* Theorem 4.4 (equality in Rengel's inequality)        — `thm4_4_rengel_eq_right_iff`,
                                                          `thm4_4_rengel_eq_left_iff`
* Theorems 4.5, 4.6, 4.7, (4.13) (monotonicity, subadditivity)
* Theorem 4.8 (continuity of the modulus)              — `thm4_8_modulus_continuous`
* Theorem 4.9 (`M(B) = 2π/λ(Γ)`)                       — `thm4_9_dcModulus_eq`
* (4.22) and its equality case                          — `eq4_22`, `eq4_22_eq_iff`
* Theorems 4.10, 4.11 (monotonicity, subadditivity for doubly connected domains)
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace LiZhongQC

namespace TopQuad

/-- `γ` is a locally rectifiable curve in `Q` joining the side `i` to the opposite side
`i + 2` (for `i = 0`: a curve joining the first pair of opposite sides, `(z₁,z₂)` and
`(z₃,z₄)`). -/
def IsJoiningCurve (Q : TopQuad) (i : Fin 4) (γ : LRCurve) : Prop :=
  γ.trace ⊆ Q.dom ∧
    (∃ p ∈ Q.side i, Tendsto (fun t => ((γ.toFun t : ℂ) : ExtPlane)) (𝓝[>] 0) (𝓝 p)) ∧
    ∃ q ∈ Q.side (i + 2), Tendsto (fun t => ((γ.toFun t : ℂ) : ExtPlane)) (𝓝[<] 1) (𝓝 q)

/-- The family of all locally rectifiable curves in `Q` joining side `i` to side `i + 2`. -/
def joiningCurves (Q : TopQuad) (i : Fin 4) : Set LRCurve := {γ | Q.IsJoiningCurve i γ}

/-- `d₁` (resp. `d₂` for `i = 1`): the infimum of the Euclidean lengths of the curves in `Q`
joining the first (resp. second) pair of opposite sides. -/
def sideDistance (Q : TopQuad) (i : Fin 4) : ℝ≥0∞ := ⨅ γ ∈ Q.joiningCurves i, γ.length

/-- The Euclidean area `m(Q)`. -/
def area (Q : TopQuad) : ℝ≥0∞ := volume Q.dom

/-- The side `i` of `Q` as a subset of `ℂ` (for a bounded quadrilateral no vertex is `∞`). -/
def sideC (Q : TopQuad) (i : Fin 4) : Set ℂ := {z : ℂ | (z : ExtPlane) ∈ Q.side i}

/-- `Qₙ` tends to `Q` from the inside (§4.5): `Qₙ ⊆ Q`, the vertices of `Qₙ` converge to
those of `Q`, the boundary of `Qₙ` eventually lies in any neighbourhood of `∂Q`, and each side
of `Qₙ` eventually lies in any neighbourhood of the corresponding side of `Q`.

The last clause is a **correction**: it is not part of the book's definition, and without it
Theorem 4.8 is false.  See the note on `thm4_8_modulus_continuous`. -/
def TendsFromInside (Qn : ℕ → TopQuad) (Q : TopQuad) : Prop :=
  (∀ n, (Qn n).dom ⊆ Q.dom) ∧ (∀ i, Tendsto (fun n => (Qn n).vert i) atTop (𝓝 (Q.vert i))) ∧
    (∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ frontier (Qn n).dom, infDist z (frontier Q.dom) < ε) ∧
    ∀ i : Fin 4, ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ (Qn n).sideC i, infDist z (Q.sideC i) < ε

end TopQuad

/-- A standard conformal map of `Q` onto `R(0, a, a+bi, bi)` carries the curves joining the first
pair of opposite sides of `Q` onto the curves joining the bottom and top edges of the rectangle
(the boundary extension maps the sides of `Q` onto those edges). -/
theorem isCurveImage_joiningCurves {Q : TopQuad} {a b : ℝ} {f : ℂ → ℂ}
    (hf : Q.IsStdConformalMap a b f) :
    IsCurveImage f (Q.joiningCurves 0) (rectJoiningCurves a b) := by
  obtain ⟨ha, hb, hconf, F, hF, hFv⟩ := hf
  have hQ := Q.isTopQuad
  have hU : IsOpen Q.dom := hQ.1.1
  have hV : IsOpen (rectangle a b) := isOpen_rectangle a b
  have hside0 : F '' Q.side 0 = toExt (Icc 0 a ×ℂ {0}) := by
    rw [TopQuad.image_side hV hconf hF 0, hFv, hFv, hFv]
    exact boundaryArc_frontier_toExt_rectangle_bottom ha hb
  have hside2 : F '' Q.side 2 = toExt (Icc 0 a ×ℂ {b}) := by
    rw [TopQuad.image_side hV hconf hF 2, hFv, hFv, hFv]
    exact boundaryArc_frontier_toExt_rectangle_top ha hb
  have hsideC : ∀ i, Q.side i ⊆ closure (toExt Q.dom) := fun i p hp =>
    frontier_subset_closure hp.1
  have hg := hconf.symm hU
  have hG : ContinuousOn (Function.invFunOn F (closure (toExt Q.dom)))
      (F '' closure (toExt Q.dom)) :=
    continuousOn_invFunOn_of_isClosed isClosed_closure hF.2.1 hF.2.2.1
  have hlim0 : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT zero_lt_one
  have hlim1 : Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT zero_lt_one
  constructor
  · intro γ hγ
    obtain ⟨htr, ⟨p, hp, hpγ⟩, ⟨q, hq, hqγ⟩⟩ := hγ
    have hmaps : MapsTo γ.toFun (Ioo 0 1) Q.dom := fun t ht => htr (mem_image_of_mem _ ht)
    have hforth : ∀ {l : Filter ℝ} {p : ExtPlane} {A : Set ℂ}, Ioo (0 : ℝ) 1 ∈ l →
        p ∈ closure (toExt Q.dom) → F p ∈ toExt A →
        Tendsto (fun t => ((γ.toFun t : ℂ) : ExtPlane)) l (𝓝 p) →
        ∃ p' ∈ A, Tendsto (f ∘ γ.toFun) l (𝓝 p') := by
      intro l p A hl hpC hFp hpγ
      obtain ⟨p', hp', hpp'⟩ := hFp
      refine ⟨p', hp', ?_⟩
      have h := hF.tendsto_comp hpC ((eventually_mem_set.2 hl).mono fun t ht => hmaps ht) hpγ
      rw [← hpp'] at h
      exact OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.2 h
    refine ⟨⟨f ∘ γ.toFun, locallyLipschitzOn_comp_of_differentiableOn hU hconf.1 isOpen_Ioo
      γ.locallyLipschitzOn hmaps⟩, ⟨?_, ?_, ?_⟩, fun t _ => rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      show f (γ.toFun t) ∈ rectangle a b
      rw [← hconf.2.2]
      exact mem_image_of_mem f (hmaps ht)
    · refine hforth hlim0 (hsideC 0 hp) ?_ hpγ
      rw [← hside0]
      exact mem_image_of_mem F hp
    · refine hforth hlim1 (hsideC 2 hq) ?_ hqγ
      rw [← hside2]
      exact mem_image_of_mem F hq
  · intro γ' hγ'
    obtain ⟨htr, ⟨p', hp', hpγ⟩, ⟨q', hq', hqγ⟩⟩ := hγ'
    have hmaps : MapsTo γ'.toFun (Ioo 0 1) (rectangle a b) := fun t ht =>
      htr (mem_image_of_mem _ ht)
    have hmaps' : MapsTo (Function.invFunOn f Q.dom ∘ γ'.toFun) (Ioo 0 1) Q.dom := fun t ht =>
      hg.mapsTo (hmaps ht)
    have hright : ∀ w ∈ rectangle a b, f (Function.invFunOn f Q.dom w) = w := fun w hw =>
      Function.invFunOn_eq (show w ∈ f '' Q.dom by rw [hconf.2.2]; exact hw)
    have hback : ∀ {l : Filter ℝ} {p : ExtPlane} {w : ℂ}, Ioo (0 : ℝ) 1 ∈ l →
        p ∈ closure (toExt Q.dom) → F p = (w : ExtPlane) → Tendsto γ'.toFun l (𝓝 w) →
        Tendsto (fun t => ((Function.invFunOn f Q.dom (γ'.toFun t) : ℂ) : ExtPlane)) l (𝓝 p) := by
      intro l p w hl hpC hFp hw
      have hw' : Tendsto (fun t => ((γ'.toFun t : ℂ) : ExtPlane)) l (𝓝 (F p)) := by
        rw [hFp]
        exact (OnePoint.continuous_coe.tendsto w).comp hw
      have hwC : Tendsto (fun t => ((γ'.toFun t : ℂ) : ExtPlane)) l
          (𝓝[F '' closure (toExt Q.dom)] (F p)) :=
        tendsto_nhdsWithin_iff.2 ⟨hw', (eventually_mem_set.2 hl).mono fun t ht => by
          rw [hF.2.2.2]
          exact subset_closure (mem_image_of_mem ((↑) : ℂ → ExtPlane) (hmaps ht))⟩
      have h := (hG (F p) (mem_image_of_mem F hpC)).tendsto.comp hwC
      rw [hF.2.2.1.leftInvOn_invFunOn hpC] at h
      refine h.congr' ((eventually_mem_set.2 hl).mono fun t ht => ?_)
      have hmem : ((Function.invFunOn f Q.dom (γ'.toFun t) : ℂ) : ExtPlane) ∈
          closure (toExt Q.dom) :=
        subset_closure (mem_image_of_mem ((↑) : ℂ → ExtPlane) (hmaps' ht))
      have hFeq : F ((Function.invFunOn f Q.dom (γ'.toFun t) : ℂ) : ExtPlane) =
          ((γ'.toFun t : ℂ) : ExtPlane) := by
        rw [hF.1 (Function.invFunOn f Q.dom (γ'.toFun t)) (hmaps' ht),
          hright (γ'.toFun t) (hmaps ht)]
      show Function.invFunOn F (closure (toExt Q.dom)) ((γ'.toFun t : ℂ) : ExtPlane) = _
      rw [← hFeq, hF.2.2.1.leftInvOn_invFunOn hmem]
    refine ⟨⟨Function.invFunOn f Q.dom ∘ γ'.toFun, locallyLipschitzOn_comp_of_differentiableOn
      (isOpen_rectangle a b) hg.1 isOpen_Ioo γ'.locallyLipschitzOn hmaps⟩, ⟨?_, ?_, ?_⟩,
      fun t ht => (hright _ (hmaps ht)).symm⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact hmaps' ht
    · have hmem : ((p' : ℂ) : ExtPlane) ∈ F '' Q.side 0 := by
        rw [hside0]
        exact mem_image_of_mem _ hp'
      obtain ⟨p, hp, hFp⟩ := hmem
      exact ⟨p, hp, hback hlim0 (hsideC 0 hp) hFp hpγ⟩
    · have hmem : ((q' : ℂ) : ExtPlane) ∈ F '' Q.side 2 := by
        rw [hside2]
        exact mem_image_of_mem _ hq'
      obtain ⟨q, hq, hFq⟩ := hmem
      exact ⟨q, hq, hback hlim1 (hsideC 2 hq) hFq hqγ⟩

/-! ## Theorem 4.1 and Rengel's inequality -/

/-- **Theorem 4.1**: `M(Q(z₁,z₂,z₃,z₄)) = [λ(Γ)]⁻¹`, where `Γ` is the family of locally
rectifiable curves in `Q` joining the first pair of opposite sides.  (A standard conformal map
carries `Γ` onto the curves joining the horizontal sides of `R(0,a,a+bi,bi)`, whose extremal
length is `b/a`; extremal length is conformally invariant.) -/
theorem thm4_1_modulus_eq_inv_extremalLength (Q : TopQuad) :
    ENNReal.ofReal Q.modulus = (extremalLength (Q.joiningCurves 0))⁻¹ := by
  obtain ⟨a, b, f, hf⟩ := thm1_1_exists_rectangle Q
  have ha : 0 < a := hf.1
  have hb : 0 < b := hf.2.1
  rw [modulus_eq_of_equivRect Q ⟨f, hf⟩, ← thm3_1_conformal_invariance Q.isTopQuad.1.1 hf.2.2.1
    (fun γ hγ => hγ.1) (isCurveImage_joiningCurves hf), extremalLength_rectJoiningCurves ha hb,
    ← ENNReal.ofReal_inv_of_pos (div_pos hb ha), inv_div]

/-- (4.6): `M(Q) ≤ m_ρ(Q)` for every Borel density `ρ` such that every curve joining the first
pair of opposite sides has `ρ`-length at least `1`. -/
theorem eq4_6_modulus_le_rhoArea (Q : TopQuad) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ)
    (hadm : ∀ γ ∈ Q.joiningCurves 0, 1 ≤ γ.rhoLength ρ) :
    ENNReal.ofReal Q.modulus ≤ rhoArea ρ Q.dom := by
  rw [thm4_1_modulus_eq_inv_extremalLength, ENNReal.inv_le_iff_inv_le]
  by_cases hfin : rhoArea ρ Q.dom = ⊤
  · rw [hfin, ENNReal.inv_top]
    exact zero_le
  have hU : IsOpen Q.dom := Q.isTopQuad.1.1
  have hA : rhoArea (Q.dom.indicator ρ) univ = rhoArea ρ Q.dom :=
    rhoArea_indicator_univ ρ hU.measurableSet
  have hle := le_extremalLengthIn isOpen_univ univ_nonempty (Q.joiningCurves 0)
    (hρ.indicator hU.measurableSet) (by rw [hA]; exact lt_top_iff_ne_top.2 hfin)
  have h1 : 1 ≤ ⨅ γ ∈ Q.joiningCurves 0, γ.rhoLength (Q.dom.indicator ρ) ^ 2 := by
    refine le_iInf₂ fun γ hγ => ?_
    rw [LRCurve.rhoLength_congr fun z hz => indicator_of_mem (hγ.1 hz) ρ]
    exact one_le_pow_of_one_le' (hadm γ hγ) 2
  calc (rhoArea ρ Q.dom)⁻¹ = 1 / rhoArea (Q.dom.indicator ρ) univ := by rw [hA, one_div]
    _ ≤ _ := ENNReal.div_le_div_right h1 _
    _ ≤ extremalLength (Q.joiningCurves 0) := hle

/-- The right-hand inequality of Rengel's inequality: `M(Q) ≤ m(Q)/d₁²` (the density `1` on `Q`
in the definition of the extremal length). -/
theorem rengel_right (Q : TopQuad) (hfin : Q.area < ⊤) :
    ENNReal.ofReal Q.modulus ≤ Q.area / Q.sideDistance 0 ^ 2 := by
  have hU : IsOpen Q.dom := Q.isTopQuad.1.1
  have hm0 : Q.area ≠ 0 := (hU.measure_pos volume Q.isTopQuad.1.2.1.nonempty).ne'
  have hA : rhoArea (Q.dom.indicator (1 : ℂ → ℝ≥0∞)) univ = Q.area := by
    rw [rhoArea_indicator_univ _ hU.measurableSet]
    simp only [Pi.one_apply, one_pow, setLIntegral_const, one_mul]
    rfl
  have hle := le_extremalLengthIn isOpen_univ univ_nonempty (Q.joiningCurves 0)
    (measurable_one.indicator hU.measurableSet) (by rw [hA]; exact hfin)
  have hL : (⨅ γ ∈ Q.joiningCurves 0, γ.rhoLength (Q.dom.indicator 1) ^ 2) =
      Q.sideDistance 0 ^ 2 := by
    rw [← iInf_rhoLength_sq]
    congr 1
    unfold TopQuad.sideDistance LRCurve.length
    exact iInf_congr fun γ => iInf_congr fun hγ =>
      LRCurve.rhoLength_congr fun z hz => indicator_of_mem (hγ.1 hz) (1 : ℂ → ℝ≥0∞)
  rw [hL, hA] at hle
  rw [thm4_1_modulus_eq_inv_extremalLength]
  calc (extremalLength (Q.joiningCurves 0))⁻¹ ≤ (Q.sideDistance 0 ^ 2 / Q.area)⁻¹ :=
        ENNReal.inv_le_inv.2 hle
    _ = Q.area / Q.sideDistance 0 ^ 2 := ENNReal.inv_div (Or.inl hfin.ne) (Or.inl hm0)

/-- The left-hand inequality of Rengel's inequality: `d₂²/m(Q) ≤ M(Q)` (Theorem 1.2 and the
right-hand inequality for `Q(z₂,z₃,z₄,z₁)`). -/
theorem rengel_left (Q : TopQuad) (hfin : Q.area < ⊤) :
    Q.sideDistance 1 ^ 2 / Q.area ≤ ENNReal.ofReal Q.modulus := by
  have h : ENNReal.ofReal Q.rotate.modulus ≤ Q.area / Q.sideDistance 1 ^ 2 :=
    rengel_right Q.rotate hfin
  have hU : IsOpen Q.dom := Q.isTopQuad.1.1
  have hm0 : Q.area ≠ 0 := (hU.measure_pos volume Q.isTopQuad.1.2.1.nonempty).ne'
  rw [thm1_2_modulus_rotate Q, one_div, ENNReal.ofReal_inv_of_pos (modulus_pos Q.rotate)]
  calc Q.sideDistance 1 ^ 2 / Q.area = (Q.area / Q.sideDistance 1 ^ 2)⁻¹ :=
        (ENNReal.inv_div (Or.inr hfin.ne) (Or.inr hm0)).symm
    _ ≤ (ENNReal.ofReal Q.rotate.modulus)⁻¹ := ENNReal.inv_le_inv.2 h

/-- **Theorem 4.2** (Rengel 不等式): `d₂²/m(Q) ≤ M(Q) ≤ m(Q)/d₁²`.
(Source note: `m(Q) < ∞` is assumed; for `m(Q) = d₁ = ∞` the right-hand side is `0` in `ℝ≥0∞`.) -/
theorem thm4_2_rengel (Q : TopQuad) (hfin : Q.area < ⊤) :
    Q.sideDistance 1 ^ 2 / Q.area ≤ ENNReal.ofReal Q.modulus ∧
      ENNReal.ofReal Q.modulus ≤ Q.area / Q.sideDistance 0 ^ 2 :=
  ⟨rengel_left Q hfin, rengel_right Q hfin⟩

/-- An extremal metric (极值度量) for the family `Γ` of curves in `D`. -/
def IsExtremalMetric (D : Set ℂ) (Γ : Set LRCurve) (ρ₀ : ℂ → ℝ≥0∞) : Prop :=
  ρ₀ ∈ densitiesP0 D ∧ (⨅ γ ∈ Γ, γ.rhoLength ρ₀ ^ 2) / rhoArea ρ₀ D = extremalLength Γ

/-- **Theorem 4.3** (existence): the modulus `|f'|` of the derivative of a standard conformal
map of `Q` onto a rectangle is an extremal metric for the curves joining the first pair of
opposite sides. -/
theorem thm4_3_extremal_metric (Q : TopQuad) {a b : ℝ} {f : ℂ → ℂ}
    (hf : Q.IsStdConformalMap a b f) :
    IsExtremalMetric Q.dom (Q.joiningCurves 0) (Q.dom.indicator fun z => ‖deriv f z‖ₑ) := by
  have ha : 0 < a := hf.1
  have hb : 0 < b := hf.2.1
  have hconf := hf.2.2.1
  have hU : IsOpen Q.dom := Q.isTopQuad.1.1
  -- `|f'|` is the pull-back by `f` of the density `1`
  have hρ₀ : (Q.dom.indicator fun z => ‖deriv f z‖ₑ) =
      Q.dom.indicator fun z => (1 : ℂ → ℝ≥0∞) (f z) * ‖deriv f z‖ₑ := by
    simp only [Pi.one_apply, one_mul]
  have harea : rhoArea (Q.dom.indicator fun z => ‖deriv f z‖ₑ) Q.dom =
      ENNReal.ofReal a * ENNReal.ofReal b := by
    have h := lintegral_image_conformal hU hconf (fun _ => (1 : ℝ≥0∞))
    simp only [mul_one, setLIntegral_const, one_mul] at h
    rw [← volume_rectangle a b, h]
    exact setLIntegral_congr_fun hU.measurableSet fun z hz => by simp [indicator_of_mem hz]
  have hm : Measurable (Q.dom.indicator fun z => ‖deriv f z‖ₑ) := by
    rw [hρ₀]
    exact measurable_pullback_density hU hconf.1.continuousOn measurable_one
  have hmem : (Q.dom.indicator fun z => ‖deriv f z‖ₑ) ∈ densitiesP0 Q.dom := by
    refine ⟨hm, ?_, ?_⟩
    · rw [harea]
      exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 ha).ne' (ENNReal.ofReal_pos.2 hb).ne'
    · rw [harea]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨hmem, le_antisymm ?_ ?_⟩
  · rw [← extremalLengthIn_eq hU Q.isTopQuad.1.2.1.nonempty (fun γ hγ => hγ.1)]
    unfold extremalLengthIn
    exact le_iSup₂_of_le _ hmem le_rfl
  · -- `λ(Γ) = b / a`, and every curve of `Γ` has `|f'|`-length at least `b`
    rw [← thm3_1_conformal_invariance hU hconf (fun γ hγ => hγ.1)
      (isCurveImage_joiningCurves hf), extremalLength_rectJoiningCurves ha hb, harea]
    have hlen : ∀ γ ∈ Q.joiningCurves 0,
        ENNReal.ofReal b ^ 2 ≤ γ.rhoLength (Q.dom.indicator fun z => ‖deriv f z‖ₑ) ^ 2 := by
      intro γ hγ
      obtain ⟨γ', hγ', heq⟩ := (isCurveImage_joiningCurves hf).1 γ hγ
      have h1 := LRCurve.rhoLength_image_conformal hU hconf hγ.1 heq 1
      rw [← hρ₀] at h1
      rw [← h1]
      exact pow_le_pow_left' (LRCurve.ofReal_le_rhoLength_one hb hγ') 2
    calc ENNReal.ofReal (b / a) =
        ENNReal.ofReal b ^ 2 / (ENNReal.ofReal a * ENNReal.ofReal b) := by
          rw [← ENNReal.ofReal_pow hb.le, ← ENNReal.ofReal_mul ha.le,
            ← ENNReal.ofReal_div_of_pos (mul_pos ha hb)]
          congr 1
          rw [div_eq_div_iff ha.ne' (mul_pos ha hb).ne']
          ring
      _ ≤ _ := ENNReal.div_le_div_right (le_iInf₂ hlen) _

/-- `(x - c)² + (c - x)² + 2cx = x² + c²` in `ℝ≥0∞` (truncated subtraction, `c < ∞`). -/
theorem ennreal_sq_sub_add_sq_sub {x c : ℝ≥0∞} (hc : c ≠ ⊤) :
    (x - c) ^ 2 + (c - x) ^ 2 + 2 * c * x = x ^ 2 + c ^ 2 := by
  lift c to ℝ≥0 using hc
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  lift x to ℝ≥0 using hx
  rcases le_total x c with h | h
  · have h1 : (x : ℝ≥0∞) - c = 0 := tsub_eq_zero_of_le (ENNReal.coe_le_coe.2 h)
    have key : (c - x) ^ 2 + 2 * c * x = x ^ 2 + c ^ 2 := by
      rw [← NNReal.coe_inj]
      push_cast [NNReal.coe_sub h]
      ring
    rw [h1, ← ENNReal.coe_sub, zero_pow two_ne_zero, zero_add]
    exact_mod_cast key
  · have h1 : (c : ℝ≥0∞) - x = 0 := tsub_eq_zero_of_le (ENNReal.coe_le_coe.2 h)
    have key : (x - c) ^ 2 + 2 * c * x = x ^ 2 + c ^ 2 := by
      rw [← NNReal.coe_inj]
      push_cast [NNReal.coe_sub h]
      ring
    rw [h1, ← ENNReal.coe_sub, zero_pow two_ne_zero, add_zero]
    exact_mod_cast key

/-- The equality case of the Cauchy–Schwarz inequality: if `(∬_s ρ)² = m(s) ∬_s ρ²` with
`0 < m(s) < ∞` and `∬_s ρ² < ∞`, then `ρ` is a.e. constant on `s`. -/
theorem ae_eq_const_of_sq_setLIntegral_eq {s : Set ℂ} {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ)
    (hV0 : volume s ≠ 0) (hVt : volume s ≠ ⊤) (hA : ∫⁻ z in s, ρ z ^ 2 ≠ ⊤)
    (heq : (∫⁻ z in s, ρ z) ^ 2 = volume s * ∫⁻ z in s, ρ z ^ 2) :
    ∀ᵐ z ∂(volume.restrict s), ρ z = (∫⁻ z in s, ρ z) / volume s := by
  obtain ⟨I, hI⟩ : ∃ I, ∫⁻ z in s, ρ z = I := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A, ∫⁻ z in s, ρ z ^ 2 = A := ⟨_, rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V, volume s = V := ⟨_, rfl⟩
  rw [hI, hAd, hVd] at heq
  rw [hAd] at hA
  rw [hVd] at hV0 hVt
  rw [hI, hVd]
  have hIt : I ≠ ⊤ := fun h => by
    rw [h, ENNReal.pow_eq_top_iff.2 ⟨rfl, two_ne_zero⟩] at heq
    exact ENNReal.mul_ne_top hVt hA heq.symm
  have hct : I / V ≠ ⊤ := ENNReal.div_ne_top hIt hV0
  have hcI : I / V * I = A := by
    rw [div_eq_mul_inv, mul_right_comm, ← sq, heq, mul_comm V, mul_assoc,
      ENNReal.mul_inv_cancel hV0 hVt, mul_one]
  have hc2V : (I / V) ^ 2 * V = A := by
    rw [sq, mul_assoc, ENNReal.div_mul_cancel hV0 hVt, hcI]
  have hmeas : Measurable fun z => (ρ z - I / V) ^ 2 + (I / V - ρ z) ^ 2 := by fun_prop
  have hsum : (∫⁻ z in s, ((ρ z - I / V) ^ 2 + (I / V - ρ z) ^ 2)) + 2 * A = A + A := by
    have h := lintegral_congr (μ := volume.restrict s)
      fun z => ennreal_sq_sub_add_sq_sub (x := ρ z) hct
    rw [lintegral_add_right _ (hρ.const_mul _), lintegral_add_right _ measurable_const,
      lintegral_const_mul _ hρ, lintegral_const, Measure.restrict_apply_univ, hI, hAd, hVd,
      mul_assoc, hcI, hc2V] at h
    exact h
  have hzero : ∫⁻ z in s, ((ρ z - I / V) ^ 2 + (I / V - ρ z) ^ 2) = 0 := by
    have h2A : 2 * A ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hA
    have h' : (∫⁻ z in s, ((ρ z - I / V) ^ 2 + (I / V - ρ z) ^ 2)) + 2 * A = 0 + 2 * A := by
      rw [zero_add, hsum, two_mul]
    exact (ENNReal.add_left_inj h2A).1 h'
  filter_upwards [(lintegral_eq_zero_iff hmeas).1 hzero] with z hz
  simp only [Pi.zero_apply, add_eq_zero, pow_eq_zero_iff two_ne_zero, tsub_eq_zero_iff_le] at hz
  exact le_antisymm hz.1 hz.2

/-- The vertical segments give `(inf_Γ l_ρ) ⋅ a ≤ ∬_R ρ` for the curves joining the horizontal
sides of `R(0, a, a+bi, bi)`. -/
theorem iInf_rhoLength_mul_le_setLIntegral {a b : ℝ} (hb : 0 < b) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) :
    (⨅ γ ∈ rectJoiningCurves a b, γ.rhoLength ρ) * ENNReal.ofReal a ≤
      ∫⁻ z in rectangle a b, ρ z := by
  calc (⨅ γ ∈ rectJoiningCurves a b, γ.rhoLength ρ) * ENNReal.ofReal a
      = ∫⁻ _ in Ioo 0 a, (⨅ γ ∈ rectJoiningCurves a b, γ.rhoLength ρ) := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
    _ ≤ ∫⁻ x in Ioo 0 a, ∫⁻ y in Ioo 0 b, ρ ((x : ℂ) + (y : ℂ) * I) :=
        setLIntegral_mono' measurableSet_Ioo fun x hx => by
          rw [← vertSeg_rhoLength hb ρ]
          exact iInf₂_le _ (vertSeg_mem hb hx)
    _ = ∫⁻ z in rectangle a b, ρ z := (setLIntegral_rectangle hρ).symm

/-- An extremal density for the curves joining the horizontal sides of `R(0, a, a+bi, bi)` is
a.e. constant on `R` (equality in the Cauchy–Schwarz inequality). -/
theorem ae_eq_const_of_rect_extremal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {σ : ℂ → ℝ≥0∞}
    (hσ : Measurable σ) (hA0 : rhoArea σ (rectangle a b) ≠ 0)
    (hAt : rhoArea σ (rectangle a b) ≠ ⊤)
    (hratio : (⨅ γ ∈ rectJoiningCurves a b, γ.rhoLength σ ^ 2) / rhoArea σ (rectangle a b) =
      ENNReal.ofReal (b / a)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ᵐ z ∂(volume.restrict (rectangle a b)), σ z = c := by
  have hV : volume (rectangle a b) = ENNReal.ofReal a * ENNReal.ofReal b := volume_rectangle a b
  have hV0 : volume (rectangle a b) ≠ 0 := by
    rw [hV]
    exact (ENNReal.mul_pos (ENNReal.ofReal_pos.2 ha).ne' (ENNReal.ofReal_pos.2 hb).ne').ne'
  have hVt : volume (rectangle a b) ≠ ⊤ := by
    rw [hV]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hL2 : (⨅ γ ∈ rectJoiningCurves a b, γ.rhoLength σ) ^ 2 =
      ENNReal.ofReal (b / a) * rhoArea σ (rectangle a b) := by
    rw [iInf_rhoLength_sq, ← hratio, ENNReal.div_mul_cancel hA0 hAt]
  have hk : ENNReal.ofReal (b / a) * ENNReal.ofReal a ^ 2 = ENNReal.ofReal a * ENNReal.ofReal b := by
    rw [← ENNReal.ofReal_pow ha.le, ← ENNReal.ofReal_mul (div_nonneg hb.le ha.le),
      ← ENNReal.ofReal_mul ha.le]
    congr 1
    rw [sq, ← mul_assoc, div_mul_cancel₀ b ha.ne', mul_comm]
  have hlow : volume (rectangle a b) * rhoArea σ (rectangle a b) ≤
      (∫⁻ z in rectangle a b, σ z) ^ 2 := by
    calc volume (rectangle a b) * rhoArea σ (rectangle a b)
        = ((⨅ γ ∈ rectJoiningCurves a b, γ.rhoLength σ) * ENNReal.ofReal a) ^ 2 := by
          rw [mul_pow, hL2, hV, mul_right_comm (ENNReal.ofReal (b / a)), hk]
      _ ≤ (∫⁻ z in rectangle a b, σ z) ^ 2 :=
          pow_le_pow_left' (iInf_rhoLength_mul_le_setLIntegral hb hσ) 2
  have heq : (∫⁻ z in rectangle a b, σ z) ^ 2 =
      volume (rectangle a b) * ∫⁻ z in rectangle a b, σ z ^ 2 :=
    le_antisymm (setLIntegral_sq_le hσ) hlow
  have hI0 : ∫⁻ z in rectangle a b, σ z ≠ 0 := fun h => by
    rw [h, zero_pow two_ne_zero] at heq
    exact mul_ne_zero hV0 hA0 heq.symm
  have hIt : ∫⁻ z in rectangle a b, σ z ≠ ⊤ := fun h => by
    rw [h, ENNReal.pow_eq_top_iff.2 ⟨rfl, two_ne_zero⟩] at heq
    exact ENNReal.mul_ne_top hVt hAt heq.symm
  exact ⟨_, ENNReal.div_ne_zero.2 ⟨hI0, hVt⟩, ENNReal.div_ne_top hIt hV0,
    ae_eq_const_of_sq_setLIntegral_eq hσ hV0 hVt hAt heq⟩

/-- **Theorem 4.3** (uniqueness): every other extremal metric differs from `|f'|` by a positive
constant factor (almost everywhere in `Q`).  (Pushed forward to the rectangle, an extremal metric is
a.e. constant by the equality case of the Cauchy–Schwarz inequality.) -/
theorem thm4_3_extremal_metric_unique (Q : TopQuad) {a b : ℝ} {f : ℂ → ℂ}
    (hf : Q.IsStdConformalMap a b f) {ρ₀ : ℂ → ℝ≥0∞}
    (hρ₀ : IsExtremalMetric Q.dom (Q.joiningCurves 0) ρ₀) :
    ∃ c : ℝ≥0, 0 < c ∧ ρ₀ =ᵐ[volume.restrict Q.dom] fun z => (c : ℝ≥0∞) * ‖deriv f z‖ₑ := by
  have ha : 0 < a := hf.1
  have hb : 0 < b := hf.2.1
  have hconf := hf.2.2.1
  have hU : IsOpen Q.dom := Q.isTopQuad.1.1
  have hV : IsOpen (rectangle a b) := isOpen_rectangle a b
  have hg := hconf.symm hU
  have himg := isCurveImage_joiningCurves hf
  have himg' : IsCurveImage (Function.invFunOn f Q.dom) (rectJoiningCurves a b)
      (Q.joiningCurves 0) :=
    himg.inv hconf.2.1 (fun γ hγ => hγ.1)
  obtain ⟨⟨hρm, hρ0, hρt⟩, hratio⟩ := hρ₀
  have hlam : extremalLength (Q.joiningCurves 0) = ENNReal.ofReal (b / a) := by
    rw [← thm3_1_conformal_invariance hU hconf (fun γ hγ => hγ.1) himg,
      extremalLength_rectJoiningCurves ha hb]
  rw [hlam] at hratio
  -- push `ρ₀` forward to the rectangle
  have hσm := measurable_pullback_density hV hg.1.continuousOn hρm
  have hσA := rhoArea_pullback hV hg ρ₀
  have hσL := iInf_rhoLength_sq_pullback hV hg (fun γ hγ => hγ.1) himg' ρ₀
  obtain ⟨c, hc0, hct, hae⟩ := ae_eq_const_of_rect_extremal ha hb hσm
    (by rw [hσA]; exact hρ0.ne') (by rw [hσA]; exact hρt.ne) (by rw [← hσL, hσA]; exact hratio)
  refine ⟨c.toNNReal, ENNReal.toNNReal_pos hc0 hct, ?_⟩
  rw [ENNReal.coe_toNNReal hct, Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet, ae_iff]
  -- pull the exceptional null set back by `f⁻¹`
  have hN := ae_iff.1 ((ae_restrict_iff' hV.measurableSet).1 hae)
  have hgN := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    ((hg.1.restrictScalars ℝ).mono fun w hw => (Classical.not_imp.1 hw).1) hN
  refine measure_mono_null (fun z hz => ?_) hgN
  obtain ⟨hzQ, hne⟩ := Classical.not_imp.1 hz
  have hfz : f z ∈ rectangle a b := by
    rw [← hconf.2.2]
    exact mem_image_of_mem f hzQ
  have hgfz : Function.invFunOn f Q.dom (f z) = z := hconf.2.1.leftInvOn_invFunOn hzQ
  refine ⟨f z, Classical.not_imp.2 ⟨hfz, fun hσc => hne ?_⟩, hgfz⟩
  have hder : deriv f z ≠ 0 := deriv_ne_zero_of_injOn hU hconf.1 hconf.2.1 hzQ
  have hgd : HasDerivAt (Function.invFunOn f Q.dom) (deriv f z)⁻¹ (f z) := by
    have hfd : HasDerivAt f (deriv f z) (Function.invFunOn f Q.dom (f z)) := by
      rw [hgfz]
      exact (hconf.1.differentiableAt (hU.mem_nhds hzQ)).hasDerivAt
    refine hfd.of_local_left_inverse (hg.1.differentiableAt (hV.mem_nhds hfz)).continuousAt
      hder ?_
    filter_upwards [hV.mem_nhds hfz] with y hy
    exact Function.invFunOn_eq (show y ∈ f '' Q.dom by rw [hconf.2.2]; exact hy)
  have hσw : (rectangle a b).indicator
      (fun w => ρ₀ (Function.invFunOn f Q.dom w) * ‖deriv (Function.invFunOn f Q.dom) w‖ₑ) (f z) =
      ρ₀ z * ‖deriv f z‖ₑ⁻¹ := by
    rw [indicator_of_mem hfz]
    show ρ₀ (Function.invFunOn f Q.dom (f z)) * ‖deriv (Function.invFunOn f Q.dom) (f z)‖ₑ = _
    rw [hgfz, hgd.deriv, enorm_inv hder]
  rw [hσw] at hσc
  show ρ₀ z = c * ‖deriv f z‖ₑ
  rw [← hσc, mul_assoc, ENNReal.inv_mul_cancel (enorm_ne_zero.2 hder) enorm_ne_top, mul_one]

/-! ### Equality in Rengel's inequality -/

/-- The rigid motion `z ↦ e^{iθ} z + c` as a homeomorphism of `ℂ`. -/
def rigidHomeomorph (θ : ℝ) (c : ℂ) : ℂ ≃ₜ ℂ where
  toFun z := exp ((θ : ℂ) * I) * z + c
  invFun w := exp (((-θ : ℝ) : ℂ) * I) * (w - c)
  left_inv z := by
    show exp (((-θ : ℝ) : ℂ) * I) * (exp ((θ : ℂ) * I) * z + c - c) = z
    rw [add_sub_cancel_right, ← mul_assoc, ← exp_add,
      show ((-θ : ℝ) : ℂ) * I + (θ : ℂ) * I = 0 by push_cast; ring, exp_zero, one_mul]
  right_inv w := by
    show exp ((θ : ℂ) * I) * (exp (((-θ : ℝ) : ℂ) * I) * (w - c)) + c = w
    rw [← mul_assoc, ← exp_add,
      show (θ : ℂ) * I + ((-θ : ℝ) : ℂ) * I = 0 by push_cast; ring, exp_zero, one_mul,
      sub_add_cancel]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The affine map `z ↦ α z + β` (`α ≠ 0`) as a homeomorphism of `ℂ`. -/
def affineHomeomorph (α β : ℂ) (hα : α ≠ 0) : ℂ ≃ₜ ℂ where
  toFun z := α * z + β
  invFun w := (w - β) / α
  left_inv z := by
    show (α * z + β - β) / α = z
    rw [add_sub_cancel_right, mul_div_cancel_left₀ z hα]
  right_inv w := by
    show α * ((w - β) / α) + β = w
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hα, sub_add_cancel]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Rigid motions preserve area. -/
theorem volume_image_rigidHomeomorph (θ : ℝ) (c : ℂ) {s : Set ℂ} (hs : IsOpen s) :
    volume (rigidHomeomorph θ c '' s) = volume s := by
  have hconf : IsConformalOnto (rigidHomeomorph θ c) s (rigidHomeomorph θ c '' s) :=
    ⟨(by fun_prop : Differentiable ℂ fun z => exp ((θ : ℂ) * I) * z + c).differentiableOn,
      (rigidHomeomorph θ c).injective.injOn, rfl⟩
  have h := lintegral_image_conformal hs hconf (fun _ => 1)
  have hd : ∀ z, ‖deriv (rigidHomeomorph θ c) z‖ₑ = 1 := fun z => by
    have hz : HasDerivAt (fun z : ℂ => exp ((θ : ℂ) * I) * z + c) (exp ((θ : ℂ) * I)) z := by
      simpa using ((hasDerivAt_id z).const_mul (exp ((θ : ℂ) * I))).add_const c
    rw [show ⇑(rigidHomeomorph θ c) = fun z : ℂ => exp ((θ : ℂ) * I) * z + c from rfl, hz.deriv,
      ← ofReal_norm, norm_exp_ofReal_mul_I, ENNReal.ofReal_one]
  simp only [hd, one_pow, one_mul, setLIntegral_const] at h
  exact h

/-- The inverse rigid motion of a rectangle `Q` and its boundary extension. -/
theorem rigid_extension_of_isRectangle {Q : TopQuad} {a b θ : ℝ} {c : ℂ}
    (hdom : Q.dom = (fun z => exp (θ * I) * z + c) '' rectangle a b)
    (hvert : ∀ i, Q.vert i = OnePoint.map (fun z => exp (θ * I) * z + c) (rectVert a b i)) :
    IsConformalOnto (rigidHomeomorph θ c).symm Q.dom (rectangle a b) ∧
      IsHomeoExtension (rigidHomeomorph θ c).symm Q.dom (rectangle a b)
        (OnePoint.map (rigidHomeomorph θ c).symm) ∧
      ∀ i, OnePoint.map (rigidHomeomorph θ c).symm (Q.vert i) = rectVert a b i := by
  have himg : (rigidHomeomorph θ c).symm '' Q.dom = rectangle a b := by
    rw [show Q.dom = rigidHomeomorph θ c '' rectangle a b from hdom, image_image]
    simp
  refine ⟨⟨?_, (rigidHomeomorph θ c).symm.injective.injOn, himg⟩,
    ⟨fun z _ => rfl, ?_, ?_, ?_⟩, fun i => ?_⟩
  · show DifferentiableOn ℂ (fun w => exp (((-θ : ℝ) : ℂ) * I) * (w - c)) Q.dom
    fun_prop
  · exact (Homeomorph.onePointCongr (rigidHomeomorph θ c).symm).continuous.continuousOn
  · exact (Homeomorph.onePointCongr (rigidHomeomorph θ c).symm).injective.injOn
  · have h1 : OnePoint.map (rigidHomeomorph θ c).symm '' toExt Q.dom = toExt (rectangle a b) := by
      unfold toExt
      rw [← himg, image_image, image_image]
      rfl
    rw [← h1]
    exact (Homeomorph.onePointCongr (rigidHomeomorph θ c).symm).image_closure (toExt Q.dom)
  · rw [hvert i]
    exact (Homeomorph.onePointCongr (rigidHomeomorph θ c)).symm_apply_apply _

/-- A rectangle `Q` has a rigid motion as standard conformal map. -/
theorem isStdConformalMap_of_isRectangle {Q : TopQuad} {a b θ : ℝ} {c : ℂ} (ha : 0 < a)
    (hb : 0 < b) (hdom : Q.dom = (fun z => exp (θ * I) * z + c) '' rectangle a b)
    (hvert : ∀ i, Q.vert i = OnePoint.map (fun z => exp (θ * I) * z + c) (rectVert a b i)) :
    Q.IsStdConformalMap a b (rigidHomeomorph θ c).symm :=
  have h := rigid_extension_of_isRectangle hdom hvert
  ⟨ha, hb, h.1, _, h.2.1, h.2.2⟩

/-- The first and third sides of a rectangle `Q = T(R(0, a, a+bi, bi))` are the images of the
bottom and top edges. -/
theorem side_of_isRectangle {Q : TopQuad} {a b θ : ℝ} {c : ℂ} (ha : 0 < a) (hb : 0 < b)
    (hdom : Q.dom = (fun z => exp (θ * I) * z + c) '' rectangle a b)
    (hvert : ∀ i, Q.vert i = OnePoint.map (fun z => exp (θ * I) * z + c) (rectVert a b i)) :
    Q.side 0 = toExt (rigidHomeomorph θ c '' (Icc 0 a ×ℂ {0})) ∧
      Q.side 2 = toExt (rigidHomeomorph θ c '' (Icc 0 a ×ℂ {b})) := by
  obtain ⟨hconf, hF, hFv⟩ := rigid_extension_of_isRectangle hdom hvert
  have hV := isOpen_rectangle a b
  have key : ∀ (S : Set ExtPlane) (E : Set ℂ),
      OnePoint.map (rigidHomeomorph θ c).symm '' S = toExt E →
        S = toExt (rigidHomeomorph θ c '' E) := by
    intro S E h
    have h' : S = OnePoint.map (rigidHomeomorph θ c) ''
        (OnePoint.map (rigidHomeomorph θ c).symm '' S) := by
      rw [image_image]
      conv_lhs => rw [← image_id S]
      exact image_congr fun x _ =>
        ((Homeomorph.onePointCongr (rigidHomeomorph θ c)).apply_symm_apply x).symm
    rw [h', h]
    unfold toExt
    rw [image_image, image_image]
    rfl
  constructor
  · apply key
    rw [TopQuad.image_side hV hconf hF 0, hFv, hFv, hFv]
    exact boundaryArc_frontier_toExt_rectangle_bottom ha hb
  · apply key
    rw [TopQuad.image_side hV hconf hF 2, hFv, hFv, hFv]
    exact boundaryArc_frontier_toExt_rectangle_top ha hb

theorem TopQuad.IsRectangle.area_ne_top {Q : TopQuad} (hQ : Q.IsRectangle) : Q.area ≠ ⊤ := by
  obtain ⟨a, b, θ, c, -, -, hdom, -⟩ := hQ
  show volume Q.dom ≠ ⊤
  rw [show Q.dom = rigidHomeomorph θ c '' rectangle a b from hdom,
    volume_image_rigidHomeomorph θ c (isOpen_rectangle a b), volume_rectangle]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- The shortest curves joining the horizontal sides of `R(0, a, a+bi, bi)` have length `b`. -/
theorem iInf_length_rectJoiningCurves {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ⨅ γ ∈ rectJoiningCurves a b, γ.length = ENNReal.ofReal b := by
  refine le_antisymm ?_ (le_iInf₂ fun γ hγ => LRCurve.ofReal_le_rhoLength_one hb hγ)
  refine (iInf₂_le (vertSeg b (a / 2)) (vertSeg_mem hb ⟨half_pos ha, half_lt_self ha⟩)).trans
    (le_of_eq ?_)
  rw [LRCurve.length, vertSeg_rhoLength hb]
  simp [Real.volume_Ioo]

/-- Equality holds on the right of Rengel's inequality for rectangles. -/
theorem rengel_right_eq_of_isRectangle {Q : TopQuad} (hQ : Q.IsRectangle) :
    ENNReal.ofReal Q.modulus = Q.area / Q.sideDistance 0 ^ 2 := by
  obtain ⟨a, b, θ, c, ha, hb, hdom, hvert⟩ := hQ
  have hS := isStdConformalMap_of_isRectangle ha hb hdom hvert
  have hU : IsOpen Q.dom := Q.isTopQuad.1.1
  have harea : Q.area = ENNReal.ofReal a * ENNReal.ofReal b := by
    show volume Q.dom = _
    rw [show Q.dom = rigidHomeomorph θ c '' rectangle a b from hdom,
      volume_image_rigidHomeomorph θ c (isOpen_rectangle a b), volume_rectangle]
  have hderiv : ∀ z, ‖deriv (rigidHomeomorph θ c).symm z‖ₑ = 1 := fun z => by
    have h : HasDerivAt (fun w : ℂ => exp (((-θ : ℝ) : ℂ) * I) * (w - c))
        (exp (((-θ : ℝ) : ℂ) * I)) z := by
      simpa using ((hasDerivAt_id z).sub_const c).const_mul (exp (((-θ : ℝ) : ℂ) * I))
    rw [show ⇑(rigidHomeomorph θ c).symm = fun w : ℂ => exp (((-θ : ℝ) : ℂ) * I) * (w - c)
      from rfl, h.deriv, ← ofReal_norm, norm_exp_ofReal_mul_I, ENNReal.ofReal_one]
  have hpb := iInf_rhoLength_sq_pullback hU hS.2.2.1 (fun γ hγ => hγ.1)
    (isCurveImage_joiningCurves hS) 1
  have hind : (Q.dom.indicator fun z => (1 : ℂ → ℝ≥0∞) ((rigidHomeomorph θ c).symm z) *
      ‖deriv (rigidHomeomorph θ c).symm z‖ₑ) = Q.dom.indicator 1 := by
    funext z
    by_cases hz : z ∈ Q.dom <;> simp [hz, hderiv]
  have hd : Q.sideDistance 0 ^ 2 = ENNReal.ofReal b ^ 2 := by
    rw [← iInf_length_rectJoiningCurves ha hb]
    unfold TopQuad.sideDistance LRCurve.length
    rw [iInf_rhoLength_sq, iInf_rhoLength_sq, hpb, hind]
    exact iInf_congr fun γ => iInf_congr fun hγ => by
      rw [LRCurve.rhoLength_congr fun z hz => indicator_of_mem (hγ.1 hz) (1 : ℂ → ℝ≥0∞)]
  rw [modulus_eq_of_equivRect Q ⟨_, hS⟩, harea, hd, ← ENNReal.ofReal_pow hb.le,
    ← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_div_of_pos (pow_pos hb 2)]
  congr 1
  rw [div_eq_div_iff hb.ne' (pow_pos hb 2).ne']
  ring

/-- `Q(z₂,z₃,z₄,z₁)` is a rectangle when `Q` is. -/
theorem TopQuad.IsRectangle.rotate {Q : TopQuad} (hQ : Q.IsRectangle) : Q.rotate.IsRectangle := by
  obtain ⟨a, b, θ, c, ha, hb, hdom, hvert⟩ := hQ
  have hI : exp (((π / 2 : ℝ) : ℂ) * I) = I := by
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  have key : ∀ z : ℂ, exp (((θ + π / 2 : ℝ) : ℂ) * I) * (-I * z + (a : ℂ) * I) +
      (exp ((θ : ℂ) * I) * a + c) = exp ((θ : ℂ) * I) * z + c := by
    intro z
    rw [show ((θ + π / 2 : ℝ) : ℂ) * I = (θ : ℂ) * I + ((π / 2 : ℝ) : ℂ) * I by push_cast; ring,
      exp_add, hI]
    linear_combination (exp ((θ : ℂ) * I) * ((a : ℂ) - z)) * I_sq
  refine ⟨b, a, θ + π / 2, exp ((θ : ℂ) * I) * a + c, hb, ha, ?_, fun i => ?_⟩
  · show Q.dom = _
    rw [hdom]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨-I * z + (a : ℂ) * I, rectangle_rotation_conformal.mapsTo hz, key z⟩
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨h1, h2, h3, h4⟩ := hu
      have e1 : (I * u + (a : ℂ)).re = a - u.im := by
        simp only [add_re, mul_re, I_re, I_im, ofReal_re]
        ring
      have e2 : (I * u + (a : ℂ)).im = u.re := by
        simp only [add_im, mul_im, I_re, I_im, ofReal_im]
        ring
      refine ⟨I * u + a, ?_, ?_⟩
      · show 0 < (I * u + (a : ℂ)).re ∧ (I * u + (a : ℂ)).re < a ∧ 0 < (I * u + (a : ℂ)).im ∧
          (I * u + (a : ℂ)).im < b
        rw [e1, e2]
        exact ⟨by linarith, by linarith, h1, h2⟩
      · have h := key (I * u + a)
        rw [show -I * (I * u + (a : ℂ)) + (a : ℂ) * I = u by linear_combination (-u) * I_sq] at h
        exact h.symm
  · show Q.vert (i + 1) = OnePoint.map _ (rectVert b a i)
    rw [hvert (i + 1), ← rectVert_rotation (a := a) (b := b) i]
    generalize rectVert a b (i + 1) = x
    induction x using OnePoint.rec with
    | infty =>
      rw [mobiusExt_infty_of_eq rfl]
      rfl
    | coe z =>
      rw [rotation_mobiusExt_coe]
      exact congrArg (fun w : ℂ => (w : ExtPlane)) (key z).symm

theorem TopQuad.isRectangle_of_rotate {Q : TopQuad} (h : Q.rotate.IsRectangle) :
    Q.IsRectangle := by
  obtain ⟨a, b, θ, c, ha, hb, hdom, hvert⟩ := h.rotate.rotate.rotate
  refine ⟨a, b, θ, c, ha, hb, hdom, fun i => ?_⟩
  have h4 : Q.vert (i + 1 + 1 + 1 + 1) =
      OnePoint.map (fun z => exp (θ * I) * z + c) (rectVert a b i) := hvert i
  have e : i + 1 + 1 + 1 + 1 = i := by fin_cases i <;> rfl
  rwa [e] at h4

/-- Equality holds on the left of Rengel's inequality for rectangles. -/
theorem rengel_left_eq_of_isRectangle {Q : TopQuad} (hQ : Q.IsRectangle) :
    Q.sideDistance 1 ^ 2 / Q.area = ENNReal.ofReal Q.modulus := by
  have h : ENNReal.ofReal Q.rotate.modulus = Q.area / Q.sideDistance 1 ^ 2 :=
    rengel_right_eq_of_isRectangle hQ.rotate
  have hU : IsOpen Q.dom := Q.isTopQuad.1.1
  have hm0 : Q.area ≠ 0 := (hU.measure_pos volume Q.isTopQuad.1.2.1.nonempty).ne'
  rw [thm1_2_modulus_rotate Q, one_div, ENNReal.ofReal_inv_of_pos (modulus_pos Q.rotate), h,
    ENNReal.inv_div (Or.inr hQ.area_ne_top) (Or.inr hm0)]

/-- If equality holds on the right of Rengel's inequality, then `Q` is a rectangle: the density `1`
is extremal, so `|f'|` is constant for a standard conformal map `f`, which is therefore affine. -/
theorem isRectangle_of_rengel_right_eq {Q : TopQuad} (hbdd : Bornology.IsBounded Q.dom)
    (heq : ENNReal.ofReal Q.modulus = Q.area / Q.sideDistance 0 ^ 2) : Q.IsRectangle := by
  obtain ⟨a, b, f, hf⟩ := thm1_1_exists_rectangle Q
  obtain ⟨ha, hb, hconf, F, hF, hFv⟩ := hf
  have hU : IsOpen Q.dom := Q.isTopQuad.1.1
  have hconn : IsConnected Q.dom := Q.isTopQuad.1.2.1
  have hmt : Q.area ≠ ⊤ := hbdd.measure_lt_top.ne
  have hm0 : Q.area ≠ 0 := (hU.measure_pos volume hconn.nonempty).ne'
  -- the density `1` on `Q` is extremal
  have hA : rhoArea (Q.dom.indicator (1 : ℂ → ℝ≥0∞)) Q.dom = Q.area := by
    unfold rhoArea TopQuad.area
    rw [setLIntegral_congr_fun hU.measurableSet (g := fun _ => (1 : ℝ≥0∞))
      fun z hz => by simp [indicator_of_mem hz], setLIntegral_const, one_mul]
  have hL : (⨅ γ ∈ Q.joiningCurves 0, γ.rhoLength (Q.dom.indicator 1) ^ 2) =
      Q.sideDistance 0 ^ 2 := by
    rw [← iInf_rhoLength_sq]
    congr 1
    unfold TopQuad.sideDistance LRCurve.length
    exact iInf_congr fun γ => iInf_congr fun hγ =>
      LRCurve.rhoLength_congr fun z hz => indicator_of_mem (hγ.1 hz) (1 : ℂ → ℝ≥0∞)
  have hlam : extremalLength (Q.joiningCurves 0) = Q.sideDistance 0 ^ 2 / Q.area := by
    rw [thm4_1_modulus_eq_inv_extremalLength] at heq
    rw [← inv_inv (extremalLength (Q.joiningCurves 0)), heq,
      ENNReal.inv_div (Or.inr hmt) (Or.inr hm0)]
  have hext : IsExtremalMetric Q.dom (Q.joiningCurves 0) (Q.dom.indicator 1) := by
    refine ⟨⟨measurable_one.indicator hU.measurableSet, ?_, ?_⟩, ?_⟩
    · rw [hA]
      exact pos_iff_ne_zero.2 hm0
    · rw [hA]
      exact lt_top_iff_ne_top.2 hmt
    · rw [hL, hA, hlam]
  obtain ⟨c, -, hae⟩ := thm4_3_extremal_metric_unique Q ⟨ha, hb, hconf, F, hF, hFv⟩ hext
  -- hence `|f'| = 1/c` on `Q`
  have hderivC : ContinuousOn (deriv f) Q.dom := (hconf.1.analyticOnNhd hU).deriv.continuousOn
  have hEq := Measure.eqOn_open_of_ae_eq hae hU
    (continuousOn_const.congr fun z hz => indicator_of_mem hz (1 : ℂ → ℝ≥0∞))
    ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp_continuousOn
      (continuous_enorm.comp_continuousOn hderivC))
  have hnorm : ∀ z ∈ Q.dom, ‖deriv f z‖ = (c : ℝ)⁻¹ := by
    intro z hz
    have h1 := hEq hz
    simp only [indicator_of_mem hz, Pi.one_apply, enorm_eq_nnnorm] at h1
    have h2 : (1 : ℝ≥0) = c * ‖deriv f z‖₊ := by exact_mod_cast h1
    have h3 : ‖deriv f z‖₊ = c⁻¹ := eq_inv_of_mul_eq_one_right h2.symm
    rw [← coe_nnnorm, h3, NNReal.coe_inv]
  -- `f'` is constant (maximum modulus principle), so `f` is affine
  obtain ⟨z₀, hz₀⟩ := hconn.nonempty
  have hmax : IsMaxOn (norm ∘ deriv f) Q.dom z₀ :=
    isMaxOn_iff.2 fun z hz => by simp only [Function.comp_apply, hnorm z hz, hnorm z₀ hz₀, le_rfl]
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hconn.isPreconnected hU
    (hconf.1.analyticOnNhd hU).deriv.differentiableOn hz₀ hmax
  have hα : deriv f z₀ ≠ 0 := deriv_ne_zero_of_injOn hU hconf.1 hconf.2.1 hz₀
  obtain ⟨β, hβ⟩ : ∃ β, ∀ z ∈ Q.dom, f z - deriv f z₀ * z = β := by
    refine hU.exists_is_const_of_fderiv_eq_zero hconn.isPreconnected
      (hconf.1.sub (differentiableOn_id.const_mul _)) fun z hz => ?_
    have h1 := (hconf.1.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    have h2 : HasDerivAt (fun z => f z - deriv f z₀ * z) (deriv f z - deriv f z₀ * 1) z :=
      h1.sub ((hasDerivAt_id z).const_mul _)
    rw [hconst hz, Function.const_apply, mul_one, sub_self] at h2
    simp [h2.hasFDerivAt.fderiv]
  have hA_eq : ∀ z ∈ Q.dom, f z = deriv f z₀ * z + β := fun z hz => by
    linear_combination hβ z hz
  -- write `f⁻¹(w) = e^{-i arg α} (w / |α|) - β / α`
  set α := deriv f z₀ with hαdef
  have hr0 : 0 < ‖α‖ := norm_pos_iff.2 hα
  have hrne : ((‖α‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hTa : ∀ w : ℂ, rigidHomeomorph (-arg α) (-β / α) (w / (‖α‖ : ℂ)) = (w - β) / α := by
    intro w
    show exp (((-arg α : ℝ) : ℂ) * I) * (w / (‖α‖ : ℂ)) + -β / α = (w - β) / α
    have hαe : (‖α‖ : ℂ) * exp ((arg α : ℂ) * I) = α := norm_mul_exp_arg_mul_I α
    have hinv : exp (((-arg α : ℝ) : ℂ) * I) = (exp ((arg α : ℂ) * I))⁻¹ := by
      rw [← exp_neg]
      congr 1
      push_cast
      ring
    rw [hinv]
    generalize (‖α‖ : ℂ) = r at hαe ⊢
    generalize exp ((arg α : ℂ) * I) = e at hαe ⊢
    rw [← hαe, inv_mul_eq_div, div_div, ← add_div, ← sub_eq_add_neg]
  have hscale : ∀ u : ℂ, u ∈ rectangle (a / ‖α‖) (b / ‖α‖) ↔ (‖α‖ : ℂ) * u ∈ rectangle a b := by
    intro u
    simp only [rectangle, mem_setOf_eq, re_ofReal_mul, im_ofReal_mul]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨mul_pos hr0 h1, (lt_div_iff₀' hr0).1 h2, mul_pos hr0 h3, (lt_div_iff₀' hr0).1 h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨pos_of_mul_pos_right h1 hr0.le, (lt_div_iff₀' hr0).2 h2,
        pos_of_mul_pos_right h3 hr0.le, (lt_div_iff₀' hr0).2 h4⟩
  have hdom : Q.dom = (fun z => exp ((-arg α : ℝ) * I) * z + -β / α) ''
      rectangle (a / ‖α‖) (b / ‖α‖) := by
    ext z
    constructor
    · intro hz
      have hfz : f z ∈ rectangle a b := by
        rw [← hconf.2.2]
        exact mem_image_of_mem f hz
      refine ⟨f z / (‖α‖ : ℂ), (hscale _).2 ?_, ?_⟩
      · rwa [mul_div_assoc', mul_div_cancel_left₀ _ hrne]
      · show rigidHomeomorph (-arg α) (-β / α) (f z / (‖α‖ : ℂ)) = z
        rw [hTa, hA_eq z hz, add_sub_cancel_right, mul_div_cancel_left₀ z hα]
    · rintro ⟨u, hu, rfl⟩
      have hru : (‖α‖ : ℂ) * u ∈ f '' Q.dom := by
        rw [hconf.2.2]
        exact (hscale u).1 hu
      obtain ⟨z, hz, hfz⟩ := hru
      have hu' : u = f z / (‖α‖ : ℂ) := by rw [hfz, mul_div_cancel_left₀ u hrne]
      show rigidHomeomorph (-arg α) (-β / α) u ∈ Q.dom
      rw [hu', hTa, hA_eq z hz, add_sub_cancel_right, mul_div_cancel_left₀ z hα]
      exact hz
  -- the boundary extension is the extension of the affine map
  have hFA : EqOn F (OnePoint.map (affineHomeomorph α β hα)) (closure (toExt Q.dom)) := by
    refine Set.EqOn.of_subset_closure (s := toExt Q.dom) ?_ hF.2.1
      (Homeomorph.onePointCongr (affineHomeomorph α β hα)).continuous.continuousOn
      subset_closure subset_rfl
    rintro _ ⟨z, hz, rfl⟩
    rw [hF.1 z hz, hA_eq z hz]
    rfl
  have hgen : ∀ w : ℂ, OnePoint.map (affineHomeomorph α β hα).symm (w : ExtPlane) =
      OnePoint.map (rigidHomeomorph (-arg α) (-β / α)) ((w / (‖α‖ : ℂ) : ℂ) : ExtPlane) :=
    fun w => congrArg (fun x : ℂ => (x : ExtPlane)) (hTa w).symm
  refine ⟨a / ‖α‖, b / ‖α‖, -arg α, -β / α, div_pos ha hr0, div_pos hb hr0, hdom, fun i => ?_⟩
  have hvC : Q.vert i ∈ closure (toExt Q.dom) := frontier_subset_closure (Q.isTopQuad.2.1 i)
  have h1 : OnePoint.map (affineHomeomorph α β hα) (Q.vert i) = rectVert a b i :=
    (hFA hvC).symm.trans (hFv i)
  have h2 : Q.vert i = OnePoint.map (affineHomeomorph α β hα).symm (rectVert a b i) := by
    rw [← h1]
    exact ((Homeomorph.onePointCongr (affineHomeomorph α β hα)).symm_apply_apply _).symm
  rw [h2]
  show _ = OnePoint.map (rigidHomeomorph (-arg α) (-β / α)) (rectVert (a / ‖α‖) (b / ‖α‖) i)
  fin_cases i
  · show OnePoint.map (affineHomeomorph α β hα).symm ((0 : ℂ) : ExtPlane) =
      OnePoint.map (rigidHomeomorph (-arg α) (-β / α)) ((0 : ℂ) : ExtPlane)
    rw [hgen, zero_div]
  · show OnePoint.map (affineHomeomorph α β hα).symm (((a : ℝ) : ℂ) : ExtPlane) =
      OnePoint.map (rigidHomeomorph (-arg α) (-β / α)) (((a / ‖α‖ : ℝ) : ℂ) : ExtPlane)
    rw [hgen]
    congr 2
    push_cast
    ring
  · show OnePoint.map (affineHomeomorph α β hα).symm (((a : ℂ) + (b : ℂ) * I : ℂ) : ExtPlane) =
      OnePoint.map (rigidHomeomorph (-arg α) (-β / α))
        ((((a / ‖α‖ : ℝ) : ℂ) + ((b / ‖α‖ : ℝ) : ℂ) * I : ℂ) : ExtPlane)
    rw [hgen]
    congr 2
    push_cast
    ring
  · show OnePoint.map (affineHomeomorph α β hα).symm (((b : ℂ) * I : ℂ) : ExtPlane) =
      OnePoint.map (rigidHomeomorph (-arg α) (-β / α)) ((((b / ‖α‖ : ℝ) : ℂ) * I : ℂ) : ExtPlane)
    rw [hgen]
    congr 2
    push_cast
    ring

/-- **Theorem 4.4** (right-hand equality in Rengel's inequality). -/
theorem thm4_4_rengel_eq_right_iff (Q : TopQuad) (hbdd : Bornology.IsBounded Q.dom) :
    ENNReal.ofReal Q.modulus = Q.area / Q.sideDistance 0 ^ 2 ↔ Q.IsRectangle :=
  ⟨isRectangle_of_rengel_right_eq hbdd, rengel_right_eq_of_isRectangle⟩

/-- **Theorem 4.4** (left-hand equality in Rengel's inequality). -/
theorem thm4_4_rengel_eq_left_iff (Q : TopQuad) (hbdd : Bornology.IsBounded Q.dom) :
    Q.sideDistance 1 ^ 2 / Q.area = ENNReal.ofReal Q.modulus ↔ Q.IsRectangle := by
  refine ⟨fun heq => TopQuad.isRectangle_of_rotate
    (isRectangle_of_rengel_right_eq (Q := Q.rotate) hbdd ?_), rengel_left_eq_of_isRectangle⟩
  have hU : IsOpen Q.dom := Q.isTopQuad.1.1
  have hmt : Q.area ≠ ⊤ := hbdd.measure_lt_top.ne
  have hm0 : Q.area ≠ 0 := (hU.measure_pos volume Q.isTopQuad.1.2.1.nonempty).ne'
  rw [thm1_2_modulus_rotate Q, one_div, ENNReal.ofReal_inv_of_pos (modulus_pos Q.rotate)] at heq
  show ENNReal.ofReal Q.rotate.modulus = Q.area / Q.sideDistance 1 ^ 2
  rw [← inv_inv (ENNReal.ofReal Q.rotate.modulus), ← heq,
    ENNReal.inv_div (Or.inl hmt) (Or.inl hm0)]

/-! ## Monotonicity, subadditivity and continuity -/

/-- Every curve contains itself. -/
theorem LRCurve.contains_refl (γ : LRCurve) : γ.Contains γ :=
  ⟨id, monotoneOn_id, mapsTo_id _, fun _ _ => ⟨1, univ, univ_mem, LipschitzWith.id.lipschitzOnWith⟩,
    fun _ _ => rfl⟩

/-- Curves of a sub-quadrilateral whose first pair of sides lies on that of `Q` join the first
pair of sides of `Q`. -/
theorem TopQuad.joiningCurves_subset {Q Q₁ : TopQuad} (hsub : Q₁.dom ⊆ Q.dom)
    (h₀ : Q₁.side 0 ⊆ Q.side 0) (h₂ : Q₁.side 2 ⊆ Q.side 2) :
    Q₁.joiningCurves 0 ⊆ Q.joiningCurves 0 := by
  rintro γ ⟨htr, ⟨p, hp, hpγ⟩, ⟨q, hq, hqγ⟩⟩
  exact ⟨htr.trans hsub, ⟨p, h₀ hp, hpγ⟩, ⟨q, h₂ hq, hqγ⟩⟩

/-- **Theorem 4.5** (单调性): if `Q₁ ⊆ Q` and the first pair of opposite sides of `Q₁` are
sub-arcs of those of `Q`, then `M(Q₁) ≤ M(Q)`. -/
theorem thm4_5_modulus_mono {Q Q₁ : TopQuad} (hsub : Q₁.dom ⊆ Q.dom)
    (h₀ : Q₁.side 0 ⊆ Q.side 0) (h₂ : Q₁.side 2 ⊆ Q.side 2) : Q₁.modulus ≤ Q.modulus := by
  have hlam : extremalLength (Q.joiningCurves 0) ≤ extremalLength (Q₁.joiningCurves 0) :=
    thm3_2_comparison fun γ hγ =>
      ⟨γ, TopQuad.joiningCurves_subset hsub h₀ h₂ hγ, LRCurve.contains_refl γ⟩
  rw [← ENNReal.ofReal_le_ofReal_iff (modulus_pos Q).le, thm4_1_modulus_eq_inv_extremalLength Q₁,
    thm4_1_modulus_eq_inv_extremalLength Q]
  exact ENNReal.inv_le_inv.2 hlam

/-- **Theorem 4.6** (次可加性): if `Q₁, Q₂ ⊆ Q` are disjoint and their first pairs of opposite
sides are sub-arcs of those of `Q`, then `M(Q₁) + M(Q₂) ≤ M(Q)`. -/
theorem thm4_6_modulus_subadditive {Q Q₁ Q₂ : TopQuad} (hsub₁ : Q₁.dom ⊆ Q.dom)
    (hsub₂ : Q₂.dom ⊆ Q.dom) (hdisj : Disjoint Q₁.dom Q₂.dom)
    (h₁₀ : Q₁.side 0 ⊆ Q.side 0) (h₁₂ : Q₁.side 2 ⊆ Q.side 2)
    (h₂₀ : Q₂.side 0 ⊆ Q.side 0) (h₂₂ : Q₂.side 2 ⊆ Q.side 2) :
    Q₁.modulus + Q₂.modulus ≤ Q.modulus := by
  have h := thm3_3_composition_i Q₁.isTopQuad.1.1 Q₂.isTopQuad.1.1 hdisj
    (Γ := Q.joiningCurves 0) (Γ₁ := Q₁.joiningCurves 0) (Γ₂ := Q₂.joiningCurves 0)
    (fun γ hγ => hγ.1) (fun γ hγ => hγ.1)
    (fun γ hγ => ⟨γ, TopQuad.joiningCurves_subset hsub₁ h₁₀ h₁₂ hγ, LRCurve.contains_refl γ⟩)
    (fun γ hγ => ⟨γ, TopQuad.joiningCurves_subset hsub₂ h₂₀ h₂₂ hγ, LRCurve.contains_refl γ⟩)
  rw [← thm4_1_modulus_eq_inv_extremalLength Q₁, ← thm4_1_modulus_eq_inv_extremalLength Q₂,
    ← thm4_1_modulus_eq_inv_extremalLength Q,
    ← ENNReal.ofReal_add (modulus_pos Q₁).le (modulus_pos Q₂).le,
    ENNReal.ofReal_le_ofReal_iff (modulus_pos Q).le] at h
  exact h

/-- The composition principle (Theorem 3.3 (i)) for countably many families of curves lying in
pairwise disjoint domains. -/
theorem composition_i_tsum {D : ℕ → Set ℂ} (hD : ∀ n, IsOpen (D n))
    (hdisj : Pairwise fun n m => Disjoint (D n) (D m)) {Γ : Set LRCurve}
    {Γn : ℕ → Set LRCurve} (hΓ : ∀ n, ∀ γ ∈ Γn n, γ.trace ⊆ D n)
    (hc : ∀ n, ∀ γ' ∈ Γn n, ∃ γ ∈ Γ, γ'.Contains γ) :
    ∑' n, (extremalLength (Γn n))⁻¹ ≤ (extremalLength Γ)⁻¹ := by
  have key : ∀ n, ∀ ρ ∈ {ρ ∈ densitiesP0 univ | ∀ γ ∈ Γ, 1 ≤ γ.rhoLength ρ},
      (extremalLength (Γn n))⁻¹ ≤ ∫⁻ z in D n, ρ z ^ 2 := by
    intro n ρ hρ
    obtain ⟨⟨hρm, -, hρtop⟩, hρ1⟩ := hρ
    have hA := rhoArea_indicator_univ ρ (hD n).measurableSet
    have hfin : rhoArea ((D n).indicator ρ) univ < ⊤ :=
      (rhoArea_indicator_le ρ (D n) univ).trans_lt hρtop
    have h1 : 1 ≤ ⨅ γ' ∈ Γn n, γ'.rhoLength ((D n).indicator ρ) ^ 2 := by
      refine le_iInf₂ fun γ' hγ' => ?_
      obtain ⟨γ, hγ, hcont⟩ := hc n γ' hγ'
      rw [LRCurve.rhoLength_congr fun z hz => indicator_of_mem (hΓ n γ' hγ' hz) ρ]
      exact one_le_pow_of_one_le' ((hρ1 γ hγ).trans (LRCurve.rhoLength_le_of_contains hcont ρ)) 2
    have hle := le_extremalLengthIn isOpen_univ univ_nonempty (Γn n)
      (hρm.indicator (hD n).measurableSet) hfin
    rw [← hA, ENNReal.inv_le_iff_inv_le]
    calc (rhoArea ((D n).indicator ρ) univ)⁻¹ = 1 / rhoArea ((D n).indicator ρ) univ :=
          (one_div _).symm
      _ ≤ _ := ENNReal.div_le_div_right h1 _
      _ ≤ extremalLength (Γn n) := hle
  rw [eq3_3 Γ, inv_inv]
  refine le_iInf₂ fun ρ hρ => ?_
  calc ∑' n, (extremalLength (Γn n))⁻¹ ≤ ∑' n, ∫⁻ z in D n, ρ z ^ 2 :=
        ENNReal.tsum_le_tsum fun n => key n ρ hρ
    _ = ∫⁻ z in ⋃ n, D n, ρ z ^ 2 :=
        (lintegral_iUnion (fun n => (hD n).measurableSet) hdisj _).symm
    _ ≤ rhoArea ρ univ := lintegral_mono_set (subset_univ _)

/-- (4.13): the subadditivity of the modulus for countably many quadrilaterals. -/
theorem eq4_13_modulus_tsum_le {Q : TopQuad} {Qn : ℕ → TopQuad} (hsub : ∀ n, (Qn n).dom ⊆ Q.dom)
    (hdisj : Pairwise fun n m => Disjoint (Qn n).dom (Qn m).dom)
    (h₀ : ∀ n, (Qn n).side 0 ⊆ Q.side 0) (h₂ : ∀ n, (Qn n).side 2 ⊆ Q.side 2) :
    ∑' n, ENNReal.ofReal (Qn n).modulus ≤ ENNReal.ofReal Q.modulus := by
  simp only [thm4_1_modulus_eq_inv_extremalLength]
  exact composition_i_tsum (fun n => (Qn n).isTopQuad.1.1) hdisj (fun n γ hγ => hγ.1)
    (fun n γ hγ => ⟨γ, TopQuad.joiningCurves_subset (hsub n) (h₀ n) (h₂ n) hγ,
      LRCurve.contains_refl γ⟩)

/-- The data of a rectangle: `M(Q) = a/b`, `m(Q) = ab`, `d₁ = b`, and `Q` is bounded. -/
theorem TopQuad.IsRectangle.exists_data {Q : TopQuad} (hQ : Q.IsRectangle) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ Bornology.IsBounded Q.dom ∧ Q.modulus = a / b ∧
      Q.area = ENNReal.ofReal a * ENNReal.ofReal b ∧ Q.sideDistance 0 = ENNReal.ofReal b := by
  obtain ⟨a, b, θ, c, ha, hb, hdom, hvert⟩ := hQ
  have hS := isStdConformalMap_of_isRectangle ha hb hdom hvert
  have hU : IsOpen Q.dom := Q.isTopQuad.1.1
  have hdom' : Q.dom = rigidHomeomorph θ c '' rectangle a b := hdom
  refine ⟨a, b, ha, hb, ?_, modulus_eq_of_equivRect Q ⟨_, hS⟩, ?_, ?_⟩
  · rw [hdom']
    exact ((isBounded_rectangle a b).isCompact_closure.image
      (rigidHomeomorph θ c).continuous).isBounded.subset (image_mono subset_closure)
  · show volume Q.dom = _
    rw [hdom', volume_image_rigidHomeomorph θ c (isOpen_rectangle a b), volume_rectangle]
  · have hderiv : ∀ z, ‖deriv (rigidHomeomorph θ c).symm z‖ₑ = 1 := fun z => by
      have h : HasDerivAt (fun w : ℂ => exp (((-θ : ℝ) : ℂ) * I) * (w - c))
          (exp (((-θ : ℝ) : ℂ) * I)) z := by
        simpa using ((hasDerivAt_id z).sub_const c).const_mul (exp (((-θ : ℝ) : ℂ) * I))
      rw [show ⇑(rigidHomeomorph θ c).symm = fun w : ℂ => exp (((-θ : ℝ) : ℂ) * I) * (w - c)
        from rfl, h.deriv, ← ofReal_norm, norm_exp_ofReal_mul_I, ENNReal.ofReal_one]
    have hind : (Q.dom.indicator fun z => (1 : ℂ → ℝ≥0∞) ((rigidHomeomorph θ c).symm z) *
        ‖deriv (rigidHomeomorph θ c).symm z‖ₑ) = Q.dom.indicator 1 := by
      funext z
      by_cases hz : z ∈ Q.dom <;> simp [hz, hderiv]
    have hlen : ∀ γ ∈ Q.joiningCurves 0, ∀ γ' : LRCurve,
        EqOn γ'.toFun ((rigidHomeomorph θ c).symm ∘ γ.toFun) (Ioo 0 1) → γ'.length = γ.length := by
      intro γ hγ γ' heq
      rw [LRCurve.length, LRCurve.rhoLength_image_conformal hU hS.2.2.1 hγ.1 heq 1, hind,
        LRCurve.length]
      exact LRCurve.rhoLength_congr fun z hz => indicator_of_mem (hγ.1 hz) (1 : ℂ → ℝ≥0∞)
    have himg := isCurveImage_joiningCurves hS
    rw [← iInf_length_rectJoiningCurves ha hb]
    unfold TopQuad.sideDistance
    apply le_antisymm
    · refine le_iInf₂ fun γ' hγ' => ?_
      obtain ⟨γ, hγ, heq⟩ := himg.2 γ' hγ'
      rw [hlen γ hγ γ' heq]
      exact iInf₂_le γ hγ
    · refine le_iInf₂ fun γ hγ => ?_
      obtain ⟨γ', hγ', heq⟩ := himg.1 γ hγ
      rw [← hlen γ hγ γ' heq]
      exact iInf₂_le γ' hγ'

/-- If `x₁ ≤ y₁`, `x₂ ≤ y₂` and `x₁ + x₂ = y₁ + y₂ < ∞`, then `x₁ = y₁`. -/
theorem ennreal_eq_of_add_eq_of_le {x₁ x₂ y₁ y₂ : ℝ≥0∞} (h₁ : x₁ ≤ y₁) (h₂ : x₂ ≤ y₂)
    (h : x₁ + x₂ = y₁ + y₂) (ht : y₁ + y₂ ≠ ⊤) : x₁ = y₁ := by
  refine le_antisymm h₁ (not_lt.1 fun hlt => ?_)
  have hx₂ : x₂ ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.1 ht).2 h₂
  exact ((ENNReal.add_lt_add_right hx₂ hlt).trans_le (add_le_add le_rfl h₂)).ne h

/-- One direction of **Theorem 4.7**: equality forces `Q₁`, `Q₂` to be rectangles filling `Q`
(Rengel's inequality `M(Qᵢ) ≤ m(Qᵢ)/b²` and Theorem 4.4). -/
theorem rect_of_subadditive_eq {Q Q₁ Q₂ : TopQuad} (hQ : Q.IsRectangle)
    (hsub₁ : Q₁.dom ⊆ Q.dom) (hsub₂ : Q₂.dom ⊆ Q.dom) (hdisj : Disjoint Q₁.dom Q₂.dom)
    (h₁₀ : Q₁.side 0 ⊆ Q.side 0) (h₁₂ : Q₁.side 2 ⊆ Q.side 2)
    (h₂₀ : Q₂.side 0 ⊆ Q.side 0) (h₂₂ : Q₂.side 2 ⊆ Q.side 2)
    (heq : Q₁.modulus + Q₂.modulus = Q.modulus) :
    Q₁.IsRectangle ∧ Q₂.IsRectangle ∧ closure Q.dom = closure Q₁.dom ∪ closure Q₂.dom := by
  obtain ⟨a, b, ha, hb, hbdd, hM, hm, hd⟩ := hQ.exists_data
  have hB0 : ENNReal.ofReal b ^ 2 ≠ 0 := pow_ne_zero 2 (ENNReal.ofReal_pos.2 hb).ne'
  have hBt : ENNReal.ofReal b ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hmt : Q.area ≠ ⊤ := by
    rw [hm]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hMQ : ENNReal.ofReal Q.modulus = Q.area / ENNReal.ofReal b ^ 2 := by
    rw [hM, hm, ← ENNReal.ofReal_pow hb.le, ← ENNReal.ofReal_mul ha.le,
      ← ENNReal.ofReal_div_of_pos (pow_pos hb 2)]
    congr 1
    rw [div_eq_div_iff hb.ne' (pow_pos hb 2).ne']
    ring
  have hpart : ∀ {Q' : TopQuad}, Q'.dom ⊆ Q.dom → Q'.side 0 ⊆ Q.side 0 → Q'.side 2 ⊆ Q.side 2 →
      ENNReal.ofReal Q'.modulus ≤ Q'.area / Q'.sideDistance 0 ^ 2 ∧
        Q'.area / Q'.sideDistance 0 ^ 2 ≤ Q'.area / ENNReal.ofReal b ^ 2 := by
    intro Q' hs h0 h2
    have harea : Q'.area ≤ Q.area := measure_mono hs
    have hdist : ENNReal.ofReal b ≤ Q'.sideDistance 0 := by
      rw [← hd]
      exact biInf_mono fun γ hγ => TopQuad.joiningCurves_subset hs h0 h2 hγ
    exact ⟨rengel_right Q' (harea.trans_lt (lt_top_iff_ne_top.2 hmt)),
      ENNReal.div_le_div_left (pow_le_pow_left' hdist 2) _⟩
  obtain ⟨hr₁, hq₁⟩ := hpart hsub₁ h₁₀ h₁₂
  obtain ⟨hr₂, hq₂⟩ := hpart hsub₂ h₂₀ h₂₂
  have hsumA : Q₁.area + Q₂.area ≤ Q.area := by
    show volume Q₁.dom + volume Q₂.dom ≤ volume Q.dom
    rw [← measure_union hdisj Q₂.isTopQuad.1.1.measurableSet]
    exact measure_mono (union_subset hsub₁ hsub₂)
  have heq' : ENNReal.ofReal Q₁.modulus + ENNReal.ofReal Q₂.modulus =
      ENNReal.ofReal Q.modulus := by
    rw [← ENNReal.ofReal_add (modulus_pos Q₁).le (modulus_pos Q₂).le, heq]
  have hchain1 : ENNReal.ofReal Q₁.modulus + ENNReal.ofReal Q₂.modulus ≤
      Q₁.area / ENNReal.ofReal b ^ 2 + Q₂.area / ENNReal.ofReal b ^ 2 :=
    add_le_add (hr₁.trans hq₁) (hr₂.trans hq₂)
  have hY : Q₁.area / ENNReal.ofReal b ^ 2 + Q₂.area / ENNReal.ofReal b ^ 2 =
      ENNReal.ofReal Q.modulus := by
    refine le_antisymm ?_ (by rw [← heq']; exact hchain1)
    rw [ENNReal.div_add_div_same, hMQ]
    exact ENNReal.div_le_div_right hsumA _
  have hYt : Q₁.area / ENNReal.ofReal b ^ 2 + Q₂.area / ENNReal.ofReal b ^ 2 ≠ ⊤ := by
    rw [hY]
    exact ENNReal.ofReal_ne_top
  have hX : ENNReal.ofReal Q₁.modulus + ENNReal.ofReal Q₂.modulus =
      Q₁.area / ENNReal.ofReal b ^ 2 + Q₂.area / ENNReal.ofReal b ^ 2 := by
    rw [heq', hY]
  have he₁ := ennreal_eq_of_add_eq_of_le (hr₁.trans hq₁) (hr₂.trans hq₂) hX hYt
  have he₂ := ennreal_eq_of_add_eq_of_le (hr₂.trans hq₂) (hr₁.trans hq₁)
    (by simpa only [add_comm] using hX) (by simpa only [add_comm] using hYt)
  refine ⟨(thm4_4_rengel_eq_right_iff Q₁ (hbdd.subset hsub₁)).1 (le_antisymm hr₁ (hq₁.trans he₁.ge)),
    (thm4_4_rengel_eq_right_iff Q₂ (hbdd.subset hsub₂)).1 (le_antisymm hr₂ (hq₂.trans he₂.ge)), ?_⟩
  -- the areas add up, so `Q ⊆ closure Q₁ ∪ closure Q₂`
  have hsumeq : Q₁.area + Q₂.area = Q.area := by
    have h := hY
    rw [ENNReal.div_add_div_same, hMQ] at h
    have h' := congrArg (· * ENNReal.ofReal b ^ 2) h
    simpa only [ENNReal.div_mul_cancel hB0 hBt] using h'
  have hUo : IsOpen (Q₁.dom ∪ Q₂.dom) := Q₁.isTopQuad.1.1.union Q₂.isTopQuad.1.1
  have hnull : volume (Q.dom \ closure (Q₁.dom ∪ Q₂.dom)) = 0 := by
    refine measure_mono_null (diff_subset_diff_right subset_closure) ?_
    rw [measure_diff (union_subset hsub₁ hsub₂) hUo.measurableSet.nullMeasurableSet
      (ne_top_of_le_ne_top hmt (measure_mono (union_subset hsub₁ hsub₂))),
      measure_union hdisj Q₂.isTopQuad.1.1.measurableSet]
    show Q.area - (Q₁.area + Q₂.area) = 0
    rw [hsumeq, tsub_self]
  have hempty : Q.dom \ closure (Q₁.dom ∪ Q₂.dom) = ∅ := by
    by_contra hne
    exact ((Q.isTopQuad.1.1.sdiff isClosed_closure).measure_pos volume
      (nonempty_iff_ne_empty.2 hne)).ne' hnull
  apply subset_antisymm
  · rw [← closure_union]
    exact closure_minimal (diff_eq_empty.1 hempty) isClosed_closure
  · exact union_subset (closure_mono hsub₁) (closure_mono hsub₂)

/-- The rectangle `R(0, a, a+bi, bi)` is convex. -/
theorem convex_rectangle (a b : ℝ) : Convex ℝ (rectangle a b) := by
  rw [rectangle_eq_reProdIm]
  exact ((convex_Ioo 0 a).linear_preimage reLm).inter ((convex_Ioo 0 b).linear_preimage imLm)

/-- The closure of a rectangle has the same area. -/
theorem volume_closure_rigid_rectangle (a b θ : ℝ) (c : ℂ) :
    volume (closure (rigidHomeomorph θ c '' rectangle a b)) =
      ENNReal.ofReal a * ENNReal.ofReal b := by
  have hs : volume (rigidHomeomorph θ c '' rectangle a b) = ENNReal.ofReal a * ENNReal.ofReal b := by
    rw [volume_image_rigidHomeomorph θ c (isOpen_rectangle a b), volume_rectangle]
  have hfr : volume (frontier (rigidHomeomorph θ c '' rectangle a b)) = 0 := by
    rw [← Homeomorph.image_frontier]
    exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      ((by fun_prop : Differentiable ℂ fun z => exp ((θ : ℂ) * I) * z + c).restrictScalars
        ℝ).differentiableOn
      ((convex_rectangle a b).addHaar_frontier volume)
  refine le_antisymm ?_ (by rw [← hs]; exact measure_mono subset_closure)
  rw [closure_eq_self_union_frontier]
  calc volume (rigidHomeomorph θ c '' rectangle a b ∪
        frontier (rigidHomeomorph θ c '' rectangle a b))
      ≤ volume (rigidHomeomorph θ c '' rectangle a b) +
          volume (frontier (rigidHomeomorph θ c '' rectangle a b)) := measure_union_le _ _
    _ = ENNReal.ofReal a * ENNReal.ofReal b := by rw [hs, hfr, add_zero]

/-- A rectangle `T₁(R(0,a₁,a₁+b₁i,b₁i))` whose horizontal sides lie on those of
`T(R(0,a,a+bi,bi))` has the same height. -/
theorem rigid_rect_aligned {a b a₁ b₁ θ θ₁ : ℝ} {c c₁ : ℂ} (hb : 0 < b) (ha₁ : 0 < a₁)
    (hb₁ : 0 < b₁)
    (h0 : rigidHomeomorph θ₁ c₁ '' (Icc 0 a₁ ×ℂ {0}) ⊆ rigidHomeomorph θ c '' (Icc 0 a ×ℂ {0}))
    (h2 : rigidHomeomorph θ₁ c₁ '' (Icc 0 a₁ ×ℂ {b₁}) ⊆ rigidHomeomorph θ c '' (Icc 0 a ×ℂ {b})) :
    b₁ = b := by
  obtain ⟨u, d, hu, hcomp⟩ : ∃ u d : ℂ, ‖u‖ = 1 ∧
      ∀ z, (rigidHomeomorph θ c).symm (rigidHomeomorph θ₁ c₁ z) = u * z + d := by
    refine ⟨exp (((-θ : ℝ) : ℂ) * I) * exp ((θ₁ : ℂ) * I), exp (((-θ : ℝ) : ℂ) * I) * (c₁ - c),
      ?_, fun z => ?_⟩
    · rw [norm_mul, norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I, one_mul]
    · show exp (((-θ : ℝ) : ℂ) * I) * (exp ((θ₁ : ℂ) * I) * z + c₁ - c) = _
      ring
  have hmem : ∀ {z : ℂ} {E : Set ℂ}, rigidHomeomorph θ₁ c₁ z ∈ rigidHomeomorph θ c '' E →
      u * z + d ∈ E := by
    intro z E hz
    obtain ⟨w, hw, hwz⟩ := hz
    rw [← hcomp, ← hwz, Homeomorph.symm_apply_apply]
    exact hw
  have hd0 := (hmem (h0 (mem_image_of_mem _
    (show (0 : ℂ) ∈ Icc 0 a₁ ×ℂ {0} by simp [mem_reProdIm, ha₁.le])))).2
  have hda := (hmem (h0 (mem_image_of_mem _
    (show ((a₁ : ℝ) : ℂ) ∈ Icc 0 a₁ ×ℂ {0} by simp [mem_reProdIm, ha₁.le])))).2
  have hdb := (hmem (h2 (mem_image_of_mem _
    (show (b₁ : ℂ) * I ∈ Icc 0 a₁ ×ℂ {b₁} by simp [mem_reProdIm, ha₁.le])))).2
  have e0 : d.im = 0 := by simpa using hd0
  have e1 : u.im * a₁ + d.im = 0 := by simpa using hda
  have e2 : u.re * b₁ + d.im = b := by simpa using hdb
  have him : u.im = 0 := (mul_eq_zero.1 (by linarith : u.im * a₁ = 0)).resolve_right ha₁.ne'
  have hnorm : u.re * u.re + u.im * u.im = 1 := by
    have h := Complex.sq_norm u
    rw [hu, Complex.normSq_apply] at h
    linarith
  have hpos : 0 < u.re := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hre : u.re = 1 := by nlinarith
  rw [hre, e0] at e2
  linarith

/-- The other direction of **Theorem 4.7**: two rectangles filling `Q` have additive moduli. -/
theorem subadditive_eq_of_rect {Q Q₁ Q₂ : TopQuad} (hQ : Q.IsRectangle)
    (hsub₁ : Q₁.dom ⊆ Q.dom) (hsub₂ : Q₂.dom ⊆ Q.dom) (hdisj : Disjoint Q₁.dom Q₂.dom)
    (h₁₀ : Q₁.side 0 ⊆ Q.side 0) (h₁₂ : Q₁.side 2 ⊆ Q.side 2)
    (h₂₀ : Q₂.side 0 ⊆ Q.side 0) (h₂₂ : Q₂.side 2 ⊆ Q.side 2)
    (h1 : Q₁.IsRectangle) (h2 : Q₂.IsRectangle)
    (hcl : closure Q.dom = closure Q₁.dom ∪ closure Q₂.dom) :
    Q₁.modulus + Q₂.modulus = Q.modulus := by
  obtain ⟨a, b, θ, c, ha, hb, hdom, hvert⟩ := hQ
  obtain ⟨a₁, b₁, θ₁, c₁, ha₁, hb₁, hdom₁, hvert₁⟩ := h1
  obtain ⟨a₂, b₂, θ₂, c₂, ha₂, hb₂, hdom₂, hvert₂⟩ := h2
  obtain ⟨hs0, hs2⟩ := side_of_isRectangle ha hb hdom hvert
  obtain ⟨hs0₁, hs2₁⟩ := side_of_isRectangle ha₁ hb₁ hdom₁ hvert₁
  obtain ⟨hs0₂, hs2₂⟩ := side_of_isRectangle ha₂ hb₂ hdom₂ hvert₂
  have hb₁b : b₁ = b := by
    rw [hs0₁, hs0] at h₁₀
    rw [hs2₁, hs2] at h₁₂
    exact rigid_rect_aligned hb ha₁ hb₁ ((image_subset_image_iff OnePoint.coe_injective).1 h₁₀)
      ((image_subset_image_iff OnePoint.coe_injective).1 h₁₂)
  have hb₂b : b₂ = b := by
    rw [hs0₂, hs0] at h₂₀
    rw [hs2₂, hs2] at h₂₂
    exact rigid_rect_aligned hb ha₂ hb₂ ((image_subset_image_iff OnePoint.coe_injective).1 h₂₀)
      ((image_subset_image_iff OnePoint.coe_injective).1 h₂₂)
  rw [modulus_eq_of_equivRect Q ⟨_, isStdConformalMap_of_isRectangle ha hb hdom hvert⟩,
    modulus_eq_of_equivRect Q₁ ⟨_, isStdConformalMap_of_isRectangle ha₁ hb₁ hdom₁ hvert₁⟩,
    modulus_eq_of_equivRect Q₂ ⟨_, isStdConformalMap_of_isRectangle ha₂ hb₂ hdom₂ hvert₂⟩]
  have hv : volume Q.dom = ENNReal.ofReal a * ENNReal.ofReal b := by
    rw [show Q.dom = rigidHomeomorph θ c '' rectangle a b from hdom,
      volume_image_rigidHomeomorph θ c (isOpen_rectangle a b), volume_rectangle]
  have hv₁ : volume Q₁.dom = ENNReal.ofReal a₁ * ENNReal.ofReal b₁ := by
    rw [show Q₁.dom = rigidHomeomorph θ₁ c₁ '' rectangle a₁ b₁ from hdom₁,
      volume_image_rigidHomeomorph θ₁ c₁ (isOpen_rectangle a₁ b₁), volume_rectangle]
  have hv₂ : volume Q₂.dom = ENNReal.ofReal a₂ * ENNReal.ofReal b₂ := by
    rw [show Q₂.dom = rigidHomeomorph θ₂ c₂ '' rectangle a₂ b₂ from hdom₂,
      volume_image_rigidHomeomorph θ₂ c₂ (isOpen_rectangle a₂ b₂), volume_rectangle]
  have hc₁ : volume (closure Q₁.dom) = ENNReal.ofReal a₁ * ENNReal.ofReal b₁ := by
    rw [show Q₁.dom = rigidHomeomorph θ₁ c₁ '' rectangle a₁ b₁ from hdom₁]
    exact volume_closure_rigid_rectangle a₁ b₁ θ₁ c₁
  have hc₂ : volume (closure Q₂.dom) = ENNReal.ofReal a₂ * ENNReal.ofReal b₂ := by
    rw [show Q₂.dom = rigidHomeomorph θ₂ c₂ '' rectangle a₂ b₂ from hdom₂]
    exact volume_closure_rigid_rectangle a₂ b₂ θ₂ c₂
  have hle1 : volume Q.dom ≤ volume (closure Q₁.dom) + volume (closure Q₂.dom) :=
    calc volume Q.dom ≤ volume (closure Q.dom) := measure_mono subset_closure
      _ = volume (closure Q₁.dom ∪ closure Q₂.dom) := by rw [hcl]
      _ ≤ _ := measure_union_le _ _
  have hle2 : volume Q₁.dom + volume Q₂.dom ≤ volume Q.dom := by
    rw [← measure_union hdisj Q₂.isTopQuad.1.1.measurableSet]
    exact measure_mono (union_subset hsub₁ hsub₂)
  rw [hc₁, hc₂, hv] at hle1
  rw [hv₁, hv₂, hv] at hle2
  have hreal : a₁ * b₁ + a₂ * b₂ = a * b := by
    have h := le_antisymm hle2 hle1
    rw [← ENNReal.ofReal_mul ha₁.le, ← ENNReal.ofReal_mul ha₂.le,
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul ha.le] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).1 h
  rw [hb₁b, hb₂b] at hreal ⊢
  rw [← add_div, div_left_inj' hb.ne']
  exact mul_right_cancel₀ hb.ne' (by rw [add_mul]; exact hreal)

/-- **Theorem 4.7**: for a rectangle `Q` and `Q₁`, `Q₂` as in Theorem 4.6,
`M(Q₁) + M(Q₂) = M(Q)` iff `Q₁` and `Q₂` are rectangles and `Q = Q₁ ∪ Q₂`. -/
theorem thm4_7_subadditive_eq_iff {Q Q₁ Q₂ : TopQuad} (hQ : Q.IsRectangle)
    (hsub₁ : Q₁.dom ⊆ Q.dom) (hsub₂ : Q₂.dom ⊆ Q.dom) (hdisj : Disjoint Q₁.dom Q₂.dom)
    (h₁₀ : Q₁.side 0 ⊆ Q.side 0) (h₁₂ : Q₁.side 2 ⊆ Q.side 2)
    (h₂₀ : Q₂.side 0 ⊆ Q.side 0) (h₂₂ : Q₂.side 2 ⊆ Q.side 2) :
    Q₁.modulus + Q₂.modulus = Q.modulus ↔
      Q₁.IsRectangle ∧ Q₂.IsRectangle ∧ closure Q.dom = closure Q₁.dom ∪ closure Q₂.dom :=
  ⟨rect_of_subadditive_eq hQ hsub₁ hsub₂ hdisj h₁₀ h₁₂ h₂₀ h₂₂,
    fun ⟨h1, h2, hcl⟩ => subadditive_eq_of_rect hQ hsub₁ hsub₂ hdisj h₁₀ h₁₂ h₂₀ h₂₂ h1 h2 hcl⟩

/-- The key estimate behind Theorem 4.8.  Let `f` be a conformal map of `Q` onto the rectangle
`R(0, a, a+bi, bi)` with boundary extension `F`, and let `Q₁ ⊆ Q` be a quadrilateral whose first
side is carried by `F` into `{Im w ≤ η}` and whose third side into `{Im w ≥ b - η}`.  Then
`M(Q₁) ≤ ab/(b - 2η)²`: the pull-back of the constant density `1/(b - 2η)` on `R` is admissible
for the curves joining the first pair of opposite sides of `Q₁`, and its area is at most
`ab/(b - 2η)²`. -/
theorem modulus_le_of_sides_near {Q Q₁ : TopQuad} {a b η : ℝ} {f : ℂ → ℂ}
    {F : ExtPlane → ExtPlane} (ha : 0 < a) (hb : 0 < b)
    (hconf : IsConformalOnto f Q.dom (rectangle a b))
    (hF : IsHomeoExtension f Q.dom (rectangle a b) F) (hsub : Q₁.dom ⊆ Q.dom)
    (hηb : 2 * η < b)
    (h0 : ∀ p ∈ Q₁.side 0, ∀ w : ℂ, F p = (w : ExtPlane) → w.im ≤ η)
    (h2 : ∀ p ∈ Q₁.side 2, ∀ w : ℂ, F p = (w : ExtPlane) → b - η ≤ w.im) :
    ENNReal.ofReal Q₁.modulus ≤ ENNReal.ofReal (a * b) / ENNReal.ofReal ((b - 2 * η) ^ 2) := by
  have hQo : IsOpen Q.dom := Q.isTopQuad.1.1
  have hb2 : 0 < b - 2 * η := by linarith
  have hclsub : closure (toExt Q₁.dom) ⊆ closure (toExt Q.dom) :=
    closure_mono (image_mono hsub)
  -- the constant density `1/(b - 2η)` on the rectangle, and its pull-back to `Q`
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (b - 2 * η)) with hc_def
  have hcne : c ≠ ⊤ := by simp [hc_def]
  set ρ' : ℂ → ℝ≥0∞ := (rectangle a b).indicator (fun _ => c) with hρ'_def
  have hρ'm : Measurable ρ' := measurable_const.indicator (isOpen_rectangle a b).measurableSet
  set ρ : ℂ → ℝ≥0∞ := Q.dom.indicator (fun z => ρ' (f z) * ‖deriv f z‖ₑ) with hρ_def
  have hρm : Measurable ρ := measurable_pullback_density hQo hconf.1.continuousOn hρ'm
  -- every curve joining the first pair of opposite sides of `Q₁` has `ρ`-length at least `1`
  have hadm : ∀ γ ∈ Q₁.joiningCurves 0, 1 ≤ γ.rhoLength ρ := by
    rintro γ ⟨htr, ⟨p, hp, hpγ⟩, ⟨q, hq, hqγ⟩⟩
    have hmaps : MapsTo γ.toFun (Ioo 0 1) Q.dom := fun t ht =>
      hsub (htr (mem_image_of_mem _ ht))
    have htrQ : γ.trace ⊆ Q.dom := fun _ hz => by
      obtain ⟨t, ht, rfl⟩ := hz
      exact hmaps ht
    set γ' : LRCurve := ⟨f ∘ γ.toFun, locallyLipschitzOn_comp_of_differentiableOn hQo hconf.1
      isOpen_Ioo γ.locallyLipschitzOn hmaps⟩ with hγ'_def
    have hmapsR : MapsTo γ'.toFun (Ioo 0 1) (rectangle a b) := fun t ht => by
      show f (γ.toFun t) ∈ rectangle a b
      rw [← hconf.2.2]
      exact mem_image_of_mem f (hmaps ht)
    have hfin : ∀ p : ExtPlane, p ∈ closure (toExt Q.dom) → ∃ w : ℂ, F p = (w : ExtPlane) := by
      intro p hp
      have hmem : F p ∈ closure (toExt (rectangle a b)) := hF.2.2.2 ▸ mem_image_of_mem F hp
      rw [closure_toExt_of_isBounded (isBounded_rectangle a b)] at hmem
      obtain ⟨w, -, hw⟩ := hmem
      exact ⟨w, hw.symm⟩
    -- the boundary extension carries the endpoints of `γ` to those of the image curve
    have hlimit : ∀ {l : Filter ℝ} {p : ExtPlane}, Ioo (0 : ℝ) 1 ∈ l →
        p ∈ closure (toExt Q.dom) →
        Tendsto (fun t => ((γ.toFun t : ℂ) : ExtPlane)) l (𝓝 p) →
        ∀ w : ℂ, F p = (w : ExtPlane) → Tendsto γ'.toFun l (𝓝 w) := by
      intro l p hl hpC hpl w hw
      have h1 : Tendsto (fun t => F ((γ.toFun t : ℂ) : ExtPlane)) l (𝓝 (F p)) := by
        refine (hF.2.1 p hpC).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hpl, ?_⟩)
        filter_upwards [hl] with t ht
        exact subset_closure (mem_image_of_mem _ (hmaps ht))
      have h2' : Tendsto (fun t => ((γ'.toFun t : ℂ) : ExtPlane)) l (𝓝 ((w : ℂ) : ExtPlane)) := by
        rw [← hw]
        refine h1.congr' ?_
        filter_upwards [hl] with t ht
        exact hF.1 _ (hmaps ht)
      exact OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.2 h2'
    have hpC : p ∈ closure (toExt Q.dom) := hclsub (frontier_subset_closure hp.1)
    have hqC : q ∈ closure (toExt Q.dom) := hclsub (frontier_subset_closure hq.1)
    obtain ⟨wp, hwp⟩ := hfin p hpC
    obtain ⟨wq, hwq⟩ := hfin q hqC
    have hlen : ENNReal.ofReal (b - 2 * η) ≤ γ'.length := by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_)
        (LRCurve.ofReal_im_sub_le_length
          (hlimit (Ioo_mem_nhdsGT zero_lt_one) hpC hpγ wp hwp)
          (hlimit (Ioo_mem_nhdsLT zero_lt_one) hqC hqγ wq hwq))
      have e0 := h0 p hp wp hwp
      have e2 := h2 q (by simpa using hq) wq hwq
      linarith
    have hrho : γ'.rhoLength ρ' = γ.rhoLength ρ :=
      LRCurve.rhoLength_image_conformal hQo hconf htrQ (fun _ _ => rfl) ρ'
    have hconst : γ'.rhoLength ρ' = c * γ'.length := by
      have h1 : γ'.rhoLength ρ' = ∫⁻ t in Ioo (0 : ℝ) 1, c * ‖deriv γ'.toFun t‖ₑ := by
        unfold LRCurve.rhoLength
        refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
        rw [hρ'_def, indicator_of_mem (hmapsR ht)]
      have h2'' : γ'.length = ∫⁻ t in Ioo (0 : ℝ) 1, ‖deriv γ'.toFun t‖ₑ := by
        simp [LRCurve.length, LRCurve.rhoLength]
      rw [h1, h2'', lintegral_const_mul' _ _ hcne]
    rw [← hrho, hconst]
    calc (1 : ℝ≥0∞) = c * ENNReal.ofReal (b - 2 * η) := by
          rw [hc_def, ← ENNReal.ofReal_mul (by positivity), one_div,
            inv_mul_cancel₀ hb2.ne', ENNReal.ofReal_one]
      _ ≤ c * γ'.length := by gcongr
  -- the area of the pull-back density is at most `ab/(b - 2η)²`
  have hval : rhoArea ρ' (rectangle a b) = c ^ 2 * (ENNReal.ofReal a * ENNReal.ofReal b) := by
    unfold rhoArea
    rw [setLIntegral_congr_fun (isOpen_rectangle a b).measurableSet
      (fun z hz => by rw [hρ'_def, indicator_of_mem hz]), setLIntegral_const, volume_rectangle]
  have hc2 : c ^ 2 * (ENNReal.ofReal a * ENNReal.ofReal b) =
      ENNReal.ofReal (a * b) / ENNReal.ofReal ((b - 2 * η) ^ 2) := by
    rw [hc_def, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul ha.le,
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_div_of_pos (show (0 : ℝ) < (b - 2 * η) ^ 2 by positivity)]
    congr 1
    field_simp
  refine (eq4_6_modulus_le_rhoArea Q₁ hρm hadm).trans ?_
  calc rhoArea ρ Q₁.dom ≤ rhoArea ρ Q.dom := lintegral_mono_set hsub
    _ = rhoArea ρ' (rectangle a b) := rhoArea_pullback hQo hconf ρ'
    _ = c ^ 2 * (ENNReal.ofReal a * ENNReal.ofReal b) := hval
    _ = ENNReal.ofReal (a * b) / ENNReal.ofReal ((b - 2 * η) ^ 2) := hc2

/-! ### Rotation -/

/-- Rotating a quadrilateral shifts its sides: `Q.rotate.side i = Q.side (i + 1)`. -/
theorem TopQuad.rotate_side (Q : TopQuad) (i : Fin 4) : Q.rotate.side i = Q.side (i + 1) := by
  have h : i + 2 + 1 = i + 1 + 2 := add_right_comm i 2 1
  unfold TopQuad.side
  simp only [TopQuad.rotate, h]

/-- Rotating a quadrilateral shifts its sides, as subsets of `ℂ`. -/
theorem TopQuad.rotate_sideC (Q : TopQuad) (i : Fin 4) : Q.rotate.sideC i = Q.sideC (i + 1) := by
  unfold TopQuad.sideC
  rw [Q.rotate_side]

/-- "Tends from the inside" is inherited by the rotated quadrilaterals. -/
theorem TopQuad.TendsFromInside.rotate {Qn : ℕ → TopQuad} {Q : TopQuad}
    (h : TopQuad.TendsFromInside Qn Q) :
    TopQuad.TendsFromInside (fun n => (Qn n).rotate) Q.rotate := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun i => h2 (i + 1), h3, fun i ε hε => ?_⟩
  filter_upwards [h4 (i + 1) ε hε] with n hn z hz
  rw [TopQuad.rotate_sideC] at hz ⊢
  exact hn z hz

/-- If `Q` is conformally the rectangle `R(0,a,a+bi,bi)`, then `Q(z₂,z₃,z₄,z₁)` is conformally
`R(0,b,b+ai,ai)` (compose with the rigid motion `w ↦ -i w + a i`; cf. Theorem 1.2). -/
theorem TopQuad.EquivRect.rotate {Q : TopQuad} {a b : ℝ} (h : Q.EquivRect a b) :
    Q.rotate.EquivRect b a := by
  obtain ⟨f, ha, hb, hf, F, hF, hv⟩ := h
  refine ⟨(fun w : ℂ => -I * w + (a : ℂ) * I) ∘ f, hb, ha, rectangle_rotation_conformal.comp hf,
    (mobiusHomeomorph (-I) ((a : ℂ) * I) 0 1 (rotation_det a)) ∘ F,
    hF.comp_homeomorph hf.mapsTo _ (fun w _ => ?_) rectangle_rotation_image, fun i => ?_⟩
  · rw [mobiusHomeomorph_apply, rotation_mobiusExt_coe]
  · show mobiusHomeomorph (-I) ((a : ℂ) * I) 0 1 (rotation_det a) (F (Q.vert (i + 1))) =
      rectVert b a i
    rw [hv (i + 1), mobiusHomeomorph_apply, rectVert_rotation]

/-! ### From side convergence to the hypotheses of `modulus_le_of_sides_near` -/

/-- The points of `closure Q.dom` that the boundary extension `F` sends outside the open set `U`
form a compact set, disjoint from the closure of the side `i` as soon as `F` carries that side
into a compact `E ⊆ U`.  Hence they lie at a positive distance `δ` from the side, and every point
of `closure Q.dom` within `δ` of the side is carried into `U`. -/
theorem exists_dist_of_side_image {Q : TopQuad} {a b : ℝ} {F : ExtPlane → ExtPlane} {i : Fin 4}
    {E U : Set ℂ} (hbdd : Bornology.IsBounded Q.dom)
    (hFc : ContinuousOn F (closure (toExt Q.dom)))
    (hFim : F '' closure (toExt Q.dom) = closure (toExt (rectangle a b)))
    (hside : F '' Q.side i = toExt E) (hEc : IsCompact E) (hU : IsOpen U) (hEU : E ⊆ U) :
    ∃ δ > 0, ∀ z : ℂ, (z : ExtPlane) ∈ closure (toExt Q.dom) →
      infDist z (Q.sideC i) < δ → ∀ w : ℂ, F (z : ExtPlane) = (w : ExtPlane) → w ∈ U := by
  have hQo : IsOpen Q.dom := Q.isTopQuad.1.1
  have hKe : closure (toExt Q.dom) = toExt (closure Q.dom) := closure_toExt_of_isBounded hbdd
  have hK : IsCompact (closure Q.dom) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hbdd.closure
  have hmaps : MapsTo (fun z : ℂ => (z : ExtPlane)) (closure Q.dom) (closure (toExt Q.dom)) :=
    fun z hz => by rw [hKe]; exact mem_image_of_mem _ hz
  have hg : ContinuousOn (fun z : ℂ => F (z : ExtPlane)) (closure Q.dom) :=
    hFc.comp OnePoint.continuous_coe.continuousOn hmaps
  -- the side, as a subset of `ℂ`, sits inside `closure Q.dom` and is nonempty
  have hsideEq : Q.side i = toExt (Q.sideC i) := by
    have hfr : frontier (toExt Q.dom) = toExt (frontier Q.dom) :=
      frontier_toExt_of_isBounded hbdd hQo
    ext p
    constructor
    · intro hp
      have : p ∈ toExt (frontier Q.dom) := hfr ▸ hp.1
      obtain ⟨z, -, rfl⟩ := this
      exact ⟨z, hp, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact hz
  have hsubK : Q.sideC i ⊆ closure Q.dom := by
    intro z hz
    have : (z : ExtPlane) ∈ closure (toExt Q.dom) := frontier_subset_closure hz.1
    rw [hKe] at this
    obtain ⟨y, hy, hyz⟩ := this
    rwa [OnePoint.coe_injective hyz] at hy
  have hne : (Q.sideC i).Nonempty := by
    have hv : Q.vert i ∈ Q.side i := ⟨Q.isTopQuad.2.1 i, Or.inl rfl⟩
    rw [hsideEq] at hv
    obtain ⟨z, hz, -⟩ := hv
    exact ⟨z, hz⟩
  -- the "bad" set is compact and misses the closure of the side
  set T : Set ExtPlane := closure (toExt (rectangle a b)) \ toExt U with hT_def
  have hTc : IsClosed T := isClosed_closure.sdiff (OnePoint.isOpen_image_coe.2 hU)
  set B : Set ℂ := closure Q.dom ∩ (fun z : ℂ => F (z : ExtPlane)) ⁻¹' T with hB_def
  have hBc : IsCompact B := hK.of_isClosed_subset
    (hg.preimage_isClosed_of_isClosed isClosed_closure hTc) inter_subset_left
  have hdisj : ∀ z ∈ B, 0 < infDist z (Q.sideC i) := by
    intro z hz
    refine (Metric.infDist_pos_iff_notMem_closure hne).mp ?_
    intro hzc
    have hsubC : closure (Q.sideC i) ⊆ closure Q.dom := closure_minimal hsubK isClosed_closure
    have himg : (fun z : ℂ => F (z : ExtPlane)) '' closure (Q.sideC i) ⊆ toExt E := by
      refine ((hg.mono hsubC).image_closure).trans ?_
      have : (fun z : ℂ => F (z : ExtPlane)) '' Q.sideC i = toExt E := by
        rw [← hside, hsideEq, toExt, ← image_comp]
        rfl
      rw [this]
      exact (hEc.image OnePoint.continuous_coe).isClosed.closure_subset
    have hmem := himg (mem_image_of_mem _ hzc)
    obtain ⟨w, hwE, hw⟩ := hmem
    exact hz.2.2 ⟨w, hEU hwE, hw⟩
  -- so the bad set is at a positive distance from the side
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, ∀ z ∈ B, δ ≤ infDist z (Q.sideC i) := by
    rcases B.eq_empty_or_nonempty with hBe | hBne
    · exact ⟨1, one_pos, fun z hz => absurd hz (by rw [hBe]; exact notMem_empty z)⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := hBc.exists_isMinOn hBne
        (Metric.continuous_infDist_pt _).continuousOn
      exact ⟨infDist z₀ (Q.sideC i), hdisj z₀ hz₀, fun z hz => hmin hz⟩
  refine ⟨δ, hδ0, fun z hzC hzd w hw => ?_⟩
  have hzK : z ∈ closure Q.dom := by
    rw [hKe] at hzC
    obtain ⟨y, hy, hyz⟩ := hzC
    rwa [OnePoint.coe_injective hyz] at hy
  have hnotB : z ∉ B := fun hzB => absurd (hδ z hzB) (not_le.2 hzd)
  have hnotT : F (z : ExtPlane) ∉ T := fun hTm => hnotB ⟨hzK, hTm⟩
  have hinR : F (z : ExtPlane) ∈ closure (toExt (rectangle a b)) :=
    hFim ▸ mem_image_of_mem F hzC
  have : F (z : ExtPlane) ∈ toExt U := by
    by_contra hc
    exact hnotT ⟨hinR, hc⟩
  obtain ⟨w', hw'U, hw'⟩ := this
  rwa [← OnePoint.coe_injective (hw'.trans hw)]

/-- The upper half of Theorem 4.8: if `Qₙ` tends to `Q` from the inside and `Q` is conformally
the rectangle `R(0,a,a+bi,bi)`, then eventually `M(Qₙ) ≤ ab/(b - 2η)²`. -/
theorem eventually_modulus_le {Q : TopQuad} {Qn : ℕ → TopQuad} {a b : ℝ}
    (hbdd : Bornology.IsBounded Q.dom) (hE : Q.EquivRect a b)
    (h : TopQuad.TendsFromInside Qn Q) {η : ℝ} (hη : 0 < η) (hηb : 2 * η < b) :
    ∀ᶠ n in atTop, (Qn n).modulus ≤ a * b / (b - 2 * η) ^ 2 := by
  obtain ⟨f, ha, hb, hconf, F, hF, hFv⟩ := hE
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hb2 : 0 < b - 2 * η := by linarith
  have hV : IsOpen (rectangle a b) := isOpen_rectangle a b
  -- `F` carries the first and third sides onto the bottom and top edges of the rectangle
  have hside0 : F '' Q.side 0 = toExt (Icc 0 a ×ℂ {0}) := by
    rw [TopQuad.image_side hV hconf hF 0, hFv, hFv, hFv]
    exact boundaryArc_frontier_toExt_rectangle_bottom ha hb
  have hside2 : F '' Q.side 2 = toExt (Icc 0 a ×ℂ {b}) := by
    rw [TopQuad.image_side hV hconf hF 2, hFv, hFv, hFv]
    exact boundaryArc_frontier_toExt_rectangle_top ha hb
  have hcpt : ∀ c : ℝ, IsCompact (Icc 0 a ×ℂ ({c} : Set ℝ)) := fun c =>
    Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_singleton)
      ((Metric.isBounded_Icc 0 a).reProdIm (Bornology.isBounded_singleton))
  -- the two separation radii
  obtain ⟨δ0, hδ0, hδ0'⟩ := exists_dist_of_side_image (i := 0) (E := Icc 0 a ×ℂ ({0} : Set ℝ))
    (U := {w : ℂ | w.im < η}) hbdd hF.2.1 hF.2.2.2 hside0 (hcpt 0)
    (isOpen_lt Complex.continuous_im continuous_const)
    (fun w hw => by simp only [mem_reProdIm, mem_singleton_iff] at hw; simp [hw.2, hη])
  obtain ⟨δ2, hδ2, hδ2'⟩ := exists_dist_of_side_image (i := 2) (E := Icc 0 a ×ℂ ({b} : Set ℝ))
    (U := {w : ℂ | b - η < w.im}) hbdd hF.2.1 hF.2.2.2 hside2 (hcpt b)
    (isOpen_lt continuous_const Complex.continuous_im)
    (fun w hw => by
      simp only [mem_reProdIm, mem_singleton_iff] at hw
      simp only [mem_setOf_eq, hw.2]
      linarith)
  filter_upwards [h4 0 δ0 hδ0, h4 2 δ2 hδ2] with n hn0 hn2
  have hbn : Bornology.IsBounded (Qn n).dom := hbdd.subset (h1 n)
  have hfr : frontier (toExt (Qn n).dom) = toExt (frontier (Qn n).dom) :=
    frontier_toExt_of_isBounded hbn (Qn n).isTopQuad.1.1
  have hkey := modulus_le_of_sides_near ha hb hconf hF (h1 n) hηb
    (fun p hp w hw => by
      obtain ⟨z, -, rfl⟩ : p ∈ toExt (frontier (Qn n).dom) := hfr ▸ hp.1
      exact le_of_lt (hδ0' z (closure_mono (image_mono (h1 n)) (frontier_subset_closure hp.1))
        (hn0 z hp) w hw))
    (fun p hp w hw => by
      obtain ⟨z, -, rfl⟩ : p ∈ toExt (frontier (Qn n).dom) := hfr ▸ hp.1
      exact le_of_lt (hδ2' z (closure_mono (image_mono (h1 n)) (frontier_subset_closure hp.1))
        (hn2 z hp) w hw))
  rw [← ENNReal.ofReal_div_of_pos (by positivity)] at hkey
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hkey

/-- **Theorem 4.8** (模的连续性): if the quadrilaterals `Qₙ` tend to the bounded quadrilateral
`Q` from the inside, then `M(Qₙ) → M(Q)`.

**Correction.**  The book's definition of "tends to `Q` from the inside" asks only that
`Qₙ ⊆ Q`, that the vertices converge, and that `∂Qₙ` lie in an `ε`-neighbourhood of `∂Q`.  With
that definition the theorem is false.  Let `Q` be the unit square with its four corners as
vertices, and let `Qₙ` be the collar `{z ∈ Q : d(z, ∂Q) < 1/n}` cut along the segment from `1/2`
to `1/2 + i/n`, again with the four corners as vertices: they lie on `∂Qₙ` in the correct cyclic
order, `Qₙ ⊆ Q`, and every point of `∂Qₙ` is within `1/n` of `∂Q`, so all of the book's
hypotheses hold.  But `Qₙ` is a thin cut collar.  Its first side is the long arc that runs
through the cut and all the way round the inner boundary, so it comes within `1/n` of the third
side; while the second and fourth sides are the right and left edges of the square, which the
cut forces apart by a distance close to `1`.  Rengel's inequality then gives
`M(Qₙ) ≥ (1 - 2/n)² / (4/n - 4/n²) → ∞`, and not `M(Q) = 1`.

`TendsFromInside` therefore also requires each side of `Qₙ` to converge to the corresponding
side of `Q` — which is what the book's Figure 1.4.3 depicts, and what the book's own proof uses
when it reads off `d₁ ≥ b - 2η` and `d₂ ≥ a - 2η` from the `η`-frame.

The proof follows the book.  `modulus_le_of_sides_near`, applied to `Qₙ` and to `Qₙ.rotate`,
bounds `M(Qₙ)` between `(a - 2η)²/ab` and `ab/(b - 2η)²`; letting `η → 0` squeezes it to
`a/b = M(Q)`. -/
theorem thm4_8_modulus_continuous {Q : TopQuad} (hbdd : Bornology.IsBounded Q.dom)
    {Qn : ℕ → TopQuad} (h : TopQuad.TendsFromInside Qn Q) :
    Tendsto (fun n => (Qn n).modulus) atTop (𝓝 Q.modulus) := by
  obtain ⟨a, b, hE⟩ := thm1_1_exists_rectangle Q
  have ha : 0 < a := by obtain ⟨g, ha, -⟩ := hE; exact ha
  have hb : 0 < b := by obtain ⟨g, -, hb, -⟩ := hE; exact hb
  have hMQ : Q.modulus = a / b := modulus_eq_of_equivRect Q hE
  have hErot : Q.rotate.EquivRect b a := hE.rotate
  have hbddrot : Bornology.IsBounded Q.rotate.dom := hbdd
  rw [hMQ, Metric.tendsto_atTop]
  intro ε hε
  -- choose `η` so small that both Rengel bounds lie within `ε` of `a/b`
  have hcu : ContinuousAt (fun t : ℝ => a * b / (b - 2 * t) ^ 2) 0 := by
    refine ContinuousAt.div continuousAt_const (by fun_prop) ?_
    simp only [mul_zero, sub_zero]
    positivity
  have hcv : ContinuousAt (fun t : ℝ => (a - 2 * t) ^ 2 / (a * b)) 0 :=
    ContinuousAt.div (by fun_prop) continuousAt_const (by positivity)
  have hu0 : a * b / (b - 2 * (0 : ℝ)) ^ 2 = a / b := by
    rw [mul_zero, sub_zero]
    field_simp
  have hv0 : (a - 2 * (0 : ℝ)) ^ 2 / (a * b) = a / b := by
    rw [mul_zero, sub_zero]
    field_simp
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), a * b / (b - 2 * t) ^ 2 < a / b + ε := by
    refine (hcu.tendsto.eventually_lt_const ?_).filter_mono nhdsWithin_le_nhds
    show a * b / (b - 2 * (0 : ℝ)) ^ 2 < a / b + ε
    rw [hu0]
    linarith
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), a / b - ε < (a - 2 * t) ^ 2 / (a * b) := by
    refine (hcv.tendsto.eventually_const_lt ?_).filter_mono nhdsWithin_le_nhds
    show a / b - ε < (a - 2 * (0 : ℝ)) ^ 2 / (a * b)
    rw [hv0]
    linarith
  have hev3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ 2 * t < a ∧ 2 * t < b := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min a b / 2 by positivity)] with t ht
    exact ⟨ht.1, lt_of_lt_of_le (by linarith [ht.2]) (min_le_left a b),
      lt_of_lt_of_le (by linarith [ht.2]) (min_le_right a b)⟩
  obtain ⟨η, ⟨hu, hv⟩, hη0, hηa, hηb⟩ := ((hev1.and hev2).and hev3).exists
  -- the two Rengel bounds
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (eventually_modulus_le hbdd hE h hη0 hηb)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 (eventually_modulus_le hbddrot hErot h.rotate hη0 hηa)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have h1 := hN1 n ((le_max_left _ _).trans hn)
  have h2 := hN2 n ((le_max_right _ _).trans hn)
  have hlowb : (a - 2 * η) ^ 2 / (a * b) ≤ (Qn n).modulus := by
    rw [thm1_2_modulus_rotate (Qn n)]
    calc (a - 2 * η) ^ 2 / (a * b) = 1 / (b * a / (a - 2 * η) ^ 2) := by
          rw [one_div_div, mul_comm b a]
      _ ≤ 1 / (Qn n).rotate.modulus := one_div_le_one_div_of_le (modulus_pos _) h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ## Doubly connected domains -/

/-- A closed rectifiable curve in `B` separating the two components of `ℂ̄ ∖ B`: every
curve joining them meets `γ`, i.e. they lie in different components of `ℂ̄ ∖ γ`. -/
def IsSeparatingCurve (B : Set ℂ) (γ : LRCurve) : Prop :=
  γ.IsClosedCurve ∧ γ.closedTrace ⊆ B ∧
    ∀ x ∈ (toExt B)ᶜ, ∀ y ∈ (toExt B)ᶜ,
      connectedComponentIn (toExt B)ᶜ x ≠ connectedComponentIn (toExt B)ᶜ y →
        connectedComponentIn (toExt γ.closedTrace)ᶜ x ≠ connectedComponentIn (toExt γ.closedTrace)ᶜ y

/-- The family of closed curves in `B` separating the two components of `ℂ̄ ∖ B`. -/
def separatingCurves (B : Set ℂ) : Set LRCurve := {γ | IsSeparatingCurve B γ}

/-! ### The annulus: area of the extremal density and the concentric circles -/

/-- `∬_{r₁<|z|<r₂} dx dy / |z|² = 2π ln(r₂/r₁)` (the `a = 2` case excluded by the §11 radial lemmas). -/
theorem lintegral_annulus_inv_normSq {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    ∫⁻ z in annulus r₁ r₂, ENNReal.ofReal (1 / ‖z‖ ^ 2) =
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (r₂ / r₁)) := by
  have key : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • (annulus r₁ r₂).indicator (fun w : ℂ => ENNReal.ofReal (1 / ‖w‖ ^ 2))
          (Complex.polarCoord.symm p)
        = (Ioo r₁ r₂).indicator (fun r : ℝ => ENNReal.ofReal (r⁻¹)) p.1 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr0 : (0 : ℝ) < r := hr
    have hnorm : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm]
      exact abs_of_pos hr0
    by_cases hmem : r ∈ Ioo r₁ r₂
    · have hmem' : Complex.polarCoord.symm (r, θ) ∈ annulus r₁ r₂ := by
        show r₁ < ‖Complex.polarCoord.symm (r, θ)‖ ∧ ‖Complex.polarCoord.symm (r, θ)‖ < r₂
        rw [hnorm]; exact hmem
      rw [Set.indicator_of_mem hmem', Set.indicator_of_mem hmem, smul_eq_mul, hnorm,
        ← ENNReal.ofReal_mul hr0.le]
      congr 1
      field_simp
    · have hmem' : Complex.polarCoord.symm (r, θ) ∉ annulus r₁ r₂ := by
        show ¬ (r₁ < ‖Complex.polarCoord.symm (r, θ)‖ ∧ ‖Complex.polarCoord.symm (r, θ)‖ < r₂)
        rw [hnorm]; exact hmem
      rw [Set.indicator_of_notMem hmem', Set.indicator_of_notMem hmem, smul_zero]
  have hle : r₁ ≤ r₂ := h₂.le
  have hint : IntegrableOn (fun r : ℝ => r⁻¹) (Ioo r₁ r₂) := by
    have h := intervalIntegral.intervalIntegrable_inv (μ := volume) (f := fun x : ℝ => x)
      (fun x hx => by
        rw [uIcc_of_le hle] at hx
        exact (h₁.trans_le hx.1).ne') continuousOn_id
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).1 h
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo r₁ r₂)] fun r : ℝ => r⁻¹ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with r hr
    exact inv_nonneg.2 (h₁.trans hr.1).le
  have hval : ∫ r in Ioo r₁ r₂, r⁻¹ = Real.log (r₂ / r₁) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle,
      integral_inv_of_pos h₁ (h₁.trans h₂)]
  have hmeas : AEMeasurable (fun x : ℝ × ℝ =>
      (Ioo r₁ r₂).indicator (fun r : ℝ => ENNReal.ofReal (r⁻¹)) x.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) :=
    (((measurable_inv.ennreal_ofReal).indicator measurableSet_Ioo).comp measurable_fst).aemeasurable
  rw [← lintegral_indicator (isOpen_annulus r₁ r₂).measurableSet,
    ← Complex.lintegral_comp_polarCoord_symm,
    setLIntegral_congr_fun polarCoord.open_target.measurableSet key,
    show (polarCoord.target : Set (ℝ × ℝ)) = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl,
    Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict, lintegral_prod _ hmeas]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
  rw [show (π : ℝ) - -π = 2 * π from by ring]
  have hsub : Ioo r₁ r₂ ∩ Ioi 0 = Ioo r₁ r₂ :=
    Set.inter_eq_self_of_subset_left fun x hx => h₁.trans hx.1
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm,
    setLIntegral_indicator measurableSet_Ioo, hsub,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]


/-- The area of the extremal density `1/(2π|z|)` of an annulus: `m_{ρ₀}(A) = ln(r₂/r₁)/(2π)`. -/
theorem rhoArea_annulus_density {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    rhoArea ((annulus r₁ r₂).indicator fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖)))
      (annulus r₁ r₂) = ENNReal.ofReal (Real.log (r₂ / r₁) / (2 * π)) := by
  unfold rhoArea
  have hcongr : ∀ z ∈ annulus r₁ r₂,
      ((annulus r₁ r₂).indicator (fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖))) z) ^ 2
        = ENNReal.ofReal (1 / (4 * π ^ 2)) * ENNReal.ofReal (1 / ‖z‖ ^ 2) := by
    intro z hz
    have hzpos : 0 < ‖z‖ := h₁.trans hz.1
    rw [Set.indicator_of_mem hz,
      ← ENNReal.ofReal_pow (show (0 : ℝ) ≤ 1 / (2 * π * ‖z‖) by positivity),
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / (4 * π ^ 2) by positivity)]
    congr 1
    field_simp
    ring
  rw [setLIntegral_congr_fun (isOpen_annulus r₁ r₂).measurableSet hcongr,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_annulus_inv_normSq h₁ h₂,
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * π by positivity),
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / (4 * π ^ 2) by positivity)]
  congr 1
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem hasDerivAt_circleCurve (r t : ℝ) :
    HasDerivAt (fun s : ℝ => circleMap 0 r (2 * π * s))
      ((2 * π : ℝ) • (circleMap 0 r (2 * π * t) * I)) t := by
  have h1 : HasDerivAt (fun s : ℝ => 2 * π * s) (2 * π) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * π)
  exact (hasDerivAt_circleMap 0 r (2 * π * t)).scomp t h1

theorem lipschitzWith_circleCurve (r : ℝ) :
    LipschitzWith (Real.nnabs r * Real.nnabs (2 * π)) (fun s : ℝ => circleMap 0 r (2 * π * s)) := by
  have h2 : LipschitzWith (Real.nnabs (2 * π)) (fun s : ℝ => 2 * π * s) :=
    LipschitzWith.of_dist_le_mul fun a b => le_of_eq (by
      simp only [Real.dist_eq]
      rw [← mul_sub, abs_mul, Real.coe_nnabs])
  exact (lipschitzWith_circleMap 0 r).comp h2

/-- The circle `|z| = r`, traversed once, as a closed rectifiable curve `t ↦ r e^{2πit}`. -/
def circleCurve (r : ℝ) : LRCurve where
  toFun t := circleMap 0 r (2 * π * t)
  locallyLipschitzOn := fun _ _ => ⟨_, univ, univ_mem, (lipschitzWith_circleCurve r).lipschitzOnWith⟩

theorem circleCurve_isClosedCurve (r : ℝ) : (circleCurve r).IsClosedCurve := by
  refine ⟨_, (lipschitzWith_circleCurve r).lipschitzOnWith, ?_⟩
  show circleMap 0 r (2 * π * 0) = circleMap 0 r (2 * π * 1)
  rw [mul_zero, mul_one]
  simpa using (periodic_circleMap 0 r 0).symm

/-- Every circle of the annulus has `ρ₀`-length exactly `1` for `ρ₀ = 1/(2π|z|)`. -/
theorem circleCurve_rhoLength {r₁ r₂ r : ℝ} (h₁ : 0 < r₁) (hr₁ : r₁ < r) (hr₂ : r < r₂) :
    (circleCurve r).rhoLength
      ((annulus r₁ r₂).indicator fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖))) = 1 := by
  have hr : 0 < r := h₁.trans hr₁
  unfold LRCurve.rhoLength
  have hconst : ∀ t ∈ Ioo (0 : ℝ) 1,
      ((annulus r₁ r₂).indicator (fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖)))
          ((circleCurve r).toFun t)) * ‖deriv (circleCurve r).toFun t‖ₑ = 1 := by
    intro t _
    have hnorm : ‖(circleCurve r).toFun t‖ = r := by
      show ‖circleMap 0 r (2 * π * t)‖ = r
      rw [norm_circleMap_zero, abs_of_pos hr]
    have hmem : (circleCurve r).toFun t ∈ annulus r₁ r₂ := by
      show r₁ < ‖(circleCurve r).toFun t‖ ∧ ‖(circleCurve r).toFun t‖ < r₂
      rw [hnorm]; exact ⟨hr₁, hr₂⟩
    have hderiv : deriv (circleCurve r).toFun t
        = (2 * π : ℝ) • (circleMap 0 r (2 * π * t) * I) :=
      (hasDerivAt_circleCurve r t).deriv
    have hnormd : ‖(2 * π : ℝ) • (circleMap 0 r (2 * π * t) * I)‖ = 2 * π * r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos Real.two_pi_pos, norm_mul, norm_circleMap_zero,
        norm_I, mul_one, abs_of_pos hr]
    have hdnorm : ‖deriv (circleCurve r).toFun t‖ₑ = ENNReal.ofReal (2 * π * r) := by
      rw [hderiv, ← ofReal_norm, hnormd]
    rw [Set.indicator_of_mem hmem, hdnorm, hnorm,
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / (2 * π * r) by positivity),
      show 1 / (2 * π * r) * (2 * π * r) = 1 from div_mul_cancel₀ 1 (by positivity),
      ENNReal.ofReal_one]
  rw [setLIntegral_congr_fun measurableSet_Ioo hconst, setLIntegral_const, Real.volume_Ioo,
    sub_zero, ENNReal.ofReal_one, one_mul]


/-! ### The circles separate the two components of `ℂ̄ ∖ A` -/

theorem circleCurve_closedTrace {r : ℝ} (hr : 0 < r) :
    (circleCurve r).closedTrace = sphere (0 : ℂ) r := by
  apply Subset.antisymm
  · rintro _ ⟨t, -, rfl⟩
    show circleMap 0 r (2 * π * t) ∈ sphere (0 : ℂ) r
    rw [mem_sphere_zero_iff_norm, norm_circleMap_zero, abs_of_pos hr]
  · intro z hz
    have hz' : z ∈ circleMap 0 r '' Ioc 0 (2 * π) := by
      rw [image_circleMap_Ioc, abs_of_pos hr]; exact hz
    obtain ⟨θ, hθ, rfl⟩ := hz'
    refine ⟨θ / (2 * π), ⟨div_nonneg hθ.1.le Real.two_pi_pos.le, ?_⟩, ?_⟩
    · rw [div_le_iff₀ Real.two_pi_pos, one_mul]; exact hθ.2
    · show circleMap 0 r (2 * π * (θ / (2 * π))) = circleMap 0 r θ
      congr 1
      field_simp

theorem isPreconnected_toExt_closedBall (r : ℝ) :
    IsPreconnected (toExt (closedBall (0 : ℂ) r)) :=
  (convex_closedBall (0 : ℂ) r).isPreconnected.image _ OnePoint.continuous_coe.continuousOn

theorem isOpen_toExt_ball (r : ℝ) : IsOpen (toExt (ball (0 : ℂ) r)) :=
  OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_ball

theorem isOpen_toExt_normGT_insert (r : ℝ) :
    IsOpen (toExt {z : ℂ | r < ‖z‖} ∪ {extInf}) := by
  rw [OnePoint.isOpen_iff_of_mem (by simp)]
  have hpre : ((↑) : ℂ → ExtPlane) ⁻¹' (toExt {z : ℂ | r < ‖z‖} ∪ {extInf})
      = {z : ℂ | r < ‖z‖} := by
    ext z
    simp [toExt, OnePoint.coe_injective.mem_set_image]
  have hc : ({z : ℂ | r < ‖z‖})ᶜ = closedBall (0 : ℂ) r := by
    ext z
    simp [not_lt]
  rw [hpre, hc]
  exact ⟨isClosed_closedBall, isCompact_closedBall 0 r⟩

theorem circleCurve_closedTrace_subset {r₁ r₂ r : ℝ} (h₁ : 0 < r₁) (hr₁ : r₁ < r) (hr₂ : r < r₂) :
    (circleCurve r).closedTrace ⊆ annulus r₁ r₂ := by
  rw [circleCurve_closedTrace (h₁.trans hr₁)]
  intro z hz
  rw [mem_sphere_zero_iff_norm] at hz
  show r₁ < ‖z‖ ∧ ‖z‖ < r₂
  rw [hz]
  exact ⟨hr₁, hr₂⟩

theorem compl_toExt_annulus_subset {r₁ r₂ : ℝ} :
    (toExt (annulus r₁ r₂))ᶜ
      ⊆ toExt (closedBall (0 : ℂ) r₁) ∪ (toExt {z : ℂ | r₂ ≤ ‖z‖} ∪ {extInf}) := by
  intro p hp
  induction p using OnePoint.rec with
  | infty => exact Or.inr (Or.inr (mem_singleton _))
  | coe z =>
    have hz : z ∉ annulus r₁ r₂ := fun h => hp ⟨z, h, rfl⟩
    by_cases h : ‖z‖ ≤ r₁
    · exact Or.inl ⟨z, mem_closedBall_zero_iff.2 h, rfl⟩
    · refine Or.inr (Or.inl ⟨z, ?_, rfl⟩)
      show r₂ ≤ ‖z‖
      by_contra h2
      exact hz ⟨not_le.1 h, not_le.1 h2⟩

theorem disjoint_toExt_ball_normGT {r : ℝ} :
    Disjoint (toExt (ball (0 : ℂ) r)) (toExt {z : ℂ | r < ‖z‖} ∪ {extInf}) := by
  rw [Set.disjoint_left]
  rintro p ⟨z, hz, rfl⟩ (⟨w, hw, hwz⟩ | hinf)
  · have hwz' := OnePoint.coe_injective hwz
    subst hwz'
    rw [mem_ball_zero_iff] at hz
    exact lt_asymm hz hw
  · exact OnePoint.coe_ne_infty z hinf

theorem compl_toExt_sphere_subset {r : ℝ} :
    (toExt (sphere (0 : ℂ) r))ᶜ
      ⊆ toExt (ball (0 : ℂ) r) ∪ (toExt {z : ℂ | r < ‖z‖} ∪ {extInf}) := by
  intro p hp
  induction p using OnePoint.rec with
  | infty => exact Or.inr (Or.inr (mem_singleton _))
  | coe z =>
    have hz : z ∉ sphere (0 : ℂ) r := fun h => hp ⟨z, h, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hz
    rcases lt_or_gt_of_ne hz with h | h
    · exact Or.inl ⟨z, mem_ball_zero_iff.2 h, rfl⟩
    · exact Or.inr (Or.inl ⟨z, h, rfl⟩)

theorem toExt_closedBall_subset_ball {r₁ r : ℝ} (h : r₁ < r) :
    toExt (closedBall (0 : ℂ) r₁) ⊆ toExt (ball (0 : ℂ) r) :=
  image_mono (closedBall_subset_ball h)

theorem toExt_normGE_insert_subset {r r₂ : ℝ} (h : r < r₂) :
    toExt {z : ℂ | r₂ ≤ ‖z‖} ∪ {extInf} ⊆ toExt {z : ℂ | r < ‖z‖} ∪ {extInf} :=
  union_subset_union_left _ (image_mono fun _ hz => h.trans_le hz)

theorem extInf_mem_closure_toExt_normGE (r₂ : ℝ) :
    extInf ∈ closure (toExt {z : ℂ | r₂ ≤ ‖z‖}) := by
  rw [mem_closure_iff_nhds_basis OnePoint.hasBasis_nhds_infty]
  rintro s ⟨-, hs⟩
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hs.isBounded
  set M : ℝ := max R r₂ + 1 with hM
  have hMR : R < M := by rw [hM]; linarith [le_max_left R r₂]
  have hMr : r₂ < M := by rw [hM]; linarith [le_max_right R r₂]
  have hnorm : ‖((M : ℝ) : ℂ)‖ = |M| := by rw [Complex.norm_real, Real.norm_eq_abs]
  refine ⟨((M : ℂ) : ExtPlane), ⟨(M : ℂ), ?_, rfl⟩, Or.inl ⟨(M : ℂ), ?_, rfl⟩⟩
  · show r₂ ≤ ‖(M : ℂ)‖
    rw [hnorm]
    exact hMr.le.trans (le_abs_self M)
  · intro hmem
    have h := hR _ hmem
    rw [hnorm] at h
    exact absurd (hMR.trans_le (le_abs_self M)) (not_lt.2 h)

theorem isPreconnected_normGE {r₂ : ℝ} (h₂ : 0 ≤ r₂) :
    IsPreconnected {z : ℂ | r₂ ≤ ‖z‖} := by
  have hmap : (fun p : ℝ × ℝ => (p.1 : ℂ) * exp ((p.2 : ℂ) * I)) '' (Ici r₂ ×ˢ univ)
      = {z : ℂ | r₂ ≤ ‖z‖} := by
    apply Subset.antisymm
    · rintro _ ⟨⟨ρ, θ⟩, ⟨hρ, -⟩, rfl⟩
      show r₂ ≤ ‖(ρ : ℂ) * exp ((θ : ℂ) * I)‖
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (h₂.trans hρ)]
      exact hρ
    · intro z hz
      exact ⟨(‖z‖, arg z), ⟨hz, mem_univ _⟩, Complex.norm_mul_exp_arg_mul_I z⟩
  rw [← hmap]
  exact (isPreconnected_Ici.prod isPreconnected_univ).image _
    (Continuous.continuousOn (by fun_prop))

theorem isPreconnected_toExt_normGE_insert {r₂ : ℝ} (h₂ : 0 ≤ r₂) :
    IsPreconnected (toExt {z : ℂ | r₂ ≤ ‖z‖} ∪ {extInf}) := by
  have hK : IsPreconnected (toExt {z : ℂ | r₂ ≤ ‖z‖}) :=
    (isPreconnected_normGE h₂).image _ OnePoint.continuous_coe.continuousOn
  refine hK.subset_closure subset_union_left ?_
  exact union_subset subset_closure (singleton_subset_iff.2 (extInf_mem_closure_toExt_normGE r₂))

/-- **Every concentric circle of the annulus is a separating curve.** -/
theorem circleCurve_mem_separatingCurves {r₁ r₂ r : ℝ} (h₁ : 0 < r₁) (hr₁ : r₁ < r) (hr₂ : r < r₂) :
    circleCurve r ∈ separatingCurves (annulus r₁ r₂) := by
  have hr : 0 < r := h₁.trans hr₁
  have htrace := circleCurve_closedTrace_subset h₁ hr₁ hr₂
  show IsSeparatingCurve (annulus r₁ r₂) (circleCurve r)
  refine ⟨circleCurve_isClosedCurve r, htrace, ?_⟩
  have hKin : IsPreconnected (toExt (closedBall (0 : ℂ) r₁)) := isPreconnected_toExt_closedBall r₁
  have hKout : IsPreconnected (toExt {z : ℂ | r₂ ≤ ‖z‖} ∪ {extInf}) :=
    isPreconnected_toExt_normGE_insert (h₁.trans (hr₁.trans hr₂)).le
  have hsplit := @compl_toExt_annulus_subset r₁ r₂
  have hKinA : toExt (closedBall (0 : ℂ) r₁) ⊆ (toExt (annulus r₁ r₂))ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    have hwz' : w = z := OnePoint.coe_injective hwz
    rw [hwz'] at hw
    rw [mem_closedBall_zero_iff] at hz
    exact absurd hw.1 (not_lt.2 hz)
  have hKoutA : toExt {z : ℂ | r₂ ≤ ‖z‖} ∪ {extInf} ⊆ (toExt (annulus r₁ r₂))ᶜ := by
    rintro p (⟨z, hz, rfl⟩ | hinf) hA
    · obtain ⟨w, hw, hwz⟩ := hA
      have hwz' : w = z := OnePoint.coe_injective hwz
      rw [hwz'] at hw
      exact absurd hw.2 (not_lt.2 hz)
    · rw [mem_singleton_iff] at hinf
      subst hinf
      obtain ⟨w, -, hw⟩ := hA
      exact OnePoint.coe_ne_infty w hw
  have hAC : (toExt (annulus r₁ r₂))ᶜ ⊆ (toExt (circleCurve r).closedTrace)ᶜ :=
    compl_subset_compl.2 (image_mono htrace)
  have hcover : (toExt (circleCurve r).closedTrace)ᶜ
      ⊆ toExt (ball (0 : ℂ) r) ∪ (toExt {z : ℂ | r < ‖z‖} ∪ {extInf}) := by
    rw [circleCurve_closedTrace hr]
    exact compl_toExt_sphere_subset
  have hUin := isOpen_toExt_ball r
  have hUout := isOpen_toExt_normGT_insert r
  have hdisj := @disjoint_toExt_ball_normGT r
  have hKinU := toExt_closedBall_subset_ball hr₁
  have hKoutU := toExt_normGE_insert_subset hr₂
  have same : ∀ {S : Set ExtPlane}, IsPreconnected S → S ⊆ (toExt (annulus r₁ r₂))ᶜ →
      ∀ {a b : ExtPlane}, a ∈ S → b ∈ S →
        connectedComponentIn (toExt (annulus r₁ r₂))ᶜ a
          = connectedComponentIn (toExt (annulus r₁ r₂))ᶜ b := by
    intro S hS hSA a b ha hb
    exact connectedComponentIn_eq (hS.subset_connectedComponentIn ha hSA hb)
  have apart : ∀ {a b : ExtPlane}, a ∈ toExt (closedBall (0 : ℂ) r₁) →
      b ∈ toExt {z : ℂ | r₂ ≤ ‖z‖} ∪ {extInf} →
      connectedComponentIn (toExt (circleCurve r).closedTrace)ᶜ a ≠
        connectedComponentIn (toExt (circleCurve r).closedTrace)ᶜ b := by
    intro a b ha hb heq
    have haC : a ∈ (toExt (circleCurve r).closedTrace)ᶜ := hAC (hKinA ha)
    have hsub : connectedComponentIn (toExt (circleCurve r).closedTrace)ᶜ a
        ⊆ toExt (ball (0 : ℂ) r) :=
      isPreconnected_connectedComponentIn.subset_left_of_subset_union hUin hUout hdisj
        ((connectedComponentIn_subset _ _).trans hcover)
        ⟨a, mem_connectedComponentIn haC, hKinU ha⟩
    have hbC : b ∈ (toExt (circleCurve r).closedTrace)ᶜ := hAC (hKoutA hb)
    have hbin : b ∈ connectedComponentIn (toExt (circleCurve r).closedTrace)ᶜ a := by
      rw [heq]; exact mem_connectedComponentIn hbC
    exact Set.disjoint_left.1 hdisj (hsub hbin) (hKoutU hb)
  intro x hx y hy hxy
  rcases hsplit hx with hxi | hxo <;> rcases hsplit hy with hyi | hyo
  · exact absurd (same hKin hKinA hxi hyi) hxy
  · exact apart hxi hyo
  · exact fun h => apart hyi hxo h.symm
  · exact absurd (same hKout hKoutA hxo hyo) hxy

/-! ### The extremal length of the annulus: upper bound -/

/-- `∫⁻_{r₁}^{r₂} dr/r = ln(r₂/r₁)`. -/
theorem lintegral_Ioo_ofReal_one_div {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    ∫⁻ r in Ioo r₁ r₂, ENNReal.ofReal (1 / r) = ENNReal.ofReal (Real.log (r₂ / r₁)) := by
  have hle : r₁ ≤ r₂ := h₂.le
  have hint : IntegrableOn (fun r : ℝ => 1 / r) (Ioo r₁ r₂) := by
    have h := intervalIntegral.intervalIntegrable_inv (μ := volume) (f := fun x : ℝ => x)
      (fun x hx => by
        rw [uIcc_of_le hle] at hx
        exact (h₁.trans_le hx.1).ne') continuousOn_id
    simpa only [one_div] using (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).1 h
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo r₁ r₂)] fun r : ℝ => 1 / r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with r hr
    exact one_div_nonneg.2 (h₁.trans hr.1).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  simp only [one_div]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle,
    integral_inv_of_pos h₁ (h₁.trans h₂)]

/-- Polar coordinates in terms of `circleMap`. -/
theorem polarCoord_symm_eq_circleMap (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
  have h : Complex.polarCoord.symm (r, θ) + 0 = circleMap 0 r θ := by
    simp only [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    ring
  simpa using h

/-- The `ρ`-length of the circle `|z| = r`, as an integral over the parameter. -/
theorem circleCurve_rhoLength_eq {r : ℝ} (hr : 0 < r) (ρ : ℂ → ℝ≥0∞) :
    (circleCurve r).rhoLength ρ
      = ∫⁻ t in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (2 * π) * (ENNReal.ofReal r * ρ (circleMap 0 r (2 * π * t))) := by
  unfold LRCurve.rhoLength
  refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
  have hderiv : deriv (circleCurve r).toFun t = (2 * π : ℝ) • (circleMap 0 r (2 * π * t) * I) :=
    (hasDerivAt_circleCurve r t).deriv
  have hnormd : ‖(2 * π : ℝ) • (circleMap 0 r (2 * π * t) * I)‖ = 2 * π * r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos Real.two_pi_pos, norm_mul, norm_circleMap_zero,
      norm_I, mul_one, abs_of_pos hr]
  rw [hderiv, ← ofReal_norm, hnormd, ENNReal.ofReal_mul Real.two_pi_pos.le]
  show ρ (circleMap 0 r (2 * π * t)) * (ENNReal.ofReal (2 * π) * ENNReal.ofReal r)
    = ENNReal.ofReal (2 * π) * (ENNReal.ofReal r * ρ (circleMap 0 r (2 * π * t)))
  ring

/-- The inverse polar coordinate map is continuous. -/
theorem continuous_complex_polarCoord_symm :
    Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
  simp only [Complex.polarCoord_symm_apply]
  fun_prop

/-- Polar coordinates on an annulus for the weight `1/|z|`:
`∬_A ρ(z)/|z| dx dy = ∫_{r₁}^{r₂} ∫_{-π}^{π} ρ(r e^{iθ}) dθ dr`. -/
theorem lintegral_annulus_mul_inv_norm {r₁ r₂ : ℝ} (h₁ : 0 < r₁) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) :
    ∫⁻ z in annulus r₁ r₂, ρ z * ENNReal.ofReal (1 / ‖z‖)
      = ∫⁻ r in Ioo r₁ r₂, ∫⁻ θ in Ioo (-π) π, ρ (Complex.polarCoord.symm (r, θ)) := by
  have key : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • (annulus r₁ r₂).indicator
          (fun w : ℂ => ρ w * ENNReal.ofReal (1 / ‖w‖)) (Complex.polarCoord.symm p)
        = (Ioo r₁ r₂ ×ˢ (univ : Set ℝ)).indicator
            (fun q => ρ (Complex.polarCoord.symm q)) p := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr0 : (0 : ℝ) < r := hr
    have hnorm : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm]
      exact abs_of_pos hr0
    by_cases hmem : r ∈ Ioo r₁ r₂
    · have hmem' : Complex.polarCoord.symm (r, θ) ∈ annulus r₁ r₂ := by
        show r₁ < ‖Complex.polarCoord.symm (r, θ)‖ ∧ ‖Complex.polarCoord.symm (r, θ)‖ < r₂
        rw [hnorm]; exact hmem
      have hmem2 : (r, θ) ∈ Ioo r₁ r₂ ×ˢ (univ : Set ℝ) := ⟨hmem, mem_univ _⟩
      rw [Set.indicator_of_mem hmem', Set.indicator_of_mem hmem2, smul_eq_mul, hnorm,
        mul_left_comm, ← ENNReal.ofReal_mul hr0.le, mul_one_div_cancel hr0.ne',
        ENNReal.ofReal_one, mul_one]
    · have hmem' : Complex.polarCoord.symm (r, θ) ∉ annulus r₁ r₂ := by
        show ¬ (r₁ < ‖Complex.polarCoord.symm (r, θ)‖ ∧ ‖Complex.polarCoord.symm (r, θ)‖ < r₂)
        rw [hnorm]; exact hmem
      have hmem2 : (r, θ) ∉ Ioo r₁ r₂ ×ˢ (univ : Set ℝ) := fun h => hmem h.1
      rw [Set.indicator_of_notMem hmem', Set.indicator_of_notMem hmem2, smul_zero]
  have hmeas : AEMeasurable (fun x : ℝ × ℝ =>
      (Ioo r₁ r₂ ×ˢ (univ : Set ℝ)).indicator (fun q => ρ (Complex.polarCoord.symm q)) x)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) :=
    ((hρ.comp continuous_complex_polarCoord_symm.measurable).indicator
      (measurableSet_Ioo.prod MeasurableSet.univ)).aemeasurable
  rw [← lintegral_indicator (isOpen_annulus r₁ r₂).measurableSet,
    ← Complex.lintegral_comp_polarCoord_symm,
    setLIntegral_congr_fun polarCoord.open_target.measurableSet key,
    show (polarCoord.target : Set (ℝ × ℝ)) = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl,
    Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict, lintegral_prod _ hmeas]
  have hinner : ∀ r : ℝ,
      ∫⁻ θ in Ioo (-π) π,
          (Ioo r₁ r₂ ×ˢ (univ : Set ℝ)).indicator (fun q => ρ (Complex.polarCoord.symm q)) (r, θ)
        = (Ioo r₁ r₂).indicator
            (fun r => ∫⁻ θ in Ioo (-π) π, ρ (Complex.polarCoord.symm (r, θ))) r := by
    intro r
    by_cases hr : r ∈ Ioo r₁ r₂
    · rw [Set.indicator_of_mem hr]
      exact setLIntegral_congr_fun measurableSet_Ioo fun θ _ =>
        Set.indicator_of_mem (show (r, θ) ∈ Ioo r₁ r₂ ×ˢ (univ : Set ℝ) from ⟨hr, mem_univ θ⟩) _
    · rw [Set.indicator_of_notMem hr]
      have h0 : ∀ θ : ℝ, (Ioo r₁ r₂ ×ˢ (univ : Set ℝ)).indicator
          (fun q => ρ (Complex.polarCoord.symm q)) (r, θ) = 0 :=
        fun θ => Set.indicator_of_notMem (fun h => hr h.1) _
      simp only [h0, lintegral_zero]
  simp_rw [hinner]
  have hsub : Ioo r₁ r₂ ∩ Ioi 0 = Ioo r₁ r₂ :=
    Set.inter_eq_self_of_subset_left fun x hx => h₁.trans hx.1
  rw [setLIntegral_indicator measurableSet_Ioo, hsub]

/-- The `ρ`-length of the circle `|z| = r` as an integral over a full turn `(0, 2π)`. -/
theorem circleCurve_rhoLength_Ioo_two_pi {r : ℝ} (hr : 0 < r) (ρ : ℂ → ℝ≥0∞) :
    (circleCurve r).rhoLength ρ
      = ENNReal.ofReal r * ∫⁻ θ in Ioo 0 (2 * π), ρ (circleMap 0 r θ) := by
  have hcv : ∫⁻ θ in Ioo 0 (2 * π), ENNReal.ofReal r * ρ (circleMap 0 r θ)
      = ∫⁻ t in Ioo (0 : ℝ) 1,
          ENNReal.ofReal |2 * π| * (ENNReal.ofReal r * ρ (circleMap 0 r (2 * π * t))) := by
    have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioo (0 : ℝ) 1)
      (f := fun t : ℝ => 2 * π * t) (f' := fun _ => 2 * π) measurableSet_Ioo
      (fun t _ => (by simpa using (hasDerivAt_id t).const_mul (2 * π) :
        HasDerivAt (fun s : ℝ => 2 * π * s) (2 * π) t).hasDerivWithinAt)
      (mul_right_injective₀ Real.two_pi_pos.ne').injOn
      (fun θ => ENNReal.ofReal r * ρ (circleMap 0 r θ))
    rw [image_mul_left_Ioo Real.two_pi_pos, mul_zero, mul_one] at h
    exact h
  rw [circleCurve_rhoLength_eq hr, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hcv]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
  rw [abs_of_pos Real.two_pi_pos]

/-- A `2π`-periodic function has the same integral over `(0, 2π)` and over `(-π, π)`. -/
theorem lintegral_Ioo_two_pi_eq_Ioo_neg_pi (h : ℝ → ℝ≥0∞) (hper : Function.Periodic h (2 * π)) :
    ∫⁻ θ in Ioo 0 (2 * π), h θ = ∫⁻ θ in Ioo (-π) π, h θ := by
  haveI : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  have key : ∀ t : ℝ,
      ∫⁻ θ in Ioc t (t + 2 * π), h θ = ∫⁻ b : AddCircle (2 * π), hper.lift b := by
    intro t
    rw [← AddCircle.lintegral_preimage (2 * π) t]
    refine setLIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
    exact (Function.Periodic.lift_coe hper θ).symm
  have hL : ∫⁻ θ in Ioo 0 (2 * π), h θ = ∫⁻ b : AddCircle (2 * π), hper.lift b := by
    rw [setLIntegral_congr Ioo_ae_eq_Ioc, ← key 0, zero_add]
  have hR : ∫⁻ θ in Ioo (-π) π, h θ = ∫⁻ b : AddCircle (2 * π), hper.lift b := by
    rw [setLIntegral_congr Ioo_ae_eq_Ioc, ← key (-π), show -π + 2 * π = π by ring]
  rw [hL, hR]

/-- The `ρ`-length of the circle `|z| = r` in polar form: `r ∫_{-π}^{π} ρ(r e^{iθ}) dθ`. -/
theorem circleCurve_rhoLength_polar {r : ℝ} (hr : 0 < r) (ρ : ℂ → ℝ≥0∞) :
    (circleCurve r).rhoLength ρ
      = ENNReal.ofReal r * ∫⁻ θ in Ioo (-π) π, ρ (Complex.polarCoord.symm (r, θ)) := by
  rw [circleCurve_rhoLength_Ioo_two_pi hr,
    lintegral_Ioo_two_pi_eq_Ioo_neg_pi (fun θ => ρ (circleMap 0 r θ))
      ((periodic_circleMap 0 r).comp ρ)]
  simp only [polarCoord_symm_eq_circleMap]

/-- Integrating the circle lengths: `(inf_Γ l_ρ) · ln(r₂/r₁) ≤ ∬_A ρ/|z|`. -/
theorem iInf_rhoLength_mul_log_le {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) :
    (⨅ γ ∈ separatingCurves (annulus r₁ r₂), γ.rhoLength ρ) * ENNReal.ofReal (Real.log (r₂ / r₁))
      ≤ ∫⁻ z in annulus r₁ r₂, ρ z * ENNReal.ofReal (1 / ‖z‖) := by
  have hmeas : Measurable fun r : ℝ => ENNReal.ofReal (1 / r) :=
    (measurable_const.div measurable_id).ennreal_ofReal
  rw [lintegral_annulus_mul_inv_norm h₁ hρ, ← lintegral_Ioo_ofReal_one_div h₁ h₂,
    ← lintegral_const_mul _ hmeas]
  refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
  have hr0 : 0 < r := h₁.trans hr.1
  have hle : (⨅ γ ∈ separatingCurves (annulus r₁ r₂), γ.rhoLength ρ)
      ≤ (circleCurve r).rhoLength ρ :=
    iInf₂_le _ (circleCurve_mem_separatingCurves h₁ hr.1 hr.2)
  rw [circleCurve_rhoLength_polar hr0 ρ] at hle
  calc (⨅ γ ∈ separatingCurves (annulus r₁ r₂), γ.rhoLength ρ) * ENNReal.ofReal (1 / r)
      ≤ (ENNReal.ofReal r * ∫⁻ θ in Ioo (-π) π, ρ (Complex.polarCoord.symm (r, θ)))
          * ENNReal.ofReal (1 / r) := by gcongr
    _ = ∫⁻ θ in Ioo (-π) π, ρ (Complex.polarCoord.symm (r, θ)) := by
        rw [mul_comm (ENNReal.ofReal r), mul_assoc, ← ENNReal.ofReal_mul hr0.le,
          mul_one_div_cancel hr0.ne', ENNReal.ofReal_one, mul_one]

/-- **The extremal length of the separating curves of an annulus is at most `2π/ln(r₂/r₁)`.** -/
theorem extremalLength_annulusSeparating_le {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    extremalLength (separatingCurves (annulus r₁ r₂))
      ≤ ENNReal.ofReal (2 * π / Real.log (r₂ / r₁)) := by
  have hLpos : 0 < Real.log (r₂ / r₁) :=
    Real.log_pos (by rw [lt_div_iff₀ h₁, one_mul]; exact h₂)
  unfold extremalLength extremalLengthIn
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨hρm, hρ0, hρtop⟩ := hρ
  rw [← iInf_rhoLength_sq, ENNReal.div_le_iff hρ0.ne' hρtop.ne]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, (⨅ γ ∈ separatingCurves (annulus r₁ r₂), γ.rhoLength ρ) = ℓ := ⟨_, rfl⟩
  rw [hℓ]
  have hgm : Measurable fun z : ℂ => ENNReal.ofReal (1 / ‖z‖) :=
    (measurable_const.div measurable_norm).ennreal_ofReal
  have hiv : ℓ * ENNReal.ofReal (Real.log (r₂ / r₁))
      ≤ ∫⁻ z in annulus r₁ r₂, ρ z * ENNReal.ofReal (1 / ‖z‖) := by
    rw [← hℓ]; exact iInf_rhoLength_mul_log_le h₁ h₂ hρm
  have hg2 : ∫⁻ z in annulus r₁ r₂, ENNReal.ofReal (1 / ‖z‖) ^ 2
      = ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (r₂ / r₁)) := by
    rw [← lintegral_annulus_inv_normSq h₁ h₂]
    refine setLIntegral_congr_fun (isOpen_annulus r₁ r₂).measurableSet fun z _ => ?_
    rw [← ENNReal.ofReal_pow (show (0 : ℝ) ≤ 1 / ‖z‖ by positivity), one_div_pow]
  have harea : ∫⁻ z in annulus r₁ r₂, ρ z ^ 2 ≤ rhoArea ρ univ :=
    lintegral_mono_set (subset_univ _)
  have hkey : ENNReal.ofReal (Real.log (r₂ / r₁)) * (ENNReal.ofReal (Real.log (r₂ / r₁)) * ℓ ^ 2)
      ≤ ENNReal.ofReal (Real.log (r₂ / r₁)) * (ENNReal.ofReal (2 * π) * rhoArea ρ univ) := by
    calc ENNReal.ofReal (Real.log (r₂ / r₁)) * (ENNReal.ofReal (Real.log (r₂ / r₁)) * ℓ ^ 2)
        = (ℓ * ENNReal.ofReal (Real.log (r₂ / r₁))) ^ 2 := by ring
      _ ≤ (∫⁻ z in annulus r₁ r₂, ρ z * ENNReal.ofReal (1 / ‖z‖)) ^ 2 := pow_le_pow_left' hiv 2
      _ ≤ (∫⁻ z in annulus r₁ r₂, ρ z ^ 2) * ∫⁻ z in annulus r₁ r₂, ENNReal.ofReal (1 / ‖z‖) ^ 2 :=
          setLIntegral_mul_sq_le hρm hgm
      _ ≤ rhoArea ρ univ * (ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (r₂ / r₁))) := by
          rw [hg2]; gcongr
      _ = ENNReal.ofReal (Real.log (r₂ / r₁)) * (ENNReal.ofReal (2 * π) * rhoArea ρ univ) := by
          ring
  have hL0 : ENNReal.ofReal (Real.log (r₂ / r₁)) ≠ 0 := (ENNReal.ofReal_pos.2 hLpos).ne'
  have hLt : ENNReal.ofReal (Real.log (r₂ / r₁)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 : ENNReal.ofReal (Real.log (r₂ / r₁)) * ℓ ^ 2 ≤ ENNReal.ofReal (2 * π) * rhoArea ρ univ :=
    (ENNReal.mul_le_mul_iff_right hL0 hLt).1 hkey
  calc ℓ ^ 2
      = (ENNReal.ofReal (Real.log (r₂ / r₁)))⁻¹ * (ENNReal.ofReal (Real.log (r₂ / r₁)) * ℓ ^ 2) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hL0 hLt, one_mul]
    _ ≤ (ENNReal.ofReal (Real.log (r₂ / r₁)))⁻¹ * (ENNReal.ofReal (2 * π) * rhoArea ρ univ) := by
        gcongr
    _ = ENNReal.ofReal (2 * π / Real.log (r₂ / r₁)) * rhoArea ρ univ := by
        rw [ENNReal.ofReal_div_of_pos hLpos, ENNReal.div_eq_inv_mul, mul_assoc]

/-! ### Separating curves of the annulus meet every ray -/

/-- `∞` lies in the closure of (the image in `ℂ̄` of) an unbounded set. -/
theorem extInf_mem_closure_toExt_of_unbounded {X : Set ℂ} (hX : ∀ R : ℝ, ∃ z ∈ X, R < ‖z‖) :
    extInf ∈ closure (toExt X) := by
  rw [mem_closure_iff_nhds_basis OnePoint.hasBasis_nhds_infty]
  rintro s ⟨-, hs⟩
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hs.isBounded
  obtain ⟨z, hz, hzR⟩ := hX R
  exact ⟨(z : ExtPlane), ⟨z, hz, rfl⟩,
    Or.inl ⟨z, fun hmem => absurd (hR z hmem) (not_le.2 hzR), rfl⟩⟩

/-- The closed ray `{s e^{iφ} : s ≥ 0}` together with `∞` is connected in `ℂ̄`. -/
theorem isPreconnected_toExt_ray_insert (φ : ℝ) :
    IsPreconnected (toExt ((fun s : ℝ => (s : ℂ) * exp (φ * I)) '' Ici 0) ∪ {extInf}) := by
  have hK : IsPreconnected (toExt ((fun s : ℝ => (s : ℂ) * exp (φ * I)) '' Ici 0)) :=
    (isPreconnected_Ici.image _ (Continuous.continuousOn (by fun_prop))).image _
      OnePoint.continuous_coe.continuousOn
  refine hK.subset_closure subset_union_left ?_
  refine union_subset subset_closure (singleton_subset_iff.2 ?_)
  refine extInf_mem_closure_toExt_of_unbounded fun R =>
    ⟨((|R| + 1 : ℝ) : ℂ) * exp (φ * I), ⟨|R| + 1, (by positivity : (0 : ℝ) ≤ |R| + 1), rfl⟩, ?_⟩
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  linarith [le_abs_self R]

/-- `0` lies outside the annulus. -/
theorem zero_mem_compl_toExt_annulus {r₁ r₂ : ℝ} (h₁ : 0 < r₁) :
    ((0 : ℂ) : ExtPlane) ∈ (toExt (annulus r₁ r₂))ᶜ := by
  rintro ⟨w, hw, hw0⟩
  have hw' : w = 0 := OnePoint.coe_injective hw0
  subst hw'
  have h := hw.1
  rw [norm_zero] at h
  linarith

/-- `0` and `∞` lie in different components of `ℂ̄ ∖ A`. -/
theorem connectedComponentIn_compl_toExt_annulus_ne {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    connectedComponentIn (toExt (annulus r₁ r₂))ᶜ ((0 : ℂ) : ExtPlane)
      ≠ connectedComponentIn (toExt (annulus r₁ r₂))ᶜ extInf := by
  set r := (r₁ + r₂) / 2 with hr
  have hr₁ : r₁ < r := by rw [hr]; linarith
  have hr₂ : r < r₂ := by rw [hr]; linarith
  have hcover : (toExt (annulus r₁ r₂))ᶜ
      ⊆ toExt (ball (0 : ℂ) r) ∪ (toExt {z : ℂ | r < ‖z‖} ∪ {extInf}) :=
    compl_toExt_annulus_subset.trans
      (union_subset_union (toExt_closedBall_subset_ball hr₁) (toExt_normGE_insert_subset hr₂))
  intro heq
  have hsub : connectedComponentIn (toExt (annulus r₁ r₂))ᶜ ((0 : ℂ) : ExtPlane)
      ⊆ toExt (ball (0 : ℂ) r) :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union (isOpen_toExt_ball r)
      (isOpen_toExt_normGT_insert r) disjoint_toExt_ball_normGT
      ((connectedComponentIn_subset _ _).trans hcover)
      ⟨_, mem_connectedComponentIn (zero_mem_compl_toExt_annulus h₁),
        ⟨0, mem_ball_self (h₁.trans hr₁), rfl⟩⟩
  have hinf : extInf ∈ connectedComponentIn (toExt (annulus r₁ r₂))ᶜ ((0 : ℂ) : ExtPlane) := by
    rw [heq]; exact mem_connectedComponentIn (extInf_mem_compl_toExt _)
  obtain ⟨w, -, hw⟩ := hsub hinf
  exact OnePoint.coe_ne_infty w hw

/-- **A separating curve of an annulus meets every ray from the origin.** -/
theorem exists_mem_ray_of_mem_separatingCurves {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂)
    {γ : LRCurve} (hγ : γ ∈ separatingCurves (annulus r₁ r₂)) (φ : ℝ) :
    ∃ t ∈ Icc (0 : ℝ) 1, γ.toFun t = (‖γ.toFun t‖ : ℂ) * exp (φ * I) := by
  obtain ⟨-, -, hsep⟩ := hγ
  by_contra hno
  have hSC : toExt ((fun s : ℝ => (s : ℂ) * exp (φ * I)) '' Ici 0) ∪ {extInf}
      ⊆ (toExt γ.closedTrace)ᶜ := by
    rintro p (⟨z, ⟨s, hs, rfl⟩, rfl⟩ | hp) ⟨w, ⟨t, ht, rfl⟩, hwz⟩
    · have hwz' : γ.toFun t = (s : ℂ) * exp (φ * I) := OnePoint.coe_injective hwz
      have hnorm : ‖γ.toFun t‖ = s := by
        rw [hwz', norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hs]
      exact hno ⟨t, ht, by rw [hnorm]; exact hwz'⟩
    · rw [mem_singleton_iff] at hp
      exact OnePoint.coe_ne_infty _ (hwz.trans hp)
  have h0S : ((0 : ℂ) : ExtPlane) ∈ toExt ((fun s : ℝ => (s : ℂ) * exp (φ * I)) '' Ici 0) ∪ {extInf} :=
    Or.inl ⟨0, ⟨0, self_mem_Ici, by simp⟩, rfl⟩
  have hinfS : extInf ∈ toExt ((fun s : ℝ => (s : ℂ) * exp (φ * I)) '' Ici 0) ∪ {extInf} :=
    Or.inr (mem_singleton _)
  exact hsep _ (zero_mem_compl_toExt_annulus h₁) _ (extInf_mem_compl_toExt _)
    (connectedComponentIn_compl_toExt_annulus_ne h₁ h₂)
    (connectedComponentIn_eq
      ((isPreconnected_toExt_ray_insert φ).subset_connectedComponentIn h0S hSC hinfS))

/-! ### A continuous argument along a curve avoiding `0`

The book bounds `∫_γ |dz|/|z|` below by `|∫_γ d arg z| ≥ 2π`; that fails for non-simple
separating curves (winding once each way gives `0`). We use instead that the continuous
argument of a curve meeting every ray oscillates by at least `2π`. -/

/-- A continuous argument along a curve on `[0, 1]` avoiding `0` (path lifting through the
covering map `ℝ → S¹`, `θ ↦ e^{iθ}`). -/
theorem exists_continuous_arg_lift {γ : ℝ → ℂ} (hc : ContinuousOn γ (Icc 0 1))
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0) :
    ∃ θ : ℝ → ℝ, Continuous θ ∧ ∀ t ∈ Icc (0 : ℝ) 1, (‖γ t‖ : ℂ) * exp (θ t * I) = γ t := by
  have hne' : ∀ t : unitInterval, (‖γ t‖ : ℂ) ≠ 0 := fun t =>
    ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne t t.2))
  have hmem : ∀ t : unitInterval, γ t / (‖γ t‖ : ℂ) ∈ Submonoid.unitSphere ℂ := fun t =>
    mem_sphere_zero_iff_norm.2 (by
      rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 (hne t t.2))])
  have hcI : Continuous fun t : unitInterval => γ t :=
    hc.comp_continuous continuous_subtype_val fun t => t.2
  let c : C(unitInterval, Circle) :=
    ⟨fun t => ⟨γ t / (‖γ t‖ : ℂ), hmem t⟩,
      Continuous.subtype_mk (hcI.div (continuous_ofReal.comp (continuous_norm.comp hcI)) hne') _⟩
  obtain ⟨Θ, hΘ, -⟩ :=
    Circle.isCoveringMap_exp.exists_path_lifts c (arg (c 0 : ℂ)) (Circle.exp_arg (c 0)).symm
  have key : ∀ x : unitInterval, exp (Θ x * I) = γ x / (‖γ (x : ℝ)‖ : ℂ) := fun x =>
    congrArg ((↑) : Circle → ℂ) (congrFun hΘ x)
  refine ⟨fun t => Θ (projIcc 0 1 zero_le_one t), Θ.continuous.comp continuous_projIcc,
    fun t ht => ?_⟩
  have h := key (projIcc 0 1 zero_le_one t)
  rw [projIcc_of_mem zero_le_one ht] at h
  have hn : (‖γ t‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne t ht))
  simp only [projIcc_of_mem zero_le_one ht]
  rw [h]
  field_simp

/-- Near each parameter, a continuous argument differs from its value there by the principal
argument of the quotient. -/
theorem eventually_arg_lift_eq {γ : ℝ → ℂ} {θ : ℝ → ℝ} (hθc : Continuous θ)
    (hθ : ∀ t ∈ Icc (0 : ℝ) 1, (‖γ t‖ : ℂ) * exp (θ t * I) = γ t)
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ᶠ s in 𝓝[Icc 0 1] t, θ s = θ t + arg (γ s / γ t) := by
  have hnear : ∀ᶠ s in 𝓝 t, |θ s - θ t| < π := by
    have h := (hθc.tendsto t).eventually (Metric.ball_mem_nhds (θ t) Real.pi_pos)
    filter_upwards [h] with s hs
    rwa [Real.dist_eq] at hs
  filter_upwards [nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with s hs hsI
  have hnt : (‖γ t‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne t ht))
  have hq : γ s / γ t = ((‖γ s‖ / ‖γ t‖ : ℝ) : ℂ) * exp (((θ s - θ t : ℝ)) * I) := by
    conv_lhs => rw [← hθ s hsI, ← hθ t ht]
    rw [ofReal_sub, sub_mul, Complex.exp_sub, ofReal_div]
    field_simp
  have hpos : 0 < ‖γ s‖ / ‖γ t‖ :=
    div_pos (norm_pos_iff.2 (hne s hsI)) (norm_pos_iff.2 (hne t ht))
  rw [hq, arg_real_mul _ hpos, arg_exp_mul_I, (toIocMod_eq_self _).2]
  · ring
  · constructor
    · linarith [(abs_lt.1 hs).1]
    · linarith [(abs_lt.1 hs).2]

/-- The derivative of a continuous argument: `θ' = Im(γ'/γ)`. -/
theorem hasDerivAt_arg_lift {γ : ℝ → ℂ} {θ : ℝ → ℝ} (hθc : Continuous θ)
    (hθ : ∀ t ∈ Icc (0 : ℝ) 1, (‖γ t‖ : ℂ) * exp (θ t * I) = γ t)
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {γ' : ℂ}
    (hγ : HasDerivAt γ γ' t) : HasDerivAt θ (γ' / γ t).im t := by
  have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
  have hev : θ =ᶠ[𝓝 t] fun s => θ t + (log (γ s / γ t)).im := by
    have h := eventually_arg_lift_eq hθc hθ hne htI
    rw [nhdsWithin_eq_nhds.2 (Icc_mem_nhds ht.1 ht.2)] at h
    filter_upwards [h] with s hs
    rw [hs, log_im]
  have hd : HasDerivAt (fun s => γ s / γ t) (γ' / γ t) t := hγ.div_const _
  have hlog := hd.clog_real (by rw [div_self (hne t htI)]; exact one_mem_slitPlane)
  rw [div_self (hne t htI), div_one] at hlog
  exact ((hasDerivAt_im_of_hasDerivAt hlog).const_add (θ t)).congr_of_eventuallyEq hev

/-- A continuous argument along a Lipschitz curve avoiding `0` is locally Lipschitz. -/
theorem locallyLipschitzOn_arg_lift {γ : ℝ → ℂ} {θ : ℝ → ℝ} {K : ℝ≥0}
    (hK : LipschitzOnWith K γ (Icc 0 1)) (hθc : Continuous θ)
    (hθ : ∀ t ∈ Icc (0 : ℝ) 1, (‖γ t‖ : ℂ) * exp (θ t * I) = γ t)
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0) : LocallyLipschitzOn (Icc 0 1) θ := by
  intro t ht
  have hg : ContDiffAt ℝ 1 (fun z : ℂ => (log (z / γ t)).im) (γ t) := by
    have hlog : ContDiffAt ℝ 1 (fun w : ℂ => (log w).im) (γ t / γ t) := by
      rw [div_self (hne t ht)]
      exact Complex.imCLM.contDiff.contDiffAt.comp _
        ((Complex.contDiffAt_log one_mem_slitPlane).restrict_scalars ℝ)
    have hdiv : ContDiffAt ℝ 1 (fun z : ℂ => z / γ t) (γ t) :=
      (contDiff_id.div_const (γ t)).contDiffAt
    exact ContDiffAt.comp (g := fun w : ℂ => (log w).im) (f := fun z : ℂ => z / γ t) (γ t)
      hlog hdiv
  obtain ⟨Kg, V, hV, hgV⟩ := hg.exists_lipschitzOnWith
  have hpre : γ ⁻¹' V ∈ 𝓝[Icc 0 1] t := hK.continuousOn t ht hV
  refine ⟨Kg * K, {s | s ∈ Icc (0 : ℝ) 1 ∧ γ s ∈ V ∧ θ s = θ t + arg (γ s / γ t)}, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin, hpre, eventually_arg_lift_eq hθc hθ hne ht]
      with s h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · intro x hx y hy
    rw [hx.2.2, hy.2.2, edist_add_left, ← log_im, ← log_im]
    exact (hgV.comp (hK.mono fun s hs => hs.1) fun s hs => hs.2.1) hx hy

/-- **A closed curve avoiding `0` and meeting every ray from `0` has `∫ |γ'|/|γ| ≥ 2π`**:
its continuous argument oscillates by at least `2π`. -/
theorem two_pi_le_lintegral_norm_deriv_div_norm {γ : LRCurve} {K : ℝ≥0}
    (hK : LipschitzOnWith K γ.toFun (Icc 0 1)) (hne : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ≠ 0)
    (hray : ∀ φ : ℝ, ∃ t ∈ Icc (0 : ℝ) 1, γ.toFun t = (‖γ.toFun t‖ : ℂ) * exp (φ * I)) :
    ENNReal.ofReal (2 * π)
      ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (‖deriv γ.toFun t‖ / ‖γ.toFun t‖) := by
  obtain ⟨θ, hθc, hθ⟩ := exists_continuous_arg_lift hK.continuousOn hne
  obtain ⟨a, ha, hamin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hθc.continuousOn
  obtain ⟨b, hb, hbmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one) hθc.continuousOn
  have hosc : 2 * π ≤ θ b - θ a := by
    by_contra hlt
    rw [not_le] at hlt
    set φ := θ b + (2 * π - (θ b - θ a)) / 2 with hφ
    obtain ⟨t, ht, hγt⟩ := hray φ
    have hn : (‖γ.toFun t‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne t ht))
    have hexp : Circle.exp φ = Circle.exp (θ t) := by
      apply Circle.ext
      rw [Circle.coe_exp, Circle.coe_exp]
      apply mul_left_cancel₀ hn
      rw [← hγt, hθ t ht]
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 hexp
    have hta : θ a ≤ θ t := isMinOn_iff.1 hamin t ht
    have htb : θ t ≤ θ b := isMaxOn_iff.1 hbmax t ht
    have h1 : (0 : ℝ) < m := by
      by_contra hc
      have : (m : ℝ) * (2 * π) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) Real.two_pi_pos.le
      linarith
    have h2 : (m : ℝ) < 1 := by
      by_contra hc
      have : 2 * π ≤ (m : ℝ) * (2 * π) := le_mul_of_one_le_left Real.two_pi_pos.le (not_lt.1 hc)
      linarith
    have h1' : (0 : ℤ) < m := by exact_mod_cast h1
    have h2' : m < 1 := by exact_mod_cast h2
    omega
  obtain ⟨Kθ, hKθ⟩ :=
    (locallyLipschitzOn_arg_lift hK hθc hθ hne).exists_lipschitzOnWith_of_compact isCompact_Icc
  have hA := LocallyLipschitzOn.ae_differentiableAt_Ioo γ.locallyLipschitzOn
  have step : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, x ≤ y →
      ‖θ y - θ x‖ₑ ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (‖deriv γ.toFun t‖ / ‖γ.toFun t‖) := by
    intro x hx y hy hxy
    have hsub : uIcc x y ⊆ Icc 0 1 := by
      rw [uIcc_of_le hxy]; exact Icc_subset_Icc hx.1 hy.2
    have hftc : ∫ u in x..y, deriv θ u = θ y - θ x :=
      (hKθ.mono hsub).absolutelyContinuousOnInterval.integral_deriv_eq_sub
    rw [← hftc, intervalIntegral.integral_of_le hxy]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ u in Ioc x y, ‖deriv θ u‖ₑ
        ≤ ∫⁻ u in Ioc x y, ENNReal.ofReal (‖deriv γ.toFun u‖ / ‖γ.toFun u‖) := by
          refine setLIntegral_mono_ae' measurableSet_Ioc ?_
          filter_upwards [hA, compl_mem_ae_iff.2 (measure_singleton (1 : ℝ))] with u hu hu1 huI
          have hu01 : u ∈ Ioo (0 : ℝ) 1 :=
            ⟨hx.1.trans_lt huI.1, lt_of_le_of_ne (huI.2.trans hy.2) hu1⟩
          have hd := hasDerivAt_arg_lift hθc hθ hne hu01 (hu hu01).hasDerivAt
          rw [hd.deriv, ← ofReal_norm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal ((abs_im_le_norm _).trans (norm_div _ _).le)
      _ ≤ ∫⁻ u in Ioc 0 1, ENNReal.ofReal (‖deriv γ.toFun u‖ / ‖γ.toFun u‖) :=
          lintegral_mono_set (Ioc_subset_Ioc hx.1 hy.2)
      _ = ∫⁻ u in Ioo 0 1, ENNReal.ofReal (‖deriv γ.toFun u‖ / ‖γ.toFun u‖) :=
          setLIntegral_congr Ioo_ae_eq_Ioc.symm
  have hab : ENNReal.ofReal (θ b - θ a) ≤ ‖θ b - θ a‖ₑ := by
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  refine (ENNReal.ofReal_le_ofReal hosc).trans (hab.trans ?_)
  rcases le_total a b with h | h
  · exact step a ha b hb h
  · rw [enorm_sub_rev]; exact step b hb a ha h

/-! ### The extremal length of the annulus -/

/-- **Every separating curve of the annulus has `ρ₀`-length at least `1`**, `ρ₀ = 1/(2π|z|)`. -/
theorem one_le_rhoLength_of_mem_separatingCurves {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂)
    {γ : LRCurve} (hγ : γ ∈ separatingCurves (annulus r₁ r₂)) :
    1 ≤ γ.rhoLength ((annulus r₁ r₂).indicator fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖))) := by
  have hray := exists_mem_ray_of_mem_separatingCurves h₁ h₂ hγ
  obtain ⟨⟨K, hK, -⟩, htr, -⟩ := hγ
  have hmemA : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ annulus r₁ r₂ := fun t ht => htr ⟨t, ht, rfl⟩
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ≠ 0 := fun t ht h0 => by
    have h := (hmemA t ht).1
    rw [h0, norm_zero] at h
    linarith
  have hI := two_pi_le_lintegral_norm_deriv_div_norm hK hne hray
  have hlen : γ.rhoLength ((annulus r₁ r₂).indicator fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖)))
      = ENNReal.ofReal (1 / (2 * π)) *
          ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (‖deriv γ.toFun t‖ / ‖γ.toFun t‖) := by
    unfold LRCurve.rhoLength
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have htA := hmemA t (Ioo_subset_Icc_self ht)
    simp only [indicator_of_mem htA]
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / (2 * π * ‖γ.toFun t‖) by positivity),
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / (2 * π) by positivity)]
    congr 1
    ring
  rw [hlen]
  calc (1 : ℝ≥0∞) = ENNReal.ofReal (1 / (2 * π)) * ENNReal.ofReal (2 * π) := by
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / (2 * π) by positivity),
          one_div_mul_cancel Real.two_pi_pos.ne', ENNReal.ofReal_one]
    _ ≤ _ := by gcongr

/-- The density `1/(2π|z|)` on the annulus is measurable. -/
theorem measurable_annulus_density (r₁ r₂ : ℝ) :
    Measurable ((annulus r₁ r₂).indicator fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖))) :=
  (measurable_const.div (measurable_const.mul measurable_norm)).ennreal_ofReal.indicator
    (isOpen_annulus r₁ r₂).measurableSet

/-- The shortest separating curve of the annulus has `ρ₀`-length `1`. -/
theorem iInf_rhoLength_sq_annulus_density {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    ⨅ γ ∈ separatingCurves (annulus r₁ r₂),
        γ.rhoLength ((annulus r₁ r₂).indicator fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖))) ^ 2
      = 1 := by
  refine le_antisymm ?_ (le_iInf₂ fun γ hγ =>
    one_le_pow₀ (one_le_rhoLength_of_mem_separatingCurves h₁ h₂ hγ))
  have hr₁ : r₁ < (r₁ + r₂) / 2 := by linarith
  have hr₂ : (r₁ + r₂) / 2 < r₂ := by linarith
  refine (iInf₂_le _ (circleCurve_mem_separatingCurves h₁ hr₁ hr₂)).trans (le_of_eq ?_)
  rw [circleCurve_rhoLength h₁ hr₁ hr₂, one_pow]

/-- `1 / (ln(r₂/r₁)/2π) = 2π/ln(r₂/r₁)`. -/
theorem one_div_ofReal_log_div_two_pi {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    1 / ENNReal.ofReal (Real.log (r₂ / r₁) / (2 * π))
      = ENNReal.ofReal (2 * π / Real.log (r₂ / r₁)) := by
  have hLpos : 0 < Real.log (r₂ / r₁) :=
    Real.log_pos (by rw [lt_div_iff₀ h₁, one_mul]; exact h₂)
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_div_of_pos (div_pos hLpos Real.two_pi_pos),
    one_div_div]

/-- **The extremal length of the separating curves of an annulus is `2π/ln(r₂/r₁)`.** -/
theorem extremalLength_annulusSeparating {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    extremalLength (separatingCurves (annulus r₁ r₂))
      = ENNReal.ofReal (2 * π / Real.log (r₂ / r₁)) := by
  refine le_antisymm (extremalLength_annulusSeparating_le h₁ h₂) ?_
  have harea : rhoArea ((annulus r₁ r₂).indicator fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖))) univ
      = ENNReal.ofReal (Real.log (r₂ / r₁) / (2 * π)) := by
    rw [rhoArea_indicator_univ _ (isOpen_annulus r₁ r₂).measurableSet,
      ← rhoArea_annulus_density h₁ h₂]
    unfold rhoArea
    refine setLIntegral_congr_fun (isOpen_annulus r₁ r₂).measurableSet fun z hz => ?_
    simp only [indicator_of_mem hz]
  have hlow := le_extremalLengthIn isOpen_univ univ_nonempty (separatingCurves (annulus r₁ r₂))
    (measurable_annulus_density r₁ r₂) (by rw [harea]; exact ENNReal.ofReal_lt_top)
  rw [iInf_rhoLength_sq_annulus_density h₁ h₂, harea, one_div_ofReal_log_div_two_pi h₁ h₂] at hlow
  exact hlow

/-- §4.6: the extremal metric of the separating curves of an annulus is `1/(2π|z|)`. -/
theorem annulus_extremal_metric {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    IsExtremalMetric (annulus r₁ r₂) (separatingCurves (annulus r₁ r₂))
      ((annulus r₁ r₂).indicator fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖))) := by
  have hLpos : 0 < Real.log (r₂ / r₁) :=
    Real.log_pos (by rw [lt_div_iff₀ h₁, one_mul]; exact h₂)
  refine ⟨⟨measurable_annulus_density r₁ r₂, ?_, ?_⟩, ?_⟩
  · rw [rhoArea_annulus_density h₁ h₂]
    exact ENNReal.ofReal_pos.2 (div_pos hLpos Real.two_pi_pos)
  · rw [rhoArea_annulus_density h₁ h₂]
    exact ENNReal.ofReal_lt_top
  · rw [iInf_rhoLength_sq_annulus_density h₁ h₂, rhoArea_annulus_density h₁ h₂,
      one_div_ofReal_log_div_two_pi h₁ h₂, extremalLength_annulusSeparating h₁ h₂]

/-! ### Similar annuli (§2.2)

A conformal map between two annuli carries separating curves onto separating curves, so by
Theorem 3.1 the two annuli have the same extremal length `2π / ln(r₂/r₁)`. The topological input is
elementary for round annuli: thin boundary bands are connected. -/

/-- An annulus `{r₁ < |z| < r₂}` with `0 ≤ r₁` is connected. -/
theorem isPreconnected_annulus {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) : IsPreconnected (annulus r₁ r₂) := by
  have hmap : (fun p : ℝ × ℝ => (p.1 : ℂ) * exp ((p.2 : ℂ) * I)) '' (Ioo r₁ r₂ ×ˢ univ)
      = annulus r₁ r₂ := by
    apply Subset.antisymm
    · rintro _ ⟨⟨ρ, θ⟩, ⟨hρ, -⟩, rfl⟩
      have hn : ‖(ρ : ℂ) * exp ((θ : ℂ) * I)‖ = ρ := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (h₁.trans hρ.1.le)]
      show r₁ < ‖(ρ : ℂ) * exp ((θ : ℂ) * I)‖ ∧ ‖(ρ : ℂ) * exp ((θ : ℂ) * I)‖ < r₂
      rw [hn]
      exact hρ
    · intro z hz
      exact ⟨(‖z‖, arg z), ⟨hz, mem_univ _⟩, Complex.norm_mul_exp_arg_mul_I z⟩
  rw [← hmap]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _
    (Continuous.continuousOn (by fun_prop))

/-- A compact subset of an annulus keeps a positive distance from both boundary circles. -/
theorem exists_pos_band_of_isCompact {r₁ r₂ : ℝ} {K : Set ℂ} (hK : IsCompact K)
    (hKA : K ⊆ annulus r₁ r₂) : ∃ ε > 0, ∀ z ∈ K, r₁ + ε ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ - ε := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun z hz => by simp at hz⟩
  obtain ⟨a, ha, hamin⟩ := hK.exists_isMinOn hne continuous_norm.continuousOn
  obtain ⟨b, hb, hbmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
  have ha' := hKA ha
  have hb' := hKA hb
  have hpos : 0 < min (‖a‖ - r₁) (r₂ - ‖b‖) := lt_min (by linarith [ha'.1]) (by linarith [hb'.2])
  refine ⟨min (‖a‖ - r₁) (r₂ - ‖b‖), hpos, fun z hz => ⟨?_, ?_⟩⟩
  · have := isMinOn_iff.1 hamin z hz
    linarith [min_le_left (‖a‖ - r₁) (r₂ - ‖b‖)]
  · have := isMaxOn_iff.1 hbmax z hz
    linarith [min_le_right (‖a‖ - r₁) (r₂ - ‖b‖)]

/-- A set coming arbitrarily close to the circle `|z| = r` from outside has a closure point
with `|p| ≤ r`. -/
theorem exists_mem_closure_norm_le {S : Set ℂ} {r : ℝ} (hS : ∀ ε > 0, ∃ z ∈ S, ‖z‖ < r + ε) :
    ∃ p ∈ closure S, ‖p‖ ≤ r := by
  have hne : ∀ n : ℕ, (closure S ∩ closedBall (0 : ℂ) (r + 1 / ((n : ℝ) + 1))).Nonempty := by
    intro n
    obtain ⟨z, hz, hzr⟩ := hS (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨z, subset_closure hz, mem_closedBall_zero_iff.2 hzr.le⟩
  obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n : ℕ => closure S ∩ closedBall (0 : ℂ) (r + 1 / ((n : ℝ) + 1)))
    (fun n => inter_subset_inter_right _ (closedBall_subset_closedBall
      ((add_le_add_iff_left r).2 (one_div_le_one_div_of_le (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
        (show (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 by push_cast; linarith)))))
    hne ((isCompact_closedBall _ _).inter_left isClosed_closure)
    (fun n => isClosed_closure.inter isClosed_closedBall)
  rw [mem_iInter] at hp
  refine ⟨p, (hp 0).1, le_of_forall_pos_lt_add fun ε hε => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have h := mem_closedBall_zero_iff.1 (hp n).2
  linarith

/-- A bounded set coming arbitrarily close to the circle `|z| = r` from inside has a closure point
with `r ≤ |q|`. -/
theorem exists_mem_closure_le_norm {S : Set ℂ} {r R : ℝ} (hSR : ∀ z ∈ S, ‖z‖ ≤ R)
    (hS : ∀ ε > 0, ∃ z ∈ S, r - ε < ‖z‖) : ∃ q ∈ closure S, r ≤ ‖q‖ := by
  have hclR : closure S ⊆ closedBall (0 : ℂ) R :=
    closure_minimal (fun z hz => mem_closedBall_zero_iff.2 (hSR z hz)) isClosed_closedBall
  have hne : ∀ n : ℕ, (closure S ∩ {z : ℂ | r - 1 / ((n : ℝ) + 1) ≤ ‖z‖}).Nonempty := by
    intro n
    obtain ⟨z, hz, hzr⟩ := hS (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨z, subset_closure hz, hzr.le⟩
  obtain ⟨q, hq⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n : ℕ => closure S ∩ {z : ℂ | r - 1 / ((n : ℝ) + 1) ≤ ‖z‖})
    (fun n => inter_subset_inter_right _ fun z (hz : r - 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ ‖z‖) =>
      show r - 1 / ((n : ℝ) + 1) ≤ ‖z‖ from
        le_trans (sub_le_sub_left (one_div_le_one_div_of_le (by positivity)
          (by push_cast; linarith)) r) hz)
    hne ((isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
      (isClosed_closure.inter (isClosed_le continuous_const continuous_norm))
      (inter_subset_left.trans hclR))
    (fun n => isClosed_closure.inter (isClosed_le continuous_const continuous_norm))
  rw [mem_iInter] at hq
  refine ⟨q, (hq 0).1, le_of_forall_pos_lt_add fun ε hε => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have h : r - 1 / ((n : ℝ) + 1) ≤ ‖q‖ := (hq n).2
  linarith

/-- **T2.** If a connected `S ⊆ A ∖ K` comes arbitrarily close to both boundary circles of the
annulus `A`, then `0` and `∞` lie in the same component of `ℂ̄ ∖ K`. -/
theorem connectedComponentIn_eq_of_reaches {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂)
    {K S : Set ℂ} (hK : K ⊆ annulus r₁ r₂) (hS : IsPreconnected S) (hSA : S ⊆ annulus r₁ r₂)
    (hSK : Disjoint S K) (hin : ∀ ε > 0, ∃ z ∈ S, ‖z‖ < r₁ + ε)
    (hout : ∀ ε > 0, ∃ z ∈ S, r₂ - ε < ‖z‖) :
    connectedComponentIn (toExt K)ᶜ ((0 : ℂ) : ExtPlane)
      = connectedComponentIn (toExt K)ᶜ extInf := by
  obtain ⟨p, hpS, hp⟩ := exists_mem_closure_norm_le hin
  obtain ⟨q, hqS, hq⟩ := exists_mem_closure_le_norm (fun z hz => (hSA hz).2.le) hout
  have hZ : IsPreconnected (insert p (insert q S)) :=
    hS.subset_closure ((subset_insert _ _).trans (subset_insert _ _))
      (insert_subset_iff.2 ⟨hpS, insert_subset_iff.2 ⟨hqS, subset_closure⟩⟩)
  have hnotK : ∀ z ∈ insert p (insert q S), z ∉ K := by
    rintro z (rfl | rfl | hz) hzK
    · exact absurd (hK hzK).1 (not_lt.2 hp)
    · exact absurd (hK hzK).2 (not_lt.2 hq)
    · exact Set.disjoint_left.1 hSK hz hzK
  have hcompl : ∀ {X : Set ℂ}, (∀ z ∈ X, z ∉ K) → toExt X ⊆ (toExt K)ᶜ := by
    rintro X hX _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    exact hX z hz (OnePoint.coe_injective hwz ▸ hw)
  have hXin : toExt (closedBall (0 : ℂ) r₁) ⊆ (toExt K)ᶜ :=
    hcompl fun z hz hzK => absurd (hK hzK).1 (not_lt.2 (mem_closedBall_zero_iff.1 hz))
  have hXout : toExt {z : ℂ | r₂ ≤ ‖z‖} ∪ {extInf} ⊆ (toExt K)ᶜ := by
    refine union_subset (hcompl fun z hz hzK => absurd (hK hzK).2 (not_lt.2 hz)) ?_
    rintro _ rfl
    exact extInf_mem_compl_toExt K
  have h1 : IsPreconnected (toExt (closedBall (0 : ℂ) r₁) ∪ toExt (insert p (insert q S))) :=
    IsPreconnected.union (p : ExtPlane) ⟨p, mem_closedBall_zero_iff.2 hp, rfl⟩
      ⟨p, mem_insert _ _, rfl⟩ (isPreconnected_toExt_closedBall r₁)
      (hZ.image _ OnePoint.continuous_coe.continuousOn)
  have hU : IsPreconnected (toExt (closedBall (0 : ℂ) r₁) ∪ toExt (insert p (insert q S))
      ∪ (toExt {z : ℂ | r₂ ≤ ‖z‖} ∪ {extInf})) :=
    IsPreconnected.union (q : ExtPlane) (Or.inr ⟨q, mem_insert_of_mem _ (mem_insert _ _), rfl⟩)
      (Or.inl ⟨q, hq, rfl⟩) h1 (isPreconnected_toExt_normGE_insert (h₁.trans h₂).le)
  have hsub : toExt (closedBall (0 : ℂ) r₁) ∪ toExt (insert p (insert q S))
      ∪ (toExt {z : ℂ | r₂ ≤ ‖z‖} ∪ {extInf}) ⊆ (toExt K)ᶜ :=
    union_subset (union_subset hXin (hcompl hnotK)) hXout
  exact connectedComponentIn_eq (hU.subset_connectedComponentIn
    (Or.inl (Or.inl ⟨0, mem_closedBall_self h₁.le, rfl⟩)) hsub (Or.inr (Or.inr rfl)))

/-- **T3.** A homeomorphism between two annuli (given with its inverse) preserves "comes arbitrarily
close to both boundary circles". -/
theorem reaches_both_image {r₁ r₂ r₁' r₂' : ℝ} (h₁ : 0 < r₁) (h₂' : r₁' < r₂')
    {f g : ℂ → ℂ} (hf : ContinuousOn f (annulus r₁ r₂)) (hg : ContinuousOn g (annulus r₁' r₂'))
    (hfA : MapsTo f (annulus r₁ r₂) (annulus r₁' r₂'))
    (hgA : MapsTo g (annulus r₁' r₂') (annulus r₁ r₂))
    (hfg : ∀ w ∈ annulus r₁' r₂', f (g w) = w) (hgf : ∀ z ∈ annulus r₁ r₂, g (f z) = z)
    {S : Set ℂ} (hSA : S ⊆ annulus r₁' r₂') (hin : ∀ ε > 0, ∃ w ∈ S, ‖w‖ < r₁' + ε)
    (hout : ∀ ε > 0, ∃ w ∈ S, r₂' - ε < ‖w‖) :
    (∀ ε > 0, ∃ z ∈ g '' S, ‖z‖ < r₁ + ε) ∧ (∀ ε > 0, ∃ z ∈ g '' S, r₂ - ε < ‖z‖) := by
  set ε' := (r₂' - r₁') / 3 with hε'
  have hε'0 : 0 < ε' := by rw [hε']; linarith
  -- the middle band of `A'` and its (compact) image under `g`
  set M' := {w : ℂ | r₁' + ε' ≤ ‖w‖ ∧ ‖w‖ ≤ r₂' - ε'} with hM'
  have hM'c : IsCompact M' :=
    (isCompact_closedBall (0 : ℂ) (r₂' - ε')).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
      fun w hw => mem_closedBall_zero_iff.2 hw.2
  have hM'A : M' ⊆ annulus r₁' r₂' := fun w hw =>
    ⟨by linarith [hw.1], by linarith [hw.2]⟩
  obtain ⟨ε₁, hε₁, hband⟩ := exists_pos_band_of_isCompact (hM'c.image_of_continuousOn
    (hg.mono hM'A)) (image_subset_iff.2 fun w hw => hgA (hM'A hw))
  -- a thin band of `A` is mapped by `f` into a thin band of `A'` on one side
  have hside : ∀ T ⊆ annulus r₁ r₂, IsPreconnected T → (∀ z ∈ T, ‖z‖ < r₁ + ε₁ ∨ r₂ - ε₁ < ‖z‖) →
      f '' T ⊆ annulus r₁' (r₁' + ε') ∨ f '' T ⊆ annulus (r₂' - ε') r₂' := by
    intro T hTA hT hTb
    refine (hT.image f (hf.mono hTA)).subset_or_subset (isOpen_annulus _ _) (isOpen_annulus _ _)
      ?_ ?_
    · rw [Set.disjoint_left]
      intro w hw1 hw2
      linarith [hw1.2, hw2.1]
    · rintro _ ⟨z, hz, rfl⟩
      have hfz := hfA (hTA hz)
      by_contra hno
      have hmid : f z ∈ M' := by
        refine ⟨?_, ?_⟩
        · by_contra h
          exact hno (Or.inl ⟨hfz.1, not_le.1 h⟩)
        · by_contra h
          exact hno (Or.inr ⟨not_le.1 h, hfz.2⟩)
      have hgz := hband (g (f z)) (mem_image_of_mem g hmid)
      rw [hgf z (hTA hz)] at hgz
      rcases hTb z hz with h | h <;> linarith [hgz.1, hgz.2]
  have hbandin : f '' annulus r₁ (min (r₁ + ε₁) r₂) ⊆ annulus r₁' (r₁' + ε') ∨
      f '' annulus r₁ (min (r₁ + ε₁) r₂) ⊆ annulus (r₂' - ε') r₂' :=
    hside _ (fun z hz => ⟨hz.1, hz.2.trans_le (min_le_right _ _)⟩) (isPreconnected_annulus h₁.le)
      fun z hz => Or.inl (hz.2.trans_le (min_le_left _ _))
  have hbandout : f '' annulus (max (r₂ - ε₁) r₁) r₂ ⊆ annulus r₁' (r₁' + ε') ∨
      f '' annulus (max (r₂ - ε₁) r₁) r₂ ⊆ annulus (r₂' - ε') r₂' :=
    hside _ (fun z hz => ⟨(le_max_right _ _).trans_lt hz.1, hz.2⟩)
      (isPreconnected_annulus (h₁.le.trans (le_max_right _ _)))
      fun z hz => Or.inr ((le_max_left _ _).trans_lt hz.1)
  -- points of `A'` near its boundary come from points of `A` near its boundary
  have hleave : ∀ ε₂ > 0, ∃ δ > 0, ∀ w ∈ annulus r₁' r₂', (‖w‖ < r₁' + δ ∨ r₂' - δ < ‖w‖) →
      ‖g w‖ < r₁ + ε₂ ∨ r₂ - ε₂ < ‖g w‖ := by
    intro ε₂ hε₂
    set M := {z : ℂ | r₁ + ε₂ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ - ε₂} with hM
    have hMc : IsCompact M :=
      (isCompact_closedBall (0 : ℂ) (r₂ - ε₂)).of_isClosed_subset
        ((isClosed_le continuous_const continuous_norm).inter
          (isClosed_le continuous_norm continuous_const))
        fun z hz => mem_closedBall_zero_iff.2 hz.2
    have hMA : M ⊆ annulus r₁ r₂ := fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩
    obtain ⟨δ, hδ, hδband⟩ := exists_pos_band_of_isCompact (hMc.image_of_continuousOn
      (hf.mono hMA)) (image_subset_iff.2 fun z hz => hfA (hMA hz))
    refine ⟨δ, hδ, fun w hw hwb => ?_⟩
    by_contra hno
    have hgM : g w ∈ M := ⟨by by_contra h; exact hno (Or.inl (not_le.1 h)),
      by by_contra h; exact hno (Or.inr (not_le.1 h))⟩
    have h := hδband (f (g w)) (mem_image_of_mem f hgM)
    rw [hfg w hw] at h
    rcases hwb with hwb | hwb <;> linarith [h.1, h.2]
  constructor
  · intro ε hε
    by_contra hno
    push Not at hno
    obtain ⟨δ, hδ, hδleave⟩ := hleave (min ε ε₁) (lt_min hε hε₁)
    have hfar : ∀ w ∈ S, (‖w‖ < r₁' + δ ∨ r₂' - δ < ‖w‖) →
        g w ∈ annulus (max (r₂ - ε₁) r₁) r₂ := by
      intro w hw hwb
      have hgw := hgA (hSA hw)
      rcases hδleave w (hSA hw) hwb with h | h
      · have := hno (g w) (mem_image_of_mem g hw)
        linarith [min_le_left ε ε₁]
      · exact ⟨max_lt (by linarith [min_le_right ε ε₁]) hgw.1, hgw.2⟩
    rcases hbandout with hb | hb
    · obtain ⟨w, hw, hwr⟩ := hout (min δ ε') (lt_min hδ hε'0)
      have hw' := hb (mem_image_of_mem f (hfar w hw (Or.inr (by linarith [min_le_left δ ε']))))
      rw [hfg w (hSA hw)] at hw'
      linarith [hw'.2, min_le_right δ ε']
    · obtain ⟨w, hw, hwr⟩ := hin (min δ ε') (lt_min hδ hε'0)
      have hw' := hb (mem_image_of_mem f (hfar w hw (Or.inl (by linarith [min_le_left δ ε']))))
      rw [hfg w (hSA hw)] at hw'
      linarith [hw'.1, min_le_right δ ε']
  · intro ε hε
    by_contra hno
    push Not at hno
    obtain ⟨δ, hδ, hδleave⟩ := hleave (min ε ε₁) (lt_min hε hε₁)
    have hfar : ∀ w ∈ S, (‖w‖ < r₁' + δ ∨ r₂' - δ < ‖w‖) →
        g w ∈ annulus r₁ (min (r₁ + ε₁) r₂) := by
      intro w hw hwb
      have hgw := hgA (hSA hw)
      rcases hδleave w (hSA hw) hwb with h | h
      · exact ⟨hgw.1, lt_min (by linarith [min_le_right ε ε₁]) hgw.2⟩
      · have := hno (g w) (mem_image_of_mem g hw)
        linarith [min_le_left ε ε₁]
    rcases hbandin with hb | hb
    · obtain ⟨w, hw, hwr⟩ := hout (min δ ε') (lt_min hδ hε'0)
      have hw' := hb (mem_image_of_mem f (hfar w hw (Or.inr (by linarith [min_le_left δ ε']))))
      rw [hfg w (hSA hw)] at hw'
      linarith [hw'.2, min_le_right δ ε']
    · obtain ⟨w, hw, hwr⟩ := hin (min δ ε') (lt_min hδ hε'0)
      have hw' := hb (mem_image_of_mem f (hfar w hw (Or.inl (by linarith [min_le_left δ ε']))))
      rw [hfg w (hSA hw)] at hw'
      linarith [hw'.1, min_le_right δ ε']

/-- **T1.** If a compact `K ⊆ A` does not separate `0` from `∞`, a connected piece of `A ∖ K`
comes arbitrarily close to both boundary circles. -/
theorem exists_reaches_of_connectedComponentIn_eq {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂)
    {K : Set ℂ} (hKc : IsCompact K) (hKA : K ⊆ annulus r₁ r₂)
    (heq : connectedComponentIn (toExt K)ᶜ ((0 : ℂ) : ExtPlane)
      = connectedComponentIn (toExt K)ᶜ extInf) :
    ∃ S ⊆ annulus r₁ r₂, IsPreconnected S ∧ Disjoint S K ∧
      (∀ ε > 0, ∃ z ∈ S, ‖z‖ < r₁ + ε) ∧ (∀ ε > 0, ∃ z ∈ S, r₂ - ε < ‖z‖) := by
  have h0K : (0 : ℂ) ∉ K := fun h => by
    have := (hKA h).1
    rw [norm_zero] at this
    linarith
  set W := connectedComponentIn Kᶜ (0 : ℂ) with hW
  have hWo : IsOpen W := hKc.isClosed.isOpen_compl.connectedComponentIn
  have h0W : (0 : ℂ) ∈ W := mem_connectedComponentIn h0K
  have hWK : W ⊆ Kᶜ := connectedComponentIn_subset _ _
  -- step 1: `W` is unbounded, otherwise `toExt W` would split the component of `0` in `ℂ̄ ∖ K`
  obtain ⟨p, hpW, hp⟩ : ∃ p ∈ W, r₂ < ‖p‖ := by
    by_contra hno
    push Not at hno
    set C := connectedComponentIn (toExt K)ᶜ ((0 : ℂ) : ExtPlane)
    have hinfC : extInf ∈ C := by
      rw [heq]; exact mem_connectedComponentIn (extInf_mem_compl_toExt K)
    have hclosed : IsClosed (toExt (closedBall (0 : ℂ) r₂)) :=
      ((isCompact_closedBall (0 : ℂ) r₂).image OnePoint.continuous_coe).isClosed
    have hcl : closure (toExt W) ⊆ toExt (closedBall (0 : ℂ) r₂) :=
      closure_minimal (image_mono fun z hz => mem_closedBall_zero_iff.2 (hno z hz)) hclosed
    have hCU : C ⊆ toExt W ∪ (closure (toExt W))ᶜ := by
      intro x hxC
      by_cases hx : x ∈ closure (toExt W)
      · left
        obtain ⟨z, -, rfl⟩ := hcl hx
        have hzcl : z ∈ closure W := by
          rw [OnePoint.isOpenEmbedding_coe.isInducing.closure_eq_preimage_closure_image]
          exact hx
        have hzK : z ∉ K := fun hzK =>
          connectedComponentIn_subset _ _ hxC ⟨z, hzK, rfl⟩
        have hpre : IsPreconnected (insert z W) :=
          isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
            (insert_subset_iff.2 ⟨hzcl, subset_closure⟩)
        have hzW : z ∈ W :=
          hpre.subset_connectedComponentIn (mem_insert_of_mem _ h0W)
            (insert_subset_iff.2 ⟨hzK, hWK⟩) (mem_insert _ _)
        exact ⟨z, hzW, rfl⟩
      · exact Or.inr hx
    have hsub := isPreconnected_connectedComponentIn.subset_left_of_subset_union
      (OnePoint.isOpenEmbedding_coe.isOpenMap _ hWo) isClosed_closure.isOpen_compl
      (Set.disjoint_left.2 fun x hx hx' => hx' (subset_closure hx)) hCU
      ⟨_, mem_connectedComponentIn (by
        rintro ⟨w, hw, hw0⟩
        exact h0K (OnePoint.coe_injective hw0 ▸ hw)), ⟨0, h0W, rfl⟩⟩
    obtain ⟨w, -, hw⟩ := hsub hinfC
    exact OnePoint.coe_ne_infty w hw
  -- step 2: a path in `W` from `0` to `p`, cut between its last visit to `|z| ≤ r₁` and its first
  -- visit to `|z| ≥ r₂`
  have hWpc : IsPathConnected W :=
    (hWo.isConnected_iff_isPathConnected).1 ⟨⟨0, h0W⟩, isPreconnected_connectedComponentIn⟩
  set γp := (hWpc.joinedIn 0 h0W p hpW).somePath with hγp
  set φ : ℝ → ℂ := fun t => γp (projIcc 0 1 zero_le_one t) with hφ
  have hφc : Continuous φ := γp.continuous.comp continuous_projIcc
  have hφW : ∀ t, φ t ∈ W := fun t => (hWpc.joinedIn 0 h0W p hpW).somePath_mem _
  have hφ0 : φ 0 = 0 := by
    simp only [hφ, projIcc_left]; exact γp.source
  have hφ1 : φ 1 = p := by
    simp only [hφ, projIcc_right]; exact γp.target
  set T := {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ r₂ ≤ ‖φ t‖} with hT
  have hTc : IsClosed T := isClosed_Icc.inter (isClosed_le continuous_const hφc.norm)
  have hTne : T.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [hφ1]; exact hp.le⟩
  have hTbdd : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  set u := sInf T with hu
  have huT : u ∈ T := hTc.csInf_mem hTne hTbdd
  have hbefore : ∀ t, 0 ≤ t → t < u → ‖φ t‖ < r₂ := by
    intro t ht0 htu
    by_contra h
    exact absurd (csInf_le hTbdd ⟨⟨ht0, htu.le.trans huT.1.2⟩, not_lt.1 h⟩) (not_le.2 htu)
  have hu0 : 0 < u := by
    rcases huT.1.1.eq_or_lt with h | h
    · have := huT.2
      rw [← h, hφ0, norm_zero] at this
      linarith
    · exact h
  set T' := {t : ℝ | t ∈ Icc (0 : ℝ) u ∧ ‖φ t‖ ≤ r₁} with hT'
  have hT'c : IsClosed T' := isClosed_Icc.inter (isClosed_le hφc.norm continuous_const)
  have hT'ne : T'.Nonempty := ⟨0, ⟨le_rfl, hu0.le⟩, by rw [hφ0, norm_zero]; exact h₁.le⟩
  have hT'bdd : BddAbove T' := ⟨u, fun t ht => ht.1.2⟩
  set s := sSup T' with hs
  have hsT' : s ∈ T' := hT'c.csSup_mem hT'ne hT'bdd
  have hafter : ∀ t, s < t → t ≤ u → r₁ < ‖φ t‖ := by
    intro t hst htu
    by_contra h
    exact absurd (le_csSup hT'bdd ⟨⟨hsT'.1.1.trans hst.le, htu⟩, not_lt.1 h⟩) (not_le.2 hst)
  have hsu : s < u := by
    rcases hsT'.1.2.eq_or_lt with h | h
    · have h1 := hsT'.2
      have h2 := huT.2
      rw [h] at h1
      linarith
    · exact h
  refine ⟨φ '' Ioo s u, ?_, isPreconnected_Ioo.image φ hφc.continuousOn, ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨hafter t ht.1 ht.2.le, hbefore t (hsT'.1.1.trans ht.1.le) ht.2⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨t, -, rfl⟩
    exact hWK (hφW t)
  · intro ε hε
    have hev : ∀ᶠ t in 𝓝 s, ‖φ t‖ < ‖φ s‖ + ε :=
      (hφc.norm.tendsto s).eventually_lt_const (lt_add_of_pos_right _ hε)
    obtain ⟨t, ht1, ht2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT hsu)).exists
    exact ⟨φ t, mem_image_of_mem φ ht2, by linarith [hsT'.2]⟩
  · intro ε hε
    have hev : ∀ᶠ t in 𝓝 u, ‖φ u‖ - ε < ‖φ t‖ :=
      (hφc.norm.tendsto u).eventually_const_lt (sub_lt_self _ hε)
    obtain ⟨t, ht1, ht2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT hsu)).exists
    exact ⟨φ t, mem_image_of_mem φ ht2, by linarith [huT.2]⟩

/-- For a set `K` in the annulus, separating `0` from `∞` means separating the two components of
`ℂ̄ ∖ A`. -/
theorem separates_compl_of_connectedComponentIn_ne {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂)
    {K : Set ℂ} (hKA : K ⊆ annulus r₁ r₂)
    (hne : connectedComponentIn (toExt K)ᶜ ((0 : ℂ) : ExtPlane)
      ≠ connectedComponentIn (toExt K)ᶜ extInf) :
    ∀ x ∈ (toExt (annulus r₁ r₂))ᶜ, ∀ y ∈ (toExt (annulus r₁ r₂))ᶜ,
      connectedComponentIn (toExt (annulus r₁ r₂))ᶜ x
          ≠ connectedComponentIn (toExt (annulus r₁ r₂))ᶜ y →
        connectedComponentIn (toExt K)ᶜ x ≠ connectedComponentIn (toExt K)ᶜ y := by
  have hKin : IsPreconnected (toExt (closedBall (0 : ℂ) r₁)) := isPreconnected_toExt_closedBall r₁
  have hKout : IsPreconnected (toExt {z : ℂ | r₂ ≤ ‖z‖} ∪ {extInf}) :=
    isPreconnected_toExt_normGE_insert (h₁.trans h₂).le
  have hKinA : toExt (closedBall (0 : ℂ) r₁) ⊆ (toExt (annulus r₁ r₂))ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    have hwz' : w = z := OnePoint.coe_injective hwz
    rw [hwz'] at hw
    rw [mem_closedBall_zero_iff] at hz
    exact absurd hw.1 (not_lt.2 hz)
  have hKoutA : toExt {z : ℂ | r₂ ≤ ‖z‖} ∪ {extInf} ⊆ (toExt (annulus r₁ r₂))ᶜ := by
    rintro p (⟨z, hz, rfl⟩ | hinf) hA
    · obtain ⟨w, hw, hwz⟩ := hA
      have hwz' : w = z := OnePoint.coe_injective hwz
      rw [hwz'] at hw
      exact absurd hw.2 (not_lt.2 hz)
    · rw [mem_singleton_iff] at hinf
      subst hinf
      obtain ⟨w, -, hw⟩ := hA
      exact OnePoint.coe_ne_infty w hw
  have hAK : (toExt (annulus r₁ r₂))ᶜ ⊆ (toExt K)ᶜ := compl_subset_compl.2 (image_mono hKA)
  have same : ∀ {S F : Set ExtPlane}, IsPreconnected S → S ⊆ F →
      ∀ {a b : ExtPlane}, a ∈ S → b ∈ S → connectedComponentIn F a = connectedComponentIn F b :=
    fun hS hSF _ _ ha hb => connectedComponentIn_eq (hS.subset_connectedComponentIn ha hSF hb)
  have h0in : ((0 : ℂ) : ExtPlane) ∈ toExt (closedBall (0 : ℂ) r₁) :=
    ⟨0, mem_closedBall_self h₁.le, rfl⟩
  have hinfout : extInf ∈ toExt {z : ℂ | r₂ ≤ ‖z‖} ∪ {extInf} := Or.inr (mem_singleton _)
  intro x hx y hy hxy
  rcases compl_toExt_annulus_subset hx with hxi | hxo <;>
    rcases compl_toExt_annulus_subset hy with hyi | hyo
  · exact absurd (same hKin hKinA hxi hyi) hxy
  · rw [same hKin (hKinA.trans hAK) hxi h0in, same hKout (hKoutA.trans hAK) hyo hinfout]
    exact hne
  · rw [same hKout (hKoutA.trans hAK) hxo hinfout, same hKin (hKinA.trans hAK) hyi h0in]
    exact hne.symm
  · exact absurd (same hKout hKoutA hxo hyo) hxy

/-- **T4 (one direction).** A conformal map between two annuli, given with its inverse, carries a
separating curve to a separating curve. -/
theorem exists_image_mem_separatingCurves_annulus {r₁ r₂ r₁' r₂' : ℝ} (h₁ : 0 < r₁)
    (h₂ : r₁ < r₂) (h₁' : 0 < r₁') (h₂' : r₁' < r₂') {f g : ℂ → ℂ}
    (hf : IsConformalOnto f (annulus r₁ r₂) (annulus r₁' r₂'))
    (hg : IsConformalOnto g (annulus r₁' r₂') (annulus r₁ r₂))
    (hfg : ∀ w ∈ annulus r₁' r₂', f (g w) = w) (hgf : ∀ z ∈ annulus r₁ r₂, g (f z) = z)
    {γ : LRCurve} (hγ : γ ∈ separatingCurves (annulus r₁ r₂)) :
    ∃ γ' ∈ separatingCurves (annulus r₁' r₂'), EqOn γ'.toFun (f ∘ γ.toFun) (Ioo 0 1) := by
  obtain ⟨⟨K, hK, hK01⟩, htr, hsep⟩ := hγ
  have hU := isOpen_annulus r₁ r₂
  have hmaps : MapsTo γ.toFun (Icc 0 1) (annulus r₁ r₂) := fun t ht => htr ⟨t, ht, rfl⟩
  have hfA : MapsTo f (annulus r₁ r₂) (annulus r₁' r₂') := fun z hz => by
    rw [← hf.2.2]; exact mem_image_of_mem f hz
  have hgA : MapsTo g (annulus r₁' r₂') (annulus r₁ r₂) := fun w hw => by
    rw [← hg.2.2]; exact mem_image_of_mem g hw
  have hloc : LocallyLipschitzOn (Icc (0 : ℝ) 1) (f ∘ γ.toFun) := by
    intro t ht
    have hcd : ContDiffAt ℂ 1 f (γ.toFun t) :=
      (hf.1.contDiffOn (n := 1) hU).contDiffAt (hU.mem_nhds (hmaps ht))
    obtain ⟨K₂, V₂, hV₂, hK₂⟩ := hcd.exists_lipschitzOnWith
    exact ⟨K₂ * K, Icc 0 1 ∩ γ.toFun ⁻¹' V₂,
      inter_mem self_mem_nhdsWithin (hK.continuousOn t ht hV₂),
      hK₂.comp (hK.mono inter_subset_left) fun x hx => hx.2⟩
  obtain ⟨K', hK'⟩ := hloc.exists_lipschitzOnWith_of_compact isCompact_Icc
  let γ' : LRCurve := ⟨f ∘ γ.toFun, locallyLipschitzOn_comp_of_differentiableOn hU hf.1 isOpen_Ioo
    γ.locallyLipschitzOn (hmaps.mono_left Ioo_subset_Icc_self)⟩
  have htr' : γ'.closedTrace = f '' γ.closedTrace := by
    show (f ∘ γ.toFun) '' Icc 0 1 = f '' (γ.toFun '' Icc 0 1)
    exact image_comp f γ.toFun _
  have htrA' : γ'.closedTrace ⊆ annulus r₁' r₂' := by
    rw [htr']; exact image_subset_iff.2 fun z hz => hfA (htr hz)
  refine ⟨γ', ⟨⟨K', hK', by show f (γ.toFun 0) = f (γ.toFun 1); rw [hK01]⟩, htrA', ?_⟩,
    fun t _ => rfl⟩
  refine separates_compl_of_connectedComponentIn_ne h₁' h₂' htrA' fun heq => ?_
  have hKc : IsCompact γ'.closedTrace := isCompact_Icc.image_of_continuousOn hK'.continuousOn
  obtain ⟨S, hSA, hS, hSK, hin, hout⟩ :=
    exists_reaches_of_connectedComponentIn_eq h₁' h₂' hKc htrA' heq
  obtain ⟨hin', hout'⟩ := reaches_both_image h₁ h₂' hf.1.continuousOn hg.1.continuousOn hfA hgA
    hfg hgf hSA hin hout
  have hdisj : Disjoint (g '' S) γ.closedTrace := by
    rw [Set.disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ hgw
    refine Set.disjoint_left.1 hSK hw ?_
    rw [htr']
    exact ⟨g w, hgw, hfg w (hSA hw)⟩
  exact hsep _ (zero_mem_compl_toExt_annulus h₁) _ (extInf_mem_compl_toExt _)
    (connectedComponentIn_compl_toExt_annulus_ne h₁ h₂)
    (connectedComponentIn_eq_of_reaches h₁ h₂ htr (hS.image g (hg.1.continuousOn.mono hSA))
      (image_subset_iff.2 fun w hw => hgA (hSA hw)) hdisj hin' hout')

/-- **A conformal map between two annuli carries the separating curves onto the separating
curves.** -/
theorem isCurveImage_separatingCurves_annulus {r₁ r₂ r₁' r₂' : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂)
    (h₁' : 0 < r₁') (h₂' : r₁' < r₂') {f : ℂ → ℂ}
    (hf : IsConformalOnto f (annulus r₁ r₂) (annulus r₁' r₂')) :
    IsCurveImage f (separatingCurves (annulus r₁ r₂)) (separatingCurves (annulus r₁' r₂')) := by
  have hg := hf.symm (isOpen_annulus r₁ r₂)
  have hfg : ∀ w ∈ annulus r₁' r₂', f (Function.invFunOn f (annulus r₁ r₂) w) = w := fun w hw =>
    Function.invFunOn_eq (show w ∈ f '' annulus r₁ r₂ by rw [hf.2.2]; exact hw)
  have hgf : ∀ z ∈ annulus r₁ r₂, Function.invFunOn f (annulus r₁ r₂) (f z) = z := fun z hz =>
    hf.2.1.leftInvOn_invFunOn hz
  refine ⟨fun γ hγ => exists_image_mem_separatingCurves_annulus h₁ h₂ h₁' h₂' hf hg hfg hgf hγ,
    fun γ' hγ' => ?_⟩
  obtain ⟨γ, hγ, heq⟩ :=
    exists_image_mem_separatingCurves_annulus h₁' h₂' h₁ h₂ hg hf hgf hfg hγ'
  refine ⟨γ, hγ, fun t ht => ?_⟩
  have hγ't : γ'.toFun t ∈ annulus r₁' r₂' := hγ'.2.1 ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  simp only [Function.comp_apply, heq ht, hfg _ hγ't]

/-- §2.2: two annuli are conformally equivalent iff they are similar, `r₂/r₁ = r₂'/r₁'`.

The book leaves this to the reader ("by analytic continuation, as for rectangles").  It is proved
here, after §4.6, from the conformal invariance of extremal length (Theorem 3.1) and the extremal
length `2π / ln(r₂/r₁)` of the separating curves of an annulus — which is why this statement (and
`dcModulus_eq_of_equiv`, `dcModulus_annulus`, which use it) live in this file rather than in S02. -/
theorem annulus_conformallyEquivalent_iff {r₁ r₂ r₁' r₂' : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂)
    (h₁' : 0 < r₁') (h₂' : r₁' < r₂') :
    ConformallyEquivalent (annulus r₁ r₂) (annulus r₁' r₂') ↔ r₂ / r₁ = r₂' / r₁' := by
  have hL : 0 < Real.log (r₂ / r₁) := Real.log_pos (by rw [lt_div_iff₀ h₁, one_mul]; exact h₂)
  have hL' : 0 < Real.log (r₂' / r₁') :=
    Real.log_pos (by rw [lt_div_iff₀ h₁', one_mul]; exact h₂')
  constructor
  · rintro ⟨f, hf⟩
    have hΓ : ∀ γ ∈ separatingCurves (annulus r₁ r₂), γ.trace ⊆ annulus r₁ r₂ := fun γ hγ =>
      (image_mono Ioo_subset_Icc_self).trans hγ.2.1
    have h := thm3_1_conformal_invariance (isOpen_annulus r₁ r₂) hf hΓ
      (isCurveImage_separatingCurves_annulus h₁ h₂ h₁' h₂' hf)
    rw [extremalLength_annulusSeparating h₁ h₂, extremalLength_annulusSeparating h₁' h₂',
      ENNReal.ofReal_eq_ofReal_iff (div_pos Real.two_pi_pos hL').le
        (div_pos Real.two_pi_pos hL).le] at h
    have hmul := (div_eq_div_iff hL'.ne' hL.ne').1 h
    have hlog : Real.log (r₂ / r₁) = Real.log (r₂' / r₁') :=
      mul_left_cancel₀ Real.two_pi_pos.ne' hmul
    exact Real.log_injOn_pos (mem_Ioi.2 (div_pos (h₁.trans h₂) h₁))
      (mem_Ioi.2 (div_pos (h₁'.trans h₂') h₁')) hlog
  · intro hr
    set c : ℝ := r₁' / r₁ with hc
    have hc0 : 0 < c := div_pos h₁' h₁
    have hcr₁ : c * r₁ = r₁' := by rw [hc]; field_simp
    have hcr₂ : c * r₂ = r₂' := by
      rw [div_eq_div_iff h₁.ne' h₁'.ne'] at hr
      rw [hc, div_mul_eq_mul_div, div_eq_iff h₁.ne']
      linear_combination hr
    refine ⟨fun z => (c : ℂ) * z, (differentiable_id.const_mul _).differentiableOn,
      fun z _ w _ h => mul_left_cancel₀ (ofReal_ne_zero.2 hc0.ne') h, ?_⟩
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hn : ‖(c : ℂ) * z‖ = c * ‖z‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
      show r₁' < ‖(c : ℂ) * z‖ ∧ ‖(c : ℂ) * z‖ < r₂'
      rw [hn, ← hcr₁, ← hcr₂]
      exact ⟨mul_lt_mul_of_pos_left hz.1 hc0, mul_lt_mul_of_pos_left hz.2 hc0⟩
    · intro hw
      refine ⟨((c⁻¹ : ℝ) : ℂ) * w, ?_, ?_⟩
      · have hn : ‖((c⁻¹ : ℝ) : ℂ) * w‖ = c⁻¹ * ‖w‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc0)]
        show r₁ < ‖((c⁻¹ : ℝ) : ℂ) * w‖ ∧ ‖((c⁻¹ : ℝ) : ℂ) * w‖ < r₂
        rw [hn]
        obtain ⟨hw1, hw2⟩ := hw
        constructor
        · rw [lt_inv_mul_iff₀ hc0, hcr₁]; exact hw1
        · rw [inv_mul_lt_iff₀ hc0, hcr₂]; exact hw2
      · show (c : ℂ) * (((c⁻¹ : ℝ) : ℂ) * w) = w
        rw [← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ hc0.ne', ofReal_one, one_mul]

/-- The modulus of a (open) domain conformally equivalent to the annulus `{r₁ < |z| < r₂}`: any two
annuli equivalent to `B` are equivalent to each other, hence similar, so every value in the
supremum defining `M(B)` equals `ln (r₂/r₁)`. -/
theorem dcModulus_eq_of_equiv {B : Set ℂ} (hB : IsOpen B) {r₁ r₂ : ℝ} (h₁ : 0 < r₁)
    (h₂ : r₁ < r₂) (h : ConformallyEquivalent B (annulus r₁ r₂)) :
    dcModulus B = ENNReal.ofReal (Real.log (r₂ / r₁)) := by
  unfold dcModulus
  rw [if_pos ⟨r₁, r₂, h₁, h₂, h⟩]
  refine le_antisymm (iSup₂_le fun r₁' r₂' => iSup_le fun hr => ?_)
    (le_iSup₂_of_le r₁ r₂ (le_iSup_of_le ⟨h₁, h₂, h⟩ le_rfl))
  obtain ⟨h₁', h₂', h'⟩ := hr
  have hA : ConformallyEquivalent (annulus r₁ r₂) (annulus r₁' r₂') := (h.symm hB).trans h'
  have hratio := (annulus_conformallyEquivalent_iff h₁ h₂ h₁' h₂').1 hA
  exact (congrArg (fun t => ENNReal.ofReal (Real.log t)) hratio).symm.le

/-- The modulus of an annulus. -/
theorem dcModulus_annulus {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    dcModulus (annulus r₁ r₂) = ENNReal.ofReal (Real.log (r₂ / r₁)) :=
  dcModulus_eq_of_equiv (isOpen_annulus r₁ r₂) h₁ h₂ (ConformallyEquivalent.refl _)

/-! ### General Theorem 4.9, piece P1 -/


theorem gsep_hasBasis_nhds_infty_ball :
    (nhds (extInf : ExtPlane)).HasBasis (fun r : ℝ => 0 < r)
      (fun r => ((↑) '' {w : ℂ | r < ‖w‖} : Set ExtPlane) ∪ {extInf}) := by
  apply OnePoint.hasBasis_nhds_infty.to_hasBasis'
  · rintro K ⟨hKc, hKK⟩
    obtain ⟨R₀, hR₀⟩ := hKK.isBounded.subset_closedBall (0 : ℂ)
    refine ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
    apply union_subset_union_left
    apply image_mono
    intro w hw hwK
    have hwc := hR₀ hwK
    rw [mem_closedBall_zero_iff] at hwc
    exact absurd hwc (not_le.2 (lt_of_le_of_lt (le_max_left R₀ 1) hw))
  · intro r hr
    rw [OnePoint.hasBasis_nhds_infty.mem_iff]
    refine ⟨closedBall (0 : ℂ) r, ⟨isClosed_closedBall, isCompact_closedBall _ _⟩, ?_⟩
    have heq : (closedBall (0 : ℂ) r)ᶜ = {w : ℂ | r < ‖w‖} := by ext w; simp [not_le]
    rw [heq]

theorem gsep_joinedIn_of_continuousOn {X : Type*} [TopologicalSpace X] {F : Set X} {x y : X}
    (f : ℝ → X) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) (h0 : f 0 = x) (h1 : f 1 = y)
    (hmaps : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ∈ F) : JoinedIn F x y := by
  have hcont : Continuous ((Set.Icc (0 : ℝ) 1).restrict f) := hf.restrict
  refine ⟨⟨⟨fun t => f (t : ℝ), hcont⟩, ?_, ?_⟩, ?_⟩
  · show f ((0 : unitInterval) : ℝ) = x
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, h0]
  · show f ((1 : unitInterval) : ℝ) = y
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, h1]
  · intro t
    exact hmaps (t : ℝ) t.2

/-- The ray path `t ↦ w/(1-t)` for `t < 1`, landing on `extInf` at `t = 1`, stays in the
ball-exterior neighbourhood of `∞` and is joined-in that set to `∞`. -/
theorem gsep_joinedIn_ray_to_infty {w : ℂ} {r : ℝ} (hr : 0 < r) (hw : r < ‖w‖) :
    JoinedIn (((↑) '' {v : ℂ | r < ‖v‖} : Set ExtPlane) ∪ {extInf}) ((w : ℂ) : ExtPlane)
      extInf := by
  set F : Set ExtPlane := ((↑) '' {v : ℂ | r < ‖v‖} : Set ExtPlane) ∪ {extInf} with hFdef
  set f : ℝ → ExtPlane :=
    fun t => if t = 1 then (extInf : ExtPlane) else ((w / (1 - t) : ℂ) : ExtPlane) with hfdef
  have hwne : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; linarith
  have hf0 : f 0 = ((w : ℂ) : ExtPlane) := by simp [hfdef]
  have hf1 : f 1 = (extInf : ExtPlane) := by simp [hfdef]
  have hmaps : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ∈ F := by
    intro t ht
    by_cases ht1 : t = 1
    · simp [hfdef, ht1, hFdef]
    · have h1t : (0 : ℝ) < 1 - t := by
        rcases ht with ⟨-, ht2⟩
        rcases lt_or_eq_of_le ht2 with h | h
        · linarith
        · exact absurd h ht1
      have hnorm : ‖w / (1 - (t : ℂ))‖ = ‖w‖ / (1 - t) := by
        rw [norm_div, show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1t]
      have hgt : r < ‖w / (1 - (t : ℂ))‖ := by
        rw [hnorm]
        have h1t1 : 1 - t ≤ 1 := by linarith [ht.1]
        have hmul : ‖w‖ * (1 - t) ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left h1t1 (norm_nonneg w)
        rw [mul_one] at hmul
        have := (le_div_iff₀ h1t).mpr hmul
        linarith
      left
      simp only [hfdef, if_neg ht1]
      exact ⟨w / (1 - t), hgt, rfl⟩
  have hcontOn : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    by_cases ht1 : t = 1
    · subst ht1
      rw [ContinuousWithinAt, hf1, gsep_hasBasis_nhds_infty_ball.tendsto_right_iff]
      intro r' hr'
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
      have hzpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
      refine ⟨‖w‖ / (r' + 1), div_pos hzpos (by linarith), ?_⟩
      intro t' ht'dist ht'mem
      rw [Real.dist_eq] at ht'dist
      by_cases ht'1 : t' = 1
      · simp [hfdef, ht'1]
      · have h1t' : (0 : ℝ) < 1 - t' := by
          rcases ht'mem with ⟨-, ht2⟩
          rcases lt_or_eq_of_le ht2 with h | h
          · linarith
          · exact absurd h ht'1
        have habs : |t' - 1| = 1 - t' := by
          rw [abs_of_neg (by linarith : t' - 1 < 0)]; ring
        rw [habs] at ht'dist
        have hnorm' : ‖w / (1 - (t' : ℂ))‖ = ‖w‖ / (1 - t') := by
          rw [norm_div, show (1 : ℂ) - (t' : ℂ) = ((1 - t' : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1t']
        have hgt' : r' < ‖w / (1 - (t' : ℂ))‖ := by
          rw [hnorm', lt_div_iff₀ h1t']
          have hlt : 1 - t' < ‖w‖ / (r' + 1) := ht'dist
          have hmul := (lt_div_iff₀ (by linarith : (0 : ℝ) < r' + 1)).mp hlt
          nlinarith [hmul]
        left
        simp only [hfdef, if_neg ht'1]
        exact ⟨w / (1 - t'), hgt', rfl⟩
    · have h1t : (0 : ℝ) < 1 - t := by
        rcases ht with ⟨-, ht2⟩
        rcases lt_or_eq_of_le ht2 with h | h
        · linarith
        · exact absurd h ht1
      have h1ne : (1 : ℂ) - (t : ℂ) ≠ 0 := by
        intro h
        apply ht1
        have : (t : ℂ) = 1 := by linear_combination -h
        exact_mod_cast this
      have hinner : ContinuousAt (fun s : ℝ => w / (1 - (s : ℂ))) t := by
        fun_prop (disch := assumption)
      have hg : ContinuousAt (fun s : ℝ => ((w / (1 - (s : ℂ)) : ℂ) : ExtPlane)) t :=
        OnePoint.continuous_coe.continuousAt.comp hinner
      have heq : (fun s : ℝ => ((w / (1 - (s : ℂ)) : ℂ) : ExtPlane)) =ᶠ[nhds t] f := by
        filter_upwards [eventually_ne_nhds ht1] with s hs
        simp [hfdef, hs]
      exact (hg.congr heq).continuousWithinAt
  exact gsep_joinedIn_of_continuousOn f hcontOn hf0 hf1 hmaps

/-- The neighbourhood-basis set at `x : ExtPlane`, used only to build `gsep_locPathConnectedSpace_extPlane`:
a metric ball at a finite point, or the ball-exterior-plus-`∞` set at `extInf`. -/
noncomputable def gsep_basisSet (x : ExtPlane) (r : ℝ) : Set ExtPlane :=
  OnePoint.rec (C := fun _ => Set ExtPlane)
    (((↑) '' {v : ℂ | r < ‖v‖} : Set ExtPlane) ∪ {extInf})
    (fun z => (↑) '' Metric.ball z r)
    x

theorem gsep_basisSet_coe (z : ℂ) :
    gsep_basisSet (z : ExtPlane) = fun r => (↑) '' Metric.ball z r := rfl

theorem gsep_basisSet_infty :
    gsep_basisSet extInf = fun r => ((↑) '' {v : ℂ | r < ‖v‖} : Set ExtPlane) ∪ {extInf} := rfl

/-- **P1.** `ℂ̄` is locally path-connected. -/
instance gsep_locPathConnectedSpace_extPlane : LocallyPathConnectedSpace ExtPlane := by
  refine LocallyPathConnectedSpace.of_bases
    (p := fun (_ : ExtPlane) (r : ℝ) => 0 < r) (s := gsep_basisSet) ?_ ?_
  · intro x
    induction x using OnePoint.rec with
    | coe z =>
      rw [gsep_basisSet_coe]
      have hb : (nhds z).HasBasis (fun r : ℝ => 0 < r) (fun r => Metric.ball z r) :=
        Metric.nhds_basis_ball
      have hmap : (nhds ((z : ℂ) : ExtPlane)) = Filter.map (↑) (nhds z) :=
        (OnePoint.isOpenEmbedding_coe.map_nhds_eq z).symm
      rw [hmap]
      exact hb.map _
    | infty =>
      rw [gsep_basisSet_infty]
      exact gsep_hasBasis_nhds_infty_ball
  · intro x r hr
    induction x using OnePoint.rec with
    | coe z =>
      rw [gsep_basisSet_coe]
      exact (Metric.isPathConnected_ball hr).image OnePoint.continuous_coe
    | infty =>
      rw [gsep_basisSet_infty]
      refine ⟨extInf, Or.inr rfl, ?_⟩
      rintro y (⟨w, hw, rfl⟩ | hy)
      · exact (gsep_joinedIn_ray_to_infty hr hw).symm
      · rw [mem_singleton_iff] at hy
        rw [hy]
        exact JoinedIn.refl (Or.inr rfl)


/-! ### General Theorem 4.9, piece T1 -/


/-- Two points of `ℂ̄ ∖ B` in different components exhaust all of `ℂ̄ ∖ B` between the two of
them, since a doubly connected `B` has exactly two components (generalizes
`exists_compl_eq_union_components`, which fixes `extInf` as the second point, to two arbitrary
points). -/
theorem gsep_compl_eq_union_of_ne {B : Set ℂ} (hB : IsDoublyConnected B) {x y : ExtPlane}
    (hx : x ∈ (toExt B)ᶜ) (hy : y ∈ (toExt B)ᶜ)
    (hne : connectedComponentIn (toExt B)ᶜ x ≠ connectedComponentIn (toExt B)ᶜ y) :
    (toExt B)ᶜ = connectedComponentIn (toExt B)ᶜ x ∪ connectedComponentIn (toExt B)ᶜ y := by
  obtain ⟨x₀, hx₀, hne₀, huniv⟩ := exists_compl_eq_union_components hB
  have hxcase : connectedComponentIn (toExt B)ᶜ x = connectedComponentIn (toExt B)ᶜ x₀ ∨
      connectedComponentIn (toExt B)ᶜ x = connectedComponentIn (toExt B)ᶜ extInf := by
    have hxmem : x ∈ (toExt B)ᶜ := hx
    rw [huniv] at hxmem
    rcases hxmem with h | h
    · exact Or.inl (connectedComponentIn_eq h).symm
    · exact Or.inr (connectedComponentIn_eq h).symm
  have hycase : connectedComponentIn (toExt B)ᶜ y = connectedComponentIn (toExt B)ᶜ x₀ ∨
      connectedComponentIn (toExt B)ᶜ y = connectedComponentIn (toExt B)ᶜ extInf := by
    have hymem : y ∈ (toExt B)ᶜ := hy
    rw [huniv] at hymem
    rcases hymem with h | h
    · exact Or.inl (connectedComponentIn_eq h).symm
    · exact Or.inr (connectedComponentIn_eq h).symm
  refine huniv.trans ?_
  rcases hxcase with hx1 | hx1 <;> rcases hycase with hy1 | hy1
  · exact absurd (hx1.trans hy1.symm) hne
  · rw [hx1, hy1]
  · rw [hx1, hy1]; exact union_comm _ _
  · exact absurd (hx1.trans hy1.symm) hne

/-- **T1' (owner -46).** General form of `exists_reaches_of_connectedComponentIn_eq` (S04:2773):
if a compact `K ⊆ B` does not separate the two complementary components of the doubly connected
`B` (represented by `x`, `y` in different components of `ℂ̄ ∖ B` but the same component of
`ℂ̄ ∖ K`), then some connected `S ⊆ B ∖ K` accumulates on both components. -/
theorem gsep_exists_reaches_of_connectedComponentIn_eq {B : Set ℂ} (hB : IsDoublyConnected B)
    {K : Set ℂ} (hKc : IsCompact K) (hKB : K ⊆ B) {x y : ExtPlane} (hx : x ∈ (toExt B)ᶜ)
    (hy : y ∈ (toExt B)ᶜ)
    (hne : connectedComponentIn (toExt B)ᶜ x ≠ connectedComponentIn (toExt B)ᶜ y)
    (heq : connectedComponentIn (toExt K)ᶜ x = connectedComponentIn (toExt K)ᶜ y) :
    ∃ S ⊆ B, IsPreconnected S ∧ Disjoint S K ∧
      (closure (toExt S) ∩ connectedComponentIn (toExt B)ᶜ x).Nonempty ∧
      (closure (toExt S) ∩ connectedComponentIn (toExt B)ᶜ y).Nonempty := by
  have hBo : IsOpen B := hB.1
  have hKBtoExt : toExt K ⊆ toExt B := image_mono hKB
  have hxK : x ∈ (toExt K)ᶜ := fun h => hx (hKBtoExt h)
  have hyK : y ∈ (toExt K)ᶜ := fun h => hy (hKBtoExt h)
  have hKcompact : IsCompact (toExt K) := hKc.image OnePoint.continuous_coe
  have hKclosed : IsClosed (toExt K) := hKcompact.isClosed
  set W := connectedComponentIn (toExt K)ᶜ x with hWdef
  have hWo : IsOpen W := hKclosed.isOpen_compl.connectedComponentIn
  have hxW : x ∈ W := mem_connectedComponentIn hxK
  have hyW : y ∈ W := by rw [heq]; exact mem_connectedComponentIn hyK
  have hWpc : IsPathConnected W :=
    (hWo.isConnected_iff_isPathConnected).1 ⟨⟨x, hxW⟩, isPreconnected_connectedComponentIn⟩
  set γp := (hWpc.joinedIn x hxW y hyW).somePath with hγpdef
  set φ : ℝ → ExtPlane := fun t => γp (projIcc 0 1 zero_le_one t) with hφdef
  have hφc : Continuous φ := γp.continuous.comp continuous_projIcc
  have hφW : ∀ t, φ t ∈ W := fun t => (hWpc.joinedIn x hxW y hyW).somePath_mem _
  have hφ0 : φ 0 = x := by simp only [hφdef, projIcc_left]; exact γp.source
  have hφ1 : φ 1 = y := by simp only [hφdef, projIcc_right]; exact γp.target
  set Cx := connectedComponentIn (toExt B)ᶜ x with hCxdef
  set Cy := connectedComponentIn (toExt B)ᶜ y with hCydef
  have hCxclosed : IsClosed Cx := isClosed_connectedComponentIn_compl_toExt hBo x
  have hCyclosed : IsClosed Cy := isClosed_connectedComponentIn_compl_toExt hBo y
  have hxCx : x ∈ Cx := mem_connectedComponentIn hx
  have hyCy : y ∈ Cy := mem_connectedComponentIn hy
  have hCxCydisj : Disjoint Cx Cy := (connectedComponentIn_eq_or_disjoint x y).resolve_left hne
  have huniv : (toExt B)ᶜ = Cx ∪ Cy := gsep_compl_eq_union_of_ne hB hx hy hne
  set T := {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ φ t ∈ Cy} with hTdef
  have hTc : IsClosed T := isClosed_Icc.inter (hCyclosed.preimage hφc)
  have hTne : T.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [hφ1]; exact hyCy⟩
  have hTbdd : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  set u := sInf T with hu
  have huT : u ∈ T := hTc.csInf_mem hTne hTbdd
  have hbefore : ∀ t, 0 ≤ t → t < u → φ t ∉ Cy := by
    intro t ht0 htu hmem
    exact absurd (csInf_le hTbdd (show t ∈ T from ⟨⟨ht0, htu.le.trans huT.1.2⟩, hmem⟩))
      (not_le.2 htu)
  have hu0 : 0 < u := by
    rcases huT.1.1.eq_or_lt with h | h
    · exfalso
      have hxCy : x ∈ Cy := by rw [← hφ0, h]; exact huT.2
      exact Set.disjoint_left.mp hCxCydisj hxCx hxCy
    · exact h
  set T' := {t : ℝ | t ∈ Icc (0 : ℝ) u ∧ φ t ∈ Cx} with hT'def
  have hT'c : IsClosed T' := isClosed_Icc.inter (hCxclosed.preimage hφc)
  have hT'ne : T'.Nonempty := ⟨0, ⟨le_rfl, hu0.le⟩, by rw [hφ0]; exact hxCx⟩
  have hT'bdd : BddAbove T' := ⟨u, fun t ht => ht.1.2⟩
  set s := sSup T' with hs
  have hsT' : s ∈ T' := hT'c.csSup_mem hT'ne hT'bdd
  have hafter : ∀ t, s < t → t ≤ u → φ t ∉ Cx := by
    intro t hst htu hmem
    exact absurd (le_csSup hT'bdd (show t ∈ T' from ⟨⟨hsT'.1.1.trans hst.le, htu⟩, hmem⟩))
      (not_le.2 hst)
  have hsu : s < u := by
    rcases hsT'.1.2.eq_or_lt with h | h
    · exfalso
      have hthis : φ u ∈ Cy := huT.2
      rw [← h] at hthis
      exact Set.disjoint_left.mp hCxCydisj hsT'.2 hthis
    · exact h
  set S : Set ℂ := {z : ℂ | (z : ExtPlane) ∈ φ '' Ioo s u} with hSdef
  have hsub_toExtB : φ '' Ioo s u ⊆ toExt B := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← compl_compl (toExt B), mem_compl_iff, huniv]
    rintro (hCxmem | hCymem)
    · exact hafter t ht.1 ht.2.le hCxmem
    · exact hbefore t (hsT'.1.1.trans ht.1.le) ht.2 hCymem
  have hSrange : φ '' Ioo s u ⊆ range ((↑) : ℂ → ExtPlane) :=
    hsub_toExtB.trans (image_subset_range _ _)
  have htoExtS : toExt S = φ '' Ioo s u := by
    show ((↑) : ℂ → ExtPlane) '' (((↑) : ℂ → ExtPlane) ⁻¹' (φ '' Ioo s u)) = φ '' Ioo s u
    rw [image_preimage_eq_inter_range, inter_eq_left.mpr hSrange]
  have hSsub : S ⊆ B := fun z hz => coe_mem_toExt_iff.mp (hsub_toExtB hz)
  have hSconn : IsPreconnected S := by
    have h1 : IsPreconnected (toExt S) := by
      rw [htoExtS]; exact isPreconnected_Ioo.image φ hφc.continuousOn
    exact (OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image).mp h1
  have hSdisj : Disjoint S K := by
    rw [Set.disjoint_left]
    intro z hz hzK
    obtain ⟨t, -, hteq⟩ := show (z : ExtPlane) ∈ φ '' Ioo s u from hz
    have hzWc : (z : ExtPlane) ∈ (toExt K)ᶜ := hteq ▸ connectedComponentIn_subset _ _ (hφW t)
    exact coe_mem_compl_toExt_iff.mp hzWc hzK
  have hSCx : (closure (toExt S) ∩ Cx).Nonempty := by
    refine ⟨φ s, ?_, hsT'.2⟩
    rw [htoExtS]
    have hscl : s ∈ closure (Ioo s u) := by rw [closure_Ioo hsu.ne]; exact ⟨le_refl s, hsu.le⟩
    exact image_closure_subset_closure_image hφc ⟨s, hscl, rfl⟩
  have hSCy : (closure (toExt S) ∩ Cy).Nonempty := by
    refine ⟨φ u, ?_, huT.2⟩
    rw [htoExtS]
    have hucl : u ∈ closure (Ioo s u) := by rw [closure_Ioo hsu.ne]; exact ⟨hsu.le, le_refl u⟩
    exact image_closure_subset_closure_image hφc ⟨u, hucl, rfl⟩
  exact ⟨S, hSsub, hSconn, hSdisj, hSCx, hSCy⟩


/-! ### General Theorem 4.9, piece EC -/


/-- `f : {r₁<|z|<r₂} → B` matches the inner end of the annulus with the end `C₁` of `B` and the outer end with
`C₂`, in both directions: a set approaching the inner circle is carried to a set accumulating on `C₁` (and outer
to `C₂`), and a set accumulating on `C₁` is carried back by `f⁻¹` to a set approaching the inner circle (and `C₂`
to the outer circle). -/
def gsep_EndsMatch (r₁ r₂ : ℝ) (B : Set ℂ) (f : ℂ → ℂ) (C₁ C₂ : Set ExtPlane) : Prop :=
  (∀ S ⊆ annulus r₁ r₂, (∀ ε > 0, ∃ z ∈ S, ‖z‖ < r₁ + ε) →
      (closure (toExt (f '' S)) ∩ C₁).Nonempty) ∧
  (∀ S ⊆ annulus r₁ r₂, (∀ ε > 0, ∃ z ∈ S, r₂ - ε < ‖z‖) →
      (closure (toExt (f '' S)) ∩ C₂).Nonempty) ∧
  (∀ S ⊆ B, (closure (toExt S) ∩ C₁).Nonempty →
      ∀ ε > 0, ∃ z ∈ Function.invFunOn f (annulus r₁ r₂) '' S, ‖z‖ < r₁ + ε) ∧
  (∀ S ⊆ B, (closure (toExt S) ∩ C₂).Nonempty →
      ∀ ε > 0, ∃ z ∈ Function.invFunOn f (annulus r₁ r₂) '' S, r₂ - ε < ‖z‖)

/-! ### Small re-derived helpers (cannot import AnnulusQC / later S04) -/

/-- Re-derived compactness margin (cf. S04's `exists_pos_band_of_isCompact`). -/
theorem gsep_exists_pos_band_of_isCompact {r₁ r₂ : ℝ} {K : Set ℂ} (hK : IsCompact K)
    (hKA : K ⊆ annulus r₁ r₂) : ∃ ε > 0, ∀ z ∈ K, r₁ + ε ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ - ε := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun z hz => by simp at hz⟩
  obtain ⟨a, ha, hamin⟩ := hK.exists_isMinOn hne continuous_norm.continuousOn
  obtain ⟨b, hb, hbmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
  have ha' := hKA ha
  have hb' := hKA hb
  have hpos : 0 < min (‖a‖ - r₁) (r₂ - ‖b‖) := lt_min (by linarith [ha'.1]) (by linarith [hb'.2])
  refine ⟨min (‖a‖ - r₁) (r₂ - ‖b‖), hpos, fun z hz => ⟨?_, ?_⟩⟩
  · have := isMinOn_iff.1 hamin z hz
    linarith [min_le_left (‖a‖ - r₁) (r₂ - ‖b‖)]
  · have := isMaxOn_iff.1 hbmax z hz
    linarith [min_le_right (‖a‖ - r₁) (r₂ - ‖b‖)]

/-- `univ : Set ExtPlane` is preconnected (no `PreconnectedSpace ExtPlane` instance exists in the
project or Mathlib, so this is derived directly from the unboundedness lemma of `ExpStripLift`). -/
theorem gsep_isPreconnected_univ_extPlane : IsPreconnected (univ : Set ExtPlane) := by
  have hunbdd : ¬ Bornology.IsBounded (univ : Set ℂ) := by
    intro hb
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hb
    have h2 := hR ((R + 1 : ℝ) : ℂ) (mem_univ _)
    rw [Complex.norm_real, Real.norm_eq_abs] at h2
    linarith [le_abs_self (R + 1)]
  have h := isPreconnected_toExt_union_extInf_of_unbounded (S := (univ : Set ℂ))
    isPreconnected_univ hunbdd
  have heq : toExt (univ : Set ℂ) ∪ {extInf} = (univ : Set ExtPlane) := by
    apply Subset.antisymm (subset_univ _)
    intro p _
    induction p using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe z => exact Or.inl ⟨z, mem_univ z, rfl⟩
  rwa [heq] at h

/-- Consistency: the same collar cannot be forced into two disjoint neighbourhoods by two
different `ε`'s (a nonempty overlap of the two collars would land in both). -/
theorem gsep_no_swap {r₁ : ℝ} (hr1 : 0 < r₁) {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') {f : ℂ → ℂ}
    {N₁ N₂ : Set ExtPlane} (hN₁N₂ : Disjoint N₁ N₂)
    (h1 : toExt (f '' annulus r₁ (r₁ + ε)) ⊆ N₁)
    (h2 : toExt (f '' annulus r₁ (r₁ + ε')) ⊆ N₂) : False := by
  set δ := min ε ε' with hδ
  have hδ0 : 0 < δ := lt_min hε hε'
  set z : ℂ := ((r₁ + δ / 2 : ℝ) : ℂ) with hzdef
  have hzr1 : (0:ℝ) ≤ r₁ + δ / 2 := by linarith
  have hznorm : ‖z‖ = r₁ + δ / 2 := by
    rw [hzdef, Complex.norm_real, Real.norm_of_nonneg hzr1]
  have hz1 : z ∈ annulus r₁ (r₁ + ε) := by
    constructor <;> rw [hznorm]
    · linarith
    · linarith [min_le_left ε ε']
  have hz2 : z ∈ annulus r₁ (r₁ + ε') := by
    constructor <;> rw [hznorm]
    · linarith
    · linarith [min_le_right ε ε']
  have hm1 : (f z : ExtPlane) ∈ N₁ := h1 ⟨f z, ⟨z, hz1, rfl⟩, rfl⟩
  have hm2 : (f z : ExtPlane) ∈ N₂ := h2 ⟨f z, ⟨z, hz2, rfl⟩, rfl⟩
  exact Set.disjoint_left.1 hN₁N₂ hm1 hm2

/-- Same consistency fact for the outer collar. -/
theorem gsep_no_swap' {r₂ : ℝ} {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    (hr2 : 0 < r₂ - ε) (hr2' : 0 < r₂ - ε') {f : ℂ → ℂ}
    {N₁ N₂ : Set ExtPlane} (hN₁N₂ : Disjoint N₁ N₂)
    (h1 : toExt (f '' annulus (r₂ - ε) r₂) ⊆ N₁)
    (h2 : toExt (f '' annulus (r₂ - ε') r₂) ⊆ N₂) : False := by
  set δ := min ε ε' with hδ
  have hδ0 : 0 < δ := lt_min hε hε'
  set z : ℂ := ((r₂ - δ / 2 : ℝ) : ℂ) with hzdef
  have hzr2 : (0:ℝ) ≤ r₂ - δ / 2 := by
    have hδε : δ ≤ ε := min_le_left ε ε'
    linarith
  have hznorm : ‖z‖ = r₂ - δ / 2 := by
    rw [hzdef, Complex.norm_real, Real.norm_of_nonneg hzr2]
  have hz1 : z ∈ annulus (r₂ - ε) r₂ := by
    constructor <;> rw [hznorm]
    · linarith [min_le_left ε ε']
    · linarith
  have hz2 : z ∈ annulus (r₂ - ε') r₂ := by
    constructor <;> rw [hznorm]
    · linarith [min_le_right ε ε']
    · linarith
  have hm1 : (f z : ExtPlane) ∈ N₁ := h1 ⟨f z, ⟨z, hz1, rfl⟩, rfl⟩
  have hm2 : (f z : ExtPlane) ∈ N₂ := h2 ⟨f z, ⟨z, hz2, rfl⟩, rfl⟩
  exact Set.disjoint_left.1 hN₁N₂ hm1 hm2

/-- The three-way partition of the annulus by a margin `ε`. -/
theorem gsep_partition_annulus {r₁ r₂ ε : ℝ} (hε : 0 < ε) (h2ε : 2 * ε < r₂ - r₁) :
    annulus r₁ r₂ = annulus r₁ (r₁ + ε) ∪ {z : ℂ | r₁ + ε ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ - ε} ∪
      annulus (r₂ - ε) r₂ := by
  ext z
  simp only [annulus, mem_union, mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_or_ge ‖z‖ (r₁ + ε) with h | h
    · exact Or.inl (Or.inl ⟨h1, h⟩)
    · rcases lt_or_ge (r₂ - ε) ‖z‖ with h' | h'
      · exact Or.inr ⟨h', h2⟩
      · exact Or.inl (Or.inr ⟨h, h'⟩)
  · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · exact ⟨h1, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, h2⟩

/-- If both collars of radius `ε₀` land in the same neighbourhood `Ma` (of `Ca`), the *other*
neighbourhood's own component `Cb` is forced to be clopen in `ℂ̄`, contradicting connectedness. -/
theorem gsep_endsMatch_of_both {r₁ r₂ ε₀ : ℝ} {B : Set ℂ} (hBo : IsOpen B) (h₁ : 0 < r₁)
    (h₂ : r₁ < r₂) (hε₀0 : 0 < ε₀) (h2ε₀ : 2 * ε₀ < r₂ - r₁) {f : ℂ → ℂ}
    (hf : IsHomeomorphOnto f (annulus r₁ r₂) B)
    {Ma Mb : Set ExtPlane} (hMao : IsOpen Ma) (hMbo : IsOpen Mb) (hMaMb : Disjoint Ma Mb)
    {Ca Cb : Set ExtPlane} (hCac : IsCompact Ca) (hCbc : IsCompact Cb)
    (hCane : Ca.Nonempty) (hCbne : Cb.Nonempty)
    (hCaB : Ca ⊆ (toExt B)ᶜ) (hCbB : Cb ⊆ (toExt B)ᶜ) (hunion : (toExt B)ᶜ = Ca ∪ Cb)
    (hCaMa : Ca ⊆ Ma) (hCbMb : Cb ⊆ Mb)
    (hU1 : toExt (f '' annulus r₁ (r₁ + ε₀)) ⊆ Ma)
    (hU2 : toExt (f '' annulus (r₂ - ε₀) r₂) ⊆ Ma) : False := by
  set U1 := annulus r₁ (r₁ + ε₀) with hU1def
  set Mid := {z : ℂ | r₁ + ε₀ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ - ε₀} with hMiddef
  set U2 := annulus (r₂ - ε₀) r₂ with hU2def
  have hApart : annulus r₁ r₂ = U1 ∪ Mid ∪ U2 := gsep_partition_annulus hε₀0 h2ε₀
  have hBpart : B = f '' U1 ∪ f '' Mid ∪ f '' U2 := by
    rw [← hf.2.2.1, hApart, Set.image_union, Set.image_union]
  have htoExtBpart : toExt B = toExt (f '' U1) ∪ toExt (f '' Mid) ∪ toExt (f '' U2) := by
    rw [hBpart, toExt_union, toExt_union]
  have hBsub : toExt B ⊆ Ma ∪ toExt (f '' Mid) := by
    rw [htoExtBpart]
    exact union_subset (union_subset (hU1.trans subset_union_left) subset_union_right)
      (hU2.trans subset_union_left)
  have hMidsub : f '' Mid ⊆ B := by
    rw [hBpart]; exact subset_union_right.trans subset_union_left
  have hMidAS : Mid ⊆ annulus r₁ r₂ := fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hMidcompact : IsCompact Mid := by
    apply (isCompact_closedBall (0 : ℂ) (r₂ - ε₀)).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
    intro z hz
    exact mem_closedBall_zero_iff.2 hz.2
  have hfMidcompact : IsCompact (f '' Mid) := hMidcompact.image_of_continuousOn (hf.1.mono hMidAS)
  have htoExtMidcompact : IsCompact (toExt (f '' Mid)) :=
    hfMidcompact.image OnePoint.continuous_coe
  have htoExtMidclosed : IsClosed (toExt (f '' Mid)) := htoExtMidcompact.isClosed
  have hCbMid : Disjoint Cb (toExt (f '' Mid)) := by
    rw [Set.disjoint_left]
    intro p hpCb hpMid
    have hpB : p ∈ toExt B := by
      obtain ⟨w, hw, rfl⟩ := hpMid
      exact ⟨w, hMidsub hw, rfl⟩
    exact (hCbB hpCb) hpB
  have huniv : (univ : Set ExtPlane) = toExt B ∪ (toExt B)ᶜ := (union_compl_self _).symm
  have hkey : (univ : Set ExtPlane) ⊆ Ma ∪ toExt (f '' Mid) ∪ Cb := by
    rw [huniv, hunion]
    apply union_subset
    · exact hBsub.trans subset_union_left
    · exact union_subset (hCaMa.trans (subset_union_left.trans subset_union_left))
        subset_union_right
  have hMbsub : Mb ⊆ toExt (f '' Mid) ∪ Cb := by
    intro p hpMb
    rcases hkey (mem_univ p) with (hpMa | hpMid) | hpCb
    · exact absurd hpMa (Set.disjoint_right.1 hMaMb hpMb)
    · exact Or.inl hpMid
    · exact Or.inr hpCb
  have hCbeq : Cb = Mb ∩ (toExt (f '' Mid))ᶜ := by
    apply Subset.antisymm
    · intro p hp
      exact ⟨hCbMb hp, fun hp' => (Set.disjoint_left.1 hCbMid hp) hp'⟩
    · rintro p ⟨hpMb, hpMid⟩
      rcases hMbsub hpMb with h | h
      · exact absurd h hpMid
      · exact h
  have hCbopen : IsOpen Cb := by
    rw [hCbeq]; exact hMbo.inter htoExtMidclosed.isOpen_compl
  have hCbclosed : IsClosed Cb := hCbc.isClosed
  have hBne : B.Nonempty := by
    rw [← hf.2.2.1]
    refine ⟨f (((r₁ + r₂) / 2 : ℝ) : ℂ), ⟨((r₁ + r₂) / 2 : ℝ), ?_, rfl⟩⟩
    constructor <;> rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)] <;> linarith
  have hCbne_univ : Cb ≠ (univ : Set ExtPlane) := by
    intro heq
    have hCBuniv : (toExt B)ᶜ = univ := Subset.antisymm (subset_univ _) (heq ▸ hCbB)
    obtain ⟨q, hq⟩ := hBne
    have hqmem : (q : ExtPlane) ∈ (toExt B)ᶜ := hCBuniv ▸ mem_univ _
    rw [coe_mem_compl_toExt_iff] at hqmem
    exact hqmem hq
  rcases gsep_isPreconnected_univ_extPlane.subset_or_subset hCbopen hCbclosed.isOpen_compl
      disjoint_compl_right (by rw [union_compl_self]) with h | h
  · exact hCbne_univ (Subset.antisymm (subset_univ _) h)
  · obtain ⟨p, hp⟩ := hCbne
    exact (h (mem_univ p)) hp

/-- The main compact-exhaustion step: given disjoint open neighbourhoods `N₁ ⊇ C₁`, `N₂ ⊇ C₂` of
the two complementary components, some thin enough pair of collars is separated by them, one way
or the other. -/
theorem gsep_exists_eps_separated {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) {B : Set ℂ}
    (hBo : IsOpen B) {f : ℂ → ℂ} (hf : IsHomeomorphOnto f (annulus r₁ r₂) B)
    {C₁ C₂ : Set ExtPlane} (hC₁c : IsCompact C₁) (hC₂c : IsCompact C₂)
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁B : C₁ ⊆ (toExt B)ᶜ) (hC₂B : C₂ ⊆ (toExt B)ᶜ) (hunion : (toExt B)ᶜ = C₁ ∪ C₂)
    {N₁ N₂ : Set ExtPlane} (hN₁o : IsOpen N₁) (hN₂o : IsOpen N₂) (hN₁N₂ : Disjoint N₁ N₂)
    (hC₁N₁ : C₁ ⊆ N₁) (hC₂N₂ : C₂ ⊆ N₂) :
    ∃ ε > 0, 2 * ε < r₂ - r₁ ∧
      ((toExt (f '' annulus r₁ (r₁ + ε)) ⊆ N₁ ∧ toExt (f '' annulus (r₂ - ε) r₂) ⊆ N₂) ∨
       (toExt (f '' annulus r₁ (r₁ + ε)) ⊆ N₂ ∧ toExt (f '' annulus (r₂ - ε) r₂) ⊆ N₁)) := by
  set A := annulus r₁ r₂ with hA
  set g := Function.invFunOn f A with hg
  set W := N₁ ∪ N₂ with hW
  have hWo : IsOpen W := hN₁o.union hN₂o
  have hinfCB : extInf ∈ (toExt B)ᶜ := extInf_mem_compl_toExt B
  rw [hunion] at hinfCB
  have hextInfW : extInf ∈ W := by
    rcases hinfCB with h | h
    · exact Or.inl (hC₁N₁ h)
    · exact Or.inr (hC₂N₂ h)
  have hWc_sub : Wᶜ ⊆ toExt B := by
    intro p hp
    by_contra hpB
    have hpB' : p ∈ (toExt B)ᶜ := hpB
    rw [hunion] at hpB'
    apply hp
    rcases hpB' with h | h
    · exact Or.inl (hC₁N₁ h)
    · exact Or.inr (hC₂N₂ h)
  have hWcClosed : IsClosed (Wᶜ) := hWo.isClosed_compl
  have hextInf_notMem_Wc : extInf ∉ Wᶜ := fun h => h hextInfW
  have hK'compact : IsCompact (((↑) : ℂ → ExtPlane) ⁻¹' Wᶜ) :=
    ((OnePoint.isClosed_iff_of_notMem hextInf_notMem_Wc).mp hWcClosed).2
  set K' : Set ℂ := ((↑) : ℂ → ExtPlane) ⁻¹' Wᶜ with hK'def
  have hK'B : K' ⊆ B := by
    intro z hz
    have hz' : (z : ExtPlane) ∈ toExt B := hWc_sub hz
    rwa [coe_mem_toExt_iff] at hz'
  have hK'fA : K' ⊆ f '' A := by rw [hf.2.2.1]; exact hK'B
  have hgK'A : g '' K' ⊆ A := by
    rintro _ ⟨z, hz, rfl⟩
    exact Function.invFunOn_mem (hK'fA hz)
  have hgK'compact : IsCompact (g '' K') :=
    hK'compact.image_of_continuousOn (hf.2.2.2.mono hK'B)
  obtain ⟨ε₁, hε₁, hmargin⟩ := gsep_exists_pos_band_of_isCompact hgK'compact hgK'A
  set ε₀ := min ε₁ ((r₂ - r₁) / 3) with hε₀def
  have hε₀0 : 0 < ε₀ := lt_min hε₁ (by linarith)
  have h2ε₀ : 2 * ε₀ < r₂ - r₁ := by
    have := min_le_right ε₁ ((r₂ - r₁) / 3); linarith
  have hε₀ε₁ : ε₀ ≤ ε₁ := min_le_left _ _
  have hmargin' : ∀ z ∈ g '' K', r₁ + ε₀ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ - ε₀ := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hmargin z hz
    exact ⟨by linarith, by linarith⟩
  -- the collars avoid K'
  have hgf : ∀ z ∈ A, g (f z) = z := hf.2.1.leftInvOn_invFunOn
  have hU1avoid : f '' annulus r₁ (r₁ + ε₀) ∩ K' = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro w ⟨⟨z, hz, rfl⟩, hwK'⟩
    have hzA : z ∈ A := ⟨hz.1, by linarith [hz.2]⟩
    have := hmargin' z ⟨f z, hwK', hgf z hzA⟩
    linarith [hz.2, this.1]
  have hU2avoid : f '' annulus (r₂ - ε₀) r₂ ∩ K' = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro w ⟨⟨z, hz, rfl⟩, hwK'⟩
    have hzA : z ∈ A := ⟨by linarith [hz.1], hz.2⟩
    have := hmargin' z ⟨f z, hwK', hgf z hzA⟩
    linarith [hz.1, this.2]
  have hWc_range : Wᶜ ⊆ range ((↑) : ℂ → ExtPlane) := hWc_sub.trans (image_subset_range _ _)
  have htoExtK' : toExt K' = Wᶜ := Set.image_preimage_eq_iff.mpr hWc_range
  have hU1subW : toExt (f '' annulus r₁ (r₁ + ε₀)) ⊆ W := by
    intro p hp
    by_contra hpW
    have hpWc : p ∈ Wᶜ := hpW
    rw [← htoExtK'] at hpWc
    obtain ⟨w, hwU1, rfl⟩ := hp
    obtain ⟨w', hw'K', hw'⟩ := hpWc
    have : w ∈ f '' annulus r₁ (r₁ + ε₀) ∩ K' := ⟨hwU1, OnePoint.coe_injective hw' ▸ hw'K'⟩
    rw [hU1avoid] at this
    exact this
  have hU2subW : toExt (f '' annulus (r₂ - ε₀) r₂) ⊆ W := by
    intro p hp
    by_contra hpW
    have hpWc : p ∈ Wᶜ := hpW
    rw [← htoExtK'] at hpWc
    obtain ⟨w, hwU2, rfl⟩ := hp
    obtain ⟨w', hw'K', hw'⟩ := hpWc
    have : w ∈ f '' annulus (r₂ - ε₀) r₂ ∩ K' := ⟨hwU2, OnePoint.coe_injective hw' ▸ hw'K'⟩
    rw [hU2avoid] at this
    exact this
  have hU1AS : annulus r₁ (r₁ + ε₀) ⊆ A := fun z hz => ⟨hz.1, by linarith [hz.2]⟩
  have hU2AS : annulus (r₂ - ε₀) r₂ ⊆ A := fun z hz => ⟨by linarith [hz.1], hz.2⟩
  have hU1pre : IsPreconnected (toExt (f '' annulus r₁ (r₁ + ε₀))) :=
    ((isPreconnected_annulus h₁.le).image f (hf.1.mono hU1AS)).image _
      OnePoint.continuous_coe.continuousOn
  have hU2pre : IsPreconnected (toExt (f '' annulus (r₂ - ε₀) r₂)) :=
    ((isPreconnected_annulus (show (0:ℝ) ≤ r₂ - ε₀ by linarith)).image f
      (hf.1.mono hU2AS)).image _ OnePoint.continuous_coe.continuousOn
  rcases hU1pre.subset_or_subset hN₁o hN₂o hN₁N₂ hU1subW with hU1case | hU1case <;>
    rcases hU2pre.subset_or_subset hN₁o hN₂o hN₁N₂ hU2subW with hU2case | hU2case
  · -- both in N₁: contradiction via C₂ clopen
    exfalso
    exact gsep_endsMatch_of_both hBo h₁ h₂ hε₀0 h2ε₀ hf hN₁o hN₂o hN₁N₂
      hC₁c hC₂c hC₁ne hC₂ne hC₁B hC₂B hunion hC₁N₁ hC₂N₂ hU1case hU2case
  · exact ⟨ε₀, hε₀0, h2ε₀, Or.inl ⟨hU1case, hU2case⟩⟩
  · exact ⟨ε₀, hε₀0, h2ε₀, Or.inr ⟨hU1case, hU2case⟩⟩
  · exfalso
    exact gsep_endsMatch_of_both hBo h₁ h₂ hε₀0 h2ε₀ hf hN₂o hN₁o hN₁N₂.symm
      hC₂c hC₁c hC₂ne hC₁ne hC₂B hC₁B (hunion.trans (union_comm _ _)) hC₂N₂ hC₁N₁ hU1case hU2case

/-- Re-derived: the image of an open subset of the domain of a homeomorphism-onto-an-open-set is
open (cf. `AnnulusQC.aqc_isOpen_image_of_isHomeomorphOnto`, not importable here). -/
theorem gsep_isOpen_image_of_isHomeomorphOnto {f : ℂ → ℂ} {D V W : Set ℂ}
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

/-- `C₁ ∪ (image of the inner collar)` is open, given that the outer collar (for the same `ε`)
already lands in `N₂`. -/
theorem gsep_C1_union_open {r₁ r₂ : ℝ} (h₁ : 0 < r₁) {B : Set ℂ} (hBo : IsOpen B) {f : ℂ → ℂ}
    (hf : IsHomeomorphOnto f (annulus r₁ r₂) B)
    {C₁ C₂ : Set ExtPlane} (hC₁B : C₁ ⊆ (toExt B)ᶜ) (hunion : (toExt B)ᶜ = C₁ ∪ C₂)
    {N₁ N₂ : Set ExtPlane} (hN₁o : IsOpen N₁) (hN₁N₂ : Disjoint N₁ N₂)
    (hC₁N₁ : C₁ ⊆ N₁) (hC₂N₂ : C₂ ⊆ N₂)
    {ε : ℝ} (hε : 0 < ε) (h2ε : 2 * ε < r₂ - r₁)
    (hU₂ : toExt (f '' annulus (r₂ - ε) r₂) ⊆ N₂) :
    IsOpen (C₁ ∪ toExt (f '' annulus r₁ (r₁ + ε))) := by
  set U1 := annulus r₁ (r₁ + ε) with hU1def
  set Mid := {z : ℂ | r₁ + ε ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ - ε} with hMiddef
  set U2 := annulus (r₂ - ε) r₂ with hU2def
  have hApart : annulus r₁ r₂ = U1 ∪ Mid ∪ U2 := gsep_partition_annulus hε h2ε
  have hBpart : B = f '' U1 ∪ f '' Mid ∪ f '' U2 := by
    rw [← hf.2.2.1, hApart, Set.image_union, Set.image_union]
  have hMidsub : f '' Mid ⊆ B := by
    rw [hBpart]; exact subset_union_right.trans subset_union_left
  have hMidAS : Mid ⊆ annulus r₁ r₂ := fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hMidcompact : IsCompact Mid := by
    apply (isCompact_closedBall (0 : ℂ) (r₂ - ε)).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
    intro z hz
    exact mem_closedBall_zero_iff.2 hz.2
  have hfMidcompact : IsCompact (f '' Mid) := hMidcompact.image_of_continuousOn (hf.1.mono hMidAS)
  have htoExtMidclosed : IsClosed (toExt (f '' Mid)) :=
    (hfMidcompact.image OnePoint.continuous_coe).isClosed
  have htoExtBpart : toExt B = toExt (f '' U1) ∪ toExt (f '' Mid) ∪ toExt (f '' U2) := by
    rw [hBpart, toExt_union, toExt_union]
  have hN1''o : IsOpen (N₁ ∩ (toExt (f '' Mid))ᶜ) := hN₁o.inter htoExtMidclosed.isOpen_compl
  have hC1sub : C₁ ⊆ N₁ ∩ (toExt (f '' Mid))ᶜ := by
    intro p hp
    refine ⟨hC₁N₁ hp, fun hpMid => ?_⟩
    have hpB : p ∈ toExt B := by obtain ⟨w, hw, rfl⟩ := hpMid; exact ⟨w, hMidsub hw, rfl⟩
    exact (hC₁B hp) hpB
  have hN1''sub : N₁ ∩ (toExt (f '' Mid))ᶜ ⊆ C₁ ∪ toExt (f '' U1) := by
    rintro p ⟨hpN1, hpMid⟩
    by_cases hpB : p ∈ toExt B
    · rw [htoExtBpart] at hpB
      rcases hpB with (h | h) | h
      · exact Or.inr h
      · exact absurd h hpMid
      · exact absurd (hU₂ h) (Set.disjoint_left.1 hN₁N₂ hpN1)
    · have hpC : p ∈ (toExt B)ᶜ := hpB
      rw [hunion] at hpC
      rcases hpC with h | h
      · exact Or.inl h
      · exact absurd (hC₂N₂ h) (Set.disjoint_left.1 hN₁N₂ hpN1)
  have hU1AS : U1 ⊆ annulus r₁ r₂ := fun z hz => ⟨hz.1, by linarith [hz.2]⟩
  have hU1o : IsOpen (f '' U1) :=
    gsep_isOpen_image_of_isHomeomorphOnto hf hBo hU1AS (isOpen_annulus r₁ (r₁ + ε))
  have hU1open : IsOpen (toExt (f '' U1)) := isOpen_toExt_iff.mpr hU1o
  have heq : C₁ ∪ toExt (f '' U1) = (N₁ ∩ (toExt (f '' Mid))ᶜ) ∪ toExt (f '' U1) := by
    apply Subset.antisymm
    · exact union_subset_union hC1sub (Subset.refl _)
    · exact union_subset hN1''sub subset_union_right
  rw [heq]
  exact hN1''o.union hU1open

/-- `C₂ ∪ (image of the outer collar)` is open, given that the inner collar (for the same `ε`)
already lands in `N₁`. -/
theorem gsep_C2_union_open {r₁ r₂ : ℝ} (h₁ : 0 < r₁) {B : Set ℂ} (hBo : IsOpen B) {f : ℂ → ℂ}
    (hf : IsHomeomorphOnto f (annulus r₁ r₂) B)
    {C₁ C₂ : Set ExtPlane} (hC₂B : C₂ ⊆ (toExt B)ᶜ) (hunion : (toExt B)ᶜ = C₁ ∪ C₂)
    {N₁ N₂ : Set ExtPlane} (hN₂o : IsOpen N₂) (hN₁N₂ : Disjoint N₁ N₂)
    (hC₁N₁ : C₁ ⊆ N₁) (hC₂N₂ : C₂ ⊆ N₂)
    {ε : ℝ} (hε : 0 < ε) (h2ε : 2 * ε < r₂ - r₁)
    (hU₁ : toExt (f '' annulus r₁ (r₁ + ε)) ⊆ N₁) :
    IsOpen (C₂ ∪ toExt (f '' annulus (r₂ - ε) r₂)) := by
  set U1 := annulus r₁ (r₁ + ε) with hU1def
  set Mid := {z : ℂ | r₁ + ε ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ - ε} with hMiddef
  set U2 := annulus (r₂ - ε) r₂ with hU2def
  have hApart : annulus r₁ r₂ = U1 ∪ Mid ∪ U2 := gsep_partition_annulus hε h2ε
  have hBpart : B = f '' U1 ∪ f '' Mid ∪ f '' U2 := by
    rw [← hf.2.2.1, hApart, Set.image_union, Set.image_union]
  have hMidsub : f '' Mid ⊆ B := by
    rw [hBpart]; exact subset_union_right.trans subset_union_left
  have hMidAS : Mid ⊆ annulus r₁ r₂ := fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hMidcompact : IsCompact Mid := by
    apply (isCompact_closedBall (0 : ℂ) (r₂ - ε)).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
    intro z hz
    exact mem_closedBall_zero_iff.2 hz.2
  have hfMidcompact : IsCompact (f '' Mid) := hMidcompact.image_of_continuousOn (hf.1.mono hMidAS)
  have htoExtMidclosed : IsClosed (toExt (f '' Mid)) :=
    (hfMidcompact.image OnePoint.continuous_coe).isClosed
  have htoExtBpart : toExt B = toExt (f '' U1) ∪ toExt (f '' Mid) ∪ toExt (f '' U2) := by
    rw [hBpart, toExt_union, toExt_union]
  have hN2''o : IsOpen (N₂ ∩ (toExt (f '' Mid))ᶜ) := hN₂o.inter htoExtMidclosed.isOpen_compl
  have hC2sub : C₂ ⊆ N₂ ∩ (toExt (f '' Mid))ᶜ := by
    intro p hp
    refine ⟨hC₂N₂ hp, fun hpMid => ?_⟩
    have hpB : p ∈ toExt B := by obtain ⟨w, hw, rfl⟩ := hpMid; exact ⟨w, hMidsub hw, rfl⟩
    exact (hC₂B hp) hpB
  have hN2''sub : N₂ ∩ (toExt (f '' Mid))ᶜ ⊆ C₂ ∪ toExt (f '' U2) := by
    rintro p ⟨hpN2, hpMid⟩
    by_cases hpB : p ∈ toExt B
    · rw [htoExtBpart] at hpB
      rcases hpB with (h | h) | h
      · exact absurd (hU₁ h) (Set.disjoint_right.1 hN₁N₂ hpN2)
      · exact absurd h hpMid
      · exact Or.inr h
    · have hpC : p ∈ (toExt B)ᶜ := hpB
      rw [hunion] at hpC
      rcases hpC with h | h
      · exact absurd (hC₁N₁ h) (Set.disjoint_right.1 hN₁N₂ hpN2)
      · exact Or.inl h
  have hU2AS : U2 ⊆ annulus r₁ r₂ := fun z hz => ⟨by linarith [hz.1], hz.2⟩
  have hU2o : IsOpen (f '' U2) :=
    gsep_isOpen_image_of_isHomeomorphOnto hf hBo hU2AS (isOpen_annulus (r₂ - ε) r₂)
  have hU2open : IsOpen (toExt (f '' U2)) := isOpen_toExt_iff.mpr hU2o
  have heq : C₂ ∪ toExt (f '' U2) = (N₂ ∩ (toExt (f '' Mid))ᶜ) ∪ toExt (f '' U2) := by
    apply Subset.antisymm
    · exact union_subset_union hC2sub (Subset.refl _)
    · exact union_subset hN2''sub subset_union_right
  rw [heq]
  exact hN2''o.union hU2open

/-- Given a fixed labeling (inner collar into `N₁`, outer into `N₂`, for some `ε₀`), the end
correspondence `gsep_EndsMatch` holds for `(C₁, C₂)`. -/
theorem gsep_endsMatch_of_labeling {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) {B : Set ℂ}
    (hBo : IsOpen B) {f : ℂ → ℂ} (hf : IsHomeomorphOnto f (annulus r₁ r₂) B)
    {C₁ C₂ : Set ExtPlane} (hC₁c : IsCompact C₁) (hC₂c : IsCompact C₂)
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁B : C₁ ⊆ (toExt B)ᶜ) (hC₂B : C₂ ⊆ (toExt B)ᶜ) (hunion : (toExt B)ᶜ = C₁ ∪ C₂)
    {N₁ N₂ : Set ExtPlane} (hN₁o : IsOpen N₁) (hN₂o : IsOpen N₂) (hN₁N₂ : Disjoint N₁ N₂)
    (hC₁N₁ : C₁ ⊆ N₁) (hC₂N₂ : C₂ ⊆ N₂)
    {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (h2ε₀ : 2 * ε₀ < r₂ - r₁)
    (hU₁ : toExt (f '' annulus r₁ (r₁ + ε₀)) ⊆ N₁)
    (hU₂ : toExt (f '' annulus (r₂ - ε₀) r₂) ⊆ N₂) :
    gsep_EndsMatch r₁ r₂ B f C₁ C₂ := by
  set g := Function.invFunOn f (annulus r₁ r₂) with hgdef
  have hgf : ∀ z ∈ annulus r₁ r₂, g (f z) = z := hf.2.1.leftInvOn_invFunOn
  have hU2mono : ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε₀ → toExt (f '' annulus (r₂ - ε') r₂) ⊆ N₂ := by
    intro ε' _ hε'le
    have hsub : annulus (r₂ - ε') r₂ ⊆ annulus (r₂ - ε₀) r₂ := fun z hz =>
      ⟨by linarith [hz.1], hz.2⟩
    exact (Set.image_mono (Set.image_mono hsub)).trans hU₂
  have hU1mono : ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε₀ → toExt (f '' annulus r₁ (r₁ + ε')) ⊆ N₁ := by
    intro ε' _ hε'le
    have hsub : annulus r₁ (r₁ + ε') ⊆ annulus r₁ (r₁ + ε₀) := fun z hz =>
      ⟨hz.1, by linarith [hz.2]⟩
    exact (Set.image_mono (Set.image_mono hsub)).trans hU₁
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- push inner → C₁
    intro S hSA hreach
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hdisj : Disjoint C₁ (closure (toExt (f '' S))) :=
      (Set.disjoint_iff_inter_eq_empty.mpr hempty).symm
    obtain ⟨N, M, hNo, hMo, hC1N, hSclM, hNM⟩ :=
      SeparatedNhds.of_isCompact_isCompact hC₁c isClosed_closure.isCompact hdisj
    have hNN1o : IsOpen (N ∩ N₁) := hNo.inter hN₁o
    have hNN1N2 : Disjoint (N ∩ N₁) N₂ := hN₁N₂.mono_left inter_subset_right
    have hC1NN1 : C₁ ⊆ N ∩ N₁ := fun p hp => ⟨hC1N hp, hC₁N₁ hp⟩
    obtain ⟨ε', hε'0, h2ε', hcase⟩ :=
      gsep_exists_eps_separated h₁ h₂ hBo hf hC₁c hC₂c hC₁ne hC₂ne hC₁B hC₂B hunion
        hNN1o hN₂o hNN1N2 hC1NN1 hC₂N₂
    have hU1_N : toExt (f '' annulus r₁ (r₁ + ε')) ⊆ N := by
      rcases hcase with ⟨h, _⟩ | ⟨h, _⟩
      · exact h.trans inter_subset_left
      · exact (gsep_no_swap h₁ hε₀0 hε'0 hN₁N₂ hU₁ h).elim
    obtain ⟨z, hzS, hzr⟩ := hreach ε' hε'0
    have hzA : z ∈ annulus r₁ (r₁ + ε') := ⟨(hSA hzS).1, hzr⟩
    have hm1 : (f z : ExtPlane) ∈ N := hU1_N ⟨f z, ⟨z, hzA, rfl⟩, rfl⟩
    have hm2 : (f z : ExtPlane) ∈ M := hSclM (subset_closure ⟨f z, ⟨z, hzS, rfl⟩, rfl⟩)
    exact Set.disjoint_left.1 hNM hm1 hm2
  · -- push outer → C₂
    intro S hSA hreach
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hdisj : Disjoint C₂ (closure (toExt (f '' S))) :=
      (Set.disjoint_iff_inter_eq_empty.mpr hempty).symm
    obtain ⟨N, M, hNo, hMo, hC2N, hSclM, hNM⟩ :=
      SeparatedNhds.of_isCompact_isCompact hC₂c isClosed_closure.isCompact hdisj
    have hNN2o : IsOpen (N ∩ N₂) := hNo.inter hN₂o
    have hNN2N1 : Disjoint N₁ (N ∩ N₂) := hN₁N₂.mono_right inter_subset_right
    have hC2NN2 : C₂ ⊆ N ∩ N₂ := fun p hp => ⟨hC2N hp, hC₂N₂ hp⟩
    obtain ⟨ε', hε'0, h2ε', hcase⟩ :=
      gsep_exists_eps_separated h₁ h₂ hBo hf hC₁c hC₂c hC₁ne hC₂ne hC₁B hC₂B hunion
        hN₁o hNN2o hNN2N1 hC₁N₁ hC2NN2
    have hr2ε₀ : 0 < r₂ - ε₀ := by linarith
    have hr2ε' : 0 < r₂ - ε' := by linarith
    have hU2_N : toExt (f '' annulus (r₂ - ε') r₂) ⊆ N := by
      rcases hcase with ⟨_, h⟩ | ⟨_, h⟩
      · exact h.trans inter_subset_left
      · exact (gsep_no_swap' hε'0 hε₀0 hr2ε' hr2ε₀ hN₁N₂ h hU₂).elim
    obtain ⟨z, hzS, hzr⟩ := hreach ε' hε'0
    have hzA : z ∈ annulus (r₂ - ε') r₂ := ⟨hzr, (hSA hzS).2⟩
    have hm1 : (f z : ExtPlane) ∈ N := hU2_N ⟨f z, ⟨z, hzA, rfl⟩, rfl⟩
    have hm2 : (f z : ExtPlane) ∈ M := hSclM (subset_closure ⟨f z, ⟨z, hzS, rfl⟩, rfl⟩)
    exact Set.disjoint_left.1 hNM hm1 hm2
  · -- pull → inner circle
    intro S hSB hSC1 ε hε
    set ε' := min ε ε₀ with hε'def
    have hε'0 : 0 < ε' := lt_min hε hε₀0
    have hε'le : ε' ≤ ε₀ := min_le_right _ _
    have hU₂' : toExt (f '' annulus (r₂ - ε') r₂) ⊆ N₂ := hU2mono ε' hε'0 hε'le
    have h2ε' : 2 * ε' < r₂ - r₁ := lt_of_le_of_lt (by linarith [min_le_right ε ε₀]) h2ε₀
    have hopen : IsOpen (C₁ ∪ toExt (f '' annulus r₁ (r₁ + ε'))) :=
      gsep_C1_union_open h₁ hBo hf hC₁B hunion hN₁o hN₁N₂ hC₁N₁ hC₂N₂ hε'0 h2ε' hU₂'
    obtain ⟨z₀, hz₀C1⟩ := hSC1
    obtain ⟨hz₀mem, hz₀C1'⟩ := hz₀C1
    have hnhd : (C₁ ∪ toExt (f '' annulus r₁ (r₁ + ε'))) ∈ 𝓝 z₀ := hopen.mem_nhds (Or.inl hz₀C1')
    obtain ⟨p, hpmem, hpS⟩ := mem_closure_iff_nhds.1 hz₀mem _ hnhd
    have hpnotC1 : p ∉ C₁ := by
      intro hpC1
      obtain ⟨w, hwS, rfl⟩ := hpS
      exact (hC₁B hpC1) ⟨w, hSB hwS, rfl⟩
    rcases hpmem with h | h
    · exact absurd h hpnotC1
    · obtain ⟨w, ⟨z, hzU1, hfz⟩, hweq2⟩ := h
      obtain ⟨w', hwS, hweq⟩ := hpS
      have hww' : w = w' := OnePoint.coe_injective (hweq2.trans hweq.symm)
      have hzA : z ∈ annulus r₁ r₂ := ⟨hzU1.1, by linarith [hzU1.2, h2ε']⟩
      have hgw' : g w' = z := by rw [← hww', ← hfz]; exact hgf z hzA
      refine ⟨z, ⟨w', hwS, hgw'⟩, ?_⟩
      linarith [hzU1.2, min_le_left ε ε₀]
  · -- pull → outer circle
    intro S hSB hSC2 ε hε
    set ε' := min ε ε₀ with hε'def
    have hε'0 : 0 < ε' := lt_min hε hε₀0
    have hε'le : ε' ≤ ε₀ := min_le_right _ _
    have hU₁' : toExt (f '' annulus r₁ (r₁ + ε')) ⊆ N₁ := hU1mono ε' hε'0 hε'le
    have h2ε' : 2 * ε' < r₂ - r₁ := lt_of_le_of_lt (by linarith [min_le_right ε ε₀]) h2ε₀
    have hopen : IsOpen (C₂ ∪ toExt (f '' annulus (r₂ - ε') r₂)) :=
      gsep_C2_union_open h₁ hBo hf hC₂B hunion hN₂o hN₁N₂ hC₁N₁ hC₂N₂ hε'0 h2ε' hU₁'
    obtain ⟨z₀, hz₀C2⟩ := hSC2
    obtain ⟨hz₀mem, hz₀C2'⟩ := hz₀C2
    have hnhd : (C₂ ∪ toExt (f '' annulus (r₂ - ε') r₂)) ∈ 𝓝 z₀ := hopen.mem_nhds (Or.inl hz₀C2')
    obtain ⟨p, hpmem, hpS⟩ := mem_closure_iff_nhds.1 hz₀mem _ hnhd
    have hpnotC2 : p ∉ C₂ := by
      intro hpC2
      obtain ⟨w, hwS, rfl⟩ := hpS
      exact (hC₂B hpC2) ⟨w, hSB hwS, rfl⟩
    rcases hpmem with h | h
    · exact absurd h hpnotC2
    · obtain ⟨w, ⟨z, hzU2, hfz⟩, hweq2⟩ := h
      obtain ⟨w', hwS, hweq⟩ := hpS
      have hww' : w = w' := OnePoint.coe_injective (hweq2.trans hweq.symm)
      have hzA : z ∈ annulus r₁ r₂ := ⟨by linarith [hzU2.1, h2ε'], hzU2.2⟩
      have hgw' : g w' = z := by rw [← hww', ← hfz]; exact hgf z hzA
      refine ⟨z, ⟨w', hwS, hgw'⟩, ?_⟩
      linarith [hzU2.1, min_le_left ε ε₀]

/-- **EC.** End correspondence: a homeomorphism of the annulus onto a doubly connected `B`
matches the two ends of the annulus with the two complementary components of `B`, one way or the
other. -/
theorem gsep_end_correspondence {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) {B : Set ℂ}
    (hB : IsDoublyConnected B) {f : ℂ → ℂ} (hf : IsHomeomorphOnto f (annulus r₁ r₂) B)
    {x : ExtPlane} (hx : x ∈ (toExt B)ᶜ)
    (hxne : connectedComponentIn (toExt B)ᶜ x ≠ connectedComponentIn (toExt B)ᶜ extInf) :
    gsep_EndsMatch r₁ r₂ B f (connectedComponentIn (toExt B)ᶜ x)
        (connectedComponentIn (toExt B)ᶜ extInf) ∨
      gsep_EndsMatch r₁ r₂ B f (connectedComponentIn (toExt B)ᶜ extInf)
        (connectedComponentIn (toExt B)ᶜ x) := by
  have hBo : IsOpen B := hB.1
  set C₁ := connectedComponentIn (toExt B)ᶜ x with hC₁def
  set C₂ := connectedComponentIn (toExt B)ᶜ extInf with hC₂def
  have hxinf : extInf ∈ (toExt B)ᶜ := extInf_mem_compl_toExt B
  have hC₁c : IsCompact C₁ := (isClosed_connectedComponentIn_compl_toExt hBo x).isCompact
  have hC₂c : IsCompact C₂ := (isClosed_connectedComponentIn_compl_toExt hBo extInf).isCompact
  have hC₁ne : C₁.Nonempty := ⟨x, mem_connectedComponentIn hx⟩
  have hC₂ne : C₂.Nonempty := ⟨extInf, mem_connectedComponentIn hxinf⟩
  have hC₁B : C₁ ⊆ (toExt B)ᶜ := connectedComponentIn_subset _ _
  have hC₂B : C₂ ⊆ (toExt B)ᶜ := connectedComponentIn_subset _ _
  have hunion : (toExt B)ᶜ = C₁ ∪ C₂ := gsep_compl_eq_union_of_ne hB hx hxinf hxne
  have hdisj : Disjoint C₁ C₂ := by
    rcases connectedComponentIn_eq_or_disjoint (F := (toExt B)ᶜ) x extInf with h | h
    · exact absurd h hxne
    · exact h
  obtain ⟨N₁, N₂, hN₁o, hN₂o, hC₁N₁, hC₂N₂, hN₁N₂⟩ :=
    SeparatedNhds.of_isCompact_isCompact hC₁c hC₂c hdisj
  obtain ⟨ε₀, hε₀0, h2ε₀, hcase⟩ :=
    gsep_exists_eps_separated h₁ h₂ hBo hf hC₁c hC₂c hC₁ne hC₂ne hC₁B hC₂B hunion
      hN₁o hN₂o hN₁N₂ hC₁N₁ hC₂N₂
  rcases hcase with ⟨hU₁, hU₂⟩ | ⟨hU₁, hU₂⟩
  · exact Or.inl (gsep_endsMatch_of_labeling h₁ h₂ hBo hf hC₁c hC₂c hC₁ne hC₂ne hC₁B hC₂B
      hunion hN₁o hN₂o hN₁N₂ hC₁N₁ hC₂N₂ hε₀0 h2ε₀ hU₁ hU₂)
  · exact Or.inr (gsep_endsMatch_of_labeling h₁ h₂ hBo hf hC₂c hC₁c hC₂ne hC₁ne hC₂B hC₁B
      (hunion.trans (union_comm _ _)) hN₂o hN₁o hN₁N₂.symm hC₂N₂ hC₁N₁ hε₀0 h2ε₀ hU₁ hU₂)


/-! ### General Theorem 4.9, piece T2 -/


/-- **T2'.** General form of `connectedComponentIn_eq_of_reaches` (S04:2615): a connected
`S ⊆ B ∖ K` whose closure meets two connected sets `C₁, C₂ ⊆ ℂ̄ ∖ B` puts `x ∈ C₁`, `y ∈ C₂` in one
component of `ℂ̄ ∖ K`. -/
theorem gsep_connectedComponentIn_eq_of_reaches {B K S : Set ℂ} (hKB : K ⊆ B)
    (hS : IsPreconnected S) (hSB : S ⊆ B) (hSK : Disjoint S K) {C₁ C₂ : Set ExtPlane}
    (hC₁ : IsPreconnected C₁) (hC₂ : IsPreconnected C₂) (hC₁B : C₁ ⊆ (toExt B)ᶜ)
    (hC₂B : C₂ ⊆ (toExt B)ᶜ) (h₁ : (closure (toExt S) ∩ C₁).Nonempty)
    (h₂ : (closure (toExt S) ∩ C₂).Nonempty) {x y : ExtPlane} (hx : x ∈ C₁) (hy : y ∈ C₂) :
    connectedComponentIn (toExt K)ᶜ x = connectedComponentIn (toExt K)ᶜ y := by
  obtain ⟨p, hpS, hpC₁⟩ := h₁
  obtain ⟨q, hqS, hqC₂⟩ := h₂
  have hKtoExtB : toExt K ⊆ toExt B := image_mono hKB
  have hSpre : IsPreconnected (toExt S) := hS.image _ OnePoint.continuous_coe.continuousOn
  have hSp : IsPreconnected (insert p (toExt S)) :=
    hSpre.subset_closure (subset_insert p _) (insert_subset_iff.mpr ⟨hpS, subset_closure⟩)
  have hSpC₁ : IsPreconnected (insert p (toExt S) ∪ C₁) :=
    IsPreconnected.union p (mem_insert_iff.mpr (Or.inl rfl)) hpC₁ hSp hC₁
  have hqclosure : q ∈ closure (insert p (toExt S) ∪ C₁) :=
    closure_mono (subset_union_of_subset_left (subset_insert p _) _) hqS
  have hbig1 : IsPreconnected (insert q (insert p (toExt S) ∪ C₁)) :=
    hSpC₁.subset_closure (subset_insert q _) (insert_subset_iff.mpr ⟨hqclosure, subset_closure⟩)
  have hbig2 : IsPreconnected (insert q (insert p (toExt S) ∪ C₁) ∪ C₂) :=
    IsPreconnected.union q (mem_insert_iff.mpr (Or.inl rfl)) hqC₂ hbig1 hC₂
  have hSKdisj : toExt S ⊆ (toExt K)ᶜ := by
    rintro _ ⟨s, hs, rfl⟩ ⟨k, hk, hks⟩
    rw [← OnePoint.coe_injective hks] at hs
    exact Set.disjoint_left.mp hSK hs hk
  have hC₁K : C₁ ⊆ (toExt K)ᶜ := fun z hz hzK => hC₁B hz (hKtoExtB hzK)
  have hC₂K : C₂ ⊆ (toExt K)ᶜ := fun z hz hzK => hC₂B hz (hKtoExtB hzK)
  have hpK : p ∈ (toExt K)ᶜ := fun hpK' => hC₁B hpC₁ (hKtoExtB hpK')
  have hqK : q ∈ (toExt K)ᶜ := fun hqK' => hC₂B hqC₂ (hKtoExtB hqK')
  have hbigsub : insert q (insert p (toExt S) ∪ C₁) ∪ C₂ ⊆ (toExt K)ᶜ :=
    union_subset
      (insert_subset_iff.mpr ⟨hqK, union_subset (insert_subset_iff.mpr ⟨hpK, hSKdisj⟩) hC₁K⟩)
      hC₂K
  have hxmem : x ∈ insert q (insert p (toExt S) ∪ C₁) ∪ C₂ :=
    Or.inl (Or.inr (Or.inr hx))
  have hstep : insert q (insert p (toExt S) ∪ C₁) ∪ C₂ ⊆ connectedComponentIn (toExt K)ᶜ x :=
    hbig2.subset_connectedComponentIn hxmem hbigsub
  have hymem : y ∈ insert q (insert p (toExt S) ∪ C₁) ∪ C₂ := Or.inr hy
  exact connectedComponentIn_eq (hstep hymem)


/-! ### General Theorem 4.9, piece MAIN -/


theorem gsep_isCurveImage_separatingCurves {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) {B : Set ℂ}
    (hB : IsDoublyConnected B) {f : ℂ → ℂ} (hf : IsConformalOnto f (annulus r₁ r₂) B) :
    IsCurveImage f (separatingCurves (annulus r₁ r₂)) (separatingCurves B) := by
  have hU := isOpen_annulus r₁ r₂
  have hg := hf.symm hU
  have hfg : ∀ w ∈ B, f (Function.invFunOn f (annulus r₁ r₂) w) = w := fun w hw =>
    Function.invFunOn_eq (show w ∈ f '' annulus r₁ r₂ by rw [hf.2.2]; exact hw)
  have hgf : ∀ z ∈ annulus r₁ r₂, Function.invFunOn f (annulus r₁ r₂) (f z) = z := fun z hz =>
    hf.2.1.leftInvOn_invFunOn hz
  have hIHom : IsHomeomorphOnto f (annulus r₁ r₂) B :=
    ⟨hf.1.continuousOn, hf.2.1, hf.2.2, hg.1.continuousOn⟩
  obtain ⟨x, hx, hxne, hxunion⟩ := exists_compl_eq_union_components hB
  have hEC := gsep_end_correspondence h₁ h₂ hB hIHom hx hxne
  set C₁ := connectedComponentIn (toExt B)ᶜ x with hC₁_def
  set C₂ := connectedComponentIn (toExt B)ᶜ extInf with hC₂_def
  have hextInf : extInf ∈ (toExt B)ᶜ := extInf_mem_compl_toExt B
  have hC₁pre : IsPreconnected C₁ := isPreconnected_connectedComponentIn
  have hC₂pre : IsPreconnected C₂ := isPreconnected_connectedComponentIn
  have hC₁sub : C₁ ⊆ (toExt B)ᶜ := connectedComponentIn_subset _ _
  have hC₂sub : C₂ ⊆ (toExt B)ᶜ := connectedComponentIn_subset _ _
  have hcomp_cases : ∀ z' : ExtPlane, z' ∈ (toExt B)ᶜ →
      connectedComponentIn (toExt B)ᶜ z' = C₁ ∨ connectedComponentIn (toExt B)ᶜ z' = C₂ := by
    intro z' hz'
    rw [hxunion] at hz'
    rcases hz' with hz' | hz'
    · exact Or.inl (connectedComponentIn_eq hz').symm
    · exact Or.inr (connectedComponentIn_eq hz').symm
  have hreach_pullback : ∀ (S : Set ℂ), S ⊆ B → (closure (toExt S) ∩ C₁).Nonempty →
      (closure (toExt S) ∩ C₂).Nonempty →
      (∀ ε > 0, ∃ z ∈ Function.invFunOn f (annulus r₁ r₂) '' S, ‖z‖ < r₁ + ε) ∧
      (∀ ε > 0, ∃ z ∈ Function.invFunOn f (annulus r₁ r₂) '' S, r₂ - ε < ‖z‖) := by
    intro S hSB hSC1 hSC2
    rcases hEC with hEC | hEC
    · exact ⟨hEC.2.2.1 S hSB hSC1, hEC.2.2.2 S hSB hSC2⟩
    · exact ⟨hEC.2.2.1 S hSB hSC2, hEC.2.2.2 S hSB hSC1⟩
  have hreach_pushforward : ∀ (S : Set ℂ), S ⊆ annulus r₁ r₂ →
      (∀ ε > 0, ∃ z ∈ S, ‖z‖ < r₁ + ε) → (∀ ε > 0, ∃ z ∈ S, r₂ - ε < ‖z‖) →
      (closure (toExt (f '' S)) ∩ C₁).Nonempty ∧ (closure (toExt (f '' S)) ∩ C₂).Nonempty := by
    intro S hSA hSin hSout
    rcases hEC with hEC | hEC
    · exact ⟨hEC.1 S hSA hSin, hEC.2.1 S hSA hSout⟩
    · exact ⟨hEC.2.1 S hSA hSout, hEC.1 S hSA hSin⟩
  refine ⟨fun γ hγ => ?_, fun γ' hγ' => ?_⟩
  · -- (⇒) forward: annulus separating curve ↦ B separating curve
    obtain ⟨⟨K, hK, hK01⟩, htr, hsep⟩ := hγ
    have hmaps : MapsTo γ.toFun (Icc 0 1) (annulus r₁ r₂) := fun t ht => htr ⟨t, ht, rfl⟩
    have hfA : MapsTo f (annulus r₁ r₂) B := fun z hz => by
      rw [← hf.2.2]; exact mem_image_of_mem f hz
    have hloc : LocallyLipschitzOn (Icc (0 : ℝ) 1) (f ∘ γ.toFun) := by
      intro t ht
      have hcd : ContDiffAt ℂ 1 f (γ.toFun t) :=
        (hf.1.contDiffOn (n := 1) hU).contDiffAt (hU.mem_nhds (hmaps ht))
      obtain ⟨K₂, V₂, hV₂, hK₂⟩ := hcd.exists_lipschitzOnWith
      exact ⟨K₂ * K, Icc 0 1 ∩ γ.toFun ⁻¹' V₂,
        inter_mem self_mem_nhdsWithin (hK.continuousOn t ht hV₂),
        hK₂.comp (hK.mono inter_subset_left) fun x hx => hx.2⟩
    obtain ⟨K', hK'⟩ := hloc.exists_lipschitzOnWith_of_compact isCompact_Icc
    let γ' : LRCurve := ⟨f ∘ γ.toFun, locallyLipschitzOn_comp_of_differentiableOn hU hf.1
      isOpen_Ioo γ.locallyLipschitzOn (hmaps.mono_left Ioo_subset_Icc_self)⟩
    have htr' : γ'.closedTrace = f '' γ.closedTrace := by
      show (f ∘ γ.toFun) '' Icc 0 1 = f '' (γ.toFun '' Icc 0 1)
      exact image_comp f γ.toFun _
    have htrA' : γ'.closedTrace ⊆ B := by
      rw [htr']; exact image_subset_iff.2 fun z hz => hfA (htr hz)
    refine ⟨γ', ⟨⟨K', hK', by show f (γ.toFun 0) = f (γ.toFun 1); rw [hK01]⟩, htrA', ?_⟩,
      fun t _ => rfl⟩
    intro x' hx' y' hy' hne' heq
    have hKc' : IsCompact γ'.closedTrace := isCompact_Icc.image_of_continuousOn hK'.continuousOn
    obtain ⟨S, hSB, hSpre, hSK, hSx', hSy'⟩ :=
      gsep_exists_reaches_of_connectedComponentIn_eq hB hKc' htrA' hx' hy' hne' heq
    have hx'c := hcomp_cases x' hx'
    have hy'c := hcomp_cases y' hy'
    have hreach12 : (closure (toExt S) ∩ C₁).Nonempty ∧ (closure (toExt S) ∩ C₂).Nonempty := by
      rcases hx'c with hx1 | hx2
      · rcases hy'c with hy1 | hy2
        · exact absurd (hx1.trans hy1.symm) hne'
        · exact ⟨hx1 ▸ hSx', hy2 ▸ hSy'⟩
      · rcases hy'c with hy1 | hy2
        · exact ⟨hy1 ▸ hSy', hx2 ▸ hSx'⟩
        · exact absurd (hx2.trans hy2.symm) hne'
    obtain ⟨hSC1, hSC2⟩ := hreach12
    obtain ⟨hin, hout⟩ := hreach_pullback S hSB hSC1 hSC2
    have hdisj : Disjoint (Function.invFunOn f (annulus r₁ r₂) '' S) γ.closedTrace := by
      rw [Set.disjoint_left]
      rintro _ ⟨s, hs, rfl⟩ hmem
      apply Set.disjoint_left.mp hSK hs
      rw [htr']
      exact ⟨Function.invFunOn f (annulus r₁ r₂) s, hmem, hfg _ (hSB hs)⟩
    have hpre : IsPreconnected (Function.invFunOn f (annulus r₁ r₂) '' S) :=
      hSpre.image _ (hg.1.continuousOn.mono hSB)
    have hsubA : Function.invFunOn f (annulus r₁ r₂) '' S ⊆ annulus r₁ r₂ := by
      have h := image_mono (f := Function.invFunOn f (annulus r₁ r₂)) hSB
      rwa [hg.2.2] at h
    have hcontra := connectedComponentIn_eq_of_reaches h₁ h₂ htr hpre hsubA hdisj hin hout
    exact hsep _ (zero_mem_compl_toExt_annulus h₁) _ (extInf_mem_compl_toExt _)
      (connectedComponentIn_compl_toExt_annulus_ne h₁ h₂) hcontra
  · -- (⇐) backward: B separating curve ↦ annulus separating curve
    obtain ⟨⟨K, hK, hK01⟩, htr', hsep'⟩ := hγ'
    have hmaps' : MapsTo γ'.toFun (Icc 0 1) B := fun t ht => htr' ⟨t, ht, rfl⟩
    have hgB : MapsTo (Function.invFunOn f (annulus r₁ r₂)) B (annulus r₁ r₂) := fun w hw => by
      have h : Function.invFunOn f (annulus r₁ r₂) w ∈ Function.invFunOn f (annulus r₁ r₂) '' B :=
        mem_image_of_mem _ hw
      rwa [hg.2.2] at h
    have hloc : LocallyLipschitzOn (Icc (0 : ℝ) 1)
        (Function.invFunOn f (annulus r₁ r₂) ∘ γ'.toFun) := by
      intro t ht
      have hcd : ContDiffAt ℂ 1 (Function.invFunOn f (annulus r₁ r₂)) (γ'.toFun t) :=
        (hg.1.contDiffOn (n := 1) hB.1).contDiffAt (hB.1.mem_nhds (hmaps' ht))
      obtain ⟨K₂, V₂, hV₂, hK₂⟩ := hcd.exists_lipschitzOnWith
      exact ⟨K₂ * K, Icc 0 1 ∩ γ'.toFun ⁻¹' V₂,
        inter_mem self_mem_nhdsWithin (hK.continuousOn t ht hV₂),
        hK₂.comp (hK.mono inter_subset_left) fun x hx => hx.2⟩
    obtain ⟨K', hK'⟩ := hloc.exists_lipschitzOnWith_of_compact isCompact_Icc
    let γ : LRCurve := ⟨Function.invFunOn f (annulus r₁ r₂) ∘ γ'.toFun,
      locallyLipschitzOn_comp_of_differentiableOn hB.1 hg.1 isOpen_Ioo γ'.locallyLipschitzOn
        (hmaps'.mono_left Ioo_subset_Icc_self)⟩
    have htreq : γ.closedTrace = Function.invFunOn f (annulus r₁ r₂) '' γ'.closedTrace := by
      show (Function.invFunOn f (annulus r₁ r₂) ∘ γ'.toFun) '' Icc 0 1 =
        Function.invFunOn f (annulus r₁ r₂) '' (γ'.toFun '' Icc 0 1)
      exact image_comp _ γ'.toFun _
    have htrA : γ.closedTrace ⊆ annulus r₁ r₂ := by
      rw [htreq]; exact image_subset_iff.2 fun z hz => hgB (htr' hz)
    refine ⟨γ, ⟨⟨K', hK', by
      show Function.invFunOn f (annulus r₁ r₂) (γ'.toFun 0) =
        Function.invFunOn f (annulus r₁ r₂) (γ'.toFun 1)
      rw [hK01]⟩, htrA, ?_⟩,
      fun t ht => (hfg (γ'.toFun t) (hmaps' (Ioo_subset_Icc_self ht))).symm⟩
    refine separates_compl_of_connectedComponentIn_ne h₁ h₂ htrA fun heq => ?_
    have hKc : IsCompact γ.closedTrace := isCompact_Icc.image_of_continuousOn hK'.continuousOn
    obtain ⟨S, hSA, hSpre, hSK, hin, hout⟩ :=
      exists_reaches_of_connectedComponentIn_eq h₁ h₂ hKc htrA heq
    obtain ⟨hSC1, hSC2⟩ := hreach_pushforward S hSA hin hout
    have hdisj : Disjoint (f '' S) γ'.closedTrace := by
      rw [Set.disjoint_left]
      rintro _ ⟨s, hs, rfl⟩ hmem
      apply Set.disjoint_left.mp hSK hs
      rw [htreq]
      exact ⟨f s, hmem, hgf _ (hSA hs)⟩
    have hpre' : IsPreconnected (f '' S) := hSpre.image _ (hf.1.continuousOn.mono hSA)
    have hsub' : f '' S ⊆ B := by rw [← hf.2.2]; exact image_mono hSA
    have hcontra := gsep_connectedComponentIn_eq_of_reaches htr' hpre' hsub' hdisj hC₁pre hC₂pre
      hC₁sub hC₂sub hSC1 hSC2 (mem_connectedComponentIn hx) (mem_connectedComponentIn hextInf)
    exact hsep' _ hx _ hextInf hxne hcontra


/-! ### General Theorem 4.9, piece Z -/


/-- A homeomorphism carries `connectedComponentIn s x` onto `connectedComponentIn (Φ''s) (Φ x)`. -/
theorem gsep_z_connectedComponentIn_image_homeomorph (Φ : ExtPlane ≃ₜ ExtPlane) {s : Set ExtPlane}
    {x : ExtPlane} (hx : x ∈ s) :
    Φ '' connectedComponentIn s x = connectedComponentIn (Φ '' s) (Φ x) := by
  have hxmem : x ∈ connectedComponentIn s x := mem_connectedComponentIn hx
  apply Subset.antisymm
  · have hpre : IsPreconnected (Φ '' connectedComponentIn s x) :=
      isPreconnected_connectedComponentIn.image Φ Φ.continuous.continuousOn
    have hsub : Φ '' connectedComponentIn s x ⊆ Φ '' s :=
      image_mono (connectedComponentIn_subset s x)
    exact hpre.subset_connectedComponentIn (mem_image_of_mem Φ hxmem) hsub
  · have hxmem' : Φ x ∈ Φ '' s := mem_image_of_mem Φ hx
    have hpre' : IsPreconnected (Φ.symm '' connectedComponentIn (Φ '' s) (Φ x)) :=
      isPreconnected_connectedComponentIn.image Φ.symm Φ.symm.continuous.continuousOn
    have hsub' : Φ.symm '' connectedComponentIn (Φ '' s) (Φ x) ⊆ s := by
      rintro y ⟨w, hw, rfl⟩
      obtain ⟨z, hz, hzeq⟩ := connectedComponentIn_subset (Φ '' s) (Φ x) hw
      rwa [← hzeq, Φ.symm_apply_apply]
    have hxmem'' : Φ.symm (Φ x) ∈ Φ.symm '' connectedComponentIn (Φ '' s) (Φ x) :=
      mem_image_of_mem Φ.symm (mem_connectedComponentIn hxmem')
    rw [Φ.symm_apply_apply] at hxmem''
    have hkey : Φ.symm '' connectedComponentIn (Φ '' s) (Φ x) ⊆ connectedComponentIn s x :=
      hpre'.subset_connectedComponentIn hxmem'' hsub'
    intro y hy
    have hy' : Φ.symm y ∈ connectedComponentIn s x := hkey ⟨y, hy, rfl⟩
    have := mem_image_of_mem Φ hy'
    rwa [Φ.apply_symm_apply] at this

/-! ### Translation of `ℂ̄` -/

/-- Translation by `p`, extended to `ℂ̄` fixing `∞` (the Möbius map `a=1,b=p,c=0,d=1`). -/
def gsep_z_translateHomeomorph (p : ℂ) : ExtPlane ≃ₜ ExtPlane :=
  mobiusHomeomorph 1 p 0 1 (by simp)

theorem gsep_z_translateHomeomorph_coe (p z : ℂ) :
    gsep_z_translateHomeomorph p (z : ExtPlane) = ((z + p : ℂ) : ExtPlane) := by
  show mobiusExt 1 p 0 1 (z : ExtPlane) = ((z + p : ℂ) : ExtPlane)
  rw [mobiusExt_coe (show (0:ℂ) * z + 1 ≠ 0 by simp)]
  congr 1
  simp [mobiusFn]

theorem gsep_z_translateHomeomorph_infty (p : ℂ) :
    gsep_z_translateHomeomorph p extInf = extInf := by
  show mobiusExt 1 p 0 1 extInf = extInf
  exact mobiusExt_infty_of_eq rfl

theorem gsep_z_translateHomeomorph_toExt (p : ℂ) (D : Set ℂ) :
    gsep_z_translateHomeomorph p '' toExt D = toExt ((· + p) '' D) := by
  ext w
  constructor
  · rintro ⟨u, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z + p, ⟨z, hz, rfl⟩, (gsep_z_translateHomeomorph_coe p z).symm⟩
  · rintro ⟨u, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨(z : ExtPlane), ⟨z, hz, rfl⟩, gsep_z_translateHomeomorph_coe p z⟩

theorem gsep_z_image_compl_of_homeomorph (Φ : ExtPlane ≃ₜ ExtPlane) (s : Set ExtPlane) :
    Φ '' sᶜ = (Φ '' s)ᶜ :=
  Φ.toEquiv.image_compl s

theorem gsep_z_annulusAt_zero (ε δ : ℝ) : annulusAt (0 : ℂ) ε δ = annulus ε δ := by
  ext z; simp [annulusAt, annulus]

theorem gsep_z_annulusAt_eq_image (q p : ℂ) (ε δ : ℝ) :
    annulusAt (q + p) ε δ = (· + p) '' annulusAt q ε δ := by
  ext z
  have hnorm : ‖z - (q + p)‖ = ‖z - p - q‖ := by rw [show z - p - q = z - (q + p) by ring]
  constructor
  · intro hz
    refine ⟨z - p, ?_, by ring⟩
    show ε < ‖z - p - q‖ ∧ ‖z - p - q‖ < δ
    rw [← hnorm]; exact hz
  · rintro ⟨w, hw, rfl⟩
    show ε < ‖w + p - (q + p)‖ ∧ ‖w + p - (q + p)‖ < δ
    rw [show w + p - (q + p) = w - q by ring]
    exact hw

/-- The complement (in `ℂ̄`) of the translate of any `S : Set ℂ` is the translate of the
complement. -/
theorem gsep_z_compl_toExt_translate_eq (p : ℂ) (S : Set ℂ) :
    (toExt ((· + p) '' S))ᶜ = gsep_z_translateHomeomorph p '' (toExt S)ᶜ := by
  rw [gsep_z_image_compl_of_homeomorph, gsep_z_translateHomeomorph_toExt]

theorem gsep_z_compl_toExt_annulusAt_eq (q p : ℂ) (ε δ : ℝ) :
    (toExt (annulusAt (q + p) ε δ))ᶜ = gsep_z_translateHomeomorph p '' (toExt (annulusAt q ε δ))ᶜ := by
  rw [gsep_z_annulusAt_eq_image, gsep_z_compl_toExt_translate_eq]

/-- Translating a closed curve. -/
def gsep_z_translateCurve (p : ℂ) (γ : LRCurve) : LRCurve :=
  ⟨(· + p) ∘ γ.toFun, locallyLipschitzOn_comp_of_differentiableOn isOpen_univ
    (differentiable_id.add_const p).differentiableOn isOpen_Ioo γ.locallyLipschitzOn
    (fun _ _ => mem_univ _)⟩

theorem gsep_z_translateCurve_toFun (p : ℂ) (γ : LRCurve) :
    (gsep_z_translateCurve p γ).toFun = (· + p) ∘ γ.toFun := rfl

theorem gsep_z_translateCurve_isClosedCurve (p : ℂ) {γ : LRCurve} (hγ : γ.IsClosedCurve) :
    (gsep_z_translateCurve p γ).IsClosedCurve := by
  obtain ⟨K, hK, hend⟩ := hγ
  refine ⟨K, ?_, ?_⟩
  · intro s hs t ht
    have h := hK hs ht
    simpa only [gsep_z_translateCurve_toFun, Function.comp_apply, edist_add_right] using h
  · show γ.toFun 0 + p = γ.toFun 1 + p
    rw [hend]

theorem gsep_z_translateCurve_closedTrace (p : ℂ) (γ : LRCurve) :
    (gsep_z_translateCurve p γ).closedTrace = (· + p) '' γ.closedTrace := by
  show ((· + p) ∘ γ.toFun) '' Icc 0 1 = (· + p) '' (γ.toFun '' Icc 0 1)
  rw [image_comp]

theorem gsep_z_isSeparatingCurve_translate (q p : ℂ) (ε δ : ℝ) {γ : LRCurve}
    (hγ : IsSeparatingCurve (annulusAt q ε δ) γ) :
    IsSeparatingCurve (annulusAt (q + p) ε δ) (gsep_z_translateCurve p γ) := by
  have htrace : (gsep_z_translateCurve p γ).closedTrace ⊆ annulusAt (q + p) ε δ := by
    rw [gsep_z_translateCurve_closedTrace, gsep_z_annulusAt_eq_image]
    exact Set.image_mono hγ.2.1
  refine ⟨gsep_z_translateCurve_isClosedCurve p hγ.1, htrace, ?_⟩
  · intro x hx y hy hxy
    set Φ := gsep_z_translateHomeomorph p with hΦdef
    have hxeq : Φ (Φ.symm x) = x := Φ.apply_symm_apply x
    have hyeq : Φ (Φ.symm y) = y := Φ.apply_symm_apply y
    have hx0 : Φ.symm x ∈ (toExt (annulusAt q ε δ))ᶜ := by
      rw [gsep_z_compl_toExt_annulusAt_eq] at hx
      obtain ⟨w, hw, hweq⟩ := hx
      rwa [← Φ.injective (hweq.trans hxeq.symm)]
    have hy0 : Φ.symm y ∈ (toExt (annulusAt q ε δ))ᶜ := by
      rw [gsep_z_compl_toExt_annulusAt_eq] at hy
      obtain ⟨w, hw, hweq⟩ := hy
      rwa [← Φ.injective (hweq.trans hyeq.symm)]
    have hx0' : Φ.symm x ∈ (toExt γ.closedTrace)ᶜ :=
      compl_subset_compl.2 (image_mono hγ.2.1) hx0
    have hy0' : Φ.symm y ∈ (toExt γ.closedTrace)ᶜ :=
      compl_subset_compl.2 (image_mono hγ.2.1) hy0
    have hcx : connectedComponentIn (toExt (annulusAt (q + p) ε δ))ᶜ x =
        Φ '' connectedComponentIn (toExt (annulusAt q ε δ))ᶜ (Φ.symm x) := by
      have h1 := gsep_z_connectedComponentIn_image_homeomorph Φ hx0
      rw [hxeq, ← gsep_z_compl_toExt_annulusAt_eq] at h1
      exact h1.symm
    have hcy : connectedComponentIn (toExt (annulusAt (q + p) ε δ))ᶜ y =
        Φ '' connectedComponentIn (toExt (annulusAt q ε δ))ᶜ (Φ.symm y) := by
      have h1 := gsep_z_connectedComponentIn_image_homeomorph Φ hy0
      rw [hyeq, ← gsep_z_compl_toExt_annulusAt_eq] at h1
      exact h1.symm
    have hxy0 : connectedComponentIn (toExt (annulusAt q ε δ))ᶜ (Φ.symm x) ≠
        connectedComponentIn (toExt (annulusAt q ε δ))ᶜ (Φ.symm y) := by
      intro heq
      exact hxy (by rw [hcx, hcy, heq])
    have hne0 := hγ.2.2 (Φ.symm x) hx0 (Φ.symm y) hy0 hxy0
    intro heq
    apply hne0
    have hcx' : connectedComponentIn (toExt (gsep_z_translateCurve p γ).closedTrace)ᶜ x =
        Φ '' connectedComponentIn (toExt γ.closedTrace)ᶜ (Φ.symm x) := by
      have h1 := gsep_z_connectedComponentIn_image_homeomorph Φ hx0'
      rw [hxeq, ← gsep_z_compl_toExt_translate_eq, ← gsep_z_translateCurve_closedTrace] at h1
      exact h1.symm
    have hcy' : connectedComponentIn (toExt (gsep_z_translateCurve p γ).closedTrace)ᶜ y =
        Φ '' connectedComponentIn (toExt γ.closedTrace)ᶜ (Φ.symm y) := by
      have h1 := gsep_z_connectedComponentIn_image_homeomorph Φ hy0'
      rw [hyeq, ← gsep_z_compl_toExt_translate_eq, ← gsep_z_translateCurve_closedTrace] at h1
      exact h1.symm
    have himg : Φ '' connectedComponentIn (toExt γ.closedTrace)ᶜ (Φ.symm x) =
        Φ '' connectedComponentIn (toExt γ.closedTrace)ᶜ (Φ.symm y) := by
      rw [← hcx', ← hcy', heq]
    exact Set.image_injective.mpr Φ.injective himg

theorem gsep_z_translateCurve_translateCurve (p q : ℂ) (γ : LRCurve) :
    (gsep_z_translateCurve p (gsep_z_translateCurve q γ)).toFun = (gsep_z_translateCurve (q + p) γ).toFun := by
  funext t
  show γ.toFun t + q + p = γ.toFun t + (q + p)
  ring

theorem gsep_z_isCurveImage_translate (p : ℂ) (ε δ : ℝ) :
    IsCurveImage (· + p) (separatingCurves (annulus ε δ)) (separatingCurves (annulusAt p ε δ)) := by
  constructor
  · intro γ hγ
    refine ⟨gsep_z_translateCurve p γ, ?_, fun _ _ => rfl⟩
    have := gsep_z_isSeparatingCurve_translate 0 p ε δ (γ := γ) (by rwa [gsep_z_annulusAt_zero])
    rwa [zero_add] at this
  · intro γ' hγ'
    refine ⟨gsep_z_translateCurve (-p) γ', ?_, fun t ht => ?_⟩
    · have h1 : IsSeparatingCurve (annulusAt (p + -p) ε δ) (gsep_z_translateCurve (-p) γ') :=
        gsep_z_isSeparatingCurve_translate p (-p) ε δ hγ'
      rw [show p + -p = (0:ℂ) by ring, gsep_z_annulusAt_zero] at h1
      exact h1
    · show γ'.toFun t = (gsep_z_translateCurve (-p) γ').toFun t + p
      show γ'.toFun t = γ'.toFun t + -p + p
      ring

theorem gsep_z_isConformalOnto_translate (p : ℂ) (ε δ : ℝ) :
    IsConformalOnto (· + p) (annulus ε δ) (annulusAt p ε δ) := by
  refine ⟨(differentiable_id.add_const p).differentiableOn, fun z _ w _ h => by
    simpa using h, ?_⟩
  rw [← gsep_z_annulusAt_zero, ← gsep_z_annulusAt_eq_image, zero_add]

/-- **The extremal length of the separating curves of `annulusAt p ε δ` is `2π/log(δ/ε)`.** -/
theorem gsep_z_extremalLength_annulusAtSeparating_le (p : ℂ) {ε δ : ℝ} (h₁ : 0 < ε) (h₂ : ε < δ) :
    extremalLength (separatingCurves (annulusAt p ε δ))
      ≤ ENNReal.ofReal (2 * π / Real.log (δ / ε)) := by
  rw [thm3_1_conformal_invariance (isOpen_annulus ε δ) (gsep_z_isConformalOnto_translate p ε δ)
    (fun γ hγ => (image_mono Ioo_subset_Icc_self).trans hγ.2.1) (gsep_z_isCurveImage_translate p ε δ)]
  exact extremalLength_annulusSeparating_le h₁ h₂

/-! ### The isolated singleton component -/

/-- With exactly two components in `ℂ̄ ∖ B`, if the component of `x` is not everything, some
other point lies in a different component. -/
theorem gsep_z_exists_other_point {B : Set ℂ} (hB : IsDoublyConnected B) {x : ExtPlane}
    (hx : x ∈ (toExt B)ᶜ) :
    ∃ y ∈ (toExt B)ᶜ, connectedComponentIn (toExt B)ᶜ x ≠ connectedComponentIn (toExt B)ᶜ y := by
  obtain ⟨c₁, c₂, hne, huniv⟩ := Nat.card_eq_two_iff.mp hB.2.2
  have hmem : ∀ c : ConnectedComponents ↥(toExt B)ᶜ, c = c₁ ∨ c = c₂ := by
    intro c
    have h : c ∈ ({c₁, c₂} : Set (ConnectedComponents ↥(toExt B)ᶜ)) := by
      rw [huniv]; exact mem_univ c
    simpa only [mem_insert_iff, mem_singleton_iff] using h
  have hgoal : ∀ c : ConnectedComponents ↥(toExt B)ᶜ,
      c ≠ ConnectedComponents.mk (⟨x, hx⟩ : ↥(toExt B)ᶜ) →
      ∃ y ∈ (toExt B)ᶜ, connectedComponentIn (toExt B)ᶜ x ≠ connectedComponentIn (toExt B)ᶜ y := by
    intro c hc
    obtain ⟨q, hq⟩ := ConnectedComponents.surjective_coe c
    refine ⟨q.1, q.2, fun heq => ?_⟩
    apply hc
    rw [← hq, ConnectedComponents.coe_eq_coe]
    rw [connectedComponentIn_eq_image hx, connectedComponentIn_eq_image q.2] at heq
    exact (Set.image_injective.mpr Subtype.val_injective heq).symm
  rcases hmem (ConnectedComponents.mk (⟨x, hx⟩ : ↥(toExt B)ᶜ)) with hxc | hxc
  · exact hgoal c₂ (by rw [hxc]; exact hne.symm)
  · exact hgoal c₁ (by rw [hxc]; exact hne)

/-- With exactly two components in `ℂ̄ ∖ B`, the components of any two points lying in
*different* components exhaust `ℂ̄ ∖ B`. -/
theorem gsep_z_compl_eq_union_of_ne {B : Set ℂ} (hB : IsDoublyConnected B) {x y : ExtPlane}
    (hx : x ∈ (toExt B)ᶜ) (hy : y ∈ (toExt B)ᶜ)
    (hxy : connectedComponentIn (toExt B)ᶜ x ≠ connectedComponentIn (toExt B)ᶜ y) :
    (toExt B)ᶜ = connectedComponentIn (toExt B)ᶜ x ∪ connectedComponentIn (toExt B)ᶜ y := by
  obtain ⟨c₁, c₂, hne, huniv⟩ := Nat.card_eq_two_iff.mp hB.2.2
  have hmem : ∀ c : ConnectedComponents ↥(toExt B)ᶜ, c = c₁ ∨ c = c₂ := by
    intro c
    have h : c ∈ ({c₁, c₂} : Set (ConnectedComponents ↥(toExt B)ᶜ)) := by
      rw [huniv]; exact mem_univ c
    simpa only [mem_insert_iff, mem_singleton_iff] using h
  have hxy' : ConnectedComponents.mk (⟨x, hx⟩ : ↥(toExt B)ᶜ) ≠
      ConnectedComponents.mk (⟨y, hy⟩ : ↥(toExt B)ᶜ) := by
    intro h
    rw [ConnectedComponents.coe_eq_coe] at h
    apply hxy
    rw [connectedComponentIn_eq_image hx, connectedComponentIn_eq_image hy]
    exact congrArg (Set.image Subtype.val) h
  have key : ∀ d : ConnectedComponents ↥(toExt B)ᶜ,
      d = ConnectedComponents.mk (⟨x, hx⟩ : ↥(toExt B)ᶜ) ∨
        d = ConnectedComponents.mk (⟨y, hy⟩ : ↥(toExt B)ᶜ) := by
    intro d
    rcases hmem d with h1 | h1 <;>
      rcases hmem (ConnectedComponents.mk (⟨x, hx⟩ : ↥(toExt B)ᶜ)) with h2 | h2 <;>
      rcases hmem (ConnectedComponents.mk (⟨y, hy⟩ : ↥(toExt B)ᶜ)) with h3 | h3 <;>
      first
        | exact absurd (h2.trans h3.symm) hxy'
        | (left; exact h1.trans h2.symm)
        | (right; exact h1.trans h3.symm)
  apply Subset.antisymm
  · intro z hz
    rcases key (ConnectedComponents.mk (⟨z, hz⟩ : ↥(toExt B)ᶜ)) with h | h <;>
      rw [ConnectedComponents.coe_eq_coe, connectedComponent_eq_iff_mem] at h
    · left; rw [connectedComponentIn_eq_image hx]; exact ⟨⟨z, hz⟩, h, rfl⟩
    · right; rw [connectedComponentIn_eq_image hy]; exact ⟨⟨z, hz⟩, h, rfl⟩
  · exact union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)

/-- If `x`'s component in `ℂ̄ ∖ B` is the singleton `{x}`, some open `V ∋ x` has
`V ∖ {x} ⊆ toExt B`. -/
theorem gsep_z_exists_nbhd_of_singleton {B : Set ℂ} (hB : IsDoublyConnected B) {x : ExtPlane}
    (hx : x ∈ (toExt B)ᶜ) (hxpt : connectedComponentIn (toExt B)ᶜ x = {x}) :
    ∃ V : Set ExtPlane, IsOpen V ∧ x ∈ V ∧ ∀ z ∈ V, z ≠ x → z ∈ toExt B := by
  obtain ⟨y, hy, hxy⟩ := gsep_z_exists_other_point hB hx
  set C' := connectedComponentIn (toExt B)ᶜ y with hC'def
  have hC'closed : IsClosed C' := isClosed_connectedComponentIn_compl_toExt hB.1 y
  refine ⟨C'ᶜ, hC'closed.isOpen_compl, ?_, ?_⟩
  · intro hxC'
    have hxmem : x ∈ connectedComponentIn (toExt B)ᶜ x ∩ C' :=
      ⟨mem_connectedComponentIn hx, hxC'⟩
    rw [hxpt] at hxmem
    have hxC'' : x ∈ C' := hxmem.2
    have heq2 : connectedComponentIn (toExt B)ᶜ y = connectedComponentIn (toExt B)ᶜ x :=
      connectedComponentIn_eq hxC''
    exact hxy heq2.symm
  · intro z hz hzx
    by_contra hzB
    have hzcomp : z ∈ (toExt B)ᶜ := hzB
    have huniv : (toExt B)ᶜ = connectedComponentIn (toExt B)ᶜ x ∪ C' :=
      gsep_z_compl_eq_union_of_ne hB hx hy hxy
    rw [huniv, hxpt] at hzcomp
    rcases hzcomp with h | h
    · exact hzx (by simpa using h)
    · exact hz h

/-- Two points separated by disjoint open sets covering `F` lie in different components. -/
theorem gsep_z_connectedComponentIn_ne_of_separated {F U V : Set ExtPlane}
    (hUo : IsOpen U) (hVo : IsOpen V) (hUV : Disjoint U V) (hFUV : F ⊆ U ∪ V)
    {a b : ExtPlane} (haF : a ∈ F) (hbF : b ∈ F) (haU : a ∈ U) (hbV : b ∈ V) :
    connectedComponentIn F a ≠ connectedComponentIn F b := by
  intro heq
  have hsub : connectedComponentIn F a ⊆ U :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union hUo hVo hUV
      ((connectedComponentIn_subset F a).trans hFUV) ⟨a, mem_connectedComponentIn haF, haU⟩
  have hb' : b ∈ connectedComponentIn F a := heq ▸ mem_connectedComponentIn hbF
  exact Set.disjoint_left.1 hUV (hsub hb') hbV

/-- A general "monotonicity" fact: separating curves of a sub-domain `D ⊆ B` are separating
curves of `B`, given that distinct `B`-components correspond to distinct `D`-components. -/
theorem gsep_z_separatingCurves_mono {B D : Set ℂ} (hDB : D ⊆ B)
    (hcorr : ∀ x ∈ (toExt B)ᶜ, ∀ y ∈ (toExt B)ᶜ,
      connectedComponentIn (toExt B)ᶜ x ≠ connectedComponentIn (toExt B)ᶜ y →
        connectedComponentIn (toExt D)ᶜ x ≠ connectedComponentIn (toExt D)ᶜ y) :
    separatingCurves D ⊆ separatingCurves B := by
  rintro γ ⟨hclosed, htrace, hsep⟩
  have hcompl : (toExt B)ᶜ ⊆ (toExt D)ᶜ := compl_subset_compl.2 (image_mono hDB)
  exact ⟨hclosed, htrace.trans hDB,
    fun x hx y hy hxy => hsep x (hcompl hx) y (hcompl hy) (hcorr x hx y hy hxy)⟩

/-- Extremal length is antitone under inclusion of the curve family. -/
theorem gsep_z_extremalLength_mono_of_subset {Γ₁ Γ₂ : Set LRCurve} (h : Γ₁ ⊆ Γ₂) :
    extremalLength Γ₂ ≤ extremalLength Γ₁ := by
  unfold extremalLength extremalLengthIn
  refine iSup₂_mono fun ρ hρ => ENNReal.div_le_div_right ?_ _
  exact le_iInf₂ fun γ hγ => iInf₂_le γ (h hγ)

/-- The finite case: a bound `2π/log(δ₀/ε)` for every small `ε`. -/
theorem gsep_z_bound_finite {B : Set ℂ} (hB : IsDoublyConnected B) {p : ℂ}
    (hx : ((p : ℂ) : ExtPlane) ∈ (toExt B)ᶜ)
    (hxpt : connectedComponentIn (toExt B)ᶜ ((p : ℂ) : ExtPlane) = {((p : ℂ) : ExtPlane)}) :
    ∃ δ0 > 0, ∀ ε, 0 < ε → ε < δ0 →
      extremalLength (separatingCurves B) ≤ ENNReal.ofReal (2 * π / Real.log (δ0 / ε)) := by
  obtain ⟨V, hVo, hxV, hVsub⟩ := gsep_z_exists_nbhd_of_singleton hB hx hxpt
  have hVnhd : V ∈ 𝓝 ((p : ℂ) : ExtPlane) := hVo.mem_nhds hxV
  have hpre : ((↑) : ℂ → ExtPlane) ⁻¹' V ∈ 𝓝 p := by
    rw [OnePoint.nhds_coe_eq, Filter.mem_map] at hVnhd; exact hVnhd
  obtain ⟨δ0, hδ00, hδ0sub⟩ := Metric.mem_nhds_iff.1 hpre
  obtain ⟨y, hy, hxy⟩ := gsep_z_exists_other_point hB hx
  set C' := connectedComponentIn (toExt B)ᶜ y with hC'def
  have hunion : (toExt B)ᶜ = {((p : ℂ) : ExtPlane)} ∪ C' := hxpt ▸ gsep_z_compl_eq_union_of_ne hB hx hy hxy
  have hxC' : ((p : ℂ) : ExtPlane) ∉ C' := by
    intro hmem
    have heq2 : connectedComponentIn (toExt B)ᶜ y = connectedComponentIn (toExt B)ᶜ ((p:ℂ):ExtPlane) :=
      connectedComponentIn_eq hmem
    exact hxy heq2.symm
  have hC'ball : C' ⊆ (toExt (ball p δ0))ᶜ := by
    intro z' hz' hz'mem
    obtain ⟨w, hw, rfl⟩ := hz'mem
    have hwV : (w : ExtPlane) ∈ V := hδ0sub hw
    by_cases hwp : w = p
    · rw [hwp] at hz'
      exact hxC' hz'
    · have hwB : (w : ExtPlane) ∈ toExt B := hVsub _ hwV (by
        intro heq; exact hwp (OnePoint.coe_injective heq))
      have hwB' : w ∈ B := coe_mem_toExt_iff.mp hwB
      have hwBc : (w : ExtPlane) ∈ (toExt B)ᶜ := connectedComponentIn_subset _ _ hz'
      exact hwBc (coe_mem_toExt_iff.mpr hwB')
  refine ⟨δ0, hδ00, fun ε hε0 hεδ0 => ?_⟩
  set m := (ε + δ0) / 2 with hmdef
  have hεm : ε < m := by rw [hmdef]; linarith
  have hmδ0 : m < δ0 := by rw [hmdef]; linarith
  have hm0 : 0 < m := lt_trans hε0 hεm
  have hAsub : annulusAt p ε δ0 ⊆ B := by
    intro z hz
    have hzp : z ≠ p := by
      intro heq
      rw [heq] at hz
      simp only [annulusAt, mem_setOf_eq, sub_self, norm_zero] at hz
      linarith [hz.1]
    have hzball : z ∈ ball p δ0 := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hz.2
    have hzV : (z : ExtPlane) ∈ V := hδ0sub hzball
    have hzB : (z : ExtPlane) ∈ toExt B := hVsub z hzV
      (fun heq => hzp (OnePoint.coe_injective heq))
    exact coe_mem_toExt_iff.mp hzB
  have hU : IsOpen (toExt (ball p m)) := isOpen_toExt_iff.mpr isOpen_ball
  have hW : IsOpen (toExt (closedBall p m))ᶜ :=
    ((isCompact_closedBall p m).image OnePoint.continuous_coe).isClosed.isOpen_compl
  have hUW : Disjoint (toExt (ball p m)) (toExt (closedBall p m))ᶜ := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ hz'
    exact hz' ⟨z, ball_subset_closedBall hz, rfl⟩
  have hFUV : (toExt (annulusAt p ε δ0))ᶜ ⊆ toExt (ball p m) ∪ (toExt (closedBall p m))ᶜ := by
    intro w hw
    induction w using OnePoint.rec with
    | infty => exact Or.inr (fun hmem => (extInf_notMem_toExt _) hmem)
    | coe z =>
      rw [coe_mem_compl_toExt_iff] at hw
      have hw' : ‖z - p‖ ≤ ε ∨ δ0 ≤ ‖z - p‖ := by
        by_contra hc
        push Not at hc
        exact hw ⟨hc.1, hc.2⟩
      rcases hw' with hw' | hw'
      · left
        refine ⟨z, ?_, rfl⟩
        rw [Metric.mem_ball, dist_eq_norm]
        linarith
      · right
        intro hmem
        obtain ⟨z', hz', hz'eq⟩ := hmem
        have hzz' : z' = z := OnePoint.coe_injective hz'eq
        rw [hzz', mem_closedBall_iff_norm] at hz'
        linarith
  have hxU : ((p : ℂ) : ExtPlane) ∈ toExt (ball p m) := ⟨p, by simp [hm0], rfl⟩
  have hcorr : ∀ x' ∈ (toExt B)ᶜ, ∀ y' ∈ (toExt B)ᶜ,
      connectedComponentIn (toExt B)ᶜ x' ≠ connectedComponentIn (toExt B)ᶜ y' →
      connectedComponentIn (toExt (annulusAt p ε δ0))ᶜ x' ≠
        connectedComponentIn (toExt (annulusAt p ε δ0))ᶜ y' := by
    intro x' hx' y' hy' hxy'
    have hcomplsub : (toExt B)ᶜ ⊆ (toExt (annulusAt p ε δ0))ᶜ :=
      compl_subset_compl.2 (image_mono hAsub)
    have hx'F : x' ∈ (toExt (annulusAt p ε δ0))ᶜ := hcomplsub hx'
    have hy'F : y' ∈ (toExt (annulusAt p ε δ0))ᶜ := hcomplsub hy'
    have hCW : C' ⊆ (toExt (closedBall p m))ᶜ := fun z' hz' hz'mem =>
      hC'ball hz' (image_mono (closedBall_subset_ball hmδ0) hz'mem)
    rw [hunion] at hx' hy'
    rcases hx' with hx'p | hx'C <;> rcases hy' with hy'p | hy'C
    · exact absurd (by rw [hx'p, hy'p]) hxy'
    · exact gsep_z_connectedComponentIn_ne_of_separated hU hW hUW hFUV hx'F hy'F (hx'p ▸ hxU)
        (hCW hy'C)
    · exact gsep_z_connectedComponentIn_ne_of_separated hW hU hUW.symm
        (hFUV.trans (union_comm _ _).subset) hx'F hy'F (hCW hx'C) (hy'p ▸ hxU)
    · have e1 : connectedComponentIn (toExt B)ᶜ x' = connectedComponentIn (toExt B)ᶜ y := by
        first
        | exact connectedComponentIn_eq hx'C
        | exact (connectedComponentIn_eq hx'C).symm
      have e2 : connectedComponentIn (toExt B)ᶜ y' = connectedComponentIn (toExt B)ᶜ y := by
        first
        | exact connectedComponentIn_eq hy'C
        | exact (connectedComponentIn_eq hy'C).symm
      exact absurd (e1.trans e2.symm) hxy'
  have hsub2 : separatingCurves (annulusAt p ε δ0) ⊆ separatingCurves B :=
    gsep_z_separatingCurves_mono hAsub hcorr
  exact (gsep_z_extremalLength_mono_of_subset hsub2).trans
    (gsep_z_extremalLength_annulusAtSeparating_le p hε0 hεδ0)

/-- The infinite case: a bound `2π/log(R/M0)` for every large `R`. -/
theorem gsep_z_bound_infinite {B : Set ℂ} (hB : IsDoublyConnected B)
    (hx : (extInf : ExtPlane) ∈ (toExt B)ᶜ)
    (hxpt : connectedComponentIn (toExt B)ᶜ (extInf : ExtPlane) = {(extInf : ExtPlane)}) :
    ∃ M0 > 0, ∀ R, M0 < R →
      extremalLength (separatingCurves B) ≤ ENNReal.ofReal (2 * π / Real.log (R / M0)) := by
  obtain ⟨V, hVo, hxV, hVsub⟩ := gsep_z_exists_nbhd_of_singleton hB hx hxpt
  have hVnhd : V ∈ 𝓝 (extInf : ExtPlane) := hVo.mem_nhds hxV
  obtain ⟨s, ⟨hsc, hscpt⟩, hssub⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.1 hVnhd
  obtain ⟨M1, hM1⟩ := isBounded_iff_forall_norm_le.1 hscpt.isBounded
  set M0 := max M1 1 with hM0def
  have hM00 : 0 < M0 := lt_max_of_lt_right one_pos
  have hM0sub : ∀ z : ℂ, ‖z‖ > M0 → (z : ExtPlane) ∈ V := by
    intro z hz
    have hzs : z ∉ s := fun h => by
      have := hM1 z h; simp only [hM0def] at hz; linarith [le_max_left M1 (1:ℝ)]
    exact hssub (Or.inl ⟨z, hzs, rfl⟩)
  obtain ⟨y, hy, hxy⟩ := gsep_z_exists_other_point hB hx
  set C' := connectedComponentIn (toExt B)ᶜ y with hC'def
  have hunion : (toExt B)ᶜ = {(extInf : ExtPlane)} ∪ C' :=
    hxpt ▸ gsep_z_compl_eq_union_of_ne hB hx hy hxy
  have hxC' : (extInf : ExtPlane) ∉ C' := by
    intro hmem
    have heq2 : connectedComponentIn (toExt B)ᶜ y = connectedComponentIn (toExt B)ᶜ (extInf : ExtPlane) :=
      connectedComponentIn_eq hmem
    exact hxy heq2.symm
  have hC'ball : C' ⊆ toExt (closedBall (0:ℂ) M0) := by
    intro z' hz'
    have hz'B : z' ∈ (toExt B)ᶜ := connectedComponentIn_subset _ _ hz'
    induction z' using OnePoint.rec with
    | infty => exact absurd hz' hxC'
    | coe w =>
      by_contra hwmem
      have hwnorm : ‖w‖ > M0 := by
        by_contra hc
        push Not at hc
        exact hwmem ⟨w, mem_closedBall_iff_norm.2 (by simpa using hc), rfl⟩
      have hwV : (w : ExtPlane) ∈ V := hM0sub w hwnorm
      have hwB : (w : ExtPlane) ∈ toExt B := hVsub _ hwV (OnePoint.coe_ne_infty w)
      exact hz'B hwB
  refine ⟨M0, hM00, fun R hM0R => ?_⟩
  set m := (M0 + R) / 2 with hmdef
  have hM0m : M0 < m := by rw [hmdef]; linarith
  have hmR : m < R := by rw [hmdef]; linarith
  have hm0 : 0 < m := lt_trans hM00 hM0m
  have hAsub : annulus M0 R ⊆ B := by
    intro z hz
    have hzV : (z : ExtPlane) ∈ V := hM0sub z hz.1
    have hzB : (z : ExtPlane) ∈ toExt B := hVsub z hzV (OnePoint.coe_ne_infty z)
    exact coe_mem_toExt_iff.mp hzB
  have hU : IsOpen (toExt (closedBall (0:ℂ) m))ᶜ :=
    ((isCompact_closedBall (0:ℂ) m).image OnePoint.continuous_coe).isClosed.isOpen_compl
  have hW : IsOpen (toExt (ball (0:ℂ) m)) := isOpen_toExt_iff.mpr isOpen_ball
  have hUW : Disjoint (toExt (closedBall (0:ℂ) m))ᶜ (toExt (ball (0:ℂ) m)) := by
    rw [Set.disjoint_right]
    rintro _ ⟨z, hz, rfl⟩ hz'
    exact hz' ⟨z, ball_subset_closedBall hz, rfl⟩
  have hFUV : (toExt (annulus M0 R))ᶜ ⊆
      (toExt (closedBall (0:ℂ) m))ᶜ ∪ toExt (ball (0:ℂ) m) := by
    intro w hw
    induction w using OnePoint.rec with
    | infty => left; exact fun hmem => (extInf_notMem_toExt _) hmem
    | coe z =>
      rw [coe_mem_compl_toExt_iff] at hw
      have hw' : ‖z‖ ≤ M0 ∨ R ≤ ‖z‖ := by
        by_contra hc
        push Not at hc
        exact hw ⟨hc.1, hc.2⟩
      rcases hw' with hw' | hw'
      · right
        refine ⟨z, ?_, rfl⟩
        rw [mem_ball_iff_norm]
        simpa using lt_of_le_of_lt hw' hM0m
      · left
        intro hmem
        obtain ⟨z', hz', hz'eq⟩ := hmem
        have hzz' : z' = z := OnePoint.coe_injective hz'eq
        rw [hzz', mem_closedBall_iff_norm] at hz'
        simp only [sub_zero] at hz'
        linarith
  have hxU : (extInf : ExtPlane) ∈ (toExt (closedBall (0:ℂ) m))ᶜ := extInf_notMem_toExt _
  have hcorr : ∀ x' ∈ (toExt B)ᶜ, ∀ y' ∈ (toExt B)ᶜ,
      connectedComponentIn (toExt B)ᶜ x' ≠ connectedComponentIn (toExt B)ᶜ y' →
      connectedComponentIn (toExt (annulus M0 R))ᶜ x' ≠
        connectedComponentIn (toExt (annulus M0 R))ᶜ y' := by
    intro x' hx' y' hy' hxy'
    have hcomplsub : (toExt B)ᶜ ⊆ (toExt (annulus M0 R))ᶜ :=
      compl_subset_compl.2 (image_mono hAsub)
    have hx'F : x' ∈ (toExt (annulus M0 R))ᶜ := hcomplsub hx'
    have hy'F : y' ∈ (toExt (annulus M0 R))ᶜ := hcomplsub hy'
    have hCW : C' ⊆ toExt (ball (0:ℂ) m) := fun z' hz' =>
      image_mono (closedBall_subset_ball hM0m) (hC'ball hz')
    rw [hunion] at hx' hy'
    rcases hx' with hx'p | hx'C <;> rcases hy' with hy'p | hy'C
    · exact absurd (by rw [hx'p, hy'p]) hxy'
    · exact gsep_z_connectedComponentIn_ne_of_separated hU hW hUW hFUV hx'F hy'F (hx'p ▸ hxU)
        (hCW hy'C)
    · exact gsep_z_connectedComponentIn_ne_of_separated hW hU hUW.symm
        (hFUV.trans (union_comm _ _).subset) hx'F hy'F (hCW hx'C) (hy'p ▸ hxU)
    · have e1 : connectedComponentIn (toExt B)ᶜ x' = connectedComponentIn (toExt B)ᶜ y := by
        first
        | exact connectedComponentIn_eq hx'C
        | exact (connectedComponentIn_eq hx'C).symm
      have e2 : connectedComponentIn (toExt B)ᶜ y' = connectedComponentIn (toExt B)ᶜ y := by
        first
        | exact connectedComponentIn_eq hy'C
        | exact (connectedComponentIn_eq hy'C).symm
      exact absurd (e1.trans e2.symm) hxy'
  have hsub2 : separatingCurves (annulus M0 R) ⊆ separatingCurves B :=
    gsep_z_separatingCurves_mono hAsub hcorr
  exact (gsep_z_extremalLength_mono_of_subset hsub2).trans
    (extremalLength_annulusSeparating_le hM00 hM0R)

theorem gsep_z_tendsto_ofReal_two_pi_div_nat :
    Tendsto (fun n : ℕ => ENNReal.ofReal (2 * π / n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (2 * π) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (2 * π)
  have h2 := ENNReal.tendsto_ofReal h1
  simpa using h2

/-- **Z.** Degenerate case: if some complementary component of `B` is a single point, the
separating curves have extremal length `0`. -/
theorem gsep_extremalLength_separatingCurves_eq_zero_of_singleton {B : Set ℂ}
    (hB : IsDoublyConnected B) {x : ExtPlane} (hx : x ∈ (toExt B)ᶜ)
    (hxpt : connectedComponentIn (toExt B)ᶜ x = {x}) :
    extremalLength (separatingCurves B) = 0 := by
  induction x using OnePoint.rec with
  | infty =>
    obtain ⟨M0, hM00, hbound⟩ := gsep_z_bound_infinite hB hx hxpt
    apply le_antisymm _ bot_le
    refine ge_of_tendsto gsep_z_tendsto_ofReal_two_pi_div_nat (Filter.eventually_atTop.2 ⟨1, ?_⟩)
    intro n hn
    set R := M0 * Real.exp (n : ℝ) with hRdef
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hM0R : M0 < R := by
      rw [hRdef]
      have hexp1 : (1:ℝ) < Real.exp (n : ℝ) := Real.one_lt_exp_iff.2 (by linarith)
      nlinarith [hexp1, hM00]
    have hlogeq : Real.log (R / M0) = n := by
      have hReq : R / M0 = Real.exp (n : ℝ) := by
        rw [hRdef, mul_div_cancel_left₀ _ hM00.ne']
      rw [hReq]; exact Real.log_exp n
    have := hbound R hM0R
    rwa [hlogeq] at this
  | coe p =>
    obtain ⟨δ0, hδ00, hbound⟩ := gsep_z_bound_finite hB hx hxpt
    apply le_antisymm _ bot_le
    refine ge_of_tendsto gsep_z_tendsto_ofReal_two_pi_div_nat (Filter.eventually_atTop.2 ⟨1, ?_⟩)
    intro n hn
    set ε := δ0 * Real.exp (-(n : ℝ)) with hεdef
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hε0 : 0 < ε := by rw [hεdef]; positivity
    have hεδ0 : ε < δ0 := by
      rw [hεdef]
      have hexp1 : Real.exp (-(n : ℝ)) < 1 := by
        rw [Real.exp_lt_one_iff]; linarith
      nlinarith [hexp1, hδ00]
    have hlogeq : Real.log (δ0 / ε) = n := by
      rw [hεdef, show δ0 / (δ0 * Real.exp (-(n:ℝ))) = Real.exp (n:ℝ) by
        rw [div_mul_eq_div_div, div_self hδ00.ne', one_div, ← Real.exp_neg, neg_neg]]
      exact Real.log_exp n
    have := hbound ε hε0 hεδ0
    rwa [hlogeq] at this



/-- A doubly connected domain with a one-point complementary component has infinite modulus
(Theorem 2.1, cases (i)/(ii), with the uniqueness lemmas). -/
theorem gsep_dcModulus_eq_top_of_singleton {B : Set ℂ} (hB : IsDoublyConnected B) {x : ExtPlane}
    (hx : x ∈ (toExt B)ᶜ) (hxpt : connectedComponentIn (toExt B)ᶜ x = {x}) : dcModulus B = ⊤ := by
  unfold dcModulus
  rw [if_neg]
  rintro ⟨r₁, r₂, h₁, h₂, hBA⟩
  rcases canonical_form_of_degenerate_component hB hx hxpt with hP | hP
  · exact thm2_1_canonical_unique_plane_annulus h₁ h₂ ((hP.symm hB.1).trans hBA)
  · exact thm2_1_canonical_unique_disc_annulus h₁ h₂ ((hP.symm hB.1).trans hBA)

/-- **Theorem 4.9**: `M(B) = 2π / λ(Γ)`, `Γ` the family of closed curves in `B` separating the
two components of `ℂ̄ ∖ B`.

Proved (2026-09-21) from the `gsep_` pieces above: the conformal model of Theorem 2.1 carries the separating
curves onto those of the annulus (`gsep_isCurveImage_separatingCurves`, end correspondence without the Jordan
curve theorem), so Theorem 3.1 transports `extremalLength_annulusSeparating`; a one-point complementary
component gives `M(B) = ∞` and `λ = 0` (`gsep_extremalLength_separatingCurves_eq_zero_of_singleton`). -/
theorem thm4_9_dcModulus_eq {B : Set ℂ} (hB : IsDoublyConnected B) :
    dcModulus B = ENNReal.ofReal (2 * π) / extremalLength (separatingCurves B) := by
  have h2π : ENNReal.ofReal (2 * π) ≠ 0 := (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne'
  by_cases hdeg : ∃ x ∈ (toExt B)ᶜ, connectedComponentIn (toExt B)ᶜ x = {x}
  · obtain ⟨x, hx, hxpt⟩ := hdeg
    rw [gsep_dcModulus_eq_top_of_singleton hB hx hxpt,
      gsep_extremalLength_separatingCurves_eq_zero_of_singleton hB hx hxpt, ENNReal.div_zero h2π]
  push Not at hdeg
  obtain ⟨r₁, r₂, h₁, h₂, hBA⟩ := thm2_1_canonical_form_annulus hB hdeg
  obtain ⟨g, hg⟩ := hBA
  have hf : IsConformalOnto (Function.invFunOn g B) (annulus r₁ r₂) B := hg.symm hB.1
  have hlam : extremalLength (separatingCurves B) =
      extremalLength (separatingCurves (annulus r₁ r₂)) :=
    thm3_1_conformal_invariance (isOpen_annulus r₁ r₂) hf
      (fun γ hγ => (image_mono Ioo_subset_Icc_self).trans hγ.2.1)
      (gsep_isCurveImage_separatingCurves h₁ h₂ hB hf)
  have hL : 0 < Real.log (r₂ / r₁) := Real.log_pos (by rw [lt_div_iff₀ h₁, one_mul]; exact h₂)
  rw [dcModulus_eq_of_equiv hB.1 h₁ h₂ ⟨g, hg⟩, hlam, extremalLength_annulusSeparating h₁ h₂,
    ← ENNReal.ofReal_div_of_pos (div_pos Real.two_pi_pos hL)]
  congr 1
  field_simp

/-! ### Corollaries of Theorem 4.9 — helpers of piece E -/


/-- **E1.** The separating curves of a domain conformally equivalent to an annulus are carried onto those of
the annulus (the reverse of `gsep_isCurveImage_separatingCurves`, via `IsCurveImage.inv` and an `EqOn`
transfer). -/
theorem cor_isCurveImage_separatingCurves_symm {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂)
    {B : Set ℂ} (hB : IsDoublyConnected B) {f : ℂ → ℂ} (hf : IsConformalOnto f B (annulus r₁ r₂)) :
    IsCurveImage f (separatingCurves B) (separatingCurves (annulus r₁ r₂)) := by
  have hBo : IsOpen B := hB.1
  set g := Function.invFunOn f B with hgdef
  have hg : IsConformalOnto g (annulus r₁ r₂) B := hf.symm hBo
  have hgf : IsCurveImage g (separatingCurves (annulus r₁ r₂)) (separatingCurves B) :=
    gsep_isCurveImage_separatingCurves h₁ h₂ hB hg
  have hΓtrace : ∀ γ ∈ separatingCurves (annulus r₁ r₂), γ.trace ⊆ annulus r₁ r₂ :=
    fun γ hγ => (image_mono Ioo_subset_Icc_self).trans hγ.2.1
  have hinv := hgf.inv hg.2.1 hΓtrace
  have hEqOn : Set.EqOn (Function.invFunOn g (annulus r₁ r₂)) f B := by
    intro z hz
    have hzmem : z ∈ g '' (annulus r₁ r₂) := hg.2.2 ▸ hz
    have h2 : g (Function.invFunOn g (annulus r₁ r₂) z) = z := Function.invFunOn_eq hzmem
    have h1 : g (f z) = z := hf.2.1.leftInvOn_invFunOn hz
    exact hg.2.1 (Function.invFunOn_mem hzmem) (hf.mapsTo hz) (h2.trans h1.symm)
  refine ⟨fun γ hγ => ?_, fun γ' hγ' => ?_⟩
  · obtain ⟨γ', hγ', heq⟩ := hinv.1 γ hγ
    refine ⟨γ', hγ', fun t ht => ?_⟩
    have hmem : γ.toFun t ∈ B := hγ.2.1 (mem_image_of_mem _ (Ioo_subset_Icc_self ht))
    rw [heq ht]
    exact hEqOn hmem
  · obtain ⟨γ, hγ, heq⟩ := hinv.2 γ' hγ'
    refine ⟨γ, hγ, fun t ht => ?_⟩
    have hmem : γ.toFun t ∈ B := hγ.2.1 (mem_image_of_mem _ (Ioo_subset_Icc_self ht))
    rw [heq ht]
    exact hEqOn hmem

/-- **E2.** Extremal metrics pull back along conformal maps: if `ρ'` is extremal for `Γ'` on `D'` and
`f : D → D'` carries `Γ` onto `Γ'`, then `ρ'(f z) |f'(z)|` is extremal for `Γ` on `D`. -/
theorem cor_isExtremalMetric_of_conformal {D D' : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : IsConformalOnto f D D') {Γ Γ' : Set LRCurve} (hΓ : ∀ γ ∈ Γ, γ.trace ⊆ D)
    (himg : IsCurveImage f Γ Γ') {ρ' : ℂ → ℝ≥0∞} (hρ' : IsExtremalMetric D' Γ' ρ') :
    IsExtremalMetric D Γ (D.indicator fun z => ρ' (f z) * ‖deriv f z‖ₑ) := by
  obtain ⟨⟨hρ'm, hρ'0, hρ'top⟩, hratio⟩ := hρ'
  have hA : rhoArea (D.indicator fun z => ρ' (f z) * ‖deriv f z‖ₑ) D = rhoArea ρ' D' :=
    rhoArea_pullback hD hf ρ'
  have hL : ⨅ γ ∈ Γ, (γ.rhoLength (D.indicator fun z => ρ' (f z) * ‖deriv f z‖ₑ)) ^ 2 =
      ⨅ γ' ∈ Γ', γ'.rhoLength ρ' ^ 2 :=
    (iInf_rhoLength_sq_pullback hD hf hΓ himg ρ').symm
  refine ⟨⟨measurable_pullback_density hD hf.1.continuousOn hρ'm, ?_, ?_⟩, ?_⟩
  · rw [hA]; exact hρ'0
  · rw [hA]; exact hρ'top
  · rw [hL, hA, hratio]
    exact thm3_1_conformal_invariance hD hf hΓ himg

/-! ### Corollaries of Theorem 4.9 — helpers of piece B -/


/-- **B1.** A closed curve avoiding `0` whose complement has `0` and `∞` in different components
meets every ray from the origin. -/
theorem cor_exists_mem_ray_of_separates {γ : LRCurve} (hγ : γ.IsClosedCurve)
    (h0 : (0 : ℂ) ∉ γ.closedTrace)
    (hne : connectedComponentIn (toExt γ.closedTrace)ᶜ ((0 : ℂ) : ExtPlane) ≠
      connectedComponentIn (toExt γ.closedTrace)ᶜ extInf) (φ : ℝ) :
    ∃ t ∈ Icc (0 : ℝ) 1, γ.toFun t = (‖γ.toFun t‖ : ℂ) * exp (φ * I) := by
  by_contra hno
  push Not at hno
  have hSC : toExt ((fun s : ℝ => (s : ℂ) * exp (φ * I)) '' Ici 0) ∪ {extInf}
      ⊆ (toExt γ.closedTrace)ᶜ := by
    rintro p (⟨z, ⟨s, hs, rfl⟩, rfl⟩ | hp) ⟨w, ⟨t, ht, rfl⟩, hwz⟩
    · have hwz' : γ.toFun t = (s : ℂ) * exp (φ * I) := OnePoint.coe_injective hwz
      have hnorm : ‖γ.toFun t‖ = s := by
        rw [hwz', norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hs]
      exact hno t ht (by rw [hnorm]; exact hwz')
    · rw [mem_singleton_iff] at hp
      exact OnePoint.coe_ne_infty _ (hwz.trans hp)
  have h0S : ((0 : ℂ) : ExtPlane) ∈ toExt ((fun s : ℝ => (s : ℂ) * exp (φ * I)) '' Ici 0) ∪ {extInf} :=
    Or.inl ⟨0, ⟨0, self_mem_Ici, by simp⟩, rfl⟩
  have hinfS : extInf ∈ toExt ((fun s : ℝ => (s : ℂ) * exp (φ * I)) '' Ici 0) ∪ {extInf} :=
    Or.inr (mem_singleton _)
  exact hne (connectedComponentIn_eq
    ((isPreconnected_toExt_ray_insert φ).subset_connectedComponentIn h0S hSC hinfS))

/-- **B2.** For such a curve, `∫_γ |dz| / (2π|z|) ≥ 1`. -/
theorem cor_one_le_rhoLength_of_separates {γ : LRCurve} (hγ : γ.IsClosedCurve)
    (h0 : (0 : ℂ) ∉ γ.closedTrace)
    (hne : connectedComponentIn (toExt γ.closedTrace)ᶜ ((0 : ℂ) : ExtPlane) ≠
      connectedComponentIn (toExt γ.closedTrace)ᶜ extInf) :
    1 ≤ γ.rhoLength fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖)) := by
  have hray := cor_exists_mem_ray_of_separates hγ h0 hne
  obtain ⟨K, hK, -⟩ := hγ
  have hne' : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ≠ 0 := fun t ht h0' => h0 ⟨t, ht, h0'⟩
  have hI := two_pi_le_lintegral_norm_deriv_div_norm hK hne' hray
  have hlen : (γ.rhoLength fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖))) =
      ENNReal.ofReal (1 / (2 * π)) *
        ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (‖deriv γ.toFun t‖ / ‖γ.toFun t‖) := by
    unfold LRCurve.rhoLength
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1 / (2 * π * ‖γ.toFun t‖) by positivity),
      ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1 / (2 * π) by positivity)]
    congr 1
    ring
  rw [hlen]
  have hstep : ENNReal.ofReal (1 / (2 * π)) * ENNReal.ofReal (2 * π) ≤
      ENNReal.ofReal (1 / (2 * π)) *
        ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (‖deriv γ.toFun t‖ / ‖γ.toFun t‖) :=
    mul_le_mul_right hI _
  rw [← ENNReal.ofReal_mul (by positivity),
    show (1 / (2 * π)) * (2 * π) = 1 by field_simp, ENNReal.ofReal_one] at hstep
  exact hstep

/-! ### Corollaries of Theorem 4.9 — helpers of piece U -/


/-- General-measure-space port of `ae_eq_const_of_sq_setLIntegral_eq`: the equality case of the
Cauchy–Schwarz inequality `(∫ρ dμ)² ≤ μ(univ) * ∫ρ² dμ` forces `ρ` to be a.e. constant. -/
theorem cor_a_ae_eq_const_of_sq_lintegral_eq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {ρ : X → ℝ≥0∞} (hρ : Measurable ρ)
    (hV0 : μ Set.univ ≠ 0) (hVt : μ Set.univ ≠ ⊤) (hA : ∫⁻ x, ρ x ^ 2 ∂μ ≠ ⊤)
    (heq : (∫⁻ x, ρ x ∂μ) ^ 2 = μ Set.univ * ∫⁻ x, ρ x ^ 2 ∂μ) :
    ∀ᵐ x ∂μ, ρ x = (∫⁻ x, ρ x ∂μ) / μ Set.univ := by
  obtain ⟨I, hI⟩ : ∃ I, ∫⁻ x, ρ x ∂μ = I := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A, ∫⁻ x, ρ x ^ 2 ∂μ = A := ⟨_, rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V, μ Set.univ = V := ⟨_, rfl⟩
  rw [hI, hAd, hVd] at heq
  rw [hAd] at hA
  rw [hVd] at hV0 hVt
  rw [hI, hVd]
  have hIt : I ≠ ⊤ := fun h => by
    rw [h, ENNReal.pow_eq_top_iff.2 ⟨rfl, two_ne_zero⟩] at heq
    exact ENNReal.mul_ne_top hVt hA heq.symm
  have hct : I / V ≠ ⊤ := ENNReal.div_ne_top hIt hV0
  have hcI : I / V * I = A := by
    rw [div_eq_mul_inv, mul_right_comm, ← sq, heq, mul_comm V, mul_assoc,
      ENNReal.mul_inv_cancel hV0 hVt, mul_one]
  have hc2V : (I / V) ^ 2 * V = A := by
    rw [sq, mul_assoc, ENNReal.div_mul_cancel hV0 hVt, hcI]
  have hmeas : Measurable fun x => (ρ x - I / V) ^ 2 + (I / V - ρ x) ^ 2 := by fun_prop
  have hsum : (∫⁻ x, ((ρ x - I / V) ^ 2 + (I / V - ρ x) ^ 2) ∂μ) + 2 * A = A + A := by
    have h := lintegral_congr (μ := μ)
      fun x => ennreal_sq_sub_add_sq_sub (x := ρ x) hct
    rw [lintegral_add_right _ (hρ.const_mul _), lintegral_add_right _ measurable_const,
      lintegral_const_mul _ hρ, lintegral_const, hI, hAd, hVd,
      mul_assoc, hcI, hc2V] at h
    exact h
  have hzero : ∫⁻ x, ((ρ x - I / V) ^ 2 + (I / V - ρ x) ^ 2) ∂μ = 0 := by
    have h2A : 2 * A ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hA
    have h' : (∫⁻ x, ((ρ x - I / V) ^ 2 + (I / V - ρ x) ^ 2) ∂μ) + 2 * A = 0 + 2 * A := by
      rw [zero_add, hsum, two_mul]
    exact (ENNReal.add_left_inj h2A).1 h'
  filter_upwards [(lintegral_eq_zero_iff hmeas).1 hzero] with x hx
  simp only [Pi.zero_apply, add_eq_zero, pow_eq_zero_iff two_ne_zero, tsub_eq_zero_iff_le] at hx
  exact le_antisymm hx.1 hx.2

/-- **U (owner -46).** Uniqueness of the extremal metric of the separating curves of an annulus:
a density attaining the extremal length is a.e. a constant multiple of `1/|z|`. -/
theorem cor_ae_eq_of_annulus_extremal {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) {σ : ℂ → ℝ≥0∞}
    (hσ : Measurable σ) (hA0 : rhoArea σ (annulus r₁ r₂) ≠ 0)
    (hAt : rhoArea σ (annulus r₁ r₂) ≠ ⊤)
    (hratio : (⨅ γ ∈ separatingCurves (annulus r₁ r₂), γ.rhoLength σ ^ 2) /
      rhoArea σ (annulus r₁ r₂) = ENNReal.ofReal (2 * π / Real.log (r₂ / r₁))) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ᵐ z ∂(volume.restrict (annulus r₁ r₂)), σ z = c * ENNReal.ofReal (1 / ‖z‖) := by
  set A := annulus r₁ r₂ with hAdef
  have hAo : IsOpen A := isOpen_annulus r₁ r₂
  have hLpos : 0 < Real.log (r₂ / r₁) :=
    Real.log_pos (by rw [lt_div_iff₀ h₁, one_mul]; exact h₂)
  have hLne0 : ENNReal.ofReal (Real.log (r₂ / r₁)) ≠ 0 := (ENNReal.ofReal_pos.2 hLpos).ne'
  have hLnetop : ENNReal.ofReal (Real.log (r₂ / r₁)) ≠ ⊤ := ENNReal.ofReal_ne_top
  set ℓ := ⨅ γ ∈ separatingCurves A, γ.rhoLength σ with hℓdef
  -- cross-multiply the hypothesis
  have hratio' : ℓ ^ 2 = ENNReal.ofReal (2 * π / Real.log (r₂ / r₁)) * rhoArea σ A := by
    rw [← iInf_rhoLength_sq] at hratio
    rw [← hratio, ENNReal.div_mul_cancel hA0 hAt]
  have hKEY : ENNReal.ofReal (Real.log (r₂ / r₁)) * ℓ ^ 2 =
      ENNReal.ofReal (2 * π) * rhoArea σ A := by
    have h2 : ENNReal.ofReal (2 * π / Real.log (r₂ / r₁)) =
        ENNReal.ofReal (2 * π) / ENNReal.ofReal (Real.log (r₂ / r₁)) :=
      ENNReal.ofReal_div_of_pos hLpos
    rw [hratio', h2, ← mul_assoc, mul_comm (ENNReal.ofReal (Real.log (r₂ / r₁))),
      ENNReal.div_mul_cancel hLne0 hLnetop]
  -- the density `g := 1/|z|` and the two chained inequalities forced to equalities
  set g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (1 / ‖z‖) with hgdef
  have hgm : Measurable g := (measurable_const.div measurable_norm).ennreal_ofReal
  have hg2 : ∫⁻ z in A, g z ^ 2 = ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (r₂ / r₁)) := by
    rw [← lintegral_annulus_inv_normSq h₁ h₂]
    refine setLIntegral_congr_fun hAo.measurableSet fun z _ => ?_
    rw [hgdef, ← ENNReal.ofReal_pow (show (0:ℝ) ≤ 1/‖z‖ by positivity), one_div_pow]
  have hab : (ℓ * ENNReal.ofReal (Real.log (r₂ / r₁))) ^ 2 ≤ (∫⁻ z in A, σ z * g z) ^ 2 :=
    pow_le_pow_left' (iInf_rhoLength_mul_log_le h₁ h₂ hσ) 2
  have hbc : (∫⁻ z in A, σ z * g z) ^ 2 ≤ rhoArea σ A * (∫⁻ z in A, g z ^ 2) :=
    setLIntegral_mul_sq_le hσ hgm
  have hac : (ℓ * ENNReal.ofReal (Real.log (r₂ / r₁))) ^ 2 = rhoArea σ A * (∫⁻ z in A, g z ^ 2) := by
    have hring : (ℓ * ENNReal.ofReal (Real.log (r₂ / r₁))) ^ 2 =
        ENNReal.ofReal (Real.log (r₂ / r₁)) * (ENNReal.ofReal (Real.log (r₂ / r₁)) * ℓ ^ 2) := by
      ring
    rw [hring, hKEY, hg2]
    ring
  have heqBC : (∫⁻ z in A, σ z * g z) ^ 2 = rhoArea σ A * (∫⁻ z in A, g z ^ 2) :=
    le_antisymm hbc (hac ▸ hab)
  -- the weighted measure `ν := (vol|_A).withDensity (g²)` and `h := σ · |z|`
  set g2 : ℂ → ℝ≥0∞ := fun z => g z ^ 2 with hg2def
  set ν : Measure ℂ := (volume.restrict A).withDensity g2 with hνdef
  set h : ℂ → ℝ≥0∞ := fun z => σ z * ENNReal.ofReal ‖z‖ with hhdef
  have hg2m : Measurable g2 := hgm.pow_const 2
  have hnormm : Measurable fun z : ℂ => ENNReal.ofReal ‖z‖ := measurable_norm.ennreal_ofReal
  have hhm : Measurable h := hσ.mul hnormm
  have hzne0 : ∀ z ∈ A, z ≠ 0 := by
    rintro z hz rfl
    have := hz.1
    rw [norm_zero] at this
    linarith
  have hg2pos : ∀ z ∈ A, g2 z ≠ 0 := by
    intro z hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr (hzne0 z hz)
    exact pow_ne_zero 2 (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hptwise1 : ∀ z ∈ A, g2 z * h z = σ z * g z := by
    intro z hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr (hzne0 z hz)
    have hcalc : (ENNReal.ofReal (1 / ‖z‖)) ^ 2 * ENNReal.ofReal ‖z‖ = ENNReal.ofReal (1 / ‖z‖) := by
      rw [← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ 1 / ‖z‖),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    show (ENNReal.ofReal (1 / ‖z‖)) ^ 2 * (σ z * ENNReal.ofReal ‖z‖) = σ z * ENNReal.ofReal (1 / ‖z‖)
    rw [mul_comm (σ z), ← mul_assoc, hcalc, mul_comm]
  have hptwise2 : ∀ z ∈ A, g2 z * (h z) ^ 2 = σ z ^ 2 := by
    intro z hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr (hzne0 z hz)
    have hcalc : (ENNReal.ofReal (1 / ‖z‖)) ^ 2 * (ENNReal.ofReal ‖z‖) ^ 2 = 1 := by
      rw [← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ 1 / ‖z‖), ← ENNReal.ofReal_pow hzpos.le,
        ← ENNReal.ofReal_mul (by positivity), show (1 / ‖z‖) ^ 2 * ‖z‖ ^ 2 = 1 by field_simp,
        ENNReal.ofReal_one]
    show (ENNReal.ofReal (1 / ‖z‖)) ^ 2 * (σ z * ENNReal.ofReal ‖z‖) ^ 2 = σ z ^ 2
    rw [mul_pow, mul_left_comm, hcalc, mul_one]
  have hνuniv : ν Set.univ = ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (r₂ / r₁)) := by
    rw [hνdef, withDensity_apply g2 MeasurableSet.univ, setLIntegral_univ]
    exact hg2
  have hνuniv0 : ν Set.univ ≠ 0 := by
    rw [hνuniv]
    exact (ENNReal.mul_pos (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne'
      (ENNReal.ofReal_pos.2 hLpos).ne').ne'
  have hνunivtop : ν Set.univ ≠ ⊤ := by
    rw [hνuniv]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hIntH : ∫⁻ z, h z ∂ν = ∫⁻ z in A, σ z * g z := by
    rw [hνdef, lintegral_withDensity_eq_lintegral_mul _ hg2m hhm]
    exact setLIntegral_congr_fun hAo.measurableSet fun z hz => hptwise1 z hz
  have hIntH2 : ∫⁻ z, (h z) ^ 2 ∂ν = rhoArea σ A := by
    rw [hνdef, lintegral_withDensity_eq_lintegral_mul _ hg2m (hhm.pow_const 2)]
    show ∫⁻ z in A, g2 z * h z ^ 2 = ∫⁻ z in A, σ z ^ 2
    exact setLIntegral_congr_fun hAo.measurableSet fun z hz => hptwise2 z hz
  have hHtop : ∫⁻ z, (h z) ^ 2 ∂ν ≠ ⊤ := hIntH2 ▸ hAt
  have heqFinal : (∫⁻ z, h z ∂ν) ^ 2 = ν Set.univ * ∫⁻ z, (h z) ^ 2 ∂ν := by
    rw [hIntH, hIntH2, hνuniv, heqBC, hg2]
    ring
  have hae := cor_a_ae_eq_const_of_sq_lintegral_eq hhm hνuniv0 hνunivtop hHtop heqFinal
  set c₀ := (∫⁻ z, h z ∂ν) / ν Set.univ with hc₀def
  have hae' : ∀ᵐ z ∂(volume.restrict A), h z = c₀ := by
    have hg2ne : ∀ᵐ z ∂(volume.restrict A), g2 z ≠ 0 := by
      filter_upwards [ae_restrict_mem hAo.measurableSet] with z hz
      exact hg2pos z hz
    have hae2 := (ae_withDensity_iff hg2m).mp hae
    filter_upwards [hae2, hg2ne] with z hz1 hz2
    exact hz1 hz2
  have hIntSGtop : ∫⁻ z in A, σ z * g z ≠ ⊤ := by
    intro hcontra
    have h2 : (∫⁻ z in A, σ z * g z) ^ 2 = ⊤ := by rw [hcontra]; simp
    rw [heqBC] at h2
    exact (ENNReal.mul_ne_top hAt (hg2 ▸ ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top)) h2
  have hc₀netop : c₀ ≠ ⊤ := by
    rw [hc₀def]; exact ENNReal.div_ne_top (hIntH ▸ hIntSGtop) hνuniv0
  have hc₀ne0 : c₀ ≠ 0 := by
    intro hc0
    have hInt0 : ∫⁻ z, h z ∂ν = 0 := by
      rw [hc₀def] at hc0
      rcases (ENNReal.div_eq_zero_iff).mp hc0 with h | h
      · exact h
      · exact absurd h hνunivtop
    rw [hInt0] at heqFinal
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at heqFinal
    have h0 : ∫⁻ z, (h z) ^ 2 ∂ν = 0 := by
      rcases mul_eq_zero.mp heqFinal.symm with h | h
      · exact absurd h hνuniv0
      · exact h
    rw [hIntH2] at h0
    exact hA0 h0
  refine ⟨c₀, hc₀ne0, hc₀netop, ?_⟩
  filter_upwards [hae', ae_restrict_mem hAo.measurableSet] with z hz1 hz2
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr (hzne0 z hz2)
  have hcalc2 : ENNReal.ofReal ‖z‖ * ENNReal.ofReal (1 / ‖z‖) = 1 := by
    rw [← ENNReal.ofReal_mul hzpos.le, mul_one_div_cancel hzpos.ne', ENNReal.ofReal_one]
  have hz1' : σ z * ENNReal.ofReal ‖z‖ = c₀ := hz1
  calc σ z = σ z * ENNReal.ofReal ‖z‖ * ENNReal.ofReal (1 / ‖z‖) := by
        rw [mul_assoc, hcalc2, mul_one]
    _ = c₀ * ENNReal.ofReal (1 / ‖z‖) := by rw [hz1']


/-! ### Corollaries of Theorem 4.9 — helpers of piece H -/


/-- `t ↦ exp(at)` (real `t`, complex constant `a`) has derivative `a·exp(at)`. -/
theorem cor_c_hasDerivAt_cexp_mul (a : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (a * t)) (a * Complex.exp (a * t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => a * (t : ℂ)) a t := by
    simpa using (hasDerivAt_id (t : ℂ)).comp_ofReal.const_mul a
  have h2 : HasDerivAt Complex.exp (Complex.exp (a * t)) (a * t) := Complex.hasDerivAt_exp _
  have h3 := h2.scomp t h1
  rw [smul_eq_mul] at h3
  exact h3

/-- The circle parametrization `t ↦ ρ e^{it}` has derivative `iρe^{it}`. -/
theorem cor_c_hasDerivAt_circle (ρ : ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (ρ : ℂ) * Complex.exp (t * I)) ((ρ : ℂ) * (I * Complex.exp (t * I))) t := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I t := by
    simpa using (hasDerivAt_id (t : ℂ)).comp_ofReal.mul_const I
  have h2 : HasDerivAt Complex.exp (Complex.exp (t * I)) (t * I) := Complex.hasDerivAt_exp _
  have h3 := h2.scomp t h1
  rw [smul_eq_mul] at h3
  simpa using h3.const_mul (ρ : ℂ)

/-- **Circle ODE.** If `w·g'(w) = c₀·g(w)` for all `w` on the circle `|w|=ρ`, then `g(ρe^{it}) =
g(ρ)·e^{ic₀t}` for all real `t`. -/
theorem cor_c_circle_eq {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (annulus r₁ r₂)) {c₀ : ℂ} {ρ : ℝ} (hρ1 : r₁ < ρ) (hρ2 : ρ < r₂)
    (hh : ∀ w ∈ annulus r₁ r₂, w * deriv g w = c₀ * g w) (t : ℝ) :
    g ((ρ : ℂ) * Complex.exp (t * I)) = g ρ * Complex.exp (c₀ * t * I) := by
  set ψ : ℝ → ℂ := fun t => (ρ : ℂ) * Complex.exp (t * I) with hψdef
  have hψmem : ∀ t : ℝ, ψ t ∈ annulus r₁ r₂ := by
    intro t
    have hnorm : ‖ψ t‖ = ρ := by
      rw [hψdef]
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (h₁.trans hρ1)]
    exact ⟨by rw [hnorm]; exact hρ1, by rw [hnorm]; exact hρ2⟩
  set φ : ℝ → ℂ := fun t => g (ψ t) * Complex.exp (-c₀ * t * I) with hφdef
  have hφderiv : ∀ t : ℝ, HasDerivAt φ 0 t := by
    intro t
    have hψderiv : HasDerivAt ψ ((ρ : ℂ) * (I * Complex.exp (t * I))) t :=
      cor_c_hasDerivAt_circle ρ t
    have hgderiv : HasDerivAt g (deriv g (ψ t)) (ψ t) :=
      (hg.differentiableAt (IsOpen.mem_nhds (isOpen_annulus r₁ r₂) (hψmem t))).hasDerivAt
    have hgψderiv : HasDerivAt (g ∘ ψ) (((ρ : ℂ) * (I * Complex.exp (t * I))) * deriv g (ψ t)) t := by
      have := hgderiv.scomp t hψderiv
      rwa [smul_eq_mul] at this
    have hexpderiv : HasDerivAt (fun t : ℝ => Complex.exp (-c₀ * t * I)) (-c₀ * I *
        Complex.exp (-c₀ * t * I)) t := by
      have h5 := cor_c_hasDerivAt_cexp_mul (-c₀ * I) t
      convert h5 using 2 with s <;> ring
    have hφderiv' : HasDerivAt φ
        ((((ρ : ℂ) * (I * Complex.exp (t * I))) * deriv g (ψ t)) * Complex.exp (-c₀ * t * I) +
          g (ψ t) * (-c₀ * I * Complex.exp (-c₀ * t * I))) t :=
      hgψderiv.mul hexpderiv
    have hkey : ψ t * deriv g (ψ t) = c₀ * g (ψ t) := hh (ψ t) (hψmem t)
    have hzero : ((((ρ : ℂ) * (I * Complex.exp (t * I))) * deriv g (ψ t)) *
          Complex.exp (-c₀ * t * I) +
        g (ψ t) * (-c₀ * I * Complex.exp (-c₀ * t * I))) = 0 := by
      have hexpprod : Complex.exp (t * I) * Complex.exp (-c₀ * t * I) =
          Complex.exp ((1 - c₀) * t * I) := by
        rw [← Complex.exp_add]; ring_nf
      have hexpprod2 : Complex.exp (-c₀ * t * I) = Complex.exp ((1 - c₀) * t * I) / Complex.exp (t * I) := by
        rw [← hexpprod]; field_simp
      have hgtI : ψ t = (ρ : ℂ) * Complex.exp (t * I) := rfl
      have h6 : (ρ : ℂ) * Complex.exp (t * I) * deriv g (ψ t) = c₀ * g (ψ t) := by
        rw [← hgtI]; exact hkey
      calc (((ρ : ℂ) * (I * Complex.exp (t * I))) * deriv g (ψ t)) *
              Complex.exp (-c₀ * t * I) +
            g (ψ t) * (-c₀ * I * Complex.exp (-c₀ * t * I))
          = I * Complex.exp (-c₀ * t * I) *
              ((ρ : ℂ) * Complex.exp (t * I) * deriv g (ψ t) - c₀ * g (ψ t)) := by ring
        _ = I * Complex.exp (-c₀ * t * I) * 0 := by rw [h6]; ring
        _ = 0 := by ring
    rwa [hzero] at hφderiv'
  have hφconst : ∀ x y : ℝ, φ x = φ y := is_const_of_deriv_eq_zero
    (fun t => (hφderiv t).differentiableAt) (fun t => (hφderiv t).deriv)
  have hφeq : φ t = φ 0 := hφconst t 0
  have hφ0eq : φ 0 = g (ρ : ℂ) := by
    show g (ψ 0) * Complex.exp (-c₀ * (0 : ℝ) * I) = g (ρ : ℂ)
    have hψ0 : ψ 0 = (ρ : ℂ) := by simp [hψdef]
    rw [hψ0]; norm_num
  have hφteq : φ t = g (ψ t) * Complex.exp (-c₀ * t * I) := rfl
  rw [hφteq, hφ0eq] at hφeq
  have hexpne : Complex.exp (-c₀ * t * I) ≠ 0 := Complex.exp_ne_zero _
  have hgψt : g (ψ t) = g (ρ : ℂ) / Complex.exp (-c₀ * t * I) := (eq_div_iff hexpne).mpr hφeq
  have hinv : Complex.exp (-c₀ * t * I) = (Complex.exp (c₀ * t * I))⁻¹ := by
    rw [← Complex.exp_neg]; congr 1; ring
  rw [hgψt, hinv, div_eq_mul_inv, inv_inv]

/-- **H.** A conformal map `g` of an annulus onto `B` with `|g'|/|g| = c/|w|` is `w ↦ K w` or
`w ↦ K / w`, so `B` is a round annulus. -/
theorem cor_eq_annulus_of_deriv_ratio {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) {B : Set ℂ}
    {g : ℂ → ℂ} (hg : IsConformalOnto g (annulus r₁ r₂) B) {c : ℝ} (hc0 : 0 < c)
    (hc : ∀ w ∈ annulus r₁ r₂, ‖deriv g w‖ / ‖g w‖ = c / ‖w‖) :
    ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ s₁ < s₂ ∧ B = annulus s₁ s₂ := by
  obtain ⟨hgdiff, hginj, hgimg⟩ := hg
  have hAo : IsOpen (annulus r₁ r₂) := isOpen_annulus r₁ r₂
  have hAne : (annulus r₁ r₂).Nonempty := ⟨((r₁ + r₂) / 2 : ℝ), by
    constructor <;> rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)] <;> linarith⟩
  have hwpos : ∀ w ∈ annulus r₁ r₂, (0:ℝ) < ‖w‖ := fun w hw => h₁.trans hw.1
  have hgne : ∀ w ∈ annulus r₁ r₂, g w ≠ 0 := by
    intro w hw hgw0
    have hlhs : ‖deriv g w‖ / ‖g w‖ = 0 := by rw [hgw0, norm_zero, div_zero]
    have hrhs : (0:ℝ) < c / ‖w‖ := div_pos hc0 (hwpos w hw)
    rw [hc w hw] at hlhs
    linarith
  have hderivdiff : DifferentiableOn ℂ (deriv g) (annulus r₁ r₂) :=
    ((hgdiff.analyticOnNhd hAo).deriv_of_isOpen hAo).differentiableOn
  set hfun : ℂ → ℂ := fun w => w * deriv g w / g w with hfundef
  have hfundiff : DifferentiableOn ℂ hfun (annulus r₁ r₂) := by
    intro w hw
    exact ((differentiableWithinAt_id.mul (hderivdiff w hw)).div (hgdiff w hw) (hgne w hw))
  have hfunnorm : ∀ w ∈ annulus r₁ r₂, ‖hfun w‖ = c := by
    intro w hw
    rw [hfundef]
    simp only
    rw [norm_div, norm_mul]
    rw [show ‖w‖ * ‖deriv g w‖ / ‖g w‖ = ‖w‖ * (‖deriv g w‖ / ‖g w‖) by ring, hc w hw]
    field_simp
    rw [div_self (hwpos w hw).ne']
  obtain ⟨w0, hw0⟩ := hAne
  have hmax : IsMaxOn (norm ∘ hfun) (annulus r₁ r₂) w0 := by
    intro w hw
    simp only [Function.comp_apply, mem_setOf_eq, le_eq_subset]
    rw [hfunnorm w hw, hfunnorm w0 hw0]
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (isPreconnected_annulus h₁.le)
    hAo hfundiff hw0 hmax
  set c₀ : ℂ := hfun w0 with hc₀def
  have hc0norm : ‖c₀‖ = c := hfunnorm w0 hw0
  have hh : ∀ w ∈ annulus r₁ r₂, w * deriv g w = c₀ * g w := by
    intro w hw
    have := hconst hw
    simp only [Function.const_apply] at this
    rw [hfundef] at this
    simp only at this
    rw [div_eq_iff (hgne w hw)] at this
    exact this
  set ρ0 : ℝ := (r₁ + r₂) / 2 with hρ0def
  have hρ01 : r₁ < ρ0 := by rw [hρ0def]; linarith
  have hρ02 : ρ0 < r₂ := by rw [hρ0def]; linarith
  have hρ0mem : (ρ0 : ℂ) ∈ annulus r₁ r₂ := by
    constructor <;> rw [Complex.norm_real, Real.norm_of_nonneg (h₁.trans hρ01).le] <;> linarith
  have hgρ0ne : g (ρ0 : ℂ) ≠ 0 := hgne _ hρ0mem
  have hcircle : ∀ t : ℝ, g ((ρ0 : ℂ) * Complex.exp (t * I)) = g ρ0 * Complex.exp (c₀ * t * I) :=
    cor_c_circle_eq h₁ h₂ hgdiff hρ01 hρ02 hh
  have h2pi1 : Complex.exp ((2 * π : ℝ) * I) = 1 :=
    Complex.exp_eq_one_iff.2 ⟨1, by push_cast; ring⟩
  have hn0 : Complex.exp (c₀ * (2 * π : ℝ) * I) = 1 := by
    have h1eq := hcircle (2 * π)
    rw [show (ρ0 : ℂ) * Complex.exp ((2 * π : ℝ) * I) = ρ0 by rw [h2pi1, mul_one]] at h1eq
    have h1eq' : g ρ0 * 1 = g ρ0 * Complex.exp (c₀ * (2 * π : ℝ) * I) := by
      rw [mul_one]; exact h1eq
    exact (mul_left_cancel₀ hgρ0ne h1eq').symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hn0
  have hc0eq : c₀ = (n : ℂ) := by
    have hπ : (2 * (π : ℂ) * I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have heq2 : c₀ * (2 * (π : ℂ) * I) = (n : ℂ) * (2 * (π : ℂ) * I) := by
      have h9 := hn
      push_cast at h9
      linear_combination h9
    exact mul_right_cancel₀ hπ heq2
  have hnc : |(n : ℝ)| = c := by
    rw [← hc0norm, hc0eq, show ((n : ℤ) : ℂ) = (((n : ℤ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  have hn0' : n ≠ 0 := by
    intro h; rw [h] at hnc; norm_num at hnc; linarith
  have hn1 : n = 1 ∨ n = -1 := by
    by_contra hcon
    push Not at hcon
    have hn2 : n ≤ -2 ∨ 2 ≤ n := by omega
    have hnR0 : (n : ℝ) ≠ 0 := Int.cast_ne_zero.2 hn0'
    have hn2R : (2:ℝ) ≤ |(n:ℝ)| := by
      rcases hn2 with h | h
      · have h' : (n:ℝ) ≤ -2 := by exact_mod_cast h
        rw [abs_of_neg (by linarith : (n:ℝ) < 0)]
        linarith
      · have h' : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast h
        rw [abs_of_pos (by linarith : (0:ℝ) < (n:ℝ))]
        linarith
    set t2 : ℝ := 2 * π / n with ht2def
    have ht2bound : |t2| ≤ π := by
      rw [ht2def, abs_div, abs_of_pos Real.two_pi_pos, div_le_iff₀ (by positivity : (0:ℝ) < |(n:ℝ)|)]
      nlinarith [Real.pi_pos, hn2R]
    have ht2ne : t2 ≠ 0 := by
      rw [ht2def]; exact div_ne_zero (by positivity) hnR0
    have ht2eq : g ((ρ0:ℂ) * Complex.exp (t2 * I)) = g ρ0 := by
      rw [hcircle t2, hc0eq]
      have hnCne : (n:ℂ) ≠ 0 := Int.cast_ne_zero.2 hn0'
      have hcancel : (n:ℂ) * (t2:ℝ) * I = ((2 * π : ℝ) : ℂ) * I := by
        rw [ht2def]; push_cast; field_simp [hnCne]
      rw [hcancel, h2pi1, mul_one]
    have ht2mem : (ρ0:ℂ) * Complex.exp (t2 * I) ∈ annulus r₁ r₂ := by
      have hnormeq : ‖(ρ0:ℂ) * Complex.exp (t2 * I)‖ = ρ0 := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (h₁.trans hρ01).le]
      exact ⟨by rw [hnormeq]; exact hρ01, by rw [hnormeq]; exact hρ02⟩
    have hne2 : (ρ0:ℂ) * Complex.exp (t2 * I) ≠ (ρ0:ℂ) := by
      intro heq
      have hρ0ne : (ρ0:ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (h₁.trans hρ01).ne'
      have hexp1 : Complex.exp (t2 * I) = 1 := by
        have heq' : (ρ0:ℂ) * Complex.exp (t2 * I) = (ρ0:ℂ) * 1 := by rw [mul_one]; exact heq
        exact mul_left_cancel₀ hρ0ne heq'
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hexp1
      have hmeq : (t2:ℝ) = m * (2 * π) := by
        have hIne : (I:ℂ) ≠ 0 := Complex.I_ne_zero
        have h7 : (t2:ℂ) * I = (m:ℂ) * (2 * π) * I := by rw [hm]; push_cast; ring
        exact_mod_cast mul_right_cancel₀ hIne h7
      rcases eq_or_ne m 0 with hm0 | hm0
      · rw [hm0] at hmeq; simp at hmeq; exact ht2ne hmeq
      · have hmR : (1:ℝ) ≤ |(m:ℝ)| := by
          rcases lt_or_gt_of_ne hm0 with h | h
          · have : (m:ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
            rw [abs_of_neg (by linarith : (m:ℝ) < 0)]; linarith
          · have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : (1:ℤ) ≤ m)
            rw [abs_of_pos (by linarith : (0:ℝ) < (m:ℝ))]; linarith
        have : π ≤ |t2| := by
          rw [hmeq, abs_mul, abs_of_pos Real.two_pi_pos]
          nlinarith [Real.pi_pos, hmR]
        have hteq : |t2| = π := le_antisymm ht2bound this
        rw [hmeq] at hteq
        rw [abs_mul, abs_of_pos Real.two_pi_pos] at hteq
        nlinarith [hmR, Real.pi_pos]
    exact hne2 (hginj ht2mem hρ0mem ht2eq)
  have hgAt : ∀ ρ : ℝ, ρ ∈ Ioo r₁ r₂ → HasDerivAt (fun y : ℝ => g (y : ℂ)) (deriv g (ρ : ℂ)) ρ := by
    intro ρ hρ
    have hρmem : (ρ : ℂ) ∈ annulus r₁ r₂ := by
      constructor <;> rw [Complex.norm_real, Real.norm_of_nonneg (h₁.trans hρ.1).le]
      · exact hρ.1
      · exact hρ.2
    exact ((hgdiff.differentiableAt (hAo.mem_nhds hρmem)).hasDerivAt).comp_ofReal
  have hIooconn : IsPreconnected (Ioo r₁ r₂) := (convex_Ioo r₁ r₂).isPreconnected
  rcases hn1 with hn1 | hn1
  · -- n = 1 : g(w) = K w
    set χ : ℝ → ℂ := fun ρ => g (ρ : ℂ) / (ρ : ℂ) with hχdef
    have hχderiv : ∀ ρ ∈ Ioo r₁ r₂, HasDerivAt χ 0 ρ := by
      intro ρ hρ
      have hρmem : (ρ : ℂ) ∈ annulus r₁ r₂ := by
        constructor <;> rw [Complex.norm_real, Real.norm_of_nonneg (h₁.trans hρ.1).le]
        · exact hρ.1
        · exact hρ.2
      have hρne : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (h₁.trans hρ.1).ne'
      have hidderiv : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 ρ := hasDerivAt_id (ρ : ℂ) |>.comp_ofReal
      have hquot := (hgAt ρ hρ).div hidderiv hρne
      have hnum : deriv g (ρ : ℂ) * (ρ : ℂ) - g (ρ : ℂ) * 1 = 0 := by
        have hkey := hh (ρ : ℂ) hρmem
        rw [hc0eq, hn1] at hkey
        push_cast at hkey
        linear_combination hkey
      rw [hnum, zero_div] at hquot
      exact hquot
    have hχconst : ∀ x y : ℝ, x ∈ Ioo r₁ r₂ → y ∈ Ioo r₁ r₂ → χ x = χ y := fun x y hx hy =>
      isOpen_Ioo.is_const_of_deriv_eq_zero hIooconn
        (fun ρ hρ => (hχderiv ρ hρ).differentiableAt.differentiableWithinAt)
        (fun ρ hρ => (hχderiv ρ hρ).deriv) hx hy
    set K : ℂ := χ ρ0 with hKdef
    have hgρeq : ∀ ρ : ℝ, ρ ∈ Ioo r₁ r₂ → g (ρ : ℂ) = K * ρ := by
      intro ρ hρ
      have hρne : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (h₁.trans hρ.1).ne'
      have heq : g (ρ : ℂ) / (ρ : ℂ) = K := hχconst ρ ρ0 hρ ⟨hρ01, hρ02⟩
      rw [div_eq_iff hρne] at heq
      exact heq
    have hgweq : ∀ w ∈ annulus r₁ r₂, g w = K * w := by
      intro w hw
      have hwne : w ≠ 0 := by
        intro h
        rw [h] at hw
        simp only [annulus, mem_setOf_eq, norm_zero] at hw
        linarith [hw.1]
      set ρ := ‖w‖ with hρdef2
      set t := Complex.arg w with htdef
      have hweq : w = (ρ : ℂ) * Complex.exp (t * I) := by
        rw [hρdef2, htdef]
        exact (Complex.norm_mul_exp_arg_mul_I w).symm
      have hρmemIoo : ρ ∈ Ioo r₁ r₂ := ⟨hw.1, hw.2⟩
      have hcircleρ := cor_c_circle_eq h₁ h₂ hgdiff hρmemIoo.1 hρmemIoo.2 hh t
      rw [hweq, hcircleρ, hgρeq ρ hρmemIoo, hc0eq, hn1]
      have h1t : ((1:ℤ):ℂ) * (t:ℝ) * I = (t:ℝ) * I := by push_cast; ring
      rw [h1t]
      ring
    have hKne : K ≠ 0 := by
      intro hK0
      exact hgρ0ne (by rw [hgρeq ρ0 ⟨hρ01, hρ02⟩, hK0, zero_mul])
    refine ⟨‖K‖ * r₁, ‖K‖ * r₂, by positivity, by
      apply mul_lt_mul_of_pos_left h₂ (norm_pos_iff.2 hKne), ?_⟩
    rw [← hgimg]
    ext z
    simp only [mem_image, annulus, mem_setOf_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hgweq w hw, norm_mul]
      constructor
      · exact mul_lt_mul_of_pos_left hw.1 (norm_pos_iff.2 hKne)
      · exact mul_lt_mul_of_pos_left hw.2 (norm_pos_iff.2 hKne)
    · rintro ⟨hz1, hz2⟩
      refine ⟨z / K, ⟨?_, ?_⟩, ?_⟩
      · rw [norm_div]
        rw [lt_div_iff₀ (norm_pos_iff.2 hKne)]
        rwa [mul_comm] at hz1
      · rw [norm_div]
        rw [div_lt_iff₀ (norm_pos_iff.2 hKne)]
        rwa [mul_comm] at hz2
      · rw [hgweq (z/K) ⟨by
          rw [norm_div, lt_div_iff₀ (norm_pos_iff.2 hKne)]; rwa [mul_comm] at hz1, by
          rw [norm_div, div_lt_iff₀ (norm_pos_iff.2 hKne)]; rwa [mul_comm] at hz2⟩]
        field_simp
  · -- n = -1 : g(w) = K / w
    set χ : ℝ → ℂ := fun ρ => g (ρ : ℂ) * (ρ : ℂ) with hχdef
    have hχderiv : ∀ ρ ∈ Ioo r₁ r₂, HasDerivAt χ 0 ρ := by
      intro ρ hρ
      have hρmem : (ρ : ℂ) ∈ annulus r₁ r₂ := by
        constructor <;> rw [Complex.norm_real, Real.norm_of_nonneg (h₁.trans hρ.1).le]
        · exact hρ.1
        · exact hρ.2
      have hidderiv : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 ρ := hasDerivAt_id (ρ : ℂ) |>.comp_ofReal
      have hprod := (hgAt ρ hρ).mul hidderiv
      have hnum : deriv g (ρ : ℂ) * (ρ : ℂ) + g (ρ : ℂ) * 1 = 0 := by
        have hkey := hh (ρ : ℂ) hρmem
        rw [hc0eq, hn1] at hkey
        push_cast at hkey
        linear_combination hkey
      rwa [hnum] at hprod
    have hχconst : ∀ x y : ℝ, x ∈ Ioo r₁ r₂ → y ∈ Ioo r₁ r₂ → χ x = χ y := fun x y hx hy =>
      isOpen_Ioo.is_const_of_deriv_eq_zero hIooconn
        (fun ρ hρ => (hχderiv ρ hρ).differentiableAt.differentiableWithinAt)
        (fun ρ hρ => (hχderiv ρ hρ).deriv) hx hy
    set K : ℂ := χ ρ0 with hKdef
    have hgρeq : ∀ ρ : ℝ, ρ ∈ Ioo r₁ r₂ → g (ρ : ℂ) = K / ρ := by
      intro ρ hρ
      have hρne : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (h₁.trans hρ.1).ne'
      have heq : g (ρ : ℂ) * (ρ : ℂ) = K := hχconst ρ ρ0 hρ ⟨hρ01, hρ02⟩
      rw [eq_div_iff hρne]
      exact heq
    have hgweq : ∀ w ∈ annulus r₁ r₂, g w = K / w := by
      intro w hw
      have hwne : w ≠ 0 := by
        intro h
        rw [h] at hw
        simp only [annulus, mem_setOf_eq, norm_zero] at hw
        linarith [hw.1]
      set ρ := ‖w‖ with hρdef2
      set t := Complex.arg w with htdef
      have hweq : w = (ρ : ℂ) * Complex.exp (t * I) := by
        rw [hρdef2, htdef]
        exact (Complex.norm_mul_exp_arg_mul_I w).symm
      have hρmemIoo : ρ ∈ Ioo r₁ r₂ := ⟨hw.1, hw.2⟩
      have hcircleρ := cor_c_circle_eq h₁ h₂ hgdiff hρmemIoo.1 hρmemIoo.2 hh t
      rw [hweq, hcircleρ, hgρeq ρ hρmemIoo, hc0eq, hn1]
      have hm1t : ((-1:ℤ):ℂ) * (t:ℝ) * I = -((t:ℝ) * I) := by push_cast; ring
      rw [hm1t, Complex.exp_neg]
      have hexpne : Complex.exp ((t:ℝ) * I) ≠ 0 := Complex.exp_ne_zero _
      have hρCne : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (h₁.trans hρmemIoo.1).ne'
      field_simp
    have hKne : K ≠ 0 := by
      intro hK0
      exact hgρ0ne (by rw [hgρeq ρ0 ⟨hρ01, hρ02⟩, hK0, zero_div])
    refine ⟨‖K‖ / r₂, ‖K‖ / r₁, div_pos (norm_pos_iff.2 hKne) (h₁.trans h₂),
      div_lt_div_of_pos_left (norm_pos_iff.2 hKne) h₁ h₂, ?_⟩
    rw [← hgimg]
    ext z
    simp only [mem_image, annulus, mem_setOf_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwne : w ≠ 0 := by
        intro h
        rw [h] at hw
        simp only [annulus, mem_setOf_eq, norm_zero] at hw
        linarith [hw.1]
      rw [hgweq w hw, norm_div]
      exact ⟨div_lt_div_of_pos_left (norm_pos_iff.2 hKne) (norm_pos_iff.2 hwne) hw.2,
        div_lt_div_of_pos_left (norm_pos_iff.2 hKne) h₁ hw.1⟩
    · rintro ⟨hz1, hz2⟩
      have hr2pos : 0 < r₂ := h₁.trans h₂
      have hzne : z ≠ 0 := by
        intro h
        rw [h, norm_zero] at hz1
        exact absurd hz1 (not_lt.2 (div_nonneg (norm_nonneg K) hr2pos.le))
      have hKlt1 : ‖K‖ < ‖z‖ * r₂ := (div_lt_iff₀ hr2pos).mp hz1
      have hKlt2 : ‖z‖ * r₁ < ‖K‖ := (lt_div_iff₀ h₁).mp hz2
      have hzbound1 : r₁ < ‖K‖ / ‖z‖ := by
        rw [lt_div_iff₀ (norm_pos_iff.2 hzne)]; linarith
      have hzbound2 : ‖K‖ / ‖z‖ < r₂ := by
        rw [div_lt_iff₀ (norm_pos_iff.2 hzne)]; linarith
      have hKzmem : K / z ∈ annulus r₁ r₂ := by
        show r₁ < ‖K / z‖ ∧ ‖K / z‖ < r₂
        rw [norm_div]
        exact ⟨hzbound1, hzbound2⟩
      refine ⟨K / z, hKzmem, ?_⟩
      rw [hgweq (K / z) hKzmem, div_div_eq_mul_div, mul_comm K z, mul_div_assoc, div_self hKne,
        mul_one]


/-- §4.6: for a general doubly connected `B` with a conformal map `f` onto an annulus, the
extremal metric of the separating curves is `|f'|/(2π|f|)`.

Proved (2026-09-21) from Theorem 4.9 (`thm4_9_dcModulus_eq`) and the `cor_` helpers above. -/
theorem dc_extremal_metric {B : Set ℂ} (hB : IsDoublyConnected B) {r₁ r₂ : ℝ} (h₁ : 0 < r₁)
    (h₂ : r₁ < r₂) {f : ℂ → ℂ} (hf : IsConformalOnto f B (annulus r₁ r₂)) :
    IsExtremalMetric B (separatingCurves B)
      (B.indicator fun z => ENNReal.ofReal (‖deriv f z‖ / (2 * π * ‖f z‖))) := by
  have hBo : IsOpen B := hB.1
  have hΓtrace : ∀ γ ∈ separatingCurves B, γ.trace ⊆ B :=
    fun γ hγ => (image_mono Ioo_subset_Icc_self).trans hγ.2.1
  have himg : IsCurveImage f (separatingCurves B) (separatingCurves (annulus r₁ r₂)) :=
    cor_isCurveImage_separatingCurves_symm h₁ h₂ hB hf
  have hρ' := annulus_extremal_metric h₁ h₂
  have hE2 := cor_isExtremalMetric_of_conformal hBo hf hΓtrace himg hρ'
  have hdens : (B.indicator fun z =>
      (annulus r₁ r₂).indicator (fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖))) (f z) *
        ‖deriv f z‖ₑ) =
      (B.indicator fun z => ENNReal.ofReal (‖deriv f z‖ / (2 * π * ‖f z‖))) := by
    funext z
    by_cases hz : z ∈ B
    · simp only [indicator_of_mem hz, indicator_of_mem (hf.mapsTo hz)]
      rw [← ofReal_norm (deriv f z), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    · simp [hz]
  rwa [hdens] at hE2

/-- The estimate following Theorem 4.9: `M(B) ≤ 2π m_ρ(B)` for every admissible `ρ`.

Proved (2026-09-21) from Theorem 4.9 (`thm4_9_dcModulus_eq`) and the `cor_` helpers above. -/
theorem dcModulus_le_rhoArea {B : Set ℂ} (hB : IsDoublyConnected B) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) (hadm : ∀ γ ∈ separatingCurves B, 1 ≤ γ.rhoLength ρ) :
    dcModulus B ≤ ENNReal.ofReal (2 * π) * rhoArea ρ B := by
  rcases eq_top_or_lt_top (rhoArea ρ B) with hArea | hArea
  · rw [hArea, ENNReal.mul_top (by positivity)]
    exact le_top
  · have hBo : IsOpen B := hB.1
    have hBne : B.Nonempty := hB.2.1.nonempty
    have hΓ : ∀ γ ∈ separatingCurves B, γ.trace ⊆ B := fun γ hγ =>
      (image_mono Ioo_subset_Icc_self).trans hγ.2.1
    have hle := le_extremalLengthIn hBo hBne (separatingCurves B) hρ hArea
    rw [extremalLengthIn_eq hBo hBne hΓ] at hle
    have hinf : (1 : ℝ≥0∞) ≤ ⨅ γ ∈ separatingCurves B, γ.rhoLength ρ ^ 2 :=
      le_iInf₂ fun γ hγ => one_le_pow_of_one_le' (hadm γ hγ) 2
    have hratio : (1 : ℝ≥0∞) / rhoArea ρ B ≤ extremalLength (separatingCurves B) :=
      (ENNReal.div_le_div_right hinf _).trans hle
    rw [thm4_9_dcModulus_eq hB]
    calc ENNReal.ofReal (2 * π) / extremalLength (separatingCurves B)
        ≤ ENNReal.ofReal (2 * π) / (1 / rhoArea ρ B) := ENNReal.div_le_div_left hratio _
      _ = ENNReal.ofReal (2 * π) * rhoArea ρ B := by
          rw [div_eq_mul_inv, one_div, inv_inv]

/-- (4.22): if the two components of `ℂ̄ ∖ B` contain `0` and `∞` respectively, then
`M(B) ≤ (1/2π) ∬_B dx dy / |z|²` (the analogue of Rengel's inequality).

Proved (2026-09-21) from Theorem 4.9 (`thm4_9_dcModulus_eq`) and the `cor_` helpers above. -/
theorem eq4_22 {B : Set ℂ} (hB : IsDoublyConnected B)
    (hsep : SeparatesSets B {((0 : ℂ) : ExtPlane)} {extInf}) :
    dcModulus B ≤ ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in B, ENNReal.ofReal (1 / ‖z‖ ^ 2) := by
  have hBo : IsOpen B := hB.1
  obtain ⟨x1, hx1, x2, hx2, h1sub, h2sub, hcompne⟩ := hsep
  have h0mem : ((0 : ℂ) : ExtPlane) ∈ (toExt B)ᶜ := connectedComponentIn_subset _ _
    (h1sub (mem_singleton _))
  have hinfmem : (extInf : ExtPlane) ∈ (toExt B)ᶜ := connectedComponentIn_subset _ _
    (h2sub (mem_singleton _))
  have e1 : connectedComponentIn (toExt B)ᶜ ((0 : ℂ) : ExtPlane) =
      connectedComponentIn (toExt B)ᶜ x1 := by
    first
    | exact connectedComponentIn_eq (h1sub (mem_singleton _))
    | exact (connectedComponentIn_eq (h1sub (mem_singleton _))).symm
  have e2 : connectedComponentIn (toExt B)ᶜ (extInf : ExtPlane) =
      connectedComponentIn (toExt B)ᶜ x2 := by
    first
    | exact connectedComponentIn_eq (h2sub (mem_singleton _))
    | exact (connectedComponentIn_eq (h2sub (mem_singleton _))).symm
  have hne_B : connectedComponentIn (toExt B)ᶜ ((0 : ℂ) : ExtPlane) ≠
      connectedComponentIn (toExt B)ᶜ extInf := by
    rw [e1, e2]; exact hcompne
  have h0notB : (0 : ℂ) ∉ B := fun h => h0mem ⟨0, h, rfl⟩
  set ρ : ℂ → ℝ≥0∞ := B.indicator fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖)) with hρdef
  have hρmeas : Measurable ρ :=
    (measurable_const.div (measurable_const.mul measurable_norm)).ennreal_ofReal.indicator
      hBo.measurableSet
  have hadm : ∀ γ ∈ separatingCurves B, 1 ≤ γ.rhoLength ρ := by
    intro γ hγ
    obtain ⟨hclosed, htrace, hsep'⟩ := hγ
    have h0trace : (0 : ℂ) ∉ γ.closedTrace := fun h => h0notB (htrace h)
    have hnetrace : connectedComponentIn (toExt γ.closedTrace)ᶜ ((0 : ℂ) : ExtPlane) ≠
        connectedComponentIn (toExt γ.closedTrace)ᶜ extInf :=
      hsep' _ h0mem _ hinfmem hne_B
    have hb2 := cor_one_le_rhoLength_of_separates hclosed h0trace hnetrace
    have heqon : EqOn ρ (fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖))) γ.trace := by
      intro z hz
      exact Set.indicator_of_mem (htrace (image_mono Ioo_subset_Icc_self hz)) _
    rwa [LRCurve.rhoLength_congr heqon]
  have hA := dcModulus_le_rhoArea hB hρmeas hadm
  have hrhoArea : rhoArea ρ B = ENNReal.ofReal (1 / (4 * π ^ 2)) *
      ∫⁻ z in B, ENNReal.ofReal (1 / ‖z‖ ^ 2) := by
    unfold rhoArea
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun hBo.measurableSet fun z hz => ?_
    rw [hρdef, indicator_of_mem hz, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hz0 : z ≠ 0 := fun h => h0notB (h ▸ hz)
    have hznorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz0
    field_simp
    ring
  rw [hrhoArea, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    show 2 * π * (1 / (4 * π ^ 2)) = 1 / (2 * π) by field_simp; ring] at hA
  exact hA

/-- Equality holds in (4.22) iff `B` is an annulus centred at `0`.

Proved (2026-09-21) from Theorem 4.9 (`thm4_9_dcModulus_eq`) and the `cor_` helpers above. -/
theorem eq4_22_eq_iff {B : Set ℂ} (hB : IsDoublyConnected B)
    (hsep : SeparatesSets B {((0 : ℂ) : ExtPlane)} {extInf})
    (hfin : ∫⁻ z in B, ENNReal.ofReal (1 / ‖z‖ ^ 2) < ⊤) :
    dcModulus B = ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in B, ENNReal.ofReal (1 / ‖z‖ ^ 2) ↔
      ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ B = annulus r₁ r₂ := by
  have hBo : IsOpen B := hB.1
  have hBne : B.Nonempty := hB.2.1.nonempty
  have h0B : (0 : ℂ) ∉ B := by
    obtain ⟨x₁, hx₁, x₂, hx₂, hE1, hE2, hne'⟩ := hsep
    have h0x1 : ((0 : ℂ) : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x₁ := hE1 (mem_singleton _)
    exact coe_mem_compl_toExt_iff.mp (connectedComponentIn_subset _ _ h0x1)
  constructor
  · intro heq
    have hRHSfin : ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in B, ENNReal.ofReal (1 / ‖z‖ ^ 2) < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
    have hMfin : dcModulus B < ⊤ := heq ▸ hRHSfin
    have hnd : ∀ x ∈ (toExt B)ᶜ, connectedComponentIn (toExt B)ᶜ x ≠ {x} := by
      intro x hx hxpt
      exact hMfin.ne (gsep_dcModulus_eq_top_of_singleton hB hx hxpt)
    obtain ⟨r₁, r₂, h₁, h₂, k, hk⟩ := thm2_1_canonical_form_annulus hB hnd
    have hMpos : 0 < dcModulus B := by
      rw [dcModulus_eq_of_equiv hBo h₁ h₂ ⟨k, hk⟩]
      exact ENNReal.ofReal_pos.2 (Real.log_pos (by rw [lt_div_iff₀ h₁, one_mul]; exact h₂))
    have hg : IsConformalOnto (Function.invFunOn k B) (annulus r₁ r₂) B := hk.symm hBo
    set g := Function.invFunOn k B with hgdef
    have hgmaps : MapsTo g (annulus r₁ r₂) B := fun w hw => hg.2.2 ▸ mem_image_of_mem g hw
    -- the density `ρ₀ = 1 / (2π|z|)` on `B`
    set ρ₀ : ℂ → ℝ≥0∞ := B.indicator fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖)) with hρ₀def
    have hρ₀meas : Measurable ρ₀ := by
      apply Measurable.indicator _ hBo.measurableSet
      exact ENNReal.measurable_ofReal.comp (measurable_const.div (by fun_prop))
    have hΓB : ∀ γ ∈ separatingCurves B, γ.trace ⊆ B := fun γ hγ =>
      (image_mono Ioo_subset_Icc_self).trans hγ.2.1
    have hadm : ∀ γ ∈ separatingCurves B, 1 ≤ γ.rhoLength ρ₀ := by
      intro γ hγ
      obtain ⟨hclosed, htr, hseg⟩ := hγ
      have h0notin : (0 : ℂ) ∉ γ.closedTrace := fun h0 => h0B (htr h0)
      have hne : connectedComponentIn (toExt γ.closedTrace)ᶜ ((0 : ℂ) : ExtPlane) ≠
          connectedComponentIn (toExt γ.closedTrace)ᶜ extInf := by
        refine hseg _ (coe_mem_compl_toExt_iff.mpr h0B) _ (extInf_notMem_toExt B) ?_
        obtain ⟨x₁, hx₁, x₂, hx₂, hE1, hE2, hne'⟩ := hsep
        have h0x1 : ((0 : ℂ) : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x₁ := hE1 (mem_singleton _)
        have hinfx2 : (extInf : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x₂ := hE2 (mem_singleton _)
        rw [(connectedComponentIn_eq h0x1).symm, (connectedComponentIn_eq hinfx2).symm]
        exact hne'
      have hb2 := cor_one_le_rhoLength_of_separates hclosed h0notin hne
      rwa [LRCurve.rhoLength_congr
        (show EqOn ρ₀ (fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖))) γ.trace from
          fun z hz => indicator_of_mem (hΓB γ ⟨hclosed, htr, hseg⟩ hz) _)]
    -- relate `rhoArea ρ₀ B` to the given integral
    have hρ₀sq : ∀ z ∈ B, ρ₀ z ^ 2 =
        ENNReal.ofReal (1 / (4 * π ^ 2)) * ENNReal.ofReal (1 / ‖z‖ ^ 2) := by
      intro z hz
      rw [hρ₀def, indicator_of_mem hz, ← ENNReal.ofReal_pow (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring
    have hρ₀area_eq : rhoArea ρ₀ B =
        ENNReal.ofReal (1 / (4 * π ^ 2)) * ∫⁻ z in B, ENNReal.ofReal (1 / ‖z‖ ^ 2) := by
      unfold rhoArea
      rw [setLIntegral_congr_fun hBo.measurableSet hρ₀sq,
        lintegral_const_mul _ (by fun_prop : Measurable fun z : ℂ => ENNReal.ofReal (1 / ‖z‖ ^ 2))]
    have hkey : dcModulus B = ENNReal.ofReal (2 * π) * rhoArea ρ₀ B := by
      rw [hρ₀area_eq, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * π),
        show (2 * π) * (1 / (4 * π ^ 2)) = 1 / (2 * π) by field_simp; ring]
      exact heq
    have hAreaNe0 : rhoArea ρ₀ B ≠ 0 := by
      intro h0
      rw [hkey, h0, mul_zero] at hMpos
      exact lt_irrefl 0 hMpos
    have hAreaNeTop : rhoArea ρ₀ B ≠ ⊤ := by
      intro ht
      rw [hkey, ht, ENNReal.mul_top (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne'] at hMfin
      exact lt_irrefl ⊤ hMfin
    have h2πne0 : ENNReal.ofReal (2 * π) ≠ 0 := (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne'
    have hLne0 : extremalLength (separatingCurves B) ≠ 0 := by
      intro h0
      rw [thm4_9_dcModulus_eq hB, h0, ENNReal.div_zero h2πne0] at hMfin
      exact lt_irrefl ⊤ hMfin
    have hLneTop : extremalLength (separatingCurves B) ≠ ⊤ := by
      intro ht
      rw [thm4_9_dcModulus_eq hB, ht, ENNReal.div_top] at hMpos
      exact lt_irrefl 0 hMpos
    have hMreal : (dcModulus B).toReal = 2 * π / (extremalLength (separatingCurves B)).toReal := by
      rw [thm4_9_dcModulus_eq hB, ENNReal.toReal_div, ENNReal.toReal_ofReal Real.two_pi_pos.le]
    have hMreal2 : (dcModulus B).toReal = 2 * π * (rhoArea ρ₀ B).toReal := by
      rw [hkey, ENNReal.toReal_mul, ENNReal.toReal_ofReal Real.two_pi_pos.le]
    have hLpos' : 0 < (extremalLength (separatingCurves B)).toReal :=
      ENNReal.toReal_pos hLne0 hLneTop
    have hApos' : 0 < (rhoArea ρ₀ B).toReal := ENNReal.toReal_pos hAreaNe0 hAreaNeTop
    have hprod : (rhoArea ρ₀ B).toReal * (extremalLength (separatingCurves B)).toReal = 1 := by
      have heqreal : 2 * π / (extremalLength (separatingCurves B)).toReal =
          2 * π * (rhoArea ρ₀ B).toReal := hMreal.symm.trans hMreal2
      rw [div_eq_iff hLpos'.ne', mul_assoc] at heqreal
      have heq2 : (2 * π) * 1 =
          (2 * π) * ((rhoArea ρ₀ B).toReal * (extremalLength (separatingCurves B)).toReal) := by
        rw [mul_one]; exact heqreal
      exact (mul_left_cancel₀ Real.two_pi_pos.ne' heq2).symm
    have hAreaMulL : rhoArea ρ₀ B * extremalLength (separatingCurves B) = 1 := by
      have hne : rhoArea ρ₀ B * extremalLength (separatingCurves B) ≠ ⊤ :=
        ENNReal.mul_ne_top hAreaNeTop hLneTop
      have htoreal : (rhoArea ρ₀ B * extremalLength (separatingCurves B)).toReal = 1 := by
        rw [ENNReal.toReal_mul]; exact hprod
      calc rhoArea ρ₀ B * extremalLength (separatingCurves B)
          = ENNReal.ofReal (rhoArea ρ₀ B * extremalLength (separatingCurves B)).toReal :=
            (ENNReal.ofReal_toReal hne).symm
        _ = ENNReal.ofReal 1 := by rw [htoreal]
        _ = 1 := ENNReal.ofReal_one
    have hLeq : extremalLength (separatingCurves B) = 1 / rhoArea ρ₀ B :=
      (ENNReal.eq_div_iff hAreaNe0 hAreaNeTop).2 hAreaMulL
    -- `ρ₀` is extremal for `separatingCurves B`
    have hρ₀ext : IsExtremalMetric B (separatingCurves B) ρ₀ := by
      refine ⟨⟨hρ₀meas, hAreaNe0.bot_lt, hAreaNeTop.lt_top⟩, ?_⟩
      have hle_a : (⨅ γ ∈ separatingCurves B, γ.rhoLength ρ₀ ^ 2) / rhoArea ρ₀ B ≤
          extremalLength (separatingCurves B) := by
        rw [← extremalLengthIn_eq hBo hBne hΓB]
        exact le_extremalLengthIn hBo hBne (separatingCurves B) hρ₀meas hAreaNeTop.lt_top
      have hinf : (1 : ℝ≥0∞) ≤ ⨅ γ ∈ separatingCurves B, γ.rhoLength ρ₀ ^ 2 :=
        le_iInf₂ fun γ hγ => one_le_pow_of_one_le' (hadm γ hγ) 2
      have hle_b : extremalLength (separatingCurves B) ≤
          (⨅ γ ∈ separatingCurves B, γ.rhoLength ρ₀ ^ 2) / rhoArea ρ₀ B := by
        rw [hLeq]
        exact ENNReal.div_le_div_right hinf _
      exact le_antisymm hle_a hle_b
    -- pull `ρ₀` back to the annulus along `g`
    have hΓann : ∀ γ ∈ separatingCurves (annulus r₁ r₂), γ.trace ⊆ annulus r₁ r₂ := fun γ hγ =>
      (image_mono Ioo_subset_Icc_self).trans hγ.2.1
    have himg := gsep_isCurveImage_separatingCurves h₁ h₂ hB hg
    have hσext := cor_isExtremalMetric_of_conformal (isOpen_annulus r₁ r₂) hg hΓann himg hρ₀ext
    set σ : ℂ → ℝ≥0∞ := (annulus r₁ r₂).indicator fun w => ρ₀ (g w) * ‖deriv g w‖ₑ with hσdef
    have hratio : (⨅ γ ∈ separatingCurves (annulus r₁ r₂), γ.rhoLength σ ^ 2) /
        rhoArea σ (annulus r₁ r₂) = ENNReal.ofReal (2 * π / Real.log (r₂ / r₁)) := by
      rw [hσext.2, extremalLength_annulusSeparating h₁ h₂]
    obtain ⟨c, hc0, hct, hae⟩ := cor_ae_eq_of_annulus_extremal h₁ h₂ hσext.1.1
      hσext.1.2.1.ne' hσext.1.2.2.ne hratio
    have hgne0 : ∀ w ∈ annulus r₁ r₂, g w ≠ 0 := fun w hw h0 => h0B (h0 ▸ hgmaps hw)
    have hwne0 : ∀ w ∈ annulus r₁ r₂, w ≠ 0 := fun w hw h0 => by
      obtain ⟨ha, -⟩ := hw
      rw [h0, norm_zero] at ha
      exact absurd ha (not_lt.2 h₁.le)
    have hgcont : ContinuousOn g (annulus r₁ r₂) := hg.1.continuousOn
    have hgdcont : ContinuousOn (deriv g) (annulus r₁ r₂) :=
      (hg.1.analyticOnNhd (isOpen_annulus r₁ r₂)).deriv.continuousOn
    have hσcont : ContinuousOn σ (annulus r₁ r₂) := by
      refine ContinuousOn.congr ?_ fun w hw => indicator_of_mem hw _
      have hcombined : ContinuousOn
          (fun w => ENNReal.ofReal ((1 / (2 * π * ‖g w‖)) * ‖deriv g w‖)) (annulus r₁ r₂) := by
        refine ENNReal.continuous_ofReal.comp_continuousOn (ContinuousOn.mul ?_ ?_)
        · exact continuousOn_const.div (continuousOn_const.mul (continuous_norm.comp_continuousOn hgcont))
            fun w hw => mul_ne_zero (by positivity) (norm_ne_zero_iff.2 (hgne0 w hw))
        · exact continuous_norm.comp_continuousOn hgdcont
      refine hcombined.congr fun w hw => ?_
      rw [hρ₀def, indicator_of_mem (hgmaps hw), ← ofReal_norm (deriv g w),
        ← ENNReal.ofReal_mul (by positivity)]
    have hRHScont : ContinuousOn (fun w => c * ENNReal.ofReal (1 / ‖w‖)) (annulus r₁ r₂) := by
      refine (ENNReal.continuous_const_mul hct).comp_continuousOn
        (ENNReal.continuous_ofReal.comp_continuousOn ?_)
      exact continuousOn_const.div continuous_norm.continuousOn
        fun w hw => norm_ne_zero_iff.2 (hwne0 w hw)
    have heverywhere := Measure.eqOn_open_of_ae_eq hae (isOpen_annulus r₁ r₂) hσcont hRHScont
    obtain ⟨c', hc'pos, hc'eq⟩ : ∃ c' : ℝ, 0 < c' ∧ c = ENNReal.ofReal c' :=
      ⟨c.toReal, ENNReal.toReal_pos hc0 hct, (ENNReal.ofReal_toReal hct).symm⟩
    have hfinal : ∀ w ∈ annulus r₁ r₂, ‖deriv g w‖ / ‖g w‖ = (2 * π * c') / ‖w‖ := by
      intro w hw
      have h1 : σ w = c * ENNReal.ofReal (1 / ‖w‖) := heverywhere hw
      rw [hσdef, indicator_of_mem hw, hρ₀def, indicator_of_mem (hgmaps hw)] at h1
      rw [← ofReal_norm (deriv g w), ← ENNReal.ofReal_mul (by positivity), hc'eq,
        ← ENNReal.ofReal_mul hc'pos.le] at h1
      have hgw0 : ‖g w‖ ≠ 0 := norm_ne_zero_iff.2 (hgne0 w hw)
      have hw0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 (hwne0 w hw)
      have heq2 := (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).1 h1
      field_simp at heq2 ⊢
      nlinarith [heq2]
    obtain ⟨s₁, s₂, hs₁, hs₂, hBeq⟩ := cor_eq_annulus_of_deriv_ratio h₁ h₂ hg
      (by positivity : (0:ℝ) < 2 * π * c') hfinal
    exact ⟨s₁, s₂, hs₁, hs₂, hBeq⟩
  · rintro ⟨r₁, r₂, h₁, h₂, rfl⟩
    have h2π : (1 / (2 * π)) * (2 * π) = 1 := by
      rw [div_mul_cancel₀]
      exact Real.two_pi_pos.ne'
    rw [dcModulus_annulus h₁ h₂, lintegral_annulus_inv_normSq h₁ h₂,
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1 / (2 * π)), h2π,
      ENNReal.ofReal_one, one_mul]

/-- `B₁` separates the two components of `ℂ̄ ∖ B`. -/
def SeparatesComplement (B₁ B : Set ℂ) : Prop :=
  ∀ x ∈ (toExt B)ᶜ, ∀ y ∈ (toExt B)ᶜ,
    connectedComponentIn (toExt B)ᶜ x ≠ connectedComponentIn (toExt B)ᶜ y →
      SeparatesSets B₁ (connectedComponentIn (toExt B)ᶜ x) (connectedComponentIn (toExt B)ᶜ y)

/-! ### Corollaries of Theorem 4.9 — helpers of piece C -/


/-- **C1.** If `B₁ ⊆ B` separates the two complementary components of `B`, every separating curve
of `B₁` is a separating curve of `B`. -/
theorem cor_separatingCurves_subset {B B₁ : Set ℂ} (hsub : B₁ ⊆ B)
    (hsep : SeparatesComplement B₁ B) : separatingCurves B₁ ⊆ separatingCurves B := by
  intro γ hγ
  obtain ⟨hclosed, htr, hseg⟩ := hγ
  have htrB : γ.closedTrace ⊆ B := htr.trans hsub
  refine ⟨hclosed, htrB, ?_⟩
  intro x hx y hy hne
  obtain ⟨x₁, hx₁, x₂, hx₂, hE1, hE2, hne'⟩ := hsep x hx y hy hne
  have hmono : ∀ {S T : Set ExtPlane} {z : ExtPlane}, S ⊆ T → z ∈ S →
      connectedComponentIn S z ⊆ connectedComponentIn T z := fun hST hz =>
    isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hz) ((connectedComponentIn_subset _ _).trans hST)
  have hB1trace : (toExt B₁)ᶜ ⊆ (toExt γ.closedTrace)ᶜ := fun z hz hzt =>
    hz (image_mono htr hzt)
  have hx1mem : x ∈ connectedComponentIn (toExt B₁)ᶜ x₁ := hE1 (mem_connectedComponentIn hx)
  have hx2mem : y ∈ connectedComponentIn (toExt B₁)ᶜ x₂ := hE2 (mem_connectedComponentIn hy)
  have hcompx : connectedComponentIn (toExt γ.closedTrace)ᶜ x =
      connectedComponentIn (toExt γ.closedTrace)ᶜ x₁ :=
    (connectedComponentIn_eq (hmono hB1trace hx₁ hx1mem)).symm
  have hcompy : connectedComponentIn (toExt γ.closedTrace)ᶜ y =
      connectedComponentIn (toExt γ.closedTrace)ᶜ x₂ :=
    (connectedComponentIn_eq (hmono hB1trace hx₂ hx2mem)).symm
  rw [hcompx, hcompy]
  exact hseg x₁ hx₁ x₂ hx₂ hne'

/-- Reflexivity of `LRCurve.Contains`. -/
theorem cor_b_contains_refl (γ : LRCurve) : γ.Contains γ :=
  ⟨id, monotoneOn_id, mapsTo_id _,
    fun _ _ => ⟨1, univ, univ_mem, (LipschitzWith.id).lipschitzOnWith⟩, eqOn_refl _ _⟩

/-! ### Corollaries of Theorem 4.9 — helpers of piece EQ2 -/


/-- **cor_c helper.** `SeparatesComplement B (annulus r₁ r₂)` gives `SeparatesSets B {0} {∞}`. -/
theorem cor_c_separatesSets_of_separatesComplement_annulus {r₁ r₂ : ℝ} (h₁ : 0 < r₁)
    (h₂ : r₁ < r₂) {B : Set ℂ} (hsep : SeparatesComplement B (annulus r₁ r₂)) :
    SeparatesSets B {((0 : ℂ) : ExtPlane)} {extInf} := by
  have h0 : ((0 : ℂ) : ExtPlane) ∈ (toExt (annulus r₁ r₂))ᶜ := zero_mem_compl_toExt_annulus h₁
  have hinf : (extInf : ExtPlane) ∈ (toExt (annulus r₁ r₂))ᶜ := extInf_mem_compl_toExt _
  have hne : connectedComponentIn (toExt (annulus r₁ r₂))ᶜ ((0 : ℂ) : ExtPlane) ≠
      connectedComponentIn (toExt (annulus r₁ r₂))ᶜ extInf :=
    connectedComponentIn_compl_toExt_annulus_ne h₁ h₂
  obtain ⟨x1, hx1, x2, hx2, h1sub, h2sub, hcompne⟩ := hsep _ h0 _ hinf hne
  exact ⟨x1, hx1, x2, hx2,
    (singleton_subset_iff.2 (mem_connectedComponentIn h0)).trans h1sub,
    (singleton_subset_iff.2 (mem_connectedComponentIn hinf)).trans h2sub, hcompne⟩

/-- **cor_c helper.** The closure of an annulus is inside the annulus together with its two
boundary circles. -/
theorem cor_c_closure_annulus_sub (s₁ s₂ : ℝ) :
    closure (annulus s₁ s₂) ⊆ annulus s₁ s₂ ∪ sphere (0 : ℂ) s₁ ∪ sphere (0 : ℂ) s₂ := by
  have hsub : annulus s₁ s₂ ⊆ {z : ℂ | s₁ ≤ ‖z‖ ∧ ‖z‖ ≤ s₂} := fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hclosed : IsClosed {z : ℂ | s₁ ≤ ‖z‖ ∧ ‖z‖ ≤ s₂} :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hcl : closure (annulus s₁ s₂) ⊆ {z : ℂ | s₁ ≤ ‖z‖ ∧ ‖z‖ ≤ s₂} :=
    closure_minimal hsub hclosed
  intro z hz
  obtain ⟨hz1, hz2⟩ := hcl hz
  rcases eq_or_lt_of_le hz1 with heq1 | hlt1
  · exact Or.inl (Or.inr (mem_sphere_zero_iff_norm.2 heq1.symm))
  · rcases eq_or_lt_of_le hz2 with heq2 | hlt2
    · exact Or.inr (mem_sphere_zero_iff_norm.2 heq2)
    · exact Or.inl (Or.inl ⟨hlt1, hlt2⟩)

/-- **cor_c helper.** If a round annulus `annulus s₁ s₂` is doubly connected and sits inside
`annulus r₁ r₂` (with `0 < r₁`), then `0 < s₁ < s₂`. -/
theorem cor_c_pos_of_isDoublyConnected_annulus_subset {s₁ s₂ r₁ r₂ : ℝ}
    (hB : IsDoublyConnected (annulus s₁ s₂)) (hr₁ : 0 < r₁)
    (hsub : annulus s₁ s₂ ⊆ annulus r₁ r₂) : 0 < s₁ ∧ s₁ < s₂ := by
  obtain ⟨z0, hz0₁, hz0₂⟩ := hB.2.1.nonempty
  have hs2pos : 0 < s₂ := lt_of_le_of_lt (norm_nonneg z0) hz0₂
  refine ⟨?_, hz0₁.trans hz0₂⟩
  by_contra hs1
  push_neg at hs1
  have hmpos : 0 < min r₁ s₂ := lt_min hr₁ hs2pos
  set t0 : ℝ := min r₁ s₂ / 2 with ht0def
  have ht0pos : 0 < t0 := by positivity
  have ht0ltr1 : t0 < r₁ := by
    have h1 : min r₁ s₂ ≤ r₁ := min_le_left _ _
    linarith
  have ht0lts2 : t0 < s₂ := by
    have h2 : min r₁ s₂ ≤ s₂ := min_le_right _ _
    linarith
  have hnorm : ‖(t0 : ℂ)‖ = t0 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0pos]
  have ht0mem : (t0 : ℂ) ∈ annulus s₁ s₂ :=
    ⟨by rw [hnorm]; linarith, by rw [hnorm]; exact ht0lts2⟩
  obtain ⟨hcontra1, hcontra2⟩ := hsub ht0mem
  rw [hnorm] at hcontra1
  exact absurd hcontra1 (not_lt.2 ht0ltr1.le)

/-- **cor_c helper.** The modulus of an annulus equals `(1/2π)` times the weighted area
integral, for any `0 < s₁ < s₂`. -/
theorem cor_c_dcModulus_annulus_eq_integral {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : s₁ < s₂) :
    dcModulus (annulus s₁ s₂) =
      ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in annulus s₁ s₂, ENNReal.ofReal (1 / ‖z‖ ^ 2) := by
  rw [dcModulus_annulus h₁ h₂, lintegral_annulus_inv_normSq h₁ h₂, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity),
    show 1 / (2 * π) * (2 * π) = 1 by field_simp, ENNReal.ofReal_one, one_mul]

/-- **Theorem 4.10**: if `B₁ ⊆ B` separates the two components of `ℂ̄ ∖ B`, then
`M(B₁) ≤ M(B)`.

Proved (2026-09-21) from Theorem 4.9 (`thm4_9_dcModulus_eq`) and the `cor_` helpers above. -/
theorem thm4_10_dcModulus_mono {B B₁ : Set ℂ} (hB : IsDoublyConnected B)
    (hB₁ : IsDoublyConnected B₁) (hsub : B₁ ⊆ B) (hsep : SeparatesComplement B₁ B) :
    dcModulus B₁ ≤ dcModulus B := by
  rw [thm4_9_dcModulus_eq hB, thm4_9_dcModulus_eq hB₁]
  have hle : extremalLength (separatingCurves B) ≤ extremalLength (separatingCurves B₁) := by
    apply thm3_2_comparison
    intro γ₁ hγ₁
    exact ⟨γ₁, cor_separatingCurves_subset hsub hsep hγ₁, cor_b_contains_refl γ₁⟩
  exact ENNReal.div_le_div_left hle _

/-- **Theorem 4.11**: if `B₁, B₂ ⊆ B` are disjoint and both separate the two components of
`ℂ̄ ∖ B`, then `M(B₁) + M(B₂) ≤ M(B)`.

Proved (2026-09-21) from Theorem 4.9 (`thm4_9_dcModulus_eq`) and the `cor_` helpers above. -/
theorem thm4_11_dcModulus_subadditive {B B₁ B₂ : Set ℂ} (hB : IsDoublyConnected B)
    (hB₁ : IsDoublyConnected B₁) (hB₂ : IsDoublyConnected B₂) (hsub₁ : B₁ ⊆ B) (hsub₂ : B₂ ⊆ B)
    (hdisj : Disjoint B₁ B₂) (hsep₁ : SeparatesComplement B₁ B)
    (hsep₂ : SeparatesComplement B₂ B) : dcModulus B₁ + dcModulus B₂ ≤ dcModulus B := by
  rw [thm4_9_dcModulus_eq hB, thm4_9_dcModulus_eq hB₁, thm4_9_dcModulus_eq hB₂]
  have hΓ₁ : ∀ γ ∈ separatingCurves B₁, γ.trace ⊆ B₁ := fun γ hγ =>
    (image_mono Ioo_subset_Icc_self).trans hγ.2.1
  have hΓ₂ : ∀ γ ∈ separatingCurves B₂, γ.trace ⊆ B₂ := fun γ hγ =>
    (image_mono Ioo_subset_Icc_self).trans hγ.2.1
  have h1 : ∀ γ₁ ∈ separatingCurves B₁, ∃ γ ∈ separatingCurves B, γ₁.Contains γ := fun γ₁ hγ₁ =>
    ⟨γ₁, cor_separatingCurves_subset hsub₁ hsep₁ hγ₁, cor_b_contains_refl γ₁⟩
  have h2 : ∀ γ₂ ∈ separatingCurves B₂, ∃ γ ∈ separatingCurves B, γ₂.Contains γ := fun γ₂ hγ₂ =>
    ⟨γ₂, cor_separatingCurves_subset hsub₂ hsep₂ hγ₂, cor_b_contains_refl γ₂⟩
  have hcomp := thm3_3_composition_i hB₁.1 hB₂.1 hdisj hΓ₁ hΓ₂ h1 h2
  have hmul := mul_le_mul_right hcomp (ENNReal.ofReal (2 * π))
  rw [mul_add] at hmul
  rwa [← div_eq_mul_inv, ← div_eq_mul_inv, ← div_eq_mul_inv] at hmul

/-- **Theorem 4.11** (equality case): when `B` is an annulus, equality holds iff `B₁` and `B₂`
are (concentric) annuli and `B₁ ∪ B₂ = B` (up to the common boundary circle).

Proved (2026-09-21) from Theorem 4.9 (`thm4_9_dcModulus_eq`) and the `cor_` helpers above. -/
theorem thm4_11_eq_iff {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) {B₁ B₂ : Set ℂ}
    (hB₁ : IsDoublyConnected B₁) (hB₂ : IsDoublyConnected B₂) (hsub₁ : B₁ ⊆ annulus r₁ r₂)
    (hsub₂ : B₂ ⊆ annulus r₁ r₂) (hdisj : Disjoint B₁ B₂)
    (hsep₁ : SeparatesComplement B₁ (annulus r₁ r₂))
    (hsep₂ : SeparatesComplement B₂ (annulus r₁ r₂)) :
    dcModulus B₁ + dcModulus B₂ = dcModulus (annulus r₁ r₂) ↔
      (∃ s₁ s₂ : ℝ, B₁ = annulus s₁ s₂) ∧ (∃ s₁ s₂ : ℝ, B₂ = annulus s₁ s₂) ∧
        closure (annulus r₁ r₂) = closure B₁ ∪ closure B₂ := by
  have hB1o : IsOpen B₁ := hB₁.1
  have hB2o : IsOpen B₂ := hB₂.1
  have hAo : IsOpen (annulus r₁ r₂) := isOpen_annulus r₁ r₂
  have hB1meas : MeasurableSet B₁ := hB1o.measurableSet
  have hB2meas : MeasurableSet B₂ := hB2o.measurableSet
  set ρ : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (1 / ‖z‖ ^ 2) with hρdef
  have hss1 := cor_c_separatesSets_of_separatesComplement_annulus h₁ h₂ hsep₁
  have hss2 := cor_c_separatesSets_of_separatesComplement_annulus h₁ h₂ hsep₂
  have hA1 : dcModulus B₁ ≤ ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in B₁, ρ z := eq4_22 hB₁ hss1
  have hA2 : dcModulus B₂ ≤ ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in B₂, ρ z := eq4_22 hB₂ hss2
  have hAeq : dcModulus (annulus r₁ r₂) =
      ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in annulus r₁ r₂, ρ z :=
    cor_c_dcModulus_annulus_eq_integral h₁ h₂
  have hAfin : (∫⁻ z in annulus r₁ r₂, ρ z) < ⊤ := by
    rw [hρdef]; simp only; rw [lintegral_annulus_inv_normSq h₁ h₂]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hintle : (∫⁻ z in B₁, ρ z) + (∫⁻ z in B₂, ρ z) ≤ ∫⁻ z in annulus r₁ r₂, ρ z := by
    rw [← lintegral_union hB2meas hdisj]
    exact lintegral_mono_set (union_subset hsub₁ hsub₂)
  have hB1fin : (∫⁻ z in B₁, ρ z) < ⊤ := lt_of_le_of_lt (le_add_right le_rfl) (hintle.trans_lt hAfin)
  have hB2fin : (∫⁻ z in B₂, ρ z) < ⊤ := lt_of_le_of_lt (le_add_left le_rfl) (hintle.trans_lt hAfin)
  have hM2fin : dcModulus B₂ ≠ ⊤ :=
    (hA2.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB2fin)).ne
  have hM1fin : dcModulus B₁ ≠ ⊤ :=
    (hA1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB1fin)).ne
  constructor
  · intro heq
    have hM1eq : dcModulus B₁ = ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in B₁, ρ z := by
      by_contra hne
      have hlt : dcModulus B₁ < ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in B₁, ρ z :=
        lt_of_le_of_ne hA1 hne
      have hsum : dcModulus B₁ + dcModulus B₂ <
          ENNReal.ofReal (1 / (2 * π)) * (∫⁻ z in B₁, ρ z) +
            ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in B₂, ρ z :=
        ENNReal.add_lt_add_of_lt_of_le hM2fin hlt hA2
      have hge : ENNReal.ofReal (1 / (2 * π)) * (∫⁻ z in B₁, ρ z) +
          ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in B₂, ρ z ≤ dcModulus B₁ + dcModulus B₂ := by
        rw [← mul_add, heq, hAeq]
        exact mul_le_mul_right hintle _
      exact absurd hsum (not_lt.2 hge)
    have hM2eq : dcModulus B₂ = ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in B₂, ρ z := by
      by_contra hne
      have hlt : dcModulus B₂ < ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in B₂, ρ z :=
        lt_of_le_of_ne hA2 hne
      have hsum : dcModulus B₁ + dcModulus B₂ <
          ENNReal.ofReal (1 / (2 * π)) * (∫⁻ z in B₁, ρ z) +
            ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in B₂, ρ z := by
        calc dcModulus B₁ + dcModulus B₂ = dcModulus B₂ + dcModulus B₁ := add_comm _ _
          _ < (ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in B₂, ρ z) +
                ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in B₁, ρ z :=
              ENNReal.add_lt_add_of_lt_of_le hM1fin hlt hA1
          _ = ENNReal.ofReal (1 / (2 * π)) * (∫⁻ z in B₁, ρ z) +
                ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in B₂, ρ z := add_comm _ _
      have hge : ENNReal.ofReal (1 / (2 * π)) * (∫⁻ z in B₁, ρ z) +
          ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in B₂, ρ z ≤ dcModulus B₁ + dcModulus B₂ := by
        rw [← mul_add, heq, hAeq]
        exact mul_le_mul_right hintle _
      exact absurd hsum (not_lt.2 hge)
    have hintfin : (∫⁻ z in B₁, ρ z) + (∫⁻ z in B₂, ρ z) ≠ ⊤ :=
      (ENNReal.add_lt_top.2 ⟨hB1fin, hB2fin⟩).ne
    have hinteq : (∫⁻ z in B₁, ρ z) + (∫⁻ z in B₂, ρ z) = ∫⁻ z in annulus r₁ r₂, ρ z := by
      have h1 := heq
      rw [hM1eq, hM2eq, ← mul_add, hAeq] at h1
      exact (ENNReal.mul_right_inj (by positivity) ENNReal.ofReal_ne_top).1 h1
    have hunionmeas : MeasurableSet (B₁ ∪ B₂) := hB1meas.union hB2meas
    have hTsub : B₁ ∪ B₂ ⊆ annulus r₁ r₂ := union_subset hsub₁ hsub₂
    have hAsplit : ∫⁻ z in annulus r₁ r₂, ρ z =
        (∫⁻ z in (annulus r₁ r₂) \ (B₁ ∪ B₂), ρ z) + ∫⁻ z in B₁ ∪ B₂, ρ z := by
      conv_lhs => rw [← diff_union_of_subset hTsub]
      exact lintegral_union hunionmeas disjoint_sdiff_self_left
    have hunioneq : ∫⁻ z in B₁ ∪ B₂, ρ z = (∫⁻ z in B₁, ρ z) + ∫⁻ z in B₂, ρ z :=
      lintegral_union hB2meas hdisj
    have hzero : (∫⁻ z in (annulus r₁ r₂) \ (B₁ ∪ B₂), ρ z) = 0 := by
      have key : (∫⁻ z in B₁, ρ z) + (∫⁻ z in B₂, ρ z) =
          (∫⁻ z in (annulus r₁ r₂) \ (B₁ ∪ B₂), ρ z) +
            ((∫⁻ z in B₁, ρ z) + ∫⁻ z in B₂, ρ z) := by
        calc (∫⁻ z in B₁, ρ z) + (∫⁻ z in B₂, ρ z) = ∫⁻ z in annulus r₁ r₂, ρ z := hinteq
          _ = (∫⁻ z in (annulus r₁ r₂) \ (B₁ ∪ B₂), ρ z) + ∫⁻ z in B₁ ∪ B₂, ρ z := hAsplit
          _ = (∫⁻ z in (annulus r₁ r₂) \ (B₁ ∪ B₂), ρ z) +
                ((∫⁻ z in B₁, ρ z) + ∫⁻ z in B₂, ρ z) := by rw [hunioneq]
      have key2 : (∫⁻ z in B₁, ρ z) + (∫⁻ z in B₂, ρ z) + 0 =
          (∫⁻ z in B₁, ρ z) + (∫⁻ z in B₂, ρ z) +
            (∫⁻ z in (annulus r₁ r₂) \ (B₁ ∪ B₂), ρ z) := by
        rw [add_zero]
        calc (∫⁻ z in B₁, ρ z) + (∫⁻ z in B₂, ρ z)
            = (∫⁻ z in (annulus r₁ r₂) \ (B₁ ∪ B₂), ρ z) +
                ((∫⁻ z in B₁, ρ z) + ∫⁻ z in B₂, ρ z) := key
          _ = (∫⁻ z in B₁, ρ z) + (∫⁻ z in B₂, ρ z) +
                (∫⁻ z in (annulus r₁ r₂) \ (B₁ ∪ B₂), ρ z) := add_comm _ _
      exact ((ENNReal.add_right_inj hintfin).1 key2).symm
    have hzeroS : volume ((annulus r₁ r₂) \ (B₁ ∪ B₂)) = 0 := by
      by_contra hvne
      have hvpos : 0 < volume ((annulus r₁ r₂) \ (B₁ ∪ B₂)) := pos_iff_ne_zero.2 hvne
      have hbound : ∀ z ∈ (annulus r₁ r₂) \ (B₁ ∪ B₂), ENNReal.ofReal (1 / r₂ ^ 2) ≤ ρ z := by
        intro z hz
        have hzr2 : ‖z‖ < r₂ := hz.1.2
        have hzpos : 0 < ‖z‖ := h₁.trans hz.1.1
        rw [hρdef]
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact (pow_lt_pow_left₀ hzr2 hzpos.le two_ne_zero).le
      have hlarger : ENNReal.ofReal (1 / r₂ ^ 2) * volume ((annulus r₁ r₂) \ (B₁ ∪ B₂)) ≤
          ∫⁻ z in (annulus r₁ r₂) \ (B₁ ∪ B₂), ρ z := by
        rw [← setLIntegral_const]
        exact setLIntegral_mono_ae' ((isOpen_annulus r₁ r₂).measurableSet.diff hunionmeas)
          (Filter.Eventually.of_forall hbound)
      rw [hzero] at hlarger
      have hr2pos : (0:ℝ) < r₂ := h₁.trans h₂
      have : (0:ℝ≥0∞) < ENNReal.ofReal (1 / r₂ ^ 2) * volume ((annulus r₁ r₂) \ (B₁ ∪ B₂)) :=
        ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne' hvpos.ne'
      exact absurd hlarger (not_le.2 this)
    have hclosure_eq : closure (annulus r₁ r₂) = closure B₁ ∪ closure B₂ := by
      have hU : IsOpen (annulus r₁ r₂ \ (closure B₁ ∪ closure B₂)) :=
        hAo.sdiff (isClosed_closure.union isClosed_closure)
      have hUnull : volume (annulus r₁ r₂ \ (closure B₁ ∪ closure B₂)) = 0 := by
        apply measure_mono_null _ hzeroS
        apply diff_subset_diff_right
        exact union_subset_union subset_closure subset_closure
      have hUempty : annulus r₁ r₂ \ (closure B₁ ∪ closure B₂) = ∅ :=
        hU.eq_empty_of_measure_zero hUnull
      have hforward : annulus r₁ r₂ ⊆ closure B₁ ∪ closure B₂ := diff_eq_empty.1 hUempty
      apply Subset.antisymm
      · calc closure (annulus r₁ r₂) ⊆ closure (closure B₁ ∪ closure B₂) :=
              closure_mono hforward
          _ = closure B₁ ∪ closure B₂ :=
              (isClosed_closure.union isClosed_closure).closure_eq
      · exact union_subset (closure_mono hsub₁) (closure_mono hsub₂)
    have hfin1 : ∫⁻ z in B₁, ρ z < ⊤ := hB1fin
    have hB1round : ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ s₁ < s₂ ∧ B₁ = annulus s₁ s₂ :=
      (eq4_22_eq_iff hB₁ hss1 hfin1).1 hM1eq
    have hfin2 : ∫⁻ z in B₂, ρ z < ⊤ := hB2fin
    have hB2round : ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ s₁ < s₂ ∧ B₂ = annulus s₁ s₂ :=
      (eq4_22_eq_iff hB₂ hss2 hfin2).1 hM2eq
    exact ⟨⟨hB1round.choose, hB1round.choose_spec.choose,
        hB1round.choose_spec.choose_spec.2.2⟩,
      ⟨hB2round.choose, hB2round.choose_spec.choose,
        hB2round.choose_spec.choose_spec.2.2⟩,
      hclosure_eq⟩
  · rintro ⟨⟨s₁, s₂, hB1eq⟩, ⟨s₁', s₂', hB2eq⟩, hclosure⟩
    subst hB1eq hB2eq
    obtain ⟨hs1pos, hs1lt⟩ := cor_c_pos_of_isDoublyConnected_annulus_subset hB₁ h₁ hsub₁
    obtain ⟨hs1'pos, hs1'lt⟩ := cor_c_pos_of_isDoublyConnected_annulus_subset hB₂ h₁ hsub₂
    have hM1 : dcModulus (annulus s₁ s₂) =
        ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in annulus s₁ s₂, ρ z :=
      cor_c_dcModulus_annulus_eq_integral hs1pos hs1lt
    have hM2 : dcModulus (annulus s₁' s₂') =
        ENNReal.ofReal (1 / (2 * π)) * ∫⁻ z in annulus s₁' s₂', ρ z :=
      cor_c_dcModulus_annulus_eq_integral hs1'pos hs1'lt
    have hunionmeas' : MeasurableSet (annulus s₁ s₂ ∪ annulus s₁' s₂') :=
      (isOpen_annulus s₁ s₂).measurableSet.union (isOpen_annulus s₁' s₂').measurableSet
    have hTsub' : annulus s₁ s₂ ∪ annulus s₁' s₂' ⊆ annulus r₁ r₂ := union_subset hsub₁ hsub₂
    have hdiffnull : volume (annulus r₁ r₂ \ (annulus s₁ s₂ ∪ annulus s₁' s₂')) = 0 := by
      have hsub4 : annulus r₁ r₂ \ (annulus s₁ s₂ ∪ annulus s₁' s₂') ⊆
          sphere (0 : ℂ) s₁ ∪ sphere (0 : ℂ) s₂ ∪ (sphere (0 : ℂ) s₁' ∪ sphere (0 : ℂ) s₂') := by
        intro z hz
        have hzcl : z ∈ closure (annulus r₁ r₂) := subset_closure hz.1
        rw [hclosure] at hzcl
        rcases hzcl with hz1 | hz2
        · rcases cor_c_closure_annulus_sub s₁ s₂ hz1 with (h | h) | h
          · exact absurd h (fun hh => hz.2 (Or.inl hh))
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
        · rcases cor_c_closure_annulus_sub s₁' s₂' hz2 with (h | h) | h
          · exact absurd h (fun hh => hz.2 (Or.inr hh))
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
      refine measure_mono_null hsub4 ?_
      refine measure_union_null (measure_union_null ?_ ?_) (measure_union_null ?_ ?_)
      · exact Measure.addHaar_sphere volume (0 : ℂ) s₁
      · exact Measure.addHaar_sphere volume (0 : ℂ) s₂
      · exact Measure.addHaar_sphere volume (0 : ℂ) s₁'
      · exact Measure.addHaar_sphere volume (0 : ℂ) s₂'
    have hzerolint : (∫⁻ z in annulus r₁ r₂ \ (annulus s₁ s₂ ∪ annulus s₁' s₂'), ρ z) = 0 := by
      have hz0 : volume.restrict (annulus r₁ r₂ \ (annulus s₁ s₂ ∪ annulus s₁' s₂')) = 0 :=
        Measure.restrict_eq_zero.2 hdiffnull
      rw [hz0, lintegral_zero_measure]
    have hintsplit : ∫⁻ z in annulus r₁ r₂, ρ z =
        (∫⁻ z in annulus r₁ r₂ \ (annulus s₁ s₂ ∪ annulus s₁' s₂'), ρ z) +
          ∫⁻ z in annulus s₁ s₂ ∪ annulus s₁' s₂', ρ z := by
      conv_lhs => rw [← diff_union_of_subset hTsub']
      exact lintegral_union hunionmeas' disjoint_sdiff_self_left
    have hinteq2 : ∫⁻ z in annulus s₁ s₂ ∪ annulus s₁' s₂', ρ z =
        (∫⁻ z in annulus s₁ s₂, ρ z) + ∫⁻ z in annulus s₁' s₂', ρ z :=
      lintegral_union (isOpen_annulus s₁' s₂').measurableSet hdisj
    rw [hzerolint, zero_add, hinteq2] at hintsplit
    rw [hM1, hM2, hAeq, ← mul_add]
    congr 1
    exact hintsplit.symm

end LiZhongQC
