import References.LehtoVirtanen1973.Ch01.S04_ModuleExtremalLength
import LiZhongQC.Ch04.S16_Quasicircles

/-!
# Lehto–Virtanen, Chapter I §5: Two basic properties of quasiconformal mappings

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. I §5
(pp. 28–30; `full.md` P1:731–772).

Uniform convergence of mappings into `ℂ̄` is taken in the spherical metric (§1.1).

* Theorem 5.1 (§5.1) — `thm1_5_1`
* Definition (uniform convergence in every compact subset, spherical metric, §5.2) — `TendstoUniformlyOnCompactsSph`
* Theorem 5.2 (§5.2) — `thm1_5_2`
* Theorem 5.3 (§5.3) — `thm1_5_3`
* Definition (`K`-quasiconformal mapping of a quadrilateral, §5.3) — `IsKQCQuadMap`
* Lemma 5.1 (§5.3) — `lemma1_5_1`
* Unlabelled (Ch. I §3.1–3.2, P1:381, 391; moved here from §3, after the converse bridge): a conformal mapping
  is `1`-quasiconformal — `conformal_isKQuasiconformal_one`
* Unlabelled (Ch. I §3.2, P1:397; moved here from §3, after the converse bridge): the inverse of a
  `K`-quasiconformal mapping is `K`-quasiconformal; composition — `kqc_inv`, `kqc_comp`
* Unlabelled (Ch. I §2.4, P1:357, 361; moved here from §2, after the converse bridge): canonical mappings exist, also onto the
  rectangle `R(0, M(Q), M(Q) + i, i)` — `exists_canonicalMap`, `exists_canonicalMap_normalized`
* The Riemann mapping theorem (Ch. I §2.1, P1:327; moved here from §2, after the Möbius and Riemann-map bridges) —
  `riemann_mapping_theorem`
-/

open Complex Set Filter Topology
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-- Helper (D). The charts at `∞` (I.1.6) are the inversion `ζ ↦ 1/ζ` of `ℂ̄`, a Möbius map `M = mobiusExt 0 1 1 0`:
`extChartInv ∞ ζ = M ζ` and `extChart ∞ q = finiteValue (M q)`. -/
theorem lv15_chart_infty :
    (∀ ζ : ℂ, extChartInv extInf ζ = LiZhongQC.mobiusExt 0 1 1 0 ζ) ∧
      ∀ q : ExtPlane, extChart extInf q = finiteValue (LiZhongQC.mobiusExt 0 1 1 0 q) := by
  refine ⟨fun ζ => ?_, fun q => ?_⟩
  · by_cases h : ζ = 0
    · simp [extChartInv, LiZhongQC.mobiusExt, h]
    · simp [extChartInv, LiZhongQC.mobiusExt, h]
  · induction q using OnePoint.rec with
    | infty => simp [extChart, LiZhongQC.mobiusExt, finiteValue]
    | coe b =>
      by_cases h : b = 0
      · simp [extChart, LiZhongQC.mobiusExt, finiteValue, h]
      · simp [extChart, LiZhongQC.mobiusExt, finiteValue, h]

/-- Helper (D). `finiteValue` is continuous at every finite point of `ℂ̄`. -/
theorem lv15_finiteValue_continuousAt (c : ℂ) : ContinuousAt finiteValue (c : ExtPlane) := by
  rw [OnePoint.continuousAt_coe]
  have e : finiteValue ∘ ((↑) : ℂ → ExtPlane) = id := funext fun _ => rfl
  rw [e]
  exact continuous_id.continuousAt

/-- Helper (D). The inverse chart at `z` maps `0` to `z` and is continuous at `0`. -/
theorem lv15_extChartInv (z : ExtPlane) : extChartInv z 0 = z ∧ ContinuousAt (extChartInv z) 0 := by
  induction z using OnePoint.rec with
  | infty =>
    have e : extChartInv extInf = fun ζ : ℂ => LiZhongQC.mobiusExt 0 1 1 0 ζ := funext lv15_chart_infty.1
    refine ⟨by simp [extChartInv], ?_⟩
    rw [e]
    exact ((LiZhongQC.continuous_mobiusExt (by norm_num)).comp OnePoint.continuous_coe).continuousAt
  | coe a =>
    have e : extChartInv (a : ExtPlane) = fun ζ : ℂ => ((a + ζ : ℂ) : ExtPlane) := rfl
    refine ⟨by simp [extChartInv], ?_⟩
    rw [e]
    exact (OnePoint.continuous_coe.comp (continuous_const.add continuous_id)).continuousAt

/-- Helper (D). The chart at `p` maps `p` to `0` and is continuous at `p`. -/
theorem lv15_extChart (p : ExtPlane) : extChart p p = 0 ∧ ContinuousAt (extChart p) p := by
  induction p using OnePoint.rec with
  | infty =>
    have e : extChart extInf = fun q => finiteValue (LiZhongQC.mobiusExt 0 1 1 0 q) := funext lv15_chart_infty.2
    refine ⟨rfl, ?_⟩
    rw [e]
    have hM : LiZhongQC.mobiusExt 0 1 1 0 extInf = ((0 : ℂ) : ExtPlane) := by simp [LiZhongQC.mobiusExt]
    show ContinuousAt (finiteValue ∘ LiZhongQC.mobiusExt 0 1 1 0) extInf
    refine ContinuousAt.comp ?_ (LiZhongQC.continuous_mobiusExt (by norm_num)).continuousAt
    rw [hM]
    exact lv15_finiteValue_continuousAt 0
  | coe a =>
    refine ⟨by simp [extChart], ?_⟩
    rw [OnePoint.continuousAt_coe]
    have e : extChart (a : ExtPlane) ∘ ((↑) : ℂ → ExtPlane) = fun b => b - a := by
      funext b
      simp [extChart]
    rw [e]
    exact (continuous_id.sub continuous_const).continuousAt

/-- Helper (D, ∞-chart bridge). The local representation of `w` at `z` (I.1.6) is continuous at `0` when `w` is
continuous at `z`: the charts `ζ ↦ z + ζ`, `ζ ↦ 1/ζ` and their inverses are continuous (the inversion being a Möbius
map of `ℂ̄`). -/
theorem lv15_localRep_continuousAt {w : ExtPlane → ExtPlane} {z : ExtPlane} (hc : ContinuousAt w z) :
    ContinuousAt (localRep w z) 0 := by
  obtain ⟨h0, hcz⟩ := lv15_extChartInv z
  have h1 : ContinuousAt (fun ζ => w (extChartInv z ζ)) 0 :=
    ContinuousAt.comp (g := w) (by rw [h0]; exact hc) hcz
  have h2 : ContinuousAt (extChart (w z)) (w (extChartInv z 0)) := by
    rw [h0]
    exact (lv15_extChart (w z)).2
  exact ContinuousAt.comp (g := extChart (w z)) h2 h1

/-- Helper (D). Complex differentiability of `localRep w z` at `ζ₀`, read through the charts: `extChartInv z` agrees
near `ζ₀` with `T` (holomorphic at `ζ₀`), `w` is finite near `T ζ₀` where `finiteMap w` is complex differentiable, and
the outer chart is a translation or, when `w z = ∞`, the inversion at a nonzero value. -/
theorem lv15_localRep_differentiableAt_of {w : ExtPlane → ExtPlane} {z : ExtPlane} {ζ₀ : ℂ} {T : ℂ → ℂ}
    (hT : ∀ᶠ ζ in 𝓝 ζ₀, extChartInv z ζ = ((T ζ : ℂ) : ExtPlane)) (hTd : DifferentiableAt ℂ T ζ₀)
    (hfin : ∀ᶠ x : ℂ in 𝓝 (T ζ₀), w x ≠ extInf) (hd : DifferentiableAt ℂ (finiteMap w) (T ζ₀))
    (hne : w z = extInf → finiteMap w (T ζ₀) ≠ 0) : DifferentiableAt ℂ (localRep w z) ζ₀ := by
  have hfin' : ∀ᶠ ζ in 𝓝 ζ₀, w ((T ζ : ℂ) : ExtPlane) ≠ extInf := hTd.continuousAt.eventually hfin
  have hFd : DifferentiableAt ℂ (fun ζ => finiteMap w (T ζ)) ζ₀ := hd.comp ζ₀ hTd
  generalize hq : w z = q at hne
  induction q using OnePoint.rec with
  | infty =>
    refine (hFd.inv (hne rfl)).congr_of_eventuallyEq ?_
    filter_upwards [hT, hfin'] with ζ h1 h2
    obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.1 h2
    show extChart (w z) (w (extChartInv z ζ)) = (finiteValue (w ((T ζ : ℂ) : ExtPlane)))⁻¹
    rw [h1, hq, ← hv]
    rfl
  | coe c =>
    refine (hFd.sub_const c).congr_of_eventuallyEq ?_
    filter_upwards [hT, hfin'] with ζ h1 h2
    obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.1 h2
    show extChart (w z) (w (extChartInv z ζ)) = finiteValue (w ((T ζ : ℂ) : ExtPlane)) - c
    rw [h1, hq, ← hv]
    rfl

/-- Helper (D). The punctured differentiability of `localRep w z` for a chart `extChartInv z = T` off `0` with
`T ζ ≠ z` and `T ζ ∉ E` for small `ζ ≠ 0`. -/
theorem lv15_punctured_of_chart {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsOpen G)
    (hc : ContinuousOn w G) (hi : InjOn w G) {E : Set ℂ}
    (hd : ∀ ζ : ℂ, (ζ : ExtPlane) ∈ G → w ζ ≠ extInf → ζ ∉ E → DifferentiableAt ℂ (finiteMap w) ζ)
    {z : ExtPlane} (hz : z ∈ G) {T : ℂ → ℂ} (hTeq : ∀ ζ : ℂ, ζ ≠ 0 → extChartInv z ζ = ((T ζ : ℂ) : ExtPlane))
    (hTd : ∀ ζ : ℂ, ζ ≠ 0 → DifferentiableAt ℂ T ζ) (hTE : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), T ζ ∉ E)
    (hTz : ∀ ζ : ℂ, ζ ≠ 0 → ((T ζ : ℂ) : ExtPlane) ≠ z) :
    ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ (localRep w z) ζ := by
  obtain ⟨h0, hcz⟩ := lv15_extChartInv z
  have hwc : ContinuousAt (fun ζ => w (extChartInv z ζ)) 0 :=
    ContinuousAt.comp (g := w) (by rw [h0]; exact hc.continuousAt (hG.mem_nhds hz)) hcz
  have hGev : ∀ᶠ ζ in 𝓝 (0 : ℂ), extChartInv z ζ ∈ G := hcz.eventually (by rw [h0]; exact hG.mem_nhds hz)
  -- `w` is finite at the chart images: by continuity, or by injectivity when `w z = ∞`
  have hfinev : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), w (extChartInv z ζ) ≠ extInf := by
    by_cases hwz : w z = extInf
    · filter_upwards [hGev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with ζ hζG hζ0 h
      exact hTz ζ hζ0 ((hTeq ζ hζ0).symm.trans (hi hζG hz (h.trans hwz.symm)))
    · exact (hwc.eventually_ne (by rw [h0]; exact hwz)).filter_mono nhdsWithin_le_nhds
  -- when `w z = ∞`, the values at the chart images stay away from `0`
  have hzero : ∀ᶠ ζ in 𝓝 (0 : ℂ), w z = extInf → w (extChartInv z ζ) ≠ ((0 : ℂ) : ExtPlane) := by
    by_cases hwz : w z = extInf
    · filter_upwards [hwc.eventually_ne (by rw [h0, hwz]; exact (OnePoint.coe_ne_infty 0).symm)] with ζ h
      exact fun _ => h
    · exact Eventually.of_forall fun ζ h => absurd h hwz
  filter_upwards [hGev.filter_mono nhdsWithin_le_nhds, hfinev, hTE, hzero.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with ζ hζG hζfin hζE hζ0' hζ0
  rw [hTeq ζ hζ0] at hζG hζfin hζ0'
  refine lv15_localRep_differentiableAt_of (T := T) ?_ (hTd ζ hζ0) ?_ (hd (T ζ) hζG hζfin hζE) ?_
  · filter_upwards [isOpen_compl_singleton.mem_nhds hζ0] with ξ hξ using hTeq ξ hξ
  · have hcp : ContinuousAt (fun x : ℂ => w x) (T ζ) :=
      ContinuousAt.comp (g := w) (hc.continuousAt (hG.mem_nhds hζG)) OnePoint.continuous_coe.continuousAt
    exact hcp.eventually_ne hζfin
  · intro hwz h
    apply hζ0' hwz
    obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.1 hζfin
    have hv' : finiteMap w (T ζ) = v := by
      show finiteValue (w ((T ζ : ℂ) : ExtPlane)) = v
      rw [← hv]
      rfl
    rw [← hv, ← hv', h]

/-- Helper (D, ∞-chart bridge). Let `w` be continuous and one-to-one on an open `G`, and let `finiteMap w` be
complex differentiable at the finite points of `G` with a finite value, outside a finite set `E`. Then at every
`z ∈ G` the local representation `localRep w z` is complex differentiable in a punctured neighbourhood of `0`. -/
theorem lv15_localRep_differentiableAt_punctured {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsOpen G)
    (hc : ContinuousOn w G) (hi : InjOn w G) {E : Set ℂ} (hE : E.Finite)
    (hd : ∀ ζ : ℂ, (ζ : ExtPlane) ∈ G → w ζ ≠ extInf → ζ ∉ E → DifferentiableAt ℂ (finiteMap w) ζ)
    {z : ExtPlane} (hz : z ∈ G) : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ (localRep w z) ζ := by
  -- finite sets are eventually avoided in a punctured neighbourhood of `0`
  have hnot : ∀ F : Set ℂ, F.Finite → ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ζ ∉ F := fun F hF => by
    have h1 : ∀ᶠ ζ in 𝓝 (0 : ℂ), ζ ∈ (F \ {0})ᶜ :=
      (hF.subset sdiff_subset).isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl
    filter_upwards [h1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with ζ hA hB hC
    exact hA ⟨hC, hB⟩
  induction z using OnePoint.rec with
  | infty =>
    refine lv15_punctured_of_chart hG hc hi hd hz (T := fun ζ => ζ⁻¹) (fun ζ hζ => ?_)
      (fun ζ hζ => differentiableAt_inv hζ) ?_ (fun ζ _ => OnePoint.coe_ne_infty _)
    · rw [lv15_chart_infty.1]
      simp [LiZhongQC.mobiusExt, hζ]
    · filter_upwards [hnot _ (hE.preimage inv_injective.injOn)] with ζ h using h
  | coe a =>
    refine lv15_punctured_of_chart hG hc hi hd hz (T := fun ζ => a + ζ) (fun ζ _ => rfl)
      (fun ζ _ => (differentiableAt_const a).add differentiableAt_id) ?_ (fun ζ hζ h => hζ ?_)
    · filter_upwards [hnot _ (hE.preimage (add_right_injective a).injOn)] with ζ h using h
    · simpa using OnePoint.coe_injective h

/-- Helper (D, ∞-chart bridge). A mapping `w`, continuous and one-to-one on a domain `G` of `ℂ̄`, whose finite part is
complex differentiable at the finite points of `G` with finite values outside a finite set, is a conformal mapping of
`G` (I.2.1): at `∞`, at `w⁻¹(∞)` and at the exceptional points the singularity of the local representation is
removable. -/
theorem lv15_isConformalMap_of_differentiableAt {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsDomainExt G)
    (hc : ContinuousOn w G) (hi : InjOn w G) {E : Set ℂ} (hE : E.Finite)
    (hd : ∀ ζ : ℂ, (ζ : ExtPlane) ∈ G → w ζ ≠ extInf → ζ ∉ E → DifferentiableAt ℂ (finiteMap w) ζ) :
    IsConformalMap w G := by
  refine ⟨hG, hc, hi, fun z hz => ?_⟩
  have h1 := lv15_localRep_continuousAt (hc.continuousAt (hG.1.mem_nhds hz))
  have h2 := lv15_localRep_differentiableAt_punctured hG.1 hc hi hE hd hz
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h2)
  -- the singularity at `0` is removable
  have hon : DifferentiableOn ℂ (localRep w z) (Metric.ball 0 r \ {0}) := fun ζ hζ =>
    (hball hζ.1 hζ.2).differentiableWithinAt
  exact ((Complex.differentiableOn_compl_singleton_and_continuousAt_iff (Metric.ball_mem_nhds 0 hr)).1
    ⟨hon, h1⟩).differentiableAt (Metric.ball_mem_nhds 0 hr)

/-- Helper (converse bridge, C2). A finite point of `ℂ̄` is the image of its finite value. -/
theorem lv15_coe_finiteValue {q : ExtPlane} (hq : q ≠ extInf) : ((finiteValue q : ℂ) : ExtPlane) = q := by
  obtain ⟨v, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hq
  rfl

/-- Helper (converse bridge, stage 2 (C2); Möbius group). Fractional linear transformations of `ℂ̄` are closed
under composition (`LiZhongQC.s16p_mobiusExt_comp`). -/
theorem lv15_isMobius_comp {S T : ExtPlane → ExtPlane} (hS : IsMobius S) (hT : IsMobius T) :
    IsMobius (S ∘ T) := by
  obtain ⟨a, b, c, d, h, rfl⟩ := hS
  obtain ⟨a', b', c', d', h', rfl⟩ := hT
  refine ⟨a * a' + b * c', a * b' + b * d', c * a' + d * c', c * b' + d * d', ?_, ?_⟩
  · rw [show (a * a' + b * c') * (c * b' + d * d') - (a * b' + b * d') * (c * a' + d * c') =
      (a * d - b * c) * (a' * d' - b' * c') by ring]
    exact mul_ne_zero h h'
  · funext p
    exact LiZhongQC.s16p_mobiusExt_comp h' p

/-- Helper (converse bridge, C2; Möbius group). A fractional linear transformation of `ℂ̄` has a fractional linear
inverse (`LiZhongQC.mobiusExt_inv_apply`). -/
theorem lv15_isMobius_inverse {T : ExtPlane → ExtPlane} (hT : IsMobius T) :
    ∃ S : ExtPlane → ExtPlane, IsMobius S ∧ (∀ q, S (T q) = q) ∧ ∀ q, T (S q) = q := by
  obtain ⟨a, b, c, d, h, rfl⟩ := hT
  have h' : d * a - -b * -c ≠ 0 := by rwa [show d * a - -b * -c = a * d - b * c by ring]
  refine ⟨LiZhongQC.mobiusExt d (-b) (-c) a, ⟨d, -b, -c, a, h', rfl⟩, LiZhongQC.mobiusExt_inv_apply h,
    fun q => ?_⟩
  simpa only [neg_neg] using LiZhongQC.mobiusExt_inv_apply h' q

/-- Helper (converse bridge, C2). `e⁻¹(e(s)) = s` for a homeomorphism `e` of `ℂ̄`. -/
theorem lv15_symm_image_image (e : ExtPlane ≃ₜ ExtPlane) (s : Set ExtPlane) : ⇑e.symm '' (⇑e '' s) = s := by
  rw [image_image]
  simp

/-- Helper (converse bridge, C2). A fractional linear transformation of `ℂ̄` is a homeomorphism whose inverse is
again fractional linear. -/
theorem lv15_mobius_homeomorph {T : ExtPlane → ExtPlane} (hT : IsMobius T) :
    ∃ e : ExtPlane ≃ₜ ExtPlane, ⇑e = T ∧ IsMobius ⇑e.symm := by
  obtain ⟨S, hS, hST, hTS⟩ := lv15_isMobius_inverse hT
  have hTc : Continuous T := by
    obtain ⟨a, b, c, d, h, rfl⟩ := hT
    exact LiZhongQC.continuous_mobiusExt h
  have hSc : Continuous S := by
    obtain ⟨a, b, c, d, h, rfl⟩ := hS
    exact LiZhongQC.continuous_mobiusExt h
  exact ⟨⟨⟨T, S, hST, hTS⟩, hTc, hSc⟩, rfl, hS⟩

/-- Helper (converse bridge, C2). The finite part of a fractional linear transformation is complex differentiable
at every finite point that is not its pole. -/
theorem lv15_differentiableAt_finiteMap_mobius {S : ExtPlane → ExtPlane} (hS : IsMobius S) {ζ : ℂ}
    (hζ : S ζ ≠ extInf) : DifferentiableAt ℂ (finiteMap S) ζ := by
  obtain ⟨a, b, c, d, h, rfl⟩ := hS
  have hden : c * ζ + d ≠ 0 := fun h0 => hζ (LiZhongQC.mobiusExt_coe_of_eq_zero h0)
  have hev : ∀ᶠ z in 𝓝 ζ, c * z + d ≠ 0 :=
    (by fun_prop : Continuous fun z : ℂ => c * z + d).continuousAt.eventually_ne hden
  have hd : DifferentiableAt ℂ (fun z : ℂ => (a * z + b) / (c * z + d)) ζ :=
    DifferentiableAt.div (by fun_prop) (by fun_prop) hden
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hev] with z hz
  show finiteValue (LiZhongQC.mobiusExt a b c d z) = (a * z + b) / (c * z + d)
  rw [LiZhongQC.mobiusExt_coe hz]
  rfl

/-- Helper (converse bridge, C2; piece P). Positive orientation (I.1.4) is invariant under fractional linear
transformations `T`. The positively oriented parametrization `γ` of `Fr G` becomes `T ∘ γ`, a parametrization of
`Fr T(G) = T(Fr G)`; the normalizing transformation `t` of `IsPositiveBoundaryParam` becomes `t ∘ T⁻¹`, with the same
logarithm `L`. -/
theorem lv15_isPositivelyOrdered_mobius {T : ExtPlane → ExtPlane} (hT : IsMobius T) {n : ℕ} {G : Set ExtPlane}
    {p : Fin n → ExtPlane} (hp : IsPositivelyOrdered G p) : IsPositivelyOrdered (T '' G) (T ∘ p) := by
  obtain ⟨e, rfl, he⟩ := lv15_mobius_homeomorph hT
  obtain ⟨γ, ⟨⟨hγc, hγp, hγi, hγr⟩, t, ht, U, htU, hUb, hU0, L, hLc, hL, hL1⟩, a, sv, hsv, hsvI, hγs⟩ := hp
  refine ⟨e ∘ γ, ⟨⟨e.continuous.comp hγc, fun x => ?_, e.injective.comp_injOn hγi, ?_⟩, t ∘ e.symm,
    lv15_isMobius_comp ht he, U, ?_, hUb, hU0, L, hLc, fun s => ?_, hL1⟩, a, sv, hsv, hsvI, fun i => ?_⟩
  · show e (γ (x + 1)) = e (γ x)
    rw [hγp x]
  · rw [range_comp, hγr]
    exact e.image_frontier G
  · rw [image_comp, lv15_symm_image_image, htU]
  · show t (e.symm (e (γ s))) = _
    rw [e.symm_apply_apply]
    exact hL s
  · show e (γ (sv i)) = e (p i)
    rw [hγs i]

/-- Helper (converse bridge, C2). Composing a homeomorphism `f : A → A′` with the inverse of a homeomorphism `e` of
`ℂ̄` gives a homeomorphism of `e(A)` onto `A′`. -/
theorem lv15_isHomeoOn_comp_symm (e : ExtPlane ≃ₜ ExtPlane) {f : ExtPlane → ExtPlane} {A A' : Set ExtPlane}
    (hf : IsHomeoOn f A A') : IsHomeoOn (f ∘ e.symm) (e '' A) A' := by
  obtain ⟨hc, hi, him, hinv⟩ := hf
  have hmaps : MapsTo e.symm (e '' A) A := by
    rintro _ ⟨x, hx, rfl⟩
    rwa [e.symm_apply_apply]
  have hi' : InjOn (f ∘ e.symm) (e '' A) := hi.comp e.symm.injective.injOn hmaps
  refine ⟨hc.comp e.symm.continuous.continuousOn hmaps, hi', ?_, ?_⟩
  · rw [image_comp, lv15_symm_image_image, him]
  · -- the inverse is `e ∘ f⁻¹`
    have heq : EqOn (e ∘ Function.invFunOn f A) (Function.invFunOn (f ∘ e.symm) (e '' A)) A' := by
      rw [← him]
      rintro _ ⟨x, hx, rfl⟩
      have h1 := hi'.leftInvOn_invFunOn (mem_image_of_mem e hx)
      simp only [Function.comp_apply, e.symm_apply_apply] at h1 ⊢
      rw [h1, hi.leftInvOn_invFunOn hx]
    exact (e.continuous.comp_continuousOn hinv).congr heq.symm

/-- Helper (converse bridge, C2). A conformal mapping `f` of `D`, composed with the inverse of a fractional linear
transformation `e`, is a conformal mapping of `e(D)`. The finite part is `finiteMap f ∘ finiteMap e⁻¹` away from the
pole of `e⁻¹`, so `lv15_isConformalMap_of_differentiableAt` applies. -/
theorem lv15_isConformalMap_comp_symm (e : ExtPlane ≃ₜ ExtPlane) (he : IsMobius ⇑e.symm)
    {f : ExtPlane → ExtPlane} {D : Set ExtPlane} (hf : IsConformalMap f D) :
    IsConformalMap (f ∘ e.symm) (e '' D) := by
  obtain ⟨hDd, hfc, hfi, hfd⟩ := hf
  have hmaps : MapsTo e.symm (e '' D) D := by
    rintro _ ⟨x, hx, rfl⟩
    rwa [e.symm_apply_apply]
  refine lv15_isConformalMap_of_differentiableAt ⟨e.isOpenMap _ hDd.1, hDd.2.image _ e.continuous.continuousOn⟩
    (hfc.comp e.symm.continuous.continuousOn hmaps) (hfi.comp e.symm.injective.injOn hmaps)
    (E := {ζ : ℂ | e.symm ζ = extInf})
    (Set.Subsingleton.finite fun ζ₁ h₁ ζ₂ h₂ => OnePoint.coe_injective (e.symm.injective (h₁.trans h₂.symm)))
    fun ζ hζ hfin hE => ?_
  have hSζ : e.symm ζ ≠ extInf := hE
  have hzc : ((finiteValue (e.symm ζ) : ℂ) : ExtPlane) = e.symm ζ := lv15_coe_finiteValue hSζ
  have hzD : ((finiteValue (e.symm ζ) : ℂ) : ExtPlane) ∈ D := by
    rw [hzc]
    exact hmaps hζ
  have hfz : f ((finiteValue (e.symm ζ) : ℂ) : ExtPlane) ≠ extInf := by
    rw [hzc]
    exact hfin
  -- `finiteMap f` is complex differentiable at the finite point `e⁻¹(ζ)`
  have hUo : IsOpen (((↑) : ℂ → ExtPlane) ⁻¹' (D ∩ f ⁻¹' {extInf}ᶜ)) :=
    (hfc.isOpen_inter_preimage hDd.1 isOpen_compl_singleton).preimage OnePoint.continuous_coe
  have hdf : DifferentiableAt ℂ (finiteMap f) (finiteValue (e.symm ζ)) :=
    lv12_differentiableAt_of_localRep hUo (fun u hu => (lv15_coe_finiteValue hu.2).symm) ⟨hzD, hfz⟩
      (hfd _ hzD)
  have hcomp : DifferentiableAt ℂ (finiteMap f ∘ finiteMap e.symm) ζ :=
    hdf.comp ζ (lv15_differentiableAt_finiteMap_mobius he hSζ)
  refine hcomp.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ ζ' : ℂ in 𝓝 ζ, e.symm ζ' ≠ extInf :=
    (e.symm.continuous.comp OnePoint.continuous_coe).continuousAt.eventually (isOpen_compl_singleton.mem_nhds hSζ)
  filter_upwards [hev] with ζ' h'
  show finiteValue (f (e.symm ζ')) = finiteValue (f ((finiteValue (e.symm ζ') : ℂ) : ExtPlane))
  rw [lv15_coe_finiteValue h']

/-- Helper (converse bridge, C2). A canonical mapping `f` of `(D, v)` gives the canonical mapping `f ∘ T⁻¹` of
`(T(D), T ∘ v)` for a fractional linear transformation `T`. -/
theorem lv15_isCanonicalMap_mobius {T : ExtPlane → ExtPlane} (hT : IsMobius T) {D : Set ExtPlane}
    {v : Fin 4 → ExtPlane} {a b : ℝ} {f : ExtPlane → ExtPlane} (hf : IsCanonicalMap D v a b f) :
    ∃ g : ExtPlane → ExtPlane, IsCanonicalMap (T '' D) (T ∘ v) a b g := by
  obtain ⟨e, rfl, he⟩ := lv15_mobius_homeomorph hT
  obtain ⟨ha, hb, hconf, hfim, hhom, hv⟩ := hf
  refine ⟨f ∘ e.symm, ha, hb, lv15_isConformalMap_comp_symm e he hconf, ?_, ?_, fun i => ?_⟩
  · rw [image_comp, lv15_symm_image_image, hfim]
  · rw [← e.image_closure]
    exact lv15_isHomeoOn_comp_symm e hhom
  · show f (e.symm (e (v i))) = _
    rw [e.symm_apply_apply]
    exact hv i

/-- Helper (converse bridge, C2; piece U). The module of quadrilateral data (I.2.4) is invariant under fractional
linear transformations `T`. A canonical mapping `f` of `(D, v)` gives the canonical mapping `f ∘ T⁻¹` of
`(T(D), T ∘ v)`. It is conformal by `lv15_isConformalMap_of_differentiableAt`, with the exceptional point `T(∞)`; the
converse uses `T⁻¹`. -/
theorem lv15_quadModule_mobius {T : ExtPlane → ExtPlane} (hT : IsMobius T) (D : Set ExtPlane)
    (v : Fin 4 → ExtPlane) : quadModule (T '' D) (T ∘ v) = quadModule D v := by
  obtain ⟨e, rfl, he⟩ := lv15_mobius_homeomorph hT
  unfold quadModule
  congr 1
  ext m
  constructor
  · rintro ⟨a, b, f, hf, rfl⟩
    obtain ⟨g, hg⟩ := lv15_isCanonicalMap_mobius he hf
    have hv : ⇑e.symm ∘ (⇑e ∘ v) = v := by
      funext i
      exact e.symm_apply_apply (v i)
    rw [lv15_symm_image_image, hv] at hg
    exact ⟨a, b, g, hg, rfl⟩
  · rintro ⟨a, b, f, hf, rfl⟩
    obtain ⟨g, hg⟩ := lv15_isCanonicalMap_mobius hT hf
    exact ⟨a, b, g, hg, rfl⟩

/-- Helper (converse bridge, C2; piece Q). The image of a quadrilateral under a fractional linear transformation is a
quadrilateral, with the image vertices and the same module. -/
theorem lv15_quadrilateral_mobius {T : ExtPlane → ExtPlane} (hT : IsMobius T) (Q : Quadrilateral) :
    ∃ Q' : Quadrilateral, Q'.dom = T '' Q.dom ∧ Q'.vert = T ∘ Q.vert ∧ Q'.module = Q.module := by
  obtain ⟨e, rfl, -⟩ := lv15_mobius_homeomorph hT
  obtain ⟨hJ, -, hfr⟩ := lv11_jordanDomain_image Q.isJordanDomain e.continuous.continuousOn e.injective.injOn
  refine ⟨⟨e '' Q.dom, e ∘ Q.vert, hJ, fun i => ?_, lv15_isPositivelyOrdered_mobius hT Q.positive⟩, rfl, rfl, ?_⟩
  · rw [hfr]
    exact mem_image_of_mem e (Q.vert_mem i)
  · exact lv15_quadModule_mobius hT Q.dom Q.vert

/-- Helper (converse bridge, C2; piece K). Li Zhong `K`-quasiconformality of the finite part passes to Möbius
conjugates `T ∘ w ∘ S`. Off the finite set of `ζ` with `S(ζ) = ∞` or `w(S(ζ)) = ∞`, the finite part of
`T ∘ w ∘ S` is `mobiusFn ∘ finiteMap w ∘ mobiusFn`. That is `K`-q.c. by `LiZhongQC.thm7_1_comp` and
`LiZhongQC.isKQC_one_of_conformal` (`1 · K · 1`). The finite set is removable (`LiZhongQC.s16p_isKQC_of_finite`). -/
theorem lv15_isKQC_mobius_conj {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hG : IsOpen G)
    (hc : ContinuousOn w G) (hi : InjOn w G)
    (hK : LiZhongQC.IsKQC (finiteMap w) {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} K)
    {S T : ExtPlane → ExtPlane} (hS : IsMobius S) (hT : IsMobius T) :
    LiZhongQC.IsKQC (finiteMap (T ∘ w ∘ S))
      {ζ : ℂ | S (ζ : ExtPlane) ∈ G ∧ T (w (S (ζ : ExtPlane))) ≠ extInf} K := by
  -- the Möbius maps are continuous and injective
  have hSc : Continuous S := by
    obtain ⟨a, b, c, d, h, rfl⟩ := hS
    exact LiZhongQC.continuous_mobiusExt h
  have hTc : Continuous T := by
    obtain ⟨a, b, c, d, h, rfl⟩ := hT
    exact LiZhongQC.continuous_mobiusExt h
  have hSi : Function.Injective S := by
    obtain ⟨S', -, hS', -⟩ := lv15_isMobius_inverse hS
    exact Function.LeftInverse.injective hS'
  have hTi : Function.Injective T := by
    obtain ⟨T', -, hT', -⟩ := lv15_isMobius_inverse hT
    exact Function.LeftInverse.injective hT'
  set D : Set ℂ := {ζ : ℂ | S (ζ : ExtPlane) ∈ G ∧ T (w (S (ζ : ExtPlane))) ≠ extInf} with hD
  set L : Set ℂ := {ζ : ℂ | S (ζ : ExtPlane) = extInf} ∪
    {ζ : ℂ | S (ζ : ExtPlane) ∈ G ∧ w (S (ζ : ExtPlane)) = extInf} with hL
  have hLf : L.Finite := by
    refine (Set.Subsingleton.finite fun ζ₁ h₁ ζ₂ h₂ => ?_).union (Set.Subsingleton.finite fun ζ₁ h₁ ζ₂ h₂ => ?_)
    · exact OnePoint.coe_injective (hSi (h₁.trans h₂.symm))
    · exact OnePoint.coe_injective (hSi (hi h₁.1 h₂.1 (h₁.2.trans h₂.2.symm)))
  have hDo : IsOpen D :=
    ((hc.isOpen_inter_preimage hG ((isOpen_compl_singleton : IsOpen ({extInf}ᶜ : Set ExtPlane)).preimage
      hTc)).preimage hSc).preimage
      OnePoint.continuous_coe
  have hDL : IsOpen (D \ L) := hDo.sdiff hLf.isClosed
  -- the finite values along `D \ L`
  have hfin : ∀ ζ ∈ D \ L, S (ζ : ExtPlane) ≠ extInf ∧ w (S (ζ : ExtPlane)) ≠ extInf := fun ζ hζ =>
    ⟨fun h => hζ.2 (Or.inl h), fun h => hζ.2 (Or.inr ⟨hζ.1.1, h⟩)⟩
  -- the three pieces
  have h1 : LiZhongQC.IsKQC (finiteMap S) (D \ L) 1 := by
    refine LiZhongQC.isKQC_one_of_conformal hDL ⟨fun ζ hζ =>
      (lv15_differentiableAt_finiteMap_mobius hS (hfin ζ hζ).1).differentiableWithinAt, fun ζ₁ h₁ ζ₂ h₂ h => ?_,
        rfl⟩
    have h' : S (ζ₁ : ExtPlane) = S (ζ₂ : ExtPlane) := by
      rw [← lv15_coe_finiteValue (hfin ζ₁ h₁).1, ← lv15_coe_finiteValue (hfin ζ₂ h₂).1]
      exact congrArg ((↑) : ℂ → ExtPlane) h
    exact OnePoint.coe_injective (hSi h')
  have hD₃ : IsOpen {u : ℂ | T (u : ExtPlane) ≠ extInf} :=
    ((isOpen_compl_singleton : IsOpen ({extInf}ᶜ : Set ExtPlane)).preimage hTc).preimage OnePoint.continuous_coe
  have h3 : LiZhongQC.IsKQC (finiteMap T) {u : ℂ | T (u : ExtPlane) ≠ extInf} 1 := by
    refine LiZhongQC.isKQC_one_of_conformal hD₃ ⟨fun u hu =>
      (lv15_differentiableAt_finiteMap_mobius hT hu).differentiableWithinAt, fun u₁ h₁ u₂ h₂ h => ?_, rfl⟩
    have h' : T (u₁ : ExtPlane) = T (u₂ : ExtPlane) := by
      rw [← lv15_coe_finiteValue h₁, ← lv15_coe_finiteValue h₂]
      exact congrArg ((↑) : ℂ → ExtPlane) h
    exact OnePoint.coe_injective (hTi h')
  have hsub1 : finiteMap S '' (D \ L) ⊆ {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} := by
    rintro _ ⟨ζ, hζ, rfl⟩
    have hc1 : ((finiteMap S ζ : ℂ) : ExtPlane) = S ζ := lv15_coe_finiteValue (hfin ζ hζ).1
    refine ⟨?_, ?_⟩
    · rw [hc1]
      exact hζ.1.1
    · rw [hc1]
      exact (hfin ζ hζ).2
  have h12 := LiZhongQC.thm7_1_comp h1 hK hsub1
  have hsub2 : (finiteMap w ∘ finiteMap S) '' (D \ L) ⊆ {u : ℂ | T (u : ExtPlane) ≠ extInf} := by
    rintro _ ⟨ζ, hζ, rfl⟩
    have hc1 : ((finiteMap S ζ : ℂ) : ExtPlane) = S ζ := lv15_coe_finiteValue (hfin ζ hζ).1
    show T ((finiteValue (w ((finiteMap S ζ : ℂ) : ExtPlane)) : ℂ) : ExtPlane) ≠ extInf
    rw [hc1, lv15_coe_finiteValue (hfin ζ hζ).2]
    exact hζ.1.2
  have h123 := LiZhongQC.thm7_1_comp h12 h3 hsub2
  rw [one_mul, mul_one] at h123
  -- the finite part of `T ∘ w ∘ S` is the composite on `D \ L`
  have hcongr : LiZhongQC.IsKQC (finiteMap (T ∘ w ∘ S)) (D \ L) K := by
    refine LiZhongQC.ad_isKQC_congr h123 fun ζ hζ => ?_
    have hc1 : ((finiteMap S ζ : ℂ) : ExtPlane) = S ζ := lv15_coe_finiteValue (hfin ζ hζ).1
    show finiteValue (T (w (S ζ))) =
      finiteValue (T ((finiteValue (w ((finiteMap S ζ : ℂ) : ExtPlane)) : ℂ) : ExtPlane))
    rw [hc1, lv15_coe_finiteValue (hfin ζ hζ).2]
  -- continuity and injectivity on `D`, then the finite set `L` is removable
  have hcont : ContinuousOn (finiteMap (T ∘ w ∘ S)) D := fun ζ hζ => by
    have hwc : ContinuousAt w (S ζ) := hc.continuousAt (hG.mem_nhds hζ.1)
    have h1 : ContinuousAt (fun ζ' : ℂ => S ζ') ζ := (hSc.comp OnePoint.continuous_coe).continuousAt
    have h2 : ContinuousAt (fun ζ' : ℂ => w (S ζ')) ζ := ContinuousAt.comp (g := w) hwc h1
    have h0 : ContinuousAt (fun ζ' : ℂ => T (w (S ζ'))) ζ := ContinuousAt.comp (g := T) hTc.continuousAt h2
    have hfv : ContinuousAt finiteValue (T (w (S ζ))) := by
      rw [← lv15_coe_finiteValue hζ.2]
      exact lv15_finiteValue_continuousAt _
    exact (ContinuousAt.comp (g := finiteValue) (f := fun ζ' : ℂ => T (w (S ζ'))) hfv h0).continuousWithinAt
  have hinj : InjOn (finiteMap (T ∘ w ∘ S)) D := by
    intro ζ₁ h₁ ζ₂ h₂ h
    have h' : T (w (S ζ₁)) = T (w (S ζ₂)) := by
      rw [← lv15_coe_finiteValue h₁.2, ← lv15_coe_finiteValue h₂.2]
      exact congrArg ((↑) : ℂ → ExtPlane) h
    exact OnePoint.coe_injective (hSi (hi h₁.1 h₂.1 (hTi h')))
  exact LiZhongQC.s16p_isKQC_of_finite hDo hK.2.1 hcont hinj hLf hcongr

/-- Helper (converse bridge, C2; piece N, normalization at `∞` and at `w⁻¹(∞)`). Let `D` be positively ordered by
some points (for instance a quadrilateral or a Jordan domain with a positive triple), with `D̄ ⊂ G`. Then there are
fractional linear transformations `t`, `S = t⁻¹` and `T` such that:
- `t(D̄)` is bounded, using the normalizing `t` of the positive parametrization;
- `T ∘ w ∘ S` is finite on `t(D̄)`, where `T = 1/(z − b)` with `b = w(p)` for a point `p ∈ G \ D̄` at which `w` is
  finite. -/
theorem lv15_normalize {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsDomainExt G) (hi : InjOn w G)
    {D : Set ExtPlane} (hDG : closure D ⊆ G) {n : ℕ} {p : Fin n → ExtPlane} (hp : IsPositivelyOrdered D p) :
    ∃ t S T : ExtPlane → ExtPlane, IsMobius t ∧ IsMobius S ∧ IsMobius T ∧ (∀ q, S (t q) = q) ∧
      (∀ q, t (S q) = q) ∧ extInf ∉ closure (t '' D) ∧
      ∀ z ∈ closure (t '' D), S z ∈ G ∧ T (w (S z)) ≠ extInf := by
  obtain ⟨_, ⟨-, t, ht, U, htU, hUb, -, -⟩, -⟩ := hp
  obtain ⟨e, rfl, he⟩ := lv15_mobius_homeomorph ht
  -- `t(D̄)` is bounded
  have hinf : extInf ∉ closure (e '' D) := by
    rw [htU, LiZhongQC.closure_toExt_of_isBounded hUb]
    rintro ⟨z, -, hz⟩
    exact OnePoint.coe_ne_infty z hz
  -- `G \ D̄` is a non-empty open set
  have hne : (G \ closure D).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at h
    have hGeq : closure D = G := subset_antisymm hDG h
    have hGc : IsClosed G := by
      rw [← hGeq]
      exact isClosed_closure
    have hGu : G = univ := IsClopen.eq_univ ⟨hGc, hG.1⟩ hG.2.nonempty
    apply hinf
    rw [← e.image_closure, hGeq, hGu, image_univ_of_surjective e.surjective]
    exact mem_univ _
  have hVo : IsOpen (G \ closure D) := hG.1.sdiff isClosed_closure
  -- two finite points of `G \ D̄`, so a point `q` of `G \ D̄` with `w(q)` finite
  obtain ⟨z, hz⟩ := OnePoint.denseRange_coe.exists_mem_open hVo hne
  have hzo : IsOpen (((↑) : ℂ → ExtPlane) ⁻¹' (G \ closure D)) := hVo.preimage OnePoint.continuous_coe
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hzo z hz
  have hz' : ((z + ε / 2 : ℂ) : ExtPlane) ∈ G \ closure D := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    rw [show (ε / 2 : ℂ) = ((ε / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith)
  obtain ⟨q, hq, hqfin⟩ : ∃ q ∈ G \ closure D, w q ≠ extInf := by
    by_cases h : w z = extInf
    · refine ⟨_, hz', fun h' => ?_⟩
      have h2 := OnePoint.coe_injective (hi hz.1 hz'.1 (h.trans h'.symm))
      have : (ε / 2 : ℂ) = 0 := by linear_combination -h2
      have : ε = 0 := by exact_mod_cast (by linear_combination 2 * this : (ε : ℂ) = 0)
      linarith
    · exact ⟨_, hz, h⟩
  -- `T = 1/(ζ − b)` with `b = w(q)` has its pole only at `b`
  set b := finiteValue (w q) with hb
  have hT : IsMobius (LiZhongQC.mobiusExt 0 1 1 (-b)) := ⟨0, 1, 1, -b, by norm_num, rfl⟩
  have hTb : ∀ x : ExtPlane, LiZhongQC.mobiusExt 0 1 1 (-b) x = extInf → x = w q := by
    intro x hx
    induction x using OnePoint.rec with
    | infty =>
      simp [LiZhongQC.mobiusExt] at hx
    | coe u =>
      by_cases hu : 1 * u + -b = 0
      · rw [← lv15_coe_finiteValue hqfin, ← hb]
        congr 1
        linear_combination hu
      · rw [LiZhongQC.mobiusExt_coe hu] at hx
        exact absurd hx (OnePoint.coe_ne_infty _)
  refine ⟨e, e.symm, _, ht, he, hT, e.symm_apply_apply, e.apply_symm_apply, hinf, fun x hx => ?_⟩
  rw [← e.image_closure] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [e.symm_apply_apply]
  refine ⟨hDG hy, fun h => hq.2 ?_⟩
  rw [hi hq.1 (hDG hy) (hTb _ h).symm]
  exact hy

/-- Helper (converse bridge, stage 3). The points of a positively ordered tuple lie on the boundary. -/
theorem lv15_mem_frontier_of_isPositivelyOrdered {D : Set ExtPlane} {n : ℕ} {v : Fin n → ExtPlane}
    (hv : IsPositivelyOrdered D v) (i : Fin n) : v i ∈ frontier D := by
  obtain ⟨γ, ⟨⟨-, -, -, hγr⟩, -⟩, a, s, -, -, hγs⟩ := hv
  rw [← hγs i, ← hγr]
  exact mem_range_self _

/-- Helper (converse bridge, stage 3). The first three points of a positively ordered quadruple are positively
ordered. -/
theorem lv15_isPositivelyOrdered_restrict {D : Set ExtPlane} {v : Fin 4 → ExtPlane}
    (hv : IsPositivelyOrdered D v) : IsPositivelyOrdered D (fun i : Fin 3 => v (Fin.castSucc i)) := by
  obtain ⟨γ, hγ, a, s, hs, hsI, hγs⟩ := hv
  exact ⟨γ, hγ, a, s ∘ Fin.castSucc, hs.comp Fin.strictMono_castSucc, fun i => hsI _, fun i => hγs _⟩

/-- Helper (converse bridge, stage 3). A positively ordered triple is completed to a positively ordered quadruple by
the boundary point at the parameter halfway between the third point and the end of the turn. -/
theorem lv15_exists_fourth_vertex {D : Set ExtPlane} {p : Fin 3 → ExtPlane} (hp : IsPositivelyOrdered D p) :
    ∃ v : Fin 4 → ExtPlane, IsPositivelyOrdered D v ∧ ∀ i : Fin 3, v (Fin.castSucc i) = p i := by
  obtain ⟨γ, hγ, a, s, hs, hsI, hγs⟩ := hp
  have h01 : s 0 < s 1 := hs (by decide)
  have h12 : s 1 < s 2 := hs (by decide)
  have h2 := hsI 2
  refine ⟨![p 0, p 1, p 2, γ ((s 2 + (a + 1)) / 2)],
    ⟨γ, hγ, a, ![s 0, s 1, s 2, (s 2 + (a + 1)) / 2], ?_, fun i => ?_, fun i => ?_⟩, fun i => ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    · exact h01
    · exact h12
    · show s 2 < (s 2 + (a + 1)) / 2
      linarith [h2.2]
  · fin_cases i
    · exact hsI 0
    · exact hsI 1
    · exact hsI 2
    · show (s 2 + (a + 1)) / 2 ∈ Ico a (a + 1)
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · fin_cases i
    · exact hγs 0
    · exact hγs 1
    · exact hγs 2
    · rfl
  · fin_cases i <;> rfl

/-- Helper (converse bridge, stage 3; the finite case, shared by C3 and C4). Let `w` be `K`-quasiconformal in Li
Zhong's sense (Definition 7.1) on its finite core in `G`, and let `Q` be an LV quadrilateral with bounded closure
contained in the part of `G` where `w` is finite. Then the image data `(w(Q), w ∘ z)` is positively ordered, and
`M(w(Q)) ≤ K M(Q)`. Proof: `Q` is an LZ quadrilateral (`lv13_isTopQuad_of_quadrilateral`), its image quadrilateral
comes from `IsKQC`, the positivity is `lv13_isPositivelyOrdered_of_isTopQuad`, and the modules are identified by
`lv12_quadModule_toExt`. -/
theorem lv15_finite_quad {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hK : LiZhongQC.IsKQC (finiteMap w) {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} K) (Q : Quadrilateral)
    (hinf : extInf ∉ closure Q.dom) (hQ : ∀ z ∈ closure Q.dom, z ∈ G ∧ w z ≠ extInf) :
    IsPositivelyOrdered (w '' Q.dom) (w ∘ Q.vert) ∧ quadModule (w '' Q.dom) (w ∘ Q.vert) ≤ K * Q.module := by
  obtain ⟨-, -, ⟨hfc, -, -, -⟩, hQK⟩ := hK
  obtain ⟨D₀, hQD, -, hTQ⟩ := lv13_isTopQuad_of_quadrilateral Q hinf
  -- `Q̄` lies in the finite core
  have hsub : closure (toExt D₀) ⊆ toExt {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} := by
    intro q hq
    rw [← hQD] at hq
    obtain ⟨hqG, hqw⟩ := hQ q hq
    have hq' : q ≠ extInf := fun h => hinf (h ▸ hq)
    obtain ⟨u, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hq'
    exact ⟨u, ⟨hqG, hqw⟩, rfl⟩
  have hD₀core : ∀ u ∈ D₀, (u : ExtPlane) ∈ G ∧ w u ≠ extInf := fun u hu => by
    obtain ⟨y, hy, hyu⟩ := hsub (subset_closure ⟨u, hu, rfl⟩)
    rw [← OnePoint.coe_injective hyu]
    exact hy
  obtain ⟨Q', ⟨hQ'd, hQ'v⟩, hmod⟩ := hQK ⟨D₀, Q.vert, hTQ⟩ hsub
  -- the image data is that of `Q'`
  have himg : w '' Q.dom = toExt Q'.dom := by
    rw [hQD, hQ'd]
    ext q
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨finiteMap w u, ⟨u, hu, rfl⟩, lv15_coe_finiteValue (hD₀core u hu).2⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, ⟨u, hu, rfl⟩, (lv15_coe_finiteValue (hD₀core u hu).2).symm⟩
  have hvert : w ∘ Q.vert = Q'.vert := by
    funext i
    rw [hQ'v i]
    have hvi : Q.vert i ∈ closure Q.dom := frontier_subset_closure (Q.vert_mem i)
    have hne : Q.vert i ≠ extInf := fun h => hinf (h ▸ hvi)
    obtain ⟨u, hu⟩ := OnePoint.ne_infty_iff_exists.1 hne
    have hvi' : (u : ExtPlane) ∈ closure Q.dom := by
      rw [hu]
      exact hvi
    show w (Q.vert i) = OnePoint.map (finiteMap w) (Q.vert i)
    rw [← hu, ← lv15_coe_finiteValue (hQ _ hvi').2]
    rfl
  -- positivity
  have hb' : Bornology.IsBounded Q'.dom := by
    rw [hQ'd]
    apply LiZhongQC.isBounded_of_extInf_notMem_closure_toExt
    intro hmem
    obtain ⟨u, -, hu⟩ := LiZhongQC.closure_toExt_image_subset hfc hsub subset_rfl hmem
    exact OnePoint.coe_ne_infty u hu
  have hpos := lv13_isPositivelyOrdered_of_isTopQuad Q'.isTopQuad hb'
  rw [← himg, ← hvert] at hpos
  -- the modules
  have hJ' := Q'.isTopQuad.1
  have hm' : quadModule (w '' Q.dom) (w ∘ Q.vert) = Q'.modulus := by
    rw [himg, hvert]
    exact lv12_quadModule_toExt hJ'.1 hJ'.2.1 Q'.vert
  have hm : Q.module = LiZhongQC.TopQuad.modulus ⟨D₀, Q.vert, hTQ⟩ := by
    show quadModule Q.dom Q.vert = LiZhongQC.quadModulusOf D₀ Q.vert
    rw [hQD]
    exact lv12_quadModule_toExt hTQ.1.1 hTQ.1.2.1 Q.vert
  refine ⟨hpos, ?_⟩
  rw [hm', hm]
  exact hmod

/-- Helper (converse bridge, stage 3; C3). Let `w` be continuous and one-to-one on the domain `G`, with finite part
`K`-quasiconformal in Li Zhong's sense on its finite core. Then `w` preserves the orientation of the boundary of every
Jordan domain `D` with `D̄ ⊂ G`. Proof:
- normalize `D` and a positive triple (`lv15_normalize`);
- complete the triple by a fourth boundary point to an LV quadrilateral;
- apply `lv15_finite_quad` to `T ∘ w ∘ S` (`lv15_isKQC_mobius_conj`);
- carry the image triple back by `T⁻¹` (`lv15_isPositivelyOrdered_mobius`). -/
theorem lv15_preservesBoundaryOrientation_of_isKQC {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hG : IsDomainExt G) (hc : ContinuousOn w G) (hi : InjOn w G)
    (hK : LiZhongQC.IsKQC (finiteMap w) {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} K) {D : Set ExtPlane}
    (hD : IsJordanDomainExt D) (hDG : closure D ⊆ G) : PreservesBoundaryOrientation w D := by
  intro p hp
  obtain ⟨t, S, T, ht, hS, hT, hSt, -, hinf, hfin⟩ := lv15_normalize hG hi hDG hp
  have htc : Continuous t := by
    obtain ⟨a, b, c, d, h, rfl⟩ := ht
    exact LiZhongQC.continuous_mobiusExt h
  have hti : Function.Injective t := Function.LeftInverse.injective hSt
  -- the normalized domain, with the triple completed to an LV quadrilateral
  have hJ : IsJordanDomainExt (t '' D) :=
    (lv11_jordanDomain_image hD htc.continuousOn hti.injOn).1
  obtain ⟨v, hv, hvp⟩ := lv15_exists_fourth_vertex (lv15_isPositivelyOrdered_mobius ht hp)
  have hK' := lv15_isKQC_mobius_conj hG.1 hc hi hK hS hT
  have hpos : IsPositivelyOrdered ((T ∘ w ∘ S) '' (t '' D)) ((T ∘ w ∘ S) ∘ v) :=
    (lv15_finite_quad (w := T ∘ w ∘ S) (G := S ⁻¹' G) hK'
      ⟨t '' D, v, hJ, lv15_mem_frontier_of_isPositivelyOrdered hv, hv⟩ hinf hfin).1
  -- back through `T⁻¹`
  obtain ⟨T', hT', hT'T, -⟩ := lv15_isMobius_inverse hT
  have h4 := lv15_isPositivelyOrdered_mobius hT' (lv15_isPositivelyOrdered_restrict hpos)
  have hdom : T' '' ((T ∘ w ∘ S) '' (t '' D)) = w '' D := by
    rw [image_image, image_image]
    simp only [Function.comp_apply, hSt, hT'T]
  have hpt : (T' ∘ fun i : Fin 3 => ((T ∘ w ∘ S) ∘ v) (Fin.castSucc i)) = w ∘ p := by
    funext i
    simp only [Function.comp_apply, hvp i, hSt, hT'T]
  rw [hdom, hpt] at h4
  exact h4

/-- Helper (converse bridge, stage 3; C4). Under the same hypotheses, `M(w(Q)) ≤ K M(Q)` for every LV quadrilateral
`Q` with `Q̄ ⊂ G`. Proof: normalize (`lv15_normalize`, `lv15_quadrilateral_mobius`), apply `lv15_finite_quad` to
`T ∘ w ∘ S`, and use the Möbius invariance of the module (`lv15_quadModule_mobius`). -/
theorem lv15_quadModule_image_le_of_isKQC {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hG : IsDomainExt G) (hc : ContinuousOn w G) (hi : InjOn w G)
    (hK : LiZhongQC.IsKQC (finiteMap w) {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} K) (Q : Quadrilateral)
    (hQ : closure Q.dom ⊆ G) : quadModule (w '' Q.dom) (w ∘ Q.vert) ≤ K * Q.module := by
  obtain ⟨t, S, T, ht, hS, hT, hSt, -, hinf, hfin⟩ := lv15_normalize hG hi hQ Q.positive
  obtain ⟨Q₁, hQ₁d, hQ₁v, hQ₁m⟩ := lv15_quadrilateral_mobius ht Q
  have hK' := lv15_isKQC_mobius_conj hG.1 hc hi hK hS hT
  have hfq := (lv15_finite_quad (w := T ∘ w ∘ S) (G := S ⁻¹' G) hK' Q₁ (by rwa [hQ₁d])
    (by rw [hQ₁d]; exact hfin)).2
  -- `T ∘ w ∘ S` on `t(Q)` is `T ∘ w` on `Q`
  have hdom : (T ∘ w ∘ S) '' Q₁.dom = T '' (w '' Q.dom) := by
    rw [hQ₁d, image_image, image_image]
    simp only [Function.comp_apply, hSt]
  have hvert : (T ∘ w ∘ S) ∘ Q₁.vert = T ∘ (w ∘ Q.vert) := by
    rw [hQ₁v]
    funext i
    simp only [Function.comp_apply, hSt]
  rw [hdom, hvert, hQ₁m, lv15_quadModule_mobius hT] at hfq
  exact hfq

/-- Helper (converse bridge, stage 3; the converse of `lv13_isKQC_of_isKQuasiconformal`). Let `w` be a continuous
one-to-one map of a domain `G ⊆ ℂ̄` whose finite part is `K`-quasiconformal in Li Zhong's sense (Definition 7.1) on
the finite core `{z ∈ ℂ : z ∈ G, w(z) ≠ ∞}`. Then `w` is `K`-quasiconformal in LV's sense (I.3.2):
- it is a homeomorphism (`lemma1_1_1`);
- it is sense-preserving (`lv15_preservesBoundaryOrientation_of_isKQC`);
- its maximal dilatation is at most `K` (`lv15_quadModule_image_le_of_isKQC`). -/
theorem lv15_isKQuasiconformal_of_isKQC {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hG : IsDomainExt G) (hc : ContinuousOn w G) (hi : InjOn w G)
    (hK : LiZhongQC.IsKQC (finiteMap w) {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} K) :
    IsKQuasiconformal w G K := by
  refine ⟨hG, ⟨lemma1_1_1 hG.1 hc hi, fun D hD hDG =>
    lv15_preservesBoundaryOrientation_of_isKQC hG hc hi hK hD hDG⟩, ?_⟩
  unfold maxDilatationK
  refine iSup₂_le fun Q hQ => ENNReal.ofReal_le_ofReal ?_
  have hle := lv15_quadModule_image_le_of_isKQC hG hc hi hK Q hQ
  have hK0 : 0 ≤ K := zero_le_one.trans hK.2.1
  have hM0 : 0 ≤ Q.module := by
    show 0 ≤ sSup {m : ℝ | ∃ (a b : ℝ) (f : ExtPlane → ExtPlane), IsCanonicalMap Q.dom Q.vert a b f ∧ m = a / b}
    refine Real.sSup_nonneg ?_
    rintro m ⟨a, b, f, hf, rfl⟩
    exact (div_pos hf.1 hf.2.1).le
  exact div_le_of_le_mul₀ hM0 hK0 hle

/-- **Unlabelled** (Ch. I §3.1–3.2, P1:381, 391). A conformal mapping is `1`-quasiconformal. -/
theorem conformal_isKQuasiconformal_one {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsConformalMap w G) :
    IsKQuasiconformal w G 1 := by
  obtain ⟨hG, hc, hi, hd⟩ := hw
  have hUo : IsOpen {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} :=
    (hc.isOpen_inter_preimage hG.1 (isOpen_compl_singleton : IsOpen ({extInf}ᶜ : Set ExtPlane))).preimage
      OnePoint.continuous_coe
  -- the finite part is holomorphic and one-to-one on the finite core, hence `1`-q.c. there
  refine lv15_isKQuasiconformal_of_isKQC hG hc hi (LiZhongQC.isKQC_one_of_conformal hUo
    ⟨fun u hu => ?_, fun u₁ h₁ u₂ h₂ h => ?_, rfl⟩)
  · exact (lv12_differentiableAt_of_localRep (f := finiteMap w) hUo
      (fun v hv => (lv15_coe_finiteValue hv.2).symm) hu (hd _ hu.1)).differentiableWithinAt
  · have h' : w (u₁ : ExtPlane) = w u₂ := by
      rw [← lv15_coe_finiteValue h₁.2, ← lv15_coe_finiteValue h₂.2]
      exact congrArg ((↑) : ℂ → ExtPlane) h
    exact OnePoint.coe_injective (hi h₁.1 h₂.1 h')

/-- **Unlabelled** (Ch. I §3.2, P1:397). The inverse of a `K`-quasiconformal mapping is `K`-quasiconformal. -/
theorem kqc_inv {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w G K) :
    IsKQuasiconformal (Function.invFunOn w G) (w '' G) K := by
  have hk := lv13_isKQC_of_isKQuasiconformal hw
  obtain ⟨hG, ⟨⟨hc, hi, -, hinv⟩, -⟩, -⟩ := hw
  have hG' : IsDomainExt (w '' G) := ⟨invariance_of_open_sets hG.1 hc hi, hG.2.image w hc⟩
  refine lv15_isKQuasiconformal_of_isKQC hG' hinv (Function.invFunOn_injOn_image w G) ?_
  -- the finite core of `w⁻¹` is the image of the finite core of `w`
  have hcore : {ζ : ℂ | (ζ : ExtPlane) ∈ w '' G ∧ Function.invFunOn w G ζ ≠ extInf} =
      finiteMap w '' {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} := by
    ext ζ
    constructor
    · rintro ⟨⟨x, hx, hxζ⟩, hfin⟩
      have hx' : Function.invFunOn w G ζ = x := by
        rw [← hxζ]
        exact hi.leftInvOn_invFunOn hx
      rw [hx'] at hfin
      obtain ⟨u, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hfin
      refine ⟨u, ⟨hx, ?_⟩, ?_⟩
      · rw [hxζ]
        exact OnePoint.coe_ne_infty ζ
      · show finiteValue (w u) = ζ
        rw [hxζ]
        rfl
    · rintro ⟨u, ⟨huG, hufin⟩, rfl⟩
      have hwu : ((finiteMap w u : ℂ) : ExtPlane) = w u := lv15_coe_finiteValue hufin
      refine ⟨⟨u, huG, hwu.symm⟩, ?_⟩
      rw [hwu, hi.leftInvOn_invFunOn huG]
      exact OnePoint.coe_ne_infty u
  rw [hcore]
  -- there the finite part of `w⁻¹` is the inverse of the finite part of `w` (Li Zhong's Theorem 7.2)
  refine LiZhongQC.ad_isKQC_congr (LiZhongQC.thm7_2_inv hk) ?_
  rintro _ ⟨u, ⟨huG, hufin⟩, rfl⟩
  have hwu : ((finiteMap w u : ℂ) : ExtPlane) = w u := lv15_coe_finiteValue hufin
  rw [hk.2.2.1.2.1.leftInvOn_invFunOn ⟨huG, hufin⟩]
  show finiteValue (Function.invFunOn w G ((finiteMap w u : ℂ) : ExtPlane)) = u
  rw [hwu, hi.leftInvOn_invFunOn huG]
  rfl

/-- **Unlabelled** (Ch. I §3.2, P1:397). The composition of a `K₁`-quasiconformal mapping `w₁ : G → G′` and a
`K₂`-quasiconformal mapping `w₂` of `G′` is `K₁K₂`-quasiconformal. -/
theorem kqc_comp {w₁ w₂ : ExtPlane → ExtPlane} {G : Set ExtPlane} {K₁ K₂ : ℝ}
    (h₁ : IsKQuasiconformal w₁ G K₁) (h₂ : IsKQuasiconformal w₂ (w₁ '' G) K₂) :
    IsKQuasiconformal (w₂ ∘ w₁) G (K₁ * K₂) := by
  have hk₁ := lv13_isKQC_of_isKQuasiconformal h₁
  have hk₂ := lv13_isKQC_of_isKQuasiconformal h₂
  obtain ⟨hG, ⟨⟨hc₁, hi₁, -, -⟩, -⟩, -⟩ := h₁
  obtain ⟨-, ⟨⟨hc₂, hi₂, -, -⟩, -⟩, -⟩ := h₂
  have hmaps : MapsTo w₁ G (w₁ '' G) := mapsTo_image w₁ G
  have hc : ContinuousOn (w₂ ∘ w₁) G := hc₂.comp hc₁ hmaps
  have hi : InjOn (w₂ ∘ w₁) G := hi₂.comp hi₁ hmaps
  refine lv15_isKQuasiconformal_of_isKQC hG hc hi ?_
  set D : Set ℂ := {z : ℂ | (z : ExtPlane) ∈ G ∧ (w₂ ∘ w₁) z ≠ extInf} with hD
  set L : Set ℂ := {z : ℂ | (z : ExtPlane) ∈ G ∧ w₁ z = extInf} with hL
  have hLf : L.Finite := Set.Subsingleton.finite fun z₁ h₁ z₂ h₂ =>
    OnePoint.coe_injective (hi₁ h₁.1 h₂.1 (h₁.2.trans h₂.2.symm))
  have hDo : IsOpen D :=
    (hc.isOpen_inter_preimage hG.1 (isOpen_compl_singleton : IsOpen ({extInf}ᶜ : Set ExtPlane))).preimage
      OnePoint.continuous_coe
  -- off the point where `w₁ = ∞`, the finite part is `finiteMap w₂ ∘ finiteMap w₁` (Li Zhong's Theorem 7.1)
  have hsub₁ : D \ L ⊆ {z : ℂ | (z : ExtPlane) ∈ G ∧ w₁ z ≠ extInf} := fun z hz =>
    ⟨hz.1.1, fun h => hz.2 ⟨hz.1.1, h⟩⟩
  have h1 := LiZhongQC.ac_t_isKQC_restrict hk₁ (hDo.sdiff hLf.isClosed) hsub₁
  have hsub₂ : finiteMap w₁ '' (D \ L) ⊆ {u : ℂ | (u : ExtPlane) ∈ w₁ '' G ∧ w₂ u ≠ extInf} := by
    rintro _ ⟨z, hz, rfl⟩
    have hc1 : ((finiteMap w₁ z : ℂ) : ExtPlane) = w₁ z := lv15_coe_finiteValue (hsub₁ hz).2
    refine ⟨?_, ?_⟩
    · rw [hc1]
      exact mem_image_of_mem w₁ hz.1.1
    · rw [hc1]
      exact hz.1.2
  have hcongr : LiZhongQC.IsKQC (finiteMap (w₂ ∘ w₁)) (D \ L) (K₁ * K₂) := by
    refine LiZhongQC.ad_isKQC_congr (LiZhongQC.thm7_1_comp h1 hk₂ hsub₂) fun z hz => ?_
    have hc1 : ((finiteMap w₁ z : ℂ) : ExtPlane) = w₁ z := lv15_coe_finiteValue (hsub₁ hz).2
    show finiteValue (w₂ (w₁ z)) = finiteValue (w₂ ((finiteMap w₁ z : ℂ) : ExtPlane))
    rw [hc1]
  -- the point where `w₁ = ∞` is removable
  have hcont : ContinuousOn (finiteMap (w₂ ∘ w₁)) D := fun z hz => by
    have h0 : ContinuousAt (fun z' : ℂ => (w₂ ∘ w₁) z') z :=
      ContinuousAt.comp (g := w₂ ∘ w₁) (hc.continuousAt (hG.1.mem_nhds hz.1)) OnePoint.continuous_coe.continuousAt
    have hfv : ContinuousAt finiteValue ((w₂ ∘ w₁) z) := by
      rw [← lv15_coe_finiteValue hz.2]
      exact lv15_finiteValue_continuousAt _
    exact (ContinuousAt.comp (g := finiteValue) (f := fun z' : ℂ => (w₂ ∘ w₁) z') hfv h0).continuousWithinAt
  have hinj : InjOn (finiteMap (w₂ ∘ w₁)) D := by
    intro z₁ h₁ z₂ h₂ h
    have h' : (w₂ ∘ w₁) (z₁ : ExtPlane) = (w₂ ∘ w₁) z₂ := by
      rw [← lv15_coe_finiteValue h₁.2, ← lv15_coe_finiteValue h₂.2]
      exact congrArg ((↑) : ℂ → ExtPlane) h
    exact OnePoint.coe_injective (hi h₁.1 h₂.1 h')
  exact LiZhongQC.s16p_isKQC_of_finite hDo (one_le_mul_of_one_le_of_one_le hk₁.2.1 hk₂.2.1) hcont hinj hLf
    hcongr

/-- **Theorem 5.1** (Ch. I §5.1, Ahlfors). A `1`-quasiconformal mapping `G → G′` is conformal. -/
theorem thm1_5_1 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsKQuasiconformal w G 1) :
    IsConformalMap w G := by
  have hk := lv13_isKQC_of_isKQuasiconformal hw
  obtain ⟨hG, hsp, -⟩ := hw
  -- the finite part is conformal on the finite core (Li Zhong's Theorem 7.3)
  have hconf := LiZhongQC.thm7_3_one_qc_conformal hk
  refine lv15_isConformalMap_of_differentiableAt hG hsp.1.1 hsp.1.2.1 Set.finite_empty fun ζ hζ hfin _ => ?_
  exact (hconf.1 ζ ⟨hζ, hfin⟩).differentiableAt (hk.1.mem_nhds ⟨hζ, hfin⟩)

/-- Uniform convergence in every compact subset of `G`, in the spherical metric: for every compact `C ⊂ G` and
`ε > 0`, eventually `k(wₙ(z), w(z)) < ε` for all `z ∈ C`. -/
def TendstoUniformlyOnCompactsSph (wn : ℕ → ExtPlane → ExtPlane) (w : ExtPlane → ExtPlane) (G : Set ExtPlane) :
    Prop :=
  ∀ C ⊆ G, IsCompact C → ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ C, sphericalDist (wn n z) (w z) < ε

/-- **Theorem 5.2** (Ch. I §5.2). If the `K`-quasiconformal mappings `wₙ` of the domain `G` converge uniformly to a
homeomorphism `w` of `G` in every compact subset of `G`, then `w` is `K`-quasiconformal in `G`. -/
theorem thm1_5_2 {wn : ℕ → ExtPlane → ExtPlane} {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hwn : ∀ n, IsKQuasiconformal (wn n) G K) (hlim : TendstoUniformlyOnCompactsSph wn w G)
    (hw : IsHomeoOn w G (w '' G)) : IsKQuasiconformal w G K := by
  sorry

/-- **Theorem 5.3** (Ch. I §5.3). Let `w` be a sense-preserving homeomorphism of a domain `G` which satisfies
`M(w(Q)) ≤ K M(Q)` for every analytic quadrilateral `Q`, `Q̄ ⊂ G`. Then `w` is a `K`-quasiconformal mapping of `G`. -/
theorem thm1_5_3 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G)
    (hQ : ∀ Q : Quadrilateral, Q.IsAnalytic → closure Q.dom ⊆ G →
      quadModule (w '' Q.dom) (w ∘ Q.vert) ≤ K * Q.module) :
    IsKQuasiconformal w G K := by
  sorry

/-- **Definition** (Ch. I §5.3). A `K`-quasiconformal mapping of the quadrilateral `Q` onto `Q′`: a homeomorphism of
the quadrilaterals (closures, vertices to vertices) which is `K`-quasiconformal in the interior of `Q`. -/
def IsKQCQuadMap (w : ExtPlane → ExtPlane) (Q Q' : Quadrilateral) (K : ℝ) : Prop :=
  IsQuadHomeo w Q Q' ∧ IsKQuasiconformal w Q.dom K

/-- **Lemma 5.1** (Ch. I §5.3). If a quadrilateral `Q` is mapped `K`-quasiconformally onto a quadrilateral `Q′`,
then `M(Q′) ≤ K M(Q)`. -/
theorem lemma1_5_1 {w : ExtPlane → ExtPlane} {Q Q' : Quadrilateral} {K : ℝ} (hw : IsKQCQuadMap w Q Q' K) :
    Q'.module ≤ K * Q.module := by
  sorry

/-- **Unlabelled** (Ch. I §2.4, P1:357). Every quadrilateral can be mapped conformally onto a rectangle: it has a
canonical mapping. -/
theorem exists_canonicalMap (Q : Quadrilateral) :
    ∃ (a b : ℝ) (f : ExtPlane → ExtPlane), IsCanonicalMap Q.dom Q.vert a b f := by
  obtain ⟨t, S, T, ht, hS, -, hSt, -, hinf, -⟩ :=
    lv15_normalize (w := id) (G := univ) ⟨isOpen_univ, isConnected_univ⟩ (injOn_id _) (D := Q.dom)
      (subset_univ _) Q.positive
  obtain ⟨Q', hQ'd, hQ'v, -⟩ := lv15_quadrilateral_mobius ht Q
  have hinf' : extInf ∉ closure Q'.dom := by
    rw [hQ'd]
    exact hinf
  obtain ⟨D, hD, -, hT⟩ := lv13_isTopQuad_of_quadrilateral Q' hinf'
  obtain ⟨a, b, f, ha, hb, hf, F, hF, hv⟩ := LiZhongQC.thm1_1_exists_rectangle ⟨D, Q'.vert, hT⟩
  have hc : IsCanonicalMap Q'.dom Q'.vert a b F := by
    rw [hD]
    exact lv12_isCanonicalMap_of_isStdConformalMap hT.1.1 hT.1.2.1 ha hb hf hF hv
  rw [hQ'v, hQ'd] at hc
  obtain ⟨g, hg⟩ := lv15_isCanonicalMap_mobius hS hc
  refine ⟨a, b, g, ?_⟩
  have e1 : S '' (t '' Q.dom) = Q.dom := by
    rw [image_image]
    simp [hSt]
  have e2 : S ∘ (t ∘ Q.vert) = Q.vert := funext fun i => hSt _
  rwa [e1, e2] at hg

/-- **Unlabelled** (Ch. I §2.4, P1:361, the normalized form cited later, e.g. P1:437). Every quadrilateral `Q` has a
canonical mapping onto the rectangle `R(0, M(Q), M(Q) + i, i)`. -/
theorem exists_canonicalMap_normalized (Q : Quadrilateral) :
    ∃ f : ExtPlane → ExtPlane, IsCanonicalMap Q.dom Q.vert Q.module 1 f := by
  obtain ⟨a, b, f, hf⟩ := exists_canonicalMap Q
  have ha : 0 < a := hf.1
  have hb : 0 < b := hf.2.1
  have hbC : ((b⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (inv_ne_zero hb.ne')
  have hm : Q.module = a / b := module_eq_of_isCanonicalMap Q hf
  have hfv := hf.2.2.2.2.2
  have hMc : ∀ y : ℂ, LiZhongQC.mobiusExt ((b⁻¹ : ℝ) : ℂ) 0 0 1 (y : ExtPlane) =
      ((((b⁻¹ : ℝ) : ℂ) * y + 0 : ℂ) : ExtPlane) := fun y => by
    rw [LiZhongQC.mobiusExt_coe (by rw [zero_mul, zero_add]; exact one_ne_zero)]
    congr 1
    rw [LiZhongQC.mobiusFn, zero_mul, zero_add, div_one]
  refine ⟨LiZhongQC.mobiusExt ((b⁻¹ : ℝ) : ℂ) 0 0 1 ∘ f, ?_⟩
  rw [hm]
  refine lv12_isCanonicalMap_comp_affine hf (c := ((b⁻¹ : ℝ) : ℂ)) (d := 0) hbC (div_pos ha hb) one_pos ?_
    fun i => ?_
  · ext w
    constructor
    · rintro ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
      have e1 : (((b⁻¹ : ℝ) : ℂ) * z + 0).re = b⁻¹ * z.re := by rw [add_zero, re_ofReal_mul]
      have e2 : (((b⁻¹ : ℝ) : ℂ) * z + 0).im = b⁻¹ * z.im := by rw [add_zero, im_ofReal_mul]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [e1]
        exact mul_pos (inv_pos.2 hb) h1
      · rw [e1, inv_mul_eq_div]
        exact (div_lt_div_iff_of_pos_right hb).2 h2
      · rw [e2]
        exact mul_pos (inv_pos.2 hb) h3
      · rw [e2, inv_mul_eq_div, div_lt_one hb]
        exact h4
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨(b : ℂ) * w, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [re_ofReal_mul]
        exact mul_pos hb h1
      · rw [re_ofReal_mul]
        rw [lt_div_iff₀ hb] at h2
        linarith
      · rw [im_ofReal_mul]
        exact mul_pos hb h3
      · rw [im_ofReal_mul]
        exact mul_lt_of_lt_one_right hb h4
      · show ((b⁻¹ : ℝ) : ℂ) * ((b : ℂ) * w) + 0 = w
        rw [add_zero, ← mul_assoc, ← ofReal_mul, inv_mul_cancel₀ hb.ne', ofReal_one, one_mul]
  · rw [hfv]
    have hbC' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    fin_cases i
    · show LiZhongQC.mobiusExt ((b⁻¹ : ℝ) : ℂ) 0 0 1 ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane)
      rw [hMc]
      congr 1
      ring
    · show LiZhongQC.mobiusExt ((b⁻¹ : ℝ) : ℂ) 0 0 1 (((a : ℝ) : ℂ) : ExtPlane) = ((((a / b : ℝ)) : ℂ) : ExtPlane)
      rw [hMc]
      congr 1
      push_cast
      field_simp
      ring
    · show LiZhongQC.mobiusExt ((b⁻¹ : ℝ) : ℂ) 0 0 1 (((a : ℂ) + (b : ℂ) * I : ℂ) : ExtPlane) =
        ((((a / b : ℝ) : ℂ) + (1 : ℝ) * I : ℂ) : ExtPlane)
      rw [hMc]
      congr 1
      push_cast
      field_simp
      ring
    · show LiZhongQC.mobiusExt ((b⁻¹ : ℝ) : ℂ) 0 0 1 (((b : ℂ) * I : ℂ) : ExtPlane) =
        ((((1 : ℝ) : ℂ) * I : ℂ) : ExtPlane)
      rw [hMc]
      congr 1
      push_cast
      field_simp
      ring

/-- Helper (Ch. I §2.1, Riemann mapping theorem). A fractional linear transformation is a conformal mapping of every domain of `ℂ̄`. -/
theorem lv15_rmt_isConformalMap_mobius {M : ExtPlane → ExtPlane} (hM : IsMobius M) {U : Set ExtPlane}
    (hU : IsDomainExt U) : IsConformalMap M U := by
  obtain ⟨e, rfl, -⟩ := lv15_mobius_homeomorph hM
  exact lv15_isConformalMap_of_differentiableAt hU e.continuous.continuousOn e.injective.injOn finite_empty
    fun ζ _ hζ _ => lv15_differentiableAt_finiteMap_mobius hM hζ

/-- Helper (Ch. I §2.1, Riemann mapping theorem). Every point `p` of `ℂ̄` is carried to `∞` by a fractional linear transformation, a
homeomorphism of `ℂ̄` whose inverse is again a fractional linear transformation (`1/(z - p)`, or the identity for
`p = ∞`). -/
theorem lv15_rmt_mobius_to_infty (p : ExtPlane) :
    ∃ e : ExtPlane ≃ₜ ExtPlane, IsMobius ⇑e ∧ IsMobius ⇑e.symm ∧ e p = extInf := by
  have hT : ∃ T : ExtPlane → ExtPlane, IsMobius T ∧ T p = extInf := by
    by_cases hp : p = extInf
    · refine ⟨LiZhongQC.mobiusExt 1 0 0 1, ⟨1, 0, 0, 1, by norm_num, rfl⟩, ?_⟩
      rw [hp]
      exact LiZhongQC.mobiusExt_infty_of_eq rfl
    · obtain ⟨a, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hp
      exact ⟨LiZhongQC.mobiusExt 0 1 1 (-a), ⟨0, 1, 1, -a, by norm_num, rfl⟩,
        LiZhongQC.mobiusExt_coe_of_eq_zero (by ring)⟩
  obtain ⟨T, hT, hTp⟩ := hT
  obtain ⟨e, rfl, he⟩ := lv15_mobius_homeomorph hT
  exact ⟨e, hT, he, hTp⟩

/-- Helper (Ch. I §2.1, Riemann mapping theorem). Let `G` be a simply connected domain whose complement contains two points `p ≠ q`, and `e` a
homeomorphism of `ℂ̄` carrying `p` to `∞`. Then `e(G)` is a domain `U` of the finite plane whose complement in `ℂ̄` is
connected and contains a finite point (`e(q)`). -/
theorem lv15_rmt_finite_model {G : Set ExtPlane} (hG : IsSimplyConnectedDomain G) {p q : ExtPlane} (hp : p ∉ G)
    (hq : q ∉ G) (hpq : p ≠ q) (e : ExtPlane ≃ₜ ExtPlane) (he : e p = extInf) :
    ∃ U : Set ℂ, IsOpen U ∧ IsConnected U ∧ IsConnected (LiZhongQC.toExt U)ᶜ ∧ Uᶜ.Nonempty ∧
      e '' G = LiZhongQC.toExt U := by
  have hinf : extInf ∉ e '' G := fun h => by
    rw [← he] at h
    exact hp (e.injective.mem_set_image.1 h)
  have heq : e '' G = LiZhongQC.toExt (finitePart (e '' G)) := by
    ext z
    constructor
    · intro hz
      have hz' : z ≠ extInf := by
        rintro rfl
        exact hinf hz
      obtain ⟨ζ, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hz'
      exact ⟨ζ, hz, rfl⟩
    · rintro ⟨ζ, hζ, rfl⟩
      exact hζ
  refine ⟨finitePart (e '' G), (e.isOpenMap G hG.1.1).preimage OnePoint.continuous_coe, ?_, ?_, ?_, heq⟩
  · have h := hG.1.2.image e e.continuous.continuousOn
    rw [heq] at h
    obtain ⟨⟨_, ζ, hζ, rfl⟩, h'⟩ := h
    exact ⟨⟨ζ, hζ⟩, OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image.1 h'⟩
  · rw [← heq, ← image_compl_eq e.bijective]
    exact ⟨⟨e p, mem_image_of_mem e hp⟩, hG.2.image e e.continuous.continuousOn⟩
  · have hq' : e q ≠ extInf := fun h => hpq (e.injective (by rw [he, h]))
    obtain ⟨a, ha⟩ := OnePoint.ne_infty_iff_exists.1 hq'
    refine ⟨a, fun h => hq ?_⟩
    have h' : (a : ExtPlane) ∈ e '' G := h
    rw [ha] at h'
    exact e.injective.mem_set_image.1 h'

/-- Helper (Ch. I §2.1, Riemann mapping theorem). Two domains `U`, `V` of the finite plane whose complements in `ℂ̄` are connected and contain a
finite point are conformally equivalent: there is a holomorphic bijection of `V` onto `U` (the Riemann mapping theorem
`RMT.exists_riemannMap_of_hasHolomorphicSqrt` with the connected-complement bridge
`LiZhongQC.hasHolomorphicSqrt_of_isConnected_compl`, and `RMT.invFunOn_riemannMap`). -/
theorem lv15_rmt_riemann_equiv {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hUcc : IsConnected (LiZhongQC.toExt U)ᶜ) (hUne : Uᶜ.Nonempty) (hV : IsOpen V) (hVc : IsConnected V)
    (hVcc : IsConnected (LiZhongQC.toExt V)ᶜ) (hVne : Vᶜ.Nonempty) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h V ∧ BijOn h V U := by
  obtain ⟨u, hu⟩ := hUc.nonempty
  obtain ⟨v, hv⟩ := hVc.nonempty
  obtain ⟨f, hf, hfb⟩ := RMT.exists_riemannMap_of_hasHolomorphicSqrt hU hUc hUne
    (LiZhongQC.hasHolomorphicSqrt_of_isConnected_compl hU hUc hUcc) hu
  obtain ⟨g, hg, hgb⟩ := RMT.exists_riemannMap_of_hasHolomorphicSqrt hV hVc hVne
    (LiZhongQC.hasHolomorphicSqrt_of_isConnected_compl hV hVc hVcc) hv
  obtain ⟨hid, hib⟩ := RMT.invFunOn_riemannMap hU hf.diff hf.injOn hfb
  exact ⟨Function.invFunOn f U ∘ g, hid.comp hg.diff hgb.mapsTo, hib.comp hgb⟩

/-- Helper (Ch. I §2.1, Riemann mapping theorem). A holomorphic bijection `h` of a domain `V` of the finite plane onto `U`, read on `ℂ̄`, is a
conformal mapping of `V` onto `U`. -/
theorem lv15_rmt_isConformalMap_lift {h : ℂ → ℂ} {U V : Set ℂ} (hV : IsOpen V) (hVc : IsConnected V)
    (hd : DifferentiableOn ℂ h V) (hb : BijOn h V U) :
    IsConformalMap (fun z => ((h (finiteValue z) : ℂ) : ExtPlane)) (LiZhongQC.toExt V) ∧
      (fun z => ((h (finiteValue z) : ℂ) : ExtPlane)) '' LiZhongQC.toExt V = LiZhongQC.toExt U := by
  have hVd : IsDomainExt (LiZhongQC.toExt V) :=
    ⟨OnePoint.isOpen_image_coe.2 hV, hVc.image _ OnePoint.continuous_coe.continuousOn⟩
  refine ⟨lv15_isConformalMap_of_differentiableAt hVd ?_ ?_ finite_empty ?_, ?_⟩
  · rintro _ ⟨ζ, hζ, rfl⟩
    apply ContinuousAt.continuousWithinAt
    rw [OnePoint.continuousAt_coe]
    exact OnePoint.continuous_coe.continuousAt.comp (hd.differentiableAt (hV.mem_nhds hζ)).continuousAt
  · rintro _ ⟨ζ₁, h₁, rfl⟩ _ ⟨ζ₂, h₂, rfl⟩ h12
    exact congrArg _ (hb.injOn h₁ h₂ (OnePoint.coe_injective h12))
  · intro ζ hζ _ _
    obtain ⟨u, hu, hue⟩ := hζ
    obtain rfl := OnePoint.coe_injective hue
    have hfm : finiteMap (fun z => ((h (finiteValue z) : ℂ) : ExtPlane)) = h := rfl
    rw [hfm]
    exact hd.differentiableAt (hV.mem_nhds hu)
  · show _ '' (((↑) : ℂ → ExtPlane) '' V) = ((↑) : ℂ → ExtPlane) '' U
    rw [image_image, ← hb.image_eq, image_image]
    rfl

/-- Helper (Ch. I §2.1, Riemann mapping theorem). The unit disc is a domain whose complement in `ℂ̄` is connected and
contains a finite point (the complement is the image of the closed unit disc under the inversion `ζ ↦ 1/ζ`). -/
theorem lv15_rmt_disc_data : IsOpen LiZhongQC.unitDisc ∧ IsConnected LiZhongQC.unitDisc ∧
    IsConnected (toExt LiZhongQC.unitDisc)ᶜ ∧ (LiZhongQC.unitDisc)ᶜ.Nonempty := by
  have hD : LiZhongQC.unitDisc = Metric.ball (0 : ℂ) 1 := rfl
  have hIM : IsMobius (LiZhongQC.mobiusExt 0 1 1 0) := ⟨0, 1, 1, 0, by norm_num, rfl⟩
  obtain ⟨M, hMeq, -⟩ := lv15_mobius_homeomorph hIM
  have hMinf : M extInf = ((0 : ℂ) : ExtPlane) := by
    rw [congrFun hMeq]
    simp [LiZhongQC.mobiusExt, extInf]
  have hMc : ∀ a : ℂ, M (a : ExtPlane) = if a = 0 then extInf else ((a⁻¹ : ℂ) : ExtPlane) := fun a => by
    rw [congrFun hMeq]
    simp [LiZhongQC.mobiusExt]
  have hS : (toExt LiZhongQC.unitDisc)ᶜ = M '' toExt (Metric.closedBall (0 : ℂ) 1) := by
    ext z
    induction z using OnePoint.rec with
    | infty =>
      refine ⟨fun _ => ⟨((0 : ℂ) : ExtPlane), ⟨0, by simp, rfl⟩, ?_⟩, fun _ => ?_⟩
      · rw [hMc]; simp
      · rintro ⟨a, ha, h⟩
        exact OnePoint.coe_ne_infty a h
    | coe a =>
      constructor
      · intro h
        have ha : 1 ≤ ‖a‖ := by
          by_contra hlt
          exact h ⟨a, by rw [hD]; simpa using not_le.1 hlt, rfl⟩
        have ha0 : a ≠ 0 := by rintro rfl; norm_num at ha
        refine ⟨((a⁻¹ : ℂ) : ExtPlane), ⟨a⁻¹, ?_, rfl⟩, ?_⟩
        · simp only [Metric.mem_closedBall, dist_zero_right, norm_inv]
          exact inv_le_one_of_one_le₀ ha
        · rw [hMc]; simp [ha0]
      · rintro ⟨y, ⟨b, hb, rfl⟩, hy⟩ ⟨c, hc, hca⟩
        have hcb := OnePoint.coe_injective hca
        rw [hMc] at hy
        by_cases hb0 : b = 0
        · simp only [hb0, ite_true] at hy
          exact OnePoint.coe_ne_infty a hy.symm
        · simp only [hb0, ite_false] at hy
          have hab := OnePoint.coe_injective hy
          have hb1 : ‖b‖ ≤ 1 := by simpa using hb
          have hbpos : 0 < ‖b‖ := norm_pos_iff.2 hb0
          rw [hD] at hc
          have : ‖c‖ < 1 := by simpa using hc
          rw [hcb, ← hab, norm_inv] at this
          have := (inv_lt_one_iff₀.1 this)
          rcases this with h | h
          · exact absurd h (not_le.2 hbpos)
          · exact absurd h (not_lt.2 hb1)
  refine ⟨Metric.isOpen_ball, (convex_ball (0 : ℂ) 1).isConnected ⟨0, by simp⟩ |> fun h => by rwa [hD], ?_,
    ⟨2, by rw [hD]; simp⟩⟩
  rw [hS]
  exact (((convex_closedBall (0 : ℂ) 1).isConnected ⟨0, by simp⟩).image _
    OnePoint.continuous_coe.continuousOn).image M M.continuous.continuousOn

/-- Helper (Ch. I §2.1, Riemann mapping theorem). A conformal mapping of a domain `toExt U` of the finite plane onto the
finite plane `toExt univ` is, read on `ℂ`, a holomorphic bijection of `U` onto `ℂ`. -/
theorem lv15_rmt_finite_part {U : Set ℂ} (hU : IsOpen U) {W : ExtPlane → ExtPlane}
    (hW : IsConformalMap W (toExt U)) (hWi : W '' toExt U = toExt univ) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F U ∧ InjOn F U ∧ F '' U = univ := by
  have hfin : ∀ z ∈ U, W (z : ExtPlane) = ((finiteMap W z : ℂ) : ExtPlane) := fun z hz => by
    have : W (z : ExtPlane) ∈ toExt (univ : Set ℂ) := hWi ▸ mem_image_of_mem W ⟨z, hz, rfl⟩
    obtain ⟨a, -, ha⟩ := this
    simp [finiteMap, finiteValue, ← ha]
  refine ⟨finiteMap W, fun z hz => ?_, fun z₁ h₁ z₂ h₂ h => ?_, ?_⟩
  · exact (lv12_differentiableAt_of_localRep hU hfin hz (hW.2.2.2 _ ⟨z, hz, rfl⟩)).differentiableWithinAt
  · have := hW.2.2.1 ⟨z₁, h₁, rfl⟩ ⟨z₂, h₂, rfl⟩ (by rw [hfin z₁ h₁, hfin z₂ h₂, h])
    exact OnePoint.coe_injective this
  · refine eq_univ_of_forall fun y => ?_
    have : ((y : ℂ) : ExtPlane) ∈ W '' toExt U := hWi ▸ ⟨y, mem_univ _, rfl⟩
    obtain ⟨x, ⟨z, hz, rfl⟩, hx⟩ := this
    exact ⟨z, hz, OnePoint.coe_injective (by rw [← hfin z hz]; exact hx)⟩

/-- Helper (Ch. I §2.1, Riemann mapping theorem). A simply connected domain whose complement contains two points is
mapped conformally onto the unit disc (Möbius map to the finite plane, the Riemann mapping theorem of the project, and
the lift). -/
theorem lv15_rmt_exists_disc {G : Set ExtPlane} (hG : IsSimplyConnectedDomain G) {p q : ExtPlane} (hp : p ∉ G)
    (hq : q ∉ G) (hpq : p ≠ q) :
    ∃ w : ExtPlane → ExtPlane, IsConformalMap w G ∧ w '' G = toExt LiZhongQC.unitDisc := by
  obtain ⟨hDo, hDc, hDcc, hDne⟩ := lv15_rmt_disc_data
  obtain ⟨A, hA, hAs, hAp⟩ := lv15_rmt_mobius_to_infty p
  obtain ⟨U, hUo, hUc, hUcc, hUne, hAG⟩ := lv15_rmt_finite_model hG hp hq hpq A hAp
  obtain ⟨h, hhd, hhb⟩ := lv15_rmt_riemann_equiv hDo hDc hDcc hDne hUo hUc hUcc hUne
  obtain ⟨hH, hHV⟩ := lv15_rmt_isConformalMap_lift hUo hUc hhd hhb
  have hAG' : IsConformalMap (fun z => ((h (finiteValue z) : ℂ) : ExtPlane)) (A '' G) := by
    rw [hAG]; exact hH
  have hAA : ⇑A.symm.symm = ⇑A := rfl
  have hc := lv15_isConformalMap_comp_symm A.symm hA hAG'
  rw [lv15_symm_image_image, hAA] at hc
  refine ⟨_, hc, ?_⟩
  rw [image_comp, hAG, hHV]

/-- Helper (Ch. I §2.1, Riemann mapping theorem). A simply connected domain whose complement contains two points is
not mapped conformally onto the finite plane (the inverse of such a map composed with a Riemann map of the finite model
of `G` onto the unit disc would be a bounded injective entire function, contradicting Liouville). -/
theorem lv15_rmt_no_plane_map {G : Set ExtPlane} (hG : IsSimplyConnectedDomain G) {p q : ExtPlane} (hp : p ∉ G)
    (hq : q ∉ G) (hpq : p ≠ q) : ¬ ∃ w : ExtPlane → ExtPlane, IsConformalMap w G ∧ w '' G = toExt univ := by
  rintro ⟨w, hw, hwi⟩
  obtain ⟨hDo, hDc, hDcc, hDne⟩ := lv15_rmt_disc_data
  obtain ⟨A, hA, hAs, hAp⟩ := lv15_rmt_mobius_to_infty p
  obtain ⟨U, hUo, hUc, hUcc, hUne, hAG⟩ := lv15_rmt_finite_model hG hp hq hpq A hAp
  obtain ⟨h, hhd, hhb⟩ := lv15_rmt_riemann_equiv hDo hDc hDcc hDne hUo hUc hUcc hUne
  have hW : IsConformalMap (w ∘ A.symm) (toExt U) := by
    rw [← hAG]; exact lv15_isConformalMap_comp_symm A hAs hw
  have hWi : (w ∘ A.symm) '' toExt U = toExt univ := by
    rw [← hAG, image_comp, lv15_symm_image_image, hwi]
  obtain ⟨F, hFd, hFi, hFs⟩ := lv15_rmt_finite_part hUo hW hWi
  obtain ⟨-, hinvd⟩ := RMT.differentiableOn_invFunOn_of_injOn hUo hFd hFi
  rw [hFs] at hinvd
  have hex : ∀ y : ℂ, ∃ a ∈ U, F a = y := fun y => by
    have : y ∈ F '' U := hFs ▸ mem_univ y
    exact this
  have hmem : ∀ y : ℂ, Function.invFunOn F U y ∈ U := fun y => Function.invFunOn_mem (hex y)
  have hFinv : ∀ y : ℂ, F (Function.invFunOn F U y) = y := fun y => Function.invFunOn_eq (hex y)
  have hgd : Differentiable ℂ (h ∘ Function.invFunOn F U) := fun y => by
    have h1 : DifferentiableAt ℂ (Function.invFunOn F U) y := hinvd.differentiableAt univ_mem
    have h2 : DifferentiableAt ℂ h (Function.invFunOn F U y) :=
      (hhd _ (hmem y)).differentiableAt (hUo.mem_nhds (hmem y))
    exact h2.comp y h1
  have hbd : Bornology.IsBounded (range (h ∘ Function.invFunOn F U)) := by
    refine (Metric.isBounded_ball (x := (0 : ℂ)) (r := 1)).subset ?_
    rintro _ ⟨y, rfl⟩
    exact hhb.mapsTo (hmem y)
  have h01 := hgd.apply_eq_apply_of_bounded hbd 0 1
  have h2 := congrArg F (hhb.injOn (hmem 0) (hmem 1) h01)
  rw [hFinv, hFinv] at h2
  exact zero_ne_one h2

/-- Helper (Ch. I §2.1, Riemann mapping theorem). The whole sphere `ℂ̄` is not mapped conformally onto the finite plane
(the image of the compact `ℂ̄` is compact, `ℂ` is not). -/
theorem lv15_rmt_no_plane_map_univ {w : ExtPlane → ExtPlane} (hw : ContinuousOn w univ) :
    w '' univ ≠ toExt univ := by
  intro h
  have hc : IsCompact (w '' univ) := isCompact_univ.image_of_continuousOn hw
  rw [h] at hc
  have hcl : IsClosed (toExt (univ : Set ℂ)) := hc.isClosed
  have hopen : IsOpen ({extInf} : Set ExtPlane) := by
    have : ({extInf} : Set ExtPlane) = (toExt (univ : Set ℂ))ᶜ := by
      ext z
      induction z using OnePoint.rec with
      | infty => simp [toExt, extInf]
      | coe a => simp [toExt, extInf]
    rw [this]
    exact hcl.isOpen_compl
  rw [OnePoint.isOpen_iff_of_mem (by simp [extInf])] at hopen
  have := hopen.2
  have h' : (((↑) : ℂ → ExtPlane) ⁻¹' ({extInf} : Set ExtPlane))ᶜ = univ := by
    ext a; simp [extInf]
  rw [h'] at this
  exact (NoncompactSpace.noncompact_univ (X := ℂ)) this

/-- **The Riemann mapping theorem** (Ch. I §2.1). Every simply connected domain of the plane can be mapped
conformally onto one of the canonical domains: 1° the whole plane `ℂ̄`, 2° the finite plane, 3° the unit disc. A
conformal mapping onto the finite plane exists if and only if the complement of the domain consists of a single
point. -/
theorem riemann_mapping_theorem {G : Set ExtPlane} (hG : IsSimplyConnectedDomain G) :
    (∃ w : ExtPlane → ExtPlane, IsConformalMap w G ∧
      (w '' G = univ ∨ w '' G = toExt univ ∨ w '' G = toExt LiZhongQC.unitDisc)) ∧
    ((∃ w : ExtPlane → ExtPlane, IsConformalMap w G ∧ w '' G = toExt univ) ↔ ∃ p, Gᶜ = {p}) := by
  by_cases h2 : ∃ p q : ExtPlane, p ∉ G ∧ q ∉ G ∧ p ≠ q
  · obtain ⟨p, q, hp, hq, hpq⟩ := h2
    obtain ⟨w, hw, hwi⟩ := lv15_rmt_exists_disc hG hp hq hpq
    refine ⟨⟨w, hw, Or.inr (Or.inr hwi)⟩, ⟨fun h => absurd h (lv15_rmt_no_plane_map hG hp hq hpq), ?_⟩⟩
    rintro ⟨p', hp'⟩
    have h1 : p ∈ ({p'} : Set ExtPlane) := hp' ▸ hp
    have h3 : q ∈ ({p'} : Set ExtPlane) := hp' ▸ hq
    exact absurd ((Set.mem_singleton_iff.1 h1).trans (Set.mem_singleton_iff.1 h3).symm) hpq
  · push Not at h2
    by_cases hne : Gᶜ.Nonempty
    · obtain ⟨p, hp⟩ := hne
      have hcs : Gᶜ = {p} := Set.eq_singleton_iff_unique_mem.2 ⟨hp, fun q hq => h2 q p hq hp⟩
      obtain ⟨e, he, hes, hep⟩ := lv15_rmt_mobius_to_infty p
      have himg : e '' G = toExt univ := by
        ext y
        have hG' : ∀ x, x ∈ G ↔ x ≠ p := fun x => by
          rw [← not_iff_not, not_not, ← Set.mem_compl_iff, hcs, Set.mem_singleton_iff]
        constructor
        · rintro ⟨x, hx, rfl⟩
          have hx' : e x ≠ extInf := fun h => (hG' x).1 hx (e.injective (h.trans hep.symm))
          obtain ⟨a, ha⟩ := OnePoint.ne_infty_iff_exists.1 hx'
          exact ⟨a, Set.mem_univ _, ha⟩
        · rintro ⟨a, -, rfl⟩
          refine ⟨e.symm a, (hG' _).2 fun h => ?_, e.apply_symm_apply _⟩
          have h' : e (e.symm (a : ExtPlane)) = extInf := by rw [h, hep]
          rw [e.apply_symm_apply] at h'
          exact OnePoint.coe_ne_infty a h'
      exact ⟨⟨e, lv15_rmt_isConformalMap_mobius he hG.1, Or.inr (Or.inl himg)⟩,
        ⟨fun _ => ⟨p, hcs⟩, fun _ => ⟨e, lv15_rmt_isConformalMap_mobius he hG.1, himg⟩⟩⟩
    · have hGu : G = univ := by
        rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hne
        exact hne
      subst hGu
      have hid : IsMobius (id : ExtPlane → ExtPlane) := ⟨1, 0, 0, 1, by norm_num, by
        funext z
        induction z using OnePoint.rec <;> simp [LiZhongQC.mobiusExt]⟩
      refine ⟨⟨id, lv15_rmt_isConformalMap_mobius hid hG.1, Or.inl (Set.image_id _)⟩, ⟨?_, ?_⟩⟩
      · rintro ⟨w, hw, hwi⟩
        exact (lv15_rmt_no_plane_map_univ hw.2.1 hwi).elim
      · rintro ⟨p, hp⟩
        simp at hp

end LehtoVirtanen1973
