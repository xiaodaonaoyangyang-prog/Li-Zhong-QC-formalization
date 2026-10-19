import References.LehtoVirtanen1973.Ch04.S05_ComplexDilatation

/-!
# Lehto–Virtanen, Chapter V §1: Existence theorem

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Introduction to
Chapter V and Ch. V §1 (pp. 190–195; `full.md` P1:5939–6039, continued in the second part P2:1–9).

Conventions of Chapter V (as in Chapter IV). A quasiconformal mapping `w : G → G′` is a sense-preserving homeomorphism
of a domain `G` of `ℂ̄` (`IsQuasiconformalMap`, `IsKQuasiconformal`), with `G′ = w(G)`; its complex dilatation is
`complexDilatationLV` (IV.5.1). A function `κ` "in `G`" is a function `κ : ℂ → ℂ` on the finite part of `G` (the point
`∞` is a null set, and its value there is without significance). "Measurable" is Lebesgue measurability for the area
measure of the finite part of `G` (`AEStronglyMeasurable κ (volume.restrict (finitePart G))`), and "almost everywhere
in `G`" is `∀ᵐ z ∂(volume.restrict (finitePart G))`. The condition `sup_{z ∈ G} |κ(z)| < 1` is the existence of a
bound `k < 1` for `|κ|` at every finite point of `G`.

The Introduction to Chapter V (P1:5941–5959) announces the results of §1–§7 and recalls facts of IV.5 (the complex
dilatation is a Borel function, bounded in absolute value by a number less than one; the Uniqueness theorem); it
contains no item of its own.

* Existence theorem (§1.3) — `existence_theorem`
* Mapping theorem (§1.3), existence of the mapping — `mapping_theorem_i`
* Mapping theorem (§1.3), uniqueness of the mapping up to a conformal mapping of `G′` onto itself — exists:
  `LehtoVirtanen1973.uniqueness_theorem` (the Uniqueness theorem IV.5.2 for two such mappings w and w₁ of G, with
  w(G) = w₁(G) = G′: the conformal mapping f of G′ with w₁ = f ∘ w maps G′ onto w₁(G) = G′; the converse, that
  f ∘ w again has complex dilatation κ almost everywhere for every conformal mapping f of G′ onto itself, is
  `LehtoVirtanen1973.eq4_5_7`)

Not stated (inventory: omitted): the remark of §1.1 on the necessary restrictions (P1:5963–5967: `κ` cannot be
prescribed at every point, measurability suffices); the reduction of the existence problem to the whole plane by
extending `κ` by `0` (P1:5975, a device of the proof); the sewing problem of §1.2 and the affine mappings (1.1)
(P1:5977–6001, steps of the proof); the remark after the Existence theorem that the quasiconformal mappings of `G` with
complex dilatation `κ` almost everywhere are exactly the `f ∘ w`, `f` conformal in `w(G)` (P1:6029: the
Uniqueness theorem IV.5.2, `uniqueness_theorem`, with (5.7) of IV.5.2, `eq4_5_7`); and the survey of other proofs in
§1.4 (P1:6035–P2:9; there the uniformization theorem is named but neither stated nor used). [OCR] P2:1 and P2:5 have
the Beltrami equation `w_{\bar z} = κ w_z` OCR'd as `w_z = κ w_z`.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane)
open References (IsDomainExt finitePart)

/-! ## §1.3 Proof of the Existence theorem -/

/-- **Existence theorem** (Ch. V §1.3). If `G` is an arbitrary domain and `κ` an arbitrary measurable function in `G`
with `sup_{z ∈ G} |κ(z)| < 1`, then there exists a quasiconformal mapping `w` of `G` whose complex dilatation coincides
with `κ` almost everywhere in `G`.
Modelling: `G` is a domain of `ℂ̄` (it may contain `∞`); `κ` is given on the finite part of `G`, and the bound
`sup |κ| < 1` is a bound `k < 1` at every finite point of `G`. The maximal dilatation of `w` is not asserted, as in the
book; where the book later takes `w` to be `K`-quasiconformal for `|κ| ≤ (K - 1)/(K + 1)` (P2:175, 441–443, 1618,
1745), this follows with Theorem IV.5.1 (`thm4_5_1_i`, `thm4_5_1_ii`), after `κ` is changed on a null set where those
uses bound it only almost everywhere. -/
theorem existence_theorem {G : Set ExtPlane} (hG : IsDomainExt G) {κ : ℂ → ℂ}
    (hκm : AEStronglyMeasurable κ (volume.restrict (finitePart G)))
    (hκ : ∃ k : ℝ, k < 1 ∧ ∀ z ∈ finitePart G, ‖κ z‖ ≤ k) :
    ∃ w : ExtPlane → ExtPlane, IsQuasiconformalMap w G ∧
      ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), complexDilatationLV w z = κ z := by
  obtain ⟨k, hk1, hκk⟩ := hκ
  have hk'0 : 0 ≤ max k 0 := le_max_right _ _
  have hk'1 : max k 0 < 1 := max_lt hk1 zero_lt_one
  have hGo : IsOpen (finitePart G) := hG.1.preimage OnePoint.continuous_coe
  -- extend `κ` by `0` off `G` (the reduction to the whole plane, P1:5975)
  have hμ : LiZhongQC.IsBeltramiCoeff ((finitePart G).indicator κ) univ (max k 0) := by
    refine ⟨?_, Eventually.of_forall fun z => ?_⟩
    · rw [Measure.restrict_univ]
      exact (aestronglyMeasurable_indicator_iff hGo.measurableSet).2 hκm
    · by_cases hz : z ∈ finitePart G
      · rw [indicator_of_mem hz]
        exact (hκk z hz).trans (le_max_left _ _)
      · rw [indicator_of_notMem hz, norm_zero]
        exact hk'0
  -- the normalized solution in the plane (Li Zhong's Theorem 13.7)
  obtain ⟨f, ⟨-, hfs, -, -, hfμ⟩, hfK, -⟩ := LiZhongQC.thm13_7_normalized_existence hk'0 hk'1 hμ
  -- `f` is a homeomorphism of `ℂ` onto itself, and `w = f` (with `∞ ↦ ∞`) a homeomorphism of `ℂ̄`
  have hbij : Function.Bijective f := by
    refine ⟨fun a b h => hfK.2.2.1.2.1 (mem_univ a) (mem_univ b) h, fun y => ?_⟩
    have hy : y ∈ f '' univ := by
      rw [hfs]
      exact mem_univ y
    obtain ⟨x, -, hx⟩ := hy
    exact ⟨x, hx⟩
  have hopen : IsOpenMap f := fun U hU =>
    LiZhongQC.isOpen_image_of_isKQC (LiZhongQC.ac_t_isKQC_restrict hfK hU (subset_univ U))
  set e : ℂ ≃ₜ ℂ := (Equiv.ofBijective f hbij).toHomeomorphOfContinuousOpen
    (continuousOn_univ.1 hfK.2.2.1.1) hopen with he
  set w : ExtPlane → ExtPlane := ⇑e.onePointCongr with hw
  have hwf : ∀ z : ℂ, w z = ((f z : ℂ) : ExtPlane) := fun z => rfl
  have hfm : finiteMap w = f := funext fun z => rfl
  -- the finite core of `w` in `G` is the finite part of `G`; there `w` is `K`-q.c. in Li Zhong's sense
  have hcore : {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ LiZhongQC.extInf} = finitePart G := by
    ext z
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rw [hwf]
    exact OnePoint.coe_ne_infty _
  have hk : LiZhongQC.IsKQC (finiteMap w) {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ LiZhongQC.extInf}
      ((1 + max k 0) / (1 - max k 0)) := by
    rw [hcore, hfm]
    exact LiZhongQC.ac_t_isKQC_restrict hfK hGo (subset_univ _)
  have hq := lv15_isKQuasiconformal_of_isKQC hG e.onePointCongr.continuous.continuousOn
    e.onePointCongr.injective.injOn hk
  refine ⟨w, ⟨hq.1, hq.2.1, lt_of_le_of_lt hq.2.2 ENNReal.ofReal_lt_top⟩, ?_⟩
  -- its complex dilatation is that of `f`, which is `κ` in `G`
  filter_upwards [ae_restrict_of_ae hfμ, ae_restrict_mem hGo.measurableSet] with z hz hzG
  rw [lv45_complexDilatationLV_eq e.onePointCongr.continuous.continuousAt
    (show w z ≠ LiZhongQC.extInf by rw [hwf]; exact OnePoint.coe_ne_infty _), hfm, hz, indicator_of_mem hzG]

/-- Helper (Tier B, B2). The Existence theorem with a global mapping: the solution can be taken to be a homeomorphism
`E` of `ℂ̄` onto itself (the normalized solution of Li Zhong's Theorem 13.7 for `κ` extended by `0`, with `∞ ↦ ∞`), as
in the proof of `existence_theorem`. -/
theorem lv51_exists_global {G : Set ExtPlane} (hG : IsDomainExt G) {κ : ℂ → ℂ}
    (hκm : AEStronglyMeasurable κ (volume.restrict (finitePart G)))
    (hκ : ∃ k : ℝ, k < 1 ∧ ∀ z ∈ finitePart G, ‖κ z‖ ≤ k) :
    ∃ E : ExtPlane ≃ₜ ExtPlane, IsQuasiconformalMap E G ∧
      ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), complexDilatationLV E z = κ z := by
  obtain ⟨k, hk1, hκk⟩ := hκ
  have hk'0 : 0 ≤ max k 0 := le_max_right _ _
  have hk'1 : max k 0 < 1 := max_lt hk1 zero_lt_one
  have hGo : IsOpen (finitePart G) := hG.1.preimage OnePoint.continuous_coe
  have hμ : LiZhongQC.IsBeltramiCoeff ((finitePart G).indicator κ) univ (max k 0) := by
    refine ⟨?_, Eventually.of_forall fun z => ?_⟩
    · rw [Measure.restrict_univ]
      exact (aestronglyMeasurable_indicator_iff hGo.measurableSet).2 hκm
    · by_cases hz : z ∈ finitePart G
      · rw [indicator_of_mem hz]
        exact (hκk z hz).trans (le_max_left _ _)
      · rw [indicator_of_notMem hz, norm_zero]
        exact hk'0
  obtain ⟨f, ⟨-, hfs, -, -, hfμ⟩, hfK, -⟩ := LiZhongQC.thm13_7_normalized_existence hk'0 hk'1 hμ
  have hbij : Function.Bijective f := by
    refine ⟨fun a b h => hfK.2.2.1.2.1 (mem_univ a) (mem_univ b) h, fun y => ?_⟩
    have hy : y ∈ f '' univ := by
      rw [hfs]
      exact mem_univ y
    obtain ⟨x, -, hx⟩ := hy
    exact ⟨x, hx⟩
  have hopen : IsOpenMap f := fun U hU =>
    LiZhongQC.isOpen_image_of_isKQC (LiZhongQC.ac_t_isKQC_restrict hfK hU (subset_univ U))
  set e : ℂ ≃ₜ ℂ := (Equiv.ofBijective f hbij).toHomeomorphOfContinuousOpen
    (continuousOn_univ.1 hfK.2.2.1.1) hopen with he
  set w : ExtPlane ≃ₜ ExtPlane := e.onePointCongr with hw
  have hwf : ∀ z : ℂ, w z = ((f z : ℂ) : ExtPlane) := fun z => rfl
  have hfm : finiteMap w = f := funext fun z => rfl
  have hcore : {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ LiZhongQC.extInf} = finitePart G := by
    ext z
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rw [hwf]
    exact OnePoint.coe_ne_infty _
  have hk : LiZhongQC.IsKQC (finiteMap w) {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ LiZhongQC.extInf}
      ((1 + max k 0) / (1 - max k 0)) := by
    rw [hcore, hfm]
    exact LiZhongQC.ac_t_isKQC_restrict hfK hGo (subset_univ _)
  have hq := lv15_isKQuasiconformal_of_isKQC hG w.continuous.continuousOn w.injective.injOn hk
  refine ⟨w, ⟨hq.1, hq.2.1, lt_of_le_of_lt hq.2.2 ENNReal.ofReal_lt_top⟩, ?_⟩
  filter_upwards [ae_restrict_of_ae hfμ, ae_restrict_mem hGo.measurableSet] with z hz hzG
  rw [lv45_complexDilatationLV_eq w.continuous.continuousAt
    (show w z ≠ LiZhongQC.extInf by rw [hwf]; exact OnePoint.coe_ne_infty _), hfm, hz, indicator_of_mem hzG]

/-- Helper (Tier B, B2). A conformal mapping `f` of `w(G)`, composed with a quasiconformal mapping `w` of `G` with
complex dilatation `κ`, is a quasiconformal mapping of `G` with the same complex dilatation
(`conformal_isKQuasiconformal_one`, `kqc_comp`, and (5.7) of IV.5.2, `eq4_5_7`). -/
theorem lv51_comp_conformal {w f : ExtPlane → ExtPlane} {G : Set ExtPlane} {κ : ℂ → ℂ}
    (hw : IsQuasiconformalMap w G)
    (hκ : ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), complexDilatationLV w z = κ z)
    (hf : IsConformalMap f (w '' G)) :
    IsQuasiconformalMap (f ∘ w) G ∧
      ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), complexDilatationLV (f ∘ w) z = κ z := by
  have hf1 := conformal_isKQuasiconformal_one hf
  have hfq : IsQuasiconformalMap f (w '' G) := ⟨hf1.1, hf1.2.1, hf1.2.2.trans_lt ENNReal.ofReal_lt_top⟩
  have hwK : IsKQuasiconformal w G (maxDilatationK w G).toReal :=
    ⟨hw.1, hw.2.1, (ENNReal.ofReal_toReal hw.2.2.ne).ge⟩
  have hc := kqc_comp hwK hf1
  refine ⟨⟨hc.1, hc.2.1, hc.2.2.trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  filter_upwards [(eq4_5_7 hw hfq).1 hf, hκ] with z h1 h2
  rw [h1, h2]

/-- Helper (Tier B, B2). A fractional linear transformation is a conformal mapping of every domain of `ℂ̄`. -/
theorem lv51_isConformalMap_mobius {M : ExtPlane → ExtPlane} (hM : LiZhongQC.IsMobius M) {U : Set ExtPlane}
    (hU : IsDomainExt U) : IsConformalMap M U := by
  obtain ⟨e, rfl, -⟩ := lv15_mobius_homeomorph hM
  exact lv15_isConformalMap_of_differentiableAt hU e.continuous.continuousOn e.injective.injOn finite_empty
    fun ζ _ hζ _ => lv15_differentiableAt_finiteMap_mobius hM hζ

/-- Helper (Tier B, B2). Every point `p` of `ℂ̄` is carried to `∞` by a fractional linear transformation, a
homeomorphism of `ℂ̄` whose inverse is again a fractional linear transformation (`1/(z - p)`, or the identity for
`p = ∞`). -/
theorem lv51_mobius_to_infty (p : ExtPlane) :
    ∃ e : ExtPlane ≃ₜ ExtPlane, LiZhongQC.IsMobius ⇑e ∧ LiZhongQC.IsMobius ⇑e.symm ∧ e p = LiZhongQC.extInf := by
  have hT : ∃ T : ExtPlane → ExtPlane, LiZhongQC.IsMobius T ∧ T p = LiZhongQC.extInf := by
    by_cases hp : p = LiZhongQC.extInf
    · refine ⟨LiZhongQC.mobiusExt 1 0 0 1, ⟨1, 0, 0, 1, by norm_num, rfl⟩, ?_⟩
      rw [hp]
      exact LiZhongQC.mobiusExt_infty_of_eq rfl
    · obtain ⟨a, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hp
      exact ⟨LiZhongQC.mobiusExt 0 1 1 (-a), ⟨0, 1, 1, -a, by norm_num, rfl⟩,
        LiZhongQC.mobiusExt_coe_of_eq_zero (by ring)⟩
  obtain ⟨T, hT, hTp⟩ := hT
  obtain ⟨e, rfl, he⟩ := lv15_mobius_homeomorph hT
  exact ⟨e, hT, he, hTp⟩

/-- Helper (Tier B, B2). Any point `x` of `ℂ̄` is carried to any point `y` by a fractional linear transformation which
is a homeomorphism of `ℂ̄`. -/
theorem lv51_mobius_map (x y : ExtPlane) : ∃ M : ExtPlane ≃ₜ ExtPlane, LiZhongQC.IsMobius ⇑M ∧ M x = y := by
  obtain ⟨e₁, he₁, -, h₁⟩ := lv51_mobius_to_infty x
  obtain ⟨e₂, -, he₂, h₂⟩ := lv51_mobius_to_infty y
  refine ⟨e₁.trans e₂.symm, ?_, ?_⟩
  · show LiZhongQC.IsMobius (⇑e₂.symm ∘ ⇑e₁)
    exact lv15_isMobius_comp he₂ he₁
  · rw [Homeomorph.trans_apply, h₁, ← h₂, Homeomorph.symm_apply_apply]

/-- Helper (Tier B, B2). Let `G` be a simply connected domain whose complement contains two points `p ≠ q`, and `e` a
homeomorphism of `ℂ̄` carrying `p` to `∞`. Then `e(G)` is a domain `U` of the finite plane whose complement in `ℂ̄` is
connected and contains a finite point (`e(q)`). -/
theorem lv51_finite_model {G : Set ExtPlane} (hG : IsSimplyConnectedDomain G) {p q : ExtPlane} (hp : p ∉ G)
    (hq : q ∉ G) (hpq : p ≠ q) (e : ExtPlane ≃ₜ ExtPlane) (he : e p = LiZhongQC.extInf) :
    ∃ U : Set ℂ, IsOpen U ∧ IsConnected U ∧ IsConnected (LiZhongQC.toExt U)ᶜ ∧ Uᶜ.Nonempty ∧
      e '' G = LiZhongQC.toExt U := by
  have hinf : LiZhongQC.extInf ∉ e '' G := fun h => by
    rw [← he] at h
    exact hp (e.injective.mem_set_image.1 h)
  have heq : e '' G = LiZhongQC.toExt (finitePart (e '' G)) := by
    ext z
    constructor
    · intro hz
      have hz' : z ≠ LiZhongQC.extInf := by
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
  · have hq' : e q ≠ LiZhongQC.extInf := fun h => hpq (e.injective (by rw [he, h]))
    obtain ⟨a, ha⟩ := OnePoint.ne_infty_iff_exists.1 hq'
    refine ⟨a, fun h => hq ?_⟩
    have h' : (a : ExtPlane) ∈ e '' G := h
    rw [ha] at h'
    exact e.injective.mem_set_image.1 h'

/-- Helper (Tier B, B2). Two domains `U`, `V` of the finite plane whose complements in `ℂ̄` are connected and contain a
finite point are conformally equivalent: there is a holomorphic bijection of `V` onto `U` (the Riemann mapping theorem
`RMT.exists_riemannMap_of_hasHolomorphicSqrt` with the connected-complement bridge
`LiZhongQC.hasHolomorphicSqrt_of_isConnected_compl`, and `RMT.invFunOn_riemannMap`). -/
theorem lv51_riemann_equiv {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
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

/-- Helper (Tier B, B2). A holomorphic bijection `h` of a domain `V` of the finite plane onto `U`, read on `ℂ̄`, is a
conformal mapping of `V` onto `U`. -/
theorem lv51_isConformalMap_lift {h : ℂ → ℂ} {U V : Set ℂ} (hV : IsOpen V) (hVc : IsConnected V)
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

/-- **Mapping theorem** (Ch. V §1.3), existence part. Let `G` and `G′` be conformally equivalent simply connected
domains and `κ` a measurable function in `G` with `sup_z |κ(z)| < 1`. Then there exists a quasiconformal mapping
`w : G → G′` whose complex dilatation coincides with `κ` almost everywhere (in `G`).
Modelling: "conformally equivalent" is the existence of a conformal mapping of `G` onto `G′`; `w : G → G′` is a
quasiconformal mapping of `G` with `w(G) = G′`; `κ` and its bound as in `existence_theorem`. The uniqueness part of
the Mapping theorem is the Uniqueness theorem IV.5.2 (`uniqueness_theorem`; see the module docstring). -/
theorem mapping_theorem_i {G G' : Set ExtPlane} (hG : IsSimplyConnectedDomain G)
    (hG' : IsSimplyConnectedDomain G') (hequiv : ∃ φ : ExtPlane → ExtPlane, IsConformalMap φ G ∧ φ '' G = G')
    {κ : ℂ → ℂ} (hκm : AEStronglyMeasurable κ (volume.restrict (finitePart G)))
    (hκ : ∃ k : ℝ, k < 1 ∧ ∀ z ∈ finitePart G, ‖κ z‖ ≤ k) :
    ∃ w : ExtPlane → ExtPlane, IsQuasiconformalMap w G ∧ w '' G = G' ∧
      ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), complexDilatationLV w z = κ z := by
  have _ := hG'
  obtain ⟨φ, hφ, hφG⟩ := hequiv
  -- it suffices to find a quasiconformal mapping of `G` onto itself with complex dilatation `κ`
  suffices h : ∃ v : ExtPlane → ExtPlane, IsQuasiconformalMap v G ∧ v '' G = G ∧
      ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), complexDilatationLV v z = κ z by
    obtain ⟨v, hv, hvG, hvκ⟩ := h
    obtain ⟨h1, h2⟩ := lv51_comp_conformal (f := φ) hv hvκ (by rwa [hvG])
    exact ⟨φ ∘ v, h1, by rw [image_comp, hvG, hφG], h2⟩
  -- the global solution `E` of the Existence theorem; `E(G)` is again a domain
  obtain ⟨E, hE, hEκ⟩ := lv51_exists_global hG.1 hκm hκ
  have hEG : IsDomainExt (E '' G) := ⟨E.isOpenMap G hG.1.1, hG.1.2.image E E.continuous.continuousOn⟩
  rcases Gᶜ.eq_empty_or_nonempty with h0 | ⟨p, hp⟩
  · -- `G = ℂ̄`: `E` itself
    have hGu : G = univ := compl_empty_iff.1 h0
    refine ⟨E, hE, ?_, hEκ⟩
    rw [hGu, image_univ_of_surjective E.surjective]
  by_cases hs : Gᶜ.Subsingleton
  · -- `Gᶜ = {p}`: a fractional linear transformation carries `E(p)` back to `p`
    have hGp : G = {p}ᶜ := by rw [← hs.eq_singleton_of_mem hp, compl_compl]
    obtain ⟨M, hM, hpM⟩ := lv51_mobius_map (E p) p
    obtain ⟨h1, h2⟩ := lv51_comp_conformal hE hEκ (lv51_isConformalMap_mobius hM hEG)
    refine ⟨M ∘ E, h1, ?_, h2⟩
    rw [image_comp, hGp, image_compl_eq E.bijective, image_singleton, image_compl_eq M.bijective,
      image_singleton, hpM]
  -- two complementary points `p ≠ q`: Riemann maps of the finite models of `E(G)` and of `G`
  obtain ⟨p, hp, q, hq, hpq⟩ := not_subsingleton_iff.1 hs
  have hD : IsSimplyConnectedDomain (E '' G) :=
    ⟨hEG, by rw [← image_compl_eq E.bijective]; exact hG.2.image E E.continuous.continuousOn⟩
  obtain ⟨A, -, hAs, hAp⟩ := lv51_mobius_to_infty p
  obtain ⟨B, hB, -, hBp⟩ := lv51_mobius_to_infty (E p)
  obtain ⟨U, hUo, hUc, hUcc, hUne, hAG⟩ := lv51_finite_model hG hp hq hpq A hAp
  obtain ⟨V, hVo, hVc, hVcc, hVne, hBD⟩ := lv51_finite_model hD (fun h => hp (E.injective.mem_set_image.1 h))
    (fun h => hq (E.injective.mem_set_image.1 h)) (E.injective.ne hpq) B hBp
  obtain ⟨h, hhd, hhb⟩ := lv51_riemann_equiv hUo hUc hUcc hUne hVo hVc hVcc hVne
  obtain ⟨hH, hHV⟩ := lv51_isConformalMap_lift hVo hVc hhd hhb
  -- `v = A⁻¹ ∘ H ∘ B ∘ E`, a conformal mapping at each step after `E`
  obtain ⟨h1, h2⟩ := lv51_comp_conformal hE hEκ (lv51_isConformalMap_mobius hB hEG)
  have hi1 : (B ∘ E) '' G = LiZhongQC.toExt V := by rw [image_comp, hBD]
  obtain ⟨h3, h4⟩ := lv51_comp_conformal (f := fun z => ((h (finiteValue z) : ℂ) : ExtPlane)) h1 h2
    (by rw [hi1]; exact hH)
  have hi2 : ((fun z => ((h (finiteValue z) : ℂ) : ExtPlane)) ∘ B ∘ E) '' G = LiZhongQC.toExt U := by
    rw [image_comp, hi1, hHV]
  have hUd : IsDomainExt (LiZhongQC.toExt U) := by
    rw [← hAG]
    exact ⟨A.isOpenMap G hG.1.1, hG.1.2.image A A.continuous.continuousOn⟩
  obtain ⟨h5, h6⟩ := lv51_comp_conformal (f := ⇑A.symm) h3 h4
    (by rw [hi2]; exact lv51_isConformalMap_mobius hAs hUd)
  refine ⟨A.symm ∘ (fun z => ((h (finiteValue z) : ℂ) : ExtPlane)) ∘ B ∘ E, h5, ?_, h6⟩
  rw [image_comp, hi2, ← hAG, lv15_symm_image_image]

end LehtoVirtanen1973
