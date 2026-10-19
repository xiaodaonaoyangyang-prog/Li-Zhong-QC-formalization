import References.GarnettMarshall2005.Ch04.S02_UniquenessExtremalMetrics

/-!
# Garnett–Marshall, Chapter IV §3: Four rules for extremal length

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. IV §3 (pp. 134–139;
`full.md` P1:6016–6134).

Conventions of Chapter IV as in §1. By the extension rule (3.1) the extremal length of a path family does not depend
on the domain, and the book writes `λ(Γ)` for `λ_Ω(Γ)` (P1:6032); here `λ(Γ_j)` is written with the open set
`Ω_j` in which `Γ_j` is contained, and `λ(Γ)` with the domain `Ω`. `1/λ` is the inverse in `[0, ∞]`
(`1/0 = ∞`, `1/∞ = 0`). "`γ'` contains `γ`" is the inclusion of point sets `γ ⊆ γ'`.

* The extension rule ((3.1), (3.2), §3) — `eq4_3_1`, `eq4_3_2`
* Unlabelled (§3, P1:6032): `d_Ω(E, F)` decreases if any of `E`, `F`, `Ω` increases, and
  `d_Ω(E, F) = d_{Ω \ (E ∪ F)}(E, F)` when `E` and `F` are closed — `extremalDistGM_antitone`,
  `extremalDistGM_diff`
* The serial rule (§3) — `serial_rule`
* The parallel rule ((3.3), §3) — `parallel_rule`
* The symmetry rule ((3.4), §3) — `symmetry_rule`

Not stated (inventory U−): the notation `λ(Γ)` (P1:6032, explained above); the examples of Figures IV.3–IV.5
(P1:6037–6040, 6055–6058, 6078–6082; applications of the rules); the remark that the parallel-rule inequality of
Figure IV.5 also follows from the serial rule for conjugate extremal distances when (1.7) holds (P1:6084); the
formula (3.5) of the symmetry rule, `d_{Ω₁}(E₁, F₁) = ½ d_Ω(E, F)` (P1:6116–6128; recorded only, leader ruling
B12(7): as printed the hypothesis `Ω₁ ⊃ Ω ∪ T(Ω)` is too weak, the argument needs `Ω₁ ∩ ℍ = Ω`, and later uses cite
"the symmetry rule"); the electrical-resistance analogy (P1:6133).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (densitiesP0 rhoArea)

/-! ### GM4-A helpers (-d9): the extension rule, sub-arcs, the serial and parallel rules -/

/-- Helper: a curve of a path family in `Ω` lies in `Ω`. -/
theorem gm4a_isPathCurve_subset {Ω γ : Set ℂ} (hγ : IsPathCurve Ω γ) : γ ⊆ Ω := by
  obtain ⟨s, hs, rfl⟩ := hγ
  exact iUnion_subset fun n => (hs n).2

/-- Helper: a curve in `Ω` is a curve in every larger set. -/
theorem gm4a_isPathCurve_mono {Ω Ω' γ : Set ℂ} (h : Ω ⊆ Ω') (hγ : IsPathCurve Ω γ) : IsPathCurve Ω' γ := by
  obtain ⟨s, hs, rfl⟩ := hγ
  exact ⟨s, fun n => ⟨(hs n).1, (hs n).2.trans h⟩, rfl⟩

/-- Helper: the set carrying a path family is non-empty. -/
theorem gm4a_nonempty_of_isPathFamily {Ω : Set ℂ} {Γ : Set (Set ℂ)} (hΓ : IsPathFamily Ω Γ) : Ω.Nonempty := by
  obtain ⟨⟨γ, hγ⟩, hΓ⟩ := hΓ
  obtain ⟨s, hs, rfl⟩ := hΓ γ hγ
  obtain ⟨⟨hJ, -⟩, -⟩ := hs 0
  obtain ⟨I, -, hI, g, -, hg⟩ := hJ
  obtain ⟨t, ht⟩ := hI.nonempty
  have hmem : g t ∈ LiZhongQC.toExt (s 0) := hg ▸ mem_image_of_mem g ht
  obtain ⟨z, hz, -⟩ := hmem
  exact ⟨z, (hs 0).2 hz⟩

/-- Helper: the area of the indicator of a disc `B ⊆ D` is `|B|`. -/
theorem gm4a_rhoArea_ball_indicator {D : Set ℂ} {x : ℂ} {ε : ℝ} (hB : ball x ε ⊆ D) :
    rhoArea ((ball x ε).indicator 1) D = volume (ball x ε) := by
  rw [gm4a_rhoArea_eq]
  have h : (fun z => (ball x ε).indicator (1 : ℂ → ℝ≥0∞) z ^ 2) = (ball x ε).indicator 1 := by
    funext z
    by_cases hz : z ∈ ball x ε <;> simp [hz]
  rw [h, lintegral_indicator_one measurableSet_ball, Measure.restrict_apply measurableSet_ball,
    inter_eq_left.2 hB]

/-- Helper: a non-empty open set carries a metric. -/
theorem gm4a_densitiesP0_nonempty {D : Set ℂ} (hD : IsOpen D) (hne : D.Nonempty) : ∃ ρ, ρ ∈ densitiesP0 D := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.1 hD x hx
  have hA := gm4a_rhoArea_ball_indicator hB
  exact ⟨(ball x ε).indicator 1, gm4a_mem_densitiesP0.2 ⟨measurable_one.indicator measurableSet_ball,
    hA ▸ measure_ball_pos volume x hε, hA ▸ measure_ball_lt_top⟩⟩

/-- Helper: a larger family has a smaller extremal length. -/
theorem gm4a_extremalLength_anti {D : Set ℂ} {Γ Γ' : Set (Set ℂ)} (h : Γ ⊆ Γ') :
    extremalLengthGM D Γ' ≤ extremalLengthGM D Γ := by
  rw [gm4a_extremalLengthGM_eq, gm4a_extremalLengthGM_eq]
  refine iSup₂_mono fun ρ _ => ?_
  gcongr
  exact gm4a_pathRhoLength_le_of_contains ρ fun γ hγ => ⟨γ, h hγ, subset_rfl⟩

/-- Helper: the extension by `0` of a metric on an open set `D ⊆ D'` is a metric on `D'`, with the same area. -/
theorem gm4a_indicator_mem {D D' : Set ℂ} (hD : IsOpen D) (hDD' : D ⊆ D') {ρ : ℂ → ℝ≥0∞}
    (hρ : ρ ∈ densitiesP0 D) : D.indicator ρ ∈ densitiesP0 D' ∧ rhoArea (D.indicator ρ) D' = rhoArea ρ D := by
  obtain ⟨hm, h0, htop⟩ := gm4a_mem_densitiesP0.1 hρ
  have hA : rhoArea (D.indicator ρ) D' = rhoArea ρ D := by
    rw [gm4a_rhoArea_eq, gm4a_rhoArea_eq]
    have h : (fun z => D.indicator ρ z ^ 2) = D.indicator (fun z => ρ z ^ 2) := by
      funext z
      by_cases hz : z ∈ D <;> simp [hz]
    rw [h, lintegral_indicator hD.measurableSet, Measure.restrict_restrict hD.measurableSet,
      inter_eq_left.2 hDD']
  exact ⟨gm4a_mem_densitiesP0.2 ⟨hm.indicator hD.measurableSet, hA ▸ h0, hA ▸ htop⟩, hA⟩

/-- Helper: on a family of curves in `D`, the extension by `0` has the same `ρ`-length. -/
theorem gm4a_pathRhoLength_indicator {D : Set ℂ} (hD : MeasurableSet D) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ)
    {Γ : Set (Set ℂ)} (hΓ : ∀ γ ∈ Γ, γ ⊆ D) : pathRhoLength Γ (D.indicator ρ) = pathRhoLength Γ ρ := by
  apply le_antisymm
  · exact gm4a_pathRhoLength_mono (hρ.indicator hD) hρ fun γ _ z _ => indicator_le_self _ _ z
  · exact gm4a_pathRhoLength_mono hρ (hρ.indicator hD) fun γ hγ z hz => by rw [indicator_of_mem (hΓ γ hγ hz)]

/-- Helper (zero area): if `A(D, ρ) = 0` but `L(Γ, ρ) > 0`, then `λ_D(Γ) = ∞`: the metric `∞ · ρ + 1_B`, `B ⊆ D` a
disc, has area `|B|` on `D` and infinite length. -/
theorem gm4a_extremalLength_eq_top {D : Set ℂ} (hD : IsOpen D) (hne : D.Nonempty) {Γ : Set (Set ℂ)}
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) (h0 : rhoArea ρ D = 0) (hL : 0 < pathRhoLength Γ ρ) :
    extremalLengthGM D Γ = ⊤ := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.1 hD x hx
  have hm : Measurable fun z => ⊤ * ρ z + (ball x ε).indicator 1 z :=
    (hρ.const_mul ⊤).add (measurable_one.indicator measurableSet_ball)
  have hρ0 : ∀ᵐ z ∂(volume.restrict D), ρ z = 0 := by
    rw [gm4a_rhoArea_eq] at h0
    filter_upwards [(lintegral_eq_zero_iff (hρ.pow_const 2)).1 h0] with z hz
    simpa using hz
  have hA : rhoArea (fun z => ⊤ * ρ z + (ball x ε).indicator 1 z) D = volume (ball x ε) := by
    rw [← gm4a_rhoArea_ball_indicator hB, gm4a_rhoArea_eq, gm4a_rhoArea_eq]
    refine lintegral_congr_ae ?_
    filter_upwards [hρ0] with z hz
    rw [hz, mul_zero, zero_add]
  have hmem : (fun z => ⊤ * ρ z + (ball x ε).indicator 1 z) ∈ densitiesP0 D :=
    gm4a_mem_densitiesP0.2 ⟨hm, hA ▸ measure_ball_pos volume x hε, hA ▸ measure_ball_lt_top⟩
  have hL' : pathRhoLength Γ (fun z => ⊤ * ρ z + (ball x ε).indicator 1 z) = ⊤ := by
    refine eq_top_iff.2 ?_
    calc ⊤ = ⊤ * pathRhoLength Γ ρ := (ENNReal.top_mul hL.ne').symm
      _ ≤ pathRhoLength Γ (fun z => ⊤ * ρ z) := gm4a_const_mul_pathRhoLength_le hρ ⊤
      _ ≤ _ := gm4a_pathRhoLength_mono (hρ.const_mul ⊤) hm fun γ _ z _ => le_self_add
  refine eq_top_iff.2 ?_
  calc ⊤ = pathRhoLength Γ (fun z => ⊤ * ρ z + (ball x ε).indicator 1 z) ^ 2 /
        rhoArea (fun z => ⊤ * ρ z + (ball x ε).indicator 1 z) D := by
        rw [hL', hA, ENNReal.top_pow two_ne_zero, ENNReal.top_div_of_ne_top measure_ball_lt_top.ne]
    _ ≤ extremalLengthGM D Γ := gm4a_ratio_le hmem

/-- Helper (the extension rule, one half): for a non-empty open `Ω ⊆ Ω'`, `λ_{Ω'}(Γ) ≤ λ_Ω(Γ)` for every family. -/
theorem gm4a_extremalLength_le_of_subset {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hΩΩ' : Ω ⊆ Ω')
    (Γ : Set (Set ℂ)) : extremalLengthGM Ω' Γ ≤ extremalLengthGM Ω Γ := by
  rw [gm4a_extremalLengthGM_eq Ω' Γ]
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨hm, -, htop'⟩ := gm4a_mem_densitiesP0.1 hρ
  have hle : rhoArea ρ Ω ≤ rhoArea ρ Ω' := by
    rw [gm4a_rhoArea_eq, gm4a_rhoArea_eq]
    exact lintegral_mono_set hΩΩ'
  rcases eq_or_ne (rhoArea ρ Ω) 0 with h0 | h0
  · rcases eq_or_ne (pathRhoLength Γ ρ) 0 with hL | hL
    · rw [hL]
      simp
    · rw [gm4a_extremalLength_eq_top hΩ hne hm h0 (pos_iff_ne_zero.2 hL)]
      exact le_top
  · have hmem : ρ ∈ densitiesP0 Ω := gm4a_mem_densitiesP0.2 ⟨hm, pos_iff_ne_zero.2 h0, hle.trans_lt htop'⟩
    exact (ENNReal.div_le_div_left hle _).trans (gm4a_ratio_le hmem)

/-- Helper (the extension rule (3.2) for open sets): `λ_Ω(Γ) ≤ λ_{Ω'}(Γ')` when the curves of `Γ` lie in the open
set `Ω ⊆ Ω'` and every curve of `Γ'` contains one of `Γ`. -/
theorem gm4a_extremalLength_le_of_contains {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω) (hΩΩ' : Ω ⊆ Ω') {Γ Γ' : Set (Set ℂ)}
    (hΓ : ∀ γ ∈ Γ, γ ⊆ Ω) (hΓΓ' : ∀ γ' ∈ Γ', ∃ γ ∈ Γ, γ ⊆ γ') :
    extremalLengthGM Ω Γ ≤ extremalLengthGM Ω' Γ' := by
  rw [gm4a_extremalLengthGM_eq Ω Γ]
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨hmem, hA⟩ := gm4a_indicator_mem hΩ hΩΩ' hρ
  have hL : pathRhoLength Γ ρ ≤ pathRhoLength Γ' (Ω.indicator ρ) := by
    rw [← gm4a_pathRhoLength_indicator hΩ.measurableSet (gm4a_mem_densitiesP0.1 hρ).1 hΓ]
    exact gm4a_pathRhoLength_le_of_contains _ hΓΓ'
  calc pathRhoLength Γ ρ ^ 2 / rhoArea ρ Ω ≤
        pathRhoLength Γ' (Ω.indicator ρ) ^ 2 / rhoArea (Ω.indicator ρ) Ω' := by
        rw [hA]
        gcongr
    _ ≤ extremalLengthGM Ω' Γ' := gm4a_ratio_le hmem

/-- Helper: a curve of `joiningFamily Ω E F` is a curve in `Ω`. -/
theorem gm4a_joiningFamily_isPathCurve {Ω E F γ : Set ℂ} (hγ : γ ∈ joiningFamily Ω E F) : IsPathCurve Ω γ := by
  exact (show IsPathCurve Ω γ ∧ _ from hγ).1

/-- Helper: `joiningFamily Ω E F` grows with `Ω`, `E` and `F`. -/
theorem gm4a_joiningFamily_mono {Ω Ω' E E' F F' : Set ℂ} (hΩ : Ω ⊆ Ω') (hE : E ⊆ E') (hF : F ⊆ F') :
    joiningFamily Ω E F ⊆ joiningFamily Ω' E' F' := by
  intro γ hγ
  obtain ⟨hc, f, hf, hinj, h0, h1, rfl⟩ := hγ
  exact ⟨gm4a_isPathCurve_mono hΩ hc, f, hf, hinj, hE h0, hF h1, rfl⟩

/-- Helper: `Ω \ (E ∪ F)` is non-empty for a domain `Ω` and disjoint non-empty closed sets `E, F ⊆ Ω̄`. -/
theorem gm4a_diff_nonempty {Ω E F : Set ℂ} (hΩ : IsOpen Ω ∧ IsConnected Ω) (hE : IsClosed E) (hF : IsClosed F)
    (hEΩ : E ⊆ closure Ω) (hFΩ : F ⊆ closure Ω) (hdisj : Disjoint E F) (hEne : E.Nonempty) (hFne : F.Nonempty) :
    (Ω \ (E ∪ F)).Nonempty := by
  by_contra hcon
  rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hcon
  have hEF : Ω ∩ (E ∩ F) = ∅ := by rw [hdisj.inter_eq, inter_empty]
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 hΩ.2.isPreconnected E F hE hF hcon hEF with h | h
  · obtain ⟨y, hy⟩ := hFne
    exact disjoint_left.1 hdisj ((hE.closure_subset_iff.2 h) (hFΩ hy)) hy
  · obtain ⟨y, hy⟩ := hEne
    exact disjoint_left.1 hdisj hy ((hF.closure_subset_iff.2 h) (hEΩ hy))

/-- Helper (last exit, first hit): for `f` continuous on `[0, 1]` with `f(0) ∈ E` and `f(1) ∈ F` (`E`, `F` closed and
disjoint) there are `0 ≤ s < t ≤ 1` with `f(s) ∈ E`, `f(t) ∈ F` and `f(u) ∉ E ∪ F` for `s < u < t`. -/
theorem gm4a_last_exit_first_hit {E F : Set ℂ} (hE : IsClosed E) (hF : IsClosed F) (hdisj : Disjoint E F)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 1)) (h0 : f 0 ∈ E) (h1 : f 1 ∈ F) :
    ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧ f s ∈ E ∧ f t ∈ F ∧ ∀ u ∈ Ioo s t, f u ∉ E ∧ f u ∉ F := by
  have hSEc : IsClosed (Icc (0 : ℝ) 1 ∩ f ⁻¹' E) := hf.preimage_isClosed_of_isClosed isClosed_Icc hE
  have hSEne : (Icc (0 : ℝ) 1 ∩ f ⁻¹' E).Nonempty := ⟨0, left_mem_Icc.2 zero_le_one, h0⟩
  have hSEbdd : BddAbove (Icc (0 : ℝ) 1 ∩ f ⁻¹' E) := bddAbove_Icc.mono inter_subset_left
  have hsSE := hSEc.csSup_mem hSEne hSEbdd
  set s := sSup (Icc (0 : ℝ) 1 ∩ f ⁻¹' E) with hs
  have hs1 : s < 1 := by
    refine lt_of_le_of_ne hsSE.1.2 fun h => ?_
    have hfs : f s ∈ E := hsSE.2
    rw [h] at hfs
    exact disjoint_left.1 hdisj hfs h1
  have hSFc : IsClosed (Icc s 1 ∩ f ⁻¹' F) :=
    (hf.mono (Icc_subset_Icc hsSE.1.1 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc hF
  have hSFne : (Icc s 1 ∩ f ⁻¹' F).Nonempty := ⟨1, ⟨hs1.le, le_rfl⟩, h1⟩
  have hSFbdd : BddBelow (Icc s 1 ∩ f ⁻¹' F) := bddBelow_Icc.mono inter_subset_left
  have htSF := hSFc.csInf_mem hSFne hSFbdd
  set t := sInf (Icc s 1 ∩ f ⁻¹' F) with ht
  have hst : s < t := by
    refine lt_of_le_of_ne htSF.1.1 fun h => ?_
    have hft : f t ∈ F := htSF.2
    rw [← h] at hft
    exact disjoint_left.1 hdisj hsSE.2 hft
  refine ⟨s, t, hsSE.1.1, hst, htSF.1.2, hsSE.2, htSF.2, fun u hu => ⟨fun huE => ?_, fun huF => ?_⟩⟩
  · have hle : u ≤ s := le_csSup hSEbdd ⟨⟨hsSE.1.1.trans hu.1.le, hu.2.le.trans htSF.1.2⟩, huE⟩
    exact (not_le.2 hu.1) hle
  · have hle : t ≤ u := csInf_le hSFbdd ⟨⟨hu.1.le, hu.2.le.trans htSF.1.2⟩, huF⟩
    exact (not_le.2 hu.2) hle

/-- Helper: `f` continuous and one-to-one on `[0, 1]` restricts to an embedding of `[0, 1]`. -/
theorem gm4a_restrict_isEmbedding {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 1)) (hinj : InjOn f (Icc 0 1)) :
    IsEmbedding ((Icc (0 : ℝ) 1).domRestrict f) := by
  have _ : CompactSpace (Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.1 isCompact_Icc
  exact ((continuousOn_iff_continuous_domRestrict.1 hf).isClosedEmbedding hinj.injective).isEmbedding

/-- Helper: for a Jordan arc `C ⊆ f((0, 1))`, the parameters `{u ∈ [0, 1] | f(u) ∈ C}` form an interval. -/
theorem gm4a_preimage_ordConnected {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 1)) (hinj : InjOn f (Icc 0 1))
    {C : Set ℂ} (hC : LehtoVirtanen1973.IsJordanArc (LiZhongQC.toExt C)) (hCγ : C ⊆ f '' Ioo 0 1) :
    (Icc (0 : ℝ) 1 ∩ f ⁻¹' C).OrdConnected := by
  obtain ⟨I, hI, -, g, hg, hgI⟩ := hC
  have hpre : IsPreconnected (LiZhongQC.toExt C) := by
    rw [← hgI]
    exact hI.isPreconnected.image g (continuousOn_iff_continuous_domRestrict.2 hg.continuous)
  have hCpre : IsPreconnected C := (OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image).1 hpre
  have hemb := gm4a_restrict_isEmbedding hf hinj
  have hrange : C ⊆ range ((Icc (0 : ℝ) 1).domRestrict f) := fun x hx => by
    obtain ⟨u, hu, rfl⟩ := hCγ hx
    exact ⟨⟨u, Ioo_subset_Icc_self hu⟩, rfl⟩
  have himg : (Icc (0 : ℝ) 1).domRestrict f '' ((Icc (0 : ℝ) 1).domRestrict f ⁻¹' C) = C :=
    image_preimage_eq_of_subset hrange
  have hK : IsPreconnected ((Icc (0 : ℝ) 1).domRestrict f ⁻¹' C) := by
    rw [← hemb.isInducing.isPreconnected_image, himg]
    exact hCpre
  have hK' := hK.image ((↑) : Icc (0 : ℝ) 1 → ℝ) continuous_subtype_val.continuousOn
  have heq : ((↑) : Icc (0 : ℝ) 1 → ℝ) '' ((Icc (0 : ℝ) 1).domRestrict f ⁻¹' C) = Icc 0 1 ∩ f ⁻¹' C := by
    ext u
    constructor
    · rintro ⟨⟨u, hu⟩, hC, rfl⟩
      exact ⟨hu, hC⟩
    · rintro ⟨hu, hC⟩
      exact ⟨⟨u, hu⟩, hC, rfl⟩
  rw [heq] at hK'
  exact isPreconnected_iff_ordConnected.1 hK'

/-- Helper: for a Jordan arc `C ⊆ f((0, 1))` (`f` one-to-one on `[0, 1]`), `{u ∈ [0, 1] | f(u) ∈ C}` has two
points. -/
theorem gm4a_preimage_nontrivial {f : ℝ → ℂ} {C : Set ℂ} (hC : LehtoVirtanen1973.IsJordanArc (LiZhongQC.toExt C))
    (hCγ : C ⊆ f '' Ioo 0 1) : (Icc (0 : ℝ) 1 ∩ f ⁻¹' C).Nontrivial := by
  obtain ⟨I, -, hInt, g, hg, hgI⟩ := hC
  obtain ⟨s, hs, t, ht, hst⟩ := hInt
  have hgs : g s ∈ LiZhongQC.toExt C := hgI ▸ mem_image_of_mem g hs
  have hgt : g t ∈ LiZhongQC.toExt C := hgI ▸ mem_image_of_mem g ht
  obtain ⟨x, hx, hxs⟩ := hgs
  obtain ⟨y, hy, hyt⟩ := hgt
  have hxy : x ≠ y := by
    intro h
    apply hst
    have h' : I.domRestrict g ⟨s, hs⟩ = I.domRestrict g ⟨t, ht⟩ := by
      show g s = g t
      rw [← hxs, ← hyt, h]
    exact congrArg Subtype.val (hg.injective h')
  obtain ⟨u, hu, rfl⟩ := hCγ hx
  obtain ⟨v, hv, rfl⟩ := hCγ hy
  exact ⟨u, ⟨Ioo_subset_Icc_self hu, hx⟩, v, ⟨Ioo_subset_Icc_self hv, hy⟩, fun h => hxy (h ▸ rfl)⟩

/-- Helper: a non-trivial interval meeting the open interval `(a, b)` meets it in a non-trivial set. -/
theorem gm4a_nontrivial_inter {K : Set ℝ} (hK : K.OrdConnected) (hKnt : K.Nontrivial) {a b : ℝ}
    (hne : (K ∩ Ioo a b).Nonempty) : (K ∩ Ioo a b).Nontrivial := by
  obtain ⟨u, huK, hu⟩ := hne
  obtain ⟨v, hvK, hvu⟩ := hKnt.exists_ne u
  rcases lt_or_gt_of_ne hvu with h | h
  · have h1 := le_max_left v a
    have h2 := le_max_right v a
    have h3 : max v a < u := max_lt h hu.1
    refine ⟨u, ⟨huK, hu⟩, (max v a + u) / 2, ⟨hK.out hvK huK ⟨by linarith, by linarith⟩, by linarith,
      by linarith [hu.2]⟩, by intro h; linarith⟩
  · have h1 := min_le_left v b
    have h2 := min_le_right v b
    have h3 : u < min v b := lt_min h hu.2
    refine ⟨u, ⟨huK, hu⟩, (u + min v b) / 2, ⟨hK.out huK hvK ⟨by linarith, by linarith⟩, by linarith [hu.1],
      by linarith⟩, by intro h; linarith⟩

/-- Helper: a non-empty piece `C ∩ f((a, b))` of a rectifiable arc `C ⊆ f((0, 1))` (`f` continuous and one-to-one on
`[0, 1]`, `0 ≤ a < b ≤ 1`) is a rectifiable arc. -/
theorem gm4a_piece_isRectifiableArc {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 1)) (hinj : InjOn f (Icc 0 1))
    {C : Set ℂ} (hC : LehtoVirtanen1973.IsRectifiableArc C) (hCγ : C ⊆ f '' Ioo 0 1) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hne : (C ∩ f '' Ioo a b).Nonempty) : LehtoVirtanen1973.IsRectifiableArc (C ∩ f '' Ioo a b) := by
  obtain ⟨hJC, hfin⟩ := hC
  refine ⟨?_, (measure_mono inter_subset_left).trans_lt hfin⟩
  have hK := gm4a_preimage_ordConnected hf hinj hJC hCγ
  have hKnt := gm4a_preimage_nontrivial hJC hCγ
  have hsub : Ioo a b ⊆ Icc 0 1 := fun u hu => ⟨ha.trans hu.1.le, hu.2.le.trans hb⟩
  have hJeq : Ioo a b ∩ f ⁻¹' C = (Icc 0 1 ∩ f ⁻¹' C) ∩ Ioo a b := by
    ext u
    constructor
    · rintro ⟨hu, hC⟩
      exact ⟨⟨hsub hu, hC⟩, hu⟩
    · rintro ⟨⟨-, hC⟩, hu⟩
      exact ⟨hu, hC⟩
  have himg : f '' (Ioo a b ∩ f ⁻¹' C) = C ∩ f '' Ioo a b := by
    ext x
    constructor
    · rintro ⟨u, ⟨hu, hC⟩, rfl⟩
      exact ⟨hC, u, hu, rfl⟩
    · rintro ⟨hC, u, hu, rfl⟩
      exact ⟨u, ⟨hu, hC⟩, rfl⟩
  have hJne : ((Icc 0 1 ∩ f ⁻¹' C) ∩ Ioo a b).Nonempty := by
    obtain ⟨x, hxC, u, hu, rfl⟩ := hne
    exact ⟨u, ⟨hsub hu, hxC⟩, hu⟩
  have hJsub : Ioo a b ∩ f ⁻¹' C ⊆ Icc 0 1 := fun u hu => hsub hu.1
  refine ⟨Ioo a b ∩ f ⁻¹' C, hJeq ▸ hK.inter ordConnected_Ioo, hJeq ▸ gm4a_nontrivial_inter hK hKnt hJne,
    (↑) ∘ f, ?_, ?_⟩
  · have h : (Ioo a b ∩ f ⁻¹' C).domRestrict (((↑) : ℂ → LiZhongQC.ExtPlane) ∘ f) =
        ((↑) : ℂ → LiZhongQC.ExtPlane) ∘ (Icc (0 : ℝ) 1).domRestrict f ∘ inclusion hJsub := rfl
    rw [h]
    exact OnePoint.isOpenEmbedding_coe.isEmbedding.comp
      ((gm4a_restrict_isEmbedding hf hinj).comp (IsEmbedding.inclusion hJsub))
  · rw [image_comp, himg]
    rfl

/-- Helper (sub-arcs): an open sub-arc `f((a, b))` of a curve `f((0, 1))` (`f` continuous and one-to-one on
`[0, 1]`) which lies in `Ω₀` is a curve in `Ω₀`: its pieces `sₙ ∩ f((a, b))` are rectifiable arcs or empty. -/
theorem gm4a_isPathCurve_subarc {Ω Ω₀ : Set ℂ} {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 1))
    (hinj : InjOn f (Icc 0 1)) (hγ : IsPathCurve Ω (f '' Ioo 0 1)) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) (hΩ₀ : f '' Ioo a b ⊆ Ω₀) : IsPathCurve Ω₀ (f '' Ioo a b) := by
  obtain ⟨S, hS, hγeq⟩ := hγ
  have hab' : Ioo a b ⊆ Ioo 0 1 := Ioo_subset_Ioo ha hb
  have hpiece : ∀ n, (S n ∩ f '' Ioo a b).Nonempty →
      LehtoVirtanen1973.IsRectifiableArc (S n ∩ f '' Ioo a b) := fun n hne =>
    gm4a_piece_isRectifiableArc hf hinj (hS n).1 ((subset_iUnion S n).trans hγeq.symm.subset) ha hb hne
  obtain ⟨x₀, hx₀⟩ : (f '' Ioo a b).Nonempty := (nonempty_Ioo.2 hab).image f
  obtain ⟨n₀, hn₀⟩ := mem_iUnion.1 (hγeq.subset (image_mono hab' hx₀))
  have hne₀ : (S n₀ ∩ f '' Ioo a b).Nonempty := ⟨x₀, hn₀, hx₀⟩
  classical
  refine ⟨fun n => if (S n ∩ f '' Ioo a b).Nonempty then S n ∩ f '' Ioo a b else S n₀ ∩ f '' Ioo a b,
    fun n => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · exact ⟨hpiece n h, inter_subset_right.trans hΩ₀⟩
    · exact ⟨hpiece n₀ hne₀, inter_subset_right.trans hΩ₀⟩
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.1 (hγeq.subset (image_mono hab' hx))
      have h : (S n ∩ f '' Ioo a b).Nonempty := ⟨x, hn, hx⟩
      refine mem_iUnion.2 ⟨n, ?_⟩
      simp only [h, ↓reduceIte]
      exact ⟨hn, hx⟩
    · refine iUnion_subset fun n => ?_
      split_ifs
      · exact inter_subset_right
      · exact inter_subset_right

/-- Helper: every arc joining `E` and `F` in `Ω` contains an arc joining them in `Ω \ (E ∪ F)` (`E`, `F` closed and
disjoint): the last-exit/first-hit sub-arc, reparametrized over `[0, 1]`. -/
theorem gm4a_joining_subarc {Ω E F : Set ℂ} (hE : IsClosed E) (hF : IsClosed F) (hdisj : Disjoint E F)
    {γ : Set ℂ} (hγ : γ ∈ joiningFamily Ω E F) : ∃ γ₀ ∈ joiningFamily (Ω \ (E ∪ F)) E F, γ₀ ⊆ γ := by
  obtain ⟨hc, f, hf, hinj, h0, h1, rfl⟩ := hγ
  obtain ⟨s, t, hs0, hst, ht1, hsE, htF, hmid⟩ := gm4a_last_exit_first_hit hE hF hdisj hf h0 h1
  have hts : 0 < t - s := sub_pos.2 hst
  have hmaps : MapsTo (fun u : ℝ => s + u * (t - s)) (Icc 0 1) (Icc 0 1) := by
    intro u hu
    constructor <;> nlinarith [hu.1, hu.2]
  have himg : (fun u : ℝ => s + u * (t - s)) '' Ioo 0 1 = Ioo s t := by
    rw [show (fun u : ℝ => s + u * (t - s)) = (fun x => s + x) ∘ (fun u => u * (t - s)) from rfl, image_comp,
      image_mul_right_Ioo _ _ hts, image_const_add_Ioo]
    simp
  have hsub : f '' Ioo s t ⊆ Ω \ (E ∪ F) := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨gm4a_isPathCurve_subset hc ⟨u, ⟨hs0.trans_lt hu.1, hu.2.trans_le ht1⟩, rfl⟩, ?_⟩
    rintro (h | h)
    · exact (hmid u hu).1 h
    · exact (hmid u hu).2 h
  refine ⟨f '' Ioo s t, ⟨gm4a_isPathCurve_subarc hf hinj hc hs0 hst ht1 hsub, fun u => f (s + u * (t - s)),
    hf.comp (by fun_prop) hmaps, ?_, by simpa using hsE, by simpa using htF, ?_⟩,
    image_mono (Ioo_subset_Ioo hs0 ht1)⟩
  · intro u hu v hv huv
    have h := hinj (hmaps hu) (hmaps hv) huv
    have h' : u * (t - s) = v * (t - s) := by linarith
    exact mul_right_cancel₀ hts.ne' h'
  · rw [← himg, image_image]

/-- Helper: the area of `1_{Ω₁} f + 1_{Ω₂} g` over `Ω ⊇ Ω₁ ∪ Ω₂` (`Ω₁`, `Ω₂` disjoint) is `A(Ω₁, f) + A(Ω₂, g)`. -/
theorem gm4a_rhoArea_two_indicators {Ω₁ Ω₂ Ω : Set ℂ} (hΩ₁ : MeasurableSet Ω₁) (hΩ₂ : MeasurableSet Ω₂)
    (hdisj : Disjoint Ω₁ Ω₂) (hΩ₁₂ : Ω₁ ∪ Ω₂ ⊆ Ω) {f g : ℂ → ℝ≥0∞} (hf : Measurable f) :
    rhoArea (fun z => Ω₁.indicator f z + Ω₂.indicator g z) Ω = rhoArea f Ω₁ + rhoArea g Ω₂ := by
  rw [gm4a_rhoArea_eq, gm4a_rhoArea_eq, gm4a_rhoArea_eq]
  have hpt : (fun z => (Ω₁.indicator f z + Ω₂.indicator g z) ^ 2) =
      fun z => Ω₁.indicator (fun z => f z ^ 2) z + Ω₂.indicator (fun z => g z ^ 2) z := by
    funext z
    by_cases h₁ : z ∈ Ω₁
    · have h₂ : z ∉ Ω₂ := disjoint_left.1 hdisj h₁
      simp [h₁, h₂]
    · by_cases h₂ : z ∈ Ω₂ <;> simp [h₁, h₂]
  rw [hpt, lintegral_add_left ((hf.pow_const 2).indicator hΩ₁), lintegral_indicator hΩ₁, lintegral_indicator hΩ₂,
    Measure.restrict_restrict hΩ₁, Measure.restrict_restrict hΩ₂,
    inter_eq_left.2 (subset_union_left.trans hΩ₁₂), inter_eq_left.2 (subset_union_right.trans hΩ₁₂)]

/-- Helper (arithmetic): with `sⱼ = Lⱼ/Aⱼ`, `(s₁L₁ + s₂L₂)²/(s₁²A₁ + s₂²A₂) = L₁²/A₁ + L₂²/A₂` (finite `Lⱼ`,
`0 < Aⱼ < ∞`). -/
theorem gm4a_serial_arith {L₁ L₂ A₁ A₂ : ℝ≥0∞} (hA₁ : A₁ ≠ 0) (hA₁' : A₁ ≠ ⊤) (hA₂ : A₂ ≠ 0) (hA₂' : A₂ ≠ ⊤)
    (hL₁ : L₁ ≠ ⊤) (hL₂ : L₂ ≠ ⊤) :
    (L₁ / A₁ * L₁ + L₂ / A₂ * L₂) ^ 2 / ((L₁ / A₁) ^ 2 * A₁ + (L₂ / A₂) ^ 2 * A₂) =
      L₁ ^ 2 / A₁ + L₂ ^ 2 / A₂ := by
  have e1 : ∀ {L A : ℝ≥0∞}, L / A * L = L ^ 2 / A := fun {L A} => by
    simp only [div_eq_mul_inv]
    ring
  have e2 : ∀ {L A : ℝ≥0∞}, A ≠ 0 → A ≠ ⊤ → (L / A) ^ 2 * A = L ^ 2 / A := fun {L A} h0 ht => by
    calc (L / A) ^ 2 * A = L ^ 2 * A⁻¹ * (A⁻¹ * A) := by simp only [div_eq_mul_inv]; ring
      _ = L ^ 2 / A := by rw [ENNReal.inv_mul_cancel h0 ht, mul_one, div_eq_mul_inv]
  rw [e1, e1, e2 hA₁ hA₁', e2 hA₂ hA₂']
  have hfin : L₁ ^ 2 / A₁ + L₂ ^ 2 / A₂ ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top (ENNReal.pow_ne_top hL₁) hA₁,
      ENNReal.div_ne_top (ENNReal.pow_ne_top hL₂) hA₂⟩
  rcases eq_or_ne (L₁ ^ 2 / A₁ + L₂ ^ 2 / A₂) 0 with h0 | h0
  · rw [h0]
    simp
  · rw [sq, ENNReal.mul_div_cancel_right h0 hfin]

/-- Helper (the serial rule for one pair of metrics): `L²(Γ₁, ρ₁)/A(Ω₁, ρ₁) + L²(Γ₂, ρ₂)/A(Ω₂, ρ₂) ≤ λ_Ω(Γ)`,
through the metric `s₁ρ₁1_{Ω₁} + s₂ρ₂1_{Ω₂}`, `sⱼ = L(Γⱼ, ρⱼ)/A(Ωⱼ, ρⱼ)`. -/
theorem gm4a_serial_pair {Ω₁ Ω₂ Ω : Set ℂ} (hΩ₁ : IsOpen Ω₁) (hΩ₂ : IsOpen Ω₂) (hdisj : Disjoint Ω₁ Ω₂)
    (hΩ₁₂ : Ω₁ ∪ Ω₂ ⊆ Ω) {Γ₁ Γ₂ Γ : Set (Set ℂ)} (hΓ₁ : ∀ γ ∈ Γ₁, γ ⊆ Ω₁) (hΓ₂ : ∀ γ ∈ Γ₂, γ ⊆ Ω₂)
    (hcont : ∀ γ ∈ Γ, (∃ γ₁ ∈ Γ₁, γ₁ ⊆ γ) ∧ ∃ γ₂ ∈ Γ₂, γ₂ ⊆ γ) {ρ₁ ρ₂ : ℂ → ℝ≥0∞}
    (hρ₁ : ρ₁ ∈ densitiesP0 Ω₁) (hρ₂ : ρ₂ ∈ densitiesP0 Ω₂) :
    pathRhoLength Γ₁ ρ₁ ^ 2 / rhoArea ρ₁ Ω₁ + pathRhoLength Γ₂ ρ₂ ^ 2 / rhoArea ρ₂ Ω₂ ≤ extremalLengthGM Ω Γ := by
  obtain ⟨hm₁, hA₁0, hA₁t⟩ := gm4a_mem_densitiesP0.1 hρ₁
  obtain ⟨hm₂, hA₂0, hA₂t⟩ := gm4a_mem_densitiesP0.1 hρ₂
  have key : ∀ s₁ s₂ : ℝ≥0∞, s₁ ≠ ⊤ → s₂ ≠ ⊤ → s₁ ≠ 0 ∨ s₂ ≠ 0 →
      (s₁ * pathRhoLength Γ₁ ρ₁ + s₂ * pathRhoLength Γ₂ ρ₂) ^ 2 /
        (s₁ ^ 2 * rhoArea ρ₁ Ω₁ + s₂ ^ 2 * rhoArea ρ₂ Ω₂) ≤ extremalLengthGM Ω Γ := by
    intro s₁ s₂ h₁ h₂ hs
    have hm₁' : Measurable (Ω₁.indicator fun z => s₁ * ρ₁ z) := (hm₁.const_mul s₁).indicator hΩ₁.measurableSet
    have hm : Measurable fun z => Ω₁.indicator (fun z => s₁ * ρ₁ z) z + Ω₂.indicator (fun z => s₂ * ρ₂ z) z :=
      hm₁'.add ((hm₂.const_mul s₂).indicator hΩ₂.measurableSet)
    have hA := gm4a_rhoArea_two_indicators hΩ₁.measurableSet hΩ₂.measurableSet hdisj hΩ₁₂ (hm₁.const_mul s₁)
      (g := fun z => s₂ * ρ₂ z)
    rw [LiZhongQC.rhoArea_const_mul ρ₁ Ω₁ h₁, LiZhongQC.rhoArea_const_mul ρ₂ Ω₂ h₂] at hA
    have hpos : 0 < s₁ ^ 2 * rhoArea ρ₁ Ω₁ + s₂ ^ 2 * rhoArea ρ₂ Ω₂ := by
      rcases hs with hs | hs
      · exact lt_of_lt_of_le (ENNReal.mul_pos (pow_ne_zero 2 hs) hA₁0.ne') le_self_add
      · exact lt_of_lt_of_le (ENNReal.mul_pos (pow_ne_zero 2 hs) hA₂0.ne') le_add_self
    have hfin : s₁ ^ 2 * rhoArea ρ₁ Ω₁ + s₂ ^ 2 * rhoArea ρ₂ Ω₂ < ⊤ :=
      ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (ENNReal.pow_lt_top h₁.lt_top) hA₁t,
        ENNReal.mul_lt_top (ENNReal.pow_lt_top h₂.lt_top) hA₂t⟩
    have hmem : (fun z => Ω₁.indicator (fun z => s₁ * ρ₁ z) z + Ω₂.indicator (fun z => s₂ * ρ₂ z) z) ∈
        densitiesP0 Ω := gm4a_mem_densitiesP0.2 ⟨hm, hA ▸ hpos, hA ▸ hfin⟩
    have hL : s₁ * pathRhoLength Γ₁ ρ₁ + s₂ * pathRhoLength Γ₂ ρ₂ ≤
        pathRhoLength Γ (fun z => Ω₁.indicator (fun z => s₁ * ρ₁ z) z + Ω₂.indicator (fun z => s₂ * ρ₂ z) z) := by
      refine le_trans ?_ (gm4a_pathRhoLength_add_le hm₁' _)
      refine add_le_add ?_ ?_
      · calc s₁ * pathRhoLength Γ₁ ρ₁ ≤ pathRhoLength Γ₁ (fun z => s₁ * ρ₁ z) :=
            gm4a_const_mul_pathRhoLength_le hm₁ s₁
          _ = pathRhoLength Γ₁ (Ω₁.indicator fun z => s₁ * ρ₁ z) :=
            (gm4a_pathRhoLength_indicator hΩ₁.measurableSet (hm₁.const_mul s₁) hΓ₁).symm
          _ ≤ _ := gm4a_pathRhoLength_le_of_contains _ fun γ hγ => (hcont γ hγ).1
      · calc s₂ * pathRhoLength Γ₂ ρ₂ ≤ pathRhoLength Γ₂ (fun z => s₂ * ρ₂ z) :=
            gm4a_const_mul_pathRhoLength_le hm₂ s₂
          _ = pathRhoLength Γ₂ (Ω₂.indicator fun z => s₂ * ρ₂ z) :=
            (gm4a_pathRhoLength_indicator hΩ₂.measurableSet (hm₂.const_mul s₂) hΓ₂).symm
          _ ≤ _ := gm4a_pathRhoLength_le_of_contains _ fun γ hγ => (hcont γ hγ).2
    calc (s₁ * pathRhoLength Γ₁ ρ₁ + s₂ * pathRhoLength Γ₂ ρ₂) ^ 2 /
          (s₁ ^ 2 * rhoArea ρ₁ Ω₁ + s₂ ^ 2 * rhoArea ρ₂ Ω₂) ≤
          pathRhoLength Γ (fun z => Ω₁.indicator (fun z => s₁ * ρ₁ z) z +
            Ω₂.indicator (fun z => s₂ * ρ₂ z) z) ^ 2 /
            rhoArea (fun z => Ω₁.indicator (fun z => s₁ * ρ₁ z) z + Ω₂.indicator (fun z => s₂ * ρ₂ z) z) Ω := by
          rw [hA]
          gcongr
      _ ≤ extremalLengthGM Ω Γ := gm4a_ratio_le hmem
  rcases eq_or_ne (pathRhoLength Γ₁ ρ₁) ⊤ with hL₁ | hL₁
  · have h := key 1 0 ENNReal.one_ne_top ENNReal.zero_ne_top (Or.inl one_ne_zero)
    rw [hL₁] at h
    simp only [one_mul, zero_mul, add_zero, one_pow, ENNReal.top_pow two_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, ENNReal.top_div_of_ne_top hA₁t.ne, top_le_iff] at h
    rw [h]
    exact le_top
  rcases eq_or_ne (pathRhoLength Γ₂ ρ₂) ⊤ with hL₂ | hL₂
  · have h := key 0 1 ENNReal.zero_ne_top ENNReal.one_ne_top (Or.inr one_ne_zero)
    rw [hL₂] at h
    simp only [one_mul, zero_mul, zero_add, one_pow, ENNReal.top_pow two_ne_zero,
      ENNReal.top_div_of_ne_top hA₂t.ne, top_le_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at h
    rw [h]
    exact le_top
  by_cases h00 : pathRhoLength Γ₁ ρ₁ = 0 ∧ pathRhoLength Γ₂ ρ₂ = 0
  · rw [h00.1, h00.2]
    simp
  have hs : pathRhoLength Γ₁ ρ₁ / rhoArea ρ₁ Ω₁ ≠ 0 ∨ pathRhoLength Γ₂ ρ₂ / rhoArea ρ₂ Ω₂ ≠ 0 := by
    rw [not_and_or] at h00
    rcases h00 with h | h
    · exact Or.inl (by simp [ENNReal.div_eq_zero_iff, h, hA₁t.ne])
    · exact Or.inr (by simp [ENNReal.div_eq_zero_iff, h, hA₂t.ne])
  have h := key _ _ (ENNReal.div_ne_top hL₁ hA₁0.ne') (ENNReal.div_ne_top hL₂ hA₂0.ne') hs
  rwa [gm4a_serial_arith hA₁0.ne' hA₁t.ne hA₂0.ne' hA₂t.ne hL₁ hL₂] at h

/-- Helper: `λ_D(Γ)⁻¹ ≤ A(D, ρ)/L²` for a measurable `ρ` of finite area on a non-empty open `D`, whenever
`0 < L ≤ L(Γ, ρ)`. -/
theorem gm4a_inv_extremalLength_le {D : Set ℂ} (hD : IsOpen D) (hne : D.Nonempty) {Γ : Set (Set ℂ)}
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) (hfin : rhoArea ρ D < ⊤) {L : ℝ≥0∞} (hL₀ : 0 < L)
    (hL : L ≤ pathRhoLength Γ ρ) : (extremalLengthGM D Γ)⁻¹ ≤ rhoArea ρ D / L ^ 2 := by
  rcases eq_or_ne (rhoArea ρ D) 0 with h0 | h0
  · rw [gm4a_extremalLength_eq_top hD hne hρ h0 (hL₀.trans_le hL), ENNReal.inv_top]
    exact zero_le
  · have hmem : ρ ∈ densitiesP0 D := gm4a_mem_densitiesP0.2 ⟨hρ, pos_iff_ne_zero.2 h0, hfin⟩
    have hle : L ^ 2 / rhoArea ρ D ≤ extremalLengthGM D Γ := by
      refine le_trans ?_ (gm4a_ratio_le hmem)
      gcongr
    calc (extremalLengthGM D Γ)⁻¹ ≤ (L ^ 2 / rhoArea ρ D)⁻¹ := ENNReal.inv_le_inv.2 hle
      _ = rhoArea ρ D / L ^ 2 := ENNReal.inv_div (Or.inl hfin.ne) (Or.inl h0)

/-- Helper: `A(Ω₁, ρ) + A(Ω₂, ρ) ≤ A(Ω, ρ)` for disjoint `Ω₁, Ω₂ ⊆ Ω`, `Ω₂` measurable. -/
theorem gm4a_rhoArea_add_le {Ω₁ Ω₂ Ω : Set ℂ} (hΩ₂ : MeasurableSet Ω₂) (hdisj : Disjoint Ω₁ Ω₂)
    (hΩ₁₂ : Ω₁ ∪ Ω₂ ⊆ Ω) (ρ : ℂ → ℝ≥0∞) : rhoArea ρ Ω₁ + rhoArea ρ Ω₂ ≤ rhoArea ρ Ω := by
  rw [gm4a_rhoArea_eq, gm4a_rhoArea_eq, gm4a_rhoArea_eq, ← lintegral_union hΩ₂ hdisj]
  exact lintegral_mono_set hΩ₁₂

/-- Helper (the parallel rule for one metric): `λ(Γ₁)⁻¹ + λ(Γ₂)⁻¹ ≤ A(Ω, ρ)/L²(Γ, ρ)`. -/
theorem gm4a_parallel_pair {Ω₁ Ω₂ Ω : Set ℂ} (hΩ₁ : IsOpen Ω₁) (hΩ₂ : IsOpen Ω₂) (hdisj : Disjoint Ω₁ Ω₂)
    (hne₁ : Ω₁.Nonempty) (hne₂ : Ω₂.Nonempty) (hΩ₁₂ : Ω₁ ∪ Ω₂ ⊆ Ω) {Γ₁ Γ₂ Γ : Set (Set ℂ)}
    (hcont : ∀ γ ∈ Γ₁ ∪ Γ₂, ∃ γ' ∈ Γ, γ' ⊆ γ) {ρ : ℂ → ℝ≥0∞} (hρ : ρ ∈ densitiesP0 Ω) :
    (extremalLengthGM Ω₁ Γ₁)⁻¹ + (extremalLengthGM Ω₂ Γ₂)⁻¹ ≤ (pathRhoLength Γ ρ ^ 2 / rhoArea ρ Ω)⁻¹ := by
  obtain ⟨hm, hA0, hAt⟩ := gm4a_mem_densitiesP0.1 hρ
  rcases eq_or_ne (pathRhoLength Γ ρ) 0 with hL | hL
  · rw [hL, zero_pow two_ne_zero, ENNReal.zero_div, ENNReal.inv_zero]
    exact le_top
  have hL₀ := pos_iff_ne_zero.2 hL
  have hsub : ∀ Ω' ⊆ Ω, rhoArea ρ Ω' < ⊤ := fun Ω' h => by
    refine lt_of_le_of_lt ?_ hAt
    rw [gm4a_rhoArea_eq, gm4a_rhoArea_eq]
    exact lintegral_mono_set h
  have h₁ := gm4a_inv_extremalLength_le hΩ₁ hne₁ hm (hsub Ω₁ (subset_union_left.trans hΩ₁₂)) hL₀
    (gm4a_pathRhoLength_le_of_contains ρ fun γ hγ => hcont γ (Or.inl hγ))
  have h₂ := gm4a_inv_extremalLength_le hΩ₂ hne₂ hm (hsub Ω₂ (subset_union_right.trans hΩ₁₂)) hL₀
    (gm4a_pathRhoLength_le_of_contains ρ fun γ hγ => hcont γ (Or.inr hγ))
  calc (extremalLengthGM Ω₁ Γ₁)⁻¹ + (extremalLengthGM Ω₂ Γ₂)⁻¹ ≤
        rhoArea ρ Ω₁ / pathRhoLength Γ ρ ^ 2 + rhoArea ρ Ω₂ / pathRhoLength Γ ρ ^ 2 := add_le_add h₁ h₂
    _ = (rhoArea ρ Ω₁ + rhoArea ρ Ω₂) / pathRhoLength Γ ρ ^ 2 := ENNReal.div_add_div_same
    _ ≤ rhoArea ρ Ω / pathRhoLength Γ ρ ^ 2 := by
        gcongr
        exact gm4a_rhoArea_add_le hΩ₂.measurableSet hdisj hΩ₁₂ ρ
    _ = (pathRhoLength Γ ρ ^ 2 / rhoArea ρ Ω)⁻¹ := (ENNReal.inv_div (Or.inl hAt.ne) (Or.inl hA0.ne')).symm

/-- **The extension rule** (Ch. IV §3), (3.1) (cited at P1:6043, 6045 and, as "the extension rule", in Chapter V,
P1:6991, 7115, 7351, 7733, 7739, 7842, 7856, and Chapter VIII, P2:3964, 4882, 4914, 4934). Let `Ω ⊆ Ω'` be domains
and let `Γ` be a path family in `Ω`. Then (3.1) `λ_{Ω'}(Γ) = λ_Ω(Γ)`.
Modelling: plane domains (open and connected). -/
theorem eq4_3_1 {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω ∧ IsConnected Ω) (hΩ' : IsOpen Ω' ∧ IsConnected Ω') (hΩΩ' : Ω ⊆ Ω')
    {Γ : Set (Set ℂ)} (hΓ : IsPathFamily Ω Γ) :
    extremalLengthGM Ω' Γ = extremalLengthGM Ω Γ := by
  have _ := hΩ'
  exact le_antisymm (gm4a_extremalLength_le_of_subset hΩ.1 hΩ.2.nonempty hΩΩ' Γ)
    (gm4a_extremalLength_le_of_contains hΩ.1 hΩΩ' (fun γ hγ => gm4a_isPathCurve_subset (hΓ.2 γ hγ))
      fun γ hγ => ⟨γ, hγ, subset_rfl⟩)

/-- **The extension rule** (Ch. IV §3), (3.2). Let `Ω ⊆ Ω'` be domains and let `Γ` be a path family in `Ω`. If `Γ'`
is a path family in `Ω'` such that every `γ' ∈ Γ'` contains some `γ ∈ Γ`, then (3.2) `λ_{Ω'}(Γ') ≥ λ_Ω(Γ)`.
Modelling: plane domains; "contains" is `γ ⊆ γ'`. -/
theorem eq4_3_2 {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω ∧ IsConnected Ω) (hΩ' : IsOpen Ω' ∧ IsConnected Ω') (hΩΩ' : Ω ⊆ Ω')
    {Γ Γ' : Set (Set ℂ)} (hΓ : IsPathFamily Ω Γ) (hΓ' : IsPathFamily Ω' Γ') (hΓΓ' : ∀ γ' ∈ Γ', ∃ γ ∈ Γ, γ ⊆ γ') :
    extremalLengthGM Ω Γ ≤ extremalLengthGM Ω' Γ' := by
  have _ := hΩ'
  have _ := hΓ'
  exact gm4a_extremalLength_le_of_contains hΩ.1 hΩΩ' (fun γ hγ => gm4a_isPathCurve_subset (hΓ.2 γ hγ)) hΓΓ'

/-- **Unlabelled** (Ch. IV §3, P1:6032; the form in which "the extension rule" is cited for extremal distances, e.g.
P1:7115 "By the extension rule, we may suppose that `E = …`", P1:7733). The extension rule shows that `d_Ω(E, F)` is
decreased if any of the sets `E`, `F` or `Ω` is increased.
Modelling: plane domains `Ω ⊆ Ω'` and sets `E ⊆ E'`, `F ⊆ F'` with `E, F ⊆ Ω̄` and `E', F' ⊆ Ω̄'` (the setting in
which `d` is defined, P1:5888). -/
theorem extremalDistGM_antitone {Ω Ω' E E' F F' : Set ℂ} (hΩ : IsOpen Ω ∧ IsConnected Ω)
    (hΩ' : IsOpen Ω' ∧ IsConnected Ω') (hΩΩ' : Ω ⊆ Ω') (hEE' : E ⊆ E') (hFF' : F ⊆ F') (hE : E ⊆ closure Ω)
    (hF : F ⊆ closure Ω) (hE' : E' ⊆ closure Ω') (hF' : F' ⊆ closure Ω') :
    extremalDistGM Ω' E' F' ≤ extremalDistGM Ω E F := by
  have _ := hΩ'
  have _ := hE
  have _ := hF
  have _ := hE'
  have _ := hF'
  calc extremalDistGM Ω' E' F' = extremalLengthGM Ω' (joiningFamily Ω' E' F') := rfl
    _ ≤ extremalLengthGM Ω' (joiningFamily Ω E F) :=
      gm4a_extremalLength_anti (gm4a_joiningFamily_mono hΩΩ' hEE' hFF')
    _ ≤ extremalLengthGM Ω (joiningFamily Ω E F) := gm4a_extremalLength_le_of_subset hΩ.1 hΩ.2.nonempty hΩΩ' _
    _ = extremalDistGM Ω E F := rfl

/-- **Unlabelled** (Ch. IV §3, P1:6032). `d_Ω(E, F) = d_{Ω \ (E ∪ F)}(E, F)` when `E` and `F` are closed.
Modelling: `Ω` is a plane domain and `E, F ⊆ Ω̄` are closed sets of `ℂ`; the open set `Ω \ (E ∪ F)` need not be
connected, and `d` is defined for it by the same formula.
[CORRECTION] As printed (only `E, F ⊆ Ω̄` closed, the setting of the definition, P1:5888) the claim is false: for
`Ω = 𝔻`, `E = 𝔻̄`, `F = ∅` the left side is `λ` of the empty family, `∞`, while `Ω \ (E ∪ F) = ∅` gives `0`; for
overlapping sets, `Ω = (−1, 1)²`, `F = [−½, ½]²`, `E = [−¼, ¼] × {0}`, the left side is `0` (arbitrarily short
curves join `E` to `F`) while no curve of `Ω \ F` reaches `E`, so the right side is `∞`. It is stated for disjoint
non-empty `E` and `F` (then `Ω \ (E ∪ F) ≠ ∅` by connectedness), where it holds by the last-exit/first-hit
sub-arc argument; the book's uses are of this kind. -/
theorem extremalDistGM_diff {Ω E F : Set ℂ} (hΩ : IsOpen Ω ∧ IsConnected Ω) (hE : IsClosed E) (hF : IsClosed F)
    (hEΩ : E ⊆ closure Ω) (hFΩ : F ⊆ closure Ω) (hdisj : Disjoint E F) (hEne : E.Nonempty)
    (hFne : F.Nonempty) :
    extremalDistGM Ω E F = extremalDistGM (Ω \ (E ∪ F)) E F := by
  have hne := gm4a_diff_nonempty hΩ hE hF hEΩ hFΩ hdisj hEne hFne
  have hopen : IsOpen (Ω \ (E ∪ F)) := hΩ.1.sdiff (hE.union hF)
  apply le_antisymm
  · calc extremalDistGM Ω E F = extremalLengthGM Ω (joiningFamily Ω E F) := rfl
      _ ≤ extremalLengthGM Ω (joiningFamily (Ω \ (E ∪ F)) E F) :=
        gm4a_extremalLength_anti (gm4a_joiningFamily_mono sdiff_subset subset_rfl subset_rfl)
      _ ≤ extremalLengthGM (Ω \ (E ∪ F)) (joiningFamily (Ω \ (E ∪ F)) E F) :=
        gm4a_extremalLength_le_of_subset hopen hne sdiff_subset _
      _ = extremalDistGM (Ω \ (E ∪ F)) E F := rfl
  · exact gm4a_extremalLength_le_of_contains hopen sdiff_subset
      (fun γ hγ => gm4a_isPathCurve_subset (gm4a_joiningFamily_isPathCurve hγ))
      fun γ hγ => gm4a_joining_subarc hE hF hdisj hγ

/-- **The serial rule** (Ch. IV §3; cited at P1:6405, 6961, 7176, P2:9, 4202). Let `Γ₁` and `Γ₂` be path families
contained in disjoint open sets `Ω₁` and `Ω₂` respectively, and let `Γ` be a path family contained in a domain
`Ω ⊃ Ω₁ ∪ Ω₂`. If each `γ ∈ Γ` contains some `γ₁ ∈ Γ₁` and some `γ₂ ∈ Γ₂`, then `λ(Γ) ≥ λ(Γ₁) + λ(Γ₂)`.
Modelling: `λ(Γ_j) = λ_{Ω_j}(Γ_j)` (open sets of the plane, not necessarily connected) and `λ(Γ) = λ_Ω(Γ)`; the sum
is taken in `[0, ∞]`. -/
theorem serial_rule {Ω₁ Ω₂ Ω : Set ℂ} (hΩ₁ : IsOpen Ω₁) (hΩ₂ : IsOpen Ω₂) (hdisj : Disjoint Ω₁ Ω₂)
    (hΩ : IsOpen Ω ∧ IsConnected Ω) (hΩ₁₂ : Ω₁ ∪ Ω₂ ⊆ Ω) {Γ₁ Γ₂ Γ : Set (Set ℂ)} (hΓ₁ : IsPathFamily Ω₁ Γ₁)
    (hΓ₂ : IsPathFamily Ω₂ Γ₂) (hΓ : IsPathFamily Ω Γ)
    (hcont : ∀ γ ∈ Γ, (∃ γ₁ ∈ Γ₁, γ₁ ⊆ γ) ∧ ∃ γ₂ ∈ Γ₂, γ₂ ⊆ γ) :
    extremalLengthGM Ω₁ Γ₁ + extremalLengthGM Ω₂ Γ₂ ≤ extremalLengthGM Ω Γ := by
  have _ := hΩ
  have _ := hΓ
  rw [gm4a_extremalLengthGM_eq Ω₁, gm4a_extremalLengthGM_eq Ω₂]
  exact ENNReal.biSup_add_biSup_le' (gm4a_densitiesP0_nonempty hΩ₁ (gm4a_nonempty_of_isPathFamily hΓ₁))
    (gm4a_densitiesP0_nonempty hΩ₂ (gm4a_nonempty_of_isPathFamily hΓ₂)) fun ρ₁ hρ₁ ρ₂ hρ₂ =>
      gm4a_serial_pair hΩ₁ hΩ₂ hdisj hΩ₁₂ (fun γ hγ => gm4a_isPathCurve_subset (hΓ₁.2 γ hγ))
        (fun γ hγ => gm4a_isPathCurve_subset (hΓ₂.2 γ hγ)) hcont hρ₁ hρ₂

/-- **The parallel rule** (Ch. IV §3), (3.3) (cited at P1:7469, P2:3970 and in App. H, P3:4758). Let `Γ₁` and `Γ₂`
be path families contained in disjoint open sets `Ω₁` and `Ω₂` respectively. If `Γ` is a path family in
`Ω ⊃ Ω₁ ∪ Ω₂` such that every `γ ∈ Γ₁ ∪ Γ₂` contains some `γ' ∈ Γ`, then (3.3)
`1/λ(Γ) ≥ 1/λ(Γ₁) + 1/λ(Γ₂)`.
Modelling: as in `serial_rule` (`Ω` a plane domain); `1/λ` is the inverse in `[0, ∞]`. The proof ends "we obtain
(2.3)", read (3.3) [misprint] (a text-layer span; leader ruling B12(6)). -/
theorem parallel_rule {Ω₁ Ω₂ Ω : Set ℂ} (hΩ₁ : IsOpen Ω₁) (hΩ₂ : IsOpen Ω₂) (hdisj : Disjoint Ω₁ Ω₂)
    (hΩ : IsOpen Ω ∧ IsConnected Ω) (hΩ₁₂ : Ω₁ ∪ Ω₂ ⊆ Ω) {Γ₁ Γ₂ Γ : Set (Set ℂ)} (hΓ₁ : IsPathFamily Ω₁ Γ₁)
    (hΓ₂ : IsPathFamily Ω₂ Γ₂) (hΓ : IsPathFamily Ω Γ) (hcont : ∀ γ ∈ Γ₁ ∪ Γ₂, ∃ γ' ∈ Γ, γ' ⊆ γ) :
    (extremalLengthGM Ω₁ Γ₁)⁻¹ + (extremalLengthGM Ω₂ Γ₂)⁻¹ ≤ (extremalLengthGM Ω Γ)⁻¹ := by
  have _ := hΩ
  have _ := hΓ
  rw [gm4a_extremalLengthGM_eq Ω]
  simp only [ENNReal.inv_iSup]
  exact le_iInf₂ fun ρ hρ => gm4a_parallel_pair hΩ₁ hΩ₂ hdisj (gm4a_nonempty_of_isPathFamily hΓ₁)
    (gm4a_nonempty_of_isPathFamily hΓ₂) hΩ₁₂ hcont hρ

/-! ### GM4-C helpers (-e8): the symmetry rule -/

/-- Helper (symmetry rule): an analytic or anti-analytic `T` on an open set is `σ ∘ S` with `S` analytic and `σ` a
linear isometry of `ℂ` (the identity or the conjugation); the real derivative of `T` at `w ∈ Ω` is a similarity of ratio
`‖S'(w)‖`. -/
theorem gm4c_sym_decomp {Ω : Set ℂ} (hΩ : IsOpen Ω) {T : ℂ → ℂ}
    (hT : DifferentiableOn ℂ T Ω ∨ DifferentiableOn ℂ (fun z => (starRingEnd ℂ) (T z)) Ω) :
    ∃ (σ : ℂ ≃ₗᵢ[ℝ] ℂ) (S : ℂ → ℂ), (∀ z, T z = σ (S z)) ∧ DifferentiableOn ℂ S Ω ∧
      ∀ w ∈ Ω, DifferentiableAt ℝ T w ∧ ‖fderiv ℝ T w‖ = ‖deriv S w‖ ∧
        ∀ x, ‖fderiv ℝ T w x‖ = ‖deriv S w‖ * ‖x‖ := by
  have key : ∀ (σ : ℂ ≃ₗᵢ[ℝ] ℂ) (S : ℂ → ℂ), (∀ z, T z = σ (S z)) → DifferentiableOn ℂ S Ω →
      ∀ w ∈ Ω, DifferentiableAt ℝ T w ∧ ‖fderiv ℝ T w‖ = ‖deriv S w‖ ∧
        ∀ x, ‖fderiv ℝ T w x‖ = ‖deriv S w‖ * ‖x‖ := by
    intro σ S hTS hS w hw
    have hSd : DifferentiableAt ℂ S w := hS.differentiableAt (hΩ.mem_nhds hw)
    have h1 : HasFDerivAt S ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv S w)).restrictScalars ℝ) w :=
      hSd.hasDerivAt.hasFDerivAt.restrictScalars ℝ
    have h2 := (σ.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).comp w h1
    have hTfun : T = σ ∘ S := funext hTS
    have h3 : fderiv ℝ T w = σ.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv S w)).restrictScalars ℝ) := by
      rw [hTfun]
      exact h2.fderiv
    have hx : ∀ x, ‖fderiv ℝ T w x‖ = ‖deriv S w‖ * ‖x‖ := by
      intro x
      rw [h3]
      simp [mul_comm]
    refine ⟨?_, ?_, hx⟩
    · rw [hTfun]
      exact h2.differentiableAt
    refine ContinuousLinearMap.opNorm_eq_of_bounds (norm_nonneg _) (fun x => (hx x).le) fun N hN hbd => ?_
    have := hbd 1
    rw [hx 1] at this
    simpa using this
  rcases hT with h | h
  · refine ⟨LinearIsometryEquiv.refl ℝ ℂ, T, fun z => rfl, h, ?_⟩
    exact key (LinearIsometryEquiv.refl ℝ ℂ) T (fun z => rfl) h
  · have hc : ∀ z, T z = Complex.conjLIE ((starRingEnd ℂ) (T z)) := fun z => by
      rw [Complex.conjLIE_apply, Complex.conj_conj]
    refine ⟨Complex.conjLIE, fun z => (starRingEnd ℂ) (T z), hc, h, ?_⟩
    exact key Complex.conjLIE (fun z => (starRingEnd ℂ) (T z)) hc h

/-- Helper (symmetry rule): for an involution `T` of an open set `Ω`, analytic or anti-analytic, the Jacobian factors
satisfy `‖T'(T z)‖ ‖T'(z)‖ = 1` (chain rule for `T ∘ T = id`; the operator norm of the real derivative is `|T'|`). -/
theorem gm4c_sym_jac {Ω : Set ℂ} (hΩ : IsOpen Ω) {T : ℂ → ℂ} (hTΩ : MapsTo T Ω Ω) (hTT : ∀ z ∈ Ω, T (T z) = z)
    (hT : DifferentiableOn ℂ T Ω ∨ DifferentiableOn ℂ (fun z => (starRingEnd ℂ) (T z)) Ω) {z : ℂ} (hz : z ∈ Ω) :
    ‖fderiv ℝ T (T z)‖ₑ * ‖fderiv ℝ T z‖ₑ = 1 := by
  obtain ⟨σ, S, hTS, hS, hF⟩ := gm4c_sym_decomp hΩ hT
  obtain ⟨hdA, hA, hAx⟩ := hF (T z) (hTΩ hz)
  obtain ⟨hdB, hB, hBx⟩ := hF z hz
  have hcomp : HasFDerivAt (T ∘ T) ((fderiv ℝ T (T z)).comp (fderiv ℝ T z)) z :=
    HasFDerivAt.comp z hdA.hasFDerivAt hdB.hasFDerivAt
  have hev : (id : ℂ → ℂ) =ᶠ[nhds z] (T ∘ T) :=
    Filter.eventually_of_mem (hΩ.mem_nhds hz) fun w hw => (hTT w hw).symm
  have hid := hcomp.congr_of_eventuallyEq hev
  have heq := (hasFDerivAt_id z).unique hid
  have h1 : (fderiv ℝ T (T z)) ((fderiv ℝ T z) 1) = 1 := by
    have := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) heq
    simpa using this.symm
  have h2 : ‖fderiv ℝ T (T z)‖ * ‖fderiv ℝ T z‖ = 1 := by
    have h3 := congrArg norm h1
    rw [hAx, hBx, norm_one, ← hA, ← hB] at h3
    simpa using h3
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _), h2, ENNReal.ofReal_one]

/-- Helper (symmetry rule, lengths): `∫_{T(γ)} ρ dμH[1] = ∫_γ (ρ ∘ T) ‖DT‖ dμH[1]` for a Borel set `γ ⊆ Ω`
(W-AREA1 for analytic `T`, and for `T = conj ∘ S` with `S` analytic, `conj` being an isometry). -/
theorem gm4c_sym_lintegral {Ω : Set ℂ} (hΩ : IsOpen Ω) {T : ℂ → ℂ} (hTΩ : MapsTo T Ω Ω)
    (hTT : ∀ z ∈ Ω, T (T z) = z)
    (hT : DifferentiableOn ℂ T Ω ∨ DifferentiableOn ℂ (fun z => (starRingEnd ℂ) (T z)) Ω) {γ : Set ℂ}
    (hγ : MeasurableSet γ) (hγΩ : γ ⊆ Ω) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    ∫⁻ z in T '' γ, ρ z ∂μH[1] = ∫⁻ z in γ, ρ (T z) * ‖fderiv ℝ T z‖ₑ ∂μH[1] := by
  have _ := hTΩ
  obtain ⟨σ, S, hTS, hS, hF⟩ := gm4c_sym_decomp hΩ hT
  have hinj : InjOn S Ω := fun a ha b hb hab => by
    have h : T a = T b := by rw [hTS a, hTS b, hab]
    rw [← hTT a ha, ← hTT b hb, h]
  have hSconf : LiZhongQC.IsConformalOnto S Ω (S '' Ω) := ⟨hS, hinj, rfl⟩
  have hmp : MeasurePreserving σ (μH[1] : Measure ℂ) μH[1] := by
    refine ⟨σ.continuous.measurable, ?_⟩
    rw [σ.isometry.map_hausdorffMeasure (Or.inl zero_le_one), σ.surjective.range_eq, Measure.restrict_univ]
  have hme : MeasurableEmbedding σ := σ.toHomeomorph.measurableEmbedding
  have himg : T '' γ = σ '' (S '' γ) := by
    rw [image_image]
    exact image_congr fun z _ => hTS z
  rw [himg, ← hmp.setLIntegral_comp_emb hme ρ (S '' γ),
    gm4b_lintegral_image_conformal hΩ hSconf hγ hγΩ (ρ := fun w => ρ (σ w)) (hρ.comp σ.continuous.measurable)]
  refine setLIntegral_congr_fun hγ fun z hz => ?_
  rw [← hTS z, ← ofReal_norm, ← ofReal_norm, (hF z (hγΩ hz)).2.1]

/-- Helper (symmetry rule, areas): `∬_Ω ((ρ ∘ T) ‖DT‖)² = ∬_Ω ρ²` (change of variables, `T` an involution of `Ω`
with `|J_T| = ‖DT‖²`). -/
theorem gm4c_sym_area {Ω : Set ℂ} (hΩ : IsOpen Ω) {T : ℂ → ℂ} (hTΩ : MapsTo T Ω Ω) (hTT : ∀ z ∈ Ω, T (T z) = z)
    (hT : DifferentiableOn ℂ T Ω ∨ DifferentiableOn ℂ (fun z => (starRingEnd ℂ) (T z)) Ω) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) :
    ∫⁻ z in Ω, (ρ (T z) * ‖fderiv ℝ T z‖ₑ) ^ 2 = ∫⁻ z in Ω, ρ z ^ 2 := by
  have _ := hρ
  obtain ⟨σ, S, hTS, hS, hF⟩ := gm4c_sym_decomp hΩ hT
  have hinj : InjOn S Ω := fun a ha b hb hab => by
    have h : T a = T b := by rw [hTS a, hTS b, hab]
    rw [← hTT a ha, ← hTT b hb, h]
  have hSconf : LiZhongQC.IsConformalOnto S Ω (S '' Ω) := ⟨hS, hinj, rfl⟩
  have hTimg : T '' Ω = Ω := by
    refine le_antisymm (hTΩ.image_subset) fun z hz => ⟨T z, hTΩ hz, hTT z hz⟩
  have hpull := LiZhongQC.rhoArea_pullback hΩ hSconf (fun w => ρ (σ w))
  have hleft : LiZhongQC.rhoArea (Ω.indicator fun z => ρ (σ (S z)) * ‖deriv S z‖ₑ) Ω =
      ∫⁻ z in Ω, (ρ (T z) * ‖fderiv ℝ T z‖ₑ) ^ 2 := by
    rw [gm4a_rhoArea_eq]
    refine setLIntegral_congr_fun hΩ.measurableSet fun z hz => ?_
    rw [indicator_of_mem hz, ← hTS z, ← ofReal_norm, ← ofReal_norm, (hF z hz).2.1]
  have hright : LiZhongQC.rhoArea (fun w => ρ (σ w)) (S '' Ω) = ∫⁻ z in Ω, ρ z ^ 2 := by
    rw [gm4a_rhoArea_eq]
    have hme : MeasurableEmbedding σ := σ.toHomeomorph.measurableEmbedding
    have := σ.measurePreserving.setLIntegral_comp_emb hme (fun w => ρ w ^ 2) (S '' Ω)
    rw [this, image_image]
    rw [show (fun a => σ (S a)) = T from funext fun a => (hTS a).symm, hTimg]
  rw [← hleft, hpull, hright]

/-- Helper (symmetry rule): the pulled-back density `1_Ω (ρ ∘ T) ‖DT‖` is Borel. -/
theorem gm4c_sym_measurable {Ω : Set ℂ} (hΩ : IsOpen Ω) {T : ℂ → ℂ}
    (hT : DifferentiableOn ℂ T Ω ∨ DifferentiableOn ℂ (fun z => (starRingEnd ℂ) (T z)) Ω) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) (hTΩ : MapsTo T Ω Ω) :
    Measurable (Ω.indicator fun z => ρ (T z) * ‖fderiv ℝ T z‖ₑ) := by
  have _ := hTΩ
  obtain ⟨σ, S, hTS, hS, hF⟩ := gm4c_sym_decomp hΩ hT
  have h := LiZhongQC.measurable_pullback_density (D := Ω) hΩ hS.continuousOn (ρ' := fun w => ρ (σ w))
    (hρ.comp σ.continuous.measurable)
  convert h using 1
  funext z
  by_cases hz : z ∈ Ω
  · simp only [indicator_of_mem hz]
    rw [← hTS z, ← ofReal_norm, ← ofReal_norm, (hF z hz).2.1]
  · simp [hz]

/-- Helper (symmetry rule): symmetrization `ρ' = ½ (ρ + 1_Ω (ρ ∘ T) ‖DT‖)` of a metric: a symmetric metric with a
length at least that of `ρ` (as `T(Γ) = Γ`) and an area at most that of `ρ` (convexity). -/
theorem gm4c_sym_average {Ω : Set ℂ} (hΩ : IsOpen Ω) {T : ℂ → ℂ} (hTΩ : MapsTo T Ω Ω)
    (hTT : ∀ z ∈ Ω, T (T z) = z)
    (hT : DifferentiableOn ℂ T Ω ∨ DifferentiableOn ℂ (fun z => (starRingEnd ℂ) (T z)) Ω) {Γ : Set (Set ℂ)}
    (hΓ : IsPathFamily Ω Γ) (hTΓ : image T '' Γ = Γ) {ρ : ℂ → ℝ≥0∞} (hρ : ρ ∈ densitiesP0 Ω) :
    ∃ ρ' ∈ densitiesP0 Ω, (∀ z ∈ Ω, ρ' z = ρ' (T z) * ‖fderiv ℝ T z‖ₑ) ∧
      pathRhoLength Γ ρ ≤ pathRhoLength Γ ρ' ∧ rhoArea ρ' Ω ≤ rhoArea ρ Ω := by
  obtain ⟨hm, hA0, hAt⟩ := gm4a_mem_densitiesP0.1 hρ
  set ρt : ℂ → ℝ≥0∞ := Ω.indicator (fun z => ρ (T z) * ‖fderiv ℝ T z‖ₑ) with hρt
  have hρtm : Measurable ρt := gm4c_sym_measurable hΩ hT hm hTΩ
  set ρ' : ℂ → ℝ≥0∞ := fun z => 2⁻¹ * (ρ z + ρt z) with hρ'
  have hρ'm : Measurable ρ' := (hm.add hρtm).const_mul 2⁻¹
  have hρtΩ : ∀ z ∈ Ω, ρt z = ρ (T z) * ‖fderiv ℝ T z‖ₑ := fun z hz => by
    simp only [hρt, indicator_of_mem hz]
  have hAρt : LiZhongQC.rhoArea ρt Ω = LiZhongQC.rhoArea ρ Ω := by
    rw [gm4a_rhoArea_eq, gm4a_rhoArea_eq, ← gm4c_sym_area hΩ hTΩ hTT hT hm]
    exact setLIntegral_congr_fun hΩ.measurableSet fun z hz => by rw [hρtΩ z hz]
  have hpt : ∀ a b : ℝ≥0∞, (2⁻¹ * (a + b)) ^ 2 ≤ 2⁻¹ * (a ^ 2 + b ^ 2) := by
    intro a b
    have h := gm4a_parallelogram a b
    have h' : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := h ▸ le_self_add
    calc (2⁻¹ * (a + b)) ^ 2 = 2⁻¹ * 2⁻¹ * (a + b) ^ 2 := by ring
      _ ≤ 2⁻¹ * 2⁻¹ * (2 * a ^ 2 + 2 * b ^ 2) := by gcongr
      _ = 2⁻¹ * (2⁻¹ * 2) * (a ^ 2 + b ^ 2) := by ring
      _ = 2⁻¹ * (a ^ 2 + b ^ 2) := by
          rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  have hArea : LiZhongQC.rhoArea ρ' Ω ≤ LiZhongQC.rhoArea ρ Ω := by
    rw [gm4a_rhoArea_eq]
    calc ∫⁻ z in Ω, ρ' z ^ 2 ≤ ∫⁻ z in Ω, 2⁻¹ * (ρ z ^ 2 + ρt z ^ 2) := lintegral_mono fun z => hpt _ _
      _ = 2⁻¹ * (LiZhongQC.rhoArea ρ Ω + LiZhongQC.rhoArea ρt Ω) := by
          rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 two_ne_zero),
            lintegral_add_left (hm.pow_const 2), gm4a_rhoArea_eq, gm4a_rhoArea_eq]
      _ = LiZhongQC.rhoArea ρ Ω := by
          rw [hAρt, ← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  have hpos : 0 < LiZhongQC.rhoArea ρ' Ω := by
    by_contra h0
    rw [not_lt, nonpos_iff_eq_zero, gm4a_rhoArea_eq, lintegral_eq_zero_iff (hρ'm.pow_const 2)] at h0
    have h1 : ρ =ᵐ[volume.restrict Ω] 0 := by
      filter_upwards [h0] with z hz
      have h2 : ρ' z = 0 := by simpa using hz
      have h3 : ρ z + ρt z = 0 := by
        rcases mul_eq_zero.1 h2 with h | h
        · exact absurd h (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
        · exact h
      simpa using (add_eq_zero.1 h3).1
    have : LiZhongQC.rhoArea ρ Ω = 0 := by
      rw [gm4a_rhoArea_eq]
      exact (lintegral_eq_zero_iff (hm.pow_const 2)).2 (h1.mono fun z hz => by simp [hz])
    exact hA0.ne' this
  have hmem : ρ' ∈ LiZhongQC.densitiesP0 Ω := gm4a_mem_densitiesP0.2 ⟨hρ'm, hpos, hArea.trans_lt hAt⟩
  refine ⟨ρ', hmem, ?_, ?_, hArea⟩
  · intro z hz
    have hTz := hTΩ hz
    have hj := gm4c_sym_jac hΩ hTΩ hTT hT hz
    have h1 : ρ' (T z) = 2⁻¹ * (ρ (T z) + ρ z * ‖fderiv ℝ T (T z)‖ₑ) := by
      simp only [hρ']
      rw [hρtΩ _ hTz, hTT z hz]
    calc ρ' z = 2⁻¹ * (ρ z + ρ (T z) * ‖fderiv ℝ T z‖ₑ) := by simp only [hρ']; rw [hρtΩ z hz]
      _ = 2⁻¹ * (ρ (T z) * ‖fderiv ℝ T z‖ₑ + ρ z * (‖fderiv ℝ T (T z)‖ₑ * ‖fderiv ℝ T z‖ₑ)) := by
          rw [hj]; ring
      _ = ρ' (T z) * ‖fderiv ℝ T z‖ₑ := by rw [h1]; ring
  · rw [gm4a_pathRhoLength_eq, gm4a_pathRhoLength_eq]
    set Lρ : ℝ≥0∞ := ⨅ γ' ∈ Γ, ∫⁻ z in γ', ρ z ∂μH[1] with hLρ
    refine le_iInf₂ fun γ hγ => ?_
    have hγΩ : γ ⊆ Ω := gm4a_isPathCurve_subset (hΓ.2 γ hγ)
    have hγm : MeasurableSet γ := gm4b_isPathCurve_measurableSet (hΓ.2 γ hγ)
    have hTγ : image T γ ∈ Γ := by
      rw [← hTΓ]
      exact mem_image_of_mem _ hγ
    have h1 : Lρ ≤ ∫⁻ z in γ, ρ z ∂μH[1] :=
      iInf₂_le (f := fun γ' (_ : γ' ∈ Γ) => ∫⁻ z in γ', ρ z ∂μH[1]) γ hγ
    have h2 : Lρ ≤ ∫⁻ z in γ, ρt z ∂μH[1] := by
      have h3 : ∫⁻ z in γ, ρt z ∂μH[1] = ∫⁻ z in image T γ, ρ z ∂μH[1] := by
        rw [gm4c_sym_lintegral hΩ hTΩ hTT hT hγm hγΩ hm]
        exact setLIntegral_congr_fun hγm fun z hz => hρtΩ z (hγΩ hz)
      rw [h3]
      exact iInf₂_le _ hTγ
    calc Lρ
        = (2⁻¹ + 2⁻¹) * Lρ := by
          rw [ENNReal.inv_two_add_inv_two, one_mul]
      _ = 2⁻¹ * Lρ +
            2⁻¹ * Lρ := by rw [add_mul]
      _ ≤ 2⁻¹ * ∫⁻ z in γ, ρ z ∂μH[1] + 2⁻¹ * ∫⁻ z in γ, ρt z ∂μH[1] := by gcongr
      _ = ∫⁻ z in γ, ρ' z ∂μH[1] := by
          rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 two_ne_zero),
            ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 two_ne_zero), ← lintegral_add_left]
          · exact lintegral_congr fun z => by simp only [hρ']; ring
          · exact hm.const_mul _

/-- **The symmetry rule** (Ch. IV §3), (3.4) (cited at P1:6122, P2:24, and in App. H, P3:4841, 4915). Let
`T : Ω → Ω` satisfy `T ∘ T(z) = z` and suppose that either `T(z)` or `\overline{T(z)}` is analytic. If `Γ` is a path
family in `Ω` such that `T(Γ) = Γ`, then (3.4) `λ(Γ) = sup {L²(Γ, ρ)/A(Ω, ρ) : ρ = (ρ ∘ T) |J_T|}`, where
`|J_T| = |T'|` when `T` is analytic and `|J_T| = |\overline{T}'|` when `\overline{T(z)}` is analytic.
Modelling: `Ω` is a plane domain; `T` maps `Ω` into itself and is an involution there, analytic or anti-analytic
on `Ω`; `T(Γ) = {T(γ) : γ ∈ Γ}`; `|J_T|(z)` is the operator norm of the real derivative of `T` at `z`, which is
`|T'(z)|` for analytic `T` and `|(\overline{T})'(z)|` for anti-analytic `T`; the supremum is over the metrics
(`LiZhongQC.densitiesP0 Ω`) with `ρ(z) = ρ(T(z)) |J_T(z)|` for `z ∈ Ω` (the formula (3.4) was checked against the
equation image). -/
theorem symmetry_rule {Ω : Set ℂ} (hΩ : IsOpen Ω ∧ IsConnected Ω) {T : ℂ → ℂ} (hTΩ : MapsTo T Ω Ω)
    (hTT : ∀ z ∈ Ω, T (T z) = z)
    (hT : DifferentiableOn ℂ T Ω ∨ DifferentiableOn ℂ (fun z => (starRingEnd ℂ) (T z)) Ω) {Γ : Set (Set ℂ)}
    (hΓ : IsPathFamily Ω Γ) (hTΓ : image T '' Γ = Γ) :
    extremalLengthGM Ω Γ = ⨆ (ρ : ℂ → ℝ≥0∞) (_ : ρ ∈ densitiesP0 Ω) (_ : ∀ z ∈ Ω, ρ z = ρ (T z) * ‖fderiv ℝ T z‖ₑ),
      pathRhoLength Γ ρ ^ 2 / rhoArea ρ Ω := by
  refine le_antisymm ?_ ?_
  · rw [gm4a_extremalLengthGM_eq]
    refine iSup₂_le fun ρ hρ => ?_
    obtain ⟨ρ', hρ', hsym, hL, hA⟩ := gm4c_sym_average hΩ.1 hTΩ hTT hT hΓ hTΓ hρ
    refine le_trans ?_ (le_iSup₂_of_le ρ' hρ' (le_iSup_of_le hsym le_rfl))
    exact ENNReal.div_le_div (pow_le_pow_left' hL 2)
      hA
  · exact iSup₂_le fun ρ hρ => iSup_le fun _ => gm4a_ratio_le hρ

end GarnettMarshall2005
