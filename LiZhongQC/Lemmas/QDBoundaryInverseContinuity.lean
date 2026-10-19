import LiZhongQC.Lemmas.QDReflectionAfterHalves
import LiZhongQC.Lemmas.QDReflectionPuncturePoles
import LiZhongQC.Lemmas.QDTransportZero
import LiZhongQC.Lemmas.QDSeamFill
import LiZhongQC.Lemmas.SchottkyCollarFromDouble

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- The exterior of a bounded Jordan domain is locally connected at its frontier points: every
neighbourhood `N` of a frontier point `p` contains a connected subset `C` of the exterior that contains
the whole exterior part of a smaller neighbourhood `M` of `p`. -/
theorem s31qe_exterior_loc_conn {Jd : Set ℂ} (hJd : IsJordanDomain Jd)
    (hbd : Bornology.IsBounded Jd) {p : ℂ} (hp : p ∈ frontier Jd) {N : Set ℂ} (hN : N ∈ 𝓝 p) :
    ∃ M ∈ 𝓝 p, ∃ C : Set ℂ, IsPreconnected C ∧ C ⊆ N ∩ (closure Jd)ᶜ ∧
      M ∩ (closure Jd)ᶜ ⊆ C := by
  classical
  have hpJ : p ∉ Jd := by
    intro h
    have := hp.2
    rw [hJd.1.interior_eq] at this
    exact this h
  have hpC : (p : ExtPlane) ∈ (toExt Jd)ᶜ := coe_mem_compl_toExt_iff.2 hpJ
  have hcl : closure (toExt Jd) = toExt (closure Jd) := closure_toExt_of_isBounded' hbd
  let p' : ↥((toExt Jd)ᶜ) := ⟨(p : ExtPlane), hpC⟩
  have hp' : p'.val ∈ frontier (toExt Jd) := by
    refine ⟨?_, ?_⟩
    · rw [hcl]
      exact coe_mem_toExt_iff.2 hp.1
    · intro h
      exact hpJ (coe_mem_toExt_iff.1 (interior_subset h))
  obtain ⟨g, V, hVo, hpV, h, -, h0, hiff, -⟩ :=
    s78ra_exterior_boundary_halfchart hJd hbd p' hp'
  let x0 : ↥V := ⟨p', hpV⟩
  have hx0 : (h x0).val = 0 := h0 hpV
  have hNe : ((↑) : ℂ → ExtPlane) '' N ∈ 𝓝 (p : ExtPlane) :=
    (OnePoint.isOpenEmbedding_coe.isOpenMap).image_mem_nhds hN
  have hS : {x : ↥V | x.val.val ∈ ((↑) : ℂ → ExtPlane) '' N} ∈ 𝓝 x0 := by
    have hc : Continuous (fun x : ↥V => x.val.val) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact hc.continuousAt.preimage_mem_nhds hNe
  have hD : h '' {x : ↥V | x.val.val ∈ ((↑) : ℂ → ExtPlane) '' N} ∈ 𝓝 (h x0) :=
    h.isOpenMap.image_mem_nhds hS
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.1 hD
  -- the half disc in the chart
  have hin : ∀ u : {z : ℂ | 0 ≤ z.im}, ‖u.val‖ < s →
      u ∈ h '' {x : ↥V | x.val.val ∈ ((↑) : ℂ → ExtPlane) '' N} := by
    intro u hu
    apply hball
    rw [Metric.mem_ball, Subtype.dist_eq, hx0, dist_zero_right]
    exact hu
  let Dc : Set ℂ := {z : ℂ | ‖z‖ < s ∧ 0 < z.im}
  have hDc : Convex ℝ Dc := by
    have h1 : Convex ℝ {z : ℂ | ‖z‖ < s} := by
      have := convex_ball (0 : ℂ) s
      convert this using 1
      ext z
      simp [dist_zero_right]
    exact h1.inter (convex_halfSpace_im_gt 0)
  haveI : PreconnectedSpace ↥Dc := Subtype.preconnectedSpace hDc.isPreconnected
  let Φ : {z : ℂ | 0 ≤ z.im} → ExtPlane := fun u => (h.symm u).val.val
  have hΦc : Continuous Φ :=
    continuous_subtype_val.comp (continuous_subtype_val.comp h.symm.continuous)
  let Φ' : ↥Dc → ExtPlane := fun z => Φ ⟨z.1, z.2.2.le⟩
  have hΦ'c : Continuous Φ' :=
    hΦc.comp (Continuous.subtype_mk continuous_subtype_val _)
  have hpre : IsPreconnected (range Φ') := isPreconnected_range hΦ'c
  -- facts on points of the half disc
  have hpt : ∀ zz : ↥Dc, ∃ x : ↥V, h x = ⟨zz.1, zz.2.2.le⟩ ∧
      x.val.val ∈ ((↑) : ℂ → ExtPlane) '' N ∧ Φ' zz = x.val.val := by
    intro zz
    obtain ⟨x, hx, hxe⟩ := hin ⟨zz.1, zz.2.2.le⟩ zz.2.1
    refine ⟨x, hxe, hx, ?_⟩
    change (h.symm ⟨zz.1, zz.2.2.le⟩).val.val = x.val.val
    rw [← hxe]
    simp
  have hrange : range Φ' ⊆ range ((↑) : ℂ → ExtPlane) := by
    rintro _ ⟨zz, rfl⟩
    obtain ⟨x, -, ⟨w, -, hw⟩, he⟩ := hpt zz
    exact ⟨w, by rw [he, ← hw]⟩
  let C : Set ℂ := ((↑) : ℂ → ExtPlane) ⁻¹' range Φ'
  have hCimg : ((↑) : ℂ → ExtPlane) '' C = range Φ' :=
    Set.image_preimage_eq_of_subset hrange
  have hCpre : IsPreconnected C := by
    rw [← OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image, hCimg]
    exact hpre
  -- the neighbourhood M
  let OK : Set ↥((toExt Jd)ᶜ) :=
    Subtype.val '' {x : ↥V | ‖(h x).val‖ < s}
  have hOKopen : IsOpen OK := by
    apply hVo.isOpenMap_subtype_val
    exact isOpen_lt (continuous_norm.comp (continuous_subtype_val.comp h.continuous))
      continuous_const
  obtain ⟨O, hOo, hOe⟩ := isOpen_induced_iff.1 hOKopen
  have hx0O : p' ∈ OK := ⟨x0, by simp [x0, hx0, hs], rfl⟩
  have hpO : (p : ExtPlane) ∈ O := by
    have : p' ∈ Subtype.val ⁻¹' O := by rw [hOe]; exact hx0O
    exact this
  refine ⟨((↑) : ℂ → ExtPlane) ⁻¹' O, ?_, C, hCpre, ?_, ?_⟩
  · exact (hOo.preimage OnePoint.continuous_coe).mem_nhds hpO
  · intro z hz
    obtain ⟨zz, hzz⟩ := hz
    obtain ⟨x, hxh, ⟨w, hwN, hw⟩, he⟩ := hpt zz
    have hzw : z = w := OnePoint.coe_injective (hzz.symm.trans (he.trans hw.symm))
    refine ⟨hzw ▸ hwN, ?_⟩
    intro hzc
    have h1 : 0 < (h x).val.im := by rw [hxh]; exact zz.2.2
    have h2 := (hiff x).1 h1
    apply h2
    rw [hcl]
    have : x.val.val = (z : ExtPlane) := by rw [← he, hzz]
    rw [this]
    exact coe_mem_toExt_iff.2 hzc
  · rintro z ⟨hzO, hzE⟩
    have hzJ : z ∉ Jd := fun h' => hzE (subset_closure h')
    have hzC : (z : ExtPlane) ∈ (toExt Jd)ᶜ := coe_mem_compl_toExt_iff.2 hzJ
    have hk : (⟨(z : ExtPlane), hzC⟩ : ↥((toExt Jd)ᶜ)) ∈ OK := by
      rw [← hOe]
      exact hzO
    obtain ⟨x, hxs, hxe⟩ := hk
    have h1 : 0 < (h x).val.im := by
      apply (hiff x).2
      rw [hcl, hxe]
      intro hm
      exact hzE (coe_mem_toExt_iff.1 hm)
    let zz : ↥Dc := ⟨(h x).val, hxs, h1⟩
    refine ⟨zz, ?_⟩
    change Φ ⟨(h x).val, _⟩ = (z : ExtPlane)
    change (h.symm ⟨(h x).val, _⟩).val.val = _
    have : (⟨(h x).val, (h x).property⟩ : {z : ℂ | 0 ≤ z.im}) = h x := rfl
    simp only [this, Homeomorph.symm_apply_apply]
    rw [hxe]

theorem s31qe_inverse_continuity
    {Jd : Set ℂ} (hJd : IsJordanDomain Jd) (hbd : Bornology.IsBounded Jd)
    {r : ℝ} (hr : 0 < r) {κ : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hcont : ContinuousOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hκinj : InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hup : MapsTo κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} (closure Jd)ᶜ)
    (hreal : MapsTo κ {z : ℂ | ‖z‖ < r ∧ z.im = 0} (frontier Jd))
    (hlocal : ∃ V : Set ℂ, IsOpen V ∧ κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} = V ∩ Jdᶜ)
    {t : ℝ} (ht : |t| < r) :
    ∀ ε > 0, ∃ δ > 0, ∀ w : ℂ, ‖w‖ < r → 0 ≤ w.im → ‖κ w - κ t‖ < δ → ‖w - t‖ < ε := by
  classical
  intro ε hε
  set H : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} with hH
  set B : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 < z.im} with hB
  have hBH : B ⊆ H := fun z hz => ⟨hz.1, hz.2.le⟩
  have hBopen : IsOpen B :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const Complex.continuous_im)
  have hnt : ‖(t : ℂ)‖ = |t| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have htH : (t : ℂ) ∈ H := ⟨by rw [hnt]; exact ht, by simp⟩
  have hnI : ∀ η : ℝ, 0 < η → ‖(η : ℂ) * I‖ = η := by
    intro η hη
    simp [abs_of_pos hη]
  -- openness of images of open subsets of `B`
  have hOpenImg : ∀ U : Set ℂ, IsOpen U → U ⊆ B → IsOpen (κ '' U) := by
    intro U hU hUB
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨w, hwU, rfl⟩
    have hana : AnalyticAt ℂ κ w := (hhol.analyticOnNhd hBopen) w (hUB hwU)
    rcases hana.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
    · exfalso
      have h1 : ∀ᶠ z in 𝓝[≠] w, κ z = κ w ∧ z ∈ U ∧ z ≠ w := by
        filter_upwards [hconst.filter_mono nhdsWithin_le_nhds,
          eventually_nhdsWithin_of_eventually_nhds (hU.mem_nhds hwU), self_mem_nhdsWithin]
          with z a b c
        exact ⟨a, b, c⟩
      obtain ⟨z, hz1, hz2, hz3⟩ := h1.exists
      have := hκinj (hBH (hUB hz2)) (hBH (hUB hwU)) hz1
      exact hz3 this
    · exact hopen (Filter.image_mem_map (hU.mem_nhds hwU))
  -- the working radius
  set e : ℝ := min ε ((r - |t|) / 2) with he
  have he0 : 0 < e := lt_min hε (by linarith)
  have heε : e ≤ ε := min_le_left _ _
  have her : e ≤ (r - |t|) / 2 := min_le_right _ _
  -- the compact annulus
  let A : Set ℂ := {w : ℂ | e / 2 ≤ ‖w - t‖ ∧ ‖w - t‖ ≤ e ∧ 0 ≤ w.im}
  have hAcl : IsClosed A :=
    ((isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).inter
      ((isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).inter
        (isClosed_le continuous_const Complex.continuous_im)))
  have hAc : IsCompact A := by
    refine (isCompact_closedBall (t : ℂ) e).of_isClosed_subset hAcl ?_
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    exact hw.2.1
  have hAH : A ⊆ H := by
    intro w hw
    refine ⟨?_, hw.2.2⟩
    have h1 : ‖w‖ ≤ ‖w - t‖ + ‖(t : ℂ)‖ := by
      calc ‖w‖ = ‖(w - t) + t‖ := by ring_nf
        _ ≤ ‖w - t‖ + ‖(t : ℂ)‖ := norm_add_le _ _
    rw [hnt] at h1
    linarith [hw.2.1]
  have hκA : IsCompact (κ '' A) := hAc.image_of_continuousOn (hcont.mono hAH)
  have hκtA : κ (t : ℂ) ∉ κ '' A := by
    rintro ⟨a, ha, hae⟩
    have := hκinj (hAH ha) htH hae
    have h2 := ha.1
    rw [this, sub_self, norm_zero] at h2
    linarith
  obtain ⟨V, hVo, hV⟩ := hlocal
  have hκtV : κ (t : ℂ) ∈ V := by
    have : κ (t : ℂ) ∈ κ '' H := mem_image_of_mem κ htH
    rw [hV] at this
    exact this.1
  have hNmem : (κ '' A)ᶜ ∩ V ∈ 𝓝 (κ (t : ℂ)) :=
    Filter.inter_mem (hκA.isClosed.isOpen_compl.mem_nhds hκtA) (hVo.mem_nhds hκtV)
  have hpfr : κ (t : ℂ) ∈ frontier Jd := hreal ⟨by rw [hnt]; exact ht, by simp⟩
  obtain ⟨M, hM, C, hCpre, hCsub, hMC⟩ := s31qe_exterior_loc_conn hJd hbd hpfr hNmem
  -- exterior points of the image of `H` come from `B`
  have hVext : ∀ y ∈ V, y ∈ (closure Jd)ᶜ → y ∈ κ '' B := by
    intro y hyV hyE
    have hyJ : y ∈ V ∩ Jdᶜ := ⟨hyV, fun h => hyE (subset_closure h)⟩
    rw [← hV] at hyJ
    obtain ⟨w, hwH, rfl⟩ := hyJ
    refine ⟨w, ⟨hwH.1, lt_of_le_of_ne hwH.2 ?_⟩, rfl⟩
    intro him
    have hf := hreal ⟨hwH.1, him.symm⟩
    exact hyE (frontier_subset_closure hf)
  have hCB : C ⊆ κ '' B := fun y hy => hVext y (hCsub hy).1.2 (hCsub hy).2
  have hCA : ∀ y ∈ C, y ∉ κ '' A := fun y hy => (hCsub hy).1.1
  -- the two pieces
  let Bin : Set ℂ := B ∩ {w | ‖w - t‖ < e / 2}
  let Bout : Set ℂ := B ∩ {w | e < ‖w - t‖}
  have hBinO : IsOpen Bin :=
    hBopen.inter (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const)
  have hBoutO : IsOpen Bout :=
    hBopen.inter (isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
  have hdisj : Disjoint (κ '' Bin) (κ '' Bout) := by
    rw [Set.disjoint_left]
    rintro _ ⟨w1, hw1, rfl⟩ ⟨w2, hw2, he2⟩
    have := hκinj (hBH hw2.1) (hBH hw1.1) he2
    rw [this] at hw2
    have h1 := hw1.2
    have h2 := hw2.2
    simp only [mem_setOf_eq] at h1 h2
    linarith
  have hcover : C ⊆ κ '' Bin ∪ κ '' Bout := by
    intro y hy
    obtain ⟨w, hwB, rfl⟩ := hCB hy
    have hwA : w ∉ A := fun hA => hCA _ hy ⟨w, hA, rfl⟩
    by_cases h1 : ‖w - t‖ < e / 2
    · exact Or.inl ⟨w, ⟨hwB, h1⟩, rfl⟩
    · refine Or.inr ⟨w, ⟨hwB, ?_⟩, rfl⟩
      by_contra h2
      exact hwA ⟨not_lt.1 h1, not_lt.1 h2, hwB.2.le⟩
  have hsub := hCpre.subset_or_subset (hOpenImg _ hBinO inter_subset_left)
    (hOpenImg _ hBoutO inter_subset_left) hdisj hcover
  -- a point of `B` close to `t`
  have hCin : C ⊆ κ '' Bin := by
    rcases hsub with h | h
    · exact h
    · exfalso
      have hcw : ContinuousWithinAt κ H (t : ℂ) := hcont _ htH
      have hpre : κ ⁻¹' M ∈ 𝓝[H] (t : ℂ) := hcw.preimage_mem_nhdsWithin hM
      obtain ⟨u, huo, htu, hu⟩ := mem_nhdsWithin.1 hpre
      obtain ⟨ρ, hρ, hρu⟩ := Metric.isOpen_iff.1 huo _ htu
      set η : ℝ := min (ρ / 2) (e / 4) with hη
      have hη0 : 0 < η := lt_min (by linarith) (by linarith)
      have hηρ : η < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hηe : η ≤ e / 4 := min_le_right _ _
      let w : ℂ := (t : ℂ) + (η : ℂ) * I
      have hwt : ‖w - t‖ = η := by
        change ‖(t : ℂ) + (η : ℂ) * I - t‖ = η
        rw [add_sub_cancel_left]
        exact hnI η hη0
      have hwB : w ∈ B := by
        refine ⟨?_, ?_⟩
        · calc ‖w‖ ≤ ‖(t : ℂ)‖ + ‖(η : ℂ) * I‖ := norm_add_le _ _
            _ = |t| + η := by rw [hnt, hnI η hη0]
            _ < r := by linarith
        · simp [w, hη0]
      have hwu : w ∈ u := hρu (by rw [mem_ball, dist_eq_norm, hwt]; exact hηρ)
      have hwM : κ w ∈ M := hu ⟨hwu, hBH hwB⟩
      have hwC : κ w ∈ C := hMC ⟨hwM, hup hwB⟩
      obtain ⟨w2, hw2, hw2e⟩ := h hwC
      have := hκinj (hBH hw2.1) (hBH hwB) hw2e
      rw [this] at hw2
      have h2 : e < ‖w - t‖ := hw2.2
      rw [hwt] at h2
      linarith
  -- the final radius
  obtain ⟨δ₀, hδ₀, hδM⟩ := Metric.mem_nhds_iff.1 hM
  refine ⟨δ₀, hδ₀, ?_⟩
  intro w1 hw1r hw1i hκw1
  have hw1H : w1 ∈ H := ⟨hw1r, hw1i⟩
  have hcw1 : ContinuousWithinAt κ H w1 := hcont _ hw1H
  have hκw1' : ‖κ w1 - κ (t : ℂ)‖ < δ₀ := hκw1
  have hε1 : 0 < δ₀ - ‖κ w1 - κ (t : ℂ)‖ := by linarith
  obtain ⟨ρ1, hρ1, hz⟩ := Metric.continuousWithinAt_iff.1 hcw1 _ hε1
  set η : ℝ := min (min (ρ1 / 2) (e / 4)) ((r - ‖w1‖) / 2) with hη
  have hη0 : 0 < η := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hηρ : η < ρ1 := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
  have hηe : η ≤ e / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hηr : η ≤ (r - ‖w1‖) / 2 := min_le_right _ _
  let z : ℂ := w1 + (η : ℂ) * I
  have hzw : ‖z - w1‖ = η := by
    change ‖w1 + (η : ℂ) * I - w1‖ = η
    rw [add_sub_cancel_left]
    exact hnI η hη0
  have hzB : z ∈ B := by
    refine ⟨?_, ?_⟩
    · calc ‖z‖ ≤ ‖w1‖ + ‖(η : ℂ) * I‖ := norm_add_le _ _
        _ = ‖w1‖ + η := by rw [hnI η hη0]
        _ < r := by linarith
    · simp [z, hη0]
      linarith
  have hzK : ‖κ z - κ (t : ℂ)‖ < δ₀ := by
    have h1 := hz (hBH hzB) (by rw [dist_eq_norm, hzw]; exact hηρ)
    rw [dist_eq_norm] at h1
    calc ‖κ z - κ (t : ℂ)‖ = ‖(κ z - κ w1) + (κ w1 - κ (t : ℂ))‖ := by ring_nf
      _ ≤ ‖κ z - κ w1‖ + ‖κ w1 - κ (t : ℂ)‖ := norm_add_le _ _
      _ < δ₀ := by linarith
  have hzM : κ z ∈ M := hδM (by rw [mem_ball, dist_eq_norm]; exact hzK)
  have hzC : κ z ∈ C := hMC ⟨hzM, hup hzB⟩
  obtain ⟨z2, hz2, hz2e⟩ := hCin hzC
  have := hκinj (hBH hz2.1) (hBH hzB) hz2e
  rw [this] at hz2
  have h2 : ‖z - t‖ < e / 2 := hz2.2
  have h3 : ‖w1 - t‖ ≤ ‖z - t‖ + ‖z - w1‖ := by
    calc ‖w1 - t‖ = ‖(z - t) - (z - w1)‖ := by ring_nf
      _ ≤ ‖z - t‖ + ‖z - w1‖ := norm_sub_le _ _
  rw [hzw] at h3
  linarith

end LiZhongQC
