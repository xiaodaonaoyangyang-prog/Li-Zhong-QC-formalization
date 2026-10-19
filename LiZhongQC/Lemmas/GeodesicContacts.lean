import LiZhongQC.Ch07.S25_QuadraticDifferentials
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
/- Insert immediately before thm25_3_unique_geodesic, within namespace LiZhongQC. -/

/-- Only finitely many zeros of a nonzero holomorphic coefficient lie on a compact trace. -/
theorem s25fc_trace_zeros_finite {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ) :
    {z ∈ γ.closedTrace | φ z = 0}.Finite := by
  classical
  obtain ⟨K, hK⟩ := hγ.1
  have hcompact : IsCompact γ.closedTrace :=
    isCompact_Icc.image_of_continuousOn hK.continuousOn
  obtain ⟨r, hr, htrace, Z, m, H, hZ, hH, hfactor⟩ :=
    b2_factor hφ hne hcompact hγ.2.1
  refine Z.finite_toSet.subset ?_
  intro z hz
  by_contra hzZ
  have hprod : (∏ a ∈ Z, (z - a) ^ m a) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.2
    intro a ha
    apply pow_ne_zero
    exact sub_ne_zero.2 (fun he => hzZ (he.symm ▸ ha))
  have he := hfactor z (htrace hz.1)
  rw [hz.2] at he
  exact (mul_ne_zero hprod (Complex.exp_ne_zero _)) he.symm

/-- A non-pausing curve with finite zero trace meets a regular point in every open interval. -/
theorem s25fc_regular_between {φ : ℂ → ℂ} {γ : LRCurve}
    (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    (hzeros : {z ∈ γ.closedTrace | φ z = 0}.Finite)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    ∃ u ∈ Ioo s t, φ (γ.toFun u) ≠ 0 := by
  by_contra! hzero
  let a : ℝ := (2 * s + t) / 3
  let b : ℝ := (s + 2 * t) / 3
  have hsa : s < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have hbt : b < t := by dsimp [b]; linarith
  have ha0 : 0 ≤ a := hs.trans hsa.le
  have hb1 : b ≤ 1 := hbt.le.trans ht
  obtain ⟨v, hv, hvne⟩ := hp a b ha0 hab hb1
  obtain ⟨K, hK⟩ := hγ.1
  have hsub : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha0 hb1
  have hconn : IsPreconnected (γ.toFun '' Icc a b) :=
    isPreconnected_Icc.image _ (hK.continuousOn.mono hsub)
  have hfin : (γ.toFun '' Icc a b).Finite := hzeros.subset (by
    rintro z ⟨u, hu, rfl⟩
    exact ⟨⟨u, hsub hu, rfl⟩, hzero u ⟨hsa.trans_le hu.1, hu.2.trans_lt hbt⟩⟩)
  have hnon : (γ.toFun '' Icc a b).Nontrivial :=
    ⟨γ.toFun v, ⟨v, hv, rfl⟩, γ.toFun a, ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩, hvne⟩
  exact (hconn.infinite_of_nontrivial hnon) hfin

/-- Non-pausing locally minimizing curves have positive length on every nontrivial interval.
This uses the existing regular chart identity, not global injectivity or a finite-chain hypothesis. -/
theorem s25fc_segment_pos {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    0 < phiSegmentLength φ γ s t := by
  obtain ⟨u, hu, hreg⟩ :=
    s25fc_regular_between hγ hp (s25fc_trace_zeros_finite hφ hne hγ) hs hst ht
  have hu01 : u ∈ Icc (0 : ℝ) 1 := ⟨hs.trans hu.1.le, hu.2.le.trans ht⟩
  obtain ⟨δ, hδ, ζ, ψ, W, w, hw, hWo, hWD, han, hinj, hopen, hψ, hmem, hseg⟩ :=
    s25g_local isOpen_ball hφ hγ hp hu01 hreg
  let a : ℝ := max s (u - δ / 2)
  let b : ℝ := min t (u + δ / 2)
  have hsa : s ≤ a := le_max_left _ _
  have hbt : b ≤ t := min_le_left _ _
  have hau : a < u := max_lt hu.1 (by linarith)
  have hub : u < b := lt_min hu.2 (by linarith)
  have hab : a < b := hau.trans hub
  have hal : u - δ < a := by
    have ha : u - δ / 2 ≤ a := le_max_right _ _
    linarith
  have hbr : b < u + δ := by
    have hb : b ≤ u + δ / 2 := min_le_right _ _
    linarith
  have ha01 : a ∈ Icc (0 : ℝ) 1 := ⟨hs.trans hsa, hab.le.trans (hbt.trans ht)⟩
  have hb01 : b ∈ Icc (0 : ℝ) 1 := ⟨ha01.1.trans hab.le, hbt.trans ht⟩
  obtain ⟨v, hv, hvne⟩ := hp a b ha01.1 hab hb01.2
  have hv01 : v ∈ Icc (0 : ℝ) 1 := ⟨ha01.1.trans hv.1, hv.2.trans hb01.2⟩
  by_contra hpos
  have hzero : phiSegmentLength φ γ s t = 0 := le_zero_iff.1 (not_lt.1 hpos)
  have hle : phiSegmentLength φ γ a v ≤ phiSegmentLength φ γ s t :=
    lintegral_mono_set (Ioo_subset_Ioo hsa (hv.2.trans hbt))
  have hav : phiSegmentLength φ γ a v = 0 := le_zero_iff.1 (hle.trans_eq hzero)
  have he := hseg a ha01 v hv01 hal hv.1 (hv.2.trans_lt hbr)
  simp only [hav, ENNReal.toReal_zero, Complex.ofReal_zero, mul_zero] at he
  exact hvne (hinj (hmem v hv01 (hal.trans_le hv.1) (hv.2.trans_lt hbr))
    (hmem a ha01 hal (hab.trans hbr)) (sub_eq_zero.1 he))

/-- The literal local distance equality and non-pausing imply local injectivity, including at zeros. -/
theorem s25fc_locally_injective {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ∃ δ > 0, InjOn γ.toFun (Icc (0 : ℝ) 1 ∩ Ioo (u - δ) (u + δ)) := by
  obtain ⟨δ, hδ, hwin⟩ := hγ.2.2 u hu
  refine ⟨δ, hδ, ?_⟩
  intro s hs t ht he
  by_contra hst
  rcases lt_or_gt_of_ne hst with hst | hts
  · have hpos := s25fc_segment_pos hφ hne hγ hp hs.1.1 hst ht.1.2
    have hlen := hwin s hs.1 t ht.1 hs.2.1 hst ht.2.2
    rw [← he, s25g_metricDist_self unitDisc _ (hγ.2.1 ⟨s, hs.1, rfl⟩)] at hlen
    rw [hlen] at hpos
    exact (lt_irrefl _ hpos)
  · have hpos := s25fc_segment_pos hφ hne hγ hp ht.1.1 hts hs.1.2
    have hlen := hwin t ht.1 s hs.1 ht.2.1 hts hs.2.2
    rw [he, s25g_metricDist_self unitDisc _ (hγ.2.1 ⟨t, ht.1, rfl⟩)] at hlen
    rw [hlen] at hpos
    exact (lt_irrefl _ hpos)

/-- Every point has finitely many parameter preimages on a non-pausing disc geodesic. -/
theorem s25fc_fiber_finite {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s) (z : ℂ) :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ γ.toFun t = z}.Finite := by
  obtain ⟨K, hK⟩ := hγ.1
  have hclosed : IsClosed {t : Icc (0 : ℝ) 1 | γ.toFun t = z} :=
    isClosed_eq hK.continuousOn.restrict continuous_const
  have heq : Subtype.val '' {t : Icc (0 : ℝ) 1 | γ.toFun t = z} =
      {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ γ.toFun t = z} := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, hu⟩
    · intro ht
      exact ⟨⟨t, ht.1⟩, ht.2, rfl⟩
  have hcompact : IsCompact {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ γ.toFun t = z} := by
    rw [← heq]
    exact hclosed.isCompact.image continuous_subtype_val
  apply hcompact.finite
  apply isDiscrete_iff_forall_mem_exists_isOpen.2
  intro u hu
  obtain ⟨δ, hδ, hinj⟩ := s25fc_locally_injective hφ hne hγ hp hu.1
  refine ⟨Ioo (u - δ) (u + δ), isOpen_Ioo, ?_⟩
  ext t
  constructor
  · intro ht
    apply mem_singleton_iff.2
    exact hinj ⟨ht.2.1, ht.1⟩ ⟨hu.1, ⟨by linarith, by linarith⟩⟩
      (ht.2.2.trans hu.2.symm)
  · intro ht
    have he : t = u := mem_singleton_iff.1 ht
    subst t
    exact ⟨⟨by linarith, by linarith⟩, hu⟩

/-- The zero set has a finite parameter preimage, without assuming global curve injectivity. -/
theorem s25fc_zero_contacts_finite {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s) :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ φ (γ.toFun t) = 0}.Finite := by
  have hZ := s25fc_trace_zeros_finite hφ hne hγ
  have hU : (⋃ z ∈ {z ∈ γ.closedTrace | φ z = 0},
      {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ γ.toFun t = z}).Finite :=
    hZ.biUnion fun z _ => s25fc_fiber_finite hφ hne hγ hp z
  refine hU.subset ?_
  intro t ht
  exact mem_iUnion.2 ⟨γ.toFun t,
    mem_iUnion.2 ⟨⟨⟨t, ht.1, rfl⟩, ht.2⟩, ⟨ht.1, rfl⟩⟩⟩

/-- Finitely many contact parameters cut the curve into regular intervals.
Every closed subinterval between contacts has the existing straight-arc parametrization. -/
theorem s25fc_finite_regular_pieces {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s) :
    ∃ P : Finset ℝ, 0 ∈ P ∧ 1 ∈ P ∧ (∀ t ∈ P, t ∈ Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, φ (γ.toFun t) = 0 → t ∈ P) ∧
      ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
        (∀ u ∈ Ioo a b, u ∉ P) →
        ∀ s t : ℝ, a < s → s < t → t < b →
          (∃ γ' : ℝ → ℂ, (∀ u ∈ Icc s t, γ' u = γ.toFun u) ∧
            IsPhiStraightArc φ γ' s t) ∨
          ∃ h : ℝ → ℝ, StrictMonoOn h (Icc s t) ∧ h '' Icc s t = Icc s t ∧
            IsPhiStraightArc φ (γ.toFun ∘ h) s t := by
  classical
  let Z := s25fc_zero_contacts_finite hφ hne hγ hp
  let P : Finset ℝ := insert 0 (insert 1 Z.toFinset)
  have hP : ∀ t ∈ Icc (0 : ℝ) 1, φ (γ.toFun t) = 0 → t ∈ P := by
    intro t ht hz
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Z.mem_toFinset.2 ⟨ht, hz⟩))
  refine ⟨P, by simp [P], by simp [P], ?_, hP, ?_⟩
  · intro t ht
    simp only [P, Finset.mem_insert, Set.Finite.mem_toFinset] at ht
    rcases ht with rfl | rfl | ht
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ht.1
  · intro a b ha hab hb hgap s t has hst htb
    have hreg : ∀ u ∈ Icc s t, φ (γ.toFun u) ≠ 0 := by
      intro u hu hz
      exact hgap u ⟨has.trans_le hu.1, hu.2.trans_lt htb⟩
        (hP u ⟨(ha.trans has.le).trans hu.1, hu.2.trans (htb.le.trans hb)⟩ hz)
    obtain ⟨γ', hstraight⟩ := s25g_part1 isOpen_ball hφ hγ hp s t
      (ha.trans has.le) hst (htb.le.trans hb) hreg
    rcases hstraight with hstraight | hstraight
    · exact Or.inl ⟨γ', hstraight⟩
    · exact Or.inr hstraight

end LiZhongQC
