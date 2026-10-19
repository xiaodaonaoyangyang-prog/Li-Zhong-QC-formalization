import LiZhongQC.Lemmas.GeodesicBigonGeometry
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real
noncomputable section
namespace LiZhongQC

/-- The open parameter interval of any actual side record lies strictly
between its original cut endpoints. -/
theorem s25bg_side_parameter_open {φ : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (S : s25cv_Side φ γ a b) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    S.par t ∈ Ioo a b := by
  have htI := Ioo_subset_Icc_self ht
  constructor
  · simpa only [S.first] using S.mono ⟨le_rfl, zero_le_one⟩ htI ht.1
  · simpa only [S.last] using S.mono htI ⟨zero_le_one, le_rfl⟩ ht.2

/-- Eliminate an actual extracted bigon after naming the second interval
in increasing order. Both endpoint pairings are handled; no chain, smooth
cover, corner bound, or no-cusp premise is supplied by the caller. -/
theorem s25bg_ordered_bigon_excluded {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ₁ γ₂ : LRCurve} (hγ₁ : IsPhiGeodesic φ unitDisc γ₁)
    (hγ₂ : IsPhiGeodesic φ unitDisc γ₂)
    (hp₁ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ₁.toFun u ≠ γ₁.toFun s)
    (hp₂ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ₂.toFun u ≠ γ₂.toFun s)
    (hi₁ : InjOn γ₁.toFun (Icc (0 : ℝ) 1)) (hi₂ : InjOn γ₂.toFun (Icc (0 : ℝ) 1))
    {a b u v : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1)
    (hpair : (γ₁.toFun a = γ₂.toFun u ∧ γ₁.toFun b = γ₂.toFun v) ∨
      (γ₁.toFun a = γ₂.toFun v ∧ γ₁.toFun b = γ₂.toFun u))
    (hoff : ∀ s ∈ Ioo a b, ∀ t ∈ Icc (0 : ℝ) 1, γ₁.toFun s ≠ γ₂.toFun t) : False := by
  classical
  obtain ⟨n, p, hn, hpm, hp0, hp1, hpI, ⟨S⟩⟩ := s25cv_actual_partition hφ hne hγ₁ hp₁ ha hab hb
  obtain ⟨m, q, hm, hqm, hq0, hq1, hqI, ⟨T⟩⟩ := s25cv_actual_partition hφ hne hγ₂ hp₂ hu huv hv
  letI : NeZero n := ⟨hn.ne'⟩
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero (n + m) := ⟨by omega⟩
  let L : Fin n → ℝ → ℂ := fun i => (S i).side
  let R : Fin m → ℝ → ℂ := fun j => (T j).side
  let iL : Fin n := ⟨n - 1, by omega⟩
  let iR : Fin m := ⟨m - 1, by omega⟩
  have hiL : iL.succ = Fin.last n := by apply Fin.ext; dsimp [iL]; omega
  have hiR : iR.succ = Fin.last m := by apply Fin.ext; dsimp [iR]; omega
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hLa : L 0 0 = γ₁.toFun a := by
    change (S 0).side 0 = γ₁.toFun a
    rw [(S 0).trace 0 h0, (S 0).first]
    change γ₁.toFun (p 0) = γ₁.toFun a
    rw [hp0]
  have hLb : L iL 1 = γ₁.toFun b := by
    change (S iL).side 1 = γ₁.toFun b
    rw [(S iL).trace 1 h1, (S iL).last, hiL, hp1]
  have hRu : R 0 0 = γ₂.toFun u := by
    change (T 0).side 0 = γ₂.toFun u
    rw [(T 0).trace 0 h0, (T 0).first]
    change γ₂.toFun (q 0) = γ₂.toFun u
    rw [hq0]
  have hRv : R iR 1 = γ₂.toFun v := by
    change (T iR).side 1 = γ₂.toFun v
    rw [(T iR).trace 1 h1, (T iR).last, hiR, hq1]
  have hSL : ∀ i : Fin n, 0 ≤ p i.castSucc ∧ p i.succ ≤ 1 :=
    fun i => ⟨ha.trans (hpI i.castSucc).1, (hpI i.succ).2.trans hb⟩
  have hTR : ∀ j : Fin m, 0 ≤ q j.castSucc ∧ q j.succ ≤ 1 :=
    fun j => ⟨hu.trans (hqI j.castSucc).1, (hqI j.succ).2.trans hv⟩
  have hcross : ∀ i : Fin n, ∀ j : Fin m,
      ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Ioo (0 : ℝ) 1, L i s ≠ R j t := by
    intro i j s hs t ht he
    have hs' := s25bg_side_parameter_open (S i) hs
    have ht' := (T j).bij.1 (Ioo_subset_Icc_self ht)
    apply hoff ((S i).par s)
      ⟨(hpI i.castSucc).1.trans_lt hs'.1, hs'.2.trans_le (hpI i.succ).2⟩
      ((T j).par t) ⟨(hTR j).1.trans ht'.1, ht'.2.trans (hTR j).2⟩
    rw [← (S i).trace s (Ioo_subset_Icc_self hs), ← (T j).trace t (Ioo_subset_Icc_self ht)]
    exact he
  have hfm : ∀ t ∈ Icc a b, γ₁.toFun t ∈ unitDisc :=
    fun t ht => hγ₁.2.1 ⟨t, ⟨ha.trans ht.1, ht.2.trans hb⟩, rfl⟩
  have hgm : ∀ t ∈ Icc u v, γ₂.toFun t ∈ unitDisc :=
    fun t ht => hγ₂.2.1 ⟨t, ⟨hu.trans ht.1, ht.2.trans hv⟩, rfl⟩
  have hblL : ∀ i : Fin n, i ≠ 0 → fx_IsBlunt φ L i := by
    intro i hi
    exact (s25ic_partition_interior_corner hφ hne hγ₁ hp₁ hpm
      (by rw [hp0]; exact ha) (by rw [hp1]; exact hb)
      (fun j => (S j).mono) (fun j => (S j).bij) (fun j => (S j).first) (fun j => (S j).last)
      (fun j => (S j).trace) (fun j => (S j).smooth)
      (fun j => (S j).regular 0 h0) (fun j => (S j).regular 1 h1) i hi).1
  have hblR : ∀ j : Fin m, j ≠ 0 → fx_IsBlunt φ R j := by
    intro j hj
    exact (s25ic_partition_interior_corner hφ hne hγ₂ hp₂ hqm
      (by rw [hq0]; exact hu) (by rw [hq1]; exact hv)
      (fun i => (T i).mono) (fun i => (T i).bij) (fun i => (T i).first) (fun i => (T i).last)
      (fun i => (T i).trace) (fun i => (T i).smooth)
      (fun i => (T i).regular 0 h0) (fun i => (T i).regular 1 h1) j hj).1
  rcases hpair with hpair | hpair
  · have hbase := s25bj_raw_forward_reverse_fields hn hm hi₁ hi₂ ha hab hb hu huv hv
      hpair.1 hpair.2 hoff hfm hgm hpm hqm hp0 hp1 hq0 hq1
      (fun j => (S j).mono) (fun j => (T j).mono)
      (fun j => (S j).first) (fun j => (S j).last) (fun j => (T j).first) (fun j => (T j).last)
      (fun j => (S j).trace) (fun j => (T j).trace)
      (fun j => (S j).straight) (fun j => (T j).straight)
      (fun j => (S j).smooth) (fun j => (T j).smooth)
      (fun j => (S j).regular) (fun j => (T j).regular)
    have hstart : arg (derivWithin (R 0) (Icc 0 1) 0 / derivWithin (L 0) (Icc 0 1) 0) ≠ 0 := by
      have h := s25bg_side_endpoint_no_cusp hφ hne hγ₂ hγ₁ hp₂ hp₁
        (hTR 0).1 (hTR 0).2 (hSL 0).1 (hSL 0).2 (T 0) (S 0)
        (x := 0) (y := 0) (Or.inl rfl) (Or.inl rfl)
        (by change R 0 0 = L 0 0; rw [hRu, hLa]; exact hpair.1.symm)
        (fun s hs t ht he => hcross 0 0 t ht s hs he.symm)
      simpa using h
    have hend : arg (derivWithin (L iL) (Icc 0 1) 1 / derivWithin (R iR) (Icc 0 1) 1) ≠ 0 := by
      have h := s25bg_side_endpoint_no_cusp hφ hne hγ₁ hγ₂ hp₁ hp₂
        (hSL iL).1 (hSL iL).2 (hTR iR).1 (hTR iR).2 (S iL) (T iR)
        (x := 1) (y := 1) (Or.inr rfl) (Or.inr rfl)
        (by change L iL 1 = R iR 1; rw [hLb, hRv]; exact hpair.2) (hcross iL iR)
      norm_num at h
      simpa only [L, R] using h
    obtain ⟨hchain, hbl⟩ := s25bc_forward_reverse_completion hn hm hbase
      (fun j => (T j).smooth) hblL hblR hstart hend
    exact s25gb_chain_excluded hφ hne hchain {0, ⟨n, by omega⟩}
      (s25bj_junction_card hm) hbl
  · have hbase := s25bj_raw_oriented_fields hn hm hi₁ hi₂ ha hab hb hu huv hv
      hpair.1 hpair.2 hoff hfm hgm hpm hqm hp0 hp1 hq0 hq1
      (fun j => (S j).mono) (fun j => (T j).mono)
      (fun j => (S j).first) (fun j => (S j).last) (fun j => (T j).first) (fun j => (T j).last)
      (fun j => (S j).trace) (fun j => (T j).trace)
      (fun j => (S j).straight) (fun j => (T j).straight)
      (fun j => (S j).smooth) (fun j => (T j).smooth)
      (fun j => (S j).regular) (fun j => (T j).regular)
    have hstart : arg (-derivWithin (R iR) (Icc 0 1) 1 / derivWithin (L 0) (Icc 0 1) 0) ≠ 0 := by
      have h := s25bg_side_endpoint_no_cusp hφ hne hγ₂ hγ₁ hp₂ hp₁
        (hTR iR).1 (hTR iR).2 (hSL 0).1 (hSL 0).2 (T iR) (S 0)
        (x := 1) (y := 0) (Or.inr rfl) (Or.inl rfl)
        (by change R iR 1 = L 0 0; rw [hRv, hLa]; exact hpair.1.symm)
        (fun s hs t ht he => hcross 0 iR t ht s hs he.symm)
      norm_num at h
      simpa only [L, R] using h
    have hend : arg (-derivWithin (L iL) (Icc 0 1) 1 / derivWithin (R 0) (Icc 0 1) 0) ≠ 0 := by
      have h := s25bg_side_endpoint_no_cusp hφ hne hγ₁ hγ₂ hp₁ hp₂
        (hSL iL).1 (hSL iL).2 (hTR 0).1 (hTR 0).2 (S iL) (T 0)
        (x := 1) (y := 0) (Or.inr rfl) (Or.inl rfl)
        (by change L iL 1 = R 0 0; rw [hLb, hRu]; exact hpair.2) (hcross iL 0)
      norm_num at h
      simpa only [L, R] using h
    obtain ⟨hchain, hbl⟩ := s25bc_direct_completion hn hm hbase hblL hblR hstart hend
    exact s25gb_chain_excluded hφ hne hchain {0, ⟨n, by omega⟩}
      (s25bj_junction_card hm) hbl

/-- The raw extracted second endpoints need not be ordered. -/
theorem s25bg_bigon_excluded {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ₁ γ₂ : LRCurve} (hγ₁ : IsPhiGeodesic φ unitDisc γ₁)
    (hγ₂ : IsPhiGeodesic φ unitDisc γ₂)
    (hp₁ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ₁.toFun u ≠ γ₁.toFun s)
    (hp₂ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ₂.toFun u ≠ γ₂.toFun s)
    (hi₁ : InjOn γ₁.toFun (Icc (0 : ℝ) 1)) (hi₂ : InjOn γ₂.toFun (Icc (0 : ℝ) 1))
    {a b u v : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (huv : u ≠ v)
    (he0 : γ₁.toFun a = γ₂.toFun u) (he1 : γ₁.toFun b = γ₂.toFun v)
    (hoff : ∀ s ∈ Ioo a b, ∀ t ∈ Icc (0 : ℝ) 1, γ₁.toFun s ≠ γ₂.toFun t) : False := by
  rcases lt_or_gt_of_ne huv with h | h
  · exact s25bg_ordered_bigon_excluded hφ hne hγ₁ hγ₂ hp₁ hp₂ hi₁ hi₂
      ha hab hb hu.1 h hv.2 (Or.inl ⟨he0, he1⟩) hoff
  · exact s25bg_ordered_bigon_excluded hφ hne hγ₁ hγ₂ hp₁ hp₂ hi₁ hi₂
      ha hab hb hv.1 h hu.2 (Or.inr ⟨he0, he1⟩) hoff

end LiZhongQC

