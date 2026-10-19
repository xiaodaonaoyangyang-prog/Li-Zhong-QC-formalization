import LiZhongQC.Lemmas.GeodesicArbitraryZeroSides
import LiZhongQC.Lemmas.GeodesicRegularJoins
import LiZhongQC.Lemmas.GeodesicParameterContinuity
/-! Actual interior-corner consumers for either loop or bigon side families.
The geometric angle results are invoked directly; no angle hypothesis is added. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ContDiff
namespace LiZhongQC

/-- At a noninitial cyclic vertex, the preceding side ends at the same cut at
which the current side starts. The wraparound vertex is deliberately excluded. -/
theorem s25sl_previous_cut {n : ℕ} [NeZero n] (j : Fin n) (hj : j ≠ 0) :
    (j - 1).succ = j.castSucc := by
  rcases s25gb_cyclic_cuts (j - 1) with h | h
  · simpa only [sub_add_cancel] using h.symm
  · have hz : j.castSucc = (0 : Fin (n + 1)) := by
      simpa only [sub_add_cancel] using h.2
    apply False.elim
    apply hj
    apply Fin.ext
    exact congrArg (fun x : Fin (n + 1) => x.val) hz

/-- Adjacent increasing representatives of one actual geodesic form a blunt,
non-cuspidal corner at every interior original time, regular or zero.
This local theorem can be used inside a loop or inside either arm of a bigon. -/
theorem s25ic_actual_interior_corner {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hpause : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ} (j : Fin n)
    {pL pR : ℝ → ℝ} {a t₀ b : ℝ}
    (ha : 0 ≤ a) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hb : b ≤ 1)
    (hL : ContDiffOn ℝ 1 (side (j - 1)) (Icc 0 1))
    (hR : ContDiffOn ℝ 1 (side j) (Icc 0 1))
    (hmL : StrictMonoOn pL (Icc (0 : ℝ) 1))
    (hmR : StrictMonoOn pR (Icc (0 : ℝ) 1))
    (hbijL : BijOn pL (Icc (0 : ℝ) 1) (Icc a t₀))
    (hbijR : BijOn pR (Icc (0 : ℝ) 1) (Icc t₀ b))
    (hL1 : pL 1 = t₀) (hR0 : pR 0 = t₀)
    (heL : ∀ t ∈ Icc (0 : ℝ) 1, side (j - 1) t = γ.toFun (pL t))
    (heR : ∀ t ∈ Icc (0 : ℝ) 1, side j t = γ.toFun (pR t))
    (hdL : derivWithin (side (j - 1)) (Icc 0 1) 1 ≠ 0)
    (hdR : derivWithin (side j) (Icc 0 1) 0 ≠ 0) :
    fx_IsBlunt φ side j ∧
      arg (-derivWithin (side (j - 1)) (Icc 0 1) 1 /
        derivWithin (side j) (Icc 0 1) 0) ≠ 0 := by
  by_cases hz : φ (γ.toFun t₀) = 0
  · exact (s25ep_arbitrary_zero_join hφ hne hγ hpause ht₀ hz j
      hL hR hmL hmR hbijL hbijR hL1 hR0 heL heR hdL hdR).2
  · have hiL : MapsTo pL (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
      intro t ht
      have h := hbijL.1 ht
      exact ⟨ha.trans h.1, h.2.trans ht₀.2.le⟩
    have hiR : MapsTo pR (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
      intro t ht
      have h := hbijR.1 ht
      exact ⟨ht₀.1.le.trans h.1, h.2.trans hb⟩
    have harg := s25gb_actual_regular_join hφ hγ hpause (Ioo_subset_Icc_self ht₀) hz
      hL hR (s25cv_par_continuous hmL hbijL) (s25cv_par_continuous hmR hbijR)
      hmL.monotoneOn hmR.monotoneOn hiL hiR hL1 hR0 heL heR hdL hdR
    have hstart : side j 0 = γ.toFun t₀ := by
      rw [heR 0 ⟨le_rfl, zero_le_one⟩, hR0]
    have hD : γ.toFun t₀ ∈ unitDisc :=
      hγ.2.1 ⟨t₀, Ioo_subset_Icc_self ht₀, rfl⟩
    have han := hφ.analyticAt (isOpen_ball.mem_nhds hD)
    have hord : meromorphicOrderAt φ (side j 0) = (0 : ℤ) := by
      rw [hstart, han.meromorphicOrderAt_eq, han.analyticOrderAt_eq_zero.mpr hz]
      rfl
    refine ⟨s25gb_blunt_of_angle j 0 hord ?_ ?_, ?_⟩
    · rw [harg, abs_of_pos Real.pi_pos]
      norm_num
    · rw [harg, abs_of_pos Real.pi_pos]
      norm_num <;> linarith
    · rw [harg]
      exact Real.pi_ne_zero

/-- A noninitial cut of a strict actual subdivision lies strictly inside (0,1).
Its two side bijections therefore feed the actual interior-corner theorem directly.
No closed-loop or simple-chain assumption is used by this reusable consumer. -/
theorem s25ic_partition_interior_corner {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hpause : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {n : ℕ} [NeZero n] {p : Fin (n + 1) → ℝ}
    (hpm : StrictMono p) (hp0 : 0 ≤ p 0) (hp1 : p (Fin.last n) ≤ 1)
    {side : Fin n → ℝ → ℂ} {par : Fin n → ℝ → ℝ}
    (hm : ∀ j, StrictMonoOn (par j) (Icc (0 : ℝ) 1))
    (hbij : ∀ j, BijOn (par j) (Icc (0 : ℝ) 1)
      (Icc (p j.castSucc) (p j.succ)))
    (h0 : ∀ j, par j 0 = p j.castSucc) (h1 : ∀ j, par j 1 = p j.succ)
    (he : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, side j t = γ.toFun (par j t))
    (hsm : ∀ j, ContDiffOn ℝ 1 (side j) (Icc 0 1))
    (hd0 : ∀ j, derivWithin (side j) (Icc 0 1) 0 ≠ 0)
    (hd1 : ∀ j, derivWithin (side j) (Icc 0 1) 1 ≠ 0)
    (j : Fin n) (hj : j ≠ 0) :
    fx_IsBlunt φ side j ∧
      arg (-derivWithin (side (j - 1)) (Icc 0 1) 1 /
        derivWithin (side j) (Icc 0 1) 0) ≠ 0 := by
  have hcut := s25sl_previous_cut j hj
  have hjpos : (0 : Fin (n + 1)) < j.castSucc := by
    change 0 < j.val
    have hv : j.val ≠ 0 := by
      intro h
      apply hj
      apply Fin.ext
      exact h
    omega
  have hjlast : j.castSucc < Fin.last n := by
    change j.val < n
    exact j.isLt
  have ht₀ : p j.castSucc ∈ Ioo (0 : ℝ) 1 :=
    ⟨hp0.trans_lt (hpm hjpos), (hpm hjlast).trans_le hp1⟩
  have hLbij : BijOn (par (j - 1)) (Icc (0 : ℝ) 1)
      (Icc (p (j - 1).castSucc) (p j.castSucc)) := by
    simpa only [hcut] using hbij (j - 1)
  have hL1 : par (j - 1) 1 = p j.castSucc := by
    rw [h1, hcut]
  exact s25ic_actual_interior_corner hφ hne hγ hpause j
    (hp0.trans (hpm.monotone (Fin.zero_le _))) ht₀
    ((hpm.monotone (Fin.le_last _)).trans hp1)
    (hsm (j - 1)) (hsm j) (hm (j - 1)) (hm j) hLbij (hbij j)
    hL1 (h0 j) (he (j - 1)) (he j) (hd1 (j - 1)) (hd0 j)

end LiZhongQC

