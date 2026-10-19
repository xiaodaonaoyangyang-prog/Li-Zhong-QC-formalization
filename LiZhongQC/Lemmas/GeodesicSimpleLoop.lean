import LiZhongQC.Lemmas.GeodesicActualPartition
import LiZhongQC.Lemmas.GeodesicInteriorCorners
import LiZhongQC.Lemmas.GeodesicExceptionalJoins
/-! Actual simple-loop exclusion and global injectivity.
Interior vertices use ActualInteriorCorners. The sole closing vertex uses
the actual exceptional-join theorem on disjoint half-sides, including n=1. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ContDiff
namespace LiZhongQC

/-- Use disjoint half-sides even when n=1. Their half-open side parameters
lie on opposite sides of 1/2, so the actual chain simplicity implication
rules out intersection without requiring distinct side indices. -/
theorem s25sl_half_sides_disjoint {n : ℕ} [NeZero n]
    {side : Fin n → ℝ → ℂ}
    (hsimple : ∀ i j : Fin n, ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1,
      side i s = side j t → i = j ∧ s = t) (j : Fin n) :
    ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Ioo (0 : ℝ) 1,
      side (j - 1) (1 + (-(1 / 2 : ℝ)) * s) ≠ side j (0 + (1 / 2 : ℝ) * t) := by
  intro s hs t ht heq
  have hs' : 1 + (-(1 / 2 : ℝ)) * s ∈ Ico (0 : ℝ) 1 := by
    constructor <;> linarith [hs.1, hs.2]
  have ht' : 0 + (1 / 2 : ℝ) * t ∈ Ico (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hparam := (hsimple (j - 1) j _ hs' _ ht' heq).2
  linarith [hs.2, ht.2]

/-- An actual joined pair of partition sides has no cusp after taking
opposite outgoing half-sides. This is used only for the closing vertex;
internal vertices are handled separately by the actual blunt-corner theorem. -/
theorem s25sl_partition_join_no_cusp {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hpause : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {n : ℕ} [NeZero n] {p : Fin (n + 1) → ℝ} (hpm : StrictMono p)
    (hi : InjOn γ.toFun (Ico (p 0) (p (Fin.last n))))
    (hclosed : γ.toFun (p 0) = γ.toFun (p (Fin.last n)))
    {side : Fin n → ℝ → ℂ} {par : Fin n → ℝ → ℝ}
    (hm : ∀ j, StrictMonoOn (par j) (Icc (0 : ℝ) 1))
    (hc : ∀ j, ContinuousOn (par j) (Icc (0 : ℝ) 1))
    (hmap : ∀ j, MapsTo (par j) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (h0 : ∀ j, par j 0 = p j.castSucc) (h1 : ∀ j, par j 1 = p j.succ)
    (he : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, side j t = γ.toFun (par j t))
    (hsm : ∀ j, ContDiffOn ℝ 1 (side j) (Icc 0 1))
    (hd0 : ∀ j, derivWithin (side j) (Icc 0 1) 0 ≠ 0)
    (hd1 : ∀ j, derivWithin (side j) (Icc 0 1) 1 ≠ 0) (j : Fin n) :
    arg (-derivWithin (side (j - 1)) (Icc 0 1) 1 /
      derivWithin (side j) (Icc 0 1) 0) ≠ 0 := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hside0 : ∀ j, side j 0 = γ.toFun (p j.castSucc) := by
    intro j
    rw [he j 0 hzero, h0]
  have hside1 : ∀ j, side j 1 = γ.toFun (p j.succ) := by
    intro j
    rw [he j 1 hone, h1]
  have hnext := s25gb_partition_next hclosed hside0 hside1
  have hsimple := s25gb_partition_simple hpm hi hm h0 h1 he
  let F : ℝ → ℂ := fun t => side (j - 1) (1 + (-(1 / 2 : ℝ)) * t)
  let G : ℝ → ℂ := fun t => side j (0 + (1 / 2 : ℝ) * t)
  let pF : ℝ → ℝ := fun t => par (j - 1) (1 + (-(1 / 2 : ℝ)) * t)
  let pG : ℝ → ℝ := fun t => par j (0 + (1 / 2 : ℝ) * t)
  have hFm : ∀ t ∈ Icc (0 : ℝ) 1,
      1 + (-(1 / 2 : ℝ)) * t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hGm : ∀ t ∈ Icc (0 : ℝ) 1,
      0 + (1 / 2 : ℝ) * t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hFsm : ContDiffOn ℝ 1 F (Icc 0 1) :=
    fx_p2_contDiffOn_affine (hsm (j - 1)) hFm
  have hGsm : ContDiffOn ℝ 1 G (Icc 0 1) :=
    fx_p2_contDiffOn_affine (hsm j) hGm
  have hFc : ContinuousOn pF (Icc (0 : ℝ) 1) :=
    (hc (j - 1)).comp (by fun_prop) hFm
  have hGc : ContinuousOn pG (Icc (0 : ℝ) 1) :=
    (hc j).comp (by fun_prop) hGm
  have hFa : StrictAntiOn pF (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact hm (j - 1) (hFm t ht) (hFm s hs) (by linarith)
  have hGs : StrictMonoOn pG (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact hm j (hGm s hs) (hGm t ht) (by linarith)
  have hFi : MapsTo pF (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) :=
    fun t ht => hmap (j - 1) (hFm t ht)
  have hGi : MapsTo pG (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) :=
    fun t ht => hmap j (hGm t ht)
  have hFe : ∀ t ∈ Icc (0 : ℝ) 1, F t = γ.toFun (pF t) :=
    fun t ht => he (j - 1) _ (hFm t ht)
  have hGe : ∀ t ∈ Icc (0 : ℝ) 1, G t = γ.toFun (pG t) :=
    fun t ht => he j _ (hGm t ht)
  have hjoin : side (j - 1) 1 = side j 0 := by
    simpa only [sub_add_cancel] using hnext (j - 1)
  have hpoint : γ.toFun (pF 0) = γ.toFun (pG 0) := by
    have h := (he (j - 1) 1 hone).symm.trans (hjoin.trans (he j 0 hzero))
    simpa only [pF, pG, mul_zero, add_zero, zero_add] using h
  have hFd : derivWithin F (Icc 0 1) 0 =
      ((-(1 / 2 : ℝ) : ℝ) : ℂ) * derivWithin (side (j - 1)) (Icc 0 1) 1 := by
    have h := fx_p2_derivWithin_affine
      (fx_p2_hasDerivWithinAt_of_contDiffOn (hsm (j - 1))) zero_lt_one hFm hzero
    simpa only [mul_zero, add_zero] using h
  have hGd : derivWithin G (Icc 0 1) 0 =
      ((1 / 2 : ℝ) : ℂ) * derivWithin (side j) (Icc 0 1) 0 := by
    have h := fx_p2_derivWithin_affine
      (fx_p2_hasDerivWithinAt_of_contDiffOn (hsm j)) zero_lt_one hGm hzero
    simpa only [G, mul_zero, zero_add] using h
  have hFd0 : derivWithin F (Icc 0 1) 0 ≠ 0 := by
    rw [hFd]
    exact mul_ne_zero (by norm_num) (hd1 (j - 1))
  have hGd0 : derivWithin G (Icc 0 1) 0 ≠ 0 := by
    rw [hGd]
    exact mul_ne_zero (by norm_num) (hd0 j)
  have hdisj : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Ioo (0 : ℝ) 1, F s ≠ G t :=
    s25sl_half_sides_disjoint hsimple j
  have hangle := s25gb_actual_exceptional_join hφ hne hγ hγ hpause hpause
    (hFi hzero) (hGi hzero) hpoint hFsm hGsm hFc hGc
    (Or.inr hFa) (Or.inl hGs) hFi hGi rfl rfl hFe hGe hFd0 hGd0 hdisj
  have hratio : derivWithin F (Icc 0 1) 0 / derivWithin G (Icc 0 1) 0 =
      -derivWithin (side (j - 1)) (Icc 0 1) 1 / derivWithin (side j) (Icc 0 1) 0 := by
    rw [hFd, hGd]
    push_cast
    field_simp [hd0 j] <;> ring
  simpa only [hratio] using hangle

/-- Actual simple-loop exclusion. The finite-side producer constructs every side;
actual interior-corner and closing-corner results supply the geometry. -/
theorem s25sl_no_simple_loop {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hclosed : γ.toFun a = γ.toFun b) (hi : InjOn γ.toFun (Ico a b)) : False := by
  classical
  obtain ⟨n, p, side, par, hn, hpm, hp0, hp1, hpI, hm, hbij, h0, h1,
    he, hstr, hsm, hreg, _hs0, _hs1, _himage, _hreggap⟩ :=
    s25cv_chain_fields hφ hne hγ hp ha hab hb
  letI : NeZero n := ⟨hn.ne'⟩
  have hicuts : InjOn γ.toFun (Ico (p 0) (p (Fin.last n))) := by
    rw [hp0, hp1]
    exact hi
  have hclosecuts : γ.toFun (p 0) = γ.toFun (p (Fin.last n)) := by
    rw [hp0, hp1]
    exact hclosed
  have hc : ∀ j, ContinuousOn (par j) (Icc (0 : ℝ) 1) :=
    fun j => s25cv_par_continuous (hm j) (hbij j)
  have hmap : ∀ j, MapsTo (par j) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro j t ht
    have h := (hbij j).1 ht
    exact ⟨ha.trans ((hpI j.castSucc).1.trans h.1),
      (h.2.trans (hpI j.succ).2).trans hb⟩
  have hd0 : ∀ j, derivWithin (side j) (Icc 0 1) 0 ≠ 0 :=
    fun j => hreg j 0 ⟨le_rfl, zero_le_one⟩
  have hd1 : ∀ j, derivWithin (side j) (Icc 0 1) 1 ≠ 0 :=
    fun j => hreg j 1 ⟨zero_le_one, le_rfl⟩
  have hbound0 : 0 ≤ p 0 := by rw [hp0]; exact ha
  have hbound1 : p (Fin.last n) ≤ 1 := by rw [hp1]; exact hb
  have hInterior := s25ic_partition_interior_corner hφ hne hγ hp hpm hbound0 hbound1
    hm hbij h0 h1 he hsm hd0 hd1
  have hClosing := s25sl_partition_join_no_cusp hφ hne hγ hp hpm hicuts hclosecuts
    hm hc hmap h0 h1 he hsm hd0 hd1 (0 : Fin n)
  have hcusp : ∀ j, arg (-derivWithin (side (j - 1)) (Icc 0 1) 1 /
      derivWithin (side j) (Icc 0 1) 0) ≠ 0 := by
    intro j
    by_cases hj : j = 0
    · subst j
      exact hClosing
    · exact (hInterior j hj).2
  have hmem : ∀ t ∈ Icc (p 0) (p (Fin.last n)), γ.toFun t ∈ unitDisc := by
    intro t ht
    rw [hp0, hp1] at ht
    exact hγ.2.1 ⟨t, ⟨ha.trans ht.1, ht.2.trans hb⟩, rfl⟩
  have hchain := s25gb_chain_of_partition hpm hicuts hclosecuts hmem
    hm h0 h1 he hstr hsm hd0 hd1 hcusp
  apply s25gb_chain_excluded hφ hne hchain ({0} : Finset (Fin n)) (by simp)
  intro j hj
  exact (hInterior j (by simpa only [Finset.mem_singleton] using hj)).1

/-- Every actual non-pausing geodesic for a nonzero holomorphic differential
in the disk is globally injective. All finite-chain and corner inputs are derived. -/
theorem s25sl_geodesic_injective {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s) :
    InjOn γ.toFun (Icc (0 : ℝ) 1) := by
  apply s25gb_injective_of_no_simple_loop hφ hne hγ hp
  intro a b ha hab hb hclosed hi
  exact s25sl_no_simple_loop hφ hne hγ hp ha hab hb hclosed hi

end LiZhongQC

