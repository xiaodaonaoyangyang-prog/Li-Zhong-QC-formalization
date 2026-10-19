import LiZhongQC.Lemmas.GeodesicRegularCorners
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real
noncomputable section
namespace LiZhongQC

/-- Shrink the whole unit interval toward any one of its points so a
continuous original-time map stays in a prescribed neighborhood. The
shrinking map fixes that point and has positive constant derivative. -/
theorem s25gb_parameter_shrink {p : ℝ → ℝ}
    (hp : ContinuousOn p (Icc (0 : ℝ) 1)) {x δ : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hδ : 0 < δ) :
    ∃ e : ℝ, 0 < e ∧ e < 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, (1 - e) * x + e * t ∈ Icc (0 : ℝ) 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, |p ((1 - e) * x + e * t) - p x| < δ := by
  obtain ⟨r, hr, hnear⟩ := Metric.continuousWithinAt_iff.1 (hp x hx) δ hδ
  let e := min r 1 / 2
  have he : 0 < e := by dsimp [e]; positivity
  have her : e < r := by dsimp [e]; linarith [min_le_left r 1]
  have he1 : e < 1 := by dsimp [e]; linarith [min_le_right r 1]
  have hmap : ∀ t ∈ Icc (0 : ℝ) 1, (1 - e) * x + e * t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    constructor
    · nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - e) hx.1, mul_nonneg he.le ht.1]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - e) (sub_nonneg.2 hx.2),
        mul_nonneg he.le (sub_nonneg.2 ht.2)]
  refine ⟨e, he, he1, hmap, ?_⟩
  intro t ht
  have hdist : dist ((1 - e) * x + e * t) x < r := by
    rw [Real.dist_eq, show (1 - e) * x + e * t - x = e * (t - x) by ring,
      abs_mul, abs_of_pos he]
    have htx : |t - x| ≤ 1 := abs_le.2 ⟨by linarith [ht.1, hx.2], by linarith [ht.2, hx.1]⟩
    exact (mul_le_mul_of_nonneg_left htx he.le).trans_lt (by simpa using her)
  simpa only [Real.dist_eq] using hnear (hmap t ht) hdist

/-- At a regular point of the actual geodesic there is one common natural
coordinate direction for EVERY smooth increasing representative ending or
starting there. Continuity of the original-time maps supplies the required
common chart by shrinking; no whole-side chart containment is assumed. -/
theorem s25gb_regular_tangent_at {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) {γ : LRCurve}
    (hγ : IsPhiGeodesic φ unitDisc γ)
    (hpause : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (hz : φ (γ.toFun t₀) ≠ 0) :
    ∃ (ζ : ℂ → ℂ) (u : ℂ), u ≠ 0 ∧
      ∀ (σ : ℝ → ℂ) (p : ℝ → ℝ) (x : ℝ),
        x ∈ Icc (0 : ℝ) 1 →
        ContDiffOn ℝ 1 σ (Icc 0 1) →
        ContinuousOn p (Icc (0 : ℝ) 1) → MonotoneOn p (Icc (0 : ℝ) 1) →
        MapsTo p (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) → p x = t₀ →
        (∀ t ∈ Icc (0 : ℝ) 1, σ t = γ.toFun (p t)) →
        derivWithin σ (Icc 0 1) x ≠ 0 →
          deriv ζ (γ.toFun t₀) ≠ 0 ∧
          ∃ r : ℝ, 0 < r ∧ deriv ζ (γ.toFun t₀) * derivWithin σ (Icc 0 1) x = (r : ℂ) * u := by
  obtain ⟨δ, hδ, ζ, u, hu, htan⟩ :=
    s25gb_regular_tangent_window hφ hγ hpause ht₀ hz
  refine ⟨ζ, u, hu, ?_⟩
  intro σ p x hx hσ hpc hpm hpi hpx heq hd
  obtain ⟨e, he, he1, hmap, hnear⟩ := s25gb_parameter_shrink hpc hx hδ
  let q : ℝ → ℝ := fun t => (1 - e) * x + e * t
  let τ : ℝ → ℂ := fun t => σ (q t)
  let k : ℝ → ℝ := fun t => p (q t)
  have hqx : q x = x := by dsimp [q]; ring
  have hτx : τ x = γ.toFun t₀ := by
    change σ (q x) = γ.toFun t₀
    rw [hqx, heq x hx, hpx]
  have hτ : ContDiffOn ℝ 1 τ (Icc 0 1) := fx_p2_contDiffOn_affine hσ hmap
  have hkm : MonotoneOn k (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    apply hpm (hmap s hs) (hmap t ht)
    change (1 - e) * x + e * s ≤ (1 - e) * x + e * t
    simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hst he.le) ((1 - e) * x)
  have hkw : ∀ t ∈ Icc (0 : ℝ) 1,
      k t ∈ Icc (0 : ℝ) 1 ∧ t₀ - δ < k t ∧ k t < t₀ + δ := by
    intro t ht
    have hn := hnear t ht
    rw [hpx, abs_lt] at hn
    exact ⟨hpi (hmap t ht), by dsimp [k, q]; linarith [hn.1],
      by dsimp [k, q]; linarith [hn.2]⟩
  have hτeq : ∀ t ∈ Icc (0 : ℝ) 1, τ t = γ.toFun (k t) :=
    fun t ht => heq _ (hmap t ht)
  have hder : derivWithin τ (Icc 0 1) x = (e : ℂ) * derivWithin σ (Icc 0 1) x := by
    have h := fx_p2_derivWithin_affine (fx_p2_hasDerivWithinAt_of_contDiffOn hσ)
      zero_lt_one hmap hx
    change derivWithin τ (Icc 0 1) x = (e : ℂ) * derivWithin σ (Icc 0 1) x
    simpa only [show (1 - e) * x + e * x = x by ring] using h
  have hec : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hτd : derivWithin τ (Icc 0 1) x ≠ 0 := by
    rw [hder]
    exact mul_ne_zero hec hd
  obtain ⟨hζd, r, hr, hrel⟩ := htan τ k hτ hkm hkw hτeq x hx hτd
  rw [hτx] at hζd hrel
  rw [hder] at hrel
  refine ⟨hζd, r / e, div_pos hr he, ?_⟩
  push_cast
  apply mul_left_cancel₀ hec
  calc
    (e : ℂ) * (deriv ζ (γ.toFun t₀) * derivWithin σ (Icc 0 1) x)
        = deriv ζ (γ.toFun t₀) * ((e : ℂ) * derivWithin σ (Icc 0 1) x) := by ring
    _ = (r : ℂ) * u := hrel
    _ = (e : ℂ) * ((r : ℂ) / e * u) := by field_simp <;> ring

/-- The literal side/par contract gives a straight angle at every regular
interior cut of one actual geodesic. No common-chart or tangent compatibility
hypothesis is added: both are derived by shrinking the original-time maps. -/
theorem s25gb_actual_regular_join {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) {γ : LRCurve}
    (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (hz : φ (γ.toFun t₀) ≠ 0)
    {L R : ℝ → ℂ} {pL pR : ℝ → ℝ}
    (hL : ContDiffOn ℝ 1 L (Icc 0 1)) (hR : ContDiffOn ℝ 1 R (Icc 0 1))
    (hcL : ContinuousOn pL (Icc (0 : ℝ) 1)) (hcR : ContinuousOn pR (Icc (0 : ℝ) 1))
    (hmL : MonotoneOn pL (Icc (0 : ℝ) 1)) (hmR : MonotoneOn pR (Icc (0 : ℝ) 1))
    (hiL : MapsTo pL (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hiR : MapsTo pR (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hpL : pL 1 = t₀) (hpR : pR 0 = t₀)
    (heL : ∀ t ∈ Icc (0 : ℝ) 1, L t = γ.toFun (pL t))
    (heR : ∀ t ∈ Icc (0 : ℝ) 1, R t = γ.toFun (pR t))
    (hdL : derivWithin L (Icc 0 1) 1 ≠ 0)
    (hdR : derivWithin R (Icc 0 1) 0 ≠ 0) :
    arg (-derivWithin L (Icc 0 1) 1 / derivWithin R (Icc 0 1) 0) = Real.pi := by
  obtain ⟨ζ, u, hu, htangent⟩ := s25gb_regular_tangent_at hφ hγ hp ht₀ hz
  obtain ⟨hζ, rL, hrL, hrelL⟩ := htangent L pL 1 ⟨zero_le_one, le_rfl⟩
    hL hcL hmL hiL hpL heL hdL
  obtain ⟨_, rR, hrR, hrelR⟩ := htangent R pR 0 ⟨le_rfl, zero_le_one⟩
    hR hcR hmR hiR hpR heR hdR
  exact s25gb_regular_tangent_ratio hζ hu hrL hrR hrelL hrelR

end LiZhongQC

