import LiZhongQC.Lemmas.GeodesicFiniteSideCover
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC

/-- Actual zero endpoints and actual regular charts together give a two-sided
local supply of smooth straight subarcs. At the ends of [0,1], the unavailable
outside half is empty, so no artificial extension of the geodesic is used. -/
theorem s25cv_actual_local_halves {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ δ > 0, ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      x - δ < s → t < x + δ → (t ≤ x ∨ x ≤ s) →
      Nonempty (s25cv_Side φ γ.toFun s t) := by
  by_cases hz : φ (γ.toFun x) = 0
  · have hleft : ∃ ε > 0, ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ x → x - ε < s →
        Nonempty (s25cv_Side φ γ.toFun s t) := by
      by_cases hx0 : 0 < x
      · obtain ⟨ε, hε, ⟨S⟩⟩ := s25cv_zero_left hφ hne hγ hp hx hx0 hz
        exact ⟨ε, hε, fun s t hs hst htx hxs => s25cv_restrict S hxs.le hst htx⟩
      · have hxz : x = 0 := le_antisymm (le_of_not_gt hx0) hx.1
        refine ⟨1, zero_lt_one, ?_⟩
        intro s t hs hst htx hxs
        exact False.elim (by rw [hxz] at htx; linarith)
    have hright : ∃ ε > 0, ∀ s t : ℝ, x ≤ s → s < t → t ≤ 1 → t < x + ε →
        Nonempty (s25cv_Side φ γ.toFun s t) := by
      by_cases hx1 : x < 1
      · obtain ⟨ε, hε, ⟨S⟩⟩ := s25cv_zero_right hφ hne hγ hp hx hx1 hz
        exact ⟨ε, hε, fun s t hxs hst ht htx => s25cv_restrict S hxs hst htx.le⟩
      · have hxo : x = 1 := le_antisymm hx.2 (le_of_not_gt hx1)
        refine ⟨1, zero_lt_one, ?_⟩
        intro s t hxs hst ht htx
        exact False.elim (by rw [hxo] at hxs; linarith)
    obtain ⟨εl, hl, hleft⟩ := hleft
    obtain ⟨εr, hr, hright⟩ := hright
    refine ⟨min εl εr, lt_min hl hr, ?_⟩
    intro s t hs hst ht hls htr hsplit
    rcases hsplit with htx | hxs
    · apply hleft s t hs hst htx
      linarith [min_le_left εl εr]
    · apply hright s t hxs hst ht
      linarith [min_le_right εl εr]
  · obtain ⟨δ, hδ, hside⟩ := s25cv_regular_window hφ hne hγ hp hx hz
    exact ⟨δ, hδ, fun s t hs hst ht hls htr _ => hside s t hs hst ht hls htr⟩

/-- Finite, strictly ordered smooth straight representatives for any actual
nondegenerate subarc of a non-pausing geodesic. No finite smooth cover or
piecewise differentiability premise is supplied by the caller. -/
theorem s25cv_actual_partition {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ (n : ℕ) (p : Fin (n + 1) → ℝ), 0 < n ∧ StrictMono p ∧
      p 0 = a ∧ p (Fin.last n) = b ∧ (∀ i, p i ∈ Icc a b) ∧
      Nonempty (∀ j : Fin n, s25cv_Side φ γ.toFun (p j.castSucc) (p j.succ)) := by
  classical
  have hlocal : ∀ x ∈ Icc a b, ∃ δ > 0, ∀ s t : ℝ,
      a ≤ s → s < t → t ≤ b → x - δ < s → t < x + δ →
        (t ≤ x ∨ x ≤ s) → Nonempty (s25cv_Side φ γ.toFun s t) := by
    intro x hx
    obtain ⟨δ, hδ, hside⟩ := s25cv_actual_local_halves hφ hne hγ hp
      (show x ∈ Icc (0 : ℝ) 1 from ⟨ha.trans hx.1, hx.2.trans hb⟩)
    exact ⟨δ, hδ, fun s t hs hst ht hls htr hsplit =>
      hside s t (ha.trans hs) hst (ht.trans hb) hls htr hsplit⟩
  obtain ⟨n, p, hn, hpm, hp0, hp1, hpI, hside⟩ :=
    s25cv_partition_of_local_halves hab hlocal
  exact ⟨n, p, hn, hpm, hp0, hp1, hpI, ⟨fun j => Classical.choice (hside j)⟩⟩

/-- Flat interface for `s25gb_chain_of_partition`: all side and parameter
fields are produced from the actual geodesic. Only the corner angle analysis
is left to the chain consumer. -/
theorem s25cv_chain_fields {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ (n : ℕ) (p : Fin (n + 1) → ℝ) (side : Fin n → ℝ → ℂ) (par : Fin n → ℝ → ℝ),
      0 < n ∧ StrictMono p ∧ p 0 = a ∧ p (Fin.last n) = b ∧
      (∀ i, p i ∈ Icc a b) ∧
      (∀ j, StrictMonoOn (par j) (Icc (0 : ℝ) 1)) ∧
      (∀ j, BijOn (par j) (Icc (0 : ℝ) 1) (Icc (p j.castSucc) (p j.succ))) ∧
      (∀ j, par j 0 = p j.castSucc) ∧ (∀ j, par j 1 = p j.succ) ∧
      (∀ j, ∀ t ∈ Icc (0 : ℝ) 1, side j t = γ.toFun (par j t)) ∧
      (∀ j, IsPhiStraightArc φ (side j) 0 1) ∧
      (∀ j, ContDiffOn ℝ 1 (side j) (Icc 0 1)) ∧
      (∀ j, ∀ t ∈ Icc (0 : ℝ) 1, derivWithin (side j) (Icc 0 1) t ≠ 0) ∧
      (∀ j, side j 0 = γ.toFun (p j.castSucc)) ∧
      (∀ j, side j 1 = γ.toFun (p j.succ)) ∧
      (∀ j, side j '' Icc (0 : ℝ) 1 = γ.toFun '' Icc (p j.castSucc) (p j.succ)) ∧
      ∀ (j : Fin n), ∀ t ∈ Ioo (p j.castSucc) (p j.succ), φ (γ.toFun t) ≠ 0 := by
  obtain ⟨n, p, hn, hpm, hp0, hp1, hpI, ⟨S⟩⟩ := s25cv_actual_partition hφ hne hγ hp ha hab hb
  refine ⟨n, p, fun j => (S j).side, fun j => (S j).par,
    hn, hpm, hp0, hp1, hpI, fun j => (S j).mono, fun j => (S j).bij,
    fun j => (S j).first, fun j => (S j).last, fun j => (S j).trace,
    fun j => (S j).straight, fun j => (S j).smooth, fun j => (S j).regular,
    ?_, ?_, ?_, fun j t ht => s25cv_side_regular_interior (S j) ht⟩
  · intro j
    simpa only [(S j).first] using (S j).trace 0 ⟨le_rfl, zero_le_one⟩
  · intro j
    simpa only [(S j).last] using (S j).trace 1 ⟨zero_le_one, le_rfl⟩
  · intro j
    apply Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨(S j).par t, (S j).bij.1 ht, ((S j).trace t ht).symm⟩
    · rintro z ⟨u, hu, rfl⟩
      obtain ⟨t, ht, he⟩ := (S j).bij.2.2 hu
      refine ⟨t, ht, ?_⟩
      change (S j).side t = γ.toFun u
      rw [(S j).trace t ht, he]

end LiZhongQC

