import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic

namespace LiZhongQC

/-- The piecewise-linear snapping profile: `0` on `[0, 1/4]`, `1` on `[3/4, 1]`, linear in between. -/
noncomputable def s78dg_cs_T (f : ℝ) : ℝ := max 0 (min 1 (2 * f - 1 / 2))

theorem s78dg_cs_T_cont : Continuous s78dg_cs_T := by
  unfold s78dg_cs_T; fun_prop

theorem s78dg_cs_T_zero : s78dg_cs_T 0 = 0 := by
  unfold s78dg_cs_T; norm_num

theorem s78dg_cs_T_one : s78dg_cs_T 1 = 1 := by
  unfold s78dg_cs_T; norm_num

theorem s78dg_cs_T_bounds (f : ℝ) : 0 ≤ s78dg_cs_T f ∧ s78dg_cs_T f ≤ 1 := by
  unfold s78dg_cs_T
  refine ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem s78dg_cs_T_low {f : ℝ} (h : f ≤ 1 / 4) : s78dg_cs_T f = 0 := by
  unfold s78dg_cs_T
  have : min 1 (2 * f - 1 / 2) = 2 * f - 1 / 2 := min_eq_right (by linarith)
  rw [this]; exact max_eq_left (by linarith)

theorem s78dg_cs_T_high {f : ℝ} (h : 3 / 4 ≤ f) : s78dg_cs_T f = 1 := by
  unfold s78dg_cs_T
  have : min 1 (2 * f - 1 / 2) = 1 := min_eq_left (by linarith)
  rw [this]; exact max_eq_right zero_le_one

theorem s78dg_cs_T_symm (f : ℝ) : s78dg_cs_T (1 - f) = 1 - s78dg_cs_T f := by
  unfold s78dg_cs_T
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- The petal (pair of glued edges) containing the unit edge `[j, j+1]` of the `4p`-gon:
edges `4i, 4i+2` form petal `2i` (the handle generator `a_i`), and `4i+1, 4i+3` form petal `2i+1`
(`b_i`). -/
def s78dg_cs_kappa (p : ℕ) (j : ℤ) : ℕ :=
  2 * ((j % ((4 * p : ℕ) : ℤ)).toNat / 4) + (j % ((4 * p : ℕ) : ℤ)).toNat % 2

theorem s78dg_cs_kappa_periodic (p : ℕ) (j : ℤ) :
    s78dg_cs_kappa p (j + ((4 * p : ℕ) : ℤ)) = s78dg_cs_kappa p j := by
  unfold s78dg_cs_kappa
  rw [Int.add_emod_right]

theorem s78dg_cs_kappa_edge (p : ℕ) {i r : ℕ} (hi : i < p) (hr : r < 4) :
    s78dg_cs_kappa p ((4 * i + r : ℕ) : ℤ) = 2 * i + r % 2 := by
  unfold s78dg_cs_kappa
  have hlt : 4 * i + r < 4 * p := by omega
  have : (((4 * i + r : ℕ) : ℤ) % ((4 * p : ℕ) : ℤ)).toNat = 4 * i + r := by
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)]
    omega
  rw [this]
  omega

/-- The snapping map: on edges of the petals in `P` it is the identity, on all other edges it
pushes each point within `1/4` of a vertex onto that vertex (and is linear in between). -/
noncomputable def s78dg_cs_tau (p : ℕ) (P : ℕ → Prop) (u : ℝ) : ℝ :=
  u + (by classical exact if P (s78dg_cs_kappa p ⌊u⌋) then 0 else s78dg_cs_T (Int.fract u) - Int.fract u)

theorem s78dg_cs_tau_pet (p : ℕ) (P : ℕ → Prop) {u : ℝ} (h : P (s78dg_cs_kappa p ⌊u⌋)) :
    s78dg_cs_tau p P u = u := by
  unfold s78dg_cs_tau
  rw [if_pos h, add_zero]

theorem s78dg_cs_tau_snap (p : ℕ) (P : ℕ → Prop) {u : ℝ} (h : ¬ P (s78dg_cs_kappa p ⌊u⌋)) :
    s78dg_cs_tau p P u = u + (s78dg_cs_T (Int.fract u) - Int.fract u) := by
  unfold s78dg_cs_tau
  rw [if_neg h]

theorem s78dg_cs_tau_int (p : ℕ) (P : ℕ → Prop) (j : ℤ) : s78dg_cs_tau p P (j : ℝ) = j := by
  by_cases h : P (s78dg_cs_kappa p ⌊(j : ℝ)⌋)
  · exact s78dg_cs_tau_pet p P h
  · rw [s78dg_cs_tau_snap p P h]
    simp [s78dg_cs_T_zero]

theorem s78dg_cs_tau_periodic (p : ℕ) (P : ℕ → Prop) (u : ℝ) :
    s78dg_cs_tau p P (u + ((4 * p : ℕ) : ℝ)) = s78dg_cs_tau p P u + ((4 * p : ℕ) : ℝ) := by
  have hfl : ⌊u + ((4 * p : ℕ) : ℝ)⌋ = ⌊u⌋ + ((4 * p : ℕ) : ℤ) := by
    rw [Int.floor_add_natCast]
  have hfr : Int.fract (u + ((4 * p : ℕ) : ℝ)) = Int.fract u := Int.fract_add_natCast _ _
  by_cases h : P (s78dg_cs_kappa p ⌊u⌋)
  · have h' : P (s78dg_cs_kappa p ⌊u + ((4 * p : ℕ) : ℝ)⌋) := by
      rw [hfl, s78dg_cs_kappa_periodic]; exact h
    rw [s78dg_cs_tau_pet p P h, s78dg_cs_tau_pet p P h']
  · have h' : ¬ P (s78dg_cs_kappa p ⌊u + ((4 * p : ℕ) : ℝ)⌋) := by
      rw [hfl, s78dg_cs_kappa_periodic]; exact h
    rw [s78dg_cs_tau_snap p P h, s78dg_cs_tau_snap p P h', hfr]
    ring

theorem s78dg_cs_tau_edge (p : ℕ) (P : ℕ → Prop) (j : ℤ) {u : ℝ} (h0 : (j : ℝ) ≤ u)
    (h1 : u ≤ (j : ℝ) + 1) : (j : ℝ) ≤ s78dg_cs_tau p P u ∧ s78dg_cs_tau p P u ≤ (j : ℝ) + 1 := by
  rcases eq_or_lt_of_le h1 with h | h
  · have : u = ((j + 1 : ℤ) : ℝ) := by push_cast; exact h
    rw [this, s78dg_cs_tau_int]
    push_cast
    constructor <;> linarith
  · have hfl : ⌊u⌋ = j := by
      rw [Int.floor_eq_iff]; exact ⟨h0, h⟩
    have hfr : Int.fract u = u - j := by rw [Int.fract, hfl]
    have hf0 : 0 ≤ u - j := by linarith
    have hf1 : u - j < 1 := by linarith
    by_cases hP : P (s78dg_cs_kappa p ⌊u⌋)
    · rw [s78dg_cs_tau_pet p P hP]; exact ⟨h0, h1⟩
    · rw [s78dg_cs_tau_snap p P hP, hfr]
      have := s78dg_cs_T_bounds (u - j)
      constructor <;> linarith [this.1, this.2]

theorem s78dg_cs_tau_cont (p : ℕ) (P : ℕ → Prop) : Continuous (s78dg_cs_tau p P) := by
  classical
  let B : ℝ → ℝ := fun f => s78dg_cs_T f - f
  have hB0 : B 0 = B 1 := by
    simp [B, s78dg_cs_T_zero, s78dg_cs_T_one]
  have hBc : Continuous (B ∘ Int.fract) :=
    ContinuousOn.comp_fract'' (by
      have : Continuous B := s78dg_cs_T_cont.sub continuous_id
      exact this.continuousOn) hB0
  let c : ℝ → ℝ := fun u => if P (s78dg_cs_kappa p ⌊u⌋) then 0 else B (Int.fract u)
  have hτ : s78dg_cs_tau p P = fun u => u + c u := by
    funext u
    unfold s78dg_cs_tau
    simp only [c, B]
  have hc : Continuous c := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : ∃ j : ℤ, x = j
    · obtain ⟨j, rfl⟩ := hx
      have hcj : c (j : ℝ) = 0 := by
        simp only [c]
        split_ifs
        · rfl
        · simp [B, s78dg_cs_T_zero]
      rw [ContinuousAt, hcj, Metric.tendsto_nhds]
      intro ε hε
      have h1 := (hBc.continuousAt (x := (j : ℝ))).tendsto
      have h0 : (B ∘ Int.fract) (j : ℝ) = 0 := by simp [B, s78dg_cs_T_zero]
      rw [h0, Metric.tendsto_nhds] at h1
      filter_upwards [h1 ε hε] with u hu
      rw [Real.dist_eq, sub_zero] at hu ⊢
      simp only [c]
      split_ifs
      · simpa using hε
      · exact hu
    · have hnj : x ≠ (⌊x⌋ : ℝ) := fun h => hx ⟨⌊x⌋, h⟩
      have hev : ∀ᶠ u in nhds x, ⌊u⌋ = ⌊x⌋ := by
        have hmem : x ∈ Set.Ioo (⌊x⌋ : ℝ) ((⌊x⌋ : ℝ) + 1) :=
          ⟨lt_of_le_of_ne (Int.floor_le x) (Ne.symm hnj), Int.lt_floor_add_one x⟩
        filter_upwards [isOpen_Ioo.mem_nhds hmem] with u hu
        rw [Int.floor_eq_iff]; exact ⟨hu.1.le, hu.2⟩
      have hceq : c =ᶠ[nhds x] fun u => if P (s78dg_cs_kappa p ⌊x⌋) then 0 else B (Int.fract u) := by
        filter_upwards [hev] with u hu
        simp only [c, hu]
      refine ContinuousAt.congr ?_ hceq.symm
      by_cases hP : P (s78dg_cs_kappa p ⌊x⌋)
      · simp only [hP, if_true]; exact continuousAt_const
      · simp only [hP, if_false]; exact hBc.continuousAt
  rw [hτ]
  exact continuous_id.add hc

/-- The snapping map commutes with the reflection that glues the edge `[e, e+1]` to `[e+2, e+3]`. -/
theorem s78dg_cs_tau_reflect (p : ℕ) (P : ℕ → Prop) (e : ℤ)
    (hκ : s78dg_cs_kappa p e = s78dg_cs_kappa p (e + 2)) {u : ℝ} (h0 : (e : ℝ) ≤ u)
    (h1 : u ≤ (e : ℝ) + 1) :
    s78dg_cs_tau p P (2 * (e : ℝ) + 3 - u) = 2 * (e : ℝ) + 3 - s78dg_cs_tau p P u := by
  rcases eq_or_lt_of_le h0 with h | h
  · have hu : u = (e : ℝ) := h.symm
    have h2 : 2 * (e : ℝ) + 3 - u = ((e + 3 : ℤ) : ℝ) := by push_cast; rw [hu]; ring
    rw [h2, hu, s78dg_cs_tau_int, s78dg_cs_tau_int]; push_cast; ring
  rcases eq_or_lt_of_le h1 with h' | h'
  · have h2 : 2 * (e : ℝ) + 3 - u = ((e + 2 : ℤ) : ℝ) := by push_cast; rw [h']; ring
    have h3 : u = ((e + 1 : ℤ) : ℝ) := by push_cast; exact h'
    rw [h2, h3, s78dg_cs_tau_int, s78dg_cs_tau_int]; push_cast; ring
  have hfl : ⌊u⌋ = e := by rw [Int.floor_eq_iff]; exact ⟨h0, h'⟩
  have hfr : Int.fract u = u - e := by rw [Int.fract, hfl]
  have hfl2 : ⌊2 * (e : ℝ) + 3 - u⌋ = e + 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  have hfr2 : Int.fract (2 * (e : ℝ) + 3 - u) = 1 - (u - e) := by
    rw [Int.fract, hfl2]; push_cast; ring
  by_cases hP : P (s78dg_cs_kappa p ⌊u⌋)
  · have hP2 : P (s78dg_cs_kappa p ⌊2 * (e : ℝ) + 3 - u⌋) := by
      rw [hfl2, ← hκ]; rw [hfl] at hP; exact hP
    rw [s78dg_cs_tau_pet p P hP, s78dg_cs_tau_pet p P hP2]
  · have hP2 : ¬ P (s78dg_cs_kappa p ⌊2 * (e : ℝ) + 3 - u⌋) := by
      rw [hfl2, ← hκ]; rw [hfl] at hP; exact hP
    rw [s78dg_cs_tau_snap p P hP, s78dg_cs_tau_snap p P hP2, hfr, hfr2, s78dg_cs_T_symm]
    ring

/-- The set of boundary parameters kept in the chart `S P`: a quarter-neighbourhood of every vertex,
together with the (open) edges of the petals in `P`. -/
def s78dg_cs_S (p : ℕ) (P : ℕ → Prop) : Set ℝ :=
  {u | (∃ j : ℤ, |u - j| < 1 / 4) ∨ P (s78dg_cs_kappa p ⌊u⌋)}

theorem s78dg_cs_S_periodic (p : ℕ) (P : ℕ → Prop) (u : ℝ) :
    u + ((4 * p : ℕ) : ℝ) ∈ s78dg_cs_S p P ↔ u ∈ s78dg_cs_S p P := by
  have hfl : ⌊u + ((4 * p : ℕ) : ℝ)⌋ = ⌊u⌋ + ((4 * p : ℕ) : ℤ) := by
    rw [Int.floor_add_natCast]
  simp only [s78dg_cs_S, Set.mem_setOf_eq, hfl, s78dg_cs_kappa_periodic]
  have hN : (((4 * p : ℕ) : ℤ) : ℝ) = ((4 * p : ℕ) : ℝ) := by norm_cast
  constructor
  · rintro (⟨j, hj⟩ | h)
    · left
      refine ⟨j - ((4 * p : ℕ) : ℤ), ?_⟩
      have : u - (((j - ((4 * p : ℕ) : ℤ) : ℤ)) : ℝ) = u + ((4 * p : ℕ) : ℝ) - j := by
        rw [Int.cast_sub, hN]; ring
      rw [this]; exact hj
    · right; exact h
  · rintro (⟨j, hj⟩ | h)
    · left
      refine ⟨j + ((4 * p : ℕ) : ℤ), ?_⟩
      have : u + ((4 * p : ℕ) : ℝ) - (((j + ((4 * p : ℕ) : ℤ) : ℤ)) : ℝ) = u - j := by
        rw [Int.cast_add, hN]; ring
      rw [this]; exact hj
    · right; exact h

theorem s78dg_cs_S_open (p : ℕ) (P : ℕ → Prop) : IsOpen (s78dg_cs_S p P) := by
  rw [isOpen_iff_mem_nhds]
  intro u hu
  by_cases hD : ∃ j : ℤ, |u - j| < 1 / 4
  · obtain ⟨j, hj⟩ := hD
    have hmem : u ∈ Metric.ball (j : ℝ) (1 / 4) := by rw [Metric.mem_ball, Real.dist_eq]; exact hj
    filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with v hv
    left
    exact ⟨j, by rw [Metric.mem_ball, Real.dist_eq] at hv; exact hv⟩
  · have hP : P (s78dg_cs_kappa p ⌊u⌋) := hu.resolve_left hD
    have hnj : u ≠ (⌊u⌋ : ℝ) := by
      intro h
      exact hD ⟨⌊u⌋, by rw [← h]; simp⟩
    have hmem : u ∈ Set.Ioo (⌊u⌋ : ℝ) ((⌊u⌋ : ℝ) + 1) :=
      ⟨lt_of_le_of_ne (Int.floor_le u) (Ne.symm hnj), Int.lt_floor_add_one u⟩
    filter_upwards [isOpen_Ioo.mem_nhds hmem] with v hv
    right
    have : ⌊v⌋ = ⌊u⌋ := by rw [Int.floor_eq_iff]; exact ⟨hv.1.le, hv.2⟩
    rw [this]; exact hP

theorem s78dg_cs_S_reflect (p : ℕ) (P : ℕ → Prop) (e : ℤ)
    (hκ : s78dg_cs_kappa p e = s78dg_cs_kappa p (e + 2)) {u : ℝ} (h0 : (e : ℝ) ≤ u)
    (h1 : u ≤ (e : ℝ) + 1) :
    2 * (e : ℝ) + 3 - u ∈ s78dg_cs_S p P ↔ u ∈ s78dg_cs_S p P := by
  rcases eq_or_lt_of_le h0 with h | h
  · have hu : u = (e : ℝ) := h.symm
    have h2 : 2 * (e : ℝ) + 3 - u = ((e + 3 : ℤ) : ℝ) := by push_cast; rw [hu]; ring
    constructor <;> intro _
    · exact Or.inl ⟨e, by rw [hu]; simp⟩
    · exact Or.inl ⟨e + 3, by rw [h2]; simp⟩
  rcases eq_or_lt_of_le h1 with h' | h'
  · have h2 : 2 * (e : ℝ) + 3 - u = ((e + 2 : ℤ) : ℝ) := by push_cast; rw [h']; ring
    have h3 : u = ((e + 1 : ℤ) : ℝ) := by push_cast; exact h'
    constructor <;> intro _
    · exact Or.inl ⟨e + 1, by rw [h3]; simp⟩
    · exact Or.inl ⟨e + 2, by rw [h2]; simp⟩
  have hfl : ⌊u⌋ = e := by rw [Int.floor_eq_iff]; exact ⟨h0, h'⟩
  have hfl2 : ⌊2 * (e : ℝ) + 3 - u⌋ = e + 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  simp only [s78dg_cs_S, Set.mem_setOf_eq, hfl, hfl2, ← hκ]
  constructor
  · rintro (⟨j, hj⟩ | hP)
    · left
      refine ⟨2 * e + 3 - j, ?_⟩
      have : u - ((2 * e + 3 - j : ℤ) : ℝ) = -(2 * (e : ℝ) + 3 - u - j) := by push_cast; ring
      rw [this, abs_neg]; exact hj
    · right; exact hP
  · rintro (⟨j, hj⟩ | hP)
    · left
      refine ⟨2 * e + 3 - j, ?_⟩
      have : 2 * (e : ℝ) + 3 - u - ((2 * e + 3 - j : ℤ) : ℝ) = -(u - j) := by push_cast; ring
      rw [this, abs_neg]; exact hj
    · right; exact hP

theorem s78dg_cs_S_star (p : ℕ) (P : ℕ → Prop) {u : ℝ} (hu : u ∈ s78dg_cs_S p P) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) * u + s * s78dg_cs_tau p P u ∈ s78dg_cs_S p P := by
  by_cases hP : P (s78dg_cs_kappa p ⌊u⌋)
  · rw [s78dg_cs_tau_pet p P hP]
    have : (1 - s) * u + s * u = u := by ring
    rw [this]; exact hu
  · obtain ⟨j, hj⟩ := hu.resolve_right hP
    have hτ : s78dg_cs_tau p P u = j := by
      rw [abs_lt] at hj
      rcases le_or_gt (j : ℝ) u with hju | hju
      · have hfl : ⌊u⌋ = j := by rw [Int.floor_eq_iff]; constructor <;> linarith
        have hfr : Int.fract u = u - j := by rw [Int.fract, hfl]
        rw [s78dg_cs_tau_snap p P hP, hfr, s78dg_cs_T_low (by linarith)]; ring
      · have hfl : ⌊u⌋ = j - 1 := by rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
        have hfr : Int.fract u = u - (j - 1) := by rw [Int.fract, hfl]; push_cast; ring
        rw [s78dg_cs_tau_snap p P hP, hfr, s78dg_cs_T_high (by linarith)]; ring
    left
    refine ⟨j, ?_⟩
    rw [hτ]
    have : (1 - s) * u + s * (j : ℝ) - j = (1 - s) * (u - j) := by ring
    rw [this, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - s)]
    calc (1 - s) * |u - j| ≤ 1 * |u - j| := by
          apply mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ < 1 / 4 := by rw [one_mul]; exact hj

end LiZhongQC
