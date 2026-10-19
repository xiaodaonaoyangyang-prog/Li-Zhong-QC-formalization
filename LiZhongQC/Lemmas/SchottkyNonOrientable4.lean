import LiZhongQC.Lemmas.SchottkyNonOrientable3
import LiZhongQC.Lemmas.SchottkyClosedSurface12

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology unitInterval

universe u

namespace LiZhongQC
/-- The coordinate along the petal `i` (a circle-valued map of the boundary parameter, with period `2p`):
it winds twice around the circle on the two edges `[2i, 2i+2]` of the petal and is `0` elsewhere. -/
noncomputable def s78dg_no_G (p i : ℕ) (u : ℝ) : AddCircle (1 : ℝ) :=
  ((min 2 (max 0 ((2 * (p : ℝ)) * Int.fract (u / (2 * p)) - 2 * (i : ℝ))) : ℝ) : AddCircle (1 : ℝ))

theorem s78dg_no_coe_two : ((2 : ℝ) : AddCircle (1 : ℝ)) = 0 :=
  (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨2, by simp⟩

theorem s78dg_no_G_periodic (p i : ℕ) (u : ℝ) :
    s78dg_no_G p i (u + 2 * p) = s78dg_no_G p i u := by
  unfold s78dg_no_G
  by_cases hp : (p : ℝ) = 0
  · simp [hp]
  have : (u + 2 * p) / (2 * p) = u / (2 * p) + 1 := by field_simp
  rw [this, Int.fract_add_one]

theorem s78dg_no_G_periodic_int (p i : ℕ) (u : ℝ) (k : ℤ) :
    s78dg_no_G p i (u + k * (2 * (p : ℝ))) = s78dg_no_G p i u := by
  have := s78dg_cs_periodic_int (fun q : Unit × ℝ => s78dg_no_G p i q.2) (2 * (p : ℝ)) ()
    (fun v => s78dg_no_G_periodic p i v) u k
  simpa using this

theorem s78dg_no_G_on_period_le (p i : ℕ) (hp : 1 ≤ p) (hi : i < p) {u : ℝ} (h0 : 0 ≤ u)
    (h1 : u ≤ 2 * p) :
    s78dg_no_G p i u = ((min 2 (max 0 (u - 2 * (i : ℝ))) : ℝ) : AddCircle (1 : ℝ)) := by
  have hN : (0 : ℝ) < 2 * p := by positivity
  rcases eq_or_lt_of_le h1 with h | h
  · have h0' : s78dg_no_G p i u = s78dg_no_G p i 0 := by
      have := s78dg_no_G_periodic p i 0
      rw [zero_add] at this
      rw [h]; exact this
    rw [h0']
    unfold s78dg_no_G
    simp only [zero_div, Int.fract_zero, mul_zero, zero_sub]
    have hi' : (i : ℝ) + 1 ≤ p := by exact_mod_cast hi
    have e1 : max 0 (-(2 * (i : ℝ))) = 0 := by
      apply max_eq_left; have : (0 : ℝ) ≤ i := Nat.cast_nonneg _; linarith
    have e2 : max 0 (u - 2 * (i : ℝ)) = u - 2 * (i : ℝ) := by
      apply max_eq_right; rw [h]; linarith
    have e3 : min 2 (u - 2 * (i : ℝ)) = 2 := by
      apply min_eq_left; rw [h]; linarith
    rw [e1, e2, e3]
    simp [s78dg_no_coe_two]
  · unfold s78dg_no_G
    rw [Int.fract_eq_self.2 ⟨by positivity, (div_lt_one hN).2 h⟩]
    congr 2
    field_simp

theorem s78dg_no_G_cont (p i : ℕ) (hp : 1 ≤ p) (hi : i < p) : Continuous (s78dg_no_G p i) := by
  have hN : (0 : ℝ) < 2 * p := by positivity
  let f : ℝ → AddCircle (1 : ℝ) := fun t =>
    ((min 2 (max 0 ((2 * (p : ℝ)) * t - 2 * (i : ℝ))) : ℝ) : AddCircle (1 : ℝ))
  have hfc : Continuous f :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp (by fun_prop)
  have hf : Continuous (f ∘ Int.fract) := by
    refine ContinuousOn.comp_fract'' hfc.continuousOn ?_
    simp only [f]
    have hi' : (i : ℝ) + 1 ≤ p := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have e1 : max 0 (2 * (p : ℝ) * 0 - 2 * (i : ℝ)) = 0 := by
      apply max_eq_left; linarith
    have e2 : max 0 (2 * (p : ℝ) * 1 - 2 * (i : ℝ)) = 2 * (p : ℝ) * 1 - 2 * (i : ℝ) := by
      apply max_eq_right; linarith
    have e3 : min 2 (2 * (p : ℝ) * 1 - 2 * (i : ℝ)) = 2 := by
      apply min_eq_left; linarith
    rw [e1, e2, e3]
    simp [s78dg_no_coe_two]
  have : s78dg_no_G p i = (f ∘ Int.fract) ∘ fun u => u / (2 * p) := by
    funext u; rfl
  rw [this]
  exact hf.comp (continuous_id.div_const _)

theorem s78dg_no_G_glue (p i : ℕ) (hp : 1 ≤ p) (hi : i < p) (j : Fin p) (x : ℝ) (h0 : 0 ≤ x)
    (h1 : x ≤ 1) :
    s78dg_no_G p i (2 * (j : ℝ) + x) = s78dg_no_G p i (2 * (j : ℝ) + 1 + x) := by
  have hj : (j : ℝ) + 1 ≤ p := by exact_mod_cast j.2
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  rw [s78dg_no_G_on_period_le p i hp hi (by linarith) (by linarith),
    s78dg_no_G_on_period_le p i hp hi (by linarith) (by linarith)]
  rcases lt_trichotomy (j : ℕ) i with h | h | h
  · have hj' : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    have e1 : max 0 (2 * (j : ℝ) + x - 2 * (i : ℝ)) = 0 := by apply max_eq_left; linarith
    have e2 : max 0 (2 * (j : ℝ) + 1 + x - 2 * (i : ℝ)) = 0 := by apply max_eq_left; linarith
    rw [e1, e2]
  · have : (j : ℝ) = i := by exact_mod_cast h
    have e1 : max 0 (2 * (j : ℝ) + x - 2 * (i : ℝ)) = x := by
      rw [this, show 2 * (i : ℝ) + x - 2 * i = x by ring]; exact max_eq_right h0
    have e2 : max 0 (2 * (j : ℝ) + 1 + x - 2 * (i : ℝ)) = 1 + x := by
      rw [this, show 2 * (i : ℝ) + 1 + x - 2 * i = 1 + x by ring]; exact max_eq_right (by linarith)
    have e3 : min 2 x = x := min_eq_right (by linarith)
    have e4 : min 2 (1 + x) = 1 + x := min_eq_right (by linarith)
    rw [e1, e2, e3, e4, AddCircle.coe_add, s78dg_cs_coe_one, zero_add]
  · have hj' : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
    have e1 : max 0 (2 * (j : ℝ) + x - 2 * (i : ℝ)) = 2 * (j : ℝ) + x - 2 * (i : ℝ) := by
      apply max_eq_right; linarith
    have e2 : max 0 (2 * (j : ℝ) + 1 + x - 2 * (i : ℝ)) = 2 * (j : ℝ) + 1 + x - 2 * (i : ℝ) := by
      apply max_eq_right; linarith
    have e3 : min 2 (2 * (j : ℝ) + x - 2 * (i : ℝ)) = 2 := min_eq_left (by linarith)
    have e4 : min 2 (2 * (j : ℝ) + 1 + x - 2 * (i : ℝ)) = 2 := min_eq_left (by linarith)
    rw [e1, e2, e3, e4]

/-- The retraction of the punctured chart onto the petal coordinate. -/
theorem s78dg_no_petal_retraction (p : ℕ) (hp : 1 ≤ p) (i : ℕ) (hi : i < p) :
    ∃ r : ↥(s78dg_gr_U (NonOrientableRel p 0)) → AddCircle (1 : ℝ), Continuous r ∧
      ∀ (ρ : Set.Ioc (0 : ℝ) 1) (u : ℝ), r (s78dg_no_Psi_fun p hp (ρ, u)) = s78dg_no_G p i u := by
  have hF : Continuous (fun a : Set.Ioc (0 : ℝ) 1 × ℝ => s78dg_no_G p i a.2) :=
    (s78dg_no_G_cont p i hp hi).comp continuous_snd
  have hres : ∀ a b : Set.Ioc (0 : ℝ) 1 × ℝ, s78dg_no_Psi_fun p hp a = s78dg_no_Psi_fun p hp b →
      s78dg_no_G p i a.2 = s78dg_no_G p i b.2 := by
    refine s78dg_no_respects p hp (s78dg_no_Psi_fun p hp) (s78dg_no_Psi_spec p hp)
      (fun a : Set.Ioc (0 : ℝ) 1 × ℝ => s78dg_no_G p i a.2)
      (fun ρ u => ?_) ⟨1, zero_lt_one, le_rfl⟩ rfl ?_
    · simp only
      have := s78dg_no_G_periodic p i u
      push_cast
      rw [this]
    · intro j x h0 h1
      exact s78dg_no_G_glue p i hp hi j x h0 h1
  obtain ⟨r, hr, hrΨ⟩ := s78dg_cs_descent _ (s78dg_no_Psi_quot p hp) _ hF hres
  exact ⟨r, hr, fun ρ u => hrΨ (ρ, u)⟩

theorem s78dg_no_tau_periodic_int (p : ℕ) (P : ℕ → Prop) (u : ℝ) (k : ℤ) :
    s78dg_no_tau p P (u + k * ((2 * p : ℕ) : ℝ)) = s78dg_no_tau p P u + k * ((2 * p : ℕ) : ℝ) := by
  have h := s78dg_cs_periodic_int (fun q : Unit × ℝ => s78dg_no_tau p P q.2 - q.2)
    ((2 * p : ℕ) : ℝ) () (fun v => by
      simp only
      rw [s78dg_no_tau_periodic]; ring) u k
  simp only at h
  linarith

theorem s78dg_no_kappa_eq_iff (p i : ℕ) (hi : i < p) (j : ℤ) :
    s78dg_no_kappa p j = i ↔
      ((j % ((2 * p : ℕ) : ℤ)).toNat = 2 * i ∨ (j % ((2 * p : ℕ) : ℤ)).toNat = 2 * i + 1) := by
  unfold s78dg_no_kappa
  have hN : (0 : ℤ) < ((2 * p : ℕ) : ℤ) := by
    have : 0 < p := by omega
    positivity
  have h0 : 0 ≤ j % ((2 * p : ℕ) : ℤ) := Int.emod_nonneg _ hN.ne'
  have h1 : j % ((2 * p : ℕ) : ℤ) < ((2 * p : ℕ) : ℤ) := Int.emod_lt_of_pos _ hN
  have hlt : (j % ((2 * p : ℕ) : ℤ)).toNat < 2 * p := by
    have := Int.toNat_of_nonneg h0
    omega
  generalize (j % ((2 * p : ℕ) : ℤ)).toNat = n at hlt ⊢
  omega

theorem s78dg_no_tau_vertex' (p : ℕ) (P : ℕ → Prop) {u : ℝ} {j : ℤ} (hj : |u - j| < 1 / 4)
    (hP : ¬ P (s78dg_no_kappa p ⌊u⌋)) : s78dg_no_tau p P u = j := by
  rw [abs_lt] at hj
  rcases le_or_gt (j : ℝ) u with hju | hju
  · have hfl : ⌊u⌋ = j := by rw [Int.floor_eq_iff]; constructor <;> linarith
    have hfr : Int.fract u = u - j := by rw [Int.fract, hfl]
    rw [s78dg_no_tau_snap p P hP, hfr, s78dg_cs_T_low (by linarith)]; ring
  · have hfl : ⌊u⌋ = j - 1 := by rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have hfr : Int.fract u = u - (j - 1) := by rw [Int.fract, hfl]; push_cast; ring
    rw [s78dg_no_tau_snap p P hP, hfr, s78dg_cs_T_high (by linarith)]; ring

theorem s78dg_no_E_mem (p i : ℕ) (hi : i < p) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    2 * (i : ℝ) + x ∈ s78dg_no_S p (fun k => k = i) := by
  have hE : 2 * (i : ℝ) = (((2 * i : ℕ) : ℤ) : ℝ) := by push_cast; ring
  rcases eq_or_lt_of_le h1 with h | h
  · left
    refine ⟨((2 * i : ℕ) : ℤ) + 1, ?_⟩
    rw [hE, h]; simp
  · right
    have hfl : ⌊2 * (i : ℝ) + x⌋ = ((2 * i : ℕ) : ℤ) := by
      rw [Int.floor_eq_iff, ← hE]; constructor <;> linarith
    rw [hfl]
    have := s78dg_no_kappa_edge p hi (r := 0) (by norm_num)
    simpa using this

theorem s78dg_no_tau_E (p i : ℕ) (hi : i < p) {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    s78dg_no_tau p (fun k => k = i) (2 * (i : ℝ) + y) = 2 * (i : ℝ) + y := by
  have hE : 2 * (i : ℝ) = (((2 * i : ℕ) : ℤ) : ℝ) := by push_cast; ring
  have hfl : ⌊2 * (i : ℝ) + y⌋ = ((2 * i : ℕ) : ℤ) := by
    rw [Int.floor_eq_iff, ← hE]; constructor <;> linarith
  apply s78dg_no_tau_pet p (fun k => k = i)
  show s78dg_no_kappa p ⌊2 * (i : ℝ) + y⌋ = i
  rw [hfl]
  have := s78dg_no_kappa_edge p hi (r := 0) (by norm_num)
  simpa using this

theorem s78dg_no_petal_include (p : ℕ) (hp : 1 ≤ p) (i : ℕ) (hi : i < p) (one : Set.Ioc (0 : ℝ) 1)
    (hone : (one : ℝ) = 1) :
    ∃ iU : AddCircle (1 : ℝ) → ↥(s78dg_gr_U (NonOrientableRel p 0)), Continuous iU ∧
      ∀ x : ℝ, iU (x : AddCircle (1 : ℝ)) =
        s78dg_no_Psi_fun p hp (one, 2 * (i : ℝ) + Int.fract x) := by
  let f : ℝ → ↥(s78dg_gr_U (NonOrientableRel p 0)) := fun x =>
    s78dg_no_Psi_fun p hp (one, 2 * (i : ℝ) + x)
  have hfc : Continuous f :=
    (s78dg_no_Psi_quot p hp).continuous.comp (continuous_const.prodMk (continuous_const.add continuous_id))
  have hf01 : f 0 = f 1 := by
    change s78dg_no_Psi_fun p hp (one, 2 * (i : ℝ) + 0) = s78dg_no_Psi_fun p hp (one, 2 * (i : ℝ) + 1)
    have h1 := s78dg_no_Psi_vertex p hp one hone ((2 * i : ℕ) : ℤ)
    have h2 := s78dg_no_Psi_vertex p hp one hone (((2 * i : ℕ) : ℤ) + 1)
    push_cast at h1 h2
    rw [add_zero, h1, h2]
  have hFc : Continuous (f ∘ Int.fract) :=
    ContinuousOn.comp_fract'' hfc.continuousOn hf01
  have hq : Topology.IsQuotientMap (fun x : ℝ => (x : AddCircle (1 : ℝ))) :=
    QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))
  have hres : ∀ a b : ℝ, (a : AddCircle (1 : ℝ)) = (b : AddCircle (1 : ℝ)) →
      (f ∘ Int.fract) a = (f ∘ Int.fract) b := by
    intro a b hab
    have h1 : (((a - b : ℝ)) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, hab, sub_self]
    obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h1
    have hab' : a = b + z := by
      have : (z : ℝ) = a - b := by simpa using hz
      linarith
    simp only [Function.comp]
    rw [hab', Int.fract_add_intCast]
  obtain ⟨iU, hi', hiΨ⟩ := s78dg_cs_descent _ hq (f ∘ Int.fract) hFc hres
  exact ⟨iU, hi', fun x => hiΨ x⟩

/-- At the boundary, snapping onto the petal and reading the petal coordinate agree. -/
theorem s78dg_no_tau_G (p : ℕ) (hp : 1 ≤ p) (i : ℕ) (hi : i < p) (one : Set.Ioc (0 : ℝ) 1)
    (hone : (one : ℝ) = 1) (iU : AddCircle (1 : ℝ) → ↥(s78dg_gr_U (NonOrientableRel p 0)))
    (hiU : ∀ x : ℝ, iU (x : AddCircle (1 : ℝ)) = s78dg_no_Psi_fun p hp (one, 2 * (i : ℝ) + Int.fract x))
    {u : ℝ} (hu : u ∈ s78dg_no_S p (fun k => k = i)) :
    s78dg_no_Psi_fun p hp (one, s78dg_no_tau p (fun k => k = i) u) = iU (s78dg_no_G p i u) := by
  have hN : (0 : ℤ) < ((2 * p : ℕ) : ℤ) := by
    have : 0 < p := by omega
    positivity
  set N : ℤ := ((2 * p : ℕ) : ℤ) with hNdef
  have hNR : (N : ℝ) = 2 * (p : ℝ) := by simp [hNdef]
  set k : ℤ := ⌊u⌋ / N with hk
  set n : ℕ := (⌊u⌋ % N).toNat with hn
  have hr0 : 0 ≤ ⌊u⌋ % N := Int.emod_nonneg _ hN.ne'
  have hr1 : ⌊u⌋ % N < N := Int.emod_lt_of_pos _ hN
  have hnZ : (n : ℤ) = ⌊u⌋ % N := Int.toNat_of_nonneg hr0
  have hnlt : n < 2 * p := by
    have : (n : ℤ) < ((2 * p : ℕ) : ℤ) := by rw [hnZ]; exact hr1
    exact_mod_cast this
  have hfl : ⌊u⌋ = (n : ℤ) + k * N := by
    rw [hnZ, hk]
    calc ⌊u⌋ = ⌊u⌋ % N + N * (⌊u⌋ / N) := (Int.emod_add_mul_ediv _ _).symm
      _ = ⌊u⌋ % N + ⌊u⌋ / N * N := by ring
  set w : ℝ := u - (k : ℝ) * (2 * (p : ℝ)) with hw
  have hwu : u = w + (k : ℝ) * (2 * (p : ℝ)) := by rw [hw]; ring
  have hwn0 : (n : ℝ) ≤ w := by
    have h1 : ((⌊u⌋ : ℤ) : ℝ) ≤ u := Int.floor_le u
    rw [hfl] at h1
    push_cast at h1
    rw [hNR] at h1
    rw [hw]; linarith
  have hwn1 : w < (n : ℝ) + 1 := by
    have h1 : u < ((⌊u⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one u
    rw [hfl] at h1
    push_cast at h1
    rw [hNR] at h1
    rw [hw]; linarith
  have hn1' : (n : ℝ) + 1 ≤ 2 * p := by exact_mod_cast Nat.succ_le_of_lt hnlt
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hG : s78dg_no_G p i u = ((min 2 (max 0 (w - 2 * (i : ℝ))) : ℝ) : AddCircle (1 : ℝ)) := by
    rw [hwu, s78dg_no_G_periodic_int]
    exact s78dg_no_G_on_period_le p i hp hi (by linarith) (by linarith)
  have hΨ : ∀ v : ℝ, s78dg_no_Psi_fun p hp (one, v + (k : ℝ) * (2 * (p : ℝ))) =
      s78dg_no_Psi_fun p hp (one, v) := by
    intro v
    have := s78dg_cs_periodic_int (fun q : Set.Ioc (0 : ℝ) 1 × ℝ => s78dg_no_Psi_fun p hp q)
      (2 * (p : ℝ)) one (fun u => by simpa using s78dg_no_Psi_periodic p hp one u) v k
    simpa using this
  have hkap : s78dg_no_kappa p ⌊u⌋ = i ↔ (n = 2 * i ∨ n = 2 * i + 1) :=
    s78dg_no_kappa_eq_iff p i hi ⌊u⌋
  by_cases hP : s78dg_no_kappa p ⌊u⌋ = i
  · rw [s78dg_no_tau_pet p (fun k => k = i) (by exact hP), hG, hiU, hwu, hΨ w]
    have hi' : (i : ℝ) + 1 ≤ p := by exact_mod_cast hi
    rcases hkap.1 hP with h | h
    · have hE : (n : ℝ) = 2 * i := by rw [h]; push_cast; ring
      have e1 : max 0 (w - 2 * (i : ℝ)) = w - 2 * i := max_eq_right (by linarith)
      have e2 : min 2 (w - 2 * (i : ℝ)) = w - 2 * i := min_eq_right (by linarith)
      rw [e1, e2, Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
      rw [show 2 * (i : ℝ) + (w - 2 * i) = w by ring]
    · have hE : (n : ℝ) = 2 * i + 1 := by rw [h]; push_cast; ring
      have e1 : max 0 (w - 2 * (i : ℝ)) = w - 2 * i := max_eq_right (by linarith)
      have e2 : min 2 (w - 2 * (i : ℝ)) = w - 2 * i := min_eq_right (by linarith)
      rw [e1, e2]
      have hfr : Int.fract (w - 2 * (i : ℝ)) = w - 2 * i - 1 := by
        rw [Int.fract, show ⌊w - 2 * (i : ℝ)⌋ = 1 by
          rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith]
        push_cast; ring
      rw [hfr]
      have := s78dg_no_Psi_rel_a p hp one hone ⟨i, hi⟩ (w - 2 * i - 1) (by linarith) (by linarith)
      simp only at this
      rw [show 2 * (i : ℝ) + (w - 2 * i - 1) = 2 * (i : ℝ) + (w - 2 * i - 1) from rfl, this]
      congr 2
      ring
  · have hP' : ¬ (fun k : ℕ => k = i) (s78dg_no_kappa p ⌊u⌋) := hP
    obtain ⟨j, hj⟩ := hu.resolve_right hP
    rw [s78dg_no_tau_vertex' p (fun k => k = i) hj hP']
    have hvert := fun (c : ℤ) => s78dg_no_Psi_vertex p hp one hone c
    have hne : ¬ (n = 2 * i ∨ n = 2 * i + 1) := fun h => hP (hkap.2 h)
    have hg : s78dg_no_G p i u = 0 := by
      rw [hG]
      rcases lt_or_gt_of_ne (show n ≠ 2 * i from fun h => hne (Or.inl h)) with h | h
      · have : (n : ℝ) + 1 ≤ 2 * (i : ℝ) := by exact_mod_cast (by omega : n + 1 ≤ 2 * i)
        have e1 : max 0 (w - 2 * (i : ℝ)) = 0 := max_eq_left (by linarith)
        rw [e1]; simp
      · have h3 : 2 * i + 2 ≤ n := by omega
        have : 2 * (i : ℝ) + 2 ≤ n := by exact_mod_cast h3
        have e1 : max 0 (w - 2 * (i : ℝ)) = w - 2 * i := max_eq_right (by linarith)
        have e2 : min 2 (w - 2 * (i : ℝ)) = 2 := min_eq_left (by linarith)
        rw [e1, e2, s78dg_no_coe_two]
    rw [hg, hvert j]
    have h0 : iU (0 : AddCircle (1 : ℝ)) = s78dg_no_Psi_fun p hp (one, 2 * (i : ℝ) + Int.fract 0) := by
      rw [← hiU 0, AddCircle.coe_zero]
    rw [h0, Int.fract_zero, add_zero]
    have := hvert ((2 * i : ℕ) : ℤ)
    push_cast at this
    exact this.symm

/-- **The petal subsurface has the homotopy type of a circle.** -/
theorem s78dg_no_petal_pi1 (p : ℕ) (hp : 1 ≤ p) (m : ℕ) (hm : m < p) (one : Set.Ioc (0 : ℝ) 1)
    (hone : (one : ℝ) = 1) :
    ∃ i : C(AddCircle (1 : ℝ), ↥(s78dg_no_Y p hp (s78dg_no_S p (fun k => k = m)))),
      (∀ x : ℝ, ((i (x : AddCircle (1 : ℝ)) : ↥(s78dg_no_Y p hp (s78dg_no_S p (fun k => k = m)))) :
          Quot (NonOrientableRel p 0)) =
        ((s78dg_no_Psi_fun p hp (one, 2 * (m : ℝ) + Int.fract x) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
          Quot (NonOrientableRel p 0))) ∧
      ∀ a : AddCircle (1 : ℝ), Function.Bijective (FundamentalGroup.map i a) := by
  obtain ⟨iU, hiUc, hiU⟩ := s78dg_no_petal_include p hp m hm one hone
  obtain ⟨r₀, hr₀c, hr₀⟩ := s78dg_no_petal_retraction p hp m hm
  obtain ⟨H, hHc, hH⟩ := s78dg_no_snap_homotopy p hp (fun k => k = m)
  let Y := s78dg_no_Y p hp (s78dg_no_S p (fun k => k = m))
  have hYU : ∀ q ∈ Y, q ∈ s78dg_gr_U (NonOrientableRel p 0) := s78dg_no_Y_sub_U p hp _
  have hmemi : ∀ t : AddCircle (1 : ℝ),
      ((iU t : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0)) ∈ Y := by
    intro t
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective t
    rw [hiU x]
    exact ⟨(one, 2 * (m : ℝ) + Int.fract x),
      s78dg_no_E_mem p m hm (Int.fract_nonneg x) (Int.fract_lt_one x).le, rfl⟩
  let i : C(AddCircle (1 : ℝ), ↥Y) := ⟨fun t =>
    ⟨((iU t : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0)), hmemi t⟩,
    Continuous.subtype_mk (continuous_subtype_val.comp hiUc) _⟩
  let r : C(↥Y, AddCircle (1 : ℝ)) := ⟨fun y => r₀ ⟨y.1, hYU _ y.2⟩,
    hr₀c.comp (Continuous.subtype_mk continuous_subtype_val _)⟩
  have hGfract : ∀ x : ℝ, s78dg_no_G p m (2 * (m : ℝ) + Int.fract x) = ((Int.fract x : ℝ) : AddCircle (1 : ℝ)) := by
    intro x
    have hm' : (m : ℝ) + 1 ≤ p := by exact_mod_cast hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have h0 := Int.fract_nonneg x
    have h1 := Int.fract_lt_one x
    rw [s78dg_no_G_on_period_le p m hp hm (by linarith) (by linarith)]
    have e1 : max 0 (2 * (m : ℝ) + Int.fract x - 2 * m) = Int.fract x := by
      rw [show 2 * (m : ℝ) + Int.fract x - 2 * m = Int.fract x by ring]; exact max_eq_right h0
    have e2 : min 2 (Int.fract x) = Int.fract x := min_eq_right (by linarith)
    rw [e1, e2]
  have hfract : ∀ x : ℝ, ((Int.fract x : ℝ) : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ)) := by
    intro x
    rw [Int.fract, AddCircle.coe_sub, s78dg_circ_int_coe, sub_zero]
  have hri : ∀ t, r (i t) = t := by
    intro t
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective t
    change r₀ ⟨((iU (x : AddCircle (1 : ℝ)) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
      Quot (NonOrientableRel p 0)), hYU _ (hmemi _)⟩ = _
    have : (⟨((iU (x : AddCircle (1 : ℝ)) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
        Quot (NonOrientableRel p 0)), hYU _ (hmemi _)⟩ : ↥(s78dg_gr_U (NonOrientableRel p 0))) =
        s78dg_no_Psi_fun p hp (one, 2 * (m : ℝ) + Int.fract x) :=
      Subtype.ext (congrArg Subtype.val (hiU x))
    rw [this, hr₀, hGfract, hfract]
  have hmemH : ∀ (s : I) (y : ↥Y), ((H (s, ⟨y.1, hYU _ y.2⟩) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
      Quot (NonOrientableRel p 0)) ∈ Y := by
    intro s y
    obtain ⟨a, ha, hay⟩ := y.2
    have hy : (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_gr_U (NonOrientableRel p 0))) =
        s78dg_no_Psi_fun p hp a := Subtype.ext hay.symm
    rw [hy]
    obtain ⟨ρ', _, hρ'⟩ := hH s a.1 a.2
    rw [show (a.1, a.2) = a from rfl] at hρ'
    rw [hρ']
    exact ⟨(ρ', _), s78dg_no_S_star p _ ha s.2.1 s.2.2, rfl⟩
  have hone' : ∀ (s : I) (ρ : Set.Ioc (0 : ℝ) 1), (ρ : ℝ) = 1 → ∀ ρ' : Set.Ioc (0 : ℝ) 1,
      (ρ' : ℝ) = (1 - (s : ℝ)) * (ρ : ℝ) + (s : ℝ) → ρ' = one := by
    intro s ρ hρ ρ' hρ'
    apply Subtype.ext
    rw [hρ', hρ, hone]; ring
  let HH : ContinuousMap.Homotopy (ContinuousMap.id ↥Y) (i.comp r) :=
    { toFun := fun x => ⟨(H (x.1, ⟨x.2.1, hYU _ x.2.2⟩) : Quot (NonOrientableRel p 0)), hmemH x.1 x.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        refine continuous_subtype_val.comp (hHc.comp (continuous_fst.prodMk ?_))
        exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_snd) _
      map_zero_left := fun y => by
        apply Subtype.ext
        obtain ⟨a, ha, hay⟩ := y.2
        have hy : (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_gr_U (NonOrientableRel p 0))) =
            s78dg_no_Psi_fun p hp a := Subtype.ext hay.symm
        change ((H ((0 : I), (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_gr_U (NonOrientableRel p 0)))) :
          ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0)) = y.1
        rw [hy]
        obtain ⟨ρ', hρ', hρ⟩ := hH 0 a.1 a.2
        rw [show (a.1, a.2) = a from rfl] at hρ
        rw [hρ]
        have e1 : ρ' = a.1 := Subtype.ext (by rw [hρ']; simp)
        have e2 : (1 - ((0 : I) : ℝ)) * a.2 + ((0 : I) : ℝ) * s78dg_no_tau p (fun k => k = m) a.2 = a.2 := by
          simp
        rw [e1, e2]
        exact hay
      map_one_left := fun y => by
        apply Subtype.ext
        obtain ⟨a, ha, hay⟩ := y.2
        have hy : (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_gr_U (NonOrientableRel p 0))) =
            s78dg_no_Psi_fun p hp a := Subtype.ext hay.symm
        change ((H ((1 : I), (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_gr_U (NonOrientableRel p 0)))) :
          ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0)) =
          ((iU (r₀ ⟨y.1, hYU _ y.2⟩) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
            Quot (NonOrientableRel p 0))
        rw [hy]
        obtain ⟨ρ', hρ', hρ⟩ := hH 1 a.1 a.2
        rw [show (a.1, a.2) = a from rfl] at hρ
        rw [hρ]
        have e1 : ρ' = one := by
          apply Subtype.ext
          rw [hρ', hone]; simp
        have e2 : (1 - ((1 : I) : ℝ)) * a.2 + ((1 : I) : ℝ) * s78dg_no_tau p (fun k => k = m) a.2 =
            s78dg_no_tau p (fun k => k = m) a.2 := by simp
        rw [e1, e2, s78dg_no_tau_G p hp m hm one hone iU hiU ha]
        have := hr₀ a.1 a.2
        rw [show (a.1, a.2) = a from rfl] at this
        rw [this] }
  refine ⟨i, fun x => congrArg Subtype.val (hiU x), fun a => ?_⟩
  refine s78dg_pi1_deformation_bijective i r hri HH (fun y s => ?_) a
  apply Subtype.ext
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  have hix : (⟨((iU (x : AddCircle (1 : ℝ)) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
      Quot (NonOrientableRel p 0)), hYU _ (hmemi _)⟩ : ↥(s78dg_gr_U (NonOrientableRel p 0))) =
      s78dg_no_Psi_fun p hp (one, 2 * (m : ℝ) + Int.fract x) :=
    Subtype.ext (congrArg Subtype.val (hiU x))
  change ((H (s, (⟨((iU (x : AddCircle (1 : ℝ)) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
      Quot (NonOrientableRel p 0)), hYU _ (hmemi _)⟩ : ↥(s78dg_gr_U (NonOrientableRel p 0)))) :
      ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0)) =
    ((iU (x : AddCircle (1 : ℝ)) : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0))
  rw [hix]
  obtain ⟨ρ', hρ', hρ⟩ := hH s one (2 * (m : ℝ) + Int.fract x)
  rw [hρ, s78dg_no_tau_E p m hm (Int.fract_nonneg x) (Int.fract_lt_one x)]
  have e1 : ρ' = one := hone' s one hone ρ' hρ'
  have e2 : (1 - (s : ℝ)) * (2 * (m : ℝ) + Int.fract x) + (s : ℝ) * (2 * (m : ℝ) + Int.fract x) =
      2 * (m : ℝ) + Int.fract x := by ring
  rw [e1, e2, hiU x]


end LiZhongQC
