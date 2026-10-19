import LiZhongQC.Lemmas.SchottkyClosedSurface5
import LiZhongQC.Lemmas.SchottkyClosedSurface6
import LiZhongQC.Lemmas.SchottkyPi1Deformation
import LiZhongQC.Lemmas.SchottkyCircleFundamental

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology unitInterval

namespace LiZhongQC

/-- The retraction of the punctured chart onto the petal coordinate. -/
theorem s78dg_cs_petal_retraction (p : ℕ) (hp : 1 ≤ p) (m : ℕ) (hm : m < 2 * p) :
    ∃ r : ↥(s78dg_cs_U p 0) → AddCircle (1 : ℝ), Continuous r ∧
      ∀ (ρ : Set.Ioc (0 : ℝ) 1) (u : ℝ), r (s78dg_cs_Psi_fun p hp (ρ, u)) =
        ((s78dg_cs_G p m u : ℝ) : AddCircle (1 : ℝ)) := by
  have hF : Continuous (fun a : Set.Ioc (0 : ℝ) 1 × ℝ => ((s78dg_cs_G p m a.2 : ℝ) : AddCircle (1 : ℝ))) :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp ((s78dg_cs_G_cont p m hp hm).comp continuous_snd)
  have hres : ∀ a b : Set.Ioc (0 : ℝ) 1 × ℝ, s78dg_cs_Psi_fun p hp a = s78dg_cs_Psi_fun p hp b →
      ((s78dg_cs_G p m a.2 : ℝ) : AddCircle (1 : ℝ)) = ((s78dg_cs_G p m b.2 : ℝ) : AddCircle (1 : ℝ)) := by
    refine s78dg_cs_respects p hp (s78dg_cs_Psi_fun p hp) (s78dg_cs_Psi_spec p hp)
      (fun a : Set.Ioc (0 : ℝ) 1 × ℝ => ((s78dg_cs_G p m a.2 : ℝ) : AddCircle (1 : ℝ)))
      (fun ρ u => ?_) ⟨1, zero_lt_one, le_rfl⟩ rfl ?_ ?_
    · simp only
      have := s78dg_cs_G_periodic p m u
      push_cast
      rw [this]
    · intro i x h0 h1
      exact s78dg_cs_G_glue_a p m hp hm i x h0 h1
    · intro i x h0 h1
      exact s78dg_cs_G_glue_b p m hp hm i x h0 h1
  obtain ⟨r, hr, hrΨ⟩ := s78dg_cs_descent _ (s78dg_cs_Psi_quot p hp) _ hF hres
  exact ⟨r, hr, fun ρ u => hrΨ (ρ, u)⟩

theorem s78dg_cs_tau_periodic_int (p : ℕ) (P : ℕ → Prop) (u : ℝ) (k : ℤ) :
    s78dg_cs_tau p P (u + k * ((4 * p : ℕ) : ℝ)) = s78dg_cs_tau p P u + k * ((4 * p : ℕ) : ℝ) := by
  have h := s78dg_cs_periodic_int (fun q : Unit × ℝ => s78dg_cs_tau p P q.2 - q.2)
    ((4 * p : ℕ) : ℝ) () (fun v => by
      simp only
      rw [s78dg_cs_tau_periodic]; ring) u k
  simp only at h
  linarith

theorem s78dg_cs_G_periodic_int (p m : ℕ) (u : ℝ) (k : ℤ) :
    s78dg_cs_G p m (u + k * (4 * (p : ℝ))) = s78dg_cs_G p m u := by
  have := s78dg_cs_periodic_int (fun q : Unit × ℝ => s78dg_cs_G p m q.2) (4 * (p : ℝ)) ()
    (fun v => s78dg_cs_G_periodic p m v) u k
  simpa using this

theorem s78dg_cs_kappa_eq_iff (p m : ℕ) (hm : m < 2 * p) (j : ℤ) :
    s78dg_cs_kappa p j = m ↔
      ((j % ((4 * p : ℕ) : ℤ)).toNat = 4 * (m / 2) + m % 2 ∨
        (j % ((4 * p : ℕ) : ℤ)).toNat = 4 * (m / 2) + m % 2 + 2) := by
  unfold s78dg_cs_kappa
  have hN : (0 : ℤ) < ((4 * p : ℕ) : ℤ) := by
    have : 0 < p := by omega
    positivity
  have h0 : 0 ≤ j % ((4 * p : ℕ) : ℤ) := Int.emod_nonneg _ hN.ne'
  have h1 : j % ((4 * p : ℕ) : ℤ) < ((4 * p : ℕ) : ℤ) := Int.emod_lt_of_pos _ hN
  have hlt : (j % ((4 * p : ℕ) : ℤ)).toNat < 4 * p := by
    have := Int.toNat_of_nonneg h0
    omega
  generalize (j % ((4 * p : ℕ) : ℤ)).toNat = n at hlt ⊢
  omega

theorem s78dg_cs_tau_vertex' (p : ℕ) (P : ℕ → Prop) {u : ℝ} {j : ℤ} (hj : |u - j| < 1 / 4)
    (hP : ¬ P (s78dg_cs_kappa p ⌊u⌋)) : s78dg_cs_tau p P u = j := by
  rw [abs_lt] at hj
  rcases le_or_gt (j : ℝ) u with hju | hju
  · have hfl : ⌊u⌋ = j := by rw [Int.floor_eq_iff]; constructor <;> linarith
    have hfr : Int.fract u = u - j := by rw [Int.fract, hfl]
    rw [s78dg_cs_tau_snap p P hP, hfr, s78dg_cs_T_low (by linarith)]; ring
  · have hfl : ⌊u⌋ = j - 1 := by rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have hfr : Int.fract u = u - (j - 1) := by rw [Int.fract, hfl]; push_cast; ring
    rw [s78dg_cs_tau_snap p P hP, hfr, s78dg_cs_T_high (by linarith)]; ring

theorem s78dg_cs_kappa_E (p m : ℕ) (hm : m < 2 * p) :
    s78dg_cs_kappa p ((4 * (m / 2) + m % 2 : ℕ) : ℤ) = m := by
  have h := s78dg_cs_kappa_edge p (i := m / 2) (r := m % 2) (by omega) (by omega)
  rw [h]; omega

theorem s78dg_cs_E_mem (p m : ℕ) (hm : m < 2 * p) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    s78dg_cs_E m + x ∈ s78dg_cs_S p (fun k => k = m) := by
  have hE : s78dg_cs_E m = ((((4 * (m / 2) + m % 2 : ℕ) : ℤ)) : ℝ) := by
    unfold s78dg_cs_E; exact (Int.cast_natCast _).symm
  rcases eq_or_lt_of_le h1 with h | h
  · left
    refine ⟨((4 * (m / 2) + m % 2 : ℕ) : ℤ) + 1, ?_⟩
    rw [hE, h]; simp
  · right
    have hfl : ⌊s78dg_cs_E m + x⌋ = ((4 * (m / 2) + m % 2 : ℕ) : ℤ) := by
      rw [Int.floor_eq_iff, hE]; constructor <;> linarith
    rw [hfl]
    exact s78dg_cs_kappa_E p m hm

/-- At the boundary, snapping onto the petal and reading the petal coordinate agree. -/
theorem s78dg_cs_tau_G (p : ℕ) (hp : 1 ≤ p) (m : ℕ) (hm : m < 2 * p) (one : Set.Ioc (0 : ℝ) 1)
    (hone : (one : ℝ) = 1) {u : ℝ} (hu : u ∈ s78dg_cs_S p (fun k => k = m)) :
    s78dg_cs_Psi_fun p hp (one, s78dg_cs_tau p (fun k => k = m) u) =
      s78dg_cs_Psi_fun p hp (one, s78dg_cs_E m + s78dg_cs_G p m u) := by
  have hN : (0 : ℤ) < ((4 * p : ℕ) : ℤ) := by
    have : 0 < p := by omega
    positivity
  set N : ℤ := ((4 * p : ℕ) : ℤ) with hNdef
  have hNR : (N : ℝ) = 4 * (p : ℝ) := by simp [hNdef]
  set k : ℤ := ⌊u⌋ / N with hk
  set n : ℕ := (⌊u⌋ % N).toNat with hn
  have hr0 : 0 ≤ ⌊u⌋ % N := Int.emod_nonneg _ hN.ne'
  have hr1 : ⌊u⌋ % N < N := Int.emod_lt_of_pos _ hN
  have hnZ : (n : ℤ) = ⌊u⌋ % N := Int.toNat_of_nonneg hr0
  have hnlt : n < 4 * p := by
    have : (n : ℤ) < ((4 * p : ℕ) : ℤ) := by rw [hnZ]; exact hr1
    exact_mod_cast this
  have hfl : ⌊u⌋ = (n : ℤ) + k * N := by
    rw [hnZ, hk]
    calc ⌊u⌋ = ⌊u⌋ % N + N * (⌊u⌋ / N) := (Int.emod_add_mul_ediv _ _).symm
      _ = ⌊u⌋ % N + ⌊u⌋ / N * N := by ring
  set w : ℝ := u - (k : ℝ) * (4 * (p : ℝ)) with hw
  have hwu : u = w + (k : ℝ) * (4 * (p : ℝ)) := by rw [hw]; ring
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
  have hG : s78dg_cs_G p m u = s78dg_cs_prof (s78dg_cs_E m) w := by
    rw [hwu, s78dg_cs_G_periodic_int]
    have hn1' : (n : ℝ) + 1 ≤ 4 * p := by exact_mod_cast Nat.succ_le_of_lt hnlt
    exact s78dg_cs_G_on_period_le p m hp hm (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      (by linarith)
  have hΨ : ∀ v : ℝ, s78dg_cs_Psi_fun p hp (one, v + (k : ℝ) * (4 * (p : ℝ))) =
      s78dg_cs_Psi_fun p hp (one, v) := by
    intro v
    have := s78dg_cs_periodic_int (fun q : Set.Ioc (0 : ℝ) 1 × ℝ => s78dg_cs_Psi_fun p hp q)
      (4 * (p : ℝ)) one (fun u => by simpa using s78dg_cs_Psi_periodic p hp one u) v k
    simpa using this
  have hEnat : s78dg_cs_E m = (((4 * (m / 2) + m % 2 : ℕ) : ℤ) : ℝ) := by
    unfold s78dg_cs_E; exact (Int.cast_natCast _).symm
  have hkap : s78dg_cs_kappa p ⌊u⌋ = m ↔
      (n = 4 * (m / 2) + m % 2 ∨ n = 4 * (m / 2) + m % 2 + 2) :=
    s78dg_cs_kappa_eq_iff p m hm ⌊u⌋
  by_cases hP : s78dg_cs_kappa p ⌊u⌋ = m
  · rw [s78dg_cs_tau_pet p (fun k => k = m) (by exact hP), hG, hwu, hΨ w]
    have hEn : s78dg_cs_E m = ((4 * (m / 2) + m % 2 : ℕ) : ℝ) := rfl
    rcases hkap.1 hP with h | h
    · have hE : s78dg_cs_E m = (n : ℝ) := by rw [hEn, h]
      rw [s78dg_cs_prof_rise (by rw [hE]; exact hwn0) (by rw [hE]; linarith)]
      rw [show s78dg_cs_E m + (w - s78dg_cs_E m) = w by ring]
    · have hE : s78dg_cs_E m + 2 = (n : ℝ) := by
        rw [hEn, h]; try (push_cast; ring)
      rw [s78dg_cs_prof_fall (by rw [hE]; exact hwn0) (by rw [← hE] at hwn1; linarith)]
      have hmi : m / 2 < p := by omega
      have hy0 : 0 ≤ w - (s78dg_cs_E m + 2) := by linarith
      have hy1 : w - (s78dg_cs_E m + 2) ≤ 1 := by linarith
      rcases Nat.mod_two_eq_zero_or_one m with h2 | h2
      · have hE4 : s78dg_cs_E m = 4 * ((⟨m / 2, hmi⟩ : Fin p) : ℝ) := by
          rw [hEn, h2]; push_cast; ring
        have := s78dg_cs_Psi_rel_a p hp one hone ⟨m / 2, hmi⟩ (1 - (w - (s78dg_cs_E m + 2)))
          (by linarith) (by linarith)
        rw [show 4 * ((⟨m / 2, hmi⟩ : Fin p) : ℝ) + (1 - (w - (s78dg_cs_E m + 2))) =
            s78dg_cs_E m + (1 - (w - (s78dg_cs_E m + 2))) by rw [hE4],
          show 4 * ((⟨m / 2, hmi⟩ : Fin p) : ℝ) + 3 - (1 - (w - (s78dg_cs_E m + 2))) = w by
            rw [← hE4]; ring] at this
        exact this.symm
      · have hE4 : s78dg_cs_E m = 4 * ((⟨m / 2, hmi⟩ : Fin p) : ℝ) + 1 := by
          rw [hEn, h2]; push_cast; ring
        have := s78dg_cs_Psi_rel_b p hp one hone ⟨m / 2, hmi⟩ (1 - (w - (s78dg_cs_E m + 2)))
          (by linarith) (by linarith)
        rw [show 4 * ((⟨m / 2, hmi⟩ : Fin p) : ℝ) + 1 + (1 - (w - (s78dg_cs_E m + 2))) =
            s78dg_cs_E m + (1 - (w - (s78dg_cs_E m + 2))) by linarith,
          show 4 * ((⟨m / 2, hmi⟩ : Fin p) : ℝ) + 4 - (1 - (w - (s78dg_cs_E m + 2))) = w by
            rw [show 4 * ((⟨m / 2, hmi⟩ : Fin p) : ℝ) = s78dg_cs_E m - 1 by linarith]; ring] at this
        exact this.symm
  · have hP' : ¬ (fun k : ℕ => k = m) (s78dg_cs_kappa p ⌊u⌋) := hP
    obtain ⟨j, hj⟩ := hu.resolve_right hP
    rw [s78dg_cs_tau_vertex' p (fun k => k = m) hj hP']
    have hvert := fun (c : ℤ) => s78dg_cs_Psi_vertex p hp one hone c
    have hEn : s78dg_cs_E m = (((4 * (m / 2) + m % 2 : ℕ) : ℤ) : ℝ) := by
      unfold s78dg_cs_E; exact (Int.cast_natCast _).symm
    have hne : ¬ (n = 4 * (m / 2) + m % 2 ∨ n = 4 * (m / 2) + m % 2 + 2) := fun h => hP (hkap.2 h)
    have hEreal : s78dg_cs_E m = ((4 * (m / 2) + m % 2 : ℕ) : ℝ) := rfl
    have hg : s78dg_cs_G p m u = 0 ∨ s78dg_cs_G p m u = 1 := by
      rw [hG]
      rcases lt_trichotomy n (4 * (m / 2) + m % 2) with h | h | h
      · left
        apply s78dg_cs_prof_zero
        have : (n : ℝ) + 1 ≤ s78dg_cs_E m := by
          rw [hEreal]; exact_mod_cast h
        linarith
      · exact absurd (Or.inl h) hne
      · rcases lt_trichotomy n (4 * (m / 2) + m % 2 + 1) with h' | h' | h'
        · omega
        · right
          have hE1 : s78dg_cs_E m + 1 = (n : ℝ) := by
            rw [hEreal, h']; try (push_cast; ring)
          apply s78dg_cs_prof_mid
          · linarith
          · linarith
        · have h3 : 4 * (m / 2) + m % 2 + 3 ≤ n := by omega
          left
          have hE3 : s78dg_cs_E m + 3 ≤ (n : ℝ) := by rw [hEreal]; exact_mod_cast h3
          apply s78dg_cs_prof_end
          linarith
    rcases hg with hg | hg
    · rw [hg, hvert j, add_zero, hEn, hvert]
    · rw [hg, hvert j]
      have hE1' : s78dg_cs_E m + 1 = ((((4 * (m / 2) + m % 2 : ℕ) : ℤ) + 1 : ℤ) : ℝ) := by
        rw [hEn, Int.cast_add, Int.cast_one]
      rw [hE1', hvert]

theorem s78dg_cs_prof_bounds (E u : ℝ) : 0 ≤ s78dg_cs_prof E u ∧ s78dg_cs_prof E u ≤ 1 := by
  unfold s78dg_cs_prof
  simp only [min_def, max_def]
  split_ifs <;> constructor <;> linarith

theorem s78dg_cs_G_bounds (p m : ℕ) (u : ℝ) : 0 ≤ s78dg_cs_G p m u ∧ s78dg_cs_G p m u ≤ 1 :=
  s78dg_cs_prof_bounds _ _

/-- The petal loop as a map from the circle into the punctured chart. -/
theorem s78dg_cs_petal_include (p : ℕ) (hp : 1 ≤ p) (m : ℕ) (hm : m < 2 * p) (one : Set.Ioc (0 : ℝ) 1)
    (hone : (one : ℝ) = 1) :
    ∃ i : AddCircle (1 : ℝ) → ↥(s78dg_cs_U p 0), Continuous i ∧
      ∀ x : ℝ, i (x : AddCircle (1 : ℝ)) =
        s78dg_cs_Psi_fun p hp (one, s78dg_cs_E m + Int.fract x) := by
  let f : ℝ → ↥(s78dg_cs_U p 0) := fun x => s78dg_cs_Psi_fun p hp (one, s78dg_cs_E m + x)
  have hfc : Continuous f :=
    (s78dg_cs_Psi_quot p hp).continuous.comp (continuous_const.prodMk (continuous_const.add continuous_id))
  have hE0 : s78dg_cs_E m = (((4 * (m / 2) + m % 2 : ℕ) : ℤ) : ℝ) := by
    unfold s78dg_cs_E; exact (Int.cast_natCast _).symm
  have hf01 : f 0 = f 1 := by
    change s78dg_cs_Psi_fun p hp (one, s78dg_cs_E m + 0) = s78dg_cs_Psi_fun p hp (one, s78dg_cs_E m + 1)
    have h1 := s78dg_cs_Psi_vertex p hp one hone ((4 * (m / 2) + m % 2 : ℕ) : ℤ)
    have h2 := s78dg_cs_Psi_vertex p hp one hone (((4 * (m / 2) + m % 2 : ℕ) : ℤ) + 1)
    rw [Int.cast_add, Int.cast_one] at h2
    rw [add_zero, hE0, h1, h2]
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
  obtain ⟨i, hi, hiΨ⟩ := s78dg_cs_descent _ hq (f ∘ Int.fract) hFc hres
  exact ⟨i, hi, fun x => hiΨ x⟩

theorem s78dg_cs_Psi_E_end (p : ℕ) (hp : 1 ≤ p) (m : ℕ) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1) :
    s78dg_cs_Psi_fun p hp (one, s78dg_cs_E m + 0) = s78dg_cs_Psi_fun p hp (one, s78dg_cs_E m + 1) := by
  have hE0 : s78dg_cs_E m = (((4 * (m / 2) + m % 2 : ℕ) : ℤ) : ℝ) := by
    unfold s78dg_cs_E; exact (Int.cast_natCast _).symm
  have h1 := s78dg_cs_Psi_vertex p hp one hone ((4 * (m / 2) + m % 2 : ℕ) : ℤ)
  have h2 := s78dg_cs_Psi_vertex p hp one hone (((4 * (m / 2) + m % 2 : ℕ) : ℤ) + 1)
  rw [Int.cast_add, Int.cast_one] at h2
  rw [add_zero, hE0, h1, h2]

theorem s78dg_cs_tau_E (p m : ℕ) (hm : m < 2 * p) {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    s78dg_cs_tau p (fun k => k = m) (s78dg_cs_E m + y) = s78dg_cs_E m + y := by
  have hE : s78dg_cs_E m = (((4 * (m / 2) + m % 2 : ℕ) : ℤ) : ℝ) := by
    unfold s78dg_cs_E; exact (Int.cast_natCast _).symm
  have hfl : ⌊s78dg_cs_E m + y⌋ = ((4 * (m / 2) + m % 2 : ℕ) : ℤ) := by
    rw [Int.floor_eq_iff, hE]; constructor <;> linarith
  apply s78dg_cs_tau_pet p (fun k => k = m)
  show s78dg_cs_kappa p ⌊s78dg_cs_E m + y⌋ = m
  rw [hfl]
  exact s78dg_cs_kappa_E p m hm

/-- **The petal subsurface has the homotopy type of a circle.**  The neighbourhood `Y_m` of the vertex
and the `m`-th petal (pair of glued edges) deformation retracts onto the petal circle; hence `π₁` of
`Y_m` is the image of `π₁(S¹) = ℤ`. -/
theorem s78dg_cs_petal_pi1 (p : ℕ) (hp : 1 ≤ p) (m : ℕ) (hm : m < 2 * p) (one : Set.Ioc (0 : ℝ) 1)
    (hone : (one : ℝ) = 1) :
    ∃ i : C(AddCircle (1 : ℝ), ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun k => k = m)))),
      (∀ x : ℝ, ((i (x : AddCircle (1 : ℝ)) : ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun k => k = m)))) :
          Quot (OrientableRel p 0)) =
        ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E m + Int.fract x) : ↥(s78dg_cs_U p 0)) :
          Quot (OrientableRel p 0))) ∧
      ∀ a : AddCircle (1 : ℝ), Function.Bijective (FundamentalGroup.map i a) := by
  obtain ⟨iU, hiUc, hiU⟩ := s78dg_cs_petal_include p hp m hm one hone
  obtain ⟨r₀, hr₀c, hr₀⟩ := s78dg_cs_petal_retraction p hp m hm
  obtain ⟨H, hHc, hH⟩ := s78dg_cs_snap_homotopy p hp (fun k => k = m)
  let Y := s78dg_cs_Y p hp (s78dg_cs_S p (fun k => k = m))
  have hYU : ∀ q ∈ Y, q ∈ s78dg_cs_U p 0 := s78dg_cs_Y_sub_U p hp _
  have hmemi : ∀ t : AddCircle (1 : ℝ), ((iU t : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) ∈ Y := by
    intro t
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective t
    rw [hiU x]
    exact ⟨(one, s78dg_cs_E m + Int.fract x),
      s78dg_cs_E_mem p m hm (Int.fract_nonneg x) (Int.fract_lt_one x).le, rfl⟩
  let i : C(AddCircle (1 : ℝ), ↥Y) := ⟨fun t => ⟨((iU t : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
    hmemi t⟩, Continuous.subtype_mk (continuous_subtype_val.comp hiUc) _⟩
  let r : C(↥Y, AddCircle (1 : ℝ)) := ⟨fun y => r₀ ⟨y.1, hYU _ y.2⟩,
    hr₀c.comp (Continuous.subtype_mk continuous_subtype_val _)⟩
  have hGfract : ∀ x : ℝ, s78dg_cs_G p m (s78dg_cs_E m + Int.fract x) = Int.fract x := by
    intro x
    have hE4 : s78dg_cs_E m + 3 ≤ 4 * p := by
      unfold s78dg_cs_E
      have : 4 * (m / 2) + m % 2 + 3 ≤ 4 * p := by omega
      exact_mod_cast this
    have hE0 : (0 : ℝ) ≤ s78dg_cs_E m := by unfold s78dg_cs_E; positivity
    have h0 := Int.fract_nonneg x
    have h1 := Int.fract_lt_one x
    rw [s78dg_cs_G_on_period_le p m hp hm (by linarith) (by linarith),
      s78dg_cs_prof_rise (by linarith) (by linarith)]
    ring
  have hfract : ∀ x : ℝ, ((Int.fract x : ℝ) : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ)) := by
    intro x
    rw [Int.fract, AddCircle.coe_sub, s78dg_circ_int_coe, sub_zero]
  have hri : ∀ t, r (i t) = t := by
    intro t
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective t
    change r₀ ⟨((iU (x : AddCircle (1 : ℝ)) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
      hYU _ (hmemi _)⟩ = _
    have : (⟨((iU (x : AddCircle (1 : ℝ)) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
        hYU _ (hmemi _)⟩ : ↥(s78dg_cs_U p 0)) = s78dg_cs_Psi_fun p hp (one, s78dg_cs_E m + Int.fract x) :=
      Subtype.ext (congrArg Subtype.val (hiU x))
    rw [this, hr₀, hGfract, hfract]
  have hmemH : ∀ (s : I) (y : ↥Y), ((H (s, ⟨y.1, hYU _ y.2⟩) : ↥(s78dg_cs_U p 0)) :
      Quot (OrientableRel p 0)) ∈ Y := by
    intro s y
    obtain ⟨a, ha, hay⟩ := y.2
    have hy : (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_cs_U p 0)) = s78dg_cs_Psi_fun p hp a := Subtype.ext hay.symm
    rw [hy]
    obtain ⟨ρ', _, hρ'⟩ := hH s a.1 a.2
    rw [show (a.1, a.2) = a from rfl] at hρ'
    rw [hρ']
    exact ⟨(ρ', _), s78dg_cs_S_star p _ ha s.2.1 s.2.2, rfl⟩
  have hone' : ∀ (s : I) (ρ : Set.Ioc (0 : ℝ) 1), (ρ : ℝ) = 1 → ∀ ρ' : Set.Ioc (0 : ℝ) 1,
      (ρ' : ℝ) = (1 - (s : ℝ)) * (ρ : ℝ) + (s : ℝ) → ρ' = one := by
    intro s ρ hρ ρ' hρ'
    apply Subtype.ext
    rw [hρ', hρ, hone]; ring
  let HH : ContinuousMap.Homotopy (ContinuousMap.id ↥Y) (i.comp r) :=
    { toFun := fun x => ⟨(H (x.1, ⟨x.2.1, hYU _ x.2.2⟩) : Quot (OrientableRel p 0)), hmemH x.1 x.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        refine continuous_subtype_val.comp (hHc.comp (continuous_fst.prodMk ?_))
        exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_snd) _
      map_zero_left := fun y => by
        apply Subtype.ext
        obtain ⟨a, ha, hay⟩ := y.2
        have hy : (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_cs_U p 0)) = s78dg_cs_Psi_fun p hp a := Subtype.ext hay.symm
        change ((H ((0 : I), (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_cs_U p 0))) : ↥(s78dg_cs_U p 0)) :
          Quot (OrientableRel p 0)) = y.1
        rw [hy]
        obtain ⟨ρ', hρ', hρ⟩ := hH 0 a.1 a.2
        rw [show (a.1, a.2) = a from rfl] at hρ
        rw [hρ]
        have e1 : ρ' = a.1 := Subtype.ext (by rw [hρ']; simp)
        have e2 : (1 - ((0 : I) : ℝ)) * a.2 + ((0 : I) : ℝ) * s78dg_cs_tau p (fun k => k = m) a.2 = a.2 := by
          simp
        rw [e1, e2]
        exact hay
      map_one_left := fun y => by
        apply Subtype.ext
        obtain ⟨a, ha, hay⟩ := y.2
        have hy : (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_cs_U p 0)) = s78dg_cs_Psi_fun p hp a := Subtype.ext hay.symm
        change ((H ((1 : I), (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_cs_U p 0))) : ↥(s78dg_cs_U p 0)) :
          Quot (OrientableRel p 0)) = ((iU (r₀ ⟨y.1, hYU _ y.2⟩) : ↥(s78dg_cs_U p 0)) :
            Quot (OrientableRel p 0))
        rw [hy]
        obtain ⟨ρ', hρ', hρ⟩ := hH 1 a.1 a.2
        rw [show (a.1, a.2) = a from rfl] at hρ
        rw [hρ]
        have e1 : ρ' = one := by
          apply Subtype.ext
          rw [hρ', hone]; simp
        have e2 : (1 - ((1 : I) : ℝ)) * a.2 + ((1 : I) : ℝ) * s78dg_cs_tau p (fun k => k = m) a.2 =
            s78dg_cs_tau p (fun k => k = m) a.2 := by simp
        rw [e1, e2, s78dg_cs_tau_G p hp m hm one hone ha]
        have := hr₀ a.1 a.2
        rw [show (a.1, a.2) = a from rfl] at this
        rw [this]
        obtain ⟨hg0, hg1⟩ := s78dg_cs_G_bounds p m a.2
        rw [show (((s78dg_cs_G p m a.2 : ℝ)) : AddCircle (1 : ℝ)) = ((s78dg_cs_G p m a.2 : ℝ) : AddCircle (1 : ℝ)) from rfl,
          hiU (s78dg_cs_G p m a.2)]
        rcases eq_or_lt_of_le hg1 with h | h
        · rw [h, Int.fract_one]
          exact congrArg Subtype.val (s78dg_cs_Psi_E_end p hp m one hone).symm
        · rw [Int.fract_eq_self.2 ⟨hg0, h⟩] }
  refine ⟨i, fun x => congrArg Subtype.val (hiU x), fun a => ?_⟩
  refine s78dg_pi1_deformation_bijective i r hri HH (fun y s => ?_) a
  apply Subtype.ext
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  have hix : (⟨((iU (x : AddCircle (1 : ℝ)) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
      hYU _ (hmemi _)⟩ : ↥(s78dg_cs_U p 0)) = s78dg_cs_Psi_fun p hp (one, s78dg_cs_E m + Int.fract x) :=
    Subtype.ext (congrArg Subtype.val (hiU x))
  change ((H (s, (⟨((iU (x : AddCircle (1 : ℝ)) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
      hYU _ (hmemi _)⟩ : ↥(s78dg_cs_U p 0))) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) =
    ((iU (x : AddCircle (1 : ℝ)) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))
  rw [hix]
  obtain ⟨ρ', hρ', hρ⟩ := hH s one (s78dg_cs_E m + Int.fract x)
  rw [hρ, s78dg_cs_tau_E p m hm (Int.fract_nonneg x) (Int.fract_lt_one x)]
  have e1 : ρ' = one := hone' s one hone ρ' hρ'
  have e2 : (1 - (s : ℝ)) * (s78dg_cs_E m + Int.fract x) + (s : ℝ) * (s78dg_cs_E m + Int.fract x) =
      s78dg_cs_E m + Int.fract x := by ring
  rw [e1, e2, hiU x]

end LiZhongQC
