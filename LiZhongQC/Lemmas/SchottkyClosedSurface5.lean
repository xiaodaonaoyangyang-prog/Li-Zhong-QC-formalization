import LiZhongQC.Lemmas.SchottkyClosedSurface3
import LiZhongQC.Lemmas.SchottkyClosedSurface4

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology unitInterval

namespace LiZhongQC

/-- The parameter map `(ρ, u) ↦ π(ρ · exp(2πi u / (4p)))` onto the punctured chart
(chosen from `s78dg_cs_Psi`). -/
noncomputable def s78dg_cs_Psi_fun (p : ℕ) (hp : 1 ≤ p) :
    Set.Ioc (0 : ℝ) 1 × ℝ → ↥(s78dg_cs_U p 0) :=
  (s78dg_cs_Psi p hp).choose

theorem s78dg_cs_Psi_quot (p : ℕ) (hp : 1 ≤ p) : Topology.IsQuotientMap (s78dg_cs_Psi_fun p hp) :=
  (s78dg_cs_Psi p hp).choose_spec.1

theorem s78dg_cs_Psi_spec (p : ℕ) (hp : 1 ≤ p) (ρ : Set.Ioc (0 : ℝ) 1) (u : ℝ) :
    ∃ z : ClosedUnitDisc,
        (z : ℂ) = ((ρ : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((u / (4 * p) : ℝ) : ℂ)) ∧
          ((s78dg_cs_Psi_fun p hp (ρ, u) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) =
            Quot.mk (OrientableRel p 0) z :=
  (s78dg_cs_Psi p hp).choose_spec.2 ρ u

/-- If two parameters give the same disc point (as complex numbers) they have the same image. -/
theorem s78dg_cs_Psi_eq_of_coe (p : ℕ) (hp : 1 ≤ p) (ρ ρ' : Set.Ioc (0 : ℝ) 1) (u u' : ℝ)
    (h : ((ρ : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((u / (4 * p) : ℝ) : ℂ)) =
      ((ρ' : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((u' / (4 * p) : ℝ) : ℂ))) :
    s78dg_cs_Psi_fun p hp (ρ, u) = s78dg_cs_Psi_fun p hp (ρ', u') := by
  obtain ⟨z, hz, hz'⟩ := s78dg_cs_Psi_spec p hp ρ u
  obtain ⟨z', hz2, hz2'⟩ := s78dg_cs_Psi_spec p hp ρ' u'
  have : z = z' := Subtype.ext (hz.trans (h.trans hz2.symm))
  apply Subtype.ext
  rw [hz', hz2', this]

theorem s78dg_cs_Psi_periodic (p : ℕ) (hp : 1 ≤ p) (ρ : Set.Ioc (0 : ℝ) 1) (u : ℝ) :
    s78dg_cs_Psi_fun p hp (ρ, u + 4 * p) = s78dg_cs_Psi_fun p hp (ρ, u) := by
  apply s78dg_cs_Psi_eq_of_coe
  have hN : (4 * (p : ℝ)) ≠ 0 := by positivity
  congr 1
  rw [(s78dg_cs_exp_eq_iff hN (u + 4 * p) u)]
  exact ⟨1, by ring⟩

theorem s78dg_cs_bdy_coe (p : ℕ) (hp : 1 ≤ p) (t : ℝ) :
    ((ClosedUnitDisc.bdyPtOfReal t : ClosedUnitDisc) : ℂ) =
      ((1 : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((t * (4 * p)) / (4 * p) : ℝ) : ℂ)) := by
  have hN : (4 * (p : ℝ)) ≠ 0 := by positivity
  have : (t * (4 * p)) / (4 * p) = t := by field_simp
  rw [this]
  simp [ClosedUnitDisc.bdyPtOfReal, Real.fourierChar_apply]
  congr 1
  push_cast; ring

/-- Gluing of the first kind of edge pair: `4i + x ~ 4i + 3 - x`. -/
theorem s78dg_cs_Psi_rel_a (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (i : Fin p) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ) + x) = s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ) + 3 - x) := by
  obtain ⟨z, hz, hz'⟩ := s78dg_cs_Psi_spec p hp one (4 * (i : ℝ) + x)
  obtain ⟨z', hz2, hz2'⟩ := s78dg_cs_Psi_spec p hp one (4 * (i : ℝ) + 3 - x)
  have hN : (4 * (p : ℝ)) ≠ 0 := by positivity
  have e1 : (4 * (i : ℝ) + x) / (4 * p + 3 * ((0 : ℕ) : ℝ)) * (4 * p) = 4 * i + x := by
    simp; field_simp
  have e2 : (4 * (i : ℝ) + 3 - x) / (4 * p + 3 * ((0 : ℕ) : ℝ)) * (4 * p) = 4 * i + 3 - x := by
    simp; field_simp
  have hzb : z = ClosedUnitDisc.bdyPtOfReal ((4 * (i : ℝ) + x) / (4 * p + 3 * ((0 : ℕ) : ℝ))) := by
    apply Subtype.ext
    rw [hz, s78dg_cs_bdy_coe p hp, e1, hone]
  have hzb' : z' = ClosedUnitDisc.bdyPtOfReal ((4 * (i : ℝ) + 3 - x) / (4 * p + 3 * ((0 : ℕ) : ℝ))) := by
    apply Subtype.ext
    rw [hz2, s78dg_cs_bdy_coe p hp, e2, hone]
  apply Subtype.ext
  rw [hz', hz2', hzb, hzb']
  exact Quot.sound (OrientableRel.a (p := p) (n := 0) ⟨x, h0, h1⟩ i)

/-- Gluing of the second kind of edge pair: `4i + 1 + x ~ 4i + 4 - x`. -/
theorem s78dg_cs_Psi_rel_b (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (i : Fin p) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ) + 1 + x) = s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ) + 4 - x) := by
  obtain ⟨z, hz, hz'⟩ := s78dg_cs_Psi_spec p hp one (4 * (i : ℝ) + 1 + x)
  obtain ⟨z', hz2, hz2'⟩ := s78dg_cs_Psi_spec p hp one (4 * (i : ℝ) + 4 - x)
  have hN : (4 * (p : ℝ)) ≠ 0 := by positivity
  have e1 : (4 * (i : ℝ) + 1 + x) / (4 * p + 3 * ((0 : ℕ) : ℝ)) * (4 * p) = 4 * i + 1 + x := by
    simp; field_simp
  have e2 : (4 * (i : ℝ) + 4 - x) / (4 * p + 3 * ((0 : ℕ) : ℝ)) * (4 * p) = 4 * i + 4 - x := by
    simp; field_simp
  have hzb : z = ClosedUnitDisc.bdyPtOfReal ((4 * (i : ℝ) + 1 + x) / (4 * p + 3 * ((0 : ℕ) : ℝ))) := by
    apply Subtype.ext
    rw [hz, s78dg_cs_bdy_coe p hp, e1, hone]
  have hzb' : z' = ClosedUnitDisc.bdyPtOfReal ((4 * (i : ℝ) + 4 - x) / (4 * p + 3 * ((0 : ℕ) : ℝ))) := by
    apply Subtype.ext
    rw [hz2, s78dg_cs_bdy_coe p hp, e2, hone]
  apply Subtype.ext
  rw [hz', hz2', hzb, hzb']
  exact Quot.sound (OrientableRel.b (p := p) (n := 0) ⟨x, h0, h1⟩ i)

/-- The four corners of the `i`-th handle block are all glued together, and to the next block. -/
theorem s78dg_cs_Psi_block (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (i : Fin p) :
    s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ) + 1) = s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ)) ∧
    s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ) + 2) = s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ)) ∧
    s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ) + 3) = s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ)) ∧
    s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ) + 4) = s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ)) := by
  have a0 := s78dg_cs_Psi_rel_a p hp one hone i 0 le_rfl zero_le_one
  have a1 := s78dg_cs_Psi_rel_a p hp one hone i 1 zero_le_one le_rfl
  have b0 := s78dg_cs_Psi_rel_b p hp one hone i 0 le_rfl zero_le_one
  have b1 := s78dg_cs_Psi_rel_b p hp one hone i 1 zero_le_one le_rfl
  have n1 : (4 * (i : ℝ) + 0) = 4 * (i : ℝ) := by ring
  have n2 : 4 * (i : ℝ) + 3 - 0 = 4 * (i : ℝ) + 3 := by ring
  have n3 : 4 * (i : ℝ) + 3 - 1 = 4 * (i : ℝ) + 2 := by ring
  have n4 : 4 * (i : ℝ) + 1 + 0 = 4 * (i : ℝ) + 1 := by ring
  have n5 : 4 * (i : ℝ) + 4 - 0 = 4 * (i : ℝ) + 4 := by ring
  have n6 : 4 * (i : ℝ) + 1 + 1 = 4 * (i : ℝ) + 2 := by ring
  have n7 : 4 * (i : ℝ) + 4 - 1 = 4 * (i : ℝ) + 3 := by ring
  have n8 : 4 * (i : ℝ) + 1 + 1 = 4 * (i : ℝ) + 2 := by ring
  rw [n1, n2] at a0
  rw [n3] at a1
  rw [n4, n5] at b0
  rw [n6, n7] at b1
  have h3 : s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ) + 3) = s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ)) := a0.symm
  have h2 : s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ) + 2) = s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ)) :=
    b1.trans h3
  have h1 : s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ) + 1) = s78dg_cs_Psi_fun p hp (one, 4 * (i : ℝ)) :=
    a1.trans h2
  exact ⟨h1, h2, h3, b0.symm.trans h1⟩

/-- All vertices of the polygon are identified in the quotient. -/
theorem s78dg_cs_Psi_vertex (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (j : ℤ) : s78dg_cs_Psi_fun p hp (one, (j : ℝ)) = s78dg_cs_Psi_fun p hp (one, 0) := by
  have hA : ∀ n : ℕ, n ≤ p → s78dg_cs_Psi_fun p hp (one, 4 * (n : ℝ)) = s78dg_cs_Psi_fun p hp (one, 0) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k < p := hk
      have hb := (s78dg_cs_Psi_block p hp one hone ⟨k, hk'⟩).2.2.2
      have : 4 * ((k + 1 : ℕ) : ℝ) = 4 * ((⟨k, hk'⟩ : Fin p) : ℝ) + 4 := by push_cast; ring
      rw [this, hb]
      exact ih hk'.le
  let N : ℤ := ((4 * p : ℕ) : ℤ)
  have hNpos : 0 < N := by simp only [N]; positivity
  set r := j % N with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hNpos.ne'
  have hr1 : r < N := Int.emod_lt_of_pos _ hNpos
  have hj : (j : ℝ) = (r : ℝ) + ((j / N : ℤ) : ℝ) * (4 * p) := by
    have : j = r + (j / N) * N := by
      rw [hr]; exact (Int.emod_add_mul_ediv j N).symm.trans (by ring)
    have h2 : (j : ℝ) = (r : ℝ) + ((j / N : ℤ) : ℝ) * (N : ℝ) := by exact_mod_cast this
    rw [h2]; simp [N]
  rw [hj]
  rw [s78dg_cs_periodic_int (fun q : Set.Ioc (0 : ℝ) 1 × ℝ => s78dg_cs_Psi_fun p hp q) (4 * p) one
    (fun u => s78dg_cs_Psi_periodic p hp one u) (r : ℝ) (j / N)]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, r = (n : ℤ) := ⟨r.toNat, (Int.toNat_of_nonneg hr0).symm⟩
  have hnlt : n < 4 * p := by
    have : (n : ℤ) < ((4 * p : ℕ) : ℤ) := by rw [← hn]; exact hr1
    exact_mod_cast this
  have hi : n / 4 < p := by omega
  have hk : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hn' : (n : ℝ) = 4 * ((n / 4 : ℕ) : ℝ) + ((n % 4 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod n 4).symm
  rw [hn]
  have hcast : (((n : ℤ) : ℝ)) = (n : ℝ) := by norm_cast
  rw [hcast, hn']
  have hblock := s78dg_cs_Psi_block p hp one hone ⟨n / 4, hi⟩
  have h4 := hA (n / 4) hi.le
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h | h | h | h
  · rw [h]; simpa using h4
  · rw [h]; push_cast; exact hblock.1.trans h4
  · rw [h]; push_cast; exact hblock.2.1.trans h4
  · rw [h]; push_cast; exact hblock.2.2.1.trans h4

/-- The open subset of the closed surface lying over the boundary parameters in `S`. -/
def s78dg_cs_Y (p : ℕ) (hp : 1 ≤ p) (S : Set ℝ) : Set (Quot (OrientableRel p 0)) :=
  {q | ∃ a : Set.Ioc (0 : ℝ) 1 × ℝ, a.2 ∈ S ∧
    ((s78dg_cs_Psi_fun p hp a : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) = q}

/-- Membership in `Y S` is detected on the boundary parameter, for `S` stable under the period and
the gluings. -/
theorem s78dg_cs_Y_mem (p : ℕ) (hp : 1 ≤ p) (S : Set ℝ)
    (hper : ∀ u, u + ((4 * p : ℕ) : ℝ) ∈ S ↔ u ∈ S)
    (hga : ∀ (i : Fin p) (x : ℝ), 0 ≤ x → x ≤ 1 → (4 * (i : ℝ) + x ∈ S ↔ 4 * (i : ℝ) + 3 - x ∈ S))
    (hgb : ∀ (i : Fin p) (x : ℝ), 0 ≤ x → x ≤ 1 →
      (4 * (i : ℝ) + 1 + x ∈ S ↔ 4 * (i : ℝ) + 4 - x ∈ S))
    (a : Set.Ioc (0 : ℝ) 1 × ℝ) :
    ((s78dg_cs_Psi_fun p hp a : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) ∈ s78dg_cs_Y p hp S ↔
      a.2 ∈ S := by
  constructor
  · rintro ⟨b, hb, hab⟩
    have hab' : s78dg_cs_Psi_fun p hp b = s78dg_cs_Psi_fun p hp a := Subtype.ext hab
    have h1 := s78dg_cs_respects p hp (s78dg_cs_Psi_fun p hp) (s78dg_cs_Psi_spec p hp)
      (fun q : Set.Ioc (0 : ℝ) 1 × ℝ => (q.2 ∈ S))
      (fun ρ u => by have := hper u; push_cast at this; exact propext this)
      ⟨1, zero_lt_one, le_rfl⟩ rfl
      (fun i x h0 h1 => propext (hga i x h0 h1))
      (fun i x h0 h1 => propext (hgb i x h0 h1)) b a hab'
    exact h1 ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem s78dg_cs_Y_open (p : ℕ) (hp : 1 ≤ p) (S : Set ℝ) (hS : IsOpen S)
    (hper : ∀ u, u + ((4 * p : ℕ) : ℝ) ∈ S ↔ u ∈ S)
    (hga : ∀ (i : Fin p) (x : ℝ), 0 ≤ x → x ≤ 1 → (4 * (i : ℝ) + x ∈ S ↔ 4 * (i : ℝ) + 3 - x ∈ S))
    (hgb : ∀ (i : Fin p) (x : ℝ), 0 ≤ x → x ≤ 1 →
      (4 * (i : ℝ) + 1 + x ∈ S ↔ 4 * (i : ℝ) + 4 - x ∈ S)) :
    IsOpen (s78dg_cs_Y p hp S) := by
  have hpre : (s78dg_cs_Psi_fun p hp) ⁻¹' {x : ↥(s78dg_cs_U p 0) |
      (x : Quot (OrientableRel p 0)) ∈ s78dg_cs_Y p hp S} = Set.univ ×ˢ S := by
    ext a
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and]
    exact s78dg_cs_Y_mem p hp S hper hga hgb a
  have hopen : IsOpen {x : ↥(s78dg_cs_U p 0) | (x : Quot (OrientableRel p 0)) ∈ s78dg_cs_Y p hp S} := by
    rw [← (s78dg_cs_Psi_quot p hp).isOpen_preimage, hpre]
    exact isOpen_univ.prod hS
  have himg : s78dg_cs_Y p hp S = Subtype.val '' {x : ↥(s78dg_cs_U p 0) |
      (x : Quot (OrientableRel p 0)) ∈ s78dg_cs_Y p hp S} := by
    ext q
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨s78dg_cs_Psi_fun p hp a, ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  rw [himg]
  exact (s78dg_cs_U_open p 0).isOpenMap_subtype_val _ hopen

/-- A reparametrisation of the boundary circle compatible with the edge gluings induces a well-defined map
of the punctured chart. -/
theorem s78dg_cs_param_respects (p : ℕ) (hp : 1 ≤ p) (rr : Set.Ioc (0 : ℝ) 1 → Set.Ioc (0 : ℝ) 1)
    (hrr : ∀ ρ : Set.Ioc (0 : ℝ) 1, (ρ : ℝ) = 1 → (rr ρ : ℝ) = 1) (g : ℝ → ℝ)
    (hper : ∀ u, g (u + ((4 * p : ℕ) : ℝ)) = g u + ((4 * p : ℕ) : ℝ))
    (hga : ∀ (i : Fin p) (u : ℝ), 4 * (i : ℝ) ≤ u → u ≤ 4 * (i : ℝ) + 1 →
      4 * (i : ℝ) ≤ g u ∧ g u ≤ 4 * (i : ℝ) + 1 ∧ g (8 * (i : ℝ) + 3 - u) = 8 * (i : ℝ) + 3 - g u)
    (hgb : ∀ (i : Fin p) (u : ℝ), 4 * (i : ℝ) + 1 ≤ u → u ≤ 4 * (i : ℝ) + 2 →
      4 * (i : ℝ) + 1 ≤ g u ∧ g u ≤ 4 * (i : ℝ) + 2 ∧ g (8 * (i : ℝ) + 5 - u) = 8 * (i : ℝ) + 5 - g u) :
    ∀ a b : Set.Ioc (0 : ℝ) 1 × ℝ, s78dg_cs_Psi_fun p hp a = s78dg_cs_Psi_fun p hp b →
      s78dg_cs_Psi_fun p hp (rr a.1, g a.2) = s78dg_cs_Psi_fun p hp (rr b.1, g b.2) := by
  refine s78dg_cs_respects p hp (s78dg_cs_Psi_fun p hp) (s78dg_cs_Psi_spec p hp)
    (fun q : Set.Ioc (0 : ℝ) 1 × ℝ => s78dg_cs_Psi_fun p hp (rr q.1, g q.2)) ?_
    ⟨1, zero_lt_one, le_rfl⟩ rfl ?_ ?_
  · intro ρ u
    simp only
    have h := hper u
    push_cast at h
    rw [h]
    exact s78dg_cs_Psi_periodic p hp (rr ρ) (g u)
  · intro i x h0 h1
    simp only
    obtain ⟨e1, e2, e3⟩ := hga i (4 * (i : ℝ) + x) (by linarith) (by linarith)
    have : g (4 * (i : ℝ) + 3 - x) = 8 * i + 3 - g (4 * (i : ℝ) + x) := by
      rw [← e3]; congr 1; ring
    have h1' : (rr ⟨1, zero_lt_one, le_rfl⟩ : ℝ) = 1 := hrr _ rfl
    rw [this]
    have := s78dg_cs_Psi_rel_a p hp (rr ⟨1, zero_lt_one, le_rfl⟩) h1' i (g (4 * (i : ℝ) + x) - 4 * i)
      (by linarith) (by linarith)
    rw [show 4 * (i : ℝ) + (g (4 * (i : ℝ) + x) - 4 * i) = g (4 * (i : ℝ) + x) by ring,
      show 4 * (i : ℝ) + 3 - (g (4 * (i : ℝ) + x) - 4 * i) = 8 * i + 3 - g (4 * (i : ℝ) + x) by ring] at this
    exact this
  · intro i x h0 h1
    simp only
    obtain ⟨e1, e2, e3⟩ := hgb i (4 * (i : ℝ) + 1 + x) (by linarith) (by linarith)
    have : g (4 * (i : ℝ) + 4 - x) = 8 * i + 5 - g (4 * (i : ℝ) + 1 + x) := by
      rw [← e3]; congr 1; ring
    have h1' : (rr ⟨1, zero_lt_one, le_rfl⟩ : ℝ) = 1 := hrr _ rfl
    rw [this]
    have := s78dg_cs_Psi_rel_b p hp (rr ⟨1, zero_lt_one, le_rfl⟩) h1' i (g (4 * (i : ℝ) + 1 + x) - 4 * i - 1)
      (by linarith) (by linarith)
    rw [show 4 * (i : ℝ) + 1 + (g (4 * (i : ℝ) + 1 + x) - 4 * i - 1) = g (4 * (i : ℝ) + 1 + x) by ring,
      show 4 * (i : ℝ) + 4 - (g (4 * (i : ℝ) + 1 + x) - 4 * i - 1) = 8 * i + 5 - g (4 * (i : ℝ) + 1 + x) by ring] at this
    exact this

/-- The convex combination `(1 - s) u + s τ(u)` of the identity and the snapping map is compatible with
the gluings. -/
theorem s78dg_cs_snap_compat (p : ℕ) (P : ℕ → Prop) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∀ u, ((1 - s) * (u + ((4 * p : ℕ) : ℝ)) + s * s78dg_cs_tau p P (u + ((4 * p : ℕ) : ℝ))) =
      ((1 - s) * u + s * s78dg_cs_tau p P u) + ((4 * p : ℕ) : ℝ)) ∧
    (∀ (i : Fin p) (u : ℝ), 4 * (i : ℝ) ≤ u → u ≤ 4 * (i : ℝ) + 1 →
      4 * (i : ℝ) ≤ (1 - s) * u + s * s78dg_cs_tau p P u ∧
      (1 - s) * u + s * s78dg_cs_tau p P u ≤ 4 * (i : ℝ) + 1 ∧
      (1 - s) * (8 * (i : ℝ) + 3 - u) + s * s78dg_cs_tau p P (8 * (i : ℝ) + 3 - u) =
        8 * (i : ℝ) + 3 - ((1 - s) * u + s * s78dg_cs_tau p P u)) ∧
    (∀ (i : Fin p) (u : ℝ), 4 * (i : ℝ) + 1 ≤ u → u ≤ 4 * (i : ℝ) + 2 →
      4 * (i : ℝ) + 1 ≤ (1 - s) * u + s * s78dg_cs_tau p P u ∧
      (1 - s) * u + s * s78dg_cs_tau p P u ≤ 4 * (i : ℝ) + 2 ∧
      (1 - s) * (8 * (i : ℝ) + 5 - u) + s * s78dg_cs_tau p P (8 * (i : ℝ) + 5 - u) =
        8 * (i : ℝ) + 5 - ((1 - s) * u + s * s78dg_cs_tau p P u)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    rw [s78dg_cs_tau_periodic]; ring
  · intro i u h0 h1
    have hκ : s78dg_cs_kappa p ((4 * i : ℕ) : ℤ) = s78dg_cs_kappa p (((4 * i : ℕ) : ℤ) + 2) := by
      have e1 := s78dg_cs_kappa_edge p i.2 (r := 0) (by norm_num)
      have e2 := s78dg_cs_kappa_edge p i.2 (r := 2) (by norm_num)
      have : ((4 * i : ℕ) : ℤ) + 2 = ((4 * (i : ℕ) + 2 : ℕ) : ℤ) := by push_cast; ring
      rw [this, e2]
      simpa using e1
    have hc : (((4 * i : ℕ) : ℤ) : ℝ) = 4 * (i : ℝ) := by push_cast; ring
    have hu0 : (((4 * i : ℕ) : ℤ) : ℝ) ≤ u := by rw [hc]; exact h0
    have hu1 : u ≤ (((4 * i : ℕ) : ℤ) : ℝ) + 1 := by rw [hc]; exact h1
    obtain ⟨t0, t1⟩ := s78dg_cs_tau_edge p P ((4 * i : ℕ) : ℤ) hu0 hu1
    have hr := s78dg_cs_tau_reflect p P ((4 * i : ℕ) : ℤ) hκ hu0 hu1
    rw [hc] at t0 t1 hr
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    have h8 : 2 * (4 * (i : ℝ)) + 3 = 8 * (i : ℝ) + 3 := by ring
    rw [h8] at hr
    rw [hr]; ring
  · intro i u h0 h1
    have hκ : s78dg_cs_kappa p ((4 * i + 1 : ℕ) : ℤ) = s78dg_cs_kappa p (((4 * i + 1 : ℕ) : ℤ) + 2) := by
      have e1 := s78dg_cs_kappa_edge p i.2 (r := 1) (by norm_num)
      have e2 := s78dg_cs_kappa_edge p i.2 (r := 3) (by norm_num)
      have : ((4 * (i : ℕ) + 1 : ℕ) : ℤ) + 2 = ((4 * (i : ℕ) + 3 : ℕ) : ℤ) := by push_cast; ring
      rw [this, e2]
      simpa using e1
    have hc : (((4 * i + 1 : ℕ) : ℤ) : ℝ) = 4 * (i : ℝ) + 1 := by push_cast; ring
    have hu0 : (((4 * i + 1 : ℕ) : ℤ) : ℝ) ≤ u := by rw [hc]; exact h0
    have hu1 : u ≤ (((4 * i + 1 : ℕ) : ℤ) : ℝ) + 1 := by rw [hc]; linarith
    obtain ⟨t0, t1⟩ := s78dg_cs_tau_edge p P ((4 * i + 1 : ℕ) : ℤ) hu0 hu1
    have hr := s78dg_cs_tau_reflect p P ((4 * i + 1 : ℕ) : ℤ) hκ hu0 hu1
    rw [hc] at t0 t1 hr
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    have h8 : 2 * (4 * (i : ℝ) + 1) + 3 = 8 * (i : ℝ) + 5 := by ring
    rw [h8] at hr
    rw [hr]; ring

/-- The homotopy `(1 - s) · id + s · snap` on the punctured chart (radially pushed to the boundary and
snapped to the vertices on the edges not in `P`). -/
theorem s78dg_cs_snap_homotopy (p : ℕ) (hp : 1 ≤ p) (P : ℕ → Prop) :
    ∃ H : I × ↥(s78dg_cs_U p 0) → ↥(s78dg_cs_U p 0), Continuous H ∧
      ∀ (s : I) (ρ : Set.Ioc (0 : ℝ) 1) (u : ℝ), ∃ ρ' : Set.Ioc (0 : ℝ) 1,
        (ρ' : ℝ) = (1 - (s : ℝ)) * (ρ : ℝ) + (s : ℝ) ∧
          H (s, s78dg_cs_Psi_fun p hp (ρ, u)) =
            s78dg_cs_Psi_fun p hp (ρ', (1 - (s : ℝ)) * u + (s : ℝ) * s78dg_cs_tau p P u) := by
  have hρ : ∀ (s : I) (ρ : Set.Ioc (0 : ℝ) 1), 0 < (1 - (s : ℝ)) * (ρ : ℝ) + (s : ℝ) ∧
      (1 - (s : ℝ)) * (ρ : ℝ) + (s : ℝ) ≤ 1 := by
    intro s ρ
    have h1 := ρ.2.1
    have h2 := ρ.2.2
    have h3 := s.2.1
    have h4 := s.2.2
    constructor <;> nlinarith
  let ρt : I → Set.Ioc (0 : ℝ) 1 → Set.Ioc (0 : ℝ) 1 := fun s ρ =>
    ⟨(1 - (s : ℝ)) * (ρ : ℝ) + (s : ℝ), hρ s ρ⟩
  let F : I × (Set.Ioc (0 : ℝ) 1 × ℝ) → ↥(s78dg_cs_U p 0) := fun x =>
    s78dg_cs_Psi_fun p hp (ρt x.1 x.2.1, (1 - (x.1 : ℝ)) * x.2.2 + (x.1 : ℝ) * s78dg_cs_tau p P x.2.2)
  have hFc : Continuous F := by
    refine (s78dg_cs_Psi_quot p hp).continuous.comp ?_
    refine Continuous.prodMk ?_ ?_
    · refine Continuous.subtype_mk ?_ _
      exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))).add
          (continuous_subtype_val.comp continuous_fst)
    · exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_snd.comp continuous_snd)).add
          ((continuous_subtype_val.comp continuous_fst).mul
            ((s78dg_cs_tau_cont p P).comp (continuous_snd.comp continuous_snd)))
  have hres : ∀ s a b, s78dg_cs_Psi_fun p hp a = s78dg_cs_Psi_fun p hp b → F (s, a) = F (s, b) := by
    intro s a b hab
    obtain ⟨c1, c2, c3⟩ := s78dg_cs_snap_compat p P (s : ℝ) s.2.1 s.2.2
    exact s78dg_cs_param_respects p hp (ρt s) (fun ρ hρ1 => by
      change (1 - (s : ℝ)) * (ρ : ℝ) + (s : ℝ) = 1
      rw [hρ1]; ring) (fun u => (1 - (s : ℝ)) * u + (s : ℝ) * s78dg_cs_tau p P u) c1
      (fun i u h0 h1 => c2 i u h0 h1) (fun i u h0 h1 => c3 i u h0 h1) a b hab
  obtain ⟨H, hHc, hH⟩ := s78dg_cs_descent_hom _ (s78dg_cs_Psi_quot p hp) F hFc hres
  refine ⟨H, hHc, fun s ρ u => ⟨ρt s ρ, rfl, ?_⟩⟩
  exact hH s (ρ, u)

theorem s78dg_cs_Y_sub_U (p : ℕ) (hp : 1 ≤ p) (S : Set ℝ) : s78dg_cs_Y p hp S ⊆ s78dg_cs_U p 0 := by
  rintro q ⟨a, _, rfl⟩
  exact (s78dg_cs_Psi_fun p hp a).2

/-- The parameter set `S P` is stable under the period and the two kinds of gluing. -/
theorem s78dg_cs_S_sat (p : ℕ) (P : ℕ → Prop) :
    (∀ u, u + ((4 * p : ℕ) : ℝ) ∈ s78dg_cs_S p P ↔ u ∈ s78dg_cs_S p P) ∧
    (∀ (i : Fin p) (x : ℝ), 0 ≤ x → x ≤ 1 →
      (4 * (i : ℝ) + x ∈ s78dg_cs_S p P ↔ 4 * (i : ℝ) + 3 - x ∈ s78dg_cs_S p P)) ∧
    (∀ (i : Fin p) (x : ℝ), 0 ≤ x → x ≤ 1 →
      (4 * (i : ℝ) + 1 + x ∈ s78dg_cs_S p P ↔ 4 * (i : ℝ) + 4 - x ∈ s78dg_cs_S p P)) := by
  refine ⟨s78dg_cs_S_periodic p P, ?_, ?_⟩
  · intro i x h0 h1
    have hκ : s78dg_cs_kappa p ((4 * i : ℕ) : ℤ) = s78dg_cs_kappa p (((4 * i : ℕ) : ℤ) + 2) := by
      have e1 := s78dg_cs_kappa_edge p i.2 (r := 0) (by norm_num)
      have e2 := s78dg_cs_kappa_edge p i.2 (r := 2) (by norm_num)
      have : ((4 * i : ℕ) : ℤ) + 2 = ((4 * (i : ℕ) + 2 : ℕ) : ℤ) := by push_cast; ring
      rw [this, e2]
      simpa using e1
    have hc : (((4 * i : ℕ) : ℤ) : ℝ) = 4 * (i : ℝ) := by push_cast; ring
    have := s78dg_cs_S_reflect p P ((4 * i : ℕ) : ℤ) hκ (u := 4 * (i : ℝ) + x)
      (by rw [hc]; linarith) (by rw [hc]; linarith)
    rw [hc] at this
    have h8 : 2 * (4 * (i : ℝ)) + 3 - (4 * (i : ℝ) + x) = 4 * (i : ℝ) + 3 - x := by ring
    rw [h8] at this
    exact this.symm
  · intro i x h0 h1
    have hκ : s78dg_cs_kappa p ((4 * i + 1 : ℕ) : ℤ) = s78dg_cs_kappa p (((4 * i + 1 : ℕ) : ℤ) + 2) := by
      have e1 := s78dg_cs_kappa_edge p i.2 (r := 1) (by norm_num)
      have e2 := s78dg_cs_kappa_edge p i.2 (r := 3) (by norm_num)
      have : ((4 * (i : ℕ) + 1 : ℕ) : ℤ) + 2 = ((4 * (i : ℕ) + 3 : ℕ) : ℤ) := by push_cast; ring
      rw [this, e2]
      simpa using e1
    have hc : (((4 * i + 1 : ℕ) : ℤ) : ℝ) = 4 * (i : ℝ) + 1 := by push_cast; ring
    have := s78dg_cs_S_reflect p P ((4 * i + 1 : ℕ) : ℤ) hκ (u := 4 * (i : ℝ) + 1 + x)
      (by rw [hc]; linarith) (by rw [hc]; linarith)
    rw [hc] at this
    have h8 : 2 * (4 * (i : ℝ) + 1) + 3 - (4 * (i : ℝ) + 1 + x) = 4 * (i : ℝ) + 4 - x := by ring
    rw [h8] at this
    exact this.symm

/-- Points of `S ∅` are within `1/4` of a vertex and are snapped onto it. -/
theorem s78dg_cs_tau_vertex (p : ℕ) {u : ℝ} (hu : u ∈ s78dg_cs_S p (fun _ => False)) :
    ∃ j : ℤ, s78dg_cs_tau p (fun _ => False) u = j := by
  obtain ⟨j, hj⟩ := hu.resolve_right (fun h => h)
  refine ⟨j, ?_⟩
  have hP : ¬ (fun _ : ℕ => False) (s78dg_cs_kappa p ⌊u⌋) := fun h => h
  rw [abs_lt] at hj
  rcases le_or_gt (j : ℝ) u with hju | hju
  · have hfl : ⌊u⌋ = j := by rw [Int.floor_eq_iff]; constructor <;> linarith
    have hfr : Int.fract u = u - j := by rw [Int.fract, hfl]
    rw [s78dg_cs_tau_snap p _ hP, hfr, s78dg_cs_T_low (by linarith)]; ring
  · have hfl : ⌊u⌋ = j - 1 := by rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have hfr : Int.fract u = u - (j - 1) := by rw [Int.fract, hfl]; push_cast; ring
    rw [s78dg_cs_tau_snap p _ hP, hfr, s78dg_cs_T_high (by linarith)]; ring

/-- The star of the vertex in the closed surface (quarter-neighbourhood of the vertex) is contractible. -/
theorem s78dg_cs_Y0_contractible (p : ℕ) (hp : 1 ≤ p) :
    ContractibleSpace ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun _ => False))) := by
  obtain ⟨H, hHc, hH⟩ := s78dg_cs_snap_homotopy p hp (fun _ => False)
  let Y0 := s78dg_cs_Y p hp (s78dg_cs_S p (fun _ => False))
  have hYU : ∀ q ∈ Y0, q ∈ s78dg_cs_U p 0 := s78dg_cs_Y_sub_U p hp _
  have hmem : ∀ (s : I) (y : ↥Y0), ((H (s, ⟨y.1, hYU _ y.2⟩) : ↥(s78dg_cs_U p 0)) :
      Quot (OrientableRel p 0)) ∈ Y0 := by
    intro s y
    obtain ⟨a, ha, hay⟩ := y.2
    have hy : (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_cs_U p 0)) = s78dg_cs_Psi_fun p hp a := Subtype.ext hay.symm
    rw [hy]
    obtain ⟨ρ', _, hρ'⟩ := hH s a.1 a.2
    have hρ := hρ'
    rw [show (a.1, a.2) = a from rfl] at hρ
    rw [hρ]
    exact ⟨(ρ', _), s78dg_cs_S_star p _ ha s.2.1 s.2.2, rfl⟩
  let one : Set.Ioc (0 : ℝ) 1 := ⟨1, zero_lt_one, le_rfl⟩
  have h0S : (0 : ℝ) ∈ s78dg_cs_S p (fun _ => False) := Or.inl ⟨0, by simp⟩
  let v0 : ↥Y0 := ⟨((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
    ⟨(one, 0), h0S, rfl⟩⟩
  let HH : ContinuousMap.Homotopy (ContinuousMap.id ↥Y0) (ContinuousMap.const ↥Y0 v0) :=
    { toFun := fun x => ⟨(H (x.1, ⟨x.2.1, hYU _ x.2.2⟩) : Quot (OrientableRel p 0)), hmem x.1 x.2⟩
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
        have e2 : (1 - ((0 : I) : ℝ)) * a.2 + ((0 : I) : ℝ) * s78dg_cs_tau p (fun _ => False) a.2 = a.2 := by
          simp
        rw [e1, e2]
        exact hay
      map_one_left := fun y => by
        apply Subtype.ext
        obtain ⟨a, ha, hay⟩ := y.2
        have hy : (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_cs_U p 0)) = s78dg_cs_Psi_fun p hp a := Subtype.ext hay.symm
        change ((H ((1 : I), (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_cs_U p 0))) : ↥(s78dg_cs_U p 0)) :
          Quot (OrientableRel p 0)) = ((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) :
            Quot (OrientableRel p 0))
        rw [hy]
        obtain ⟨ρ', hρ', hρ⟩ := hH 1 a.1 a.2
        rw [show (a.1, a.2) = a from rfl] at hρ
        rw [hρ]
        obtain ⟨j, hj⟩ := s78dg_cs_tau_vertex p ha
        have e2 : (1 - ((1 : I) : ℝ)) * a.2 + ((1 : I) : ℝ) * s78dg_cs_tau p (fun _ => False) a.2 = j := by
          rw [hj]; simp
        rw [e2]
        have hρ1 : (ρ' : ℝ) = 1 := by rw [hρ']; simp
        have hρone : ρ' = one := Subtype.ext hρ1
        rw [hρone]
        exact congrArg Subtype.val (s78dg_cs_Psi_vertex p hp one rfl j) }
  exact (contractible_iff_id_nullhomotopic _).2 ⟨v0, ⟨HH⟩⟩

end LiZhongQC
