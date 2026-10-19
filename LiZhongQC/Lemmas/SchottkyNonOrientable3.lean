import LiZhongQC.Lemmas.SchottkyNonOrientable2
import LiZhongQC.Lemmas.SchottkyClosedSurface12

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology unitInterval

universe u

namespace LiZhongQC
/-- The open subset of the closed surface lying over the boundary parameters in `S`. -/
def s78dg_no_Y (p : ℕ) (hp : 1 ≤ p) (S : Set ℝ) : Set (Quot (NonOrientableRel p 0)) :=
  {q | ∃ a : Set.Ioc (0 : ℝ) 1 × ℝ, a.2 ∈ S ∧
    ((s78dg_no_Psi_fun p hp a : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0)) = q}

/-- Membership in `Y S` is detected on the boundary parameter, for `S` stable under the period and
the gluing. -/
theorem s78dg_no_Y_mem (p : ℕ) (hp : 1 ≤ p) (S : Set ℝ)
    (hper : ∀ u, u + ((2 * p : ℕ) : ℝ) ∈ S ↔ u ∈ S)
    (hga : ∀ (i : Fin p) (x : ℝ), 0 ≤ x → x ≤ 1 → (2 * (i : ℝ) + x ∈ S ↔ 2 * (i : ℝ) + 1 + x ∈ S))
    (a : Set.Ioc (0 : ℝ) 1 × ℝ) :
    ((s78dg_no_Psi_fun p hp a : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0)) ∈
      s78dg_no_Y p hp S ↔ a.2 ∈ S := by
  constructor
  · rintro ⟨b, hb, hab⟩
    have hab' : s78dg_no_Psi_fun p hp b = s78dg_no_Psi_fun p hp a := Subtype.ext hab
    have h1 := s78dg_no_respects p hp (s78dg_no_Psi_fun p hp) (s78dg_no_Psi_spec p hp)
      (fun q : Set.Ioc (0 : ℝ) 1 × ℝ => (q.2 ∈ S))
      (fun ρ u => by have := hper u; push_cast at this; exact propext this)
      ⟨1, zero_lt_one, le_rfl⟩ rfl
      (fun i x h0 h1 => propext (hga i x h0 h1)) b a hab'
    exact h1 ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem s78dg_no_Y_open (p : ℕ) (hp : 1 ≤ p) (S : Set ℝ) (hS : IsOpen S)
    (hper : ∀ u, u + ((2 * p : ℕ) : ℝ) ∈ S ↔ u ∈ S)
    (hga : ∀ (i : Fin p) (x : ℝ), 0 ≤ x → x ≤ 1 → (2 * (i : ℝ) + x ∈ S ↔ 2 * (i : ℝ) + 1 + x ∈ S)) :
    IsOpen (s78dg_no_Y p hp S) := by
  have hpre : (s78dg_no_Psi_fun p hp) ⁻¹' {x : ↥(s78dg_gr_U (NonOrientableRel p 0)) |
      (x : Quot (NonOrientableRel p 0)) ∈ s78dg_no_Y p hp S} = Set.univ ×ˢ S := by
    ext a
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and]
    exact s78dg_no_Y_mem p hp S hper hga a
  have hopen : IsOpen {x : ↥(s78dg_gr_U (NonOrientableRel p 0)) |
      (x : Quot (NonOrientableRel p 0)) ∈ s78dg_no_Y p hp S} := by
    rw [← (s78dg_no_Psi_quot p hp).isOpen_preimage, hpre]
    exact isOpen_univ.prod hS
  have himg : s78dg_no_Y p hp S = Subtype.val '' {x : ↥(s78dg_gr_U (NonOrientableRel p 0)) |
      (x : Quot (NonOrientableRel p 0)) ∈ s78dg_no_Y p hp S} := by
    ext q
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨s78dg_no_Psi_fun p hp a, ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  rw [himg]
  exact (s78dg_gr_U_open (s78dg_no_hb p)).isOpenMap_subtype_val _ hopen

/-- A reparametrisation of the boundary circle compatible with the edge gluing induces a well-defined map
of the punctured chart. -/
theorem s78dg_no_param_respects (p : ℕ) (hp : 1 ≤ p) (rr : Set.Ioc (0 : ℝ) 1 → Set.Ioc (0 : ℝ) 1)
    (hrr : ∀ ρ : Set.Ioc (0 : ℝ) 1, (ρ : ℝ) = 1 → (rr ρ : ℝ) = 1) (g : ℝ → ℝ)
    (hper : ∀ u, g (u + ((2 * p : ℕ) : ℝ)) = g u + ((2 * p : ℕ) : ℝ))
    (hga : ∀ (i : Fin p) (u : ℝ), 2 * (i : ℝ) ≤ u → u ≤ 2 * (i : ℝ) + 1 →
      2 * (i : ℝ) ≤ g u ∧ g u ≤ 2 * (i : ℝ) + 1 ∧ g (u + 1) = g u + 1) :
    ∀ a b : Set.Ioc (0 : ℝ) 1 × ℝ, s78dg_no_Psi_fun p hp a = s78dg_no_Psi_fun p hp b →
      s78dg_no_Psi_fun p hp (rr a.1, g a.2) = s78dg_no_Psi_fun p hp (rr b.1, g b.2) := by
  refine s78dg_no_respects p hp (s78dg_no_Psi_fun p hp) (s78dg_no_Psi_spec p hp)
    (fun q : Set.Ioc (0 : ℝ) 1 × ℝ => s78dg_no_Psi_fun p hp (rr q.1, g q.2)) ?_
    ⟨1, zero_lt_one, le_rfl⟩ rfl ?_
  · intro ρ u
    simp only
    have h := hper u
    push_cast at h
    rw [h]
    exact s78dg_no_Psi_periodic p hp (rr ρ) (g u)
  · intro i x h0 h1
    simp only
    obtain ⟨e1, e2, e3⟩ := hga i (2 * (i : ℝ) + x) (by linarith) (by linarith)
    have : g (2 * (i : ℝ) + 1 + x) = g (2 * (i : ℝ) + x) + 1 := by
      rw [← e3]; congr 1; ring
    have h1' : (rr ⟨1, zero_lt_one, le_rfl⟩ : ℝ) = 1 := hrr _ rfl
    rw [this]
    have := s78dg_no_Psi_rel_a p hp (rr ⟨1, zero_lt_one, le_rfl⟩) h1' i (g (2 * (i : ℝ) + x) - 2 * i)
      (by linarith) (by linarith)
    rw [show 2 * (i : ℝ) + (g (2 * (i : ℝ) + x) - 2 * i) = g (2 * (i : ℝ) + x) by ring,
      show 2 * (i : ℝ) + 1 + (g (2 * (i : ℝ) + x) - 2 * i) = g (2 * (i : ℝ) + x) + 1 by ring] at this
    exact this

/-- The convex combination `(1 - s) u + s τ(u)` of the identity and the snapping map is compatible with
the gluing. -/
theorem s78dg_no_snap_compat (p : ℕ) (P : ℕ → Prop) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∀ u, ((1 - s) * (u + ((2 * p : ℕ) : ℝ)) + s * s78dg_no_tau p P (u + ((2 * p : ℕ) : ℝ))) =
      ((1 - s) * u + s * s78dg_no_tau p P u) + ((2 * p : ℕ) : ℝ)) ∧
    (∀ (i : Fin p) (u : ℝ), 2 * (i : ℝ) ≤ u → u ≤ 2 * (i : ℝ) + 1 →
      2 * (i : ℝ) ≤ (1 - s) * u + s * s78dg_no_tau p P u ∧
      (1 - s) * u + s * s78dg_no_tau p P u ≤ 2 * (i : ℝ) + 1 ∧
      (1 - s) * (u + 1) + s * s78dg_no_tau p P (u + 1) =
        ((1 - s) * u + s * s78dg_no_tau p P u) + 1) := by
  refine ⟨?_, ?_⟩
  · intro u
    rw [s78dg_no_tau_periodic]; ring
  · intro i u h0 h1
    have hκ : s78dg_no_kappa p ((2 * i : ℕ) : ℤ) = s78dg_no_kappa p (((2 * i : ℕ) : ℤ) + 1) := by
      have e1 := s78dg_no_kappa_edge p i.2 (r := 0) (by norm_num)
      have e2 := s78dg_no_kappa_edge p i.2 (r := 1) (by norm_num)
      have : ((2 * i : ℕ) : ℤ) + 1 = ((2 * (i : ℕ) + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this, e2]
      simpa using e1
    have hc : (((2 * i : ℕ) : ℤ) : ℝ) = 2 * (i : ℝ) := by push_cast; ring
    have hu0 : (((2 * i : ℕ) : ℤ) : ℝ) ≤ u := by rw [hc]; exact h0
    have hu1 : u ≤ (((2 * i : ℕ) : ℤ) : ℝ) + 1 := by rw [hc]; exact h1
    obtain ⟨t0, t1⟩ := s78dg_no_tau_edge p P ((2 * i : ℕ) : ℤ) hu0 hu1
    have hr := s78dg_no_tau_translate p P ((2 * i : ℕ) : ℤ) hκ hu0 hu1
    rw [hc] at t0 t1
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    rw [hr]; ring

/-- The homotopy `(1 - s) · id + s · snap` on the punctured chart (radially pushed to the boundary and
snapped to the vertices on the edges not in `P`). -/
theorem s78dg_no_snap_homotopy (p : ℕ) (hp : 1 ≤ p) (P : ℕ → Prop) :
    ∃ H : I × ↥(s78dg_gr_U (NonOrientableRel p 0)) → ↥(s78dg_gr_U (NonOrientableRel p 0)), Continuous H ∧
      ∀ (s : I) (ρ : Set.Ioc (0 : ℝ) 1) (u : ℝ), ∃ ρ' : Set.Ioc (0 : ℝ) 1,
        (ρ' : ℝ) = (1 - (s : ℝ)) * (ρ : ℝ) + (s : ℝ) ∧
          H (s, s78dg_no_Psi_fun p hp (ρ, u)) =
            s78dg_no_Psi_fun p hp (ρ', (1 - (s : ℝ)) * u + (s : ℝ) * s78dg_no_tau p P u) := by
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
  let F : I × (Set.Ioc (0 : ℝ) 1 × ℝ) → ↥(s78dg_gr_U (NonOrientableRel p 0)) := fun x =>
    s78dg_no_Psi_fun p hp (ρt x.1 x.2.1, (1 - (x.1 : ℝ)) * x.2.2 + (x.1 : ℝ) * s78dg_no_tau p P x.2.2)
  have hFc : Continuous F := by
    refine (s78dg_no_Psi_quot p hp).continuous.comp ?_
    refine Continuous.prodMk ?_ ?_
    · refine Continuous.subtype_mk ?_ _
      exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))).add
          (continuous_subtype_val.comp continuous_fst)
    · exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_snd.comp continuous_snd)).add
          ((continuous_subtype_val.comp continuous_fst).mul
            ((s78dg_no_tau_cont p P).comp (continuous_snd.comp continuous_snd)))
  have hres : ∀ s a b, s78dg_no_Psi_fun p hp a = s78dg_no_Psi_fun p hp b → F (s, a) = F (s, b) := by
    intro s a b hab
    obtain ⟨c1, c2⟩ := s78dg_no_snap_compat p P (s : ℝ) s.2.1 s.2.2
    exact s78dg_no_param_respects p hp (ρt s) (fun ρ hρ1 => by
      change (1 - (s : ℝ)) * (ρ : ℝ) + (s : ℝ) = 1
      rw [hρ1]; ring) (fun u => (1 - (s : ℝ)) * u + (s : ℝ) * s78dg_no_tau p P u) c1
      (fun i u h0 h1 => c2 i u h0 h1) a b hab
  obtain ⟨H, hHc, hH⟩ := s78dg_cs_descent_hom _ (s78dg_no_Psi_quot p hp) F hFc hres
  refine ⟨H, hHc, fun s ρ u => ⟨ρt s ρ, rfl, ?_⟩⟩
  exact hH s (ρ, u)

theorem s78dg_no_Y_sub_U (p : ℕ) (hp : 1 ≤ p) (S : Set ℝ) : s78dg_no_Y p hp S ⊆ s78dg_gr_U (NonOrientableRel p 0) := by
  rintro q ⟨a, _, rfl⟩
  exact (s78dg_no_Psi_fun p hp a).2

/-- The parameter set `S P` is stable under the period and the gluing. -/
theorem s78dg_no_S_sat (p : ℕ) (P : ℕ → Prop) :
    (∀ u, u + ((2 * p : ℕ) : ℝ) ∈ s78dg_no_S p P ↔ u ∈ s78dg_no_S p P) ∧
    (∀ (i : Fin p) (x : ℝ), 0 ≤ x → x ≤ 1 →
      (2 * (i : ℝ) + x ∈ s78dg_no_S p P ↔ 2 * (i : ℝ) + 1 + x ∈ s78dg_no_S p P)) := by
  refine ⟨s78dg_no_S_periodic p P, ?_⟩
  intro i x h0 h1
  have hκ : s78dg_no_kappa p ((2 * i : ℕ) : ℤ) = s78dg_no_kappa p (((2 * i : ℕ) : ℤ) + 1) := by
    have e1 := s78dg_no_kappa_edge p i.2 (r := 0) (by norm_num)
    have e2 := s78dg_no_kappa_edge p i.2 (r := 1) (by norm_num)
    have : ((2 * i : ℕ) : ℤ) + 1 = ((2 * (i : ℕ) + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, e2]
    simpa using e1
  have hc : (((2 * i : ℕ) : ℤ) : ℝ) = 2 * (i : ℝ) := by push_cast; ring
  have := s78dg_no_S_translate p P ((2 * i : ℕ) : ℤ) hκ (u := 2 * (i : ℝ) + x)
    (by rw [hc]; linarith) (by rw [hc]; linarith)
  have h8 : 2 * (i : ℝ) + x + 1 = 2 * (i : ℝ) + 1 + x := by ring
  rw [h8] at this
  exact this.symm

/-- Points of `S ∅` are within `1/4` of a vertex and are snapped onto it. -/
theorem s78dg_no_tau_vertex (p : ℕ) {u : ℝ} (hu : u ∈ s78dg_no_S p (fun _ => False)) :
    ∃ j : ℤ, s78dg_no_tau p (fun _ => False) u = j := by
  obtain ⟨j, hj⟩ := hu.resolve_right (fun h => h)
  refine ⟨j, ?_⟩
  have hP : ¬ (fun _ : ℕ => False) (s78dg_no_kappa p ⌊u⌋) := fun h => h
  rw [abs_lt] at hj
  rcases le_or_gt (j : ℝ) u with hju | hju
  · have hfl : ⌊u⌋ = j := by rw [Int.floor_eq_iff]; constructor <;> linarith
    have hfr : Int.fract u = u - j := by rw [Int.fract, hfl]
    rw [s78dg_no_tau_snap p _ hP, hfr, s78dg_cs_T_low (by linarith)]; ring
  · have hfl : ⌊u⌋ = j - 1 := by rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have hfr : Int.fract u = u - (j - 1) := by rw [Int.fract, hfl]; push_cast; ring
    rw [s78dg_no_tau_snap p _ hP, hfr, s78dg_cs_T_high (by linarith)]; ring

/-- The star of the vertex in the closed surface (quarter-neighbourhood of the vertex) is contractible. -/
theorem s78dg_no_Y0_contractible (p : ℕ) (hp : 1 ≤ p) :
    ContractibleSpace ↥(s78dg_no_Y p hp (s78dg_no_S p (fun _ => False))) := by
  obtain ⟨H, hHc, hH⟩ := s78dg_no_snap_homotopy p hp (fun _ => False)
  let Y0 := s78dg_no_Y p hp (s78dg_no_S p (fun _ => False))
  have hYU : ∀ q ∈ Y0, q ∈ s78dg_gr_U (NonOrientableRel p 0) := s78dg_no_Y_sub_U p hp _
  have hmem : ∀ (s : I) (y : ↥Y0), ((H (s, ⟨y.1, hYU _ y.2⟩) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
      Quot (NonOrientableRel p 0)) ∈ Y0 := by
    intro s y
    obtain ⟨a, ha, hay⟩ := y.2
    have hy : (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_gr_U (NonOrientableRel p 0))) = s78dg_no_Psi_fun p hp a := Subtype.ext hay.symm
    rw [hy]
    obtain ⟨ρ', _, hρ'⟩ := hH s a.1 a.2
    have hρ := hρ'
    rw [show (a.1, a.2) = a from rfl] at hρ
    rw [hρ]
    exact ⟨(ρ', _), s78dg_no_S_star p _ ha s.2.1 s.2.2, rfl⟩
  let one : Set.Ioc (0 : ℝ) 1 := ⟨1, zero_lt_one, le_rfl⟩
  have h0S : (0 : ℝ) ∈ s78dg_no_S p (fun _ => False) := Or.inl ⟨0, by simp⟩
  let v0 : ↥Y0 := ⟨((s78dg_no_Psi_fun p hp (one, 0) : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0)),
    ⟨(one, 0), h0S, rfl⟩⟩
  let HH : ContinuousMap.Homotopy (ContinuousMap.id ↥Y0) (ContinuousMap.const ↥Y0 v0) :=
    { toFun := fun x => ⟨(H (x.1, ⟨x.2.1, hYU _ x.2.2⟩) : Quot (NonOrientableRel p 0)), hmem x.1 x.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        refine continuous_subtype_val.comp (hHc.comp (continuous_fst.prodMk ?_))
        exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_snd) _
      map_zero_left := fun y => by
        apply Subtype.ext
        obtain ⟨a, ha, hay⟩ := y.2
        have hy : (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_gr_U (NonOrientableRel p 0))) = s78dg_no_Psi_fun p hp a := Subtype.ext hay.symm
        change ((H ((0 : I), (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_gr_U (NonOrientableRel p 0)))) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
          Quot (NonOrientableRel p 0)) = y.1
        rw [hy]
        obtain ⟨ρ', hρ', hρ⟩ := hH 0 a.1 a.2
        rw [show (a.1, a.2) = a from rfl] at hρ
        rw [hρ]
        have e1 : ρ' = a.1 := Subtype.ext (by rw [hρ']; simp)
        have e2 : (1 - ((0 : I) : ℝ)) * a.2 + ((0 : I) : ℝ) * s78dg_no_tau p (fun _ => False) a.2 = a.2 := by
          simp
        rw [e1, e2]
        exact hay
      map_one_left := fun y => by
        apply Subtype.ext
        obtain ⟨a, ha, hay⟩ := y.2
        have hy : (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_gr_U (NonOrientableRel p 0))) = s78dg_no_Psi_fun p hp a := Subtype.ext hay.symm
        change ((H ((1 : I), (⟨y.1, hYU _ y.2⟩ : ↥(s78dg_gr_U (NonOrientableRel p 0)))) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
          Quot (NonOrientableRel p 0)) = ((s78dg_no_Psi_fun p hp (one, 0) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
            Quot (NonOrientableRel p 0))
        rw [hy]
        obtain ⟨ρ', hρ', hρ⟩ := hH 1 a.1 a.2
        rw [show (a.1, a.2) = a from rfl] at hρ
        rw [hρ]
        obtain ⟨j, hj⟩ := s78dg_no_tau_vertex p ha
        have e2 : (1 - ((1 : I) : ℝ)) * a.2 + ((1 : I) : ℝ) * s78dg_no_tau p (fun _ => False) a.2 = j := by
          rw [hj]; simp
        rw [e2]
        have hρ1 : (ρ' : ℝ) = 1 := by rw [hρ']; simp
        have hρone : ρ' = one := Subtype.ext hρ1
        rw [hρone]
        exact congrArg Subtype.val (s78dg_no_Psi_vertex p hp one rfl j) }
  exact (contractible_iff_id_nullhomotopic _).2 ⟨v0, ⟨HH⟩⟩


end LiZhongQC
