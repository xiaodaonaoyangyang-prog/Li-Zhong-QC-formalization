import LiZhongQC.Lemmas.SchottkyNonOrientable5
import LiZhongQC.Lemmas.SchottkyClosedSurface12

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology unitInterval

universe u

namespace LiZhongQC

theorem s78dg_no_edge_gen (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (e : FundamentalGroup ↥(s78dg_gr_U (NonOrientableRel p 0)) (s78dg_no_Psi_fun p hp (one, 0)) ≃* FreeGroup (Fin p))
    (he : ∀ (j : ℕ) (hj : j < p) (L : Path (s78dg_no_Psi_fun p hp (one, 0))
          (s78dg_no_Psi_fun p hp (one, 0))),
        (∀ t, (((L t : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0))) =
          ((s78dg_no_Psi_fun p hp (one, 2 * (j : ℝ) + Int.fract (t : ℝ)) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
            Quot (NonOrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩)
    (j : ℕ) (hj : j < p) (L : Path (s78dg_no_Psi_fun p hp (one, 0)) (s78dg_no_Psi_fun p hp (one, 0)))
    (hL : ∀ t : I, L t = s78dg_no_Psi_fun p hp (one, 2 * (j : ℝ) + (t : ℝ))) :
    e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩ := by
  refine he j hj L (fun t => ?_)
  by_cases ht : (t : ℝ) < 1
  · rw [hL t, Int.fract_eq_self.2 ⟨t.2.1, ht⟩]
  · have h1 : (t : ℝ) = 1 := le_antisymm t.2.2 (not_lt.1 ht)
    rw [hL t, h1, Int.fract_one]
    have hv := s78dg_no_Psi_vertex p hp one hone ((2 * j : ℕ) : ℤ)
    have hv' := s78dg_no_Psi_vertex p hp one hone (((2 * j : ℕ) : ℤ) + 1)
    push_cast at hv hv'
    rw [add_zero]
    exact congrArg Subtype.val (hv'.trans hv.symm)

theorem s78dg_no_edge0 (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (e : FundamentalGroup ↥(s78dg_gr_U (NonOrientableRel p 0)) (s78dg_no_Psi_fun p hp (one, 0)) ≃* FreeGroup (Fin p))
    (he : ∀ (j : ℕ) (hj : j < p) (L : Path (s78dg_no_Psi_fun p hp (one, 0))
          (s78dg_no_Psi_fun p hp (one, 0))),
        (∀ t, (((L t : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0))) =
          ((s78dg_no_Psi_fun p hp (one, 2 * (j : ℝ) + Int.fract (t : ℝ)) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
            Quot (NonOrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩)
    (n : ℕ) (hn : n < p) (ε : Path (s78dg_no_Psi_fun p hp (one, 0)) (s78dg_no_Psi_fun p hp (one, 0)))
    (hε : ∀ t : I, ε t = s78dg_no_Psi_fun p hp (one, 2 * (n : ℝ) + (t : ℝ))) :
    e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ε)) = FreeGroup.of ⟨n, hn⟩ :=
  s78dg_no_edge_gen p hp one hone e he n hn ε hε

theorem s78dg_no_edge1 (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (e : FundamentalGroup ↥(s78dg_gr_U (NonOrientableRel p 0)) (s78dg_no_Psi_fun p hp (one, 0)) ≃* FreeGroup (Fin p))
    (he : ∀ (j : ℕ) (hj : j < p) (L : Path (s78dg_no_Psi_fun p hp (one, 0))
          (s78dg_no_Psi_fun p hp (one, 0))),
        (∀ t, (((L t : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0))) =
          ((s78dg_no_Psi_fun p hp (one, 2 * (j : ℝ) + Int.fract (t : ℝ)) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
            Quot (NonOrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩)
    (n : ℕ) (hn : n < p) (ε : Path (s78dg_no_Psi_fun p hp (one, 0)) (s78dg_no_Psi_fun p hp (one, 0)))
    (hε : ∀ t : I, ε t = s78dg_no_Psi_fun p hp (one, 2 * (n : ℝ) + 1 + (t : ℝ))) :
    e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ε)) = FreeGroup.of ⟨n, hn⟩ :=
  s78dg_no_edge_gen p hp one hone e he n hn ε (fun t => by
    rw [hε t]
    exact (s78dg_no_Psi_rel_a p hp one hone ⟨n, hn⟩ (t : ℝ) t.2.1 t.2.2).symm)

theorem s78dg_no_vertex_all (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1) :
    ∀ x : ℝ, (∃ n : ℤ, x = n) → (fun u : ℝ => s78dg_no_Psi_fun p hp (one, u)) x =
      s78dg_no_Psi_fun p hp (one, 0) := by
  rintro x ⟨n, rfl⟩
  exact s78dg_no_Psi_vertex p hp one hone n

theorem s78dg_no_Psi_cont (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) :
    Continuous (fun u : ℝ => s78dg_no_Psi_fun p hp (one, u)) :=
  (s78dg_no_Psi_quot p hp).continuous.comp (continuous_const.prodMk continuous_id)

/-- **One crosscap of the boundary.**  Going once around a block of two edges multiplies the class by `aᵢ²`. -/
theorem s78dg_no_block (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (e : FundamentalGroup ↥(s78dg_gr_U (NonOrientableRel p 0)) (s78dg_no_Psi_fun p hp (one, 0)) ≃* FreeGroup (Fin p))
    (he : ∀ (j : ℕ) (hj : j < p) (L : Path (s78dg_no_Psi_fun p hp (one, 0))
          (s78dg_no_Psi_fun p hp (one, 0))),
        (∀ t, (((L t : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0))) =
          ((s78dg_no_Psi_fun p hp (one, 2 * (j : ℝ) + Int.fract (t : ℝ)) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
            Quot (NonOrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩)
    (n : ℕ) (hn : n < p)
    (β : Path (s78dg_no_Psi_fun p hp (one, 0)) (s78dg_no_Psi_fun p hp (one, 0)))
    (hβ : ∀ t : I, β t = s78dg_no_Psi_fun p hp (one, ((2 * n : ℕ) : ℝ) * (t : ℝ))) :
    ∃ β' : Path (s78dg_no_Psi_fun p hp (one, 0)) (s78dg_no_Psi_fun p hp (one, 0)),
      (∀ t : I, β' t = s78dg_no_Psi_fun p hp (one, ((2 * (n + 1) : ℕ) : ℝ) * (t : ℝ))) ∧
      (e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β')))⁻¹ =
        (e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β)))⁻¹ *
          ((FreeGroup.of ⟨n, hn⟩)⁻¹ * (FreeGroup.of ⟨n, hn⟩)⁻¹) := by
  have hf := s78dg_no_Psi_cont p hp one
  have hv := s78dg_no_vertex_all p hp one hone
  obtain ⟨ε0, hε0⟩ := s78dg_exists_edge_loop _ hf hv (2 * n)
  obtain ⟨ε1, hε1⟩ := s78dg_exists_edge_loop _ hf hv (2 * n + 1)
  obtain ⟨β1, hβ1, hc0⟩ := s78dg_loop_step _ hf hv (2 * n) β ε0 hβ hε0
  obtain ⟨β2, hβ2, hc1⟩ := s78dg_loop_step _ hf hv (2 * n + 1) β1 ε1 hβ1 hε1
  refine ⟨β2, fun t => ?_, ?_⟩
  · rw [hβ2 t]
    congr 2
  · have c0 := s78dg_no_edge0 p hp one hone e he n hn ε0 (fun t => by
      rw [hε0 t]; congr 2; push_cast; ring)
    have c1 := s78dg_no_edge1 p hp one hone e he n hn ε1 (fun t => by
      rw [hε1 t]; congr 2; push_cast; ring)
    rw [hc1, map_mul, hc0, map_mul, c0, c1]
    group

theorem s78dg_no_boundary_induction (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (e : FundamentalGroup ↥(s78dg_gr_U (NonOrientableRel p 0)) (s78dg_no_Psi_fun p hp (one, 0)) ≃* FreeGroup (Fin p))
    (he : ∀ (j : ℕ) (hj : j < p) (L : Path (s78dg_no_Psi_fun p hp (one, 0))
          (s78dg_no_Psi_fun p hp (one, 0))),
        (∀ t, (((L t : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0))) =
          ((s78dg_no_Psi_fun p hp (one, 2 * (j : ℝ) + Int.fract (t : ℝ)) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
            Quot (NonOrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩)
    (n : ℕ) (hn : n ≤ p) :
    ∃ β : Path (s78dg_no_Psi_fun p hp (one, 0)) (s78dg_no_Psi_fun p hp (one, 0)),
      (∀ t : I, β t = s78dg_no_Psi_fun p hp (one, ((2 * n : ℕ) : ℝ) * (t : ℝ))) ∧
      (e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β)))⁻¹ =
        (List.ofFn fun i : Fin n =>
          ((FreeGroup.of ⟨(i : ℕ), by omega⟩ : FreeGroup (Fin p))⁻¹ *
            (FreeGroup.of ⟨(i : ℕ), by omega⟩)⁻¹)).prod := by
  induction n with
  | zero =>
    refine ⟨Path.refl _, fun t => ?_, ?_⟩
    · show _ = _
      simp only [Path.refl_apply, Nat.mul_zero, Nat.cast_zero, zero_mul]
    · have : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (Path.refl (s78dg_no_Psi_fun p hp (one, 0)))) = 1 := rfl
      rw [this, map_one]
      simp
  | succ n ih =>
    obtain ⟨β, hβ, hc⟩ := ih (by omega)
    obtain ⟨β', hβ', hc'⟩ := s78dg_no_block p hp one hone e he n (by omega) β hβ
    refine ⟨β', hβ', ?_⟩
    rw [hc', hc, List.ofFn_succ', List.prod_concat]
    simp

/-- **The boundary word.** -/
theorem s78dg_no_boundary_word (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (e : FundamentalGroup ↥(s78dg_gr_U (NonOrientableRel p 0)) (s78dg_no_Psi_fun p hp (one, 0)) ≃* FreeGroup (Fin p))
    (he : ∀ (j : ℕ) (hj : j < p) (L : Path (s78dg_no_Psi_fun p hp (one, 0))
          (s78dg_no_Psi_fun p hp (one, 0))),
        (∀ t, (((L t : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0))) =
          ((s78dg_no_Psi_fun p hp (one, 2 * (j : ℝ) + Int.fract (t : ℝ)) : ↥(s78dg_gr_U (NonOrientableRel p 0))) :
            Quot (NonOrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩)
    :
    ∃ β : Path (s78dg_no_Psi_fun p hp (one, 0)) (s78dg_no_Psi_fun p hp (one, 0)),
      (∀ t : I, β t = s78dg_no_Psi_fun p hp (one, 2 * (p : ℝ) * (t : ℝ))) ∧
      (e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β)))⁻¹ =
        (List.ofFn fun i : Fin p =>
          ((FreeGroup.of ⟨(i : ℕ), by omega⟩ : FreeGroup (Fin p))⁻¹ *
            (FreeGroup.of ⟨(i : ℕ), by omega⟩)⁻¹)).prod := by
  obtain ⟨β, hβ, hc⟩ := s78dg_no_boundary_induction p hp one hone e he p le_rfl
  refine ⟨β, fun t => ?_, hc⟩
  rw [hβ t]
  congr 2
  push_cast; ring


/-- **The circle of radius `1/2` is conjugate to the boundary loop.**  Changing the base point along the
radial path turns the loop `t ↦ Ψ(1/2, 4p t)` into the boundary loop. -/
theorem s78dg_no_circle_conj (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (half : Set.Ioc (0 : ℝ) 1) (hhalf : (half : ℝ) = 1 / 2)
    (x₁ : ↥(s78dg_gr_U (NonOrientableRel p 0))) (c : Path x₁ x₁)
    (hc : ∀ t : I, c t = s78dg_no_Psi_fun p hp (half, 2 * (p : ℝ) * (t : ℝ)))
    (β : Path (s78dg_no_Psi_fun p hp (one, 0)) (s78dg_no_Psi_fun p hp (one, 0)))
    (hβ : ∀ t : I, β t = s78dg_no_Psi_fun p hp (one, 2 * (p : ℝ) * (t : ℝ))) :
    ∃ r : Path x₁ (s78dg_no_Psi_fun p hp (one, 0)),
      FundamentalGroup.fundamentalGroupMulEquivOfPath r
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β) := by
  let ρ : I → Set.Ioc (0 : ℝ) 1 := fun s =>
    ⟨1 / 2 + (s : ℝ) / 2, by have := s.2.1; positivity, by have := s.2.2; linarith⟩
  have hρc : Continuous ρ :=
    Continuous.subtype_mk (continuous_const.add (continuous_subtype_val.div_const 2)) _
  have hρ0 : ρ 0 = half := Subtype.ext (by simp [ρ, hhalf])
  have hρ1 : ρ 1 = one := Subtype.ext (by simp [ρ, hone]; norm_num)
  let F : C(I × I, ↥(s78dg_gr_U (NonOrientableRel p 0))) :=
    ⟨fun q => s78dg_no_Psi_fun p hp (ρ q.1, 2 * (p : ℝ) * (q.2 : ℝ)),
      (s78dg_no_Psi_quot p hp).continuous.comp
        ((hρc.comp continuous_fst).prodMk
          (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))⟩
  have hx₁ : x₁ = s78dg_no_Psi_fun p hp (half, 0) := by
    have := hc 0
    rw [c.source] at this
    rw [this]; simp
  let r : Path x₁ (s78dg_no_Psi_fun p hp (one, 0)) :=
    { toFun := fun s => s78dg_no_Psi_fun p hp (ρ s, 0)
      continuous_toFun := (s78dg_no_Psi_quot p hp).continuous.comp (hρc.prodMk continuous_const)
      source' := by
        show s78dg_no_Psi_fun p hp (ρ 0, 0) = x₁
        rw [hρ0, hx₁]
      target' := by
        show s78dg_no_Psi_fun p hp (ρ 1, 0) = _
        rw [hρ1] }
  refine ⟨r, s78dg_pi1_conj r c β ?_⟩
  refine s78dg_square F r β c r (fun s => ?_) (fun t => ?_) (fun t => ?_) (fun s => ?_)
  · show _ = s78dg_no_Psi_fun p hp (ρ s, 2 * (p : ℝ) * ((0 : I) : ℝ))
    simp
    rfl
  · rw [hβ t]
    show _ = s78dg_no_Psi_fun p hp (ρ 1, 2 * (p : ℝ) * (t : ℝ))
    rw [hρ1]
  · rw [hc t]
    show _ = s78dg_no_Psi_fun p hp (ρ 0, 2 * (p : ℝ) * (t : ℝ))
    rw [hρ0]
  · show s78dg_no_Psi_fun p hp (ρ s, 0) = s78dg_no_Psi_fun p hp (ρ s, 2 * (p : ℝ) * ((1 : I) : ℝ))
    have := s78dg_no_Psi_periodic p hp (ρ s) 0
    simp only [zero_add] at this
    rw [← this]
    simp


theorem s78dg_no_norm_param (ρ r : ℝ) (h : 0 < ρ) :
    ‖(ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = ρ := by
  rw [norm_mul, show (2 * Real.pi * Complex.I * (r : ℂ)) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos h, mul_one]

theorem s78dg_no_overlap_char (p : ℕ) (hp : 1 ≤ p) (q : Quot (NonOrientableRel p 0)) :
    q ∈ s78dg_gr_U (NonOrientableRel p 0) ∩ s78dg_gr_V (NonOrientableRel p 0) ↔
      ∃ a : Set.Ioc (0 : ℝ) 1 × ℝ, (a.1 : ℝ) < 1 ∧
        ((s78dg_no_Psi_fun p hp a : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0)) = q := by
  constructor
  · rintro ⟨hqU, ⟨y, hy, hyq⟩⟩
    obtain ⟨a, ha⟩ := (s78dg_no_Psi_quot p hp).surjective (⟨q, hqU⟩ : ↥(s78dg_gr_U (NonOrientableRel p 0)))
    refine ⟨a, ?_, congrArg Subtype.val ha⟩
    obtain ⟨z, hz, hz'⟩ := s78dg_no_Psi_spec p hp a.1 a.2
    have hq : Quot.mk (NonOrientableRel p 0) z = Quot.mk (NonOrientableRel p 0) y :=
      hz'.symm.trans ((congrArg Subtype.val ha).trans hyq.symm)
    rcases s78dg_gr_eqv_boundary (s78dg_no_hb p) (Quot.eqvGen_exact hq) with h | h
    · have hy' : ‖(y : ℂ)‖ < 1 := hy
      rw [← h] at hy'
      rw [hz, s78dg_no_norm_param _ _ a.1.2.1] at hy'
      exact hy'
    · have hy' : ‖(y : ℂ)‖ < 1 := hy
      exact absurd h.2 hy'.ne
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(s78dg_no_Psi_fun p hp a).2, ?_⟩
    obtain ⟨z, hz, hz'⟩ := s78dg_no_Psi_spec p hp a.1 a.2
    refine ⟨z, ?_, hz'.symm⟩
    show ‖(z : ℂ)‖ < 1
    rw [hz, s78dg_no_norm_param _ _ a.1.2.1]
    exact ha

theorem s78dg_no_overlap_pathConnected (p : ℕ) (hp : 1 ≤ p) :
    PathConnectedSpace ↥(s78dg_gr_U (NonOrientableRel p 0) ∩ s78dg_gr_V (NonOrientableRel p 0)) := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  let W := s78dg_gr_U (NonOrientableRel p 0) ∩ s78dg_gr_V (NonOrientableRel p 0)
  let half : Set.Ioc (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  let cl : ℝ → ℝ := fun s => max 0 (min 1 s)
  have hcl : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
  have hcl0 : ∀ s, 0 ≤ cl s := fun s => le_max_left _ _
  have hcl1 : ∀ s, cl s ≤ 1 := fun s => max_le zero_le_one (min_le_left _ _)
  have hcl_0 : cl 0 = 0 := by simp [cl]
  have hcl_1 : cl 1 = 1 := by simp [cl]
  have hmem : ∀ (ρ : Set.Ioc (0 : ℝ) 1) (u : ℝ), (ρ : ℝ) < 1 →
      ((s78dg_no_Psi_fun p hp (ρ, u) : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0)) ∈ W :=
    fun ρ u h => (s78dg_no_overlap_char p hp _).2 ⟨(ρ, u), h, rfl⟩
  refine ⟨((s78dg_no_Psi_fun p hp (half, 0) : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0)),
    hmem half 0 (by show (1 : ℝ) / 2 < 1; norm_num), ?_⟩
  intro q hq
  obtain ⟨⟨ρ, u⟩, hρ, rfl⟩ := (s78dg_no_overlap_char p hp q).1 hq
  have hρ0 := ρ.2.1
  -- radial segment at height `u` from `ρ` to `1/2`
  let r : ℝ → Set.Ioc (0 : ℝ) 1 := fun s =>
    ⟨(ρ : ℝ) + cl s * (1 / 2 - ρ), by
      have : (0 : ℝ) < (1 - cl s) * ρ + cl s * (1 / 2) := by
        have := hcl0 s; have := hcl1 s
        rcases eq_or_lt_of_le (hcl1 s) with h | h
        · rw [h]; norm_num
        · have : 0 < 1 - cl s := by linarith
          positivity
      nlinarith, by
      have h1 := hcl0 s
      have h2 := hcl1 s
      nlinarith⟩
  have hrc : Continuous r :=
    Continuous.subtype_mk (continuous_const.add (hcl.mul continuous_const)) _
  have hrad : JoinedIn W
      ((s78dg_no_Psi_fun p hp (half, u) : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0))
      ((s78dg_no_Psi_fun p hp (ρ, u) : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0)) := by
    refine JoinedIn.ofLine (f := fun s => ((s78dg_no_Psi_fun p hp (r (1 - s), u) :
      ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0))) ?_ ?_ ?_ ?_
    · exact (continuous_subtype_val.comp ((s78dg_no_Psi_quot p hp).continuous.comp
        ((hrc.comp (continuous_const.sub continuous_id)).prodMk continuous_const))).continuousOn
    · have : r (1 - 0) = half := Subtype.ext (by simp [r, hcl_1, half])
      rw [this]
    · have : r (1 - 1) = ρ := Subtype.ext (by simp [r, hcl_0])
      rw [this]
    · rintro _ ⟨s, _, rfl⟩
      refine hmem _ _ ?_
      have h1 := hcl0 (1 - s)
      have h2 := hcl1 (1 - s)
      show (ρ : ℝ) + cl (1 - s) * (1 / 2 - ρ) < 1
      nlinarith
  -- rotate
  have hrot : JoinedIn W
      ((s78dg_no_Psi_fun p hp (half, 0) : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0))
      ((s78dg_no_Psi_fun p hp (half, u) : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0)) := by
    refine JoinedIn.ofLine (f := fun s => ((s78dg_no_Psi_fun p hp (half, cl s * u) :
      ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0))) ?_ ?_ ?_ ?_
    · exact (continuous_subtype_val.comp ((s78dg_no_Psi_quot p hp).continuous.comp
        (continuous_const.prodMk (hcl.mul continuous_const)))).continuousOn
    · simp [hcl_0]
    · simp [hcl_1]
    · rintro _ ⟨s, _, rfl⟩
      exact hmem _ _ (by show (1 : ℝ) / 2 < 1; norm_num)
  exact hrot.trans hrad

theorem s78dg_no_U_pathConnected (p : ℕ) (hp : 1 ≤ p) : PathConnectedSpace ↥(s78dg_gr_U (NonOrientableRel p 0)) := by
  haveI := s78dg_no_Y_pathConnected p hp (fun m => m < p)
  exact (Homeomorph.setCongr (s78dg_no_Y_full p hp)).pathConnectedSpace

/-- Inversion of all generators is an automorphism of the free group. -/
theorem s78dg_free_inv_equiv (α : Type) :
    ∃ ι : FreeGroup α ≃* FreeGroup α, ∀ i, ι (FreeGroup.of i) = (FreeGroup.of i)⁻¹ := by
  let f : FreeGroup α →* FreeGroup α := FreeGroup.lift (fun i => (FreeGroup.of i)⁻¹)
  have hff : f.comp f = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro i
    simp [f]
  refine ⟨MonoidHom.toMulEquiv f f hff hff, fun i => ?_⟩
  simp [f]

/-- **π₁ of the closed nonorientable surface with `p` crosscaps, at one base point.** -/
theorem s78dg_no_pi1_base (p : ℕ) (hp : 1 ≤ p) :
    ∃ x : Quot (NonOrientableRel p 0), Nonempty (FundamentalGroup (Quot (NonOrientableRel p 0)) x ≃*
      PresentedGroup ({(List.ofFn fun i : Fin p => FreeGroup.of i ^ 2).prod} : Set (FreeGroup (Fin p)))) := by
  let one : Set.Ioc (0 : ℝ) 1 := ⟨1, zero_lt_one, le_rfl⟩
  have hone : (one : ℝ) = 1 := rfl
  let half : Set.Ioc (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  have hhalf : (half : ℝ) = 1 / 2 := rfl
  obtain ⟨e, he⟩ := s78dg_no_pi1_free p hp one hone
  obtain ⟨β, hβ, hW⟩ := s78dg_no_boundary_word p hp one hone e he
  obtain ⟨b, γ, hγv, hγgen⟩ := s78dg_gr_overlap_generator (s78dg_no_hb p)
  obtain ⟨ι, hι⟩ := s78dg_free_inv_equiv (Fin p)
  obtain ⟨T, hT⟩ := s78dg_free_presented_empty (Fin p)
  haveI : PathConnectedSpace ↥(s78dg_gr_U (NonOrientableRel p 0)) := s78dg_no_U_pathConnected p hp
  haveI := s78dg_gr_V_contractible (s78dg_no_hb p)
  haveI := s78dg_no_overlap_pathConnected p hp
  refine ⟨(b : Quot (NonOrientableRel p 0)), ?_⟩
  have hx₀ : (b : Quot (NonOrientableRel p 0)) ∈
      s78dg_gr_U (NonOrientableRel p 0) ∩ s78dg_gr_V (NonOrientableRel p 0) := b.2
  let x₁ : ↥(s78dg_gr_U (NonOrientableRel p 0)) := ⟨(b : Quot (NonOrientableRel p 0)), hx₀.1⟩
  let c : Path x₁ x₁ :=
    { toFun := fun t => ⟨((γ t : ↥(s78dg_gr_U (NonOrientableRel p 0) ∩ s78dg_gr_V (NonOrientableRel p 0))) :
        Quot (NonOrientableRel p 0)), (γ t).2.1⟩
      continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp γ.continuous) _
      source' := Subtype.ext (congrArg (fun x : ↥(s78dg_gr_U (NonOrientableRel p 0) ∩
        s78dg_gr_V (NonOrientableRel p 0)) => (x : Quot (NonOrientableRel p 0))) γ.source)
      target' := Subtype.ext (congrArg (fun x : ↥(s78dg_gr_U (NonOrientableRel p 0) ∩
        s78dg_gr_V (NonOrientableRel p 0)) => (x : Quot (NonOrientableRel p 0))) γ.target) }
  have hc : ∀ t : I, c t = s78dg_no_Psi_fun p hp (half, 2 * (p : ℝ) * (t : ℝ)) := by
    intro t
    obtain ⟨x, hx, hxq⟩ := hγv t
    obtain ⟨z, hz, hz'⟩ := s78dg_no_Psi_spec p hp half (2 * (p : ℝ) * (t : ℝ))
    have hN : (2 * (p : ℝ)) ≠ 0 := by positivity
    have hzx : z = x := by
      apply Subtype.ext
      rw [hz, hx, Complex.real_smul, Circle.coe_exp]
      have h1 : (2 * (p : ℝ) * (t : ℝ)) / (2 * p) = t := by field_simp
      rw [h1]
      congr 1
      congr 1
      push_cast; ring
    apply Subtype.ext
    rw [hz']
    show ((γ t : ↥(s78dg_gr_U (NonOrientableRel p 0) ∩ s78dg_gr_V (NonOrientableRel p 0))) :
      Quot (NonOrientableRel p 0)) = _
    rw [hxq, hzx]
  obtain ⟨r, hr⟩ := s78dg_no_circle_conj p hp one hone half hhalf x₁ c hc β hβ
  let E : FundamentalGroup ↥(s78dg_gr_U (NonOrientableRel p 0)) x₁ ≃* FreeGroup (Fin p) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPath r).trans (e.trans ι)
  let eU : DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactor
      (s78dg_gr_U (NonOrientableRel p 0)) (s78dg_gr_V (NonOrientableRel p 0))
      (b : Quot (NonOrientableRel p 0)) hx₀ false ≃* PresentedGroup (∅ : Set (FreeGroup (Fin p))) :=
    E.trans T
  let γ' : FundamentalGroup ↑(s78dg_gr_U (NonOrientableRel p 0) ∩ s78dg_gr_V (NonOrientableRel p 0))
      (DifferentialGeometry.Topology.VanKampen.overlapBasepoint (s78dg_gr_U (NonOrientableRel p 0))
        (s78dg_gr_V (NonOrientableRel p 0)) (b : Quot (NonOrientableRel p 0)) hx₀) :=
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))⁻¹
  have hγ' : ∀ z, z ∈ Subgroup.zpowers γ' := fun z => by
    have := hγgen z
    rwa [← Subgroup.zpowers_inv] at this
  let w : FreeGroup (Fin p) := (List.ofFn fun i : Fin p => FreeGroup.of i ^ 2).prod
  have hιw : ι ((List.ofFn fun i : Fin p =>
      ((FreeGroup.of ⟨(i : ℕ), by omega⟩ : FreeGroup (Fin p))⁻¹ *
        (FreeGroup.of ⟨(i : ℕ), by omega⟩)⁻¹)).prod) = w := by
    simp only [w, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp [hι, pow_two]
  have hw : PresentedGroup.mk (∅ : Set (FreeGroup (Fin p))) w =
      eU (DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamation
        (s78dg_gr_U (NonOrientableRel p 0)) (s78dg_gr_V (NonOrientableRel p 0))
        (b : Quot (NonOrientableRel p 0)) hx₀ false γ') := by
    have h2 : FundamentalGroup.mapOfEq (DifferentialGeometry.Topology.VanKampen.interToLeft
        (s78dg_gr_U (NonOrientableRel p 0)) (s78dg_gr_V (NonOrientableRel p 0)))
        (DifferentialGeometry.Topology.VanKampen.interToLeft_overlapBasepoint
          (s78dg_gr_U (NonOrientableRel p 0)) (s78dg_gr_V (NonOrientableRel p 0))
          (b : Quot (NonOrientableRel p 0)) hx₀) (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c) :=
      s78dg_pi1_mapOfEq_mk (DifferentialGeometry.Topology.VanKampen.interToLeft _ _) _ _
        (DifferentialGeometry.Topology.VanKampen.interToLeft_overlapBasepoint _ _ _ hx₀) γ c
        (fun t => rfl)
    have h1 : DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamation
        (s78dg_gr_U (NonOrientableRel p 0)) (s78dg_gr_V (NonOrientableRel p 0))
        (b : Quot (NonOrientableRel p 0)) hx₀ false γ' =
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c))⁻¹ :=
      (map_inv (FundamentalGroup.mapOfEq (DifferentialGeometry.Topology.VanKampen.interToLeft
        (s78dg_gr_U (NonOrientableRel p 0)) (s78dg_gr_V (NonOrientableRel p 0)))
        (DifferentialGeometry.Topology.VanKampen.interToLeft_overlapBasepoint
          (s78dg_gr_U (NonOrientableRel p 0)) (s78dg_gr_V (NonOrientableRel p 0))
          (b : Quot (NonOrientableRel p 0)) hx₀)) _).trans (congrArg _ h2)
    rw [h1]
    have h3 : eU (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c))⁻¹ =
        T (ι ((e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β)))⁻¹)) := by
      show T (E _) = _
      rw [map_inv]
      show T ((ι (e (FundamentalGroup.fundamentalGroupMulEquivOfPath r
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c)))))⁻¹) = _
      rw [hr, map_inv, map_inv]
      exact (map_inv T _).symm
    rw [h3, hW, ← hT, hιw]
  obtain ⟨e2⟩ := s78dg_svk_one_cell (s78dg_gr_U (NonOrientableRel p 0)) (s78dg_gr_V (NonOrientableRel p 0))
    (s78dg_gr_U_open (s78dg_no_hb p)) (s78dg_gr_V_open (s78dg_no_hb p)) (s78dg_gr_cover (s78dg_no_hb p))
    (b : Quot (NonOrientableRel p 0)) hx₀ eU γ' hγ' w hw
  have hins : insert w (∅ : Set (FreeGroup (Fin p))) = {w} := by
    ext x; simp
  rw [hins] at e2
  exact ⟨e2⟩

theorem s78dg_no_closed_pathConnected (p : ℕ) (hp : 1 ≤ p) :
    PathConnectedSpace (Quot (NonOrientableRel p 0)) := by
  haveI := s78dg_no_U_pathConnected p hp
  haveI := s78dg_gr_V_contractible (s78dg_no_hb p)
  have hU : IsPathConnected (s78dg_gr_U (NonOrientableRel p 0)) :=
    isPathConnected_iff_pathConnectedSpace.2 inferInstance
  have hV : IsPathConnected (s78dg_gr_V (NonOrientableRel p 0)) :=
    isPathConnected_iff_pathConnectedSpace.2 inferInstance
  have hne : (s78dg_gr_U (NonOrientableRel p 0) ∩ s78dg_gr_V (NonOrientableRel p 0)).Nonempty := by
    haveI := s78dg_no_overlap_pathConnected p hp
    obtain ⟨b⟩ := (inferInstance : Nonempty ↥(s78dg_gr_U (NonOrientableRel p 0) ∩
      s78dg_gr_V (NonOrientableRel p 0)))
    exact ⟨b, b.2⟩
  have := hU.union hV hne
  rw [s78dg_gr_cover (s78dg_no_hb p)] at this
  exact pathConnectedSpace_iff_univ.2 this

/-- **π₁ of the closed nonorientable surface of `p ≥ 1` crosscaps** is `⟨a₁, …, aₚ | a₁² ⋯ aₚ²⟩`
at every base point. -/
theorem s78dg_nonor_pi1 (p : ℕ) (hp : 1 ≤ p) (x : Quot (NonOrientableRel p 0)) :
    Nonempty (FundamentalGroup (Quot (NonOrientableRel p 0)) x ≃*
      PresentedGroup ({(List.ofFn fun i : Fin p => FreeGroup.of i ^ 2).prod} : Set (FreeGroup (Fin p)))) := by
  obtain ⟨x₀, ⟨f⟩⟩ := s78dg_no_pi1_base p hp
  haveI := s78dg_no_closed_pathConnected p hp
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x x₀).trans f⟩


end LiZhongQC
