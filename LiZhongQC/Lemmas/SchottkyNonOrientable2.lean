import LiZhongQC.Lemmas.SchottkyNonOrientable1
import LiZhongQC.Lemmas.SchottkyClosedSurface12

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology unitInterval

universe u

namespace LiZhongQC

theorem s78dg_no_rel_boundary {p n : ℕ} {x y : ClosedUnitDisc} (h : NonOrientableRel p n x y) :
    ‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1 := by
  cases h <;> exact ⟨s78dg_cs_bdy_norm _, s78dg_cs_bdy_norm _⟩

/-- The parameter map `(ρ, u) ↦ π(ρ · exp(2πi u / (4p)))` onto the punctured chart is a quotient map. -/
theorem s78dg_no_hb (p : ℕ) :
    ∀ x y, NonOrientableRel p 0 x y → ‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1 :=
  fun _ _ h => s78dg_no_rel_boundary h

theorem s78dg_no_Psi (p : ℕ) (hp : 1 ≤ p) :
    ∃ Ψ : Set.Ioc (0 : ℝ) 1 × ℝ → ↥(s78dg_gr_U (NonOrientableRel p 0)), Topology.IsQuotientMap Ψ ∧
      ∀ (ρ : Set.Ioc (0 : ℝ) 1) (u : ℝ), ∃ z : ClosedUnitDisc,
        (z : ℂ) = ((ρ : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((u / (2 * p) : ℝ) : ℂ)) ∧
          ((Ψ (ρ, u) : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0)) = Quot.mk (NonOrientableRel p 0) z := by
  have hp0 : (0 : ℝ) < 2 * p := by positivity
  let c : ℝ := 2 * Real.pi / (2 * p)
  have hc : c ≠ 0 := by positivity
  let ε : ℝ → Circle := fun u => Circle.exp (c * u)
  have hεc : Continuous ε := Circle.exp.continuous.comp (continuous_const.mul continuous_id)
  have hεo : IsOpenMap ε :=
    (Circle.isCoveringMap_exp.isLocalHomeomorph.isOpenMap).comp (Homeomorph.mulLeft₀ c hc).isOpenMap
  have hεs : Function.Surjective ε := by
    intro w
    refine ⟨Complex.arg w / c, ?_⟩
    change Circle.exp (c * (Complex.arg w / c)) = w
    rw [mul_div_cancel₀ _ hc]
    exact Circle.exp_arg w
  have hq1 : IsQuotientMap (Prod.map (id : Set.Ioc (0 : ℝ) 1 → Set.Ioc (0 : ℝ) 1) ε) :=
    (IsOpenMap.id.prodMap hεo).isQuotientMap (continuous_id.prodMap hεc)
      (Function.surjective_id.prodMap hεs)
  have hq2 : IsQuotientMap (s78dg_cs_polar.symm : (Set.Ioc (0 : ℝ) 1 × Circle) →
      {z : ClosedUnitDisc // (z : ℂ) ≠ 0}) := s78dg_cs_polar.symm.isQuotientMap
  have hset : (Quot.mk (NonOrientableRel p 0)) ⁻¹' (s78dg_gr_U (NonOrientableRel p 0)) =
      {z : ClosedUnitDisc | (z : ℂ) ≠ 0} := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have := Quot.eqvGen_exact hxy
      rcases s78dg_gr_eqv_boundary (s78dg_no_hb p) this with h | h
      · rw [← h]; exact hx
      · intro hy0
        have := h.2
        rw [hy0, norm_zero] at this
        exact zero_ne_one this
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hq3 := isQuotientMap_quot_mk.restrictPreimage_isOpen (s78dg_gr_U_open (s78dg_no_hb p))
  let e0 : {z : ClosedUnitDisc // (z : ℂ) ≠ 0} ≃ₜ ↥((Quot.mk (NonOrientableRel p 0)) ⁻¹' (s78dg_gr_U (NonOrientableRel p 0))) :=
    Homeomorph.setCongr hset.symm
  have hq4 : IsQuotientMap (fun z : {z : ClosedUnitDisc // (z : ℂ) ≠ 0} =>
      ((s78dg_gr_U (NonOrientableRel p 0)).restrictPreimage (Quot.mk (NonOrientableRel p 0))) (e0 z)) :=
    hq3.comp e0.isQuotientMap
  refine ⟨fun q => ((s78dg_gr_U (NonOrientableRel p 0)).restrictPreimage (Quot.mk (NonOrientableRel p 0)))
    (e0 (s78dg_cs_polar.symm (Prod.map id ε q))), (hq4.comp (hq2.comp hq1)), ?_⟩
  intro ρ u
  refine ⟨(s78dg_cs_polar.symm (ρ, ε u)).1, ?_, rfl⟩
  change (((ρ : ℝ) : ℂ) * ((ε u : Circle) : ℂ)) = _
  congr 1
  change ((Circle.exp (c * u) : Circle) : ℂ) = _
  rw [Circle.coe_exp]
  congr 1
  push_cast
  simp only [c]
  push_cast
  field_simp


/-- A map out of the parameter space which is periodic and compatible with the generating gluings
(on the boundary circle `ρ = 1`) is constant on the fibres of the parameter map `Ψ`. -/
theorem s78dg_no_respects (p : ℕ) (hp : 1 ≤ p)
    (Ψ : Set.Ioc (0 : ℝ) 1 × ℝ → ↥(s78dg_gr_U (NonOrientableRel p 0)))
    (hΨ : ∀ (ρ : Set.Ioc (0 : ℝ) 1) (u : ℝ), ∃ z : ClosedUnitDisc,
        (z : ℂ) = ((ρ : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((u / (2 * p) : ℝ) : ℂ)) ∧
          ((Ψ (ρ, u) : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0)) = Quot.mk (NonOrientableRel p 0) z)
    {Y : Type*} (G : Set.Ioc (0 : ℝ) 1 × ℝ → Y)
    (hper : ∀ ρ u, G (ρ, u + 2 * p) = G (ρ, u))
    (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (hga : ∀ (i : Fin p) (x : ℝ), 0 ≤ x → x ≤ 1 → G (one, 2 * i + x) = G (one, 2 * i + 1 + x)) :
    ∀ a b, Ψ a = Ψ b → G a = G b := by
  have hN : (2 * (p : ℝ)) ≠ 0 := by positivity
  let ce : ℝ → ℂ := fun u => Complex.exp (2 * Real.pi * Complex.I * ((u / (2 * p) : ℝ) : ℂ))
  have hce_norm : ∀ u, ‖ce u‖ = 1 := by
    intro u
    simp only [ce]
    have : (2 * Real.pi * Complex.I * ((u / (2 * p) : ℝ) : ℂ)) =
        ((2 * Real.pi * (u / (2 * p)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  -- values of `G` on the boundary circle depend only on the point of the circle
  have hbdy : ∀ u v, ce u = ce v → G (one, u) = G (one, v) := by
    intro u v h
    obtain ⟨m, hm⟩ := (s78dg_cs_exp_eq_iff hN u v).1 h
    rw [hm]
    exact s78dg_cs_periodic_int G (2 * p) one (fun u => hper one u) v m
  have hbd : ∀ t : ℝ, ((ClosedUnitDisc.bdyPtOfReal t : ClosedUnitDisc) : ℂ) = ce (t * (2 * p)) := by
    intro t
    have : (t * (2 * p)) / (2 * p) = t := by field_simp
    simp only [ce, this]
    simp [ClosedUnitDisc.bdyPtOfReal, Real.fourierChar_apply]
    congr 1
    push_cast; ring
  -- the generated equivalence relation
  have key : ∀ x y : ClosedUnitDisc, Relation.EqvGen (NonOrientableRel p 0) x y →
      x = y ∨ (‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1 ∧ ∀ u v, (x : ℂ) = ce u → (y : ℂ) = ce v →
        G (one, u) = G (one, v)) := by
    intro x y h
    induction h with
    | rel a b hab =>
      refine Or.inr ⟨(s78dg_no_rel_boundary hab).1, (s78dg_no_rel_boundary hab).2, ?_⟩
      intro u v hu hv
      cases hab with
      | a x' i =>
        have e1 : ((2 * (i : ℝ) + x') / (2 * p + 3 * ((0 : ℕ) : ℝ))) * (2 * p) = 2 * i + x' := by
          simp; field_simp
        have e2 : ((2 * (i : ℝ) + 1 + x') / (2 * p + 3 * ((0 : ℕ) : ℝ))) * (2 * p) = 2 * i + 1 + x' := by
          simp; field_simp
        rw [hbd, e1] at hu
        rw [hbd, e2] at hv
        rw [hbdy u _ hu.symm, hbdy v _ hv.symm]
        exact hga i x' x'.2.1 x'.2.2
      | c x' i => exact i.elim0
    | refl a => exact Or.inl rfl
    | symm a b _ ih =>
      rcases ih with rfl | h1
      · exact Or.inl rfl
      · exact Or.inr ⟨h1.2.1, h1.1, fun u v hu hv => (h1.2.2 v u hv hu).symm⟩
    | trans a b c _ _ ih1 ih2 =>
      rcases ih1 with rfl | h1
      · exact ih2
      · rcases ih2 with rfl | h2
        · exact Or.inr h1
        · refine Or.inr ⟨h1.1, h2.2.1, fun u v hu hv => ?_⟩
          obtain ⟨w, hw⟩ := s78dg_cs_exists_param hN (b : ℂ) h1.2.1
          exact (h1.2.2 u w hu hw).trans (h2.2.2 w v hw hv)
  rintro ⟨ρa, ua⟩ ⟨ρb, ub⟩ hab
  obtain ⟨za, hza, hza'⟩ := hΨ ρa ua
  obtain ⟨zb, hzb, hzb'⟩ := hΨ ρb ub
  have hπ : Quot.mk (NonOrientableRel p 0) za = Quot.mk (NonOrientableRel p 0) zb := by
    rw [← hza', ← hzb', hab]
  have hnorm : ∀ (ρ : Set.Ioc (0 : ℝ) 1) (u : ℝ),
      ‖((ρ : ℝ) : ℂ) * ce u‖ = ρ := by
    intro ρ u
    rw [norm_mul, hce_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ρ.2.1]
  rcases key za zb (Quot.eqvGen_exact hπ) with h | h
  · -- same point of the disc
    have h1 : ((ρa : ℝ) : ℂ) * ce ua = ((ρb : ℝ) : ℂ) * ce ub := by
      have := hza.symm.trans ((congrArg (fun z : ClosedUnitDisc => (z : ℂ)) h).trans hzb)
      exact this
    have hρ : ρa = ρb := by
      apply Subtype.ext
      have := congrArg norm h1
      rw [hnorm, hnorm] at this
      exact this
    subst hρ
    have hρC : ((ρa : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ρa.2.1.ne'
    have h2 : ce ua = ce ub := mul_left_cancel₀ hρC h1
    obtain ⟨m, hm⟩ := (s78dg_cs_exp_eq_iff hN ua ub).1 h2
    rw [hm]
    exact s78dg_cs_periodic_int G (2 * p) ρa (fun u => hper ρa u) ub m
  · -- boundary points
    have hna : ((ρa : ℝ) : ℝ) = 1 := by
      have := h.1
      rw [hza, hnorm] at this
      exact this
    have hnb : ((ρb : ℝ) : ℝ) = 1 := by
      have := h.2.1
      rw [hzb, hnorm] at this
      exact this
    have ha : ρa = one := Subtype.ext (hna.trans hone.symm)
    have hb : ρb = one := Subtype.ext (hnb.trans hone.symm)
    subst ha hb
    refine h.2.2 ua ub ?_ ?_
    · change (za : ℂ) = ce ua
      rw [hza, hna]; change (((1 : ℝ) : ℂ)) * ce ua = ce ua; simp
    · change (zb : ℂ) = ce ub
      rw [hzb, hnb]; change (((1 : ℝ) : ℂ)) * ce ub = ce ub; simp


/-- The parameter map `(ρ, u) ↦ π(ρ · exp(2πi u / (4p)))` onto the punctured chart
(chosen from `s78dg_no_Psi`). -/
noncomputable def s78dg_no_Psi_fun (p : ℕ) (hp : 1 ≤ p) :
    Set.Ioc (0 : ℝ) 1 × ℝ → ↥(s78dg_gr_U (NonOrientableRel p 0)) :=
  (s78dg_no_Psi p hp).choose

theorem s78dg_no_Psi_quot (p : ℕ) (hp : 1 ≤ p) : Topology.IsQuotientMap (s78dg_no_Psi_fun p hp) :=
  (s78dg_no_Psi p hp).choose_spec.1

theorem s78dg_no_Psi_spec (p : ℕ) (hp : 1 ≤ p) (ρ : Set.Ioc (0 : ℝ) 1) (u : ℝ) :
    ∃ z : ClosedUnitDisc,
        (z : ℂ) = ((ρ : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((u / (2 * p) : ℝ) : ℂ)) ∧
          ((s78dg_no_Psi_fun p hp (ρ, u) : ↥(s78dg_gr_U (NonOrientableRel p 0))) : Quot (NonOrientableRel p 0)) =
            Quot.mk (NonOrientableRel p 0) z :=
  (s78dg_no_Psi p hp).choose_spec.2 ρ u

/-- If two parameters give the same disc point (as complex numbers) they have the same image. -/
theorem s78dg_no_Psi_eq_of_coe (p : ℕ) (hp : 1 ≤ p) (ρ ρ' : Set.Ioc (0 : ℝ) 1) (u u' : ℝ)
    (h : ((ρ : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((u / (2 * p) : ℝ) : ℂ)) =
      ((ρ' : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((u' / (2 * p) : ℝ) : ℂ))) :
    s78dg_no_Psi_fun p hp (ρ, u) = s78dg_no_Psi_fun p hp (ρ', u') := by
  obtain ⟨z, hz, hz'⟩ := s78dg_no_Psi_spec p hp ρ u
  obtain ⟨z', hz2, hz2'⟩ := s78dg_no_Psi_spec p hp ρ' u'
  have : z = z' := Subtype.ext (hz.trans (h.trans hz2.symm))
  apply Subtype.ext
  rw [hz', hz2', this]

theorem s78dg_no_Psi_periodic (p : ℕ) (hp : 1 ≤ p) (ρ : Set.Ioc (0 : ℝ) 1) (u : ℝ) :
    s78dg_no_Psi_fun p hp (ρ, u + 2 * p) = s78dg_no_Psi_fun p hp (ρ, u) := by
  apply s78dg_no_Psi_eq_of_coe
  have hN : (2 * (p : ℝ)) ≠ 0 := by positivity
  congr 1
  rw [(s78dg_cs_exp_eq_iff hN (u + 2 * p) u)]
  exact ⟨1, by ring⟩

theorem s78dg_no_bdy_coe (p : ℕ) (hp : 1 ≤ p) (t : ℝ) :
    ((ClosedUnitDisc.bdyPtOfReal t : ClosedUnitDisc) : ℂ) =
      ((1 : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((t * (2 * p)) / (2 * p) : ℝ) : ℂ)) := by
  have hN : (2 * (p : ℝ)) ≠ 0 := by positivity
  have : (t * (2 * p)) / (2 * p) = t := by field_simp
  rw [this]
  simp [ClosedUnitDisc.bdyPtOfReal, Real.fourierChar_apply]
  congr 1
  push_cast; ring

/-- Gluing of the edge pair: `2i + x ~ 2i + 1 + x`. -/
theorem s78dg_no_Psi_rel_a (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (i : Fin p) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    s78dg_no_Psi_fun p hp (one, 2 * (i : ℝ) + x) = s78dg_no_Psi_fun p hp (one, 2 * (i : ℝ) + 1 + x) := by
  obtain ⟨z, hz, hz'⟩ := s78dg_no_Psi_spec p hp one (2 * (i : ℝ) + x)
  obtain ⟨z', hz2, hz2'⟩ := s78dg_no_Psi_spec p hp one (2 * (i : ℝ) + 1 + x)
  have hN : (2 * (p : ℝ)) ≠ 0 := by positivity
  have e1 : (2 * (i : ℝ) + x) / (2 * p + 3 * ((0 : ℕ) : ℝ)) * (2 * p) = 2 * i + x := by
    simp; field_simp
  have e2 : (2 * (i : ℝ) + 1 + x) / (2 * p + 3 * ((0 : ℕ) : ℝ)) * (2 * p) = 2 * i + 1 + x := by
    simp; field_simp
  have hzb : z = ClosedUnitDisc.bdyPtOfReal ((2 * (i : ℝ) + x) / (2 * p + 3 * ((0 : ℕ) : ℝ))) := by
    apply Subtype.ext
    rw [hz, s78dg_no_bdy_coe p hp, e1, hone]
  have hzb' : z' = ClosedUnitDisc.bdyPtOfReal ((2 * (i : ℝ) + 1 + x) / (2 * p + 3 * ((0 : ℕ) : ℝ))) := by
    apply Subtype.ext
    rw [hz2, s78dg_no_bdy_coe p hp, e2, hone]
  apply Subtype.ext
  rw [hz', hz2', hzb, hzb']
  exact Quot.sound (NonOrientableRel.a (p := p) (n := 0) ⟨x, h0, h1⟩ i)

theorem s78dg_no_Psi_even (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (i : ℕ) (hi : i < p) :
    s78dg_no_Psi_fun p hp (one, ((2 * i + 1 : ℕ) : ℝ)) = s78dg_no_Psi_fun p hp (one, ((2 * i : ℕ) : ℝ)) := by
  have h := s78dg_no_Psi_rel_a p hp one hone ⟨i, hi⟩ 0 le_rfl zero_le_one
  simp only [add_zero] at h
  push_cast
  exact h.symm.trans (by congr 2)

theorem s78dg_no_Psi_odd (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (i : ℕ) (hi : i < p) :
    s78dg_no_Psi_fun p hp (one, ((2 * i + 1 + 1 : ℕ) : ℝ)) = s78dg_no_Psi_fun p hp (one, ((2 * i + 1 : ℕ) : ℝ)) := by
  have h := s78dg_no_Psi_rel_a p hp one hone ⟨i, hi⟩ 1 zero_le_one le_rfl
  push_cast
  exact h.symm.trans (by congr 2)

/-- All vertices of the polygon are identified in the quotient. -/
theorem s78dg_no_Psi_vertex (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (j : ℤ) : s78dg_no_Psi_fun p hp (one, (j : ℝ)) = s78dg_no_Psi_fun p hp (one, 0) := by
  have hA : ∀ n : ℕ, n ≤ 2 * p → s78dg_no_Psi_fun p hp (one, (n : ℝ)) = s78dg_no_Psi_fun p hp (one, 0) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k < 2 * p := hk
      have h1 := ih hk'.le
      obtain ⟨i, rfl | rfl⟩ : ∃ i, k = 2 * i ∨ k = 2 * i + 1 := ⟨k / 2, by omega⟩
      · exact (s78dg_no_Psi_even p hp one hone i (by omega)).trans h1
      · exact (s78dg_no_Psi_odd p hp one hone i (by omega)).trans h1
  let N : ℤ := ((2 * p : ℕ) : ℤ)
  have hNpos : 0 < N := by simp only [N]; positivity
  set r := j % N with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hNpos.ne'
  have hr1 : r < N := Int.emod_lt_of_pos _ hNpos
  have hj : (j : ℝ) = (r : ℝ) + ((j / N : ℤ) : ℝ) * (2 * p) := by
    have : j = r + (j / N) * N := by
      rw [hr]; exact (Int.emod_add_mul_ediv j N).symm.trans (by ring)
    have h2 : (j : ℝ) = (r : ℝ) + ((j / N : ℤ) : ℝ) * (N : ℝ) := by exact_mod_cast this
    rw [h2]; simp [N]
  rw [hj]
  rw [s78dg_cs_periodic_int (fun q : Set.Ioc (0 : ℝ) 1 × ℝ => s78dg_no_Psi_fun p hp q) (2 * p) one
    (fun u => s78dg_no_Psi_periodic p hp one u) (r : ℝ) (j / N)]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, r = (n : ℤ) := ⟨r.toNat, (Int.toNat_of_nonneg hr0).symm⟩
  have hnlt : n < 2 * p := by
    have : (n : ℤ) < ((2 * p : ℕ) : ℤ) := by rw [← hn]; exact hr1
    exact_mod_cast this
  rw [hn]
  have hcast : (((n : ℤ) : ℝ)) = (n : ℝ) := by norm_cast
  rw [hcast]
  exact hA n hnlt.le

/-- The petal (pair of glued edges) containing the unit edge `[j, j+1]` of the `2p`-gon:
edges `2i, 2i+1` form petal `i` (the crosscap generator `a_i`). -/
def s78dg_no_kappa (p : ℕ) (j : ℤ) : ℕ :=
  (j % ((2 * p : ℕ) : ℤ)).toNat / 2

theorem s78dg_no_kappa_periodic (p : ℕ) (j : ℤ) :
    s78dg_no_kappa p (j + ((2 * p : ℕ) : ℤ)) = s78dg_no_kappa p j := by
  unfold s78dg_no_kappa
  rw [Int.add_emod_right]

theorem s78dg_no_kappa_edge (p : ℕ) {i r : ℕ} (hi : i < p) (hr : r < 2) :
    s78dg_no_kappa p ((2 * i + r : ℕ) : ℤ) = i := by
  unfold s78dg_no_kappa
  have hlt : 2 * i + r < 2 * p := by omega
  have : (((2 * i + r : ℕ) : ℤ) % ((2 * p : ℕ) : ℤ)).toNat = 2 * i + r := by
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)]
    omega
  rw [this]
  omega

/-- The snapping map: on edges of the petals in `P` it is the identity, on all other edges it
pushes each point within `1/4` of a vertex onto that vertex (and is linear in between). -/
noncomputable def s78dg_no_tau (p : ℕ) (P : ℕ → Prop) (u : ℝ) : ℝ :=
  u + (by classical exact if P (s78dg_no_kappa p ⌊u⌋) then 0 else s78dg_cs_T (Int.fract u) - Int.fract u)

theorem s78dg_no_tau_pet (p : ℕ) (P : ℕ → Prop) {u : ℝ} (h : P (s78dg_no_kappa p ⌊u⌋)) :
    s78dg_no_tau p P u = u := by
  unfold s78dg_no_tau
  rw [if_pos h, add_zero]

theorem s78dg_no_tau_snap (p : ℕ) (P : ℕ → Prop) {u : ℝ} (h : ¬ P (s78dg_no_kappa p ⌊u⌋)) :
    s78dg_no_tau p P u = u + (s78dg_cs_T (Int.fract u) - Int.fract u) := by
  unfold s78dg_no_tau
  rw [if_neg h]

theorem s78dg_no_tau_int (p : ℕ) (P : ℕ → Prop) (j : ℤ) : s78dg_no_tau p P (j : ℝ) = j := by
  by_cases h : P (s78dg_no_kappa p ⌊(j : ℝ)⌋)
  · exact s78dg_no_tau_pet p P h
  · rw [s78dg_no_tau_snap p P h]
    simp [s78dg_cs_T_zero]

theorem s78dg_no_tau_periodic (p : ℕ) (P : ℕ → Prop) (u : ℝ) :
    s78dg_no_tau p P (u + ((2 * p : ℕ) : ℝ)) = s78dg_no_tau p P u + ((2 * p : ℕ) : ℝ) := by
  have hfl : ⌊u + ((2 * p : ℕ) : ℝ)⌋ = ⌊u⌋ + ((2 * p : ℕ) : ℤ) := by
    rw [Int.floor_add_natCast]
  have hfr : Int.fract (u + ((2 * p : ℕ) : ℝ)) = Int.fract u := Int.fract_add_natCast _ _
  by_cases h : P (s78dg_no_kappa p ⌊u⌋)
  · have h' : P (s78dg_no_kappa p ⌊u + ((2 * p : ℕ) : ℝ)⌋) := by
      rw [hfl, s78dg_no_kappa_periodic]; exact h
    rw [s78dg_no_tau_pet p P h, s78dg_no_tau_pet p P h']
  · have h' : ¬ P (s78dg_no_kappa p ⌊u + ((2 * p : ℕ) : ℝ)⌋) := by
      rw [hfl, s78dg_no_kappa_periodic]; exact h
    rw [s78dg_no_tau_snap p P h, s78dg_no_tau_snap p P h', hfr]
    ring

theorem s78dg_no_tau_edge (p : ℕ) (P : ℕ → Prop) (j : ℤ) {u : ℝ} (h0 : (j : ℝ) ≤ u)
    (h1 : u ≤ (j : ℝ) + 1) : (j : ℝ) ≤ s78dg_no_tau p P u ∧ s78dg_no_tau p P u ≤ (j : ℝ) + 1 := by
  rcases eq_or_lt_of_le h1 with h | h
  · have : u = ((j + 1 : ℤ) : ℝ) := by push_cast; exact h
    rw [this, s78dg_no_tau_int]
    push_cast
    constructor <;> linarith
  · have hfl : ⌊u⌋ = j := by
      rw [Int.floor_eq_iff]; exact ⟨h0, h⟩
    have hfr : Int.fract u = u - j := by rw [Int.fract, hfl]
    have hf0 : 0 ≤ u - j := by linarith
    have hf1 : u - j < 1 := by linarith
    by_cases hP : P (s78dg_no_kappa p ⌊u⌋)
    · rw [s78dg_no_tau_pet p P hP]; exact ⟨h0, h1⟩
    · rw [s78dg_no_tau_snap p P hP, hfr]
      have := s78dg_cs_T_bounds (u - j)
      constructor <;> linarith [this.1, this.2]

theorem s78dg_no_tau_cont (p : ℕ) (P : ℕ → Prop) : Continuous (s78dg_no_tau p P) := by
  classical
  let B : ℝ → ℝ := fun f => s78dg_cs_T f - f
  have hB0 : B 0 = B 1 := by
    simp [B, s78dg_cs_T_zero, s78dg_cs_T_one]
  have hBc : Continuous (B ∘ Int.fract) :=
    ContinuousOn.comp_fract'' (by
      have : Continuous B := s78dg_cs_T_cont.sub continuous_id
      exact this.continuousOn) hB0
  let c : ℝ → ℝ := fun u => if P (s78dg_no_kappa p ⌊u⌋) then 0 else B (Int.fract u)
  have hτ : s78dg_no_tau p P = fun u => u + c u := by
    funext u
    unfold s78dg_no_tau
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
      have hceq : c =ᶠ[nhds x] fun u => if P (s78dg_no_kappa p ⌊x⌋) then 0 else B (Int.fract u) := by
        filter_upwards [hev] with u hu
        simp only [c, hu]
      refine ContinuousAt.congr ?_ hceq.symm
      by_cases hP : P (s78dg_no_kappa p ⌊x⌋)
      · simp only [hP, if_true]; exact continuousAt_const
      · simp only [hP, if_false]; exact hBc.continuousAt
  rw [hτ]
  exact continuous_id.add hc

/-- The snapping map commutes with the translation that glues the edge `[e, e+1]` to `[e+1, e+2]`. -/
theorem s78dg_no_tau_translate (p : ℕ) (P : ℕ → Prop) (e : ℤ)
    (hκ : s78dg_no_kappa p e = s78dg_no_kappa p (e + 1)) {u : ℝ} (h0 : (e : ℝ) ≤ u)
    (h1 : u ≤ (e : ℝ) + 1) :
    s78dg_no_tau p P (u + 1) = s78dg_no_tau p P u + 1 := by
  rcases eq_or_lt_of_le h1 with h | h
  · have h2 : u = ((e + 1 : ℤ) : ℝ) := by push_cast; exact h
    have h3 : u + 1 = ((e + 2 : ℤ) : ℝ) := by push_cast; rw [h]; ring
    rw [h3, h2, s78dg_no_tau_int, s78dg_no_tau_int]; push_cast; ring
  have hfl : ⌊u⌋ = e := by rw [Int.floor_eq_iff]; exact ⟨h0, h⟩
  have hfl2 : ⌊u + 1⌋ = e + 1 := by rw [Int.floor_add_one, hfl]
  have hfr2 : Int.fract (u + 1) = Int.fract u := Int.fract_add_one u
  by_cases hP : P (s78dg_no_kappa p ⌊u⌋)
  · have hP2 : P (s78dg_no_kappa p ⌊u + 1⌋) := by
      rw [hfl2, ← hκ]; rw [hfl] at hP; exact hP
    rw [s78dg_no_tau_pet p P hP, s78dg_no_tau_pet p P hP2]
  · have hP2 : ¬ P (s78dg_no_kappa p ⌊u + 1⌋) := by
      rw [hfl2, ← hκ]; rw [hfl] at hP; exact hP
    rw [s78dg_no_tau_snap p P hP, s78dg_no_tau_snap p P hP2, hfr2]
    ring

/-- The set of boundary parameters kept in the chart `S P`: a quarter-neighbourhood of every vertex,
together with the (open) edges of the petals in `P`. -/
def s78dg_no_S (p : ℕ) (P : ℕ → Prop) : Set ℝ :=
  {u | (∃ j : ℤ, |u - j| < 1 / 4) ∨ P (s78dg_no_kappa p ⌊u⌋)}

theorem s78dg_no_S_periodic (p : ℕ) (P : ℕ → Prop) (u : ℝ) :
    u + ((2 * p : ℕ) : ℝ) ∈ s78dg_no_S p P ↔ u ∈ s78dg_no_S p P := by
  have hfl : ⌊u + ((2 * p : ℕ) : ℝ)⌋ = ⌊u⌋ + ((2 * p : ℕ) : ℤ) := by
    rw [Int.floor_add_natCast]
  simp only [s78dg_no_S, Set.mem_setOf_eq, hfl, s78dg_no_kappa_periodic]
  have hN : (((2 * p : ℕ) : ℤ) : ℝ) = ((2 * p : ℕ) : ℝ) := by norm_cast
  constructor
  · rintro (⟨j, hj⟩ | h)
    · left
      refine ⟨j - ((2 * p : ℕ) : ℤ), ?_⟩
      have : u - (((j - ((2 * p : ℕ) : ℤ) : ℤ)) : ℝ) = u + ((2 * p : ℕ) : ℝ) - j := by
        rw [Int.cast_sub, hN]; ring
      rw [this]; exact hj
    · right; exact h
  · rintro (⟨j, hj⟩ | h)
    · left
      refine ⟨j + ((2 * p : ℕ) : ℤ), ?_⟩
      have : u + ((2 * p : ℕ) : ℝ) - (((j + ((2 * p : ℕ) : ℤ) : ℤ)) : ℝ) = u - j := by
        rw [Int.cast_add, hN]; ring
      rw [this]; exact hj
    · right; exact h

theorem s78dg_no_S_open (p : ℕ) (P : ℕ → Prop) : IsOpen (s78dg_no_S p P) := by
  rw [isOpen_iff_mem_nhds]
  intro u hu
  by_cases hD : ∃ j : ℤ, |u - j| < 1 / 4
  · obtain ⟨j, hj⟩ := hD
    have hmem : u ∈ Metric.ball (j : ℝ) (1 / 4) := by rw [Metric.mem_ball, Real.dist_eq]; exact hj
    filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with v hv
    left
    exact ⟨j, by rw [Metric.mem_ball, Real.dist_eq] at hv; exact hv⟩
  · have hP : P (s78dg_no_kappa p ⌊u⌋) := hu.resolve_left hD
    have hnj : u ≠ (⌊u⌋ : ℝ) := by
      intro h
      exact hD ⟨⌊u⌋, by rw [← h]; simp⟩
    have hmem : u ∈ Set.Ioo (⌊u⌋ : ℝ) ((⌊u⌋ : ℝ) + 1) :=
      ⟨lt_of_le_of_ne (Int.floor_le u) (Ne.symm hnj), Int.lt_floor_add_one u⟩
    filter_upwards [isOpen_Ioo.mem_nhds hmem] with v hv
    right
    have : ⌊v⌋ = ⌊u⌋ := by rw [Int.floor_eq_iff]; exact ⟨hv.1.le, hv.2⟩
    rw [this]; exact hP

theorem s78dg_no_S_translate (p : ℕ) (P : ℕ → Prop) (e : ℤ)
    (hκ : s78dg_no_kappa p e = s78dg_no_kappa p (e + 1)) {u : ℝ} (h0 : (e : ℝ) ≤ u)
    (h1 : u ≤ (e : ℝ) + 1) :
    u + 1 ∈ s78dg_no_S p P ↔ u ∈ s78dg_no_S p P := by
  rcases eq_or_lt_of_le h0 with h | h
  · have hu : u = (e : ℝ) := h.symm
    constructor <;> intro _
    · exact Or.inl ⟨e, by rw [hu]; simp⟩
    · exact Or.inl ⟨e + 1, by rw [hu]; push_cast; ring_nf; simp⟩
  rcases eq_or_lt_of_le h1 with h' | h'
  · have h3 : u = ((e + 1 : ℤ) : ℝ) := by push_cast; exact h'
    constructor <;> intro _
    · exact Or.inl ⟨e + 1, by rw [h3]; simp⟩
    · exact Or.inl ⟨e + 2, by rw [h3]; push_cast; ring_nf; simp⟩
  have hfl : ⌊u⌋ = e := by rw [Int.floor_eq_iff]; exact ⟨h0, h'⟩
  have hfl2 : ⌊u + 1⌋ = e + 1 := by rw [Int.floor_add_one, hfl]
  simp only [s78dg_no_S, Set.mem_setOf_eq, hfl, hfl2, ← hκ]
  constructor
  · rintro (⟨j, hj⟩ | hP)
    · left
      refine ⟨j - 1, ?_⟩
      have : u - ((j - 1 : ℤ) : ℝ) = u + 1 - j := by push_cast; ring
      rw [this]; exact hj
    · right; exact hP
  · rintro (⟨j, hj⟩ | hP)
    · left
      refine ⟨j + 1, ?_⟩
      have : u + 1 - ((j + 1 : ℤ) : ℝ) = u - j := by push_cast; ring
      rw [this]; exact hj
    · right; exact hP

theorem s78dg_no_S_star (p : ℕ) (P : ℕ → Prop) {u : ℝ} (hu : u ∈ s78dg_no_S p P) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) * u + s * s78dg_no_tau p P u ∈ s78dg_no_S p P := by
  by_cases hP : P (s78dg_no_kappa p ⌊u⌋)
  · rw [s78dg_no_tau_pet p P hP]
    have : (1 - s) * u + s * u = u := by ring
    rw [this]; exact hu
  · obtain ⟨j, hj⟩ := hu.resolve_right hP
    have hτ : s78dg_no_tau p P u = j := by
      rw [abs_lt] at hj
      rcases le_or_gt (j : ℝ) u with hju | hju
      · have hfl : ⌊u⌋ = j := by rw [Int.floor_eq_iff]; constructor <;> linarith
        have hfr : Int.fract u = u - j := by rw [Int.fract, hfl]
        rw [s78dg_no_tau_snap p P hP, hfr, s78dg_cs_T_low (by linarith)]; ring
      · have hfl : ⌊u⌋ = j - 1 := by rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
        have hfr : Int.fract u = u - (j - 1) := by rw [Int.fract, hfl]; push_cast; ring
        rw [s78dg_no_tau_snap p P hP, hfr, s78dg_cs_T_high (by linarith)]; ring
    left
    refine ⟨j, ?_⟩
    rw [hτ]
    have : (1 - s) * u + s * (j : ℝ) - j = (1 - s) * (u - j) := by ring
    rw [this, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - s)]
    calc (1 - s) * |u - j| ≤ 1 * |u - j| := by
          apply mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ < 1 / 4 := by rw [one_mul]; exact hj


end LiZhongQC
