import LiZhongQC.Lemmas.SchottkyClosedSurface2

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology unitInterval

namespace LiZhongQC

theorem s78dg_cs_polar_aux1 (z : {z : ClosedUnitDisc // (z : ℂ) ≠ 0}) : ‖(z.1 : ℂ)‖ ≤ 1 :=
  mem_closedBall_zero_iff.1 z.1.2

/-- Polar coordinates on the punctured closed disc. -/
noncomputable def s78dg_cs_polar : {z : ClosedUnitDisc // (z : ℂ) ≠ 0} ≃ₜ (Set.Ioc (0 : ℝ) 1 × Circle) where
  toFun z := (⟨‖(z.1 : ℂ)‖, norm_pos_iff.2 z.2, s78dg_cs_polar_aux1 z⟩,
    ⟨(z.1 : ℂ) / (‖(z.1 : ℂ)‖ : ℂ), by simp [Submonoid.unitSphere, z.2]⟩)
  invFun q := ⟨⟨((q.1 : ℝ) : ℂ) * (q.2 : ℂ), mem_closedBall_zero_iff.2 (by
      rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos q.1.2.1]
      exact q.1.2.2)⟩, by
      have h1 : ((q.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast q.1.2.1.ne'
      have h2 : (q.2 : ℂ) ≠ 0 := by
        intro h
        have := Circle.norm_coe q.2
        rw [h, norm_zero] at this
        exact zero_ne_one this
      exact mul_ne_zero h1 h2⟩
  left_inv z := by
    apply Subtype.ext; apply Subtype.ext
    have : (‖(z.1 : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 z.2
    change (‖(z.1 : ℂ)‖ : ℂ) * ((z.1 : ℂ) / (‖(z.1 : ℂ)‖ : ℂ)) = (z.1 : ℂ)
    field_simp
  right_inv q := by
    have hρ : (q.1 : ℝ) ≠ 0 := q.1.2.1.ne'
    have hρC : ((q.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρ
    have hn : ‖((q.1 : ℝ) : ℂ) * (q.2 : ℂ)‖ = (q.1 : ℝ) := by
      rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos q.1.2.1]
    apply Prod.ext
    · apply Subtype.ext
      exact hn
    · apply Subtype.ext
      change (((q.1 : ℝ) : ℂ) * (q.2 : ℂ)) / (‖((q.1 : ℝ) : ℂ) * (q.2 : ℂ)‖ : ℂ) = (q.2 : ℂ)
      rw [hn]
      field_simp
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact Continuous.subtype_mk (continuous_norm.comp (continuous_subtype_val.comp
        continuous_subtype_val)) _
    · refine Continuous.subtype_mk ?_ _
      exact (continuous_subtype_val.comp continuous_subtype_val).div
        (Complex.continuous_ofReal.comp (continuous_norm.comp (continuous_subtype_val.comp
          continuous_subtype_val))) (fun z => by exact_mod_cast norm_ne_zero_iff.2 z.2)
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)

/-- The parameter map `(ρ, u) ↦ π(ρ · exp(2πi u / (4p)))` onto the punctured chart is a quotient map. -/
theorem s78dg_cs_Psi (p : ℕ) (hp : 1 ≤ p) :
    ∃ Ψ : Set.Ioc (0 : ℝ) 1 × ℝ → ↥(s78dg_cs_U p 0), Topology.IsQuotientMap Ψ ∧
      ∀ (ρ : Set.Ioc (0 : ℝ) 1) (u : ℝ), ∃ z : ClosedUnitDisc,
        (z : ℂ) = ((ρ : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((u / (4 * p) : ℝ) : ℂ)) ∧
          ((Ψ (ρ, u) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) = Quot.mk (OrientableRel p 0) z := by
  have hp0 : (0 : ℝ) < 4 * p := by positivity
  let c : ℝ := 2 * Real.pi / (4 * p)
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
  have hset : (Quot.mk (OrientableRel p 0)) ⁻¹' (s78dg_cs_U p 0) =
      {z : ClosedUnitDisc | (z : ℂ) ≠ 0} := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have := Quot.eqvGen_exact hxy
      rcases s78dg_cs_eqv_boundary this with h | h
      · rw [← h]; exact hx
      · intro hy0
        have := h.2
        rw [hy0, norm_zero] at this
        exact zero_ne_one this
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hq3 := isQuotientMap_quot_mk.restrictPreimage_isOpen (s78dg_cs_U_open p 0)
  let e0 : {z : ClosedUnitDisc // (z : ℂ) ≠ 0} ≃ₜ ↥((Quot.mk (OrientableRel p 0)) ⁻¹' (s78dg_cs_U p 0)) :=
    Homeomorph.setCongr hset.symm
  have hq4 : IsQuotientMap (fun z : {z : ClosedUnitDisc // (z : ℂ) ≠ 0} =>
      ((s78dg_cs_U p 0).restrictPreimage (Quot.mk (OrientableRel p 0))) (e0 z)) :=
    hq3.comp e0.isQuotientMap
  refine ⟨fun q => ((s78dg_cs_U p 0).restrictPreimage (Quot.mk (OrientableRel p 0)))
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

theorem s78dg_cs_exp_eq_iff {N : ℝ} (hN : N ≠ 0) (u v : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * ((u / N : ℝ) : ℂ)) =
        Complex.exp (2 * Real.pi * Complex.I * ((v / N : ℝ) : ℂ)) ↔ ∃ m : ℤ, u = v + m * N := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero]
    have h3 : ((u / N : ℝ) : ℂ) = ((v / N : ℝ) : ℂ) + m := by
      apply mul_left_cancel₀ h2
      rw [mul_add, hm]; ring
    have h4 : u / N = v / N + m := by exact_mod_cast h3
    field_simp at h4
    linarith
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h4 : u / N = v / N + m := by
      field_simp; linarith
    have : ((u / N : ℝ) : ℂ) = ((v / N : ℝ) : ℂ) + m := by exact_mod_cast h4
    rw [this]; ring

theorem s78dg_cs_exists_param {N : ℝ} (hN : N ≠ 0) (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ u : ℝ, z = Complex.exp (2 * Real.pi * Complex.I * ((u / N : ℝ) : ℂ)) := by
  refine ⟨Complex.arg z * N / (2 * Real.pi), ?_⟩
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  have h1 : Complex.exp (Complex.arg z * Complex.I) = z := by
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz] at this
    simpa using this
  refine h1.symm.trans ?_
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  push_cast
  field_simp

theorem s78dg_cs_periodic_int {α Y : Type*} (G : α × ℝ → Y) (N : ℝ) (a : α)
    (hper : ∀ u, G (a, u + N) = G (a, u)) (u : ℝ) (m : ℤ) : G (a, u + m * N) = G (a, u) := by
  have hn : ∀ n : ℕ, ∀ u : ℝ, G (a, u + (n : ℝ) * N) = G (a, u) := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      have : u + ((k + 1 : ℕ) : ℝ) * N = (u + (k : ℝ) * N) + N := by push_cast; ring
      rw [this, hper, ih]
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · simpa using hn n u
  · have h := hn n (u + ((-(n : ℤ) : ℤ) : ℝ) * N)
    have : u + ((-(n : ℤ) : ℤ) : ℝ) * N + (n : ℝ) * N = u := by push_cast; ring
    rw [this] at h
    exact h.symm

/-- A map out of the parameter space which is periodic and compatible with the generating gluings
(on the boundary circle `ρ = 1`) is constant on the fibres of the parameter map `Ψ`. -/
theorem s78dg_cs_respects (p : ℕ) (hp : 1 ≤ p)
    (Ψ : Set.Ioc (0 : ℝ) 1 × ℝ → ↥(s78dg_cs_U p 0))
    (hΨ : ∀ (ρ : Set.Ioc (0 : ℝ) 1) (u : ℝ), ∃ z : ClosedUnitDisc,
        (z : ℂ) = ((ρ : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((u / (4 * p) : ℝ) : ℂ)) ∧
          ((Ψ (ρ, u) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) = Quot.mk (OrientableRel p 0) z)
    {Y : Type*} (G : Set.Ioc (0 : ℝ) 1 × ℝ → Y)
    (hper : ∀ ρ u, G (ρ, u + 4 * p) = G (ρ, u))
    (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (hga : ∀ (i : Fin p) (x : ℝ), 0 ≤ x → x ≤ 1 → G (one, 4 * i + x) = G (one, 4 * i + 3 - x))
    (hgb : ∀ (i : Fin p) (x : ℝ), 0 ≤ x → x ≤ 1 → G (one, 4 * i + 1 + x) = G (one, 4 * i + 4 - x)) :
    ∀ a b, Ψ a = Ψ b → G a = G b := by
  have hN : (4 * (p : ℝ)) ≠ 0 := by positivity
  let ce : ℝ → ℂ := fun u => Complex.exp (2 * Real.pi * Complex.I * ((u / (4 * p) : ℝ) : ℂ))
  have hce_norm : ∀ u, ‖ce u‖ = 1 := by
    intro u
    simp only [ce]
    have : (2 * Real.pi * Complex.I * ((u / (4 * p) : ℝ) : ℂ)) =
        ((2 * Real.pi * (u / (4 * p)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  -- values of `G` on the boundary circle depend only on the point of the circle
  have hbdy : ∀ u v, ce u = ce v → G (one, u) = G (one, v) := by
    intro u v h
    obtain ⟨m, hm⟩ := (s78dg_cs_exp_eq_iff hN u v).1 h
    rw [hm]
    exact s78dg_cs_periodic_int G (4 * p) one (fun u => hper one u) v m
  have hbd : ∀ t : ℝ, ((ClosedUnitDisc.bdyPtOfReal t : ClosedUnitDisc) : ℂ) = ce (t * (4 * p)) := by
    intro t
    have : (t * (4 * p)) / (4 * p) = t := by field_simp
    simp only [ce, this]
    simp [ClosedUnitDisc.bdyPtOfReal, Real.fourierChar_apply]
    congr 1
    push_cast; ring
  -- the generated equivalence relation
  have key : ∀ x y : ClosedUnitDisc, Relation.EqvGen (OrientableRel p 0) x y →
      x = y ∨ (‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1 ∧ ∀ u v, (x : ℂ) = ce u → (y : ℂ) = ce v →
        G (one, u) = G (one, v)) := by
    intro x y h
    induction h with
    | rel a b hab =>
      refine Or.inr ⟨(s78dg_cs_rel_boundary hab).1, (s78dg_cs_rel_boundary hab).2, ?_⟩
      intro u v hu hv
      cases hab with
      | a x' i =>
        have e1 : ((4 * (i : ℝ) + x') / (4 * p + 3 * ((0 : ℕ) : ℝ))) * (4 * p) = 4 * i + x' := by
          simp; field_simp
        have e2 : ((4 * (i : ℝ) + 3 - x') / (4 * p + 3 * ((0 : ℕ) : ℝ))) * (4 * p) = 4 * i + 3 - x' := by
          simp; field_simp
        rw [hbd, e1] at hu
        rw [hbd, e2] at hv
        rw [hbdy u _ hu.symm, hbdy v _ hv.symm]
        exact hga i x' x'.2.1 x'.2.2
      | b x' i =>
        have e1 : ((4 * (i : ℝ) + 1 + x') / (4 * p + 3 * ((0 : ℕ) : ℝ))) * (4 * p) = 4 * i + 1 + x' := by
          simp; field_simp
        have e2 : ((4 * (i : ℝ) + 4 - x') / (4 * p + 3 * ((0 : ℕ) : ℝ))) * (4 * p) = 4 * i + 4 - x' := by
          simp; field_simp
        rw [hbd, e1] at hu
        rw [hbd, e2] at hv
        rw [hbdy u _ hu.symm, hbdy v _ hv.symm]
        exact hgb i x' x'.2.1 x'.2.2
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
  have hπ : Quot.mk (OrientableRel p 0) za = Quot.mk (OrientableRel p 0) zb := by
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
    exact s78dg_cs_periodic_int G (4 * p) ρa (fun u => hper ρa u) ub m
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

/-- Maps out of a quotient: a continuous map compatible with the fibres descends. -/
theorem s78dg_cs_descent {X Q Y : Type*} [TopologicalSpace X] [TopologicalSpace Q] [TopologicalSpace Y]
    (Ψ : X → Q) (hq : Topology.IsQuotientMap Ψ) (F : X → Y) (hF : Continuous F)
    (hres : ∀ a b, Ψ a = Ψ b → F a = F b) :
    ∃ F' : Q → Y, Continuous F' ∧ ∀ a, F' (Ψ a) = F a := by
  choose g hg using hq.surjective
  refine ⟨fun q => F (g q), ?_, fun a => hres _ _ (hg (Ψ a))⟩
  rw [hq.continuous_iff]
  have : (fun q => F (g q)) ∘ Ψ = F := funext fun a => hres _ _ (hg (Ψ a))
  rw [this]
  exact hF

/-- Homotopies out of a quotient: a continuous family compatible with the fibres descends. -/
theorem s78dg_cs_descent_hom {X Q Y : Type*} [TopologicalSpace X] [TopologicalSpace Q] [TopologicalSpace Y]
    (Ψ : X → Q) (hq : Topology.IsQuotientMap Ψ) (F : I × X → Y) (hF : Continuous F)
    (hres : ∀ s a b, Ψ a = Ψ b → F (s, a) = F (s, b)) :
    ∃ F' : I × Q → Y, Continuous F' ∧ ∀ s a, F' (s, Ψ a) = F (s, a) := by
  choose g hg using hq.surjective
  refine ⟨fun x => F (x.1, g x.2), ?_, fun s a => hres s _ _ (hg (Ψ a))⟩
  refine hq.continuous_lift_prod_right (g := fun x : I × Q => F (x.1, g x.2)) ?_
  have : (fun p : I × X => F (p.1, g (Ψ p.2))) = F := by
    funext p
    exact hres p.1 _ _ (hg (Ψ p.2))
  rw [show (fun p : I × X => (fun x : I × Q => F (x.1, g x.2)) (p.1, Ψ p.2)) = F from this]
  exact hF

end LiZhongQC
