import LiZhongQC.Lemmas.StdGenChord
import LiZhongQC.Lemmas.S27ChordMidpoints

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Metric Filter Topology unitInterval
open scoped Manifold ContDiff UpperHalfPlane

/-!
# Chord loops of the closed normal form (R83, S27 `[a']`, `[a+b]`; La1-La3 by 下属3, the rest by 下属1)

* `s83sg_chart_half`, `s83sg_chord_loop`, `s83sg_chord_chart`: the disc chart at the centre and the chord loops.
* `s83sg_chord_glue_a`, `s83sg_chord_glue_b`, `s83sg_chord_meet`: gluing of the chord ends; two chord loops with
  different midpoints meet only at the centre.
* `s83sg_chord_model` [a+b]: the two chord loops of the last handle, their chart data and their `π₁` classes.
-/

noncomputable section
namespace LiZhongQC

universe u

/-- The chart of the closed normal form at the centre: the radius-`1/2` sub-disc of the 2-cell, scaled by `2`. -/
theorem s83sg_chart_half (p : ℕ) :
    ∃ e : OpenPartialHomeomorph (Quot (OrientableRel p 0)) ℂ, e.target = Metric.ball 0 1 ∧
      (∀ z : ClosedUnitDisc, ‖(z : ℂ)‖ < 1 / 2 →
        Quot.mk (OrientableRel p 0) z ∈ e.source ∧ e (Quot.mk (OrientableRel p 0) z) = 2 * (z : ℂ)) ∧
      (∀ q ∈ e.source, ∃ z : ClosedUnitDisc, ‖(z : ℂ)‖ < 1 / 2 ∧ q = Quot.mk (OrientableRel p 0) z) := by
  let S0 : Set ClosedUnitDisc := {z | ‖(z : ℂ)‖ < 1 / 2}
  have hS0 : IsOpen S0 := isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  have hemb := s78dg_cs_open_embedding (p := p) (n := 0) S0 hS0 (fun x hx => by
    have : ‖(x : ℂ)‖ < 1 / 2 := hx
    linarith)
  have : Nonempty S0 := ⟨⟨⟨0, by simp⟩, by simp [S0]⟩⟩
  let ph := hemb.toOpenPartialHomeomorph
  let e2 : S0 ≃ₜ ↥(Metric.ball (0 : ℂ) 1) :=
    { toFun := fun z => ⟨2 * (z.1 : ℂ), by
        have : ‖(z.1 : ℂ)‖ < 1 / 2 := z.2
        rw [mem_ball_zero_iff, norm_mul]
        simp
        linarith⟩
      invFun := fun w => ⟨⟨(w : ℂ) / 2, by
        have := mem_ball_zero_iff.1 w.2
        rw [mem_closedBall_zero_iff, norm_div]
        simp
        linarith⟩, by
        have := mem_ball_zero_iff.1 w.2
        show ‖(w : ℂ) / 2‖ < 1 / 2
        rw [norm_div]
        simp
        linarith⟩
      left_inv := fun z => by
        apply Subtype.ext
        apply Subtype.ext
        show 2 * (z.1 : ℂ) / 2 = z.1
        ring
      right_inv := fun w => by
        apply Subtype.ext
        show 2 * ((w : ℂ) / 2) = w
        ring
      continuous_toFun := by
        apply Continuous.subtype_mk
        fun_prop
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        fun_prop }
  let g : S0 → ℂ := fun z => 2 * (z.1 : ℂ)
  have hg : IsOpenEmbedding g :=
    (Metric.isOpen_ball.isOpenEmbedding_subtypeVal).comp e2.isOpenEmbedding
  let sg := hg.toOpenPartialHomeomorph
  have hrange : Set.range g = Metric.ball (0 : ℂ) 1 := by
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact (e2 z).2
    · intro hw
      exact ⟨e2.symm ⟨w, hw⟩, by
        have := e2.apply_symm_apply ⟨w, hw⟩
        exact congrArg Subtype.val this⟩
  have hphs : ph.symm.target = Set.univ := by simp [ph]
  have hpht : ph.symm.source = Set.range (fun w : S0 => Quot.mk (OrientableRel p 0) (w : ClosedUnitDisc)) := by
    simp [ph]
  have hsgs : sg.source = Set.univ := by simp [sg]
  have hsgt : sg.target = Metric.ball (0 : ℂ) 1 := by simp [sg, hrange]
  refine ⟨ph.symm.trans sg, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_target, hphs, hsgt]
    simp
  · intro z hz
    have hzS : z ∈ S0 := hz
    have hf : ph.symm (Quot.mk (OrientableRel p 0) z) = ⟨z, hzS⟩ :=
      hemb.toOpenPartialHomeomorph_left_inv (fun w : S0 => Quot.mk (OrientableRel p 0) (w : ClosedUnitDisc)) (x := ⟨z, hzS⟩)
    have hmem : Quot.mk (OrientableRel p 0) z ∈ ph.symm.source := by
      rw [hpht]
      exact ⟨⟨z, hzS⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.trans_source, hsgs]
      exact ⟨hmem, by simp⟩
    · show sg (ph.symm (Quot.mk (OrientableRel p 0) z)) = _
      rw [hf]
      simp [sg, g]
  · intro q hq
    rw [OpenPartialHomeomorph.trans_source] at hq
    have hq' := hq.1
    rw [hpht] at hq'
    obtain ⟨w, rfl⟩ := hq'
    exact ⟨w.1, w.2, rfl⟩

theorem s83sg_ray_eq {r r' : ℝ} {φ φ' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (hne : Complex.exp ((φ : ℂ) * Complex.I) ≠ Complex.exp ((φ' : ℂ) * Complex.I))
    (h : (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) = (r' : ℂ) * Complex.exp ((φ' : ℂ) * Complex.I)) :
    r = 0 ∧ r' = 0 := by
  have hn := congrArg norm h
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, mul_one, mul_one,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr,
    abs_of_nonneg hr'] at hn
  subst hn
  by_cases h0 : r = 0
  · exact ⟨h0, h0⟩
  · exfalso
    apply hne
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast h0
    exact mul_left_cancel₀ hr0 h

/-- The chord loop through the centre: out along the ray of angle `φ`, back along the ray of angle `φ'`. -/
theorem s83sg_chord_loop (p : ℕ) (φ φ' : ℝ)
    (hne : Complex.exp ((φ : ℂ) * Complex.I) ≠ Complex.exp ((φ' : ℂ) * Complex.I))
    (hglue : ∀ z z' : ClosedUnitDisc, (z : ℂ) = Complex.exp ((φ : ℂ) * Complex.I) →
      (z' : ℂ) = Complex.exp ((φ' : ℂ) * Complex.I) →
      Quot.mk (OrientableRel p 0) z = Quot.mk (OrientableRel p 0) z') :
    ∃ (L : ℝ → Quot (OrientableRel p 0)) (P : ℝ → ClosedUnitDisc), Continuous L ∧
      (∀ t, L (t + 1) = L t) ∧ (∀ t, L t = Quot.mk (OrientableRel p 0) (P (Int.fract t))) ∧
      (∀ u, 0 ≤ u → u ≤ 1 / 2 → (P u : ℂ) = ((2 * u : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) ∧
      (∀ u, 1 / 2 < u → u ≤ 1 →
        (P u : ℂ) = ((2 * (1 - u) : ℝ) : ℂ) * Complex.exp ((φ' : ℂ) * Complex.I)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∃ z : ClosedUnitDisc,
        (z : ℂ) = ((2 * t : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) ∧
          L t = Quot.mk (OrientableRel p 0) z) ∧
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∃ z : ClosedUnitDisc,
        (z : ℂ) = ((2 * (1 - t) : ℝ) : ℂ) * Complex.exp ((φ' : ℂ) * Complex.I) ∧
          L t = Quot.mk (OrientableRel p 0) z) ∧
      (∀ s t, L s = L t → ∃ n : ℤ, s = t + n) := by
  -- ray points of the closed disc
  have hnorm : ∀ θ r : ℝ, ‖(((Set.projIcc (0 : ℝ) 1 zero_le_one r : Set.Icc (0 : ℝ) 1) : ℝ) : ℂ) *
      Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ 1 := by
    intro θ r
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Set.projIcc (0 : ℝ) 1 zero_le_one r).2.1]
    exact (Set.projIcc (0 : ℝ) 1 zero_le_one r).2.2
  let rp : ℝ → ℝ → ClosedUnitDisc := fun θ r =>
    ⟨(((Set.projIcc (0 : ℝ) 1 zero_le_one r : Set.Icc (0 : ℝ) 1) : ℝ) : ℂ) *
      Complex.exp ((θ : ℂ) * Complex.I), mem_closedBall_zero_iff.2 (hnorm θ r)⟩
  have hrp_val : ∀ θ r : ℝ, 0 ≤ r → r ≤ 1 → (rp θ r : ℂ) = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    intro θ r h0 h1
    show (((Set.projIcc (0 : ℝ) 1 zero_le_one r : Set.Icc (0 : ℝ) 1) : ℝ) : ℂ) * _ = _
    rw [Set.projIcc_of_mem zero_le_one ⟨h0, h1⟩]
  have hrp_cont : ∀ θ : ℝ, Continuous (fun r : ℝ => rp θ r) := by
    intro θ
    apply Continuous.subtype_mk
    exact (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_projIcc)).mul continuous_const
  have hrp_zero : ∀ θ θ' : ℝ, rp θ 0 = rp θ' 0 := by
    intro θ θ'
    apply Subtype.ext
    rw [hrp_val θ 0 le_rfl zero_le_one, hrp_val θ' 0 le_rfl zero_le_one]
    simp
  let P : ℝ → ClosedUnitDisc := fun u => if u ≤ 1 / 2 then rp φ (2 * u) else rp φ' (2 * (1 - u))
  let α0 : ℝ → Quot (OrientableRel p 0) := fun u => Quot.mk (OrientableRel p 0) (P u)
  have hα0cont : Continuous α0 := by
    have h1 : Continuous (fun u : ℝ => Quot.mk (OrientableRel p 0) (rp φ (2 * u))) :=
      continuous_quot_mk.comp ((hrp_cont φ).comp (continuous_const.mul continuous_id))
    have h2 : Continuous (fun u : ℝ => Quot.mk (OrientableRel p 0) (rp φ' (2 * (1 - u)))) :=
      continuous_quot_mk.comp ((hrp_cont φ').comp (continuous_const.mul (continuous_const.sub continuous_id)))
    have h3 := Continuous.if_le h1 h2 continuous_id (continuous_const (y := (1 / 2 : ℝ))) (fun u hu => by
      have hu : u = 1 / 2 := hu
      have hu2 : 2 * u = 1 := by linarith
      have hu3 : 2 * (1 - u) = 1 := by linarith
      rw [hu2, hu3]
      refine hglue _ _ ?_ ?_
      · rw [hrp_val φ 1 zero_le_one le_rfl]; simp
      · rw [hrp_val φ' 1 zero_le_one le_rfl]; simp)
    convert h3 using 1
    funext u
    by_cases h : u ≤ 1 / 2
    · simp only [α0, P, id, if_pos h]
    · simp only [α0, P, id, if_neg h]
  have hα0eq : α0 0 = α0 1 := by
    show Quot.mk _ (P 0) = Quot.mk _ (P 1)
    have h0 : P 0 = rp φ 0 := by simp [P]
    have h1 : P 1 = rp φ' 0 := by
      simp only [P]
      rw [if_neg (by norm_num)]
      simp
    rw [h0, h1, hrp_zero]
  have hLcont : Continuous (α0 ∘ Int.fract) :=
    ContinuousOn.comp_fract'' hα0cont.continuousOn hα0eq
  have hPa : ∀ u, 0 ≤ u → u ≤ 1 / 2 → (P u : ℂ) = ((2 * u : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) := by
    intro u h0 h1
    simp only [P]
    rw [if_pos h1, hrp_val φ _ (by linarith) (by linarith)]
  have hPb : ∀ u, 1 / 2 < u → u ≤ 1 →
      (P u : ℂ) = ((2 * (1 - u) : ℝ) : ℂ) * Complex.exp ((φ' : ℂ) * Complex.I) := by
    intro u h0 h1
    simp only [P]
    rw [if_neg (not_le.2 h0), hrp_val φ' _ (by linarith) (by linarith)]
  have hfrac : ∀ t : ℝ, 0 ≤ t → t < 1 → Int.fract t = t := fun t h0 h1 => Int.fract_eq_self.2 ⟨h0, h1⟩
  refine ⟨fun t => α0 (Int.fract t), P, hLcont, ?_, fun t => rfl, hPa, hPb, ?_, ?_, ?_⟩
  · intro t
    show α0 (Int.fract (t + 1)) = α0 (Int.fract t)
    rw [Int.fract_add_one]
  · intro t ht
    refine ⟨P t, hPa t ht.1 ht.2, ?_⟩
    show α0 (Int.fract t) = α0 t
    rw [hfrac t ht.1 (by linarith [ht.2])]
  · intro t ht
    by_cases h1 : t = 1
    · subst h1
      refine ⟨rp φ' 0, ?_, ?_⟩
      · rw [hrp_val φ' 0 le_rfl zero_le_one]; simp
      · show α0 (Int.fract 1) = _
        rw [Int.fract_one]
        show Quot.mk _ (P 0) = _
        have h0 : P 0 = rp φ 0 := by simp [P]
        rw [h0, hrp_zero]
    · have ht1 : t < 1 := lt_of_le_of_ne ht.2 h1
      rcases ht.1.lt_or_eq with h2 | h2
      · refine ⟨P t, hPb t h2 ht.2, ?_⟩
        show α0 (Int.fract t) = α0 t
        rw [hfrac t (by linarith) ht1]
      · subst h2
        refine ⟨rp φ' 1, ?_, ?_⟩
        · rw [hrp_val φ' 1 zero_le_one le_rfl]; norm_num
        · show α0 (Int.fract (1 / 2)) = _
          rw [hfrac _ (by norm_num) (by norm_num)]
          show Quot.mk _ (P (1 / 2)) = _
          have : P (1 / 2) = rp φ 1 := by
            simp only [P]
            rw [if_pos le_rfl]
            norm_num
          rw [this]
          refine hglue _ _ ?_ ?_
          · rw [hrp_val φ 1 zero_le_one le_rfl]; simp
          · rw [hrp_val φ' 1 zero_le_one le_rfl]; simp
  · -- simplicity
    intro s t hst
    have hnP : ∀ w : ℝ, 0 ≤ w → w < 1 → ‖(P w : ℂ)‖ = if w ≤ 1 / 2 then 2 * w else 2 * (1 - w) := by
      intro w h0 h1
      by_cases hw : w ≤ 1 / 2
      · rw [if_pos hw, hPa w h0 hw, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      · rw [if_neg hw, hPb w (not_le.1 hw) h1.le, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have key : ∀ u v : ℝ, 0 ≤ u → u < 1 → 0 ≤ v → v < 1 →
        Quot.mk (OrientableRel p 0) (P u) = Quot.mk (OrientableRel p 0) (P v) → u = v := by
      intro u v hu0 hu1 hv0 hv1 h
      have hE := Quot.eqvGen_exact h
      rcases s78dg_cs_eqv_boundary hE with heq | ⟨h1, h2⟩
      · have hc : (P u : ℂ) = (P v : ℂ) := congrArg Subtype.val heq
        have hex : ∀ ψ : ℝ, Complex.exp ((ψ : ℂ) * Complex.I) ≠ 0 := fun ψ => Complex.exp_ne_zero _
        by_cases hu' : u ≤ 1 / 2 <;> by_cases hv' : v ≤ 1 / 2
        · rw [hPa u hu0 hu', hPa v hv0 hv'] at hc
          have := mul_right_cancel₀ (hex φ) hc
          have := Complex.ofReal_injective this
          linarith
        · rw [hPa u hu0 hu', hPb v (not_le.1 hv') hv1.le] at hc
          have := (s83sg_ray_eq (by linarith) (by linarith) hne hc).2
          linarith
        · rw [hPb u (not_le.1 hu') hu1.le, hPa v hv0 hv'] at hc
          have := (s83sg_ray_eq (by linarith) (by linarith) hne hc.symm).2
          linarith
        · rw [hPb u (not_le.1 hu') hu1.le, hPb v (not_le.1 hv') hv1.le] at hc
          have := mul_right_cancel₀ (hex φ') hc
          have := Complex.ofReal_injective this
          linarith
      · rw [hnP u hu0 hu1] at h1
        rw [hnP v hv0 hv1] at h2
        have hu2 : u = 1 / 2 := by
          by_cases hu' : u ≤ 1 / 2
          · rw [if_pos hu'] at h1; linarith
          · rw [if_neg hu'] at h1; exfalso; push Not at hu'; linarith
        have hv2 : v = 1 / 2 := by
          by_cases hv' : v ≤ 1 / 2
          · rw [if_pos hv'] at h2; linarith
          · rw [if_neg hv'] at h2; exfalso; push Not at hv'; linarith
        rw [hu2, hv2]
    have hfs := key (Int.fract s) (Int.fract t) (Int.fract_nonneg s) (Int.fract_lt_one s)
      (Int.fract_nonneg t) (Int.fract_lt_one t) hst
    refine ⟨⌊s⌋ - ⌊t⌋, ?_⟩
    have h1 := Int.self_sub_floor s
    have h2 := Int.self_sub_floor t
    push_cast
    linarith

/-- Two angles less than a full turn apart give different unit vectors. -/
theorem s83sg_exp_ne {φ φ' : ℝ} (h1 : φ < φ') (h2 : φ' < φ + 2 * Real.pi) :
    Complex.exp ((φ : ℂ) * Complex.I) ≠ Complex.exp ((φ' : ℂ) * Complex.I) := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have key : φ = φ' + n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simp at this
    linarith
  have h3 : (n : ℝ) < 0 := by
    by_contra hc
    push_neg at hc
    nlinarith [Real.pi_pos]
  have h4 : -1 < (n : ℝ) := by
    by_contra hc
    push_neg at hc
    nlinarith [Real.pi_pos]
  have h3' : n < 0 := by exact_mod_cast h3
  have h4' : -1 < n := by exact_mod_cast h4
  omega

/-- A boundary point of the disc at position `u` (units `2π/(4g)`) is the point `Ψ (1, u)` of `Q`. -/
theorem s83sg_glue_pt (g : ℕ) (hp : 1 ≤ g) (u : ℝ) (z : ClosedUnitDisc)
    (hz : (z : ℂ) = Complex.exp (((2 * Real.pi * u / (4 * g) : ℝ) : ℂ) * Complex.I)) :
    Quot.mk (OrientableRel g 0) z = ((s78dg_cs_Psi_fun g hp (⟨1, zero_lt_one, le_rfl⟩, u) :
      ↥(s78dg_cs_U g 0)) : Quot (OrientableRel g 0)) := by
  obtain ⟨z', hz', h⟩ := s78dg_cs_Psi_spec g hp ⟨1, zero_lt_one, le_rfl⟩ u
  rw [h]
  congr 1
  apply Subtype.ext
  rw [hz, hz']
  show _ = ((1 : ℝ) : ℂ) * _
  rw [Complex.ofReal_one, one_mul]
  congr 1
  push_cast
  ring

/-- The chord through the midpoints of the two `a_{g-1}` sides: its two boundary endpoints are glued. -/
theorem s83sg_chord_glue_a (g : ℕ) (hg : 1 < g) (z z' : ClosedUnitDisc)
    (hz : (z : ℂ) = Complex.exp (((2 * Real.pi * (4 * ((g : ℝ) - 1) + 0 + 1 / 2) / (4 * g) : ℝ) : ℂ) *
      Complex.I))
    (hz' : (z' : ℂ) = Complex.exp (((2 * Real.pi * (4 * ((g : ℝ) - 1) + 2 + 1 / 2) / (4 * g) : ℝ) : ℂ) *
      Complex.I)) :
    Quot.mk (OrientableRel g 0) z = Quot.mk (OrientableRel g 0) z' := by
  have hp : 1 ≤ g := by omega
  rw [s83sg_glue_pt g hp _ z hz, s83sg_glue_pt g hp _ z' hz']
  let i₀ : Fin g := ⟨g - 1, by omega⟩
  have hi : ((i₀ : ℕ) : ℝ) = (g : ℝ) - 1 := by
    show (((g - 1 : ℕ)) : ℝ) = _
    rw [Nat.cast_sub hp, Nat.cast_one]
  have e1 : 4 * ((g : ℝ) - 1) + 0 + 1 / 2 = 4 * ((i₀ : ℕ) : ℝ) + 1 / 2 := by rw [hi]; ring
  have e2 : 4 * ((g : ℝ) - 1) + 2 + 1 / 2 = 4 * ((i₀ : ℕ) : ℝ) + 3 - 1 / 2 := by rw [hi]; ring
  rw [e1, e2]
  exact congrArg Subtype.val
    (s78dg_cs_Psi_rel_a g hp ⟨1, zero_lt_one, le_rfl⟩ rfl i₀ (1 / 2) (by norm_num) (by norm_num))

/-- The chord through the midpoints of the two `b_{g-1}` sides: its two boundary endpoints are glued. -/
theorem s83sg_chord_glue_b (g : ℕ) (hg : 1 < g) (z z' : ClosedUnitDisc)
    (hz : (z : ℂ) = Complex.exp (((2 * Real.pi * (4 * ((g : ℝ) - 1) + 1 + 1 / 2) / (4 * g) : ℝ) : ℂ) *
      Complex.I))
    (hz' : (z' : ℂ) = Complex.exp (((2 * Real.pi * (4 * ((g : ℝ) - 1) + 3 + 1 / 2) / (4 * g) : ℝ) : ℂ) *
      Complex.I)) :
    Quot.mk (OrientableRel g 0) z = Quot.mk (OrientableRel g 0) z' := by
  have hp : 1 ≤ g := by omega
  rw [s83sg_glue_pt g hp _ z hz, s83sg_glue_pt g hp _ z' hz']
  let i₀ : Fin g := ⟨g - 1, by omega⟩
  have hi : ((i₀ : ℕ) : ℝ) = (g : ℝ) - 1 := by
    show (((g - 1 : ℕ)) : ℝ) = _
    rw [Nat.cast_sub hp, Nat.cast_one]
  have e1 : 4 * ((g : ℝ) - 1) + 1 + 1 / 2 = 4 * ((i₀ : ℕ) : ℝ) + 1 + 1 / 2 := by rw [hi]
  have e2 : 4 * ((g : ℝ) - 1) + 3 + 1 / 2 = 4 * ((i₀ : ℕ) : ℝ) + 4 - 1 / 2 := by rw [hi]; ring
  rw [e1, e2]
  exact congrArg Subtype.val
    (s78dg_cs_Psi_rel_b g hp ⟨1, zero_lt_one, le_rfl⟩ rfl i₀ (1 / 2) (by norm_num) (by norm_num))

/-- Norm of a point on a ray. -/
theorem s83sg_ray_norm' (r θ : ℝ) (hr : 0 ≤ r) : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

/-- Two chord loops (rays at angles `θa, θa'` resp. `θb, θb'`, all four directions different) whose boundary
midpoints are different points of `Q` meet only at the centre. -/
theorem s83sg_chord_meet (g : ℕ) (Pα Pβ : ℝ → ClosedUnitDisc) (θa θa' θb θb' : ℝ)
    (hne : ∀ φ ∈ ({θa, θa'} : Set ℝ), ∀ φ' ∈ ({θb, θb'} : Set ℝ),
      Complex.exp ((φ : ℂ) * Complex.I) ≠ Complex.exp ((φ' : ℂ) * Complex.I))
    (hPa : ∀ u, 0 ≤ u → u ≤ 1 / 2 → (Pα u : ℂ) = ((2 * u : ℝ) : ℂ) * Complex.exp ((θa : ℂ) * Complex.I))
    (hPa' : ∀ u, 1 / 2 < u → u ≤ 1 →
      (Pα u : ℂ) = ((2 * (1 - u) : ℝ) : ℂ) * Complex.exp ((θa' : ℂ) * Complex.I))
    (hPb : ∀ u, 0 ≤ u → u ≤ 1 / 2 → (Pβ u : ℂ) = ((2 * u : ℝ) : ℂ) * Complex.exp ((θb : ℂ) * Complex.I))
    (hPb' : ∀ u, 1 / 2 < u → u ≤ 1 →
      (Pβ u : ℂ) = ((2 * (1 - u) : ℝ) : ℂ) * Complex.exp ((θb' : ℂ) * Complex.I))
    (hmid : Quot.mk (OrientableRel g 0) (Pα (1 / 2)) ≠ Quot.mk (OrientableRel g 0) (Pβ (1 / 2)))
    {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (h : Quot.mk (OrientableRel g 0) (Pα u) = Quot.mk (OrientableRel g 0) (Pβ v)) : u = 0 ∧ v = 0 := by
  -- each value is a ray point `r e^{iφ}` with the radius determining the parameter
  have hA : ∃ r φ : ℝ, 0 ≤ r ∧ φ ∈ ({θa, θa'} : Set ℝ) ∧ (Pα u : ℂ) = (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) ∧
      (r = 0 → u = 0) ∧ (r = 1 → u = 1 / 2) := by
    by_cases hu : u ≤ 1 / 2
    · exact ⟨2 * u, θa, by linarith, Or.inl rfl, hPa u hu0 hu, fun h => by linarith, fun h => by linarith⟩
    · exact ⟨2 * (1 - u), θa', by linarith, Or.inr rfl, hPa' u (not_le.1 hu) hu1.le,
        fun h => by linarith, fun h => by linarith [not_le.1 hu]⟩
  have hB : ∃ r φ : ℝ, 0 ≤ r ∧ φ ∈ ({θb, θb'} : Set ℝ) ∧ (Pβ v : ℂ) = (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) ∧
      (r = 0 → v = 0) ∧ (r = 1 → v = 1 / 2) := by
    by_cases hv : v ≤ 1 / 2
    · exact ⟨2 * v, θb, by linarith, Or.inl rfl, hPb v hv0 hv, fun h => by linarith, fun h => by linarith⟩
    · exact ⟨2 * (1 - v), θb', by linarith, Or.inr rfl, hPb' v (not_le.1 hv) hv1.le,
        fun h => by linarith, fun h => by linarith [not_le.1 hv]⟩
  obtain ⟨r, φ, hr, hφ, hPu, hr0, hr1⟩ := hA
  obtain ⟨r', φ', hr', hφ', hPv, hr0', hr1'⟩ := hB
  rcases s78dg_cs_eqv_boundary (Quot.eqvGen_exact h) with heq | ⟨h1, h2⟩
  · have hc : (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) = (r' : ℂ) * Complex.exp ((φ' : ℂ) * Complex.I) := by
      rw [← hPu, ← hPv, heq]
    obtain ⟨h0, h0'⟩ := s83sg_ray_eq hr hr' (hne φ hφ φ' hφ') hc
    exact ⟨hr0 h0, hr0' h0'⟩
  · rw [hPu, s83sg_ray_norm' r φ hr] at h1
    rw [hPv, s83sg_ray_norm' r' φ' hr'] at h2
    have hu := hr1 h1
    have hv := hr1' h2
    subst hu
    subst hv
    exact absurd h hmid

/-- Chart facts for a chord loop. -/
theorem s83sg_chord_chart (p : ℕ) (e : OpenPartialHomeomorph (Quot (OrientableRel p 0)) ℂ)
    (hE1 : ∀ z : ClosedUnitDisc, ‖(z : ℂ)‖ < 1 / 2 →
      Quot.mk (OrientableRel p 0) z ∈ e.source ∧ e (Quot.mk (OrientableRel p 0) z) = 2 * (z : ℂ))
    (hE2 : ∀ q ∈ e.source, ∃ z : ClosedUnitDisc, ‖(z : ℂ)‖ < 1 / 2 ∧ q = Quot.mk (OrientableRel p 0) z)
    (φ φ' : ℝ) (L : ℝ → Quot (OrientableRel p 0)) (P : ℝ → ClosedUnitDisc)
    (hL : ∀ t, L t = Quot.mk (OrientableRel p 0) (P (Int.fract t)))
    (hPa : ∀ u, 0 ≤ u → u ≤ 1 / 2 → (P u : ℂ) = ((2 * u : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
    (hPb : ∀ u, 1 / 2 < u → u ≤ 1 →
      (P u : ℂ) = ((2 * (1 - u) : ℝ) : ℂ) * Complex.exp ((φ' : ℂ) * Complex.I)) :
    (∀ t : ℝ, L t ∈ e.source ↔ ∃ n : ℤ, |t - n| < 1 / 4) ∧
      (∀ t : ℝ, 0 < t → t < 1 / 4 →
        e (L t) = ((t / (1 / 4) : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) ∧
      (∀ t : ℝ, -(1 / 4) < t → t < 0 →
        e (L t) = ((-t / (1 / 4) : ℝ) : ℂ) * Complex.exp ((φ' : ℂ) * Complex.I)) ∧
      L 0 ∈ e.source ∧ e (L 0) = 0 := by
  have hnP : ∀ w : ℝ, 0 ≤ w → w < 1 → ‖(P w : ℂ)‖ = if w ≤ 1 / 2 then 2 * w else 2 * (1 - w) := by
    intro w h0 h1
    by_cases hw : w ≤ 1 / 2
    · rw [if_pos hw, hPa w h0 hw, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    · rw [if_neg hw, hPb w (not_le.1 hw) h1.le, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have h0 : L 0 = Quot.mk (OrientableRel p 0) (P 0) := by rw [hL]; simp
  have hP0 : ‖(P 0 : ℂ)‖ = 0 := by
    rw [hnP 0 le_rfl one_pos]; simp
  have hP0z : (P 0 : ℂ) = 0 := norm_eq_zero.1 hP0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    constructor
    · intro ht
      obtain ⟨z, hz, hq⟩ := hE2 _ ht
      rw [hL] at hq
      have hu0 := Int.fract_nonneg t
      have hu1 := Int.fract_lt_one t
      have hzP : z = P (Int.fract t) := by
        have hE := Quot.eqvGen_exact hq.symm
        exact s78dg_cs_interior_class (by linarith : ‖(z : ℂ)‖ < 1) hE
      rw [hzP, hnP _ hu0 hu1] at hz
      by_cases hu : Int.fract t ≤ 1 / 2
      · rw [if_pos hu] at hz
        refine ⟨⌊t⌋, ?_⟩
        rw [abs_lt]
        have := Int.self_sub_floor t
        constructor <;> linarith
      · rw [if_neg hu] at hz
        refine ⟨⌊t⌋ + 1, ?_⟩
        rw [abs_lt]
        have := Int.self_sub_floor t
        push_cast
        constructor <;> linarith
    · rintro ⟨n, hn⟩
      rw [hL]
      have hu0 := Int.fract_nonneg t
      have hu1 := Int.fract_lt_one t
      have hfl := Int.self_sub_floor t
      rw [abs_lt] at hn
      have hn1 : (n : ℝ) ≤ ⌊t⌋ + 1 := by
        have : n ≤ ⌊t⌋ + 1 := by
          by_contra hc
          have h2 : (⌊t⌋ : ℝ) + 2 ≤ n := by exact_mod_cast (by omega : ⌊t⌋ + 2 ≤ n)
          linarith [Int.lt_floor_add_one t, hn.2]
        exact_mod_cast this
      have hn2 : (⌊t⌋ : ℝ) ≤ n + 1 := by
        have : ⌊t⌋ ≤ n + 1 := by
          by_contra hc
          have h2 : (n : ℝ) + 2 ≤ ⌊t⌋ := by exact_mod_cast (by omega : n + 2 ≤ ⌊t⌋)
          linarith [Int.floor_le t, hn.1]
        exact_mod_cast this
      have hcases : n = ⌊t⌋ ∨ n = ⌊t⌋ + 1 := by
        have hnn1 : n ≤ ⌊t⌋ + 1 := by exact_mod_cast hn1
        have hnn2 : ⌊t⌋ ≤ n + 1 := by exact_mod_cast hn2
        by_contra hc
        push Not at hc
        have : n = ⌊t⌋ - 1 ∨ n ≤ ⌊t⌋ - 2 ∨ n ≥ ⌊t⌋ + 2 := by omega
        rcases this with h | h | h
        · have : (n : ℝ) = ⌊t⌋ - 1 := by rw [h]; push_cast; ring
          rw [this] at hn
          linarith [hn.1, Int.floor_le t]
        · have : (n : ℝ) ≤ ⌊t⌋ - 2 := by exact_mod_cast h
          linarith [hn.1, Int.floor_le t]
        · exfalso; omega
      rcases hcases with rfl | rfl
      · have hlt : ‖(P (Int.fract t) : ℂ)‖ < 1 / 2 := by
          rw [hnP _ hu0 hu1, if_pos (by linarith)]
          linarith
        exact (hE1 _ hlt).1
      · have hlt : ‖(P (Int.fract t) : ℂ)‖ < 1 / 2 := by
          rw [hnP _ hu0 hu1, if_neg (by push_cast at hn; linarith)]
          push_cast at hn
          linarith
        exact (hE1 _ hlt).1
  · intro t ht0 ht1
    rw [hL, Int.fract_eq_self.2 ⟨ht0.le, by linarith⟩]
    have hlt : ‖(P t : ℂ)‖ < 1 / 2 := by
      rw [hnP _ ht0.le (by linarith), if_pos (by linarith)]
      linarith
    rw [(hE1 _ hlt).2, hPa t ht0.le (by linarith)]
    push_cast
    ring
  · intro t ht0 ht1
    have hfr : Int.fract t = 1 + t := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, -1, ?_⟩
      push_cast; ring
    rw [hL, hfr]
    have hlt : ‖(P (1 + t) : ℂ)‖ < 1 / 2 := by
      rw [hnP _ (by linarith) (by linarith), if_neg (by linarith)]
      linarith
    rw [(hE1 _ hlt).2, hPb (1 + t) (by linarith) (by linarith)]
    push_cast
    ring
  · rw [h0]
    have hlt : ‖(P 0 : ℂ)‖ < 1 / 2 := by rw [hP0]; norm_num
    exact (hE1 _ hlt).1
  · rw [h0]
    have hlt : ‖(P 0 : ℂ)‖ < 1 / 2 := by rw [hP0]; norm_num
    rw [(hE1 _ hlt).2, hP0z]
    simp

/-- **[a+b, chord model]**  In the closed normal form `Q` of genus `g > 1` there are two loops `α, β` through the
centre `c₀` of the 2-cell that are simple, meet only at `c₀`, and are, in a chart `e` at `c₀` (a disc), the rays
at angles `θ₀ < θ₁ < θ₂ < θ₃ < θ₀ + 2π` (so `α` leaves along `θ₀` and returns along `θ₂`; `β` leaves along `θ₁` and
returns along `θ₃`: they alternate around `c₀`).  Their classes in `π₁(Q, c₀)` are, under a suitable isomorphism
`e₀ : π₁(Q, c₀) ≃* surfaceGroup g`, the conjugates `w b^{s₁} w⁻¹` and `w (b^{s₂} a^{s₃} b^{-s₂}) w⁻¹` of the last
generators (`a = of (inl last)`, `b = of (inr last)`, signs `s_i = ±1` fixed by the orientation conventions). -/
theorem s83sg_chord_model (g : ℕ) (hg : 1 < g) :
    ∃ (c₀ : Quot (OrientableRel g 0)) (α β : ℝ → Quot (OrientableRel g 0))
      (e : OpenPartialHomeomorph (Quot (OrientableRel g 0)) ℂ) (ε θ₀ θ₁ θ₂ θ₃ : ℝ)
      (e₀ : FundamentalGroup (Quot (OrientableRel g 0)) c₀ ≃* surfaceGroup g) (w ga gb : surfaceGroup g)
      (s₁ s₂ s₃ : ℤ),
      ga = (PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩ : Fin g ⊕ Fin g) : surfaceGroup g) ∧
      gb = (PresentedGroup.of (Sum.inr ⟨g - 1, by omega⟩ : Fin g ⊕ Fin g) : surfaceGroup g) ∧
      Continuous α ∧ Continuous β ∧ (∀ t, α (t + 1) = α t) ∧ (∀ t, β (t + 1) = β t) ∧ α 0 = c₀ ∧ β 0 = c₀ ∧
      (∀ s t, α s = α t → ∃ n : ℤ, s = t + n) ∧ (∀ s t, β s = β t → ∃ n : ℤ, s = t + n) ∧
      (∀ s t, α s = β t → (∃ m : ℤ, s = m) ∧ ∃ n : ℤ, t = n) ∧
      c₀ ∈ e.source ∧ e c₀ = 0 ∧ e.target = Metric.ball 0 1 ∧ 0 < ε ∧ ε < 1 / 2 ∧
      θ₀ < θ₁ ∧ θ₁ < θ₂ ∧ θ₂ < θ₃ ∧ θ₃ < θ₀ + 2 * Real.pi ∧
      (∀ t : ℝ, α t ∈ e.source ↔ ∃ n : ℤ, |t - n| < ε) ∧ (∀ t : ℝ, β t ∈ e.source ↔ ∃ n : ℤ, |t - n| < ε) ∧
      (∀ t, 0 < t → t < ε → e (α t) = ((t / ε : ℝ) : ℂ) * Complex.exp (θ₀ * Complex.I)) ∧
      (∀ t, -ε < t → t < 0 → e (α t) = ((-t / ε : ℝ) : ℂ) * Complex.exp (θ₂ * Complex.I)) ∧
      (∀ t, 0 < t → t < ε → e (β t) = ((t / ε : ℝ) : ℂ) * Complex.exp (θ₁ * Complex.I)) ∧
      (∀ t, -ε < t → t < 0 → e (β t) = ((-t / ε : ℝ) : ℂ) * Complex.exp (θ₃ * Complex.I)) ∧
      (s₁ = 1 ∨ s₁ = -1) ∧ (s₂ = 1 ∨ s₂ = -1) ∧ (s₃ = 1 ∨ s₃ = -1) ∧
      (∀ L : Path c₀ c₀, (∀ t : I, L t = α t) →
        e₀ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = w * gb ^ s₁ * w⁻¹) ∧
      (∀ L : Path c₀ c₀, (∀ t : I, L t = β t) →
        e₀ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) =
          w * (gb ^ s₂ * ga ^ s₃ * gb ^ (-s₂)) * w⁻¹) := by
  have hgr : (2 : ℝ) ≤ g := by exact_mod_cast hg
  let θ₀ : ℝ := 2 * Real.pi * (4 * ((g : ℝ) - 1) + 0 + 1 / 2) / (4 * g)
  let θ₁ : ℝ := 2 * Real.pi * (4 * ((g : ℝ) - 1) + 1 + 1 / 2) / (4 * g)
  let θ₂ : ℝ := 2 * Real.pi * (4 * ((g : ℝ) - 1) + 2 + 1 / 2) / (4 * g)
  let θ₃ : ℝ := 2 * Real.pi * (4 * ((g : ℝ) - 1) + 3 + 1 / 2) / (4 * g)
  have h4g : (0 : ℝ) < 4 * g := by positivity
  have hlt : ∀ a b : ℝ, a < b → 2 * Real.pi * (4 * ((g : ℝ) - 1) + a + 1 / 2) / (4 * g) <
      2 * Real.pi * (4 * ((g : ℝ) - 1) + b + 1 / 2) / (4 * g) := fun a b hab =>
    (div_lt_div_iff_of_pos_right h4g).2 (by nlinarith [Real.pi_pos])
  have h01 : θ₀ < θ₁ := hlt 0 1 (by norm_num)
  have h12 : θ₁ < θ₂ := hlt 1 2 (by norm_num)
  have h23 : θ₂ < θ₃ := hlt 2 3 (by norm_num)
  have h30 : θ₃ < θ₀ + 2 * Real.pi := by
    have key : θ₃ = θ₀ + 2 * Real.pi * (3 / (4 * g)) := by
      show 2 * Real.pi * (4 * ((g : ℝ) - 1) + 3 + 1 / 2) / (4 * g) =
        2 * Real.pi * (4 * ((g : ℝ) - 1) + 0 + 1 / 2) / (4 * g) + 2 * Real.pi * (3 / (4 * g))
      field_simp
      ring
    have h3 : 3 / (4 * (g : ℝ)) < 1 := (div_lt_one h4g).2 (by linarith)
    rw [key]
    nlinarith [Real.pi_pos]
  have hne02 : Complex.exp ((θ₀ : ℂ) * Complex.I) ≠ Complex.exp ((θ₂ : ℂ) * Complex.I) :=
    s83sg_exp_ne (by linarith) (by linarith)
  have hne13 : Complex.exp ((θ₁ : ℂ) * Complex.I) ≠ Complex.exp ((θ₃ : ℂ) * Complex.I) :=
    s83sg_exp_ne (by linarith) (by linarith)
  obtain ⟨α, Pα, hαc, hαp, hαL, hPa, hPa', hα1, hα2, hαs⟩ :=
    s83sg_chord_loop g θ₀ θ₂ hne02 (fun z z' hz hz' => s83sg_chord_glue_a g hg z z' hz hz')
  obtain ⟨β, Pβ, hβc, hβp, hβL, hPb, hPb', hβ1, hβ2, hβs⟩ :=
    s83sg_chord_loop g θ₁ θ₃ hne13 (fun z z' hz hz' => s83sg_chord_glue_b g hg z z' hz hz')
  obtain ⟨e₀, ga, gb, s₁, s₂, s₃, hga, hgb, hs₁, hs₂, hs₃, hcα, hcβ⟩ :=
    s83sg_chord_classes g hg α β hα1 hα2 hβ1 hβ2
  obtain ⟨e, het, hE1, hE2⟩ := s83sg_chart_half g
  obtain ⟨hαe, hαp', hαm', hα0e, he0⟩ := s83sg_chord_chart g e hE1 hE2 θ₀ θ₂ α Pα hαL hPa hPa'
  obtain ⟨hβe, hβp', hβm', -, -⟩ := s83sg_chord_chart g e hE1 hE2 θ₁ θ₃ β Pβ hβL hPb hPb'
  have hP0 : ∀ (P : ℝ → ClosedUnitDisc) (φ : ℝ),
      (∀ u, 0 ≤ u → u ≤ 1 / 2 → (P u : ℂ) = ((2 * u : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) →
      (P 0 : ℂ) = 0 := fun P φ h => by
    rw [h 0 le_rfl (by norm_num)]
    simp
  have hβ0 : β 0 = α 0 := by
    rw [hβL, hαL, Int.fract_zero]
    congr 1
    exact Subtype.ext ((hP0 _ _ hPb).trans (hP0 _ _ hPa).symm)
  have hhalf : ∀ (P : ℝ → ClosedUnitDisc) (φ : ℝ),
      (∀ u, 0 ≤ u → u ≤ 1 / 2 → (P u : ℂ) = ((2 * u : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) →
      (P (1 / 2) : ℂ) = Complex.exp ((φ : ℂ) * Complex.I) := fun P φ h => by
    rw [h (1 / 2) (by norm_num) le_rfl, show (2 * (1 / 2) : ℝ) = 1 by norm_num, Complex.ofReal_one, one_mul]
  have hmid : Quot.mk (OrientableRel g 0) (Pα (1 / 2)) ≠ Quot.mk (OrientableRel g 0) (Pβ (1 / 2)) :=
    s83sg_midpoints_distinct g hg _ _ (hhalf _ _ hPa) (hhalf _ _ hPb)
  have hneAll : ∀ φ ∈ ({θ₀, θ₂} : Set ℝ), ∀ φ' ∈ ({θ₁, θ₃} : Set ℝ),
      Complex.exp ((φ : ℂ) * Complex.I) ≠ Complex.exp ((φ' : ℂ) * Complex.I) := by
    intro φ hφ φ' hφ'
    rcases hφ with rfl | rfl <;> rcases hφ' with rfl | rfl
    · exact s83sg_exp_ne (by linarith) (by linarith)
    · exact s83sg_exp_ne (by linarith) (by linarith)
    · exact (s83sg_exp_ne (by linarith) (by linarith)).symm
    · exact s83sg_exp_ne (by linarith) (by linarith)
  have hmeet : ∀ s t, α s = β t → (∃ m : ℤ, s = m) ∧ ∃ n : ℤ, t = n := by
    intro s t hst
    rw [hαL, hβL] at hst
    obtain ⟨hs0, ht0⟩ := s83sg_chord_meet g Pα Pβ θ₀ θ₂ θ₁ θ₃ hneAll hPa hPa' hPb hPb' hmid
      (Int.fract_nonneg s) (Int.fract_lt_one s) (Int.fract_nonneg t) (Int.fract_lt_one t) hst
    exact ⟨⟨⌊s⌋, by linarith [Int.floor_add_fract s]⟩, ⟨⌊t⌋, by linarith [Int.floor_add_fract t]⟩⟩
  refine ⟨α 0, α, β, e, 1 / 4, θ₀, θ₁, θ₂, θ₃, e₀, 1, ga, gb, s₁, s₂, s₃, hga, hgb, hαc, hβc, hαp, hβp,
    rfl, hβ0, hαs, hβs, hmeet, hα0e, he0, het, by norm_num, by norm_num, h01, h12, h23, h30, hαe, hβe,
    hαp', hαm', hβp', hβm', hs₁, hs₂, hs₃, fun L hL => ?_, fun L hL => ?_⟩
  · rw [hcα L hL]
    simp
  · rw [hcβ L hL]
    simp

end LiZhongQC
