import LiZhongQC.Lemmas.Conformal

/-!
# Automorphisms of the unit disc

The classification of the conformal self-maps of `Δ`, which the book uses from §14 on and which
Mathlib lists as an explicit TODO in `Mathlib/Analysis/Complex/Schwarz.lean`:

* the Blaschke factor `M_a(z) = (z - a)/(1 - ā z)` is a conformal map of `Δ` onto itself
                                                              — `blaschke`, `isConformalOnto_blaschke`;
* every conformal map of `Δ` onto itself is a Möbius transformation
                                                              — `exists_mobius_of_isConformalOnto_unitDisc`.

The proof is the classical one: `M_a` moves `a` to `0`, so `g = h ∘ M_a⁻¹` fixes `0`; the Schwarz
lemma applied to `g` and to `g⁻¹` forces `‖g z‖ = ‖z‖`, and the equality case of the Schwarz lemma
(`Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div`) makes `g` a rotation.
-/

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace LiZhongQC

/-! ### The Blaschke factor -/

/-- The Blaschke factor `M_a(z) = (z - a)/(1 - ā z)`. -/
def blaschke (a z : ℂ) : ℂ := (z - a) / (1 - conj a * z)

/-- The algebraic identity behind the Blaschke factor: `|1 - āz|² - |z - a|² = (1-|z|²)(1-|a|²)`. -/
theorem normSq_blaschke_key (a z : ℂ) :
    normSq (1 - conj a * z) - normSq (z - a) = (1 - normSq z) * (1 - normSq a) := by
  simp only [normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

/-- The denominator of the Blaschke factor does not vanish on the disc. -/
theorem blaschke_den_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    (1 : ℂ) - conj a * z ≠ 0 := by
  intro hcon
  have h1 : normSq (1 - conj a * z) = 0 := by rw [hcon, map_zero]
  have h2 := normSq_blaschke_key a z
  rw [h1] at h2
  have hza : normSq z < 1 := normSq_lt_one_iff.mpr hz
  have haa : normSq a < 1 := normSq_lt_one_iff.mpr ha
  nlinarith [normSq_nonneg (z - a)]

/-- The Blaschke factor maps the unit disc into itself. -/
theorem blaschke_mem_unitDisc {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖blaschke a z‖ < 1 := by
  have hden := blaschke_den_ne_zero ha hz
  have hza : normSq z < 1 := normSq_lt_one_iff.mpr hz
  have haa : normSq a < 1 := normSq_lt_one_iff.mpr ha
  have hkey := normSq_blaschke_key a z
  have hlt : normSq (z - a) < normSq (1 - conj a * z) := by nlinarith
  rw [← normSq_lt_one_iff, blaschke, normSq_div]
  rw [div_lt_one (normSq_pos.mpr hden)]
  exact hlt

/-- The Blaschke factor sends `a` to `0`. -/
@[simp] theorem blaschke_self (a : ℂ) : blaschke a a = 0 := by simp [blaschke]

/-- `M_{-a}` inverts `M_a` on the disc. -/
theorem blaschke_neg_blaschke {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    blaschke (-a) (blaschke a z) = z := by
  have hden := blaschke_den_ne_zero ha hz
  have hden' : (1 : ℂ) - z * conj a ≠ 0 := by rw [mul_comm]; exact hden
  have hne : (1 : ℂ) - conj a * a ≠ 0 := by
    have haa : normSq a < 1 := normSq_lt_one_iff.mpr ha
    intro hcon
    have hre := congrArg Complex.re hcon
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.zero_re] at hre
    rw [normSq_apply] at haa
    nlinarith
  have key : (1 : ℂ) - conj (-a) * blaschke a z = (1 - conj a * a) / (1 - conj a * z) := by
    simp only [blaschke, map_neg, neg_mul, sub_neg_eq_add]
    field_simp
    ring
  have keynum : blaschke a z - -a = z * (1 - conj a * a) / (1 - conj a * z) := by
    simp only [blaschke, sub_neg_eq_add]
    field_simp
    ring
  have hden2 : (1 : ℂ) - conj (-a) * blaschke a z ≠ 0 := by
    rw [key]; exact div_ne_zero hne hden
  rw [blaschke, div_eq_iff hden2, keynum, key, mul_div_assoc]

/-! ### A conformal self-map of `Δ` fixing `0` is a rotation -/

/-- The Schwarz lemma applied to `g` and to `g⁻¹` forces `‖g z‖ = ‖z‖`, and its equality case then
makes `g` a rotation. -/
theorem exists_rotation_of_isConformalOnto_fix_zero {g : ℂ → ℂ}
    (hg : IsConformalOnto g unitDisc unitDisc) (hg0 : g 0 = 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ EqOn g (fun z => c * z) unitDisc := by
  have h0mem : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hmapsTo := hg.mapsTo
  have hd1 : DifferentiableOn ℂ g (ball (0 : ℂ) 1) := hg.1
  have hmaps : MapsTo g (ball (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := fun z hz =>
    ball_subset_closedBall (hmapsTo hz)
  -- Schwarz for `g`
  have hup : ∀ z ∈ unitDisc, ‖g z‖ ≤ ‖z‖ := fun z hz =>
    Complex.norm_le_norm_of_mapsTo_ball hd1 hmaps hg0 (mem_ball_zero_iff.mp hz)
  -- Schwarz for the inverse, which also fixes `0`
  have hsymm := hg.symm isOpen_ball
  have hinv0 : Function.invFunOn g unitDisc 0 = 0 := by
    have h := hg.2.1.leftInvOn_invFunOn h0mem
    rwa [hg0] at h
  have hd2 : DifferentiableOn ℂ (Function.invFunOn g unitDisc) (ball (0 : ℂ) 1) := hsymm.1
  have hmaps2 : MapsTo (Function.invFunOn g unitDisc) (ball (0 : ℂ) 1) (closedBall (0 : ℂ) 1) :=
    fun z hz => ball_subset_closedBall (hsymm.mapsTo hz)
  have hdown : ∀ w ∈ unitDisc, ‖Function.invFunOn g unitDisc w‖ ≤ ‖w‖ := fun w hw =>
    Complex.norm_le_norm_of_mapsTo_ball hd2 hmaps2 hinv0 (mem_ball_zero_iff.mp hw)
  -- hence `‖g z‖ = ‖z‖` throughout the disc
  have heq : ∀ z ∈ unitDisc, ‖g z‖ = ‖z‖ := by
    intro z hz
    refine le_antisymm (hup z hz) ?_
    have h1 := hdown (g z) (hmapsTo hz)
    rwa [hg.2.1.leftInvOn_invFunOn hz] at h1
  -- the equality case, read at the point `1/2`
  have hz₀ : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    norm_num
  have hz₀mem : (1 / 2 : ℂ) ∈ unitDisc := hz₀
  have hz₀ne : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have hdsl : ‖dslope g 0 (1 / 2 : ℂ)‖ = 1 := by
    rw [dslope_of_ne _ hz₀ne, slope_def_field, hg0, sub_zero, sub_zero, norm_div,
      heq _ hz₀mem, div_self (norm_ne_zero_iff.mpr hz₀ne)]
  have hmaps' : MapsTo g (ball (0 : ℂ) 1) (closedBall (g 0) 1) := by
    rw [hg0]; exact hmaps
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hd1 hmaps' hz₀
    (by rw [hdsl]; norm_num)
  refine ⟨dslope g 0 (1 / 2 : ℂ), hdsl, fun z hz => ?_⟩
  have h := haff (show z ∈ ball (0 : ℂ) 1 from hz)
  simpa [hg0, smul_eq_mul, mul_comm] using h

/-! ### The Blaschke factor is a conformal self-map of `Δ` -/

/-- `1 - a ā ≠ 0` on the disc. -/
theorem one_sub_mul_conj_ne_zero {a : ℂ} (ha : ‖a‖ < 1) : (1 : ℂ) - a * conj a ≠ 0 := by
  have haa : normSq a < 1 := normSq_lt_one_iff.mpr ha
  intro hcon
  have hre := congrArg Complex.re hcon
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.zero_re] at hre
  rw [normSq_apply] at haa
  nlinarith

@[simp] theorem blaschke_neg_zero (a : ℂ) : blaschke (-a) 0 = a := by simp [blaschke]

/-- `M_a` inverts `M_{-a}` on the disc. -/
theorem blaschke_blaschke_neg {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    blaschke a (blaschke (-a) w) = w := by
  have h := blaschke_neg_blaschke (a := -a) (z := w) (by simpa using ha) hw
  rwa [neg_neg] at h

/-- The Blaschke factor is holomorphic on the disc. -/
theorem differentiableOn_blaschke {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (blaschke a) unitDisc := by
  intro z hz
  have hden := blaschke_den_ne_zero ha (mem_ball_zero_iff.mp hz)
  refine DifferentiableAt.differentiableWithinAt ?_
  exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - a) z).div
    (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 1 - conj a * w) z) hden

/-- **The Blaschke factor is a conformal map of `Δ` onto itself.** -/
theorem isConformalOnto_blaschke {a : ℂ} (ha : ‖a‖ < 1) :
    IsConformalOnto (blaschke a) unitDisc unitDisc := by
  refine ⟨differentiableOn_blaschke ha, ?_, ?_⟩
  · intro z₁ h₁ z₂ h₂ heq
    have e₁ := blaschke_neg_blaschke ha (mem_ball_zero_iff.mp h₁)
    have e₂ := blaschke_neg_blaschke ha (mem_ball_zero_iff.mp h₂)
    rw [← e₁, ← e₂, heq]
  · refine Subset.antisymm ?_ ?_
    · rintro w ⟨z, hz, rfl⟩
      exact mem_ball_zero_iff.mpr (blaschke_mem_unitDisc ha (mem_ball_zero_iff.mp hz))
    · intro w hw
      have hwn : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
      refine ⟨blaschke (-a) w, ?_, blaschke_blaschke_neg ha hwn⟩
      exact mem_ball_zero_iff.mpr (blaschke_mem_unitDisc (by simpa using ha) hwn)

/-! ### The classification -/

/-- **Every conformal map of `Δ` onto itself is a rotation composed with a Blaschke factor.**

Writing `a` for the preimage of `0`, the map `h ∘ M_{-a}` fixes `0`, hence is a rotation `z ↦ cz`
by `exists_rotation_of_isConformalOnto_fix_zero`, and so `h = c M_a`. -/
theorem exists_rotation_blaschke_of_isConformalOnto_unitDisc {h : ℂ → ℂ}
    (hh : IsConformalOnto h unitDisc unitDisc) :
    ∃ c a : ℂ, ‖c‖ = 1 ∧ ‖a‖ < 1 ∧ EqOn h (fun z => c * blaschke a z) unitDisc := by
  have h0mem : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have h0img : (0 : ℂ) ∈ h '' unitDisc := by rw [hh.2.2]; exact h0mem
  set a : ℂ := Function.invFunOn h unitDisc 0 with hadef
  have hamem : a ∈ unitDisc := Function.invFunOn_mem h0img
  have ha : ‖a‖ < 1 := mem_ball_zero_iff.mp hamem
  have hha : h a = 0 := Function.invFunOn_eq h0img
  have hbl : IsConformalOnto (blaschke (-a)) unitDisc unitDisc :=
    isConformalOnto_blaschke (by simpa using ha)
  have hg : IsConformalOnto (h ∘ blaschke (-a)) unitDisc unitDisc := hh.comp hbl
  have hg0 : (h ∘ blaschke (-a)) 0 = 0 := by
    simp only [Function.comp_apply, blaschke_neg_zero]
    exact hha
  obtain ⟨c, hc1, hceq⟩ := exists_rotation_of_isConformalOnto_fix_zero hg hg0
  refine ⟨c, a, hc1, ha, fun z hz => ?_⟩
  have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hbmem : blaschke a z ∈ unitDisc := mem_ball_zero_iff.mpr (blaschke_mem_unitDisc ha hzn)
  have hval := hceq hbmem
  rwa [Function.comp_apply, blaschke_neg_blaschke ha hzn] at hval

/-- **Every conformal map of `Δ` onto itself is a Möbius transformation.**

This is the classification that `Mathlib/Analysis/Complex/Schwarz.lean` lists as a TODO. -/
theorem exists_mobius_of_isConformalOnto_unitDisc {h : ℂ → ℂ}
    (hh : IsConformalOnto h unitDisc unitDisc) :
    ∃ A B C D : ℂ, A * D - B * C ≠ 0 ∧ EqOn h (mobiusFn A B C D) unitDisc := by
  obtain ⟨c, a, hc1, ha, heq⟩ := exists_rotation_blaschke_of_isConformalOnto_unitDisc hh
  have hc0 : c ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at hc1
    norm_num at hc1
  refine ⟨c, -(c * a), -conj a, 1, ?_, fun z hz => ?_⟩
  · have hrw : c * 1 - -(c * a) * -conj a = c * (1 - a * conj a) := by ring
    rw [hrw]
    exact mul_ne_zero hc0 (one_sub_mul_conj_ne_zero ha)
  · have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hden := blaschke_den_ne_zero ha hzn
    have hden2 : -conj a * z + 1 ≠ 0 := by
      intro hcon; exact hden (by linear_combination hcon)
    have hz' : h z = c * blaschke a z := heq hz
    rw [hz', mobiusFn, blaschke]
    field_simp
    ring

/-! ### The derivative and the density identity -/

/-- `1 - |M_a(z)|² = (1 - |z|²)(1 - |a|²)/|1 - ā z|²`. -/
theorem one_sub_normSq_blaschke {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - normSq (blaschke a z)
      = (1 - normSq z) * (1 - normSq a) / normSq (1 - conj a * z) := by
  have hden := blaschke_den_ne_zero ha hz
  have hpos : normSq (1 - conj a * z) ≠ 0 := ne_of_gt (normSq_pos.mpr hden)
  have key := normSq_blaschke_key a z
  rw [blaschke, normSq_div, eq_div_iff hpos, sub_mul, one_mul, div_mul_cancel₀ _ hpos]
  linarith [key]

/-- The derivative of the Blaschke factor: `M_a'(z) = (1 - a ā)/(1 - ā z)²`. -/
theorem hasDerivAt_blaschke {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (blaschke a) ((1 - a * conj a) / (1 - conj a * z) ^ 2) z := by
  have hden := blaschke_den_ne_zero ha hz
  have h0 : HasDerivAt (fun w : ℂ => w) 1 z := hasDerivAt_id z
  have h1 : HasDerivAt (fun w : ℂ => w - a) 1 z := by simpa using h0.sub_const a
  have h2 : HasDerivAt (fun w : ℂ => 1 - conj a * w) (-conj a) z := by
    simpa using HasDerivAt.const_sub 1 (h0.const_mul (conj a))
  have h3 := h1.div h2 hden
  have hfun : blaschke a = fun w : ℂ => (w - a) / (1 - conj a * w) := rfl
  rw [hfun]
  convert h3 using 1
  field_simp
  ring

end LiZhongQC
